#lang forge

sig State {
    next : lone State,
    toRun : set Code,
    locks : set Program -> Mutex
}

sig Mutex{}
sig Program {}

sig Code {
    owner : one Program,
    target : one Mutex,
    operation : one Command,
    nextLine : lone Code
}

abstract sig Command {}
one sig Unlock extends Command {}
one sig Lock extends Command {}

pred ValidStates {
    all s : State | all ins: s.toRun | {
        -- in toRun, each program have at most one entries
        ins.owner not in (s.toRun - ins).owner
    }

    -- each program 
    all p: Program | some first: Code {
        -- each program have at least one line of code
        first.owner = p

        -- truly the first line
        no nextLine.first

        -- every code in this program is reachable from first
        owner.p in first.*nextLine

        -- the subsequence code is also from the same owner
        first.^nextLine.owner in first.owner
    }

    -- the code is linear (injective)
    nextLine.~nextLine in iden
}

test expect ValidTest {
    {
        ValidStates implies {
            all ins: Code | {
                -- every code in next lines belong to the same program
                ins.^nextLine.owner in ins.owner
            }

            -- no cycle in the program
            no iden & ^nextLine

            -- each program should have at least one line of code
            Program in Code.owner

            -- in a state, no two code may have the same owner
            not (some s: State | some c1, c2: s.toRun | c1 != c2 and c1.owner in c2.owner)
        }
    } for 4 Program, 8 Code is theorem
}

pred canTransition[s1: State, s2: State] {
    -- Cannot cause a deadlock
    -- Cannot unlock a mutex that is not locked by the program
    some running: s1.toRun | {
        -- every other lines is not changing
        s1.toRun - running + running.nextLine = s2.toRun

        running.operation = Lock implies {
            running.target not in s1.locks[Program]
            running.target in s2.locks[Program]
            -- every other locks stay the same
            s2.locks - (running.owner)->(running.target) =  s1.locks     
        }
        running.operation = Unlock implies {
            running.target in s1.locks[Program]
            running.target not in s2.locks[Program]
            s1.locks - Program->(running.target) = s2.locks -- every other locks stay the same
            
            -- ownership is right
            running.owner in s1.locks.(running.target)
        }
    } 
}

pred initState[s : State] {
    Code = s.toRun.*nextLine
    no s.locks
}

pred finalWithoutDeadlock[s : State] {
    no s.next
    s.toRun = none
    no s.locks
}

pred finalWithDeadlock[s: State] {
    no s.next
    some s.toRun
    all runnable: s.toRun | {
        runnable.operation = Lock
        runnable.target in s.locks[Program]
    }
}

pred TransitionStatesSafe {
    some start, end : State | {
        initState[start]
        finalWithoutDeadlock[end]
        State in start.*next
        all s1, s2 : State {
            s1.next = s2 implies {canTransition[s1, s2]}
        }
    }
}

pred TransitionStatesUnsafe {
    some start, end : State | {
        initState[start]
        finalWithDeadlock[end]
        State in start.*next
        all s1, s2 : State {
            s1.next = s2 implies {canTransition[s1, s2]}
        }
    }
}

-- for testing the transition function
pred good[s: State] {
    -- no mutex is held by two programs
    s.locks.~(s.locks) in iden

    -- no two entries in toRun belonging to the same program
    all p: Program | lone c: s.toRun | c.owner = p
}

test expect {
    goodTransitionSafe: {
        ValidStates and TransitionStatesSafe implies {
            all s: State | good[s] -- every states are good
            one s: State | no s.next -- only one final
            some s: State | no s.next and no s.toRun and no s.locks -- lock-free final state
        }
    } for 8 Code is theorem 

    goodTransitionUnsafe: { 
        ValidStates and TransitionStatesUnsafe implies {
            all s: State | good[s] -- every states are good
            one s: State | no s.next -- only one final
            some s: State | {
                no s.next
                some mux: s.locks[Program] | {
                    mux in (operation.Lock & s.toRun).target
                }
            } -- deadlocked final state
        }
    } for 8 Code is theorem
}

//run {
//    ValidStates
//    TransitionStatesSafe 
//} for 7 State, exactly 2 Program, exactly 2 Mutex, exactly 2 Command, 6 Code

run {
    ValidStates
    TransitionStatesUnsafe 
} for exactly 5 State, exactly 2 Program, exactly 2 Mutex, exactly 2 Command, 5 Code

// initState tests
example validInit is initState[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example unreachableCode is not initState[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = none
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example startingLock is not initState[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

// finalWithoutDeadlock tests
example validFinal is finalWithoutDeadlock[State] for {
    State = State0
    next = none
    toRun = none
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example nextExists is not finalWithoutDeadlock[State] for {
    State = State0 + State1
    next = State0 -> State1
    toRun = none
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example leftoverCode is not finalWithoutDeadlock[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example leftoverLocks is not finalWithoutDeadlock[State] for {
    State = State0
    next = none
    toRun = none
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

//finalWithDeadlock tests
example validDeadlock is finalWithDeadlock[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0 + State0 -> Code2
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex1
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example ableToUnlockDeadlock is not finalWithDeadlock[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0 + State0 -> Code2
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex1
    + Code3 -> Mutex1
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example ableToLockDeadlock is not finalWithDeadlock[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0 + State0 -> Code2
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex1
    + Code3 -> Mutex1
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example nothingToRun is not finalWithDeadlock[State] for {
    State = State0
    next = none
    toRun = none
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex1
    + Code3 -> Mutex1
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example validDeadlockWith2 is finalWithDeadlock[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0 + State0 -> Code2
    locks = State0 -> Program0 -> Mutex0
    + State0 -> Program0 -> Mutex1
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex1
    + Code3 -> Mutex1
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

//good tests
example validGood is good[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = none
    Mutex = Mutex0
    Program = Program0
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example twoLocks is not good[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    locks = State0 -> Program0 -> Mutex0
    + State0 -> Program1 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example sameProgramToRun is not good[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    + State0 -> Code1
    locks = none
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program0
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example multipleToRun is good[State] for {
    State = State0
    next = none
    toRun = State0 -> Code0
    + State0 -> Code1
    locks = none
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1
    owner = Code0 -> Program0
    + Code1 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    nextLine = Code0 -> Code1
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

//canTransition tests
example validLock is canTransition[next.State, State.next] for {
    // Code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State1 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example invalidLock is not canTransition[next.State, State.next] for {
    // No new lock after code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = none
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example alreadyLocked is not canTransition[next.State, State.next] for {
    // Code0 is run, but it was already locked before
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0 + State1 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example alreadyLockedByAnotherProgram is not canTransition[next.State, State.next] for {
    // Code2 is run, but there was already a lock
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code0
    + State1 -> Code3
    locks = State0 -> Program0 -> Mutex0 + State1 -> Program1 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example inappropriateLockChange is not canTransition[next.State, State.next] for {
    // A lock that was in State1 goes missing from State2
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0 + State1 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example hold2Locks is canTransition[next.State, State.next] for {
    // Tests if a lock on a different mutex will remain
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex1
    + State1 -> Program0 -> Mutex1
    + State1 -> Program0 -> Mutex0
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example incorrectCommand is not canTransition[next.State, State.next] for {
    // Runs as if it was an unlock command, but it's meant to lock
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example validUnlock is canTransition[next.State, State.next] for {
    //Code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example invalidUnlock is not canTransition[next.State, State.next] for {
    //Old lock remains
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    + State1 -> Program0 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example lockTheft is not canTransition[next.State, State.next] for {
    //Lock does not belong to them
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program1 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example lockDNE is not canTransition[next.State, State.next] for {
    //target lock does not exist
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = none
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example holdingTwoUnlock is canTransition[next.State, State.next] for {
    //Code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    + State0 -> Program0 -> Mutex1
    + State1 -> Program0 -> Mutex1
    Mutex = Mutex0 + Mutex1
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example incorrectCommand2 is not canTransition[next.State, State.next] for {
    //Adds locks rather than taking them away
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    + State1 -> Program0 -> Mutex0
    + State1 -> Program1 -> Mutex0
    Mutex = Mutex0
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example genericUnlock is canTransition[next.State, State.next] for {
    //Code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State0 -> Program0 -> Mutex0
    + State0 -> Program0 -> Mutex2
    + State0 -> Program1 -> Mutex1
    + State1 -> Program0 -> Mutex2
    + State1 -> Program1 -> Mutex1
    Mutex = Mutex0 + Mutex1 + Mutex2
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Unlock0
    + Code1 -> Lock0
    + Code2 -> Unlock0
    + Code3 -> Lock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}

example genericLock is canTransition[next.State, State.next] for {
    //Code0 is run
    State = State0 + State1
    next = State0 -> State1
    toRun = State0 -> Code0
    + State0 -> Code2
    + State1 -> Code1
    + State1 -> Code2
    locks = State1 -> Program0 -> Mutex0
    + State0 -> Program0 -> Mutex2
    + State0 -> Program1 -> Mutex1
    + State1 -> Program0 -> Mutex2
    + State1 -> Program1 -> Mutex1
    Mutex = Mutex0 + Mutex1 + Mutex2
    Program = Program0 + Program1
    Code = Code0 + Code1 + Code2 + Code3
    owner = Code0 -> Program0
    + Code1 -> Program0
    + Code2 -> Program1
    + Code3 -> Program1
    target = Code0 -> Mutex0
    + Code1 -> Mutex0
    + Code2 -> Mutex0
    + Code3 -> Mutex0
    operation = Code0 -> Lock0
    + Code1 -> Unlock0
    + Code2 -> Lock0
    + Code3 -> Unlock0
    nextLine = Code0 -> Code1
    + Code2 -> Code3
    Command = Lock0 + Unlock0
    Lock = Lock0
    Unlock = Unlock0
}