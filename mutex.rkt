#lang forge

abstract sig Command {}
one sig Unlock extends Command {}
one sig Lock extends Command {}

sig Mutex{}

sig Program {
}

sig Code{
    // Alternative idea, store just the Program to Mutex relation that we potentially want to lock/unlock
    --target : one Program -> Mutex,
    owner : one Program,
    target : one Mutex,
    operation : one Command,
    nextLine : lone Code
}

sig State {
    // We want a chain of states
    next : lone State,
    // Programs that have not been completed
    toRun : set Code,
    // Current programs that hold mutexes
    locks : set Program -> Mutex
}

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


pred initState[s : State] {
    // All code is reachable from the start
    Code = s.toRun.*nextLine
    //
    some s.toRun
    // No locks
    no s.locks
}

pred canTransition[s1: State, s2: State] {
    some running: s1.toRun | {
        s1.toRun - running + running.nextLine = s2.toRun
        running.operation = Lock implies {
            running.target not in s1.locks[Program]
            running.target in s2.locks[Program]
            s2.locks - Program->(running.target) =  s1.locks // possible overconstrain?
        }
        running.operation = Unlock implies {
            running.target in s1.locks[Program]
            running.target not in s2.locks[Program]
            s1.locks - Program->(running.target) = s2.locks
            running.owner in s1.locks.(running.target)
        }
    } 
}

pred finalWithDeadlock[s: State] {
    no s.next
    all runnable: s.toRun | {
        runnable.operation = Lock
        runnable.target in s.locks[Program]
    }
}

pred finalWithoutDeadlock[s : State] {
    no s.next
    // No more code to run
    s.toRun = none
    // No locks
    no s.locks
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

pred good[s : State] {
    all s : State | {
        s.locks.~(s.locks) in iden
    }
}

pred NoDeadlock {
    all s : State | {
        s.locks.~(s.locks) in iden
    }
}

run {
    ValidStates
    TransitionStatesSafe
    NoDeadlock
} for 6 State