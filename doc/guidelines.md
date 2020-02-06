# Writing and Coding Guidelines

This project targets Coq *non*-experts. Accordingly, great emphasis is placed
on keeping it as simple and as accessible as possible.

**Note**: this is a living document that will evolve as we collectively gather experience.

## Core Principles

1. **Readability** matters most. Specifications that are difficult to grasp are fundamentally no more trustworthy than elegant pen&paper proofs. 

2. **Verbosity** is good. The overarching goal is to make it easy for the (non-expert) reader. Being verbose and (within reason) repetitive helps to make a spec more readable because most statements can then be understood within a local scope.

3. **Good names** are essential. Choose long, self-explanatory names. Even if this means "more work" when typing the name a lot, it greatly helps with providing a helpful intuition to the reader.
   
4. **Comment** profusely. Make an effort to comment all high-level steps and definitions. In particular, comment all hypotheses, definitions, lemmas, etc.
   
5. **Keep it simple.** Shy away from advanced Coq techniques. At the very least, the spec and all lemmas should be readable and understandable with a basic understanding of Coq.


## Specific Advice

- Use many, mostly short sections. Sections are a great way to structure code and to guide the reader; they serve the reader by establishing a local scope that is easier to remember.

- Keep proofs short. Aim for just a few lines, and definitely not more than 30-50. Long arguments should be structured into many individual lemmas (in their own section) that correspond to high-level proof steps. Some exceptions may be needed, but such cases should truly remain *exceptional*.

- Keep definitions and proofs in separate sections. This makes the definition section short and more clearly separates the computation of the actual bounds from their validity arguments.

- Make extensive use of the `Hypothesis` feature. They are very readable and are accessible even to non-Coq users, especially when paired with self-explanatory names.

- For consistency, start the name of hypothesis with `H_`.

- Make proofs "step-able." This means preferring `.` over `;` when possible. This makes it easier for novices to learn from existing proofs.

- Document the tactics that you use in the [list of tactics](doc/tactics.md). For new users, it can be quite difficult to identify the right tactics to use. This list ist intended to give novices a starting to point in the search for the "right" tools.

- Use renaming to introduce local names that are more meaningful. In many cases, this is also useful to bind necessary context to local names. For example:
```
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task sched tsk.
``` 

- Interleave running commentary *as if you were writing a paper* with the actual definitions and lemmas. This helps greatly with making the spec more accessible to everyone. Good example from [bertogna_fp_theory.v](../bertogna_fp_theory.v):
```
   (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.
   (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
```

- Document the sources of lemmas and theorems in the comments. For example, say something like "Theorem XXX in (Foo & Bar, 2007)", and document at the beginning of the file what "(Foo & Bar, 2007)" refers to.


## Writing Proofs

- Make use of the code blocks feature (i.e., indentation with `{` and `}`) to structure code.

- Make use of the `by` syntax to stop the proof script early in case of any changes in the assumptions.

*To be continued… please feel free to add your advice.*