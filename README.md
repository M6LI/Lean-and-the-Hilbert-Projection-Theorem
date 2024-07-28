This project uses the functional programming language Lean to formally prove the Hilbert Projection Theorem, and was created as part of the Formalising Mathematics course taught by Prof. Kevin Buzzard in 2022. There was no such proof available prior to this project.

The Hilbert Projection Theorem is a famous result in analysis which says that for any vector $x$ in a Hilbert space and any nonempty closed convex subset $C$, there exists a unique vector $m \in C$ for which $\inf_{y \in C}\|y-x\|$ is achieved by $m$.

The proof consists of three sections:

### Section 1: Preliminary definitions:
Here we define basic structures that we will use, such as the definition of a Cauchy sequence, closedness and convexity of subsets of a normed space.

### Section 2: Preliminary lemmas:
Here we prove a series of lemmas which we will need in the main proof. For example, we prove that the parallelogram law holds in a normed space, and some general properties of cauchy sequences.

### Section 3: The main proof:
This is where we construct the main proof, utilising the lemmas and definitions from the previous two sections.
