# Roadmap: reductive algebraic groups (paved)

The theory of reductive algebraic groups is the long game: it underpins the Langlands
programme, automorphic forms, and much of FLT, and it is almost entirely absent from
Mathlib. **We are not waiting for it to appear upstream; we build it here**, in
`TauCeti/`, as a large, iteratively-expandable tower. Suggested home:
`TauCeti/Algebra/AlgebraicGroup/` (foundations) and `TauCeti/AlgebraicGeometry/`
(the scheme-side dictionary).

Early sketches in this area get the *types* roughly right but the *mathematics* subtly
wrong; the common traps are flagged inline below (marked ⚠) so we avoid them from the
start.

## Standing hypotheses

Spell hypotheses out; **do not** bundle them into one mega-class (Kevin Buzzard,
repeatedly on Zulip: separate typeclass assumptions let every result be proved in its
correct generality). Work over a field `k` to start; generalize to a base later.

Keep **two distinct notions**, and never make smoothness implicit:
- an **affine group scheme of finite type** over `k`: a commutative Hopf `k`-algebra `A`
  finitely generated as a `k`-algebra. This admits `μ_p`, `αₚ`, and other non-smooth /
  non-reduced groups, and is the right default generality.
- a **smooth** such group (an "algebraic group" in the classical sense): add smoothness
  as a named hypothesis. For group schemes locally of finite type over a *field*,
  smoothness ⇔ geometric reducedness of `A` (a fact special to the homogeneous,
  finite-type-over-a-field setting, *not* a general commutative-algebra equivalence; in
  characteristic 0 every such group is automatically smooth, by Cartier).

There will be **no** monolithic `LinearAlgebraicGroup`/`Variety` definition. Like
Mathlib, we state exactly the hypotheses each result needs.

## What "paved" means here

Maintain **three equivalent views** of an affine algebraic group and the explicit
equivalences between them, so any proof can work in whichever is most convenient:

1. **Commutative Hopf algebras** over `k` (the coordinate ring `A`).
2. **Group objects in schemes**: `GrpObj (Over.mk (φ : G ⟶ Spec k))` with `IsAffine`.
3. **The functor of points**: a representable group-valued functor `R ↦ Homₖ(A, R)`.

Representations are then **comodules over `A`**, and we keep the
representation ⇆ comodule ⇆ Tannakian dictionary in sync throughout. Wherever there is
a modelling fork (Hopf-ideal kernel vs. scheme-theoretic kernel; root data vs. dynamic
parabolics; reductive-via-unipotent-radical vs. linearly-reductive), **do both and
prove them equivalent** rather than committing.

## Inventory: what Mathlib master already gives us (consume)

- **Hopf/coalgebra algebra:** `Mathlib/RingTheory/HopfAlgebra/{Basic,GroupLike,TensorProduct}.lean`,
  `Mathlib/RingTheory/Coalgebra/{Convolution,GroupLike}.lean`.
- **Categorical group objects:** `Mathlib/CategoryTheory/Monoidal/{Mon_,Comon_,Bimon_,Grp_,CommGrp_}.lean`
  and the cartesian/`Over` variants, so view 2 is expressible (and Kevin's equivalence
  statements below already elaborate).
- **Algebra categories:** `Mathlib/Algebra/Category/CoalgCat/ComonEquivalence.lean`
  (coalgebras ≃ comonoids), `Mathlib/Algebra/Category/CommAlgCat/{Basic,FiniteType,Monoidal}.lean`.
- **Scheme-side group theory:** `Mathlib/AlgebraicGeometry/Group/Abelian.lean` (the
  rigidity theorem: proper group schemes are commutative) and `…/Group/Smooth.lean`.
- **Smoothness ingredient:** `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`.
- **Combinatorial prerequisites** (not ready-made algebraic-group infrastructure; they
  supply abstract root systems/Weyl groups; extracting a *root datum from a group* still
  needs substantial glue): `Mathlib/LinearAlgebra/RootSystem/*` (root pairings, bases,
  Cartan matrices) and `Mathlib/GroupTheory/Coxeter/*`.
- **Representation theory to mine for patterns** (finite-group / module flavour; it does
  *not* generalize directly without building comodules and rational representations first):
  `Mathlib/RepresentationTheory/{FDRep,Character,Tannaka,Maschke,Semisimple,Irreducible}.lean`.

## Inventory: what is missing (build here)

Comodules over a coalgebra (**none in Mathlib**) and the finite-dimensional subcoalgebra
theory; the convolution group structure on the functor of points; the fppf-sheaf /
faithfully-flat-descent machinery on `CommAlgCat k`; the explicit Hopf ⇆
affine-group-scheme equivalence (the Toric work,
[mathlib4#39281](https://github.com/leanprover-community/mathlib4/pull/39281), is not in
master); the Lie algebra `Lie(G)` and the adjoint representation; Hopf ideals / closed
subgroup schemes and quotients; the identity component and component group; Jordan
decomposition; diagonalizable / multiplicative-type groups and tori with character
lattices; unipotent groups and the unipotent radical; reductive/semisimple groups, central
isogenies and simply-connected/adjoint forms; Borel and parabolic subgroups, root data of
a group, Bruhat/BN-pairs; and the classification.

---

## The build, in layers

Each layer is self-contained mathematics the next layer needs. As a layer makes the
next layer's *types* expressible, state that layer's milestones in `Targets.lean` (with
`sorry`) and hand them to the AIs to discharge in `TauCeti/`. The ordering below is the
dependency order, not a strict schedule; independent lanes can proceed in parallel.

**Cross-cutting prerequisite: sheaves and descent.** Several constructions below (the
functor-of-points view, quotients, torsors, representability) need the fppf topology and
faithfully-flat descent, so this is a lane that starts early, not a single layer:
presheaves on `CommAlgCat k`, Yoneda/representability, fppf sheafification, torsors, and
faithfully-flat descent.

### Layer 0: the functor of points and the three-way dictionary
- **R-points as a group.** Generalize `AlgPoints R A := A →ₐ[k] R` for every *commutative*
  `k`-algebra `R` (the functor of points lives on `CommAlgCat k`; the *values* `G(R)` may
  be non-commutative, but `R` is commutative). Give it a group structure by **convolution**
  (not composition): `(f * g)(a) = ∑ f(a₁) g(a₂)`, identity the counit `ε`, inverse `f ∘ S`.
  - ⚠ Pitfall: `GroupLike k A` is **not** the points functor; for `GLₙ` the points are
    non-commutative, but group-like elements always form a commutative group.
  - Ingredient already in Mathlib: the antipode is an anti-homomorphism, `S(ab) = S(b) S(a)`
    (`HopfAlgebra.antipode_mul`). Use it to show algebra homs are closed under convolution
    and that `f ∘ S` is the inverse; then prove functoriality in `R`.
- **The equivalences (first concrete targets, already compile as `sorry` in `Targets.lean`):**
  ```lean
  -- Γ(G) is an R-Hopf algebra, for G an affine group scheme over Spec R:
  example (G : Scheme) (φ : G ⟶ Spec(R)) [GrpObj (Over.mk φ)] [IsAffine G] :
      HopfAlgebra R (Γ.obj (op G)) := sorry
  -- the affine group scheme Spec A over Spec R associated to a Hopf algebra A:
  example (A : Type u) [CommRing A] [HopfAlgebra R A] :
      GrpObj (Over.mk (map (ofHom (algebraMap R A)) : Spec(A) ⟶ Spec(R))) := sorry
  ```
  The `Γ`-direction needs supporting facts first: affine fibre products and
  `Γ(Spec A ×_{Spec R} Spec B) ≅ A ⊗_R B`, the terminal object over `Spec R`, and the
  contravariant translation of multiplication/unit/inverse into comultiplication/counit/
  antipode. Assemble these into a full **anti-equivalence**
  `(CommHopfAlg k)ᵒᵖ ≌ AffGrpSch k` (finite-type/smooth kept as predicates, not baked into
  the category) and a third equivalence with representable group functors. (Consume
  `CoalgCat/ComonEquivalence`, `Grp_`, `CommAlgCat`; the Toric route gives one direction
  once available.)
- **Base change.** `K ⊗[k] A` as a Hopf algebra over `K` (use
  `HopfAlgebra/TensorProduct.lean`). Geometric notions are all defined after base change
  to `k̄`.

### Layer 1: representations = comodules
- **Comodules** over a coalgebra/Hopf algebra `A`: a coaction `ρ : V → V ⊗ A` with
  coassociativity and counit; comodule morphisms; the (rigid monoidal) category of
  **finite-dimensional** comodules; tensor products, duals, the regular representation.
- **Finite-dimensional subcoalgebras** (the fundamental theorem of comodules): every
  element lies in a finite-dimensional subcoalgebra; every comodule is the union of its
  finite-dimensional subcomodules. This is the real engine behind the embedding theorem.
- **The dictionary:** representation of `G` ⇆ `A`-comodule; matrix coefficients.
- **Faithfulness done right:** define a representation to be faithful when
  `G → GL(V)` is a **closed immersion**, and prove this is equivalent to its **matrix
  coefficients generating `A`**. ⚠ This is *not* the same as the coaction (or the map on
  `k`/`k̄`-points) being injective.
- **Embedding theorem (hard):** every affine group scheme of finite type has a faithful
  f.d. representation, i.e. a closed immersion `G ↪ GLₙ`, proved via the f.d.
  subcoalgebra theorem, not bare Noetherianity.
- **Tannakian reconstruction:** recover `G` from its tensor category of representations
  (mine `RepresentationTheory/Tannaka.lean` for the pattern; the content must be rebuilt
  for comodules).

### Layer 2: Lie algebra and the adjoint representation
- **Tangent space at the identity / `Lie(G)`**, the differential of a homomorphism, the
  Lie algebra of a closed subgroup, and the **adjoint action** `Ad : G → GL(Lie G)`.
- **Smoothness and dimension tools** via `Lie(G)` (dimension of kernels, the smoothness
  criterion). These are needed before Jordan decomposition, root spaces, and the unipotent
  radical, which is why this sits early.

### Layer 3: subgroups, quotients, components
- **Hopf ideals ↔ closed subgroup schemes:** an ideal `I` with `Δ(I) ⊆ I⊗A + A⊗I`,
  `ε(I)=0`, `S(I) ⊆ I`; the quotient Hopf algebra `A/I`; the anti-equivalence; kernels.
- **Normality and quotients:** normal = Hopf ideal stable under the adjoint coaction
  (needs the conjugation/adjoint morphism at Hopf level). The quotient `G/H` is first the
  **fppf sheaf quotient**; whether it is represented by a scheme (and when by an *affine*
  one, e.g. `H` reductive, by Matsushima) is a **theorem with hypotheses**, not automatic.
  Then short exact sequences.
- **Identity component `G°` and component group `π₀(G)`:** geometric connectedness
  (`A ⊗ k̄` has no nontrivial idempotents, *stronger* than over `k`). Under smoothness
  (and over a perfect field, or suitable hypotheses) `π₀(G)` is finite étale.
  ⚠ Reserve the term **connected–étale sequence** for *finite* group schemes; here use
  "identity component and component group", and "connected" always means the geometric
  notion.

### Layer 4: Jordan decomposition, diagonalizable groups, tori
- **Jordan decomposition** of elements into semisimple and unipotent parts (geometric,
  over `k̄`), functorial under representations.
- **Diagonalizable groups and groups of multiplicative type:** the anti-equivalence
  `M ↦ D(M) = Spec k[M]` between finitely generated abelian groups and diagonalizable
  groups; `μ_n = D(ℤ/n)`, `𝔾_m = D(ℤ)`; the non-smooth example `μ_p` in characteristic `p`.
  (*Cartier duality* proper is the duality of **finite locally free** commutative group
  schemes, a related but distinct statement to develop separately.)
- **Tori:** split and non-split; the **character lattice** `X*(T)` and **cocharacter
  lattice** `X_*(T)` with their perfect pairing: the input to root data.

### Layer 5: solvable and unipotent groups; the unipotent radical
- **Unipotent groups** (correct, geometric definition): `g ∈ G(k̄)` is unipotent iff
  `ρ_g − id` is nilpotent for **every** f.d. representation; a smooth connected group is
  unipotent iff it embeds in the upper-triangular unipotent `Uₙ`.
  - ⚠ "No nontrivial characters" is **not** equivalent to unipotent (e.g. `SLₙ` has no
    nontrivial characters but is semisimple). The implication is one-way: a *connected
    unipotent* group has no nontrivial characters; the converse needs solvability.
  - ⚠ A naïve `IsUnipotent` that tests nilpotence in the reduced ring `A` is *vacuous*
    (only `g = 1` qualifies): the correct definition needs comodule theory (Layer 1).
- **Lie–Kolchin**; solvable groups.
- **The unipotent radical `R_u(G)`** (the hard core, SGA3/Borel level): the maximal
  connected normal unipotent closed subgroup. ⚠ Over **imperfect** fields the geometric
  unipotent radical `R_u(G_{k̄})` need *not* descend to `k`; this is exactly where
  pseudo-reductive groups appear. **Assume `k` perfect first** (so descent is fine), or
  define reductivity by the geometric condition without constructing a descended subgroup;
  distinguish the `k`-unipotent radical from the geometric one in general.

### Layer 6: reductive and semisimple groups
- **Reductive:** smooth, connected, with `R_u(G_{k̄})` trivial. **Semisimple:** radical
  `R(G)` (maximal connected normal solvable, geometric) trivial. Develop the radical,
  the centre `Z(G)`, the derived group `G_der`, **central isogenies**, and the simply
  connected and adjoint forms: these are not optional for the classification.
- **Alternative paving, linearly reductive:** every f.d. representation is completely
  reducible. ⚠ Reductive groups are **not** linearly reductive in characteristic `p`
  (rational representations are generally not semisimple). State the equivalence precisely:
  for smooth connected affine groups in **characteristic 0**, reductive ⇔ linearly
  reductive (Maschke-flavoured; mine `Semisimple`/`Maschke`); over an algebraically closed
  field of characteristic `p`, a connected group is linearly reductive iff it is a torus.
  Provide both definitions and the char-0 equivalence so downstream work can pick either.

### Layer 7: structure theory
- **Borel subgroups, maximal tori**, and their conjugacy; **parabolic** subgroups and
  **Levi** decomposition.
- **Root datum** `(X*(T), Φ, X_*(T), Φ^∨)` of `(G, T)` with its **Weyl group**: do the
  **split** case first (split maximal torus, or work over `k̄`), consuming
  `LinearAlgebra/RootSystem/*` and `GroupTheory/Coxeter/*`; then add the **absolute root
  datum with Galois action** and the **relative root system** for non-split groups.
- **Bruhat decomposition** and **BN-pairs / Tits systems**. Keep the **dynamic** approach
  to parabolics/Levi/unipotent radical (Kevin, Shurui Liu, Stepan Nesterov on Zulip) as a
  parallel route that avoids full root data, useful for the `p`-adic representation-theory
  consumers, who can ask only for a BN-pair.

### Layer 8: classification and existence (long horizon)
- The **isomorphism** and **existence theorems**: split reductive groups ↔ root data;
  classification of semisimple groups by Dynkin diagrams; central isogenies and the
  isogeny theorem; Chevalley existence.
- **Relative theory over a base** and **pseudo-reductive groups**
  (Conrad–Gabber–Prasad), flagged as far-future generalizations.

---

## Worked examples (build alongside, as "checks along the way")

Concrete Hopf algebras / group schemes that exercise and validate the definitions:
`𝔾_a`, `𝔾_m`, `μ_n`/`μ_p`, `GLₙ`, `SLₙ`, `PGLₙ`, `SOₙ`, `Sp₂ₙ`, and tori. Prove they are
reductive where applicable via `R_u = 1` / root data (the definition that works in all
characteristics), and *additionally* via complete reducibility only in characteristic 0
or for linearly reductive groups. Exercise the diagonalizable/Cartier-duality theory on
the multiplicative-type examples. (Kevin's caution: don't *develop the general theory* from
`GLₙ`, but examples are exactly how we keep the definitions honest.)

## Design notes (from Zulip)

- **Functor of points is the notion of points**, not `GroupLike`, not just `k`-points.
- **Faithful = matrix coefficients generate `A`**, not "coaction injective".
- **Geometric notions** (connected, unipotent, reductive) are defined after base change
  to `k̄`.
- **Don't bundle** typeclasses; **admit** non-smooth/non-reduced groups (`μ_p`) and make
  smoothness an explicit hypothesis where used.
- **Pave**: keep the Hopf / group-object / functor-of-points views and the
  representation ⇆ comodule dictionary synchronized via explicit equivalences.

## Downstream consumers (why this matters)

`p`-adic representation theory of `G(K)` (smooth/admissible representations, Hecke
algebras, Shurui Liu et al.), the Langlands programme, automorphic forms (Kevin
Buzzard), and FLT. Several of these can start against a **BN-pair** or the dynamic
parabolic API before the full root-data classification exists: another reason to pave.

## References

- J. S. Milne, *Algebraic Groups* (2017): the modern scheme-theoretic reference.
- W. C. Waterhouse, *Introduction to Affine Group Schemes*: Hopf algebras, comodules,
  closed subgroups, the unipotent radical.
- A. Borel, *Linear Algebraic Groups*; T. A. Springer, *Linear Algebraic Groups*.
- J. C. Jantzen, *Representations of Algebraic Groups*.
- B. Conrad, *Reductive Group Schemes* (SGA3 exposition); **SGA3**, Exposé XIX.
- B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups* (relative theory).

## Acknowledgements

This roadmap builds directly on earlier discussions on the [Lean
Zulip](https://leanprover.zulipchat.com/), and would not have been possible without them:

- [#Is there code for X? > Algebraic groups](https://leanprover.zulipchat.com/#narrow/channel/217875-Is%20there%20code%20for%20X%3F/topic/Algebraic%20groups)
  (Michael Rothgang, Bryan Gin-ge Chen, Yaël Dillies), on the Hopf / group-scheme
  dictionary and the convolution-product work in mathlib4#39281.
- [#maths > class and def (p-adic reps)](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/class%20and%20def%20%28p-adic%20reps%29)
  (Kevin Buzzard, Shurui Liu, Stepan Nesterov), discussing the dynamic-parabolics /
  BN-pair approach and the downstream p-adic-representation consumers cited above.

Thanks to everyone who contributed to these discussions, and for the recurring Zulip
guidance on keeping typeclass assumptions unbundled.
