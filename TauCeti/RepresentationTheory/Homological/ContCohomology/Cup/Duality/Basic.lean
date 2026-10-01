/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod

import TauCeti.Algebra.Group.Hom.Instances
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Evaluation cups for finite discrete modules

For a finite discrete `G`-module `M` and a discrete module `N`, evaluation is an equivariant
biadditive pairing from `InternalHom G M N` and `M` to `N`. The three low-degree cup shapes of
total degree two give pairings from `Hⁱ(G, InternalHom G M N)` and `H²⁻ⁱ(G, M)` to `H²(G, N)`.
These are the underlying cohomological pairings used in duality statements.

The cochain formulas below fix the order of the two inputs: the internal hom is always the first
factor, so in degree `(1,1)` the evaluation is `a(g) (g • b(h))`.

The three pairings are compatible with the maps of coefficients in two ways (Serre, exposé 252,
§9.1, following Tate). First, they are **natural in the module**: a `G`-map `f : M →+[G] M'` and
its dual `InternalHom.precomp G f` are adjoint, `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩` in each of the three
shapes. Second, they are **compatible with the connecting maps** of a short exact sequence
`0 → A → B → C → 0` and of its dual sequence `0 → C' → B' → A' → 0`, whenever the latter exists
(`DiscreteShortExact.dual`, for instance for modules killed by a prime): in the two shapes of
total degree two that involve a connecting map, the connecting map of the dual sequence, paired
against a class of the original one, is the connecting map of the original sequence paired against
the dual class, with the Leibniz sign `(-1)^(p+1)` of the degree `p` of the dual class. These are
the low-degree identities needed to compare the duality maps
`Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, N))`, `i = 0, 1, 2`, along the segment

```text
H⁰(G, A) → H⁰(G, B) → H⁰(G, C) → H¹(G, A) → H¹(G, B) → H¹(G, C) → H²(G, A) → H²(G, B) → H²(G, C)
```

of the long exact sequence of a short exact sequence and the corresponding segment for its dual.

Read with the module first, the same cups give **Tate's duality maps**
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, InternalHom G M N), H²(G, N))`, `x ↦ ⟨x, -⟩`, for `i = 0, 1, 2`
(Serre, *Structure de certains pro-p-groupes*, §9.1): `TauCeti.ContCohomology.dualityMap0`,
`dualityMap1` and `dualityMap2`. They are the explicit cups along the opposite evaluation pairing
`(m, φ) ↦ φ m`, so graded commutativity relates them to the evaluation cups: `α₀` and `α₂` are the
`(2,0)` and `(0,2)` evaluation cups with their arguments swapped, and `α₁` is the negative of the
swapped `(1,1)` evaluation cup. For a trivial action on `ZMod n` the internal hom is `ZMod n` again,
by evaluation at `1`, and the duality maps are scalar multiplication on `H²(G, ZMod n)` in degrees
`0` and `2` and the cup product of multiplication in degree `1`. In that setting `α₂` is always
bijective, and `α₀` is bijective as soon as `H²(G, ZMod p)` is one-dimensional.

Read through the duality maps, naturality in the module says `αᵢ (f_* x) b = αᵢ x (f^* b)`, so for a
bijective `f` the square formed by `αᵢ` on `M`, `αᵢ` on `M'`, `f_*` on cohomology and `f^*` on the
targets commutes, and bijectivity of each `αᵢ` transports from `M'` to `M`. This is how a base case
stated for `ZMod p` applies to every trivial module of order `p`.

## Main statements

* `TauCeti.ContCohomology.explicitDualityPairing02`, `explicitDualityPairing11` and
  `explicitDualityPairing20`, with their cochain formulas `explicitDualityPairing02_mk`,
  `explicitDualityPairing11_mk` and `explicitDualityPairing20_mk`.
* `TauCeti.ContCohomology.explicitDualityPairing02_explicitCoeff2`,
  `explicitDualityPairing11_explicitCoeff1` and `explicitDualityPairing20_explicitCoeff0`:
  **naturality in the module**, `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩`, one identity per shape.
* `explicitDualityPairing11_explicitDelta0_dual_eq_neg_explicitDualityPairing02_explicitDelta1` and
  `explicitDualityPairing20_explicitDelta1_dual_eq_explicitDualityPairing11_explicitDelta0`:
  **compatibility with the connecting maps** of a short exact sequence and of its dual sequence,
  `⟨δ x, y⟩ = (-1)^(p+1) ⟨x, δ y⟩`, in the two shapes of total degree two that involve a
  connecting map.
* `TauCeti.ContCohomology.dualityMap0`, `dualityMap1` and `dualityMap2`: Tate's duality maps,
  with their cochain formulas `dualityMap0_mk`, `dualityMap1_mk`, `dualityMap2_mk` and their
  comparison with the evaluation cups `dualityMap0_eq_explicitDualityPairing20`,
  `dualityMap1_eq_neg_explicitDualityPairing11` and `dualityMap2_eq_explicitDualityPairing02`.
* `TauCeti.ContCohomology.dualityMap0_explicitCoeff0`, `dualityMap1_explicitCoeff1` and
  `dualityMap2_explicitCoeff2`: **naturality of the duality maps in the module**,
  `αᵢ (f_* x) b = αᵢ x (f^* b)`.
* `TauCeti.ContCohomology.dualityMap0_bijective_of_bijective`, `dualityMap1_bijective_of_bijective`
  and `dualityMap2_bijective_of_bijective`: bijectivity of each duality map transports along an
  isomorphism of modules.
* `TauCeti.ContCohomology.explicitCoeff2_dualityMap0`, `explicitCoeff2_dualityMap1` and
  `explicitCoeff2_dualityMap2`: **naturality of the duality maps in the coefficients**,
  `f_* (αᵢ x b) = αᵢ x ((f ∘ -)_* b)` for a `G`-map `f : N →+[G] N'`.
* `TauCeti.ContCohomology.dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero`,
  `dualityMap1_bijective_of_injective_of_forall_nsmul_eq_zero` and
  `dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero`: on a module killed by `n`,
  bijectivity of each duality map transports along an injection of coefficients `N →+[G] N'` whose
  range is the `n`-torsion, on the modules and on `H²`.
* `TauCeti.ContCohomology.dualityMap2_zmod_bijective` and
  `dualityMap0_zmod_bijective_of_finrank_eq_one`: bijectivity of `α₂` and of `α₀` for a trivial
  action on `ZMod n`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1: Tate's duality argument, in which the evaluation pairings are
  compared along the long exact sequences of a finite module and of its dual.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.2), (1.4.3)
  and (1.4.5): naturality of the cup product in the coefficients and its compatibility with the
  connecting homomorphisms.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §0, the cup-product properties
  (0.1.1)-(0.1.6).
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uM' uN uN' uA uB uC

section ZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H⁰(G, InternalHom G M N) × H²(G, M)`. -/
noncomputable def explicitDualityPairing02 :
    H0 G (InternalHom G M N) →+ H2 G M →+ H2 G N :=
  explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(0,2)` evaluation pairing is the explicit `(0,2)` cup along the evaluation pairing. -/
theorem explicitDualityPairing02_def :
    explicitDualityPairing02 G M N =
      explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- On cocycles, the `(0,2)` evaluation cup evaluates the invariant homomorphism pointwise. -/
@[simp]
theorem explicitDualityPairing02_mk (a : H0 G (InternalHom G M N)) (b : Z2 G M) :
    explicitDualityPairing02 G M N a (b : H2 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G (a : InternalHom G M N) ((b : G × G → M) q),
        cup02_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing02] using
    explicitCup02_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end ZeroTwo

section OneOneAndTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H¹(G, InternalHom G M N) × H¹(G, M)`. -/
noncomputable def explicitDualityPairing11 :
    H1 G (InternalHom G M N) →+ H1 G M →+ H2 G N :=
  explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(1,1)` evaluation pairing is the explicit `(1,1)` cup along the evaluation pairing. -/
theorem explicitDualityPairing11_def :
    explicitDualityPairing11 G M N =
      explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- Evaluation on `H²(G, InternalHom G M N) × H⁰(G, M)`. -/
noncomputable def explicitDualityPairing20 :
    H2 G (InternalHom G M N) →+ H0 G M →+ H2 G N :=
  explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(2,0)` evaluation pairing is the explicit `(2,0)` cup along the evaluation pairing. -/
theorem explicitDualityPairing20_def :
    explicitDualityPairing20 G M N =
      explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- On cocycles, the `(1,1)` evaluation cup applies the first cocycle to the translate of the
second. -/
@[simp]
theorem explicitDualityPairing11_mk (a : Z1 G (InternalHom G M N)) (b : Z1 G M) :
    explicitDualityPairing11 G M N (a : H1 G (InternalHom G M N)) (b : H1 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G → InternalHom G M N) q.1)
          (q.1 • (b : G → M) q.2),
        cup11_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing11] using
    explicitCup11_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- On cocycles, the `(2,0)` evaluation cup evaluates at an invariant element of `M`. -/
@[simp]
theorem explicitDualityPairing20_mk (a : Z2 G (InternalHom G M N)) (b : H0 G M) :
    explicitDualityPairing20 G M N (a : H2 G (InternalHom G M N)) b =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G × G → InternalHom G M N) q)
          ((q.1 * q.2) • (b : M)),
        cup20_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing20] using
    explicitCup20_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end OneOneAndTwoZero

/-! ### Naturality in the module

For a `G`-map `f : M →+[G] M'` the dual map is precomposition,
`f^* = InternalHom.precomp G f : InternalHom G M' N →+[G] InternalHom G M N`, and the evaluation
pairings of `M` and of `M'` are intertwined by `(f^* φ) m = φ (f m)`. On cohomology this is the
adjunction `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩`, one identity for each of the three shapes `(0, 2)`, `(1, 1)`
and `(2, 0)`. Each follows from the naturality of the cup product in the pairing, applied twice:
once from the mixed pairing `(φ, m) ↦ φ (f m)` of `InternalHom G M' N` with `M` to the evaluation
pairing of `M'`, along `(id, f)`, and once from the mixed pairing to the evaluation pairing of `M`,
along `(f^*, id)`. -/

section NaturalityInModule

-- The identities below are deliberately not `simp` lemmas: neither side is a normal form, as each
-- moves the coefficient map from one factor of the pairing to the other.

variable {G : Type uG} [Group G] {M : Type uM} [AddCommGroup M] [DistribMulAction G M]
  {M' : Type uM'} [AddCommGroup M'] [DistribMulAction G M']
  {N : Type uN} [AddCommGroup N] [DistribMulAction G N] (f : M →+[G] M')

/-- The mixed pairing `(φ, m) ↦ φ (f m)` of `InternalHom G M' N` with `M`, through which the
evaluation pairings of `M` and of `M'` are compared. -/
private def evalPairingComp : InternalHom G M' N →+ M →+ N :=
  (InternalHom.evalPairing G).comp (InternalHom.precomp G f (N := N)).toAddMonoidHom

private theorem evalPairingComp_apply (φ : InternalHom G M' N) (m : M) :
    evalPairingComp f φ m = InternalHom.evalPairing G φ (f m) :=
  InternalHom.evalPairing_precomp f φ m

private theorem evalPairingComp_eq_evalPairing_precomp (φ : InternalHom G M' N) (m : M) :
    evalPairingComp f φ m = InternalHom.evalPairing G (InternalHom.precomp G f φ) m :=
  (evalPairingComp_apply f φ m).trans (InternalHom.evalPairing_precomp f φ m).symm

private theorem evalPairingComp_equivariant (g : G) (φ : InternalHom G M' N) (m : M) :
    evalPairingComp f (g • φ) (g • m) = g • evalPairingComp f φ m := by
  rw [evalPairingComp_apply, evalPairingComp_apply, map_smul f,
    InternalHom.evalPairing_equivariant]

variable [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- **Naturality of the `(0,2)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`,
an invariant `φ` of `InternalHom G M' N` and a class `b ∈ H²(G, M)`, pairing `φ` with `f_* b`
is pairing the precomposed invariant `f^* φ` with `b`. -/
theorem explicitDualityPairing02_explicitCoeff2 (φ : H0 G (InternalHom G M' N)) (b : H2 G M) :
    explicitDualityPairing02 G M' N φ (explicitCoeff2 G M f continuous_of_discreteTopology b) =
      explicitDualityPairing02 G M N
        (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f) φ) b := by
  have h₁ := explicitCoeff2_explicitCup02 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_of_discreteTopology continuous_id
    (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup02 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_id continuous_id
    (evalPairingComp_eq_evalPairing_precomp f) φ b
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing02
  exact h₁.symm.trans h₂

end NaturalityInModule

section NaturalityInModuleFinite

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M'] [Finite M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (f : M →+[G] M')

/-- **Naturality of the `(1,1)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`
and classes `φ ∈ H¹(G, InternalHom G M' N)` and `b ∈ H¹(G, M)`, pairing `φ` with `f_* b` is
pairing the precomposed class `f^* φ` with `b`. -/
theorem explicitDualityPairing11_explicitCoeff1 (φ : H1 G (InternalHom G M' N)) (b : H1 G M) :
    explicitDualityPairing11 G M' N φ (explicitCoeff1 G M f continuous_of_discreteTopology b) =
      explicitDualityPairing11 G M N
        (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
          continuous_of_discreteTopology φ) b := by
  have h₁ := explicitCoeff2_explicitCup11 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_id continuous_of_discreteTopology continuous_id
    (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup11 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id continuous_id (evalPairingComp_eq_evalPairing_precomp f) φ b
  simp only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing11
  exact h₁.symm.trans h₂

/-- **Naturality of the `(2,0)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`,
a class `φ ∈ H²(G, InternalHom G M' N)` and an invariant `b` of `M`, pairing `φ` with `f b` is
pairing the precomposed class `f^* φ` with `b`. -/
theorem explicitDualityPairing20_explicitCoeff0 (φ : H2 G (InternalHom G M' N)) (b : H0 G M) :
    explicitDualityPairing20 G M' N φ (explicitCoeff0 G M f b) =
      explicitDualityPairing20 G M N
        (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
          continuous_of_discreteTopology φ) b := by
  have h₁ := explicitCoeff2_explicitCup20 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_id continuous_id (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup20 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id (evalPairingComp_eq_evalPairing_precomp f) φ b
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing20
  exact h₁.symm.trans h₂

end NaturalityInModuleFinite

/-! ### Compatibility with the connecting maps of a short exact sequence and of its dual

Let `0 → A → B → C → 0` be a short exact sequence of finite discrete `G`-modules and let
`0 → C' → B' → A' → 0` be its dual sequence `DiscreteShortExact.dual`, where
`X' = InternalHom G X N`; the dual sequence exists whenever homomorphisms `A →+ N` extend to
`B`, for instance when `B` is killed by a prime. The sub-object `C'` of the dual sequence pairs
with the quotient `C` of the original one, and the quotient `A'` pairs with the sub-object `A`, so
the two sequences are a compatibly paired pair in the sense of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/ConnectingMap.lean`, and the
adjointness identities there specialize to the evaluation pairings. -/

section ConnectingMaps

-- As in `Cup/ConnectingMap.lean`, these are not `simp` lemmas: the left-hand sides do not
-- determine the original sequence.
--
-- `[Finite B]` is needed even though `B` appears in neither statement: the connecting maps of the
-- dual sequence need `ContinuousSMul G (InternalHom G B N)` on its middle module, and the
-- conjugation action on an internal hom is continuous only for a finite source.

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
  {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
  (S : DiscreteShortExact G A B C)
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (hsurj : Function.Surjective (InternalHom.precomp G S.inclDistribMulActionHom (N := N)))

omit [Finite A] in
/-- **The connecting maps `δ⁰` of the dual sequence and `δ¹` of the original sequence are
anti-adjoint under the evaluation pairings.** For an invariant `x` of `A' = InternalHom G A N` and
a class `y ∈ H¹(G, C)`, the `(1,1)` pairing of `δ⁰ x ∈ H¹(G, C')` with `y` is the negative of the
`(0,2)` pairing of `x` with `δ¹ y ∈ H²(G, A)`. -/
theorem explicitDualityPairing11_explicitDelta0_dual_eq_neg_explicitDualityPairing02_explicitDelta1
    (x : H0 G (InternalHom G A N)) (y : H1 G C) :
    explicitDualityPairing11 G C N ((S.dual N hsurj).explicitDelta0 x) y =
      -explicitDualityPairing02 G A N x (S.explicitDelta1 y) :=
  explicitCup11_explicitDelta0_eq_neg_explicitCup02_explicitDelta1 (S.dual N hsurj) S
    (InternalHom.evalPairing G) (InternalHom.evalPairing G) (InternalHom.evalPairing G)
    (S.evalPairing_dual_incl N hsurj) (fun ψ a => (S.evalPairing_dual_proj N hsurj ψ a).symm)
    (InternalHom.evalPairing_equivariant (G := G)) x y

/-- **The connecting maps `δ¹` of the dual sequence and `δ⁰` of the original sequence are adjoint
under the evaluation pairings.** For a class `x ∈ H¹(G, A')`, `A' = InternalHom G A N`, and an
invariant `y` of `C`, the `(2,0)` pairing of `δ¹ x ∈ H²(G, C')` with `y` is the `(1,1)` pairing of
`x` with `δ⁰ y ∈ H¹(G, A)`; the Leibniz sign is `1` because `x` has degree one. -/
theorem explicitDualityPairing20_explicitDelta1_dual_eq_explicitDualityPairing11_explicitDelta0
    (x : H1 G (InternalHom G A N)) (y : H0 G C) :
    explicitDualityPairing20 G C N ((S.dual N hsurj).explicitDelta1 x) y =
      explicitDualityPairing11 G A N x (S.explicitDelta0 y) :=
  explicitCup20_explicitDelta1_eq_explicitCup11_explicitDelta0 (S.dual N hsurj) S
    (InternalHom.evalPairing G) (InternalHom.evalPairing G) (InternalHom.evalPairing G)
    (S.evalPairing_dual_incl N hsurj) (fun ψ a => (S.evalPairing_dual_proj N hsurj ψ a).symm)
    (InternalHom.evalPairing_equivariant (G := G)) x y

end ConnectingMaps

section DualityMap

/-! ### Tate's duality maps

The evaluation cups with the module in the first slot. -/

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **Tate's duality map in degree `0`**,
`α₀ : H⁰(G, M) → Hom(H²(G, InternalHom G M N), H²(G, N))`: the `(0,2)` cup along the opposite
evaluation pairing, `α₀ m b = ⟨m, b⟩`, the class of the cocycle `(g, h) ↦ b (g, h) m`. -/
noncomputable def dualityMap0 : H0 G M →+ H2 G (InternalHom G M N) →+ H2 G N :=
  explicitCup02 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- **Tate's duality map in degree `1`**,
`α₁ : H¹(G, M) → Hom(H¹(G, InternalHom G M N), H²(G, N))`: the `(1,1)` cup along the opposite
evaluation pairing, `α₁ a b = ⟨a, b⟩`, the class of the cocycle `(g, h) ↦ (g • b h) (a g)`. -/
noncomputable def dualityMap1 : H1 G M →+ H1 G (InternalHom G M N) →+ H2 G N :=
  explicitCup11 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- On cocycles, `α₀` evaluates the cocycle at the invariant element. -/
@[simp]
theorem dualityMap0_mk (m : H0 G M) (b : Z2 G (InternalHom G M N)) :
    dualityMap0 G M N m (b : H2 G (InternalHom G M N)) =
      ((⟨fun q : G × G =>
          (InternalHom.evalPairing G).flip (m : M) ((b : G × G → InternalHom G M N) q),
        cup02_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          m b.2⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap0] using
    explicitCup02_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) m b

/-- On cocycles, `α₁` applies the translate of the second cocycle to the first. -/
@[simp]
theorem dualityMap1_mk (a : Z1 G M) (b : Z1 G (InternalHom G M N)) :
    dualityMap1 G M N (a : H1 G M) (b : H1 G (InternalHom G M N)) =
      ((⟨fun q : G × G => (InternalHom.evalPairing G).flip ((a : G → M) q.1)
          (q.1 • (b : G → InternalHom G M N) q.2),
        cup11_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          a.2 b.2⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap1] using
    explicitCup11_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) a b

/-- `α₀` is the `(2,0)` evaluation cup with its arguments swapped: graded commutativity in
bidegree `(0,2)`, where the sign is `1` (`explicitCup02_eq_cup20_flip` along the opposite
evaluation pairing). -/
theorem dualityMap0_eq_explicitDualityPairing20 (m : H0 G M) (b : H2 G (InternalHom G M N)) :
    dualityMap0 G M N m b = explicitDualityPairing20 G M N b m :=
  explicitCup02_eq_cup20_flip G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) m b

/-- `α₁` is the negative of the `(1,1)` evaluation cup with its arguments swapped: graded
commutativity in bidegree `(1,1)`, where the sign is `-1` (`explicitCup11_eq_neg_flip` along the
opposite evaluation pairing). -/
theorem dualityMap1_eq_neg_explicitDualityPairing11 (a : H1 G M)
    (b : H1 G (InternalHom G M N)) :
    dualityMap1 G M N a b = -explicitDualityPairing11 G M N b a :=
  explicitCup11_eq_neg_flip G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) a b

end DualityMap

section DualityMapTwo

/-! In degree `2` the internal hom sits in the degree-zero slot of the cup, whose continuity is
never used, so `α₂` needs neither continuous inversion on `G` nor finiteness of `M`. -/

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **Tate's duality map in degree `2`**,
`α₂ : H²(G, M) → Hom(H⁰(G, InternalHom G M N), H²(G, N))`: the `(2,0)` cup along the opposite
evaluation pairing, `α₂ b φ = ⟨b, φ⟩`, the class of the cocycle `(g, h) ↦ φ (b (g, h))` for an
invariant `φ`. -/
noncomputable def dualityMap2 : H2 G M →+ H0 G (InternalHom G M N) →+ H2 G N :=
  explicitCup20 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- On cocycles, `α₂` applies the translate of the invariant homomorphism to the cocycle. -/
@[simp]
theorem dualityMap2_mk (b : Z2 G M) (φ : H0 G (InternalHom G M N)) :
    dualityMap2 G M N (b : H2 G M) φ =
      ((⟨fun q : G × G => (InternalHom.evalPairing G).flip ((b : G × G → M) q)
          ((q.1 * q.2) • (φ : InternalHom G M N)),
        cup20_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          b.2 φ⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap2] using
    explicitCup20_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) b φ

/-- `α₂` is the `(0,2)` evaluation cup with its arguments swapped: graded commutativity in
bidegree `(2,0)`, where the sign is `1` (`explicitCup02_eq_cup20_flip` along the evaluation
pairing, read backwards). -/
theorem dualityMap2_eq_explicitDualityPairing02 (b : H2 G M) (φ : H0 G (InternalHom G M N)) :
    dualityMap2 G M N b φ = explicitDualityPairing02 G M N φ b :=
  (explicitCup02_eq_cup20_flip G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) φ b).symm

end DualityMapTwo

/-! ### Naturality of the duality maps in the module

Through the comparison with the evaluation cups, the adjunction `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩` reads
`αᵢ (f_* x) b = αᵢ x (f^* b)` for each of the three duality maps. As for the evaluation cups, these
are not `simp` lemmas: neither side is a normal form. -/

section DualityMapNaturality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M'] [Finite M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (f : M →+[G] M')

/-- **Naturality of `α₀` in the module**: `α₀ (f_* x) b = α₀ x (f^* b)`. -/
theorem dualityMap0_explicitCoeff0 (x : H0 G M) (b : H2 G (InternalHom G M' N)) :
    dualityMap0 G M' N (explicitCoeff0 G M f x) b =
      dualityMap0 G M N x (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
        continuous_of_discreteTopology b) := by
  rw [dualityMap0_eq_explicitDualityPairing20, dualityMap0_eq_explicitDualityPairing20,
    explicitDualityPairing20_explicitCoeff0]

/-- **Naturality of `α₁` in the module**: `α₁ (f_* x) b = α₁ x (f^* b)`. -/
theorem dualityMap1_explicitCoeff1 (x : H1 G M) (b : H1 G (InternalHom G M' N)) :
    dualityMap1 G M' N (explicitCoeff1 G M f continuous_of_discreteTopology x) b =
      dualityMap1 G M N x (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
        continuous_of_discreteTopology b) := by
  rw [dualityMap1_eq_neg_explicitDualityPairing11, dualityMap1_eq_neg_explicitDualityPairing11,
    explicitDualityPairing11_explicitCoeff1]

end DualityMapNaturality

section DualityMapTwoNaturality

variable {G : Type uG} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (f : M →+[G] M')

/-- **Naturality of `α₂` in the module**: `α₂ (f_* x) b = α₂ x (f^* b)`. -/
theorem dualityMap2_explicitCoeff2 (x : H2 G M) (b : H0 G (InternalHom G M' N)) :
    dualityMap2 G M' N (explicitCoeff2 G M f continuous_of_discreteTopology x) b =
      dualityMap2 G M N x (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f) b) := by
  rw [dualityMap2_eq_explicitDualityPairing02, dualityMap2_eq_explicitDualityPairing02,
    explicitDualityPairing02_explicitCoeff2]

end DualityMapTwoNaturality

/-! ### Transport along an isomorphism of modules

A bijective equivariant homomorphism `f : M →+[G] M'` induces bijections on cohomology and, through
its dual `f^*`, on the targets of the duality maps; the naturality squares then carry bijectivity
of each duality map from `M'` to `M`. -/

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {f : M →+[G] M'} (hf : Function.Bijective f)

include hf

section ContinuousMul

variable [ContinuousMul G]

/-- **Bijectivity of `α₂` transports along an isomorphism of modules.** -/
theorem dualityMap2_bijective_of_bijective (h : Function.Bijective (dualityMap2 G M' N)) :
    Function.Bijective (dualityMap2 G M N) := by
  have hu : Function.Bijective (explicitCoeff2 G M f continuous_of_discreteTopology) :=
    explicitCoeff2_bijective G M hf
  have hw : Function.Bijective (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f)) :=
    explicitCoeff0_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hf)
  have hsq : ⇑(explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f)).compHom' ∘
      ⇑(dualityMap2 G M N) =
      ⇑(dualityMap2 G M' N) ∘ ⇑(explicitCoeff2 G M f continuous_of_discreteTopology) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap2_explicitCoeff2 f x b).symm
  refine (Function.Bijective.of_comp_iff' (AddMonoidHom.compHom'_bijective (P := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

end ContinuousMul

variable [IsTopologicalGroup G] [Finite M] [Finite M']

/-- **Bijectivity of `α₀` transports along an isomorphism of modules.** -/
theorem dualityMap0_bijective_of_bijective (h : Function.Bijective (dualityMap0 G M' N)) :
    Function.Bijective (dualityMap0 G M N) := by
  have hu : Function.Bijective (explicitCoeff0 G M f) := explicitCoeff0_bijective G M hf
  have hw : Function.Bijective (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff2_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hf)
  have hsq : ⇑(explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology).compHom' ∘ ⇑(dualityMap0 G M N) =
      ⇑(dualityMap0 G M' N) ∘ ⇑(explicitCoeff0 G M f) := funext fun x =>
    AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap0_explicitCoeff0 f x b).symm
  refine (Function.Bijective.of_comp_iff' (AddMonoidHom.compHom'_bijective (P := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

/-- **Bijectivity of `α₁` transports along an isomorphism of modules.** -/
theorem dualityMap1_bijective_of_bijective (h : Function.Bijective (dualityMap1 G M' N)) :
    Function.Bijective (dualityMap1 G M N) := by
  have hu : Function.Bijective (explicitCoeff1 G M f continuous_of_discreteTopology) :=
    explicitCoeff1_bijective G M hf
  have hw : Function.Bijective (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff1_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hf)
  have hsq : ⇑(explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology).compHom' ∘ ⇑(dualityMap1 G M N) =
      ⇑(dualityMap1 G M' N) ∘ ⇑(explicitCoeff1 G M f continuous_of_discreteTopology) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap1_explicitCoeff1 f x b).symm
  refine (Function.Bijective.of_comp_iff' (AddMonoidHom.compHom'_bijective (P := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

end Transport

/-! ### Naturality of the duality maps in the coefficients

An equivariant homomorphism `f : N →+[G] N'` of coefficient modules induces `f_*` on `H²(G, -)` and,
through postcomposition `f ∘ -` on the internal hom, maps between the sources of the targets of the
duality maps, and the three duality maps are natural in the coefficients:
`f_* (αᵢ x b) = αᵢ x ((f ∘ -)_* b)`. When `f` is injective with range the `n`-torsion of `N'`, both
on the modules and on `H²`, and `M` is killed by `n`, bijectivity of each `αᵢ` transports from `N`
to `N'`: the groups `H²⁻ⁱ(G, InternalHom G M N)` are killed by `n`, so postcomposition with `f_*`
is a bijection onto the homomorphisms into `H²(G, N')`. This is how the duality at `𝔽_p`
coefficients is read at the coefficients `ℤ/pⁱ`, on a module killed by `p`. -/

section NaturalityInCoefficients

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {N' : Type uN'} [AddCommGroup N'] [TopologicalSpace N'] [DiscreteTopology N']
    [DistribMulAction G N'] [ContinuousSMul G N']
  (f : N →+[G] N')

section DegreeTwo

variable [ContinuousMul G]

/-- **Naturality of `α₂` in the coefficients**: `f_* (α₂ x b) = α₂ x ((f ∘ -)_* b)`. -/
theorem explicitCoeff2_dualityMap2 (x : H2 G M) (b : H0 G (InternalHom G M N)) :
    explicitCoeff2 G N f continuous_of_discreteTopology (dualityMap2 G M N x b) =
      dualityMap2 G M N' x (explicitCoeff0 G (InternalHom G M N) (InternalHom.postcomp G f) b) := by
  have h := explicitCoeff2_explicitCup20 G M (InternalHom G M N) N M (InternalHom G M N') N'
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (DistribMulActionHom.id G) (InternalHom.postcomp G f) f continuous_id
    continuous_of_discreteTopology (fun m φ => (InternalHom.evalPairing_postcomp f φ m).symm) x b
  simpa only [explicitCoeff2_id, AddMonoidHom.id_apply, dualityMap2] using h

/-- **Bijectivity of `α₂` transports along an injection of coefficients onto the `n`-torsion**, on
a module `M` killed by `n`: if `f : N →+[G] N'` is injective with range the `n`-torsion of `N'`, and
`f_*` is injective on `H²` with range the `n`-torsion of `H²(G, N')`, then `α₂` at the coefficients
`N'` is bijective as soon as it is at the coefficients `N`. -/
theorem dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero {n : ℕ}
    (hM : ∀ x : M, n • x = 0) (hf : Function.Injective f)
    (hN' : ∀ y : N', n • y = 0 → ∃ x, f x = y)
    (hH : Function.Injective (explicitCoeff2 G N f continuous_of_discreteTopology))
    (hH' : ∀ y : H2 G N', n • y = 0 →
      ∃ x, explicitCoeff2 G N f continuous_of_discreteTopology x = y)
    (h : Function.Bijective (dualityMap2 G M N)) : Function.Bijective (dualityMap2 G M N') := by
  have hw : Function.Bijective (explicitCoeff0 G (InternalHom G M N) (InternalHom.postcomp G f)) :=
    explicitCoeff0_bijective G (InternalHom G M N)
      (InternalHom.postcomp_bijective_of_forall_nsmul_eq_zero hf hM hN')
  have hΨ : Function.Bijective (AddMonoidHom.compHom
      (explicitCoeff2 G N f continuous_of_discreteTopology) :
        (H0 G (InternalHom G M N) →+ H2 G N) →+ H0 G (InternalHom G M N) →+ H2 G N') :=
    AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero hH
      (fun v => Subtype.ext (by simpa using InternalHom.nsmul_eq_zero_of_domain hM v.1)) hH'
  have hsq : ⇑(AddMonoidHom.compHom' (explicitCoeff0 G (InternalHom G M N)
      (InternalHom.postcomp G f))) ∘ ⇑(dualityMap2 G M N') =
      ⇑(AddMonoidHom.compHom (explicitCoeff2 G N f continuous_of_discreteTopology)) ∘
        ⇑(dualityMap2 G M N) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply,
        AddMonoidHom.compHom_apply_apply, AddMonoidHom.comp_apply]
      exact (explicitCoeff2_dualityMap2 f x b).symm
  refine (Function.Bijective.of_comp_iff'
    (AddMonoidHom.compHom'_bijective (P := H2 G N') hw) _).1 ?_
  rw [hsq]
  exact hΨ.comp h

end DegreeTwo

variable [IsTopologicalGroup G] [Finite M]

/-- **Naturality of `α₀` in the coefficients**: `f_* (α₀ x b) = α₀ x ((f ∘ -)_* b)`. -/
theorem explicitCoeff2_dualityMap0 (x : H0 G M) (b : H2 G (InternalHom G M N)) :
    explicitCoeff2 G N f continuous_of_discreteTopology (dualityMap0 G M N x b) =
      dualityMap0 G M N' x (explicitCoeff2 G (InternalHom G M N) (InternalHom.postcomp G f)
        continuous_of_discreteTopology b) := by
  have h := explicitCoeff2_explicitCup02 G M (InternalHom G M N) N M (InternalHom G M N') N'
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (DistribMulActionHom.id G) (InternalHom.postcomp G f) f continuous_of_discreteTopology
    continuous_of_discreteTopology (fun m φ => (InternalHom.evalPairing_postcomp f φ m).symm) x b
  simpa only [explicitCoeff0_id, AddMonoidHom.id_apply, dualityMap0] using h

/-- **Naturality of `α₁` in the coefficients**: `f_* (α₁ x b) = α₁ x ((f ∘ -)_* b)`. -/
theorem explicitCoeff2_dualityMap1 (x : H1 G M) (b : H1 G (InternalHom G M N)) :
    explicitCoeff2 G N f continuous_of_discreteTopology (dualityMap1 G M N x b) =
      dualityMap1 G M N' x (explicitCoeff1 G (InternalHom G M N) (InternalHom.postcomp G f)
        continuous_of_discreteTopology b) := by
  have h := explicitCoeff2_explicitCup11 G M (InternalHom G M N) N M (InternalHom G M N') N'
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (InternalHom.evalPairing G).flip continuous_of_discreteTopology
    (InternalHom.evalPairing_flip_equivariant (G := G))
    (DistribMulActionHom.id G) (InternalHom.postcomp G f) f continuous_id
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun m φ => (InternalHom.evalPairing_postcomp f φ m).symm) x b
  simpa only [explicitCoeff1_id, AddMonoidHom.id_apply, dualityMap1] using h

/-- **Bijectivity of `α₀` transports along an injection of coefficients onto the `n`-torsion**, on
a finite module `M` killed by `n`; the hypotheses are those of
`dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero`. -/
theorem dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero {n : ℕ}
    (hM : ∀ x : M, n • x = 0) (hf : Function.Injective f)
    (hN' : ∀ y : N', n • y = 0 → ∃ x, f x = y)
    (hH : Function.Injective (explicitCoeff2 G N f continuous_of_discreteTopology))
    (hH' : ∀ y : H2 G N', n • y = 0 →
      ∃ x, explicitCoeff2 G N f continuous_of_discreteTopology x = y)
    (h : Function.Bijective (dualityMap0 G M N)) : Function.Bijective (dualityMap0 G M N') := by
  have hw : Function.Bijective (explicitCoeff2 G (InternalHom G M N) (InternalHom.postcomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff2_bijective G (InternalHom G M N)
      (InternalHom.postcomp_bijective_of_forall_nsmul_eq_zero hf hM hN')
  have hΨ : Function.Bijective (AddMonoidHom.compHom
      (explicitCoeff2 G N f continuous_of_discreteTopology) :
        (H2 G (InternalHom G M N) →+ H2 G N) →+ H2 G (InternalHom G M N) →+ H2 G N') :=
    AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero hH
      (nsmul_H2_eq_zero (InternalHom.nsmul_eq_zero_of_domain hM)) hH'
  have hsq : ⇑(AddMonoidHom.compHom' (explicitCoeff2 G (InternalHom G M N)
      (InternalHom.postcomp G f) continuous_of_discreteTopology)) ∘ ⇑(dualityMap0 G M N') =
      ⇑(AddMonoidHom.compHom (explicitCoeff2 G N f continuous_of_discreteTopology)) ∘
        ⇑(dualityMap0 G M N) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply,
        AddMonoidHom.compHom_apply_apply, AddMonoidHom.comp_apply]
      exact (explicitCoeff2_dualityMap0 f x b).symm
  refine (Function.Bijective.of_comp_iff'
    (AddMonoidHom.compHom'_bijective (P := H2 G N') hw) _).1 ?_
  rw [hsq]
  exact hΨ.comp h

/-- **Bijectivity of `α₁` transports along an injection of coefficients onto the `n`-torsion**, on
a finite module `M` killed by `n`; the hypotheses are those of
`dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero`. -/
theorem dualityMap1_bijective_of_injective_of_forall_nsmul_eq_zero {n : ℕ}
    (hM : ∀ x : M, n • x = 0) (hf : Function.Injective f)
    (hN' : ∀ y : N', n • y = 0 → ∃ x, f x = y)
    (hH : Function.Injective (explicitCoeff2 G N f continuous_of_discreteTopology))
    (hH' : ∀ y : H2 G N', n • y = 0 →
      ∃ x, explicitCoeff2 G N f continuous_of_discreteTopology x = y)
    (h : Function.Bijective (dualityMap1 G M N)) : Function.Bijective (dualityMap1 G M N') := by
  have hw : Function.Bijective (explicitCoeff1 G (InternalHom G M N) (InternalHom.postcomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff1_bijective G (InternalHom G M N)
      (InternalHom.postcomp_bijective_of_forall_nsmul_eq_zero hf hM hN')
  have hΨ : Function.Bijective (AddMonoidHom.compHom
      (explicitCoeff2 G N f continuous_of_discreteTopology) :
        (H1 G (InternalHom G M N) →+ H2 G N) →+ H1 G (InternalHom G M N) →+ H2 G N') :=
    AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero hH
      (nsmul_H1_eq_zero (InternalHom.nsmul_eq_zero_of_domain hM)) hH'
  have hsq : ⇑(AddMonoidHom.compHom' (explicitCoeff1 G (InternalHom G M N)
      (InternalHom.postcomp G f) continuous_of_discreteTopology)) ∘ ⇑(dualityMap1 G M N') =
      ⇑(AddMonoidHom.compHom (explicitCoeff2 G N f continuous_of_discreteTopology)) ∘
        ⇑(dualityMap1 G M N) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply,
        AddMonoidHom.compHom_apply_apply, AddMonoidHom.comp_apply]
      exact (explicitCoeff2_dualityMap1 f x b).symm
  refine (Function.Bijective.of_comp_iff'
    (AddMonoidHom.compHom'_bijective (P := H2 G N') hw) _).1 ?_
  rw [hsq]
  exact hΨ.comp h

end NaturalityInCoefficients

section TrivialZMod

/-! ### Trivial `ZMod n` coefficients

For a trivial action of `G` on `ZMod n` the conjugation action on the internal hom
`InternalHom G (ZMod n) (ZMod n)` is trivial too
(`TauCeti.InternalHom.smul_eq_self_of_smul_eq_self`), and evaluation at `1` identifies the internal
hom with `ZMod n` as `G`-modules (`TauCeti.InternalHom.zmodEquiv_smul`). Under that identification
`α₀` and `α₂` are scalar multiplication on `H²(G, ZMod n)`, and `α₁` is the cup product of
multiplication in `ZMod n`. -/

-- Preferring the ring path keeps a single additive structure on `ZMod n`, so that the module
-- structure of `H²(G, ZMod n)` below is the one its consumers see.
attribute [local instance 2000] Ring.toAddCommGroup

variable {n : ℕ} {G : Type uG} [Group G] [DistribMulAction G (ZMod n)]
  (htriv : ∀ (g : G) (m : ZMod n), g • m = m)

include htriv

variable [NeZero n] [TopologicalSpace G] [ContinuousSMul G (ZMod n)]

section ContinuousMul

/-! The two statements about `α₂` need only continuous multiplication on `G`. -/

variable [ContinuousMul G]

/-- **`α₂` at trivial `ZMod n` coefficients is scalar multiplication**: `α₂ b φ = φ 1 • b`. -/
theorem dualityMap2_zmod (b : H2 G (ZMod n)) (φ : H0 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap2 G (ZMod n) (ZMod n) b φ =
      InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n)) • b := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [dualityMap2_mk, zmod_smul_mk]
    refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
      (Subtype.ext (funext fun q => ?_))
    dsimp only
    rw [InternalHom.smul_eq_self_of_smul_eq_self htriv htriv, AddMonoidHom.flip_apply,
      InternalHom.evalPairing_apply, InternalHom.toAddMonoidHom_apply_eq_smul]
    simp [nsmul_eq_mul, mul_comm]

/-- **`α₂` at trivial `ZMod n` coefficients is bijective**, for every group `G` with continuous
multiplication acting trivially on `ZMod n`: under evaluation at `1` it sends `b` to `c ↦ c • b`,
and a homomorphism out of `ZMod n` into a group killed by `n` is determined by its value at `1`. -/
theorem dualityMap2_zmod_bijective : Function.Bijective (dualityMap2 G (ZMod n) (ZMod n)) := by
  -- the identity of `ZMod n` is an invariant element of the internal hom, with value `1` at `1`
  have hid : InternalHom.of G (AddMonoidHom.id (ZMod n)) ∈
      H0 G (InternalHom G (ZMod n) (ZMod n)) :=
    (FixedPoints.mem_addSubgroup _ _ _).2 fun g =>
      InternalHom.smul_eq_self_of_smul_eq_self htriv htriv g _
  constructor
  · intro b b' h
    have := congrArg
      (fun f : H0 G (InternalHom G (ZMod n) (ZMod n)) →+ H2 G (ZMod n) => f ⟨_, hid⟩) h
    simpa [dualityMap2_zmod htriv] using this
  · intro f
    refine ⟨f ⟨_, hid⟩, AddMonoidHom.ext fun φ => ?_⟩
    -- an invariant homomorphism `φ` is `φ 1` times the identity
    have hφ : φ = (InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n))).val •
        (⟨_, hid⟩ : H0 G (InternalHom G (ZMod n) (ZMod n))) := by
      ext x
      rw [InternalHom.toAddMonoidHom_apply_eq_smul]
      simp [nsmul_eq_mul, mul_comm]
    have hf : f φ = (InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n))).val •
        f ⟨_, hid⟩ := by
      rw [← map_nsmul, ← hφ]
    rw [dualityMap2_zmod htriv, hf, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]

end ContinuousMul

variable [IsTopologicalGroup G]

/-- For a trivial action on `ZMod n`, the first cohomology of `InternalHom G (ZMod n) (ZMod n)` is
that of `ZMod n`, along evaluation at `1`. -/
noncomputable def H1InternalHomZModEquiv :
    H1 G (InternalHom G (ZMod n) (ZMod n)) ≃+ H1 G (ZMod n) :=
  explicitCoeff1Equiv G (InternalHom G (ZMod n) (ZMod n)) (InternalHom.zmodEquiv G)
    continuous_of_discreteTopology continuous_of_discreteTopology (InternalHom.zmodEquiv_smul htriv)

/-- For a trivial action on `ZMod n`, the second cohomology of `InternalHom G (ZMod n) (ZMod n)` is
that of `ZMod n`, along evaluation at `1`. -/
noncomputable def H2InternalHomZModEquiv :
    H2 G (InternalHom G (ZMod n) (ZMod n)) ≃+ H2 G (ZMod n) :=
  explicitMap2Equiv G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMulEquiv.refl G)
    (InternalHom.zmodEquiv G) continuous_of_discreteTopology continuous_of_discreteTopology
    (InternalHom.zmodEquiv_smul htriv)

/-- On cocycle classes, `H1InternalHomZModEquiv` evaluates the cocycle at `1` pointwise: it is the
cocycle pushforward along `TauCeti.InternalHom.zmodEquiv`, whose values are given by
`cocyclesMap1_apply`. -/
theorem H1InternalHomZModEquiv_mk (c : Z1 G (InternalHom G (ZMod n) (ZMod n))) :
    H1InternalHomZModEquiv htriv (c : H1 G (InternalHom G (ZMod n) (ZMod n))) =
      (cocyclesMap1 G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMonoidHom.id G)
        (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
        continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c :
          H1 G (ZMod n)) := by
  rw [H1InternalHomZModEquiv, explicitCoeff1Equiv_mk]
  rfl

/-- On cocycle classes, `H2InternalHomZModEquiv` evaluates the cocycle at `1` pointwise: it is the
cocycle pushforward along `TauCeti.InternalHom.zmodEquiv`, whose values are given by
`cocyclesMap2_apply`. -/
theorem H2InternalHomZModEquiv_mk (c : Z2 G (InternalHom G (ZMod n) (ZMod n))) :
    H2InternalHomZModEquiv htriv (c : H2 G (InternalHom G (ZMod n) (ZMod n))) =
      (cocyclesMap2 G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMonoidHom.id G)
        (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
        continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c :
          H2 G (ZMod n)) := by
  rw [H2InternalHomZModEquiv]
  -- `explicitMap2Equiv` is sealed, so its `_apply` lemma is used as a term rather than rewritten
  refine ((explicitMap2Equiv_apply G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n)
    (ContinuousMulEquiv.refl G) (InternalHom.zmodEquiv G) continuous_of_discreteTopology
    continuous_of_discreteTopology (InternalHom.zmodEquiv_smul htriv) c).trans
    (explicitMap2_mk G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMulEquiv.refl G)
      (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
      continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c)).trans ?_
  rfl

/-- **`α₀` at trivial `ZMod n` coefficients is scalar multiplication**: `α₀ m b = m • b`, reading
`b` in `H²(G, ZMod n)` through evaluation at `1`. -/
theorem dualityMap0_zmod (m : H0 G (ZMod n)) (b : H2 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap0 G (ZMod n) (ZMod n) m b = (m : ZMod n) • H2InternalHomZModEquiv htriv b := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [dualityMap0_mk, H2InternalHomZModEquiv_mk, zmod_smul_mk]
    refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
      (Subtype.ext (funext fun q => ?_))
    obtain ⟨g, h⟩ := q
    dsimp only
    rw [AddMonoidHom.flip_apply, InternalHom.evalPairing_apply,
      InternalHom.toAddMonoidHom_apply_eq_smul]
    simp [nsmul_eq_mul]

/-- **`α₁` at trivial `ZMod n` coefficients is the cup product of multiplication**:
`α₁ a b = a ⌣ b`, reading `b` in `H¹(G, ZMod n)` through evaluation at `1`. -/
theorem dualityMap1_zmod (a : H1 G (ZMod n)) (b : H1 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap1 G (ZMod n) (ZMod n) a b =
      explicitCup11 G (ZMod n) (ZMod n) (ZMod n) AddMonoidHom.mul continuous_mul
        (smul_mul_smul_of_smul_eq_self htriv) a (H1InternalHomZModEquiv htriv b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      rw [dualityMap1_mk, H1InternalHomZModEquiv_mk]
      -- `explicitCup11_mk` is applied as a term: the continuity of multiplication is stated at
      -- `fun p => p.1 * p.2`, which `rw` does not identify with the pairing `AddMonoidHom.mul`
      refine Eq.trans ?_ (explicitCup11_mk G (ZMod n) (ZMod n) (ZMod n) AddMonoidHom.mul
        continuous_mul (smul_mul_smul_of_smul_eq_self htriv) x _).symm
      refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
        (Subtype.ext (funext fun q => ?_))
      obtain ⟨g, h⟩ := q
      dsimp only
      rw [InternalHom.smul_eq_self_of_smul_eq_self htriv htriv, AddMonoidHom.flip_apply,
        InternalHom.evalPairing_apply, InternalHom.toAddMonoidHom_apply_eq_smul]
      simp [htriv]

/-- **`α₀` at trivial `𝔽_p` coefficients is bijective when `H²(G, 𝔽_p)` is one-dimensional**:
under evaluation at `1` it sends `c` to multiplication by `c`, and every endomorphism of a
one-dimensional space is a scalar. -/
theorem dualityMap0_zmod_bijective_of_finrank_eq_one [Fact n.Prime]
    (hrank : Module.finrank (ZMod n) (H2 G (ZMod n)) = 1) :
    Function.Bijective (dualityMap0 G (ZMod n) (ZMod n)) := by
  have : Nontrivial (H2 G (ZMod n)) :=
    Module.nontrivial_of_finrank_pos (R := ZMod n) (hrank ▸ Nat.one_pos)
  constructor
  · intro m m' h
    obtain ⟨w, hw⟩ := exists_ne (0 : H2 G (ZMod n))
    have := congrArg (fun f : H2 G (InternalHom G (ZMod n) (ZMod n)) →+ H2 G (ZMod n) =>
      f ((H2InternalHomZModEquiv htriv).symm w)) h
    simp only [dualityMap0_zmod htriv, AddEquiv.apply_symm_apply] at this
    exact Subtype.ext (smul_left_injective (ZMod n) hw this)
  · intro f
    obtain ⟨c, hc⟩ := ((f.comp (H2InternalHomZModEquiv htriv).symm.toAddMonoidHom).toZModLinearMap
      n).existsUnique_eq_smul_id_of_finrank_eq_one hrank |>.exists
    refine ⟨⟨c, (FixedPoints.mem_addSubgroup _ _ _).2 fun g => htriv g c⟩,
      AddMonoidHom.ext fun b => ?_⟩
    rw [dualityMap0_zmod htriv]
    have := LinearMap.congr_fun hc (H2InternalHomZModEquiv htriv b)
    simpa using this.symm

end TrivialZMod

end TauCeti.ContCohomology
