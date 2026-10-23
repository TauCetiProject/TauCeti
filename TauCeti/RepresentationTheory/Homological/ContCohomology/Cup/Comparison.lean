/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product

/-!
# The canonical cup product agrees with the explicit low-degree cup products

Let `G` be a topological group, let `M`, `N` and `P` be discrete `G`-modules, and let
`μ : M →+ N →+ P` be an equivariant biadditive map. In each bidegree `(m, n)` with `m + n ≤ 2` two
cup products `Hᵐ(G, M) × Hⁿ(G, N) → Hᵐ⁺ⁿ(G, P)` are available: the explicit one on inhomogeneous
cocycles, `TauCeti.ContCohomology.explicitCup00`, …, `explicitCup20`, given by cochain formulas
such as `(a ⌣ b) (g, h) = μ (a g) (g • b h)` in bidegree `(1, 1)`, and the canonical one on
Mathlib's continuous cohomology, `TauCeti.TopPairing.cup` at the coefficient pairing
`TauCeti.ofDiscreteModulePairing μ`, built from the Alexander–Whitney product of homogeneous
cochains. This file proves that they agree under the comparison isomorphisms
`TauCeti.ContCohomology.explicitH0IsoContinuousCohomology`,
`TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` and
`TauCeti.ContCohomology.explicitH2IsoContinuousCohomology` between the explicit and the canonical
cohomology, one theorem per bidegree.

Each agreement holds already on cocycles. The homogeneous form of an inhomogeneous one-cocycle `a`
is `(g₀, g₁) ↦ g₀ • a (g₀⁻¹ g₁)`, that of a two-cocycle is
`(g₀, g₁, g₂) ↦ g₀ • a (g₀⁻¹ g₁, g₁⁻¹ g₂)`, and an invariant element `m` becomes the `0`-cocycle
`g ↦ g • m` (`TauCeti.ContCohomology.cocycle0`). The Alexander–Whitney product of homogeneous
cochains is `μ (A (g₀, …, g_m)) (B (g_m, …, g_{m+n}))`, and equivariance of `μ` turns it into the
homogeneous form of the explicit cochain formula. Passing to classes is then the compatibility of
the comparisons with the class maps on both sides.

In bidegree `(0, 0)` the class-level agreement is stated once, under the degree-zero comparison
isomorphism `explicitH0IsoContinuousCohomology`, which exists for every topological group. In the
other five bidegrees it is stated twice. The additive comparisons
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` and
`TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology` exist for every topological group,
resp. every locally compact one, and the agreement under them carries exactly these hypotheses.
The degree-one and degree-two comparison isomorphisms in `TopModuleCat ℤ` assume `G` compact,
which makes the canonical cohomology discrete; the agreement under them is a corollary.

This is what lets a consumer compute the canonical cup product of low-degree classes on explicit
cocycles, for instance the cup square `H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)` against which the
Demushkin condition on a pro-`p` group is stated.

## Main results

* `TauCeti.ContCohomology.cocycle0_cup00`, `TauCeti.ContCohomology.cocycleEquiv1_cup01`,
  `TauCeti.ContCohomology.cocycleEquiv1_cup10`, `TauCeti.ContCohomology.cocycleEquiv2_cup02`,
  `TauCeti.ContCohomology.cocycleEquiv2_cup11`, `TauCeti.ContCohomology.cocycleEquiv2_cup20`: on
  cocycles, the homogeneous form of each explicit cup product is the Alexander–Whitney product of
  the homogeneous forms.
* `TauCeti.ContCohomology.explicitAddEquiv_cup01`, `TauCeti.ContCohomology.explicitAddEquiv_cup10`,
  `TauCeti.ContCohomology.explicitAddEquiv_cup02`, `TauCeti.ContCohomology.explicitAddEquiv_cup11`,
  `TauCeti.ContCohomology.explicitAddEquiv_cup20`: the canonical and the explicit cup products
  agree under the additive comparisons, for every topological group in total degree one and every
  locally compact one in total degree two.
* `TauCeti.ContCohomology.explicitIso_cup00`, `TauCeti.ContCohomology.explicitIso_cup01`,
  `TauCeti.ContCohomology.explicitIso_cup10`, `TauCeti.ContCohomology.explicitIso_cup02`,
  `TauCeti.ContCohomology.explicitIso_cup`, `TauCeti.ContCohomology.explicitIso_cup20`: **the
  canonical and the explicit cup products agree** under the comparison isomorphisms, in each
  bidegree `(m, n)` with `m + n ≤ 2`; `explicitIso_cup` is the bidegree `(1, 1)`. Only the
  bidegree `(0, 0)` holds for every topological group; the other five assume `G` compact.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the
  Alexander–Whitney formula and its inhomogeneous form.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, for the inhomogeneous cup product formulas.
-/

public section

namespace TauCeti.ContCohomology

open CategoryTheory TopRep _root_.ContinuousCohomology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type u) [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hequiv : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-! ### Agreement on cocycles -/

/-- **On cocycles, the explicit `(0,0)` cup product is the Alexander–Whitney product.** -/
theorem cocycle0_cup00 (m : H0 G M) (n : H0 G N) :
    cocycle0 G P (explicitCup00 G M N P μ hequiv m n) =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 0 0 (cocycle0 G M m) (cocycle0 G N n) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (0 + 0)
  rw [TopPairing.iCycles_cupCocycles, iCycles_cocycle0, iCycles_cocycle0, iCycles_cocycle0]
  apply Subtype.ext
  ext g
  -- both sides evaluated at `g` are `μ (g • m) (g • n)`
  rw [cochainEquiv0_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_zero_zero_apply, cochainEquiv0_apply, cochainEquiv0_apply,
    ofDiscreteModulePairing_bil_apply, coe_explicitCup00, hequiv]

/-- **On cocycles, the explicit `(0,1)` cup product is the Alexander–Whitney product.** -/
theorem cocycleEquiv1_cup01 (m : H0 G M) (b : Z1 G N) :
    cocycleEquiv1 G P ⟨fun g => μ (m : M) ((b : G → N) g),
        cup01_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv m b.2⟩ =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 0 1
        (cocycle0 G M m) (cocycleEquiv1 G N b) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (0 + 1)
  -- Read the short-complex inclusions as the inclusions of the homogeneous complexes.
  have e₁ : (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles (0 + 1)
      (cocycleEquiv1 G P ⟨fun g => μ (m : M) ((b : G → N) g),
        cup01_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv m b.2⟩) =
      cochainEquiv1 G P ⟨_, Z1_le_C1 G P
        (cup01_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv m b.2)⟩ :=
    iCycles_cocycleEquiv1 G P _
  have e₁' : (homogeneousCochains (ofDiscreteModule ℤ G N)).iCycles 1 (cocycleEquiv1 G N b) =
      cochainEquiv1 G N ⟨b.val, Z1_le_C1 G N b.property⟩ := iCycles_cocycleEquiv1 G N b
  rw [e₁, TopPairing.iCycles_cupCocycles, iCycles_cocycle0, e₁']
  apply Subtype.ext
  ext g₀ g₁
  -- both sides evaluated at `(g₀, g₁)` are `μ (g₀ • m) (g₀ • b (g₀⁻¹g₁))`
  rw [cochainEquiv1_apply, homogeneous1_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_zero_one_apply, cochainEquiv0_apply, cochainEquiv1_apply,
    homogeneous1_apply, ofDiscreteModulePairing_bil_apply, ← hequiv]

/-- **On cocycles, the explicit `(1,0)` cup product is the Alexander–Whitney product.** -/
theorem cocycleEquiv1_cup10 (a : Z1 G M) (n : H0 G N) :
    cocycleEquiv1 G P ⟨fun g => μ ((a : G → M) g) (g • (n : N)),
        cup10_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv a.2 n⟩ =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 1 0
        (cocycleEquiv1 G M a) (cocycle0 G N n) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (1 + 0)
  -- Read the short-complex inclusions as the inclusions of the homogeneous complexes.
  have e₁ : (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles (1 + 0)
      (cocycleEquiv1 G P ⟨fun g => μ ((a : G → M) g) (g • (n : N)),
        cup10_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv a.2 n⟩) =
      cochainEquiv1 G P ⟨_, Z1_le_C1 G P
        (cup10_mem_Z1 G M N P μ continuous_of_discreteTopology hequiv a.2 n)⟩ :=
    iCycles_cocycleEquiv1 G P _
  have e₁' : (homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 1 (cocycleEquiv1 G M a) =
      cochainEquiv1 G M ⟨a.val, Z1_le_C1 G M a.property⟩ := iCycles_cocycleEquiv1 G M a
  rw [e₁, TopPairing.iCycles_cupCocycles, e₁', iCycles_cocycle0]
  apply Subtype.ext
  ext g₀ g₁
  -- both sides evaluated at `(g₀, g₁)` are `μ (g₀ • a (g₀⁻¹g₁)) (g₁ • n)`
  rw [cochainEquiv1_apply, homogeneous1_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_one_zero_apply, cochainEquiv1_apply, homogeneous1_apply,
    cochainEquiv0_apply, ofDiscreteModulePairing_bil_apply, ← hequiv, smul_smul,
    mul_inv_cancel_left]

section LocallyCompact

/-! The degree-two cocycle comparison `TauCeti.ContCohomology.cocycleEquiv2` uncurries, which
needs `G` locally compact; a compact group qualifies. -/

variable [LocallyCompactSpace G]

/-- **On cocycles, the explicit `(0,2)` cup product is the Alexander–Whitney product.** -/
theorem cocycleEquiv2_cup02 (m : H0 G M) (b : Z2 G N) :
    cocycleEquiv2 G P ⟨fun q : G × G => μ (m : M) ((b : G × G → N) q),
        cup02_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv m b.2⟩ =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 0 2
        (cocycle0 G M m) (cocycleEquiv2 G N b) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (0 + 2)
  -- Read the short-complex inclusions as the inclusions of the homogeneous complexes.
  have e₂ : (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles (0 + 2)
      (cocycleEquiv2 G P ⟨fun q : G × G => μ (m : M) ((b : G × G → N) q),
        cup02_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv m b.2⟩) =
      cochainEquiv2 G P ⟨_, Z2_le_C2 G P
        (cup02_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv m b.2)⟩ :=
    iCycles_cocycleEquiv2 G P _
  have e₂' : (homogeneousCochains (ofDiscreteModule ℤ G N)).iCycles 2 (cocycleEquiv2 G N b) =
      cochainEquiv2 G N ⟨b.val, Z2_le_C2 G N b.property⟩ := iCycles_cocycleEquiv2 G N b
  rw [e₂, TopPairing.iCycles_cupCocycles, iCycles_cocycle0, e₂']
  apply Subtype.ext
  ext g₀ g₁ g₂
  -- both sides evaluated at `(g₀, g₁, g₂)` are `μ (g₀ • m) (g₀ • b (g₀⁻¹g₁, g₁⁻¹g₂))`
  rw [cochainEquiv2_apply, homogeneous2_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_zero_two_apply, cochainEquiv0_apply, cochainEquiv2_apply,
    homogeneous2_apply, ofDiscreteModulePairing_bil_apply, ← hequiv]

/-- **On cocycles, the explicit `(1,1)` cup product is the Alexander–Whitney product.** The
homogeneous form of the inhomogeneous two-cocycle `(g, h) ↦ μ (a g) (g • b h)` is the cup product
of the homogeneous forms of the one-cocycles `a` and `b`, for the coefficient pairing attached to
`μ`. -/
theorem cocycleEquiv2_cup11 (a : Z1 G M) (b : Z1 G N) :
    cocycleEquiv2 G P ⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
        cup11_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 b.2⟩ =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 1 1
        (cocycleEquiv1 G M a) (cocycleEquiv1 G N b) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (1 + 1)
  -- Read the short-complex inclusions as the inclusions of the homogeneous complexes.
  have e₂ : (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles (1 + 1)
      (cocycleEquiv2 G P ⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
        cup11_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 b.2⟩) =
      cochainEquiv2 G P ⟨_, Z2_le_C2 G P
        (cup11_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 b.2)⟩ :=
    iCycles_cocycleEquiv2 G P _
  have e₁ : (homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 1 (cocycleEquiv1 G M a) =
      cochainEquiv1 G M ⟨a.val, Z1_le_C1 G M a.property⟩ := iCycles_cocycleEquiv1 G M a
  have e₁' : (homogeneousCochains (ofDiscreteModule ℤ G N)).iCycles 1 (cocycleEquiv1 G N b) =
      cochainEquiv1 G N ⟨b.val, Z1_le_C1 G N b.property⟩ := iCycles_cocycleEquiv1 G N b
  rw [e₂, TopPairing.iCycles_cupCocycles, e₁, e₁']
  apply Subtype.ext
  ext g₀ g₁ g₂
  -- both sides evaluated at `(g₀, g₁, g₂)` are `μ (g₀ • a (g₀⁻¹g₁)) (g₁ • b (g₁⁻¹g₂))`
  rw [cochainEquiv2_apply, homogeneous2_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_one_one_apply, cochainEquiv1_apply, cochainEquiv1_apply,
    homogeneous1_apply, homogeneous1_apply, ofDiscreteModulePairing_bil_apply, ← hequiv,
    smul_smul, mul_inv_cancel_left]

/-- **On cocycles, the explicit `(2,0)` cup product is the Alexander–Whitney product.** -/
theorem cocycleEquiv2_cup20 (a : Z2 G M) (n : H0 G N) :
    cocycleEquiv2 G P ⟨fun q : G × G => μ ((a : G × G → M) q) ((q.1 * q.2) • (n : N)),
        cup20_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 n⟩ =
      (ofDiscreteModulePairing μ hequiv).cupCocycles 2 0
        (cocycleEquiv2 G M a) (cocycle0 G N n) := by
  apply (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles_injective (2 + 0)
  -- Read the short-complex inclusions as the inclusions of the homogeneous complexes.
  have e₂ : (homogeneousCochains (ofDiscreteModule ℤ G P)).iCycles (2 + 0)
      (cocycleEquiv2 G P ⟨fun q : G × G => μ ((a : G × G → M) q) ((q.1 * q.2) • (n : N)),
        cup20_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 n⟩) =
      cochainEquiv2 G P ⟨_, Z2_le_C2 G P
        (cup20_mem_Z2 G M N P μ continuous_of_discreteTopology hequiv a.2 n)⟩ :=
    iCycles_cocycleEquiv2 G P _
  have e₂' : (homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2 (cocycleEquiv2 G M a) =
      cochainEquiv2 G M ⟨a.val, Z2_le_C2 G M a.property⟩ := iCycles_cocycleEquiv2 G M a
  rw [e₂, TopPairing.iCycles_cupCocycles, e₂', iCycles_cocycle0]
  apply Subtype.ext
  ext g₀ g₁ g₂
  -- both sides evaluated at `(g₀, g₁, g₂)` are `μ (g₀ • a (g₀⁻¹g₁, g₁⁻¹g₂)) (g₂ • n)`
  rw [cochainEquiv2_apply, homogeneous2_apply, TopPairing.coe_cupCochain,
    TopPairing.resolutionCupPairing_two_zero_apply, cochainEquiv2_apply, homogeneous2_apply,
    cochainEquiv0_apply, ofDiscreteModulePairing_bil_apply, ← hequiv, smul_smul, mul_assoc,
    mul_inv_cancel_left, mul_inv_cancel_left]

end LocallyCompact

/-! ### Agreement on classes, under the additive comparisons -/

/-- **The canonical and the explicit `(0,0)` cup products agree** under the degree-zero
comparison isomorphism: the cup product of two invariant elements is their pairing `μ m n`. -/
theorem explicitIso_cup00 (m : H0 G M) (n : H0 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 0 0
        ((explicitH0IsoContinuousCohomology G M).hom m)
        ((explicitH0IsoContinuousCohomology G N).hom n) =
      (explicitH0IsoContinuousCohomology G P).hom (explicitCup00 G M N P μ hequiv m n) := by
  rw [explicitH0IsoContinuousCohomology_hom_eq_π, explicitH0IsoContinuousCohomology_hom_eq_π,
    explicitH0IsoContinuousCohomology_hom_eq_π, cocycle0_cup00, TopPairing.cup_π]

/-- **The canonical and the explicit `(0,1)` cup products agree** under the additive comparisons,
for every topological group `G`: the canonical cup product `TauCeti.TopPairing.cup` in bidegree
`(0, 1)` at the coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup01`,
`(m ⌣ b) g = μ m (b g)`. -/
theorem explicitAddEquiv_cup01 (m : H0 G M) (y : H1 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 0 1
        ((explicitH0IsoContinuousCohomology G M).hom m)
        (explicitH1AddEquivContinuousCohomology G N y) =
      explicitH1AddEquivContinuousCohomology G P
        (explicitCup01 G M N P μ continuous_of_discreteTopology hequiv m y) := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    rw [explicitH0IsoContinuousCohomology_hom_eq_π, explicitH1AddEquivContinuousCohomology_apply,
      explicitCup01_mk, explicitH1AddEquivContinuousCohomology_apply, cocycleEquiv1_cup01,
      TopPairing.cup_π]

/-- **The canonical and the explicit `(1,0)` cup products agree** under the additive comparisons,
for every topological group `G`: the canonical cup product `TauCeti.TopPairing.cup` in bidegree
`(1, 0)` at the coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup10`,
`(a ⌣ n) g = μ (a g) (g • n)`. -/
theorem explicitAddEquiv_cup10 (x : H1 G M) (n : H0 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 1 0
        (explicitH1AddEquivContinuousCohomology G M x)
        ((explicitH0IsoContinuousCohomology G N).hom n) =
      explicitH1AddEquivContinuousCohomology G P
        (explicitCup10 G M N P μ continuous_of_discreteTopology hequiv x n) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    rw [explicitH0IsoContinuousCohomology_hom_eq_π, explicitH1AddEquivContinuousCohomology_apply,
      explicitCup10_mk, explicitH1AddEquivContinuousCohomology_apply, cocycleEquiv1_cup10,
      TopPairing.cup_π]

section LocallyCompact

/-! The degree-two additive comparison
`TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology` needs `G` locally compact, as does
the cocycle comparison it is built from. -/

variable [LocallyCompactSpace G]

/-- **The canonical and the explicit `(0,2)` cup products agree** under the additive comparisons,
for every locally compact group `G`: the canonical cup product `TauCeti.TopPairing.cup` in bidegree
`(0, 2)` at the coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup02`,
`(m ⌣ b) (g, h) = μ m (b (g, h))`. -/
theorem explicitAddEquiv_cup02 (m : H0 G M) (y : H2 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 0 2
        ((explicitH0IsoContinuousCohomology G M).hom m)
        (explicitH2AddEquivContinuousCohomology G N y) =
      explicitH2AddEquivContinuousCohomology G P
        (explicitCup02 G M N P μ continuous_of_discreteTopology hequiv m y) := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    rw [explicitH0IsoContinuousCohomology_hom_eq_π, explicitH2AddEquivContinuousCohomology_apply,
      explicitCup02_mk, explicitH2AddEquivContinuousCohomology_apply, cocycleEquiv2_cup02,
      TopPairing.cup_π]

/-- **The canonical and the explicit `(1,1)` cup products agree** under the additive comparisons,
for every locally compact group `G`: the canonical cup product `TauCeti.TopPairing.cup` in bidegree
`(1, 1)` at the coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup11`,
`(a ⌣ b) (g, h) = μ (a g) (g • b h)`. -/
theorem explicitAddEquiv_cup11 (x : H1 G M) (y : H1 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 1 1
        (explicitH1AddEquivContinuousCohomology G M x)
        (explicitH1AddEquivContinuousCohomology G N y) =
      explicitH2AddEquivContinuousCohomology G P
        (explicitCup11 G M N P μ continuous_of_discreteTopology hequiv x y) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      rw [explicitH1AddEquivContinuousCohomology_apply,
        explicitH1AddEquivContinuousCohomology_apply, explicitCup11_mk,
        explicitH2AddEquivContinuousCohomology_apply, cocycleEquiv2_cup11, TopPairing.cup_π]

/-- **The canonical and the explicit `(2,0)` cup products agree** under the additive comparisons,
for every locally compact group `G`: the canonical cup product `TauCeti.TopPairing.cup` in bidegree
`(2, 0)` at the coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup20`,
`(a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n)`. -/
theorem explicitAddEquiv_cup20 (x : H2 G M) (n : H0 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 2 0
        (explicitH2AddEquivContinuousCohomology G M x)
        ((explicitH0IsoContinuousCohomology G N).hom n) =
      explicitH2AddEquivContinuousCohomology G P
        (explicitCup20 G M N P μ continuous_of_discreteTopology hequiv x n) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    rw [explicitH0IsoContinuousCohomology_hom_eq_π, explicitH2AddEquivContinuousCohomology_apply,
      explicitCup20_mk, explicitH2AddEquivContinuousCohomology_apply, cocycleEquiv2_cup20,
      TopPairing.cup_π]

end LocallyCompact

/-! ### Agreement on classes, under the comparison isomorphisms -/

section Compact

/-! Compactness of `G` enters only through the comparison isomorphisms in degrees one and two,
which need the canonical cohomology to be discrete; each statement here is the one under the
additive comparisons above, read on the discrete carriers `TauCeti.ContCohomology.DiscreteH1` and
`TauCeti.ContCohomology.DiscreteH2`. -/

variable [CompactSpace G]

/-- **The canonical and the explicit `(0,1)` cup products agree** under the comparison
isomorphisms: the canonical cup product `TauCeti.TopPairing.cup` in bidegree `(0, 1)` at the
coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup01`,
`(m ⌣ b) g = μ m (b g)`. -/
theorem explicitIso_cup01 (m : H0 G M) (y : DiscreteH1 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 0 1
        ((explicitH0IsoContinuousCohomology G M).hom m)
        ((explicitH1IsoContinuousCohomology G N).hom y) =
      (explicitH1IsoContinuousCohomology G P).hom
        ((discreteH1Equiv G P).symm
          (explicitCup01 G M N P μ continuous_of_discreteTopology hequiv m
            (discreteH1Equiv G N y))) := by
  rw [explicitH1IsoContinuousCohomology_hom_apply, explicitH1IsoContinuousCohomology_hom_apply,
    AddEquiv.apply_symm_apply, explicitAddEquiv_cup01]

/-- **The canonical and the explicit `(1,0)` cup products agree** under the comparison
isomorphisms: the canonical cup product `TauCeti.TopPairing.cup` in bidegree `(1, 0)` at the
coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup10`,
`(a ⌣ n) g = μ (a g) (g • n)`. -/
theorem explicitIso_cup10 (x : DiscreteH1 G M) (n : H0 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 1 0
        ((explicitH1IsoContinuousCohomology G M).hom x)
        ((explicitH0IsoContinuousCohomology G N).hom n) =
      (explicitH1IsoContinuousCohomology G P).hom
        ((discreteH1Equiv G P).symm
          (explicitCup10 G M N P μ continuous_of_discreteTopology hequiv
            (discreteH1Equiv G M x) n)) := by
  rw [explicitH1IsoContinuousCohomology_hom_apply, explicitH1IsoContinuousCohomology_hom_apply,
    AddEquiv.apply_symm_apply, explicitAddEquiv_cup10]

/-- **The canonical and the explicit `(0,2)` cup products agree** under the comparison
isomorphisms: the canonical cup product `TauCeti.TopPairing.cup` in bidegree `(0, 2)` at the
coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup02`,
`(m ⌣ b) (g, h) = μ m (b (g, h))`. -/
theorem explicitIso_cup02 (m : H0 G M) (y : DiscreteH2 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 0 2
        ((explicitH0IsoContinuousCohomology G M).hom m)
        ((explicitH2IsoContinuousCohomology G N).hom y) =
      (explicitH2IsoContinuousCohomology G P).hom
        ((discreteH2Equiv G P).symm
          (explicitCup02 G M N P μ continuous_of_discreteTopology hequiv m
            (discreteH2Equiv G N y))) := by
  rw [explicitH2IsoContinuousCohomology_hom_apply, explicitH2IsoContinuousCohomology_hom_apply,
    AddEquiv.apply_symm_apply, explicitAddEquiv_cup02]

/-- **The canonical and the explicit `(1,1)` cup products agree.** Under the comparison
isomorphisms of `H¹` and `H²` with Mathlib's continuous cohomology, the canonical cup product
`TauCeti.TopPairing.cup` in bidegree `(1, 1)` at the coefficient pairing attached to `μ` is the
explicit cup product `TauCeti.ContCohomology.explicitCup11`, `(a ⌣ b) (g, h) = μ (a g) (g • b h)`.
-/
theorem explicitIso_cup (x : DiscreteH1 G M) (y : DiscreteH1 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 1 1
        ((explicitH1IsoContinuousCohomology G M).hom x)
        ((explicitH1IsoContinuousCohomology G N).hom y) =
      (explicitH2IsoContinuousCohomology G P).hom
        ((discreteH2Equiv G P).symm
          (explicitCup11 G M N P μ continuous_of_discreteTopology hequiv
            (discreteH1Equiv G M x) (discreteH1Equiv G N y))) := by
  rw [explicitH1IsoContinuousCohomology_hom_apply, explicitH1IsoContinuousCohomology_hom_apply,
    explicitH2IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply, explicitAddEquiv_cup11]

/-- **The canonical and the explicit `(2,0)` cup products agree** under the comparison
isomorphisms: the canonical cup product `TauCeti.TopPairing.cup` in bidegree `(2, 0)` at the
coefficient pairing attached to `μ` is `TauCeti.ContCohomology.explicitCup20`,
`(a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n)`. -/
theorem explicitIso_cup20 (x : DiscreteH2 G M) (n : H0 G N) :
    (ofDiscreteModulePairing μ hequiv).cup 2 0
        ((explicitH2IsoContinuousCohomology G M).hom x)
        ((explicitH0IsoContinuousCohomology G N).hom n) =
      (explicitH2IsoContinuousCohomology G P).hom
        ((discreteH2Equiv G P).symm
          (explicitCup20 G M N P μ continuous_of_discreteTopology hequiv
            (discreteH2Equiv G M x) n)) := by
  rw [explicitH2IsoContinuousCohomology_hom_apply, explicitH2IsoContinuousCohomology_hom_apply,
    AddEquiv.apply_symm_apply, explicitAddEquiv_cup20]

end Compact

end TauCeti.ContCohomology
