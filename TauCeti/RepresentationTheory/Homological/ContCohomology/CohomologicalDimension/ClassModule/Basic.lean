/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# The pro-p class module of an open normal subgroup

For a normal subgroup `V` of a topological group `G`, this file defines the maximal pro-`p`
quotient `V^ab(p)` of the topological abelianization of `V`. Conjugation induces a continuous
action of `G ⧸ V` on this quotient. If `V` is open, the defect

`q.out * r.out * (q * r).out⁻¹`

of the representatives chosen by `Quotient.out` defines a continuous `2`-cocycle with values in
`V^ab(p)`, and hence a canonical class `u_{G/V}(p) ∈ H²(G ⧸ V, V^ab(p))`.

The openness assumption is used only for continuity of the factor set: the quotient
`G ⧸ V` is discrete. The cocycle identity itself is the associativity identity for the chosen
representatives, after passing to the abelianization.

## Main definitions

* `TauCeti.abelianizationProP`: the maximal pro-`p` quotient `V^ab(p)`.
* `TauCeti.abelianizationProPMk`: the canonical map `V → V^ab(p)`.
* `TauCeti.abelianizationProPFactorSet`: the factor set defined by `Quotient.out`.
* `TauCeti.abelianizationProPClass`: its class in continuous `H²`.

## Main results

* `TauCeti.continuous_abelianizationProPMk`: the canonical map is continuous.
* `TauCeti.abelianizationProPMk_conj`: the canonical map is equivariant for conjugation.
* `TauCeti.abelianizationProPFactorSet_mem_Z2`: the factor set is a continuous `2`-cocycle when
  `V` is open.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Proposition (3.6.2).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The maximal pro-`p` quotient `V^ab(p)` of the topological abelianization of `V`. -/
abbrev abelianizationProP (V : Subgroup G) : Type u :=
  maximalProPQuotient p (TopologicalAbelianization V)

/-- The quotient map `V → V^ab(p)`, through the topological abelianization of `V`. -/
noncomputable def abelianizationProPMk (V : Subgroup G) : V →* abelianizationProP p G V :=
  (maximalProPQuotient.mk p (TopologicalAbelianization V)).comp
    (QuotientGroup.mk' (commutator V).topologicalClosure)

/-- Every element of `V^ab(p)` is represented by an element of `V`. -/
theorem abelianizationProPMk_surjective (V : Subgroup G) :
    Function.Surjective (abelianizationProPMk p G V) :=
  (maximalProPQuotient.mk_surjective p (TopologicalAbelianization V)).comp
    (QuotientGroup.mk'_surjective (commutator V).topologicalClosure)

/-- The quotient map `V → V^ab(p)` is continuous. -/
theorem continuous_abelianizationProPMk (V : Subgroup G) :
    Continuous (abelianizationProPMk p G V) :=
  (maximalProPQuotient.continuous_mk
    (p := p) (G := TopologicalAbelianization V)).comp QuotientGroup.continuous_mk

/-- The pro-`p` kernel of `V^ab` is stable under conjugation by `G ⧸ V`. -/
noncomputable instance abelianizationProPQuotientAction (V : Subgroup G) [V.Normal] :
    MulAction.QuotientAction (G ⧸ V) (proPKernel p (TopologicalAbelianization V)) where
  inv_mul_mem q _ _ h := by
    rw [← smul_inv', ← smul_mul']
    exact proPKernel_le_comap
      (MulDistribMulAction.toMonoidHom (TopologicalAbelianization V) q)
        (continuous_const_smul q) h

/-- Conjugation by `G ⧸ V` on `V^ab` descends to `V^ab(p)`. -/
noncomputable instance abelianizationProPAction (V : Subgroup G) [V.Normal] :
    MulDistribMulAction (G ⧸ V) (abelianizationProP p G V) :=
  Function.Surjective.mulDistribMulAction
    (maximalProPQuotient.mk p (TopologicalAbelianization V))
    (maximalProPQuotient.mk_surjective p (TopologicalAbelianization V))
    fun q x => (MulAction.Quotient.smul_mk _ q x).symm

/-- The quotient map `V → V^ab(p)` intertwines conjugation by `g : G` with the action of the
class of `g` in `G ⧸ V`. -/
@[simp]
theorem abelianizationProPMk_conj (V : Subgroup G) [V.Normal] (g : G) (v : V) :
    (g : G ⧸ V) • abelianizationProPMk p G V v =
      abelianizationProPMk p G V (MulAut.conjNormal g v) := by
  simp [abelianizationProPMk, TopologicalAbelianization.mk_smul_mk]

/-- The action of `G ⧸ V` on `V^ab(p)` is jointly continuous. -/
instance abelianizationProP_continuousSMul (V : Subgroup G) [V.Normal] :
    ContinuousSMul (G ⧸ V) (abelianizationProP p G V) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (QuotientGroup.isOpenQuotientMap_mk
        (N := proPKernel p (TopologicalAbelianization V)))).continuous_comp_iff]
    exact (QuotientGroup.continuous_mk.comp continuous_smul).congr fun x =>
      (MulAction.Quotient.smul_mk _ x.1 x.2).symm

/-- The factor set of the extension of `G ⧸ V` by `V^ab(p)`, written additively. It sends
`(q, r)` to the class of `q.out * r.out * (q * r).out⁻¹`. -/
noncomputable def abelianizationProPFactorSet (V : Subgroup G) [V.Normal] :
    (G ⧸ V) × (G ⧸ V) → Additive (abelianizationProP p G V) :=
  fun q => Additive.ofMul (abelianizationProPMk p G V
    ⟨q.1.out * q.2.out * (q.1 * q.2).out⁻¹,
      QuotientGroup.out_mul_out_mul_inv_mem V q.1 q.2⟩)

/-- The factor set evaluates to the class of the defect of the chosen representatives. -/
@[simp]
theorem abelianizationProPFactorSet_apply (V : Subgroup G) [V.Normal]
    (q r : G ⧸ V) :
    abelianizationProPFactorSet p G V (q, r) =
      Additive.ofMul (abelianizationProPMk p G V
        ⟨q.out * r.out * (q * r).out⁻¹, QuotientGroup.out_mul_out_mul_inv_mem V q r⟩) := by
  rfl

/-- For open normal `V`, the factor set is a continuous `2`-cocycle of `G ⧸ V` with values in
`V^ab(p)`. -/
theorem abelianizationProPFactorSet_mem_Z2 (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) :
    abelianizationProPFactorSet p G V ∈ Z2 (G ⧸ V) (Additive (abelianizationProP p G V)) := by
  let _ : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  rw [mem_Z2_iff]
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro q r s
  let c : (G ⧸ V) → (G ⧸ V) → V := fun a b =>
    ⟨a.out * b.out * (a * b).out⁻¹, QuotientGroup.out_mul_out_mul_inv_mem V a b⟩
  apply Additive.toMul.injective
  -- Addition in `Additive` and its canonical scalar action are definitionally multiplication
  -- and the multiplicative action. After applying `toMul`, `change` exposes those operations
  -- and the local factor `c` together, so the multiplicative homomorphism lemmas apply directly.
  change abelianizationProPMk p G V (c (q * r) s) * abelianizationProPMk p G V (c q r) =
    q • abelianizationProPMk p G V (c r s) * abelianizationProPMk p G V (c q (r * s))
  rw [mul_comm (abelianizationProPMk p G V (c (q * r) s)), ← map_mul]
  rw [← QuotientGroup.out_eq' q, abelianizationProPMk_conj, ← map_mul]
  apply congrArg (abelianizationProPMk p G V)
  apply Subtype.ext
  simp [c, MulAut.conjNormal_apply, mul_assoc]

/-- The canonical class `u_{G/V}(p) ∈ H²(G ⧸ V, V^ab(p))` of an open normal subgroup. -/
noncomputable def abelianizationProPClass (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) : H2 (G ⧸ V) (Additive (abelianizationProP p G V)) :=
  H2pi (G ⧸ V) (Additive (abelianizationProP p G V))
    ⟨abelianizationProPFactorSet p G V, abelianizationProPFactorSet_mem_Z2 p G V hV⟩

/-- The class `u_{G/V}(p)` is the image of the factor-set cocycle under the class map. -/
theorem abelianizationProPClass_def (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) :
    abelianizationProPClass p G V hV =
      H2pi (G ⧸ V) (Additive (abelianizationProP p G V))
        ⟨abelianizationProPFactorSet p G V, abelianizationProPFactorSet_mem_Z2 p G V hV⟩ := by
  rfl

end TauCeti
