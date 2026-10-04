/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# The pro-p class module of an open normal subgroup

For a normal subgroup `V` of a topological group `G`, this file defines the maximal pro-`p`
quotient `V^ab(p)` of the topological abelianization of `V`. Conjugation induces a continuous
action of `G ⧸ V` on this quotient. If `V` is open, the defect

`q.out * r.out * (q * r).out⁻¹`

of the representatives chosen by `Quotient.out` defines a continuous `2`-cocycle with values in
`V^ab(p)`, and hence a canonical class `u_{G/V}(p) ∈ H²(G ⧸ V, V^ab(p))`.

The openness assumption is used only for continuity of the factor set: the finite quotient
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
    MulDistribMulAction (G ⧸ V) (abelianizationProP p G V) where
  toMulAction := inferInstance
  smul_mul q x y := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y => rw [← QuotientGroup.mk_mul, MulAction.Quotient.smul_mk,
          MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_mul',
          QuotientGroup.mk_mul]
  smul_one q := by
    rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_one]

/-- The quotient map `V^ab → V^ab(p)` is equivariant for conjugation by `G ⧸ V`. -/
@[simp]
theorem abelianizationProP_smul_mk (V : Subgroup G) [V.Normal] (q : G ⧸ V)
    (x : TopologicalAbelianization V) :
    q • maximalProPQuotient.mk p (TopologicalAbelianization V) x =
      maximalProPQuotient.mk p (TopologicalAbelianization V) (q • x) :=
  MulAction.Quotient.smul_mk _ q x

/-- The quotient map `V → V^ab(p)` intertwines conjugation by `g : G` with the action of the
class of `g` in `G ⧸ V`. -/
@[simp]
theorem abelianizationProPMk_conj (V : Subgroup G) [V.Normal] (g : G) (v : V) :
    (g : G ⧸ V) • abelianizationProPMk p G V v =
      abelianizationProPMk p G V (MulAut.conjNormal g v) := by
  simp [abelianizationProPMk, TopologicalAbelianization.mk_smul_mk]

/-- The conjugation action on `V^ab(p)`, in the additive notation used by group cohomology. -/
noncomputable instance abelianizationProPAdditiveAction (V : Subgroup G) [V.Normal] :
    DistribMulAction (G ⧸ V) (Additive (abelianizationProP p G V)) where
  smul q x := Additive.ofMul (q • Additive.toMul x)
  one_smul x := by
    change Additive.ofMul ((1 : G ⧸ V) • Additive.toMul x) = _
    rw [one_smul]
    rfl
  mul_smul q r x := by
    change Additive.ofMul ((q * r) • Additive.toMul x) = _
    rw [mul_smul]
    rfl
  smul_zero q := by
    change Additive.ofMul (q • (1 : abelianizationProP p G V)) = _
    rw [smul_one]
    rfl
  smul_add q x y := by
    change Additive.ofMul (q • (Additive.toMul x * Additive.toMul y)) = _
    rw [smul_mul']
    rfl

/-- The action of `G ⧸ V` on `V^ab(p)` is jointly continuous. -/
instance abelianizationProP_continuousSMul (V : Subgroup G) [V.Normal] :
    ContinuousSMul (G ⧸ V) (Additive (abelianizationProP p G V)) where
  continuous_smul := by
    change Continuous fun x : (G ⧸ V) × abelianizationProP p G V => x.1 • x.2
    have hquot : IsOpenQuotientMap (Prod.map id
        (QuotientGroup.mk : TopologicalAbelianization V → abelianizationProP p G V)) :=
      (IsOpenQuotientMap.id : IsOpenQuotientMap (id : (G ⧸ V) → G ⧸ V)).prodMap
        QuotientGroup.isOpenQuotientMap_mk
    rw [← hquot.continuous_comp_iff]
    have h : (fun x : (G ⧸ V) × abelianizationProP p G V => x.1 • x.2) ∘
        Prod.map id (QuotientGroup.mk : TopologicalAbelianization V →
          abelianizationProP p G V) =
          (QuotientGroup.mk : TopologicalAbelianization V →
            abelianizationProP p G V) ∘
            fun x : (G ⧸ V) × TopologicalAbelianization V => x.1 • x.2 :=
      funext fun x => abelianizationProP_smul_mk p G V x.1 x.2
    rw [h]
    exact (maximalProPQuotient.continuous_mk
      (p := p) (G := TopologicalAbelianization V)).comp
      (ContinuousSMul.continuous_smul (M := G ⧸ V) (X := TopologicalAbelianization V))

/-- The factor set of the extension of `G ⧸ V` by `V^ab(p)`, written additively. It sends
`(q, r)` to the class of `q.out * r.out * (q * r).out⁻¹`. -/
noncomputable def abelianizationProPFactorSet (V : Subgroup G) [V.Normal] :
    (G ⧸ V) × (G ⧸ V) → Additive (abelianizationProP p G V) :=
  fun q => Additive.ofMul (abelianizationProPMk p G V
    ⟨q.1.out * q.2.out * (q.1 * q.2).out⁻¹,
      QuotientGroup.out_mul_out_mul_inv_mem V q.1 q.2⟩)

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

end TauCeti
