/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# The class module under change of group

Let `V ≤ W` be subgroups of a topological group `G`, with `V` open and normal in `G`. The pair
`V.subgroupOf W ◁ W`, computed inside the group `W`, has its own class module
`(V.subgroupOf W)^ab(p)` with the conjugation action of `W ⧸ V.subgroupOf W`, and its own class
`u_{W/V}(p)`. This file identifies these with the restriction of the data of the pair `V ◁ G` to the
subgroup `W.map (mk' V)` of `G ⧸ V`:

* the groups are identified by `TauCeti.quotientSubgroupOfEquivMap`,
  `W ⧸ V.subgroupOf W ≃ₜ* W.map (mk' V)`;
* the coefficients are identified by `TauCeti.abelianizationProPSubgroupOfEquiv`,
  `(V.subgroupOf W)^ab(p) ≃ₜ* V^ab(p)`, which intertwines the two conjugation actions
  (`TauCeti.abelianizationProPSubgroupOfEquiv_smul`);
* the compatible-pair pullbacks along this pair are additive equivalences
  `TauCeti.abelianizationProPSubgroupOfH1Equiv` and `TauCeti.abelianizationProPSubgroupOfH2Equiv`
  on explicit `H¹` and `H²`;
* the latter carries `u_{W/V}(p)` to the restriction of `u_{G/V}(p)` to `W.map (mk' V)`
  (`TauCeti.abelianizationProPSubgroupOfH2Equiv_class`).

The last statement is not a tautology: the two classes are defined by factor sets built from
different representatives, chosen by `Quotient.out` in `W ⧸ V.subgroupOf W` and in `G ⧸ V`
respectively. If `a_s = c_s * b_s` relates the two choices of representatives of `s`, with
`c_s ∈ V`, the two factor sets differ by the coboundary of `s ↦ [c_s]`.

This is how statements about the class module of a pair `V ◁ W` with `W` an open subgroup of `G`
are read off from statements about the pair `V ◁ G`, and conversely.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Proposition (3.6.1)(i).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Coefficients

variable {V W : Subgroup G} (hVW : V ≤ W)

/-- For subgroups `V ≤ W`, the maximal pro-`p` abelian quotient of `V`, computed inside `W`, is
the one computed inside `G`: the isomorphism `(V.subgroupOf W)^ab(p) ≃ₜ* V^ab(p)` induced by
`Subgroup.subgroupOfContinuousMulEquivOfLe`. -/
noncomputable def abelianizationProPSubgroupOfEquiv :
    abelianizationProP p W (V.subgroupOf W) ≃ₜ* abelianizationProP p G V :=
  let e := (Subgroup.subgroupOfContinuousMulEquivOfLe hVW).topologicalAbelianizationCongr
  e.quotientCongr _ _ (map_proPKernel_eq (p := p) e)

/-- `abelianizationProPSubgroupOfEquiv` sends the class of an element of `V.subgroupOf W` to the
class of the same element of `V`. -/
@[simp]
theorem abelianizationProPSubgroupOfEquiv_mk (w : W) (hw : w ∈ V.subgroupOf W) :
    abelianizationProPSubgroupOfEquiv p hVW (abelianizationProPMk p W (V.subgroupOf W) ⟨w, hw⟩) =
      abelianizationProPMk p G V ⟨w, hw⟩ := by
  rw [abelianizationProPMk_apply, abelianizationProPMk_apply, abelianizationProPSubgroupOfEquiv]
  exact (ContinuousMulEquiv.quotientCongr_mk _ _ _ _ _).trans
    (congrArg _ (ContinuousMulEquiv.topologicalAbelianizationCongr_mk _ _))

/-- `abelianizationProPSubgroupOfEquiv` intertwines conjugation by `w : W` on
`(V.subgroupOf W)^ab(p)` with conjugation by `w` on `V^ab(p)`. -/
theorem abelianizationProPSubgroupOfEquiv_mk_smul [V.Normal] (w : W)
    (x : abelianizationProP p W (V.subgroupOf W)) :
    abelianizationProPSubgroupOfEquiv p hVW ((w : W ⧸ V.subgroupOf W) • x) =
      ((w : G) : G ⧸ V) • abelianizationProPSubgroupOfEquiv p hVW x := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := abelianizationProPMk_surjective p W (V.subgroupOf W) x
  rw [abelianizationProPMk_conj, abelianizationProPSubgroupOfEquiv_mk,
    abelianizationProPSubgroupOfEquiv_mk, abelianizationProPMk_conj]
  exact congrArg _ (Subtype.ext (by simp [MulAut.conjNormal_apply]))

variable [V.Normal] (hV : IsOpen (V : Set G))

/-- `abelianizationProPSubgroupOfEquiv` intertwines the action of `W ⧸ V.subgroupOf W` on
`(V.subgroupOf W)^ab(p)` with the action of its image in `G ⧸ V` on `V^ab(p)`, the two quotients
being identified by `quotientSubgroupOfEquivMap`. -/
theorem abelianizationProPSubgroupOfEquiv_smul (q : W ⧸ V.subgroupOf W)
    (x : abelianizationProP p W (V.subgroupOf W)) :
    abelianizationProPSubgroupOfEquiv p hVW (q • x) =
      (quotientSubgroupOfEquivMap V W hV q : G ⧸ V) •
        abelianizationProPSubgroupOfEquiv p hVW x := by
  induction q using QuotientGroup.induction_on with
  | H w => rw [abelianizationProPSubgroupOfEquiv_mk_smul, coe_quotientSubgroupOfEquivMap_mk]

/-- On the additive coefficient modules, `abelianizationProPSubgroupOfEquiv` carries the action of
`(quotientSubgroupOfEquivMap V W hV).symm s` to the action of `s`. This is the compatibility
under which the pair of these two isomorphisms induces maps on explicit cohomology. -/
theorem abelianizationProPSubgroupOfEquiv_toAdditive_smul (s : W.map (QuotientGroup.mk' V))
    (x : Additive (abelianizationProP p W (V.subgroupOf W))) :
    (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive
        ((quotientSubgroupOfEquivMap V W hV).symm s • x) =
      s • (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive x := by
  have h := abelianizationProPSubgroupOfEquiv_smul p hVW hV
    ((quotientSubgroupOfEquivMap V W hV).symm s) x.toMul
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact congrArg Additive.ofMul h

end Coefficients

section Cohomology

variable {V W : Subgroup G} [V.Normal] (hVW : V ≤ W) (hV : IsOpen (V : Set G))

/-- The change of group on explicit `H¹`: the compatible-pair pullback along
`(quotientSubgroupOfEquivMap V W hV).symm` and `abelianizationProPSubgroupOfEquiv p hVW`, an
isomorphism `H¹(W ⧸ V.subgroupOf W, (V.subgroupOf W)^ab(p)) ≃+ H¹(W.map (mk' V), V^ab(p))`. -/
noncomputable def abelianizationProPSubgroupOfH1Equiv :
    H1 (W ⧸ V.subgroupOf W) (Additive (abelianizationProP p W (V.subgroupOf W))) ≃+
      H1 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)) :=
  explicitMap1Equiv (W ⧸ V.subgroupOf W) (Additive (abelianizationProP p W (V.subgroupOf W)))
    (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V))
    (quotientSubgroupOfEquivMap V W hV).symm
    (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive
    (by exact (abelianizationProPSubgroupOfEquiv p hVW).continuous)
    (by exact (abelianizationProPSubgroupOfEquiv p hVW).symm.continuous)
    (abelianizationProPSubgroupOfEquiv_toAdditive_smul p hVW hV)

/-- `abelianizationProPSubgroupOfH1Equiv` is `explicitMap1Equiv` along its compatible pair. -/
theorem abelianizationProPSubgroupOfH1Equiv_def :
    abelianizationProPSubgroupOfH1Equiv p hVW hV =
      explicitMap1Equiv (W ⧸ V.subgroupOf W)
        (Additive (abelianizationProP p W (V.subgroupOf W)))
        (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V))
        (quotientSubgroupOfEquivMap V W hV).symm
        (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive
        (by exact (abelianizationProPSubgroupOfEquiv p hVW).continuous)
        (by exact (abelianizationProPSubgroupOfEquiv p hVW).symm.continuous)
        (abelianizationProPSubgroupOfEquiv_toAdditive_smul p hVW hV) :=
  (rfl)

/-- The change of group on explicit `H²`: the compatible-pair pullback along
`(quotientSubgroupOfEquivMap V W hV).symm` and `abelianizationProPSubgroupOfEquiv p hVW`, an
isomorphism `H²(W ⧸ V.subgroupOf W, (V.subgroupOf W)^ab(p)) ≃+ H²(W.map (mk' V), V^ab(p))`. -/
noncomputable def abelianizationProPSubgroupOfH2Equiv :
    H2 (W ⧸ V.subgroupOf W) (Additive (abelianizationProP p W (V.subgroupOf W))) ≃+
      H2 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V)) :=
  explicitMap2Equiv (W ⧸ V.subgroupOf W) (Additive (abelianizationProP p W (V.subgroupOf W)))
    (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V))
    (quotientSubgroupOfEquivMap V W hV).symm
    (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive
    (by exact (abelianizationProPSubgroupOfEquiv p hVW).continuous)
    (by exact (abelianizationProPSubgroupOfEquiv p hVW).symm.continuous)
    (abelianizationProPSubgroupOfEquiv_toAdditive_smul p hVW hV)

/-- `abelianizationProPSubgroupOfH2Equiv` is `explicitMap2Equiv` along its compatible pair. -/
theorem abelianizationProPSubgroupOfH2Equiv_def :
    abelianizationProPSubgroupOfH2Equiv p hVW hV =
      explicitMap2Equiv (W ⧸ V.subgroupOf W)
        (Additive (abelianizationProP p W (V.subgroupOf W)))
        (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V))
        (quotientSubgroupOfEquivMap V W hV).symm
        (abelianizationProPSubgroupOfEquiv p hVW).toMulEquiv.toAdditive
        (by exact (abelianizationProPSubgroupOfEquiv p hVW).continuous)
        (by exact (abelianizationProPSubgroupOfEquiv p hVW).symm.continuous)
        (abelianizationProPSubgroupOfEquiv_toAdditive_smul p hVW hV) :=
  (rfl)

/-- **NSW (3.6.1)(i).** The change of group carries the class `u_{W/V}(p)` of the pair
`V.subgroupOf W ◁ W` to the restriction of the class `u_{G/V}(p)` to the subgroup `W.map (mk' V)`
of `G ⧸ V`. -/
theorem abelianizationProPSubgroupOfH2Equiv_class :
    abelianizationProPSubgroupOfH2Equiv p hVW hV
        (abelianizationProPClass p W (V.subgroupOf W) (W.subgroupOf_isOpen V hV)) =
      explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V)) (W.map (QuotientGroup.mk' V))
        (abelianizationProPClass p G V hV) := by
  -- With `a s` the representative of `s` chosen in `W ⧸ V.subgroupOf W` and `b s` the one chosen
  -- in `G ⧸ V`, the element `c s = a s / b s` lies in `V`, and the two factor sets differ by the
  -- coboundary of `s ↦ [c s]`: the identity
  -- `a s * a t * (a (s * t))⁻¹ =`
  -- `  c s * (b s * c t * (b s)⁻¹) * (b s * b t * (b (s * t))⁻¹) * (c (s * t))⁻¹`
  -- holds in `V`, and its image in the abelian group `V^ab(p)` is the coboundary relation.
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  set φ := (quotientSubgroupOfEquivMap V W hV).symm
  -- The representative of `s` chosen in `W ⧸ V.subgroupOf W` lies over `s`.
  have ha (s : W.map (QuotientGroup.mk' V)) :
      ((((φ s).out : W) : G) : G ⧸ V) = (s : G ⧸ V) := by
    rw [← coe_quotientSubgroupOfEquivMap_mk V W hV, QuotientGroup.out_eq',
      ContinuousMulEquiv.apply_symm_apply]
  have hmem (s : W.map (QuotientGroup.mk' V)) :
      (((φ s).out : W) : G) / (s : G ⧸ V).out ∈ V :=
    QuotientGroup.eq_iff_div_mem.mp ((ha s).trans (QuotientGroup.out_eq' _).symm)
  let c : W.map (QuotientGroup.mk' V) → V := fun s => ⟨_, hmem s⟩
  rw [abelianizationProPSubgroupOfH2Equiv_def, explicitMap2Equiv_apply, abelianizationProPClass_def,
    abelianizationProPClass_def, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    explicitRes2_mk]
  -- `explicitMap2Equiv` states the continuity of its coefficient map at the `AddEquiv` coercion,
  -- while `explicitMap2_mk` states it at the `AddMonoidHom` coercion, so the latter is applied as
  -- a term rather than rewritten.
  refine (explicitMap2_mk _ _ _ _ _ _ _ _ _).trans ?_
  rw [H2pi_eq_iff, mem_B2_iff']
  refine ⟨fun s => Additive.ofMul (abelianizationProPMk p G V (c s)),
    continuous_of_discreteTopology, fun s t => ?_⟩
  rw [Pi.sub_apply]
  refine Eq.trans ?_ (congrArg₂ (· - ·) (cocyclesMap2_apply _ _ _ _ _ _ _ _ _ s t).symm rfl)
  simp only [cocyclesMap2_apply, abelianizationProPFactorSet_apply]
  apply Additive.toMul.injective
  simp only [toMul_add, toMul_sub, Additive.toMul_smul, toMul_ofMul,
    ContinuousMulEquiv.toMulEquiv_eq_coe, AddEquiv.toAddMonoidHom_eq_coe,
    ContinuousMonoidHom.coe_coe, AddMonoidHom.coe_ofClass, MulEquiv.toAdditive_apply_apply,
    ContinuousMulEquiv.coe_toMulEquiv,
    abelianizationProPSubgroupOfEquiv_mk, Subgroup.coe_mul, InvMemClass.coe_inv,
    ContinuousMonoidHom.subgroupSubtype_apply, AddMonoidHom.id_apply]
  -- Rearrange the commutative side so that the identity is the image of an identity in `V`.
  have hconj (v : V) : (s : G ⧸ V) • abelianizationProPMk p G V v =
      abelianizationProPMk p G V (MulAut.conjNormal (s : G ⧸ V).out v) := by
    rw [← abelianizationProPMk_conj, QuotientGroup.out_eq']
  rw [eq_div_iff_mul_eq', Subgroup.smul_def, hconj, div_mul_eq_mul_div, div_mul_eq_mul_div,
    mul_comm _ (abelianizationProPMk p G V (c s)), ← map_mul, ← map_mul, ← map_div]
  congr 1
  ext
  simp only [div_eq_mul_inv, map_mul φ, Subgroup.coe_mul, MulAut.conjNormal_apply,
    InvMemClass.coe_inv, mul_inv_rev, inv_inv, c, φ]
  group

end Cohomology

end TauCeti
