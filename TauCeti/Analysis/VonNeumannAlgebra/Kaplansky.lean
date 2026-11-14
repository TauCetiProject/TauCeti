/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
public import TauCeti.Analysis.InnerProductSpace.WeakOperatorTopology
public import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# The Kaplansky density theorem: self-adjoint and positive forms

For a unital star subalgebra `S` of bounded operators on a complex Hilbert space `H`, the
strong operator closure of the self-adjoint contractions of `S` is the set of self-adjoint
contractions of the double commutant `S''`, and the strong operator closure of the positive
contractions `0 ≤ x ≤ 1` of `S` is the set of positive contractions of `S''`. By the bicommutant
theorem the strong closure of `S` is `S''`, but a strongly convergent net of operators need not be
norm bounded, so the point is that the approximants can be chosen in the unit ball of `S`.

The self-adjoint form is proved with the Kaplansky function `t ↦ 2 t / (1 + t ^ 2)`. Given a
self-adjoint contraction `y ∈ S''`, the self-adjoint operator `a = cfc kaplanskyFunInv y` lies in
`S''` and satisfies `cfc kaplanskyFun a = y`. The self-adjoint part of `S` is strongly dense in that
of `S''`, so a net `x` of self-adjoint elements of `S` converges strongly to `a`. Since the
Kaplansky function is strongly continuous on self-adjoint operators, the contractions
`cfc kaplanskyFun x` converge strongly to `y`. They lie in the norm closure of `S`, whose
self-adjoint contractions are norm limits of self-adjoint contractions of `S`.

The positive form follows: if `0 ≤ y ≤ 1` in `S''`, then self-adjoint contractions `x` of `S`
converging strongly to `√y` give positive contractions `x * x` of `S`, and these converge strongly
to `y` because multiplication is jointly strongly continuous on norm-bounded sets.

The closures are taken in Mathlib's strong operator topology copy `H →Lₚₜ[ℂ] H`.

## Main results

* `StarSubalgebra.topologicalClosure_inter_selfAdjoint_inter_closedBall_subset`: in a normed star
  algebra, the self-adjoint contractions of the norm closure of a star subalgebra are norm limits
  of self-adjoint contractions of the star subalgebra.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall`:
  the strong closure of the self-adjoint contractions of `S` is the set of self-adjoint
  contractions of `S''`.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Icc`: the strong closure of the
  positive contractions of `S` is the set of positive contractions of `S''`.

## References

* Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.5.
* Jones, *Von Neumann Algebras*, Theorem 5.2.1.
-/

public section

open Filter Metric Topology

namespace StarSubalgebra

section Normed

variable {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [StarModule 𝕜 A] [ContinuousStar A]

/-- The self-adjoint contractions of the norm closure of a star subalgebra are norm limits of
self-adjoint contractions of the star subalgebra. -/
theorem topologicalClosure_inter_selfAdjoint_inter_closedBall_subset (S : StarSubalgebra 𝕜 A) :
    (S.topologicalClosure : Set A) ∩ selfAdjoint A ∩ closedBall 0 1 ⊆
      closure ((S : Set A) ∩ selfAdjoint A ∩ closedBall 0 1) := by
  rintro y ⟨⟨hyS, hysa⟩, hy1⟩
  -- Take the real part, then rescale it into the unit ball.
  let re : A → A := fun x => (2⁻¹ : 𝕜) • (x + star x)
  let c : A → ℝ := fun x => (max 1 ‖re x‖)⁻¹
  let f : A → A := fun x => (c x : 𝕜) • re x
  have hc : ∀ x, 0 < max 1 ‖re x‖ := fun x => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hre : Continuous re := by fun_prop
  have hf : Continuous f :=
    (RCLike.continuous_ofReal.comp ((continuous_const.max (continuous_norm.comp hre)).inv₀
      fun x => (hc x).ne')).smul hre
  have hfy : f y = y := by
    have hrey : re y = y := by
      simp only [re]
      rw [hysa.star_eq, ← two_smul 𝕜 y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    have hy1' : ‖y‖ ≤ 1 := by simpa using hy1
    simp only [f, c, hrey, max_eq_left hy1', inv_one, RCLike.ofReal_one, one_smul]
  have hmaps : Set.MapsTo f S ((S : Set A) ∩ selfAdjoint A ∩ closedBall 0 1) := by
    intro x hx
    have h2 : IsSelfAdjoint (2⁻¹ : 𝕜) := by simp [IsSelfAdjoint]
    have hsa : IsSelfAdjoint (re x) := h2.smul (.add_star_self x)
    have hcx : IsSelfAdjoint (c x : 𝕜) := by simp [IsSelfAdjoint]
    refine ⟨⟨SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (add_mem hx (star_mem hx))),
      hcx.smul hsa⟩, ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr (hc x)),
      inv_mul_le_iff₀ (hc x), mul_one]
    exact le_max_right _ _
  rw [topologicalClosure_coe] at hyS
  exact hfy ▸ map_mem_closure hf hyS hmaps

end Normed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Kaplansky density theorem, self-adjoint form.** The strong operator closure of the
self-adjoint contractions of a unital star subalgebra `S` of `H →L[ℂ] H` is the set of
self-adjoint contractions of its double commutant. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 1) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  set X := (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H)
  refine subset_antisymm (closure_minimal (Set.image_mono
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer))) ?_) ?_
  · rw [Set.image_inter ContinuousLinearMap.toPointwiseConvergenceCLM_injective,
      ← S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact isClosed_closure.inter (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM
      (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 1).isClosed)
  rintro _ ⟨y, ⟨⟨hyS, hysa⟩, hy1⟩, rfl⟩
  -- `a = cfc kaplanskyFunInv y` is a self-adjoint element of `S''` with `cfc kaplanskyFun a = y`.
  have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
  set a := cfc TauCeti.kaplanskyFunInv y
  have haS : a ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM]
    exact cfc_mem (s := VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))) _
      (by rwa [← SetLike.mem_coe, hM])
  have hasa : IsSelfAdjoint a := cfc_predicate _ _
  have hya : cfc TauCeti.kaplanskyFun a = y :=
    hysa.cfc_kaplanskyFun_cfc_kaplanskyFunInv (by simpa using hy1)
  -- The self-adjoint part of `S` is strongly dense in that of `S''`; take the filter of
  -- self-adjoint elements of `S` strongly close to `a`.
  have ha : q a ∈ closure (q '' X) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨a, ⟨haS, hasa⟩, rfl⟩
  set l := Filter.comap q (𝓝[q '' X] (q a)) ⊓ 𝓟 X
  have : l.NeBot := comap_inf_principal_neBot_of_image_mem
    (mem_closure_iff_nhdsWithin_neBot.mp ha) self_mem_nhdsWithin
  have hlim : Tendsto (fun x => q x) l (𝓝 (q a)) :=
    (tendsto_comap.mono_left inf_le_left).mono_right nhdsWithin_le_nhds
  have hX : ∀ᶠ x in l, x ∈ X := mem_inf_of_right (mem_principal_self X)
  -- Along this filter the Kaplansky function converges strongly to `y`, through self-adjoint
  -- contractions of the norm closure of `S`.
  have hT : q y ∈ closure (q '' ((S.topologicalClosure : Set (H →L[ℂ] H)) ∩
      selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1)) := by
    have := S.isClosed_topologicalClosure
    refine mem_closure_of_tendsto (hya ▸ TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun
      (x := fun x => x) (hX.mono fun x hx => hx.2) hasa hlim) ?_
    filter_upwards [hX] with x hx
    refine ⟨cfc TauCeti.kaplanskyFun x, ⟨⟨?_, cfc_predicate _ _⟩, ?_⟩, rfl⟩
    · exact cfc_mem (s := S.topologicalClosure) _ (S.le_topologicalClosure hx.1)
    · exact mem_closedBall_zero_iff.mpr (TauCeti.norm_cfc_kaplanskyFun_le x)
  refine closure_minimal ?_ isClosed_closure hT
  exact (Set.image_mono S.topologicalClosure_inter_selfAdjoint_inter_closedBall_subset).trans
    (image_closure_subset_closure_image q.continuous)

/-- **The Kaplansky density theorem, positive form.** The strong operator closure of the positive
contractions `0 ≤ x ≤ 1` of a unital star subalgebra `S` of `H →L[ℂ] H` is the set of positive
contractions of its double commutant. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_Icc (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      ((S : Set (H →L[ℂ] H)) ∩ Set.Icc 0 1)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ Set.Icc 0 1) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  set X := (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 1
  refine subset_antisymm (closure_minimal (Set.image_mono
    (Set.inter_subset_inter_left _ Set.subset_centralizer_centralizer)) ?_) ?_
  · refine ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM ?_
    rw [Set.image_inter ContinuousLinearMapWOT.ofCLM_injective]
    exact (Set.isClosed_image_ofCLM_centralizer _).inter
      ContinuousLinearMapWOT.isClosed_image_ofCLM_Icc
  rintro _ ⟨y, ⟨hyS, hy0, hy1⟩, rfl⟩
  -- `√y` is a self-adjoint contraction of `S''` with `√y * √y = y`.
  have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
  have hbS : CFC.sqrt y ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM, SetLike.mem_coe, CFC.sqrt_eq_real_sqrt y hy0]
    exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))) _
      (by rwa [← SetLike.mem_coe, hM])
  have hb1 : ‖CFC.sqrt y‖ ≤ 1 := by
    rw [CFC.norm_sqrt y hy0]
    exact Real.sqrt_le_one.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg y hy0).mpr hy1)
  -- Take the filter of self-adjoint contractions of `S` strongly close to `√y`.
  have hb : q (CFC.sqrt y) ∈ closure (q '' X) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall]
    exact ⟨CFC.sqrt y, ⟨⟨hbS, (CFC.sqrt_nonneg y).isSelfAdjoint⟩,
      mem_closedBall_zero_iff.mpr hb1⟩, rfl⟩
  set l := Filter.comap q (𝓝[q '' X] (q (CFC.sqrt y))) ⊓ 𝓟 X
  have : l.NeBot := comap_inf_principal_neBot_of_image_mem
    (mem_closure_iff_nhdsWithin_neBot.mp hb) self_mem_nhdsWithin
  have hlim : ∀ v, Tendsto (fun x : H →L[ℂ] H => x v) l (𝓝 ((CFC.sqrt y) v)) :=
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
      ((tendsto_comap.mono_left inf_le_left).mono_right nhdsWithin_le_nhds)
  have hX : ∀ᶠ x in l, x ∈ X := mem_inf_of_right (mem_principal_self X)
  -- Squaring is strongly continuous on contractions, and squares of self-adjoint contractions of
  -- `S` are positive contractions of `S`.
  refine mem_closure_of_tendsto (f := fun x => q (x * x)) (b := l) ?_ ?_
  · rw [← CFC.sqrt_mul_sqrt_self y hy0, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    exact ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
      (hX.mono fun x hx => mem_closedBall_zero_iff.mp hx.2)
  filter_upwards [hX] with x ⟨⟨hxS, hxsa⟩, hx1⟩
  have hxx : 0 ≤ x * x := hxsa.mul_self_nonneg
  refine ⟨x * x, ⟨mul_mem hxS hxS, hxx, ?_⟩, rfl⟩
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hxx).mp ?_
  have hx1' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx1
  exact (norm_mul_le x x).trans (by nlinarith [norm_nonneg x])

end StarSubalgebra
