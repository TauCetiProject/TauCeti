/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Basic
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
strong operator closure of the self-adjoint elements of norm at most `r` of `S` is the set of
self-adjoint elements of norm at most `r` of the double commutant `S''`, and the strong operator
closure of the positive contractions `0 ≤ x ≤ 1` of `S` is the set of positive contractions of
`S''`. By the bicommutant theorem the strong closure of `S` is `S''`, but a strongly convergent net
of operators need not be norm bounded, so the point is that the approximants can be chosen in a
ball of `S`.

The self-adjoint form is proved with the Kaplansky function `t ↦ 2 t / (1 + t ^ 2)`, after
rescaling to `r = 1`. Given a self-adjoint contraction `y ∈ S''`, the self-adjoint operator
`a = cfc kaplanskyFunInv y` lies in `S''` and satisfies `cfc kaplanskyFun a = y`. The
self-adjoint part of `S` is strongly dense in that of `S''`, so a net `x` of self-adjoint elements
of `S` converges strongly to `a`. Since the Kaplansky function is strongly continuous on
self-adjoint operators, the contractions `cfc kaplanskyFun x` converge strongly to `y`. They lie
in the norm closure of `S`, whose self-adjoint contractions are norm limits of self-adjoint
contractions of `S` (`TauCeti.closure_inter_selfAdjoint_inter_closedBall`).

The positive form follows: if `0 ≤ y ≤ 1` in `S''`, then self-adjoint contractions `x` of `S`
converging strongly to `√y` give positive contractions `x * x` of `S`, and these converge strongly
to `y` because multiplication is jointly strongly continuous on norm-bounded sets.

The closures are taken in Mathlib's strong operator topology copy `H →Lₚₜ[ℂ] H`.

## Main results

* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall`:
  the strong closure of the self-adjoint elements of norm at most `r` of `S` is the set of
  self-adjoint elements of norm at most `r` of `S''`.
* `StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_Icc`: the strong closure of the
  positive contractions of `S` is the set of positive contractions of `S''`.

## References

* Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.5.
* Jones, *Von Neumann Algebras*, Theorem 5.2.1.
-/

public section

open Filter Metric Topology

/-- A point of the closure of `q '' s` is a limit of `q` along a nontrivial filter that is
eventually in `s`. -/
private theorem exists_tendsto_of_mem_closure_image {α β : Type*} [TopologicalSpace β]
    {q : α → β} {s : Set α} {b : β} (hb : b ∈ closure (q '' s)) :
    ∃ l : Filter α, l.NeBot ∧ (∀ᶠ x in l, x ∈ s) ∧ Tendsto q l (𝓝 b) :=
  ⟨comap q (𝓝[q '' s] b) ⊓ 𝓟 s, comap_inf_principal_neBot_of_image_mem
    (mem_closure_iff_nhdsWithin_neBot.mp hb) self_mem_nhdsWithin,
    mem_inf_of_right (mem_principal_self s),
    (tendsto_comap.mono_left inf_le_left).mono_right nhdsWithin_le_nhds⟩

namespace StarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Kaplansky density theorem, self-adjoint form.** The strong operator closure of the
self-adjoint elements of norm at most `r` of a unital star subalgebra `S` of `H →L[ℂ] H` is the set
of self-adjoint elements of norm at most `r` of its double commutant. -/
theorem closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (r : ℝ) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        ((S : Set (H →L[ℂ] H)).centralizer.centralizer ∩ selfAdjoint (H →L[ℂ] H) ∩
          closedBall 0 r) := by
  set q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  set X := (S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H)
  refine subset_antisymm (closure_minimal (Set.image_mono
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _
      Set.subset_centralizer_centralizer))) ?_) ?_
  · rw [Set.image_inter ContinuousLinearMap.toPointwiseConvergenceCLM_injective,
      ← S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact isClosed_closure.inter
      (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
        (ContinuousLinearMapWOT.isCompact_image_ofCLM_closedBall 0 r).isClosed)
  rintro _ ⟨y, ⟨⟨hyS, hysa⟩, hyr⟩, rfl⟩
  have hyr' : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp hyr
  rcases ((norm_nonneg y).trans hyr').eq_or_lt with rfl | hr
  · obtain rfl : y = 0 := norm_le_zero_iff.mp hyr'
    exact subset_closure ⟨0, ⟨⟨zero_mem S, .zero _⟩, mem_closedBall_self le_rfl⟩, rfl⟩
  have hM : (VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      (S : Set (H →L[ℂ] H)).centralizer.centralizer :=
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq S).subset
  -- Rescale `y` to the self-adjoint contraction `z = r⁻¹ • y` of `S''`.
  set z := ((r⁻¹ : ℝ) : ℂ) • y
  have hyz : y = (r : ℂ) • z := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  have hzS : z ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM] at hyS ⊢
    exact SMulMemClass.smul_mem _ hyS
  have hzsa : IsSelfAdjoint z := (by simp [IsSelfAdjoint] : IsSelfAdjoint ((r⁻¹ : ℝ) : ℂ)).smul hysa
  have hz1 : ‖z‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      inv_mul_le_iff₀ hr, mul_one]
    exact hyr'
  -- `a = cfc kaplanskyFunInv z` is a self-adjoint element of `S''` with `cfc kaplanskyFun a = z`.
  set a := cfc TauCeti.kaplanskyFunInv z
  have haS : a ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [← hM]
    exact cfc_mem (s := VonNeumannAlgebra.adjoin (S : Set (H →L[ℂ] H))) _
      (by rwa [← SetLike.mem_coe, hM])
  have hasa : IsSelfAdjoint a := cfc_predicate _ _
  have hza : cfc TauCeti.kaplanskyFun a = z := hzsa.cfc_kaplanskyFun_cfc_kaplanskyFunInv hz1
  -- The self-adjoint part of `S` is strongly dense in that of `S''`; take a filter of
  -- self-adjoint elements of `S` converging strongly to `a`.
  have ha : q a ∈ closure (q '' X) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨a, ⟨haS, hasa⟩, rfl⟩
  obtain ⟨l, hl, hX, hlim⟩ := exists_tendsto_of_mem_closure_image ha
  -- Along this filter `r • cfc kaplanskyFun` converges strongly to `y`, through self-adjoint
  -- elements of norm at most `r` of the norm closure of `S`.
  have hT : q y ∈ closure (q '' (closure (S : Set (H →L[ℂ] H)) ∩
      selfAdjoint (H →L[ℂ] H) ∩ closedBall 0 r)) := by
    have hK := (TauCeti.tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun
      (x := fun x => x) (hX.mono fun x hx => hx.2) hasa hlim).const_smul (r : ℂ)
    rw [hza, ← map_smul, ← hyz] at hK
    refine mem_closure_of_tendsto (f := fun x => q ((r : ℂ) • cfc TauCeti.kaplanskyFun x))
      (by simpa only [map_smul] using hK) ?_
    filter_upwards [hX] with x hx
    refine ⟨(r : ℂ) • cfc TauCeti.kaplanskyFun x, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · have := S.isClosed_topologicalClosure
      rw [← topologicalClosure_coe]
      exact SMulMemClass.smul_mem _
        (cfc_mem (s := S.topologicalClosure) _ (S.le_topologicalClosure hx.1))
    · exact (by simp [IsSelfAdjoint] : IsSelfAdjoint (r : ℂ)).smul (cfc_predicate _ _)
    · rw [mem_closedBall_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      simpa using mul_le_mul_of_nonneg_left (TauCeti.norm_cfc_kaplanskyFun_le x) hr.le
  refine closure_minimal ?_ isClosed_closure hT
  rw [← TauCeti.closure_inter_selfAdjoint_inter_closedBall ℂ S r]
  exact image_closure_subset_closure_image q.continuous

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
  · refine ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
      ?_
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
  -- Take a filter of self-adjoint contractions of `S` converging strongly to `√y`.
  have hb : q (CFC.sqrt y) ∈ closure (q '' X) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint_inter_closedBall]
    exact ⟨CFC.sqrt y, ⟨⟨hbS, (CFC.sqrt_nonneg y).isSelfAdjoint⟩,
      mem_closedBall_zero_iff.mpr hb1⟩, rfl⟩
  obtain ⟨l, hl, hX, hq⟩ := exists_tendsto_of_mem_closure_image hb
  have hlim : ∀ v, Tendsto (fun x : H →L[ℂ] H => x v) l (𝓝 ((CFC.sqrt y) v)) := by
    have h := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hq
    simp only [q, ContinuousLinearMap.toPointwiseConvergenceCLM_apply] at h
    -- Evaluating an operator through the pointwise copy `H →Lₚₜ[ℂ] H` is evaluating it.
    exact h
  -- Squaring is strongly continuous on contractions, and squares of self-adjoint contractions of
  -- `S` are positive contractions of `S`.
  refine mem_closure_of_tendsto (f := fun x => q (x * x)) (b := l) ?_ ?_
  · rw [← CFC.sqrt_mul_sqrt_self y hy0, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro v
    simp only [q, ContinuousLinearMap.toPointwiseConvergenceCLM_apply, ContinuousLinearMap.mul_def]
    exact ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
      (hX.mono fun x hx => mem_closedBall_zero_iff.mp hx.2) v
  filter_upwards [hX] with x ⟨⟨hxS, hxsa⟩, hx1⟩
  have hxx : 0 ≤ x * x := hxsa.mul_self_nonneg
  refine ⟨x * x, ⟨mul_mem hxS hxS, hxx, ?_⟩, rfl⟩
  refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ hxx).mp ?_
  have hx1' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx1
  exact (norm_mul_le x x).trans (by nlinarith [norm_nonneg x])

end StarSubalgebra
