/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.CauchyRiemann.Weak

/-!
# `C¹` solutions of the Cauchy–Riemann equation for a `C¹` complex structure

Let `E` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open, `A : ℂ → E →L[ℝ] E` a field of
complex structures of class `C¹` on `Ω`, `A(z)² = -1`, and `u : ℂ → E` a map of class `C¹` on `Ω`
solving the Cauchy–Riemann equation

`∂ₜu = A(z) ∂ₛu`

in the coordinate `z = s + i t`. The main case is `A = J ∘ u` for an almost complex structure `J`
of class `C¹`, which makes `u` a `J`-holomorphic curve in local coordinates. Such a `u` need not
be `C²`, but it has two weak derivatives:

* `u ∈ W^{2,p}_loc(Ω)` for every finite `p`
  (`TauCeti.memWkpLoc_two_of_contDiffOn_of_cauchyRiemann`). The equation is the linear equation
  `∂ₛu + A ∂ₜu = 0` with the coefficient `A ∈ W^{1,p}_loc`, so this is interior regularity at order
  one (`TauCeti.IsWeakCRSolution.memWkpLoc_succ`, McDuff–Salamon, Proposition B.4.9). The endpoint
  `p = ∞` fails (`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`).
* `∂ₜu` is a weak solution of the linearized equation
  `∂ₛ(∂ₜu) + A ∂ₜ(∂ₜu) + (∂ₜA) ∂ₜu = 0`
  (`TauCeti.isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann`): this is the
  `t`-derivative of the equation (`TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`), which
  needs only one weak derivative of `∂ₜu`. Its coefficient `∂ₜA` is continuous, so the weak
  similarity principle and its consequences
  (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn`) apply to `∂ₜu`.

This is the first step of McDuff–Salamon, Lemma 2.4.1, for a structure of class `C¹`: the
critical points of `u`, where `∂ₜu` vanishes, are those of a solution of a linear Cauchy–Riemann
equation. The weak theory needs an inner product on the target; a finite-dimensional normed `E`
is first identified with a Euclidean space.

## Main results

* `TauCeti.memWkpLoc_two_of_contDiffOn_of_cauchyRiemann`: `u ∈ W^{2,p}_loc` for finite `p`.
* `TauCeti.isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann`: `∂ₜu` solves the
  linearized equation weakly.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and Appendix B.4 (Proposition B.4.9, Theorem B.4.1).
-/

public section

open Complex MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Inner product targets -/

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {A : ℂ → V →L[ℝ] V} {u : ℂ → V}

/-- A `C¹` coefficient is a Sobolev coefficient, with weak derivative its classical one and zero
zeroth-order term. -/
private theorem isSobolevCRCoefficients_of_contDiffOn (hA : ContDiffOn ℝ 1 A Ω) (p : ℝ≥0∞) :
    IsSobolevCRCoefficients p Ω A (fderiv ℝ A) 0 where
  hasWeakFDerivOn := hA.hasWeakFDerivOn_fderiv
  memLpLoc_coeff := hA.continuousOn.memLpLoc
  memLpLoc_deriv := (hA.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).memLpLoc
  memLpLoc_zeroth := memLpLoc_zero

omit [FiniteDimensional ℝ V] in
/-- `∂ₜu = A ∂ₛu` is `∂ₛu + A ∂ₜu = 0` when `A² = -1`. -/
private theorem fderiv_one_add_apply_fderiv_I {z : ℂ}
    (hAA : A z ∘L A z = -ContinuousLinearMap.id ℝ V)
    (hCR : fderiv ℝ u z I = A z (fderiv ℝ u z 1)) :
    fderiv ℝ u z 1 + A z (fderiv ℝ u z I) = 0 := by
  rw [hCR, ← ContinuousLinearMap.comp_apply, hAA]
  simp

/-- A `C¹` solution is a weak solution of the linear equation `∂ₛu + A ∂ₜu = 0`. -/
private theorem isWeakCRSolution_of_contDiffOn (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hp : p ≠ ⊤) : IsWeakCRSolution p Ω A (fderiv ℝ A) 0 u 0 := by
  have hpq : p⁻¹ + p⁻¹ ≤ 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    exact add_le_add (ENNReal.inv_le_inv.2 hp2) (ENNReal.inv_le_inv.2 hp2)
  refine ((isSobolevCRCoefficients_of_contDiffOn hA p).isWeakCRSolution_iff_ae hpq hp hp
    hu.hasWeakFDerivOn_fderiv hu.continuousOn.memLpLoc
    (hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).memLpLoc locallyIntegrableOn_zero).2 ?_
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall fun z hz ↦ ?_)
  simpa using fderiv_one_add_apply_fderiv_I (hAA z hz) (hCR z hz)

/-- `W^{2,p}_loc` regularity for `2 < p < ∞` on an inner product space. -/
private theorem memWkpLoc_two_of_two_lt (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0} (hp : 2 < p) :
    MemWkpLoc p Ω 2 u := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hpq : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    exact ENNReal.add_lt_add (ENNReal.inv_lt_inv.2 hp') (ENNReal.inv_lt_inv.2 hp')
  have hJ2 : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), A z * A z = -1 :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall hAA)
  exact (isWeakCRSolution_of_contDiffOn hA hAA hu hCR hp'.le ENNReal.coe_ne_top).memWkpLoc_succ
    (k := 1) (isSobolevCRCoefficients_of_contDiffOn hA p) hp hJ2 hpq le_rfl
    (hA.memWkpLoc subset_rfl) memWkpLoc_zero_fun memWkpLoc_zero_fun

/-- `∂ₜu` solves the linearized equation weakly, for `2 < p < ∞`, on an inner product space. -/
private theorem isWeakLinearCauchyRiemannOn_of_two_lt (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0} (hp : 2 < p) :
    IsWeakLinearCauchyRiemannOn p Ω A (fun z ↦ fderiv ℝ A z I) (fun z ↦ fderiv ℝ u z I) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hpq : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    exact add_le_add (ENNReal.inv_le_inv.2 hp'.le) (ENNReal.inv_le_inv.2 hp'.le)
  have hc := isSobolevCRCoefficients_of_contDiffOn hA p
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  -- a weak derivative of `∂ₜu`, from `u ∈ W^{2,p}_loc`
  have h2 := memWkpLoc_two_of_two_lt hA hAA hu hCR hp
  obtain ⟨-, hDu⟩ := h2.hasWeakFDerivOn_fderiv_of_contDiffOn (k := 1)
    (by rw [Opens.interior_coe]) (by simpa using hu)
    (Filter.EventuallyEq.refl _ _)
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_succ_iff_of_isOpen.1 hDu
  have hDI := hD.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hsol := (isWeakCRSolution_of_contDiffOn hA hAA hu hCR hp'.le
    ENNReal.coe_ne_top).apply_I_of_hasWeakFDerivOn hc hpq ENNReal.coe_ne_top ENNReal.coe_ne_top
    hasWeakFDerivOn_zero memLpLoc_zero hu.hasWeakFDerivOn_fderiv hdu.memLpLoc
    hasWeakFDerivOn_zero
  have hlin := ((hc.add_zeroth (hc.memLpLoc_deriv_apply I)).isWeakLinearCauchyRiemannOn_iff hpq
    ENNReal.coe_ne_top ENNReal.coe_ne_top).2 ⟨hdu.clm_apply continuousOn_const, by
      convert hsol using 2 with z
      simp, _, hDI,
    (memWkpLoc_zero_iff.1 hDp).clm_comp (ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] V) V
      (.apply ℝ V I))⟩
  simpa only [Pi.zero_apply, zero_add] using hlin

end InnerProduct

/-! ### Normed targets -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens ℂ} {A : ℂ → E →L[ℝ] E} {u : ℂ → E}

omit [FiniteDimensional ℝ E] in
/-- The data `(A, u)` read in a Euclidean model `e : E ≃ ℝᵈ`: the conjugated structure
`e A e⁻¹` is `C¹` with square `-1`, and `e ∘ u` is a `C¹` solution for it. -/
private theorem euclidean_model (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    ContDiffOn ℝ 1 (fun z ↦ e.arrowCongr e (A z)) Ω ∧
      (∀ z ∈ Ω, e.arrowCongr e (A z) ∘L e.arrowCongr e (A z) = -ContinuousLinearMap.id ℝ _) ∧
      ContDiffOn ℝ 1 (fun z ↦ e (u z)) Ω ∧
      (∀ z ∈ Ω, fderiv ℝ (fun z ↦ e (u z)) z = (e : E →L[ℝ] _) ∘L fderiv ℝ u z) ∧
      ∀ z ∈ Ω, fderiv ℝ (fun z ↦ e (u z)) z I =
        e.arrowCongr e (A z) (fderiv ℝ (fun z ↦ e (u z)) z 1) := by
  have hfd : ∀ z ∈ Ω, fderiv ℝ (fun z ↦ e (u z)) z = (e : E →L[ℝ] _) ∘L fderiv ℝ u z :=
    fun z hz ↦ (e.hasFDerivAt.comp z ((hu.differentiableOn one_ne_zero).differentiableAt
      (Ω.isOpen.mem_nhds hz)).hasFDerivAt).fderiv
  refine ⟨(e.arrowCongr e).contDiff.comp_contDiffOn hA,
    fun z hz ↦ ?_, e.contDiff.comp_contDiffOn hu, hfd, fun z hz ↦ ?_⟩
  · ext1 v
    have h := congr($(hAA z hz) (e.symm v))
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply] at h ⊢
    simp [h]
  · simp [hfd z hz, hCR z hz]

/-- **`W^{2,p}` regularity of `C¹` solutions for a `C¹` structure.** Let `u` be of class `C¹` on
an open set `Ω` and solve `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex structures,
`A(z)² = -1`, on a finite-dimensional real normed space. Then `u ∈ W^{2,p}_loc(Ω)` for every
finite exponent `p`. -/
theorem memWkpLoc_two_of_contDiffOn_of_cauchyRiemann (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemWkpLoc p Ω 2 u := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let e := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
    (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (by simp)
  obtain ⟨hA', hAA', hu', -, hCR'⟩ := euclidean_model hA hAA hu hCR e
  lift p to ℝ≥0 using hp
  have h := (memWkpLoc_two_of_two_lt hA' hAA' hu' hCR' (p := max p 3)
    (lt_max_of_lt_right (by norm_num))).mono_exponent (q := p) (by exact_mod_cast le_max_left _ _)
  simpa using h.clm_comp (e.symm : _ →L[ℝ] E)

/-- **The linearized equation for `∂ₜu`.** Let `u` be of class `C¹` on an open set `Ω` and solve
`∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex structures, `A(z)² = -1`, on a
finite-dimensional real normed space. Then `∂ₜu` is a weak solution, for every finite exponent, of
the linear equation `∂ₛξ + A ∂ₜξ + (∂ₜA) ξ = 0`. -/
theorem isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann
    (hA : ContDiffOn ℝ 1 A Ω) (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hu : ContDiffOn ℝ 1 u Ω) (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    IsWeakLinearCauchyRiemannOn p Ω A (fun z ↦ fderiv ℝ A z I) (fun z ↦ fderiv ℝ u z I) := by
  let e := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
    (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (by simp)
  obtain ⟨hA', hAA', hu', hfd, hCR'⟩ := euclidean_model hA hAA hu hCR e
  lift p to ℝ≥0 using hp
  have h := ((isWeakLinearCauchyRiemannOn_of_two_lt hA' hAA' hu' hCR' (p := max p 3)
    (lt_max_of_lt_right (by norm_num))).mono_exponent (q := p)
    (by exact_mod_cast le_max_left _ _)).continuousLinearEquiv_comp e.symm
  -- read the transported equation back on `E`
  have hfdA : ∀ z ∈ Ω, fderiv ℝ (fun z ↦ e.arrowCongr e (A z)) z I =
      e.arrowCongr e (fderiv ℝ A z I) := fun z hz ↦ by
    have h := ((e.arrowCongr e).hasFDerivAt.comp z ((hA.differentiableOn one_ne_zero
      ).differentiableAt (Ω.isOpen.mem_nhds hz)).hasFDerivAt).fderiv
    simp only [Function.comp_def] at h
    rw [h]
    rfl
  refine (isWeakCauchyRiemannOn_congr (fun z hz ↦ ?_)).1
    ((isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h)
  · simp [hfd z hz]
  · exact Filter.Eventually.of_forall fun z ↦ (by ext1 v; simp)
  · rw [Ω.isOpen.interior_eq]
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall fun z hz ↦ ?_)
    simp [hfdA z hz]

end TauCeti
