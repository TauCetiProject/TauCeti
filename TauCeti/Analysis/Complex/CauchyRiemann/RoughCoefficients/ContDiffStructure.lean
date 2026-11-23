/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.CauchyRiemann.NormalDerivative
import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Data.ENNReal.Holder

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

/-- A `C¹` solution of `∂ₜu = A ∂ₛu` is a weak solution of `∂ₛu + A ∂ₜu = 0`. -/
private theorem isWeakCRSolution_of_cauchyRiemann (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0} :
    IsWeakCRSolution p Ω A (fderiv ℝ A) 0 u 0 :=
  (isWeakCRSolution_iff_of_contDiffOn hA continuous_zero.continuousOn hu
    continuous_zero.continuousOn).2 fun z hz ↦ by
      simpa using (add_apply_add_eq_iff_eq_apply_add_sub (hAA z hz) (c := 0) (y := 0)).2
        (by simpa using hCR z hz)

/-- `W^{2,p}_loc` regularity for `2 < p < ∞` on an inner product space. -/
private theorem memWkpLoc_two_of_two_lt (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0} (hp : 2 < p) :
    MemWkpLoc p Ω 2 u := by
  have hJ2 : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), A z * A z = -1 :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall hAA)
  exact (isWeakCRSolution_of_cauchyRiemann hA hAA hu hCR).memWkpLoc_succ (k := 1)
    (.of_contDiffOn hA continuous_zero.continuousOn p) hp hJ2
    (ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)) le_rfl
    (hA.memWkpLoc subset_rfl) memWkpLoc_zero_fun memWkpLoc_zero_fun

/-- `∂ₜu` solves the linearized equation weakly, for `2 < p < ∞`, on an inner product space. -/
private theorem isWeakLinearCauchyRiemannOn_of_two_lt (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ V) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0} (hp : 2 < p) :
    IsWeakLinearCauchyRiemannOn p Ω A (fun z ↦ fderiv ℝ A z I) (fun z ↦ fderiv ℝ u z I) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hpq : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ ≤ 1 :=
    (ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)).le
  have hc := IsSobolevCRCoefficients.of_contDiffOn hA continuous_zero.continuousOn p
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  -- a weak derivative of `∂ₜu`, from `u ∈ W^{2,p}_loc`
  have h2 := memWkpLoc_two_of_two_lt hA hAA hu hCR hp
  obtain ⟨-, hDu⟩ := h2.hasWeakFDerivOn_fderiv_of_contDiffOn (k := 1)
    (by rw [Opens.interior_coe]) (by simpa using hu)
    (Filter.EventuallyEq.refl _ _)
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_succ_iff_of_isOpen.1 hDu
  have hDI := hD.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hsol := (isWeakCRSolution_of_cauchyRiemann (p := p) hA hAA hu hCR
    ).apply_I_of_hasWeakFDerivOn hc hpq ENNReal.coe_ne_top ENNReal.coe_ne_top
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
      ∀ z ∈ Ω, fderiv ℝ (fun z ↦ e (u z)) z I =
        e.arrowCongr e (A z) (fderiv ℝ (fun z ↦ e (u z)) z 1) := by
  refine ⟨(e.arrowCongr e).contDiff.comp_contDiffOn hA, fun z hz ↦ ?_,
    e.contDiff.comp_contDiffOn hu, fun z hz ↦ ?_⟩
  · -- `e.arrowCongr e` is the algebra equivalence `e.conjContinuousAlgEquiv`
    change e.conjContinuousAlgEquiv (A z) ∘L e.conjContinuousAlgEquiv (A z) = _
    simpa [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.one_def] using
      congr(e.conjContinuousAlgEquiv $(hAA z hz))
  · simp [← Function.comp_def e u, e.comp_fderiv, hCR z hz]

/-- **`W^{2,p}` regularity of `C¹` solutions for a `C¹` structure.** Let `u` be of class `C¹` on
an open set `Ω` and solve `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex structures,
`A(z)² = -1`, on a finite-dimensional real normed space. Then `u ∈ W^{2,p}_loc(Ω)` for every
finite exponent `p`. -/
theorem memWkpLoc_two_of_contDiffOn_of_cauchyRiemann (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemWkpLoc p Ω 2 u := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let e : E ≃L[ℝ] _ := toEuclidean
  obtain ⟨hA', hAA', hu', hCR'⟩ := euclidean_model hA hAA hu hCR e
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
  let e : E ≃L[ℝ] _ := toEuclidean
  obtain ⟨hA', hAA', hu', hCR'⟩ := euclidean_model hA hAA hu hCR e
  lift p to ℝ≥0 using hp
  have h := ((isWeakLinearCauchyRiemannOn_of_two_lt hA' hAA' hu' hCR' (p := max p 3)
    (lt_max_of_lt_right (by norm_num))).mono_exponent (q := p)
    (by exact_mod_cast le_max_left _ _)).continuousLinearEquiv_comp e.symm
  -- read the transported equation back on `E`
  refine (isWeakCauchyRiemannOn_congr (fun z _ ↦ ?_)).1
    ((isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h)
  · simp [← Function.comp_def e u, e.comp_fderiv]
  · exact Filter.Eventually.of_forall fun z ↦ (by ext1 v; simp)
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    simp [← Function.comp_def (e.arrowCongr e) A, (e.arrowCongr e).comp_fderiv]

end TauCeti
