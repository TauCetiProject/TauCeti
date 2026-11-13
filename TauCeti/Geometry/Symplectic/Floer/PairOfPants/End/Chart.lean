/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# The pair of pants and its end charts in real coordinates

Integrals over the pair of pants `S = ℂ ∖ {0, 1}` are computed in the real coordinates
`ℝ × ℝ ≃ ℂ`, where the coordinate formulas of `TauCeti.Geometry.Symplectic.Floer.Energy` and
`TauCeti.Geometry.Symplectic.Floer.Pullback` live. This file transports `S`
(`TauCeti.Floer.thricePuncturedSphereReal`), the pair-of-pants perturbation and the cylindrical
end lifts of `S` to these coordinates. The end chart `φ_q` (`TauCeti.Floer.endChart q`) is the end
lift of the end `q` in real coordinates, a holomorphic change of coordinates from the cylinder of
the end to `S`. On the strip `±s > 1/2`, `t ∈ [-1/2, 1/2)` (`TauCeti.Floer.endStrip q`) it is
injective, and it preserves orientation, so the change of variables formula applies on the images
of the three strips; these images are disjoint and measurable. Along the end chart, the
pair-of-pants perturbation pulls back to its components in the end coordinates.

On the input ends `0`, `1` the end coordinate `s` tends to `+∞`, on the output end `∞` to `-∞`.
The positive end chart `φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart q`), with the
sign of the end, reads every end as a positive end; it is again holomorphic, orientation
preserving and `1`-periodic in `t`. Where a perturbation is `H_q(t) dt` on the end `q`, it pulls
back along `φ'_q` to `H'_q(t) dt` for the Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), so that results about positive Floer half-cylinders
apply to all three ends.

## Main definitions

* `TauCeti.Floer.thricePuncturedSphereReal`: the pair of pants `S` in the real coordinates
  `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endChart q`: the end lift of `q` in the real coordinates `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endStrip q`: the part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the cylinder of the end
  `q`.
* `TauCeti.Floer.positiveEndChart q`: the end chart of `q` read as a positive end.
* `TauCeti.Floer.positiveEndHamiltonian H q`: the end Hamiltonian in the positive end chart.

## Main results

* `TauCeti.Floer.isCompact_preimage_truncation`,
  `TauCeti.Floer.preimage_truncation_subset_thricePuncturedSphereReal`,
  `TauCeti.Floer.exists_lt_endSign_mul_re_endCoord_of_notMem_truncation`: in real coordinates the
  truncation `S_R` is compact and lies in `S`, and every other point of `S` lies beyond `R` on some
  end.
* `TauCeti.Floer.setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation`: the integral over
  `S` of a function vanishing beyond `R` on every end is its integral over `S_R`.
* `TauCeti.Floer.contDiffAt_uncurry_pairOfPantsPerturbation`,
  `TauCeti.Floer.differentiableAt_pairOfPantsPerturbation_target`: in real coordinates, the
  components of the perturbation are `Cⁿ` on `S × V` for `Cⁿ` Hamiltonians, and in particular
  differentiable in the target point for `C¹` Hamiltonians.
* `TauCeti.Floer.contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt`: a datum
  which is `C¹` on `S × M` has `C¹` components in the real coordinates of `S`.
* `TauCeti.Floer.differentiableAt_pairOfPantsPerturbation_domain`,
  `TauCeti.Floer.mdifferentiableAt_pairOfPantsPerturbation_target`: for `C¹` Hamiltonians on a
  manifold, the components of the perturbation are differentiable at points of `S` in the domain
  and in the target point separately.
* `TauCeti.Floer.endChart_mem_thricePuncturedSphereReal`, `TauCeti.Floer.re_endCoord_endChart`:
  the end chart sends the part `±s > 0` of the end into `S` and preserves the longitudinal
  coordinate.
* `TauCeti.Floer.injOn_endChart`, `TauCeti.Floer.det_fderiv_endChart_nonneg`,
  `TauCeti.Floer.det_fderiv_endChart_pos`: the end chart is injective on the strip, preserves
  orientation and is a local diffeomorphism.
* `TauCeti.Floer.pairwise_disjoint_image_endChart`: the images of the three strips are disjoint.
* `TauCeti.Floer.mem_image_endChart`: they contain every point of `S` with signed longitudinal
  coordinate greater than `1/2` on some end.
* `TauCeti.Floer.injOn_endChart_univ_prod_Ico`: the end chart is injective on every band of
  angular width one.
* `TauCeti.Floer.image_endChart_prod_Ico`: the image of `P × [0, 1)` under the end chart is the
  set of points of `S` whose longitudinal coordinate lies in `P`, for any set `P` of positive
  signed longitudinal coordinates.
* `TauCeti.Floer.preimage_truncation_inter_eq_image_endChart`: the part `±s > c` of the end `q`
  in the truncation `S_R` is the image under the end chart of `c < ±s ≤ R`, `t ∈ [0, 1)`.
* `TauCeti.Floer.perturbationPullback_endChart_eq_cylindricalEndLift`: the pullback of a
  perturbation along the end chart is the perturbation evaluated on the image of a tangent vector
  under the end lift.
* `TauCeti.Floer.perturbationPullback_endChart`: the pullback of the pair-of-pants perturbation
  along the end chart is its component in the end coordinates.
* `TauCeti.Floer.isComplexLinearMap_fderiv_endChart`: the end chart is holomorphic.
* `TauCeti.Floer.perturbationPullback_endChart_stdComplexLineImag_of_le`,
  `TauCeti.Floer.perturbationPullback_endChart_stdComplexLineReal_of_le`: where a perturbation is
  `H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_t` to `H_q(t)` and `∂_s`
  to `0`.
* `TauCeti.Floer.isComplexLinearMap_fderiv_positiveEndChart`,
  `TauCeti.Floer.det_fderiv_positiveEndChart_pos`, `TauCeti.Floer.injOn_positiveEndChart`,
  `TauCeti.Floer.positiveEndChart_add_one`: the positive end chart is holomorphic, orientation
  preserving, injective on the band `ℝ × (0, 1)` and `1`-periodic in `t`.
* `TauCeti.Floer.perturbationPullback_positiveEndChart_stdComplexLineReal_of_le`,
  `TauCeti.Floer.perturbationPullback_positiveEndChart_stdComplexLineImag_of_le`: where a
  perturbation is `H_q(t) dt` on the end `q`, its pullback along the positive end chart is
  `H'_q(t) dt`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4, on the
  cylindrical end coordinates of a punctured Riemann surface.
-/

public section

open Set Real Function MeasureTheory Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- The pair of pants `S = ℂ ∖ {0, 1}`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
@[expose] def thricePuncturedSphereReal : Set (ℝ × ℝ) :=
  {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}

/-- The defining equation of `S` in real coordinates, for rewriting between `S` and the set of
points that are neither `0` nor `1` as complex numbers. -/
theorem thricePuncturedSphereReal_def : thricePuncturedSphereReal =
    {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} :=
  (rfl)

/-- A point lies in `S` when, as a complex number, it is neither `0` nor `1`. -/
@[simp]
theorem mem_thricePuncturedSphereReal_iff {z : ℝ × ℝ} :
    z ∈ thricePuncturedSphereReal ↔
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 :=
  Iff.rfl

/-- The pair of pants is open in real coordinates. -/
theorem isOpen_thricePuncturedSphereReal : IsOpen thricePuncturedSphereReal :=
  (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)

/-- The truncation at heights `R` is compact in real coordinates. -/
theorem isCompact_preimage_truncationAt (R : Puncture → ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncationAt R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncationAt R)

/-- The truncation at heights `R`, in real coordinates, lies in `S`. -/
theorem preimage_truncationAt_subset_thricePuncturedSphereReal (R : Puncture → ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncationAt R ⊆ thricePuncturedSphereReal :=
  fun _ hz ↦ mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncationAt.1 hz).1,
    (mem_truncationAt.1 hz).2.1⟩

/-- In real coordinates, cutting the truncation `S_R` along the circle `±s = c` of the end `q`, for
`c ≤ R`, gives the truncation at the height `c` on `q` and `R` on the other two ends. -/
theorem preimage_truncation_inter_eq_preimage_truncationAt (q : Puncture) {c R : ℝ}
    (hcR : c ≤ R) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c} =
      Complex.equivRealProdCLM.symm ⁻¹' truncationAt (Function.update (fun _ ↦ R) q c) := by
  rw [← truncation_inter_eq_truncationAt q hcR, preimage_inter,
    preimage_ofPred_eq (p := fun w ↦ q.endSign * (q.endCoord w).re ≤ c)]

/-- The truncation `S_R` is compact in real coordinates. -/
theorem isCompact_preimage_truncation (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)

/-- The truncation `S_R`, in real coordinates, lies in `S`. -/
theorem preimage_truncation_subset_thricePuncturedSphereReal (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal :=
  fun _ hz ↦ mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1,
    (mem_truncation.1 hz).2.1⟩

/-- A point of `S` outside the truncation `S_R` lies beyond `R` on some end. -/
theorem exists_lt_endSign_mul_re_endCoord_of_notMem_truncation {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (hzR : Complex.equivRealProdCLM.symm z ∉ truncation R) :
    ∃ q : Puncture, R < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
  by_contra! h
  exact hzR (mem_truncation.2 ⟨(mem_thricePuncturedSphereReal_iff.1 hz).1,
    (mem_thricePuncturedSphereReal_iff.1 hz).2, h⟩)

/-- The integral over `S` of a function vanishing at every point of `S` beyond `R` on some end is
its integral over the truncation `S_R`. -/
theorem setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E} {R : ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ∀ q : Puncture,
      R < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re → f z = 0) :
    ∫ z in thricePuncturedSphereReal, f z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    isOpen_thricePuncturedSphereReal.measurableSet
    (preimage_truncation_subset_thricePuncturedSphereReal R) fun z hz ↦ ?_
  obtain ⟨q, hq⟩ := exists_lt_endSign_mul_re_endCoord_of_notMem_truncation hz.1 hz.2
  exact hf z hz.1 q hq

/-- Almost every point of the plane lies in the pair of pants: the two punctures form a null
set. -/
theorem ae_mem_thricePuncturedSphereReal : ∀ᵐ z : ℝ × ℝ, z ∈ thricePuncturedSphereReal := by
  refine measure_mono_null (t := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1})
    (fun z hz ↦ ?_) ?_
  · rcases not_and_or.1 (mem_thricePuncturedSphereReal_iff.not.1 hz) with h | h
    · exact Or.inl (by rw [← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
    · exact Or.inr (by
        rw [Set.mem_singleton_iff, ← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
  · rw [Measure.volume_eq_prod]
    exact (Set.toFinite _).measure_zero _

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are `Cⁿ`
jointly in the domain and target points, for `Cⁿ` Hamiltonians. -/
theorem contDiffAt_uncurry_pairOfPantsPerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ n (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    ContDiffAt ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (z, x) :=
  ((contDiffAt_pairOfPantsPerturbation_prod hH hHs hz x).comp
    (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are
differentiable in the target point, for `C¹` Hamiltonians. -/
theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x :=
  ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).differentiableAt
    one_ne_zero).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)

section Manifold

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- A perturbation one-form `K` on `ℂ` which is `C¹` at every point of `S × M` has components
`(z, x) ↦ K(z, x)(v)`, in the real coordinates of `S`, that are `C¹` jointly on `S × M`. -/
theorem contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    {K : ℂ → M → ℂ →L[ℝ] ℝ}
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x)) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact (((hK ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (z, x) hφ).clm_apply
    contMDiffAt_const).contMDiffWithinAt

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`, for `C¹` Hamiltonians on a manifold. -/
theorem differentiableAt_pairOfPantsPerturbation_domain {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ pairOfPantsPerturbation H w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_pairOfPantsPerturbation hH hHs
      ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (f := fun w : ℂ ↦ (w, x)) _
      (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- The components of the perturbation are differentiable in the target point, at points
of `S`, for `C¹` Hamiltonians on a manifold. -/
theorem mdifferentiableAt_pairOfPantsPerturbation_target {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  (((contMDiffAt_pairOfPantsPerturbation hH hHs
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp
      (f := fun y : M ↦ (Complex.equivRealProdCLM.symm z, y)) x
      (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply contMDiffAt_const).mdifferentiableAt
    one_ne_zero

end Manifold

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_apply (q : Puncture) (z : ℝ × ℝ) :
    endChart q z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- The end chart is the end lift read in the real coordinates. -/
theorem endChart_eq_realChart (q : Puncture) :
    endChart q = TauCeti.Complex.realChart q.cylindricalEndLift :=
  funext fun z ↦ (TauCeti.Complex.realChart_apply _ z).symm

/-- The end chart at a point `(s, t)` of the cylinder is the end lift at `s + i t`. -/
theorem endChart_mk (q : Puncture) (s t : ℝ) :
    endChart q (s, t) = Complex.equivRealProdCLM (q.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  simp [endChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- The end chart is `1`-periodic in the angular coordinate. -/
theorem endChart_add_one (q : Puncture) (s t : ℝ) :
    endChart q (s, t + 1) = endChart q (s, t) := by
  rw [endChart_mk, endChart_mk]
  exact congrArg Complex.equivRealProdCLM (by exact_mod_cast q.periodic_cylindricalEndLift s t)

/-- In complex coordinates the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart q z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The longitudinal coordinate of the end `q` at the image of `(s, t)` is `s`. -/
theorem re_endCoord_endChart (q : Puncture) (z : ℝ × ℝ) :
    (q.endCoord (Complex.equivRealProdCLM.symm (endChart q z))).re = z.1 := by
  rw [equivRealProdCLM_symm_endChart, re_endCoord_cylindricalEndLift]
  simp [Complex.equivRealProdCLM_symm_apply]

/-- The end chart sends the part `±s > 0` of the end into `S`. -/
theorem endChart_mem_thricePuncturedSphereReal {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) :
    endChart q z ∈ thricePuncturedSphereReal := by
  rw [mem_thricePuncturedSphereReal_iff, equivRealProdCLM_symm_endChart]
  exact cylindricalEndLift_ne_zero_and_ne_one q (by simpa using hz)

/-- The part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates. It
contains the support of the curvature of the end, and the end lift is injective on it. -/
noncomputable def endStrip (q : Puncture) : Set (ℝ × ℝ) :=
  {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2)

theorem endStrip_def (q : Puncture) :
    endStrip q = {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2) :=
  (rfl)

/-- A point lies in the strip of the end `q` when its signed longitudinal coordinate exceeds `1/2`
and its angular coordinate lies in `[-1/2, 1/2)`. -/
@[simp]
theorem mem_endStrip_iff {q : Puncture} {z : ℝ × ℝ} :
    z ∈ endStrip q ↔ 1 / 2 < q.endSign * z.1 ∧ z.2 ∈ Ico (-1 / 2) (1 / 2) :=
  Iff.rfl

/-- Points of the strip of an end have positive signed longitudinal coordinate. -/
theorem endSign_mul_pos_of_mem_endStrip {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ endStrip q) : 0 < q.endSign * z.1 := by
  have h : 1 / 2 < q.endSign * z.1 := hz.1
  linarith

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
theorem hasFDerivAt_endChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt (endChart q)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := ((q.hasDerivAt_cylindricalEndLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

/-- The derivative of the end chart is multiplication by the derivative of the end lift, in real
coordinates. -/
theorem fderiv_endChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ (endChart q) z v = Complex.equivRealProdCLM
      (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
        Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_endChart q z).fderiv]
  simp [mul_comm]

/-- The end charts are holomorphic: their derivatives are complex linear. -/
theorem isComplexLinearMap_fderiv_endChart (q : Puncture) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (endChart q) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_endChart_apply,
    AlmostComplexStructure.product_apply]
  apply Prod.ext <;>
    simp [Complex.equivRealProdCLM_symm_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem contDiff_endChart (q : Puncture) (n : WithTop ℕ∞) : ContDiff ℝ n (endChart q) := by
  exact Complex.equivRealProdCLM.contDiff.comp
    (((q.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff)

/-- **Perturbation data in end coordinates.** Let `K` be a perturbation one-form on `ℂ`, with
`ds` and `dt` components `K(z)(1)` and `K(z)(i)` in the global coordinate `z = s + i t`. Its
pullback along the end chart of `q`, evaluated on a tangent vector `v` of the cylinder, is `K` at
the image point evaluated on the image `φ'(z) v` of `v` under the end lift `φ`. -/
theorem perturbationPullback_endChart_eq_cylindricalEndLift {X : Type*}
    (K : ℂ → X → ℂ →L[ℝ] ℝ) (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun z x ↦ K (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
        (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
          Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, fderiv_endChart_apply, equivRealProdCLM_symm_endChart, hL]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback of the perturbation along the end chart of `q`, evaluated on a tangent vector
`v`, is its component `TauCeti.Floer.pairOfPantsEndComponent` along `v` in the end coordinates. -/
theorem perturbationPullback_endChart (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift (pairOfPantsPerturbation H)]
  funext z x
  rw [pairOfPantsEndComponent_def, Complex.equivRealProdCLM_symm_apply, ← Complex.mk_eq_add_mul_I]

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_t` to
`H_q(t)`. -/
theorem perturbationPullback_endChart_stdComplexLineImag_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ q.endSign * ζ.1) (x : X) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x =
      H q ζ.2 x := by
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  rw [perturbationPullback_endChart_eq_cylindricalEndLift K, hI]
  beta_reduce
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm ζ)
  have hre : (q.endCoord (q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ))).re = ζ.1 := by
    simp [hk]
  rw [hKH q _ x (by rwa [hre]), smul_apply, endAngularForm_cylindricalEndLift,
    hk, smul_eq_mul, Complex.I_im, mul_one]
  simpa using congrFun ((hH q).int_mul k ζ.2) x

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_s` to `0`. -/
theorem perturbationPullback_endChart_stdComplexLineReal_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ q.endSign * ζ.1) (x : X) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ x =
      0 := by
  have h1 : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  rw [perturbationPullback_endChart_eq_cylindricalEndLift K, h1]
  beta_reduce
  have hre : (q.endCoord (q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ))).re = ζ.1 := by
    rw [re_endCoord_cylindricalEndLift]
    simp [Complex.equivRealProdCLM_symm_apply]
  rw [hKH q _ x (by rwa [hre]), smul_apply, endAngularForm_cylindricalEndLift, Complex.one_im,
    smul_zero]

/-- The end chart is injective on every band `ℝ × [t₀, t₀ + 1)` of angular width one: two points
with the same image differ by an integer multiple of `i`. -/
theorem injOn_endChart_univ_prod_Ico (q : Puncture) (t₀ : ℝ) :
    InjOn (endChart q) (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift t₀ (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- The end lift is injective on the strip `endStrip q`, whose angular coordinate ranges over one
period. -/
theorem injOn_endChart (q : Puncture) : InjOn (endChart q) (endStrip q) :=
  (injOn_endChart_univ_prod_Ico q (-1 / 2)).mono (prod_mono (subset_univ _) (by norm_num))

/-- Every point of `S` where some end has signed longitudinal coordinate greater than `1/2` is the
image of a point of that end's strip. -/
theorem mem_image_endChart {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    {q : Puncture} (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endStrip q := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q),
    ContinuousLinearEquiv.apply_symm_apply]

/-- The points of `S` at which the longitudinal coordinate of the end `q` lies in a set `P` of
positive signed values are exactly the images under the end chart of `P × [0, 1)`. -/
theorem image_endChart_prod_Ico {q : Puncture} {P : Set ℝ} (hP : ∀ s ∈ P, 0 < q.endSign * s) :
    endChart q '' (P ×ˢ Ico 0 1) =
      {z | z ∈ thricePuncturedSphereReal ∧
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re ∈ P} := by
  ext z
  constructor
  · rintro ⟨ζ, ⟨hζ, -⟩, rfl⟩
    exact ⟨endChart_mem_thricePuncturedSphereReal (hP _ hζ), by rwa [re_endCoord_endChart]⟩
  · rintro ⟨hz, hzP⟩
    set w := q.endCoord (Complex.equivRealProdCLM.symm z)
    -- Move the angular coordinate into `[0, 1)` by an integer shift.
    refine ⟨(w.re, Int.fract w.im), ⟨hzP, Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have hper := (q.periodic_cylindricalEndLift w.re).sub_int_mul_eq (x := w.im) ⌊w.im⌋
    rw [mul_one] at hper
    rw [endChart_apply, Complex.equivRealProdCLM_symm_apply, Int.fract, hper,
      Complex.re_add_im, q.cylindricalEndLift_endCoord
        (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q),
      ContinuousLinearEquiv.apply_symm_apply]

/-- For `0 ≤ c`, the part `±s > c` of the end `q` in the truncation `S_R` is the image under the
end chart of `c < ±s ≤ R`, `t ∈ [0, 1)`. -/
theorem preimage_truncation_inter_eq_image_endChart (q : Puncture) {c : ℝ} (hc : 0 ≤ c)
    (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | c < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re} =
      endChart q '' ({s : ℝ | c < q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico 0 1) := by
  rw [image_endChart_prod_Ico fun s hs ↦ by linarith [hs.1]]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_truncation, mem_ofPred_eq,
    mem_thricePuncturedSphereReal_iff]
  constructor
  · rintro ⟨⟨h₀, h₁, hR⟩, h⟩
    exact ⟨⟨h₀, h₁⟩, h, hR q⟩
  · rintro ⟨⟨h₀, h₁⟩, h, hR⟩
    refine ⟨⟨h₀, h₁, fun r ↦ ?_⟩, h⟩
    by_cases hr : q = r
    · exact hr ▸ hR
    · linarith [endSign_mul_re_endCoord_nonpos hr (by linarith : 0 < q.endSign *
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re)]

/-- The strip of an end is measurable. -/
theorem measurableSet_endStrip (q : Puncture) : MeasurableSet (endStrip q) := by
  rw [endStrip_def]
  exact (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod
    measurableSet_Ico

/-- The end charts preserve orientation. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (ζ : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (endChart q) ζ).det := by
  rw [endChart_eq_realChart]
  exact TauCeti.Complex.det_fderiv_realChart_nonneg
    (q.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt

/-- The end charts are local diffeomorphisms: their Jacobian determinants are positive. -/
theorem det_fderiv_endChart_pos (q : Puncture) (ζ : ℝ × ℝ) :
    0 < (fderiv ℝ (endChart q) ζ).det := by
  rw [endChart_eq_realChart, TauCeti.Complex.det_fderiv_realChart
    (q.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt]
  exact Complex.normSq_pos.2 (q.deriv_cylindricalEndLift_ne_zero _)

/-- The three end strips have disjoint images. -/
theorem pairwise_disjoint_image_endChart :
    Pairwise (Disjoint on fun q ↦ endChart q '' endStrip q) := by
  intro q r hqr
  refine Set.disjoint_left.2 ?_
  rintro z ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', h⟩
  rw [endChart_apply, endChart_apply] at h
  refine cylindricalEndLift_ne_cylindricalEndLift hqr ?_ ?_
    (Complex.equivRealProdCLM.injective h).symm
  · simpa using endSign_mul_pos_of_mem_endStrip hζ
  · simpa using endSign_mul_pos_of_mem_endStrip hζ'

/-! ### Positive end charts -/

/-- The end chart of `q` read as a positive end: `(s, t) ↦ φ_q(±s, ±t)`, with the sign `±` of the
end, so that `s → ∞` along every end. It is the end chart `TauCeti.Floer.endChart q` on the input
ends, and `(s, t) ↦ φ_∞(-s, -t)` on the output end. -/
noncomputable def positiveEndChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart q (q.endSign • z)

theorem positiveEndChart_apply (q : Puncture) (z : ℝ × ℝ) :
    positiveEndChart q z = endChart q (q.endSign • z) :=
  (rfl)

theorem positiveEndChart_mk (q : Puncture) (s t : ℝ) :
    positiveEndChart q (s, t) = endChart q (q.endSign * s, q.endSign * t) := by
  simp [positiveEndChart_apply]

/-- The end chart at `(±s, t)` is the positive end chart at `(s, ±t)`. -/
theorem endChart_eq_positiveEndChart (q : Puncture) (s t : ℝ) :
    endChart q (q.endSign * s, t) = positiveEndChart q (s, q.endSign * t) := by
  rw [positiveEndChart_mk, ← mul_assoc, endSign_mul_self, one_mul]

/-- The positive end chart is `1`-periodic in the angular coordinate. -/
theorem positiveEndChart_add_one (q : Puncture) (s t : ℝ) :
    positiveEndChart q (s, t + 1) = positiveEndChart q (s, t) := by
  rw [positiveEndChart_mk, positiveEndChart_mk]
  rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> simp only [h, one_mul, neg_one_mul]
  · exact endChart_add_one q s t
  · rw [← endChart_add_one q (-s) (-(t + 1)), neg_add, neg_add_cancel_right]

/-- The derivative of the positive end chart is the derivative of the end chart at the reflected
point, composed with the reflection `v ↦ ±v`. -/
theorem hasFDerivAt_positiveEndChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt (positiveEndChart q)
      ((fderiv ℝ (endChart q) (q.endSign • z)).comp
        (q.endSign • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
  ((contDiff_endChart q 1).differentiable one_ne_zero _).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul q.endSign)

theorem fderiv_positiveEndChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ (positiveEndChart q) z v = q.endSign • fderiv ℝ (endChart q) (q.endSign • z) v := by
  simp [(hasFDerivAt_positiveEndChart q z).fderiv]

theorem contDiff_positiveEndChart (q : Puncture) (n : WithTop ℕ∞) :
    ContDiff ℝ n (positiveEndChart q) :=
  (contDiff_endChart q n).comp (contDiff_const_smul q.endSign)

/-- The positive end charts are holomorphic. -/
theorem isComplexLinearMap_fderiv_positiveEndChart (q : Puncture) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (positiveEndChart q) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  have h := (isComplexLinearMap_iff_apply _ _ _).1 (isComplexLinearMap_fderiv_endChart q
    (q.endSign • z))
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_positiveEndChart_apply] at h ⊢
  rw [h, map_smul]

/-- The positive end charts preserve orientation strictly. -/
theorem det_fderiv_positiveEndChart_pos (q : Puncture) (z : ℝ × ℝ) :
    0 < (fderiv ℝ (positiveEndChart q) z).det := by
  have h : fderiv ℝ (positiveEndChart q) z = q.endSign • fderiv ℝ (endChart q) (q.endSign • z) :=
    ContinuousLinearMap.ext fun v ↦ fderiv_positiveEndChart_apply q z v
  rw [h, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
    Module.finrank_prod, Module.finrank_self, one_add_one_eq_two, sq, endSign_mul_self, one_mul]
  exact det_fderiv_endChart_pos q _

/-- The positive end chart sends the part `s > 0` of the end into `S`. -/
theorem positiveEndChart_mem_thricePuncturedSphereReal {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal := by
  refine endChart_mem_thricePuncturedSphereReal ?_
  simpa [← mul_assoc] using hz

/-- The positive end chart is injective on the open band `ℝ × (0, 1)`. -/
theorem injOn_positiveEndChart (q : Puncture) :
    InjOn (positiveEndChart q) (univ ×ˢ Ioo 0 1) := by
  intro a ha b hb hab
  -- The reflection `v ↦ ±v` moves the band `ℝ × (0, 1)` into a band of width one.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, ∀ c : ℝ × ℝ, c ∈ univ ×ˢ Ioo (0 : ℝ) 1 →
      q.endSign • c ∈ univ ×ˢ Ico t₀ (t₀ + 1) := by
    rcases q.endSign_eq_one_or_eq_neg_one with h | h
    · refine ⟨0, fun c hc ↦ ⟨mem_univ _, ?_, ?_⟩⟩ <;>
        simp only [h, Prod.smul_snd, smul_eq_mul] <;> linarith [hc.2.1, hc.2.2]
    · refine ⟨-1, fun c hc ↦ ⟨mem_univ _, ?_, ?_⟩⟩ <;>
        simp only [h, Prod.smul_snd, smul_eq_mul] <;> linarith [hc.2.1, hc.2.2]
  exact smul_right_injective _ q.endSign_ne_zero
    (injOn_endChart_univ_prod_Ico q t₀ (ht₀ a ha) (ht₀ b hb) hab)

/-- The Hamiltonian of the end `q` in its positive end chart: `H'_q(t, x) = ±H_q(±t, x)` with the
sign of the end. It is `H_q` on the input ends and `(t, x) ↦ -H_∞(-t, x)` on the output end. -/
noncomputable def positiveEndHamiltonian {X : Type*} (H : Puncture → ℝ → X → ℝ) (q : Puncture)
    (t : ℝ) (x : X) : ℝ :=
  q.endSign * H q (q.endSign * t) x

theorem positiveEndHamiltonian_apply {X : Type*} (H : Puncture → ℝ → X → ℝ) (q : Puncture)
    (t : ℝ) (x : X) : positiveEndHamiltonian H q t x = q.endSign * H q (q.endSign * t) x :=
  (rfl)

theorem periodic_positiveEndHamiltonian {X : Type*} {H : Puncture → ℝ → X → ℝ} {q : Puncture}
    (hH : Periodic (H q) 1) : Periodic (positiveEndHamiltonian H q) 1 := by
  intro t
  funext x
  rcases q.endSign_eq_one_or_eq_neg_one with h | h <;>
    simp only [positiveEndHamiltonian_apply, h, mul_add, mul_one, one_mul, neg_one_mul,
      ← sub_eq_add_neg, hH.sub_eq, hH _]

theorem contDiff_uncurry_positiveEndHamiltonian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Puncture → ℝ → E → ℝ} {q : Puncture} {n : WithTop ℕ∞}
    (hH : ContDiff ℝ n (uncurry (H q))) : ContDiff ℝ n (uncurry (positiveEndHamiltonian H q)) :=
  contDiff_const.mul (hH.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))

/-- A `1`-periodic loop read with the time `±t` of an end is `1`-periodic. -/
theorem periodic_comp_endSign_mul {α : Type*} {q : Puncture} {x : ℝ → α} (hx : Periodic x 1) :
    Periodic (fun t ↦ x (q.endSign * t)) 1 := by
  have h := hx.const_mul q.endSign
  rw [inv_endSign, mul_one] at h
  rcases q.endSign_eq_one_or_eq_neg_one with hσ | hσ
  · simpa only [hσ] using h
  · simpa only [hσ, neg_neg] using h.neg

/-- The pullback of a perturbation along the positive end chart is the pullback along the end
chart at the reflected point, multiplied by the sign of the end. -/
theorem perturbationPullback_positiveEndChart {X : Type*} {K : ℂ → X → ℂ →L[ℝ] ℝ} (q : Puncture)
    (v ζ : ℝ × ℝ) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ x =
      q.endSign * perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v (q.endSign • ζ) x := by
  simp only [perturbationPullback_apply, fderiv_positiveEndChart_apply, positiveEndChart_apply,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the positive end chart sends `∂_s`
to `0`. -/
theorem perturbationPullback_positiveEndChart_stdComplexLineReal_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ x =
      0 := by
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_stdComplexLineReal_of_le hKH (by simpa [← mul_assoc] using hζ),
    mul_zero]

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the positive end chart sends `∂_t`
to the end Hamiltonian `H'_q(t)` of the positive end. -/
theorem perturbationPullback_positiveEndChart_stdComplexLineImag_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x =
      positiveEndHamiltonian H q ζ.2 x := by
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_stdComplexLineImag_of_le hKH hH
      (by simpa [← mul_assoc] using hζ), positiveEndHamiltonian_apply, Prod.smul_snd, smul_eq_mul]

end Floer

end TauCeti
