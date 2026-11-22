/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral
public import TauCeti.Analysis.Complex.RealChart
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Complex.RootsOfUnity.Sector
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Conformal invariance and degree scaling of the energy

The energy of a map from a surface depends on a metric on the domain only through its conformal
class. In a domain coordinate the energy density of a differential `F` is
`ω(F ∂s, J F ∂s) + ω(F ∂t, J F ∂t)`; for a compatible pair this is `|F ∂s|² + |F ∂t|²` in the
metric `g = ω(·, J ·)`, and the energy is the usual `(1 / 2) ∫ |du|²` measured in `g`. The
energy `TauCeti.SymplecticForm.stdComplexLineEnergy` integrates the positive part of half the
density, which is half the density itself once `ω` tames `J`. The invariance is the following
computation. A real-linear map `L` of the standard complex line `ℝ × ℝ` which is complex linear
is multiplication by a complex number `a + b i`, so it rotates and scales by `√(a² + b²)`; its
determinant is `a² + b²` (`TauCeti.IsComplexLinearMap.det_eq_sq_add_sq`). Precomposing `F` by
`L` therefore multiplies the energy density by `a² + b² = det L`
(`TauCeti.SymplecticForm.stdComplexLineEnergyDensity_comp_of_isComplexLinearMap`), with no
hypothesis relating the symplectic form and the almost complex structure.

For a change of domain coordinates `φ` whose derivative is complex linear, a holomorphic one,
the density of the reparametrized differential `du (φ x) ∘ dφ_x` is the Jacobian `det dφ_x`
times the density of `du` at `φ x`. The change of variables formula then shows that the energy
over `φ '' s` equals the energy of the pullback over `s`, whenever `φ` is injective on `s`
(`TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_image`, and
`TauCeti.SymplecticForm.fderiv_stdComplexLineEnergy_restrict_image` for differentials of maps).
This is the invariance of the energy under holomorphic changes of chart, which makes the energy
of a map from a Riemann surface independent of the charts used to compute it.

Without injectivity a holomorphic map counts its sheets. If `s` is covered, up to a null set, by
`n` disjoint measurable pieces on each of which `φ` is injective with image `t` up to a null set,
then the energy of the pullback over `s` is `n` times the energy over `t`
(`TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_eq_card_smul`). For the local model of a
branched cover, `z ↦ z ^ d` in real coordinates, the sheets are the sectors of
`TauCeti.exists_pairwise_disjoint_injOn_pow_image_eq_slitPlane`, and precomposition with
`z ↦ z ^ d` multiplies the energy by `d`: the energy of the pullback over the preimage of any
measurable set `t` is `d` times the energy over `t`
(`TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_preimage_realChart_pow`).

## Main results

* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_comp_of_isComplexLinearMap`: precomposition
  with a complex-linear `L` multiplies the energy density by `det L`.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_image`: invariance of the energy under
  injective holomorphic changes of coordinates.
* `TauCeti.SymplecticForm.fderiv_stdComplexLineEnergy_restrict_image`: the same for the
  differentials of a map and of its reparametrization.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_eq_card_smul`: a holomorphic map with `n`
  sheets multiplies the energy by `n`.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_restrict_preimage_realChart_pow`: precomposition with
  `z ↦ z ^ d` multiplies the energy by `d`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.2 (the energy of a map from a Riemann surface
  depends only on the conformal structure of the domain).
-/

public section

open Function MeasureTheory Set
open TauCeti.Complex (realChart)

namespace TauCeti

namespace SymplecticForm

section Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}

/-- **Transformation of the energy density under complex-linear maps.** Precomposing a
differential `F` with a complex-linear endomorphism `L` of the standard complex line multiplies
its energy density by `det L`. No relation between `ω` and `J` is needed. -/
theorem stdComplexLineEnergyDensity_comp_of_isComplexLinearMap {L : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ}
    (hL : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) L)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergyDensity J (F ∘ₗ L) =
      LinearMap.det L * ω.stdComplexLineEnergyDensity J F := by
  rw [hL.det_eq_sq_add_sq]
  -- `L` is multiplication by `a + b i`, sending `∂s` to `a ∂s + b ∂t` and `∂t` to `-b ∂s + a ∂t`.
  set a := (L stdComplexLineReal).1
  set b := (L stdComplexLineReal).2
  have hs : L stdComplexLineReal = a • stdComplexLineReal + b • stdComplexLineImag :=
    stdComplexLine_eq_smul_real_add_smul_imag _
  have ht : L stdComplexLineImag = (-b) • stdComplexLineReal + a • stdComplexLineImag := by
    rw [hL.apply_stdComplexLineImag, AlmostComplexStructure.product_apply]
    ext <;> simp [a, b, stdComplexLineReal, stdComplexLineImag]
  rw [stdComplexLineEnergyDensity_def, stdComplexLineEnergyDensity_def,
    LinearMap.comp_apply, LinearMap.comp_apply, ht, hs]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

end Pointwise

section Integral

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {φ : ℝ × ℝ → ℝ × ℝ} {s t : Set (ℝ × ℝ)}

/-- **Invariance of the energy under holomorphic changes of coordinates.** If `φ` is injective
and differentiable on a measurable set `s`, with complex-linear derivative, then the energy of a
differential field `du` over `φ '' s` is the energy of its pullback `du (φ x) ∘ dφ_x` over `s`. -/
theorem stdComplexLineEnergy_restrict_image (hs : MeasurableSet s) (hinj : InjOn φ s)
    (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x)
    (hhol : ∀ x ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
    (du : ℝ × ℝ → (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergy J du (volume.restrict (φ '' s)) =
      ω.stdComplexLineEnergy J (fun x ↦ du (φ x) ∘ₗ (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
        (volume.restrict s) := by
  rw [stdComplexLineEnergy_def, stdComplexLineEnergy_def]
  refine lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hs hinj hφ fun x hx ↦ ?_
  rw [stdComplexLineEnergyDensity_comp_of_isComplexLinearMap (hhol x hx), mul_div_assoc,
    ContinuousLinearMap.det, abs_of_nonneg (hhol x hx).det_nonneg]

/-- **Degree scaling of the energy.** Suppose that, up to a null set, a measurable set `s` is the
disjoint union of `n` measurable pieces `S i`, and that the holomorphic map `φ` is injective on
each piece with image `t` up to a null set. Then the energy of the pullback `du (φ x) ∘ dφ_x`
over `s` is `n` times the energy of `du` over `t`: each sheet of `φ` contributes one copy. -/
theorem stdComplexLineEnergy_restrict_eq_card_smul {ι : Type*} [Fintype ι]
    {S : ι → Set (ℝ × ℝ)} (hS : ∀ i, MeasurableSet (S i)) (hdisj : Pairwise (Disjoint on S))
    (hcover : (⋃ i, S i : Set (ℝ × ℝ)) =ᵐ[volume] s) (hinj : ∀ i, InjOn φ (S i))
    (himage : ∀ i, φ '' S i =ᵐ[volume] t) (hφ : ∀ i, ∀ x ∈ S i, DifferentiableAt ℝ φ x)
    (hhol : ∀ i, ∀ x ∈ S i, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
    (du : ℝ × ℝ → (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergy J (fun x ↦ du (φ x) ∘ₗ (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
        (volume.restrict s) =
      Fintype.card ι • ω.stdComplexLineEnergy J du (volume.restrict t) := by
  have hpiece (i : ι) :
      ∫⁻ x in S i, ENNReal.ofReal (ω.stdComplexLineEnergyDensity J
        (du (φ x) ∘ₗ (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) / 2) =
        ω.stdComplexLineEnergy J du (volume.restrict t) := by
    rw [← stdComplexLineEnergy_def, ← stdComplexLineEnergy_restrict_image (hS i) (hinj i) (hφ i)
      (hhol i), Measure.restrict_congr_set (himage i)]
  rw [← Measure.restrict_congr_set hcover, stdComplexLineEnergy_def, lintegral_iUnion hS hdisj,
    tsum_fintype]
  simp only [hpiece, Finset.sum_const, Finset.card_univ]

/-- **Precomposition with `z ↦ z ^ d` multiplies the energy by `d`.** For every measurable set `t`
in the real coordinates of `ℂ`, the energy of the pullback of a differential field `du` along
the real chart of `z ↦ z ^ d` over the preimage of `t` is `d` times the energy of `du` over `t`.
For `d = 0` both sides vanish, since the pulled back field is zero. -/
theorem stdComplexLineEnergy_restrict_preimage_realChart_pow (d : ℕ) (ht : MeasurableSet t)
    (du : ℝ × ℝ → (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergy J (fun z ↦ du (realChart (· ^ d) z) ∘ₗ
        (fderiv ℝ (realChart (· ^ d)) z : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
        (volume.restrict (realChart (· ^ d) ⁻¹' t)) =
      d • ω.stdComplexLineEnergy J du (volume.restrict t) := by
  set e := Complex.equivRealProdCLM
  have hderiv (z : ℝ × ℝ) : HasDerivAt (· ^ d) (d * e.symm z ^ (d - 1)) (e.symm z) := by
    simpa using hasDerivAt_pow d (e.symm z)
  rcases eq_or_ne d 0 with rfl | hd
  · -- For `d = 0` the map is constant, so its derivative and the pulled back field vanish.
    have hzero (z : ℝ × ℝ) : (fderiv ℝ (realChart (· ^ 0)) z : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) = 0 := by
      refine LinearMap.ext fun v ↦ ?_
      rw [ContinuousLinearMap.coe_coe, Complex.fderiv_realChart_apply (hderiv z)]
      simp
    simp only [hzero, LinearMap.comp_zero, stdComplexLineEnergy_zero, zero_smul]
  obtain ⟨S, hSm, hdisj, hinj, himage, hcover⟩ :=
    exists_pairwise_disjoint_injOn_pow_image_eq_slitPlane hd
  -- Points whose real coordinates avoid a null set of `ℂ` form a conull set of `ℝ × ℝ`.
  have hnull {N : Set ℂ} (hN : volume N = 0) : volume (e.symm ⁻¹' N) = 0 :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.preimage_null hN
  have hcont : Continuous (realChart (· ^ d)) := (Complex.contDiff_realChart (contDiff_id.pow d)
    (n := 0)).continuous
  let T : Fin d → Set (ℝ × ℝ) := fun k ↦ e.symm ⁻¹' S k ∩ realChart (· ^ d) ⁻¹' t
  have hT (k : Fin d) : realChart (· ^ d) '' T k = e.symm ⁻¹' Complex.slitPlane ∩ t := by
    rw [image_inter_preimage, Complex.image_realChart_preimage, himage k]
  refine (stdComplexLineEnergy_restrict_eq_card_smul (S := T) (t := t) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    du).trans (by rw [Fintype.card_fin])
  · exact fun k ↦ (e.symm.continuous.measurable (hSm k)).inter (hcont.measurable ht)
  · exact fun i j hij ↦ ((hdisj hij).preimage e.symm).mono inter_subset_left inter_subset_left
  · -- The pieces cover the preimage of `t` up to the points `z` with `z ^ d ∉ slitPlane`.
    rw [← iUnion_inter, ← preimage_iUnion]
    refine inter_ae_eq_right_of_ae_eq_univ (ae_eq_univ.2 (measure_mono_null ?_
      (hnull (volume_setOf_pow_notMem_slitPlane d))))
    intro z hz
    exact fun hzd ↦ hz (mem_preimage.2 (hcover hzd))
  · exact fun k ↦ Complex.injOn_realChart ((hinj k).mono
      (image_subset_iff.2 fun z hz ↦ hz.1))
  · -- The image misses only the points of `t` off the slit plane.
    refine fun k ↦ (hT k).symm ▸ inter_ae_eq_right_of_ae_eq_univ (ae_eq_univ.2 ?_)
    refine measure_mono_null (fun z hz ↦ ?_) (hnull (volume_setOf_pow_notMem_slitPlane 1))
    simpa using hz
  · exact fun k z _ ↦ (Complex.hasFDerivAt_realChart (hderiv z)).differentiableAt
  · exact fun k z _ ↦ isComplexLinearMap_fderiv_realChart (hderiv z)

end Integral

section Differentiable

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {φ : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {u : ℝ × ℝ → V}

/-- **Invariance of the energy of a map under holomorphic reparametrization.** If `φ` is
injective and differentiable on a measurable set `s`, with complex-linear derivative, and `u` is
differentiable on `φ '' s`, then the energy of `u` over `φ '' s` is the energy of `u ∘ φ` over
`s`. -/
theorem fderiv_stdComplexLineEnergy_restrict_image (hs : MeasurableSet s) (hinj : InjOn φ s)
    (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x)
    (hhol : ∀ x ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ x ∈ s, DifferentiableAt ℝ u (φ x)) :
    ω.stdComplexLineEnergy J (fun z ↦ (fderiv ℝ u z : (ℝ × ℝ) →ₗ[ℝ] V))
        (volume.restrict (φ '' s)) =
      ω.stdComplexLineEnergy J (fun x ↦ (fderiv ℝ (u ∘ φ) x : (ℝ × ℝ) →ₗ[ℝ] V))
        (volume.restrict s) := by
  rw [stdComplexLineEnergy_restrict_image hs hinj hφ hhol]
  refine stdComplexLineEnergy_congr_ae (ae_restrict_of_forall_mem hs fun x hx ↦ ?_)
  simp only [fderiv_comp x (hu x hx) (hφ x hx), ContinuousLinearMap.toLinearMap_comp]

end Differentiable

end SymplecticForm

end TauCeti
