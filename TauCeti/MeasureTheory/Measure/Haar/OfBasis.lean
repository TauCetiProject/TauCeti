/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The additive Haar measure of the standard basis

The additive Haar measure attached to a basis gives measure one to the parallelepiped the basis
spans. For the standard basis of `ι → ℝ` that parallelepiped is the unit cube, so the measure is
product Lebesgue measure. A general change of basis rescales its normalized Haar measure
by the inverse absolute determinant, while the linear equivalence sending one basis to another
carries the normalized Haar measure of the first to that of the second.

## Main results

* `Module.Basis.addHaar_basisFun` — the additive Haar measure of `Pi.basisFun ℝ ι` is `volume`.
* `Module.Basis.addHaar_singleton`, `Module.Basis.addHaar_finTwoProd` — the additive Haar measures
  of the standard bases of `ℝ` and `ℝ × ℝ` are `volume`.
* `Complex.addHaar_basisOneI` — the additive Haar measure of the basis `(1, i)` of `ℂ` is
  `volume`.
* `Module.Basis.addHaar_eq_dirac` — the additive Haar measure of a basis indexed by an empty type
  is the Dirac mass at `0`.
* `Module.Basis.addHaar_eq_smul_of_basis` — change of basis rescales `b.addHaar` by `|det|⁻¹`.
* `Module.Basis.integral_addHaar_congr_measurableSpace` and
  `Module.Basis.setIntegral_addHaar_congr_measurableSpace` — Bochner (set) integrals against
  `b.addHaar` are independent of the choice of `BorelSpace` measurable-space instance.
* `Module.Basis.measurePreserving_equiv` — the linear equivalence matching two bases carries the
  additive Haar measure of one to that of the other.

## Attribution

`Module.Basis.measurePreserving_equiv` is adapted from the measure-preservation lemma for the chart
coordinate change in
[TauCetiProject/TauCeti#40536](https://github.com/TauCetiProject/TauCeti/pull/40536).
-/

public section

open MeasureTheory

namespace Module.Basis

/-- The additive Haar measure attached to the standard basis of `ι → ℝ` is product Lebesgue
measure, because the basis parallelepiped is the unit cube. -/
theorem addHaar_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [addHaar_def, parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]

/-- The additive Haar measure attached to the standard basis of `ℝ`, indexed by any type with
exactly one element, is Lebesgue measure.

The `Fintype ι` instance is a separate argument, rather than the one derived from `Unique ι`, so
that the lemma rewrites `addHaar` whatever finiteness instance it carries (e.g. `Fin.fintype 1`). -/
@[simp]
theorem addHaar_singleton {ι : Type*} [Fintype ι] [Unique ι] :
    (Basis.singleton ι ℝ).addHaar = volume := by
  -- `addHaar` depends on the `Fintype` instance only up to `Subsingleton (Fintype ι)`.
  obtain rfl : ‹Fintype ι› = Unique.fintype := Subsingleton.elim _ _
  rw [← OrthonormalBasis.toBasis_singleton]
  exact OrthonormalBasis.addHaar_eq_volume _

/-- The additive Haar measure attached to the standard basis `((1, 0), (0, 1))` of `ℝ × ℝ` is
Lebesgue measure. -/
theorem addHaar_finTwoProd : (Basis.finTwoProd ℝ).addHaar = volume := by
  have h : ((Basis.singleton (Fin 1) ℝ).prod (Basis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv = Basis.finTwoProd ℝ :=
    Basis.eq_of_apply_eq (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  rw [← h, addHaar_reindex, prod_addHaar, addHaar_singleton, Measure.volume_eq_prod]

/-- The normalized Haar measure of a basis indexed by an empty type is the Dirac mass at the
origin of the (zero) space. -/
@[simp]
theorem addHaar_eq_dirac {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [Fintype ι] [IsEmpty ι]
    (b : Basis ι ℝ V) : b.addHaar = Measure.dirac 0 := by
  have : Subsingleton V := b.equivFun.injective.subsingleton
  have hp : _root_.parallelepiped b = Set.univ := Set.Nonempty.eq_univ
    ⟨0, (mem_parallelepiped_iff _ _).2 ⟨0, by simp, Subsingleton.elim _ _⟩⟩
  ext s -
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [hs.eq_univ, Measure.dirac_apply_of_mem (Set.mem_univ 0), ← hp, addHaar_self]

section ChangeBasis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

/-- A change of basis rescales its normalized Haar measure by the inverse absolute determinant. -/
theorem addHaar_eq_smul_of_basis (b b' : Basis ι ℝ E) :
    b'.addHaar = ENNReal.ofReal |(b.det b')⁻¹| • b.addHaar := by
  have := b.finiteDimensional_of_finite
  let e : E ≃ₗ[ℝ] E := b.equiv b' (Equiv.refl ι)
  have hmap : b.map e = b' := by
    ext i
    simp [e]
  have hdet : e.toLinearMap.det = b.det b' := by
    simpa only [e] using det_basis b' b
  calc
    b'.addHaar = Measure.map e.toContinuousLinearEquiv b.addHaar := by
      rw [b.map_addHaar, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, hmap]
    _ = _ := by
      simpa only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_coe, hdet] using
        Measure.map_linearMap_addHaar_eq_smul_addHaar b.addHaar e.isUnit_det'.ne_zero

end ChangeBasis

section MeasurableSpace

variable {E ι F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Bochner integral against `b.addHaar` does not depend on the choice of `BorelSpace`
measurable-space instance on `E`. -/
theorem integral_addHaar_congr_measurableSpace (b : Basis ι ℝ E) (ms₁ ms₂ : MeasurableSpace E)
    (hb₁ : @BorelSpace E _ ms₁) (hb₂ : @BorelSpace E _ ms₂) (g : E → F) :
    ∫ z, g z ∂(@Basis.addHaar _ _ _ _ _ ms₁ hb₁ b) =
      ∫ z, g z ∂(@Basis.addHaar _ _ _ _ _ ms₂ hb₂ b) := by
  obtain rfl : ms₁ = ms₂ := hb₁.measurable_eq.trans hb₂.measurable_eq.symm; rfl

/-- The Bochner set integral against `b.addHaar` does not depend on the choice of `BorelSpace`
measurable-space instance on `E`. -/
theorem setIntegral_addHaar_congr_measurableSpace (b : Basis ι ℝ E) (ms₁ ms₂ : MeasurableSpace E)
    (hb₁ : @BorelSpace E _ ms₁) (hb₂ : @BorelSpace E _ ms₂) (s : Set E) (g : E → F) :
    ∫ z in s, g z ∂(@Basis.addHaar _ _ _ _ _ ms₁ hb₁ b) =
      ∫ z in s, g z ∂(@Basis.addHaar _ _ _ _ _ ms₂ hb₂ b) := by
  obtain rfl : ms₁ = ms₂ := hb₁.measurable_eq.trans hb₂.measurable_eq.symm; rfl

end MeasurableSpace

section Equiv

variable {E F ι ι' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [Fintype ι] [Fintype ι']

/-- The linear equivalence `b.equiv b' e` sending each vector of a basis `b` to the corresponding
vector of a basis `b'` carries the normalized Haar measure of `b` to that of `b'`. -/
theorem measurePreserving_equiv (b : Basis ι ℝ E) (b' : Basis ι' ℝ F) (e : ι ≃ ι') :
    MeasurePreserving (b.equiv b' e) b.addHaar b'.addHaar := by
  have := b.finiteDimensional_of_finite
  have := b'.finiteDimensional_of_finite
  have hmap : b.map (b.equiv b' e) = b'.reindex e.symm := by
    ext i
    simp
  refine ⟨(b.equiv b' e).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  rw [← LinearEquiv.coe_toContinuousLinearEquiv', b.map_addHaar,
    LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, hmap, addHaar_reindex]

end Equiv

end Module.Basis

/-- The additive Haar measure attached to the basis `(1, i)` of `ℂ` is Lebesgue measure. -/
theorem Complex.addHaar_basisOneI : Complex.basisOneI.addHaar = (volume : Measure ℂ) := by
  rw [← Complex.toBasis_orthonormalBasisOneI]
  exact Complex.orthonormalBasisOneI.addHaar_eq_volume

end
