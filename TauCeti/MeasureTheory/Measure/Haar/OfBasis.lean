/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The additive Haar measure of the standard basis

The additive Haar measure attached to a basis gives measure one to the parallelepiped the basis
spans. For the standard basis of `ι → ℝ` that parallelepiped is the unit cube, so the measure is
product Lebesgue measure. A general change of basis rescales its normalized Haar measure
by the inverse absolute determinant.

## Main results

* `Module.Basis.addHaar_basisFun` — the additive Haar measure of `Pi.basisFun ℝ ι` is `volume`.
* `Module.Basis.addHaar_singleton`, `Module.Basis.addHaar_finTwoProd` — the additive Haar measures
  of the standard bases of `ℝ` and `ℝ × ℝ` are `volume`.
* `Module.Basis.addHaar_eq_dirac` — the additive Haar measure of a basis indexed by an empty type
  is the Dirac mass at `0`.
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

end Module.Basis

end
