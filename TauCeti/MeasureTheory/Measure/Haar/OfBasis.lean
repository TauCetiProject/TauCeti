/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod

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
* `Module.Basis.addHaar_withDensity_eq_of_eq_abs_det_mul` — Haar measures weighted by densities
  that scale by the absolute determinant of a change of basis agree.
* `Module.Basis.setLIntegral_prod_of_addHaar_withDensity_eq` — a weighted Haar integral over a
  product set whose density factors in a product basis is the product of the factor integrals.
* `Module.Basis.measurePreserving_equiv` — the linear equivalence matching two bases carries the
  additive Haar measure of one to that of the other.
* `ContinuousLinearEquiv.exists_map_restrict_preimage_eq_smul_addHaar` — a continuous linear
  equivalence onto a finite-dimensional space maps an additive Haar measure, restricted to
  preimages, to a fixed positive multiple of the restricted Haar measure of `Module.finBasis`.

## Attribution

`Module.Basis.measurePreserving_equiv` is adapted from the measure-preservation lemma for the chart
coordinate change in
[TauCetiProject/TauCeti#40536](https://github.com/TauCetiProject/TauCeti/pull/40536).
-/

public section

open MeasureTheory
open scoped ENNReal

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

/-- **Densities that scale like a change of basis give the same weighted Haar measure.** If the
density `f` used with the Haar measure of `b'` is the density `g` used with the Haar measure of
`b`, multiplied by the absolute determinant of the change of basis, then the two weighted measures
agree: the change of basis rescales the Haar measure by the inverse factor. -/
theorem addHaar_withDensity_eq_of_eq_abs_det_mul (b b' : Basis ι ℝ E) {f g : E → ℝ≥0∞}
    (hfg : ∀ x, f x = ENNReal.ofReal |b.det b'| * g x) :
    b'.addHaar.withDensity f = b.addHaar.withDensity g := by
  have hd : ENNReal.ofReal |(b.det b')⁻¹| * ENNReal.ofReal |b.det b'| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel₀ (b.isUnit_det b').ne_zero,
      abs_one, ENNReal.ofReal_one]
  have hf : f = ENNReal.ofReal |b.det b'| • g := funext hfg
  rw [addHaar_eq_smul_of_basis b b', withDensity_smul_measure, hf,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul, hd, one_smul]

end ChangeBasis

section Prod

variable {E F ι ι' κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [Fintype ι] [Fintype ι'] [Fintype κ]

/-- **Weighted Haar integrals over product sets.** Suppose the Haar measure of a basis `b₀` of
`E × F` weighted by `D₀` is the Haar measure of the product basis of `b₁` and `b₂`, reindexed
along `e`, weighted by `D`. If `D` factors on `A₁ ×ˢ A₂` as `f z.1 * g z.2`, then the integral of
`D₀` over `A₁ ×ˢ A₂` is the product of the integrals of `f` and `g`, since the Haar measure of a
product basis is the product of the Haar measures. The Borel structure on `E × F` is arbitrary,
so this applies to the chart measurable structure of a manifold model space. -/
theorem setLIntegral_prod_of_addHaar_withDensity_eq [mEF : MeasurableSpace (E × F)]
    [BorelSpace (E × F)] (e : ι ⊕ ι' ≃ κ) (b₀ : Basis κ ℝ (E × F)) (b₁ : Basis ι ℝ E)
    (b₂ : Basis ι' ℝ F) {A₁ : Set E} {A₂ : Set F} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) {D₀ D : E × F → ℝ≥0∞} {f : E → ℝ≥0∞} {g : F → ℝ≥0∞}
    (hD : b₀.addHaar.withDensity D₀ = ((b₁.prod b₂).reindex e).addHaar.withDensity D)
    (hf : AEMeasurable f (b₁.addHaar.restrict A₁)) (hg : AEMeasurable g (b₂.addHaar.restrict A₂))
    (hfg : ∀ z ∈ A₁ ×ˢ A₂, D z = f z.1 * g z.2) :
    ∫⁻ z in A₁ ×ˢ A₂, D₀ z ∂b₀.addHaar =
      (∫⁻ x in A₁, f x ∂b₁.addHaar) * ∫⁻ y in A₂, g y ∂b₂.addHaar := by
  have : FiniteDimensional ℝ F := b₂.finiteDimensional_of_finite
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans (Prod.borelSpace (α := E) (β := F)).measurable_eq.symm
  rw [← withDensity_apply _ (hA₁.prod hA₂), hD, withDensity_apply _ (hA₁.prod hA₂),
    setLIntegral_congr_fun (hA₁.prod hA₂) hfg, addHaar_reindex, prod_addHaar,
    ← Measure.prod_restrict, lintegral_prod_mul hf hg]

end Prod


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

/-- A continuous linear equivalence `L` onto a finite-dimensional space `E` maps an additive Haar
measure `μ`, restricted to the preimage of a set `s`, to a fixed positive multiple of the Haar
measure of `Module.finBasis ℝ E` restricted to `s`. -/
theorem ContinuousLinearEquiv.exists_map_restrict_preimage_eq_smul_addHaar
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (L : F ≃L[ℝ] E) (μ : Measure F) [μ.IsAddHaarMeasure] :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ s : Set E,
      (μ.restrict (L ⁻¹' s)).map L = c • (Module.finBasis ℝ E).addHaar.restrict s := by
  refine ⟨Measure.addHaarScalarFactor (μ.map L) (Module.finBasis ℝ E).addHaar,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun s ↦ ?_⟩
  rw [← Measure.restrict_smul, ← Measure.isAddLeftInvariant_eq_smul]
  exact (L.toHomeomorph.toMeasurableEquiv.restrict_map μ s).symm

/-- The additive Haar measure attached to the basis `(1, i)` of `ℂ` is Lebesgue measure. -/
theorem Complex.addHaar_basisOneI : Complex.basisOneI.addHaar = (volume : Measure ℂ) := by
  rw [← Complex.toBasis_orthonormalBasisOneI]
  exact Complex.orthonormalBasisOneI.addHaar_eq_volume

end
