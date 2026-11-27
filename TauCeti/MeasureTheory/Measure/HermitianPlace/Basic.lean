/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Instances.Matrix
import TauCeti.MeasureTheory.Group.MeasurableEquiv

/-!
# Places for hermitian analysis

A *place* is the local ring over which hermitian forms are analysed: a commutative ring `A` with
an involution `star` and a Haar measure `volume`, together with the data that
measure theory on quadrics of a hermitian form and Fourier analysis on `A^ι` need. The data are

* an element `τ` with `τ + star τ = 1`, and a unit `δ` with `star δ = -δ`; for a skew element
  `β` the element `δ⁻¹β` is self-adjoint, so `δ⁻¹` identifies skew elements with values of hermitian
  forms;
* a Haar measure `ν` on the additive group `A⁻` of skew elements, normalised so that
  `(a, b) ↦ τδ⁻¹a + b` carries `ν × ν` to `volume`;
* a multiplicative *modulus* `mod : Aˣ → [0, ∞)` on the units, invariant under the involution,
  such that every matrix `M` with unit determinant scales Haar measure of `A^n` by
  `mod (det M)⁻¹`;
* a continuous additive character `ψ : A → 𝕊¹`, and a *Plancherel constant* `c ∈ [0, ∞]` bounding
  the `L¹` norm of the transform `w ↦ ∫ G(v) ψ(star v * w) dv` of some continuous integrable damping
  kernel `G ≥ 0` with `G(0) = 1`;

and almost every element of `A` is a unit, with `mod(u)⁻¹ ≤ |g(u)|²` on units for a locally
integrable `g`. The complex numbers with complex conjugation are a place
(`TauCeti.HermitianPlace.complex`), but nothing in the definition is specific to `ℂ`: the same
data make sense at non-archimedean places.

The structure only records the data and their laws. The topological hypotheses on `A` (a locally
compact, second countable topological ring with continuous involution, whose `volume` is an
additive Haar measure) are typeclass assumptions of the results that use them.

## Main definitions

* `TauCeti.HermitianPlace A`: a place structure on `A`.

## Main results

* `TauCeti.HermitianPlace.modulus_ne_zero`, `TauCeti.HermitianPlace.modulus_neg`: the modulus
  of a unit is a positive real number, and the modulus is even.
* `TauCeti.HermitianPlace.map_mulVec_volume`: a matrix with unit determinant, on `A^ι` for any
  finite type `ι`, scales Haar measure by the inverse modulus of its determinant.
* `TauCeti.HermitianPlace.lintegral_comp_smul`, `TauCeti.HermitianPlace.integral_comp_smul`,
  `TauCeti.HermitianPlace.integrable_comp_smul`: the change of variables `v ↦ u • v` on `A^ι` for
  a unit `u`.
* `TauCeti.HermitianPlace.exists_seq_units_tendsto_zero`: there is a sequence of units tending
  to `0`.

## References

* A. Weil, *Basic Number Theory*, 3rd ed., Springer (1974), Chapters I and II: Haar
  measure on locally compact rings and the modulus of an automorphism.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory* (1967): additive characters and self-dual measures
  at a place.

The structure follows the definition of a place in the Lean project grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), declaration
`New.Floors.Place` in `src/Lib/General/Measure/QuadricDisintegration.lean`.
-/

public section

open MeasureTheory Matrix Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace TauCeti

/-- A **place**: a commutative ring `A` with involution `star` and a measure `volume` (an
additive Haar measure in every application), with the data of hermitian analysis over `A`.

* `τ` satisfies `τ + star τ = 1`, and the unit `δ` satisfies `star δ = -δ`.
* `ν` is a Haar measure on the skew elements such that `(a, b) ↦ τδ⁻¹a + b` carries `ν × ν`
  to `volume`.
* `modulus` is a measurable multiplicative map `Aˣ → [0, ∞)` invariant under `star`, such that
  for every `n` and every `n × n` matrix `M` whose determinant is a unit `u`, `x ↦ Mx` carries
  Haar measure of `A^n` to `modulus u⁻¹` times itself. It is defined on the units only, since
  only their moduli enter the theory.
* `ψ` is a continuous additive character with values in the unit circle.
* `plancherelConst` bounds `∫ |∫ G(v) ψ(star v * w) dv| dw` for some continuous integrable
  `G ≥ 0` with `G(0) = 1`.
* Almost every element of `A` is a unit, and `modulus u⁻¹ ≤ |g(u)|²` on units for some locally
  integrable `g`. -/
structure HermitianPlace (A : Type*) [CommRing A] [StarRing A] [TopologicalSpace A]
    [MeasureSpace A] where
  /-- An element with `τ + star τ = 1`. -/
  τ : A
  τ_add_star : τ + star τ = 1
  /-- A unit with `star δ = -δ`. -/
  δ : Aˣ
  star_δ : star (δ : A) = -δ
  /-- The Haar measure on the additive group of skew elements. -/
  ν : Measure (skewAdjoint A)
  [isAddHaarMeasure_ν : ν.IsAddHaarMeasure]
  map_prod_ν : (ν.prod ν).map (fun p ↦ τ * ↑δ⁻¹ * ↑p.1 + ↑p.2) = volume
  /-- The modulus: the factor by which multiplication by a unit scales Haar measure. -/
  modulus : Aˣ →* ℝ≥0
  measurable_modulus : Measurable modulus
  modulus_star (u : Aˣ) : modulus (star u) = modulus u
  map_mulVec_fin (n : ℕ) (M : Matrix (Fin n) (Fin n) A) (u : Aˣ) (hM : M.det = u) :
    (volume : Measure (Fin n → A)).map M.mulVec = (modulus u)⁻¹ • volume
  /-- The additive character. -/
  ψ : AddChar A Circle
  continuous_ψ : Continuous ψ
  /-- The Plancherel constant `c_A`. -/
  plancherelConst : ℝ≥0∞
  exists_damping_kernel : ∃ G : A → ℝ, Continuous G ∧ Integrable G ∧ (∀ x, 0 ≤ G x) ∧ G 0 = 1 ∧
    ∫⁻ w, ‖∫ v, (G v : ℂ) * ψ (star v * w)‖ₑ ≤ plancherelConst
  ae_isUnit : ∀ᵐ x ∂(volume : Measure A), IsUnit x
  exists_locallyIntegrable :
    ∃ g : A → ℝ, LocallyIntegrable g ∧ ∀ u : Aˣ, (modulus u)⁻¹ ≤ ‖g u‖₊ ^ 2

namespace HermitianPlace

variable {A : Type*} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  (P : HermitianPlace A)

instance : P.ν.IsAddHaarMeasure := P.isAddHaarMeasure_ν

/-- `star τ = 1 - τ`. -/
theorem star_τ : star P.τ = 1 - P.τ := by
  rw [← P.τ_add_star, add_sub_cancel_left]

/-- `δ⁻¹` is skew, like `δ`. -/
theorem star_δ_inv : star (↑P.δ⁻¹ : A) = -↑P.δ⁻¹ := by
  have h : (P.δ : A) * star (↑P.δ⁻¹ : A) = -1 := by
    have := congrArg star (Units.inv_mul P.δ)
    rwa [star_mul, P.star_δ, star_one, neg_mul, neg_eq_iff_eq_neg] at this
  calc star (↑P.δ⁻¹ : A) = ↑P.δ⁻¹ * (↑P.δ * star (↑P.δ⁻¹ : A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = -↑P.δ⁻¹ := by rw [h, mul_neg_one]

/-! ### The character and the hermitian pairing -/

/-- `ψ(x) * conj (ψ(y)) = ψ(x - y)` along the hermitian pairing `v*w = ∑ i, star vᵢ * wᵢ` of
`A^ι`. -/
theorem ψ_mul_dotProduct_mul_conj {ι : Type*} [Fintype ι] (η : A) (v w w' : ι → A) :
    (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * conj (P.ψ (η * (star v ⬝ᵥ w')) : ℂ) =
      P.ψ (η * (star v ⬝ᵥ (w - w'))) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, dotProduct_sub, mul_sub, sub_eq_add_neg]

/-- `(v, w) ↦ ψ(η · v*w)` is continuous on `A^ι × A^ι`. -/
theorem continuous_ψ_mul_dotProduct [IsTopologicalRing A] [ContinuousStar A] {ι : Type*}
    [Fintype ι] (η : A) :
    Continuous fun p : (ι → A) × (ι → A) ↦ (P.ψ (η * (star p.1 ⬝ᵥ p.2)) : ℂ) :=
  continuous_subtypeVal.comp <| P.continuous_ψ.comp <|
    continuous_const.mul ((continuous_star.comp continuous_fst).dotProduct continuous_snd)

/-! ### The modulus -/

/-- The modulus of a unit is nonzero. -/
theorem modulus_ne_zero (u : Aˣ) : P.modulus u ≠ 0 :=
  ((Group.isUnit u).map P.modulus).ne_zero

/-- The modulus is even. -/
@[simp]
theorem modulus_neg (u : Aˣ) : P.modulus (-u) = P.modulus u := by
  have h : P.modulus (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  rw [neg_eq_neg_one_mul, map_mul, (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h,
    one_mul]

/-! ### Change of variables on `A^ι` -/

section ChangeOfVariables

variable [IsTopologicalRing A] [SecondCountableTopology A] [BorelSpace A]
  [SigmaFinite (volume : Measure A)] {ι : Type*} [Fintype ι]

/-- A square matrix whose determinant is a unit `u`, indexed by any finite type `ι`, carries Haar
measure of `A^ι` to `modulus u⁻¹` times itself. -/
theorem map_mulVec_volume [DecidableEq ι] (M : Matrix ι ι A) (u : Aˣ) (hM : M.det = u) :
    (volume : Measure (ι → A)).map M.mulVec = (P.modulus u)⁻¹ • volume := by
  -- Transport the statement for `Fin (card ι)` along a reindexing of the coordinates.
  let e := Fintype.equivFin ι
  let Φ := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ A) e.symm
  have hΦ : MeasurePreserving Φ := measurePreserving_piCongrLeft (fun _ : ι ↦ volume) e.symm
  have hΦy (y : Fin (Fintype.card ι) → A) : Φ y = y ∘ e := by
    ext i
    simp [Φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  set M' := M.submatrix e.symm e.symm
  have hcomm : M.mulVec ∘ Φ = Φ ∘ M'.mulVec := by
    ext y i
    simp [hΦy, M', submatrix_mulVec_equiv]
  have hM' : M'.det = u := by rwa [det_submatrix_equiv_self]
  have hM'meas : Measurable M'.mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hMmeas : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  calc (volume : Measure (ι → A)).map M.mulVec
      = ((volume : Measure (Fin (Fintype.card ι) → A)).map M'.mulVec).map Φ := by
        rw [Measure.map_map Φ.measurable hM'meas, ← hcomm,
          ← Measure.map_map hMmeas Φ.measurable, hΦ.map_eq]
    _ = (P.modulus u)⁻¹ • volume := by
        rw [P.map_mulVec_fin _ M' u hM', Measure.map_smul _ Φ.measurable.aemeasurable, hΦ.map_eq]

/-- Multiplication by a unit `u` scales Haar measure of `A^ι` by `modulus u⁻¹ ^ card ι`. -/
theorem map_smul_volume (u : Aˣ) :
    (volume : Measure (ι → A)).map ((u : A) • ·) =
      (P.modulus u)⁻¹ ^ Fintype.card ι • volume := by
  classical
  have h := P.map_mulVec_volume ((u : A) • (1 : Matrix ι ι A)) (u ^ Fintype.card ι)
    (by simp)
  have hfun : ((u : A) • (1 : Matrix ι ι A)).mulVec = ((u : A) • ·) := by
    ext v : 1
    rw [smul_mulVec, one_mulVec]
  rwa [hfun, map_pow, ← inv_pow] at h

/-- The change of variables `v ↦ u • v` on `A^ι` for a unit `u`, for lower integrals. -/
theorem lintegral_comp_smul (u : Aˣ) (f : (ι → A) → ℝ≥0∞) :
    ∫⁻ v, f ((u : A) • v) = ((P.modulus u)⁻¹ ^ Fintype.card ι : ℝ≥0) * ∫⁻ v, f v := by
  rw [← u.isUnit.measurableEmbedding_const_smul.lintegral_map, P.map_smul_volume,
    lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

/-- The change of variables `v ↦ u • v` on `A^ι` for a unit `u`, for Bochner integrals. -/
theorem integral_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Aˣ)
    (f : (ι → A) → E) :
    ∫ v, f ((u : A) • v) = ((P.modulus u)⁻¹ ^ Fintype.card ι : ℝ≥0) • ∫ v, f v := by
  rw [← u.isUnit.measurableEmbedding_const_smul.integral_map, P.map_smul_volume,
    integral_smul_nnreal_measure]

include P in
/-- The change of variables `v ↦ u • v` on `A^ι` for a unit `u` preserves integrability. -/
theorem integrable_comp_smul {E : Type*} [NormedAddCommGroup E] (u : Aˣ) {f : (ι → A) → E}
    (hf : Integrable f) : Integrable fun v ↦ f ((u : A) • v) :=
  u.isUnit.measurableEmbedding_const_smul.integrable_map_iff.mp <| by
    rw [P.map_smul_volume]
    exact hf.smul_measure_nnreal

end ChangeOfVariables

include P in
/-- There is a sequence of units of `A` tending to `0`: every neighbourhood of `0` has positive
Haar measure, and almost every element of `A` is a unit. -/
theorem exists_seq_units_tendsto_zero [FirstCountableTopology A] [OpensMeasurableSpace A]
    [(volume : Measure A).IsOpenPosMeasure] :
    ∃ u : ℕ → Aˣ, Tendsto (fun n ↦ (u n : A)) atTop (𝓝 0) := by
  have : (comap ((↑) : Aˣ → A) (𝓝 0)).NeBot := by
    refine comap_neBot fun t ht ↦ ?_
    obtain ⟨U, hUt, hUo, h0U⟩ := mem_nhds_iff.mp ht
    have : (ae (volume.restrict U)).NeBot :=
      ae_restrict_neBot.2 (hUo.measure_ne_zero volume ⟨0, h0U⟩)
    obtain ⟨x, hxu, hxU⟩ :=
      ((ae_restrict_of_ae P.ae_isUnit).and (ae_restrict_mem hUo.measurableSet)).exists
    exact ⟨hxu.unit, hUt hxU⟩
  obtain ⟨u, hu⟩ := exists_seq_tendsto (comap ((↑) : Aˣ → A) (𝓝 0))
  exact ⟨u, tendsto_comap_iff.mp hu⟩

end HermitianPlace

end TauCeti
