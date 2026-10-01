/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive functionals on commutative C⋆-algebras are measures on the character space

Let `A` be a unital commutative C⋆-algebra, with character space `Δ = characterSpace ℂ A`. A
linear functional `f : A → ℂ` that is nonnegative on every `star a * a` is integration against a
finite positive measure on `Δ`:

`f a = ∫ ω, ω a ∂μ`.

The Gelfand transform identifies `A` with `C(Δ, ℂ)`, and under this identification
`star a * a` runs through the nonnegative functions, so `f` becomes a positive linear functional
on `C(Δ, ℝ)`. The compact space `Δ` then carries its Riesz–Markov–Kakutani measure.

This is the commutative case of the passage from states to spectral data; it turns a cyclic
commuting family of operators, such as a unitary representation of an abelian group, into a
measure on the joint spectrum.

## Main declarations

* `LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq`: a functional nonnegative on
  `star a * a` is integration against a finite measure on the character space.
* `PositiveLinearMap.exists_isFiniteMeasure_integral_characterSpace_eq`: the same for a positive
  linear functional, for any order making `A` a star-ordered ring.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 11.18 and §12.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), §2.1.
-/

public section

noncomputable section

open MeasureTheory WeakDual ComplexOrder ContinuousMap
open scoped CompactlySupported

variable {A : Type*} [CommCStarAlgebra A]

namespace TauCeti.CharacterSpaceMeasure

variable (f : A →ₗ[ℂ] ℂ)

/-- Pulled back along the Gelfand transform, a functional nonnegative on `star a * a` is
nonnegative on nonnegative real functions: such a function is `star h * h` for `h = √g`. -/
private lemma nonneg_apply_symm_realToRCLike (hf : ∀ a, 0 ≤ f (star a * a))
    {g : C(characterSpace ℂ A, ℝ)} (hg : 0 ≤ g) :
    0 ≤ f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) := by
  set h : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ √(g ω), g.continuous.sqrt⟩
  have hgh : g = star h * h := by
    ext ω
    have hgω : 0 ≤ g ω := hg ω
    simp [h, Real.mul_self_sqrt hgω]
  rw [hgh, realToRCLike_mul, realToRCLike_star, map_mul, map_star]
  exact hf _

/-- Pulled back along the Gelfand transform, a functional nonnegative on `star a * a` is real on
real functions. -/
private lemma apply_symm_realToRCLike_eq_re (hf : ∀ a, 0 ≤ f (star a * a))
    (g : C(characterSpace ℂ A, ℝ)) :
    f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) =
      (f ((gelfandStarTransform A).symm (g.realToRCLike ℂ))).re := by
  have hp := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf (posPart_nonneg g))).2
  have hn := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf (negPart_nonneg g))).2
  rw [← posPart_sub_negPart g, ← realToRCLikeStarAlgHom_apply, map_sub, map_sub, map_sub,
    realToRCLikeStarAlgHom_apply, realToRCLikeStarAlgHom_apply]
  set p := f ((gelfandStarTransform A).symm (g⁺.realToRCLike ℂ))
  set n := f ((gelfandStarTransform A).symm (g⁻.realToRCLike ℂ))
  apply Complex.ext <;> simp [← hp, ← hn]

/-- The positive linear functional on `C_c(Δ, ℝ) = C(Δ, ℝ)` induced by `f` through the Gelfand
transform. -/
private def realFunctional (hf : ∀ a, 0 ≤ f (star a * a)) :
    C_c(characterSpace ℂ A, ℝ) →ₚ[ℝ] ℝ where
  toFun g := (f ((gelfandStarTransform A).symm (g.toContinuousMap.realToRCLike ℂ))).re
  map_add' g h := by
    have : (g + h).toContinuousMap.realToRCLike ℂ =
        g.toContinuousMap.realToRCLike ℂ + h.toContinuousMap.realToRCLike ℂ := by
      ext; simp
    rw [this, map_add, map_add, Complex.add_re]
  map_smul' c g := by
    have : (c • g).toContinuousMap.realToRCLike ℂ =
        (c : ℂ) • g.toContinuousMap.realToRCLike ℂ := by
      ext; simp
    rw [this, map_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply,
      smul_eq_mul]
  monotone' g h hgh := by
    have hle : 0 ≤ h.toContinuousMap - g.toContinuousMap :=
      sub_nonneg.mpr fun ω ↦ hgh ω
    have := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf hle)).1
    rw [← realToRCLikeStarAlgHom_apply, map_sub, map_sub, map_sub, Complex.sub_re] at this
    simp only [realToRCLikeStarAlgHom_apply] at this
    linarith

private lemma realFunctional_apply (hf : ∀ a, 0 ≤ f (star a * a))
    (g : C_c(characterSpace ℂ A, ℝ)) :
    realFunctional f hf g =
      (f ((gelfandStarTransform A).symm (g.toContinuousMap.realToRCLike ℂ))).re :=
  rfl

end TauCeti.CharacterSpaceMeasure

open TauCeti.CharacterSpaceMeasure

variable [MeasurableSpace (characterSpace ℂ A)] [BorelSpace (characterSpace ℂ A)]

/-- **States on a commutative C⋆-algebra are measures on its character space.** A linear
functional on a unital commutative C⋆-algebra that is nonnegative on every `star a * a` is
integration against a finite positive measure `μ` on the character space:
`f a = ∫ ω, ω a ∂μ`. -/
theorem LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq (f : A →ₗ[ℂ] ℂ)
    (hf : ∀ a, 0 ≤ f (star a * a)) :
    ∃ μ : Measure (characterSpace ℂ A), IsFiniteMeasure μ ∧ ∀ a, f a = ∫ ω, ω a ∂μ := by
  set Λ := realFunctional f hf
  set μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, fun a ↦ ?_⟩
  -- Split the Gelfand transform `F` of `a` into its real part `u` and imaginary part `v`.
  set F := gelfandStarTransform A a
  let u : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ (F ω).re, Complex.continuous_re.comp F.continuous⟩
  let v : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ (F ω).im, Complex.continuous_im.comp F.continuous⟩
  have hF : F = u.realToRCLike ℂ + Complex.I • v.realToRCLike ℂ := by
    ext ω
    simp [u, v, mul_comm Complex.I]
  -- On a real function, `f` agrees with the Riesz–Markov–Kakutani integral.
  have hreal (g : C(characterSpace ℂ A, ℝ)) :
      f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) = ((∫ ω, g ω ∂μ : ℝ) : ℂ) := by
    have h := RealRMK.integral_rieszMeasure Λ ⟨g, .of_compactSpace _⟩
    rw [realFunctional_apply, CompactlySupportedContinuousMap.coe_mk] at h
    rw [apply_symm_realToRCLike_eq_re f hf g, h]
  have hFint : Integrable F μ :=
    F.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
  calc f a = f ((gelfandStarTransform A).symm F) := by simp [F]
    _ = (∫ ω, u ω ∂μ : ℝ) + ((∫ ω, v ω ∂μ : ℝ) : ℂ) * Complex.I := by
      rw [hF, map_add, map_smul, map_add, map_smul, hreal, hreal, smul_eq_mul, mul_comm]
    _ = ∫ ω, F ω ∂μ := integral_re_add_im hFint
    _ = ∫ ω, ω a ∂μ := by simp [F]

/-- **Positive functionals on a commutative C⋆-algebra are measures on its character space.**
For any order making the unital commutative C⋆-algebra `A` a star-ordered ring, a positive
linear functional `f : A →ₚ[ℂ] ℂ` is integration against a finite positive measure on the
character space. -/
theorem PositiveLinearMap.exists_isFiniteMeasure_integral_characterSpace_eq [PartialOrder A]
    [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ) :
    ∃ μ : Measure (characterSpace ℂ A), IsFiniteMeasure μ ∧ ∀ a, f a = ∫ ω, ω a ∂μ :=
  (f : A →ₗ[ℂ] ℂ).exists_isFiniteMeasure_integral_characterSpace_eq fun a ↦
    f.map_nonneg (star_mul_self_nonneg a)
