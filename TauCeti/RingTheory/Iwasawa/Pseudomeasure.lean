/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic

/-!
# Pseudo-measures and admissible evaluation

Let `G` be a monoid (in applications a profinite group), `R` a commutative ring, `δ : G →* R` a
monoid homomorphism and `Q` a commutative `R`-algebra, typically the total quotient ring of `R`.
A *pseudo-measure* is an element `z : Q` such that `(δ g - 1) * z` comes from `R` for every
`g : G`. When `R` is the commutative completed group algebra of a profinite group and `δ` sends a
group element to its Dirac measure, these are the pseudo-measures of Serre, whose basic example
is the `p`-adic zeta function of Kubota–Leopoldt.

The pseudo-measures form an `R`-submodule of `Q` but not a subring in general. A ring
homomorphism `f : R → A` need not extend to `Q`, so a pseudo-measure is evaluated by clearing a
denominator: if `f (δ g - 1)` is a unit of the `R`-algebra `A`, the value of `z` is
`f (δ g - 1)⁻¹ * f ((δ g - 1) * z)`. This value does not depend on the admissible element `g`,
and it is the unique `R`-linear extension of `f` from the integral pseudo-measures.

## Main definitions

* `TauCeti.Iwasawa.pseudomeasures δ Q`: the `R`-submodule of pseudo-measures in `Q`.
* `TauCeti.Iwasawa.integral δ Q`: the inclusion of `R` into the pseudo-measures.
* `TauCeti.Iwasawa.numerator δ Q g`: the cleared numerator of a pseudo-measure, an element of `R`
  whose image in `Q` is `(δ g - 1) * z`.
* `TauCeti.Iwasawa.evalAt δ Q A g hg`: evaluation of pseudo-measures in `A` through the
  admissible clearing element `g`.

## Main results

* `TauCeti.Iwasawa.mem_pseudomeasures_iff`: the membership criterion.
* `TauCeti.Iwasawa.evalAt_unique`: an `R`-linear map on pseudo-measures which extends the
  structure map of `A` on integral elements is `evalAt`.
* `TauCeti.Iwasawa.evalAt_independent`: the evaluation does not depend on the admissible
  clearing element.
* `TauCeti.Iwasawa.existsUnique_evalAt`: the evaluation is characterised by the cleared identity
  `f (δ g - 1) * L z = f r` whenever `r = (δ g - 1) * z` in `Q`.
* `TauCeti.Iwasawa.evalAt_eq_algHom`: the evaluation agrees with every `R`-algebra map `Q → A`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential
  Number Theory 4 (2025), §3.6, Definition 3.34, equation (3-11) and Remark 3.35.
-/

public noncomputable section

namespace TauCeti.Iwasawa

open Submodule

variable {G R : Type*} [Monoid G] [CommRing R] (δ : G →* R) (Q : Type*) [CommRing Q] [Algebra R Q]

/-- The pseudo-measures for `δ : G →* R` in an `R`-algebra `Q`: the elements `z` with
`(δ g - 1) * z` in the image of `R` for every `g : G`. This is an `R`-submodule of `Q`, not a
subring in general. -/
def pseudomeasures : Submodule R Q :=
  1 / span R (Set.range fun g : G => algebraMap R Q (δ g - 1))

variable {δ Q}

/-- The membership criterion: `z` is a pseudo-measure if and only if `(δ g - 1) * z` comes from
`R` for every `g`. -/
theorem mem_pseudomeasures_iff {z : Q} :
    z ∈ pseudomeasures δ Q ↔ ∀ g : G, ∃ r : R, algebraMap R Q r = algebraMap R Q (δ g - 1) * z := by
  simp_rw [pseudomeasures, mem_div_iff_forall_mul_mem, mem_one]
  constructor
  · intro h g
    simpa [mul_comm] using h _ (subset_span ⟨g, rfl⟩)
  · intro h y hy
    have hle : span R (Set.range fun g : G => algebraMap R Q (δ g - 1)) ≤
        (1 : Submodule R Q).comap (LinearMap.mulLeft R z) := by
      rw [span_le]
      rintro _ ⟨g, rfl⟩
      simpa [mem_one, mul_comm] using h g
    simpa [mem_one] using hle hy

/-- If every `δ g` is `1`, every element of `Q` is a pseudo-measure. -/
theorem pseudomeasures_eq_top (h : ∀ g, δ g = 1) : pseudomeasures δ Q = ⊤ :=
  eq_top_iff.2 fun z _ => mem_pseudomeasures_iff.2 fun g => ⟨0, by simp [h g]⟩

/-- Every element of `R` is a pseudo-measure: `(δ g - 1) * r` comes from `R`. -/
theorem algebraMap_mem_pseudomeasures (r : R) : algebraMap R Q r ∈ pseudomeasures δ Q :=
  mem_pseudomeasures_iff.2 fun g => ⟨(δ g - 1) * r, map_mul _ _ _⟩

variable (δ Q)

/-- The integral pseudo-measures: the inclusion of `R` into the pseudo-measures. -/
def integral : R →ₗ[R] pseudomeasures δ Q :=
  (Algebra.linearMap R Q).codRestrict _ algebraMap_mem_pseudomeasures

variable {δ Q}

/-- An integral pseudo-measure is the image of its element of `R` in `Q`. -/
@[simp]
theorem coe_integral (r : R) : (integral δ Q r : Q) = algebraMap R Q r := (rfl)

/-- The inclusion of `R` into the pseudo-measures is injective when `R → Q` is, that is, when
`Q` is a faithful `R`-algebra (for instance the total quotient ring of `R`). -/
theorem integral_injective [FaithfulSMul R Q] : Function.Injective (integral δ Q) :=
  fun _ _ h => FaithfulSMul.algebraMap_injective R Q congr(($h : Q))

variable [FaithfulSMul R Q]

variable (δ Q) in
/-- The cleared numerator of a pseudo-measure `z` at `g`: the element of `R` whose image in `Q`
is `(δ g - 1) * z`. -/
def numerator (g : G) : pseudomeasures δ Q →ₗ[R] R :=
  (LinearEquiv.ofInjective (Algebra.linearMap R Q)
      (FaithfulSMul.algebraMap_injective R Q)).symm.toLinearMap ∘ₗ
    ((LinearMap.mulLeft R (algebraMap R Q (δ g - 1))).comp (pseudomeasures δ Q).subtype
      |>.codRestrict _ fun z => by
        obtain ⟨r, hr⟩ := mem_pseudomeasures_iff.1 z.2 g
        exact ⟨r, by simpa using hr⟩)

/-- The defining property of the cleared numerator: its image in `Q` is `(δ g - 1) * z`. -/
@[simp]
theorem algebraMap_numerator (g : G) (z : pseudomeasures δ Q) :
    algebraMap R Q (numerator δ Q g z) = algebraMap R Q (δ g - 1) * z := by
  rw [← Algebra.linearMap_apply,
    ← LinearEquiv.ofInjective_apply _ (h := FaithfulSMul.algebraMap_injective R Q)]
  simp [numerator]

/-- Uniqueness of the cleared numerator: since `R → Q` is injective, any `r : R` whose image in
`Q` is `(δ g - 1) * z` is the numerator of `z` at `g`. -/
theorem numerator_eq_of_algebraMap_eq {g : G} {z : pseudomeasures δ Q} {r : R}
    (h : algebraMap R Q r = algebraMap R Q (δ g - 1) * z) : numerator δ Q g z = r :=
  FaithfulSMul.algebraMap_injective R Q <| by rw [algebraMap_numerator, h]

/-- The cleared numerator of the integral pseudo-measure `r` at `g` is `(δ g - 1) * r`. -/
@[simp]
theorem numerator_integral (g : G) (r : R) : numerator δ Q g (integral δ Q r) = (δ g - 1) * r :=
  numerator_eq_of_algebraMap_eq <| by simp

/-- The clearing factor at `g = 1` is `δ 1 - 1 = 0`, so every cleared numerator at `1` vanishes. -/
@[simp]
theorem numerator_one : numerator δ Q (1 : G) = 0 :=
  LinearMap.ext fun _ => numerator_eq_of_algebraMap_eq <| by simp

/-- Multiplying a pseudo-measure by `δ g - 1` makes it integral, with the cleared numerator. -/
theorem sub_one_smul_eq_integral_numerator (g : G) (z : pseudomeasures δ Q) :
    (δ g - 1) • z = integral δ Q (numerator δ Q g z) :=
  Subtype.ext <| by simp [Algebra.smul_def]

/-- Cross-multiplication of cleared numerators. -/
theorem numerator_cross (g h : G) (z : pseudomeasures δ Q) :
    (δ h - 1) * numerator δ Q g z = (δ g - 1) * numerator δ Q h z :=
  FaithfulSMul.algebraMap_injective R Q <| by simp only [map_mul, algebraMap_numerator]; ring

variable (A : Type*) [CommRing A] [Algebra R A]

variable (δ Q) in
/-- Evaluation of pseudo-measures in an `R`-algebra `A` through a clearing element `g` such that
`δ g - 1` maps to a unit of `A`: a pseudo-measure `z` is sent to
`(δ g - 1)⁻¹ * numerator δ Q g z`, computed in `A`. -/
def evalAt (g : G) (hg : IsUnit (algebraMap R A (δ g - 1))) :
    pseudomeasures δ Q →ₗ[R] A :=
  LinearMap.mulLeft R (↑hg.unit⁻¹ : A) ∘ₗ (Algebra.linearMap R A ∘ₗ numerator δ Q g)

variable {A}

/-- Unfolding the evaluation: `z` is sent to `(δ g - 1)⁻¹ * numerator δ Q g z` in `A`. -/
theorem evalAt_apply (g : G) (hg : IsUnit (algebraMap R A (δ g - 1))) (z : pseudomeasures δ Q) :
    evalAt δ Q A g hg z = ↑hg.unit⁻¹ * algebraMap R A (numerator δ Q g z) := (rfl)

/-- The cleared identity for the evaluation: multiplying the value of `z` by the image of the
admissible clearing factor `δ g - 1` in `A` gives the image of the cleared numerator of `z` at
`g`. Since that clearing factor is a unit of `A`, this determines the value. -/
theorem evalAt_spec (g : G) (hg : IsUnit (algebraMap R A (δ g - 1))) (z : pseudomeasures δ Q) :
    algebraMap R A (δ g - 1) * evalAt δ Q A g hg z = algebraMap R A (numerator δ Q g z) := by
  rw [evalAt_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

/-- The evaluation extends the structure map `R → A` on integral pseudo-measures. -/
@[simp]
theorem evalAt_integral (g : G) (hg : IsUnit (algebraMap R A (δ g - 1))) (r : R) :
    evalAt δ Q A g hg (integral δ Q r) = algebraMap R A r := by
  rw [evalAt_apply, numerator_integral, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]

/-- Uniqueness of admissible evaluation: an `R`-linear map on pseudo-measures extending the
structure map `R → A` on integral elements is the evaluation at any admissible `g`. -/
theorem evalAt_unique (g : G) (hg : IsUnit (algebraMap R A (δ g - 1)))
    (L : pseudomeasures δ Q →ₗ[R] A) (hL : ∀ r, L (integral δ Q r) = algebraMap R A r) :
    L = evalAt δ Q A g hg := by
  ext z
  apply hg.mul_left_cancel
  rw [evalAt_spec, ← hL (numerator δ Q g z), ← sub_one_smul_eq_integral_numerator, map_smul,
    Algebra.smul_def]

/-- The evaluation of pseudo-measures does not depend on the admissible clearing element. -/
theorem evalAt_independent (g h : G) (hg : IsUnit (algebraMap R A (δ g - 1)))
    (hh : IsUnit (algebraMap R A (δ h - 1))) : evalAt δ Q A g hg = evalAt δ Q A h hh :=
  evalAt_unique h hh _ (evalAt_integral g hg)

/-- The evaluation of pseudo-measures is the unique `R`-linear map `L` satisfying the cleared
identity `f (δ g - 1) * L z = f r` whenever `r = (δ g - 1) * z` in `Q`, where `f` is the
structure map of `A`. -/
theorem existsUnique_evalAt (g : G) (hg : IsUnit (algebraMap R A (δ g - 1))) :
    ∃! L : pseudomeasures δ Q →ₗ[R] A, ∀ (z : pseudomeasures δ Q) (r : R),
      algebraMap R Q r = algebraMap R Q (δ g - 1) * z →
        algebraMap R A (δ g - 1) * L z = algebraMap R A r := by
  refine ⟨evalAt δ Q A g hg, fun z r hr => ?_, fun L hL => LinearMap.ext fun z => ?_⟩
  · rw [evalAt_spec, numerator_eq_of_algebraMap_eq hr]
  · exact hg.mul_left_cancel <| by rw [hL z _ (algebraMap_numerator g z), evalAt_spec]

/-- Evaluation of pseudo-measures commutes with `R`-algebra maps between coefficient algebras. -/
theorem evalAt_map {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (g : G)
    (hg : IsUnit (algebraMap R A (δ g - 1))) (hg' : IsUnit (algebraMap R B (δ g - 1)))
    (z : pseudomeasures δ Q) : φ (evalAt δ Q A g hg z) = evalAt δ Q B g hg' z :=
  LinearMap.congr_fun (evalAt_unique g hg' (φ.toLinearMap ∘ₗ evalAt δ Q A g hg) fun r => by
    simp) z

/-- Where the structure map `R → A` extends to an `R`-algebra map on `Q`, the evaluation of
pseudo-measures is that map. -/
theorem evalAt_eq_algHom (F : Q →ₐ[R] A) (g : G) (hg : IsUnit (algebraMap R A (δ g - 1)))
    (z : pseudomeasures δ Q) : evalAt δ Q A g hg z = F z :=
  (LinearMap.congr_fun (evalAt_unique g hg (F.toLinearMap ∘ₗ (pseudomeasures δ Q).subtype)
    fun r => by simp) z).symm

/-! ### Examples -/

-- For `Units.coeHom ℤ` the pseudo-measures in `ℚ` are the `r` with `2 * r ∈ ℤ`: `1 / 2` belongs
-- and `1 / 4 = 1 / 2 * 1 / 2` does not, so the pseudo-measures do not form a subring.
example : (1 / 2 : ℚ) ∈ pseudomeasures (Units.coeHom ℤ) ℚ ∧
    (1 / 4 : ℚ) ∉ pseudomeasures (Units.coeHom ℤ) ℚ := by
  refine ⟨mem_pseudomeasures_iff.2 fun g => ?_, fun h => ?_⟩
  · rcases Int.units_eq_one_or g with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by norm_num⟩
  · obtain ⟨r, hr⟩ := mem_pseudomeasures_iff.1 h (-1)
    have h2 : ((2 * r : ℤ) : ℚ) = ((-1 : ℤ) : ℚ) := by norm_num at hr ⊢; rw [hr]; norm_num
    have := Int.cast_injective h2
    omega

-- The clearing factor of `g = -1` is `-2`, a unit of `ZMod 3`.
example : IsUnit (algebraMap ℤ (ZMod 3) (Units.coeHom ℤ (-1) - 1)) := by
  rw [show algebraMap ℤ (ZMod 3) (Units.coeHom ℤ (-1) - 1) = 1 by decide]
  exact isUnit_one

-- The cleared numerator of `1 / 2` at `g = -1` is `-1`, so evaluation in `ZMod 3` through `g = -1`
-- sends `1 / 2` to `-1 / -2 = 2`, the inverse of `2` in `ZMod 3`.
example (h : (1 / 2 : ℚ) ∈ pseudomeasures (Units.coeHom ℤ) ℚ)
    (hg : IsUnit (algebraMap ℤ (ZMod 3) (Units.coeHom ℤ (-1) - 1))) :
    numerator (Units.coeHom ℤ) ℚ (-1) ⟨1 / 2, h⟩ = -1 ∧
      evalAt (Units.coeHom ℤ) ℚ (ZMod 3) (-1) hg ⟨1 / 2, h⟩ = 2 := by
  have hn : numerator (Units.coeHom ℤ) ℚ (-1) ⟨1 / 2, h⟩ = -1 :=
    numerator_eq_of_algebraMap_eq (by norm_num)
  refine ⟨hn, ?_⟩
  have hspec := evalAt_spec (-1) hg ⟨1 / 2, h⟩
  rw [hn, show algebraMap ℤ (ZMod 3) (Units.coeHom ℤ (-1) - 1) = 1 by decide, one_mul] at hspec
  rw [hspec]
  decide

end TauCeti.Iwasawa

end
