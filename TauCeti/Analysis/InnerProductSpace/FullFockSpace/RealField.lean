/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic

/-!
# Real field operators on complexified full Fock space

Embedding a real inner product space `H` isometrically into its `L²` complexification
`WithLp 2 (Complexification H)` via `WithLp.complexificationOfRealₗᵢ H` attaches to each vector
`h : H` the bounded self-adjoint *real field operator*
`FullFockSpace.realField h = field ℂ (WithLp.complexificationOfRealₗᵢ H h)` on the complex Hilbert
space `FullFockSpace ℂ (WithLp 2 (Complexification H))`.

Both `FullFockSpace.field ℂ` and `FullFockSpace.realField` are `ℝ`-linear (while `field ℂ` is not
`ℂ`-linear because annihilation is conjugate-linear). Starting from a real inner product space
`H`, `realField` bundles into the continuous `ℝ`-linear map `FullFockSpace.realFieldCLM H` of exact
pointwise operator norm `‖realField h‖ = 2 * ‖h‖`, and its second vacuum moments reproduce the real
inner product: `vacuumState ℂ _ (realField h * realField k) = (⟪h, k⟫_ℝ : ℂ)`. No completeness
assumption on `H` is needed.

## Main definitions

* `TauCeti.FullFockSpace.realField`: the self-adjoint real field operator on
  `FullFockSpace ℂ (WithLp 2 (Complexification H))` attached to `h : H`.
* `TauCeti.FullFockSpace.realFieldCLM`: `realField` bundled as a continuous `ℝ`-linear map into
  bounded operators on `FullFockSpace ℂ (WithLp 2 (Complexification H))`.

## Main results

* `TauCeti.FullFockSpace.norm_realField`: `‖realField h‖ = 2 * ‖h‖`.
* `TauCeti.FullFockSpace.vacuumState_realField`,
  `TauCeti.FullFockSpace.vacuumState_realField_mul_realField`, and
  `TauCeti.FullFockSpace.vacuumState_realField_sq`: first and second vacuum moments of `realField`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TauCeti

universe v

namespace FullFockSpace

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The self-adjoint *real field operator* on the complex Fock space
`FullFockSpace ℂ (WithLp 2 (Complexification H))` attached to a vector `h` in a real inner product
space `H`, defined via the isometric real inclusion `WithLp.complexificationOfRealₗᵢ H`. -/
def realField (h : H) :
    FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
      FullFockSpace ℂ (WithLp 2 (Complexification H)) :=
  field ℂ (WithLp.complexificationOfRealₗᵢ H h)

theorem realField_def (h : H) :
    realField h = field ℂ (WithLp.complexificationOfRealₗᵢ H h) :=
  (rfl)

@[simp]
theorem adjoint_realField (h : H) : (realField h).adjoint = realField h :=
  adjoint_field _

@[simp]
theorem star_realField (h : H) : star (realField h) = realField h :=
  star_field _

theorem isSelfAdjoint_realField (h : H) : IsSelfAdjoint (realField h) :=
  isSelfAdjoint_field _

@[simp]
theorem realField_zero : realField (0 : H) = 0 := by
  simp [realField_def]

@[simp]
theorem realField_add (h k : H) : realField (h + k) = realField h + realField k := by
  rw [realField_def, map_add, field_add, ← realField_def, ← realField_def]

@[simp]
theorem realField_neg (h : H) : realField (-h) = -realField h := by
  rw [realField_def, map_neg, field_neg, ← realField_def]

@[simp]
theorem realField_sub (h k : H) : realField (h - k) = realField h - realField k := by
  rw [realField_def, map_sub, field_sub, ← realField_def, ← realField_def]

@[simp]
theorem realField_smul (r : ℝ) (h : H) : realField (r • h) = r • realField h := by
  rw [realField_def, map_smul, ← Complex.coe_smul,
    field_smul_of_isSelfAdjoint (by simp [IsSelfAdjoint]), ← realField_def]
  ext x n
  simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply]
  exact Complex.coe_smul r (realField h x n)

/-- Each real field operator `realField h` has exact operator norm `2 * ‖h‖`. -/
@[simp]
theorem norm_realField (h : H) : ‖realField h‖ = 2 * ‖h‖ := by
  simp [realField_def]

theorem realField_injective : Function.Injective (realField (H := H)) := fun _ _ h =>
  (WithLp.complexificationOfRealₗᵢ H).injective (field_injective h)

@[simp]
theorem realField_eq_zero_iff {h : H} : realField h = 0 ↔ h = 0 :=
  ⟨fun hh => realField_injective (hh.trans realField_zero.symm), fun hh => hh ▸ realField_zero⟩

variable (H) in
/-- `FullFockSpace.realField` bundled as a continuous `ℝ`-linear map of operator norm at most `2`
into bounded operators on `FullFockSpace ℂ (WithLp 2 (Complexification H))`. -/
def realFieldCLM :
    H →L[ℝ]
      (FullFockSpace ℂ (WithLp 2 (Complexification H)) →L[ℂ]
        FullFockSpace ℂ (WithLp 2 (Complexification H))) :=
  LinearMap.mkContinuous
    { toFun := realField
      map_add' := realField_add
      map_smul' := realField_smul }
    2 fun h => (norm_realField h).le

@[simp]
theorem realFieldCLM_apply (h : H) : realFieldCLM H h = realField h :=
  (rfl)

theorem realField_vacuum (h : H) :
    realField h vacuum = creation ℂ (WithLp.complexificationOfRealₗᵢ H h) vacuum :=
  field_vacuum _

theorem inner_vacuum_realField (h : H)
    (x : FullFockSpace ℂ (WithLp 2 (Complexification H))) :
    ⟪vacuum, realField h x⟫_ℂ =
      ⟪vacuum, annihilation ℂ (WithLp.complexificationOfRealₗᵢ H h) x⟫_ℂ :=
  inner_vacuum_field _ x

@[simp]
theorem inner_vacuum_realField_vacuum (h : H) :
    ⟪vacuum, realField h vacuum⟫_ℂ = 0 :=
  inner_vacuum_field_vacuum _

@[simp]
theorem inner_vacuum_realField_realField_vacuum (h k : H) :
    ⟪vacuum, realField h (realField k vacuum)⟫_ℂ = (⟪h, k⟫_ℝ : ℂ) := by
  simpa [realField_def] using
    vacuumState_field_mul_field (𝕜 := ℂ)
      (WithLp.complexificationOfRealₗᵢ H h) (WithLp.complexificationOfRealₗᵢ H k)

@[simp]
theorem inner_vacuum_realField_sq (h : H) :
    ⟪vacuum, (realField h ^ 2) vacuum⟫_ℂ = (‖h‖ ^ 2 : ℂ) := by
  simp [realField_def]

/-- Real field operators have zero vacuum expectation. -/
theorem vacuumState_realField (h : H) :
    vacuumState ℂ (WithLp 2 (Complexification H)) (realField h) = 0 := by
  simp

/-- Second vacuum moment of real field operators: `ω_Ω(realField h * realField k) = ⟪h, k⟫_ℝ`. -/
theorem vacuumState_realField_mul_realField (h k : H) :
    vacuumState ℂ (WithLp 2 (Complexification H)) (realField h * realField k) =
      (⟪h, k⟫_ℝ : ℂ) := by
  simp

/-- Vacuum variance of a real field operator `realField h`. -/
theorem vacuumState_realField_sq (h : H) :
    vacuumState ℂ (WithLp 2 (Complexification H)) (realField h ^ 2) = (‖h‖ ^ 2 : ℂ) := by
  simp

end FullFockSpace

end TauCeti
