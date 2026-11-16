/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional

/-!
# The vacuum state and field operators on full Fock space

On the full Fock space `FullFockSpace 𝕜 H` (`𝓕(H)`) over `𝕜` (`ℝ` or `ℂ`), we define:

* `TauCeti.FullFockSpace.vacuumState 𝕜 H`: the normalised positive linear functional
  `T ↦ ⟪vacuum, T vacuum⟫_𝕜` (`(FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) →ₚ[𝕜] 𝕜`) attached to
  the unit vacuum vector `Ω`. Over `𝕜 = ℂ`, `FullFockSpace ℂ H →L[ℂ] FullFockSpace ℂ H` is a unital
  C⋆-algebra (even when `H` is incomplete, since each tensor grade in `FullFockSpace` is completed)
  and `vacuumState ℂ H` is its vacuum vector state.
* `TauCeti.FullFockSpace.field 𝕜 h`: the self-adjoint field (or position) operator
  `s(h) = creation 𝕜 h + annihilation 𝕜 h` (`ℓ(h) + ℓ(h)*`), with exact operator norm `2 * ‖h‖`,
  vacuum expectation `0`, and covariance `vacuumState 𝕜 H (field 𝕜 h * field 𝕜 k) = ⟪h, k⟫_𝕜`.
* `TauCeti.FullFockSpace.realField x`: the self-adjoint field operator on
  `FullFockSpace ℂ (WithLp 2 (Complexification X))` attached to `x : X` in a real inner product
  space `X` via `x ↦ x + i 0`.

## Main definitions

* `TauCeti.FullFockSpace.vacuumState`: the vacuum vector functional `T ↦ ⟪Ω, T Ω⟫_𝕜` as a
  `PositiveLinearMap`.
* `TauCeti.FullFockSpace.field`: the self-adjoint field operator `ℓ(h) + ℓ(h)*`.
* `TauCeti.FullFockSpace.realField`: the self-adjoint field operator on the complexified full Fock
  space attached to a vector in a real inner product space.

## Main results

* `TauCeti.FullFockSpace.vacuumState_one`, `TauCeti.FullFockSpace.continuous_vacuumState`:
  normalisation `vacuumState 𝕜 H 1 = 1` and operator-norm continuity.
* `TauCeti.FullFockSpace.vacuumState_creation_mul`,
  `TauCeti.FullFockSpace.vacuumState_mul_annihilation`: vacuum expectations of products starting
  with creation or ending with annihilation vanish.
* `TauCeti.FullFockSpace.isSelfAdjoint_field`, `TauCeti.FullFockSpace.norm_field`,
  `TauCeti.FullFockSpace.continuous_field`: self-adjointness, exact norm `‖field 𝕜 h‖ = 2 * ‖h‖`,
  and continuity of `field 𝕜`.
* `TauCeti.FullFockSpace.field_wordVector_cons`: action of `field 𝕜 h` on a nonempty pure tensor
  word `wordVector 𝕜 (k :: w)`.
* `TauCeti.FullFockSpace.vacuumState_field`, `TauCeti.FullFockSpace.vacuumState_field_mul_field`:
  first and second vacuum moments of field operators.
* `TauCeti.FullFockSpace.isSelfAdjoint_realField`, `TauCeti.FullFockSpace.norm_realField`,
  `TauCeti.FullFockSpace.vacuumState_realField_mul_realField`: operator and vacuum-moment properties
  of `realField`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace NNReal

namespace TauCeti

universe u v

namespace FullFockSpace

section VacuumState

/-- The *vacuum vector functional* `T ↦ ⟪vacuum, T vacuum⟫_𝕜` on bounded operators on
`FullFockSpace 𝕜 H`, bundled as a positive linear map. -/
def vacuumState (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    (FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) →ₚ[𝕜] 𝕜 :=
  ContinuousLinearMap.innerPositiveLinearMap 𝕜 vacuum

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem vacuumState_def :
    vacuumState 𝕜 H = ContinuousLinearMap.innerPositiveLinearMap 𝕜 (vacuum : FullFockSpace 𝕜 H) :=
  (rfl)

theorem vacuumState_apply (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :
    vacuumState 𝕜 H T = ⟪vacuum, T vacuum⟫_𝕜 :=
  ContinuousLinearMap.innerPositiveLinearMap_apply vacuum T

@[simp]
theorem vacuumState_one : vacuumState 𝕜 H 1 = 1 := by
  simp [vacuumState_apply]

/-- The vacuum functional is contractive (`‖vacuumState 𝕜 H T‖ ≤ ‖T‖`). -/
theorem norm_vacuumState_apply_le (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :
    ‖vacuumState 𝕜 H T‖ ≤ ‖T‖ := by
  simpa [vacuumState] using ContinuousLinearMap.norm_innerPositiveLinearMap_apply_le vacuum T

/-- The vacuum functional is continuous with respect to the operator norm. -/
@[fun_prop]
theorem continuous_vacuumState : Continuous (vacuumState 𝕜 H) :=
  ((vacuumState 𝕜 H).toLinearMap.mkContinuous 1 fun T => by
    simpa using norm_vacuumState_apply_le T).continuous

@[simp]
theorem vacuumState_vacuumProj : vacuumState 𝕜 H vacuumProj = 1 := by
  simp [vacuumState_apply]

/-- Any operator product with a left creation factor on the left has zero vacuum expectation. -/
@[simp]
theorem vacuumState_creation_mul (h : H) (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :
    vacuumState 𝕜 H (creation 𝕜 h * T) = 0 := by
  simp [vacuumState_apply]

/-- Any operator product with a left annihilation factor on the right has zero vacuum
expectation. -/
@[simp]
theorem vacuumState_mul_annihilation (T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) (h : H) :
    vacuumState 𝕜 H (T * annihilation 𝕜 h) = 0 := by
  simp [vacuumState_apply]

@[simp]
theorem vacuumState_creation (h : H) : vacuumState 𝕜 H (creation 𝕜 h) = 0 := by
  simp [vacuumState_apply]

@[simp]
theorem vacuumState_annihilation (h : H) : vacuumState 𝕜 H (annihilation 𝕜 h) = 0 := by
  simp [vacuumState_apply]

end VacuumState

section Field

/-- The self-adjoint *field* (or *position*) *operator* `s(h) = ℓ(h) + ℓ(h)*` on
`FullFockSpace 𝕜 H`. -/
def field (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (h : H) :
    FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H :=
  creation 𝕜 h + annihilation 𝕜 h

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem field_def (h : H) : field 𝕜 h = creation 𝕜 h + annihilation 𝕜 h :=
  (rfl)

theorem field_apply (h : H) (x : FullFockSpace 𝕜 H) :
    field 𝕜 h x = creation 𝕜 h x + annihilation 𝕜 h x :=
  (rfl)

@[simp]
theorem adjoint_field (h : H) : (field 𝕜 h).adjoint = field 𝕜 h := by
  rw [field_def, map_add, adjoint_creation, adjoint_annihilation, add_comm]

@[simp]
theorem star_field (h : H) : star (field 𝕜 h) = field 𝕜 h :=
  adjoint_field h

theorem isSelfAdjoint_field (h : H) : IsSelfAdjoint (field 𝕜 h) :=
  isSelfAdjoint_iff.mpr (star_field h)

/-- The field operator `field 𝕜 h` has exact operator norm `2 * ‖h‖`. -/
@[simp]
theorem norm_field (h : H) : ‖field 𝕜 h‖ = 2 * ‖h‖ :=
  norm_creation_add_annihilation h

@[simp]
theorem field_zero : field 𝕜 (0 : H) = 0 := by
  simp [field_def]

@[simp]
theorem field_eq_zero {h : H} : field 𝕜 h = 0 ↔ h = 0 := by
  rw [← norm_eq_zero, norm_field, mul_eq_zero, norm_eq_zero]
  simp

@[simp]
theorem field_add (h k : H) : field 𝕜 (h + k) = field 𝕜 h + field 𝕜 k := by
  rw [field_def, creation_add, annihilation_add, add_add_add_comm, ← field_def, ← field_def]

@[simp]
theorem field_neg (h : H) : field 𝕜 (-h) = -field 𝕜 h := by
  rw [field_def, creation_neg, annihilation_neg, ← neg_add, ← field_def]

@[simp]
theorem field_sub (h k : H) : field 𝕜 (h - k) = field 𝕜 h - field 𝕜 k := by
  rw [sub_eq_add_neg, field_add, field_neg, ← sub_eq_add_neg]

@[simp]
theorem field_inj {h k : H} : field 𝕜 h = field 𝕜 k ↔ h = k := by
  rw [← sub_eq_zero, ← field_sub, field_eq_zero, sub_eq_zero]

@[fun_prop]
theorem continuous_field :
    Continuous (field 𝕜 : H → FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) :=
  (LipschitzWith.of_dist_le_mul (K := 2) fun h k => by
    rw [dist_eq_norm, dist_eq_norm, ← field_sub, norm_field]
    rfl).continuous

/-- Real scalar multiples commute with `field 𝕜`. Over `ℂ`, general complex scalars do not because
`creation 𝕜` is linear whereas `annihilation 𝕜` is conjugate-linear. -/
@[simp]
theorem field_smul_ofReal (r : ℝ) (h : H) :
    field 𝕜 ((r : 𝕜) • h) = (r : 𝕜) • field 𝕜 h := by
  ext x : 1
  simp [field_apply, RCLike.star_def]

@[simp]
theorem field_real_smul {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (h : E) : field ℝ (r • h) = r • field ℝ h :=
  field_smul_ofReal r h

@[simp]
theorem field_complex_real_smul {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ) (h : E) : field ℂ (r • h) = r • field ℂ h := by
  have : IsScalarTower ℝ ℂ E := Real.isScalarTower
  have : IsScalarTower ℝ ℂ (FullFockSpace ℂ E) := Real.isScalarTower
  rw [← algebraMap_smul ℂ r h, RCLike.algebraMap_eq_ofReal, field_smul_ofReal]
  ext x : 1
  simp only [smul_apply, ← RCLike.algebraMap_eq_ofReal, algebraMap_smul]

@[simp]
theorem field_vacuum (h : H) : field 𝕜 h vacuum = creation 𝕜 h vacuum := by
  simp [field_apply]

theorem field_creation (h k : H) (x : FullFockSpace 𝕜 H) :
    field 𝕜 h (creation 𝕜 k x) = creation 𝕜 h (creation 𝕜 k x) + ⟪h, k⟫_𝕜 • x := by
  simp [field_apply]

/-- Acting by `field 𝕜 h` on a nonempty pure tensor word prepends `h` and contracts `h` against the
head letter `k`. -/
theorem field_wordVector_cons (h k : H) (w : List H) :
    field 𝕜 h (wordVector 𝕜 (k :: w)) =
      wordVector 𝕜 (h :: k :: w) + ⟪h, k⟫_𝕜 • wordVector 𝕜 w := by
  simp [field_apply]

@[simp]
theorem vacuumState_field (h : H) : vacuumState 𝕜 H (field 𝕜 h) = 0 := by
  simp [field_def]

@[simp]
theorem vacuumState_field_mul_field (h k : H) :
    vacuumState 𝕜 H (field 𝕜 h * field 𝕜 k) = ⟪h, k⟫_𝕜 := by
  simp [field_def, add_mul, mul_add]

@[simp]
theorem vacuumState_field_sq (h : H) :
    vacuumState 𝕜 H (field 𝕜 h ^ 2) = (‖h‖ ^ 2 : 𝕜) := by
  rw [sq, vacuumState_field_mul_field, inner_self_eq_norm_sq_to_K]

end Field

section RealField

variable {X : Type v} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The self-adjoint field operator on `FullFockSpace ℂ (WithLp 2 (Complexification X))` attached
to a vector `x : X` in a real inner product space `X` via `x ↦ x + i 0`. -/
def realField (x : X) :
    FullFockSpace ℂ (WithLp 2 (Complexification X)) →L[ℂ]
      FullFockSpace ℂ (WithLp 2 (Complexification X)) :=
  field ℂ (WithLp.complexificationOfRealₗᵢ X x)

theorem realField_def (x : X) :
    realField x = field ℂ (WithLp.complexificationOfRealₗᵢ X x) :=
  (rfl)

@[simp]
theorem adjoint_realField (x : X) : (realField x).adjoint = realField x :=
  adjoint_field _

@[simp]
theorem star_realField (x : X) : star (realField x) = realField x :=
  star_field _

theorem isSelfAdjoint_realField (x : X) : IsSelfAdjoint (realField x) :=
  isSelfAdjoint_field _

@[simp]
theorem norm_realField (x : X) : ‖realField x‖ = 2 * ‖x‖ := by
  rw [realField_def, norm_field, LinearIsometry.norm_map]

@[simp]
theorem realField_zero : realField (0 : X) = 0 := by
  simp [realField_def]

@[simp]
theorem realField_eq_zero {x : X} : realField x = 0 ↔ x = 0 := by
  rw [realField_def, field_eq_zero, map_eq_zero_iff _ (WithLp.complexificationOfRealₗᵢ X).injective]

@[simp]
theorem realField_add (x y : X) : realField (x + y) = realField x + realField y := by
  rw [realField_def, map_add, field_add, ← realField_def, ← realField_def]

@[simp]
theorem realField_neg (x : X) : realField (-x) = -realField x := by
  rw [realField_def, map_neg, field_neg, ← realField_def]

@[simp]
theorem realField_sub (x y : X) : realField (x - y) = realField x - realField y := by
  rw [realField_def, map_sub, field_sub, ← realField_def, ← realField_def]

@[simp]
theorem realField_inj {x y : X} : realField x = realField y ↔ x = y := by
  rw [← sub_eq_zero, ← realField_sub, realField_eq_zero, sub_eq_zero]

@[simp]
theorem realField_smul (r : ℝ) (x : X) : realField (r • x) = r • realField x := by
  rw [realField_def, map_smul, field_complex_real_smul, ← realField_def]

@[fun_prop]
theorem continuous_realField :
    Continuous (realField : X → FullFockSpace ℂ (WithLp 2 (Complexification X)) →L[ℂ]
      FullFockSpace ℂ (WithLp 2 (Complexification X))) :=
  continuous_field.comp (WithLp.complexificationOfRealₗᵢ X).continuous

@[simp]
theorem vacuumState_realField (x : X) :
    vacuumState ℂ (WithLp 2 (Complexification X)) (realField x) = 0 :=
  vacuumState_field _

@[simp]
theorem vacuumState_realField_mul_realField (x y : X) :
    vacuumState ℂ (WithLp 2 (Complexification X)) (realField x * realField y) =
      (⟪x, y⟫_ℝ : ℂ) := by
  rw [realField_def, realField_def, vacuumState_field_mul_field,
    WithLp.complexificationOfRealₗᵢ_apply, WithLp.complexificationOfRealₗᵢ_apply,
    WithLp.complexification_inner_toLp_ofReal]

@[simp]
theorem vacuumState_realField_sq (x : X) :
    vacuumState ℂ (WithLp 2 (Complexification X)) (realField x ^ 2) =
      ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [sq, vacuumState_realField_mul_realField, real_inner_self_eq_norm_sq]

end RealField

end FullFockSpace

end TauCeti
