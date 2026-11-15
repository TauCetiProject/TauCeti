/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
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

## Main definitions

* `TauCeti.FullFockSpace.vacuumState`: the vacuum vector functional `T ↦ ⟪Ω, T Ω⟫_𝕜` as a
  `PositiveLinearMap`.
* `TauCeti.FullFockSpace.field`: the self-adjoint field operator `ℓ(h) + ℓ(h)*`.

## Main results

* `TauCeti.FullFockSpace.vacuumState_one`, `TauCeti.FullFockSpace.continuous_vacuumState`:
  normalisation `vacuumState 𝕜 H 1 = 1` and operator-norm continuity.
* `TauCeti.FullFockSpace.vacuumState_creation_mul`,
  `TauCeti.FullFockSpace.vacuumState_mul_annihilation`,
  `TauCeti.FullFockSpace.vacuumState_annihilation_mul_creation`: vacuum expectations of products
  starting with creation or ending with annihilation vanish, and
  `vacuumState 𝕜 H (ℓ(h)* ℓ(k)) = ⟪h, k⟫_𝕜`.
* `TauCeti.FullFockSpace.isSelfAdjoint_field`, `TauCeti.FullFockSpace.norm_field`: self-adjointness
  and exact norm `‖field 𝕜 h‖ = 2 * ‖h‖`.
* `TauCeti.FullFockSpace.field_wordVector_cons`: action of `field 𝕜 h` on a nonempty pure tensor
  word `wordVector 𝕜 (k :: w)`.
* `TauCeti.FullFockSpace.vacuumState_field`, `TauCeti.FullFockSpace.vacuumState_field_mul_field`:
  first and second vacuum moments of field operators.

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

theorem vacuumState_annihilation_mul_creation (h k : H) :
    vacuumState 𝕜 H (annihilation 𝕜 h * creation 𝕜 k) = ⟪h, k⟫_𝕜 := by
  simp

theorem vacuumState_creation_mul_annihilation (h k : H) :
    vacuumState 𝕜 H (creation 𝕜 h * annihilation 𝕜 k) = 0 := by
  simp

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
theorem field_add (h k : H) : field 𝕜 (h + k) = field 𝕜 h + field 𝕜 k := by
  rw [field_def, creation_add, annihilation_add, add_add_add_comm, ← field_def, ← field_def]

@[simp]
theorem field_neg (h : H) : field 𝕜 (-h) = -field 𝕜 h := by
  rw [field_def, creation_neg, annihilation_neg, ← neg_add, ← field_def]

@[simp]
theorem field_sub (h k : H) : field 𝕜 (h - k) = field 𝕜 h - field 𝕜 k := by
  rw [sub_eq_add_neg, field_add, field_neg, ← sub_eq_add_neg]

/-- Real scalar multiples commute with `field 𝕜`. Over `ℂ`, general complex scalars do not because
`creation 𝕜` is linear whereas `annihilation 𝕜` is conjugate-linear. -/
@[simp]
theorem field_smul_ofReal (r : ℝ) (h : H) :
    field 𝕜 ((r : 𝕜) • h) = (r : 𝕜) • field 𝕜 h := by
  ext x : 1
  simp [field_apply, RCLike.star_def]

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

end FullFockSpace

end TauCeti
