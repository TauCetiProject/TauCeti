/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle

/-!
# Acute pairs of subspaces, principal tangents and the quarter turn

Let `U` and `V` be subspaces of an inner product space with orthogonal projections `P_U` and `P_V`.

The pair `(U, V)` is *acute* (`Submodule.IsAcute`) when `P_V` is injective on `U` and `P_U` is
injective on `V`, that is, when no nonzero vector of one subspace is orthogonal to the other. A
pair whose gap `‖P_U - P_V‖` is less than `1` is acute, with no completeness or dimension
hypothesis. In finite dimension, `P_V` is injective on `U` exactly when every principal angle from
`U` to `V` is strictly below `π/2`, exactly when the directed gap `‖P_{Vᗮ} P_U‖` is less than `1`;
so for subspaces of equal dimension, acuteness is the condition `‖P_U - P_V‖ < 1`.

On this pole-free locus the *principal tangents* (`Submodule.principalTangents`) are the tangents
of the principal angles; a right angle records the junk value `Real.tan (π / 2) = 0`. They are the
quantities in which `tan Θ` perturbation bounds for spectral subspaces are stated.

A pair *avoids the quarter turn* (`Submodule.AvoidsQuarterTurn`) when no principal angle equals
`π/4`; this holds in particular when all principal angles are below `π/4`, which happens exactly
when the directed gap is less than `√2/2`.

## Main definitions

* `Submodule.IsAcute U V`: the orthogonal projection onto each subspace is injective on the other.
* `Submodule.principalTangents U V`: the tangents of the principal angles from `U` to `V`.
* `Submodule.AvoidsQuarterTurn U V`: no principal angle from `U` to `V` is `π/4`.

## Main results

* `Submodule.isAcute_iff_disjoint`: acuteness in terms of the subspaces `U ⊓ Vᗮ` and `V ⊓ Uᗮ`.
* `Submodule.IsAcute.of_projectionGap_lt_one`: a pair with gap less than `1` is acute.
* `Submodule.isAcute_iff_principalAngles_lt_pi_div_two`: in finite dimension, a pair is acute
  exactly when all principal angles in both directions are strictly below `π/2`;
  `Submodule.isAcute_iff_projectionGap_lt_one_of_finrank_eq` for subspaces of equal dimension.
* `Submodule.principalTangents_apply_eq_div`: `tan θᵢ = sᵢ / √(1 - sᵢ²)` for the principal
  sines `sᵢ`.
* `Submodule.arctan_principalTangents`, `Submodule.principalTangents_antitone`: on the pole-free
  locus the principal tangents recover the principal angles and are nonincreasing.
* `Submodule.AvoidsQuarterTurn.of_projectionGap_lt`: a pair with gap less than `√2/2` avoids the
  quarter turn, since then all principal angles are below `π/4`
  (`Submodule.principalAngles_lt_pi_div_four_iff`).

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §I.6.8.
-/

public section

noncomputable section

namespace Submodule

open Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ### Acute pairs -/

/-- A pair of subspaces `(U, V)` is *acute* when the orthogonal projection onto each of them is
injective on the other: no nonzero vector of one subspace is orthogonal to the other. -/
structure IsAcute : Prop where
  /-- The orthogonal projection onto `V` is injective on `U`. -/
  injOn_left : Set.InjOn V.starProjection U
  /-- The orthogonal projection onto `U` is injective on `V`. -/
  injOn_right : Set.InjOn U.starProjection V

variable {U V} in
/-- A pair is acute exactly when `U ⊓ Vᗮ = ⊥` and `V ⊓ Uᗮ = ⊥`. -/
theorem isAcute_iff_disjoint : U.IsAcute V ↔ Disjoint U Vᗮ ∧ Disjoint V Uᗮ := by
  rw [← injOn_starProjection_iff_disjoint, ← injOn_starProjection_iff_disjoint]
  exact ⟨fun h ↦ ⟨h.injOn_left, h.injOn_right⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable {U V} in
theorem IsAcute.symm (h : U.IsAcute V) : V.IsAcute U :=
  ⟨h.injOn_right, h.injOn_left⟩

theorem isAcute_comm : U.IsAcute V ↔ V.IsAcute U :=
  ⟨IsAcute.symm, IsAcute.symm⟩

/-- Every subspace makes an acute pair with itself. -/
theorem isAcute_self : U.IsAcute U :=
  isAcute_iff_disjoint.2 ⟨U.orthogonal_disjoint, U.orthogonal_disjoint⟩

/-- **Acuteness from the projection gap.** A pair of subspaces with `‖P_U - P_V‖ < 1` is acute. -/
theorem IsAcute.of_projectionGap_lt_one (h : U.projectionGap V < 1) : U.IsAcute V :=
  isAcute_iff_disjoint.2
    ⟨disjoint_orthogonal_of_directedProjectionGap_lt_one U V
        ((directedProjectionGap_le_projectionGap U V).trans_lt h),
      disjoint_orthogonal_of_directedProjectionGap_lt_one V U
        ((directedProjectionGap_le_projectionGap V U).trans_lt (projectionGap_comm U V ▸ h))⟩

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- In finite dimension, a pair of subspaces is acute exactly when all principal angles from `U`
to `V` and from `V` to `U` are strictly below `π/2`. -/
theorem isAcute_iff_principalAngles_lt_pi_div_two :
    U.IsAcute V ↔
      (∀ i, U.principalAngles V i < Real.pi / 2) ∧ ∀ i, V.principalAngles U i < Real.pi / 2 := by
  rw [isAcute_iff_disjoint, principalAngles_lt_pi_div_two_iff, principalAngles_lt_pi_div_two_iff]

/-- For subspaces of the same dimension, the pair is acute exactly when all principal angles from
`U` to `V` are strictly below `π/2`. -/
theorem isAcute_iff_principalAngles_lt_pi_div_two_of_finrank_eq
    (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.IsAcute V ↔ ∀ i, U.principalAngles V i < Real.pi / 2 := by
  rw [isAcute_iff_principalAngles_lt_pi_div_two, principalAngles_comm V U h.symm, and_self]

/-- For subspaces of the same dimension, the pair is acute exactly when `‖P_U - P_V‖ < 1`. -/
theorem isAcute_iff_projectionGap_lt_one_of_finrank_eq (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.IsAcute V ↔ U.projectionGap V < 1 := by
  rw [isAcute_iff_principalAngles_lt_pi_div_two_of_finrank_eq U V h,
    principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one,
    projectionGap_eq_directedProjectionGap_of_finrank_eq U V h]

/-! ### Principal tangents -/

/-- The principal tangents of `U` and `V`: the tangents of the principal angles from `U` to `V`,
in the order of the principal angles and padded with zeros. They are meaningful on the pole-free
locus where every principal angle is strictly below `π/2`
(`Submodule.principalAngles_lt_pi_div_two_iff`); a principal angle equal to `π/2` contributes
`Real.tan (π / 2) = 0`. -/
def principalTangents : ℕ →₀ ℝ :=
  (U.principalAngles V).mapRange Real.tan Real.tan_zero

theorem principalTangents_def :
    U.principalTangents V = (U.principalAngles V).mapRange Real.tan Real.tan_zero :=
  (rfl)

theorem principalTangents_apply (i : ℕ) :
    U.principalTangents V i = Real.tan (U.principalAngles V i) := by
  rw [principalTangents, Finsupp.mapRange_apply]

/-- The principal tangents in terms of the principal sines: `tan θᵢ = sᵢ / √(1 - sᵢ²)`. -/
theorem principalTangents_apply_eq_div (i : ℕ) :
    U.principalTangents V i = U.principalSines V i / √(1 - U.principalSines V i ^ 2) := by
  rw [principalTangents_apply, principalAngles_apply, Real.tan_arcsin]

theorem principalTangents_nonneg (i : ℕ) : 0 ≤ U.principalTangents V i := by
  rw [principalTangents_apply]
  exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two (principalAngles_nonneg U V i)
    (principalAngles_le_pi_div_two U V i)

/-- On the pole-free locus, the arctangents of the principal tangents are the principal angles. -/
theorem arctan_principalTangents (h : ∀ i, U.principalAngles V i < Real.pi / 2) (i : ℕ) :
    Real.arctan (U.principalTangents V i) = U.principalAngles V i := by
  rw [principalTangents_apply, Real.arctan_tan
    (by linarith [principalAngles_nonneg U V i, Real.pi_pos]) (h i)]

/-- On the pole-free locus, the principal tangents are nonincreasing. -/
theorem principalTangents_antitone (h : ∀ i, U.principalAngles V i < Real.pi / 2) :
    Antitone (U.principalTangents V) := fun i j hij ↦ by
  rw [← Real.arctan_strictMono.le_iff_le, arctan_principalTangents U V h,
    arctan_principalTangents U V h]
  exact principalAngles_antitone U V hij

/-- On the pole-free locus, the principal tangents all vanish exactly when `U ≤ V`. -/
theorem principalTangents_eq_zero_iff (h : ∀ i, U.principalAngles V i < Real.pi / 2) :
    U.principalTangents V = 0 ↔ U ≤ V := by
  rw [← principalAngles_eq_zero_iff, Finsupp.ext_iff, Finsupp.ext_iff]
  refine forall_congr' fun i ↦ ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · rw [← arctan_principalTangents U V h, hi, Finsupp.coe_zero, Pi.zero_apply, Real.arctan_zero]
  · rw [principalTangents_apply, hi, Finsupp.coe_zero, Pi.zero_apply, Real.tan_zero]

@[simp]
theorem principalTangents_self : U.principalTangents U = 0 := by
  ext i
  rw [principalTangents_apply, principalAngles_self, Finsupp.coe_zero, Pi.zero_apply,
    Real.tan_zero]

/-- There are at most `dim U` nonzero principal tangents. -/
theorem principalTangents_of_finrank_le {i : ℕ} (hi : finrank 𝕜 U ≤ i) :
    U.principalTangents V i = 0 := by
  rw [principalTangents_apply, principalAngles_of_finrank_le U V hi, Real.tan_zero]

/-- For subspaces of the same dimension, the principal tangents are symmetric in `U` and `V`. -/
theorem principalTangents_comm (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.principalTangents V = V.principalTangents U := by
  rw [principalTangents, principalTangents, principalAngles_comm U V h]

/-! ### Quarter-turn avoidance -/

/-- The pair `(U, V)` *avoids the quarter turn* when no principal angle from `U` to `V` equals
`π/4`. -/
def AvoidsQuarterTurn : Prop :=
  ∀ i, U.principalAngles V i ≠ Real.pi / 4

/-- The pair avoids the quarter turn exactly when no principal angle equals `π/4`. -/
theorem avoidsQuarterTurn_iff_principalAngles :
    U.AvoidsQuarterTurn V ↔ ∀ i, U.principalAngles V i ≠ Real.pi / 4 :=
  Iff.rfl

/-- The pair avoids the quarter turn exactly when no principal sine equals `√2/2`. -/
theorem avoidsQuarterTurn_iff : U.AvoidsQuarterTurn V ↔ ∀ i, U.principalSines V i ≠ √2 / 2 := by
  rw [avoidsQuarterTurn_iff_principalAngles]
  refine forall_congr' fun i ↦ not_congr ?_
  rw [principalAngles_apply, Real.arcsin_eq_iff_eq_sin
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, Real.sin_pi_div_four]

/-- **Quarter-turn avoidance on the diagonal.** Every subspace avoids the quarter turn with
itself. -/
theorem avoidsQuarterTurn_self : U.AvoidsQuarterTurn U := by
  refine (avoidsQuarterTurn_iff_principalAngles U U).2 fun i ↦ ?_
  rw [principalAngles_self, Finsupp.coe_zero, Pi.zero_apply]
  exact (div_pos Real.pi_pos four_pos).ne

/-- A pair whose directed gap is less than `√2/2` avoids the quarter turn. -/
theorem AvoidsQuarterTurn.of_directedProjectionGap_lt (h : U.directedProjectionGap V < √2 / 2) :
    U.AvoidsQuarterTurn V :=
  (avoidsQuarterTurn_iff_principalAngles U V).2 fun i ↦
    ((principalAngles_lt_pi_div_four_iff U V).2 h i).ne

/-- A pair whose gap `‖P_U - P_V‖` is less than `√2/2` avoids the quarter turn. -/
theorem AvoidsQuarterTurn.of_projectionGap_lt (h : U.projectionGap V < √2 / 2) :
    U.AvoidsQuarterTurn V :=
  .of_directedProjectionGap_lt U V ((directedProjectionGap_le_projectionGap U V).trans_lt h)

/-- For subspaces of the same dimension, quarter-turn avoidance is symmetric in `U` and `V`. -/
theorem avoidsQuarterTurn_comm (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.AvoidsQuarterTurn V ↔ V.AvoidsQuarterTurn U := by
  rw [avoidsQuarterTurn_iff_principalAngles, avoidsQuarterTurn_iff_principalAngles,
    principalAngles_comm U V h]

end FiniteDimensional

end Submodule
