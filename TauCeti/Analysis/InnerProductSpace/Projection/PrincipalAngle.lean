/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Principal angles between two subspaces

For subspaces `U` and `V` of an inner product space with orthogonal projections `P_U` and `P_V`,
the relative position of `U` and `V` is recorded by the two cross-projections

* the *cosine map* `P_V P_U`, which projects vectors of `U` onto `V`, and
* the *directed sine map* `P_{Vᗮ} P_U`, which keeps the component of a vector of `U` orthogonal
  to `V`,

together with the *double-angle operator* `2 P_{Uᗮ} P_V P_U`, the off-diagonal `U → Uᗮ` block of
`2 P_V`, in which `sin 2Θ` bounds are stated.

In finite dimension the singular values of the cosine map and of the directed sine map are the
*principal cosines* and the *principal sines* of `U` and `V`, each listed in nonincreasing order
and padded with zeros, and the *principal angles* are the arcsines of the principal sines, so they
lie in `[0, π/2]`. These are the quantities in which perturbation bounds for spectral subspaces
(the Davis–Kahan `sin Θ` theorems) are stated; the operator norm of the directed sine map is the
directed gap `Submodule.directedProjectionGap U V`.

The principal cosines are symmetric in `U` and `V`. The principal sines are symmetric only when
`U` and `V` have the same finite dimension (`Submodule.principalSines_comm`), the main result of
this file. Without the dimension hypothesis the statement fails: for a line `U` inside a plane
`V`, all principal sines of `U` and `V` vanish but one principal sine of `V` and `U` is `1`.

## Main definitions

* `Submodule.cosThetaMap U V`: the cosine map `P_V P_U`.
* `Submodule.sinThetaMap U V`: the directed sine map `P_{Vᗮ} P_U`.
* `Submodule.sinTwoAngleOperator U V`: the double-angle operator `2 P_{Uᗮ} P_V P_U`.
* `Submodule.principalCosines U V`, `Submodule.principalSines U V`: the singular values of the
  cosine map and of the directed sine map.
* `Submodule.principalAngles U V`: the arcsines of the principal sines.

## Main results

* `Submodule.principalCosines_comm`: the principal cosines are symmetric in `U` and `V`.
* `Submodule.principalSines_comm`, `Submodule.principalAngles_comm`: for subspaces of the same
  dimension, the principal sines and the principal angles are symmetric in `U` and `V`.
* `Submodule.principalSines_eq_zero_iff`, `Submodule.principalAngles_eq_zero_iff`: all principal
  angles of `U` and `V` vanish exactly when `U ≤ V`; in particular the principal angles of a
  subspace with itself vanish (`Submodule.principalAngles_self`).
* `Submodule.principalCosines_eq_zero_iff`: all principal cosines vanish exactly when `U ⟂ V`.
* `Submodule.sin_principalAngles`: the sine of the `i`-th principal angle is the `i`-th principal
  sine.
* `Submodule.principalSines_zero`: the largest principal sine is the directed gap `‖P_{Vᗮ} P_U‖`;
  hence `Submodule.forall_principalSines_lt_iff`: all principal sines are below `c` exactly when
  the directed gap is.
* `Submodule.ncard_ofPred_principalAngles_eq_pi_div_two`: the number of principal angles from `U`
  to `V` equal to `π/2` is `dim (U ⊓ Vᗮ)`; hence `Submodule.principalAngles_lt_pi_div_two_iff`:
  all of them are strictly below `π/2` exactly when no nonzero vector of `U` is orthogonal to `V`.
* `Submodule.directedProjectionGap_lt_one_iff`: the directed gap from `U` to `V` is less than `1`
  exactly when no nonzero vector of `U` is orthogonal to `V`.
* `Submodule.principalAngles_lt_pi_div_four_iff`: all principal angles are below `π/4` exactly
  when the directed gap is less than `√2/2`.
* `Submodule.norm_sinTwoAngleOperator_le_one`: the double-angle operator is a contraction, and
  `Submodule.sinTwoAngleOperator_eq_zero_iff`: it vanishes exactly when `P_U` and `P_V` commute.

## References

* Å. Björck, G. H. Golub, *Numerical methods for computing angles between linear subspaces*,
  Math. Comp. **27** (1973), 579–594.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.1.
-/

public section

noncomputable section

namespace Submodule

open Module Module.End
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ### The cross-projections -/

/-- The cosine map `P_V P_U` of two subspaces with orthogonal projections. -/
def cosThetaMap : E →L[𝕜] E :=
  V.starProjection ∘L U.starProjection

/-- The directed sine map `P_{Vᗮ} P_U` of two subspaces with orthogonal projections: it keeps the
component orthogonal to `V` of the projection of a vector onto `U`. -/
def sinThetaMap : E →L[𝕜] E :=
  Vᗮ.starProjection ∘L U.starProjection

theorem cosThetaMap_def : U.cosThetaMap V = V.starProjection ∘L U.starProjection :=
  (rfl)

theorem sinThetaMap_def : U.sinThetaMap V = Vᗮ.starProjection ∘L U.starProjection :=
  (rfl)

@[simp]
theorem cosThetaMap_apply (x : E) :
    U.cosThetaMap V x = V.starProjection (U.starProjection x) :=
  (rfl)

@[simp]
theorem sinThetaMap_apply (x : E) :
    U.sinThetaMap V x = Vᗮ.starProjection (U.starProjection x) :=
  (rfl)

/-- The cosine and sine maps split the projection onto `U`: `P_V P_U + P_{Vᗮ} P_U = P_U`. -/
theorem cosThetaMap_add_sinThetaMap :
    U.cosThetaMap V + U.sinThetaMap V = U.starProjection := by
  ext x
  simp

/-- The operator norm of the directed sine map is the directed gap from `U` to `V`. -/
theorem norm_sinThetaMap : ‖U.sinThetaMap V‖ = U.directedProjectionGap V := by
  rw [sinThetaMap_def, directedProjectionGap_def]

theorem norm_cosThetaMap_le_one : ‖U.cosThetaMap V‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans <| (mul_le_mul (starProjection_norm_le V)
    (starProjection_norm_le U) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem norm_sinThetaMap_le_one : ‖U.sinThetaMap V‖ ≤ 1 :=
  norm_sinThetaMap U V ▸ directedProjectionGap_le_one U V

/-- The cosine map vanishes exactly when `U` and `V` are orthogonal. -/
@[simp]
theorem cosThetaMap_eq_zero_iff : U.cosThetaMap V = 0 ↔ U ⟂ V := by
  rw [cosThetaMap_def, starProjection_comp_starProjection_eq_zero_iff, isOrtho_comm]

/-- The directed sine map vanishes exactly when `U ≤ V`. -/
@[simp]
theorem sinThetaMap_eq_zero_iff : U.sinThetaMap V = 0 ↔ U ≤ V := by
  rw [← norm_eq_zero, norm_sinThetaMap, directedProjectionGap_eq_zero_iff]

@[simp]
theorem sinThetaMap_self : U.sinThetaMap U = 0 :=
  (sinThetaMap_eq_zero_iff U U).2 le_rfl

/-! ### The double-angle operator -/

/-- The double-angle operator `2 P_{Uᗮ} P_V P_U` of two subspaces with orthogonal projections: the
off-diagonal `U → Uᗮ` block of `2 P_V` relative to `E = U ⊕ Uᗮ`. It is the operator in which
`sin 2Θ` perturbation bounds for spectral subspaces are stated. -/
def sinTwoAngleOperator : E →L[𝕜] E :=
  (2 : 𝕜) • (Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection)

theorem sinTwoAngleOperator_def :
    U.sinTwoAngleOperator V =
      (2 : 𝕜) • (Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection) :=
  (rfl)

@[simp]
theorem sinTwoAngleOperator_apply (x : E) :
    U.sinTwoAngleOperator V x =
      (2 : 𝕜) • Uᗮ.starProjection (V.starProjection (U.starProjection x)) :=
  (rfl)

/-- The double-angle operator is twice the directed sine map from `V` to `U` composed with the
cosine map from `U` to `V`: `2 P_{Uᗮ} P_V P_U = 2 (P_{Uᗮ} P_V) (P_V P_U)`. -/
theorem sinTwoAngleOperator_eq_smul_sinThetaMap_comp_cosThetaMap :
    U.sinTwoAngleOperator V = (2 : 𝕜) • (V.sinThetaMap U ∘L U.cosThetaMap V) := by
  ext x
  simp [starProjection_eq_self_iff.2 (V.starProjection_apply_mem _)]

/-- **The double-angle operator is a contraction**: `‖2 P_{Uᗮ} P_V P_U‖ ≤ 1`, the operator form of
`sin 2θ ≤ 1`. -/
theorem norm_sinTwoAngleOperator_le_one : ‖U.sinTwoAngleOperator V‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  set u := U.starProjection x
  set v := V.starProjection u
  -- `‖v‖² = ⟪P_V u, u⟫ = ⟪P_U v, u⟫ ≤ ‖P_U v‖ ‖u‖` since `u ∈ U`.
  have hv : ‖v‖ ^ 2 ≤ ‖U.starProjection v‖ * ‖u‖ := by
    have h : ⟪v, v⟫_𝕜 = ⟪U.starProjection v, u⟫_𝕜 := by
      calc ⟪v, v⟫_𝕜 = ⟪V.starProjection v, u⟫_𝕜 :=
            (inner_starProjection_left_eq_right V _ _).symm
        _ = ⟪v, U.starProjection u⟫_𝕜 := by
            rw [starProjection_eq_self_iff.2 (V.starProjection_apply_mem u),
              starProjection_eq_self_iff.2 (U.starProjection_apply_mem x)]
        _ = ⟪U.starProjection v, u⟫_𝕜 := (inner_starProjection_left_eq_right U _ _).symm
    rw [@norm_sq_eq_re_inner 𝕜, h]
    exact re_inner_le_norm _ _
  -- With Pythagoras `‖v‖² = ‖P_U v‖² + ‖P_{Uᗮ} v‖²`, this gives `4 ‖P_{Uᗮ} v‖² ≤ ‖u‖²`.
  have hpy := norm_sq_eq_add_norm_sq_starProjection v U
  have hu : ‖u‖ ≤ ‖x‖ := U.norm_starProjection_apply_le x
  have hsq : (2 * ‖Uᗮ.starProjection v‖) ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u‖ - 2 * ‖U.starProjection v‖)]
  have h2 : 2 * ‖Uᗮ.starProjection v‖ ≤ ‖u‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq
  rw [sinTwoAngleOperator_apply, norm_smul, RCLike.norm_ofNat, one_mul]
  exact h2.trans hu

/-- The double-angle operator vanishes when `U ≤ V`. -/
theorem sinTwoAngleOperator_eq_zero_of_le (h : U ≤ V) : U.sinTwoAngleOperator V = 0 := by
  have hVU : V.starProjection ∘L U.starProjection = U.starProjection := by
    ext x
    exact starProjection_eq_self_iff.2 (h (U.starProjection_apply_mem x))
  rw [sinTwoAngleOperator_def, hVU,
    (isOrtho_orthogonal_left U).starProjection_comp_starProjection, smul_zero]

/-- The double-angle operator vanishes when `U` and `V` are orthogonal. -/
theorem sinTwoAngleOperator_eq_zero_of_isOrtho (h : U ⟂ V) : U.sinTwoAngleOperator V = 0 := by
  rw [sinTwoAngleOperator_eq_smul_sinThetaMap_comp_cosThetaMap,
    (cosThetaMap_eq_zero_iff U V).2 h, ContinuousLinearMap.comp_zero, smul_zero]

@[simp]
theorem sinTwoAngleOperator_self : U.sinTwoAngleOperator U = 0 :=
  sinTwoAngleOperator_eq_zero_of_le U U le_rfl

/-- The double-angle operator vanishes exactly when the orthogonal projections onto `U` and `V`
commute. -/
@[simp]
theorem sinTwoAngleOperator_eq_zero_iff :
    U.sinTwoAngleOperator V = 0 ↔ Commute U.starProjection V.starProjection := by
  rw [commute_iff_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  constructor
  · intro h
    -- `P_{Uᗮ} P_V P_U = 0` says that `P_V P_U` takes values in `U`, so `P_U P_V P_U = P_V P_U`.
    have hU (x : E) : U.starProjection (V.starProjection (U.starProjection x)) =
        V.starProjection (U.starProjection x) := by
      have hx := congrArg (· x) h
      simp only [sinTwoAngleOperator_apply, zero_apply, smul_eq_zero,
        two_ne_zero, false_or, starProjection_apply_eq_zero_iff, orthogonal_orthogonal] at hx
      exact starProjection_eq_self_iff.2 hx
    -- Taking adjoints, `P_U P_V = P_U P_V P_U = P_V P_U`.
    refine ContinuousLinearMap.ext fun y ↦ ext_inner_left 𝕜 fun z ↦ ?_
    calc ⟪z, U.starProjection (V.starProjection y)⟫_𝕜
        = ⟪V.starProjection (U.starProjection z), y⟫_𝕜 := by
          rw [← inner_starProjection_left_eq_right U, inner_starProjection_left_eq_right V]
      _ = ⟪U.starProjection (V.starProjection (U.starProjection z)), y⟫_𝕜 := by rw [hU]
      _ = ⟪z, U.starProjection (V.starProjection (U.starProjection y))⟫_𝕜 := by
          rw [inner_starProjection_left_eq_right U, inner_starProjection_left_eq_right V,
            inner_starProjection_left_eq_right U]
      _ = ⟪z, V.starProjection (U.starProjection y)⟫_𝕜 := by rw [hU]
  · intro h
    rw [sinTwoAngleOperator_def, ← h, ← ContinuousLinearMap.comp_assoc,
      (isOrtho_orthogonal_left U).starProjection_comp_starProjection,
      ContinuousLinearMap.zero_comp, smul_zero]

/-! ### Principal cosines, sines and angles -/

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- The principal cosines of `U` and `V`: the singular values of the cosine map `P_V P_U`, in
nonincreasing order and padded with zeros. -/
def principalCosines : ℕ →₀ ℝ :=
  (U.cosThetaMap V : E →ₗ[𝕜] E).singularValues

/-- The principal sines of `U` and `V`: the singular values of the directed sine map
`P_{Vᗮ} P_U`, in nonincreasing order and padded with zeros. -/
def principalSines : ℕ →₀ ℝ :=
  (U.sinThetaMap V : E →ₗ[𝕜] E).singularValues

/-- The principal angles of `U` and `V`: the arcsines of the principal sines. They lie in
`[0, π/2]` and are listed in nonincreasing order. -/
def principalAngles : ℕ →₀ ℝ :=
  (U.principalSines V).mapRange Real.arcsin Real.arcsin_zero

theorem principalCosines_def :
    U.principalCosines V = (U.cosThetaMap V : E →ₗ[𝕜] E).singularValues :=
  (rfl)

theorem principalSines_def :
    U.principalSines V = (U.sinThetaMap V : E →ₗ[𝕜] E).singularValues :=
  (rfl)

theorem principalAngles_def :
    U.principalAngles V = (U.principalSines V).mapRange Real.arcsin Real.arcsin_zero :=
  (rfl)

theorem principalAngles_apply (i : ℕ) :
    U.principalAngles V i = Real.arcsin (U.principalSines V i) := by
  rw [principalAngles, Finsupp.mapRange_apply]

theorem principalCosines_nonneg (i : ℕ) : 0 ≤ U.principalCosines V i :=
  LinearMap.singularValues_nonneg _ i

theorem principalSines_nonneg (i : ℕ) : 0 ≤ U.principalSines V i :=
  LinearMap.singularValues_nonneg _ i

theorem principalCosines_le_one (i : ℕ) : U.principalCosines V i ≤ 1 :=
  LinearMap.singularValues_le_of_norm_apply_le zero_le_one
    (fun x ↦ (U.cosThetaMap V).le_of_opNorm_le (norm_cosThetaMap_le_one U V) x) i

theorem principalSines_le_one (i : ℕ) : U.principalSines V i ≤ 1 :=
  LinearMap.singularValues_le_of_norm_apply_le zero_le_one
    (fun x ↦ (U.sinThetaMap V).le_of_opNorm_le (norm_sinThetaMap_le_one U V) x) i

theorem principalCosines_antitone : Antitone (U.principalCosines V) :=
  LinearMap.singularValues_antitone _

theorem principalSines_antitone : Antitone (U.principalSines V) :=
  LinearMap.singularValues_antitone _

theorem principalAngles_antitone : Antitone (U.principalAngles V) := fun i j hij ↦ by
  simpa only [principalAngles_apply] using
    Real.arcsin_le_arcsin (principalSines_antitone U V hij)

theorem principalAngles_nonneg (i : ℕ) : 0 ≤ U.principalAngles V i := by
  simpa only [principalAngles_apply] using Real.arcsin_nonneg.2 (principalSines_nonneg U V i)

theorem principalAngles_le_pi_div_two (i : ℕ) : U.principalAngles V i ≤ Real.pi / 2 := by
  simpa only [principalAngles_apply] using Real.arcsin_le_pi_div_two _

/-- The sine of the `i`-th principal angle is the `i`-th principal sine. -/
@[simp]
theorem sin_principalAngles (i : ℕ) : Real.sin (U.principalAngles V i) = U.principalSines V i := by
  rw [principalAngles_apply, Real.sin_arcsin (by linarith [principalSines_nonneg U V i])
    (principalSines_le_one U V i)]

/-- The largest principal sine from `U` to `V` is the directed gap `‖P_{Vᗮ} P_U‖`. -/
theorem principalSines_zero : U.principalSines V 0 = U.directedProjectionGap V := by
  rw [principalSines_def, ← ContinuousLinearMap.singularValue_eq_linearMap_singularValues,
    ContinuousLinearMap.singularValue_zero, coe_nnnorm, norm_sinThetaMap]

/-- All principal sines from `U` to `V` are below `c` exactly when the largest one, the directed
gap `‖P_{Vᗮ} P_U‖`, is. -/
theorem forall_principalSines_lt_iff {c : ℝ} :
    (∀ i, U.principalSines V i < c) ↔ U.directedProjectionGap V < c := by
  rw [← principalSines_zero]
  exact ⟨fun h ↦ h 0, fun h i ↦ (principalSines_antitone U V (Nat.zero_le i)).trans_lt h⟩

/-- There are at most `dim U` nonzero principal cosines. -/
theorem principalCosines_of_finrank_le {i : ℕ} (hi : finrank 𝕜 U ≤ i) :
    U.principalCosines V i = 0 := by
  rw [principalCosines_def, LinearMap.singularValues_eq_zero_iff_le_finrank_range]
  exact (finrank_range_comp_starProjection_le U _).trans hi

/-- There are at most `dim U` nonzero principal sines. -/
theorem principalSines_of_finrank_le {i : ℕ} (hi : finrank 𝕜 U ≤ i) :
    U.principalSines V i = 0 := by
  rw [principalSines_def, LinearMap.singularValues_eq_zero_iff_le_finrank_range]
  exact (finrank_range_comp_starProjection_le U _).trans hi

/-- There are at most `dim U` nonzero principal angles. -/
theorem principalAngles_of_finrank_le {i : ℕ} (hi : finrank 𝕜 U ≤ i) :
    U.principalAngles V i = 0 := by
  rw [principalAngles_apply, principalSines_of_finrank_le U V hi, Real.arcsin_zero]

/-- The principal cosines of `U` and `V` all vanish exactly when `U` and `V` are orthogonal. -/
@[simp]
theorem principalCosines_eq_zero_iff : U.principalCosines V = 0 ↔ U ⟂ V := by
  rw [principalCosines_def, LinearMap.singularValues_eq_zero_iff,
    ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj, cosThetaMap_eq_zero_iff]

/-- The principal sines of `U` and `V` all vanish exactly when `U ≤ V`. -/
@[simp]
theorem principalSines_eq_zero_iff : U.principalSines V = 0 ↔ U ≤ V := by
  rw [principalSines_def, LinearMap.singularValues_eq_zero_iff,
    ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj, sinThetaMap_eq_zero_iff]

/-- The principal angles of `U` and `V` all vanish exactly when `U ≤ V`. -/
@[simp]
theorem principalAngles_eq_zero_iff : U.principalAngles V = 0 ↔ U ≤ V := by
  simp only [← principalSines_eq_zero_iff, Finsupp.ext_iff, principalAngles_apply,
    Finsupp.coe_zero, Pi.zero_apply, Real.arcsin_eq_zero_iff]

@[simp]
theorem principalSines_self : U.principalSines U = 0 :=
  (principalSines_eq_zero_iff U U).2 le_rfl

/-- The principal angles of a subspace with itself vanish. -/
@[simp]
theorem principalAngles_self : U.principalAngles U = 0 :=
  (principalAngles_eq_zero_iff U U).2 le_rfl

/-- The principal cosines are symmetric in the two subspaces. -/
theorem principalCosines_comm : U.principalCosines V = V.principalCosines U := by
  rw [principalCosines_def, ← LinearMap.singularValues_adjoint, cosThetaMap_def,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.adjoint_comp,
    V.starProjection_isSymmetric.adjoint_eq, U.starProjection_isSymmetric.adjoint_eq,
    principalCosines_def, cosThetaMap_def, ContinuousLinearMap.toLinearMap_comp]

/-! ### Symmetry of the principal sines -/

/-- The Gram operator of the directed sine map is `P_U P_{Vᗮ} P_U = P_U - P_U P_V P_U`. -/
private theorem adjoint_comp_sinThetaMap_apply (x : E) :
    (LinearMap.adjoint (U.sinThetaMap V : E →ₗ[𝕜] E) ∘ₗ (U.sinThetaMap V : E →ₗ[𝕜] E)) x =
      U.starProjection x - U.starProjection (V.starProjection (U.starProjection x)) := by
  rw [sinThetaMap_def, ContinuousLinearMap.toLinearMap_comp, LinearMap.adjoint_comp,
    Vᗮ.starProjection_isSymmetric.adjoint_eq, U.starProjection_isSymmetric.adjoint_eq]
  have hP (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (y : E) :
      K.starProjection (K.starProjection y) = K.starProjection y :=
    starProjection_eq_self_iff.2 (K.starProjection_apply_mem y)
  simp [map_sub, hP]

/-- For `t ≠ 0`, the `t`-eigenvectors of the Gram operator `P_U P_{Vᗮ} P_U` of the directed sine
map are the vectors `x ∈ U` with `P_U P_V x = (1 - t) x`. -/
private theorem mem_eigenspace_sinThetaMap_iff {t : 𝕜} (ht : t ≠ 0) (x : E) :
    x ∈ eigenspace (LinearMap.adjoint (U.sinThetaMap V : E →ₗ[𝕜] E) ∘ₗ
        (U.sinThetaMap V : E →ₗ[𝕜] E)) t ↔
      x ∈ U ∧ U.starProjection (V.starProjection x) = (1 - t) • x := by
  rw [mem_eigenspace_iff, adjoint_comp_sinThetaMap_apply]
  constructor
  · intro h
    -- Applying `P_U` to the eigenvalue equation gives `t • P_U x = t • x`, so `x ∈ U`.
    have hP (y : E) : U.starProjection (U.starProjection y) = U.starProjection y :=
      starProjection_eq_self_iff.2 (U.starProjection_apply_mem y)
    have hU : U.starProjection x = x := by
      refine smul_right_injective E ht (?_ : t • U.starProjection x = t • x)
      rw [← map_smul, ← h, map_sub, hP, hP]
    refine ⟨starProjection_eq_self_iff.1 hU, ?_⟩
    rw [hU] at h
    rw [sub_smul, one_smul, ← h, sub_sub_cancel]
  · rintro ⟨hx, h⟩
    rw [starProjection_eq_self_iff.2 hx, h, sub_smul, one_smul, sub_sub_cancel]

/-- Away from `0` and `1`, the `t`-eigenspace of the Gram operator `P_U P_{Vᗮ} P_U` of the directed
sine map is the `(1 - t)`-eigenspace of `P_U P_V`. -/
private theorem eigenspace_sinThetaMap_of_ne {t : 𝕜} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    eigenspace (LinearMap.adjoint (U.sinThetaMap V : E →ₗ[𝕜] E) ∘ₗ
        (U.sinThetaMap V : E →ₗ[𝕜] E)) t =
      eigenspace ((U.starProjection : E →ₗ[𝕜] E) ∘ₗ (V.starProjection : E →ₗ[𝕜] E)) (1 - t) := by
  ext x
  rw [mem_eigenspace_sinThetaMap_iff U V ht₀, mem_eigenspace_iff, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, and_iff_right_iff_imp]
  intro h
  -- `x = (1 - t)⁻¹ • P_U (P_V x)` lies in `U`.
  rw [← inv_smul_smul₀ (sub_ne_zero.2 ht₁.symm) x, ← h]
  exact U.smul_mem _ (U.starProjection_apply_mem _)

/-- The `1`-eigenspace of the Gram operator `P_U P_{Vᗮ} P_U` of the directed sine map is
`U ⊓ Vᗮ`. -/
private theorem eigenspace_sinThetaMap_one :
    eigenspace (LinearMap.adjoint (U.sinThetaMap V : E →ₗ[𝕜] E) ∘ₗ
        (U.sinThetaMap V : E →ₗ[𝕜] E)) 1 = U ⊓ Vᗮ := by
  ext x
  rw [mem_eigenspace_sinThetaMap_iff U V one_ne_zero, sub_self, zero_smul, mem_inf,
    ← starProjection_apply_eq_zero_iff]
  refine and_congr_right fun hx ↦
    ⟨fun h ↦ (inner_self_eq_zero (𝕜 := 𝕜)).1 ?_, fun h ↦ by rw [h, map_zero]⟩
  -- `‖P_V x‖² = ⟪P_V x, x⟫ = ⟪P_V x, P_U x⟫ = ⟪P_U P_V x, x⟫ = 0`.
  calc ⟪V.starProjection x, V.starProjection x⟫_𝕜
      = ⟪V.starProjection (V.starProjection x), x⟫_𝕜 :=
        (inner_starProjection_left_eq_right V _ _).symm
    _ = ⟪V.starProjection x, U.starProjection x⟫_𝕜 := by
        rw [starProjection_eq_self_iff.2 (V.starProjection_apply_mem x),
          starProjection_eq_self_iff.2 hx]
    _ = ⟪U.starProjection (V.starProjection x), x⟫_𝕜 :=
        (inner_starProjection_left_eq_right U _ _).symm
    _ = 0 := by rw [h, inner_zero_left]

/-- **Equal-rank symmetry of the principal sines.** For subspaces of the same dimension, the
principal sines of `U` and `V` are those of `V` and `U`. -/
theorem principalSines_comm (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.principalSines V = V.principalSines U := by
  -- The `t`-eigenvectors of the Gram operator `P_U P_{Vᗮ} P_U` of the sine map are, for
  -- `t ≠ 0, 1`, the `(1 - t)`-eigenvectors of `P_U P_V`, whose nonzero eigenvalues are those of
  -- `P_V P_U` with the same multiplicities, while its `1`-eigenspace is `U ⊓ Vᗮ`, whose dimension
  -- matches that of `V ⊓ Uᗮ` when `dim U = dim V`.
  refine Finsupp.eq_of_antitone_of_ncard_eq (principalSines_antitone U V)
    (principalSines_antitone V U) fun s hs ↦ ?_
  rcases hs.lt_or_gt with hs | hs
  · -- No principal sine is negative.
    have hempty (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
        {i | U.principalSines V i = s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (principalSines_nonneg U V i).not_gt (hi ▸ hs)
    rw [hempty U V, hempty V U]
  rw [principalSines_def, principalSines_def, LinearMap.ncard_ofPred_singularValues_eq _ hs,
    LinearMap.ncard_ofPred_singularValues_eq _ hs]
  have ht₀ : ((s ^ 2 : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast (pow_pos hs 2).ne'
  by_cases ht₁ : ((s ^ 2 : ℝ) : 𝕜) = 1
  · rw [ht₁, eigenspace_sinThetaMap_one, eigenspace_sinThetaMap_one,
      finrank_inf_orthogonal_comm U V h]
  · rw [eigenspace_sinThetaMap_of_ne U V ht₀ ht₁, eigenspace_sinThetaMap_of_ne V U ht₀ ht₁]
    exact finrank_eigenspace_comp_comm _ _ (sub_ne_zero.2 (Ne.symm ht₁)).isUnit

/-- **Equal-rank symmetry of the principal angles.** For subspaces of the same dimension, the
principal angles of `U` and `V` are those of `V` and `U`. -/
theorem principalAngles_comm (h : finrank 𝕜 U = finrank 𝕜 V) :
    U.principalAngles V = V.principalAngles U := by
  rw [principalAngles, principalAngles, principalSines_comm U V h]

/-! ### Right principal angles -/

/-- **Counting right principal angles.** The number of principal angles from `U` to `V` equal to
`π/2` is the dimension of `U ⊓ Vᗮ`, the subspace of vectors of `U` orthogonal to `V`. -/
theorem ncard_ofPred_principalAngles_eq_pi_div_two :
    {i | U.principalAngles V i = Real.pi / 2}.ncard = finrank 𝕜 ↥(U ⊓ Vᗮ) := by
  have hset : {i | U.principalAngles V i = Real.pi / 2} = {i | U.principalSines V i = 1} := by
    ext i
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, principalAngles_apply, Real.arcsin_eq_pi_div_two]
    exact ⟨fun h ↦ le_antisymm (principalSines_le_one U V i) h, ge_of_eq⟩
  rw [hset, principalSines_def, LinearMap.ncard_ofPred_singularValues_eq _ one_pos, one_pow,
    RCLike.ofReal_one, eigenspace_sinThetaMap_one]

/-- All principal angles from `U` to `V` are strictly below `π/2` exactly when no nonzero vector
of `U` is orthogonal to `V`. -/
theorem principalAngles_lt_pi_div_two_iff :
    (∀ i, U.principalAngles V i < Real.pi / 2) ↔ Disjoint U Vᗮ := by
  have hfin : {i | U.principalAngles V i = Real.pi / 2}.Finite :=
    (U.principalAngles V).hasFiniteSupport.subset fun i (hi : _ = _) ↦ by
      rw [Function.mem_support, hi]
      positivity
  rw [disjoint_iff, ← Submodule.finrank_eq_zero, ← ncard_ofPred_principalAngles_eq_pi_div_two,
    Set.ncard_eq_zero hfin, Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun i ↦ (principalAngles_le_pi_div_two U V i).lt_iff_ne

/-- All principal angles from `U` to `V` are strictly below `π/2` exactly when the directed gap
`‖P_{Vᗮ} P_U‖`, the largest principal sine, is less than `1`. -/
theorem principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one :
    (∀ i, U.principalAngles V i < Real.pi / 2) ↔ U.directedProjectionGap V < 1 := by
  simp only [principalAngles_apply, Real.arcsin_lt_pi_div_two]
  exact forall_principalSines_lt_iff U V

/-- In finite dimension, the directed gap `‖P_{Vᗮ} P_U‖` from `U` to `V` is less than `1` exactly
when no nonzero vector of `U` is orthogonal to `V`. -/
theorem directedProjectionGap_lt_one_iff : U.directedProjectionGap V < 1 ↔ Disjoint U Vᗮ := by
  rw [← principalAngles_lt_pi_div_two_iff_directedProjectionGap_lt_one,
    principalAngles_lt_pi_div_two_iff]

/-- All principal angles from `U` to `V` are strictly below `π/4` exactly when the directed gap
`‖P_{Vᗮ} P_U‖` is less than `√2/2`. -/
theorem principalAngles_lt_pi_div_four_iff :
    (∀ i, U.principalAngles V i < Real.pi / 4) ↔ U.directedProjectionGap V < √2 / 2 := by
  have hπ : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs (i : ℕ) : U.principalSines V i ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [principalSines_nonneg U V i], principalSines_le_one U V i⟩
  simp only [principalAngles_apply, Real.arcsin_lt_iff_lt_sin (hs _) hπ, Real.sin_pi_div_four]
  exact forall_principalSines_lt_iff U V

end FiniteDimensional

end Submodule
