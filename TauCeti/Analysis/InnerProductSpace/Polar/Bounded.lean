/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# The polar decomposition of a bounded operator

Every bounded operator `T : E →L[𝕜] F` between Hilbert spaces over `RCLike 𝕜` factors as
`T = U |T|`, where `|T| = T.modulus` is its modulus and `U` is a partial isometry. The canonical
polar factor `T.polarFactor` is the continuous extension of the isometric rule `|T| x ↦ T x` from
the range of `|T|` to its closure, extended by zero on the orthogonal complement. It is the
canonical factor `T.factorThru T.modulus` of `T` through its modulus. No finite dimension is
assumed; for linear maps between finite-dimensional spaces the corresponding factor is
`LinearMap.polarFactor`.

The initial space of `U` is the closure of the range of `|T|`, which is `(ker T)ᗮ`, and its final
space is the closure of the range of `T`; its initial and final projections `U† U` and `U U†` are
the orthogonal projections onto these spaces. The polar factor is the unique bounded operator `V`
with `V |T| = T` that vanishes on `ker T`.

The adjoint of the polar factor inverts it on the modulus, `U† T = |T|`, and conjugates the two
moduli into each other, `|T†| = T U† = U |T| U†`. Consequently the polar factor of `T†` is `U†`,
and `T = |T†| U` is the left polar decomposition. When `T` is injective the polar factor is an
isometry, and when `|T|` is invertible it is `T |T|⁻¹`.

## Main declarations

* `ContinuousLinearMap.polarFactor`: the canonical polar partial isometry of a bounded operator.
* `ContinuousLinearMap.polarFactor_comp_modulus`: the polar decomposition `U |T| = T`.
* `ContinuousLinearMap.isPartialIsometry_polarFactor`: `U` is a partial isometry.
* `ContinuousLinearMap.ker_polarFactor`, `ContinuousLinearMap.range_polarFactor`: `ker U = ker T`
  and the range of `U` is the closure of the range of `T`.
* `ContinuousLinearMap.adjoint_polarFactor_comp_polarFactor`,
  `ContinuousLinearMap.polarFactor_comp_adjoint_polarFactor`: the initial and final projections.
* `ContinuousLinearMap.eq_polarFactor_iff`: uniqueness of the polar factor.
* `ContinuousLinearMap.modulus_adjoint`: `|T†| = T U†`.
* `ContinuousLinearMap.polarFactor_adjoint`: the polar factor of `T†` is `U†`.
* `ContinuousLinearMap.modulus_adjoint_comp_polarFactor`: the left polar decomposition
  `|T†| U = T`.
* `ContinuousLinearMap.polarFactor_eq_comp_inverse`: `U = T |T|⁻¹` when `|T|` is invertible.
* `ContinuousLinearMap.norm_sub_polarFactor_le`: `‖T - U‖ ≤ ‖|T| - 1‖` for an endomorphism `T`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §VIII.3.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  ed., Academic Press (1980), Theorem VI.10.
-/

public section

noncomputable section

open scoped InnerProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **polar factor** of a bounded operator `T`: the canonical polar partial isometry, which
sends `|T| x` to `T x` and vanishes on `ker T`. It is the canonical factor of `T` through its
modulus. -/
def polarFactor (T : E →L[𝕜] F) : E →L[𝕜] F :=
  T.factorThru T.modulus

variable (T : E →L[𝕜] F)

/-- The polar factor is the canonical factor of `T` through its modulus. -/
theorem polarFactor_eq_factorThru : T.polarFactor = T.factorThru T.modulus :=
  (rfl)

/-- The polar factor carries the modulus of a vector to its image under `T`:
`U (|T| x) = T x`. -/
@[simp]
theorem polarFactor_modulus_apply (x : E) : T.polarFactor (T.modulus x) = T x :=
  factorThru_apply_apply ⟨1, fun x ↦ by rw [one_mul, norm_modulus_apply]⟩ x

/-- **Polar decomposition** of a bounded operator: `U |T| = T`. -/
@[simp]
theorem polarFactor_comp_modulus : T.polarFactor ∘L T.modulus = T :=
  ext T.polarFactor_modulus_apply

/-- The polar factor vanishes on the kernel of `T`. -/
@[simp]
theorem polarFactor_apply_of_mem_ker {x : E} (hx : x ∈ T.ker) : T.polarFactor x = 0 :=
  factorThru_apply_of_mem_orthogonal (by rwa [orthogonal_range_modulus])

/-- The polar factor has the same kernel as `T`. -/
@[simp]
theorem ker_polarFactor : T.polarFactor.ker = T.ker :=
  ker_factorThru_of_isStarNormal (fun x ↦ (T.norm_modulus_apply x).symm)
    T.isSelfAdjoint_modulus.isStarNormal

/-- The polar factor preserves norms on its initial space `(ker T)ᗮ`. -/
theorem norm_polarFactor_apply {x : E} (hx : x ∈ T.kerᗮ) : ‖T.polarFactor x‖ = ‖x‖ :=
  norm_factorThru_apply (fun x ↦ (T.norm_modulus_apply x).symm)
    (T.topologicalClosure_range_modulus ▸ hx)

/-- The polar factor of an injective operator is an isometry. -/
theorem norm_polarFactor_apply_of_injective (hT : Function.Injective T) (x : E) :
    ‖T.polarFactor x‖ = ‖x‖ :=
  T.norm_polarFactor_apply <| by
    rw [LinearMap.ker_eq_bot.2 (by exact hT), Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top

/-- The polar factor is a partial isometry. -/
@[simp]
theorem isPartialIsometry_polarFactor : T.polarFactor.IsPartialIsometry :=
  isPartialIsometry_factorThru (fun x ↦ (T.norm_modulus_apply x).symm)

/-- The initial projection `U† U` of the polar factor is the orthogonal projection onto
`(ker T)ᗮ`. -/
theorem adjoint_polarFactor_comp_polarFactor :
    T.polarFactor† ∘L T.polarFactor = T.kerᗮ.starProjection :=
  adjoint_factorThru_comp_factorThru_of_isStarNormal (fun x ↦ (T.norm_modulus_apply x).symm)
    T.isSelfAdjoint_modulus.isStarNormal

/-- The range of the polar factor is the closure of the range of `T`. -/
@[simp]
theorem range_polarFactor : T.polarFactor.range = T.range.topologicalClosure :=
  range_factorThru (fun x ↦ (T.norm_modulus_apply x).symm)

/-- The final projection `U U†` of the polar factor is the orthogonal projection onto the closure
of the range of `T`. -/
theorem polarFactor_comp_adjoint_polarFactor :
    T.polarFactor ∘L T.polarFactor† = T.range.topologicalClosure.starProjection :=
  factorThru_comp_adjoint_factorThru (fun x ↦ (T.norm_modulus_apply x).symm)

variable {T} in
/-- **Uniqueness of the polar factor.** A bounded operator `V` with `V |T| = T` that vanishes on
`ker T` is the polar factor of `T`. It is not assumed to be a partial isometry. -/
theorem eq_polarFactor {V : E →L[𝕜] F} (hV : V ∘L T.modulus = T) (hV₀ : ∀ x ∈ T.ker, V x = 0) :
    V = T.polarFactor :=
  eq_factorThru_of_isStarNormal (fun x ↦ (T.norm_modulus_apply x).symm)
    T.isSelfAdjoint_modulus.isStarNormal hV hV₀

/-- A bounded operator is the polar factor of `T` exactly when it factors `T` through its modulus
and vanishes on `ker T`. -/
theorem eq_polarFactor_iff {V : E →L[𝕜] F} :
    V = T.polarFactor ↔ V ∘L T.modulus = T ∧ ∀ x ∈ T.ker, V x = 0 := by
  refine ⟨?_, fun ⟨hV, hV₀⟩ ↦ eq_polarFactor hV hV₀⟩
  rintro rfl
  exact ⟨T.polarFactor_comp_modulus, fun _ ↦ T.polarFactor_apply_of_mem_ker⟩

/-- The polar factor of the zero operator is zero. -/
@[simp]
theorem polarFactor_zero : (0 : E →L[𝕜] F).polarFactor = 0 :=
  (eq_polarFactor (by simp) fun _ _ ↦ rfl).symm

/-! ### The adjoint of the polar factor -/

/-- The adjoint of the polar factor carries the image of a vector back to its modulus:
`U† (T x) = |T| x`. -/
@[simp]
theorem adjoint_polarFactor_apply_apply (x : E) : (T.polarFactor†) (T x) = T.modulus x :=
  congr($(adjoint_factorThru_comp (fun x ↦ (T.norm_modulus_apply x).symm)) x)

/-- The adjoint of the polar factor carries `T` back to its modulus: `U† T = |T|`. -/
@[simp]
theorem adjoint_polarFactor_comp : T.polarFactor† ∘L T = T.modulus :=
  ext T.adjoint_polarFactor_apply_apply

/-- The adjoint of the polar decomposition: `|T| U† = T†`. -/
@[simp]
theorem modulus_comp_adjoint_polarFactor : T.modulus ∘L T.polarFactor† = T† := by
  conv_rhs => rw [← T.polarFactor_comp_modulus]
  rw [adjoint_comp, adjoint_modulus]

/-- The adjoint of the polar decomposition, applied to a vector: `|T| (U† y) = T† y`. -/
@[simp]
theorem modulus_apply_adjoint_polarFactor_apply (y : F) :
    T.modulus ((T.polarFactor†) y) = (T†) y :=
  congr($(T.modulus_comp_adjoint_polarFactor) y)

/-- The modulus of the adjoint is `T` composed with the adjoint of its polar factor:
`|T†| = T U†`, equivalently `|T†| = U |T| U†`. -/
theorem modulus_adjoint : (T†).modulus = T ∘L T.polarFactor† := by
  refine (eq_modulus_iff.2 ⟨?_, ?_⟩).symm
  · have h : T ∘L T.polarFactor† = T.polarFactor ∘L T.modulus ∘L T.polarFactor† := by
      rw [← comp_assoc, polarFactor_comp_modulus]
    rw [h]
    exact T.isPositive_modulus.conj_adjoint T.polarFactor
  · rw [adjoint_adjoint, comp_assoc, ← comp_assoc (T.polarFactor†), adjoint_polarFactor_comp,
      modulus_comp_adjoint_polarFactor]

/-- The polar factor of the adjoint is the adjoint of the polar factor. -/
@[simp]
theorem polarFactor_adjoint : (T†).polarFactor = T.polarFactor† := by
  refine (eq_polarFactor ?_ fun y hy ↦ ?_).symm
  · rw [modulus_adjoint, ← comp_assoc, adjoint_polarFactor_comp, modulus_comp_adjoint_polarFactor]
  · -- `ker U† = (range U)ᗮ = (closure (range T))ᗮ = (range T)ᗮ = ker T†`.
    have hy' : y ∈ (T.polarFactor†).ker := by
      rwa [← orthogonal_range, range_polarFactor, Submodule.orthogonal_closure, orthogonal_range]
    exact hy'

/-- The polar decomposition of the adjoint in terms of the adjoint of the polar factor:
`U† |T†| = T†`. -/
@[simp]
theorem adjoint_polarFactor_comp_modulus_adjoint : T.polarFactor† ∘L (T†).modulus = T† := by
  rw [← polarFactor_adjoint, polarFactor_comp_modulus]

/-- The adjoint of the polar factor has the same kernel as `T†`. -/
@[simp]
theorem ker_adjoint_polarFactor : (T.polarFactor†).ker = (T†).ker := by
  rw [← polarFactor_adjoint, ker_polarFactor]

/-- The range of the adjoint of the polar factor is the closure of the range of `T†`. -/
@[simp]
theorem range_adjoint_polarFactor : (T.polarFactor†).range = (T†).range.topologicalClosure := by
  rw [← polarFactor_adjoint, range_polarFactor]

/-- **Left polar decomposition:** `|T†| U = T`. -/
@[simp]
theorem modulus_adjoint_comp_polarFactor : (T†).modulus ∘L T.polarFactor = T := by
  have h := congrArg adjoint (T†).polarFactor_comp_modulus
  rwa [polarFactor_adjoint, adjoint_comp, adjoint_adjoint, adjoint_adjoint, adjoint_modulus] at h

/-- The left polar decomposition, applied to a vector: `|T†| (U x) = T x`. -/
@[simp]
theorem modulus_adjoint_apply_polarFactor_apply (x : E) :
    (T†).modulus (T.polarFactor x) = T x :=
  congr($(T.modulus_adjoint_comp_polarFactor) x)

/-! ### Comparison with the modulus -/

/-- If the modulus of `T` is invertible, the polar factor is `T |T|⁻¹`. -/
theorem polarFactor_eq_comp_inverse (hT : IsUnit T.modulus) :
    T.polarFactor = T ∘L Ring.inverse T.modulus :=
  factorThru_eq_comp_inverse hT

/-- The polar factor `U` of an endomorphism `T` satisfies `‖T - U‖ ≤ ‖|T| - 1‖`. -/
theorem norm_sub_polarFactor_le (T : E →L[𝕜] E) : ‖T - T.polarFactor‖ ≤ ‖T.modulus - 1‖ :=
  norm_sub_factorThru_le fun x ↦ (T.norm_modulus_apply x).ge

end ContinuousLinearMap
