/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Symplectic.AlmostComplex

import Mathlib.Tactic.FinCases

/-!
# The metric of a tame pair

A symplectic form `ω` taming an almost complex structure `J` need not be `J`-invariant, so the
bilinear form `ω(v, J w)` from `AlmostComplex.lean` is in general not symmetric. Its symmetric
part, however, always is a metric: `gₛ(v, w) = ω(v, J w) + ω(w, J v)` is symmetric, automatically
`J`-invariant, and -- under taming alone -- positive definite. This is the standard "every tame
`J` carries a `J`-invariant metric" construction (McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.5), the first step of the proof that the space of tame almost
complex structures is contractible, recorded here at the pointwise linear-algebra level.

Tame and compatible are kept as separate named hypotheses, so this file builds the metric from the
strictly weaker `SymplecticForm.Tames` predicate, paralleling the compatible construction
`SymplecticForm.Compatible.innerProductCore` rather than reusing it. When `ω` is in fact compatible,
the symmetric part is just twice the asymmetric metric `ω(·, J ·)`, which is recorded as the bridge
`SymplecticForm.Compatible.symmetrizedBilinForm_apply`.

On a finite-dimensional space, the **gradient for the symmetric metric**
(`TauCeti.SymplecticForm.Tames.symmetrizedGradient`) sends `η` to the gradient of the linear form
`ξ ↦ ω(ξ, η)` for the metric `gₛ / 2`: the unique vector `G η` with `gₛ(ξ, G η) = 2 ω(ξ, η)` for
every `ξ`. This is the pointwise form of the gradient of the symplectic action functional, whose
first variation along a loop `γ` pairs the variation `ξ` with `γ' - X_H` through `ω`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_symmetrizedGradient`).
For a compatible pair it is `-J`, and
among tame pairs only for compatible ones: `gₛ(ξ, -J η) = ω(ξ, η) + ω(J ξ, J η)`. Tameness does not
imply compatibility: on `ℝ⁴` with its standard symplectic form, the structure
`(a, b, c, d) ↦ (c - b, a - d, -d, c)` is tame but not compatible, so its gradient is not `-J`
(`TauCeti.SymplecticForm.exists_symmetrizedGradient_ne_neg`).

## Main declarations

* `TauCeti.SymplecticForm.symmetrizedBilinForm`: the symmetric part `gₛ(v, w) = ω(v, J w) +
  ω(w, J v)` of the metric of `(ω, J)`.
* `TauCeti.SymplecticForm.symmetrizedBilinForm_isSymm`: `gₛ` is symmetric, for any `J`.
* `TauCeti.SymplecticForm.symmetrizedBilinForm_invariant`: `gₛ(J v, J w) = gₛ(v, w)`, for any
  taming-or-not `ω`; the symmetric part is always `J`-invariant.
* `TauCeti.SymplecticForm.Tames.symmetrizedBilinForm_posDef`: under taming, `gₛ` is positive
  definite.
* `TauCeti.SymplecticForm.Tames.innerProductCore`: the symmetric part of the metric of a tame
  pair as an `InnerProductSpace.Core ℝ V`.
* `TauCeti.SymplecticForm.Tames.innerProductCore_inner_invariant`: the packaged inner product is
  `J`-invariant, `⟪J v, J w⟫ = ⟪v, w⟫`.
* `TauCeti.SymplecticForm.Tames.symmetrizedGradient`: the gradient for the symmetric metric,
  characterized by `TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_iff`.
* `TauCeti.SymplecticForm.Compatible.symmetrizedGradient_apply`,
  `TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_neg_iff`: the gradient is `-J` exactly for
  compatible pairs.
* `TauCeti.SymplecticForm.exists_tames_not_compatible`,
  `TauCeti.SymplecticForm.exists_symmetrizedGradient_ne_neg`: a tame pair on `ℝ⁴` which is not
  compatible, and whose gradient is not `-J`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Sections 2.1 and 2.5.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (ω : SymplecticForm V) (J : AlmostComplexStructure V)

/-- The symmetric part of the metric of `(ω, J)`: `gₛ(v, w) = ω(v, J w) + ω(w, J v)`.

Unlike `SymplecticForm.associatedBilinForm`, this is symmetric for every `J`, and `J`-invariant;
taming makes it positive definite, hence an inner product. -/
def symmetrizedBilinForm : LinearMap.BilinForm ℝ V :=
  ω.associatedBilinForm J + (ω.associatedBilinForm J).flip

@[simp]
lemma symmetrizedBilinForm_apply (v w : V) :
    ω.symmetrizedBilinForm J v w = ω v (J w) + ω w (J v) := by
  simp [symmetrizedBilinForm]

variable {ω J}

/-- The symmetric part of the metric is symmetric, for any almost complex structure. -/
lemma symmetrizedBilinForm_isSymm : (ω.symmetrizedBilinForm J).IsSymm :=
  ⟨fun v w => by simp only [symmetrizedBilinForm_apply]; ring⟩

/-- The symmetric part of the metric is `J`-invariant, for any symplectic form: `gₛ(J v, J w) =
gₛ(v, w)`. This uses only `J² = -1` and skew-symmetry of `ω`, not taming. -/
lemma symmetrizedBilinForm_invariant (v w : V) :
    ω.symmetrizedBilinForm J (J v) (J w) = ω.symmetrizedBilinForm J v w := by
  have e₁ : ω (J v) (-w) = ω w (J v) :=
    (map_neg (ω.toBilinForm (J v)) w).trans (ω.neg_eq (J v) w)
  have e₂ : ω (J w) (-v) = ω v (J w) :=
    (map_neg (ω.toBilinForm (J w)) v).trans (ω.neg_eq (J w) v)
  rw [symmetrizedBilinForm_apply, symmetrizedBilinForm_apply,
    AlmostComplexStructure.apply_apply, AlmostComplexStructure.apply_apply, e₁, e₂, add_comm]

/-- The diagonal of the symmetric part is twice the symplectic diagonal: `gₛ(v, v) = 2 ω(v, Jv)`. -/
lemma symmetrizedBilinForm_apply_self (v : V) :
    ω.symmetrizedBilinForm J v v = 2 * ω v (J v) := by
  rw [symmetrizedBilinForm_apply, two_mul]

namespace Tames

/-- The symplectic diagonal `ω(v, J v)` is nonnegative under taming. -/
lemma symplecticForm_apply_apply_self_nonneg (h : ω.Tames J) (v : V) : 0 ≤ ω v (J v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (h v hv).le

/-- The diagonal of the symmetric part is positive on nonzero vectors. -/
lemma symmetrizedBilinForm_self_pos (h : ω.Tames J) {v : V} (hv : v ≠ 0) :
    0 < ω.symmetrizedBilinForm J v v := by
  rw [symmetrizedBilinForm_apply_self]
  have := h v hv
  linarith

/-- The diagonal of the symmetric part is nonnegative. -/
lemma symmetrizedBilinForm_self_nonneg (h : ω.Tames J) (v : V) :
    0 ≤ ω.symmetrizedBilinForm J v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (h.symmetrizedBilinForm_self_pos hv).le

/-- Under taming, the symmetric part of the metric is positive definite. -/
lemma symmetrizedBilinForm_posDef (h : ω.Tames J) :
    (ω.symmetrizedBilinForm J).toQuadraticMap.PosDef := fun v hv => by
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using h.symmetrizedBilinForm_self_pos hv

/-- The diagonal of the symmetric part detects zero vectors. -/
lemma symmetrizedBilinForm_self_eq_zero (h : ω.Tames J) {v : V} :
    ω.symmetrizedBilinForm J v v = 0 ↔ v = 0 := by
  refine ⟨fun hv => ?_, ?_⟩
  · by_contra hne
    exact (h.symmetrizedBilinForm_self_pos hne).ne' hv
  · rintro rfl
    simp

/-- The symmetric part of the metric of a tame pair is nondegenerate. -/
lemma symmetrizedBilinForm_nondegenerate (h : ω.Tames J) :
    (ω.symmetrizedBilinForm J).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    symmetrizedBilinForm_isSymm.isRefl).mpr ?_
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  intro v hv
  refine h.symmetrizedBilinForm_self_eq_zero.mp ?_
  simpa using LinearMap.congr_fun hv v

/-- The symmetric part of the metric of a tame pair, packaged as an `InnerProductSpace.Core ℝ V`.

The inner product is `⟪v, w⟫ = ω(v, J w) + ω(w, J v)`, the symmetric part of `ω(·, J ·)`. -/
@[expose, implicit_reducible]
noncomputable def innerProductCore (h : ω.Tames J) : InnerProductSpace.Core ℝ V where
  inner v w := ω.symmetrizedBilinForm J v w
  conj_inner_symm v w := by
    simpa only [RCLike.conj_to_real] using symmetrizedBilinForm_isSymm.eq w v
  re_inner_nonneg v := by
    simpa using h.symmetrizedBilinForm_self_nonneg v
  add_left v w x := by
    simp only [map_add, LinearMap.add_apply]
  smul_left v w r := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]
  definite v hv := h.symmetrizedBilinForm_self_eq_zero.mp hv

/-- The inner product from `innerProductCore` is the symmetric part `ω(v, J w) + ω(w, J v)`. -/
@[simp]
lemma innerProductCore_inner (h : ω.Tames J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner v w = ω v (J w) + ω w (J v) :=
  -- `inner` for `innerProductCore` is the field `ω.symmetrizedBilinForm J v w` by construction.
  symmetrizedBilinForm_apply ω J v w

/-- The inner product from `innerProductCore` is `J`-invariant: `⟪J v, J w⟫ = ⟪v, w⟫`. -/
lemma innerProductCore_inner_invariant (h : ω.Tames J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner (J v) (J w)
      = @inner ℝ V h.innerProductCore.toInner v w :=
  -- `inner` for `innerProductCore` is the field `ω.symmetrizedBilinForm J · ·` by construction.
  symmetrizedBilinForm_invariant v w

end Tames

namespace Compatible

/-- When `ω` is compatible with `J`, its asymmetric metric `ω(·, J ·)` is already symmetric, so
the symmetric part is just twice it: `gₛ(v, w) = 2 ω(v, J w)`. -/
lemma symmetrizedBilinForm_apply (h : ω.Compatible J) (v w : V) :
    ω.symmetrizedBilinForm J v w = 2 * ω v (J w) := by
  rw [SymplecticForm.symmetrizedBilinForm_apply, ← h.associatedBilinForm_apply_swap v w, two_mul]

end Compatible

/-! ### The gradient for the symmetric metric -/

section Gradient

variable [FiniteDimensional ℝ V]

namespace Tames

/-- The **gradient for the symmetric metric** of a tame pair: the linear map sending `η` to the
gradient of the linear form `ξ ↦ ω(ξ, η)` for the metric `gₛ / 2`, that is, the unique vector
`G η` with `gₛ(ξ, G η) = 2 ω(ξ, η)` for every `ξ`
(`TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_iff`).

For a compatible pair, `gₛ / 2` is the metric `ω(·, J ·)` and the gradient is `-J`
(`TauCeti.SymplecticForm.Compatible.symmetrizedGradient_apply`); among tame pairs this
characterizes compatibility (`TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_neg_iff`). -/
noncomputable def symmetrizedGradient (h : ω.Tames J) : V →ₗ[ℝ] V :=
  ((2 : ℝ) • ω.toBilinForm.flip).symmCompOfNondegenerate (ω.symmetrizedBilinForm J)
    h.symmetrizedBilinForm_nondegenerate

/-- The defining property of the gradient for the symmetric metric, with the gradient in the
first argument: `gₛ(G η, ξ) = 2 ω(ξ, η)`. -/
@[simp high]
theorem symmetrizedBilinForm_symmetrizedGradient_left (h : ω.Tames J) (η ξ : V) :
    ω.symmetrizedBilinForm J (h.symmetrizedGradient η) ξ = 2 * ω ξ η := by
  rw [symmetrizedGradient, LinearMap.BilinForm.symmCompOfNondegenerate_left_apply]
  simp

/-- The defining property of the gradient for the symmetric metric:
`gₛ(ξ, G η) = 2 ω(ξ, η)`. -/
@[simp high]
theorem symmetrizedBilinForm_symmetrizedGradient_right (h : ω.Tames J) (ξ η : V) :
    ω.symmetrizedBilinForm J ξ (h.symmetrizedGradient η) = 2 * ω ξ η := by
  have := h.symmetrizedBilinForm_symmetrizedGradient_left η ξ
  rw [symmetrizedBilinForm_apply] at this ⊢
  linarith

/-- **Characterization of the gradient for the symmetric metric**: `G η = v` exactly when
`gₛ(ξ, v) = 2 ω(ξ, η)` for every `ξ`. -/
theorem symmetrizedGradient_eq_iff (h : ω.Tames J) {η v : V} :
    h.symmetrizedGradient η = v ↔ ∀ ξ, ω.symmetrizedBilinForm J ξ v = 2 * ω ξ η := by
  refine ⟨fun hv ξ ↦ hv ▸ h.symmetrizedBilinForm_symmetrizedGradient_right ξ η, fun hv ↦ ?_⟩
  refine sub_eq_zero.1 (h.symmetrizedBilinForm_nondegenerate.2 _ fun ξ ↦ ?_)
  rw [map_sub, hv ξ, h.symmetrizedBilinForm_symmetrizedGradient_right, sub_self]

/-- The gradient for the symmetric metric vanishes only at zero. -/
@[simp]
theorem symmetrizedGradient_eq_zero_iff (h : ω.Tames J) {η : V} :
    h.symmetrizedGradient η = 0 ↔ η = 0 := by
  refine ⟨fun hη ↦ ω.separatingRight η fun ξ ↦ ?_, fun hη ↦ by rw [hη, map_zero]⟩
  have := (h.symmetrizedGradient_eq_iff.1 hη) ξ
  rw [map_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left two_ne_zero

/-- The gradient for the symmetric metric is injective. -/
theorem symmetrizedGradient_injective (h : ω.Tames J) :
    Function.Injective h.symmetrizedGradient :=
  (injective_iff_map_eq_zero _).2 fun _ ↦ h.symmetrizedGradient_eq_zero_iff.1

end Tames

/-- **For a compatible pair, the gradient for the symmetric metric is `-J`**: then
`gₛ(ξ, -J η) = 2 ω(ξ, J (-J η)) = 2 ω(ξ, η)`. -/
theorem Compatible.symmetrizedGradient_apply (h : ω.Compatible J) (η : V) :
    h.tames.symmetrizedGradient η = -J η := by
  refine h.tames.symmetrizedGradient_eq_iff.2 fun ξ ↦ ?_
  rw [h.symmetrizedBilinForm_apply]
  simp only [map_neg, AlmostComplexStructure.apply_apply, neg_neg]

/-- **The gradient for the symmetric metric is `-J` exactly for compatible pairs.** For a tame pair,
`gₛ(ξ, -J η) = ω(ξ, η) + ω(J ξ, J η)`, which is `2 ω(ξ, η)` for all `ξ` and `η` exactly when `ω`
is `J`-invariant. -/
theorem Tames.symmetrizedGradient_eq_neg_iff (h : ω.Tames J) :
    h.symmetrizedGradient = -J.toLinearMap ↔ ω.Compatible J := by
  refine ⟨fun hG ↦ Compatible.of_tames ((ω.invariant_iff J).2 fun v w ↦ ?_) h,
    fun hc ↦ LinearMap.ext hc.symmetrizedGradient_apply⟩
  have := (h.symmetrizedGradient_eq_iff.1 (LinearMap.congr_fun hG w)) v
  simp only [LinearMap.neg_apply, symmetrizedBilinForm_apply, map_neg,
    AlmostComplexStructure.apply_apply] at this
  linarith [ω.neg_eq (J v) (J w)]

end Gradient

/-! ### A tame pair which is not compatible -/

section Example

/-- The linear map `(a, b, c, d) ↦ (c - b, a - d, -d, c)` of `ℝ⁴`. -/
private def tameExampleLinearMap : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ where
  toFun v := ![v 2 - v 1, v 0 - v 3, -v 3, v 2]
  map_add' u v := funext fun i ↦ by fin_cases i <;> simp <;> ring
  map_smul' c v := funext fun i ↦ by fin_cases i <;> simp <;> ring

/-- The almost complex structure `(a, b, c, d) ↦ (c - b, a - d, -d, c)` of `ℝ⁴`. -/
private def tameExampleJ : AlmostComplexStructure (Fin 4 → ℝ) where
  toLinearMap := tameExampleLinearMap
  square_neg := LinearMap.ext fun v ↦ funext fun i ↦ by
    fin_cases i
    · simp [tameExampleLinearMap]
      ring
    all_goals simp [tameExampleLinearMap]

/-- The standard symplectic form `a b' - b a' + c d' - d c'` of `ℝ⁴`. -/
private def tameExampleForm : LinearMap.BilinForm ℝ (Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun u v ↦ u 0 * v 1 - u 1 * v 0 + u 2 * v 3 - u 3 * v 2)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem tameExampleForm_isAlt : tameExampleForm.IsAlt := fun v ↦ by
  simp only [tameExampleForm, LinearMap.mk₂_apply]
  ring

private theorem tameExampleForm_apply_pos {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    0 < tameExampleForm v (tameExampleJ v) := by
  have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
    by_contra hle
    refine hv (funext fun i ↦ ?_)
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2),
      sq_nonneg (v 3)]
  simp only [tameExampleForm, tameExampleJ, tameExampleLinearMap, LinearMap.mk₂_apply]
  simp
  nlinarith [sq_nonneg (v 0 - v 3), sq_nonneg (v 1 - v 2)]

/-- **A tame pair need not be compatible.** On `ℝ⁴` with the standard symplectic form
`ω = a b' - b a' + c d' - d c'`, the almost complex structure
`J (a, b, c, d) = (c - b, a - d, -d, c)` is tamed by `ω`, with
`ω(v, J v) = a² + b² + c² + d² - a d - b c`, but `ω` is not `J`-invariant:
`ω(J e₀, J e₂) = -1` while `ω(e₀, e₂) = 0`. -/
theorem exists_tames_not_compatible :
    ∃ (ω : SymplecticForm (Fin 4 → ℝ)) (J : AlmostComplexStructure (Fin 4 → ℝ)),
      ω.Tames J ∧ ¬ ω.Compatible J := by
  refine ⟨ofTames tameExampleForm tameExampleForm_isAlt fun v hv ↦ tameExampleForm_apply_pos hv,
    tameExampleJ, tames_ofTames _ _, fun h ↦ ?_⟩
  have := h.invariant_apply (Pi.single 0 1) (Pi.single 2 1)
  simp [tameExampleForm, tameExampleJ, tameExampleLinearMap] at this

/-- **For a merely tame pair the gradient for the symmetric metric need not be `-J`.** This is the
pair of `TauCeti.SymplecticForm.exists_tames_not_compatible`, through
`TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_neg_iff`. -/
theorem exists_symmetrizedGradient_ne_neg :
    ∃ (ω : SymplecticForm (Fin 4 → ℝ)) (J : AlmostComplexStructure (Fin 4 → ℝ)) (h : ω.Tames J),
      h.symmetrizedGradient ≠ -J.toLinearMap := by
  obtain ⟨ω, J, h, hc⟩ := exists_tames_not_compatible
  exact ⟨ω, J, h, fun hG ↦ hc (h.symmetrizedGradient_eq_neg_iff.1 hG)⟩

end Example

end SymplecticForm

end TauCeti
