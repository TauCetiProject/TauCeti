/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Left translation on `ℓᵖ`

Let a group `G` act on a type `α`. Left translation of sequences indexed by `α`,

```text
(L_g f)(a) = f (g⁻¹ • a),        L_g L_h = L_(g * h),
```

is reindexing along the permutation `a ↦ g • a`, so it is a linear isometry equivalence of
`ℓᵖ(α, E)` for `1 ≤ p` (`LinearIsometryEquiv.lpCongrLeft`). This gives a group homomorphism
`lp.leftTranslation p 𝕜 : G →* (ℓᵖ(α, E) ≃ₗᵢ[𝕜] ℓᵖ(α, E))`, which moves the unit vector at `a`
to the unit vector at `g • a`.

For the left regular action of `G` on itself, `ℓ¹(G)` with these translations is the space in
which Reiter's condition for amenable discrete groups is stated: there are finitely supported
probability densities `u` with `‖L_g u - u‖` small for the finitely many `g` in any given finite
set.

## Main definitions

* `lp.leftTranslation p 𝕜`: left translation `g ↦ L_g` on `ℓᵖ(α, E)`, as a group homomorphism to
  linear isometry equivalences.

## Main results

* `lp.leftTranslation_def`: `L_g` is reindexing along `a ↦ g • a`.
* `lp.leftTranslation_apply`: `(L_g f)(a) = f (g⁻¹ • a)`.
* `lp.leftTranslation_single`: `L_g δ_a = δ_(g • a)`.
* `lp.norm_leftTranslation_sub_eq_tsum_norm`: in `ℓ¹`, `‖L_g f - f‖ = ∑_a ‖f (g⁻¹ • a) - f a‖`.
-/

public section

noncomputable section

open scoped ENNReal

namespace lp

variable {G α E : Type*} [Group G] [MulAction G α] [NormedAddCommGroup E] (p : ℝ≥0∞)
  [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Left translation `g ↦ L_g` on `ℓᵖ(α, E)` for an action of a group `G` on `α`, where
`(L_g f)(a) = f (g⁻¹ • a)`, as a group homomorphism to linear isometry equivalences. -/
def leftTranslation : G →* (lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : α ↦ E) p) where
  toFun g := LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g)
  map_one' := by
    ext f a
    simp
  map_mul' g h := by
    ext f a
    simp [mul_smul]

variable {p 𝕜}

/-- Left translation by `g` is reindexing along the permutation `a ↦ g • a`. -/
theorem leftTranslation_def (g : G) :
    leftTranslation p 𝕜 g =
      LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g : Equiv.Perm α) :=
  (rfl)

/-- The left translate `L_g f` is the sequence `a ↦ f (g⁻¹ • a)`. -/
@[simp]
theorem leftTranslation_apply (g : G) (f : lp (fun _ : α ↦ E) p) (a : α) :
    leftTranslation p 𝕜 g f a = f (g⁻¹ • a) := by
  simp [leftTranslation]

/-- As a function, the left translate `L_g f` is `a ↦ f (g⁻¹ • a)`. -/
theorem coe_leftTranslation (g : G) (f : lp (fun _ : α ↦ E) p) :
    ⇑(leftTranslation p 𝕜 g f) = fun a ↦ f (g⁻¹ • a) :=
  funext (leftTranslation_apply g f)

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
theorem leftTranslation_symm (g : G) :
    (leftTranslation p 𝕜 g).symm = leftTranslation p 𝕜 (α := α) (E := E) g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- The inverse of left translation by `g` is the sequence `a ↦ f (g • a)`. -/
@[simp]
theorem leftTranslation_symm_apply (g : G) (f : lp (fun _ : α ↦ E) p) (a : α) :
    (leftTranslation p 𝕜 g).symm f a = f (g • a) := by
  rw [leftTranslation_symm, leftTranslation_apply, inv_inv]

/-- Left translation by `g` moves the unit vector at `a` to the unit vector at `g • a`. -/
@[simp]
theorem leftTranslation_single [DecidableEq α] (g : G) (a : α) (x : E) :
    leftTranslation p 𝕜 g (lp.single p a x) = lp.single p (g • a) x :=
  LinearIsometryEquiv.lpCongrLeft_single _ a x

/-- In `ℓ¹`, the distance from `f` to its left translate `L_g f` is
`∑_a ‖f (g⁻¹ • a) - f a‖`. -/
theorem norm_leftTranslation_sub_eq_tsum_norm (g : G) (f : lp (fun _ : α ↦ E) 1) :
    ‖leftTranslation 1 𝕜 g f - f‖ = ∑' a, ‖f (g⁻¹ • a) - f a‖ := by
  rw [← (hasSum_norm_one _).tsum_eq]
  simp

end lp
