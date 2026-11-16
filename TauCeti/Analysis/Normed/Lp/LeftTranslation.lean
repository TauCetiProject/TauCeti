/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reindexing and left translation on `ℓᵖ`

Reindexing a sequence in `ℓᵖ` along a bijection `e : α ≃ β` preserves membership and norms,
inducing the linear isometry equivalence
`LinearIsometryEquiv.lpCongrLeft p 𝕜 E e : lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : β ↦ E) p`
with `(lpCongrLeft p 𝕜 E e f) y = f (e.symm y)`. It maps coordinate vectors `lp.single p a v` to
`lp.single p (e a) v`, preserves unconditional sums, and acts as an adjoint pair on
`lp.dualPairing`.

Specializing to the permutations `MulAction.toPerm g` of a group action `[MulAction G α]` gives the
left translation homomorphism

```text
lp.leftTranslation p 𝕜 : G →* (lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : α ↦ E) p),
(lp.leftTranslation p 𝕜 g f) x = f (g⁻¹ • x).
```

It sends a point mass `lp.single p x v` to `lp.single p (g • x) v`, preserves `tsum`, and satisfies
the adjoint identity `⟨L_g a, b⟩ = ⟨a, L_{g⁻¹} b⟩` for `lp.dualPairing`.

## Main definitions

* `LinearIsometryEquiv.lpCongrLeft`: reindexing `ℓᵖ` along a bijection `e : α ≃ β`, as a linear
  isometry equivalence.
* `lp.leftTranslation`: left translation on `ℓᵖ` for a group action, as a group homomorphism into
  linear isometry equivalences.

## Main results

* `Memℓp.comp_equiv`, `Equiv.memℓp_comp_iff`: membership in `ℓᵖ` is invariant under precomposition
  with a bijection.
* `LinearIsometryEquiv.lpCongrLeft_single`: reindexing sends `lp.single p a v` to
  `lp.single p (e a) v`.
* `lp.leftTranslation_single`: left translation sends `lp.single p x v` to `lp.single p (g • x) v`.
* `lp.dualPairing_leftTranslation_left`, `lp.dualPairing_leftTranslation_right`: adjointness of
  left translation with respect to `lp.dualPairing`.
-/

public section

noncomputable section

open scoped ENNReal NNReal

section Memℓp

variable {α β E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Membership in `ℓᵖ` is preserved by precomposition with a bijection. -/
theorem Memℓp.comp_equiv {f : β → E} (hf : Memℓp f p) (e : α ≃ β) : Memℓp (f ∘ e) p := by
  simpa using hf.indicator_comp (s := Set.univ) e.injective.injOn

/-- Membership in `ℓᵖ` is invariant under precomposition with a bijection. -/
theorem Equiv.memℓp_comp_iff (e : α ≃ β) {f : β → E} : Memℓp (f ∘ e) p ↔ Memℓp f p :=
  ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

end Memℓp

namespace LinearIsometryEquiv

variable {α β γ : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 E : Type*) [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Reindexing `ℓᵖ` along a bijection `e : α ≃ β`, as a linear isometry equivalence sending `f` to
`y ↦ f (e.symm y)`. -/
def lpCongrLeft (e : α ≃ β) :
    lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : β ↦ E) p where
  toFun f := ⟨f ∘ e.symm, (lp.memℓp f).comp_equiv e.symm⟩
  invFun g := ⟨g ∘ e, (lp.memℓp g).comp_equiv e⟩
  left_inv f := lp.ext <| funext fun x ↦ by simp
  right_inv g := lp.ext <| funext fun y ↦ by simp
  map_add' _ _ := lp.ext <| funext fun _ ↦ rfl
  map_smul' _ _ := lp.ext <| funext fun _ ↦ rfl
  norm_map' f := by
    have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    refine le_antisymm
      (lp.norm_le_of_forall_eq_indicator_comp hp (s := Set.univ) e.symm.injective.injOn
        fun _ ↦ by simp) ?_
    exact lp.norm_le_of_forall_eq_indicator_comp hp (s := Set.univ) e.injective.injOn
      (f := (⟨f ∘ e.symm, (lp.memℓp f).comp_equiv e.symm⟩ : lp (fun _ : β ↦ E) p))
      fun _ ↦ by simp

variable {p 𝕜 E}

/-- Reindexing `ℓᵖ` along `e` evaluates at `e.symm y`. -/
@[simp]
theorem lpCongrLeft_apply (e : α ≃ β) (f : lp (fun _ : α ↦ E) p) (y : β) :
    lpCongrLeft p 𝕜 E e f y = f (e.symm y) :=
  (rfl)

/-- The inverse of `lpCongrLeft` along `e` is `lpCongrLeft` along `e.symm`. -/
@[simp]
theorem lpCongrLeft_symm (e : α ≃ β) :
    (lpCongrLeft p 𝕜 E e).symm = lpCongrLeft p 𝕜 E e.symm := by
  ext f x
  rfl

/-- Reindexing `ℓᵖ` along the identity equivalence is the identity. -/
@[simp]
theorem lpCongrLeft_refl :
    lpCongrLeft p 𝕜 E (Equiv.refl α) = LinearIsometryEquiv.refl 𝕜 (lp (fun _ : α ↦ E) p) := by
  ext f x
  rfl

/-- Reindexing `ℓᵖ` is functorial in the bijection. -/
@[simp]
theorem lpCongrLeft_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (lpCongrLeft p 𝕜 E e₁).trans (lpCongrLeft p 𝕜 E e₂) =
      lpCongrLeft p 𝕜 E (e₁.trans e₂) := by
  ext f z
  rfl

/-- Reindexing `ℓᵖ` along `e` sends a coordinate vector at `a` to the coordinate vector at `e a`. -/
@[simp]
theorem lpCongrLeft_single [DecidableEq α] [DecidableEq β] (e : α ≃ β) (a : α) (v : E) :
    lpCongrLeft p 𝕜 E e (lp.single p a v) = lp.single p (e a) v := by
  ext y
  simp [lp.single_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- Reindexing `ℓᵖ` along a bijection preserves the unconditional sum of coordinates. -/
theorem tsum_lpCongrLeft (e : α ≃ β) (f : lp (fun _ : α ↦ E) p) :
    ∑' y, lpCongrLeft p 𝕜 E e f y = ∑' x, f x :=
  e.symm.tsum_eq fun x ↦ f x

end LinearIsometryEquiv

namespace lp

section DualPairingCongr

variable {α β 𝕜 E F H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [CompleteSpace H] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Reindexing both factors of `lp.dualPairing` along the same bijection leaves the pairing
unchanged. -/
theorem dualPairing_lpCongrLeft (B : E →L[𝕜] F →L[𝕜] H) {K : ℝ≥0} (hBK : ‖B‖ ≤ K) (e : α ≃ β)
    (a : lp (fun _ : α ↦ E) p) (b : lp (fun _ : α ↦ F) q) :
    dualPairing p q (fun _ : β ↦ B) (fun _ ↦ hBK)
        (LinearIsometryEquiv.lpCongrLeft p 𝕜 E e a)
        (LinearIsometryEquiv.lpCongrLeft q 𝕜 F e b) =
      dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) a b :=
  e.symm.tsum_eq fun x ↦ B (a x) (b x)

/-- Moving `lpCongrLeft` from the left argument to the right argument of `lp.dualPairing` inverts
the bijection. -/
theorem dualPairing_lpCongrLeft_left (B : E →L[𝕜] F →L[𝕜] H) {K : ℝ≥0} (hBK : ‖B‖ ≤ K)
    (e : α ≃ β) (a : lp (fun _ : α ↦ E) p) (b : lp (fun _ : β ↦ F) q) :
    dualPairing p q (fun _ : β ↦ B) (fun _ ↦ hBK)
        (LinearIsometryEquiv.lpCongrLeft p 𝕜 E e a) b =
      dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK)
        a (LinearIsometryEquiv.lpCongrLeft q 𝕜 F e.symm b) := by
  have h := dualPairing_lpCongrLeft B hBK e a (LinearIsometryEquiv.lpCongrLeft q 𝕜 F e.symm b)
  rwa [← LinearIsometryEquiv.lpCongrLeft_symm, LinearIsometryEquiv.apply_symm_apply] at h

end DualPairingCongr

section LeftTranslation

variable {G α E : Type*} [Group G] [MulAction G α] [NormedAddCommGroup E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Left translation `g ↦ L_g` on `lp (fun _ : α ↦ E) p` for a group action of `G` on `α`,
where `(L_g f) x = f (g⁻¹ • x)`, as a group homomorphism into linear isometry equivalences. -/
def leftTranslation : G →* (lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : α ↦ E) p) where
  toFun g := LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

variable {p 𝕜}

/-- Left translation by `g` is reindexing along the permutation `MulAction.toPerm g`. -/
theorem leftTranslation_eq_lpCongrLeft (g : G) :
    leftTranslation (α := α) (E := E) p 𝕜 g =
      LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g) := by
  ext f x
  rfl

/-- Left translation by `g` evaluates at `g⁻¹ • x`. -/
@[simp]
theorem leftTranslation_apply (g : G) (f : lp (fun _ : α ↦ E) p) (x : α) :
    leftTranslation p 𝕜 g f x = f (g⁻¹ • x) :=
  (rfl)

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
@[simp]
theorem leftTranslation_symm (g : G) :
    (leftTranslation (α := α) (E := E) p 𝕜 g).symm = leftTranslation p 𝕜 g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Left translation by `g` sends a coordinate vector at `x` to the coordinate vector at `g • x`. -/
@[simp]
theorem leftTranslation_single [DecidableEq α] (g : G) (x : α) (v : E) :
    leftTranslation p 𝕜 g (lp.single p x v) = lp.single p (g • x) v :=
  LinearIsometryEquiv.lpCongrLeft_single (MulAction.toPerm g) x v

/-- Left translation preserves the unconditional sum of coordinates. -/
theorem tsum_leftTranslation (g : G) (f : lp (fun _ : α ↦ E) p) :
    ∑' x, leftTranslation p 𝕜 g f x = ∑' x, f x :=
  LinearIsometryEquiv.tsum_lpCongrLeft (MulAction.toPerm g) f

end LeftTranslation

section DualPairingLeftTranslation

variable {G α 𝕜 E F H : Type*} [Group G] [MulAction G α] [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] [CompleteSpace H] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- Simultaneous left translation of both arguments preserves `lp.dualPairing`. -/
theorem dualPairing_leftTranslation (B : E →L[𝕜] F →L[𝕜] H) {K : ℝ≥0} (hBK : ‖B‖ ≤ K) (g : G)
    (a : lp (fun _ : α ↦ E) p) (b : lp (fun _ : α ↦ F) q) :
    dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK)
        (leftTranslation p 𝕜 g a) (leftTranslation q 𝕜 g b) =
      dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) a b :=
  dualPairing_lpCongrLeft B hBK (MulAction.toPerm g) a b

/-- Left translation on the first argument of `lp.dualPairing` moves to inverse left translation on
the second argument. -/
theorem dualPairing_leftTranslation_left (B : E →L[𝕜] F →L[𝕜] H) {K : ℝ≥0} (hBK : ‖B‖ ≤ K)
    (g : G) (a : lp (fun _ : α ↦ E) p) (b : lp (fun _ : α ↦ F) q) :
    dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) (leftTranslation p 𝕜 g a) b =
      dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) a (leftTranslation q 𝕜 g⁻¹ b) := by
  have h := dualPairing_leftTranslation B hBK g a (leftTranslation q 𝕜 g⁻¹ b)
  rwa [← leftTranslation_symm, LinearIsometryEquiv.apply_symm_apply, leftTranslation_symm] at h

/-- Left translation on the second argument of `lp.dualPairing` moves to inverse left translation
on the first argument. -/
theorem dualPairing_leftTranslation_right (B : E →L[𝕜] F →L[𝕜] H) {K : ℝ≥0} (hBK : ‖B‖ ≤ K)
    (g : G) (a : lp (fun _ : α ↦ E) p) (b : lp (fun _ : α ↦ F) q) :
    dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) a (leftTranslation q 𝕜 g b) =
      dualPairing p q (fun _ : α ↦ B) (fun _ ↦ hBK) (leftTranslation p 𝕜 g⁻¹ a) b := by
  have h := dualPairing_leftTranslation B hBK g (leftTranslation p 𝕜 g⁻¹ a) b
  rwa [← leftTranslation_symm, LinearIsometryEquiv.apply_symm_apply, leftTranslation_symm] at h

end DualPairingLeftTranslation

end lp
