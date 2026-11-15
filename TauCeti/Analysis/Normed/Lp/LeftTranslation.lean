/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Finsupp

/-!
# Domain equivalences and left translation on `ℓᵖ`

Reindexing along a bijection `e : α ≃ β` by `(e_* f) b = f (e.symm b)` preserves `Memℓp` and the
`ℓᵖ` norm at every exponent, giving an additive equivalence `AddEquiv.lpCongrLeft` for all `p` and,
for `1 ≤ p`, a linear isometric equivalence `LinearIsometryEquiv.lpCongrLeft`, the `lp` counterpart
of `LinearIsometryEquiv.piLpCongrLeft`. It sends coordinate vectors `lp.single p a v` to
`lp.single p (e a) v` and pushes finitely supported functions forward by `Finsupp.mapDomain e`.

When a group `G` acts on `X`, applying `LinearIsometryEquiv.lpCongrLeft` to the permutations
`MulAction.toPerm g` assembles into the left-translation representation

```text
lp.leftTranslation X p 𝕜 E : G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : X ↦ E) p),
(L_g f) x = f (g⁻¹ • x),        L_g (δ_x) = δ_{g • x}.
```

It preserves coordinate sums and nonnegativity, fixes the constant sequence `1` in `ℓ∞`, pushes
finitely supported probability distributions `w : Convexity.StdSimplex ℝ X` forward to
`w.map (g • ·)`, and in `ℓ¹` satisfies `‖L_g f - f‖ = ∑' x, ‖f (g⁻¹ • x) - f x‖`.

## Main definitions

* `AddEquiv.lpCongrLeft p E e`: reindexing `lp (fun _ : α ↦ E) p ≃+ lp (fun _ : β ↦ E) p` along
  `e : α ≃ β`.
* `LinearIsometryEquiv.lpCongrLeft p 𝕜 E e`: for `1 ≤ p`, reindexing as a `𝕜`-linear isometric
  equivalence.
* `lp.leftTranslation X p 𝕜 E`: left translation `G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] ...)` for a
  `G`-action on `X`.

## Main results

* `LinearIsometryEquiv.lpCongrLeft_single`: reindexing sends `lp.single p a v` to
  `lp.single p (e a) v`.
* `lp.leftTranslation_single`: `L_g (lp.single p x v) = lp.single p (g • x) v`.
* `lp.tsum_leftTranslation`: `∑' x, L_g f x = ∑' x, f x`.
* `lp.norm_leftTranslation_sub_one`: `‖L_g f - f‖ = ∑' x, ‖f (g⁻¹ • x) - f x‖` in `ℓ¹`.
* `Convexity.StdSimplex.leftTranslation_toLp`: `L_g (w.toLp p) = (w.map (g • ·)).toLp p`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.1 and G.3.
-/

public section

noncomputable section

open Convexity
open scoped ENNReal

section CongrLeft

variable {α β γ : Type*}

/-- Precomposing with a bijection preserves membership in `ℓᵖ` at every exponent. -/
theorem Equiv.memℓp_comp_iff {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (e : α ≃ β)
    {f : β → E} : Memℓp (f ∘ e) p ↔ Memℓp f p := by
  rcases p.trichotomy with rfl | rfl | hp
  · simp only [memℓp_zero_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ h.preimage e.injective.injOn⟩
    simpa [Set.preimage_preimage] using h.preimage e.symm.injective.injOn
  · rw [memℓp_infty_iff, memℓp_infty_iff, ← e.surjective.range_comp (fun b ↦ ‖f b‖)]
    rfl
  · simp only [memℓp_gen_iff hp]
    exact e.summable_iff (f := fun b ↦ ‖f b‖ ^ p.toReal)

/-- An equivalence of index types `e : α ≃ β` induces an additive equivalence
`lp (fun _ : α ↦ E) p ≃+ lp (fun _ : β ↦ E) p` sending `f` to `f ∘ e.symm`. -/
def AddEquiv.lpCongrLeft (p : ℝ≥0∞) (E : Type*) [NormedAddCommGroup E] (e : α ≃ β) :
    lp (fun _ : α ↦ E) p ≃+ lp (fun _ : β ↦ E) p where
  toFun f := ⟨f ∘ e.symm, e.symm.memℓp_comp_iff.2 (lp.memℓp f)⟩
  invFun f := ⟨f ∘ e, e.memℓp_comp_iff.2 (lp.memℓp f)⟩
  left_inv f := lp.ext <| funext fun a ↦ by simp
  right_inv f := lp.ext <| funext fun b ↦ by simp
  map_add' _ _ := lp.ext rfl

@[simp]
theorem AddEquiv.lpCongrLeft_apply {p : ℝ≥0∞} {E : Type*} [NormedAddCommGroup E] (e : α ≃ β)
    (f : lp (fun _ : α ↦ E) p) (b : β) : AddEquiv.lpCongrLeft p E e f b = f (e.symm b) :=
  (rfl)

@[simp]
theorem AddEquiv.lpCongrLeft_symm {p : ℝ≥0∞} {E : Type*} [NormedAddCommGroup E] (e : α ≃ β) :
    (AddEquiv.lpCongrLeft p E e).symm = AddEquiv.lpCongrLeft p E e.symm :=
  AddEquiv.ext fun _ ↦ lp.ext rfl

/-- Reindexing `lp` along an equivalence preserves the `ℓᵖ` norm for every `0 ≤ p ≤ ∞`. -/
@[simp]
theorem AddEquiv.norm_lpCongrLeft {p : ℝ≥0∞} {E : Type*} [NormedAddCommGroup E] (e : α ≃ β)
    (f : lp (fun _ : α ↦ E) p) : ‖AddEquiv.lpCongrLeft p E e f‖ = ‖f‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · simp only [lp.norm_eq_card_dsupport]
    refine congrArg Nat.cast (Finset.card_bij (fun b _ ↦ e.symm b) ?_ ?_ ?_)
    · intro b hb
      simpa using hb
    · intro b₁ _ b₂ _ h
      exact e.symm.injective h
    · intro a ha
      exact ⟨e a, by simpa using ha, e.symm_apply_apply a⟩
  · simp only [lp.norm_eq_ciSup, lpCongrLeft_apply]
    exact e.symm.iSup_congr fun _ ↦ rfl
  · simp only [lp.norm_eq_tsum_rpow hp, lpCongrLeft_apply]
    congr 1
    exact e.symm.tsum_eq fun a ↦ ‖f a‖ ^ p.toReal

section LinearIsometryEquiv

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- An equivalence of index types `e : α ≃ β` induces a linear isometric equivalence
`lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : β ↦ E) p` sending `f` to `f ∘ e.symm`. -/
def LinearIsometryEquiv.lpCongrLeft (e : α ≃ β) :
    lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : β ↦ E) p where
  __ := AddEquiv.lpCongrLeft p E e
  map_smul' _ _ := lp.ext rfl
  norm_map' := AddEquiv.norm_lpCongrLeft e

variable {p 𝕜 E}

@[simp]
theorem LinearIsometryEquiv.lpCongrLeft_apply (e : α ≃ β) (f : lp (fun _ : α ↦ E) p) (b : β) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E e f b = f (e.symm b) :=
  (rfl)

@[simp]
theorem LinearIsometryEquiv.lpCongrLeft_refl :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E (Equiv.refl α) =
      LinearIsometryEquiv.refl 𝕜 (lp (fun _ : α ↦ E) p) :=
  LinearIsometryEquiv.ext fun _ ↦ lp.ext rfl

@[simp]
theorem LinearIsometryEquiv.lpCongrLeft_symm (e : α ≃ β) :
    (LinearIsometryEquiv.lpCongrLeft p 𝕜 E e).symm =
      LinearIsometryEquiv.lpCongrLeft p 𝕜 E e.symm :=
  LinearIsometryEquiv.ext fun _ ↦ lp.ext rfl

theorem LinearIsometryEquiv.lpCongrLeft_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E (e₁.trans e₂) =
      (LinearIsometryEquiv.lpCongrLeft p 𝕜 E e₁).trans
        (LinearIsometryEquiv.lpCongrLeft p 𝕜 E e₂) :=
  LinearIsometryEquiv.ext fun _ ↦ lp.ext rfl

@[simp]
theorem LinearIsometryEquiv.lpCongrLeft_single [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (a : α) (v : E) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E e (lp.single p a v) = lp.single p (e a) v := by
  ext b
  simp [lp.single_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem LinearIsometryEquiv.tsum_lpCongrLeft (e : α ≃ β) (f : lp (fun _ : α ↦ E) p) :
    ∑' b, LinearIsometryEquiv.lpCongrLeft p 𝕜 E e f b = ∑' a, f a :=
  e.symm.tsum_eq f

@[simp]
theorem LinearIsometryEquiv.lpCongrLeft_toLp_finsupp (e : α ≃ β) (f : α →₀ E) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E e (f.toLp p) = (f.mapDomain e).toLp p := by
  ext b
  rw [lpCongrLeft_apply, Finsupp.coeFn_toLp, Finsupp.coeFn_toLp,
    ← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]

end LinearIsometryEquiv

end CongrLeft

namespace lp

variable {G : Type*} [Group G] (X : Type*) [MulAction G X] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Left translation `g ↦ L_g` on `lp (fun _ : X ↦ E) p` for an action of a group `G` on `X`,
where `(L_g f) x = f (g⁻¹ • x)`, as a group homomorphism to linear isometric equivalences. -/
def leftTranslation : G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : X ↦ E) p) where
  toFun g := LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

variable {X p 𝕜 E}

/-- Evaluating `L_g f` at `x` gives `f (g⁻¹ • x)`. -/
@[simp]
theorem leftTranslation_apply (g : G) (f : lp (fun _ : X ↦ E) p) (x : X) :
    leftTranslation X p 𝕜 E g f x = f (g⁻¹ • x) :=
  (rfl)

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
@[simp]
theorem leftTranslation_symm (g : G) :
    (leftTranslation X p 𝕜 E g).symm = leftTranslation X p 𝕜 E g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Left translation sends the coordinate vector `lp.single p x v` to `lp.single p (g • x) v`. -/
@[simp]
theorem leftTranslation_single [DecidableEq X] (g : G) (x : X) (v : E) :
    leftTranslation X p 𝕜 E g (lp.single p x v) = lp.single p (g • x) v :=
  LinearIsometryEquiv.lpCongrLeft_single (MulAction.toPerm g) x v

/-- Left translation preserves coordinate sums. -/
theorem tsum_leftTranslation (g : G) (f : lp (fun _ : X ↦ E) p) :
    ∑' x, leftTranslation X p 𝕜 E g f x = ∑' x, f x :=
  (MulAction.toPerm g).symm.tsum_eq f

/-- Left translation preserves coordinatewise nonnegativity on real `ℓᵖ`. -/
theorem forall_nonneg_leftTranslation_iff {g : G} {f : lp (fun _ : X ↦ ℝ) p} :
    (∀ x, 0 ≤ leftTranslation X p ℝ ℝ g f x) ↔ ∀ x, 0 ≤ f x :=
  ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ h (g⁻¹ • x)⟩

/-- Left translation fixes the constant sequence `1` in `ℓ∞`. -/
@[simp]
theorem leftTranslation_one (g : G) :
    leftTranslation X ∞ ℝ ℝ g (1 : lp (fun _ : X ↦ ℝ) ∞) = 1 := by
  ext x
  rfl

/-- In `ℓ¹`, the norm of `L_g f - f` is `∑' x, ‖f (g⁻¹ • x) - f x‖`. -/
theorem norm_leftTranslation_sub_one (g : G) (f : lp (fun _ : X ↦ E) 1) :
    ‖leftTranslation X 1 𝕜 E g f - f‖ = ∑' x, ‖f (g⁻¹ • x) - f x‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by simp) (leftTranslation X 1 𝕜 E g f - f)

/-- Left translation pushes `f.toLp p` forward along `Finsupp.mapDomain (g • ·)`. -/
@[simp]
theorem leftTranslation_toLp_finsupp (g : G) (f : X →₀ E) :
    leftTranslation X p 𝕜 E g (f.toLp p) = (f.mapDomain (g • ·)).toLp p :=
  LinearIsometryEquiv.lpCongrLeft_toLp_finsupp (MulAction.toPerm g) f

end lp

namespace Convexity.StdSimplex

/-- Left translation on `ℓᵖ` pushes a finitely supported probability distribution `w` forward to
`w.map (g • ·)`. -/
@[simp]
theorem leftTranslation_toLp {G X : Type*} [Group G] [MulAction G X] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : G) (w : StdSimplex ℝ X) :
    lp.leftTranslation X p ℝ ℝ g (w.toLp p) = (w.map (g • ·)).toLp p := by
  rw [toLp_def, toLp_def, weights_map]
  exact lp.leftTranslation_toLp_finsupp g w.weights

end Convexity.StdSimplex
