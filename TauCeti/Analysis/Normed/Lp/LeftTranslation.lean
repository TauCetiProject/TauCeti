/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Finsupp

/-!
# Left translation on `ℓᵖ`

When a group `G` acts on `X` and `1 ≤ p`, applying `LinearIsometryEquiv.lpCongrLeft` to the
permutations `MulAction.toPerm g` assembles into the left-translation representation

```text
lp.leftTranslation X p 𝕜 E : G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : X ↦ E) p),
(L_g f) x = f (g⁻¹ • x),        L_g (δ_x) = δ_{g • x}.
```

It preserves coordinate sums and nonnegativity, fixes the constant sequence `1` in `ℓ∞`, pushes
finitely supported probability distributions `w : Convexity.StdSimplex ℝ X` forward to
`w.map (g • ·)`, and in `ℓ¹` satisfies `‖L_g f - f‖ = ∑' x, ‖f (g⁻¹ • x) - f x‖`.

## Main definitions

* `lp.leftTranslation X p 𝕜 E`: left translation `G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] ...)` for a
  `G`-action on `X`.

## Main results

* `lp.leftTranslation_single`: `L_g (lp.single p x v) = lp.single p (g • x) v`.
* `lp.tsum_leftTranslation`: `∑' x, L_g f x = ∑' x, f x`.
* `lp.norm_leftTranslation_sub_eq_tsum`: `‖L_g f - f‖ = ∑' x, ‖f (g⁻¹ • x) - f x‖` in `ℓ¹`.
* `Convexity.StdSimplex.leftTranslation_toLp`: `L_g (w.toLp p) = (w.map (g • ·)).toLp p`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.1 and G.3.
-/

public section

noncomputable section

open Convexity
open scoped ENNReal

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

/-- `lp.leftTranslation` acts by reindexing `ℓᵖ` along `MulAction.toPerm g`. -/
theorem leftTranslation_def (g : G) :
    leftTranslation X p 𝕜 E g = LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g) :=
  (rfl)

/-- Evaluating `L_g f` at `x` gives `f (g⁻¹ • x)`. -/
@[simp]
theorem leftTranslation_apply (g : G) (f : lp (fun _ : X ↦ E) p) (x : X) :
    leftTranslation X p 𝕜 E g f x = f (g⁻¹ • x) := by
  simp [leftTranslation_def]

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
theorem leftTranslation_symm (g : G) :
    (leftTranslation X p 𝕜 E g).symm = leftTranslation X p 𝕜 E g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Evaluating `(L_g).symm f` at `x` gives `f (g • x)`. -/
@[simp]
theorem leftTranslation_symm_apply (g : G) (f : lp (fun _ : X ↦ E) p) (x : X) :
    (leftTranslation X p 𝕜 E g).symm f x = f (g • x) := by
  rw [leftTranslation_symm, leftTranslation_apply, inv_inv]

/-- Left translation sends the coordinate vector `lp.single p x v` to `lp.single p (g • x) v`. -/
@[simp]
theorem leftTranslation_single [DecidableEq X] (g : G) (x : X) (v : E) :
    leftTranslation X p 𝕜 E g (lp.single p x v) = lp.single p (g • x) v :=
  LinearIsometryEquiv.lpCongrLeft_single (MulAction.toPerm g) x v

/-- Left translation preserves coordinate sums. -/
theorem tsum_leftTranslation (g : G) (f : lp (fun _ : X ↦ E) p) :
    ∑' x, leftTranslation X p 𝕜 E g f x = ∑' x, f x := by
  rw [leftTranslation_def]
  exact LinearIsometryEquiv.tsum_lpCongrLeft (MulAction.toPerm g) f

/-- Left translation preserves coordinatewise nonnegativity. -/
theorem forall_leftTranslation_nonneg_iff [LE E] {g : G} {f : lp (fun _ : X ↦ E) p} :
    (∀ x, 0 ≤ leftTranslation X p 𝕜 E g f x) ↔ ∀ x, 0 ≤ f x :=
  ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ by simpa using h (g⁻¹ • x)⟩

/-- Left translation fixes the constant sequence `1` in `ℓ∞`. -/
@[simp]
theorem leftTranslation_one {R : Type*} [NormedRing R] [NormOneClass R] [Module 𝕜 R]
    [IsBoundedSMul 𝕜 R] (g : G) :
    leftTranslation X ∞ 𝕜 R g (1 : lp (fun _ : X ↦ R) ∞) = 1 :=
  LinearIsometryEquiv.lpCongrLeft_one (MulAction.toPerm g)

/-- In `ℓ¹`, the norm of `L_g f - f` is `∑' x, ‖f (g⁻¹ • x) - f x‖`. -/
theorem norm_leftTranslation_sub_eq_tsum (g : G) (f : lp (fun _ : X ↦ E) 1) :
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
