/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Abutment

/-!
# Convergence bounds of a spectral object

Let `X` be a spectral object in an abelian category, indexed by `EInt`. It has *convergence
bounds* `a, b` in degree `n` (`CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds`) when
`H^n(⊥ ≤ i)` and `H^{n+1}(⊥ ≤ i)` vanish for every integer `i ≤ a`, and the map
`H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` induced by `j ≤ ⊤` is an isomorphism for every integer `j ≥ b`. No
order between `a` and `b` is imposed. These are the hypotheses of the convergence lemma for
bounded filtrations, in degree `n` and in spectral-object form.

The bounds follow from the vanishing of `H^m(⊥ ≤ i)` for `m ∈ {n, n + 1}`, `i ≤ a`, and of
`H^m(j ≤ ⊤)` for `m ∈ {n - 1, n}`, `j ≥ b` (`HasConvergenceBounds.of_isZero`), by exactness of
`H^{n-1}(j ≤ ⊤) ⟶ H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤) ⟶ H^n(j ≤ ⊤)`. Lowering `a` or raising `b` keeps
convergence bounds (`HasConvergenceBounds.mono`), and they transport along isomorphisms of
spectral objects (`HasConvergenceBounds.of_iso`). Under convergence bounds, the filtration of the
abutment vanishes from `a` down (`HasConvergenceBounds.isZero_abutmentFiltration`) and is the whole
abutment from `b` up (`HasConvergenceBounds.isIso_abutmentFiltrationι`), so the abutment vanishes
when `b ≤ a` (`HasConvergenceBounds.isZero_abutment`).

A first-quadrant spectral object has convergence bounds `min 0 (n + 1)` and `n + 1` in every
degree `n`, and its abutment vanishes in negative degrees; a third-quadrant one has convergence
bounds `min m 1` and `1` in every cohomological degree `m`.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds`: convergence bounds in degree `n`.

## Main results

* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.of_isZero`: endpoint vanishing
  implies convergence bounds.
* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.mono`,
  `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.of_iso`: monotonicity and transport.
* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isZero_abutmentFiltration`,
  `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isIso_abutmentFiltrationι`: the
  filtration of the abutment is bounded by `a` and `b`.
* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isZero_abutment`: convergence bounds
  with `b ≤ a` force the abutment to vanish.
* `CategoryTheory.Abelian.SpectralObject.hasConvergenceBounds_of_isFirstQuadrant`,
  `CategoryTheory.Abelian.SpectralObject.hasConvergenceBounds_of_isThirdQuadrant`: quadrant
  spectral objects have convergence bounds in every degree.

## References

* [Stacks, Tag 0BK5](https://stacks.math.columbia.edu/tag/0BK5)
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- A spectral object `X` indexed by `EInt` has **convergence bounds** `a, b` in degree `n` when
`H^n(⊥ ≤ i)` and `H^{n+1}(⊥ ≤ i)` vanish for every integer `i ≤ a`, and the map
`H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` induced by `j ≤ ⊤` is an isomorphism for every integer `j ≥ b`. -/
structure HasConvergenceBounds (X : SpectralObject C EInt) (n a b : ℤ) : Prop where
  /-- `H^n(⊥ ≤ i)` vanishes for `i ≤ a`. -/
  isZero_H (i : ℤ) (hi : i ≤ a) : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i))))
  /-- `H^{n+1}(⊥ ≤ i)` vanishes for `i ≤ a`. -/
  isZero_H_add_one (i : ℤ) (hi : i ≤ a) :
    IsZero ((X.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i))))
  /-- `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` is an isomorphism for `j ≥ b`. -/
  isIso_H_map (j : ℤ) (hj : b ≤ j) :
    IsIso ((X.H n).map (twoδ₂Toδ₁ (homOfLE (bot_le : (⊥ : EInt) ≤ j))
      (homOfLE (le_top : (j : EInt) ≤ ⊤)) (homOfLE bot_le) (Subsingleton.elim _ _)))

namespace HasConvergenceBounds

variable {X : SpectralObject C EInt} {n a b : ℤ}

/-- **Endpoint vanishing gives convergence bounds.** If `H^m(⊥ ≤ i)` vanishes for `m ∈ {n, n + 1}`
and `i ≤ a`, and `H^m(j ≤ ⊤)` vanishes for `m ∈ {n - 1, n}` and `j ≥ b`, then `X` has convergence
bounds `a, b` in degree `n`. -/
theorem of_isZero
    (ha : ∀ i : ℤ, i ≤ a → IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i)))))
    (ha' : ∀ i : ℤ, i ≤ a →
      IsZero ((X.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i)))))
    (hb : ∀ j : ℤ, b ≤ j →
      IsZero ((X.H (n - 1)).obj (mk₁ (homOfLE (le_top : (j : EInt) ≤ ⊤)))))
    (hb' : ∀ j : ℤ, b ≤ j → IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (j : EInt) ≤ ⊤))))) :
    X.HasConvergenceBounds n a b where
  isZero_H := ha
  isZero_H_add_one := ha'
  isIso_H_map j hj :=
    X.isIso_H_map_twoδ₂Toδ₁ (n - 1) n (sub_add_cancel n 1) _ _ _ _ (hb j hj) (hb' j hj)

/-- **Convergence bounds are monotone**: lowering `a` or raising `b` keeps them. -/
theorem mono (h : X.HasConvergenceBounds n a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    X.HasConvergenceBounds n a' b' where
  isZero_H i hi := h.isZero_H i (hi.trans ha)
  isZero_H_add_one i hi := h.isZero_H_add_one i (hi.trans ha)
  isIso_H_map j hj := h.isIso_H_map j (hb.trans hj)

/-- Two sets of convergence bounds in degree `n` have common ones. -/
theorem exists_common {Y : SpectralObject C EInt} {a' b' : ℤ}
    (hX : X.HasConvergenceBounds n a b) (hY : Y.HasConvergenceBounds n a' b') :
    ∃ a'' b'' : ℤ, X.HasConvergenceBounds n a'' b'' ∧ Y.HasConvergenceBounds n a'' b'' :=
  ⟨min a a', max b b', hX.mono (min_le_left _ _) (le_max_left _ _),
    hY.mono (min_le_right _ _) (le_max_right _ _)⟩

/-- **Convergence bounds transport along isomorphisms** of spectral objects. -/
theorem of_iso {Y : SpectralObject C EInt} (e : X ≅ Y) (h : X.HasConvergenceBounds n a b) :
    Y.HasConvergenceBounds n a b where
  isZero_H i hi := (h.isZero_H i hi).of_iso ((asIso (e.hom.hom n)).app _).symm
  isZero_H_add_one i hi := (h.isZero_H_add_one i hi).of_iso ((asIso (e.hom.hom (n + 1))).app _).symm
  isIso_H_map j hj := (NatIso.isIso_map_iff (asIso (e.hom.hom n)) _).mp (h.isIso_H_map j hj)

/-- Under convergence bounds `a, b` in degree `n`, the filtration of the abutment vanishes at
every `i ≤ a`. -/
theorem isZero_abutmentFiltration (h : X.HasConvergenceBounds n a b) {i : ℤ} (hi : i ≤ a) :
    IsZero (X.abutmentFiltration i n) :=
  X.isZero_abutmentFiltration (h.isZero_H i hi)

/-- Under convergence bounds `a, b` in degree `n`, the filtration of the abutment is the whole
abutment at every `j ≥ b`. -/
theorem isIso_abutmentFiltrationι (h : X.HasConvergenceBounds n a b) {j : ℤ} (hj : b ≤ j) :
    IsIso (X.abutmentFiltrationι j n) :=
  have := h.isIso_H_map j hj
  X.isIso_abutmentFiltrationι_of_epi

/-- Convergence bounds `a, b` in degree `n` with `b ≤ a` force the abutment in degree `n` to
vanish: its filtration is the whole abutment at `b` and vanishes there. -/
theorem isZero_abutment (h : X.HasConvergenceBounds n a b) (hba : b ≤ a) :
    IsZero (X.abutment n) :=
  have := h.isIso_abutmentFiltrationι (le_refl b)
  (h.isZero_abutmentFiltration hba).of_iso (asIso (X.abutmentFiltrationι b n)).symm

end HasConvergenceBounds

section Quadrant

variable (X : SpectralObject C EInt)

/-- A first-quadrant spectral object has convergence bounds `min 0 (n + 1)` and `n + 1` in every
degree `n`. -/
theorem hasConvergenceBounds_of_isFirstQuadrant [X.IsFirstQuadrant] (n : ℤ) :
    X.HasConvergenceBounds n (min 0 (n + 1)) (n + 1) :=
  .of_isZero
    (fun i hi ↦ X.isZero₁_of_isFirstQuadrant _ _ _ (by simpa using (hi.trans (min_le_left _ _))) _)
    (fun i hi ↦ X.isZero₁_of_isFirstQuadrant _ _ _ (by simpa using (hi.trans (min_le_left _ _))) _)
    (fun j hj ↦ X.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia))
    (fun j hj ↦ X.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia))

/-- The abutment `H^n(⊥ ≤ ⊤)` of a first-quadrant spectral object vanishes in negative degrees. -/
theorem isZero_abutment_of_isFirstQuadrant [X.IsFirstQuadrant] {n : ℤ} (hn : n < 0) :
    IsZero (X.abutment n) :=
  (X.hasConvergenceBounds_of_isFirstQuadrant n).isZero_abutment (by lia)

/-- A third-quadrant spectral object has convergence bounds `min m 1` and `1` in every
cohomological degree `m`. -/
theorem hasConvergenceBounds_of_isThirdQuadrant [X.IsThirdQuadrant] (m : ℤ) :
    X.HasConvergenceBounds m (min m 1) 1 :=
  .of_isZero
    (fun i hi ↦ X.isZero₂_of_isThirdQuadrant _ _ _ _ (by simpa using (hi.trans (min_le_left _ _))))
    (fun i hi ↦ X.isZero₂_of_isThirdQuadrant _ _ _ _ (by simp; lia))
    (fun j hj ↦ X.isZero₁_of_isThirdQuadrant _ _ _ (by simp; lia) _)
    (fun j hj ↦ X.isZero₁_of_isThirdQuadrant _ _ _ (by simp; lia) _)

end Quadrant

end CategoryTheory.Abelian.SpectralObject
