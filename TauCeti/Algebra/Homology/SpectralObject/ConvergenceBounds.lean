/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import TauCeti.Algebra.Homology.SpectralObject.PageHomology

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

Under convergence bounds, the spectral sequence `X.spectralSequence coreE₂Cohomological` computes
the graded pieces of the abutment in degree `n` on its late pages. At the position `(p, q)` with
`p + q = n`, the object of the page `r` is `E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`. On every page
`r ≥ 2` with `r ≥ q - a + 2` and `r ≥ b - q + 1`:

* the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` is
  an isomorphism (Mathlib's `isIso_mapFourδ₁Toδ₀'`, since `H^{n+1}(⊥ ≤ q - r + 2)` vanishes), and
  so is the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤) = X.EInfty q n`
  (`HasConvergenceBounds.isIso_mapFourδ₄Toδ₃'`), because `H^n(⊥ ≤ q + r - 1) ⟶ H^n(⊥ ≤ ⊤)` is a
  monomorphism (`isIso_mapFourδ₄Toδ₃'_of_mono`);
* hence the page object maps isomorphically onto the limit object `X.EInfty q n`, the graded piece
  of the abutment (`HasConvergenceBounds.isIso_spectralSequencePageXToEInfty`, an instance of the
  general criterion `isIso_spectralSequencePageXToEInfty_of_mono`), and isomorphically onto the
  objects at `(p, q)` of all later pages
  (`HasConvergenceBounds.isIso_spectralSequencePageXToPageX`);
* both differentials at `(p, q)` vanish (`HasConvergenceBounds.page_d_eq_zero`), as they do at any
  position where the passage to the next page is an isomorphism
  (`page_d_eq_zero_of_isIso_spectralSequencePageXToPageX`).

The limit object `X.EInfty q n` vanishes for `q < a` and for `q ≥ b`
(`HasConvergenceBounds.isZero_EInfty_of_lt`, `HasConvergenceBounds.isZero_EInfty_of_le`), so the
nonzero graded pieces sit at `a ≤ q < b`, where every position stabilizes from the page
`max 2 (b - a + 1)` on.

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
* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isIso_spectralSequencePageXToEInfty`,
  `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isIso_spectralSequencePageXToPageX`,
  `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.page_d_eq_zero`: under convergence
  bounds, the positions of total degree `n` stabilize on the late pages, at the graded pieces of
  the abutment.
* `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isZero_EInfty_of_lt`,
  `CategoryTheory.Abelian.SpectralObject.HasConvergenceBounds.isZero_EInfty_of_le`: the graded
  pieces vanish outside `[a, b)`.
* `CategoryTheory.Abelian.SpectralObject.hasConvergenceBounds_of_isFirstQuadrant`,
  `CategoryTheory.Abelian.SpectralObject.hasConvergenceBounds_of_isThirdQuadrant`: quadrant
  spectral objects have convergence bounds in every degree.

## References

* [Stacks, Tag 0BK5](https://stacks.math.columbia.edu/tag/0BK5), Lemma 24.13, in its
  filtered-complex form.
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

section Convergence

namespace HasConvergenceBounds

variable {X : SpectralObject C EInt} {n a b : ℤ}

/-- **The limit object is reached at the top under convergence bounds.** If `X` has convergence
bounds `a, b` in degree `n`, then for `q + 1 ≤ j` and `b ≤ j` the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ j) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤) = X.EInfty q n` is an isomorphism. -/
lemma isIso_mapFourδ₄Toδ₃' (h : X.HasConvergenceBounds n a b) (q j : ℤ) (hqj : q + 1 ≤ j)
    (hj : b ≤ j) :
    IsIso (X.mapFourδ₄Toδ₃' ⊥ q ((q + 1 : ℤ) : EInt) j ⊤ bot_le (coe_le_coe_add_one q)
      (by simpa using hqj) le_top (n - 1) n (n + 1)) :=
  have := h.isIso_H_map j hj
  X.isIso_mapFourδ₄Toδ₃'_of_mono _ _ _ _ _ _ _ _ _ _ _ _ inferInstance

/-- **Stabilization under convergence bounds.** If `X` has convergence bounds `a, b` in degree
`n = p + q`, the epimorphism `X.spectralSequencePageXToEInfty` from the object at `(p, q)` on the
page `r` onto the limit object `X.EInfty q n` is an isomorphism on every page `r ≥ 2` with
`r ≥ q - a + 2` and `r ≥ b - q + 1`. -/
theorem isIso_spectralSequencePageXToEInfty (h : X.HasConvergenceBounds n a b) (r : ℤ)
    (hr : 2 ≤ r) (pq : ℤ × ℤ) (hn : n = pq.1 + pq.2) (hra : pq.2 - a + 2 ≤ r)
    (hrb : b - pq.2 + 1 ≤ r) :
    IsIso (X.spectralSequencePageXToEInfty r hr pq n hn (h.isZero_H_add_one _ (by lia))) :=
  have := h.isIso_H_map (pq.2 + r - 1) (by lia)
  X.isIso_spectralSequencePageXToEInfty_of_mono r hr pq n hn _ inferInstance

/-- Under convergence bounds `a, b` in degree `n = p + q`, the canonical maps between the objects at
`(p, q)` on the pages `r ≤ r'` are isomorphisms as soon as `r ≥ 2`, `r ≥ q - a + 2` and
`r ≥ b - q + 1`. -/
theorem isIso_spectralSequencePageXToPageX (h : X.HasConvergenceBounds n a b) (r r' : ℤ)
    (hr : 2 ≤ r) (hrr' : r ≤ r') (pq : ℤ × ℤ) (hn : n = pq.1 + pq.2) (hra : pq.2 - a + 2 ≤ r)
    (hrb : b - pq.2 + 1 ≤ r) :
    IsIso (X.spectralSequencePageXToPageX r r' hr hrr' pq n hn (h.isZero_H_add_one _ (by lia))
      (h.isZero_H_add_one _ (by lia))) := by
  have := h.isIso_spectralSequencePageXToEInfty r' (hr.trans hrr') pq hn (by lia) (by lia)
  have : IsIso (X.spectralSequencePageXToPageX r r' hr hrr' pq n hn
      (h.isZero_H_add_one _ (by lia)) (h.isZero_H_add_one _ (by lia)) ≫
        X.spectralSequencePageXToEInfty r' (hr.trans hrr') pq n hn
          (h.isZero_H_add_one _ (by lia))) := by
    rw [spectralSequencePageXToPageX_spectralSequencePageXToEInfty]
    exact h.isIso_spectralSequencePageXToEInfty r hr pq hn hra hrb
  exact IsIso.of_isIso_comp_right _ (X.spectralSequencePageXToEInfty r' (hr.trans hrr') pq n hn
    (h.isZero_H_add_one _ (by lia)))

/-- **Degeneration at a position under convergence bounds.** If `X` has convergence bounds `a, b`
in degree `n = p + q`, both differentials at the position `(p, q)` vanish on every page `r ≥ 2`
with `r ≥ q - a + 2` and `r ≥ b - q + 1`. -/
theorem page_d_eq_zero (h : X.HasConvergenceBounds n a b) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hn : n = pq.1 + pq.2) (hra : pq.2 - a + 2 ≤ r) (hrb : b - pq.2 + 1 ≤ r) {i j : ℤ × ℤ}
    (hij : i = pq ∨ j = pq) :
    ((X.spectralSequence coreE₂Cohomological).page r hr).d i j = 0 := by
  have := h.isIso_spectralSequencePageXToPageX r (r + 1) hr (by lia) pq hn hra hrb
  exact X.page_d_eq_zero_of_isIso_spectralSequencePageXToPageX r hr pq n hn _ _ hij

/-- Under convergence bounds `a, b` in degree `n`, the limit object `X.EInfty q n` vanishes for
`q < a`: it is the graded piece `F_{q+1} H^n / F_q H^n`, and `F_{q+1} H^n` vanishes. -/
lemma isZero_EInfty_of_lt (h : X.HasConvergenceBounds n a b) {q : ℤ} (hq : q < a) :
    IsZero (X.EInfty q n) :=
  (IsZero.of_epi (cokernel.π _) (h.isZero_abutmentFiltration (by lia))).of_iso
    (X.EInftyIsoCokernel q n)

/-- Under convergence bounds `a, b` in degree `n`, the limit object `X.EInfty q n` vanishes for
`b ≤ q`: it is the graded piece `F_{q+1} H^n / F_q H^n`, and both pieces are the whole abutment. -/
lemma isZero_EInfty_of_le (h : X.HasConvergenceBounds n a b) {q : ℤ} (hq : b ≤ q) :
    IsZero (X.EInfty q n) := by
  have := h.isIso_abutmentFiltrationι hq
  have := h.isIso_abutmentFiltrationι (j := q + 1) (by lia)
  have : IsIso (X.abutmentFiltrationMap q n) := by
    have := X.abutmentFiltrationMap_ι q n
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  exact (isZero_cokernel_of_epi _).of_iso (X.EInftyIsoCokernel q n)

end HasConvergenceBounds

end Convergence

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
