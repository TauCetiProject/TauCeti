/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.MittagLeffler
public import TauCeti.Algebra.Homology.SpectralObject.Image
public import TauCeti.Algebra.Homology.SpectralObject.ModuleCat

/-!
# Regular spectral sequences of spectral objects of modules indexed by `EInt`

Let `X` be a spectral object in `ModuleCat R` indexed by `EInt`, with spectral sequence
`X.spectralSequence coreE₂Cohomological`, and let `n = p + q`. The object at `(p, q)` on page `r`
is `E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`, the image of `H^n(q - r + 2 ≤ q + 1)` in
`H^n(q ≤ q + r - 1)`. Its representatives in `H^n(q ≤ q + 1)` that come from
`H^n(q - r + 2 ≤ q + 1)` are the cycles `Z_r` of page `r`.

The spectral sequence is *regular* at `(n - t, t)` from `i₀` on when the cycles `Z_r` at that
position are the same on all pages `r ≥ t - i₀ + 2`
(`CategoryTheory.Abelian.SpectralObject.IsRegularAt`). This holds as soon as the differentials
leaving the object at `(n - t, t)` vanish on all late enough pages, which is Weibel's definition
of regularity (`CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`).

Regularity at every position `t ≤ q` makes the tower of the modules `H^n(s ≤ q + 1)`, `s ≤ q`,
Mittag-Leffler (`CategoryTheory.Abelian.SpectralObject.exists_range_le_range_of_isRegularAt`).
So a class of `H^n(q ≤ q + 1)` lying in every `Z_r` extends to a compatible family of classes of
all the `H^n(s ≤ q + 1)`
(`CategoryTheory.Abelian.SpectralObject.exists_compatible_family_of_forall_mem_range`). For the
spectral sequence of a filtered complex,
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Regular` lifts such families to the cohomology
of the complex when the filtration is complete, which gives the weak convergence of Weibel's
Complete Convergence Theorem 5.5.10.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.IsRegularAt`: regularity at a position, through the
  stabilization of the cycles.

## Main results

* `CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`: vanishing of the
  differentials leaving a position gives regularity there.
* `CategoryTheory.Abelian.SpectralObject.exists_range_le_range_of_isRegularAt`: regularity makes
  the tower `s ↦ H^n(s ≤ q + 1)` Mittag-Leffler.
* `CategoryTheory.Abelian.SpectralObject.exists_compatible_family_of_forall_mem_range`: lifting
  along this Mittag-Leffler tower.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, §3.5 (towers and the Mittag-Leffler
  condition), §5.2 (regular and weakly convergent spectral sequences) and Theorem 5.5.10.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

universe v

variable {R : Type*} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-! ### Regularity -/

/-- The spectral sequence of `X` is **regular in total degree `n` at the position `t` from `i₀`
on** when the images of the maps `H^n(i ≤ t + 1) ⟶ H^n(t ≤ t + 1)` are the same for all `i ≤ i₀`.
For `i = t - r + 2` this image is the module of cycles `Z_r` of the object at `(n - t, t)` on
page `r` (the elements represented by `H^n(t - r + 2 ≤ t + 1)`), so this says that
`Z_r = Z_{t - i₀ + 2}` for all `r ≥ t - i₀ + 2`. Weibel calls a spectral sequence regular when the
differentials leaving each object vanish on all late enough pages; that implies this property
(`CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`). -/
def IsRegularAt (n t i₀ : ℤ) : Prop :=
  ∃ h₀ : i₀ ≤ t, ∀ (i : ℤ) (_ : i ≤ i₀),
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i₀ : EInt) (t : EInt) ((t + 1 : ℤ) : EInt)
        (WithBotTop.coe_le_coe.2 h₀) (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (t : EInt) ((t + 1 : ℤ) : EInt)
        (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia)))).hom

variable {X}

/-- The stage `i₀` from which a spectral sequence is regular at the position `t` is at most `t`. -/
lemma IsRegularAt.le {n t i₀ : ℤ} (h : X.IsRegularAt n t i₀) : i₀ ≤ t := h.1

/-- The defining property of `IsRegularAt`, with `t + 1` given as any `u` equal to it. -/
lemma IsRegularAt.range_le {n t i₀ : ℤ} (h : X.IsRegularAt n t i₀) {u : ℤ} (hu : t + 1 = u)
    (i : ℤ) (hi : i ≤ i₀) :
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i₀ : EInt) (t : EInt) (u : EInt)
        (WithBotTop.coe_le_coe.2 h.le) (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (t : EInt) (u : EInt)
        (WithBotTop.coe_le_coe.2 (hi.trans h.le)) (WithBotTop.coe_le_coe.2 (by lia)))).hom := by
  subst hu
  exact h.2 i hi

/-- The characteristic property of `IsRegularAt`: the images of the maps
`H^n(i ≤ t + 1) ⟶ H^n(t ≤ t + 1)` are the same for all `i ≤ i₀ ≤ t`. -/
lemma isRegularAt_iff {n t i₀ : ℤ} :
    X.IsRegularAt n t i₀ ↔ ∃ h₀ : i₀ ≤ t, ∀ (i : ℤ) (_ : i ≤ i₀),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i₀ : EInt) (t : EInt) ((t + 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.2 h₀) (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
        LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (t : EInt) ((t + 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia)))).hom :=
  Iff.rfl

/-- A spectral sequence regular at the position `t` from `i₀` on is regular there from any
`i₁ ≤ i₀` on. -/
lemma IsRegularAt.mono {n t i₀ i₁ : ℤ} (h : X.IsRegularAt n t i₀) (hi : i₁ ≤ i₀) :
    X.IsRegularAt n t i₁ := by
  have := h.le
  exact ⟨by lia, fun i hi' ↦ (X.range_H_map_twoδ₁Toδ₀'_le (WithBotTop.coe_le_coe.2 hi) _ _).trans
    (h.range_le rfl i (hi'.trans hi))⟩

variable (X)

/-- Let `i₀ ≤ a ≤ b ≤ t ≤ u` and `x ∈ H^n(b ≤ u)`. If the image of `δ x ∈ H^{n+1}(i₀ ≤ b)` in
`H^{n+1}(a ≤ t)` vanishes, then the image of `x` in `H^n(t ≤ u)` comes from `H^n(a ≤ u)`. -/
private lemma mem_range_of_H_map_δ_eq_zero {n : ℤ} {i₀ a b t u : EInt} (h₀a : i₀ ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) (htu : t ≤ u) (φ : mk₁ (homOfLE (h₀a.trans hab)) ⟶ mk₁ (homOfLE (hab.trans hbt)))
    (x : (X.H n).obj (mk₁ (homOfLE (hbt.trans htu))))
    (hx : (X.H (n + 1)).map φ
      (X.δ (homOfLE (h₀a.trans hab)) (homOfLE (hbt.trans htu)) n (n + 1) rfl x) = 0) :
    (X.H n).map (twoδ₁Toδ₀' b t u hbt htu) x ∈
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' a t u (hab.trans hbt) htu)).hom := by
  -- The image `y` of `δ x` in `H^{n+1}(a ≤ b)` vanishes in `H^{n+1}(a ≤ t)`, so it is `δ v` for
  -- some `v ∈ H^n(b ≤ t)`.
  let α : mk₁ (homOfLE (h₀a.trans hab)) ⟶ mk₁ (homOfLE hab) :=
    homMk₁ (homOfLE h₀a) (𝟙 _) (Subsingleton.elim _ _)
  obtain ⟨v, hv⟩ := X.exists_δ_eq hab hbt
    ((X.H (n + 1)).map α (X.δ (homOfLE (h₀a.trans hab)) (homOfLE (hbt.trans htu)) n (n + 1) rfl x))
    (by rw [X.H_map_map_apply _ _ φ, hx])
  -- So `x` minus the image of `v` has vanishing `δ` into `H^{n+1}(a ≤ b)`.
  let β : mk₁ (homOfLE hbt) ⟶ mk₁ (homOfLE (hbt.trans htu)) :=
    homMk₁ (𝟙 _) (homOfLE htu) (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := X.exists_H_map_twoδ₁Toδ₀'_eq hab (hbt.trans htu) (x - (X.H n).map β v) (by
    rw [map_sub, X.δ_naturality_apply (homOfLE hab) (homOfLE hbt) _ _ (𝟙 _) β v,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply, hv,
      ← X.δ_naturality_apply (homOfLE (h₀a.trans hab)) _ (homOfLE hab) _ α (𝟙 _) x,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply, sub_self])
  refine ⟨w, ?_⟩
  rw [eq_sub_iff_add_eq] at hw
  rw [← hw, map_add, X.H_map_map_apply _ _ (twoδ₁Toδ₀' a t u (hab.trans hbt) htu)]
  -- The image of `v` in `H^n(t ≤ u)` factors through `H^n(t ≤ t) = 0`.
  have hz : (X.H n).map (twoδ₁Toδ₀' b t t hbt le_rfl) v = 0 :=
    have := (ModuleCat.isZero_iff_subsingleton).1 (X.isZero_H_obj_of_isIso (homOfLE (le_refl t))
      (by rw [Subsingleton.elim (homOfLE (le_refl t)) (𝟙 t)]; infer_instance) n)
    Subsingleton.elim _ _
  rw [X.H_map_map_apply _ _ (twoδ₁Toδ₀' b t t hbt le_rfl ≫ twoδ₂Toδ₁' t t u le_rfl htu),
    Functor.map_comp, ConcreteCategory.comp_apply, hz, map_zero, add_zero]

/-- **Cycles surviving a vanishing differential.** If the differential leaving the object at
`(n - t, t)` on page `r` vanishes, then every class of `H^n(t ≤ t + 1)` coming from
`H^n(t - r + 2 ≤ t + 1)`, that is a cycle of page `r`, comes from `H^n(t - r + 1 ≤ t + 1)`: it is
a cycle of page `r + 1`. -/
theorem range_le_range_of_page_d_eq_zero {n t r : ℤ} (hr : 2 ≤ r)
    (hd : ((X.spectralSequence coreE₂Cohomological).page r).d (n - t, t)
      (n - t + r, t - r + 1) = 0) :
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' ((t - r + 2 : ℤ) : EInt) (t : EInt)
        ((t + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' ((t - r + 1 : ℤ) : EInt) (t : EInt)
        ((t + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega)))).hom := by
  rintro _ ⟨x, rfl⟩
  have hpq : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (n - t, t) (n - t + r, t - r + 1) :=
    ComplexShape.up'_mk _ _ _ (Prod.ext (by simp) (by simp; ring))
  have h := ConcreteCategory.congr_hom (X.toE_spectralSequence_page_d coreE₂Cohomological r hr
    (n - t, t) (n - t + r, t - r + 1) hpq
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) :
      ((t - r + 1 - r + 2 : ℤ) : EInt) ⟶ ((t - r + 1 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) :
      ((t - r + 1 : ℤ) : EInt) ⟶ ((t - r + 2 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) : ((t - r + 2 : ℤ) : EInt) ⟶ (t : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) : (t : EInt) ⟶ ((t + 1 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) :
      ((t + 1 : ℤ) : EInt) ⟶ ((t + r - 1 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega))) (homOfLE (WithBotTop.coe_le_coe.2 (by omega)))
    rfl rfl rfl rfl rfl rfl (n - 1) n (n + 1) (n + 2) (by simp [coreE₂Cohomological])
    (by omega) (by omega) (by omega)) x
  rw [hd, Limits.comp_zero, Limits.comp_zero] at h
  simp only [ConcreteCategory.comp_apply] at h
  -- `δ x` represents zero on the target page, so its image in `H^{n+1}(t - r + 1 ≤ t)` vanishes.
  have h₁ := ((ModuleCat.mono_iff_injective _).1 inferInstance).eq_iff' (map_zero _) |>.1 h.symm
  have h₂ := congrArg (X.fromE (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) :
      ((t - r + 1 - r + 2 : ℤ) : EInt) ⟶ ((t - r + 1 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) :
      ((t - r + 1 : ℤ) : EInt) ⟶ ((t - r + 2 : ℤ) : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega)) : ((t - r + 2 : ℤ) : EInt) ⟶ (t : EInt))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega))) rfl n (n + 1) (n + 2) (by omega)
    (by omega)).hom h₁
  rw [← ConcreteCategory.comp_apply, X.toE_fromE (n₀ := n) (n₁ := n + 1) (n₂ := n + 2)
    (hn₂ := by omega), map_zero] at h₂
  exact X.mem_range_of_H_map_δ_eq_zero (WithBotTop.coe_le_coe.2 (by omega))
    (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))
    (WithBotTop.coe_le_coe.2 (by omega)) _ x h₂

/-- **Regularity in the sense of Weibel.** If the differentials leaving the object at
`(n - t, t)` vanish on every page `r ≥ r₀`, the spectral sequence is regular in total degree `n`
at the position `t` from `t - r₀ + 2` on. -/
theorem isRegularAt_of_page_d_eq_zero {n t r₀ : ℤ} (hr₀ : 2 ≤ r₀)
    (hd : ∀ (r : ℤ) (hr : r₀ ≤ r), ((X.spectralSequence coreE₂Cohomological).page r).d (n - t, t)
      (n - t + r, t - r + 1) = 0) :
    X.IsRegularAt n t (t - r₀ + 2) := by
  refine ⟨by omega, fun i hi ↦ ?_⟩
  -- The cycles of page `r₀` survive to every later page.
  have key (k : ℕ) : LinearMap.range ((X.H n).map (twoδ₁Toδ₀' ((t - r₀ + 2 : ℤ) : EInt) (t : EInt)
      ((t + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' ((t - (r₀ + k) + 2 : ℤ) : EInt) (t : EInt)
        ((t + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega)))).hom := by
    induction k with
    | zero => exact X.range_H_map_twoδ₁Toδ₀'_le (WithBotTop.coe_le_coe.2 (by omega)) _ _
    | succ k ih =>
      exact ih.trans ((X.range_le_range_of_page_d_eq_zero (r := r₀ + k) (by omega)
        (hd _ (by omega))).trans (X.range_H_map_twoδ₁Toδ₀'_le
          (WithBotTop.coe_le_coe.2 (by omega)) _ _))
  exact (key (t - r₀ + 2 - i).toNat).trans
    (X.range_H_map_twoδ₁Toδ₀'_le (WithBotTop.coe_le_coe.2 (by omega)) _ _)

/-! ### The Mittag-Leffler property -/

/-- One step of the Mittag-Leffler induction: if the images in `H^n(s ≤ b)` stabilize from `m₁`
on and the spectral sequence is regular at `s' = s - 1` from `i₁` on, then the images in
`H^n(s' ≤ b)` stabilize from any `m ≤ m₁, i₁` on. -/
private lemma range_le_range_of_isRegularAt_of_range_le {n s' s b : ℤ} (hs : s' + 1 = s)
    (hsb : s ≤ b) {m₁ : ℤ} (hm₁ : m₁ ≤ s)
    (hml : ∀ (i : ℤ) (hi : i ≤ m₁),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m₁ : EInt) (s : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 hm₁) (WithBotTop.coe_le_coe.2 hsb))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (s : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 hsb))).hom)
    {i₁ : ℤ} (hreg : X.IsRegularAt n s' i₁) {m : ℤ} (hmm₁ : m ≤ m₁) (hmi₁ : m ≤ i₁)
    (i : ℤ) (hi : i ≤ m) :
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m : EInt) (s' : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by have := hreg.le; lia))
        (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (s' : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by have := hreg.le; lia))
        (WithBotTop.coe_le_coe.2 (by lia)))).hom := by
  have hi₁ := hreg.le
  rintro _ ⟨a, rfl⟩
  -- The image of `a` in `H^n(s ≤ b)` comes from `H^n(i ≤ b)`, by the stabilization at level `s`.
  obtain ⟨bb, hbb⟩ := hml i (by lia) ⟨(X.H n).map (twoδ₁Toδ₀' (m : EInt) (m₁ : EInt) (b : EInt)
      (WithBotTop.coe_le_coe.2 hmm₁) (WithBotTop.coe_le_coe.2 (by lia))) a, X.H_map_map_apply _ _
      (twoδ₁Toδ₀' (m : EInt) (s : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 (by lia))
        (WithBotTop.coe_le_coe.2 hsb)) a⟩
  -- So `a` minus the image of `bb` vanishes in `H^n(s ≤ b)`, hence comes from `H^n(m ≤ s)`.
  obtain ⟨c, hc⟩ := X.exists_H_map_twoδ₂Toδ₁'_eq (n := n) (WithBotTop.coe_le_coe.2 (by lia : m ≤ s))
    (WithBotTop.coe_le_coe.2 hsb)
    (a - (X.H n).map (twoδ₁Toδ₀' (i : EInt) (m : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 hi)
      (WithBotTop.coe_le_coe.2 (by lia))) bb)
    (by
      rw [map_sub, X.H_map_map_apply _ _ (twoδ₁Toδ₀' (i : EInt) (s : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 hsb)), hbb, sub_self])
  -- The image of `c` in `H^n(s' ≤ s)` comes from `H^n(i ≤ s)`, by the regularity at `s'`.
  obtain ⟨c', hc'⟩ := hreg.range_le hs i (by lia) ⟨(X.H n).map (twoδ₁Toδ₀' (m : EInt) (i₁ : EInt)
      (s : EInt) (WithBotTop.coe_le_coe.2 hmi₁) (WithBotTop.coe_le_coe.2 (by lia))) c,
    X.H_map_map_apply _ _ (twoδ₁Toδ₀' (m : EInt) (s' : EInt) (s : EInt)
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))) c⟩
  refine ⟨(X.H n).map (twoδ₂Toδ₁' (i : EInt) (s : EInt) (b : EInt)
    (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 hsb)) c' + bb, ?_⟩
  rw [eq_sub_iff_add_eq] at hc
  rw [← hc, map_add, map_add, X.H_map_map_apply _ _ (twoδ₁Toδ₀' (i : EInt) (s' : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))) bb]
  congr 1
  rw [X.H_map_map_apply_eq _ _ (twoδ₁Toδ₀' (i : EInt) (s' : EInt) (s : EInt)
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia)))
    (twoδ₂Toδ₁' (s' : EInt) (s : EInt) (b : EInt)
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 hsb)), hc',
    X.H_map_map_apply_eq]

private lemma exists_range_le_range_of_isRegularAt_aux {n q : ℤ} (k : ℕ)
    (hreg : ∀ t, q - k ≤ t → t ≤ q → ∃ i₀, X.IsRegularAt n t i₀) :
    ∃ (m : ℤ) (hm : m ≤ q - k), ∀ (i : ℤ) (hi : i ≤ m),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m : EInt) ((q - k : ℤ) : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hm)
        (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) ((q - k : ℤ) : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by lia))
        (WithBotTop.coe_le_coe.2 (by lia)))).hom := by
  induction k with
  | zero =>
    obtain ⟨i₀, h⟩ := hreg (q - (0 : ℕ)) le_rfl (by lia)
    exact ⟨i₀, h.le, h.range_le (by lia)⟩
  | succ k ih =>
    obtain ⟨m₁, hm₁, hml⟩ := ih fun t ht ht' ↦ hreg t (by lia) ht'
    obtain ⟨i₁, h₁⟩ := hreg (q - (k + 1 : ℕ)) le_rfl (by lia)
    have := h₁.le
    exact ⟨min m₁ i₁, by lia, X.range_le_range_of_isRegularAt_of_range_le (by push_cast; ring)
      (by lia) hm₁ hml h₁
      (min_le_left _ _) (min_le_right _ _)⟩

/-- **Regularity makes the tower `s ↦ H^n(s ≤ q + 1)` Mittag-Leffler.** If the spectral sequence
is regular in total degree `n` at every position `t` with `s ≤ t ≤ q`, then the images of the maps
`H^n(i ≤ q + 1) ⟶ H^n(s ≤ q + 1)`, which decrease as `i` decreases, are the same for all `i ≤ m`,
for some `m ≤ s`. -/
theorem exists_range_le_range_of_isRegularAt {n q s : ℤ} (hs : s ≤ q)
    (hreg : ∀ t, s ≤ t → t ≤ q → ∃ i₀, X.IsRegularAt n t i₀) :
    ∃ (m : ℤ) (hm : m ≤ s), ∀ (i : ℤ) (hi : i ≤ m),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m : EInt) (s : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hm)
        (WithBotTop.coe_le_coe.2 (by lia)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (s : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by lia))
        (WithBotTop.coe_le_coe.2 (by lia)))).hom := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = q - k := ⟨(q - s).toNat, by lia⟩
  exact X.exists_range_le_range_of_isRegularAt_aux k hreg

/-- The tower `k ↦ H^n(q - k ≤ b)`, with the maps `H^n(q - k' ≤ b) ⟶ H^n(q - k ≤ b)` for
`k ≤ k'`. -/
private noncomputable def hTower (n q b : ℤ) (hqb : q ≤ b) : TauCeti.ModuleTower.{v} R :=
  { obj k := mk₁ (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q - k.unop ≤ b)))
    map {k k'} f := twoδ₁Toδ₀' ((q - k.unop : ℤ) : EInt) ((q - k'.unop : ℤ) : EInt) (b : EInt)
      (WithBotTop.coe_le_coe.2 (by have := leOfHom f.unop; omega))
      (WithBotTop.coe_le_coe.2 (by omega))
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ } ⋙ X.H n

/-- A sequence of elements `g k ∈ H^n(q - k ≤ b)` compatible under the maps between consecutive
levels gives a family of elements of all the `H^n(s ≤ b)`, `s ≤ b`, compatible under all the maps
`H^n(s ≤ b) ⟶ H^n(s' ≤ b)`, whose element at `q` is the image of `g 0`. -/
private lemma exists_compatible_family_of_compatible_seq {n q b : ℤ} (hqb : q ≤ b)
    (g : ∀ k : ℕ, (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q - k ≤ b)))))
    (hg : ∀ k : ℕ, (X.H n).map (twoδ₁Toδ₀' ((q - (k + 1 : ℕ) : ℤ) : EInt) ((q - k : ℤ) : EInt)
      (b : EInt) (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)))
        (g (k + 1)) = g k) :
    ∃ x : ∀ (s : ℤ) (_ : s ≤ b), (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 ‹s ≤ b›))),
      (∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ b),
        (X.H n).map (twoδ₁Toδ₀' (s : EInt) (s' : EInt) (b : EInt)
          (WithBotTop.coe_le_coe.2 h) (WithBotTop.coe_le_coe.2 h')) (x s (h.trans h')) =
          x s' h') ∧
      x q hqb = (X.H n).map (twoδ₁Toδ₀' ((q - (0 : ℕ) : ℤ) : EInt) (q : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 hqb)) (g 0) := by
  -- Compatibility across several levels.
  have hg' (j k : ℕ) (hkj : k ≤ j) : (X.H n).map (twoδ₁Toδ₀' ((q - j : ℤ) : EInt)
      ((q - k : ℤ) : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega))) (g j) = g k := by
    induction j with
    | zero =>
      obtain rfl : k = 0 := by omega
      exact X.H_map_self_apply _ _
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with hk | hk
      · rw [← X.H_map_map_apply (twoδ₁Toδ₀' ((q - (j + 1 : ℕ) : ℤ) : EInt) ((q - j : ℤ) : EInt)
          (b : EInt) (WithBotTop.coe_le_coe.2 (by omega))
          (WithBotTop.coe_le_coe.2 (by omega))) _, hg, ih (by omega)]
      · obtain rfl : k = j + 1 := by omega
        exact X.H_map_self_apply _ _
  -- The element at `s` is the image of the element of the sequence at the level `min s q`.
  refine ⟨fun s hs ↦ (X.H n).map (twoδ₁Toδ₀' ((q - (q - s).toNat : ℤ) : EInt) (s : EInt)
      (b : EInt) (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 hs))
      (g (q - s).toNat), fun s s' h h' ↦ ?_, ?_⟩
  · dsimp only
    rw [X.H_map_map_apply _ _ (twoδ₁Toδ₀' ((q - (q - s).toNat : ℤ) : EInt) (s' : EInt)
      (b : EInt) (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 h')),
      ← hg' (q - s).toNat (q - s').toNat (by omega), X.H_map_map_apply]
  · dsimp only
    rw [← hg' (q - q).toNat 0 (by omega), X.H_map_map_apply]

/-- **Lifting along a Mittag-Leffler tower.** Suppose that the images of the maps
`H^n(i ≤ q + 1) ⟶ H^n(s ≤ q + 1)` stabilize for every `s ≤ q`. Then every element `z` of
`H^n(q ≤ q + 1)` that comes from every `H^n(i ≤ q + 1)`, `i ≤ q`, is the image of a family of
elements `x s ∈ H^n(s ≤ q + 1)`, `s ≤ q + 1`, compatible under the maps
`H^n(s ≤ q + 1) ⟶ H^n(s' ≤ q + 1)`, with `x q = z`. This is
`TauCeti.ModuleTower.exists_limπ_eq_of_forall_mem_range` for the Mittag-Leffler tower
`k ↦ H^n(q - k ≤ q + 1)`. -/
theorem exists_compatible_family_of_forall_mem_range {n q : ℤ}
    (hml : ∀ (s : ℤ) (hs : s ≤ q), ∃ (m : ℤ) (hm : m ≤ s), ∀ (i : ℤ) (hi : i ≤ m),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m : EInt) (s : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hm)
        (WithBotTop.coe_le_coe.2 (by omega)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (s : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega)))).hom)
    (z : (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1)))))
    (hz : ∀ (i : ℤ) (hi : i ≤ q), z ∈ LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt)
      (q : EInt) ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hi)
      (WithBotTop.coe_le_coe.2 (by omega)))).hom) :
    ∃ x : ∀ (s : ℤ) (_ : s ≤ q + 1),
        (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 ‹s ≤ q + 1›))),
      (∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ q + 1),
        (X.H n).map (twoδ₁Toδ₀' (s : EInt) (s' : EInt) ((q + 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.2 h) (WithBotTop.coe_le_coe.2 h')) (x s (h.trans h')) =
          x s' h') ∧ x q (by omega) = z := by
  -- The tower `k ↦ H^n(q - k ≤ q + 1)` is Mittag-Leffler.
  have hML : (X.hTower n q (q + 1) (by omega)).IsMittagLeffler := by
    refine (TauCeti.ModuleTower.isMittagLeffler_iff_ranges _).2 fun k ↦ ?_
    obtain ⟨m, hm, hm'⟩ := hml (q - k) (by omega)
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = q - j := ⟨(q - m).toNat, by omega⟩
    refine ⟨j, by omega, fun k' hk' ↦ le_antisymm
      (TauCeti.ModuleTower.range_transitionOfLE_le _ _ hk') ?_⟩
    simp only [TauCeti.ModuleTower.transitionOfLE_def]
    exact hm' (q - k') (by omega)
  -- The image of `z` at the level `q - 0` lifts to the limit of the tower.
  obtain ⟨y, hy⟩ := TauCeti.ModuleTower.exists_limπ_eq_of_forall_mem_range _ hML
    (x := (X.H n).map (twoδ₁Toδ₀' (q : EInt) ((q - (0 : ℕ) : ℤ) : EInt) ((q + 1 : ℤ) : EInt)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))) z)
    fun k _ ↦ by
      obtain ⟨w, hw⟩ := hz (q - k) (by omega)
      refine ⟨w, ?_⟩
      rw [TauCeti.ModuleTower.transitionOfLE_def, ← hw]
      exact (X.H_map_map_apply _ _ _ w).symm
  obtain ⟨x, hx, hxq⟩ := X.exists_compatible_family_of_compatible_seq (by omega)
    (fun k ↦ (y : (X.hTower n q (q + 1) (by omega)).Product) k) fun k ↦ by
      have := (TauCeti.ModuleTower.mem_lim _).1 y.2 k
      rw [TauCeti.ModuleTower.transition_def] at this
      exact this
  refine ⟨x, hx, ?_⟩
  rw [hxq, ← TauCeti.ModuleTower.limπ_apply, hy, X.H_map_map_apply _ _ (𝟙 _), X.H_map_self_apply]

end CategoryTheory.Abelian.SpectralObject
