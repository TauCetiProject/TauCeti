/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.BoundedBelow
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.Algebra.Homology.ModuleCat.Cokernel

/-!
# Weak convergence of the regular spectral sequence of a complete filtration

Let `F` be an increasing filtration of a cochain complex of modules `K`, with spectral sequence
`E`, and let `n = p + q`. The object at `(p, q)` on page `r` is
`E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`, the image of `H^n(F_{q+1}/F_{q-r+2})` in
`H^n(F_{q+r-1}/F_q)`. Its representatives in `H^n(F_{q+1}/F_q)` that come from
`H^n(F_{q+1}/F_{q-r+2})` are the cycles `Z_r` of page `r`. The graded piece
`F_{q+1} H^n / F_q H^n` of the abutment is `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`), whose representatives are the
*permanent cycles*, the classes that come from `H^n(F_{q+1})` itself. When `F` is not bounded below,
the permanent cycles can be strictly fewer than the classes lying in every `Z_r`. This file shows
that they are not when the filtration is complete and the spectral sequence is regular, which is
the weak convergence part of Weibel's Complete Convergence Theorem 5.5.10.

The spectral sequence is *regular* at `(n - t, t)` from `i₀` on when the cycles `Z_r` at that
position are the same on all pages `r ≥ t - i₀ + 2`
(`CategoryTheory.Abelian.SpectralObject.IsRegularAt`). This holds as soon as the differentials
leaving the object at `(n - t, t)` vanish on all late enough pages, which is Weibel's definition
of regularity (`CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`). The proof
of weak convergence has two steps.

* **Mittag-Leffler.** Regularity at every position `t ≤ q` makes the tower of the modules
  `H^n(F_{q+1}/F_s)`, `s ≤ q`, Mittag-Leffler
  (`CategoryTheory.Abelian.SpectralObject.exists_range_le_range_of_isRegularAt`). So a class of
  `H^n(F_{q+1}/F_q)` lying in every `Z_r` extends to a compatible family of classes of all the
  `H^n(F_{q+1}/F_s)`
  (`CategoryTheory.Abelian.SpectralObject.exists_compatible_family_of_forall_mem_range`).
* **Completeness.** If the stages `F_{q+1-k}` form a complete filtration of `K^n` and the
  filtration of `K^{n+1}` is separated, a compatible family of classes of the `H^n(F_{q+1}/F_s)`
  comes from `H^n(F_{q+1})`
  (`CochainComplex.exists_spectralObject_H_map_eq_of_isCompleteFiltration`).
  This is the surjectivity of `H^n(lim) ⟶ lim H^n` for the tower of quotients, proved by
  successive approximation of cocycle representatives.

Together, the permanent cycles are the cycles of all late enough pages
(`CochainComplex.exists_spectralObject_H_map_eq_of_isRegularAt`), so the canonical maps
`E^n(⊥ ≤ q ≤ q + 1 ≤ j) ⟶ E^n(i ≤ q ≤ q + 1 ≤ j)` are isomorphisms for `i` small enough
(`CochainComplex.isIso_mapFourδ₁Toδ₀'_of_isRegularAt`). For a filtration, the object at `(p, q)` on
every late enough page `r` is therefore `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`
(`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`) and maps onto the graded piece
`F_{q+1} H^n / F_q H^n` (`CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`). When
the filtration is moreover exhaustive in degree `n - 1`, an element vanishes in the graded piece
exactly when it vanishes on some later page
(`CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff`): the graded piece
is the direct limit of the pages, which is weak convergence. No boundedness of the filtration is
assumed in any degree; the strong convergence statements of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete` need in addition the vanishing of the
graded cohomology beyond a bound.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.IsRegularAt`: regularity at a position, through the
  stabilization of the cycles.
* `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`,
  `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`: the late pages of a regular
  spectral sequence of a complete filtration, and their epimorphisms onto the graded pieces.

## Main results

* `CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`: vanishing of the
  differentials leaving a position gives regularity there.
* `CochainComplex.isIso_mapFourδ₁Toδ₀'_of_isRegularAt`: for a complete filtration with regular
  spectral sequence, the permanent cycles are the cycles of the late pages.
* `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff`: **weak
  convergence** of the regular spectral sequence of a complete exhaustive filtration.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, §3.5 (towers and the Mittag-Leffler
  condition), §5.2 (regular and weakly convergent spectral sequences) and Theorem 5.5.10.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

universe v

variable {R : Type*} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

section Elementwise

/-! ### Elementwise computations in a spectral object of modules indexed by `EInt`

Morphisms in `ComposableArrows EInt 1` are unique, so the maps `H^n(f) ⟶ H^n(g)` compose to the
map induced by any morphism `f ⟶ g`. -/

private lemma H_map_map_apply {n : ℤ} {A B C : ComposableArrows EInt 1} (φ : A ⟶ B)
    (ψ : B ⟶ C) (χ : A ⟶ C) (x : (X.H n).obj A) :
    (X.H n).map ψ ((X.H n).map φ x) = (X.H n).map χ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (φ ≫ ψ) χ]

private lemma H_map_map_apply_eq {n : ℤ} {A B B' C : ComposableArrows EInt 1} (φ : A ⟶ B)
    (ψ : B ⟶ C) (φ' : A ⟶ B') (ψ' : B' ⟶ C) (x : (X.H n).obj A) :
    (X.H n).map ψ ((X.H n).map φ x) = (X.H n).map ψ' ((X.H n).map φ' x) := by
  rw [X.H_map_map_apply φ ψ (φ ≫ ψ), X.H_map_map_apply φ' ψ' (φ ≫ ψ)]

private lemma H_map_self_apply {n : ℤ} {A : ComposableArrows EInt 1} (φ : A ⟶ A)
    (x : (X.H n).obj A) : (X.H n).map φ x = x := by
  rw [Subsingleton.elim φ (𝟙 A), Functor.map_id, ModuleCat.id_apply]

/-- Exactness of `H^n(i ≤ j) ⟶ H^n(i ≤ k) ⟶ H^n(j ≤ k)`, on elements. -/
private lemma exists_H_map_twoδ₂Toδ₁'_eq {n : ℤ} {i j k : EInt} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (X.H n).obj (mk₁ (homOfLE (hij.trans hjk))))
    (hx : (X.H n).map (twoδ₁Toδ₀' i j k hij hjk) x = 0) :
    ∃ y : (X.H n).obj (mk₁ (homOfLE hij)), (X.H n).map (twoδ₂Toδ₁' i j k hij hjk) y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₂ (homOfLE hij) (homOfLE hjk) _ rfl n) x hx

/-- Exactness of `H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j) ⟶ H^{n+1}(i ≤ k)`, on elements. -/
private lemma exists_δ_eq {n : ℤ} {i j k : EInt} (hij : i ≤ j) (hjk : j ≤ k)
    (y : (X.H (n + 1)).obj (mk₁ (homOfLE hij)))
    (hy : (X.H (n + 1)).map (twoδ₂Toδ₁' i j k hij hjk) y = 0) :
    ∃ u : (X.H n).obj (mk₁ (homOfLE hjk)), X.δ (homOfLE hij) (homOfLE hjk) n (n + 1) rfl u = y :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₁ (homOfLE hij) (homOfLE hjk) _ rfl n (n + 1)) y hy

/-- Exactness of `H^n(i ≤ k) ⟶ H^n(j ≤ k) ⟶ H^{n+1}(i ≤ j)`, on elements. -/
private lemma exists_H_map_twoδ₁Toδ₀'_eq {n : ℤ} {i j k : EInt} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (X.H n).obj (mk₁ (homOfLE hjk)))
    (hx : X.δ (homOfLE hij) (homOfLE hjk) n (n + 1) rfl x = 0) :
    ∃ w : (X.H n).obj (mk₁ (homOfLE (hij.trans hjk))),
      (X.H n).map (twoδ₁Toδ₀' i j k hij hjk) w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (X.exact₃ (homOfLE hij) (homOfLE hjk) _ rfl n (n + 1)) x hx

private lemma δ_naturality_apply {n : ℤ} {i j k i' j' k' : EInt} (f : i ⟶ j) (g : j ⟶ k)
    (f' : i' ⟶ j') (g' : j' ⟶ k') (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g')
    (x : (X.H n).obj (mk₁ g)) :
    X.δ f' g' n (n + 1) rfl ((X.H n).map β x) = (X.H (n + 1)).map α (X.δ f g n (n + 1) rfl x) :=
  ConcreteCategory.congr_hom (X.δ_naturality f g f' g' α β n (n + 1) (Subsingleton.elim _ _)) x

/-- The images of the maps `H^n(i ≤ b) ⟶ H^n(s ≤ b)` decrease as `i` decreases. -/
private lemma range_H_map_twoδ₁Toδ₀'_le {n : ℤ} {i i' s b : EInt} (hi : i' ≤ i) (his : i ≤ s)
    (hsb : s ≤ b) :
    LinearMap.range ((X.H n).map (twoδ₁Toδ₀' i' s b (hi.trans his) hsb)).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' i s b his hsb)).hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(X.H n).map (twoδ₁Toδ₀' i' i b hi (his.trans hsb)) y, X.H_map_map_apply _ _ _ y⟩

end Elementwise

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
  have hpq : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (n - t, t) (n - t + r, t - r + 1) := by
    change (n - t, t) + (r, 1 - r) = (n - t + r, t - r + 1)
    ext <;> simp
    ring
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

/-- One step of the lifting along a Mittag-Leffler tower: if the images in `H^n(s' ≤ b)` stabilize
from `m` on, an element of `H^n(s ≤ b)`, `s' ≤ s`, coming from every `H^n(i ≤ b)`, `i ≤ s`, is the
image of an element of `H^n(s' ≤ b)` coming from every `H^n(i ≤ b)`, `i ≤ s'`. -/
private lemma exists_H_map_eq_of_forall_mem_range {n s' s b m : ℤ} (hs : s' ≤ s) (hsb : s ≤ b)
    (hm : m ≤ s')
    (hml : ∀ (i : ℤ) (hi : i ≤ m),
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (m : EInt) (s' : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 hm) (WithBotTop.coe_le_coe.2 (by omega)))).hom ≤
      LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt) (s' : EInt) (b : EInt)
        (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)))).hom)
    (y : (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 hsb))))
    (hy : ∀ (i : ℤ) (hi : i ≤ s), y ∈ LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt)
      (s : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 hi) (WithBotTop.coe_le_coe.2 hsb))).hom) :
    ∃ y' : (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 (hs.trans hsb)))),
      (∀ (i : ℤ) (hi : i ≤ s'), y' ∈ LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt)
        (s' : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 hi)
        (WithBotTop.coe_le_coe.2 (hs.trans hsb)))).hom) ∧
      (X.H n).map (twoδ₁Toδ₀' (s' : EInt) (s : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 hs)
        (WithBotTop.coe_le_coe.2 hsb)) y' = y := by
  obtain ⟨w, rfl⟩ := hy m (by omega)
  refine ⟨(X.H n).map (twoδ₁Toδ₀' (m : EInt) (s' : EInt) (b : EInt) (WithBotTop.coe_le_coe.2 hm)
    (WithBotTop.coe_le_coe.2 (by omega))) w, fun i hi ↦ ?_, X.H_map_map_apply _ _ _ w⟩
  rcases le_or_gt i m with him | him
  · exact hml i him ⟨w, rfl⟩
  · exact ⟨(X.H n).map (twoδ₁Toδ₀' (m : EInt) (i : EInt) (b : EInt)
      (WithBotTop.coe_le_coe.2 him.le) (WithBotTop.coe_le_coe.2 (by omega))) w,
      X.H_map_map_apply _ _ _ w⟩

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
`H^n(s ≤ q + 1) ⟶ H^n(s' ≤ q + 1)`, with `x q = z`. -/
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
  -- The elements of `H^n(q - k ≤ q + 1)` that come from every `H^n(i ≤ q + 1)`, `i ≤ q - k`.
  let P (k : ℕ) (y : (X.H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2
      (by omega : q - k ≤ q + 1))))) : Prop :=
    ∀ (i : ℤ) (hi : i ≤ q - k), y ∈ LinearMap.range ((X.H n).map (twoδ₁Toδ₀' (i : EInt)
      ((q - k : ℤ) : EInt) ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hi)
      (WithBotTop.coe_le_coe.2 (by omega)))).hom
  -- They lift to the next level, by the Mittag-Leffler property there.
  have step (k : ℕ) (y) (hy : P k y) : ∃ y', P (k + 1) y' ∧
      (X.H n).map (twoδ₁Toδ₀' ((q - (k + 1 : ℕ) : ℤ) : EInt) ((q - k : ℤ) : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega))) y' = y :=
    let ⟨_, hm, hm'⟩ := hml (q - (k + 1 : ℕ)) (by omega)
    X.exists_H_map_eq_of_forall_mem_range (by omega) (by omega) hm hm' y hy
  choose f hf using step
  -- The image of `z` at the level `q - 0`.
  have h₀ : P 0 ((X.H n).map (twoδ₁Toδ₀' (q : EInt) ((q - (0 : ℕ) : ℤ) : EInt)
      ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega))) z) := fun i hi ↦ by
    obtain ⟨w, hw⟩ := hz i (by omega)
    exact ⟨w, by rw [← hw, X.H_map_map_apply]⟩
  -- The sequence of successive lifts of `z`.
  obtain ⟨g, hg₀, hgs⟩ : ∃ g : (k : ℕ) → {y // P k y},
      (g 0).1 = (X.H n).map (twoδ₁Toδ₀' (q : EInt) ((q - (0 : ℕ) : ℤ) : EInt)
        ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
        (WithBotTop.coe_le_coe.2 (by omega))) z ∧
      ∀ k, (g (k + 1)).1 = f k (g k).1 (g k).2 :=
    ⟨fun k ↦ Nat.rec ⟨_, h₀⟩ (fun k y ↦ ⟨f k y.1 y.2, (hf k y.1 y.2).1⟩) k, rfl, fun _ ↦ rfl⟩
  obtain ⟨x, hx, hxq⟩ := X.exists_compatible_family_of_compatible_seq (by omega)
    (fun k ↦ (g k).1) fun k ↦ by rw [hgs]; exact (hf k _ _).2
  refine ⟨x, hx, ?_⟩
  rw [hxq, hg₀, X.H_map_map_apply _ _ (𝟙 _), X.H_map_self_apply]

end CategoryTheory.Abelian.SpectralObject

namespace CochainComplex

universe v

variable {R : Type*} [Ring R]

section Functor

variable (G : EInt ⥤ CochainComplex (ModuleCat.{v} R) ℤ)

/-- The maps between the quotients `G_a / G_s` induced by `G`, on representatives in `G_a`. -/
private lemma cokernelMap_f_π_f_apply {s s' a : EInt} (f : s ⟶ a) (g : s' ⟶ a) (u : s ⟶ s')
    (v : a ⟶ a)
    (w : G.map f ≫ G.map v = G.map u ≫ G.map g) (m : ℤ) (y : (G.obj a).X m) :
    (cokernel.map (G.map f) (G.map g) (G.map u) (G.map v) w).f m ((cokernel.π (G.map f)).f m y) =
      (cokernel.π (G.map g)).f m y := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, cokernel.π_desc,
    Subsingleton.elim v (𝟙 a), G.map_id, Category.id_comp]

/-- The maps between the quotients `G_a / G_s` induced by `G`, on homology classes of
representatives in `G_a`. -/
private lemma homologyMap_cokernelMap_moduleCatKerHomologyClass {s s' a : EInt} (f : s ⟶ a)
    (g : s' ⟶ a)
    (u : s ⟶ s') (v : a ⟶ a) (w : G.map f ≫ G.map v = G.map u ≫ G.map g) (n : ℤ)
    (y : (G.obj a).X n)
    (hy : ((cokernel (G.map f)).d n (n + 1)) ((cokernel.π (G.map f)).f n y) = 0)
    (hy' : ((cokernel (G.map g)).d n (n + 1)) ((cokernel.π (G.map g)).f n y) = 0) :
    HomologicalComplex.homologyMap (cokernel.map (G.map f) (G.map g) (G.map u) (G.map v) w) n
        ((cokernel (G.map f)).moduleCatKerHomologyClass (CochainComplex.next ℤ n)
          ⟨(cokernel.π (G.map f)).f n y, hy⟩) =
      (cokernel (G.map g)).moduleCatKerHomologyClass (CochainComplex.next ℤ n)
        ⟨(cokernel.π (G.map g)).f n y, hy'⟩ := by
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass]
  congr 2
  exact cokernelMap_f_π_f_apply G f g u v w n y

private lemma range_map_f_le {s s' a : EInt} (f : s ⟶ a) (g : s' ⟶ a) (u : s ⟶ s') (m : ℤ) :
    LinearMap.range ((G.map f).f m).hom ≤ LinearMap.range ((G.map g).f m).hom := by
  rw [Subsingleton.elim f (u ≫ g), G.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  exact LinearMap.range_comp_le_range _ _

private lemma map_comp_map_eq {s s' a b : EInt} (f : s ⟶ a) (v : a ⟶ b) (u : s ⟶ s') (g : s' ⟶ b) :
    G.map f ≫ G.map v = G.map u ≫ G.map g := by
  rw [← G.map_comp, ← G.map_comp, Subsingleton.elim (f ≫ v) (u ≫ g)]

/-- The cochain `c` of `G_a` represents the class `ξ` of `H^n(G_a / G_s)`. -/
private def IsCokernelRep {s a : EInt} (f : s ⟶ a) {n : ℤ}
    (ξ : (cokernel (G.map f)).homology n) (c : (G.obj a).X n) : Prop :=
  ∃ hc : ((cokernel (G.map f)).d n (n + 1)) ((cokernel.π (G.map f)).f n c) = 0,
    (cokernel (G.map f)).moduleCatKerHomologyClass (CochainComplex.next ℤ n) ⟨_, hc⟩ = ξ

private lemma exists_isCokernelRep {s a : EInt} (f : s ⟶ a) {n : ℤ}
    (ξ : (cokernel (G.map f)).homology n) : ∃ c, IsCokernelRep G f ξ c := by
  obtain ⟨⟨z, hz⟩, hzξ⟩ := HomologicalComplex.moduleCatKerHomologyClass_surjective _ _ ξ
  obtain ⟨c, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n z
  exact ⟨c, hz, hzξ⟩

/-- Let `s' ≤ s ≤ a`, and let `ξ` be the image of a class `ξ'` of `H^n(G_a / G_{s'})` in
`H^n(G_a / G_s)`. A representative of `ξ` is corrected by an element of `G_s` to a representative
of `ξ'`. -/
private lemma exists_isCokernelRep_sub_mem_range {s' s a : EInt} (f' : s' ⟶ a) (f : s ⟶ a)
    (u : s' ⟶ s) {n : ℤ} (ξ' : (cokernel (G.map f')).homology n)
    (ξ : (cokernel (G.map f)).homology n)
    (hξ : HomologicalComplex.homologyMap (cokernel.map (G.map f') (G.map f) (G.map u)
      (G.map (𝟙 a)) (map_comp_map_eq G _ _ _ _)) n ξ' = ξ)
    (c : (G.obj a).X n) (hc : IsCokernelRep G f ξ c) :
    ∃ c', IsCokernelRep G f' ξ' c' ∧ c' - c ∈ LinearMap.range ((G.map f).f n).hom := by
  obtain ⟨c', hc'₁, hc'₂⟩ := exists_isCokernelRep G f' ξ'
  -- `c'` also represents `ξ` modulo `G_s`, so it differs from `c` by a boundary modulo `G_s`.
  have hc'₃ := (HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff (G.map f) n (n + 1) c').2
    (range_map_f_le G _ _ u _ ((HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1)
      c').1 hc'₁))
  obtain ⟨e, he⟩ := HomologicalComplex.exists_sub_sub_d_mem_range_of_moduleCatKerHomologyClass_eq
    _ (CochainComplex.next ℤ n) (CochainComplex.prev ℤ n) c' c hc'₃ hc.1 (by
      rw [← homologyMap_cokernelMap_moduleCatKerHomologyClass G _ _ u (𝟙 _)
        (map_comp_map_eq G _ _ _ _) n c' hc'₁ hc'₃, hc'₂, hξ, hc.2])
  have h₁ : ((cokernel (G.map f')).d n (n + 1))
      ((cokernel.π (G.map f')).f n (c' - (G.obj a).d (n - 1) n e)) = 0 := by
    rw [HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff, map_sub,
      HomologicalComplex.d_comp_d_apply, sub_zero]
    exact (HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1) c').1 hc'₁
  exact ⟨c' - (G.obj a).d (n - 1) n e,
    ⟨h₁, by rw [HomologicalComplex.moduleCatKerHomologyClass_cokernel_π_sub_d _
      (CochainComplex.next ℤ n) (CochainComplex.prev ℤ n) c' e h₁ hc'₁, hc'₂]⟩,
    by rwa [sub_right_comm]⟩

/-- The form of `CochainComplex.exists_spectralObject_H_map_eq_of_isCompleteFiltration` for the
cohomology of the quotients `G_a / G_s`. The proof is by successive approximation: the
representatives in `G_a` of the classes are corrected step by step so that consecutive ones agree
modulo deeper and deeper stages, and their limit is a cocycle of `G_a` representing all of them. -/
private theorem exists_homologyMap_cokernelMap_eq {a n : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom)
    (hs : ∀ y : (G.obj a).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f (n + 1)).hom) →
        y = 0)
    (ξ : ∀ (s : ℤ) (hs : s ≤ a),
      (cokernel (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).homology n)
    (hξ : ∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ a) (u : (s : EInt) ⟶ s') (v : (a : EInt) ⟶ a) w,
      HomologicalComplex.homologyMap (cokernel.map
        (G.map (homOfLE (WithBotTop.coe_le_coe.2 (h.trans h'))))
        (G.map (homOfLE (WithBotTop.coe_le_coe.2 h'))) (G.map u) (G.map v) w) n
          (ξ s (h.trans h')) = ξ s' h') :
    ∃ y : (cokernel (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).homology n,
      ∀ (s : ℤ) (hs : s ≤ a) (u : (⊥ : EInt) ⟶ s) (v : (a : EInt) ⟶ a) w,
        HomologicalComplex.homologyMap (cokernel.map (G.map (homOfLE bot_le))
          (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs))) (G.map u) (G.map v) w) n y =
          ξ s hs := by
  -- `Rep k c`: the cochain `c` of `G_a` represents `ξ (a - k)` modulo `G_{a-k}`.
  let Rep (k : ℕ) (c : (G.obj a).X n) : Prop :=
    IsCokernelRep G (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))
      (ξ (a - k) (by omega)) c
  have step (k : ℕ) (c) (hc : Rep k c) : ∃ c', Rep (k + 1) c' ∧ c' - c ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom :=
    exists_isCokernelRep_sub_mem_range G _ _
      (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - (k + 1 : ℕ) ≤ a - k))) _ _
      (hξ _ _ (by omega) _ _ _ _) c hc
  obtain ⟨c₀, hc₀⟩ := exists_isCokernelRep G _ (ξ (a - (0 : ℕ)) (by omega))
  -- The successive representatives, and their limit `L` in `G_a`.
  choose next hnext using step
  obtain ⟨seq, -, hseqs⟩ : ∃ seq : (k : ℕ) → {c // Rep k c}, (seq 0).1 = c₀ ∧
      ∀ k, (seq (k + 1)).1 = next k (seq k).1 (seq k).2 :=
    ⟨fun k ↦ Nat.rec ⟨c₀, hc₀⟩ (fun k c ↦ ⟨next k c.1 c.2, (hnext k c.1 c.2).1⟩) k, rfl,
      fun _ ↦ rfl⟩
  obtain ⟨L, hL⟩ := hc.exists_limit (fun k ↦ (seq k).1) fun k ↦ by
    rw [hseqs]
    exact (hnext k _ _).2
  -- `L` is a cocycle: its boundary lies in every `G_{a-k}`.
  have hdL : (G.obj a).d n (n + 1) L = 0 := hs _ fun k ↦ by
    rw [← sub_add_cancel L (seq k).1, map_add]
    refine add_mem ?_
      ((HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1) _).1 (seq k).2.1)
    obtain ⟨z, hz⟩ := hL k
    exact ⟨(G.obj _).d n (n + 1) z, by rw [← HomologicalComplex.Hom.comm_apply, hz]⟩
  have hL₀ : ((cokernel (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).d n (n + 1))
      ((cokernel.π (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).f n L) = 0 := by
    rw [HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff, hdL]
    exact zero_mem _
  refine ⟨HomologicalComplex.moduleCatKerHomologyClass _ (CochainComplex.next ℤ n) ⟨_, hL₀⟩,
    fun s hs u v w ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = a - k := ⟨(a - s).toNat, by omega⟩
  -- Modulo `G_{a-k}`, `L` and the `k`th representative agree.
  have hLk : (cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n L =
      (cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n (seq k).1 := by
    rw [← sub_eq_zero, ← map_sub, HomologicalComplex.cokernel_π_f_apply_eq_zero_iff]
    exact hL k
  have hLk' : ((cokernel (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).d n (n + 1))
      ((cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n L) = 0 := by
    rw [hLk]
    exact (seq k).2.1
  rw [homologyMap_cokernelMap_moduleCatKerHomologyClass G _ _ u v w n L hL₀ hLk', ← (seq k).2.2]
  congr 2

variable [∀ {a b : EInt} (f : a ⟶ b), Mono (G.map f)]

/-- **Compatible classes of the quotients of a complete filtration lift.** Let `G` have monomorphic
transition maps, and suppose that the stages `G_{a-k}` cut out a complete filtration of `G_a^n` and
a separated filtration of `G_a^{n+1}`. Then a family of classes `x s ∈ H^n(s ≤ a)`, `s ≤ a`, of the
quotients `G_a / G_s`, compatible under the maps `H^n(s ≤ a) ⟶ H^n(s' ≤ a)`, is the image of a
single class of `H^n(⊥ ≤ a)`. This is the surjectivity of `H^n(lim) ⟶ lim H^n` for the tower of
quotients of `G_a`, whose limit is `G_a` by completeness. -/
theorem exists_spectralObject_H_map_eq_of_isCompleteFiltration {a n : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom)
    (hs : ∀ y : (G.obj a).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f (n + 1)).hom) →
        y = 0)
    (x : ∀ (s : ℤ) (hs : s ≤ a),
      ((spectralObject G).H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 hs))))
    (hx : ∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ a),
      ((spectralObject G).H n).map (twoδ₁Toδ₀' (s : EInt) (s' : EInt) (a : EInt)
        (WithBotTop.coe_le_coe.2 h) (WithBotTop.coe_le_coe.2 h')) (x s (h.trans h')) = x s' h') :
    ∃ y : ((spectralObject G).H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a))),
      ∀ (s : ℤ) (hs : s ≤ a), ((spectralObject G).H n).map (twoδ₁Toδ₀' ⊥ (s : EInt) (a : EInt)
        bot_le (WithBotTop.coe_le_coe.2 hs)) y = x s hs := by
  obtain ⟨y, hy⟩ := exists_homologyMap_cokernelMap_eq G hc hs
    (fun s hs ↦ (spectralObjectHIsoCokernel G _ n).hom (x s hs)) fun s s' h h' u v w ↦ by
      obtain rfl : u = homOfLE (WithBotTop.coe_le_coe.2 h) := Subsingleton.elim _ _
      obtain rfl : v = 𝟙 _ := Subsingleton.elim _ _
      rw [← hx s s' h h', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom]
      rfl
  refine ⟨(spectralObjectHIsoCokernel G _ n).inv y, fun s hs ↦
    (ModuleCat.mono_iff_injective (spectralObjectHIsoCokernel G _ n).hom).1 inferInstance ?_⟩
  rw [← hy s hs (homOfLE bot_le) (𝟙 _) (map_comp_map_eq G _ _ _ _), ← ConcreteCategory.comp_apply,
    spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply]
  rfl

/-- **Permanent cycles of a regular spectral sequence of a complete filtration.** Suppose that the
stages `G_{q+1-k}` cut out a complete filtration of `G_{q+1}^n` and a separated filtration of
`G_{q+1}^{n+1}`, and that the spectral sequence is regular in total degree `n` at the position `q`
from `i₀` on and at every position `t < q`. Then for `i ≤ i₀`, every class of `H^n(q ≤ q + 1)`
coming from `H^n(i ≤ q + 1)` comes from `H^n(⊥ ≤ q + 1)`: the cycles of the object at
`(n - q, q)` on the pages `r ≥ q - i₀ + 2` are permanent cycles. -/
theorem exists_spectralObject_H_map_eq_of_isRegularAt {q n i₀ : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f n).hom)
    (hs : ∀ y : (G.obj ((q + 1 : ℤ) : EInt)).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f
        (n + 1)).hom) → y = 0)
    (hq : (spectralObject G).IsRegularAt n q i₀)
    (hreg : ∀ t < q, ∃ i₁, (spectralObject G).IsRegularAt n t i₁)
    (i : ℤ) (hi : i ≤ i₀)
    (w : ((spectralObject G).H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2
      (by have := hq.le; omega : i ≤ q + 1))))) :
    ∃ y : ((spectralObject G).H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))),
      ((spectralObject G).H n).map (twoδ₁Toδ₀' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (by omega))) y =
      ((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
        (WithBotTop.coe_le_coe.2 (by have := hq.le; omega))
        (WithBotTop.coe_le_coe.2 (by omega))) w := by
  have hi₀ := hq.le
  -- The tower `s ↦ H^n(s ≤ q + 1)` is Mittag-Leffler.
  have hml (s : ℤ) (hs : s ≤ q) := (spectralObject G).exists_range_le_range_of_isRegularAt hs
    fun t _ ht ↦ (eq_or_lt_of_le ht).elim (fun h ↦ h ▸ ⟨i₀, hq⟩) (hreg t)
  obtain ⟨x, hx, hxq⟩ := (spectralObject G).exists_compatible_family_of_forall_mem_range hml
    (((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))) w)
    fun i' hi' ↦ by
      rcases le_or_gt i i' with hii' | hii'
      · exact ⟨((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (i' : EInt)
          ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hii') (WithBotTop.coe_le_coe.2 (by omega)))
          w, (spectralObject G).H_map_map_apply _ _ _ w⟩
      · exact hq.range_le rfl i' (by omega) ⟨((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt)
          (i₀ : EInt) ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hi)
          (WithBotTop.coe_le_coe.2 (by omega))) w, (spectralObject G).H_map_map_apply _ _ _ w⟩
  obtain ⟨y, hy⟩ := exists_spectralObject_H_map_eq_of_isCompleteFiltration G hc hs x hx
  exact ⟨y, (hy q (by omega)).trans hxq⟩

/-- **The late pages of a regular spectral sequence of a complete filtration.** Under the
hypotheses of `CochainComplex.exists_spectralObject_H_map_eq_of_isRegularAt`, for `i ≤ i₀` and
`q + 1 ≤ j` the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ j) ⟶ E^n(i ≤ q ≤ q + 1 ≤ j)` is an isomorphism.
For `i = q - r + 2` and `j = q + r - 1`, its target is the object at `(n - q, q)` on page `r`. -/
theorem isIso_mapFourδ₁Toδ₀'_of_isRegularAt {q n i₀ : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f n).hom)
    (hs : ∀ y : (G.obj ((q + 1 : ℤ) : EInt)).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f
        (n + 1)).hom) → y = 0)
    (hq : (spectralObject G).IsRegularAt n q i₀)
    (hreg : ∀ t < q, ∃ i₁, (spectralObject G).IsRegularAt n t i₁)
    (i : ℤ) (hi : i ≤ i₀) (j : EInt) (hj : ((q + 1 : ℤ) : EInt) ≤ j) :
    IsIso ((spectralObject G).mapFourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj
      (n - 1) n (n + 1)) := by
  have hi₀ := hq.le
  have := (spectralObject G).mono_map (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (fourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj) (n - 1) n
      (n + 1)
  refine (isIso_iff_mono_and_epi _).2 ⟨this, (ModuleCat.epi_iff_surjective _).2 fun e ↦ ?_⟩
  -- Write `e` through a representative `w ∈ H^n(i ≤ q + 1)`, and lift it to `H^n(⊥ ≤ q + 1)`.
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective ((spectralObject G).toE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q + 1))) rfl (n - 1) n (n + 1))).1
    inferInstance e
  obtain ⟨y, hy⟩ := exists_spectralObject_H_map_eq_of_isRegularAt G hc hs hq hreg i hi w
  refine ⟨(spectralObject G).toE (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE bot_le) rfl (n - 1) n (n + 1) (by omega) (by omega) y, ?_⟩
  -- Compare the two elements through their images in `H^n(q ≤ j)`.
  apply (ModuleCat.mono_iff_injective ((spectralObject G).fromE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE ((WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1)).trans hj)) rfl
    (n - 1) n (n + 1))).1 inferInstance
  -- The arrows `q ≤ q + 1 ≤ j` and `q ≤ j`, shared by both objects.
  let f₂ := homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))
  let f₂₃ := homOfLE ((WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1)).trans hj)
  have h₁ := ConcreteCategory.congr_hom ((spectralObject G).map_fromE
    (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj) f₂₃ rfl
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q))) f₂ (homOfLE hj) f₂₃ rfl
    (fourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj) (n - 1) n
      (n + 1) (𝟙 _) (by cat_disch) (by cat_disch) (by omega) (by omega))
    ((spectralObject G).toE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj)
      (homOfLE bot_le) rfl (n - 1) n (n + 1) (by omega) (by omega) y)
  have h₂ := ConcreteCategory.congr_hom ((spectralObject G).toE_fromE
    (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj) (homOfLE bot_le) rfl f₂₃ rfl
    (n - 1) n (n + 1) (by omega) (by omega)) y
  have h₃ := ConcreteCategory.congr_hom ((spectralObject G).toE_fromE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q))) f₂ (homOfLE hj)
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q + 1))) rfl f₂₃ rfl
    (n - 1) n (n + 1) (by omega) (by omega)) w
  simp only [ConcreteCategory.comp_apply, CategoryTheory.Functor.map_id, ModuleCat.id_apply]
    at h₁ h₂ h₃
  rw [h₁, h₂, h₃, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  exact congrArg _ hy

end Functor

section Filtration

variable {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- Completeness of the stages `F_{a-k}` in `K^m` is completeness of their images in `G_a^m`. -/
lemma isCompleteFiltration_range_filtrationFunctor_map_f {a m : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m).hom) :
    TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      (((filtrationFunctor F hF).map (homOfLE (WithBotTop.coe_le_coe.2
        (by omega : a - k ≤ a)))).f m).hom := by
  convert hc.comap ((filtrationFunctorArrow F hF a).f m).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance) ?_ using 1
  · funext k
    ext y
    exact mem_range_filtrationFunctor_map_f_iff F hF _ y
  · rintro _ ⟨u, rfl⟩
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF a).symm).f m
      ((Subobject.ofLE _ _ (hF (by omega : a - ((0 : ℕ) : ℤ) ≤ a))).f m u), ?_⟩
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      eqToHom_comp_filtrationFunctorArrow, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]

/-- Separatedness of the filtration of `K^m` gives separatedness of the stages `G_{a-k}` in
`G_a^m`. -/
lemma eq_zero_of_forall_mem_range_filtrationFunctor_map_f {a m : ℤ}
    (hs : ∀ x : K.X m, (∀ i, x ∈ LinearMap.range ((F i).arrow.f m).hom) → x = 0)
    (y : ((filtrationFunctor F hF).obj (a : EInt)).X m)
    (hy : ∀ k : ℕ, y ∈ LinearMap.range (((filtrationFunctor F hF).map
      (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f m).hom) :
    y = 0 := by
  apply (ModuleCat.mono_iff_injective ((filtrationFunctorArrow F hF a).f m)).1 inferInstance
  rw [map_zero]
  refine hs _ fun i ↦ Subobject.range_arrow_f_hom_le (hF (by omega : a - (a - i).toNat ≤ i)) m
    ((mem_range_filtrationFunctor_map_f_iff F hF _ y).1 (hy (a - i).toNat))

section Pages

variable (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) {i₀ : ℤ}
  (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
    LinearMap.range ((F (pq.2 + 1 - k)).arrow.f (pq.1 + pq.2)).hom)
  (hs : ∀ x : K.X (pq.1 + pq.2 + 1),
    (∀ i, x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 + 1)).hom) → x = 0)
  (hq : (spectralObject (filtrationFunctor F hF)).IsRegularAt (pq.1 + pq.2) pq.2 i₀)
  (hreg : ∀ t < pq.2,
    ∃ i₁, (spectralObject (filtrationFunctor F hF)).IsRegularAt (pq.1 + pq.2) t i₁)
  (hri : pq.2 - r + 2 ≤ i₀)

/-- **The late pages of the regular spectral sequence of a complete filtration.** Let
`pq = (p, q)` and `n = p + q`. Suppose that the stages `F_{q+1-k}` form a complete filtration of
`K^n`, that the filtration of `K^{n+1}` is separated, and that the spectral sequence is regular in
total degree `n` at the position `q` from `i₀` on and at every position `t < q`. Then on every
page `r ≥ 2` with `q - r + 2 ≤ i₀`, the object at `(p, q)` is `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`. -/
noncomputable def filtrationSpectralSequencePageXIsoEBotOfRegular :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      (spectralObject (filtrationFunctor F hF)).E (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (WithBotTop.coe_le_coe.2 (by omega : pq.2 + 1 ≤ pq.2 + r - 1)))
        (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) (by omega) (by omega) :=
  have := isIso_mapFourδ₁Toδ₀'_of_isRegularAt (filtrationFunctor F hF)
    (isCompleteFiltration_range_filtrationFunctor_map_f F hF hc)
    (eq_zero_of_forall_mem_range_filtrationFunctor_map_f F hF hs) hq hreg (pq.2 - r + 2) hri
    ((pq.2 + r - 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
  (spectralObject _).spectralSequencePageXIso coreE₂Cohomological r hr pq
      ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) (by omega) ≪≫
    (asIso ((spectralObject _).mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (coe_le_coe_add_one pq.2)
      (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)
      _ _)).symm

/-- The inverse of `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular` is the canonical
map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` followed by the
identification of the latter with the page object. -/
lemma filtrationSpectralSequencePageXIsoEBotOfRegular_inv :
    (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).inv =
      (spectralObject _).mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2
          ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) bot_le
          (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (coe_le_coe_add_one pq.2)
          (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)
          (by omega) (by omega) ≫
        ((spectralObject _).spectralSequencePageXIso coreE₂Cohomological r hr pq
          ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
          rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega)
          (by omega)).inv :=
  (rfl)

/-- **The late pages map onto the graded pieces.** Under the hypotheses of
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`, the epimorphism from the object
at `(p, q)` on page `r` onto the graded piece `F_{q+1} H^n / F_q H^n` of the filtration of
`H^n(K)`, `n = p + q`, through `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
noncomputable def filtrationSpectralSequencePageXToGradedOfRegular :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ⟶
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom ≫
    (spectralObject _).mapFourδ₄Toδ₃' ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + r - 1 : ℤ) : EInt) ⊤
      bot_le (coe_le_coe_add_one pq.2) (WithBotTop.coe_le_coe.2 (by omega)) le_top
      (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) _ _ ≫
    ((spectralObject _).EInftyIsoCokernel _ _).hom

/-- `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular` is
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular` followed by the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` and the identification of the latter
with the graded piece. -/
lemma filtrationSpectralSequencePageXToGradedOfRegular_def :
    filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri =
      (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom ≫
        (spectralObject _).mapFourδ₄Toδ₃' ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
          ((pq.2 + r - 1 : ℤ) : EInt) ⊤ bot_le (coe_le_coe_add_one pq.2)
          (WithBotTop.coe_le_coe.2 (by omega)) le_top (pq.1 + pq.2 - 1) (pq.1 + pq.2)
          (pq.1 + pq.2 + 1) (by omega) (by omega) ≫
        ((spectralObject _).EInftyIsoCokernel _ _).hom :=
  (rfl)

instance :
    Epi (filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri) := by
  rw [filtrationSpectralSequencePageXToGradedOfRegular_def]
  infer_instance

/-- **Weak convergence of the regular spectral sequence of a complete exhaustive filtration**
(Weibel, Theorem 5.5.10). Under the hypotheses of
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`, suppose also that every element
of `K^{n-1}` lies in some `F_i`, `n = p + q`. Then an element of the object at `(p, q)` on page `r`
vanishes in the graded piece `F_{q+1} H^n / F_q H^n` exactly when it vanishes on some later page
`r'`, under the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)`
read through `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`. With the surjectivity
of `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`, the graded piece is the direct
limit of the objects at `(p, q)` on the late pages. -/
theorem filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (x : ((spectralSequence (filtrationFunctor F hF)).page r).X pq) :
    filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri x = 0 ↔
      ∃ (r' : ℤ) (hrr' : r ≤ r'),
        (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r' (hr.trans hrr') pq hc hs hq hreg
          (by omega)).inv ((spectralObject (filtrationFunctor F hF)).mapFourδ₄Toδ₃' ⊥
            (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
            ((pq.2 + r - 1 : ℤ) : EInt) ((pq.2 + r' - 1 : ℤ) : EInt) bot_le
            (coe_le_coe_add_one pq.2) (WithBotTop.coe_le_coe.2 (by omega))
            (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2)
            (pq.1 + pq.2 + 1) _ _
            ((filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom
              x)) = 0 := by
  set x' := (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom x
  rw [filtrationSpectralSequencePageXToGradedOfRegular_def, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, (ModuleCat.mono_iff_injective
      ((spectralObject (filtrationFunctor F hF)).EInftyIsoCokernel _ _).hom).1 inferInstance
      |>.eq_iff' (map_zero _)]
  constructor
  · intro h
    obtain ⟨j', hj', h'⟩ := exists_mapFourδ₄Toδ₃'_eq_zero (filtrationFunctor F hF) (q := pq.2)
      (j := pq.2 + r - 1) (n := pq.1 + pq.2) (by omega) (exists_filtrationFunctor_map_f_eq F hF hex)
      x' h
    obtain ⟨r', rfl⟩ : ∃ r', j' = pq.2 + r' - 1 := ⟨j' - pq.2 + 1, by ring⟩
    exact ⟨r', by omega, by rw [h', map_zero]⟩
  · rintro ⟨r', hrr', h⟩
    rw [(ModuleCat.mono_iff_injective (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r'
      (hr.trans hrr') pq hc hs hq hreg (by omega)).inv).1 inferInstance |>.eq_iff' (map_zero _)]
      at h
    have := ConcreteCategory.congr_hom
      ((spectralObject (filtrationFunctor F hF)).mapFourδ₄Toδ₃'_comp
      ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
      ((pq.2 + r' - 1 : ℤ) : EInt) ⊤ bot_le (coe_le_coe_add_one pq.2)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) le_top
      (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)) x'
    rw [ConcreteCategory.comp_apply, h, map_zero] at this
    exact this.symm

end Pages

end Filtration

end CochainComplex
