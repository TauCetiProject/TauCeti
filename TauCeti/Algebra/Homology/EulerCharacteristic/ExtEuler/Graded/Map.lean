/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Sesquilinear

/-!
# Naturality of the q-Euler form under graded exact functors

Let `C` and `D` be `k`-linear abelian categories with grading shifts `e` and `e'`, and let
`F : C ⥤ D` be an exact `k`-linear functor together with an isomorphism
`σ : e ⋙ F ≅ F ⋙ e'` commuting it with the shifts. Then `F` commutes with every internal shift,
`F(Y{j}) ≅ (F Y){j}` (`CategoryTheory.Equivalence.powCommIso`), so it induces `k`-linear maps of
bigraded `Ext` groups (`CategoryTheory.Functor.mapGradedExtLinearMap`)

```text
Ext^{n,j}(X, Y) = Extⁿ(X, Y{j}) ⟶ Extⁿ(F X, F(Y{j})) ≅ Extⁿ(F X, (F Y){j}) = Ext^{n,j}(F X, F Y).
```

The first map is Mathlib's `CategoryTheory.Functor.mapExtAddHom`, and the hypotheses below are
stated in terms of it alone; `σ` only identifies its target. This file proves that the two
finiteness conditions behind the q-Euler characteristic are carried along `F`, respectively
reflected by it, under surjectivity, respectively injectivity, of these maps, and that when they
are bijective

```text
χ_q(F X, F Y) = χ_q(X, Y).
```

At the level of graded Grothendieck groups, if `F` carries the extension-closed, shift-stable
properties `P` and `Q` of `C` into such properties `P'` and `Q'` of `D`, its restrictions induce
`ℤ[q,q⁻¹]`-linear maps of graded `K₀`. If moreover `F` is bijective on the bigraded `Ext` groups
of every pair of objects in `P × Q`, these maps intertwine the two q-Euler forms
(`TauCeti.gradedExtEulerSesquilinear_map_map`). This is the graded counterpart of
`TauCeti.extEulerPairing_map_map`.

The bijectivity hypothesis holds for the forward functor of an additive equivalence
(`CategoryTheory.Equivalence.mapExtAddHom_bijective`), so the q-Euler characteristic is invariant
under shift-compatible equivalences (`TauCeti.gradedExtEuler_map_equivalence`). For a fully
faithful exact functor out of a category with enough projectives which preserves projective
objects it is Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects`.

## Main results

* `CategoryTheory.Functor.mapGradedExtLinearMap`: the map `Ext^{n,j}(X, Y) → Ext^{n,j}(F X, F Y)`,
  injective, respectively surjective, exactly when `F.mapExtAddHom` is
  (`CategoryTheory.Functor.mapGradedExtLinearMap_injective_iff`,
  `CategoryTheory.Functor.mapGradedExtLinearMap_surjective_iff`).
* `TauCeti.IsGradedEulerAdmissible.map` and `TauCeti.IsGradedEulerAdmissible.of_map`: graded
  Euler-admissibility is carried along `F`, respectively reflected by it, under surjectivity,
  respectively injectivity, of the maps on `Ext`; `TauCeti.IsGradedEulerAdmissibleOn.of_map` is the
  version for object properties.
* `TauCeti.gradedExtEuler_map`: `χ_q(F X, F Y) = χ_q(X, Y)` when `F` is bijective on `Ext`.
* `TauCeti.gradedExtEuler_map_equivalence`: the same for a shift-compatible equivalence, with no
  further hypothesis.
* `TauCeti.gradedExtEulerSesquilinear_map_map`: the maps of graded `K₀` induced by a graded
  exact functor which is bijective on the bigraded `Ext` groups of every pair in `P × Q`
  intertwine the q-Euler forms.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for the bigraded Ext-Euler form.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for `Ext`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w' v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {k : Type t} [Field k] [Linear k C] [Linear k D] [HasExt.{w} C] [HasExt.{w'} D]
  {e : C ≌ C} {e' : D ≌ D}
  (F : C ⥤ D) [F.Additive] [F.Linear k] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (σ : e.functor ⋙ F ≅ F ⋙ e'.functor) {X Y : C}

variable (k) in
/-- **The map of bigraded `Ext` induced by a shift-compatible exact functor.** The `k`-linear map
`Ext^{n,j}(X, Y) → Ext^{n,j}(F X, F Y)`: apply `F`, then identify `F(Y{j})` with `(F Y){j}`
through the powers of `σ`. -/
noncomputable def _root_.CategoryTheory.Functor.mapGradedExtLinearMap (X Y : C) (n : ℕ) (j : ℤ) :
    GradedExt.{w} e X Y n j →ₗ[k] GradedExt.{w'} e' (F.obj X) (F.obj Y) n j :=
  (extLinearEquivOfIso k (Iso.refl _) ((e.powCommIso σ j).app Y) n).toLinearMap ∘ₗ
    F.mapExtLinearMap k X ((e ^ j).functor.obj Y) n

/-- `F.mapGradedExtLinearMap k σ` applies `F` to a class, then composes with the component at `Y`
of the `j`-th power of `σ`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapGradedExtLinearMap_apply (n : ℕ) (j : ℤ)
    (α : GradedExt.{w} e X Y n j) :
    F.mapGradedExtLinearMap k σ X Y n j α =
      extAddEquivOfIso (Iso.refl _) ((e.powCommIso σ j).app Y) n (α.mapExactFunctor F) := by
  simp [Functor.mapGradedExtLinearMap, extLinearEquivOfIso_apply, Functor.mapExtLinearMap_apply]

/-- The additive identification `Extⁿ(F X, F(Y{j})) ≃ Ext^{n,j}(F X, F Y)` through the powers of
`σ`. -/
private noncomputable def shiftCommExtEquiv (X Y : C) (n : ℕ) (j : ℤ) :
    Ext.{w'} (F.obj X) (F.obj ((e ^ j).functor.obj Y)) n ≃+
      GradedExt.{w'} e' (F.obj X) (F.obj Y) n j :=
  extAddEquivOfIso (Iso.refl _) ((e.powCommIso σ j).app Y) n

/-- `F.mapGradedExtLinearMap k σ` is `F.mapExtAddHom` followed by the identification
`shiftCommExtEquiv`. -/
private theorem coe_mapGradedExtLinearMap (n : ℕ) (j : ℤ) :
    ⇑(F.mapGradedExtLinearMap k σ X Y n j) =
      shiftCommExtEquiv F σ X Y n j ∘ F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n := by
  ext
  simp [shiftCommExtEquiv]

/-- The map of bigraded `Ext` induced by `F` is injective exactly when `F` is injective on the
underlying `Ext` group. -/
theorem _root_.CategoryTheory.Functor.mapGradedExtLinearMap_injective_iff {n : ℕ} {j : ℤ} :
    Function.Injective (F.mapGradedExtLinearMap k σ X Y n j) ↔
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n) := by
  rw [coe_mapGradedExtLinearMap]
  exact EquivLike.comp_injective _ _

/-- The map of bigraded `Ext` induced by `F` is surjective exactly when `F` is surjective on the
underlying `Ext` group. -/
theorem _root_.CategoryTheory.Functor.mapGradedExtLinearMap_surjective_iff {n : ℕ} {j : ℤ} :
    Function.Surjective (F.mapGradedExtLinearMap k σ X Y n j) ↔
      Function.Surjective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n) := by
  rw [coe_mapGradedExtLinearMap]
  exact EquivLike.comp_surjective _ _

/-! ### Transporting the finiteness conditions -/

section Admissible

include σ

/-- Finite internal support of bigraded `Ext` is reflected by a shift-compatible exact functor
which is injective on `Ext`. -/
theorem IsGradedExtInternallyFinite.of_map
    (h : IsGradedExtInternallyFinite.{w'} k e' (F.obj X) (F.obj Y))
    (hF : ∀ n (j : ℤ),
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtInternallyFinite.{w} k e X Y :=
  ⟨fun n ↦ (h.finiteLaurentSupport n).of_injective (F.mapGradedExtLinearMap k σ X Y n)
    fun j ↦ (F.mapGradedExtLinearMap_injective_iff σ).2 (hF n j)⟩

/-- Finite internal support of bigraded `Ext` is carried along a shift-compatible exact functor
which is surjective on `Ext`. -/
theorem IsGradedExtInternallyFinite.map (h : IsGradedExtInternallyFinite.{w} k e X Y)
    (hF : ∀ n (j : ℤ),
      Function.Surjective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtInternallyFinite.{w'} k e' (F.obj X) (F.obj Y) :=
  ⟨fun n ↦ (h.finiteLaurentSupport n).of_surjective (F.mapGradedExtLinearMap k σ X Y n)
    fun j ↦ (F.mapGradedExtLinearMap_surjective_iff σ).2 (hF n j)⟩

/-- A cohomological vanishing bound for bigraded `Ext` is reflected by a shift-compatible exact
functor which is injective on `Ext` from that degree on. -/
theorem IsGradedExtBoundedBy.of_map {N : ℕ}
    (h : IsGradedExtBoundedBy.{w'} e' (F.obj X) (F.obj Y) N)
    (hF : ∀ ⦃n⦄, N ≤ n → ∀ j : ℤ,
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtBoundedBy.{w} e X Y N :=
  ⟨fun n hn j ↦ haveI := h.subsingleton hn j
    haveI := (shiftCommExtEquiv F σ X Y n j).toEquiv.subsingleton
    (hF hn j).subsingleton⟩

/-- A cohomological vanishing bound for bigraded `Ext` is carried along a shift-compatible exact
functor which is surjective on `Ext` from that degree on. -/
theorem IsGradedExtBoundedBy.map {N : ℕ} (h : IsGradedExtBoundedBy.{w} e X Y N)
    (hF : ∀ ⦃n⦄, N ≤ n → ∀ j : ℤ,
      Function.Surjective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtBoundedBy.{w'} e' (F.obj X) (F.obj Y) N :=
  ⟨fun n hn j ↦ haveI := h.subsingleton hn j
    haveI := (hF hn j).subsingleton
    (shiftCommExtEquiv F σ X Y n j).symm.toEquiv.subsingleton⟩

/-- Eventual vanishing of bigraded `Ext` is reflected by a shift-compatible exact functor which
is injective on `Ext` in all large cohomological degrees. -/
theorem IsGradedExtBounded.of_map (h : IsGradedExtBounded.{w'} e' (F.obj X) (F.obj Y))
    (hF : ∀ᶠ n in Filter.atTop, ∀ j : ℤ,
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtBounded.{w} e X Y := by
  obtain ⟨N, hN⟩ := h.exists_bound
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hF
  exact ((hN.mono (le_max_left N M)).of_map F σ fun n hn ↦
    hM n ((le_max_right N M).trans hn)).isGradedExtBounded

/-- Eventual vanishing of bigraded `Ext` is carried along a shift-compatible exact functor which
is surjective on `Ext` in all large cohomological degrees. -/
theorem IsGradedExtBounded.map (h : IsGradedExtBounded.{w} e X Y)
    (hF : ∀ᶠ n in Filter.atTop, ∀ j : ℤ,
      Function.Surjective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedExtBounded.{w'} e' (F.obj X) (F.obj Y) := by
  obtain ⟨N, hN⟩ := h.exists_bound
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hF
  exact ((hN.mono (le_max_left N M)).map F σ fun n hn ↦
    hM n ((le_max_right N M).trans hn)).isGradedExtBounded

/-- Graded Euler-admissibility is reflected by a shift-compatible exact functor which is injective
on `Ext`. -/
theorem IsGradedEulerAdmissible.of_map
    (h : IsGradedEulerAdmissible.{w'} k e' (F.obj X) (F.obj Y))
    (hF : ∀ n (j : ℤ),
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedEulerAdmissible.{w} k e X Y :=
  ⟨h.internallyFinite.of_map F σ hF, h.bounded.of_map F σ (.of_forall hF)⟩

/-- Graded Euler-admissibility is carried along a shift-compatible exact functor which is
surjective on `Ext`. -/
theorem IsGradedEulerAdmissible.map (h : IsGradedEulerAdmissible.{w} k e X Y)
    (hF : ∀ n (j : ℤ),
      Function.Surjective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedEulerAdmissible.{w'} k e' (F.obj X) (F.obj Y) :=
  ⟨h.internallyFinite.map F σ hF, h.bounded.map F σ (.of_forall hF)⟩

/-- Graded Euler-admissibility on a pair of object properties is reflected by a shift-compatible
exact functor carrying them into graded Euler-admissible properties and injective on the `Ext`
groups between them. -/
theorem IsGradedEulerAdmissibleOn.of_map {P Q : ObjectProperty C} {P' Q' : ObjectProperty D}
    (h : IsGradedEulerAdmissibleOn.{w'} (k := k) (e := e') P' Q')
    (hFP : ∀ ⦃X⦄, P X → P' (F.obj X)) (hFQ : ∀ ⦃Y⦄, Q Y → Q' (F.obj Y))
    (hF : ∀ ⦃X Y⦄, P X → Q Y → ∀ n (j : ℤ),
      Function.Injective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n)) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q :=
  ⟨fun _ _ hX hY ↦ (h.isGradedEulerAdmissible (hFP hX) (hFQ hY)).of_map F σ (hF hX hY)⟩

end Admissible

/-! ### Naturality of the q-Euler characteristic -/

/-- **Naturality of the q-Euler characteristic**: a shift-compatible exact functor which is
bijective on `Ext` preserves it, `χ_q(F X, F Y) = χ_q(X, Y)`. -/
theorem gradedExtEuler_map
    (hF : ∀ n (j : ℤ),
      Function.Bijective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n))
    (h : IsGradedEulerAdmissible.{w} k e X Y) :
    gradedExtEuler k e' (h.map F σ fun n j ↦ (hF n j).2) = gradedExtEuler k e h :=
  gradedExtEuler_congr k (fun n j ↦ LinearEquiv.ofBijective (F.mapGradedExtLinearMap k σ X Y n j)
    ⟨(F.mapGradedExtLinearMap_injective_iff σ).2 (hF n j).1,
      (F.mapGradedExtLinearMap_surjective_iff σ).2 (hF n j).2⟩) h

omit [F.Additive] [F.Linear k] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- **Invariance of the q-Euler characteristic under graded equivalences**: a `k`-linear
equivalence commuting with the grading shifts preserves it, `χ_q(G X, G Y) = χ_q(X, Y)`. -/
theorem gradedExtEuler_map_equivalence (G : C ≌ D) [G.functor.Additive]
    [G.functor.Linear k] (σ : e.functor ⋙ G.functor ≅ G.functor ⋙ e'.functor)
    (h : IsGradedEulerAdmissible.{w} k e X Y) :
    gradedExtEuler k e'
        (h.map G.functor σ fun n _ ↦ (G.mapExtAddHom_bijective X _ n).2) =
      gradedExtEuler k e h :=
  gradedExtEuler_map G.functor σ (fun n _ ↦ G.mapExtAddHom_bijective X _ n) h

/-! ### Naturality of the q-Euler form -/

section Pairing

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]
  {P' Q' : ObjectProperty D} [LocallySmall.{w'} D]
  [ObjectProperty.EssentiallySmall.{w'} P'] [ObjectProperty.EssentiallySmall.{w'} Q']
  [P'.ContainsZero] [P'.IsClosedUnderBinaryProducts]
  [Q'.ContainsZero] [Q'.IsClosedUnderBinaryProducts]
  [e.functor.Additive] [e.functor.Linear k] [e'.functor.Additive] [e'.functor.Linear k]

/-- **Naturality of the q-Euler form.** Let the exact functor `F`, commuting with the grading
shifts through `σ`, carry the extension-closed, shift-stable properties `P` and `Q` of `C` into
such properties `P'` and `Q'` of `D`, and let `F` be bijective on the bigraded `Ext` groups of
every pair in `P × Q`. Then the `ℤ[q,q⁻¹]`-linear maps of graded `K₀` induced by the restrictions
of `F` to the full subcategories intertwine the two q-Euler forms.

The admissibility witness on `C` is obtained from `h'` by
`TauCeti.IsGradedEulerAdmissibleOn.of_map`. -/
theorem gradedExtEulerSesquilinear_map_map
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (hP' : (GradedExactStructure.abelian D e').toExactStructure.IsExtensionClosed P')
    (hQ' : (GradedExactStructure.abelian D e').toExactStructure.IsExtensionClosed Q')
    (hP'shift : P'.inverseImage (GradedExactStructure.abelian D e').shift.functor = P')
    (hQ'shift : Q'.inverseImage (GradedExactStructure.abelian D e').shift.functor = Q')
    (h' : IsGradedEulerAdmissibleOn.{w'} (k := k) (e := e') P' Q')
    (hFP : ∀ ⦃X⦄, P X → P' (F.obj X)) (hFQ : ∀ ⦃Y⦄, Q Y → Q' (F.obj Y))
    (hFext : ∀ ⦃X Y⦄, P X → Q Y → ∀ n (j : ℤ),
      Function.Bijective (F.mapExtAddHom.{w, w'} X ((e ^ j).functor.obj Y) n))
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) :
    gradedExtEulerSesquilinear hP' hQ' hP'shift hQ'shift h'
        (LaurentK0.map ((GradedConflationExact.abelian F σ).lift _ P hP hP' hPshift hP'shift
          fun X ↦ hFP X.property) x)
        (LaurentK0.map ((GradedConflationExact.abelian F σ).lift _ Q hQ hQ' hQshift hQ'shift
          fun Y ↦ hFQ Y.property) y) =
      gradedExtEulerSesquilinear hP hQ hPshift hQshift
        (h'.of_map F σ hFP hFQ fun _ _ hX hY n j ↦ (hFext hX hY n j).1) x y := by
  let h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q :=
    h'.of_map F σ hFP hFQ fun _ _ hX hY n j ↦ (hFext hX hY n j).1
  let mapP := LaurentK0.map ((GradedConflationExact.abelian F σ).lift _ P hP hP' hPshift hP'shift
    fun X ↦ hFP X.property)
  let mapQ := LaurentK0.map ((GradedConflationExact.abelian F σ).lift _ Q hQ hQ' hQshift hQ'shift
    fun Y ↦ hFQ Y.property)
  let B := ((gradedExtEulerSesquilinear hP' hQ' hP'shift hQ'shift h').comp mapP).compl₂ mapQ
  have hB : B = gradedExtEulerSesquilinear hP hQ hPshift hQshift h :=
    gradedExtEulerSesquilinear_unique hP hQ hPshift hQshift h B fun X Y ↦ by
      simp only [B, mapP, mapQ, LinearMap.compl₂_apply, LinearMap.comp_apply, LaurentK0.map_of,
        gradedExtEulerSesquilinear_of_of]
      exact gradedExtEuler_map F σ (hFext X.property Y.property)
        (h.isGradedEulerAdmissible X.property Y.property)
  exact DFunLike.congr_fun (DFunLike.congr_fun hB x) y

end Pairing

end TauCeti
