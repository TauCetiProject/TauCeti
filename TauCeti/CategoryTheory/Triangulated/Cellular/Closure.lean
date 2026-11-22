/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic
public import TauCeti.CategoryTheory.Triangulated.LocalizingClosure

/-!
# Cellular closure in pretriangulated categories with coproducts

In a pretriangulated category `T` (with morphisms in `Type v`) admitting `Type v`-indexed
coproducts, `TauCeti.InCellClosure G` is the smallest isomorphism-invariant class containing a
family `G : I → T` (`I : Type v`) closed under `Type v`-indexed coproducts and third objects (cones)
of distinguished triangles.

We establish:
1. Closure under small coproducts (`InCellClosure.coproduct_of_small`), zero objects
   (`InCellClosure.of_isZero`, `InCellClosure.zero`), nonnegative shifts
   (`InCellClosure.shift_nat`), and sequential Milnor homotopy colimits
   (`InCellClosure.of_milnorTriangle`).
2. Characterization of the empty-family closure (`inCellClosure_empty_iff`) and containment in the
   localizing closure (`inCellClosure_le_localizingClosure`).
3. Negative-shift obstructions (`hom_shift_eq_zero_of_inCellClosure`,
   `not_inCellClosure_shift_neg_one_of_hom`,
   `CategoryTheory.Functor.isZero_obj_shift_of_inCellClosure`,
   `CategoryTheory.Functor.not_inCellClosure_shift_neg_one`).

## Main definitions

* `TauCeti.InCellClosure`

## Main results

* `TauCeti.InCellClosure.induction_on`, `TauCeti.InCellClosure.shift_nat`,
  `TauCeti.InCellClosure.of_milnorTriangle`, `TauCeti.inCellClosure_empty_iff`,
  `TauCeti.inCellClosure_le_localizingClosure`
* `TauCeti.hom_shift_eq_zero_of_inCellClosure`,
  `CategoryTheory.Functor.isZero_obj_shift_of_inCellClosure`,
  `CategoryTheory.Functor.not_inCellClosure_shift_neg_one`

## References

* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Section 8.2.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4 and Lemma 5.6.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
open CategoryTheory.Pretriangulated

universe w v u

namespace TauCeti

section CellClosure

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]

/-- The cellular closure of a `Type v`-indexed family `G : I → T`: an object `R` lies in
`InCellClosure G` if it belongs to every isomorphism-invariant class containing each `G i` and
closed under `Type v`-indexed coproducts and third objects of distinguished triangles whose first
two objects belong to the class. -/
def InCellClosure {I : Type v} (G : I → T) (R : T) : Prop :=
  ∀ P : T → Prop, (∀ i, P (G i)) → (∀ {A B : T}, (A ≅ B) → P A → P B) →
    (∀ (J : Type v) (f : J → T), (∀ j, P (f j)) → P (∐ f)) →
    (∀ t : Triangle T, t ∈ distTriang T → P t.obj₁ → P t.obj₂ → P t.obj₃) → P R

variable {I : Type v} {G : I → T}

/-- Elimination / induction principle for `InCellClosure G`. -/
theorem InCellClosure.induction_on {P : T → Prop} {R : T} (hR : InCellClosure G R)
    (generator : ∀ i, P (G i)) (of_iso : ∀ {A B : T}, (A ≅ B) → P A → P B)
    (coproduct : ∀ (J : Type v) (f : J → T), (∀ j, P (f j)) → P (∐ f))
    (of_distTriang : ∀ t : Triangle T, t ∈ distTriang T → P t.obj₁ → P t.obj₂ → P t.obj₃) :
    P R := hR P generator of_iso coproduct of_distTriang

/-- Every generator lies in its own cellular closure. -/
theorem InCellClosure.generator (G : I → T) (i : I) : InCellClosure G (G i) := fun _ h _ _ _ ↦ h i

/-- Membership in `InCellClosure G` is invariant under isomorphism. -/
theorem InCellClosure.of_iso {A B : T} (e : A ≅ B) (hA : InCellClosure G A) :
    InCellClosure G B := fun P hgen hiso hcop htri ↦ hiso e (hA P hgen hiso hcop htri)

theorem inCellClosure_iff_of_iso {A B : T} (e : A ≅ B) :
    InCellClosure G A ↔ InCellClosure G B := ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- `InCellClosure G` is closed under `Type v`-indexed coproducts. -/
theorem InCellClosure.coproduct {J : Type v} (f : J → T) (hf : ∀ j, InCellClosure G (f j)) :
    InCellClosure G (∐ f) := fun P hgen hiso hcop htri ↦ hcop J f fun j ↦ hf j P hgen hiso hcop htri

/-- `InCellClosure G` is closed under coproducts indexed by any `v`-small type (such as `ℕ` or any
finite type). -/
theorem InCellClosure.coproduct_of_small {J : Type w} [Small.{v} J] (f : J → T) [HasCoproduct f]
    (hf : ∀ j, InCellClosure G (f j)) : InCellClosure G (∐ f) :=
  let e : J ≃ Shrink.{v} J := equivShrink.{v} J
  (InCellClosure.coproduct (G := G) (f ∘ e.symm) fun k ↦ hf (e.symm k)).of_iso
    (Limits.Sigma.reindex e.symm f)

/-- Every zero object lies in `InCellClosure G` (as the empty coproduct). -/
theorem InCellClosure.of_isZero (G : I → T) {Z : T} (hZ : IsZero Z) : InCellClosure G Z := by
  have h0 : IsZero (∐ (PEmpty.elim : PEmpty.{v + 1} → T)) := by
    rw [IsZero.iff_id_eq_zero]; exact Sigma.hom_ext _ _ fun j ↦ PEmpty.elim j
  exact (InCellClosure.coproduct (G := G) (PEmpty.elim : PEmpty.{v + 1} → T)
    fun j ↦ PEmpty.elim j).of_iso (h0.iso hZ)

/-- The chosen zero object lies in `InCellClosure G`. -/
theorem InCellClosure.zero (G : I → T) : InCellClosure G (0 : T) :=
  InCellClosure.of_isZero G (isZero_zero T)

/-- `InCellClosure G` is closed under taking the third object (cone) of a distinguished triangle
whose first two objects lie in `InCellClosure G`. -/
theorem InCellClosure.of_distTriang {t : Triangle T} (ht : t ∈ distTriang T)
    (h₁ : InCellClosure G t.obj₁) (h₂ : InCellClosure G t.obj₂) : InCellClosure G t.obj₃ :=
  fun P hgen hiso hcop htri ↦ htri t ht (h₁ P hgen hiso hcop htri) (h₂ P hgen hiso hcop htri)

/-- `InCellClosure G` is closed under unit positive suspension `⟦1⟧` (as the cone of
`R ⟶ 0`). -/
theorem InCellClosure.shift_one {R : T} (hR : InCellClosure G R) :
    InCellClosure G (R⟦(1 : ℤ)⟧) :=
  InCellClosure.of_distTriang (contractible_distinguished₂ R) hR (InCellClosure.zero G)

/-- `InCellClosure G` is closed under nonnegative integer shifts `⟦(n : ℤ)⟧`. -/
theorem InCellClosure.shift_nat {R : T} (hR : InCellClosure G R) :
    ∀ n : ℕ, InCellClosure G (R⟦(n : ℤ)⟧)
  | 0 => hR.of_iso ((shiftFunctorZero T ℤ).symm.app R)
  | n + 1 => by
    rw [Nat.cast_succ]
    exact (hR.shift_nat n).shift_one.of_iso ((shiftFunctorAdd T (n : ℤ) 1).symm.app R)

/-- `InCellClosure G` is closed under sequential Milnor homotopy colimits. -/
theorem InCellClosure.of_milnorTriangle {X : ℕ ⥤ T} [HasCoproduct X.obj] {M : T}
    {ψ : (∐ X.obj) ⟶ M} {δ : M ⟶ (∐ X.obj)⟦(1 : ℤ)⟧}
    (ht : Triangle.mk X.sequenceDifference ψ δ ∈ distTriang T)
    (hX : ∀ n, InCellClosure G (X.obj n)) : InCellClosure G M := by
  have hS : InCellClosure G (∐ X.obj) := InCellClosure.coproduct_of_small X.obj hX
  exact InCellClosure.of_distTriang ht hS hS

/-- Monotonicity of `InCellClosure` up to isomorphism of generators. -/
theorem InCellClosure.mono {I' : Type v} {G' : I' → T}
    (h : ∀ i, ∃ j, Nonempty (G i ≅ G' j)) {R : T} (hR : InCellClosure G R) :
    InCellClosure G' R :=
  hR.induction_on
    (fun i ↦ let ⟨j, ⟨e⟩⟩ := h i; (InCellClosure.generator G' j).of_iso e.symm)
    (fun e hA ↦ hA.of_iso e)
    (fun _ f hf ↦ InCellClosure.coproduct f hf)
    (fun _ ht h₁ h₂ ↦ InCellClosure.of_distTriang ht h₁ h₂)

/-- Inclusion of generator ranges implies inclusion of cellular closures. -/
theorem InCellClosure.of_range_subset {I' : Type v} {G' : I' → T}
    (h : Set.range G ⊆ Set.range G') {R : T} (hR : InCellClosure G R) :
    InCellClosure G' R :=
  hR.mono fun i ↦ let ⟨j, hj⟩ := h ⟨i, rfl⟩; ⟨j, ⟨eqToIso hj.symm⟩⟩

/-- Replacing generators by isomorphic objects leaves `InCellClosure` unchanged. -/
theorem inCellClosure_iff_of_iso_family {G' : I → T} (e : ∀ i, G i ≅ G' i) (R : T) :
    InCellClosure G R ↔ InCellClosure G' R :=
  ⟨fun h ↦ h.mono fun i ↦ ⟨i, ⟨e i⟩⟩, fun h ↦ h.mono fun i ↦ ⟨i, ⟨(e i).symm⟩⟩⟩

/-- The cellular closure of the empty family consists precisely of the zero objects. -/
@[simp]
theorem inCellClosure_empty_iff (R : T) :
    InCellClosure (PEmpty.elim : PEmpty.{v + 1} → T) R ↔ IsZero R := by
  refine ⟨fun hR ↦ ?_, InCellClosure.of_isZero _⟩
  refine hR.induction_on (fun i ↦ PEmpty.elim i) (fun e hA ↦ hA.of_iso e.symm)
    (fun _ f hf ↦ ?_) (fun t ht h₁ h₂ ↦ ?_)
  · rw [IsZero.iff_id_eq_zero]; exact Sigma.hom_ext _ _ fun j ↦ (hf j).eq_of_src _ _
  · have hm : t.mor₁ = (h₁.iso h₂).hom := h₁.eq_of_src _ _
    have : IsIso t.mor₁ := hm ▸ inferInstance
    exact t.isZero₃_of_isIso₁ ht inferInstance

/-- The cellular closure of `G` is contained in the localizing closure of its range. -/
theorem inCellClosure_le_localizingClosure (G : I → T) :
    InCellClosure G ≤ ObjectProperty.localizingClosure (fun X ↦ ∃ i, G i = X) := fun _ hR ↦
  hR.induction_on
    (fun i ↦ ObjectProperty.le_localizingClosure _ _ ⟨i, rfl⟩)
    (fun e hA ↦ ObjectProperty.prop_of_iso _ e hA)
    (fun _ f hf ↦ ObjectProperty.prop_colimit _ (Discrete.functor f) fun ⟨j⟩ ↦ hf j)
    (fun t ht h₁ h₂ ↦ ObjectProperty.ext_of_isTriangulatedClosed₃ _ t ht h₁ h₂)

/-- If every morphism from `(G i)⟦k⟧` to `W` vanishes for all `k > n`, then the same holds for
every object `R` in `InCellClosure G`. -/
theorem hom_shift_eq_zero_of_inCellClosure (W : T) (n : ℤ)
    (hG : ∀ i, ∀ k : ℤ, n < k → ∀ g : (G i)⟦k⟧ ⟶ W, g = 0) {R : T}
    (hR : InCellClosure G R) : ∀ k : ℤ, n < k → ∀ g : R⟦k⟧ ⟶ W, g = 0 := by
  refine hR.induction_on (P := fun A ↦ ∀ k : ℤ, n < k → ∀ g : A⟦k⟧ ⟶ W, g = 0) hG ?_ ?_ ?_
  · intro A B e hA k hk g
    exact (cancel_epi (e.hom⟦k⟧')).1 (by rw [comp_zero]; exact hA k hk (e.hom⟦k⟧' ≫ g))
  · intro J f hf k hk g
    refine (isColimitOfPreserves (shiftFunctor T k) (coproductIsCoproduct f)).hom_ext fun ⟨j⟩ ↦ ?_
    dsimp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app]
    rw [comp_zero]; exact hf j k hk ((Sigma.ι f j)⟦k⟧' ≫ g)
  · intro t ht h₁ h₂ k hk g
    let ts := (CategoryTheory.shiftFunctor (Triangle T) k).obj t
    have hts : ts ∈ distTriang T := t.shift_distinguished ht k
    obtain ⟨h, rfl⟩ := ts.yoneda_exact₃ hts g (h₂ k hk (ts.mor₂ ≫ g))
    let e : t.obj₁⟦k + 1⟧ ≅ (t.obj₁⟦k⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd T k 1).app t.obj₁
    let h' : (t.obj₁⟦k⟧)⟦(1 : ℤ)⟧ ⟶ W := h
    have hh : e.hom ≫ h' = 0 := h₁ (k + 1) (by omega) (e.hom ≫ h')
    have hh0 : h' = 0 := (cancel_epi e.hom).1 (hh.trans comp_zero.symm)
    exact (congrArg (ts.mor₃ ≫ ·) hh0).trans comp_zero

/-- If `X` is nonzero and `Hom(X⟦k⟧, X) = 0` for all `k > 0`, then the negative shift
`X⟦-1⟧` does not belong to the cellular closure of `{X}`. -/
theorem not_inCellClosure_shift_neg_one_of_hom {X : T} (hX : ¬ IsZero X)
    (hpos : ∀ k : ℤ, 0 < k → ∀ g : X⟦k⟧ ⟶ X, g = 0) :
    ¬ InCellClosure (fun _ : PUnit.{v + 1} ↦ X) (X⟦(-1 : ℤ)⟧) := by
  intro hmem
  let e : (X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X := (shiftEquiv T (1 : ℤ)).counitIso.app X
  have he : e.hom = 0 :=
    hom_shift_eq_zero_of_inCellClosure X 0 (fun _ ↦ hpos) hmem 1 zero_lt_one e.hom
  exact hX ((IsZero.iff_id_eq_zero X).2 (by rw [← e.inv_hom_id, he, comp_zero]))

end CellClosure

end TauCeti

namespace CategoryTheory.Functor

section

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]
  {I : Type v} {G : I → T}

/-- If a coproduct-preserving homological functor `H : T ⥤ A` into an abelian category `A`
vanishes on `(G i)⟦k⟧` for all `k > n`, then `H.obj (R⟦k⟧)` vanishes for every `R` in
`TauCeti.InCellClosure G` and all `k > n`. -/
theorem isZero_obj_shift_of_inCellClosure {A : Type*} [Category A] [Abelian A] (H : T ⥤ A)
    [H.IsHomological] (hH : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) H) (n : ℤ)
    (hG : ∀ i, ∀ k : ℤ, n < k → IsZero (H.obj ((G i)⟦k⟧))) {R : T}
    (hR : TauCeti.InCellClosure G R) : ∀ k : ℤ, n < k → IsZero (H.obj (R⟦k⟧)) := by
  refine hR.induction_on (P := fun B ↦ ∀ k : ℤ, n < k → IsZero (H.obj (B⟦k⟧))) hG ?_ ?_ ?_
  · intro B₁ B₂ e hB k hk; exact (hB k hk).of_iso (H.mapIso ((shiftFunctor T k).mapIso e.symm))
  · intro J f hf k hk
    have := hH J
    have hc :
        IsColimit (H.mapCocone ((shiftFunctor T k).mapCocone (Cofan.mk (∐ f) (Sigma.ι f)))) :=
      isColimitOfPreserves H (isColimitOfPreserves (shiftFunctor T k) (coproductIsCoproduct f))
    rw [IsZero.iff_id_eq_zero]
    exact hc.hom_ext fun ⟨j⟩ ↦ (hf j k hk).eq_of_src _ _
  · intro t ht h₁ h₂ k hk
    let ts := (CategoryTheory.shiftFunctor (Triangle T) k).obj t
    have hrot : ts.rotate ∈ distTriang T := rot_of_distTriang _ (t.shift_distinguished ht k)
    have hZ₁ : IsZero (H.obj ((t.obj₁⟦k⟧)⟦(1 : ℤ)⟧)) :=
      (h₁ (k + 1) (by omega)).of_iso (H.mapIso ((shiftFunctorAdd T k 1).symm.app t.obj₁))
    have hZ₂ : IsZero (H.obj (t.obj₂⟦k⟧)) := h₂ k hk
    exact (H.map_distinguished_exact _ hrot).isZero_of_both_isZero hZ₂ hZ₁

/-- If a coproduct-preserving homological functor `H : T ⥤ A` is nonzero on `X` and vanishes on
`X⟦k⟧` for all `k > 0`, then `X⟦-1⟧` does not lie in the cellular closure of `{X}`. -/
theorem not_inCellClosure_shift_neg_one {X : T} {A : Type*} [Category A] [Abelian A] (H : T ⥤ A)
    [H.IsHomological] (hH : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) H)
    (hX0 : ¬ IsZero (H.obj X)) (hXpos : ∀ k : ℤ, 0 < k → IsZero (H.obj (X⟦k⟧))) :
    ¬ TauCeti.InCellClosure (fun _ : PUnit.{v + 1} ↦ X) (X⟦(-1 : ℤ)⟧) := by
  intro hmem
  have h1 : IsZero (H.obj ((X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)) :=
    H.isZero_obj_shift_of_inCellClosure hH 0 (fun _ ↦ hXpos) hmem 1 zero_lt_one
  exact hX0 (h1.of_iso (H.mapIso ((shiftEquiv T (1 : ℤ)).counitIso.symm.app X)))

end

end CategoryTheory.Functor
