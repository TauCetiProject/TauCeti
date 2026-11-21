/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.CategoryTheory.Triangulated.HomotopyColimit
public import TauCeti.CategoryTheory.Triangulated.LocalizingClosure

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import TauCeti.Algebra.Category.Grp.Products
import TauCeti.Algebra.DirectSum.Exact

/-!
# Cellular approximation in pretriangulated categories with coproducts

In a pretriangulated category `T` (with morphisms in `Type v`), we establish:

1. **Compact objects form a thick triangulated subcategory:** `TauCeti.compactForCoproducts T` is
   isomorphism-closed, retract-closed, shift-closed, and triangulated
   (`TauCeti.IsCompactForCoproducts.of_distTriang`, via the five lemma).
2. **Cellular closure:** `TauCeti.InCellClosure G R` is the smallest isomorphism-invariant class
   containing `G : I → T` (`I : Type v`) closed under `Type v`-indexed coproducts and cones. We
   prove closure under small coproducts, zero objects, positive shifts `⟦n⟧`, and Milnor
   homotopy colimits, containment in `ObjectProperty.localizingClosure`,
   `TauCeti.inCellClosure_empty_iff`, and the negative-shift obstruction
   (`TauCeti.hom_shift_eq_zero_of_inCellClosure`,
   `CategoryTheory.Functor.isZero_shift_of_inCellClosure`,
   `CategoryTheory.Functor.not_inCellClosure_shift_neg_one`).
3. **Generic cellular approximation:** for compact `G : I → T` and homological
   `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` taking `Type v`-indexed coproducts to products, there exist
   `R` in `InCellClosure G` and `x : E.obj (op R)` with `(G i ⟶ R) ≃ E.obj (op (G i))`
   (`TauCeti.cellularApproximation`), yielding `TauCeti.cellularApproximation_obj` without
   `IsTriangulated T`.

## Main definitions

* `TauCeti.compactForCoproducts`, `TauCeti.InCellClosure`

## Main results

* `TauCeti.IsCompactForCoproducts.of_distTriang`, `TauCeti.IsCompactForCoproducts.of_distTriang₁`,
  `TauCeti.IsCompactForCoproducts.of_distTriang₂`
* `TauCeti.InCellClosure.shift_nat`, `TauCeti.InCellClosure.of_milnorTriangle`,
  `TauCeti.inCellClosure_empty_iff`, `TauCeti.inCellClosure_le_localizingClosure`
* `TauCeti.hom_shift_eq_zero_of_inCellClosure`,
  `CategoryTheory.Functor.isZero_shift_of_inCellClosure`,
  `CategoryTheory.Functor.not_inCellClosure_shift_neg_one`
* `TauCeti.cellularApproximation`, `TauCeti.cellularApproximation_obj`

## References

* A. Neeman, *Triangulated categories*, Princeton Univ. Press (2001), Lemma 4.2.4, Section 8.2.
* S. Schwede, *Symmetric spectra*, Chapter II, Def. 5.4, Lemma 5.6, and Prop. 5.14.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped DirectSum

universe w v u

namespace TauCeti

section CompactSubcategory

/-- The `ObjectProperty` of objects compact for coproducts in a preadditive category. -/
def compactForCoproducts (T : Type u) [Category.{v} T] [Preadditive T] : ObjectProperty T :=
  IsCompactForCoproducts

section Preadditive

variable {T : Type u} [Category.{v} T] [Preadditive T]

@[simp]
theorem compactForCoproducts_iff (G : T) :
    compactForCoproducts T G ↔ IsCompactForCoproducts G :=
  Iff.rfl

instance : (compactForCoproducts T).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso e

instance : (compactForCoproducts T).IsStableUnderRetracts where
  of_retract h hY := hY.of_retract h

end Preadditive

section Pretriangulated

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- If the first two objects of a distinguished triangle are compact for coproducts, then so is the
third object. -/
theorem IsCompactForCoproducts.of_distTriang {t : Triangle T} (ht : t ∈ distTriang T)
    (h₁ : IsCompactForCoproducts t.obj₁) (h₂ : IsCompactForCoproducts t.obj₂) :
    IsCompactForCoproducts t.obj₃ := by
  rw [isCompactForCoproducts_iff]
  intro J _ f _
  have ht₁ : t.rotate ∈ distTriang T := rot_of_distTriang _ ht
  have ht₂ : t.rotate.rotate ∈ distTriang T := rot_of_distTriang _ ht₁
  have hcomm {A B : T} (u : A ⟶ B) :
      (Preadditive.leftComp (∐ f) u).toIntLinearMap.comp
          (coprodComparisonAddHom B f).toIntLinearMap =
        (coprodComparisonAddHom A f).toIntLinearMap.comp
          (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) u).toIntLinearMap) :=
    DirectSum.linearMap_ext _ fun j ↦ LinearMap.ext fun g ↦ by
      simp [DirectSum.lof_eq_of, Preadditive.leftComp, Category.assoc]
  have hex {s : Triangle T} (hs : s ∈ distTriang T) (W : T) :
      Function.Exact (Preadditive.leftComp W s.mor₂).toIntLinearMap
        (Preadditive.leftComp W s.mor₁).toIntLinearMap := fun g ↦
    ⟨fun hg ↦ let ⟨h, hh⟩ := s.yoneda_exact₂ hs g hg; ⟨h, hh.symm⟩,
      fun ⟨h, hh⟩ ↦ hh ▸ (comp_distTriang_mor_zero₁₂_assoc _ hs h).trans zero_comp⟩
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (DirectSum.lmap (R := ℤ) fun j ↦
      (Preadditive.leftComp (f j) (-t.mor₁⟦(1 : ℤ)⟧')).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₃).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₂).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₁).toIntLinearMap)
    (Preadditive.leftComp (∐ f) (-t.mor₁⟦(1 : ℤ)⟧')).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₃).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₂).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₁).toIntLinearMap
    (coprodComparisonAddHom (t.obj₂⟦(1 : ℤ)⟧) f).toIntLinearMap
    (coprodComparisonAddHom (t.obj₁⟦(1 : ℤ)⟧) f).toIntLinearMap
    (coprodComparisonAddHom t.obj₃ f).toIntLinearMap
    (coprodComparisonAddHom t.obj₂ f).toIntLinearMap
    (coprodComparisonAddHom t.obj₁ f).toIntLinearMap
    (hcomm (-t.mor₁⟦(1 : ℤ)⟧')) (hcomm t.mor₃) (hcomm t.mor₂) (hcomm t.mor₁)
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht₂ (f j))
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht₁ (f j))
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht (f j))
    (hex ht₂ (∐ f)) (hex ht₁ (∐ f)) (hex ht (∐ f))
    ((isCompactForCoproducts_iff _).1 (h₂.shift (1 : ℤ)) J f).2
    ((isCompactForCoproducts_iff _).1 (h₁.shift (1 : ℤ)) J f)
    ((isCompactForCoproducts_iff _).1 h₂ J f)
    ((isCompactForCoproducts_iff _).1 h₁ J f).1

/-- If the first and third objects of a distinguished triangle are compact for coproducts, then so
is the second object. -/
theorem IsCompactForCoproducts.of_distTriang₂ {t : Triangle T} (ht : t ∈ distTriang T)
    (h₁ : IsCompactForCoproducts t.obj₁) (h₃ : IsCompactForCoproducts t.obj₃) :
    IsCompactForCoproducts t.obj₂ :=
  (h₃.shift (-1 : ℤ)).of_distTriang (inv_rot_of_distTriang _ ht) h₁

/-- If the second and third objects of a distinguished triangle are compact for coproducts, then so
is the first object. -/
theorem IsCompactForCoproducts.of_distTriang₁ {t : Triangle T} (ht : t ∈ distTriang T)
    (h₂ : IsCompactForCoproducts t.obj₂) (h₃ : IsCompactForCoproducts t.obj₃) :
    IsCompactForCoproducts t.obj₁ :=
  (isCompactForCoproducts_shift_iff t.obj₁ (1 : ℤ)).1 (h₂.of_distTriang (rot_of_distTriang _ ht) h₃)

instance : (compactForCoproducts T).IsTriangulated where
  exists_zero := ⟨0, isZero_zero T, isCompactForCoproducts_zero⟩
  isStableUnderShiftBy a := ⟨fun _ h ↦ h.shift a⟩
  toIsTriangulatedClosed₂ := .mk' fun _ ht h₁ h₃ ↦ h₁.of_distTriang₂ ht h₃

end Pretriangulated

end CompactSubcategory

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
theorem InCellClosure.induction {P : T → Prop} {R : T} (hR : InCellClosure G R)
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
  hR.induction
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
theorem inCellClosure_empty_iff (R : T) :
    InCellClosure (PEmpty.elim : PEmpty.{v + 1} → T) R ↔ IsZero R := by
  refine ⟨fun hR ↦ ?_, InCellClosure.of_isZero _⟩
  refine hR.induction (fun i ↦ PEmpty.elim i) (fun e hA ↦ hA.of_iso e.symm)
    (fun _ f hf ↦ ?_) (fun t ht h₁ h₂ ↦ ?_)
  · rw [IsZero.iff_id_eq_zero]; exact Sigma.hom_ext _ _ fun j ↦ (hf j).eq_of_src _ _
  · have hm : t.mor₁ = (h₁.iso h₂).hom := h₁.eq_of_src _ _
    have : IsIso t.mor₁ := hm ▸ inferInstance
    exact t.isZero₃_of_isIso₁ ht inferInstance

/-- The cellular closure of `G` is contained in the localizing closure of its range. -/
theorem inCellClosure_le_localizingClosure (G : I → T) {R : T} (hR : InCellClosure G R) :
    ObjectProperty.localizingClosure (fun X ↦ ∃ i, G i = X) R :=
  hR.induction
    (fun i ↦ ObjectProperty.le_localizingClosure _ _ ⟨i, rfl⟩)
    (fun e hA ↦ ObjectProperty.prop_of_iso _ e hA)
    (fun _ f hf ↦ ObjectProperty.prop_colimit _ (Discrete.functor f) fun ⟨j⟩ ↦ hf j)
    (fun t ht h₁ h₂ ↦ ObjectProperty.ext_of_isTriangulatedClosed₃ _ t ht h₁ h₂)

/-- If every morphism from `(G i)⟦k⟧` to `W` vanishes for all `k > n`, then the same holds for
every object `R` in `InCellClosure G`. -/
theorem hom_shift_eq_zero_of_inCellClosure (W : T) (n : ℤ)
    (hG : ∀ i, ∀ k : ℤ, n < k → ∀ g : (G i)⟦k⟧ ⟶ W, g = 0) {R : T}
    (hR : InCellClosure G R) : ∀ k : ℤ, n < k → ∀ g : R⟦k⟧ ⟶ W, g = 0 := by
  refine hR.induction (P := fun A ↦ ∀ k : ℤ, n < k → ∀ g : A⟦k⟧ ⟶ W, g = 0) hG ?_ ?_ ?_
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

/-- If a coproduct-preserving homological functor `H : T ⥤ AddCommGrpCat.{v}` vanishes on
`(G i)⟦k⟧` for all `k > n`, then it vanishes on `R⟦k⟧` for every `R` in `TauCeti.InCellClosure G`
and all `k > n`. -/
theorem isZero_shift_of_inCellClosure (H : T ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) H) (n : ℤ)
    (hG : ∀ i, ∀ k : ℤ, n < k → IsZero (H.obj ((G i)⟦k⟧))) {R : T}
    (hR : TauCeti.InCellClosure G R) : ∀ k : ℤ, n < k → IsZero (H.obj (R⟦k⟧)) := by
  refine hR.induction (P := fun A ↦ ∀ k : ℤ, n < k → IsZero (H.obj (A⟦k⟧))) hG ?_ ?_ ?_
  · intro A B e hA k hk; exact (hA k hk).of_iso (H.mapIso ((shiftFunctor T k).mapIso e.symm))
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
    have hex := (ShortComplex.ab_exact_iff _).1 (H.map_distinguished_exact _ hrot)
    dsimp only [ShortComplex.map, shortComplexOfDistTriangle, Triangle.rotate] at hex
    have hZ₁ : IsZero (H.obj ((t.obj₁⟦k⟧)⟦(1 : ℤ)⟧)) :=
      (h₁ (k + 1) (by omega)).of_iso (H.mapIso ((shiftFunctorAdd T k 1).symm.app t.obj₁))
    have hZ₂ : IsZero (H.obj (t.obj₂⟦k⟧)) := h₂ k hk
    rw [IsZero.iff_id_eq_zero]
    ext a
    have ha₁ : H.map ts.mor₃ a = 0 :=
      congrArg (fun φ : H.obj ((t.obj₁⟦k⟧)⟦(1 : ℤ)⟧) ⟶ _ ↦ φ (H.map ts.mor₃ a))
        ((IsZero.iff_id_eq_zero _).1 hZ₁)
    obtain ⟨b, hb⟩ := hex a ha₁
    have hb0 : (b : H.obj (t.obj₂⟦k⟧)) = 0 :=
      congrArg (fun φ : H.obj (t.obj₂⟦k⟧) ⟶ _ ↦ φ b) ((IsZero.iff_id_eq_zero _).1 hZ₂)
    exact hb.symm.trans ((congrArg (H.map ts.mor₂) hb0).trans (map_zero _))

/-- If a coproduct-preserving homological functor `H` is nonzero on `X` and vanishes on `X⟦k⟧`
for all `k > 0`, then `X⟦-1⟧` does not lie in the cellular closure of `{X}`. -/
theorem not_inCellClosure_shift_neg_one {X : T} (H : T ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) H)
    (hX0 : ¬ IsZero (H.obj X)) (hXpos : ∀ k : ℤ, 0 < k → IsZero (H.obj (X⟦k⟧))) :
    ¬ TauCeti.InCellClosure (fun _ : PUnit.{v + 1} ↦ X) (X⟦(-1 : ℤ)⟧) := by
  intro hmem
  have h1 : IsZero (H.obj ((X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)) :=
    H.isZero_shift_of_inCellClosure hH 0 (fun _ ↦ hXpos) hmem 1 zero_lt_one
  exact hX0 (h1.of_iso (H.mapIso ((shiftEquiv T (1 : ℤ)).counitIso.symm.app X)))

end

end CategoryTheory.Functor

namespace TauCeti

section CellularApproximation

noncomputable section

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCoproducts.{v} T]
  {I : Type v}

/-- One stage in the inductive construction of a cellular approximation. -/
private structure ApproxStage (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj : T
  cell : InCellClosure G obj
  pt : E.obj (op obj)

/-- The initial cellular stage: a coproduct of copies of `G i` indexed by all pairs `(i, y)` with
`y : E.obj (op (G i))`, together with the universal element matching every `y` on its summand. -/
private def approxStageZero (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E) : ApproxStage G E :=
  let J₀ := Σ i : I, E.obj (op (G i))
  let f₀ : J₀ → T := fun p ↦ G p.1
  have : PreservesLimitsOfShape (Discrete J₀) E := hE J₀
  { obj := ∐ f₀
    cell := InCellClosure.coproduct f₀ fun p ↦ InCellClosure.generator G p.1
    pt := ((coproductIsCoproduct f₀).cofanOpToPiAddEquiv E).symm fun p ↦ p.2 }

private lemma approxStageZero_map_ι (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E)
    (i : I) (y : E.obj (op (G i))) :
    E.map (Sigma.ι (fun p : Σ i : I, E.obj (op (G i)) ↦ G p.1) ⟨i, y⟩).op
        (approxStageZero G E hE).pt = y := by
  let J₀ := Σ i : I, E.obj (op (G i))
  let f₀ : J₀ → T := fun p ↦ G p.1
  have : PreservesLimitsOfShape (Discrete J₀) E := hE J₀
  exact IsColimit.map_inj_cofanOpToPiAddEquiv_symm (coproductIsCoproduct f₀) E
    (fun p : J₀ ↦ p.2) ⟨i, y⟩

/-- One inductive step attaching cells along all morphisms from `G i` that annihilate the current
cohomology class `s.pt`. -/
private structure ApproxStep (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (s : ApproxStage G E) where
  next : ApproxStage G E
  mor : s.obj ⟶ next.obj
  map_pt : E.map mor.op next.pt = s.pt
  kill : ∀ (i : I) (f : G i ⟶ s.obj), E.map f.op s.pt = 0 → f ≫ mor = 0

private def approxStep (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological]
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E)
    (s : ApproxStage G E) : ApproxStep G E s := by
  let K := Σ i : I, { f : G i ⟶ s.obj // E.map f.op s.pt = 0 }
  let g : K → T := fun p ↦ G p.1
  let k : (∐ g) ⟶ s.obj := Sigma.desc fun p ↦ p.2.1
  have htri := distinguished_cocone_triangle k
  let nextObj : T := htri.choose
  let j : s.obj ⟶ nextObj := htri.choose_spec.choose
  let δ : nextObj ⟶ (∐ g)⟦(1 : ℤ)⟧ := htri.choose_spec.choose_spec.choose
  have ht : Triangle.mk k j δ ∈ distTriang T := htri.choose_spec.choose_spec.choose_spec
  have hcell : InCellClosure G nextObj :=
    InCellClosure.of_distTriang ht
      (InCellClosure.coproduct g fun p ↦ InCellClosure.generator G p.1) s.cell
  have hk0 : E.map k.op s.pt = 0 := by
    have := hE K
    apply ((coproductIsCoproduct g).cofanOpToPiAddEquiv E).injective
    rw [map_zero]; funext p; rw [IsColimit.cofanOpToPiAddEquiv_apply]
    dsimp only [Cofan.inj, Cofan.mk_ι_app]
    rw [← CategoryTheory.comp_apply, ← E.map_comp, ← op_comp, Sigma.ι_comp_desc]
    exact p.2.2
  have hlift : ∃ u : E.obj (op nextObj), E.map j.op u = s.pt := by
    have hex := (ShortComplex.ab_exact_iff _).1 (E.map_distinguished_op_exact _ ht)
    dsimp only [ShortComplex.op, ShortComplex.map, shortComplexOfDistTriangle] at hex
    exact hex s.pt hk0
  exact
    { next := ⟨nextObj, hcell, hlift.choose⟩
      mor := j
      map_pt := hlift.choose_spec
      kill := fun i f hf ↦ by
        have hfk : f = Sigma.ι g ⟨i, ⟨f, hf⟩⟩ ≫ k :=
          (Sigma.ι_comp_desc (fun p : K ↦ p.2.1) ⟨i, ⟨f, hf⟩⟩).symm
        have hkj : k ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ ht
        rw [hfk, Category.assoc, hkj, comp_zero] }

/-- **Cellular approximation in a pretriangulated category with coproducts** (Schwede, *Symmetric
spectra*, Chapter II, Proposition 5.14): for any small family `G : I → T` of compact objects and
any contravariant homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` sending `Type v`-indexed
coproducts to products, there exist `R` in the cellular closure of `G` and `x : E.obj (op R)` such
that evaluation `f ↦ E.map f.op x` is bijective on `G i ⟶ R` for every `i`. -/
theorem cellularApproximation (G : I → T) (hG : ∀ i, IsCompactForCoproducts (G i))
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological]
    (hE : ∀ J : Type v, PreservesLimitsOfShape (Discrete J) E) :
    ∃ R : T, InCellClosure G R ∧ ∃ x : E.obj (op R),
      ∀ i, Function.Bijective (fun f : G i ⟶ R ↦ E.map f.op x) := by
  let stage : ℕ → ApproxStage G E :=
    Nat.rec (approxStageZero G E hE) fun _ s ↦ (approxStep G E hE s).next
  let X : ℕ ⥤ T := Functor.ofSequence fun n ↦ (approxStep G E hE (stage n)).mor
  have : HasCoproductsOfShape ℕ T :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{v})
  have : PreservesLimitsOfShape (Discrete ℕ) E :=
    have := hE (ULift.{v} ℕ)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{v}) E
  obtain ⟨R, ψ, δ, ht⟩ := distinguished_cocone_triangle X.sequenceDifference
  have hcell : InCellClosure G R := InCellClosure.of_milnorTriangle ht fun n ↦ (stage n).cell
  obtain ⟨x, hx⟩ := exists_lift_of_milnorTriangle ht E (fun n ↦ (stage n).pt) fun n ↦ by
    rw [Functor.ofSequence_map_homOfLE_succ]; exact (approxStep G E hE (stage n)).map_pt
  refine ⟨R, hcell, x, fun i ↦ ⟨fun f₁ f₂ hfeq ↦ sub_eq_zero.1 ?_, fun y ↦ ?_⟩⟩
  · have hf : E.map (f₁ - f₂).op x = 0 := by
      dsimp only at hfeq; simpa [op_sub, E.map_sub] using sub_eq_zero.2 hfeq
    obtain ⟨N, h, hfac⟩ := exists_factor_of_milnorTriangle ht (hG i) (f₁ - f₂)
    rw [hfac] at hf ⊢
    have hh : E.map h.op (stage N).pt = 0 := by
      rw [← hx N, ← CategoryTheory.comp_apply, ← E.map_comp, ← op_comp]; exact hf
    have hkill : h ≫ X.map (homOfLE (Nat.le_add_right N 1)) = 0 := by
      rw [Functor.ofSequence_map_homOfLE_succ]; exact (approxStep G E hE (stage N)).kill i h hh
    have hψ : X.sequenceDifference ≫ ψ = 0 := comp_distTriang_mor_zero₁₂ _ ht
    rw [← X.map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero hψ (Nat.le_add_right N 1),
      ← Category.assoc, hkill, zero_comp]
  · let ι₀ : G i ⟶ X.obj 0 := Sigma.ι (fun p : Σ i : I, E.obj (op (G i)) ↦ G p.1) ⟨i, y⟩
    refine ⟨ι₀ ≫ Sigma.ι X.obj 0 ≫ ψ, ?_⟩
    dsimp only; rw [op_comp, E.map_comp, CategoryTheory.comp_apply, hx 0]
    exact approxStageZero_map_ι G E hE i y

/-- **Cellular approximation of an object:** for a small family `G` of compact objects and any
object `Y : T`, there exist an object `R` in `InCellClosure G` and a morphism `u : R ⟶ Y` inducing
bijections `(G i ⟶ R) → (G i ⟶ Y)` by postcomposition for every `i`. -/
theorem cellularApproximation_obj (G : I → T) (hG : ∀ i, IsCompactForCoproducts (G i)) (Y : T) :
    ∃ R : T, InCellClosure G R ∧ ∃ u : R ⟶ Y,
      ∀ i, Function.Bijective (fun f : G i ⟶ R ↦ f ≫ u) :=
  cellularApproximation G hG (preadditiveYoneda.obj Y) fun _ ↦ inferInstance

/-- For a subsingleton (for instance zero) contravariant functor, the zero object and its zero
class provide a cellular approximation directly without compactness or exactness hypotheses. -/
theorem cellularApproximation_of_subsingleton (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [∀ X, Subsingleton (E.obj X)] :
    InCellClosure G (0 : T) ∧
      ∀ i, Function.Bijective (fun f : G i ⟶ (0 : T) ↦ E.map f.op (0 : E.obj (op 0))) := by
  refine ⟨InCellClosure.zero G, fun i ↦ ?_⟩
  have : Subsingleton (G i ⟶ (0 : T)) := ⟨fun f g ↦ (isZero_zero T).eq_of_tgt f g⟩
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

end

end CellularApproximation

end TauCeti
