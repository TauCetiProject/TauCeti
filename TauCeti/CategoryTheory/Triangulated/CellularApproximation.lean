/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import TauCeti.CategoryTheory.Triangulated.HomotopyColimit
public import TauCeti.CategoryTheory.Triangulated.LocalizingClosure
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Cellular closures and cellular approximation in pretriangulated categories

Let `P` be a class of objects in a pretriangulated category `C`. Its **cellular closure**
(`CategoryTheory.ObjectProperty.cellClosure P`) is the smallest isomorphism-closed property
containing `P` that is closed under coproducts indexed by types in the hom universe of `C` and
under third objects of distinguished triangles whose first two objects lie in the property
(`CategoryTheory.ObjectProperty.IsTriangulatedClosed₃`).

Unlike `CategoryTheory.ObjectProperty.localizingClosure`, `P.cellClosure` is only closed under
*nonnegative* shifts (`X⟦(n : ℤ)⟧` for `n : ℕ`), derived from the rotated contractible triangle
`X ⟶ 0 ⟶ X⟦1⟧ ⟶ X⟦1⟧` together with closure under empty coproducts (`ContainsZero`). It need
not be closed under negative shifts: if a coproduct-preserving covariant homological functor `H`
vanishes on `X⟦k⟧` for all `k ≥ n` and `P X`, then it vanishes on `R⟦k⟧` for all `k ≥ n` and
`P.cellClosure R` (`CategoryTheory.ObjectProperty.isZero_map_shift_of_cellClosure`).

When `C` has all hom-universe-indexed coproducts, `{G i}` is a small family of objects whose
additive represented functors preserve countable coproducts (for instance, compact objects in the
sense of `TauCeti.IsCompactForCoproducts`), and `E : Cᵒᵖ ⥤ AddCommGrpCat.{v}` is a contravariant
homological functor sending hom-universe-indexed coproducts to products, **cellular approximation**
(`TauCeti.cellularApproximation`) constructs an object `R` in `(ObjectProperty.ofObj G).cellClosure`
and an element `x : E.obj (op R)` such that evaluation `f ↦ E.map f.op x` is bijective from
`G i ⟶ R` onto `E.obj (op (G i))` for every `i`. The object `R` is built as the homotopy colimit
(`TauCeti.HomotopyColimit`) of a sequence `R₀ ⟶ R₁ ⟶ ⋯` killing kernel elements of `E` on `G i`
at each step, and `x` is lifted via the Milnor short exact sequence
(`TauCeti.HomotopyColimit.exists_map_ι_eq`).

## Main definitions

* `CategoryTheory.ObjectProperty.cellClosure`: the smallest isomorphism-closed class containing `P`
  and closed under `Type v`-coproducts and cones (`IsTriangulatedClosed₃`).

## Main results

* `CategoryTheory.ObjectProperty.cellClosure_le_iff`: universal property of `cellClosure`.
* `CategoryTheory.ObjectProperty.prop_cellClosure_bot_iff`: the cellular closure of `⊥` consists
  precisely of zero objects.
* `CategoryTheory.ObjectProperty.prop_cellClosure_ofObj_iff`: explicit four-clause induction
  principle for `(ObjectProperty.ofObj G).cellClosure` when `C` has `Type v`-coproducts.
* `CategoryTheory.ObjectProperty.isZero_map_shift_of_cellClosure`,
  `CategoryTheory.ObjectProperty.not_cellClosure_singleton_shift_neg_one`: connectivity
  preservation by `cellClosure` and obstruction to negative-shift closure.
* `TauCeti.cellularApproximation`: Schwede's cellular approximation theorem in a pretriangulated
  category with coproducts.

## References

* S. Schwede, *Symmetric spectra*, Chapter II, Proposition 5.14.
* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Theorem 8.3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Pretriangulated Pretriangulated.Opposite ZeroObject

universe v v' u u' w

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section CellClosure

variable (P : ObjectProperty C)

/-- The **cellular closure** of `P`: the smallest isomorphism-closed class of objects containing
`P`, closed under coproducts indexed by `Type v`, and closed under cones (`IsTriangulatedClosed₃`),
defined as the infimum of all such classes. -/
def cellClosure : ObjectProperty C :=
  ⨅ (Q : ObjectProperty C) (_ : P ≤ Q) (_ : Q.IsClosedUnderIsomorphisms)
    (_ : ∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J))
    (_ : Q.IsTriangulatedClosed₃), Q

/-- An object lies in `P.cellClosure` exactly when it lies in every isomorphism-closed property
containing `P` and closed under `Type v`-coproducts and third objects of distinguished triangles. -/
lemma prop_cellClosure_iff (X : C) :
    P.cellClosure X ↔ ∀ Q : ObjectProperty C, P ≤ Q → Q.IsClosedUnderIsomorphisms →
      (∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)) →
      Q.IsTriangulatedClosed₃ → Q X := by
  simp [cellClosure]

lemma le_cellClosure : P ≤ P.cellClosure :=
  fun X hX ↦ (P.prop_cellClosure_iff X).2 fun _ hPQ _ _ _ ↦ hPQ X hX

variable {P} in
/-- The cellular closure of `P` is contained in every class containing `P` and closed under
`Type v`-coproducts and cones. Isomorphism closure of `Q` is not assumed: it follows from closure
under coproducts. -/
lemma cellClosure_le {Q : ObjectProperty C}
    [∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₃] (h : P ≤ Q) : P.cellClosure ≤ Q :=
  have := IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape (P := Q)
    fun (_ : Type v) _ ↦ inferInstance
  fun X hX ↦ (P.prop_cellClosure_iff X).1 hX Q h
    (IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q) inferInstance inferInstance

/-- The universal property of `cellClosure`. Isomorphism closure of `Q` is not assumed: it follows
from closure under coproducts. -/
lemma cellClosure_le_iff {Q : ObjectProperty C}
    [∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)]
    [Q.IsTriangulatedClosed₃] :
    P.cellClosure ≤ Q ↔ P ≤ Q :=
  ⟨P.le_cellClosure.trans, cellClosure_le⟩

instance : P.cellClosure.IsClosedUnderIsomorphisms where
  of_iso e hX := (P.prop_cellClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.prop_of_iso e ((P.prop_cellClosure_iff _).1 hX Q hPQ ‹_› ‹_› ‹_›)

instance (J : Type v) : P.cellClosure.IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := fun _ ⟨h⟩ ↦ (P.prop_cellClosure_iff _).2 fun _ hPQ _ _ _ ↦
    (h.ofLE (cellClosure_le hPQ)).prop

instance : P.cellClosure.IsTriangulatedClosed₃ :=
  .mk' fun T hT h₁ h₂ ↦ (P.prop_cellClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.ext_of_isTriangulatedClosed₃ T hT
      ((P.prop_cellClosure_iff _).1 h₁ Q hPQ ‹_› ‹_› ‹_›)
      ((P.prop_cellClosure_iff _).1 h₂ Q hPQ ‹_› ‹_› ‹_›)

/-- `P.cellClosure` is closed under coproducts indexed by any `v`-small type `J`. -/
lemma isClosedUnderColimitsOfShape_cellClosure_of_small (J : Type w) [Small.{v} J] :
    P.cellClosure.IsClosedUnderColimitsOfShape (Discrete J) :=
  .of_equivalence (Discrete.equivalence (equivShrink.{v} J).symm)

instance : P.cellClosure.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
  P.isClosedUnderColimitsOfShape_cellClosure_of_small ℕ

instance : P.cellClosure.ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero C, ?_⟩
    let c : Cocone (Discrete.functor (C := C) (I := PEmpty.{v + 1}) PEmpty.elim) :=
      { pt := 0
        ι := Discrete.natTrans fun ⟨x⟩ ↦ PEmpty.elim x }
    have hc : IsColimit c :=
      { desc := fun s ↦ (isZero_zero C).to_ s.pt
        fac := fun _ ⟨x⟩ ↦ PEmpty.elim x
        uniq := fun _ _ _ ↦ (isZero_zero C).eq_of_src _ _ }
    exact P.cellClosure.prop_of_isColimit hc fun ⟨x⟩ ↦ PEmpty.elim x

instance : P.cellClosure.IsStableUnderShiftBy (1 : ℤ) where
  le_shift X hX :=
    P.cellClosure.ext_of_isTriangulatedClosed₃ (contractibleTriangle X).rotate
      (rot_of_distTriang _ (contractible_distinguished X)) hX P.cellClosure.prop_zero

/-- The cellular closure is closed under all nonnegative shifts `X⟦(n : ℤ)⟧`. -/
lemma prop_cellClosure_shift_nat {X : C} (hX : P.cellClosure X) (n : ℕ) :
    P.cellClosure (X⟦(n : ℤ)⟧) := by
  induction n with
  | zero =>
    exact P.cellClosure.prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
  | succ n ih =>
    have h1 : P.cellClosure ((X⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧) := P.cellClosure.le_shift (1 : ℤ) _ ih
    have e : (X⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X⟦((n + 1 : ℕ) : ℤ)⟧ :=
      (shiftFunctorAdd' C (n : ℤ) (1 : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; rfl)).symm.app X
    exact P.cellClosure.prop_of_iso e h1

variable {P} in
lemma monotone_cellClosure {Q : ObjectProperty C} (h : P ≤ Q) :
    P.cellClosure ≤ Q.cellClosure :=
  cellClosure_le (h.trans Q.le_cellClosure)

@[simp]
lemma cellClosure_cellClosure : P.cellClosure.cellClosure = P.cellClosure :=
  le_antisymm (cellClosure_le le_rfl) P.cellClosure.le_cellClosure

@[simp]
lemma cellClosure_isoClosure : P.isoClosure.cellClosure = P.cellClosure :=
  le_antisymm
    (cellClosure_le ((P.isoClosure_le_iff P.cellClosure).2 P.le_cellClosure))
    (monotone_cellClosure P.le_isoClosure)

/-- The cellular closure is contained in the localizing closure. -/
theorem cellClosure_le_localizingClosure : P.cellClosure ≤ P.localizingClosure :=
  cellClosure_le P.le_localizingClosure

/-- The cellular closure of the empty property consists precisely of the zero objects. -/
theorem prop_cellClosure_bot_iff (X : C) :
    (⊥ : ObjectProperty C).cellClosure X ↔ IsZero X := by
  refine ⟨fun hX ↦ ?_, fun hX ↦ (⊥ : ObjectProperty C).cellClosure.prop_of_isZero hX⟩
  let Z : ObjectProperty C := IsZero
  have : Z.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso e.symm⟩
  have (J : Type v) : Z.IsClosedUnderColimitsOfShape (Discrete J) :=
    { colimitsOfShape_le := fun Y ⟨h⟩ ↦ by
        change IsZero Y
        rw [IsZero.iff_id_eq_zero]
        exact h.isColimit.hom_ext fun j ↦ (h.prop_diag_obj j).eq_of_src _ _ }
  have : Z.IsTriangulatedClosed₃ := .mk' fun T hT h₁ h₂ ↦ by
    have heq : T.mor₁ = (IsZero.iso h₁ h₂).hom := h₁.eq_of_src _ _
    have : IsIso T.mor₁ := by rw [heq]; infer_instance
    exact T.isZero₃_of_isIso₁ hT inferInstance
  exact cellClosure_le (Q := Z) bot_le X hX

/-- The cellular closure of `⊥` is `IsZero`. -/
@[simp]
theorem cellClosure_bot : (⊥ : ObjectProperty C).cellClosure = IsZero :=
  funext fun X ↦ propext (prop_cellClosure_bot_iff X)

/-- Every generator in a family `G : I → C` belongs to `(ofObj G).cellClosure`. -/
lemma prop_cellClosure_ofObj {I : Type w} (G : I → C) (i : I) :
    (ofObj G).cellClosure (G i) :=
  (ofObj G).le_cellClosure _ (ofObj_apply G i)

/-- Replacing a generating family by pointwise isomorphic objects yields the same cellular
closure. -/
lemma cellClosure_ofObj_eq_of_iso {I : Type w} {G G' : I → C} (e : ∀ i, G i ≅ G' i) :
    (ofObj G).cellClosure = (ofObj G').cellClosure := by
  apply le_antisymm
  · exact cellClosure_le fun X hX ↦ by
      rcases (ofObj_iff G X).1 hX with ⟨i, rfl⟩
      exact (ofObj G').cellClosure.prop_of_iso (e i).symm (prop_cellClosure_ofObj G' i)
  · exact cellClosure_le fun X hX ↦ by
      rcases (ofObj_iff G' X).1 hX with ⟨i, rfl⟩
      exact (ofObj G).cellClosure.prop_of_iso (e i) (prop_cellClosure_ofObj G i)

/-- When `C` has `Type v`-coproducts, `(ofObj G).cellClosure R` is equivalent to membership of `R`
in every isomorphism-invariant class containing each `G i` and closed under `Type v`-coproducts
and third objects of distinguished triangles. -/
theorem prop_cellClosure_ofObj_iff [HasCoproducts.{v} C] {I : Type w} (G : I → C) (R : C) :
    (ofObj G).cellClosure R ↔
      ∀ Q : C → Prop, (∀ i, Q (G i)) →
        (∀ {A B : C}, (A ≅ B) → Q A → Q B) →
        (∀ (J : Type v) (f : J → C), (∀ j, Q (f j)) → Q (∐ f)) →
        (∀ t : Triangle C, t ∈ distTriang C → Q t.obj₁ → Q t.obj₂ → Q t.obj₃) → Q R := by
  constructor
  · intro hR Q hG hiso hcop htri
    let P : ObjectProperty C := Q
    have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hiso e h⟩
    have (J : Type v) : P.IsClosedUnderColimitsOfShape (Discrete J) :=
      ⟨fun Y ⟨h⟩ ↦ by
        let f : J → C := fun j ↦ h.diag.obj ⟨j⟩
        let c : Cofan f := Cofan.mk Y fun j ↦ h.ι.app ⟨j⟩
        let toCocone (s : Cocone (Discrete.functor f)) : Cocone h.diag :=
          Cocone.mk s.pt (Discrete.natTrans fun ⟨j⟩ ↦ s.ι.app ⟨j⟩)
        have hc : IsColimit c :=
          { desc := fun s ↦ h.isColimit.desc (toCocone s)
            fac := fun s ⟨j⟩ ↦ h.isColimit.fac (toCocone s) ⟨j⟩
            uniq := fun s m hm ↦ h.isColimit.uniq (toCocone s) m fun ⟨j⟩ ↦ hm ⟨j⟩ }
        exact hiso (IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct f) hc)
          (hcop J f fun j ↦ h.prop_diag_obj ⟨j⟩)⟩
    have : P.IsTriangulatedClosed₃ := .mk' fun t ht h₁ h₂ ↦ htri t ht h₁ h₂
    exact (ofObj G).prop_cellClosure_iff R |>.1 hR P ((ofObj_le_iff G P).2 hG)
      inferInstance inferInstance inferInstance
  · intro hR
    exact hR (ofObj G).cellClosure (prop_cellClosure_ofObj G)
      (fun e h ↦ (ofObj G).cellClosure.prop_of_iso e h)
      (fun J f hf ↦ (ofObj G).cellClosure.prop_colimit _ fun ⟨j⟩ ↦ hf j)
      (fun t ht h₁ h₂ ↦ (ofObj G).cellClosure.ext_of_isTriangulatedClosed₃ t ht h₁ h₂)

/-- **Connectivity preservation under cellular closure**: if a covariant homological functor
`H : C ⥤ A` preserving `Type v`-coproducts vanishes on `X⟦k⟧` for all `k ≥ n` whenever `P X`, then
it vanishes on `R⟦k⟧` for all `k ≥ n` whenever `P.cellClosure R`. -/
theorem isZero_map_shift_of_cellClosure {A : Type u'} [Category.{v'} A] [Abelian A]
    (H : C ⥤ A) [H.IsHomological] [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H]
    (n : ℤ) {P : ObjectProperty C}
    (hP : ∀ X, P X → ∀ k : ℤ, n ≤ k → IsZero (H.obj (X⟦k⟧)))
    {R : C} (hR : P.cellClosure R) (k : ℤ) (hk : n ≤ k) :
    IsZero (H.obj (R⟦k⟧)) := by
  let Q : ObjectProperty C := fun X ↦ ∀ m : ℤ, n ≤ m → IsZero (H.obj (X⟦m⟧))
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e hX m hm ↦ (hX m hm).of_iso (H.mapIso ((shiftFunctor C m).mapIso e)).symm⟩
  have (J : Type v) : Q.IsClosedUnderColimitsOfShape (Discrete J) :=
    { colimitsOfShape_le := fun Y ⟨h⟩ m hm ↦ by
        have hc : IsColimit ((shiftFunctor C m ⋙ H).mapCocone (Cocone.mk _ h.ι)) :=
          isColimitOfPreserves (shiftFunctor C m ⋙ H) h.isColimit
        rw [IsZero.iff_id_eq_zero]
        exact hc.hom_ext fun j ↦ (h.prop_diag_obj j m hm).eq_of_src _ _ }
  have : Q.IsTriangulatedClosed₃ := .mk' fun T hT h₁ h₂ m hm ↦ by
    have hrot : (Triangle.shiftFunctor C m).obj T.rotate ∈ distTriang C :=
      Triangle.shift_distinguished _ (rot_of_distTriang _ hT) m
    have hex := H.map_distinguished_exact _ hrot
    have hX₁ : IsZero (H.obj (T.obj₂⟦m⟧)) := h₂ m hm
    have e₃ : (T.obj₁⟦(1 : ℤ)⟧)⟦m⟧ ≅ T.obj₁⟦m + 1⟧ :=
      (shiftFunctorAdd' C (1 : ℤ) m (m + 1) (add_comm 1 m)).symm.app T.obj₁
    have hX₃ : IsZero (H.obj ((T.obj₁⟦(1 : ℤ)⟧)⟦m⟧)) :=
      (h₁ (m + 1) (by lia)).of_iso (H.mapIso e₃)
    exact hex.isZero_of_both_isZero hX₁ hX₃
  exact cellClosure_le (Q := Q) hP R hR k hk

/-- If a coproduct-preserving covariant homological functor `H : C ⥤ A` is nonzero on `X` but
vanishes on all strictly positive shifts `X⟦k⟧` (`k > 0`), then `X⟦-1⟧` does not lie in the
cellular closure of `X`. -/
theorem not_cellClosure_singleton_shift_neg_one {A : Type u'} [Category.{v'} A] [Abelian A]
    (H : C ⥤ A) [H.IsHomological] [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H]
    {X : C} (h0 : ¬ IsZero (H.obj X)) (hpos : ∀ k : ℤ, 0 < k → IsZero (H.obj (X⟦k⟧))) :
    ¬ (singleton X).cellClosure (X⟦(-1 : ℤ)⟧) := by
  intro hmem
  have hz : IsZero (H.obj ((X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)) :=
    isZero_map_shift_of_cellClosure H (1 : ℤ)
      (fun Y hY k hk ↦ by
        obtain rfl := (singleton_iff X Y).1 hY
        exact hpos k (by lia))
      hmem (1 : ℤ) le_rfl
  have e : (X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X :=
    (shiftFunctorAdd' C (-1 : ℤ) (1 : ℤ) (0 : ℤ) (neg_add_cancel 1)).symm.app X ≪≫
      (shiftFunctorZero C ℤ).app X
  exact h0 (hz.of_iso (H.mapIso e).symm)

end CellClosure

end CategoryTheory.ObjectProperty

namespace TauCeti

namespace HomotopyColimit

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A homotopy colimit of a sequence of objects in `P.cellClosure` again lies in
`P.cellClosure`. -/
theorem prop_cellClosure {P : ObjectProperty C} {X : ℕ ⥤ C}
    [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)
    (hX : ∀ n, P.cellClosure (X.obj n)) : P.cellClosure h.pt :=
  h.prop_pt hX

end HomotopyColimit

section CoproductPiHelpers

variable {T : Type u} [Category.{v} T] [HasCoproducts.{v} T]

/-- For a functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` preserving `Discrete J`-limits, identify
`E(∐ f)` with the product abelian group `∀ j, E(f j)`. -/
private def mapCoprodIsoPi (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) {J : Type v}
    [PreservesLimitsOfShape (Discrete J) E] (f : J → T) :
    E.obj (op (∐ f)) ≅ AddCommGrpCat.of (∀ j : J, E.obj (op (f j))) :=
  IsLimit.conePointUniqueUpToIso
    (isLimitFanMkObjOfIsLimit E (fun j ↦ op (f j)) (fun j ↦ (Sigma.ι f j).op)
      (Cofan.IsColimit.op (coproductIsCoproduct f)))
    (AddCommGrpCat.HasLimit.productLimitCone (fun j : J ↦ E.obj (op (f j)))).isLimit

private lemma mapCoprodIsoPi_hom_apply (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) {J : Type v}
    [PreservesLimitsOfShape (Discrete J) E] (f : J → T) (x : E.obj (op (∐ f))) (j : J) :
    (mapCoprodIsoPi E f).hom x j = E.map (Sigma.ι f j).op x := by
  have h1 := IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitFanMkObjOfIsLimit E (fun j ↦ op (f j)) (fun j ↦ (Sigma.ι f j).op)
      (Cofan.IsColimit.op (coproductIsCoproduct f)))
    (AddCommGrpCat.HasLimit.productLimitCone (fun j : J ↦ E.obj (op (f j)))).isLimit ⟨j⟩
  exact ConcreteCategory.congr_hom h1 x

private lemma map_ι_mapCoprodIsoPi_inv (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) {J : Type v}
    [PreservesLimitsOfShape (Discrete J) E] (f : J → T) (a : ∀ j : J, E.obj (op (f j))) (j : J) :
    E.map (Sigma.ι f j).op ((mapCoprodIsoPi E f).inv a) = a j := by
  rw [← mapCoprodIsoPi_hom_apply, ← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

private lemma eq_zero_of_map_ι_eq_zero (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) {J : Type v}
    [PreservesLimitsOfShape (Discrete J) E] (f : J → T) {x : E.obj (op (∐ f))}
    (hx : ∀ j : J, E.map (Sigma.ι f j).op x = 0) : x = 0 := by
  apply (mapCoprodIsoPi E f).addCommGroupIsoToAddEquiv.injective
  rw [map_zero]
  ext j
  exact (mapCoprodIsoPi_hom_apply E f x j).trans (hx j)

end CoproductPiHelpers

section CellularApproximation

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  [HasCoproducts.{v} T]

/-- One stage in the inductive construction of a cellular approximation. -/
private structure ApproxStage {I : Type w} (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj : T
  cell : (ObjectProperty.ofObj G).cellClosure obj
  elem : E.obj (op obj)

/-- Initial stage `R₀ = ∐_{(i, a)} G i` with the universal class `x₀ ∈ E(R₀)`. -/
private def approxInit {I : Type w} [Small.{v} I] (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E] :
    ApproxStage G E where
  obj := ∐ fun p : Shrink.{v} (Σ i : I, E.obj (op (G i))) ↦ G ((equivShrink _).symm p).1
  cell := (ObjectProperty.ofObj G).cellClosure.prop_colimit _ fun ⟨p⟩ ↦
    ObjectProperty.prop_cellClosure_ofObj G ((equivShrink _).symm p).1
  elem := (mapCoprodIsoPi E
      (fun p : Shrink.{v} (Σ i : I, E.obj (op (G i))) ↦ G ((equivShrink _).symm p).1)).inv
    fun p ↦ ((equivShrink _).symm p).2

private lemma approxInit_surj {I : Type w} [Small.{v} I] (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E] (i : I) (a : E.obj (op (G i))) :
    ∃ g : G i ⟶ (approxInit G E).obj, E.map g.op (approxInit G E).elem = a := by
  let P := Shrink.{v} (Σ j : I, E.obj (op (G j)))
  let F : P → T := fun p ↦ G ((equivShrink _).symm p).1
  have h : ∀ q : Σ j : I, E.obj (op (G j)),
      ∃ g : G q.1 ⟶ (approxInit G E).obj, E.map g.op (approxInit G E).elem = q.2 := fun q ↦ by
    let p : P := equivShrink.{v} (Σ j : I, E.obj (op (G j))) q
    rw [← (equivShrink.{v} (Σ j : I, E.obj (op (G j)))).symm_apply_apply q]
    exact ⟨Sigma.ι F p, map_ι_mapCoprodIsoPi_inv E F (fun r ↦ ((equivShrink _).symm r).2) p⟩
  exact h ⟨i, a⟩

/-- One step from stage `s` to `next`, lifting `s.elem` and killing all `G i ⟶ s.obj` that
annihilate `s.elem`. -/
private structure ApproxTransition {I : Type w} (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    (s : ApproxStage G E) where
  next : ApproxStage G E
  hom : s.obj ⟶ next.obj
  map_elem : E.map hom.op next.elem = s.elem
  kills : ∀ i (f : G i ⟶ s.obj), E.map f.op s.elem = 0 → f ≫ hom = 0

/-- Given stage `s`, attach cells along all morphisms `f : G i ⟶ s.obj` with `E(f)(s.elem) = 0`. -/
private def approxStep {I : Type w} [Small.{v} I] (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [E.IsHomological] [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E]
    (s : ApproxStage G E) : ApproxTransition G E s := by
  let K := Shrink.{v} (Σ i : I, { f : G i ⟶ s.obj // E.map f.op s.elem = 0 })
  let F : K → T := fun k ↦ G ((equivShrink _).symm k).1
  let α : (∐ F) ⟶ s.obj := Sigma.desc fun k ↦ ((equivShrink _).symm k).2.1
  let htr := Classical.choose_spec (distinguished_cocone_triangle α)
  let Z : T := Classical.choose (distinguished_cocone_triangle α)
  let hom : s.obj ⟶ Z := Classical.choose htr
  let htr' := Classical.choose_spec htr
  let δ : Z ⟶ (∐ F)⟦(1 : ℤ)⟧ := Classical.choose htr'
  have hdist : Triangle.mk α hom δ ∈ distTriang T := Classical.choose_spec htr'
  have hFcell : (ObjectProperty.ofObj G).cellClosure (∐ F) :=
    (ObjectProperty.ofObj G).cellClosure.prop_colimit _ fun ⟨k⟩ ↦
      ObjectProperty.prop_cellClosure_ofObj G ((equivShrink _).symm k).1
  have hZcell : (ObjectProperty.ofObj G).cellClosure Z :=
    (ObjectProperty.ofObj G).cellClosure.ext_of_isTriangulatedClosed₃ _ hdist hFcell s.cell
  have hαzero : E.map α.op s.elem = 0 := by
    refine eq_zero_of_map_ι_eq_zero E F fun k ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← E.map_comp, ← op_comp, Sigma.ι_comp_desc]
    exact ((equivShrink _).symm k).2.2
  have hex := E.map_distinguished_op_exact _ hdist
  have hlift := (ShortComplex.ab_exact_iff _).1 hex s.elem hαzero
  refine ⟨⟨Z, hZcell, Classical.choose hlift⟩, hom, Classical.choose_spec hlift, ?_⟩
  intro i f hf
  have hkill : ∀ q : Σ j : I, { g : G j ⟶ s.obj // E.map g.op s.elem = 0 },
      q.2.1 ≫ hom = 0 := fun q ↦ by
    let Q := Σ j : I, { g : G j ⟶ s.obj // E.map g.op s.elem = 0 }
    let k : K := equivShrink.{v} Q q
    rw [← (equivShrink.{v} Q).symm_apply_apply q]
    have hcomp : α ≫ hom = 0 := comp_distTriang_mor_zero₁₂ _ hdist
    calc ((equivShrink _).symm k).2.1 ≫ hom
        = (Sigma.ι F k ≫ α) ≫ hom := by rw [Sigma.ι_comp_desc]
      _ = Sigma.ι F k ≫ (α ≫ hom) := Category.assoc _ _ _
      _ = 0 := by rw [hcomp, comp_zero]
  exact hkill ⟨i, ⟨f, hf⟩⟩

private def approxStage {I : Type w} [Small.{v} I] (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [E.IsHomological] [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E] :
    ℕ → ApproxStage G E
  | 0 => approxInit G E
  | n + 1 => (approxStep G E (approxStage G E n)).next

private def approxTrans {I : Type w} [Small.{v} I] (G : I → T) (E : Tᵒᵖ ⥤ AddCommGrpCat.{v})
    [E.IsHomological] [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E] (n : ℕ) :
    (approxStage G E n).obj ⟶ (approxStage G E (n + 1)).obj :=
  (approxStep G E (approxStage G E n)).hom

/-- **Cellular approximation in a pretriangulated category with coproducts** (Schwede,
*Symmetric spectra* II, Proposition 5.14): given a small family of countably compact objects
`G : I → T` and a contravariant homological functor `E : Tᵒᵖ ⥤ AddCommGrpCat.{v}` sending
`Type v`-coproducts to products, there exist an object `R` in the cellular closure of `G` and an
element `x ∈ E(R)` such that evaluation `f ↦ E(f)(x)` is a bijection `(G i ⟶ R) ≃ E(G i)` for
every `i : I`.

Any family of compact objects in the sense of `TauCeti.IsCompactForCoproducts` satisfies the
countable compactness hypothesis via `IsCompactForCoproducts.preservesColimitsOfShape_of_small ℕ`.
-/
theorem cellularApproximation {I : Type w} [Small.{v} I] (G : I → T)
    [∀ i, PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op (G i)))]
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{v}) [E.IsHomological]
    [∀ J : Type v, PreservesLimitsOfShape (Discrete J) E] :
    ∃ R : T, (ObjectProperty.ofObj G).cellClosure R ∧ ∃ x : E.obj (op R),
      ∀ i, Function.Bijective (fun f : G i ⟶ R ↦ E.map f.op x) := by
  let X : ℕ ⥤ T := Functor.ofSequence (approxTrans G E)
  have : HasColimitsOfShape (Discrete ℕ) T :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{v})
  have : PreservesLimitsOfShape (Discrete ℕ) E :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{v}) E
  let h : HomotopyColimit X := Classical.choice (HomotopyColimit.nonempty X)
  have hcell : (ObjectProperty.ofObj G).cellClosure h.pt :=
    h.prop_cellClosure fun n ↦ (approxStage G E n).cell
  obtain ⟨u, hu⟩ := h.exists_map_ι_eq E (fun n ↦ (approxStage G E n).elem) fun n ↦ by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (approxStep G E (approxStage G E n)).map_elem
  refine ⟨h.pt, hcell, u, fun i ↦ ⟨?_, ?_⟩⟩
  · let evalHom : (G i ⟶ h.pt) →+ E.obj (op (G i)) :=
      { toFun := fun f ↦ E.map f.op u
        map_zero' := by simp
        map_add' := fun f g ↦ by simp }
    change Function.Injective evalHom
    rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨N, g, rfl⟩ := h.exists_eq_comp_ι f
    have hg : E.map g.op (approxStage G E N).elem = 0 := by
      rw [← hu N, ← ConcreteCategory.comp_apply, ← E.map_comp, ← op_comp]
      exact hf
    have hkill : g ≫ X.map (homOfLE (Nat.le_add_right N 1)) = 0 := by
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact (approxStep G E (approxStage G E N)).kills i g hg
    rw [← h.map_homOfLE_comp_ι (Nat.le_add_right N 1), ← Category.assoc, hkill, zero_comp]
  · intro a
    obtain ⟨g, hg⟩ := approxInit_surj G E i a
    let g₀ : G i ⟶ X.obj 0 := g
    refine ⟨g₀ ≫ h.ι 0, ?_⟩
    change E.map (g₀ ≫ h.ι 0).op u = a
    rw [op_comp, E.map_comp, ConcreteCategory.comp_apply, hu 0]
    exact hg

end CellularApproximation

end TauCeti

end
