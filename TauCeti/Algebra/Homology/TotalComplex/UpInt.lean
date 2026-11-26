/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotalComplex.MappingCone
import TauCeti.Algebra.Homology.ComplexShape.Signs
import TauCeti.Algebra.Homology.TotalComplex.AcyclicAssembly

/-!
# Coaugmentations of integer-indexed total complexes

A coaugmentation of column zero induces a map to the total complex with its native differential
`d₁ + (-1)^p d₂`. Exact coaugmented rows make this map a quasi-isomorphism whenever each
antidiagonal has only finitely many nonzero terms. In particular this applies when the horizontal
index is nonnegative and the vertical complexes have a common lower bound, of any integer value.
The construction is the integer-indexed analogue of `HomologicalComplex₂.totalCoaugmentation`
from `TauCeti.Algebra.Homology.TotalComplex.UpNat`, with the same native total differential.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)] {E : CochainComplex C ℤ}
  (η : E ⟶ K.X 0) (hη : η ≫ K.d 0 1 = 0)

/-- The coaugmentation of the total complex induced by a coaugmentation of column zero. -/
def totalCoaugmentationUpInt : E ⟶ K.total (ComplexShape.up ℤ) where
  f n := η.f n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
  comm' := by
    rintro n _ rfl
    rw [Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq K _ (ComplexShape.up_mk 0 1 rfl) n (n + 1) (by simp [add_comm]),
      d₂_eq K _ 0 (ComplexShape.up_mk n (n + 1) rfl) (n + 1) (by simp)]
    have h₁ : η.f n ≫ (K.d 0 1).f n = 0 := by
      rw [← HomologicalComplex.comp_f, hη, HomologicalComplex.zero_f]
    simp [reassoc_of% h₁]

/-- The total coaugmentation is the given column coaugmentation followed by the inclusion of
bidegree `(0,n)`. -/
@[simp]
lemma totalCoaugmentationUpInt_f (n : ℤ) :
    (K.totalCoaugmentationUpInt η hη).f n =
      η.f n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (by simp) := by rfl

/-- The total coaugmentation commutes with a morphism of bicomplexes. -/
@[reassoc (attr := simp)]
lemma totalCoaugmentationUpInt_total_map
    {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [L.HasTotal (ComplexShape.up ℤ)] (φ : K ⟶ L) :
    K.totalCoaugmentationUpInt η hη ≫ total.map φ (ComplexShape.up ℤ) =
      L.totalCoaugmentationUpInt (η ≫ φ.f 0)
        (by rw [Category.assoc, φ.comm, ← Category.assoc, hη, zero_comp]) := by
  ext n
  simp

section Row

variable [HasZeroObject C]

omit [K.HasTotal (ComplexShape.up ℤ)] in
/-- The coaugmentation of a horizontal row, from the single complex in degree zero. -/
def rowCoaugmentationUpInt (q : ℤ) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (E.X q) ⟶ K.flip.X q :=
  HomologicalComplex.mkHomFromSingle (η.f q) fun k hk ↦ by
    obtain rfl : k = 1 := by simpa using hk.symm
    simpa using HomologicalComplex.congr_hom hη q

omit [K.HasTotal (ComplexShape.up ℤ)] in
/-- In degree zero, the row coaugmentation is the component of the column coaugmentation. -/
@[reassoc (attr := simp)]
lemma rowCoaugmentationUpInt_f_zero (q : ℤ) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (E.X q)).inv ≫
      (K.rowCoaugmentationUpInt η hη q).f 0 = η.f q := by
  simp [rowCoaugmentationUpInt, HomologicalComplex.mkHomFromSingle_f]

end Row

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)] {E : CochainComplex C ℤ}
  (η : E ⟶ K.X 0) (hη : η ≫ K.d 0 1 = 0)

/-- Exact coaugmented rows make the coaugmentation into a total complex a quasi-isomorphism
when every antidiagonal has finitely many nonzero terms. -/
theorem quasiIso_totalCoaugmentationUpInt
    (hfin : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite)
    (hrows : ∀ q, QuasiIso (K.rowCoaugmentationUpInt η hη q)) :
    QuasiIso (K.totalCoaugmentationUpInt η hη) := by
  let S : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj E
  have hS (n : ℤ) : {p : ℤ | ¬ IsZero ((S.X p).X (n - p))}.Finite := by
    refine (Set.finite_singleton 0).subset fun p hp ↦ ?_
    by_contra hp'
    exact hp ((HomologicalComplex.eval C _ _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp'))
  have := hasTotal_of_finite_antidiagonals S hS
  let φ : S ⟶ K := HomologicalComplex.mkHomFromSingle η fun k hk ↦ by
    obtain rfl : k = 1 := by simpa using hk.symm
    exact hη
  have hφ : (HomologicalComplex.singleObjXSelf _ 0 E).inv ≫ φ.f 0 = η := by
    simp [φ, HomologicalComplex.mkHomFromSingle_f]
  have hφrows (q : ℤ) : QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ) := by
    let e := (HomologicalComplex.singleMapHomologicalComplex (eval C (ComplexShape.up ℤ) q)
      (ComplexShape.up ℤ) 0).app E
    have he : K.rowCoaugmentationUpInt η hη q =
        e.inv ≫ ((eval C _ q).mapHomologicalComplex _).map φ := by
      refine HomologicalComplex.from_single_hom_ext ?_
      suffices η.f q = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).inv.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom.f q ≫ η.f q by
        simpa [rowCoaugmentationUpInt, e, φ, HomologicalComplex.mkHomFromSingle_f] using this
      rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
        HomologicalComplex.id_f, Category.id_comp]
    have := hrows q
    rw [he] at this
    exact (quasiIso_iff_comp_left e.inv _).1 this
  have := quasiIso_total_map_of_rows_up_int φ hS hfin hφrows
  let α : E ⟶ S.total (ComplexShape.up ℤ) :=
    S.totalCoaugmentationUpInt (HomologicalComplex.singleObjXSelf _ 0 E).inv (by
      rw [HomologicalComplex.single_obj_d, comp_zero])
  have hα : IsIso α := by
    have hi (n : ℤ) : IsIso (S.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) :=
      isIso_ιTotal_of_isZero S 0 (fun p hp ↦
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hp) (by simp)
    have hi' (n : ℤ) : IsIso (α.f n) := by
      dsimp only [α]
      rw [totalCoaugmentationUpInt_f]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components α
  have he : α ≫ total.map φ (ComplexShape.up ℤ) = K.totalCoaugmentationUpInt η hη := by
    rw [totalCoaugmentationUpInt_total_map]
    congr 1
  rw [← he]
  infer_instance

end HomologicalComplex₂
