/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import TauCeti.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic
import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Bass's automorphism presentation of K₁

The Bass group of an additive category has a generator for each automorphism. Composition and
binary direct sum give addition, and transport along an isomorphism preserves the class.
A triangular automorphism whose diagonal blocks are automorphisms has class equal to the sum of
their classes. This gives additivity on split short exact sequences even when the automorphism
moves a chosen complement.
The presentation uses Mathlib’s integral module presentations, `Module.Relations`.

* `TauCeti.BassK1.of` is the class of an automorphism.
* `TauCeti.BassK1.lift` descends an invariant satisfying the three relations.
* `TauCeti.BassK1.map` applies a biproduct-preserving functor to representatives.

## References

* C. Weibel, *The K-book*, III, Lemma 1.6 and Corollary 1.6.3, for the presentation
  by automorphisms of finitely generated projective modules.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v v' v'' u u' u''

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

namespace BassK1

private abbrev Generators := (X : C) × (X ≅ X)

private def generator {X : C} (a : X ≅ X) : Generators C →₀ ℤ :=
  Finsupp.single ⟨X, a⟩ 1

private inductive Rel
  | iso {X Y : C} (a : X ≅ X) (b : Y ≅ Y) (e : X ≅ Y) (h : a.hom ≫ e.hom = e.hom ≫ b.hom)
  | comp {X : C} (a b : X ≅ X)
  | sum {X Y : C} (a : X ≅ X) (b : Y ≅ Y)

private abbrev relations : Module.Relations ℤ where
  G := Generators C
  R := Rel C
  relation
    | .iso a b _ _ => generator C a - generator C b
    | .comp a b => generator C (a ≪≫ b) - (generator C a + generator C b)
    | .sum a b => generator C (biprod.mapIso a b) - (generator C a + generator C b)

end BassK1

/-- The Bass group of automorphisms, with the composition, conjugacy and biproduct relations. -/
def BassK1 : Type (max u v) := (BassK1.relations C).Quotient
deriving AddCommGroup

namespace BassK1

variable {C}

/-- The class of the automorphism `a` in the Bass group. -/
def of {X : C} (a : X ≅ X) : BassK1 C :=
  (relations C).toQuotient (generator C a)

/-- An isomorphism intertwining two automorphisms identifies their Bass classes. -/
theorem of_congr {X Y : C} {a : X ≅ X} {b : Y ≅ Y} (e : X ≅ Y)
    (h : a.hom ≫ e.hom = e.hom ≫ b.hom) : of a = of b := by
  simpa only [relations, map_sub, sub_eq_zero, of, BassK1] using
    (relations C).toQuotient_relation (.iso a b e h)

/-- Conjugating an automorphism along a change of object preserves its class. -/
@[simp] theorem of_conjugate {X Y : C} (e : X ≅ Y) (a : X ≅ X) :
    of (e.symm ≪≫ a ≪≫ e) = of a :=
  of_congr e.symm (by simp)

/-- Composition of automorphisms adds their classes. -/
@[simp] theorem of_trans {X : C} (a b : X ≅ X) : of (a ≪≫ b) = of a + of b := by
  have h := (relations C).toQuotient_relation (.comp a b)
  simp only [relations, map_sub, map_add, sub_eq_zero] at h
  exact h

/-- The class of a block diagonal automorphism is the sum of the diagonal classes. -/
@[simp] theorem of_mapIso {X Y : C} (a : X ≅ X) (b : Y ≅ Y) :
    of (biprod.mapIso a b) = of a + of b := by
  have h := (relations C).toQuotient_relation (.sum a b)
  simp only [relations, map_sub, map_add, sub_eq_zero] at h
  exact h

@[simp] theorem of_refl (X : C) : of (Iso.refl X) = 0 := by
  simpa using (of_trans (Iso.refl X) (Iso.refl X)).symm

@[simp] theorem of_symm {X : C} (a : X ≅ X) : of a.symm = -of a := by
  apply eq_neg_of_add_eq_zero_left
  simpa using (of_trans a.symm a).symm

/-- Homomorphisms out of the Bass group agree if they agree on automorphism classes. -/
@[ext] theorem hom_ext {G : Type*} [AddCommGroup G] {f g : BassK1 C →+ G}
    (h : ∀ {X : C} (a : X ≅ X), f (of a) = g (of a)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact Module.Relations.Quotient.linearMap_ext (relations := relations C) fun ⟨_, a⟩ => h a

/-- Every class is represented by a single automorphism when the category has an object. -/
theorem exists_eq_of [Nonempty C] (x : BassK1 C) : ∃ (X : C) (a : X ≅ X), x = of a := by
  let S : AddSubgroup (BassK1 C) :=
    { carrier := {y | ∃ (X : C) (a : X ≅ X), y = of a}
      zero_mem' := ⟨_, Iso.refl (Classical.arbitrary C), (of_refl _).symm⟩
      add_mem' := by
        rintro _ _ ⟨X, a, rfl⟩ ⟨Y, b, rfl⟩
        exact ⟨_, _, (of_mapIso a b).symm⟩
      neg_mem' := by
        rintro _ ⟨X, a, rfl⟩
        exact ⟨_, _, (of_symm a).symm⟩ }
  have h : QuotientAddGroup.mk' S = 0 :=
    hom_ext fun a => (QuotientAddGroup.eq_zero_iff _).2 ⟨_, a, rfl⟩
  exact (QuotientAddGroup.eq_zero_iff x).1 (DFunLike.congr_fun h x)

variable {G : Type*} [AddCommGroup G]

/-- An invariant of automorphisms descends to the Bass group if it is invariant under
intertwining isomorphisms and additive for composition and biproducts. -/
def lift (f : ∀ {X : C}, (X ≅ X) → G)
    (hi : ∀ {X Y : C} (a : X ≅ X) (b : Y ≅ Y) (e : X ≅ Y),
      a.hom ≫ e.hom = e.hom ≫ b.hom → f a = f b)
    (hc : ∀ {X : C} (a b : X ≅ X), f (a ≪≫ b) = f a + f b)
    (hs : ∀ {X Y : C} (a : X ≅ X) (b : Y ≅ Y), f (biprod.mapIso a b) = f a + f b) :
    BassK1 C →+ G :=
  let s : (relations C).Solution G :=
    { var := fun p => f p.2
      linearCombination_var_relation := by
        intro r
        cases r with
        | iso a b e h => simp [relations, generator, hi a b e h]
        | comp a b => simp [relations, generator, hc]
        | sum a b => simp [relations, generator, hs] }
  s.fromQuotient.toAddMonoidHom

@[simp] theorem lift_of (f : ∀ {X : C}, (X ≅ X) → G) (hi hc hs) {X : C} (a : X ≅ X) :
    lift f hi hc hs (of a) = f a :=
  (Module.Relations.Solution.fromQuotient_toQuotient _ _).trans
    (Module.Relations.Solution.π_single _ _)

section Functor

variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]

/-- A functor preserving zero morphisms and binary biproducts induces a map on Bass groups. -/
def map : BassK1 C →+ BassK1 D :=
  lift (fun a => of (F.mapIso a))
    (fun a b e h => of_congr (F.mapIso e) (by
      simpa only [Functor.mapIso_hom, ← F.map_comp] using congrArg F.map h))
    (fun a b => by simp)
    (fun {X Y} a b => by
      rw [← of_mapIso]
      exact of_congr (F.mapBiprod X Y) (F.biprodComparison_natural a.hom b.hom))

@[simp] theorem map_of {X : C} (a : X ≅ X) : map F (of a) = of (F.mapIso a) :=
  lift_of _ _ _ _ _

@[simp] theorem map_id : map (𝟭 C) = AddMonoidHom.id _ :=
  hom_ext fun a => by simp [Functor.mapIso]

@[simp] theorem map_comp {E : Type u''} [Category.{v''} E] [HasZeroMorphisms E]
    [HasBinaryBiproducts E] (H : D ⥤ E) [H.PreservesZeroMorphisms] [PreservesBinaryBiproducts H] :
    map (F ⋙ H) = (map H).comp (map F) :=
  hom_ext fun a => by simp [Functor.mapIso]

/-- Naturally isomorphic functors induce the same homomorphism. -/
theorem map_congr {H : C ⥤ D} [H.PreservesZeroMorphisms] [PreservesBinaryBiproducts H]
    (e : F ≅ H) : map F = map H :=
  hom_ext fun a => by simpa only [map_of] using of_congr (e.app _) (e.hom.naturality a.hom)

/-- An equivalence of categories identifies their Bass groups. -/
def mapEquiv (e : C ≌ D) : BassK1 C ≃+ BassK1 D :=
  (map e.functor).toAddEquiv (map e.inverse)
    (by rw [← map_comp, ← map_congr _ e.unitIso, map_id])
    (by rw [← map_comp, map_congr _ e.counitIso, map_id])

@[simp] theorem mapEquiv_toAddMonoidHom (e : C ≌ D) :
    (mapEquiv e : BassK1 C →+ BassK1 D) = map e.functor := (rfl)

@[simp] theorem mapEquiv_symm_toAddMonoidHom (e : C ≌ D) :
    ((mapEquiv e).symm : BassK1 D →+ BassK1 C) = map e.inverse := (rfl)

@[simp] theorem mapEquiv_refl :
    mapEquiv (CategoryTheory.Equivalence.refl : C ≌ C) = AddEquiv.refl (BassK1 C) := by
  apply AddEquiv.toAddMonoidHom_injective
  simp only [AddEquiv.toAddMonoidHom_eq_coe, mapEquiv_toAddMonoidHom,
    AddEquiv.toAddMonoidHom_refl, CategoryTheory.Equivalence.refl_functor, map_id]

@[simp] theorem mapEquiv_trans {E : Type u''} [Category.{v''} E] [HasZeroMorphisms E]
    [HasBinaryBiproducts E] (e : C ≌ D) (f : D ≌ E) :
    mapEquiv (e.trans f) = (mapEquiv e).trans (mapEquiv f) := by
  apply AddEquiv.toAddMonoidHom_injective
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddEquiv.toAddMonoidHom_trans, mapEquiv_toAddMonoidHom,
    CategoryTheory.Equivalence.trans_functor, map_comp]

@[simp] theorem mapEquiv_symm (e : C ≌ D) :
    mapEquiv e.symm = (mapEquiv e).symm := by
  apply AddEquiv.toAddMonoidHom_injective
  simp only [AddEquiv.toAddMonoidHom_eq_coe, mapEquiv_toAddMonoidHom, mapEquiv_symm_toAddMonoidHom,
    CategoryTheory.Equivalence.symm_functor]

@[simp] theorem mapEquiv_of (e : C ≌ D) {X : C} (a : X ≅ X) :
    mapEquiv e (of a) = of (e.functor.mapIso a) := map_of _ _

@[simp] theorem mapEquiv_symm_of (e : C ≌ D) {Y : D} (b : Y ≅ Y) :
    (mapEquiv e).symm (of b) = of (e.inverse.mapIso b) := map_of _ _

end Functor

section Triangular

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A] {X Y : A}

/-- A unipotent block automorphism represents zero in the Bass group. -/
@[simp] theorem of_unipotentUpper (r : X ⟶ Y) : of (Biprod.unipotentUpper r) = 0 := by
  -- After adjoining a copy of Y, the elementary block is the commutator of
  -- the blocks from X to the new Y and from the new Y to the original Y.
  let p := Biprod.unipotentUpper ((biprod.fst : X ⊞ Y ⟶ X) ≫ r)
  let q := Biprod.unipotentLower (biprod.inr : Y ⟶ X ⊞ Y)
  have h : p ≪≫ q = q ≪≫ p ≪≫ biprod.mapIso (Biprod.unipotentUpper r) (Iso.refl Y) := by
    apply Iso.ext
    ext <;> simp [p, q, Biprod.ofComponents, Category.assoc]
  have hc := congrArg of h
  simp only [of_trans, of_mapIso, of_refl, add_zero] at hc
  apply add_left_cancel (a := of q + of p)
  simpa [add_assoc, add_comm, add_left_comm] using hc.symm

/-- A block triangular automorphism whose diagonal blocks are automorphisms has class equal to the
sum of their classes, independently of the off-diagonal morphism. The block indices here follow
Mathlib's `Biprod.ofComponents`. -/
theorem of_upperTriangular (e : X ⊞ Y ≅ X ⊞ Y) (a : X ≅ X) (b : Y ≅ Y) (r : X ⟶ Y)
    (h : e.hom = Biprod.ofComponents a.hom r 0 b.hom) : of e = of a + of b := by
  have he : e = biprod.mapIso a b ≪≫ Biprod.unipotentUpper (a.inv ≫ r) := by
    apply Iso.ext
    ext <;> simp [h, Biprod.ofComponents]
  simp [he]

/-- A lower unipotent block also represents zero in the Bass group. -/
@[simp] theorem of_unipotentLower (r : Y ⟶ X) : of (Biprod.unipotentLower r) = 0 := by
  rw [← of_unipotentUpper r]
  apply of_congr (biprod.braiding X Y)
  ext <;> simp [Biprod.ofComponents, biprod.braiding]

/-- The lower triangular block formula, with morphisms indexed as in `Biprod.ofComponents`. -/
theorem of_lowerTriangular (e : X ⊞ Y ≅ X ⊞ Y) (a : X ≅ X) (b : Y ≅ Y) (r : Y ⟶ X)
    (h : e.hom = Biprod.ofComponents a.hom 0 r b.hom) : of e = of a + of b := by
  have he : e = biprod.mapIso a b ≪≫ Biprod.unipotentLower (b.inv ≫ r) := by
    apply Iso.ext
    ext <;> simp [h, Biprod.ofComponents]
  simp [he]

/-- For an automorphism of a split short exact sequence, the middle class is the sum of the
outer classes. The automorphism may move the chosen splitting. -/
theorem _root_.CategoryTheory.ShortComplex.Splitting.bassK1_eq_add {S : ShortComplex A}
    (s : S.Splitting) (e : S ≅ S) :
    of (ShortComplex.π₂.mapIso e) =
      of (ShortComplex.π₁.mapIso e) + of (ShortComplex.π₃.mapIso e) := by
  let i := s.isoBinaryBiproduct
  let b := ShortComplex.π₂.mapIso e
  calc
    of b = of (i.symm ≪≫ b ≪≫ i) := (of_conjugate i b).symm
    _ = _ := by
      apply of_lowerTriangular _ _ _ (s.s ≫ e.hom.τ₂ ≫ s.r)
      ext <;> simp [i, b, Biprod.ofComponents, ← e.hom.comm₁₂_assoc, e.hom.comm₂₃]

end Triangular

end BassK1

end TauCeti
