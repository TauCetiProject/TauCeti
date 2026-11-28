/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TauCeti.ModelTheory.Substructures.Cardinality

/-!
# Cardinal-bounded cofiltered closure of arrows

`Set.cofilteredArrowClosure` enlarges a set of arrows in a cofiltered category
by adding endpoint identities, composites, and chosen cone and equalizing arrows. Unlike
full subcategory closure, it need not add all morphisms between its objects. It is monotone
in the generating set. `Set.mem_cofilteredArrowClosure_iff` characterizes membership by closed
supersets, `Set.cofilteredArrowClosure_idem` gives idempotence, and
`Set.mk_cofilteredArrowClosure_le` bounds the cardinal by `max ℵ₀ #s` for generators `s`.

The construction uses Mathlib's `IsCofiltered.minToLeft`, `IsCofiltered.minToRight`,
`IsCofiltered.eqHom` and Tau Ceti's `FirstOrder.Language.Substructure.lift_mk_closure_le`.
It gives the closure step for the cardinal induction on cofiltered diagrams in Scholze,
*Étale cohomology of diamonds*, Lemma 11.22 and Proposition 11.23.
-/

public section

open Cardinal
namespace Set

open CategoryTheory CategoryTheory.IsCofiltered

variable {C : Type*} [Category* C] [IsCofilteredOrEmpty C]

private def arrowLanguage : FirstOrder.Language :=
  ⟨fun n ↦ {_i : Fin 6 // n = 2}, fun _ ↦ Empty⟩

private noncomputable def arrowOp (i : Fin 6) (a b : Arrow C) : Arrow C := by
  classical
  exact ![Arrow.mk (𝟙 a.left), Arrow.mk (𝟙 a.right),
    if h : a.right = b.left then Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom) else a,
    Arrow.mk (minToLeft a.left b.left), Arrow.mk (minToRight a.left b.left),
    if h : a.left = b.left ∧ a.right = b.right then
      Arrow.mk (eqHom a.hom (eqToHom h.1 ≫ b.hom ≫ eqToHom h.2.symm)) else a] i

private noncomputable instance : arrowLanguage.Structure (Arrow C) where
  funMap f x := arrowOp f.val (x ⟨0, f.property ▸ Nat.zero_lt_two⟩)
    (x ⟨1, f.property ▸ Nat.one_lt_two⟩)
  RelMap f := Empty.elim f

/-- The least set containing `s` closed under endpoint identities, composition, and the
chosen pair-cone and equalizing arrows of the ambient cofiltered category.
See Scholze, *Étale cohomology of diamonds*, Lemma 11.22. -/
noncomputable def cofilteredArrowClosure (s : Set (Arrow C)) : Set (Arrow C) :=
  FirstOrder.Language.Substructure.closure arrowLanguage s

variable {s : Set (Arrow C)} {X Y Z : C}

/-- The generating arrows are included in the closure as a set of ambient arrows. -/
theorem subset_cofilteredArrowClosure : s ⊆ cofilteredArrowClosure s := by
  exact FirstOrder.Language.Substructure.subset_closure

/-- Enlarging the generators enlarges the cofiltered arrow closure. -/
theorem cofilteredArrowClosure_mono : Monotone (cofilteredArrowClosure (C := C)) := by
  exact SetLike.coe_mono.comp (FirstOrder.Language.Substructure.closure arrowLanguage).monotone

private theorem arrowOp_mem (i : Fin 6) {a b : Arrow C}
    (ha : a ∈ cofilteredArrowClosure s) (hb : b ∈ cofilteredArrowClosure s) :
    arrowOp i a b ∈ cofilteredArrowClosure s := by
  let S := FirstOrder.Language.Substructure.closure arrowLanguage s
  have hargs : ∀ j : Fin 2, (![a, b] : Fin 2 → Arrow C) j ∈ S :=
    Fin.forall_fin_two.2 ⟨ha, hb⟩
  exact S.fun_mem (n := 2) ⟨i, rfl⟩ ![a, b] hargs

/-- The identity of the source of an arrow in the closure belongs to the closure. -/
theorem id_left_mem_cofilteredArrowClosure {a : Arrow C} (ha : a ∈ cofilteredArrowClosure s) :
    Arrow.mk (𝟙 a.left) ∈ cofilteredArrowClosure s := by
  exact arrowOp_mem 0 ha ha

/-- The identity of the target of an arrow in the closure belongs to the closure. -/
theorem id_right_mem_cofilteredArrowClosure {a : Arrow C} (ha : a ∈ cofilteredArrowClosure s) :
    Arrow.mk (𝟙 a.right) ∈ cofilteredArrowClosure s := by
  exact arrowOp_mem 1 ha ha

/-- Composites of arrows in the closure belong to the closure. -/
theorem comp_mem_cofilteredArrowClosure {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Arrow.mk f ∈ cofilteredArrowClosure s) (hg : Arrow.mk g ∈ cofilteredArrowClosure s) :
    Arrow.mk (f ≫ g) ∈ cofilteredArrowClosure s := by
  classical
  have h : (if e : Y = Y then Arrow.mk (f ≫ eqToHom e ≫ g) else Arrow.mk f) ∈
      cofilteredArrowClosure s := arrowOp_mem 2 hf hg
  rw [dite_eq_left (Eq.refl Y)] at h
  simpa only [eqToHom_refl, Category.id_comp] using h

/-- The chosen cone over two objects whose identities lie in the closure has its left leg in
the closure. -/
theorem minToLeft_mem_cofilteredArrowClosure (hX : Arrow.mk (𝟙 X) ∈ cofilteredArrowClosure s)
    (hY : Arrow.mk (𝟙 Y) ∈ cofilteredArrowClosure s) :
    Arrow.mk (minToLeft X Y) ∈ cofilteredArrowClosure s := by
  exact arrowOp_mem 3 hX hY

/-- The chosen cone over two objects whose identities lie in the closure has its right leg in
the closure. -/
theorem minToRight_mem_cofilteredArrowClosure (hX : Arrow.mk (𝟙 X) ∈ cofilteredArrowClosure s)
    (hY : Arrow.mk (𝟙 Y) ∈ cofilteredArrowClosure s) :
    Arrow.mk (minToRight X Y) ∈ cofilteredArrowClosure s := by
  exact arrowOp_mem 4 hX hY

/-- The chosen arrow equalizing two parallel arrows in the closure belongs to the closure. -/
theorem eqHom_mem_cofilteredArrowClosure {f g : X ⟶ Y}
    (hf : Arrow.mk f ∈ cofilteredArrowClosure s) (hg : Arrow.mk g ∈ cofilteredArrowClosure s) :
    Arrow.mk (eqHom f g) ∈ cofilteredArrowClosure s := by
  classical
  have h : (if e : X = X ∧ Y = Y then
      Arrow.mk (eqHom f (eqToHom e.1 ≫ g ≫ eqToHom e.2.symm)) else Arrow.mk f) ∈
      cofilteredArrowClosure s := arrowOp_mem 5 hf hg
  have he : X = X ∧ Y = Y := ⟨rfl, rfl⟩
  rw [dite_eq_left he] at h
  have hg' : eqToHom he.1 ≫ g ≫ eqToHom he.2.symm = g := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rwa [hg'] at h

/-- The cofiltered arrow closure is contained in every set that contains the generators
and is closed under the chosen cofiltered operations. -/
theorem cofilteredArrowClosure_subset {t : Set (Arrow C)} (hst : s ⊆ t)
    (hright : ∀ a ∈ t, Arrow.mk (𝟙 a.right) ∈ t)
    (hcomp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z},
      Arrow.mk f ∈ t → Arrow.mk g ∈ t → Arrow.mk (f ≫ g) ∈ t)
    (hminLeft : ∀ X Y : C, Arrow.mk (𝟙 X) ∈ t → Arrow.mk (𝟙 Y) ∈ t →
      Arrow.mk (minToLeft X Y) ∈ t)
    (hminRight : ∀ X Y : C, Arrow.mk (𝟙 X) ∈ t → Arrow.mk (𝟙 Y) ∈ t →
      Arrow.mk (minToRight X Y) ∈ t)
    (heq : ∀ {X Y : C} {f g : X ⟶ Y},
      Arrow.mk f ∈ t → Arrow.mk g ∈ t → Arrow.mk (eqHom f g) ∈ t) :
    s.cofilteredArrowClosure ⊆ t := by
  classical
  -- The right endpoint of an equalizing arrow is the common source.
  have hleft (a : Arrow C) (ha : a ∈ t) : Arrow.mk (𝟙 a.left) ∈ t := by
    have ha' : Arrow.mk a.hom ∈ t := (Arrow.mk_eq a).symm ▸ ha
    exact hright _ (heq ha' ha')
  have hop (i : Fin 6) (a b : Arrow C) (ha : a ∈ t) (hb : b ∈ t) : arrowOp i a b ∈ t := by
    fin_cases i
    · exact hleft a ha
    · exact hright a ha
    · have h : (if e : a.right = b.left then Arrow.mk (a.hom ≫ eqToHom e ≫ b.hom)
          else a) ∈ t := by
        by_cases e : a.right = b.left
        · rw [dite_eq_left e]
          have hg : Arrow.mk (eqToHom e ≫ b.hom) ∈ t := by
            rwa [Arrow.arrow_mk_eqToHom_comp, Arrow.mk_eq]
          exact hcomp (by rwa [Arrow.mk_eq]) hg
        · rwa [dite_eq_right e]
      exact h
    · exact hminLeft a.left b.left (hleft a ha) (hleft b hb)
    · exact hminRight a.left b.left (hleft a ha) (hleft b hb)
    · have h : (if e : a.left = b.left ∧ a.right = b.right then
          Arrow.mk (eqHom a.hom (eqToHom e.1 ≫ b.hom ≫ eqToHom e.2.symm)) else a) ∈ t := by
        by_cases e : a.left = b.left ∧ a.right = b.right
        · rw [dite_eq_left e]
          have hg : Arrow.mk (eqToHom e.1 ≫ b.hom ≫ eqToHom e.2.symm) ∈ t := by
            rwa [← Category.assoc, Arrow.arrow_mk_comp_eqToHom,
              Arrow.arrow_mk_eqToHom_comp, Arrow.mk_eq]
          exact heq (by rwa [Arrow.mk_eq]) hg
        · rwa [dite_eq_right e]
      exact h
  let T : arrowLanguage.Substructure (Arrow C) :=
    ⟨t, fun f x hx ↦ hop f.val _ _ (hx _) (hx _)⟩
  have hT : s ⊆ T := hst
  exact FirstOrder.Language.Substructure.closure_le.mpr hT

/-- An arrow belongs to the cofiltered closure of `s` exactly when it belongs to every superset
of `s` closed under target identities, composition, and the chosen cone and equalizing arrows. -/
theorem mem_cofilteredArrowClosure_iff {a : Arrow C} : a ∈ s.cofilteredArrowClosure ↔
    ∀ t : Set (Arrow C), s ⊆ t →
      (∀ b ∈ t, Arrow.mk (𝟙 b.right) ∈ t) →
      (∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z},
        Arrow.mk f ∈ t → Arrow.mk g ∈ t → Arrow.mk (f ≫ g) ∈ t) →
      (∀ X Y : C, Arrow.mk (𝟙 X) ∈ t → Arrow.mk (𝟙 Y) ∈ t → Arrow.mk (minToLeft X Y) ∈ t) →
      (∀ X Y : C, Arrow.mk (𝟙 X) ∈ t → Arrow.mk (𝟙 Y) ∈ t → Arrow.mk (minToRight X Y) ∈ t) →
      (∀ {X Y : C} {f g : X ⟶ Y},
        Arrow.mk f ∈ t → Arrow.mk g ∈ t → Arrow.mk (eqHom f g) ∈ t) → a ∈ t := by
  constructor
  · intro ha t hst hright hcomp hminLeft hminRight heq
    exact cofilteredArrowClosure_subset hst hright hcomp hminLeft hminRight heq ha
  · intro ha
    exact ha _ subset_cofilteredArrowClosure (fun _ h ↦ id_right_mem_cofilteredArrowClosure h)
      comp_mem_cofilteredArrowClosure (fun _ _ ↦ minToLeft_mem_cofilteredArrowClosure)
      (fun _ _ ↦ minToRight_mem_cofilteredArrowClosure) eqHom_mem_cofilteredArrowClosure

/-- Applying cofiltered arrow closure twice gives the same set as applying it once. -/
@[simp]
theorem cofilteredArrowClosure_idem (s : Set (Arrow C)) :
    s.cofilteredArrowClosure.cofilteredArrowClosure = s.cofilteredArrowClosure := by
  open FirstOrder.Language.Substructure in
  have h : closure arrowLanguage (closure arrowLanguage s : Set (Arrow C)) =
      closure arrowLanguage s := closure_eq_of_le Subset.rfl subset_closure
  exact congrArg SetLike.coe h

/-- The closure of the empty set of arrows is empty. -/
@[simp]
theorem cofilteredArrowClosure_empty : (∅ : Set (Arrow C)).cofilteredArrowClosure = ∅ := by
  apply eq_empty_of_subset_empty
  apply cofilteredArrowClosure_subset <;> simp

/-- Closing a set of arrows under the chosen cofiltered operations takes at most
`max ℵ₀ #s` arrows. -/
theorem mk_cofilteredArrowClosure_le (s : Set (Arrow C)) :
    #s.cofilteredArrowClosure ≤ max ℵ₀ #s := by
  have hinj : Function.Injective
      (fun f : Σ n, arrowLanguage.Functions n ↦ f.2.val) := by
    rintro ⟨_, ⟨i, rfl⟩⟩ ⟨_, ⟨j, rfl⟩⟩ rfl
    rfl
  have hsym : #(Σ n, arrowLanguage.Functions n) ≤ ℵ₀ :=
    (mk_le_of_injective hinj).trans mk_le_aleph0
  have hs : lift.{0} #s ≤ max ℵ₀ #s := by
    rw [lift_uzero]
    exact le_max_right _ _
  have hc : lift.{0} #s.cofilteredArrowClosure ≤ max ℵ₀ #s :=
    FirstOrder.Language.Substructure.lift_mk_closure_le (L := arrowLanguage) (le_max_left _ _)
      ((lift_le_aleph0.mpr hsym).trans (le_max_left _ _)) hs
  rwa [lift_uzero] at hc

end Set
