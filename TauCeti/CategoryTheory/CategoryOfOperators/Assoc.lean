/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.CategoryTheory.Category.Pointed.Fin

/-!
# The category of operators of the associative operad

The category `Assoc^⊗` has one object `⟨n⟩` for each natural number `n`, like `Fin_*`. A morphism
`⟨m⟩ ⟶ ⟨n⟩` is a pointed map `f : ⟨m⟩ ⟶ ⟨n⟩` of `Fin_*` together with a linear order on each
fibre `f⁻¹{j}` over an element `j` of `⟨n⟩` other than the basepoint, and composites carry the
lexicographic orders. This is the category of operators of the associative operad: its nerve over
`N(Fin_*)` is the associative `∞`-operad, over which monoidal quasicategories are coCartesian
fibrations of `∞`-operads.

A linear order on a finite set is the same as a list enumerating it without repetitions. So we
record a morphism by its underlying map `Hom.base` together with, for each `j`, the word
`Hom.word j` listing the fibre over `j` (indexing the elements of `⟨n⟩` other than the basepoint
by `Fin n`, the element `j : Fin n` standing for `j.succ`). Composition concatenates words: the
word of `f ≫ g` over `k` is the concatenation, along the word of `g` over `k`, of the words of
`f`. This is exactly the lexicographic order of Lurie's definition.

The forgetful functor `Assoc.toFinPointed : Assoc^⊗ ⥤ Fin_*` is full, since every fibre can be
ordered (`Assoc.Hom.ofBase` orders them increasingly). Over an inert map every fibre has exactly
one element, so the order is unique, and every morphism over an inert map is strongly
coCartesian for `Assoc.toFinPointed`: these are the coCartesian lifts of inert maps required of an
`∞`-operad.

## Main definitions

* `TauCeti.Assoc`: the category of operators `Assoc^⊗` of the associative operad.
* `TauCeti.Assoc.Hom.word`: the word, that is the ordered fibre, of a morphism over an element.
* `TauCeti.Assoc.toFinPointed`: the forgetful functor `Assoc^⊗ ⥤ Fin_*`.
* `TauCeti.Assoc.Hom.ofBase`: the lift of a map of `Fin_*` ordering every fibre increasingly.

## Main results

* `TauCeti.Assoc.homLiftEquiv`: lifts over a fixed pointed map decompose into single-output lifts.
* `TauCeti.Assoc.Hom.ext_of_isInert`: a morphism over an inert map is determined by that map.
* `TauCeti.Assoc.Hom.epi_of_isInert`: a morphism over an inert map is an epimorphism.
* `TauCeti.Assoc.isStronglyCocartesian_of_isInert`: every morphism over an inert map is strongly
  coCartesian for `Assoc.toFinPointed`.

## References

* J. Lurie, *Higher Algebra*, Definition 4.1.1.3.
-/

public section

universe u

open CategoryTheory Functor

namespace TauCeti

/-- The category of operators `Assoc^⊗` of the associative operad: an object `⟨n⟩` is a natural
number `n`, standing for the pointed set `Fin (n + 1)` of `Fin_*`. -/
@[ext]
structure Assoc : Type u where
  /-- The object `⟨n⟩` of `Assoc^⊗`. -/
  mk ::
  /-- The number of elements of the pointed set other than its basepoint. -/
  len : ℕ

namespace Assoc

@[simp]
lemma mk_len (X : Assoc.{u}) : mk X.len = X := rfl

/-- A morphism `⟨m⟩ ⟶ ⟨n⟩` of `Assoc^⊗`: a pointed map `base` of `Fin_*` together with a linear
order on each fibre over an element `j.succ` other than the basepoint, given as the word
`word j` listing that fibre without repetitions. -/
structure Hom (X Y : Assoc.{u}) : Type u where
  /-- The morphism given by a map of `Fin_*` and an enumeration of each of its fibres. -/
  mk ::
  /-- The underlying map of finite pointed sets. -/
  base : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len
  /-- The fibre of `base` over `j.succ`, listed in its chosen order. -/
  word : Fin Y.len → List (Fin X.len)
  mem_word_iff (i : Fin X.len) (j : Fin Y.len) : i ∈ word j ↔ base.toFun i.succ = j.succ
  nodup_word (j : Fin Y.len) : (word j).Nodup

namespace Hom

variable {X Y Z : Assoc.{u}}

lemma base_toFun_succ_eq_zero_iff (f : Hom X Y) (i : Fin X.len) :
    f.base.toFun i.succ = 0 ↔ ∀ j, i ∉ f.word j := by
  simp only [f.mem_word_iff]
  refine ⟨fun h j h' ↦ Fin.succ_ne_zero j (h'.symm.trans h), fun h ↦ ?_⟩
  obtain h0 | ⟨j, hj⟩ := Fin.eq_zero_or_eq_succ (f.base.toFun i.succ)
  · exact h0
  · exact absurd hj (h j)

/-- The words determine the underlying map, before installing the category structure. -/
private lemma ext {f g : Hom X Y} (h : ∀ j, f.word j = g.word j) : f = g := by
  have hb : f.base = g.base := by
    refine FinPointed.hom_ext fun i ↦ ?_
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      obtain h0 | ⟨j, hj⟩ := Fin.eq_zero_or_eq_succ (f.base.toFun i.succ)
      · rw [h0, eq_comm, g.base_toFun_succ_eq_zero_iff]
        simpa [← h] using (f.base_toFun_succ_eq_zero_iff i).1 h0
      · rw [hj, eq_comm, ← g.mem_word_iff, ← h, f.mem_word_iff, hj]
  cases f
  cases g
  simp only at hb h
  subst hb
  obtain rfl := funext h
  rfl

end Hom

/-- The composition of `Assoc^⊗`: the word of `f ≫ g` over `k` concatenates, along the word of
`g` over `k`, the words of `f`; the identity has the one-letter word `j` over `j`. -/
instance : SmallCategory Assoc.{u} where
  Hom := Hom
  id _ :=
    { base := 𝟙 _
      word j := [j]
      mem_word_iff i j := by simp
      nodup_word _ := List.nodup_singleton _ }
  comp {_ _ Z} f g :=
    { base := f.base ≫ g.base
      word k := (g.word k).flatMap f.word
      mem_word_iff i k := by
        simp only [List.mem_flatMap, g.mem_word_iff, f.mem_word_iff, FinPointed.comp_toFun]
        refine ⟨fun ⟨_, hj, hi⟩ ↦ hi ▸ hj, fun h ↦ ?_⟩
        obtain ⟨j, hj⟩ := FinPointed.exists_toFun_eq_succ_of_toFun_toFun_eq_succ h
        exact ⟨j, hj ▸ h, hj⟩
      nodup_word k := by
        refine List.nodup_flatMap.2 ⟨fun j _ ↦ f.nodup_word j, (g.nodup_word k).imp ?_⟩
        intro j j' hne i hi hi'
        rw [f.mem_word_iff] at hi hi'
        exact hne (Fin.succ_injective _ (hi.symm.trans hi')) }
  id_comp f := by exact Hom.ext fun _ ↦ List.flatMap_singleton' _
  comp_id f := by exact Hom.ext fun _ ↦ List.flatMap_singleton _ _
  assoc f g h := by exact Hom.ext fun _ ↦ List.flatMap_assoc.symm

variable {X Y Z : Assoc.{u}}

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : ∀ j, f.word j = g.word j) : f = g :=
  Hom.ext h

@[simp]
lemma id_base : Hom.base (𝟙 X) = 𝟙 _ := rfl

@[simp]
lemma id_word (j : Fin X.len) : Hom.word (𝟙 X) j = [j] := rfl

@[simp]
lemma comp_base (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base := rfl

@[simp]
lemma comp_word (f : X ⟶ Y) (g : Y ⟶ Z) (k : Fin Z.len) :
    (f ≫ g).word k = (g.word k).flatMap f.word :=
  rfl

/-- The forgetful functor `Assoc^⊗ ⥤ Fin_*`, sending `⟨n⟩` to `⟨n⟩` and a morphism to its
underlying map, forgetting the orders of the fibres. The body is exposed so that
`toFinPointed.obj X` is visibly `FinPointed.mk X.len`, the type of the underlying maps. -/
@[expose]
def toFinPointed : Assoc.{u} ⥤ FinPointed.{u} where
  obj X := FinPointed.mk X.len
  map f := f.base

@[simp]
lemma toFinPointed_obj (X : Assoc.{u}) : toFinPointed.obj X = FinPointed.mk X.len := (rfl)

@[simp]
lemma toFinPointed_map (f : X ⟶ Y) : toFinPointed.map f = f.base := (rfl)

/-- Every morphism lies over its underlying map. -/
instance isHomLift_base (f : X ⟶ Y) : toFinPointed.IsHomLift f.base f :=
  inferInstanceAs (toFinPointed.IsHomLift (toFinPointed.map f) f)

/-- A morphism lies over a map of `Fin_*` exactly when that map is its underlying map. -/
lemma isHomLift_iff {f : X ⟶ Y} {g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len} :
    toFinPointed.IsHomLift g f ↔ f.base = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ isHomLift_base f⟩
  -- Restate `h` over `toFinPointed.obj X` and `toFinPointed.obj Y`, as
  -- `IsHomLift.eq_of_isHomLift` requires.
  have : toFinPointed.IsHomLift (R := toFinPointed.obj X) (S := toFinPointed.obj Y) g f := h
  exact (IsHomLift.eq_of_isHomLift (p := toFinPointed) g f).symm

/-- The canonical inert projection selecting the output `j`. -/
def ρ (j : Fin Y.len) : Y ⟶ mk 1 where
  base := FinPointed.ρ j
  word _ := [j]
  mem_word_iff i k := by
    have : k = 0 := Subsingleton.elim _ _
    subst k
    simp [FinPointed.ρ_toFun, Fin.ext_iff]
  nodup_word _ := List.nodup_singleton _

@[simp]
lemma ρ_base (j : Fin Y.len) : (ρ j).base = FinPointed.ρ j := (rfl)

@[simp]
lemma ρ_word (j : Fin Y.len) (k : Fin 1) : (ρ j).word k = [j] := (rfl)

/-- Lifts of a fixed pointed map are equivalent to families of its single-output lifts.
The forward map postcomposes with the canonical inert projections; the inverse assembles
one ordered fibre from each member of the family. This includes an empty target. -/
def homLiftEquiv (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len) :
    {f : X ⟶ Y // toFinPointed.IsHomLift g f} ≃
      ((j : Fin Y.len) → {f : X ⟶ mk 1 //
        toFinPointed.IsHomLift (g ≫ FinPointed.ρ j) f}) where
  toFun f j := ⟨f.val ≫ ρ j, isHomLift_iff.2 (by
    simp [isHomLift_iff.1 f.property])⟩
  invFun f := ⟨
    { base := g
      word j := (f j).val.word 0
      mem_word_iff i j := by
        rw [(f j).val.mem_word_iff, isHomLift_iff.1 (f j).property]
        simp [FinPointed.ρ_toFun]
      nodup_word j := (f j).val.nodup_word 0 }, isHomLift_iff.2 rfl⟩
  left_inv f := Subtype.ext (hom_ext fun j ↦ by simp)
  right_inv f := by
    funext j
    apply Subtype.ext
    apply hom_ext
    intro k
    have : k = 0 := Subsingleton.elim _ _
    subst k
    simp

@[simp]
lemma homLiftEquiv_apply_val
    (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len)
    (f : {f : X ⟶ Y // toFinPointed.IsHomLift g f}) (j : Fin Y.len) :
    (homLiftEquiv g f j).val = f.val ≫ ρ j := (rfl)

@[simp]
lemma homLiftEquiv_symm_apply_word
    (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len)
    (f : (j : Fin Y.len) → {f : X ⟶ mk 1 //
      toFinPointed.IsHomLift (g ≫ FinPointed.ρ j) f}) (j : Fin Y.len) :
    ((homLiftEquiv g).symm f).val.word j = (f j).val.word 0 := (rfl)

namespace Hom

/-- The lift of a map of `Fin_*` to `Assoc^⊗` ordering every fibre increasingly. -/
def ofBase (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len) : X ⟶ Y where
  base := f
  word j := (List.finRange X.len).filter fun i ↦ f.toFun i.succ = j.succ
  mem_word_iff i j := by simp
  nodup_word _ := (List.nodup_finRange _).filter _

@[simp]
lemma ofBase_base (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len) : (ofBase f).base = f :=
  (rfl)

lemma ofBase_word (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len) (j : Fin Y.len) :
    (ofBase f).word j = (List.finRange X.len).filter fun i ↦ f.toFun i.succ = j.succ :=
  (rfl)

/-- Over an inert map, every fibre is a one-letter word. -/
lemma exists_word_eq_singleton_of_isInert {f : X ⟶ Y} (hf : f.base.IsInert) (j : Fin Y.len) :
    ∃ i, f.word j = [i] := by
  obtain ⟨i', hi', huniq⟩ := (FinPointed.Hom.isInert_iff _).1 hf j.succ (Fin.succ_ne_zero j)
  obtain ⟨i, rfl⟩ : ∃ i : Fin X.len, i.succ = i' := Fin.exists_succ_eq.2 fun h ↦
    Fin.succ_ne_zero j (by rw [← hi', h, FinPointed.Hom.map_zero])
  refine ⟨i, List.Perm.eq_singleton ((List.perm_ext_iff_of_nodup (f.nodup_word j)
    (List.nodup_singleton i)).2 fun i'' ↦ ?_)⟩
  rw [f.mem_word_iff, List.mem_singleton]
  exact ⟨fun h ↦ Fin.succ_injective _ (huniq _ h), fun h ↦ h ▸ hi'⟩

/-- A morphism of `Assoc^⊗` over an inert map is determined by that map: its fibres have one
element each, so they carry only one order. -/
lemma ext_of_isInert {f g : X ⟶ Y} (h : f.base = g.base) (hf : f.base.IsInert) : f = g := by
  refine hom_ext fun j ↦ ?_
  obtain ⟨i, hi⟩ := exists_word_eq_singleton_of_isInert hf j
  obtain ⟨i', hi'⟩ := exists_word_eq_singleton_of_isInert (h ▸ hf) j
  have : i ∈ g.word j := (g.mem_word_iff i j).2 (h ▸ (f.mem_word_iff i j).1 (by simp [hi]))
  rw [hi'] at this
  rw [hi, hi', List.mem_singleton.1 this]

/-- Precomposing with a morphism whose words are the letters `σ j` relabels words along `σ`. -/
lemma comp_word_of_word_eq_singleton {φ : X ⟶ Y} {σ : Fin Y.len → Fin X.len}
    (hσ : ∀ j, φ.word j = [σ j]) (ψ : Y ⟶ Z) (k : Fin Z.len) :
    (φ ≫ ψ).word k = (ψ.word k).map σ := by
  rw [comp_word, List.map_eq_flatMap]
  exact List.flatMap_congr fun j _ ↦ hσ j

/-- The letters `σ j` forming the one-letter words of a morphism are distinct. -/
lemma injective_of_word_eq_singleton {φ : X ⟶ Y} {σ : Fin Y.len → Fin X.len}
    (hσ : ∀ j, φ.word j = [σ j]) : σ.Injective := fun j j' h ↦ by
  have hj := (φ.mem_word_iff (σ j) j).1 (by simp [hσ])
  have hj' := (φ.mem_word_iff (σ j') j').1 (by simp [hσ])
  exact Fin.succ_injective _ (hj.symm.trans (h ▸ hj'))

/-- A morphism of `Assoc^⊗` over an inert map is an epimorphism: precomposing with it relabels
the words along an injective map. -/
lemma epi_of_isInert {φ : X ⟶ Y} (hφ : φ.base.IsInert) : Epi φ := by
  choose σ hσ using exists_word_eq_singleton_of_isInert hφ
  refine ⟨fun ψ ψ' h ↦ hom_ext fun k ↦ List.map_injective_iff.2
    (injective_of_word_eq_singleton hσ) ?_⟩
  rw [← comp_word_of_word_eq_singleton hσ, ← comp_word_of_word_eq_singleton hσ, h]

end Hom

/-- Every morphism of `Assoc^⊗` over an inert map of `Fin_*` is strongly coCartesian for the
forgetful functor `Assoc^⊗ ⥤ Fin_*`. -/
theorem isStronglyCocartesian_of_isInert (φ : X ⟶ Y) (hφ : φ.base.IsInert) :
    toFinPointed.IsStronglyCocartesian φ.base φ := by
  choose σ hσ using Hom.exists_word_eq_singleton_of_isInert hφ
  have hmem (j : Fin Y.len) : φ.base.toFun (σ j).succ = j.succ :=
    (φ.mem_word_iff _ _).1 (by simp [hσ])
  refine ⟨fun {Z} g φ' hl ↦ ?_⟩
  have hφ' : φ'.base = φ.base ≫ g := isHomLift_iff.1 hl
  -- The partial inverse of `σ`, sending `i` to the element `j` with `φ (i + 1) = j + 1`.
  let τ : Fin X.len → Option (Fin Y.len) := fun i ↦ finSuccEquiv Y.len (φ.base.toFun i.succ)
  have hτ {i : Fin X.len} {j : Fin Y.len} : τ i = some j ↔ φ.base.toFun i.succ = j.succ := by
    simp only [τ, ← finSuccEquiv_succ, (finSuccEquiv Y.len).apply_eq_iff_eq]
  have hτσ {i : Fin X.len} {j : Fin Y.len} (h : τ i = some j) : σ j = i := by
    rw [hτ, ← φ.mem_word_iff, hσ, List.mem_singleton] at h
    exact h.symm
  -- Every letter `i` of a word of `φ'` is sent by `φ` to some `j + 1`.
  have hcover {k : Fin Z.len} {i : Fin X.len} (hi : i ∈ φ'.word k) : ∃ j, τ i = some j := by
    rw [φ'.mem_word_iff, hφ', FinPointed.comp_toFun] at hi
    obtain ⟨j, hj⟩ := FinPointed.exists_toFun_eq_succ_of_toFun_toFun_eq_succ hi
    exact ⟨j, hτ.2 hj⟩
  -- The factorization `χ` of `φ'` through `φ` reads the words of `φ'` along `τ`.
  let χ : Y ⟶ Z :=
    { base := g
      word k := (φ'.word k).filterMap τ
      mem_word_iff j k := by
        rw [List.mem_filterMap]
        constructor
        · rintro ⟨i, hi, hij⟩
          rw [φ'.mem_word_iff, hφ', FinPointed.comp_toFun, hτ.1 hij] at hi
          exact hi
        · intro h
          refine ⟨σ j, ?_, hτ.2 (hmem j)⟩
          rw [φ'.mem_word_iff, hφ', FinPointed.comp_toFun, hmem, h]
      nodup_word k := (φ'.nodup_word k).filterMap fun i i' j hi hi' ↦
        (hτσ hi).symm.trans (hτσ hi') }
  have hfac : φ ≫ χ = φ' := by
    refine hom_ext fun k ↦ ?_
    rw [Hom.comp_word_of_word_eq_singleton hσ, List.map_filterMap]
    conv_rhs => rw [← List.filterMap_some (l := φ'.word k)]
    refine List.filterMap_congr rfl fun i hi ↦ ?_
    obtain ⟨j, hj⟩ := hcover hi
    simp [hj, hτσ hj]
  have := Hom.epi_of_isInert hφ
  exact ⟨χ, ⟨isHomLift_base χ, hfac⟩, fun ψ ⟨_, hψ⟩ ↦ cancel_epi φ |>.1 (hψ.trans hfac.symm)⟩

instance : toFinPointed.{u}.Full :=
  ⟨fun f ↦ ⟨Hom.ofBase f, rfl⟩⟩

end Assoc

end TauCeti
