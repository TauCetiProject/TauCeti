/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CategoryOfOperators.Assoc

/-!
# The category of operators of the left module operad

The operad `LM` has two colors, `a` (the algebra) and `m` (the module). Its operations are
those of the associative operad, an ordered word of inputs, subject to a condition on colors: an
operation with output `a` has only inputs `a`, and an operation with output `m` has an ordered
word of inputs `a` followed by its one input `m`. Its algebras are the pairs of an associative
algebra and a left module over it.

The category of operators `LM^⊗` has as objects the finite words of colors, that is a natural
number `n` and a color of each element of `⟨n⟩` other than the basepoint. A morphism is a
morphism of `Assoc^⊗` between the underlying objects whose word over each output has the input
profile allowed by `LM` for the color of that output (`TauCeti.LM.IsProfile`); inputs sent to
the basepoint are forgotten, whatever their color. Admissible profiles are closed under
substitution, so these morphisms compose. Forgetting colors is a functor `LM.toAssoc` to
`Assoc^⊗`, and `LM.toFinPointed : LM^⊗ ⥤ Fin_*` is its composite with `Assoc.toFinPointed`.

Coloring every element by `a` is a fully faithful functor `Assoc.toLM : Assoc^⊗ ⥤ LM^⊗` over
`Fin_*`, the inclusion of the associative operad. The target of a morphism of `LM^⊗` is its source
colored along the underlying map (`LM.pushforwardColor`), and a map of `Fin_*` lifts with a given
source exactly when each of its fibres over the elements other than the basepoint contains at most
one input colored `m` (`LM.exists_hom_toAssoc_base_eq_iff`). In particular every inert map of
`Fin_*` lifts, with a given source, to `LM^⊗` (`LM.Hom.ofInert`); every morphism over an inert map
is that lift up to the identification of its target, and is strongly coCartesian for
`LM.toFinPointed`.

## Main definitions

* `TauCeti.LM.Color`: the two colors `a` and `m`.
* `TauCeti.LM.IsProfile`: the input words of colors allowed for an output color.
* `TauCeti.LM`: the category of operators `LM^⊗`.
* `TauCeti.LM.toAssoc`, `TauCeti.LM.toFinPointed`: the functors to `Assoc^⊗` and `Fin_*`.
* `TauCeti.Assoc.toLM`: the inclusion `Assoc^⊗ ⥤ LM^⊗`.
* `TauCeti.LM.pushforwardColor`: the colors of the target of a lift of a map of `Fin_*`.
* `TauCeti.LM.Hom.ofBase`: the lift of a map of `Fin_*` with a given source, when it exists.
* `TauCeti.LM.Hom.ofInert`: the lift of an inert map of `Fin_*` with a given source.

## Main results

* `TauCeti.LM.homLiftEquiv`: lifts over a fixed pointed map decompose into colored output lifts.
* `TauCeti.Assoc.fullyFaithfulToLM`: the inclusion `Assoc^⊗ ⥤ LM^⊗` is fully faithful.
* `TauCeti.Assoc.toLM_comp_toFinPointed`: the inclusion lies over `Fin_*`.
* `TauCeti.LM.exists_hom_toAssoc_base_eq_iff`: the maps of `Fin_*` that lift with a given source.
* `TauCeti.LM.Hom.ofInert_comp_eqToHom`: every morphism over an inert map is `LM.Hom.ofInert`, up to
  the identification of its target.
* `TauCeti.LM.isStronglyCocartesian_of_isInert`: every morphism over an inert map is strongly
  coCartesian for `LM.toFinPointed`.

## References

* J. Lurie, *Higher Algebra*, Definition 4.2.1.7.
-/

public section

universe u

open CategoryTheory Functor

namespace TauCeti

/-- The two colors of the left module operad: `a`, the algebra, and `m`, the module. -/
inductive LM.Color : Type
  /-- The algebra color. -/
  | a
  /-- The module color. -/
  | m
  deriving DecidableEq

namespace LM

open Color

/-- The words of input colors allowed for an operation of `LM` with output color `c`: only
inputs `a` for the output `a`, and inputs `a` followed by one input `m` for the output `m`. -/
def IsProfile : Color → List Color → Prop
  | a, w => m ∉ w
  | m, w => ∃ l, m ∉ l ∧ w = l ++ [m]

@[simp]
lemma isProfile_a (w : List Color) : IsProfile a w ↔ m ∉ w := Iff.rfl

@[simp]
lemma isProfile_m (w : List Color) : IsProfile m w ↔ ∃ l, m ∉ l ∧ w = l ++ [m] := Iff.rfl

@[simp]
lemma isProfile_singleton_iff (c c' : Color) : IsProfile c [c'] ↔ c' = c := by
  cases c <;> cases c'
  case m.a =>
    simp only [isProfile_m, reduceCtorEq, iff_false, not_exists, not_and]
    intro l _ h
    have : m ∈ [a] := h ▸ List.mem_append_right l (List.mem_singleton_self m)
    simp at this
  all_goals simp

/-- Admissible profiles are closed under substitution: substituting, into an operation whose
inputs `j` have the colors `color j`, operations with outputs `color j` and admissible profiles
gives an operation with an admissible profile. -/
lemma IsProfile.flatMap {α β : Type*} {c : Color} {color : α → Color} {color' : β → Color}
    {l : List α} (hl : IsProfile c (l.map color)) {f : α → List β}
    (hf : ∀ j ∈ l, IsProfile (color j) ((f j).map color')) :
    IsProfile c ((l.flatMap f).map color') := by
  -- Substituting into an operation with inputs `a` only gives an operation with inputs `a` only.
  have hA {l : List α} (hl : m ∉ l.map color)
      (hf : ∀ j ∈ l, IsProfile (color j) ((f j).map color')) :
      m ∉ (l.flatMap f).map color' := by
    simp only [List.map_flatMap, List.mem_flatMap, not_exists, not_and]
    intro j hj
    have hj' : color j = a := by
      cases h : color j
      · rfl
      · exact absurd (h ▸ List.mem_map_of_mem hj) hl
    simpa [hj'] using hf j hj
  cases c with
  | a => exact hA hl hf
  | m =>
    obtain ⟨w, hw, hlw⟩ := hl
    obtain ⟨l₁, l₂, rfl, rfl, hl₂⟩ := List.map_eq_append_iff.1 hlw
    obtain ⟨j, rfl, hj⟩ := List.map_eq_singleton_iff.1 hl₂
    have hfj := hf j (by simp)
    rw [hj, isProfile_m] at hfj
    obtain ⟨w', hw', hjw⟩ := hfj
    refine ⟨(l₁.flatMap f).map color' ++ w', ?_, ?_⟩
    · rw [List.mem_append, not_or]
      exact ⟨hA hw fun j hj ↦ hf j (by simp [hj]), hw'⟩
    · simp [List.flatMap_append, hjw]

end LM

/-- The category of operators `LM^⊗` of the left module operad: an object is a natural number `n`
together with a color of each element of `⟨n⟩` other than the basepoint. -/
structure LM : Type u where
  /-- The object `⟨n⟩` of `LM^⊗` with the given colors. -/
  mk ::
  /-- The number of elements of the pointed set other than its basepoint. -/
  len : ℕ
  /-- The color of the element `i.succ`. -/
  color : Fin len → LM.Color

namespace LM

/-- Two objects of `LM^⊗` are equal when they have the same length and, along the resulting
identification of their elements, the same colors. The colors depend on the length, so no
`ext_iff` form is generated. -/
@[ext (iff := false)]
lemma ext {X Y : LM.{u}} (hlen : X.len = Y.len)
    (hcolor : ∀ i, X.color i = Y.color (Fin.cast hlen i)) : X = Y := by
  obtain ⟨n, c⟩ := X
  obtain ⟨n', c'⟩ := Y
  obtain rfl : n = n' := hlen
  exact congrArg (LM.mk n) (funext hcolor)

/-- The underlying object of `Assoc^⊗`, forgetting the colors. -/
abbrev toAssocObj (X : LM.{u}) : Assoc.{u} := Assoc.mk X.len

/-- A morphism of `LM^⊗`: a morphism of `Assoc^⊗` between the underlying objects whose word over
each output has the input profile allowed for the color of that output. -/
structure Hom (X Y : LM.{u}) : Type u where
  /-- The morphism given by a morphism of `Assoc^⊗` with admissible profiles. -/
  mk ::
  /-- The underlying morphism of `Assoc^⊗`. -/
  toAssoc : X.toAssocObj ⟶ Y.toAssocObj
  isProfile (j : Fin Y.len) : IsProfile (Y.color j) ((toAssoc.word j).map X.color)

/-- The composition of `LM^⊗` is that of `Assoc^⊗`. -/
instance : SmallCategory LM.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toAssocObj, fun j ↦ by simp⟩
  comp f g := ⟨f.toAssoc ≫ g.toAssoc, fun k ↦ by
    simpa using (g.isProfile k).flatMap fun j _ ↦ f.isProfile j⟩

variable {X Y Z : LM.{u}}

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.toAssoc = g.toAssoc) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[simp]
lemma id_toAssoc : Hom.toAssoc (𝟙 X) = 𝟙 X.toAssocObj := rfl

@[simp]
lemma comp_toAssoc (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).toAssoc = f.toAssoc ≫ g.toAssoc := rfl

/-- The functor `LM^⊗ ⥤ Assoc^⊗` forgetting the colors. -/
@[expose]
def toAssoc : LM.{u} ⥤ Assoc.{u} where
  obj X := X.toAssocObj
  map f := f.toAssoc

@[simp]
lemma toAssoc_obj (X : LM.{u}) : toAssoc.obj X = X.toAssocObj := (rfl)

@[simp]
lemma toAssoc_map (f : X ⟶ Y) : toAssoc.map f = f.toAssoc := (rfl)

instance : toAssoc.{u}.Faithful where
  map_injective h := hom_ext h

/-- The functor `LM^⊗ ⥤ Fin_*`, sending a word of colors of length `n` to `⟨n⟩` and a morphism
to its underlying map. The body is exposed so that `toFinPointed.obj X` is visibly
`FinPointed.mk X.len`. -/
@[expose]
def toFinPointed : LM.{u} ⥤ FinPointed.{u} :=
  toAssoc ⋙ Assoc.toFinPointed

@[simp]
lemma toFinPointed_obj (X : LM.{u}) : toFinPointed.obj X = FinPointed.mk X.len := (rfl)

@[simp]
lemma toFinPointed_map (f : X ⟶ Y) : toFinPointed.map f = f.toAssoc.base := (rfl)

/-- Every morphism lies over its underlying map. -/
instance isHomLift_base (f : X ⟶ Y) : toFinPointed.IsHomLift f.toAssoc.base f :=
  inferInstanceAs (toFinPointed.IsHomLift (toFinPointed.map f) f)

/-- A morphism lies over a map of `Fin_*` exactly when that map is its underlying map. -/
lemma isHomLift_iff {f : X ⟶ Y} {g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len} :
    toFinPointed.IsHomLift g f ↔ f.toAssoc.base = g :=
  -- The endpoints are fixed explicitly, since `g` mentions `X` and `Y` only through their
  -- lengths.
  isHomLift_iff_map_eq (p := toFinPointed) (a := X) (b := Y)

/-- The canonical inert projection to the single output with color `Y.color j`. -/
def ρ (j : Fin Y.len) : Y ⟶ ⟨1, fun _ ↦ Y.color j⟩ where
  toAssoc := Assoc.ρ j
  isProfile _ := by simp

@[simp]
lemma ρ_toAssoc (j : Fin Y.len) : (ρ j).toAssoc = Assoc.ρ j := (rfl)

/-- The lift to `Assoc^⊗` assembled by `Assoc.homLiftEquiv` from the underlying lifts of a
family of colored output lifts. The objects of `Assoc.homLiftEquiv` are fixed explicitly here:
its statement mentions them only through their lengths, as in `FinPointed.mk X.len`, and
unification cannot solve `?X.len =?= X.len` for `?X`. Here the type of the family fixes `X` and
`Y`, so the proofs below need not supply them. -/
private def assocLift (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len)
    (f : (j : Fin Y.len) → {f : X ⟶ LM.mk 1 (fun _ ↦ Y.color j) //
      toFinPointed.IsHomLift (g ≫ FinPointed.ρ j) f}) :
    {f : X.toAssocObj ⟶ Y.toAssocObj // Assoc.toFinPointed.IsHomLift g f} :=
  (Assoc.homLiftEquiv (X := X.toAssocObj) (Y := Y.toAssocObj) g).symm fun j ↦
    ⟨(f j).val.toAssoc, Assoc.isHomLift_iff.2 (isHomLift_iff.1 (f j).property)⟩

/-- Lifts of a fixed pointed map are equivalent to families of lifts to its colored outputs.
The forward map postcomposes with the canonical inert projections. The inverse assembles
the ordered fibres, whose profiles are supplied by the individual lifts. -/
def homLiftEquiv (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len) :
    {f : X ⟶ Y // toFinPointed.IsHomLift g f} ≃
      ((j : Fin Y.len) → {f : X ⟶ LM.mk 1 (fun _ ↦ Y.color j) //
        toFinPointed.IsHomLift (g ≫ FinPointed.ρ j) f}) where
  toFun f j := ⟨f.val ≫ ρ j, isHomLift_iff.2 (by
    simp [isHomLift_iff.1 f.property])⟩
  invFun f :=
    ⟨⟨(assocLift g f).val, fun j ↦ by
      rw [assocLift, Assoc.homLiftEquiv_symm_apply_word (X := X.toAssocObj) (Y := Y.toAssocObj)]
      exact (f j).val.isProfile 0⟩,
      isHomLift_iff.2 (Assoc.isHomLift_iff.1 (assocLift g f).property)⟩
  -- Both inverse laws are those of `Assoc.homLiftEquiv`, since forgetting the colors commutes
  -- with the projections.
  left_inv f := by
    refine Subtype.ext (hom_ext ?_)
    have h := congrArg Subtype.val
      ((Assoc.homLiftEquiv (X := X.toAssocObj) (Y := Y.toAssocObj) g).symm_apply_apply
        ⟨f.val.toAssoc, Assoc.isHomLift_iff.2 (isHomLift_iff.1 f.property)⟩)
    refine Eq.trans (congrArg (fun F ↦
      ((Assoc.homLiftEquiv (X := X.toAssocObj) (Y := Y.toAssocObj) g).symm F).val)
      (funext fun j ↦ Subtype.ext ?_)) h
    rw [Assoc.homLiftEquiv_apply_val]
    exact (comp_toAssoc _ _).trans (congrArg _ (ρ_toAssoc j))
  right_inv f := by
    refine funext fun j ↦ Subtype.ext (hom_ext ?_)
    have h := congrArg Subtype.val (congrFun
      ((Assoc.homLiftEquiv (X := X.toAssocObj) (Y := Y.toAssocObj) g).apply_symm_apply
        fun j ↦ ⟨(f j).val.toAssoc, Assoc.isHomLift_iff.2 (isHomLift_iff.1 (f j).property)⟩) j)
    rw [Assoc.homLiftEquiv_apply_val] at h
    exact h

@[simp]
lemma homLiftEquiv_apply_val
    (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len)
    (f : {f : X ⟶ Y // toFinPointed.IsHomLift g f}) (j : Fin Y.len) :
    (homLiftEquiv g f j).val = f.val ≫ ρ j := (rfl)

@[simp]
lemma homLiftEquiv_symm_apply_word
    (g : FinPointed.mk.{u} X.len ⟶ FinPointed.mk Y.len)
    (f : (j : Fin Y.len) → {f : X ⟶ LM.mk 1 (fun _ ↦ Y.color j) //
      toFinPointed.IsHomLift (g ≫ FinPointed.ρ j) f}) (j : Fin Y.len) :
    ((homLiftEquiv g).symm f).val.toAssoc.word j = (f j).val.toAssoc.word 0 :=
  Assoc.homLiftEquiv_symm_apply_word (X := X.toAssocObj) (Y := Y.toAssocObj) g _ j

/-- If the word of `f` over the output `j` is the single letter `i`, then the output `j` has
the color of the input `i`. -/
lemma Hom.color_eq_of_word_eq_singleton (f : X ⟶ Y) {j : Fin Y.len} {i : Fin X.len}
    (h : f.toAssoc.word j = [i]) : Y.color j = X.color i :=
  (by simpa [h] using f.isProfile j : X.color i = Y.color j).symm

/-- Every morphism of `LM^⊗` over an inert map of `Fin_*` is strongly coCartesian for the
functor `LM^⊗ ⥤ Fin_*`. -/
theorem isStronglyCocartesian_of_isInert (φ : X ⟶ Y) (hφ : φ.toAssoc.base.IsInert) :
    toFinPointed.IsStronglyCocartesian φ.toAssoc.base φ := by
  choose σ hσ using Assoc.Hom.exists_word_eq_singleton_of_isInert hφ
  have hcc := Assoc.isStronglyCocartesian_of_isInert φ.toAssoc hφ
  refine ⟨fun {Z} g φ' hl ↦ ?_⟩
  have hφ' : φ'.toAssoc.base = φ.toAssoc.base ≫ g := isHomLift_iff.1 hl
  -- The universal property of `φ.toAssoc` for `Assoc.toFinPointed`, applied to `φ'.toAssoc`.
  have : Assoc.toFinPointed.IsHomLift (φ.toAssoc.base ≫ g) φ'.toAssoc :=
    Assoc.isHomLift_iff.2 hφ'
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := IsStronglyCocartesian.universal_property Assoc.toFinPointed
    φ.toAssoc.base φ.toAssoc g _ rfl φ'.toAssoc
  have hχ' : χ.base = g := Assoc.isHomLift_iff.1 hχ
  -- The colors of `Y` are those of `X` along `σ`, so `χ` has the profiles of `φ'`.
  have hprofile (k : Fin Z.len) : IsProfile (Z.color k) ((χ.word k).map Y.color) := by
    have hY : Y.color = X.color ∘ σ :=
      funext fun j ↦ φ.color_eq_of_word_eq_singleton (hσ j)
    rw [hY, ← List.map_map, ← Assoc.Hom.comp_word_of_word_eq_singleton hσ, hfac]
    exact φ'.isProfile k
  refine ⟨⟨χ, hprofile⟩, ⟨isHomLift_iff.2 hχ', hom_ext hfac⟩, fun ψ ⟨hψl, hψ⟩ ↦ ?_⟩
  exact hom_ext (huniq ψ.toAssoc ⟨Assoc.isHomLift_iff.2 (isHomLift_iff.1 hψl),
    congrArg Hom.toAssoc hψ⟩)

/-- The candidate target colors along a pointed map: an output is colored `m` when one of
its preimages is. Every LM morphism has these target colors (`Hom.mk_pushforwardColor_eq`), but
this coloring alone does not guarantee a lift: a lift exists exactly when each fibre over an
element other than the basepoint contains at most one input colored `m`
(`exists_hom_toAssoc_base_eq_iff`). -/
def pushforwardColor (X : LM.{u}) {k : ℕ} (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (j : Fin k) : Color :=
  if ∃ i, f.toFun i.succ = j.succ ∧ X.color i = .m then .m else .a

/-- An output has color `m` exactly when some input over it has color `m`. -/
@[simp]
lemma pushforwardColor_eq_m_iff (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) (j : Fin k) :
    X.pushforwardColor f j = .m ↔ ∃ i, f.toFun i.succ = j.succ ∧ X.color i = .m := by
  simp [pushforwardColor]

/-- An output has color `a` exactly when every input over it has color `a`. -/
@[simp]
lemma pushforwardColor_eq_a_iff (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) (j : Fin k) :
    X.pushforwardColor f j = .a ↔ ∀ i, f.toFun i.succ = j.succ → X.color i = .a := by
  have h (c : Color) : c ≠ .m ↔ c = .a := by cases c <;> simp
  simp [pushforwardColor, h]

/-- Every LM morphism has the target coloring prescribed by its underlying pointed map. -/
lemma Hom.color_eq_pushforwardColor (f : X ⟶ Y) (j : Fin Y.len) :
    Y.color j = X.pushforwardColor f.toAssoc.base j := by
  symm
  have hp := f.isProfile j
  cases hc : Y.color j with
  | a =>
    rw [pushforwardColor_eq_a_iff]
    rw [hc, isProfile_a] at hp
    intro i hi
    cases hiC : X.color i with
    | a => rfl
    | m => exact False.elim (hp (List.mem_map.2
        ⟨i, (f.toAssoc.mem_word_iff i j).2 hi, hiC⟩))
  | m =>
    rw [pushforwardColor_eq_m_iff]
    rw [hc, isProfile_m] at hp
    obtain ⟨l, _, hl⟩ := hp
    have hm : .m ∈ (f.toAssoc.word j).map X.color := by simp [hl]
    obtain ⟨i, hi, hiC⟩ := List.mem_map.1 hm
    exact ⟨i, (f.toAssoc.mem_word_iff i j).1 hi, hiC⟩

/-- An output with exactly one input has the color of that input. -/
lemma pushforwardColor_eq_of_unique (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) {i : Fin X.len} {j : Fin k}
    (hi : f.toFun i.succ = j.succ) (huniq : ∀ i', f.toFun i'.succ = j.succ → i' = i) :
    X.pushforwardColor f j = X.color i := by
  have hpre (i' : Fin X.len) : f.toFun i'.succ = j.succ ↔ i' = i :=
    ⟨huniq i', fun h ↦ h ▸ hi⟩
  cases hc : X.color i <;> simp [hpre, hc]

/-- Along an inert map, each output has the color of its unique input. -/
lemma pushforwardColor_eq_of_isInert (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) (hf : f.IsInert)
    {i : Fin X.len} {j : Fin k} (hi : f.toFun i.succ = j.succ) :
    X.pushforwardColor f j = X.color i :=
  X.pushforwardColor_eq_of_unique f hi fun _ hi' ↦ hf.eq_of_toFun_succ_eq hi' hi

/-- The lift of a map `f : ⟨n⟩ ⟶ ⟨k⟩` of `Fin_*` with source `X` each of whose fibres over the
elements other than the basepoint contains at most one input colored `m`. Its target is `⟨k⟩`
colored along `f`, and its word over each output lists the inputs colored `a` increasingly,
followed by the input colored `m` if there is one. -/
def Hom.ofBase (X : LM.{u}) {k : ℕ} (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (hf : ∀ (j : Fin k) (i i' : Fin X.len), f.toFun i.succ = j.succ → f.toFun i'.succ = j.succ →
      X.color i = .m → X.color i' = .m → i = i') :
    X ⟶ ⟨k, X.pushforwardColor f⟩ where
  toAssoc :=
    { base := f
      word j := (List.finRange X.len).filter (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .a) ++
        (List.finRange X.len).filter (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .m)
      mem_word_iff i j := by cases hc : X.color i <;> simp [hc]
      nodup_word j := ((List.nodup_finRange _).filter _).append ((List.nodup_finRange _).filter _)
        (List.disjoint_left.2 fun i hi hi' ↦ by simp_all) }
  isProfile j := by
    -- The target is a constructor application, so its color at `j` reduces to
    -- `X.pushforwardColor f j`.
    dsimp only
    -- The prefix of inputs colored `a` contains no color `m`.
    have hA : .m ∉ ((List.finRange X.len).filter
        (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .a)).map X.color := by
      simp +contextual
    cases hc : X.pushforwardColor f j with
    | a =>
      rw [pushforwardColor_eq_a_iff] at hc
      -- No input over `j` is colored `m`, so the suffix of inputs colored `m` is empty.
      have hM : (List.finRange X.len).filter
          (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .m) = [] :=
        List.filter_eq_nil_iff.2 fun i _ ↦ by simp +contextual [hc i]
      rw [isProfile_a, hM, List.append_nil]
      exact hA
    | m =>
      obtain ⟨i₀, hi₀, hc₀⟩ := (X.pushforwardColor_eq_m_iff f j).1 hc
      -- The only input colored `m` over `j` is `i₀`.
      have hM : (List.finRange X.len).filter
          (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .m) = [i₀] :=
        List.Perm.eq_singleton ((List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _)
          (List.nodup_singleton i₀)).2 fun i ↦ by
            simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
              List.mem_singleton]
            exact ⟨fun h ↦ hf j i i₀ h.1 hi₀ h.2 hc₀, fun h ↦ h ▸ ⟨hi₀, hc₀⟩⟩)
      exact ⟨_, hA, by rw [hM, List.map_append, List.map_singleton, hc₀]⟩

@[simp]
lemma Hom.ofBase_toAssoc_base (X : LM.{u}) {k : ℕ} (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (hf : ∀ (j : Fin k) (i i' : Fin X.len), f.toFun i.succ = j.succ → f.toFun i'.succ = j.succ →
      X.color i = .m → X.color i' = .m → i = i') :
    (Hom.ofBase X f hf).toAssoc.base = f :=
  (rfl)

/-- The word of `Hom.ofBase` over an output lists the inputs colored `a` over it increasingly,
followed by the input colored `m` over it if there is one. -/
lemma Hom.ofBase_toAssoc_word (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (hf : ∀ (j : Fin k) (i i' : Fin X.len), f.toFun i.succ = j.succ → f.toFun i'.succ = j.succ →
      X.color i = .m → X.color i' = .m → i = i') (j : Fin k) :
    (Hom.ofBase X f hf).toAssoc.word j =
      (List.finRange X.len).filter (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .a) ++
        (List.finRange X.len).filter (fun i ↦ f.toFun i.succ = j.succ ∧ X.color i = .m) :=
  (rfl)

/-- The lift of an inert map `f : ⟨n⟩ ⟶ ⟨k⟩` of `Fin_*` with source `X`: its target is `⟨k⟩`
colored along `f`, and its words are the one-letter fibres of `f`. It is `Hom.ofBase`, whose
fibre condition holds since the fibres of `f` over the elements other than the basepoint are
singletons. -/
def Hom.ofInert (X : LM.{u}) {k : ℕ} (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (hf : f.IsInert) : X ⟶ ⟨k, X.pushforwardColor f⟩ :=
  Hom.ofBase X f fun _ _ _ hi hi' _ _ ↦ hf.eq_of_toFun_succ_eq hi hi'

@[simp]
lemma Hom.ofInert_toAssoc (X : LM.{u}) {k : ℕ} (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k)
    (hf : f.IsInert) : (Hom.ofInert X f hf).toAssoc = Assoc.Hom.ofBase f :=
  Assoc.Hom.ext_of_isInert (by rw [Hom.ofInert, Hom.ofBase_toAssoc_base, Assoc.Hom.ofBase_base])
    (by rwa [Hom.ofInert, Hom.ofBase_toAssoc_base])

/-- The target of every morphism is its source colored along its underlying map. -/
lemma Hom.mk_pushforwardColor_eq (φ : X ⟶ Y) :
    (⟨Y.len, X.pushforwardColor φ.toAssoc.base⟩ : LM.{u}) = Y :=
  congrArg (LM.mk Y.len) (funext fun j ↦ (φ.color_eq_pushforwardColor j).symm)

/-- Every morphism over an inert map is the lift `Hom.ofInert` of that map, followed by the
identification `Hom.mk_pushforwardColor_eq` of its target with the source colored along that
map. -/
lemma Hom.ofInert_comp_eqToHom (φ : X ⟶ Y) (hφ : φ.toAssoc.base.IsInert) :
    Hom.ofInert X φ.toAssoc.base hφ ≫ eqToHom φ.mk_pushforwardColor_eq = φ := by
  refine hom_ext ?_
  -- Forgetting the colors sends the identification of targets to an identity.
  have h : (eqToHom φ.mk_pushforwardColor_eq).toAssoc =
      eqToHom (congrArg toAssocObj φ.mk_pushforwardColor_eq) :=
    eqToHom_map LM.toAssoc φ.mk_pushforwardColor_eq
  rw [comp_toAssoc, h, eqToHom_refl, Category.comp_id]
  exact Assoc.Hom.ext_of_isInert (by simp) (by simpa using hφ)

/-- The lift of an inert map with a given source is strongly coCartesian. -/
lemma isStronglyCocartesian_ofInert (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) (hf : f.IsInert) :
    toFinPointed.IsStronglyCocartesian f (Hom.ofInert X f hf) := by
  simpa using isStronglyCocartesian_of_isInert (Hom.ofInert X f hf) (by simpa using hf)

/-- A map `f : ⟨n⟩ ⟶ ⟨k⟩` of `Fin_*` lifts to `LM^⊗` with source `X`, necessarily with target
`⟨k⟩` colored along `f` (`Hom.mk_pushforwardColor_eq`), exactly when each of its fibres over the
elements other than the basepoint contains at most one input colored `m`. -/
theorem exists_hom_toAssoc_base_eq_iff (X : LM.{u}) {k : ℕ}
    (f : FinPointed.mk.{u} X.len ⟶ FinPointed.mk k) :
    (∃ φ : X ⟶ ⟨k, X.pushforwardColor f⟩, φ.toAssoc.base = f) ↔
      ∀ (j : Fin k) (i i' : Fin X.len), f.toFun i.succ = j.succ → f.toFun i'.succ = j.succ →
        X.color i = .m → X.color i' = .m → i = i' := by
  refine ⟨fun ⟨φ, hφ⟩ j i i' hi hi' hc hc' ↦ ?_, fun hf ↦ ⟨Hom.ofBase X f hf, rfl⟩⟩
  -- The word of `φ` over `j` is `w ++ [x]`, where no input of `w` is colored `m`.
  have hp := φ.isProfile j
  -- The target is a constructor application, so its color at `j` reduces to
  -- `X.pushforwardColor f j`, which is `m` since the input `i` over `j` is colored `m`.
  dsimp only at hp
  rw [(X.pushforwardColor_eq_m_iff f j).2 ⟨i, hi, hc⟩, isProfile_m] at hp
  obtain ⟨l, hl, hw⟩ := hp
  obtain ⟨w, w', hww', rfl, hw'⟩ := List.map_eq_append_iff.1 hw
  obtain ⟨x, rfl, -⟩ := List.map_eq_singleton_iff.1 hw'
  -- So every input colored `m` over `j` is the last letter `x`.
  have hlast (i : Fin X.len) (hi : f.toFun i.succ = j.succ) (hc : X.color i = .m) : i = x := by
    have hmem := (φ.toAssoc.mem_word_iff i j).2 (by rw [hφ]; exact hi)
    rw [hww'] at hmem
    rcases List.mem_append.1 hmem with h | h
    · exact absurd (hc ▸ List.mem_map_of_mem h) hl
    · exact List.mem_singleton.1 h
  exact (hlast i hi hc).trans (hlast i' hi' hc').symm

end LM

namespace Assoc

/-- The inclusion `Assoc^⊗ ⥤ LM^⊗` of the associative operad, coloring every element by `a`. -/
@[expose]
def toLM : Assoc.{u} ⥤ LM.{u} where
  obj X := ⟨X.len, fun _ ↦ .a⟩
  map f := ⟨f, fun _ ↦ by simp⟩

@[simp]
lemma toLM_obj_len (X : Assoc.{u}) : (toLM.obj X).len = X.len := (rfl)

@[simp]
lemma toLM_obj_color (X : Assoc.{u}) (i : Fin X.len) : (toLM.obj X).color i = .a := (rfl)

@[simp]
lemma toLM_map_toAssoc {X Y : Assoc.{u}} (f : X ⟶ Y) : (toLM.map f).toAssoc = f := (rfl)

/-- The inclusion `Assoc^⊗ ⥤ LM^⊗` is fully faithful: between objects colored by `a` only, every
morphism of `Assoc^⊗` has admissible profiles. -/
def fullyFaithfulToLM : toLM.{u}.FullyFaithful where
  preimage f := f.toAssoc

instance : toLM.{u}.Full := fullyFaithfulToLM.full

instance : toLM.{u}.Faithful := fullyFaithfulToLM.faithful

/-- Forgetting the colors of the inclusion `Assoc^⊗ ⥤ LM^⊗` gives back `Assoc^⊗`. -/
@[simp]
lemma toLM_comp_toAssoc : toLM.{u} ⋙ LM.toAssoc = 𝟭 _ := rfl

/-- The inclusion `Assoc^⊗ ⥤ LM^⊗` lies over `Fin_*`. -/
@[simp]
lemma toLM_comp_toFinPointed : toLM.{u} ⋙ LM.toFinPointed = toFinPointed := rfl

end Assoc

end TauCeti
