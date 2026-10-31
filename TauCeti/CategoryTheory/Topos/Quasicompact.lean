/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import TauCeti.CategoryTheory.EffectiveEpi.Types

/-!
# Quasicompact and quasiseparated objects and morphisms of a topos

In a topos, the covering families of an object `X` are the effective epimorphic families
`Y i ⟶ X`. Following SGA 4 VI, an object `X` is *quasicompact* if every such family has a finite
subfamily that is still effective epimorphic, and *quasiseparated* if the fibre product of any two
quasicompact objects over `X` is quasicompact. A morphism `f : Y ⟶ X` is *quasicompact* if its base
change along every map from a quasicompact object has quasicompact source, and *quasiseparated* if
its diagonal `Y ⟶ Y ×_X Y` is quasicompact.

The definitions make sense in any category, and are stated in that generality; they are meant for
Grothendieck topoi, where effective epimorphic families are the jointly epimorphic ones. Coherent
(quasicompact and quasiseparated) objects are the finiteness condition on objects used, for
instance, to define locally weakly contractible and algebraic topoi.

Quasicompactness of an object is not quasicompactness of its map to the terminal object: the
identity of every object is a quasicompact morphism, while in sheaves on an infinite discrete
space the terminal sheaf is not a quasicompact object. When the terminal object is quasicompact,
an object whose map to it is quasicompact is itself quasicompact
(`TauCeti.Topos.isQuasicompact_of_isTerminal`).

## Main definitions

* `TauCeti.Topos.IsQuasicompact X`: every effective epimorphic family onto `X` has a finite
  effective epimorphic subfamily.
* `TauCeti.Topos.IsQuasiseparated X`: fibre products over `X` of quasicompact objects are
  quasicompact.
* `TauCeti.Topos.quasicompact`: the quasicompact morphisms, as a `MorphismProperty`.
* `TauCeti.Topos.quasiseparated`: the quasiseparated morphisms, whose diagonal is quasicompact.

## Main results

* `TauCeti.Topos.isQuasicompact_of_isInitial`: an initial object is quasicompact.
* Quasicompact morphisms contain the identities and are stable under composition and base change;
  hence so are quasiseparated morphisms, through Mathlib's `MorphismProperty.diagonal`. Every
  monomorphism is quasiseparated (`TauCeti.Topos.monomorphisms_le_quasiseparated`).
* `TauCeti.Topos.isQuasicompact_of_quasicompact`: the source of a quasicompact morphism with
  quasicompact target is quasicompact. In particular, if the terminal object is quasicompact, an
  object whose map to it is quasicompact is quasicompact
  (`TauCeti.Topos.isQuasicompact_of_isTerminal`).
* `TauCeti.Topos.isQuasicompact_iff_finite`: in the topos of sets, an object is quasicompact if and
  only if it is finite. Every set is quasiseparated (`TauCeti.Topos.isQuasiseparated_type`) and
  every map of sets is quasiseparated (`TauCeti.Topos.quasiseparated_type`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
  (SGA 4), Exposé VI, Définitions 1.1, 1.7 and 1.13.
-/

public section

open CategoryTheory Limits MorphismProperty

universe v u

namespace TauCeti.Topos

variable {C : Type u} [Category.{v} C]

/-- An object `X` is *quasicompact* if every effective epimorphic family onto `X`, indexed by a
type in the universe of morphisms, has a finite subfamily which is effective epimorphic. -/
def IsQuasicompact (X : C) : Prop :=
  ∀ ⦃ι : Type v⦄ (Y : ι → C) (π : (i : ι) → Y i ⟶ X), EffectiveEpiFamily Y π →
    ∃ s : Finset ι, EffectiveEpiFamily (fun i : s ↦ Y i) (fun i ↦ π i)

/-- An object `X` is *quasiseparated* if every fibre product over `X` of two quasicompact objects
is quasicompact. -/
def IsQuasiseparated (X : C) : Prop :=
  ∀ ⦃Y Z W : C⦄ (f : Y ⟶ X) (g : Z ⟶ X) (fst : W ⟶ Y) (snd : W ⟶ Z),
    IsPullback fst snd f g → IsQuasicompact Y → IsQuasicompact Z → IsQuasicompact W

/-- A morphism `f : Y ⟶ X` is *quasicompact* if for every morphism `g : Z ⟶ X` from a
quasicompact object, the fibre product `Z ×_X Y` is quasicompact. -/
def quasicompact : MorphismProperty C := fun _ X f ↦
  ∀ ⦃Z W : C⦄ (g : Z ⟶ X) (fst : W ⟶ Z) (snd : W ⟶ _), IsPullback fst snd g f →
    IsQuasicompact Z → IsQuasicompact W

/-- A morphism is *quasiseparated* if its diagonal is quasicompact. -/
def quasiseparated [HasPullbacks C] : MorphismProperty C := quasicompact.diagonal

theorem isQuasicompact_iff (X : C) :
    IsQuasicompact X ↔ ∀ ⦃ι : Type v⦄ (Y : ι → C) (π : (i : ι) → Y i ⟶ X),
      EffectiveEpiFamily Y π →
        ∃ s : Finset ι, EffectiveEpiFamily (fun i : s ↦ Y i) (fun i ↦ π i) :=
  Iff.rfl

theorem isQuasiseparated_iff (X : C) :
    IsQuasiseparated X ↔ ∀ ⦃Y Z W : C⦄ (f : Y ⟶ X) (g : Z ⟶ X) (fst : W ⟶ Y) (snd : W ⟶ Z),
      IsPullback fst snd f g → IsQuasicompact Y → IsQuasicompact Z → IsQuasicompact W :=
  Iff.rfl

theorem quasicompact_iff {X Y : C} (f : Y ⟶ X) :
    quasicompact f ↔ ∀ ⦃Z W : C⦄ (g : Z ⟶ X) (fst : W ⟶ Z) (snd : W ⟶ Y),
      IsPullback fst snd g f → IsQuasicompact Z → IsQuasicompact W :=
  Iff.rfl

theorem quasiseparated_iff [HasPullbacks C] {X Y : C} (f : Y ⟶ X) :
    quasiseparated f ↔ quasicompact (pullback.diagonal f) :=
  Iff.rfl

/-- Quasicompactness is invariant under isomorphism. -/
theorem IsQuasicompact.of_iso {X X' : C} (e : X ≅ X') (hX : IsQuasicompact X) :
    IsQuasicompact X' := by
  intro ι Y π _
  obtain ⟨s, _⟩ := hX Y (fun i ↦ π i ≫ e.inv) inferInstance
  refine ⟨s, ?_⟩
  simpa using (inferInstance :
    EffectiveEpiFamily (fun i : s ↦ Y i) (fun i ↦ (π i ≫ e.inv) ≫ e.hom))

theorem isQuasicompact_iff_of_iso {X X' : C} (e : X ≅ X') :
    IsQuasicompact X ↔ IsQuasicompact X' :=
  ⟨.of_iso e, .of_iso e.symm⟩

/-- An initial object is quasicompact: the empty subfamily of any family onto it is effective
epimorphic. -/
theorem isQuasicompact_of_isInitial {X : C} (hX : IsInitial X) : IsQuasicompact X := by
  intro ι Y π _
  refine ⟨∅, ⟨⟨{ desc := fun _ _ ↦ hX.to _, fac := fun _ _ i ↦ ?_, uniq := ?_ }⟩⟩⟩
  · exact (Finset.notMem_empty _ i.2).elim
  · exact fun _ _ _ _ ↦ hX.hom_ext _ _

/-- Identities are quasicompact: a fibre product along an identity is isomorphic to the base. -/
instance : (quasicompact : MorphismProperty C).ContainsIdentities where
  id_mem _ _ _ g _ _ h hZ :=
    hZ.of_iso (h.isoIsPullback _ _ (IsPullback.of_id_fst (f := g))).symm

/-- Quasicompact morphisms are stable under base change, by pasting pullback squares. -/
instance : (quasicompact : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f _ f' _} sq hg _ _ h fst snd t hZ :=
    hg (h ≫ f) fst (snd ≫ f') (t.flip.paste_horiz sq).flip hZ

/-- Quasicompact morphisms are stable under composition. -/
instance [HasPullbacks C] : (quasicompact : MorphismProperty C).IsStableUnderComposition where
  comp_mem {_ _ _} f g hf hg _ W h fst snd t hZ := by
    -- `Z ×_S X` is quasicompact since `g` is, and `W = Z ×_S Y` is its fibre product with `Y`
    -- over `X`, which is quasicompact since `f` is.
    have hP := hg h (pullback.fst h g) (pullback.snd h g) (.of_hasPullback h g) hZ
    let u : W ⟶ pullback h g := pullback.lift fst (snd ≫ f) (by simpa using t.w)
    exact hf (pullback.snd h g) u snd
      (IsPullback.of_bot (by simpa [u] using t.flip) (by simp [u])
        (IsPullback.of_hasPullback h g).flip).flip hP

/-- Every monomorphism is quasiseparated: its diagonal is an isomorphism. -/
theorem monomorphisms_le_quasiseparated [HasPullbacks C] :
    monomorphisms C ≤ quasiseparated := by
  rw [← diagonal_isomorphisms]
  exact fun _ _ f (_ : IsIso _) ↦ quasicompact.of_isIso (pullback.diagonal f)

/-- The source of a quasicompact morphism with quasicompact target is quasicompact: it is the
fibre product of the morphism with the identity of the target. -/
theorem isQuasicompact_of_quasicompact {X Y : C} (f : X ⟶ Y) (hY : IsQuasicompact Y)
    (hf : quasicompact f) : IsQuasicompact X :=
  hf (𝟙 Y) f (𝟙 X) (IsPullback.of_id_snd (f := f)) hY

/-- If the terminal object is quasicompact, every object whose map to it is quasicompact is
quasicompact. Without the assumption on the terminal object this fails: the identity of any
object is a quasicompact morphism. -/
theorem isQuasicompact_of_isTerminal {T X : C} (hT : IsTerminal T) (hTq : IsQuasicompact T)
    (hX : quasicompact (hT.from X)) : IsQuasicompact X :=
  isQuasicompact_of_quasicompact (hT.from X) hTq hX

/-! ### The topos of sets -/

/-- In the topos of sets, an object is quasicompact if and only if it is finite. -/
@[simp]
theorem isQuasicompact_iff_finite (X : Type u) : IsQuasicompact X ↔ Finite X := by
  simp only [isQuasicompact_iff, Types.effectiveEpiFamily_iff]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h (fun _ : X ↦ PUnit) (fun x ↦ TypeCat.ofHom fun _ ↦ x)
      fun x ↦ ⟨x, PUnit.unit, rfl⟩
    refine Finite.of_surjective (fun i : s ↦ (i : X)) fun x ↦ ?_
    obtain ⟨i, _, hi⟩ := hs x
    exact ⟨i, hi⟩
  · intro _ ι Y π hπ
    classical
    choose a y hy using hπ
    have := Fintype.ofFinite X
    refine ⟨Finset.univ.image a, fun x ↦ ⟨⟨a x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩,
      y x, hy x⟩⟩

/-- In the topos of sets, a monomorphism is quasicompact: a subset of a finite set is finite. -/
theorem monomorphisms_le_quasicompact_type : monomorphisms (Type u) ≤ quasicompact := by
  intro Y X f (_ : Mono f) Z W g fst snd h hZ
  rw [isQuasicompact_iff_finite] at hZ ⊢
  have : Mono fst := h.mono_fst_of_mono
  exact Finite.of_injective _ ((mono_iff_injective fst).mp this)

/-- In the topos of sets, every map is quasiseparated, its diagonal being a monomorphism. -/
theorem quasiseparated_type : (quasiseparated : MorphismProperty (Type u)) = ⊤ := by
  ext Y X f
  simp only [MorphismProperty.top_apply, iff_true]
  exact monomorphisms_le_quasicompact_type _ (monomorphisms.infer_property _)

/-- In the topos of sets, every object is quasiseparated: a fibre product of finite sets is
finite. -/
@[simp]
theorem isQuasiseparated_type (X : Type u) : IsQuasiseparated X := by
  intro Y Z W f g fst snd h hY hZ
  rw [isQuasicompact_iff_finite] at hY hZ ⊢
  refine Finite.of_injective (β := Y × Z) (fun w ↦ (fst w, snd w)) fun w w' hw ↦ ?_
  simp only [Prod.mk.injEq] at hw
  rw [← homOfElement_eq_iff]
  exact h.hom_ext (ConcreteCategory.hom_ext _ _ fun _ ↦ hw.1)
    (ConcreteCategory.hom_ext _ _ fun _ ↦ hw.2)

end TauCeti.Topos
