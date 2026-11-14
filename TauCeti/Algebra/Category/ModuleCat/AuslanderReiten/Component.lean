/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.CategoryTheory.IrreducibleMorphism
public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.Algebra.Category.ModuleCat.Biproducts.Regular
import TauCeti.Algebra.Category.ModuleCat.Connected
import TauCeti.Algebra.Category.ModuleCat.HaradaSai
import TauCeti.Algebra.Category.ModuleCat.Injective.LeftAlmostSplit
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Finiteness
import TauCeti.CategoryTheory.AlmostSplit.Irreducible
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Auslander's theorem on classes of bounded length

Let `A` be an Artinian ring, and `S` a nonempty class of finitely generated indecomposable
`A`-modules, closed under isomorphism and under irreducible maps of `mod A = FGModuleCat A` between
finitely generated indecomposable modules in both directions; the unions of components of the
Auslander–Reiten quiver are exactly such classes. **Auslander's theorem** says that if the lengths
of the modules in `S` are bounded, `A` is connected, and the modules in `S` that are not injective,
respectively not projective, in `FGModuleCat A` have source and sink maps in `FGModuleCat A`, then
`S` contains every finitely generated indecomposable module, and `A` is representation-finite.
Over a finite-dimensional algebra the source and sink maps come from the almost-split sequences,
and the hypothesis disappears (`TauCeti.forall_prop_and_isRepresentationFinite_of_length_le`).

The argument has three steps, all in `FGModuleCat A`.

* Every finitely generated indecomposable module has a source map, a left minimal left almost
  split map, into a finite biproduct of finitely generated indecomposable modules whose components
  are irreducible (`FGModuleCat.exists_isLeftAlmostSplit_biproduct`), and dually a sink map
  (`FGModuleCat.exists_isRightAlmostSplit_biproduct`). At injective and projective modules they are
  `N ⟶ N ⧸ soc N` and `rad P ⟶ P`.
* A nonzero morphism from a module in `S` to a finitely generated indecomposable module outside
  `S` factors through such a source map, giving a nonzero composite with an irreducible map that
  stays inside `S`. Repeating this gives arbitrarily long chains of non-isomorphisms in `S` with
  nonzero composites, which the Harada–Sai lemma forbids. So every morphism between `S` and a
  finitely generated indecomposable module outside `S`, in either direction, vanishes
  (`TauCeti.eq_zero_of_length_le_of_prop_of_not_prop` and
  `TauCeti.eq_zero_of_length_le_of_not_prop_of_prop`).
* The indecomposable summands of the regular module split into those in `S` and the others, with
  no nonzero morphisms between the two groups. The projection onto the first group is then right
  multiplication by a central idempotent of `A`
  (`TauCeti.forall_or_forall_of_forall_hom_eq_zero`, in
  `TauCeti/Algebra/Category/ModuleCat/Connected.lean`), so for connected `A` one group is empty.
  Since `S` is nonempty, every summand of the regular module lies in `S`, and every finitely
  generated indecomposable module receives a nonzero morphism from one of them, so it lies in `S`
  too. Iterating the source maps from the summands of the regular module then reaches only
  finitely many modules up to isomorphism (`TauCeti.exists_finite_forall_iso_of_hom_ne_zero`, the
  argument of the first Brauer–Thrall conjecture), so `A` is representation-finite.

## Main results

* `FGModuleCat.exists_isLeftAlmostSplit_biproduct` and
  `FGModuleCat.exists_isRightAlmostSplit_biproduct`: source and sink maps with irreducible
  components.
* `TauCeti.eq_zero_of_length_le_of_prop_of_not_prop` and
  `TauCeti.eq_zero_of_length_le_of_not_prop_of_prop`: the morphisms between a class of finitely
  generated indecomposable modules of bounded length closed under irreducible maps and a finitely
  generated indecomposable module outside it vanish.
* `TauCeti.forall_prop_and_isRepresentationFinite_of_length_le_of_isLeftAlmostSplit`:
  **Auslander's theorem** over an Artinian ring with source and sink maps, named after the
  analogous `TauCeti.isRepresentationFinite_of_length_le_of_isLeftAlmostSplit`.
* `TauCeti.forall_prop_and_isRepresentationFinite_of_length_le`: **Auslander's theorem** for a
  finite-dimensional algebra.

## References

* M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974), 269–310.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorem VI.1.4.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v w

namespace FGModuleCat

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]

/-- **Source maps.** Let `A` be an Artinian ring, and `X` a finitely generated indecomposable
module that, unless it is injective in `FGModuleCat A`, has a left minimal left almost split map in
`FGModuleCat A`. Then `X` has a left minimal left almost split map into a finite biproduct of
finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isLeftAlmostSplit_biproduct {X : FGModuleCat.{w} A} (hX : Indecomposable X.obj)
    (hsrc : ¬ Injective X → ∃ (E : FGModuleCat.{w} A) (i : X ⟶ E), IsLeftAlmostSplit i ∧
      ∀ u : E ⟶ E, i ≫ u = i → IsIso u) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (i : X ⟶ ⨁ F),
      (∀ j, Indecomposable (F j).obj) ∧ IsLeftAlmostSplit i ∧
        (∀ u : ⨁ F ⟶ ⨁ F, i ≫ u = i → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (i ≫ biproduct.π F j) := by
  have : IsLocalRing (End X) := isLocalRing_end_of_indecomposable hX
  -- A left minimal left almost split map.
  obtain ⟨E, f, hf, hmin⟩ : ∃ (E : FGModuleCat.{w} A) (f : X ⟶ E), IsLeftAlmostSplit f ∧
      ∀ u : E ⟶ E, f ≫ u = f → IsIso u := by
    by_cases hinj : Injective X
    · -- By Baer's criterion `X` is an injective module, with the source map `X ⟶ X ⧸ soc X`.
      have := moduleInjective_of_injective X
      have : Injective X.obj := Module.injective_object_of_injective_module A X
      have : IsLocalRing (End X.obj) := (indecomposable_iff_isLocalRing_end X.obj
        (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)).mp hX
      obtain ⟨S, -, hS⟩ := exists_isAtom_isLeftAlmostSplit_ofHom_mkQ (N := X.obj)
      let q : X ⟶ of A (X ⧸ S) := ObjectProperty.homMk (ModuleCat.ofHom S.mkQ)
      have : Epi q := (ObjectProperty.ι _).epi_of_epi_map
        ((ModuleCat.epi_iff_surjective _).mpr S.mkQ_surjective)
      refine ⟨_, q, (ObjectProperty.ι _).isLeftAlmostSplit_of_map q hS, fun u hu ↦ ?_⟩
      rw [(cancel_epi q).mp (hu.trans (Category.comp_id _).symm)]
      infer_instance
    · exact hsrc hinj
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, f ≫ e.hom, hF, hf.comp_iso e.hom, fun u hu ↦ ?_, fun j ↦ ?_⟩
  · -- Left minimality is invariant under the isomorphism `e`.
    have := hmin (e.hom ≫ u ≫ e.inv) (by
      rw [← Category.assoc, ← Category.assoc, hu, Category.assoc, e.hom_inv_id, Category.comp_id])
    simpa using (inferInstance : IsIso (e.inv ≫ (e.hom ≫ u ≫ e.inv) ≫ e.hom))
  · have hrad := comp_mem_jacobsonRadical_right hf.mem_jacobsonRadical (e.hom ≫ biproduct.π F j)
    rw [Category.assoc]
    exact hf.isIrreducibleMorphism_comp_of_isSplitEpi hmin _ fun _ ↦ (hF j).1
      ((ObjectProperty.ι _).map_isZero (isZero_of_isSplitEpi_of_mem_jacobsonRadical hrad))

/-- **Sink maps.** Let `A` be an Artinian ring, and `X` a finitely generated indecomposable module
that, unless it is projective in `FGModuleCat A`, has a right minimal right almost split map in
`FGModuleCat A`. Then `X` has a right minimal right almost split map out of a finite biproduct of
finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isRightAlmostSplit_biproduct {X : FGModuleCat.{w} A} (hX : Indecomposable X.obj)
    (hsink : ¬ Projective X → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ X), IsRightAlmostSplit p ∧
      ∀ u : E ⟶ E, u ≫ p = p → IsIso u) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (p : ⨁ F ⟶ X),
      (∀ j, Indecomposable (F j).obj) ∧ IsRightAlmostSplit p ∧
        (∀ u : ⨁ F ⟶ ⨁ F, u ≫ p = p → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (biproduct.ι F j ≫ p) := by
  have : IsLocalRing (End X) := isLocalRing_end_of_indecomposable hX
  -- A right minimal right almost split map.
  obtain ⟨E, g, hg, hmin⟩ : ∃ (E : FGModuleCat.{w} A) (g : E ⟶ X), IsRightAlmostSplit g ∧
      ∀ u : E ⟶ E, u ≫ g = g → IsIso u := by
    by_cases hproj : Projective X
    · -- `X` is a projective module, with the sink map `rad X ⟶ X`.
      have := moduleProjective_of_projective X
      have : IsLocalRing (End X.obj) :=
        ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).isLocalRing
      have : IsLocalRing (Module.End A X) := X.obj.endRingEquiv.isLocalRing
      let r : of A (Module.jacobson A X) ⟶ X := ofHom (Module.jacobson A X).subtype
      have : Mono r := (ObjectProperty.ι _).mono_of_mono_map
        ((ModuleCat.mono_iff_injective _).mpr (Module.jacobson A X).injective_subtype)
      refine ⟨_, r, isRightAlmostSplit_ofHom_subtype_jacobson A X, fun u hu ↦ ?_⟩
      rw [(cancel_mono r).mp (hu.trans (Category.id_comp _).symm)]
      infer_instance
    · exact hsink hproj
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, e.inv ≫ g, hF, hg.iso_comp e.inv, fun u hu ↦ ?_, fun j ↦ ?_⟩
  · -- Right minimality is invariant under the isomorphism `e`.
    have := hmin (e.hom ≫ u ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, hu, e.hom_inv_id_assoc])
    simpa using (inferInstance : IsIso (e.inv ≫ (e.hom ≫ u ≫ e.inv) ≫ e.hom))
  · have hrad := comp_mem_jacobsonRadical_left (biproduct.ι F j ≫ e.inv) hg.mem_jacobsonRadical
    rw [← Category.assoc]
    exact hg.isIrreducibleMorphism_comp_of_isSplitMono hmin _ fun _ ↦ (hF j).1
      ((ObjectProperty.ι _).map_isZero (isZero_of_isSplitMono_of_mem_jacobsonRadical hrad))

end FGModuleCat

namespace TauCeti

section Vanishing

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]
  (S : ObjectProperty (FGModuleCat.{w} A)) [S.IsClosedUnderIsomorphisms]
  (hS : ∀ X, S X → Indecomposable X.obj)
  (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b)

include hS hb

/-- **Morphisms out of a class of bounded length.** Let `A` be an Artinian ring, and `S` a class of
finitely generated indecomposable modules of bounded length, closed under isomorphism, whose
members that are not injective in `FGModuleCat A` have left minimal left almost split maps in
`FGModuleCat A`. If `S` contains the target of every irreducible map of `FGModuleCat A` out of one
of its members into a finitely generated indecomposable module, then every morphism from a module
in `S` to a finitely generated indecomposable module outside `S` is zero. -/
theorem eq_zero_of_length_le_of_prop_of_not_prop
    (hsrc : ∀ N, S N → ¬ Injective N → ∃ (E : FGModuleCat.{w} A) (i : N ⟶ E),
      IsLeftAlmostSplit i ∧ ∀ u : E ⟶ E, i ≫ u = i → IsIso u)
    (hirr : ∀ {X Y : FGModuleCat.{w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable Y.obj → S X → S Y)
    {X Y : FGModuleCat.{w} A} (hX : S X) (hY : Indecomposable Y.obj) (hSY : ¬ S Y) (f : X ⟶ Y) :
    f = 0 := by
  have : IsLocalRing (End Y) := FGModuleCat.isLocalRing_end_of_indecomposable hY
  -- A non-isomorphism into `Y` factors through the source map of a module in `S`, along an
  -- irreducible component whose target lies in `S` again.
  have hstep (Z : FGModuleCat.{w} A) (hZ : S Z) (c : X ⟶ Z) (g : Z ⟶ Y) (hg : ¬ IsIso g)
      (hc : c ≫ g ≠ 0) : ∃ E, S E ∧ ∃ (ι : Z ⟶ E) (t : E ⟶ Y), ¬ IsIso ι ∧ c ≫ ι ≫ t ≠ 0 := by
    have : IsLocalRing (End Z) := FGModuleCat.isLocalRing_end_of_indecomposable (hS Z hZ)
    obtain ⟨n, F, i, hF, hi, -, hirrF⟩ :=
      FGModuleCat.exists_isLeftAlmostSplit_biproduct (hS Z hZ) (hsrc Z hZ)
    obtain ⟨j, t, ht⟩ := hi.exists_comp_π_comp_ne_zero
      (mem_jacobsonRadical_iff_not_isSplitMono.mp (mem_jacobsonRadical_iff_not_isIso.mpr hg)) hc
    exact ⟨F j, hirr _ (hirrF j) (hF j) hZ, _, t, (hirrF j).not_isIso, ht⟩
  by_contra hf
  obtain ⟨Q, hQ, ⟨e⟩⟩ := S.exists_nonempty_iso_target_of_ne_zero
    (fun X hX hz ↦ (hS X hX).1 ((ObjectProperty.ι _).map_isZero hz)) hstep (2 ^ b - 1)
    (fun M f hM hf ↦ (ObjectProperty.ι _).map_injective <| by
      -- The Harada–Sai lemma, read in `ModuleCat A`.
      rw [Functor.map_zero]
      refine map_eq_zero_of_length_le (F := Functor.ofSequence f ⋙ ObjectProperty.ι _)
        (fun n ↦ hS _ (hM n)) (fun n ↦ hb _ (hM n)) (fun n h ↦ hf n ?_) _ (by omega)
      rw [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] at h
      exact (isIso_iff_of_reflects_iso (f n) (ObjectProperty.ι _)).mp h) hX hf
  exact hSY (S.prop_of_iso e.symm hQ)

/-- **Morphisms into a class of bounded length.** Let `A` be an Artinian ring, and `S` a class of
finitely generated indecomposable modules of bounded length, closed under isomorphism, whose
members that are not projective in `FGModuleCat A` have right minimal right almost split maps in
`FGModuleCat A`. If `S` contains the source of every irreducible map of `FGModuleCat A` from a
finitely generated indecomposable module into one of its members, then every morphism from a
finitely generated indecomposable module outside `S` to a module in `S` is zero. -/
theorem eq_zero_of_length_le_of_not_prop_of_prop
    (hsink : ∀ M, S M → ¬ Projective M → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ M),
      IsRightAlmostSplit p ∧ ∀ u : E ⟶ E, u ≫ p = p → IsIso u)
    (hirr : ∀ {X Y : FGModuleCat.{w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable X.obj → S Y → S X)
    {X Y : FGModuleCat.{w} A} (hX : Indecomposable X.obj) (hSX : ¬ S X) (hY : S Y) (f : X ⟶ Y) :
    f = 0 := by
  have : IsLocalRing (End X) := FGModuleCat.isLocalRing_end_of_indecomposable hX
  -- A non-isomorphism out of `X` factors through the sink map of a module in `S`, along an
  -- irreducible component whose source lies in `S` again.
  have hstep (Z : FGModuleCat.{w} A) (hZ : S Z) (c : Z ⟶ Y) (g : X ⟶ Z) (hg : ¬ IsIso g)
      (hc : g ≫ c ≠ 0) : ∃ E, S E ∧ ∃ (ι : E ⟶ Z) (t : X ⟶ E), ¬ IsIso ι ∧ t ≫ ι ≫ c ≠ 0 := by
    have : IsLocalRing (End Z) := FGModuleCat.isLocalRing_end_of_indecomposable (hS Z hZ)
    obtain ⟨n, F, p, hF, hp, -, hirrF⟩ :=
      FGModuleCat.exists_isRightAlmostSplit_biproduct (hS Z hZ) (hsink Z hZ)
    obtain ⟨j, t, ht⟩ := hp.exists_ι_comp_comp_ne_zero
      (mem_jacobsonRadical_iff_not_isSplitEpi.mp (mem_jacobsonRadical_iff_not_isIso.mpr hg)) hc
    exact ⟨F j, hirr _ (hirrF j) (hF j) hZ, _, t, (hirrF j).not_isIso, ht⟩
  by_contra hf
  obtain ⟨Q, hQ, ⟨e⟩⟩ := S.exists_nonempty_iso_source_of_ne_zero
    (fun X hX hz ↦ (hS X hX).1 ((ObjectProperty.ι _).map_isZero hz)) hstep (2 ^ b - 1)
    (fun M f hM hf ↦ (ObjectProperty.ι _).map_injective <| by
      -- The Harada–Sai lemma for descending chains, read in `ModuleCat A`.
      rw [Functor.map_zero]
      refine map_op_eq_zero_of_length_le (G := Functor.ofOpSequence f ⋙ ObjectProperty.ι _)
        (fun n ↦ hS _ (hM n)) (fun n ↦ hb _ (hM n)) (fun n h ↦ hf n ?_) le_rfl
      rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] at h
      exact (isIso_iff_of_reflects_iso (f n) (ObjectProperty.ι _)).mp h) hY hf
  exact hSX (S.prop_of_iso e.symm hQ)

end Vanishing

section Artinian

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]

/-- **Auslander's theorem from source and sink maps.** Let `A` be a connected Artinian ring, and
`S` a nonempty class of finitely generated indecomposable `A`-modules, closed under isomorphism
and under irreducible maps of `FGModuleCat A` between finitely generated indecomposable modules in
both directions. Suppose that the members of `S` that are not injective, respectively not
projective, in `FGModuleCat A` have left minimal left almost split maps, respectively right minimal
right almost split maps, in `FGModuleCat A`. If the lengths of the modules in `S` are bounded, then
`S` contains every finitely generated indecomposable module, and `A` is representation-finite. -/
theorem forall_prop_and_isRepresentationFinite_of_length_le_of_isLeftAlmostSplit
    (hA : centralIdempotents A ⊆ {0, 1})
    (S : ObjectProperty (FGModuleCat.{w} A)) [S.IsClosedUnderIsomorphisms]
    (hS : ∀ X, S X → Indecomposable X.obj)
    (hsrc : ∀ N, S N → ¬ Injective N → ∃ (E : FGModuleCat.{w} A) (i : N ⟶ E),
      IsLeftAlmostSplit i ∧ ∀ u : E ⟶ E, i ≫ u = i → IsIso u)
    (hsink : ∀ M, S M → ¬ Projective M → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ M),
      IsRightAlmostSplit p ∧ ∀ u : E ⟶ E, u ≫ p = p → IsIso u)
    (hirr : ∀ {X Y : FGModuleCat.{w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable X.obj → Indecomposable Y.obj → (S X ↔ S Y))
    (hne : ∃ X, S X) (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b) :
    (∀ X : FGModuleCat.{w} A, Indecomposable X.obj → S X) ∧ IsRepresentationFinite.{w} A := by
  have hfwd {X Y : FGModuleCat.{w} A} (hX : S X) (hY : Indecomposable Y.obj) (hSY : ¬ S Y)
      (f : X ⟶ Y) : f = 0 :=
    eq_zero_of_length_le_of_prop_of_not_prop S hS b hb hsrc
      (fun f hf hY hX ↦ (hirr f hf (hS _ hX) hY).mp hX) hX hY hSY f
  have hbwd {X Y : FGModuleCat.{w} A} (hX : S X) (hY : Indecomposable Y.obj) (hSY : ¬ S Y)
      (f : Y ⟶ X) : f = 0 :=
    eq_zero_of_length_le_of_not_prop_of_prop S hS b hb hsink
      (fun f hf hX hY ↦ (hirr f hf hX (hS _ hY)).mpr hY) hY hSY hX f
  -- The indecomposable summands of the regular module, as objects of `FGModuleCat A`.
  let eG := (Shrink.linearEquiv.{w} A A).symm
  let G : ModuleCat.{w} A := ModuleCat.of A (Shrink.{w} A)
  have : Module.Finite A G := Module.Finite.equiv eG
  obtain ⟨n, P, hP, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct G
  have hPf (j : Fin n) : (ModuleCat.isFG.{w} A) (P j) :=
    (ModuleCat.isFG_iff _).mpr (Module.Finite.of_surjective (e.hom ≫ biproduct.π P j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))
  let P' (j : Fin n) : FGModuleCat.{w} A := ⟨P j, hPf j⟩
  have homMk_ne_zero {X Y : FGModuleCat.{w} A} {f : X.obj ⟶ Y.obj} (hf : f ≠ 0) :
      ObjectProperty.homMk f ≠ 0 := fun h ↦ hf (by simpa using congrArg (ObjectProperty.ι _).map h)
  -- Connectedness puts every summand in `S`.
  have hPS (j : Fin n) : S (P' j) := by
    obtain ⟨X, hX⟩ := hne
    obtain ⟨i, f, hf⟩ := exists_hom_ne_zero_of_iso_biproduct eG e (hS X hX).1
    have hi : S (P' i) := by_contra fun h ↦ homMk_ne_zero hf (hbwd hX (hP i) h _)
    refine ((forall_or_forall_of_forall_hom_eq_zero hA eG e (fun j ↦ (hP j).1) (fun j ↦ S (P' j))
      fun a b ha hb ↦ ⟨fun f ↦ by_contra fun hf ↦ homMk_ne_zero hf (hfwd ha (hP b) hb _),
        fun f ↦ by_contra fun hf ↦ homMk_ne_zero hf (hbwd ha (hP b) hb _)⟩)
      |>.resolve_right fun h ↦ h i hi) j
  have hall (Y : FGModuleCat.{w} A) (hY : Indecomposable Y.obj) : S Y := by
    by_contra h
    -- A nonzero module receives a nonzero morphism from a summand of the regular module.
    obtain ⟨j, f, hf⟩ := exists_hom_ne_zero_of_iso_biproduct eG e hY.1
    exact homMk_ne_zero hf (hfwd (hPS j) hY h (Y := Y) _)
  -- Iterating source maps from the summands of the regular module reaches finitely many modules.
  obtain ⟨T, hT, -, hTmem⟩ := exists_finite_forall_iso_of_hom_ne_zero S
    (fun X hX ↦ FGModuleCat.isLocalRing_end_of_indecomposable (hS X hX))
    (fun X hX ↦ by
      obtain ⟨n, F, i, hF, hi, -, hirrF⟩ :=
        FGModuleCat.exists_isLeftAlmostSplit_biproduct (hS X hX) (hsrc X hX)
      exact ⟨n, F, i, fun j ↦ (hirr _ (hirrF j) (hS X hX) (hF j)).mp hX, hi⟩)
    (2 ^ b - 1)
    (fun M f hM hf ↦ (ObjectProperty.ι _).map_injective <| by
      -- The Harada–Sai lemma, read in `ModuleCat A`.
      rw [Functor.map_zero]
      refine map_eq_zero_of_length_le (F := Functor.ofSequence f ⋙ ObjectProperty.ι _)
        (fun n ↦ hS _ (hM n)) (fun n ↦ hb _ (hM n)) (fun n h ↦ hf n ?_) _ (by omega)
      rw [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] at h
      exact (isIso_iff_of_reflects_iso (f n) (ObjectProperty.ι _)).mp h)
    (Set.finite_range P') (by rintro _ ⟨j, rfl⟩; exact hPS j)
  refine ⟨hall, isRepresentationFinite_of_forall_exists_iso (hT.image (·.obj)) fun M hM hiM ↦ ?_⟩
  let Y : FGModuleCat.{w} A := ⟨M, (ModuleCat.isFG_iff _).mpr hM⟩
  obtain ⟨j, f, hf⟩ := exists_hom_ne_zero_of_iso_biproduct eG e hiM.1
  obtain ⟨Q, hQ, ⟨e'⟩⟩ := hTmem Y (hall Y hiM) (P' j) ⟨j, rfl⟩ _ (homMk_ne_zero (Y := Y) hf)
  exact ⟨Q.obj, ⟨Q, hQ, rfl⟩, ⟨(ObjectProperty.ι _).mapIso e'⟩⟩

end Artinian

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

include k in
/-- **Auslander's theorem.** Let `A` be a connected finite-dimensional algebra, and `S` a nonempty
class of finitely generated indecomposable `A`-modules, closed under isomorphism and under
irreducible maps of `FGModuleCat A` between finitely generated indecomposable modules in both
directions. If the lengths of the modules in `S` are bounded, then `S` contains every finitely
generated indecomposable module, and `A` is representation-finite. -/
theorem forall_prop_and_isRepresentationFinite_of_length_le (hA : centralIdempotents A ⊆ {0, 1})
    (S : ObjectProperty (FGModuleCat.{max u v w} A)) [S.IsClosedUnderIsomorphisms]
    (hS : ∀ X, S X → Indecomposable X.obj)
    (hirr : ∀ {X Y : FGModuleCat.{max u v w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable X.obj → Indecomposable Y.obj → (S X ↔ S Y))
    (hne : ∃ X, S X) (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b) :
    (∀ X : FGModuleCat.{max u v w} A, Indecomposable X.obj → S X) ∧
      IsRepresentationFinite.{max u v w} A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- The source and sink maps at non-injective and non-projective modules come from the
  -- almost-split sequences in `ModuleCat A`, restricted to `FGModuleCat A`.
  refine forall_prop_and_isRepresentationFinite_of_length_le_of_isLeftAlmostSplit hA S hS
    (fun N hN hinj ↦ ?_) (fun M hM hproj ↦ ?_) hirr hne b hb
  · have hinj' : ¬ Injective N.obj := fun _ ↦ hinj <| by
      have := Module.injective_module_of_injective_object A N
      exact FGModuleCat.injective_of_moduleInjective N
    obtain ⟨E, _, f, _, _, hE, -, hseq⟩ :=
      ModuleCat.exists_isAlmostSplit_of_not_injective k N.obj (hS N hN) hinj'
    refine ⟨⟨E, (ModuleCat.isFG_iff _).mpr hE⟩, ObjectProperty.homMk f,
      (ObjectProperty.ι _).isLeftAlmostSplit_of_map _ hseq.isLeftAlmostSplit_f, fun u hu ↦ ?_⟩
    have : IsIso ((ObjectProperty.ι _).map u) :=
      hseq.isIso_of_f_comp_eq u.hom (congrArg (ObjectProperty.ι _).map hu)
    exact isIso_of_fully_faithful (ObjectProperty.ι _) u
  · have hproj' : ¬ Projective M.obj := fun _ ↦ hproj <| by
      have := ModuleCat.projective_of_module_projective (R := A) M.obj
      exact FGModuleCat.projective_of_moduleProjective A M
    obtain ⟨E, _, p, _, hE, hseq⟩ :=
      ModuleCat.exists_isAlmostSplit_arTranslate k M.obj (hS M hM) hproj'
    refine ⟨⟨E, (ModuleCat.isFG_iff _).mpr hE⟩, ObjectProperty.homMk p,
      (ObjectProperty.ι _).isRightAlmostSplit_of_map _ hseq.isRightAlmostSplit_g, fun u hu ↦ ?_⟩
    have : IsIso ((ObjectProperty.ι _).map u) :=
      hseq.isIso_of_comp_g_eq u.hom (congrArg (ObjectProperty.ι _).map hu)
    exact isIso_of_fully_faithful (ObjectProperty.ι _) u

end TauCeti
