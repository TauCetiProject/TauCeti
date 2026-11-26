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
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Length
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Basic
import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.Sequence
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.Algebra.Category.ModuleCat.Connected
import TauCeti.Algebra.Category.ModuleCat.Length
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Finiteness
import TauCeti.CategoryTheory.Abelian.HaradaSai
import TauCeti.CategoryTheory.Generator.Biproduct
import TauCeti.CategoryTheory.Preadditive.CentralIdempotent
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Auslander's theorem on classes of bounded length

Let `A` be an Artinian ring, and `S` a nonempty class of finitely generated indecomposable
`A`-modules, closed under isomorphism and under irreducible maps of `mod A = FGModuleCat A` between
finitely generated indecomposable modules in both directions; the unions of components of the
Auslander–Reiten quiver are exactly such classes. **Auslander's theorem** says that if the lengths
of the modules in `S` are bounded, `A` is connected, and the modules in `S` that are not injective,
respectively not projective, in `FGModuleCat A` are the sources of left almost split maps,
respectively the targets of right almost split maps, in `FGModuleCat A`, then `S` contains every
finitely generated indecomposable module, and `A` is representation-finite. Over an Artin
algebra, a finite algebra over a commutative Artinian ring, these maps come from the almost-split
sequences, and the hypothesis disappears
(`TauCeti.forall_prop_and_isRepresentationFinite_of_length_le`).

The argument has three steps, all in `FGModuleCat A`.

* Every module in `S` has a source map, a left minimal left almost split map, into a finite
  biproduct of finitely generated indecomposable modules whose components are irreducible
  (`FGModuleCat.exists_isLeftAlmostSplit_biproduct`), and dually a sink map
  (`FGModuleCat.exists_isRightAlmostSplit_biproduct`): at a module that is not injective,
  respectively not projective, the assumed almost split map is made minimal, and at injective
  and projective modules they are `N ⟶ N ⧸ soc N` and `rad P ⟶ P`.
* A nonzero morphism from a module in `S` to a finitely generated indecomposable module outside
  `S` factors through such a source map, giving a nonzero composite with an irreducible map that
  stays inside `S`. Repeating this gives arbitrarily long chains of non-isomorphisms in `S` with
  nonzero composites, which the Harada–Sai lemma forbids. So every morphism between `S` and a
  finitely generated indecomposable module outside `S`, in either direction, vanishes
  (`CategoryTheory.ObjectProperty.eq_zero_of_length_le_of_prop_of_not_prop` and
  `CategoryTheory.ObjectProperty.eq_zero_of_length_le_of_not_prop_of_prop`).
* The indecomposable summands of the regular module split into those in `S` and the others, with
  no nonzero morphisms between the two groups. The projection onto the first group is then right
  multiplication by a central idempotent of `A`, so for connected `A` one group is empty
  (`TauCeti.forall_or_forall_not_of_forall_hom_eq_zero` and
  `TauCeti.centralIdempotents_end_subset_of_linearEquiv`).
  Since `S` is nonempty, every summand of the regular module lies in `S`, and every finitely
  generated indecomposable module receives a nonzero morphism from one of them, so it lies in `S`
  too. Iterating the source maps from the summands of the regular module then reaches only
  finitely many modules up to isomorphism (`TauCeti.exists_finite_forall_iso_of_hom_ne_zero`, the
  argument of the first Brauer–Thrall conjecture), so `A` is representation-finite.

## Main results

* `CategoryTheory.ObjectProperty.eq_zero_of_length_le_of_prop_of_not_prop` and
  `CategoryTheory.ObjectProperty.eq_zero_of_length_le_of_not_prop_of_prop`: the morphisms
  between a class of finitely generated indecomposable modules of bounded length closed under
  irreducible maps and a finitely generated indecomposable module outside it vanish.
* `TauCeti.forall_prop_and_isRepresentationFinite_of_isLeftAlmostSplit_of_isRightAlmostSplit`:
  **Auslander's theorem** over an Artinian ring with source and sink maps.
* `TauCeti.forall_prop_and_isRepresentationFinite_of_length_le`: **Auslander's theorem** for an
  Artin algebra.

## References

* M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974), 269–310.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorem VI.1.4.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v w

namespace CategoryTheory.ObjectProperty

section Vanishing

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]
  (S : ObjectProperty (FGModuleCat.{w} A)) [S.IsClosedUnderIsomorphisms]
  (hS : ∀ X, S X → Indecomposable X.obj)
  (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b)

include hS hb

omit [IsArtinianRing A] [Small.{w} A] [S.IsClosedUnderIsomorphisms] in
/-- The Harada–Sai lemma for sequences of non-isomorphisms in `S`, read in `FGModuleCat A`. -/
private theorem ofSequence_map_eq_zero_of_prop (M : ℕ → FGModuleCat.{w} A)
    (f : ∀ n, M n ⟶ M (n + 1)) (hM : ∀ n, S (M n)) (hf : ∀ n, ¬ IsIso (f n)) :
    (Functor.ofSequence f).map (homOfLE (Nat.zero_le (2 ^ b - 1))) = 0 :=
  (ObjectProperty.ι _).map_injective <| by
    rw [Functor.map_zero]
    refine map_eq_zero_of_length_le (F := Functor.ofSequence f ⋙ ObjectProperty.ι _)
      (fun n ↦ hS _ (hM n)) (fun n ↦ (ModuleCat.length_eq _).trans_le (hb _ (hM n)))
      (fun n h ↦ hf n ?_) _ (by omega)
    rw [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] at h
    exact (isIso_iff_of_reflects_iso (f n) (ObjectProperty.ι _)).mp h

/-- **Morphisms out of a class of bounded length.** Let `A` be an Artinian ring, and `S` a class of
finitely generated indecomposable modules of bounded length, closed under isomorphism, whose
members that are not injective in `FGModuleCat A` have left almost split maps in
`FGModuleCat A`. If `S` contains the target of every irreducible map of `FGModuleCat A` out of one
of its members into a finitely generated indecomposable module, then every morphism from a module
in `S` to a finitely generated indecomposable module outside `S` is zero. -/
theorem eq_zero_of_length_le_of_prop_of_not_prop
    (hsrc : ∀ N, S N → ¬ Injective N → ∃ (E : FGModuleCat.{w} A) (i : N ⟶ E),
      IsLeftAlmostSplit i)
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
  obtain ⟨Q, hQ, ⟨e⟩⟩ := S.exists_nonempty_iso_target_of_ne_zero hstep (2 ^ b - 1)
    (ofSequence_map_eq_zero_of_prop S hS b hb) hX hf
  exact hSY (S.prop_of_iso e.symm hQ)

/-- **Morphisms into a class of bounded length.** Let `A` be an Artinian ring, and `S` a class of
finitely generated indecomposable modules of bounded length, closed under isomorphism, whose
members that are not projective in `FGModuleCat A` are the targets of right almost split maps
in `FGModuleCat A`. If `S` contains the source of every irreducible map of `FGModuleCat A` from a
finitely generated indecomposable module into one of its members, then every morphism from a
finitely generated indecomposable module outside `S` to a module in `S` is zero. -/
theorem eq_zero_of_length_le_of_not_prop_of_prop
    (hsink : ∀ M, S M → ¬ Projective M → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ M),
      IsRightAlmostSplit p)
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
  obtain ⟨Q, hQ, ⟨e⟩⟩ := S.exists_nonempty_iso_source_of_ne_zero hstep (2 ^ b - 1)
    (fun M f hM hf ↦ (ObjectProperty.ι _).map_injective <| by
      -- The Harada–Sai lemma for descending chains, read in `ModuleCat A`.
      rw [Functor.map_zero]
      refine map_op_eq_zero_of_length_le (G := Functor.ofOpSequence f ⋙ ObjectProperty.ι _)
        (fun n ↦ hS _ (hM n)) (fun n ↦ (ModuleCat.length_eq _).trans_le (hb _ (hM n)))
        (fun n h ↦ hf n ?_) _ (by omega)
      rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] at h
      exact (isIso_iff_of_reflects_iso (f n) (ObjectProperty.ι _)).mp h) hY hf
  exact hSX (S.prop_of_iso e.symm hQ)

end Vanishing

end CategoryTheory.ObjectProperty

namespace TauCeti

section Artinian

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]

/-- **Auslander's theorem from source and sink maps.** Let `A` be a connected Artinian ring, and
`S` a nonempty class of finitely generated indecomposable `A`-modules, closed under isomorphism
and under irreducible maps of `FGModuleCat A` between finitely generated indecomposable modules in
both directions. Suppose that the members of `S` that are not injective, respectively not
projective, in `FGModuleCat A` have left almost split maps out of them, respectively right almost
split maps into them, in `FGModuleCat A`. If the lengths of the modules in `S` are bounded, then
`S` contains every finitely generated indecomposable module, and `A` is representation-finite. -/
theorem forall_prop_and_isRepresentationFinite_of_isLeftAlmostSplit_of_isRightAlmostSplit
    (hA : centralIdempotents A ⊆ {0, 1})
    (S : ObjectProperty (FGModuleCat.{w} A)) [S.IsClosedUnderIsomorphisms]
    (hS : ∀ X, S X → Indecomposable X.obj)
    (hsrc : ∀ N, S N → ¬ Injective N → ∃ (E : FGModuleCat.{w} A) (i : N ⟶ E),
      IsLeftAlmostSplit i)
    (hsink : ∀ M, S M → ¬ Projective M → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ M),
      IsRightAlmostSplit p)
    (hirr : ∀ {X Y : FGModuleCat.{w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable X.obj → Indecomposable Y.obj → (S X ↔ S Y))
    (hne : ∃ X, S X) (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b) :
    (∀ X : FGModuleCat.{w} A, Indecomposable X.obj → S X) ∧ IsRepresentationFinite.{w} A := by
  have hfwd {X Y : FGModuleCat.{w} A} (hX : S X) (hY : Indecomposable Y.obj) (hSY : ¬ S Y)
      (f : X ⟶ Y) : f = 0 :=
    S.eq_zero_of_length_le_of_prop_of_not_prop hS b hb hsrc
      (fun f hf hY hX ↦ (hirr f hf (hS _ hX) hY).mp hX) hX hY hSY f
  have hbwd {X Y : FGModuleCat.{w} A} (hX : S X) (hY : Indecomposable Y.obj) (hSY : ¬ S Y)
      (f : Y ⟶ X) : f = 0 :=
    S.eq_zero_of_length_le_of_not_prop_of_prop hS b hb hsink
      (fun f hf hX hY ↦ (hirr f hf hX (hS _ hY)).mpr hY) hY hSY hX f
  -- The indecomposable summands of the regular module, as objects of `FGModuleCat A`.
  let eG := (Shrink.linearEquiv.{w} A A).symm
  let G : ModuleCat.{w} A := ModuleCat.of A (Shrink.{w} A)
  have : Module.Finite A G := Module.Finite.equiv eG
  have hG : IsSeparator G := ModuleCat.isSeparator A
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
    obtain ⟨i, f, hf⟩ := hG.exists_hom_ne_zero_of_iso_biproduct e (hS X hX).1
    have hi : S (P' i) := by_contra fun h ↦ homMk_ne_zero hf (hbwd hX (hP i) h _)
    refine ((forall_or_forall_not_of_forall_hom_eq_zero
      (centralIdempotents_end_subset_of_linearEquiv hA eG) e (fun j ↦ (hP j).1) (fun j ↦ S (P' j))
      fun a b ha hb ↦ ⟨fun f ↦ by_contra fun hf ↦ homMk_ne_zero hf (hfwd ha (hP b) hb _),
        fun f ↦ by_contra fun hf ↦ homMk_ne_zero hf (hbwd ha (hP b) hb _)⟩)
      |>.resolve_right fun h ↦ h i hi) j
  have hall (Y : FGModuleCat.{w} A) (hY : Indecomposable Y.obj) : S Y := by
    by_contra h
    -- A nonzero module receives a nonzero morphism from a summand of the regular module.
    obtain ⟨j, f, hf⟩ := hG.exists_hom_ne_zero_of_iso_biproduct e hY.1
    exact homMk_ne_zero hf (hfwd (hPS j) hY h (Y := Y) _)
  -- Iterating source maps from the summands of the regular module reaches finitely many modules.
  obtain ⟨T, hT, -, hTmem⟩ := exists_finite_forall_iso_of_hom_ne_zero S
    (fun X hX ↦ FGModuleCat.isLocalRing_end_of_indecomposable (hS X hX))
    (fun X hX ↦ by
      obtain ⟨n, F, i, hF, hi, -, hirrF⟩ :=
        FGModuleCat.exists_isLeftAlmostSplit_biproduct (hS X hX) (hsrc X hX)
      exact ⟨n, F, i, fun j ↦ (hirr _ (hirrF j) (hS X hX) (hF j)).mp hX, hi⟩)
    (2 ^ b - 1) (S.ofSequence_map_eq_zero_of_prop hS b hb) (Set.finite_range P')
    (by rintro _ ⟨j, rfl⟩; exact hPS j)
  refine ⟨hall, isRepresentationFinite_iff_exists_finite_forall_exists_iso.mpr
    ⟨_, hT.image (·.obj), fun M hM hiM ↦ ?_⟩⟩
  let Y : FGModuleCat.{w} A := ⟨M, (ModuleCat.isFG_iff _).mpr hM⟩
  obtain ⟨j, f, hf⟩ := hG.exists_hom_ne_zero_of_iso_biproduct e hiM.1
  obtain ⟨Q, hQ, ⟨e'⟩⟩ := hTmem Y (hall Y hiM) (P' j) ⟨j, rfl⟩ _ (homMk_ne_zero (Y := Y) hf)
  exact ⟨Q.obj, ⟨Q, hQ, rfl⟩, ⟨(ObjectProperty.ι _).mapIso e'⟩⟩

end Artinian

variable (R : Type u) [CommRing R] [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A]
  [Module.Finite R A] [Small.{w} A]

include R in
/-- **Auslander's theorem.** Let `A` be a connected Artin algebra over a commutative Artinian ring
`R`, and `S` a nonempty class of finitely generated indecomposable `A`-modules, closed under
isomorphism and under irreducible maps of `FGModuleCat A` between finitely generated
indecomposable modules in both directions. If the lengths of the modules in `S` are bounded, then
`S` contains every finitely generated indecomposable module, and `A` is representation-finite. The
modules may live in any universe in which `A` is small. -/
theorem forall_prop_and_isRepresentationFinite_of_length_le (hA : centralIdempotents A ⊆ {0, 1})
    (S : ObjectProperty (FGModuleCat.{w} A)) [S.IsClosedUnderIsomorphisms]
    (hS : ∀ X, S X → Indecomposable X.obj)
    (hirr : ∀ {X Y : FGModuleCat.{w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Indecomposable X.obj → Indecomposable Y.obj → (S X ↔ S Y))
    (hne : ∃ X, S X) (b : ℕ) (hb : ∀ X, S X → Module.length A X.obj ≤ b) :
    (∀ X : FGModuleCat.{w} A, Indecomposable X.obj → S X) ∧ IsRepresentationFinite.{w} A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  -- The source and sink maps at non-injective and non-projective modules are the end maps of the
  -- almost-split sequences of `FGModuleCat A`, moved to the given module along the end isomorphism.
  refine forall_prop_and_isRepresentationFinite_of_isLeftAlmostSplit_of_isRightAlmostSplit hA S hS
    (fun N hN hinj ↦ ?_) (fun M hM hproj ↦ ?_) hirr hne b hb
  · obtain ⟨T, hT, ⟨e⟩⟩ := FGModuleCat.exists_isAlmostSplit_of_not_injective R N
      ((FGModuleCat.indecomposable_obj_iff N).mp (hS N hN)) hinj
    exact ⟨T.X₂, e.inv ≫ T.f, hT.isLeftAlmostSplit_f.iso_comp e.inv⟩
  · obtain ⟨T, hT, ⟨e⟩⟩ := FGModuleCat.exists_isAlmostSplit R M
      ((FGModuleCat.indecomposable_obj_iff M).mp (hS M hM)) hproj
    exact ⟨T.X₂, T.g ≫ e.hom, hT.isRightAlmostSplit_g.comp_iso e.hom⟩

end TauCeti
