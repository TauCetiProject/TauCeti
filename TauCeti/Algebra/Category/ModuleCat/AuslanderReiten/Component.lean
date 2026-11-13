/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.CategoryTheory.IrreducibleMorphism
public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.BrauerThrall
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
import TauCeti.Algebra.Category.ModuleCat.HaradaSai
import TauCeti.Algebra.Category.ModuleCat.Injective.LeftAlmostSplit
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Projective.RightAlmostSplit
import TauCeti.CategoryTheory.AlmostSplit.Finiteness
import TauCeti.CategoryTheory.AlmostSplit.Irreducible
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Auslander's theorem on classes of bounded length

Let `A` be a finite-dimensional algebra over a field `k`, and `S` a class of finitely generated
indecomposable `A`-modules, closed under isomorphism and under irreducible maps between finitely
generated indecomposable modules in both directions; the unions of components of the
Auslander–Reiten quiver are exactly such classes. **Auslander's theorem** says that if the lengths
of the modules in `S` are bounded and `A` is connected, then `S` contains every finitely generated
indecomposable module, and `A` is representation-finite.

The argument has three steps.

* Every finitely generated indecomposable module has a left almost split map into a finite
  biproduct of finitely generated indecomposable modules whose components are irreducible
  (`ModuleCat.exists_isLeftAlmostSplit_biproduct`), and dually a right almost split map
  (`ModuleCat.exists_isRightAlmostSplit_biproduct`). They come from the almost-split sequences,
  and at injective and projective modules from `N ⟶ N ⧸ soc N` and `rad P ⟶ P`.
* A nonzero morphism from a module in `S` to an indecomposable module outside `S` factors through
  such a left almost split map, giving a nonzero composite with an irreducible map that stays
  inside `S`. Repeating this gives arbitrarily long chains of non-isomorphisms in `S` with nonzero
  composites, which the Harada–Sai lemma forbids. So every morphism between `S` and an
  indecomposable module outside `S`, in either direction, vanishes
  (`TauCeti.eq_zero_of_prop_of_not_prop` and `TauCeti.eq_zero_of_not_prop_of_prop`).
* The indecomposable summands of the regular module split into those in `S` and the others, with
  no nonzero morphisms between the two groups. The projection onto the first group is then right
  multiplication by a central idempotent of `A`
  (`TauCeti.forall_or_forall_of_forall_hom_eq_zero`), so for connected `A` one group is empty.
  Since `S` is nonempty, every summand of the regular module lies in `S`, and every indecomposable
  module receives a nonzero morphism from one of them, so it lies in `S` too. The first
  Brauer–Thrall conjecture, `TauCeti.isRepresentationFinite_of_length_le`, then shows that `A` is
  representation-finite.

## Main results

* `ModuleCat.exists_isLeftAlmostSplit_biproduct` and
  `ModuleCat.exists_isRightAlmostSplit_biproduct`: source and sink maps with irreducible
  components.
* `TauCeti.eq_zero_of_prop_of_not_prop` and `TauCeti.eq_zero_of_not_prop_of_prop`: the morphisms
  between a class of bounded length closed under irreducible maps and an indecomposable module
  outside it vanish.
* `TauCeti.forall_or_forall_of_forall_hom_eq_zero`: over a connected ring, the indecomposable
  summands of the regular module admit no splitting into two groups without morphisms between
  them.
* `TauCeti.forall_prop_and_isRepresentationFinite_of_length_le`: **Auslander's theorem**.

## References

* M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974), 269–310.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorem VI.1.4.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti
open scoped ModuleCat.Algebra

universe u v w

namespace ModuleCat

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

include k in
/-- **Source maps.** Over a finite-dimensional algebra, a finitely generated indecomposable module
`X` has a left almost split map into a finite biproduct of finitely generated indecomposable
modules, each of whose components is irreducible. -/
theorem exists_isLeftAlmostSplit_biproduct (X : ModuleCat.{max u v w} A) [Module.Finite A X]
    (hX : Indecomposable X) :
    ∃ (n : ℕ) (F : Fin n → ModuleCat.{max u v w} A) (i : X ⟶ ⨁ F),
      (∀ j, Module.Finite A (F j) ∧ Indecomposable (F j)) ∧ IsLeftAlmostSplit i ∧
        ∀ j, IsIrreducibleMorphism (i ≫ biproduct.π F j) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsLocalRing (End X) := isLocalRing_end_of_indecomposable (R := k) hX
  -- A left minimal left almost split map with finitely generated target.
  obtain ⟨E, f, hE, hf, hmin⟩ : ∃ (E : ModuleCat.{max u v w} A) (f : X ⟶ E), Module.Finite A E ∧
      IsLeftAlmostSplit f ∧ ∀ u : E ⟶ E, f ≫ u = f → IsIso u := by
    by_cases hinj : Injective X
    · obtain ⟨S, -, hS⟩ := exists_isAtom_isLeftAlmostSplit_ofHom_mkQ (N := X)
      refine ⟨_, _, inferInstanceAs (Module.Finite A (X ⧸ S)), hS, fun u hu ↦ ?_⟩
      have : Epi (ofHom S.mkQ) := (epi_iff_surjective _).mpr S.mkQ_surjective
      rw [(cancel_epi (ofHom S.mkQ)).mp (hu.trans (Category.comp_id _).symm)]
      infer_instance
    · obtain ⟨E, M, f, p, h, hE, -, hS⟩ := exists_isAlmostSplit_of_not_injective k X hX hinj
      exact ⟨E, f, hE, hS.isLeftAlmostSplit_f, hS.isIso_of_f_comp_eq⟩
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, f ≫ e.hom, fun j ↦ ⟨?_, hF j⟩, hf.comp_iso e.hom, fun j ↦ ?_⟩
  · exact Module.Finite.of_surjective (e.hom ≫ biproduct.π F j).hom
      ((epi_iff_surjective _).mp inferInstance)
  · have hrad := comp_mem_jacobsonRadical_right
      (mem_jacobsonRadical_iff_not_isSplitMono.mpr hf.not_isSplitMono) (e.hom ≫ biproduct.π F j)
    rw [Category.assoc]
    exact hf.isIrreducibleMorphism_comp_of_isSplitEpi hmin _ fun _ ↦
      (hF j).1 (isZero_of_isSplitEpi_of_mem_jacobsonRadical hrad)

include k in
/-- **Sink maps.** Over a finite-dimensional algebra, a finitely generated indecomposable module
`X` has a right almost split map out of a finite biproduct of finitely generated indecomposable
modules, each of whose components is irreducible. -/
theorem exists_isRightAlmostSplit_biproduct (X : ModuleCat.{max u v w} A) [Module.Finite A X]
    (hX : Indecomposable X) :
    ∃ (n : ℕ) (F : Fin n → ModuleCat.{max u v w} A) (p : ⨁ F ⟶ X),
      (∀ j, Module.Finite A (F j) ∧ Indecomposable (F j)) ∧ IsRightAlmostSplit p ∧
        ∀ j, IsIrreducibleMorphism (biproduct.ι F j ≫ p) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsLocalRing (End X) := isLocalRing_end_of_indecomposable (R := k) hX
  -- A right minimal right almost split map with finitely generated source.
  obtain ⟨E, g, hE, hg, hmin⟩ : ∃ (E : ModuleCat.{max u v w} A) (g : E ⟶ X), Module.Finite A E ∧
      IsRightAlmostSplit g ∧ ∀ u : E ⟶ E, u ≫ g = g → IsIso u := by
    by_cases hproj : Projective X
    · refine ⟨_, _, inferInstanceAs (Module.Finite A (Module.jacobson A X)),
        isRightAlmostSplit_ofHom_subtype_jacobson, fun u hu ↦ ?_⟩
      have : Mono (ofHom (Module.jacobson A X).subtype) :=
        (mono_iff_injective _).mpr (Module.jacobson A X).injective_subtype
      rw [(cancel_mono (ofHom (Module.jacobson A X).subtype)).mp
        (hu.trans (Category.id_comp _).symm)]
      infer_instance
    · obtain ⟨E, i, p, h, hE, hS⟩ := exists_isAlmostSplit_arTranslate k X hX hproj
      exact ⟨E, p, hE, hS.isRightAlmostSplit_g, hS.isIso_of_comp_g_eq⟩
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, e.inv ≫ g, fun j ↦ ⟨?_, hF j⟩, hg.iso_comp e.inv, fun j ↦ ?_⟩
  · exact Module.Finite.of_surjective (e.hom ≫ biproduct.π F j).hom
      ((epi_iff_surjective _).mp inferInstance)
  · have hrad := comp_mem_jacobsonRadical_left (biproduct.ι F j ≫ e.inv)
      (mem_jacobsonRadical_iff_not_isSplitEpi.mpr hg.not_isSplitEpi)
    rw [← Category.assoc]
    exact hg.isIrreducibleMorphism_comp_of_isSplitMono hmin _ fun _ ↦
      (hF j).1 (isZero_of_isSplitMono_of_mem_jacobsonRadical hrad)

end ModuleCat

namespace TauCeti

section Vanishing

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (S : ObjectProperty (ModuleCat.{max u v w} A)) [S.IsClosedUnderIsomorphisms]
  (hS : ∀ X, S X → Module.Finite A X ∧ Indecomposable X)
  (b : ℕ) (hb : ∀ X, S X → Module.length A X ≤ b)

include k hS hb

/-- **Morphisms out of a class of bounded length.** Over a finite-dimensional algebra, let `S` be a
class of finitely generated indecomposable modules of bounded length, closed under isomorphism,
that contains the target of every irreducible map out of one of its members into a finitely
generated indecomposable module. Then every morphism from a module in `S` to a finitely generated
indecomposable module outside `S` is zero. -/
theorem eq_zero_of_prop_of_not_prop
    (hirr : ∀ {X Y : ModuleCat.{max u v w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Module.Finite A Y → Indecomposable Y → S X → S Y)
    {X Y : ModuleCat.{max u v w} A} (hX : S X) [Module.Finite A Y] (hY : Indecomposable Y)
    (hSY : ¬ S Y) (f : X ⟶ Y) : f = 0 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsLocalRing (End Y) := isLocalRing_end_of_indecomposable (R := k) hY
  -- A non-isomorphism into `Y` factors through the source map of a module in `S`, along an
  -- irreducible component whose target lies in `S` again.
  have hstep (Z : ModuleCat.{max u v w} A) (hZ : S Z) (c : X ⟶ Z) (g : Z ⟶ Y) (hg : ¬ IsIso g)
      (hc : c ≫ g ≠ 0) : ∃ E, S E ∧ ∃ (ι : Z ⟶ E) (t : E ⟶ Y), ¬ IsIso ι ∧ c ≫ ι ≫ t ≠ 0 := by
    have := (hS Z hZ).1
    have : IsLocalRing (End Z) := isLocalRing_end_of_indecomposable (R := k) (hS Z hZ).2
    obtain ⟨n, F, i, hF, hi, hirrF⟩ := ModuleCat.exists_isLeftAlmostSplit_biproduct k Z (hS Z hZ).2
    obtain ⟨j, t, ht⟩ := hi.exists_comp_π_comp_ne_zero
      (mem_jacobsonRadical_iff_not_isSplitMono.mp (mem_jacobsonRadical_iff_not_isIso.mpr hg)) hc
    exact ⟨F j, hirr _ (hirrF j) (hF j).1 (hF j).2 hZ, _, t,
      fun _ ↦ (hirrF j).not_isSplitMono inferInstance, ht⟩
  by_contra hf
  obtain ⟨Q, hQ, ⟨e⟩⟩ := exists_nonempty_iso_target_of_ne_zero S (fun X hX ↦ (hS X hX).2.1)
    hstep (2 ^ b - 1) (fun M f hM hf ↦ ofSequence_map_eq_zero_of_length_le f
      (fun n ↦ (hS _ (hM n)).2) (fun n ↦ hb _ (hM n)) hf le_rfl) hX hf
  exact hSY (S.prop_of_iso e.symm hQ)

/-- **Morphisms into a class of bounded length.** Over a finite-dimensional algebra, let `S` be a
class of finitely generated indecomposable modules of bounded length, closed under isomorphism,
that contains the source of every irreducible map from a finitely generated indecomposable module
into one of its members. Then every morphism to a module in `S` from a finitely generated
indecomposable module outside `S` is zero. -/
theorem eq_zero_of_not_prop_of_prop
    (hirr : ∀ {X Y : ModuleCat.{max u v w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Module.Finite A X → Indecomposable X → S Y → S X)
    {X Y : ModuleCat.{max u v w} A} (hX : S X) [Module.Finite A Y] (hY : Indecomposable Y)
    (hSY : ¬ S Y) (f : Y ⟶ X) : f = 0 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsLocalRing (End Y) := isLocalRing_end_of_indecomposable (R := k) hY
  -- A non-isomorphism out of `Y` factors through the sink map of a module in `S`, along an
  -- irreducible component whose source lies in `S` again.
  have hstep (Z : ModuleCat.{max u v w} A) (hZ : S Z) (c : Z ⟶ X) (g : Y ⟶ Z) (hg : ¬ IsIso g)
      (hc : g ≫ c ≠ 0) : ∃ E, S E ∧ ∃ (ι : E ⟶ Z) (t : Y ⟶ E), ¬ IsIso ι ∧ t ≫ ι ≫ c ≠ 0 := by
    have := (hS Z hZ).1
    have : IsLocalRing (End Z) := isLocalRing_end_of_indecomposable (R := k) (hS Z hZ).2
    obtain ⟨n, F, p, hF, hp, hirrF⟩ :=
      ModuleCat.exists_isRightAlmostSplit_biproduct k Z (hS Z hZ).2
    obtain ⟨j, t, ht⟩ := hp.exists_ι_comp_comp_ne_zero
      (mem_jacobsonRadical_iff_not_isSplitEpi.mp (mem_jacobsonRadical_iff_not_isIso.mpr hg)) hc
    exact ⟨F j, hirr _ (hirrF j) (hF j).1 (hF j).2 hZ, _, t,
      fun _ ↦ (hirrF j).not_isSplitMono inferInstance, ht⟩
  by_contra hf
  obtain ⟨Q, hQ, ⟨e⟩⟩ := exists_nonempty_iso_source_of_ne_zero S (fun X hX ↦ (hS X hX).2.1)
    hstep (2 ^ b - 1) (fun M f hM hf ↦ ofOpSequence_map_eq_zero_of_length_le f
      (fun n ↦ (hS _ (hM n)).2) (fun n ↦ hb _ (hM n)) hf le_rfl) hX hf
  exact hSY (S.prop_of_iso e.symm hQ)

end Vanishing

section Connected

variable {A : Type v} [Ring A]

/-- **Connected rings admit no Hom-orthogonal splitting of the regular module.** Let the regular
module of a ring `A` without central idempotents other than `0` and `1` be a finite biproduct of
nonzero modules `P j`. If no nonzero morphism, in either direction, joins a summand satisfying a
predicate `p` to one that does not, then either all summands satisfy `p` or none does. -/
theorem forall_or_forall_of_forall_hom_eq_zero (hA : centralIdempotents A ⊆ {0, 1}) {n : ℕ}
    {P : Fin n → ModuleCat.{max v w} A} (e : ModuleCat.of A (ULift.{w} A) ≅ ⨁ P)
    (hP : ∀ j, ¬ IsZero (P j)) (p : Fin n → Prop)
    (hp : ∀ a b, p a → ¬ p b → (∀ f : P a ⟶ P b, f = 0) ∧ ∀ f : P b ⟶ P a, f = 0) :
    (∀ j, p j) ∨ ∀ j, ¬ p j := by
  classical
  let G := ModuleCat.of A (ULift.{w} A)
  -- Every endomorphism of the regular module is right multiplication by the image of `1`.
  have hom_apply_up_down (φ : G ⟶ G) (a : A) :
      (φ.hom (ULift.up a)).down = a * (φ.hom (ULift.up 1)).down := by
    have h : (ULift.up a : ULift.{w} A) = a • ULift.up 1 := by ext; simp
    rw [h, map_smul, ULift.smul_down, smul_eq_mul]
  -- The projection onto the summands satisfying `p`.
  let d (j : Fin n) : P j ⟶ P j := if p j then 𝟙 _ else 0
  let σ : ⨁ P ⟶ ⨁ P := biproduct.map d
  have hσ (ψ : ⨁ P ⟶ ⨁ P) : ψ ≫ σ = σ ≫ ψ := by
    refine biproduct.hom_ext' _ _ fun a ↦ biproduct.hom_ext _ _ fun b ↦ ?_
    simp only [σ, Category.assoc, biproduct.map_π, biproduct.ι_map_assoc, d]
    by_cases ha : p a <;> by_cases hb : p b <;>
      simp only [ha, hb, ↓reduceIte, Category.comp_id, Category.id_comp, comp_zero, zero_comp]
    · exact ((hp a b ha hb).1 _).symm
    · exact (hp b a hb ha).2 _
  have hσσ : σ ≫ σ = σ := by
    refine biproduct.hom_ext' _ _ fun a ↦ ?_
    by_cases ha : p a <;> simp [σ, d, ha]
  -- Transported to the regular module, `σ` is right multiplication by a central idempotent.
  let E : G ⟶ G := e.hom ≫ σ ≫ e.inv
  have hE (φ : G ⟶ G) : φ ≫ E = E ≫ φ := by
    have h := hσ (e.inv ≫ φ ≫ e.hom)
    simp only [Category.assoc] at h
    simp only [E, ← Category.assoc, ← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← cancel_epi e.inv]
    simpa using h
  let ε : A := (E.hom (ULift.up 1)).down
  have hE1 : E.hom (ULift.up 1) = ULift.up ε := rfl
  have hcentral : ε ∈ centralIdempotents A := by
    refine mem_centralIdempotents.mpr ⟨?_, Subring.mem_center_iff.mpr fun x ↦ ?_⟩
    · have h := congrArg (fun φ : G ⟶ G ↦ (φ.hom (ULift.up 1)).down)
        (show E ≫ E = E by simp [E, reassoc_of% hσσ])
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hE1] at h
      exact (hom_apply_up_down E ε).symm.trans h
    · -- Compare `E` with right multiplication by `x`.
      let φ : G ⟶ G := ModuleCat.ofHom (LinearMap.toSpanSingleton A G (ULift.up x) ∘ₗ
        (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)
      have hφ (a : A) : φ.hom (ULift.up a) = ULift.up (a * x) := rfl
      have h := congrArg (fun ψ : G ⟶ G ↦ (ψ.hom (ULift.up 1)).down) (hE φ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hφ, one_mul, hE1] at h
      exact (hom_apply_up_down E x).symm.trans h
  -- Then `σ` is `0` or the identity, which pins down `p` on the summands.
  have hσE : σ = e.inv ≫ E ≫ e.hom := by simp [E]
  rcases hA hcentral with h0 | h1
  · right
    intro j hj
    have hE0 : E = 0 := by
      ext x
      exact (hom_apply_up_down E x.down).trans (by simp [ε] at h0; simp [h0])
    have hσ0 : σ = 0 := by rw [hσE, hE0, zero_comp, comp_zero]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ0
  · left
    intro j
    by_contra hj
    have hE1 : E = 𝟙 G := by
      ext x
      exact (hom_apply_up_down E x.down).trans (by simp [ε] at h1; simp [h1])
    have hσ1 : σ = 𝟙 _ := by rw [hσE, hE1, Category.id_comp, Iso.inv_hom_id]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using (congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ1).symm

end Connected

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

include k in
/-- **Auslander's theorem.** Let `A` be a connected finite-dimensional algebra, and `S` a nonempty
class of finitely generated indecomposable `A`-modules, closed under isomorphism and under
irreducible maps between finitely generated indecomposable modules in both directions. If the
lengths of the modules in `S` are bounded, then `S` contains every finitely generated
indecomposable module, and `A` is representation-finite. -/
theorem forall_prop_and_isRepresentationFinite_of_length_le (hA : centralIdempotents A ⊆ {0, 1})
    (S : ObjectProperty (ModuleCat.{max u v w} A)) [S.IsClosedUnderIsomorphisms]
    (hS : ∀ X, S X → Module.Finite A X ∧ Indecomposable X)
    (hirr : ∀ {X Y : ModuleCat.{max u v w} A} (f : X ⟶ Y), IsIrreducibleMorphism f →
      Module.Finite A X → Indecomposable X → Module.Finite A Y → Indecomposable Y → (S X ↔ S Y))
    (hne : ∃ X, S X) (b : ℕ) (hb : ∀ X, S X → Module.length A X ≤ b) :
    (∀ X : ModuleCat.{max u v w} A, Module.Finite A X → Indecomposable X → S X) ∧
      IsRepresentationFinite.{max u v w} A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hfwd {X Y : ModuleCat.{max u v w} A} (hX : S X) (hY : Module.Finite A Y)
      (hiY : Indecomposable Y) (hSY : ¬ S Y) (f : X ⟶ Y) : f = 0 :=
    eq_zero_of_prop_of_not_prop k S hS b hb
      (fun f hf hY hiY hX ↦ (hirr f hf (hS _ hX).1 (hS _ hX).2 hY hiY).mp hX) hX hiY hSY f
  have hbwd {X Y : ModuleCat.{max u v w} A} (hX : S X) (hY : Module.Finite A Y)
      (hiY : Indecomposable Y) (hSY : ¬ S Y) (f : Y ⟶ X) : f = 0 :=
    eq_zero_of_not_prop_of_prop k S hS b hb
      (fun f hf hX hiX hY ↦ (hirr f hf hX hiX (hS _ hY).1 (hS _ hY).2).mpr hY) hX hiY hSY f
  -- The indecomposable summands of the regular module.
  let G : ModuleCat.{max u v w} A := ModuleCat.of A (ULift.{max u w} A)
  have : Module.Finite A G := Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
  obtain ⟨n, P, hP, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct G
  have hPf (j : Fin n) : Module.Finite A (P j) :=
    Module.Finite.of_surjective (e.hom ≫ biproduct.π P j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  -- A nonzero module receives a nonzero morphism from one of them.
  have hsummand (M : ModuleCat.{max u v w} A) (hM : Indecomposable M) :
      ∃ (j : Fin n) (f : P j ⟶ M), f ≠ 0 := by
    have : Nontrivial M := ((indecomposable_iff_isIndecomposableModule M).mp hM).nontrivial
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    let t : G ⟶ M := ModuleCat.ofHom
      (LinearMap.toSpanSingleton A M x ∘ₗ (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)
    have ht : e.inv ≫ t ≠ 0 := fun h ↦ hx <| by
      have h₀ : t = 0 := by simpa using congrArg (e.hom ≫ ·) h
      simpa [t, G] using ConcreteCategory.congr_hom h₀ (ULift.up 1 : ULift.{max u w} A)
    obtain ⟨j, hj⟩ : ∃ j, biproduct.ι P j ≫ e.inv ≫ t ≠ 0 := by
      by_contra! hzero
      exact ht (biproduct.hom_ext' _ _ fun j ↦ by rw [hzero j, comp_zero])
    exact ⟨j, _, hj⟩
  -- Connectedness puts every summand in `S`.
  have hPS (j : Fin n) : S (P j) := by
    obtain ⟨X, hX⟩ := hne
    obtain ⟨i, f, hf⟩ := hsummand X (hS X hX).2
    have hi : S (P i) := by_contra fun h ↦ hf (hbwd hX (hPf i) (hP i) h f)
    refine ((forall_or_forall_of_forall_hom_eq_zero hA e (fun j ↦ (hP j).1) (fun j ↦ S (P j))
      fun a b ha hb ↦ ⟨fun f ↦ hfwd ha (hPf b) (hP b) hb f, fun f ↦ hbwd ha (hPf b) (hP b) hb f⟩)
      |>.resolve_right fun h ↦ h i hi) j
  have hall (Y : ModuleCat.{max u v w} A) (hY : Module.Finite A Y) (hiY : Indecomposable Y) :
      S Y := by
    by_contra h
    obtain ⟨j, f, hf⟩ := hsummand Y hiY
    exact hf (hfwd (hPS j) hY hiY h f)
  exact ⟨hall,
    isRepresentationFinite_of_length_le.{u, v, w} k b fun M hM hiM ↦ hb M (hall M hM hiM)⟩

end TauCeti
