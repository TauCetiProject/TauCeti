/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleComposite
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.Radical.RepresentationFinite

/-!
# The radical and irreducible morphisms of a representation-finite Artin algebra

Let `A` be an Artin algebra, that is, an algebra over a commutative Artinian ring `R` that is
finitely generated as an `R`-module; a finite-dimensional algebra over a field is the basic
example. Suppose that `A` is representation-finite. Then, in the category `FGModuleCat A` of
finitely generated `A`-modules:

* the radical is nilpotent: some power `radᴺ` vanishes
  (`TauCeti.IsRepresentationFinite.exists_jacobsonRadicalIdeal_pow_eq_bot`);
* every morphism between finitely generated indecomposable modules that is not an isomorphism is a
  sum of composites of irreducible morphisms between finitely generated indecomposable modules
  (`TauCeti.IsRepresentationFinite.mem_closure_isIrreducibleComposite`).

Both are the case `C = FGModuleCat A` of the results for linear categories with finitely many
indecomposable objects, `TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables`
and `TauCeti.mem_closure_isIrreducibleComposite_of_finite_indecomposables`. The category
`FGModuleCat A` is `R`-linear through `A` (`ModuleCat.Algebra.instLinear`), it is abelian and hence
idempotent complete, and its morphism modules are finitely generated over `R`
(`FGModuleCat.finite_hom`). Representation-finiteness provides finitely many modules `P i` that
represent every indecomposable object (`TauCeti.IsRepresentationFinite.exists_indecomposable_iso`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u

variable (R : Type u) {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- Over a representation-finite Noetherian ring `A`, every indecomposable object of
`FGModuleCat A` is isomorphic to one of finitely many objects `P i`. This is the form in which
representation-finiteness enters the results for linear categories with finitely many
indecomposable objects, such as
`TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables`. -/
theorem IsRepresentationFinite.exists_indecomposable_iso [IsNoetherianRing A]
    (h : IsRepresentationFinite.{w} A) :
    ∃ (m : ℕ) (P : Fin m → FGModuleCat.{w} A),
      ∀ X : FGModuleCat.{w} A, Indecomposable X → ∃ i, Nonempty (X ≅ P i) := by
  classical
  rw [isRepresentationFinite_iff] at h
  -- One module from each isomorphism class of finitely generated indecomposable modules.
  let Q : ObjectProperty (ModuleCat.{w} A) := fun M ↦ Module.Finite A M ∧ Indecomposable M
  let S := Q.FullSubcategory
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Skeleton S)
  refine ⟨m, fun i ↦ ⟨((fromSkeleton S).obj (e.symm i)).obj,
    (ModuleCat.isFG_iff _).mpr ((fromSkeleton S).obj (e.symm i)).property.1⟩, fun X hX ↦ ?_⟩
  have hX' : Indecomposable X.obj := (ObjectProperty.ι _).indecomposable_obj_of_map_bijective hX
    ((ObjectProperty.fullyFaithfulι _).map_bijective X X)
  let Y : S := ⟨X.obj, (ModuleCat.isFG_iff _).mp X.property, hX'⟩
  refine ⟨e (toSkeleton Y), ⟨(ObjectProperty.fullyFaithfulι _).preimageIso ?_⟩⟩
  simp only [Equiv.symm_apply_apply]
  exact (Q.ι.mapIso (fromSkeletonToSkeletonIso Y)).symm

open ModuleCat.Algebra in
include R in
/-- **The radical of a representation-finite Artin algebra is nilpotent**: some power of the
radical of the category of finitely generated modules vanishes. -/
theorem IsRepresentationFinite.exists_jacobsonRadicalIdeal_pow_eq_bot
    (h : IsRepresentationFinite.{w} A) :
    ∃ N : ℕ, jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ N = ⊥ := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : HasFiniteBiproducts (FGModuleCat.{w} A) := .of_hasFiniteProducts
  obtain ⟨m, P, hP⟩ := h.exists_indecomposable_iso
  exact exists_jacobsonRadicalIdeal_pow_eq_bot_of_finite_indecomposables R P hP

open ModuleCat.Algebra in
include R in
/-- **Non-isomorphisms are sums of composites of irreducible morphisms.** Over a
representation-finite Artin algebra, every morphism between finitely generated indecomposable
modules that is not an isomorphism is a sum of composites of irreducible morphisms between
finitely generated indecomposable modules. -/
theorem IsRepresentationFinite.mem_closure_isIrreducibleComposite
    (h : IsRepresentationFinite.{w} A) {X Y : FGModuleCat.{w} A} (hX : Indecomposable X.obj)
    (hY : Indecomposable Y.obj) {f : X ⟶ Y} (hf : ¬ IsIso f) :
    f ∈ AddSubgroup.closure {g : X ⟶ Y | IsIrreducibleComposite g} := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : HasFiniteBiproducts (FGModuleCat.{w} A) := .of_hasFiniteProducts
  obtain ⟨m, P, hP⟩ := h.exists_indecomposable_iso
  -- Indecomposability in `ModuleCat A` gives a local endomorphism ring in `FGModuleCat A`.
  have := FGModuleCat.isLocalRing_end_of_indecomposable hX
  have := FGModuleCat.isLocalRing_end_of_indecomposable hY
  exact mem_closure_isIrreducibleComposite_of_finite_indecomposables R P hP
    indecomposable_of_isLocalRing_end indecomposable_of_isLocalRing_end hf

end TauCeti
