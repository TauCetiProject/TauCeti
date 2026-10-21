/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.Preadditive.Radical.Nilpotent
public import Mathlib.RingTheory.Artinian.Defs
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.RingTheory.Artinian.End
import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# The radical of a representation-finite Artin algebra is nilpotent

Let `A` be an Artin algebra, that is, an algebra over a commutative Artinian ring `R` that is
finitely generated as an `R`-module; a finite-dimensional algebra over a field is the basic
example. If `A` is representation-finite, the radical of the category `FGModuleCat A` of finitely
generated `A`-modules is nilpotent: some power `radᴺ` vanishes
(`TauCeti.IsRepresentationFinite.exists_jacobsonRadicalIdeal_pow_eq_bot`).

The sum `G` of one module from each isomorphism class of finitely generated indecomposable modules
is finitely generated. By the existence half of the Krull-Schmidt theorem, every finitely generated
module is a direct summand of a finite sum of indecomposable modules
(`FGModuleCat.exists_indecomposable_sum_comp_eq_id`), hence of a finite sum of copies of `G`. The
endomorphism ring of `G` is Artinian (`Module.End.isArtinianRing`), so the radical is nilpotent by
`TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot`.

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

include R in
/-- **The radical of a representation-finite Artin algebra is nilpotent**: some power of the
radical of the category of finitely generated modules vanishes. -/
theorem IsRepresentationFinite.exists_jacobsonRadicalIdeal_pow_eq_bot
    (h : IsRepresentationFinite.{w} A) :
    ∃ N : ℕ, jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ N = ⊥ := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  rw [isRepresentationFinite_iff] at h
  -- One module from each isomorphism class of finitely generated indecomposable modules.
  let S := ObjectProperty.FullSubcategory fun M : ModuleCat.{w} A ↦
    Module.Finite A M ∧ Indecomposable M
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Skeleton S)
  let P (i : Fin m) : ModuleCat.{w} A := ((fromSkeleton S).obj (e.symm i)).obj
  have : ∀ i, Module.Finite A (P i) := fun i ↦ ((fromSkeleton S).obj (e.symm i)).property.1
  have hP (M : FGModuleCat.{w} A) (hM : Indecomposable M.obj) : ∃ i, Nonempty (P i ≅ M.obj) := by
    refine ⟨e (toSkeleton ⟨M.obj, (ModuleCat.isFG_iff _).mp M.property, hM⟩), ⟨?_⟩⟩
    simp only [P, Equiv.symm_apply_apply]
    exact (ObjectProperty.ι _).mapIso (fromSkeletonToSkeletonIso _)
  have : Module.Finite A (⨁ P : ModuleCat.{w} A) :=
    .equiv (ModuleCat.biproductIsoPi P).toLinearEquiv.symm
  let G : FGModuleCat.{w} A := ⟨⨁ P, (ModuleCat.isFG_iff _).mpr inferInstance⟩
  -- `End G` is the endomorphism ring of a finitely generated module, hence Artinian.
  let eG : End G ≃+* Module.End A (⨁ P : ModuleCat.{w} A) :=
    ((ObjectProperty.fullyFaithfulι _).ringEquivEnd G).trans (ModuleCat.endRingEquiv _)
  -- Let `R` act on `G` through `A`; then `G` is finitely generated over `R`.
  let : Module R (⨁ P : ModuleCat.{w} A) := Module.compHom _ (algebraMap R A)
  have : IsScalarTower R A (⨁ P : ModuleCat.{w} A) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite R (⨁ P : ModuleCat.{w} A) := .trans A _
  have : IsArtinianRing (Module.End A (⨁ P : ModuleCat.{w} A)) := Module.End.isArtinianRing R
  have : IsArtinianRing (End G) := eG.symm.isArtinianRing
  refine TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot G fun X ↦ ?_
  -- Decompose `X` into indecomposables and match each summand with some `P i`.
  obtain ⟨n, W, a, b, hW, hab⟩ := FGModuleCat.exists_indecomposable_sum_comp_eq_id X
  choose i c using fun j ↦ hP (W j) (hW j)
  refine ⟨n, fun j ↦ a j ≫ ObjectProperty.homMk ((c j).some.inv ≫ biproduct.ι P (i j)),
    fun j ↦ ObjectProperty.homMk (biproduct.π P (i j) ≫ (c j).some.hom) ≫ b j, ?_⟩
  convert hab using 2 with j
  ext : 1
  simp

end TauCeti
