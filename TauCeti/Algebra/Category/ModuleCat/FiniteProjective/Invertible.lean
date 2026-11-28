/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FractionalIdeal.Projective
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Ring
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.RingTheory.PicardGroup.RankOne
import TauCeti.RingTheory.PicardGroup.Submodule

/-!
# Projective classes of invertible modules

For an invertible module `M` over a commutative ring `A`, the reduced class `[M] - [A]` in
projective `K₀(A)` vanishes exactly when `M` is free. One direction is the stable-freeness
criterion `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff`: a stably free invertible module
is free (`Module.free_of_isStablyFree_of_invertible`). For invertible submodules, and in
particular nonzero finite projective ideals of a domain, freeness is principality.

Extension of scalars along a ring homomorphism `f : A →+* B` sends the class of the invertible
module representing a Picard class `L` to the class of the invertible module representing
`CommRing.Pic.mapRingHom f L`: on the classes of invertible modules, the map of projective `K₀`
induced by `f` is the map of Picard groups.

## Main results

* `TauCeti.FiniteProjectiveModules.classOf_one_eq_zero_iff`: a finite projective module has
  zero reduced class in rank one exactly when it is isomorphic to the base ring.
* `TauCeti.FiniteProjectiveModules.classOf_eq_zero_iff_free`: an invertible module has zero
  reduced class exactly when it is free.
* `TauCeti.FiniteProjectiveModules.classOf_submodule_eq_zero_iff_isPrincipal`: an invertible
  submodule has zero reduced class exactly when it is principal.
* `TauCeti.FiniteProjectiveModules.classOf_ideal_eq_zero_iff_isPrincipal`: a nonzero finite
  projective ideal of a domain has zero reduced class exactly when it is principal.
* `TauCeti.FiniteProjectiveModules.splitK0_of_pic_one`: the invertible module of the trivial
  Picard class has class `1` in projective `K₀`.
* `TauCeti.FiniteProjectiveModules.map_extendScalars_of_pic`: extension of scalars on the class
  of the invertible module of a Picard class.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Chapter II,
  Proposition 2.6 (the determinant map), and Chapter I, Proposition 3.5 (invertible ideals).
-/

public section

namespace TauCeti

namespace FiniteProjectiveModules

universe u

variable {A : Type u} [CommRing A]

/-- A finite projective module has zero reduced class in rank one exactly when it is
isomorphic to the base ring. -/
theorem classOf_one_eq_zero_iff {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    classOf A M 1 = 0 ↔ Nonempty (M ≃ₗ[A] A) := by
  constructor
  · rw [classOf_eq_zero_iff]
    rintro ⟨k, ⟨e⟩⟩
    have := Module.Free.of_equiv e.symm
    have : Module.IsStablyFree A M := .of_free_prod A _ (Fin k → A)
    have : Module.Invertible A M := .of_rankAtStalk_eq_one fun p ↦ by
      have := p.nontrivial
      have h := congrFun (Module.rankAtStalk_eq_of_equiv e) p
      rw [Module.rankAtStalk_prod] at h
      simp at h
      omega
    have := Module.free_of_isStablyFree_of_invertible A M
    exact Module.Invertible.free_iff_linearEquiv.mp inferInstance
  · rintro ⟨e⟩
    rw [classOf_congr e]
    simp [classOf_def]

/-- An invertible module has zero reduced projective class exactly when it is free. -/
theorem classOf_eq_zero_iff_free {M : Type u} [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : classOf A M 1 = 0 ↔ Module.Free A M :=
  classOf_one_eq_zero_iff.trans Module.Invertible.free_iff_linearEquiv.symm

/-- An invertible submodule has zero reduced projective class exactly when it is principal. -/
theorem classOf_submodule_eq_zero_iff_isPrincipal {P : Type u} [AddCommGroup P] [Module A P]
    (I : Submodule A P) [Module.Invertible A I] : classOf A I 1 = 0 ↔ I.IsPrincipal := by
  rw [classOf_eq_zero_iff_free, I.free_iff_isPrincipal]

/-- A nonzero finite projective ideal of a domain has zero reduced projective class exactly when
it is principal. The finiteness and projectivity instances are required to express the left-hand
side using `classOf`. -/
theorem classOf_ideal_eq_zero_iff_isPrincipal [IsDomain A] {I : Ideal A} [Module.Finite A I]
    [Module.Projective A I] (hI : I ≠ ⊥) : classOf A I 1 = 0 ↔ I.IsPrincipal := by
  have : Module.Invertible A I := I.moduleInvertible_of_ne_bot hI
  exact classOf_submodule_eq_zero_iff_isPrincipal I

/-- An invertible fractional ideal in a faithful algebra has zero reduced projective class exactly
when it is principal. -/
theorem classOf_fractionalIdeal_eq_zero_iff_isPrincipal {S : Submonoid A} {P : Type u}
    [CommRing P] [Algebra A P] [FaithfulSMul A P] (I : (FractionalIdeal S P)ˣ) :
    classOf A (I : FractionalIdeal S P) 1 = 0 ↔ (I : Submodule A P).IsPrincipal :=
  classOf_submodule_eq_zero_iff_isPrincipal (I : Submodule A P)

/-- The invertible module of the trivial Picard class has class `1 = [A]` in projective `K₀(A)`:
it is free of rank one. -/
@[simp]
theorem splitK0_of_pic_one : SplitK0.of.{u} (of A (1 : CommRing.Pic A)) = 1 := by
  rw [← splitK0_of_self]
  exact SplitK0.of_congr (CategoryTheory.ObjectProperty.isoMk _
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some.toModuleIso)

open scoped TensorProduct in
/-- **Extension of scalars of an invertible module.** Along a ring homomorphism `f : A →+* B`,
extension of scalars sends the class in projective `K₀(A)` of the invertible module of a Picard
class `L` to the class in projective `K₀(B)` of the invertible module of
`CommRing.Pic.mapRingHom f L`. -/
theorem map_extendScalars_of_pic {B : Type u} [CommRing B] (f : A →+* B) (L : CommRing.Pic A) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (SplitK0.of.{u} (of A L)) =
      SplitK0.of.{u} (of B (CommRing.Pic.mapRingHom f L)) := by
  let _ : Algebra A B := f.toAlgebra
  rw [SplitK0.map_of, ← RingHom.algebraMap_toAlgebra f, CommRing.Pic.mapRingHom_algebraMap,
    CommRing.Pic.mapAlgebra_apply]
  -- The balanced extension of `L` is Mathlib's `B ⊗[A] L`, which represents `mapAlgebra A B L`.
  exact SplitK0.of_extendScalars_obj
    (((BalancedExtension.extendScalarsIso (algebraMap A B)).app (ModuleCat.of A L) ≪≫
      ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of A L)).toLinearEquiv.trans
        (CommRing.Pic.mk.linearEquiv B (B ⊗[A] L)).symm)

end FiniteProjectiveModules

end TauCeti
