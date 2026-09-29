/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic

/-!
# Ext-Euler admissibility from simple modules

Euler-admissibility is closed under extensions in either variable, so it propagates along a
composition series: a module `Y` which is Euler-admissible against every simple module is
Euler-admissible against every module of finite length. Over an Artinian ring every finitely
generated module has finite length, and the criterion becomes a hypothesis on simple first
arguments only. This is how admissibility of all pairs of finitely generated modules is obtained
for algebras whose simple modules are known, for example path algebras of finite acyclic quivers,
when no finite projective resolution is at hand.

## Main results

* `TauCeti.isEulerAdmissible_of_isFiniteLength`: admissibility against every simple module gives
  admissibility against every module of finite length.
* `TauCeti.isEulerAdmissibleOn_isFG_of_forall_isSimpleModule`: over an Artinian ring, every pair
  of finitely generated modules is Euler-admissible as soon as every pair with a simple first
  argument is.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u

variable (k : Type*) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- **Euler-admissibility descends along composition series.** If `Y` is Euler-admissible against
every simple module, it is Euler-admissible against every module of finite length. -/
theorem isEulerAdmissible_of_isFiniteLength (Y : ModuleCat.{u} R)
    (h : ∀ S : ModuleCat.{u} R, IsSimpleModule R S → IsEulerAdmissible.{u} k S Y)
    (X : ModuleCat.{u} R) (hX : IsFiniteLength R X) : IsEulerAdmissible.{u} k X Y := by
  suffices key : ∀ (M : Type u) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      IsEulerAdmissible.{u} k (ModuleCat.of R M) Y from key X hX
  intro M _ _ hM
  induction hM with
  | of_subsingleton =>
    exact IsEulerAdmissible.of_isZero_left k (ModuleCat.isZero_of_subsingleton _)
  | @of_simple_quotient M _ _ N _ _ ih =>
    let T : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by
        ext x
        exact (LinearMap.exact_subtype_mkQ N).apply_apply_eq_zero x)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      (LinearMap.exact_subtype_mkQ N) N.injective_subtype N.mkQ_surjective
    exact IsEulerAdmissible.of_shortExact₂' hT ih
      (h (ModuleCat.of R (M ⧸ N)) (inferInstanceAs (IsSimpleModule R (M ⧸ N))))

variable [IsArtinianRing R]

/-- **Euler-admissibility of finitely generated modules is tested on simple first arguments.**
Over an Artinian ring, if every simple module is Euler-admissible against every finitely
generated module, then every pair of finitely generated modules is Euler-admissible. -/
theorem isEulerAdmissibleOn_isFG_of_forall_isSimpleModule
    (h : ∀ S Y : ModuleCat.{u} R, IsSimpleModule R S → Module.Finite R Y →
      IsEulerAdmissible.{u} k S Y) :
    IsEulerAdmissibleOn.{u} k (ModuleCat.isFG R) (ModuleCat.isFG R) where
  isEulerAdmissible X Y hX hY :=
    have : Module.Finite R X := (ModuleCat.isFG_iff X).mp hX
    isEulerAdmissible_of_isFiniteLength k Y (fun S hS ↦ h S Y hS ((ModuleCat.isFG_iff Y).mp hY))
      X (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end TauCeti
