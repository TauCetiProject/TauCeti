/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.AsModule

/-!
# Maschke's theorem for intertwining maps

Mathlib states Maschke's theorem for modules over the group algebra: over a field in which the
order of the finite group `G` is invertible, a `k[G]`-linear injection has a `k[G]`-linear left
inverse (`MonoidAlgebra.exists_leftInverse_of_injective`).  This file reads that statement through
Mathlib's dictionary `Representation.IntertwiningMap.equivLinearMapAsModule` between intertwining
maps and `k[G]`-linear maps of the attached modules, so that it applies to representations as they
are usually given, without passing to `Representation.asModule`.

The form recorded here is the one used to compare the two meanings of "a constituent of `ρ`": an
irreducible `σ` that embeds in `ρ` is also a quotient of `ρ`, because the embedding splits.

## Main statements

* `Representation.IntertwiningMap.exists_comp_eq_id_of_injective`: an injective intertwining map
  has an intertwining left inverse.
-/

public section

open scoped MonoidAlgebra

namespace Representation.IntertwiningMap

variable {k G V W : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- **Maschke's theorem for intertwining maps.**  Over a field in which the order of the finite
group `G` is invertible, an injective intertwining map `f : ρ → σ` has an intertwining left
inverse `p : σ → ρ`, that is, `p ∘ f = id`. -/
theorem exists_comp_eq_id_of_injective (f : IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ∃ p : IntertwiningMap σ ρ, p.comp f = IntertwiningMap.id ρ := by
  let e := IntertwiningMap.equivLinearMapAsModule ρ σ
  obtain ⟨q, hq⟩ := MonoidAlgebra.exists_leftInverse_of_injective (e f)
    (LinearMap.ker_eq_bot.mpr hf)
  let e' := IntertwiningMap.equivLinearMapAsModule σ ρ
  let p := e'.symm q
  refine ⟨p, IntertwiningMap.ext (LinearMap.ext fun v => ?_)⟩
  rw [IntertwiningMap.coe_toLinearMap, IntertwiningMap.comp_apply,
    IntertwiningMap.coe_toLinearMap, IntertwiningMap.id_apply]
  have hef : e f (ρ.asModuleEquiv.symm v) = σ.asModuleEquiv.symm (f v) := by
    apply σ.asModuleEquiv.eq_symm_apply.mpr
    rw [IntertwiningMap.equivLinearMapAsModule_apply,
      Representation.asModuleEquiv_symm_apply]
    -- `f v` is read as an element of `σ.asModule`, where `asModuleEquiv` evaluates.
    exact Representation.asModuleEquiv_apply (show σ.asModule from f v)
  have hqv := congrArg (fun l => ρ.asModuleEquiv (l (ρ.asModuleEquiv.symm v))) hq
  rw [LinearMap.comp_apply, hef, LinearMap.id_apply, LinearEquiv.apply_symm_apply] at hqv
  calc
    p (f v) = ρ.asModuleEquiv (q (σ.asModuleEquiv.symm (f v))) := by
      simpa only [p, e'] using
        (IntertwiningMap.equivLinearMapAsModule_symm_apply q (f v))
    _ = v := hqv

end Representation.IntertwiningMap
