/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MazurFiniteness
import TauCeti.NumberTheory.NumberField.RestrictedRamification.Cohomology

/-!
# Mazur's finiteness condition for Galois groups with restricted ramification

For a number field `K` and a finite set `S` of its finite places, Hermite's theorem gives
finitely many continuous homomorphisms from each open subgroup of `G_{K,S}` to a finite discrete
group (`TauCeti.RestrictedRamification.finite_continuousMonoidHom`). For `p ≠ 0`, taking the
target to be the additive group of `ZMod p` supplies the finiteness hypothesis for global Galois
deformation rings.

## References

* T. Gee, *Modularity lifting theorems*, Essential Number Theory 1 (2022), §3.1.
* M. Kisin, *Lectures on deformations of Galois representations*, Lecture 1, (1.2).
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace TauCeti.RestrictedRamification

/-- The Galois group of the maximal subextension of a normal extension `Ω/K` unramified outside
a finite set `S` of finite places of a number field `K` satisfies Mazur's finiteness condition
for every `p ≠ 0`, with characters valued in the additive group of `ZMod p`. Ramification at
infinite places is allowed. -/
theorem mazurFiniteness_galoisGroupS {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Normal K Ω] (p : ℕ) [NeZero p]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    MazurFiniteness p (galoisGroupS K Ω S) :=
  mazurFiniteness_iff_forall_finite.mpr fun U ↦
    have : Finite (U.toSubgroup →ₜ* Multiplicative (ZMod p)) :=
      finite_continuousMonoidHom S hS U.isOpen (Multiplicative (ZMod p))
    inferInstance

end TauCeti.RestrictedRamification
