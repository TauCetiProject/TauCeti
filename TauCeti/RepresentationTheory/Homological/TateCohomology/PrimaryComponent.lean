/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear

/-!
# Primary components of Tate cohomology

The `p`-primary component of Tate cohomology vanishes when multiplication by `p` acts bijectively
on the coefficient representation. Scalar multiplication on the coefficients induces the same
scalar multiplication on Tate cohomology, so an invertible scalar acts injectively on every Tate
group; this excludes nonzero elements killed by a power of `p`.
-/

public section

open CategoryTheory Representation

namespace TauCeti.TateCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- **An invertible scalar contributes no primary Tate cohomology.** If multiplication by a natural
number `p` is bijective on a representation `A`, then the `p`-primary component of `Ĥⁿ(S, A)` is
zero for every finite subgroup `S` and every integer degree `n`. -/
theorem primaryComponent_tateCohomology_eq_bot (p : ℕ) (A : Rep k G)
    (hA : Function.Bijective fun x : A.V => (p : k) • x) (S : Subgroup G) [Fintype S]
    (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology (Rep.res S.subtype A) n) p = ⊥ := by
  have hp : Function.Bijective fun x : tateCohomology (Rep.res S.subtype A) n =>
      (p : k) • x :=
    smul_bijective (p : k) (Rep.res S.subtype A) (by simpa using hA) n
  apply TauCeti.primaryComponent_eq_bot_of_injective_nsmul
  simpa only [Nat.cast_smul_eq_nsmul] using hp.1

end TauCeti.TateCohomology
