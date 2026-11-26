/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Essential
public import TauCeti.RingTheory.LocalRing.Socle

/-!
# Artinian modules over commutative local rings

Let `R` be a commutative local ring with maximal ideal `𝔪`. By
`TauCeti.IsLocalRing.isEssential_torsionBySet_maximalIdeal` (from
`TauCeti/RingTheory/LocalRing/Socle.lean`), the socle `M[𝔪]` of an Artinian `R`-module `M` is
essential in `M`.

When `R` is Noetherian, essentiality of `M[𝔪]` implies that every element of an Artinian
`R`-module is killed by a power of `𝔪`, so `M` carries the canonical action of the `𝔪`-adic
completion `R̂`.

## Main results

* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`: over a Noetherian local ring,
  every Artinian module is maximal-ideal-power torsion.
* `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian`: every element of an Artinian module
  over a Noetherian local ring is annihilated by a power of the maximal ideal.

## References

* [Stacks Project, Section 47.7](https://stacks.math.columbia.edu/tag/08Z1) and
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

open IsLocalRing Submodule

namespace TauCeti

universe u w

section Noetherian

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type w} [AddCommGroup M] [Module R M] [IsArtinian R M]

variable (R M) in
/-- Over a Noetherian local ring, every Artinian module equals its maximal-ideal primary component:
each element is annihilated by some power of the maximal ideal. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian :
    (maximalIdeal R).primaryComponent M = ⊤ := by
  apply (TauCeti.IsLocalRing.isEssential_torsionBySet_maximalIdeal (R := R)
    (M := M)).primaryComponent_eq_top
  intro x hx
  exact ((maximalIdeal R).primaryComponent_mem M x).mpr ⟨1, by simpa using hx⟩

/-- Every element of an Artinian module over a Noetherian local ring is annihilated by a power of
the maximal ideal. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M :=
  primaryComponent_maximalIdeal_eq_top_of_isArtinian R M ▸ mem_top

end Noetherian

end TauCeti
