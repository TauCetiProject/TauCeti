/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import TauCeti.RingTheory.Artinian.Torsion

/-!
# Artinian modules over a local ring

Let `R` be a commutative local ring with maximal ideal `𝔪`, and let `M` be an Artinian
`R`-module. When `𝔪` is finitely generated (in particular when `R` is Noetherian),
`Ideal.primaryComponent_eq_top_of_isArtinian` shows that `M` equals its `𝔪`-primary component
(`TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`).

## Main results

* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian` and
  `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian`: over a commutative local ring with
  finitely generated maximal ideal `𝔪`, every Artinian module is `𝔪`-power torsion.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

namespace TauCeti

open IsLocalRing Submodule

section LocalRing

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- Every Artinian module over a commutative local ring with finitely generated maximal ideal is
maximal-ideal-power torsion. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian [IsArtinian R M]
    (h𝔪 : (maximalIdeal R).FG) :
    (maximalIdeal R).primaryComponent M = ⊤ :=
  (maximalIdeal R).primaryComponent_eq_top_of_isArtinian h𝔪
    (IsLocalRing.ringJacobson_eq_maximalIdeal (R := R)).ge

/-- Every element of an Artinian module over a commutative local ring with finitely generated
maximal ideal is killed by a power of the maximal ideal. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian [IsArtinian R M]
    (h𝔪 : (maximalIdeal R).FG) (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M := by
  rw [primaryComponent_maximalIdeal_eq_top_of_isArtinian h𝔪]
  exact mem_top

end LocalRing

end TauCeti
