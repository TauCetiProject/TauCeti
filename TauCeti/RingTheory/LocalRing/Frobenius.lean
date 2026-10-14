/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CharP.Frobenius.Nilpotent
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Frobenius on Artinian local algebras

In characteristic `p`, a sufficiently high iterate of Frobenius kills a nilpotent ideal.
If reduction has a ring section, that iterate is reduction followed by Frobenius on the
quotient and the section. In particular, for an Artinian local algebra with its coefficient
field identified with the residue field, high Frobenius powers factor through the coefficient
field. The bound is uniform in the elements of the ring and applies to every larger iterate.

On spectra this makes high Frobenius base changes of a family come from its special fibre.
The coefficient-field Frobenius remains in the formula: Frobenius need not fix the coefficients.
Neither perfection nor algebraic closedness of the residue field is needed.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, proof of 5.3.6.
* Mathlib's `IsArtinianRing.isNilpotent_jacobson_bot` supplies the uniform nilpotence bound.
-/

public section

namespace TauCeti

open IsLocalRing

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [Algebra k R] (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p]

/-- On an Artinian local algebra whose coefficient field maps bijectively onto the residue
field, high Frobenius powers factor through that field. The retraction is residue reduction
followed by the inverse of the specified residue-field identification. -/
theorem exists_iterateFrobenius_eq_algebraMap_comp
    (hres : Function.Bijective (algebraMap k (ResidueField R))) :
    ∃ N : ℕ, ∀ n ≥ N,
      iterateFrobenius R p n = (algebraMap k R).comp
        ((iterateFrobenius k p n).comp
          ((RingEquiv.ofBijective (algebraMap k (ResidueField R)) hres).symm.toRingHom.comp
            (residue R))) := by
  let e := RingEquiv.ofBijective (algebraMap k (ResidueField R)) hres
  let f := e.symm.toRingHom.comp (residue R)
  have hs : f.comp (algebraMap k R) = RingHom.id k := by
    ext a
    simp only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply k R (ResidueField R)]
    exact e.symm_apply_apply a
  have hker : RingHom.ker f = maximalIdeal R := by
    exact (RingHom.ker_comp_of_injective (residue R) e.symm.injective).trans ker_residue
  have hnil : IsNilpotent (RingHom.ker f) := by
    rw [hker, ← jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  exact f.exists_iterateFrobenius_eq_of_isNilpotent_ker p (algebraMap k R) hs
    (Fact.out : p.Prime).one_lt hnil

end TauCeti
