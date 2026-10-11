/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Algebra.Group.Hom.Lift

/-!
# Descent of linear characters

A linear character of a monoid of exponent dividing `n` takes values in the `n`-th roots of unity.
If a commutative semiring `K` contains a primitive `n`-th root and embeds into an integral domain
`L`, every linear character over `L` therefore comes from a unique linear character over `K`.
The embedding is supplied by a faithful `K`-algebra structure on `L`. This gives the coefficient
descent used to realize monomial representations over cyclotomic fields.

The result requires neither characteristic zero nor finiteness of the monoid: a nonzero exponent
bound and a primitive root suffice when the coefficient algebra is an integral domain and the
scalar action is faithful.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
-/

public section

universe u v w

namespace TauCeti

variable {K : Type u} {L : Type v} [CommSemiring K] [CommRing L] [IsDomain L]
  [Algebra K L] [FaithfulSMul K L]
variable {G : Type w} [Monoid G]

/-- A primitive `n`-th root in a base semiring descends every linear character of a monoid whose
exponent divides the nonzero integer `n`, along a faithful algebra into an integral domain. -/
theorem _root_.MonoidHom.existsUnique_unitsMap_comp_eq_of_isPrimitiveRoot (χ : G →* Lˣ)
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hG : Monoid.exponent G ∣ n) :
    ∃! ψ : G →* Kˣ, (Units.map (algebraMap K L : K →* L)).comp ψ = χ := by
  have hf := FaithfulSMul.algebraMap_injective K L
  have hζL := (hζ.isUnit_unit (NeZero.ne n)).map_of_injective (Units.map_injective hf)
  apply χ.existsUnique_comp_eq_of_injective _ (Units.map_injective hf)
  intro g
  have hpow : χ g ^ n = 1 := by
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hG g, map_one]
  obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity n (χ g)).mpr hpow)
  refine ⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩
  simpa using hi

end TauCeti
