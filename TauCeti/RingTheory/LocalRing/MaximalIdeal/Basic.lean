/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import TauCeti.RingTheory.Ideal.Span

/-!
# Elements in the maximal ideal of a local ring

In a commutative local semiring, every nonunit belongs to the unique maximal ideal
`IsLocalRing.maximalIdeal R`. In particular, any element that fails to divide another lies in the
maximal ideal (`TauCeti.IsLocalRing.mem_maximalIdeal_of_not_dvd`), and every irreducible element
lies in `IsLocalRing.maximalIdeal R` (`Irreducible.mem_maximalIdeal`) and is never a product of two
elements of `IsLocalRing.maximalIdeal R` (`Irreducible.ne_mul_of_mem_maximalIdeal`).

In a commutative local ring, a minimal nonzero ideal is annihilated by the maximal ideal
(`IsAtom.maximalIdeal_mul_eq_bot`).

For a homomorphism `f` of commutative local rings, the maximal ideal of the target is the greatest
ideal whose contraction along `f` is contained in the maximal ideal of the source
(`Ideal.isGreatest_comap_le_maximalIdeal`).
-/

public section

namespace TauCeti.IsLocalRing

/-- In a commutative local semiring, any element that fails to divide another lies in the maximal
ideal. -/
theorem mem_maximalIdeal_of_not_dvd {R : Type*} [CommSemiring R] [IsLocalRing R] {f a : R}
    (hfa : ¬ f ∣ a) : f ∈ _root_.IsLocalRing.maximalIdeal R :=
  of_not_not fun h ↦ hfa (_root_.IsLocalRing.notMem_maximalIdeal.mp h).dvd

end TauCeti.IsLocalRing

namespace Irreducible

variable {R : Type*} [CommSemiring R] [IsLocalRing R]

/-- Every irreducible element of a local ring belongs to its maximal ideal. -/
theorem mem_maximalIdeal {c : R} (hc : Irreducible c) : c ∈ IsLocalRing.maximalIdeal R :=
  (IsLocalRing.mem_maximalIdeal c).mpr hc.not_isUnit

/-- An irreducible element of a local ring cannot be written as a product of two elements of the
maximal ideal. -/
theorem ne_mul_of_mem_maximalIdeal {c x y : R} (hc : Irreducible c)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hy : y ∈ IsLocalRing.maximalIdeal R) :
    c ≠ x * y := fun h ↦
  (hc.isUnit_or_isUnit h).elim ((IsLocalRing.mem_maximalIdeal x).mp hx)
    ((IsLocalRing.mem_maximalIdeal y).mp hy)

end Irreducible

/-- In a commutative local ring, a minimal nonzero ideal `I` is annihilated by the maximal
ideal. -/
theorem IsAtom.maximalIdeal_mul_eq_bot {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : IsAtom I) : IsLocalRing.maximalIdeal R * I = ⊥ := by
  -- Otherwise `𝔪 I = I` by minimality, and a generator `t` of `I` satisfies `t = x t` for some
  -- `x ∈ 𝔪`, forcing `t = 0` as `1 - x` is a unit.
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
  refine (hI.le_iff.mp Ideal.mul_le_right).resolve_right fun h ↦ ht0 ?_
  have htm : t ∈ IsLocalRing.maximalIdeal R * Ideal.span {t} := by
    rwa [hI.span_singleton_eq ht ht0, h]
  obtain ⟨x, hx, hxt⟩ := Ideal.mem_mul_span_singleton.mp htm
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits x hx
  rw [← hunit.mul_right_eq_zero, sub_mul, one_mul, hxt, sub_self]

namespace Ideal

/-- For any homomorphism `f` of local rings, the maximal ideal of the target is the greatest ideal
contracting into the maximal ideal of the source. For instance, if `V` is a field inside a
local domain `W` and `p = 0`, then `p.map f = 0` while the greatest ideal of `W` contracting into
`p` is the maximal ideal of `W`. -/
theorem isGreatest_comap_le_maximalIdeal {V W : Type*} [CommSemiring V] [CommSemiring W]
    (f : V →+* W) [IsLocalRing V] [IsLocalRing W] :
    IsGreatest {J : Ideal W | J.comap f ≤ IsLocalRing.maximalIdeal V}
      (IsLocalRing.maximalIdeal W) :=
  ⟨IsLocalRing.le_maximalIdeal (comap_ne_top f (IsLocalRing.maximalIdeal.isMaximal W).ne_top),
    fun J hJ ↦ IsLocalRing.le_maximalIdeal fun h ↦
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.mp (by simpa [h] using hJ))⟩

end Ideal
