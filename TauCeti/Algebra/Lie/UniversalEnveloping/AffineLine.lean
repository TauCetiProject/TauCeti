/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Algebra.Lie.UniversalEnveloping.PCenter
import Mathlib.Data.ZMod.Basic

/-!
# Central `p`-polynomials for the two-dimensional nonabelian Lie algebra

`TauCeti.LieAlgebra.AffineLine K` is the Lie algebra of the affine line, spanned by a dilation `x`
and a translation `y` with `⁅x, y⁆ = y`.  This file computes, explicitly and for every element,
the central `p`-polynomial in `U(L)` whose existence
`TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial` asserts abstractly.

The computation is driven by one identity at the Lie-algebra level: the adjoint action of
`u : AffineLine K` satisfies `T ^ n = u.1 ^ (n - 1) • T` for `n ≠ 0`
(`TauCeti.LieAlgebra.AffineLine.ad_pow`), because `T` kills the dilation direction into the
translation line and scales that line by the dilation coordinate `u.1`.  Taking `n = p` turns it
into a monic linearized relation of degree `p`, so

`ι u ^ p - u.1 ^ (p - 1) • ι u`

is central in `U(L)`; having zero constant term it also lies in the augmentation ideal, by
`TauCeti.UniversalEnvelopingAlgebra.pPolynomial_ι_mem_augmentation_toIdeal`, so it belongs to
Hochschild's `Z(U(L)) ∩ U⁺(L)`.  At the two generators this reads
`ι x ^ p - ι x` and `ι y ^ p`, the two shapes a linearized polynomial can take: the adjoint action
of the dilation is idempotent, and that of the translation squares to zero.

The characteristic is assumed positive throughout, that is `p ≠ 1`: in characteristic zero the
displayed polynomial is `ι u - ι u = 0` and the statements below would say nothing.

The exponent is genuinely needed.  No nonzero element of `AffineLine K` becomes central in `U(L)`
(`TauCeti.LieAlgebra.AffineLine.ι_mem_center_iff_eq_zero`), so the polynomials above are not
central for the trivial reason that their linear parts already are.

For contrast, in the one-dimensional abelian Lie algebra the exponent may be taken to be
`p ^ 0 = 1`: `U(L)` is commutative there
(`TauCeti.UniversalEnvelopingAlgebra.instCommRing`), so `Subalgebra.center_eq_top` makes every
element central and `ι x` is itself a central `p`-polynomial.

## Main statements

* `TauCeti.LieAlgebra.AffineLine.ι_pow_sub_smul_ι_mem_center`: the explicit central
  `p`-polynomial of an arbitrary element.
* `TauCeti.LieAlgebra.AffineLine.ι_dilation_pow_sub_ι_dilation_mem_center` and
  `TauCeti.LieAlgebra.AffineLine.ι_translation_pow_mem_center`: the two generators.
* `TauCeti.LieAlgebra.AffineLine.ι_mem_center_iff_eq_zero`: over a field, the canonical copy of
  the Lie algebra meets the centre of `U(L)` only in `0`.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531--533.
* N. Jacobson, *Lie Algebras*, Interscience (1962), pp. 202--203.
-/

public section

namespace TauCeti

namespace LieAlgebra

namespace AffineLine

-- Mathlib does not register the Lie ring of an associative ring as a global instance; the
-- commutator of two elements of an enveloping algebra is written with it below.
attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {K : Type*} [CommRing K]

/-- **The explicit central `p`-polynomial of an element of the affine line.**  For every
`u : AffineLine K` the linearized polynomial `ι u ^ p - u.1 ^ (p - 1) • ι u` is central in
`U(L)`, where `u.1` is the dilation coordinate of `u`.  It is monic of degree `p` and has zero
constant term, so it is a central `p`-polynomial in the sense of
`TauCeti.UniversalEnvelopingAlgebra.exists_pCentralPolynomial`, exhibited here with no
Noetherian search.  The characteristic is positive: for `p = 1` the polynomial `T ^ p - T` is the
zero polynomial and the statement would be empty. -/
theorem ι_pow_sub_smul_ι_mem_center (p : ℕ) [ExpChar K p] (hp : p ≠ 1) (u : AffineLine K) :
    _root_.UniversalEnvelopingAlgebra.ι K u ^ p -
        u.1 ^ (p - 1) • _root_.UniversalEnvelopingAlgebra.ι K u ∈
      Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K (AffineLine K)) := by
  have hp0 : p ≠ 0 := ((expChar_is_prime_or_one K p).resolve_right hp).ne_zero
  have key := UniversalEnvelopingAlgebra.mem_center_of_ad_pPolynomial_eq_zero
    (R := K) (L := AffineLine K) (e := 1) (a := fun _ => -(u.1 ^ (p - 1))) (x := u) p ?_
  · simpa [Fin.sum_univ_one, neg_smul, sub_eq_add_neg] using key
  · simp only [pow_one, Fin.sum_univ_one, Fin.val_zero, pow_zero, neg_smul]
    rw [ad_pow u hp0, add_neg_cancel]

variable (K)

/-- **The central `p`-polynomial of the dilation** `x` is `ι x ^ p - ι x`: the adjoint action of
`x` is the projection onto the translation line, hence idempotent, so the linearized relation it
satisfies is `T ^ p = T`. -/
theorem ι_dilation_pow_sub_ι_dilation_mem_center (p : ℕ) [ExpChar K p] (hp : p ≠ 1) :
    _root_.UniversalEnvelopingAlgebra.ι K (dilation K) ^ p -
        _root_.UniversalEnvelopingAlgebra.ι K (dilation K) ∈
      Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K (AffineLine K)) := by
  simpa using ι_pow_sub_smul_ι_mem_center p hp (dilation K)

/-- **The central `p`-polynomial of the translation** `y` is the single Frobenius power
`ι y ^ p`: the adjoint action of `y` squares to zero, so already `T ^ p = 0` in positive
characteristic.  This is the shape
`TauCeti.UniversalEnvelopingAlgebra.exists_pow_ι_mem_center_of_isNilpotent_ad` predicts for an
adjoint-nilpotent element, here with the exponent `p ^ 1`. -/
theorem ι_translation_pow_mem_center (p : ℕ) [ExpChar K p] (hp : p ≠ 1) :
    _root_.UniversalEnvelopingAlgebra.ι K (translation K) ^ p ∈
      Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K (AffineLine K)) := by
  have hp1 : p - 1 ≠ 0 := by have := expChar_pos K p; omega
  simpa [zero_pow hp1] using ι_pow_sub_smul_ι_mem_center p hp (translation K)

/-- The canonical Lie generator attached to the translation `y` is nonzero: the adjoint
representation of `U(L)` sends it to `LieAlgebra.ad K (AffineLine K) y`, which moves the
dilation. -/
theorem ι_translation_ne_zero [Nontrivial K] :
    _root_.UniversalEnvelopingAlgebra.ι K (translation K) ≠ 0 := by
  intro h
  have hrep := congrArg
    (UniversalEnvelopingAlgebra.representation K (AffineLine K) (AffineLine K)) h
  rw [UniversalEnvelopingAlgebra.representation_ι_ad, map_zero] at hrep
  exact ad_translation_ne_zero K hrep

end CommRing

section Field

variable (K : Type*) [Field K]

/-- **The canonical copy of the affine line meets the centre of `U(L)` only in `0`.**  Hence the
passage to `p`-th powers in `TauCeti.LieAlgebra.AffineLine.ι_pow_sub_smul_ι_mem_center` is not an
artifact: apart from `0`, no element of the Lie algebra is already central in its enveloping
algebra. -/
theorem ι_mem_center_iff_eq_zero {u : AffineLine K} :
    _root_.UniversalEnvelopingAlgebra.ι K u ∈
        Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K (AffineLine K)) ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]; exact Subalgebra.zero_mem _⟩
  have hy : _root_.UniversalEnvelopingAlgebra.ι K (translation K) ≠ 0 := ι_translation_ne_zero K
  have hcent := (UniversalEnvelopingAlgebra.mem_center_iff_forall_lie_ι K (AffineLine K)).mp h
  -- Bracketing against the translation reads off the dilation coordinate of `u`.
  have hfst : u.1 • _root_.UniversalEnvelopingAlgebra.ι K (translation K) = 0 := by
    have := hcent (translation K)
    rw [← LieHom.map_lie] at this
    have hlie : ⁅u, translation K⁆ = u.1 • translation K := by ext <;> simp
    rwa [hlie, map_smul] at this
  -- Bracketing against the dilation reads off its translation coordinate.
  have hsnd : (-u.2) • _root_.UniversalEnvelopingAlgebra.ι K (translation K) = 0 := by
    have := hcent (dilation K)
    rw [← LieHom.map_lie] at this
    have hlie : ⁅u, dilation K⁆ = (-u.2) • translation K := by ext <;> simp
    rwa [hlie, map_smul] at this
  rw [smul_eq_zero] at hfst hsnd
  refine ext (hfst.resolve_right hy) ?_
  have := hsnd.resolve_right hy
  simpa using neg_eq_zero.mp this

end Field

section WorkedExamples

/-! ### The acceptance checks in characteristics `2` and `3`

The two smallest positive characteristics, over the prime fields, with the two central
`p`-polynomials made completely explicit. -/

example :
    _root_.UniversalEnvelopingAlgebra.ι (ZMod 2) (dilation (ZMod 2)) ^ 2 -
        _root_.UniversalEnvelopingAlgebra.ι (ZMod 2) (dilation (ZMod 2)) ∈
      Subalgebra.center (ZMod 2)
        (_root_.UniversalEnvelopingAlgebra (ZMod 2) (AffineLine (ZMod 2))) :=
  ι_dilation_pow_sub_ι_dilation_mem_center (ZMod 2) 2 (by norm_num)

example :
    _root_.UniversalEnvelopingAlgebra.ι (ZMod 2) (translation (ZMod 2)) ^ 2 ∈
      Subalgebra.center (ZMod 2)
        (_root_.UniversalEnvelopingAlgebra (ZMod 2) (AffineLine (ZMod 2))) :=
  ι_translation_pow_mem_center (ZMod 2) 2 (by norm_num)

example :
    _root_.UniversalEnvelopingAlgebra.ι (ZMod 3) (dilation (ZMod 3)) ^ 3 -
        _root_.UniversalEnvelopingAlgebra.ι (ZMod 3) (dilation (ZMod 3)) ∈
      Subalgebra.center (ZMod 3)
        (_root_.UniversalEnvelopingAlgebra (ZMod 3) (AffineLine (ZMod 3))) :=
  ι_dilation_pow_sub_ι_dilation_mem_center (ZMod 3) 3 (by norm_num)

example :
    _root_.UniversalEnvelopingAlgebra.ι (ZMod 3) (translation (ZMod 3)) ^ 3 ∈
      Subalgebra.center (ZMod 3)
        (_root_.UniversalEnvelopingAlgebra (ZMod 3) (AffineLine (ZMod 3))) :=
  ι_translation_pow_mem_center (ZMod 3) 3 (by norm_num)

end WorkedExamples

end AffineLine

end LieAlgebra

end TauCeti
