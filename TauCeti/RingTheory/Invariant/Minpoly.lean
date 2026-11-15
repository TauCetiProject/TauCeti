/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import TauCeti.Algebra.Ring.Action.End
public import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Ideal.Inertia

/-!
# The orbit polynomial of an algebra generator

For a faithful finite group action with invariant ring `R`, the orbit polynomial of a generator
of the `R`-algebra is its minimal polynomial, mapped to the algebra. Its derivative is therefore
the product of the nonidentity displacements, and its `g`-translates divide and are divided by
displacements of a generator of a normal-subgroup fixed subalgebra. This connects the different
and quotient ramification filtration of a monogenic extension with its lower filtration.

The orbit polynomial and its derivative are those of `MulSemiringAction.charpoly` and
`TauCeti.MulSemiringAction.eval_derivative_charpoly`.
-/

public section

open Polynomial

namespace TauCeti.MulSemiringAction

section Minpoly

variable {R S G : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
  [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsInvariant R S G] [FaithfulSMul G S]

/-- The minimal polynomial of an algebra generator is the orbit polynomial of a faithful
finite group action with invariant ring `R`. -/
theorem map_minpoly_eq_charpoly_of_adjoin_eq_top {x : S}
    (hx : Algebra.adjoin R {x} = ⊤) :
    (minpoly R x).map (algebraMap R S) = MulSemiringAction.charpoly G x := by
  have hint : IsIntegral R x := (Algebra.IsInvariant.isIntegral R S G).isIntegral x
  obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts R S G x
  simp only [coe_mapRingHom] at hp
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hint).map _)
    (MulSemiringAction.monic_charpoly G x)
  · have hroot : aeval x p = 0 := by
      rw [← eval_map_algebraMap, hp, MulSemiringAction.eval_charpoly]
    rw [← hp]
    exact Polynomial.map_dvd _ (minpoly.isIntegrallyClosed_dvd hint hroot)
  · exact Polynomial.natDegree_le_of_dvd
      (TauCeti.MulSemiringAction.charpoly_dvd
        (smul_left_injective_of_adjoin_singleton_eq_top hx)
        (fun g ↦ by simp only [eval_map_algebraMap, aeval_smul, minpoly.aeval, smul_zero]))
      ((minpoly.monic hint).map _).ne_zero

/-- At an algebra generator, the derivative of the minimal polynomial is the product of the
nonidentity displacements under the group action. -/
theorem aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top [DecidableEq G] {x : S}
    (hx : Algebra.adjoin R {x} = ⊤) :
    aeval x (derivative (minpoly R x)) =
      ∏ g ∈ (Finset.univ : Finset G).erase 1, (x - g • x) := by
  rw [← eval_map_algebraMap, ← derivative_map,
    map_minpoly_eq_charpoly_of_adjoin_eq_top (G := G) hx,
    TauCeti.MulSemiringAction.eval_derivative_charpoly]

end Minpoly

/-- If `FixedPoints.subalgebra R S H` is generated over `R` by `y`, then `g • y - y` divides
`(g • MulSemiringAction.charpoly H x).eval x`. -/
theorem smul_sub_dvd_eval_smul_charpoly {R S G : Type*} [CommRing R] [CommRing S]
    [IsLeftCancelMulZero S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (H : Subgroup G) [H.Normal] [Fintype H] {y : FixedPoints.subalgebra R S H}
    (hy : Algebra.adjoin R {y} = ⊤) (g : G) (x : S) :
    g • (y : S) - (y : S) ∣ (g • MulSemiringAction.charpoly H x).eval x := by
  set P := MulSemiringAction.charpoly H x
  rw [← sub_zero ((g • P).eval x), ← MulSemiringAction.eval_charpoly H x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  simpa [AddMonoidAlgebra.coeff_smul_apply] using TauCeti.coe_dvd_coe_fixedPoints_subalgebra_iff.2
    (TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (QuotientGroup.mk' H g)
      ⟨P.coeff n, MulSemiringAction.smul_coeff_charpoly x n⟩)

/-- If `S` is generated over `R` by `x` and `H ≤ G` acts faithfully on the domain `S`, then
`(g • MulSemiringAction.charpoly H x).eval x` divides `y - g • y` for every `H`-fixed `y ∈ S`. -/
theorem eval_smul_charpoly_dvd_sub_smul {R S G : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (H : Subgroup G) [Fintype H] [FaithfulSMul H S] {x y : S} (hx : Algebra.adjoin R {x} = ⊤)
    (hy : y ∈ MulAction.fixedPoints H S) (g : G) :
    (g • MulSemiringAction.charpoly H x).eval x ∣ y - g • y := by
  obtain ⟨q, hq⟩ : ∃ q : R[X], aeval x q = y := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
  set Q : S[X] := q.map (algebraMap R S) - C y
  obtain ⟨r, hr⟩ := TauCeti.MulSemiringAction.charpoly_dvd (f := Q)
    (TauCeti.smul_left_injective_of_adjoin_singleton_eq_top (G := H) hx) fun h ↦ by
      rw [eval_sub, eval_C, eval_map_algebraMap, Polynomial.aeval_smul, hq, hy h, sub_self]
  have hgQ : g • Q = q.map (algebraMap R S) - C (g • y) := by
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map,
      (RingHom.ext fun r₀ ↦ smul_algebraMap g r₀ :
        (MulSemiringAction.toRingHom G S g).comp (algebraMap R S) = algebraMap R S)]
  exact ⟨(g • r).eval x, by
    rw [← eval_mul, ← smul_mul', ← hr, hgQ, eval_sub, eval_C, eval_map_algebraMap, hq]⟩

end TauCeti.MulSemiringAction
