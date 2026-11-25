/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RingTheory.StableRange.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Bass stable range of semilocal rings

Stable range is unchanged by quotienting by an ideal contained in the Jacobson radical.
Semisimple rings have stable range at most one, so the same holds for semilocal rings.
The rank-one bound is the input to reduction of stable invertible matrices to units.

See Weibel, *The K-book*, Chapter I, Exercises 1.5(c) and 1.12(v), and Vaserstein,
*Stable rank of rings and dimensionality of topological spaces*, Lemma 3.
-/

public section

namespace TauCeti

/-- Passing to a quotient by a two-sided ideal in the Jacobson radical preserves every
Bass stable range bound. -/
theorem hasStableRangeLE_quotient_iff_of_le_jacobson {R : Type*} [Ring R]
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R) {s : ℕ} :
    HasStableRangeLE (R ⧸ I) s ↔ HasStableRangeLE R s := by
  refine ⟨fun h ↦ hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_,
    fun h ↦ h.of_surjective (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective⟩
  let q := Ideal.Quotient.mk I
  have hq : ∑ i, q (a i) * q (b i) = 1 := by
    simpa only [map_sum, map_mul, map_one] using congrArg q hab
  obtain ⟨c, d, hcd⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp h _ _ hq
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  choose c' hc using fun i ↦ hsurj (c i)
  choose d' hd using fun i ↦ hsurj (d i)
  let t := ∑ i, (a (Fin.castSucc i) + a (Fin.last s) * c' i) * d' i
  have ht : q t = q 1 := by
    simpa only [t, map_sum, map_mul, map_add, hc, hd, map_one] using hcd
  have hmem : t - 1 ∈ Ring.jacobson R := hI (Ideal.Quotient.eq.mp ht)
  have hunit : IsUnit t := by
    simpa using (Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mp hmem) 1
  -- Normalize the lifted witness on the right; the shortened row stays fixed.
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨c', fun i ↦ d' i * v, ?_⟩
  simpa only [t, Finset.sum_mul, mul_assoc] using hv

/-- The endomorphism ring of a finite-dimensional vector space over a division ring has
Bass stable range at most one. -/
theorem hasStableRangeLE_one_end (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] : HasStableRangeLE (Module.End K V) 1 := by
  refine hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_
  let A := a 0
  let B := a 1
  let q := A.range.mkQ
  have hqA (v : V) : q (A v) = 0 := by simp [q, Submodule.mkQ_apply]
  have hAB : A * b 0 + B * b 1 = 1 := by simpa [Fin.sum_univ_two, A, B] using hab
  have hqB : Function.Surjective (q.comp B) := by
    intro z
    obtain ⟨v, rfl⟩ := A.range.mkQ_surjective z
    refine ⟨b 1 v, ?_⟩
    simpa only [LinearMap.add_apply, mul_apply_eq_comp, one_apply_eq_self, map_add, hqA,
      zero_add, LinearMap.comp_apply] using congrArg q (LinearMap.congr_fun hAB v)
  obtain ⟨j, hj⟩ := (q.comp B).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqB)
  obtain ⟨p, hp⟩ := A.ker.subtype.exists_leftInverse_of_injective A.ker.ker_subtype
  let e : A.ker ≃ₗ[K] V ⧸ A.range :=
    LinearEquiv.ofFinrankEq _ _ (LinearMap.finrank_quotient_range_eq_finrank_ker A).symm
  -- Correct A on its kernel by lifting an isomorphism from the kernel to the cokernel.
  let C := j.comp (e.toLinearMap.comp p)
  have hqC (v : V) : q ((A + B * C) v) = e (p v) := by
    simpa only [map_add, LinearMap.add_apply, mul_apply_eq_comp, C, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hqA, zero_add, LinearMap.id_apply] using LinearMap.congr_fun hj (e (p v))
  have hinj : Function.Injective (A + B * C) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' := LinearMap.mem_ker.mp hv
    have hpv : p v = 0 := e.injective (by simpa [hv'] using (hqC v).symm)
    have hAv : A v = 0 := by simpa [C, hpv] using hv'
    have h := LinearMap.congr_fun hp (⟨v, LinearMap.mem_ker.mpr hAv⟩ : A.ker)
    simpa [hpv] using h.symm
  have hunit : IsUnit (A + B * C) :=
    (Module.End.isUnit_iff _).mpr ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  obtain ⟨D, hD⟩ := hunit.exists_right_inv
  exact ⟨fun _ ↦ C, fun _ ↦ D, by simpa [A, B] using hD⟩

/-- A possibly noncommutative semisimple ring has Bass stable range at most one. -/
theorem hasStableRangeLE_one_of_semisimple (R : Type*) [Ring R] [IsSemisimpleRing R] :
    HasStableRangeLE R 1 := by
  obtain ⟨n, D, d, hD, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let (i : Fin n) : DivisionRing (D i) := hD i
  refine e.hasStableRangeLE_iff.mpr (hasStableRangeLE_pi_iff.mpr fun i ↦ ?_)
  classical
  exact matrixRingEquivEndVecMulOpposite.hasStableRangeLE_iff.mpr
    (hasStableRangeLE_mop_iff.mpr (hasStableRangeLE_one_end (D i) (Fin (d i) → D i)))

/-- A ring with semisimple Jacobson quotient (a semilocal ring) has
Bass stable range at most one. -/
theorem hasStableRangeLE_one_of_isSemisimpleRing (R : Type*) [Ring R]
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] : HasStableRangeLE R 1 :=
  (hasStableRangeLE_quotient_iff_of_le_jacobson (Ring.jacobson R) le_rfl).mp
    (hasStableRangeLE_one_of_semisimple (R ⧸ Ring.jacobson R))

end TauCeti
