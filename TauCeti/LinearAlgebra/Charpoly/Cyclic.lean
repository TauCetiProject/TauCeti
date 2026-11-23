/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic polynomials of cyclic endomorphisms

If a monic polynomial `p` of degree `finrank R M` annihilates an endomorphism `f` of a finite free
module `M` over a commutative ring `R`, and the first `finrank R M` powers of `f` applied to a
vector `v` are linearly independent, then `f.charpoly = p`: the difference `f.charpoly - p` has
degree `< finrank R M` and annihilates `f`, so evaluating at `v` forces every coefficient below
`finrank R M` to vanish.

## Main results

* `LinearMap.charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_linearIndependent_pow`: a monic
  annihilating polynomial of degree `finrank R M` equals `f.charpoly` when the first
  `finrank R M` powers of `f` on `v` are linearly independent.
-/

public section

open Polynomial

namespace LinearMap

/-- **Cyclic-vector criterion for the characteristic polynomial of an endomorphism.** If `p` is
monic of degree `finrank R M`, annihilates `f`, and the first `finrank R M` powers `(f ^ i) v` are
linearly independent, then `f.charpoly = p`. -/
theorem charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_linearIndependent_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {f : Module.End R M} {p : R[X]} {v : M}
    (hp : p.IsMonicOfDegree (Module.finrank R M)) (hann : aeval f p = 0)
    (hli : LinearIndependent R fun i : Fin (Module.finrank R M) ↦ (f ^ (i : ℕ)) v) :
    f.charpoly = p := by
  nontriviality R
  rcases Nat.eq_zero_or_pos (Module.finrank R M) with hr | hr
  · have hfp : f.charpoly = 1 :=
      eq_one_of_monic_natDegree_zero f.charpoly_monic (by rw [f.charpoly_natDegree, hr])
    have hp1 : p = 1 := isMonicOfDegree_zero_iff.mp (hr ▸ hp)
    exact hfp.trans hp1.symm
  have hdeg_lt : (f.charpoly - p).natDegree < Module.finrank R M :=
    IsMonicOfDegree.natDegree_sub_lt hr.ne' ⟨f.charpoly_natDegree, f.charpoly_monic⟩ hp
  have hann_sub : aeval f (f.charpoly - p) = 0 := by
    rw [map_sub, f.aeval_self_charpoly, hann, sub_zero]
  rw [← sub_eq_zero]
  set q := f.charpoly - p
  have h0 : aeval f q v = 0 := by rw [hann_sub, LinearMap.zero_apply]
  rw [aeval_eq_sum_range' hdeg_lt, LinearMap.sum_apply] at h0
  simp_rw [LinearMap.smul_apply] at h0
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ q.coeff i • (f ^ i) v)] at h0
  have hcoeff :=
    Fintype.linearIndependent_iff.mp hli (fun i : Fin (Module.finrank R M) ↦ q.coeff i) h0
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j (Module.finrank R M) with hj | hj
  · exact hcoeff ⟨j, hj⟩
  · exact coeff_eq_zero_of_natDegree_lt (hdeg_lt.trans_le hj)

end LinearMap
