/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Quaternion
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.SplitCenter

import TauCeti.Algebra.Subalgebra.Center
import TauCeti.LinearAlgebra.CliffordAlgebra.OddSplitting
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Quaternion factors of quaternary Spin groups with split center

Let `Q` be a regular four-dimensional quadratic form over a field of characteristic different
from two. If the center of its even Clifford algebra splits as `K × K`, then the even Clifford
algebra is a product of two copies of a quaternion algebra. Clifford reversal becomes quaternion
conjugation in each factor, so the Spin group is the product of the corresponding two norm-one
quaternion groups.

The proof first reduces the even Clifford algebra to the full Clifford algebra of a regular
ternary form. The image of its volume element under either coordinate of the split center gives
a square root of the volume square. After normalization, the odd-dimensional splitting identifies
the full ternary Clifford algebra with two copies of its even algebra. The existing ternary
quaternion model identifies each copy with the same quaternion algebra.

The conclusion does not say that the quaternion algebra itself splits. Over the reals this
distinguishes the compact product of Hamilton quaternion norm-one groups from the split product
of two special linear groups.

## Main results

* `CliffordAlgebra.exists_evenQuaternionProdEquiv_of_finrank_eq_four` gives a
  reversal-preserving quaternion-product model for a regular quaternary form with split center.
* `CliffordAlgebra.spinGroupEquivQuaternionUnitaryProd` transports a chosen model to Spin.
* `CliffordAlgebra.normForm_fst_spinGroupEquivQuaternionUnitaryProd` and
  `CliffordAlgebra.normForm_snd_spinGroupEquivQuaternionUnitaryProd` identify both factors as
  norm-one quaternion groups.
* `CliffordAlgebra.exists_spinGroupEquivQuaternionUnitaryProd_of_finrank_eq_four` packages the
  resulting group equivalence existentially.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- A regular quaternary even Clifford algebra with split center is a product of two copies of a
quaternion algebra. The equivalence carries Clifford reversal to componentwise quaternion
conjugation. The quaternion symbols are units but need not be squares. -/
theorem exists_evenQuaternionProdEquiv_of_finrank_eq_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (hE : Nonempty (Subalgebra.center K (even Q) ≃ₐ[K] K × K)) :
    ∃ a b : Kˣ, ∃ e : even Q ≃ₐ[K]
        ℍ[K,(a : K),0,(b : K)] × ℍ[K,(a : K),0,(b : K)],
      ∀ x, e (reverseEven Q x) = star (e x) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨eC⟩ := hE
  obtain ⟨n, P, hP, hn, g, hg⟩ :=
    TauCeti.CliffordAlgebra.exists_reversalEquiv_even_of_finrank_pos hQ (by omega)
  have hn3 : n = 3 := by omega
  subst n
  let eZ : Subalgebra.center K (CliffordAlgebra P) ≃ₐ[K] K × K :=
    (TauCeti.centerCongr g).symm.trans eC
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hP.exists_list_pairwise_isOrtho
  have hlen3 : l.length = 3 := by
    rw [hlen, Module.finrank_fin_fun]
  have hodd : Odd l.length := by rw [hlen3]; decide
  let c : K := (-1 : K) ^ l.length.choose 2 * (l.map P).prod
  let z : Subalgebra.center K (CliffordAlgebra P) :=
    ⟨(l.map (ι P)).prod, prod_map_ι_mem_center_of_odd_length hl hodd hspan⟩
  let t : K := (eZ z).1
  have hzsq : z * z = algebraMap K (Subalgebra.center K (CliffordAlgebra P)) c := by
    apply Subtype.ext
    exact prod_map_ι_sq_scalar hl
  have ht : t * t = c := by
    have h := congrArg Prod.fst (congrArg eZ hzsq)
    simpa [t, c] using h
  have hc : c ≠ 0 := neg_one_pow_choose_two_mul_prod_map_ne_zero hQl
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hc
    rw [← ht, ht0, zero_mul]
  let s : K := t⁻¹
  have hs : s * s * ((-1 : K) ^ l.length.choose 2 * (l.map P).prod) = 1 := by
    have hsc : s * s * c = 1 := by
      rw [← ht]
      calc
        s * s * (t * t) = (t⁻¹ * t) * (t⁻¹ * t) := by simp [s]; ring
        _ = 1 := by simp [ht0]
    simpa only [c] using hsc
  let split := equivEvenProdOfOddLength hl hodd hspan hs
  have hstarVolume : star (s • (l.map (ι P)).prod) = s • (l.map (ι P)).prod := by
    simp [star_def, involute_prod_map_ι, reverse_prod_map_ι_of_pairwise_isOrtho hl,
      hlen3, smul_smul]
    norm_num
  obtain ⟨a, b, q, hq⟩ :=
    exists_evenQuaternionEquiv_of_finrank_eq_three P hP (by simp)
  let e := g.trans (split.trans (q.prodCongr q))
  refine ⟨a, b, e, ?_⟩
  intro x
  simp only [e, AlgEquiv.trans_apply, hg, split]
  rw [equivEvenProdOfOddLength_star hl hodd hspan hs hstarVolume]
  ext <;> simp [hq]

/-- A chosen reversal-preserving quaternion-product model identifies the quaternary Spin group
with the product of the two quaternion unitary groups. -/
noncomputable def spinGroupEquivQuaternionUnitaryProd
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    {a b : K} (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    spinGroup Q ≃* unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b] :=
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ (by omega) (by omega) e he).trans <|
    Unitary.prodEquiv ℍ[K,a,0,b] ℍ[K,a,0,b]

/-- The chosen Spin equivalence evaluates the quaternion-product algebra model on the underlying
even Clifford element. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitaryProd_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    {a b : K} (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    (((spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).1 : ℍ[K,a,0,b]),
      ((spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).2 : ℍ[K,a,0,b])) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  rw [spinGroupEquivQuaternionUnitaryProd, MulEquiv.trans_apply,
    Unitary.coe_prodEquiv_apply,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply]

/-- The inverse chosen Spin equivalence recovers the Clifford value through the inverse
quaternion-product algebra model. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitaryProd_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    {a b : K} (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x))
    (q : unitary ℍ[K,a,0,b] × unitary ℍ[K,a,0,b]) :
    ((spinGroupEquivQuaternionUnitaryProd Q hQ hV e he).symm q : CliffordAlgebra Q) =
      (e.symm ((q.1 : ℍ[K,a,0,b]), (q.2 : ℍ[K,a,0,b])) : CliffordAlgebra Q) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  rw [spinGroupEquivQuaternionUnitaryProd, MulEquiv.symm_trans_apply,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_symm_apply,
    Unitary.coe_prodEquiv_symm_apply]

/-- The first quaternion attached to a quaternary Spin element has norm one. -/
@[simp]
theorem normForm_fst_spinGroupEquivQuaternionUnitaryProd
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    {a b : K} (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    QuaternionAlgebra.normForm a 0 b
      (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).1 = 1 :=
  (QuaternionAlgebra.mem_unitary_iff_normForm_eq_one _ _ _ _).mp
    (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).1.2

/-- The second quaternion attached to a quaternary Spin element has norm one. -/
@[simp]
theorem normForm_snd_spinGroupEquivQuaternionUnitaryProd
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    {a b : K} (e : even Q ≃ₐ[K] ℍ[K,a,0,b] × ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    QuaternionAlgebra.normForm a 0 b
      (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).2 = 1 :=
  (QuaternionAlgebra.mem_unitary_iff_normForm_eq_one _ _ _ _).mp
    (spinGroupEquivQuaternionUnitaryProd Q hQ hV e he s).2.2

/-- Every regular quaternary Spin group with split even-Clifford center is isomorphic to the
product of two norm-one groups of a quaternion algebra with unit symbols. -/
theorem exists_spinGroupEquivQuaternionUnitaryProd_of_finrank_eq_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (hE : Nonempty (Subalgebra.center K (even Q) ≃ₐ[K] K × K)) :
    ∃ a b : Kˣ, Nonempty (spinGroup Q ≃*
      unitary ℍ[K,(a : K),0,(b : K)] × unitary ℍ[K,(a : K),0,(b : K)]) := by
  obtain ⟨a, b, e, he⟩ := exists_evenQuaternionProdEquiv_of_finrank_eq_four Q hQ hV hE
  exact ⟨a, b, ⟨spinGroupEquivQuaternionUnitaryProd Q hQ hV e he⟩⟩

end CliffordAlgebra

end
