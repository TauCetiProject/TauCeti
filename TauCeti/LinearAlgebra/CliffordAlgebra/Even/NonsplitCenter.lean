/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center

import TauCeti.Algebra.Quaternion.CentralSimple
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Center
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Quaternion models of quaternary even Clifford algebras over field centers

Let `Q` be a regular four-dimensional quadratic form over a field of characteristic different
from two. When the center `E` of its even Clifford algebra is a field, the even Clifford algebra
is a quaternion algebra over `E`, and Clifford reversal is quaternion conjugation.

Choose three vectors `v₀, v₁, v₂` from an anisotropic orthogonal basis. The bivectors
`i = v₀v₁` and `j = v₀v₂` anticommute, and their squares are the nonzero scalars
`-Q(v₀)Q(v₁)` and `-Q(v₀)Q(v₂)`. They therefore induce a homomorphism from a quaternion algebra
over `E`. The source is simple, while source and target both have dimension four over `E`, so this
homomorphism is an equivalence. Reversal fixes `E` and negates `i`, `j`, and `ij`, which proves
compatibility with conjugation.

## Main results

* `CliffordAlgebra.exists_evenQuaternionEquiv_of_finrank_eq_four_of_isField_center` constructs
  the reversal-preserving quaternion model over the center.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

open Module

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- A regular quaternary even Clifford algebra whose center is a field is a quaternion algebra
over that center. The equivalence carries Clifford reversal to quaternion conjugation, and its two
symbol parameters are units. -/
theorem exists_evenQuaternionEquiv_of_finrank_eq_four_of_isField_center
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (hfield : IsField (Subalgebra.center K (even Q))) :
    ∃ a b : (Subalgebra.center K (even Q))ˣ,
      ∃ e : even Q ≃ₐ[Subalgebra.center K (even Q)]
          ℍ[Subalgebra.center K (even Q),(a : _),0,(b : _)],
        ∀ x, e (reverseEven Q x) = star (e x) := by
  let E := Subalgebra.center K (even Q)
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : IsScalarTower K E (even Q) := Subalgebra.isScalarTower_centerAlgebra
  obtain ⟨B, horth, haniso⟩ := hQ.exists_orthogonal_basis
  let n0 : Fin (finrank K V) := ⟨0, by omega⟩
  let n1 : Fin (finrank K V) := ⟨1, by omega⟩
  let n2 : Fin (finrank K V) := ⟨2, by omega⟩
  have h01 : Q.IsOrtho (B n0) (B n1) := horth n0 n1 (by simp [n0, n1])
  have h02 : Q.IsOrtho (B n0) (B n2) := horth n0 n2 (by simp [n0, n2])
  have h12 : Q.IsOrtho (B n1) (B n2) := horth n1 n2 (by simp [n1, n2])
  let aK : Kˣ := Units.mk0 (-(Q (B n0) * Q (B n1)))
    (neg_ne_zero.mpr (mul_ne_zero (haniso n0) (haniso n1)))
  let bK : Kˣ := Units.mk0 (-(Q (B n0) * Q (B n2)))
    (neg_ne_zero.mpr (mul_ne_zero (haniso n0) (haniso n2)))
  let a : Eˣ := Units.map (algebraMap K E).toMonoidHom aK
  let b : Eˣ := Units.map (algebraMap K E).toMonoidHom bK
  let i : even Q := (even.ι Q).bilin (B n0) (B n1)
  let j : even Q := (even.ι Q).bilin (B n0) (B n2)
  -- The center action on the even algebra is multiplication by its algebra map; unfolding the
  -- mapped units then exposes the original base-field symbol parameters.
  have ha_smul : (a : E) • (1 : even Q) =
      algebraMap K (even Q) (-(Q (B n0) * Q (B n1))) := by
    change algebraMap E (even Q) (algebraMap K E (-(Q (B n0) * Q (B n1)))) * 1 = _
    rw [Subalgebra.centerAlgebra_algebraMap_apply, mul_one]
    rfl
  have hb_smul : (b : E) • (1 : even Q) =
      algebraMap K (even Q) (-(Q (B n0) * Q (B n2))) := by
    change algebraMap E (even Q) (algebraMap K E (-(Q (B n0) * Q (B n2)))) * 1 = _
    rw [Subalgebra.centerAlgebra_algebraMap_apply, mul_one]
    rfl
  have hi_sq : i * i = (a : E) • (1 : even Q) := by
    rw [ha_smul]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, coe_even_ι_bilin, ι_mul_ι_mul_self_of_isOrtho h01]
    simp
  have hj_sq : j * j = (b : E) • (1 : even Q) := by
    rw [hb_smul]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, coe_even_ι_bilin, ι_mul_ι_mul_self_of_isOrtho h02]
    simp
  have hji : j * i = -(i * j) := by
    apply Subtype.ext
    -- After subtype extensionality, expose the four Clifford generators represented by the two
    -- even bivectors so the orthogonality commutation lemmas apply.
    change (ι Q (B n0) * ι Q (B n2)) * (ι Q (B n0) * ι Q (B n1)) =
      -((ι Q (B n0) * ι Q (B n1)) * (ι Q (B n0) * ι Q (B n2)))
    calc
      _ = -((ι Q (B n0) * ι Q (B n0)) * (ι Q (B n2) * ι Q (B n1))) :=
        mul_ι_mul_ι_mul_comm_of_isOrtho (ι Q (B n0)) h02.symm (ι Q (B n1))
      _ = (ι Q (B n0) * ι Q (B n0)) * (ι Q (B n1) * ι Q (B n2)) := by
        rw [ι_mul_ι_comm_of_isOrtho h12.symm]
        simp
      _ = -(-((ι Q (B n0) * ι Q (B n0)) * (ι Q (B n1) * ι Q (B n2)))) := by simp
      _ = _ := by
        rw [← mul_ι_mul_ι_mul_comm_of_isOrtho (ι Q (B n0)) h01.symm (ι Q (B n2))]
  let qBasis : QuaternionAlgebra.Basis (even Q) (a : E) 0 (b : E) := {
    i := i
    j := j
    k := i * j
    i_mul_i := by
      calc
        i * i = (a : E) • (1 : even Q) := hi_sq
        _ = (a : E) • (1 : even Q) + (0 : E) • i := by
          apply Subtype.ext
          simp
    j_mul_j := hj_sq
    i_mul_j := rfl
    j_mul_i := by
      calc
        j * i = -(i * j) := hji
        _ = (0 : E) • j - i * j := by
          apply Subtype.ext
          simp
  }
  let f : ℍ[E,(a : E),0,(b : E)] →ₐ[E] even Q := qBasis.liftHom
  -- Unfold the local bivector abbreviations before using the reversal formula for `even.ι`.
  have hrev_i : reverseEven Q i = -i := by
    change reverseEven Q ((even.ι Q).bilin (B n0) (B n1)) =
      -((even.ι Q).bilin (B n0) (B n1))
    rw [reverseEven_ι]
    apply Subtype.ext
    simp only [coe_even_ι_bilin]
    exact ι_mul_ι_comm_of_isOrtho h01.symm
  have hrev_j : reverseEven Q j = -j := by
    change reverseEven Q ((even.ι Q).bilin (B n0) (B n2)) =
      -((even.ι Q).bilin (B n0) (B n2))
    rw [reverseEven_ι]
    apply Subtype.ext
    simp only [coe_even_ι_bilin]
    exact ι_mul_ι_comm_of_isOrtho h02.symm
  have hrev_scalar (z : E) :
      reverseEven Q (algebraMap E (even Q) z) = algebraMap E (even Q) z :=
    TauCeti.CliffordAlgebra.reverseEven_eq_self_of_mem_center_of_finrank_eq_four
      hQ hV z.property
  have hrev_alg_mul (z : E) (x : even Q) :
      reverseEven Q (algebraMap E (even Q) z * x) =
        algebraMap E (even Q) z * reverseEven Q x := by
    rw [reverseEven_mul, hrev_scalar]
    exact Subalgebra.mem_center_iff.mp z.property (reverseEven Q x)
  have hf_star (x : ℍ[E,(a : E),0,(b : E)]) :
      reverseEven Q (f x) = f (star x) := by
    simp only [f, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
    simp only [map_add, hrev_scalar, Algebra.smul_def]
    rw [hrev_alg_mul, hrev_alg_mul, hrev_alg_mul]
    simp only [QuaternionAlgebra.re_star, zero_mul, add_zero,
      QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star]
    dsimp only [qBasis]
    rw [(algebraMap E (even Q)).map_neg, (algebraMap E (even Q)).map_neg,
      (algebraMap E (even Q)).map_neg]
    simp only [neg_mul]
    -- The quaternion lift expands into four center-scalar products; state that common normal form
    -- explicitly before substituting the reversal equations for the generators.
    change algebraMap E (even Q) x.re +
          algebraMap E (even Q) x.imI * reverseEven Q i +
          algebraMap E (even Q) x.imJ * reverseEven Q j +
          algebraMap E (even Q) x.imK * reverseEven Q (i * j) =
      algebraMap E (even Q) x.re + -(algebraMap E (even Q) x.imI * i) +
          -(algebraMap E (even Q) x.imJ * j) +
          -(algebraMap E (even Q) x.imK * (i * j))
    rw [hrev_i, hrev_j, reverseEven_mul, hrev_j, hrev_i, neg_mul_neg, hji]
    simp only [mul_neg]
  let _ := hfield.toField
  have htwoE : (2 : E) ≠ 0 := by
    intro h
    have h' : algebraMap K E (2 : K) = algebraMap K E (0 : K) := by
      simpa only [map_ofNat, map_zero] using h
    exact (isUnit_of_invertible (2 : K)).ne_zero
      (FaithfulSMul.algebraMap_injective K E h')
  let _ : Invertible (2 : E) := invertibleOfNonzero htwoE
  let _ : IsSimpleRing ℍ[E,(a : E),0,(b : E)] :=
    TauCeti.QuaternionAlgebra.instIsSimpleRing a b
  let _ : Module.Finite E (even Q) := finite_even_over_center Q
  have hf_inj : Function.Injective f := f.toRingHom.injective
  have hdim : finrank E ℍ[E,(a : E),0,(b : E)] = finrank E (even Q) := by
    rw [QuaternionAlgebra.finrank_eq_four,
      finrank_even_over_center_of_finrank_eq_four Q hQ hV hfield]
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hf_inj
  let fEquiv : ℍ[E,(a : E),0,(b : E)] ≃ₐ[E] even Q :=
    AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨a, b, fEquiv.symm, ?_⟩
  intro x
  apply fEquiv.injective
  rw [fEquiv.apply_symm_apply]
  -- Unfold `fEquiv` only at this inverse-image boundary so `hf_star` applies to the original
  -- presentation homomorphism `f`.
  change reverseEven Q x = f (star (fEquiv.symm x))
  rw [← hf_star]
  congr 1
  exact (fEquiv.apply_symm_apply x).symm

end CliffordAlgebra

end
