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

section Quaternary

variable (Q : QuadraticForm K V)

/-- The center of the even Clifford algebra of `Q`. -/
local notation "𝓩" => Subalgebra.center K (even Q)

/-- Two anticommuting elements of the even Clifford algebra, with central scalar squares and
negated by reversal, give a reversal-compatible homomorphism from the quaternion algebra over
the center. -/
private lemma exists_algHom_reverse_star (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) {a b : 𝓩ˣ} {i j : even Q}
    (hi_sq : i * i = (a : 𝓩) • (1 : even Q))
    (hj_sq : j * j = (b : 𝓩) • (1 : even Q))
    (hji : j * i = -(i * j)) (hrev_i : reverseEven Q i = -i) (hrev_j : reverseEven Q j = -j) :
    ∃ f : ℍ[𝓩,(a : _),0,(b : _)] →ₐ[𝓩]
        even Q, ∀ x, reverseEven Q (f x) = f (star x) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let qBasis : QuaternionAlgebra.Basis (even Q) (a : 𝓩) 0 (b : 𝓩) := {
    i := i
    j := j
    k := i * j
    i_mul_i := by
      calc
        i * i = (a : 𝓩) • (1 : even Q) := hi_sq
        _ = (a : 𝓩) • (1 : even Q) + (0 : 𝓩) • i := by
          apply Subtype.ext
          simp
    j_mul_j := hj_sq
    i_mul_j := rfl
    j_mul_i := by
      calc
        j * i = -(i * j) := hji
        _ = (0 : 𝓩) • j - i * j := by
          apply Subtype.ext
          simp
  }
  have hrev_scalar (z : 𝓩) :
      reverseEven Q (algebraMap 𝓩 (even Q) z) = algebraMap 𝓩 (even Q) z :=
    TauCeti.CliffordAlgebra.reverseEven_eq_self_of_mem_center_of_finrank_eq_four
      hQ hV z.property
  have hrev_alg_mul (z : 𝓩) (x : even Q) :
      reverseEven Q (algebraMap 𝓩 (even Q) z * x) =
        algebraMap 𝓩 (even Q) z * reverseEven Q x := by
    rw [reverseEven_mul, hrev_scalar]
    exact Subalgebra.mem_center_iff.mp z.property (reverseEven Q x)
  refine ⟨qBasis.liftHom, fun x => ?_⟩
  simp only [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
  simp only [map_add, hrev_scalar, Algebra.smul_def]
  rw [hrev_alg_mul, hrev_alg_mul, hrev_alg_mul]
  simp only [QuaternionAlgebra.re_star, zero_mul, add_zero,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  dsimp only [qBasis]
  rw [(algebraMap 𝓩 (even Q)).map_neg, (algebraMap 𝓩 (even Q)).map_neg,
    (algebraMap 𝓩 (even Q)).map_neg]
  simp only [neg_mul]
  -- The quaternion lift expands into four center-scalar products; state that common normal form
  -- explicitly before substituting the reversal equations for the generators.
  change algebraMap 𝓩 (even Q) x.re +
        algebraMap 𝓩 (even Q) x.imI * reverseEven Q i +
        algebraMap 𝓩 (even Q) x.imJ * reverseEven Q j +
        algebraMap 𝓩 (even Q) x.imK * reverseEven Q (i * j) =
    algebraMap 𝓩 (even Q) x.re + -(algebraMap 𝓩 (even Q) x.imI * i) +
        -(algebraMap 𝓩 (even Q) x.imJ * j) +
        -(algebraMap 𝓩 (even Q) x.imK * (i * j))
  rw [hrev_i, hrev_j, reverseEven_mul, hrev_j, hrev_i, neg_mul_neg, hji]
  simp only [mul_neg]

/-- A reversal-compatible homomorphism from a quaternion algebra over the field center of a
quaternary even Clifford algebra is an equivalence. -/
private lemma exists_equiv_of_algHom_reverse_star (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) (hfield : IsField 𝓩)
    (a b : 𝓩ˣ)
    (f : ℍ[𝓩,(a : _),0,(b : _)] →ₐ[𝓩]
      even Q)
    (hf_star : ∀ x, reverseEven Q (f x) = f (star x)) :
    ∃ e : even Q ≃ₐ[𝓩]
        ℍ[𝓩,(a : _),0,(b : _)],
      ∀ x, e (reverseEven Q x) = star (e x) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : IsScalarTower K 𝓩 (even Q) := Subalgebra.isScalarTower_centerAlgebra
  let _ := hfield.toField
  let _ : Invertible (2 : 𝓩) := IsScalarTower.invertibleAlgebraCoeNat K 𝓩 2
  let _ : IsSimpleRing ℍ[𝓩,(a : 𝓩),0,(b : 𝓩)] :=
    TauCeti.QuaternionAlgebra.instIsSimpleRing a b
  let _ : Module.Finite 𝓩 (even Q) := finite_even_over_center Q
  have hf_inj : Function.Injective f := f.toRingHom.injective
  have hdim : finrank 𝓩 ℍ[𝓩,(a : 𝓩),0,(b : 𝓩)] = finrank 𝓩 (even Q) := by
    rw [QuaternionAlgebra.finrank_eq_four,
      finrank_even_over_center_of_finrank_eq_four Q hQ hV hfield]
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hf_inj
  let fEquiv : ℍ[𝓩,(a : 𝓩),0,(b : 𝓩)] ≃ₐ[𝓩] even Q :=
    AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨fEquiv.symm, ?_⟩
  intro x
  apply fEquiv.injective
  rw [fEquiv.apply_symm_apply]
  -- Unfold `fEquiv` only at this inverse-image boundary so `hf_star` applies to the original
  -- presentation homomorphism `f`.
  change reverseEven Q x = f (star (fEquiv.symm x))
  rw [← hf_star]
  congr 1
  exact (fEquiv.apply_symm_apply x).symm

end Quaternary

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
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ := hQ.exists_orthogonal_triple (by omega)
  let _ : IsScalarTower K (Subalgebra.center K (even Q)) (even Q) :=
    Subalgebra.isScalarTower_centerAlgebra
  let a : (Subalgebra.center K (even Q))ˣ :=
    Units.map (algebraMap K (Subalgebra.center K (even Q))).toMonoidHom
      (Units.mk0 (-(Q x * Q y)) (neg_ne_zero.mpr (mul_ne_zero hx hy)))
  let b : (Subalgebra.center K (even Q))ˣ :=
    Units.map (algebraMap K (Subalgebra.center K (even Q))).toMonoidHom
      (Units.mk0 (-(Q x * Q z)) (neg_ne_zero.mpr (mul_ne_zero hx hz)))
  -- The center action on the even algebra is multiplication by its algebra map; unfolding the
  -- mapped units then exposes the original base-field symbol parameters.
  have ha_smul : (a : Subalgebra.center K (even Q)) • (1 : even Q) =
      algebraMap K (even Q) (-(Q x * Q y)) := by
    change algebraMap (Subalgebra.center K (even Q)) (even Q)
      (algebraMap K (Subalgebra.center K (even Q)) (-(Q x * Q y))) * 1 = _
    rw [Subalgebra.centerAlgebra_algebraMap_apply, mul_one]
    rfl
  have hb_smul : (b : Subalgebra.center K (even Q)) • (1 : even Q) =
      algebraMap K (even Q) (-(Q x * Q z)) := by
    change algebraMap (Subalgebra.center K (even Q)) (even Q)
      (algebraMap K (Subalgebra.center K (even Q)) (-(Q x * Q z))) * 1 = _
    rw [Subalgebra.centerAlgebra_algebraMap_apply, mul_one]
    rfl
  obtain ⟨f, hf_star⟩ := exists_algHom_reverse_star Q hQ hV (a := a) (b := b)
    (i := (even.ι Q).bilin x y) (j := (even.ι Q).bilin x z)
    (by rw [ha_smul]; exact even_ι_bilin_mul_self_of_isOrtho hxy)
    (by rw [hb_smul]; exact even_ι_bilin_mul_self_of_isOrtho hxz)
    (even_ι_bilin_comm_of_isOrtho hxy hxz hyz) (reverseEven_even_ι_bilin_of_isOrtho hxy)
    (reverseEven_even_ι_bilin_of_isOrtho hxz)
  obtain ⟨e, he⟩ := exists_equiv_of_algHom_reverse_star Q hQ hV hfield a b f hf_star
  exact ⟨a, b, e, he⟩

end CliffordAlgebra

end
