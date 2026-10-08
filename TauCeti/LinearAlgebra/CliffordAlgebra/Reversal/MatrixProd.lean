/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
public import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

import Mathlib.Algebra.Central.Matrix
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.QuaternionProduct

/-!
# Reversal in a product of two-by-two matrix algebras

Every matrix-product model of the even Clifford algebra of a regular four-dimensional quadratic
space carries reversal to adjugation in both factors. Consequently its reverse norm-one equation
is precisely the pair of determinant-one equations. In particular, this applies to the model given
by the two half-spin actions, so the factors of the Spin group act on the half-spin modules by
their standard representations.

The quaternion-product description
`CliffordAlgebra.exists_evenQuaternionProdEquiv_of_finrank_eq_four` supplies the intrinsic fact
that an element plus its reversal is central. The product version of
`Matrix.eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one` then identifies reversal.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, §15.
-/

public section

namespace CliffordAlgebra

open scoped Quaternion

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  (Q : QuadraticForm K V)

private theorem add_reverseEven_mem_center_of_split_center
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (hE : Nonempty (Subalgebra.center K (even Q) ≃ₐ[K] K × K)) (x : even Q) :
    x + reverseEven Q x ∈ Subalgebra.center K (even Q) := by
  obtain ⟨a, b, e, he⟩ := exists_evenQuaternionProdEquiv_of_finrank_eq_four Q hQ hV hE
  rw [Subalgebra.mem_center_iff]
  intro y
  apply e.injective
  simp only [map_mul, map_add, he]
  apply Prod.ext <;>
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_add, Prod.snd_add,
      Prod.fst_star, Prod.snd_star, QuaternionAlgebra.self_add_star'] <;>
    exact (QuaternionAlgebra.coe_commute _ _).eq.symm

/-- Every two-by-two matrix-product model of a regular quaternary even Clifford algebra
carries reversal to adjugation in both factors. -/
@[simp]
theorem map_reverseEven_eq_adjugate_prod_of_finrank_eq_four
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (x : even Q) :
    e (reverseEven Q x) = (Matrix.adjugate (e x).1, Matrix.adjugate (e x).2) := by
  let M := Matrix (Fin 2) (Fin 2) K
  let ep : (Fin 2 → M) ≃ₐ[K] M × M :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ : Fin 2 => M)) (fun _ => rfl)
  let ek : (Fin 2 → K) ≃ₐ[K] K × K :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ : Fin 2 => K)) (fun _ => rfl)
  have hE : Nonempty (Subalgebra.center K (even Q) ≃ₐ[K] K × K) :=
    ⟨(TauCeti.centerCongr (e.trans ep.symm)).trans <|
      TauCeti.centerPiAlgEquiv.trans <|
        (AlgEquiv.piCongrRight (fun _ => TauCeti.centerAlgEquivOfIsCentral K M)).trans ek⟩
  let f : M × M →ₗ[K] M × M :=
    e.toLinearMap.comp ((reverseEven Q).comp e.symm.toLinearMap)
  have hf (A : M × M) : f A = e (reverseEven Q (e.symm A)) := rfl
  have hmul (A B : M × M) : f (A * B) = f B * f A := by
    simp only [hf, map_mul, reverseEven_mul]
  have hscalar (A : M × M) :
      A + f A ∈ Subalgebra.center K (M × M) := by
    have h : e (e.symm A + reverseEven Q (e.symm A)) ∈ Subalgebra.center K (M × M) :=
      TauCeti.map_center_eq_center e ▸
        Subalgebra.mem_map.mpr ⟨_,
          add_reverseEven_mem_center_of_split_center Q hQ hV hE _, rfl⟩
    simpa only [map_add, e.apply_symm_apply, ← hf] using h
  have hscalar' (A : M × M) : ∃ r s : K, A + f A = (r • 1, s • 1) := by
    have h := hscalar A
    rw [Subalgebra.center_prod, Subalgebra.mem_prod] at h
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff K).mp h.1
    obtain ⟨s, hs⟩ := (Algebra.IsCentral.mem_center_iff K).mp h.2
    exact ⟨r, s, Prod.ext
      (by simpa [Algebra.algebraMap_eq_smul_one] using hr)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hs)⟩
  simpa only [LinearMap.toAddMonoidHom_coe, hf, e.symm_apply_apply] using
    Matrix.eq_adjugate_prod_of_antimultiplicative_of_exists_add_eq_smul_one
      f.toAddMonoidHom hmul hscalar' (e x)

/-- The reverse norm-one equation in a quaternary matrix-product model is exactly determinant
one in both factors. -/
theorem reverseEven_mul_eq_one_iff_det_eq_one_prod_of_finrank_eq_four
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (x : even Q) :
    reverseEven Q x * x = 1 ↔ (e x).1.det = 1 ∧ (e x).2.det = 1 := by
  rw [← map_eq_one_iff e e.injective, map_mul,
    map_reverseEven_eq_adjugate_prod_of_finrank_eq_four Q hQ hV e]
  rw [Prod.ext_iff]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_one, Prod.snd_one,
    Matrix.adjugate_mul_self_eq_one_iff_det_eq_one]

end CliffordAlgebra
