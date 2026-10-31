/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.LeftMulMatrixRpow
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Adjoint
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Complexification
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Real powers of positive Spin elements

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space over `𝕜 = ℝ` or `ℂ`, and
fix a basis `B` of its Clifford algebra. For a Clifford element `a` whose left multiplication
matrix `M` is positive semidefinite, the real power `Algebra.leftMulMatrixRpow B a t` is the
Clifford element with matrix `M ^ t`. If `a` lies in the Spin group, then so does every real
power `a ^ t`.

The Spin group consists of the even elements `x` with `star x * x = 1`, `x * star x = 1` and
`involute x * v * star x` a vector for every vector `v`. The real power of an even element is
even, being a polynomial in it. The other conditions are bilinear identities `Φ (x, x) = d`, since
`star` is linear. The natural powers `a ^ n` are Spin elements, so they satisfy these identities,
and `Algebra.bilin_leftMulMatrixRpow_eq_of_forall_pow` extends the identities to all real powers.

For a real form `Q` with a real orthonormal basis, the ordered-product basis `e_s` of the
complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` is orthonormal for the positive-form trace pairing.
For a Spin element `g`, the matrix of `g† * g` is positive definite, where
`g† = complexConj (reverse g)` is the positive-form adjoint
(`CliffordAlgebra.posDef_toMatrix_mulLeft_complexConj_reverse_mul_self`). Also, `g† * g` is again
a Spin element (`CliffordAlgebra.complexConj_reverse_mem_spinGroup`). So all the real powers
`(g† g) ^ t` lie in the Spin group. They are the positive factors of the polar decomposition
`g = (g (g† g) ^ (-1/2)) (g† g) ^ (1/2)` of complex Spin elements.

## Main results

* `CliffordAlgebra.leftMulMatrixRpow_mem_spinGroup`: for a nondegenerate form, the real powers of
  a Spin element with positive semidefinite matrix are Spin elements.
* `CliffordAlgebra.leftMulMatrixRpow_complexConj_reverse_mul_self_mem_spinGroup`: for a real
  orthonormal basis, the real powers of `g† * g` are Spin elements for every Spin element `g`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace CliffordAlgebra

/-- **Real powers of positive Spin elements are Spin elements.** Let `Q` be a nondegenerate
quadratic form on a finite-dimensional space over `𝕜 = ℝ` or `ℂ`, and `B` a basis of its Clifford
algebra. If `a` lies in the Spin group and its left multiplication matrix is positive
semidefinite, then every real power `Algebra.leftMulMatrixRpow B a t` lies in the Spin group. -/
theorem leftMulMatrixRpow_mem_spinGroup {𝕜 W J : Type*} [RCLike 𝕜] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] [Fintype J] [DecidableEq J] {Q : QuadraticForm 𝕜 W}
    (hQ : Q.Nondegenerate) (B : Module.Basis J 𝕜 (CliffordAlgebra Q)) {a : CliffordAlgebra Q}
    (ha : a ∈ spinGroup Q) (hM : 0 ≤ Algebra.leftMulMatrix B a) (t : ℝ) :
    Algebra.leftMulMatrixRpow B a t ∈ spinGroup Q := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · -- On the zero space the Lipschitz group is trivial, so `a = 1` and its real powers are `1`.
    obtain ⟨u, hu, rfl⟩ := pinGroup.mem_lipschitzGroup (spinGroup.mem_pin ha)
    simp only [SetLike.mem_coe, Subgroup.mem_toSubmonoid, lipschitzGroup_eq_bot,
      Subgroup.mem_bot] at hu
    subst hu
    rw [Units.coeHom_apply, Units.val_one,
      (Algebra.leftMulMatrixRpow_eq_iff B (y := 1)).2 (by simp)]
    exact one_mem _
  have hspin (x : CliffordAlgebra Q) :=
    mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι (x := x) Q hQ hQ.exists_isUnit
  have hpow (n : ℕ) := (hspin _).1 (pow_mem ha n)
  -- The real power is a polynomial in the even element `a`, so it is even.
  have heven : Algebra.leftMulMatrixRpow B a t ∈ even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (by simpa using (hpow 1).2.1))
      (Algebra.leftMulMatrixRpow_mem_adjoin B a t)
  -- The other conditions are bilinear identities, since `star = reverse ∘ involute` is linear.
  let starL : CliffordAlgebra Q →ₗ[𝕜] CliffordAlgebra Q := reverse ∘ₗ involute.toLinearMap
  have hstarL (x : CliffordAlgebra Q) : starL x = star x := (star_def x).symm
  rw [hspin, Unitary.mem_iff]
  refine ⟨⟨?_, ?_⟩, heven, fun m ↦ ?_⟩
  · simpa [hstarL] using Algebra.bilin_leftMulMatrixRpow_eq_of_forall_pow hM
      ((LinearMap.mul 𝕜 _).compl₁₂ starL LinearMap.id) 1
      (fun n ↦ by simpa [hstarL] using (Unitary.mem_iff.1 (hpow n).1).1) t
  · simpa [hstarL] using Algebra.bilin_leftMulMatrixRpow_eq_of_forall_pow hM
      ((LinearMap.mul 𝕜 _).compl₁₂ LinearMap.id starL) 1
      (fun n ↦ by simpa [hstarL] using (Unitary.mem_iff.1 (hpow n).1).2) t
  · -- Twisted conjugation by an even element is ordinary conjugation; read it modulo vectors.
    have key := Algebra.bilin_leftMulMatrixRpow_eq_of_forall_pow hM
      (((LinearMap.mul 𝕜 _).compl₁₂ (LinearMap.mulRight 𝕜 (ι Q m)) starL).compr₂
        (LinearMap.range (ι Q)).mkQ) 0
      (fun n ↦ by
        have hn := (hpow n).2.2 m
        rw [involute_eq_of_mem_even (hpow n).2.1] at hn
        simpa [hstarL, Submodule.Quotient.mk_eq_zero] using hn) t
    rw [involute_eq_of_mem_even heven]
    simpa [hstarL, Submodule.Quotient.mk_eq_zero] using key

/-- **The real powers of `g† g` are Spin elements.** Let `Q` be a real quadratic form with a real
orthonormal basis `b`, and `e_s` the ordered-product basis of `Cℓ(ℂ ⊗ V, Q_ℂ)` for `1 ⊗ b`. For
every Spin element `g` of `Q_ℂ`, every real power `(g† g) ^ t`, taken through the matrix of
`g† * g` in the basis `e_s`, lies in the Spin group. Here `g† = complexConj (reverse g)` is the
positive-form adjoint, and the matrix of `g† * g` is positive definite. -/
theorem leftMulMatrixRpow_complexConj_reverse_mul_self_mem_spinGroup {V I : Type*}
    [AddCommGroup V] [Module ℝ V] [LinearOrder I] [Fintype I] {Q : QuadraticForm ℝ V}
    {b : Module.Basis I ℝ V} (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (hQ : ∀ i, Q (b i) = 1) (g : spinGroup (Q.baseChange ℂ)) (t : ℝ) :
    Algebra.leftMulMatrixRpow (basis (Q.baseChange ℂ) (b.baseChange ℂ))
        (complexConj Q (reverse (g : CliffordAlgebra (Q.baseChange ℂ))) * g) t ∈
      spinGroup (Q.baseChange ℂ) := by
  have : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
  have hg : IsUnit (g : CliffordAlgebra (Q.baseChange ℂ)) :=
    Unitary.isUnit_coe (U := (⟨g, pinGroup.mem_unitary (spinGroup.mem_pin g.2)⟩ :
      unitary (CliffordAlgebra (Q.baseChange ℂ))))
  have hM := (posDef_toMatrix_mulLeft_complexConj_reverse_mul_self hb hQ hg).posSemidef.nonneg
  rw [Algebra.toMatrix_lmul_eq] at hM
  exact leftMulMatrixRpow_mem_spinGroup
    (QuadraticForm.Nondegenerate.baseChange (QuadraticMap.nondegenerate_of_isOrthoᵢ hb
      (by simp [hQ])))
    _ (mul_mem (complexConj_reverse_mem_spinGroup g.2) g.2) hM t

end CliffordAlgebra
