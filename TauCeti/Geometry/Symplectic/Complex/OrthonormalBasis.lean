/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Adapted orthonormal bases of an orthogonal complex structure

An orthogonal almost complex structure `J` on a finite-dimensional real inner product space
of dimension `2 * n` admits an orthonormal basis `(u₁, J u₁, …, uₙ, J uₙ)`. The statement
includes dimension zero. Such a basis gives the orientation induced by `J`.

The construction takes a complex orthonormal basis for the Hermitian metric induced by `J`,
then uses `TauCeti.complexEuclideanRealLinearIsometryEquiv` to place each real coordinate
immediately before its imaginary coordinate. Both constructions preserve the original norm
and real scalar action.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

namespace TauCeti.AlmostComplexStructure

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- An orthogonal complex structure admits an orthonormal basis consisting of consecutive
pairs `(u₁, J u₁, …, uₙ, J uₙ)`, including the empty basis in dimension zero. -/
theorem exists_adapted_orthonormalBasis (J : AlmostComplexStructure V) (hJ : ∀ v, ‖J v‖ = ‖v‖)
    (n : ℕ) (hdim : finrank ℝ V = 2 * n) :
    ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ V,
      ∀ k : Fin n, b ⟨2 * k.val + 1, by omega⟩ = J (b ⟨2 * k.val, by omega⟩) := by
  classical
  let := J.complexInnerProductSpace hJ
  let := J.complexInnerProductSpace_isScalarTower hJ
  have hI (v : V) : Complex.I • v = J v := by
    rw [J.complexInnerProductSpace_smul_def hJ]
    simp
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  have hn : finrank ℂ V = n := by
    have h := Module.finrank_mul_finrank ℝ ℂ V
    rw [Complex.finrank_real_complex, hdim] at h
    omega
  let b := (stdOrthonormalBasis ℂ V).reindex (finCongr hn)
  let f : V ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { b.repr.toLinearEquiv.restrictScalars ℝ with norm_map' := b.repr.norm_map }
  let e := f.trans (complexEuclideanRealLinearIsometryEquiv n)
  refine ⟨OrthonormalBasis.ofRepr e, fun k ↦ ?_⟩
  have hsingle :
      (complexEuclideanRealLinearIsometryEquiv n).symm
          (EuclideanSpace.single ⟨2 * k.val + 1, by omega⟩ (1 : ℝ)) =
        Complex.I • (complexEuclideanRealLinearIsometryEquiv n).symm
          (EuclideanSpace.single ⟨2 * k.val, by omega⟩ (1 : ℝ)) := by
    ext j
    simp only [complexEuclideanRealLinearIsometryEquiv_symm_apply,
      PiLp.smul_apply, smul_eq_mul]
    simp only [PiLp.single_apply, Fin.ext_iff, finProdFinEquiv, Equiv.coe_fn_mk,
      Fin.cast_mk]
    split_ifs <;> first | omega | norm_num
  simp only [OrthonormalBasis.coe_ofRepr, e, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply]
  rw [hsingle]
  exact (b.repr.symm.map_smul Complex.I _).trans (hI _)

end TauCeti.AlmostComplexStructure
