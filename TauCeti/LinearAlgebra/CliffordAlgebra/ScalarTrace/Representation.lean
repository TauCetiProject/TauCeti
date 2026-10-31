/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Spinor traces and the Hilbert–Schmidt pairing

For a complex Clifford representation of an even-dimensional Euclidean space with negative
quadratic form, the ordinary trace is the dimension of the representation times the Clifford
scalar trace. No irreducibility or metric on the representation is needed for this identity.
Chirality implements the grade involution, which makes the ordinary trace grade invariant;
`CliffordAlgebra.eq_smul_scalarTrace` then identifies this functional.

For a representation with skew-adjoint real generators, this identifies the scalar-trace
pairing with the normalized Hilbert–Schmidt pairing. In orthonormal coordinates the pairing
is the ordinary coefficient pairing of the ordered Clifford monomials. Thus the monomials
are orthonormal for the normalized, not the unnormalized, Hilbert–Schmidt pairing on a
nonzero representation. Through the native `CliffordAlgebra.equivExterior`, these identities
fix the metric normalization in comparisons of exterior forms with endomorphisms of spinors,
including dimension zero.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module
open scoped TensorProduct ComplexConjugate

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : Even (finrank ℝ V))

include hQ hn

section Trace

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)

/-- On an even-dimensional negative-metric Clifford module, the trace of the action is
`dim S` times the scalar trace. This holds for reducible and zero modules as well. -/
theorem trace_map_eq_finrank_mul_scalarTrace (a : CliffordAlgebra (Q.baseChange ℂ)) :
    LinearMap.trace ℂ S (ρ a) = finrank ℂ S * scalarTrace (Q.baseChange ℂ) a := by
  let : Fact (finrank ℝ V = finrank ℝ V) := ⟨rfl⟩
  let o := (stdOrthonormalBasis ℝ V).toBasis.orientation
  obtain ⟨l, hl, hspan⟩ := QuadraticMap.exists_list_pairwise_isOrtho (Q.baseChange ℂ)
  have h := LinearMap.congr_fun (eq_smul_scalarTrace hl hspan
    ((LinearMap.trace ℂ S).comp ρ.toLinearMap)
    (fun x y => by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      LinearMap.trace_mul_comm])
    (fun x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [← complexVolume_mul_mul_complexVolume o hQ hn x]
      simp only [map_mul]
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ,
        complexVolume_mul_self o hQ, map_one, one_mul])) a
  simpa using h

end Trace

section Metric

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)
  (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
    -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))

include hρ

/-- The Hilbert–Schmidt pairing of a Clifford action is `dim S` times the scalar-trace
pairing, when real Clifford multiplication is skew-adjoint. -/
theorem trace_adjoint_map_mul (a b : CliffordAlgebra (Q.baseChange ℂ)) :
    LinearMap.trace ℂ S ((ρ a).adjoint * ρ b) =
      finrank ℂ S * scalarTrace (Q.baseChange ℂ) (conjStar Q a * b) := by
  rw [adjoint_map_eq_map_conjStar ρ hρ, ← map_mul,
    trace_map_eq_finrank_mul_scalarTrace hQ hn]

/-- In an orthonormal frame the Hilbert–Schmidt pairing of Clifford operators is
`dim S` times the coefficient pairing of their ordered monomials. -/
theorem trace_adjoint_map_mul_eq_sum {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) (a b : CliffordAlgebra (Q.baseChange ℂ)) :
    LinearMap.trace ℂ S ((ρ a).adjoint * ρ b) = finrank ℂ S *
      ((basis (Q.baseChange ℂ) (e.toBasis.baseChange ℂ)).repr a).sum
        (fun s z => conj z * (basis (Q.baseChange ℂ) (e.toBasis.baseChange ℂ)).repr b s) := by
  rw [trace_adjoint_map_mul hQ hn ρ hρ, scalarTrace_conjStar_mul (e.isOrthoᵢ_associated hQ)]
  simp [hQ, e.orthonormal.1]

/-- Ordered Clifford monomials from an orthonormal frame are pairwise Hilbert–Schmidt
orthogonal, with squared Hilbert–Schmidt norm `dim S`. -/
theorem trace_adjoint_map_basis_mul_basis {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) (s t : Finset I) :
    LinearMap.trace ℂ S
      ((ρ (basis (Q.baseChange ℂ) (e.toBasis.baseChange ℂ) s)).adjoint *
        ρ (basis (Q.baseChange ℂ) (e.toBasis.baseChange ℂ) t)) =
      if s = t then (finrank ℂ S : ℂ) else 0 := by
  rw [trace_adjoint_map_mul_eq_sum hQ hn ρ hρ e]
  simp only [Module.Basis.repr_self]
  rw [Finsupp.sum_single_index (by simp)]
  simp [Finsupp.single_apply, eq_comm]

/-- Under the inverse Chevalley map, the exterior Gram metric is carried to `1 / dim S`
times the Hilbert–Schmidt pairing. Here it is stated without division, so it also applies to
the zero representation. The exterior metric is the supplied form making increasing wedges
of a complexified real orthonormal frame orthonormal. -/
theorem trace_adjoint_map_equivExterior_symm_mul {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V)
    (a b : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    LinearMap.trace ℂ S
      ((ρ ((equivExterior (Q.baseChange ℂ)).symm a)).adjoint *
        ρ ((equivExterior (Q.baseChange ℂ)).symm b)) =
      finrank ℂ S * Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ) a b := by
  classical
  rw [trace_adjoint_map_mul_eq_sum hQ hn ρ hρ e, Matrix.toLinearMapₛₗ₂_one_apply]
  -- The Clifford basis is the exterior basis transported by the inverse Chevalley map.
  simp only [basis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]

end Metric

omit hn

section Spinor

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)

/-- In a full spinor representation the scalar trace is `2 ^ (-dim V / 2)` times the
ordinary trace. The factor is one in dimension zero. -/
theorem scalarTrace_eq_inv_two_pow_mul_trace (a : CliffordAlgebra (Q.baseChange ℂ)) :
    scalarTrace (Q.baseChange ℂ) a =
      (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S (ρ a) := by
  have heven : Even (finrank ℂ (ℂ ⊗[ℝ] V)) := even_finrank_of_algEquiv_end _ ρ
  have hevenR : Even (finrank ℝ V) := by simpa only [finrank_baseChange] using heven
  -- Use the dimension theorem for the module whose action is exactly `ρ`.
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) S := Module.compHom S ρ.toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) : a • s = ρ a s := rfl
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S :=
    ⟨fun c a s => by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  have hlsmul : Algebra.lsmul ℂ ℂ S = ρ.toAlgHom := by
    apply AlgHom.ext
    intro a
    exact LinearMap.ext (hact a)
  have hbij : Function.Bijective (Algebra.lsmul ℂ ℂ S :
      CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) := by
    rw [hlsmul]
    exact ρ.bijective
  have hdim := finrank_eq_two_pow_of_bijective_lsmul (Q.baseChange ℂ) hbij heven
  rw [finrank_baseChange] at hdim
  have htrace := trace_map_eq_finrank_mul_scalarTrace hQ hevenR ρ.toAlgHom a
  simp only [AlgEquiv.toAlgHom_apply] at htrace
  rw [htrace, hdim, Nat.cast_pow, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]

end Spinor

section SpinorMetric

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)

/-- **The normalized Hilbert–Schmidt comparison.** The inverse Chevalley map followed by a
full spinor representation carries the exterior Gram metric to
`2 ^ (-dim V / 2) * tr(A† B)`. In particular, the unnormalized Hilbert–Schmidt squared norm
is `2 ^ (dim V / 2)` times the exterior squared norm. -/
theorem inv_two_pow_mul_trace_adjoint_map_equivExterior_symm_mul
    (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
    {I : Type*} [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)
    (a b : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * LinearMap.trace ℂ S
      ((ρ ((equivExterior (Q.baseChange ℂ)).symm a)).adjoint *
        ρ ((equivExterior (Q.baseChange ℂ)).symm b)) =
      Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ) a b := by
  have heven := even_finrank_of_algEquiv_end (Q.baseChange ℂ) ρ
  rw [finrank_baseChange] at heven
  have hnorm : (2 ^ (finrank ℝ V / 2) : ℂ)⁻¹ * (finrank ℂ S : ℂ) = 1 := by
    simpa using (scalarTrace_eq_inv_two_pow_mul_trace hQ ρ 1).symm
  have hpair := trace_adjoint_map_equivExterior_symm_mul hQ heven ρ.toAlgHom
    (by simpa only [AlgEquiv.toAlgHom_apply] using hρ) e a b
  simp only [AlgEquiv.toAlgHom_apply] at hpair
  rw [hpair, ← mul_assoc, hnorm, one_mul]

end SpinorMetric

end CliffordAlgebra
