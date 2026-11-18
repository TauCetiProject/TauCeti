/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.Geometry.Symplectic.Darboux.Basis

import Mathlib.LinearAlgebra.Eigenspace.Pi
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Simultaneous hyperbolic normal form in `sp(V, ω)`

Let `(V, ω)` be a finite-dimensional real symplectic vector space. This file proves that a
pairwise commuting family `f` of semisimple elements of the symplectic Lie algebra `sp(V, ω)` with
real spectra is diagonal in a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`, with opposite eigenvalues on
each pair:

`f i qₖ = c i k • qₖ`,  `f i pₖ = -c i k • pₖ`

(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`).

Indeed the joint eigenspaces of the family span `V`. Since `ω (f i u) v = -ω u (f i v)`, the form
`ω` pairs the joint eigenspaces for `χ` and `ψ` trivially unless `ψ = -χ`, so the graded
symplectic-basis theorem `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top`,
for the involution `χ ↦ -χ`, gives a Darboux basis of joint eigenvectors; the pairing
`ω(qₖ, pₖ) = 1` then forces the eigenvalues of `pₖ` to be opposite to those of `qₖ`. No hypothesis
on the eigenvalues is needed: the zero eigenvalue is allowed, and then `f i` vanishes on the
corresponding pair.

This is the linear algebra behind Williamson's classification of split Cartan subalgebras of
`sp(V, ω)`. Its analogue for commuting complex-linear elements of `sp(V, ω)`, which act on
complex lines instead, is
`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint`.

## Main results

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`: commuting
  semisimple elements of `sp(V, ω)` with real spectra are simultaneously diagonal in a Darboux
  basis, with opposite eigenvalues on `qₖ` and `pₖ`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-- **Simultaneous hyperbolic normal form.** A pairwise commuting family `f` of semisimple
elements of `sp(V, ω)` whose spectra are real (their generalized eigenspaces span `V`) is
simultaneously diagonal in a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`, with opposite eigenvalues on
each pair: `f i qₖ = c i k • qₖ` and `f i pₖ = -c i k • pₖ`. -/
theorem exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint [FiniteDimensional ℝ V]
    {ι : Type*} (f : ι → Module.End ℝ V) (hf : ∀ i, f i ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple)
    (hsplit : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (c : ι → Fin n → ℝ), ω.IsDarbouxBasis b ∧
      ∀ i k, f i (b (k, 0)) = c i k • b (k, 0) ∧ f i (b (k, 1)) = -c i k • b (k, 1) := by
  have hf' (i : ι) (v w : V) : ω (f i v) w = -ω v (f i w) := by
    simpa using (LinearMap.mem_skewAdjointSubmodule _).1 (hf i) v w
  have hmem {χ : ι → ℝ} {v : V} (hv : v ∈ ⨅ i, (f i).eigenspace (χ i)) (i : ι) :
      f i v = χ i • v :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv i)
  -- The family is simultaneously diagonalizable: its joint eigenspaces span `V`.
  have heq (i : ι) (μ : ℝ) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hspan : ⨆ χ : ι → ℝ, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
        hcomm hsplit
  -- `ω` pairs the joint eigenspaces for `χ` and `ψ` trivially unless `ψ = -χ`.
  have horth {χ ψ : ι → ℝ} {v w : V} (hv : v ∈ ⨅ i, (f i).eigenspace (χ i))
      (hw : w ∈ ⨅ i, (f i).eigenspace (ψ i)) (hvw : ω v w ≠ 0) : ψ = -χ := by
    funext i
    have h := hf' i v w
    beta_reduce at h hvw
    rw [hmem hv i, hmem hw i, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul] at h
    have h' : (χ i + ψ i) * ω.toBilinForm v w = 0 := by linear_combination h
    rw [Pi.neg_apply]
    linear_combination (mul_eq_zero.1 h').resolve_right hvw
  -- A Darboux basis of joint eigenvectors, with opposite eigenvalues on each pair.
  obtain ⟨m, d, hd, hdW⟩ := ω.isAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top ω.nondegenerate
    (σ := Neg.neg) neg_involutive hspan
    fun χ ψ hψ v hv w hw ↦ by_contra fun h ↦ hψ (horth hv hw h)
  choose χ hχ using hdW
  have hb : ω.IsDarbouxBasis (d.reindex (darbouxIndexEquiv m).symm) :=
    isDarbouxBasis_reindex_symm_iff.2 hd
  refine ⟨m, d.reindex (darbouxIndexEquiv m).symm, fun i k ↦ χ (.inr k) i, hb, fun i k ↦ ?_⟩
  have hneg : χ (.inl k) = -χ (.inr k) := horth (hχ (.inr k)) (hχ (.inl k)) <| by
    simpa [Basis.reindex_apply] using (hb.apply_fst_snd k k).trans_ne (by simp)
  simp only [Basis.reindex_apply, Equiv.symm_symm, darbouxIndexEquiv_apply_zero,
    darbouxIndexEquiv_apply_one]
  exact ⟨hmem (hχ (.inr k)) i, by rw [hmem (hχ (.inl k)) i, hneg, Pi.neg_apply]⟩

end TauCeti.SymplecticForm
