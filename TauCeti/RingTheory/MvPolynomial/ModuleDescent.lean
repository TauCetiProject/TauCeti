/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.LinearAlgebra.Matrix.BaseChange

/-!
# Finite-variable descent of module presentations

A finitely presented module over `R[σ]`, even for infinite `σ`, is obtained by extension of
scalars from a finitely presented module over a polynomial subalgebra in finitely many of the
same variables. Indeed, the entries of a finite presentation matrix involve only finitely
many variables. The comparison is a linear equivalence over the full polynomial ring,
not just an identification after restricting scalars.

We use `MvPolynomial.supported R s` for the finite stage, so the coefficient map is its
actual inclusion in `R[σ]`. Mathlib's `supportedEquivMvPolynomial` identifies this stage with
`R[s]`. In particular, when `R` is Noetherian these stages are Noetherian, although `R[σ]`
need not be. No Noetherian hypothesis is needed for the descent itself.

The construction uses Mathlib's `Module.FinitePresentation.exists_fin'` by Joël Riou for
the finite presentation and `MvPolynomial.mem_supported` for variable support. The matrix
cokernel comparison then supplies the scalar-extension equivalence.
-/

public section

open scoped TensorProduct

namespace Module.FinitePresentation

universe u v w

variable {R : Type u} {σ : Type w} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module (MvPolynomial σ R) M]
  [Module.FinitePresentation (MvPolynomial σ R) M]

/-- A finite presentation over a polynomial ring descends, with its finite matrix, to the
subalgebra supported on finitely many variables. The matrix has the same generator and
relation counts before and after extension of scalars. -/
theorem exists_matrix_supported :
    ∃ (s : Finset σ) (n m : ℕ)
      (A : Matrix (Fin n) (Fin m) (MvPolynomial.supported R (s : Set σ))),
      Nonempty (MvPolynomial σ R ⊗[MvPolynomial.supported R (s : Set σ)]
        ((Fin n → MvPolynomial.supported R (s : Set σ)) ⧸ LinearMap.range A.mulVecLin)
          ≃ₗ[MvPolynomial σ R] M) := by
  classical
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' (MvPolynomial σ R) M
  let B := LinearMap.toMatrix' g
  let s : Finset σ := Finset.univ.biUnion fun ij : Fin n × Fin m ↦ (B ij.1 ij.2).vars
  have hB (i : Fin n) (j : Fin m) : B i j ∈ MvPolynomial.supported R (s : Set σ) := by
    rw [MvPolynomial.mem_supported]
    intro k hk
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, hk⟩
  let A : Matrix (Fin n) (Fin m) (MvPolynomial.supported R (s : Set σ)) :=
    fun i j ↦ ⟨B i j, hB i j⟩
  have hA : A.map (algebraMap (MvPolynomial.supported R (s : Set σ)) (MvPolynomial σ R)) = B :=
    rfl
  have hg : B.mulVecLin = g := Matrix.toLin'_toMatrix' g
  have hrange : LinearMap.range g = LinearMap.ker f := hgf.linearMap_ker_eq.symm
  refine ⟨s, n, m, A, ⟨?_⟩⟩
  exact A.cokernelBaseChangeEquiv ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [hA, hg, hrange]) ≪≫ₗ
      LinearMap.quotKerEquivOfSurjective f hf

/-- Every finitely presented module over a polynomial ring is the scalar extension of a
finitely presented module over a finite-variable polynomial subalgebra. The descended
module can be chosen in the universe of the polynomial ring. -/
theorem exists_supported_baseChange :
    ∃ (s : Finset σ) (N : Type (max u w)) (_ : AddCommGroup N)
      (_ : Module (MvPolynomial.supported R (s : Set σ)) N),
      Module.FinitePresentation (MvPolynomial.supported R (s : Set σ)) N ∧
        Nonempty (MvPolynomial σ R ⊗[MvPolynomial.supported R (s : Set σ)] N
          ≃ₗ[MvPolynomial σ R] M) := by
  obtain ⟨s, n, m, A, e⟩ := exists_matrix_supported (R := R) (σ := σ) M
  refine ⟨s, _, inferInstance, inferInstance, ?_, e⟩
  apply Module.finitePresentation_of_surjective (LinearMap.range A.mulVecLin).mkQ
    (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range _

end Module.FinitePresentation
