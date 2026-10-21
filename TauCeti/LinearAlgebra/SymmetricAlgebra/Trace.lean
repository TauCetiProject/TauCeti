/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete
import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# Graded traces on a symmetric algebra

An endomorphism `f` of a module `M` acts on each homogeneous component `Symⁿ M` of the symmetric
algebra, by the restriction of `SymmetricAlgebra.map f`. When `f` is diagonal in a finite basis,
with eigenvalues `aᵢ`, the monomials in that basis are eigenvectors of the induced map, so its
trace on `Symⁿ M` is the complete homogeneous symmetric polynomial `hₙ(a)`. Collecting these
traces into a power series gives the **graded trace formula**

`∑ₙ tr(f | Symⁿ M) tⁿ = det(1 - t f)⁻¹`,

stated as `(∑ₙ tr(f | Symⁿ M) tⁿ) * det(1 - t f) = 1` in `R⟦t⟧`, with `det(1 - t f)` the reverse of
the characteristic polynomial of `f`. Averaged over a finite group acting on `M = V*`, this is the
term-by-term content of Molien's formula for the Hilbert series of the invariants of `Sym(V*)`.

## Main results

* `Module.Basis.homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous_of_apply`: an endomorphism
  diagonal in a basis is diagonal in the induced monomial basis of `Symⁿ M`.
* `Module.Basis.trace_homogeneousSubmoduleMapₛₗ_of_apply`: its trace on `Symⁿ M` is the sum of
  the eigenvalue products over the degree-`n` multisets of basis indices.
* `Module.Basis.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_apply`: the graded
  trace formula.
* `Module.End.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_iSup_eigenspace_eq_top`:
  the graded trace formula for an endomorphism of a finite-dimensional vector space whose
  eigenspaces span, which therefore has an eigenbasis.
* `Module.End.IsSemisimple.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly`: the case of
  a semisimple endomorphism over an algebraically closed field.

## References

* T. Molien, *Über die Invarianten der linearen Substitutionsgruppen*, Sitzungsber. Königl.
  Preuss. Akad. Wiss. (1897), 1152–1156.
* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), 475–511, Theorem 2.1.
-/

public section

open Module

namespace TauCeti.SymmetricAlgebra

variable {R M κ : Type*}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **An endomorphism diagonal in a basis is diagonal in the monomial basis of `Symⁿ M`**: the
monomial indexed by `s` is an eigenvector of the induced map, with eigenvalue the product of the
eigenvalues listed by `s`. -/
theorem _root_.Module.Basis.homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous_of_apply
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (hf : ∀ i, f (b i) = a i • b i) (n : ℕ)
    (s : Sym κ n) :
    homogeneousSubmoduleMapₛₗ f n (b.symmetricAlgebraHomogeneous n s) =
      ((s : Multiset κ).map a).prod • b.symmetricAlgebraHomogeneous n s := by
  apply Subtype.ext
  simp [b.coe_symmetricAlgebraHomogeneous_apply, map_multiset_prod, hf, Algebra.smul_def,
    ← Multiset.prod_map_mul]

/-- **The trace on `Symⁿ M` of an endomorphism diagonal in a finite basis** is the sum, over the
degree-`n` multisets of basis indices, of the product of the corresponding eigenvalues: the
complete homogeneous symmetric polynomial `hₙ` evaluated at the eigenvalues. -/
theorem _root_.Module.Basis.trace_homogeneousSubmoduleMapₛₗ_of_apply [Fintype κ] [DecidableEq κ]
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (hf : ∀ i, f (b i) = a i • b i) (n : ℕ) :
    LinearMap.trace R (homogeneousSubmodule R M n) (homogeneousSubmoduleMapₛₗ f n) =
      ∑ s : Sym κ n, ((s : Multiset κ).map a).prod := by
  rw [LinearMap.trace_eq_matrix_trace R (b.symmetricAlgebraHomogeneous n), Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    b.homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous_of_apply f a hf]
  simp

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- **The graded trace formula.** If `f` is diagonal in a finite basis, the generating function
of its traces on the homogeneous components of the symmetric algebra is the inverse of
`det(1 - t f)`, the reverse of the characteristic polynomial of `f`:
`(∑ₙ tr(f | Symⁿ M) tⁿ) * det(1 - t f) = 1`. -/
theorem _root_.Module.Basis.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_apply
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (hf : ∀ i, f (b i) = a i • b i) :
    PowerSeries.mk (fun n ↦
        LinearMap.trace R (homogeneousSubmodule R M n) (homogeneousSubmoduleMapₛₗ f n)) *
      (f.charpoly.reverse : PowerSeries R) = 1 := by
  classical
  nontriviality R
  have : Fintype κ := have := Module.Finite.finite_basis b; Fintype.ofFinite κ
  have hrev : (f.charpoly.reverse : PowerSeries R) =
      ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) := by
    rw [b.reverse_charpoly_of_apply f a hf, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  have hmk : PowerSeries.mk (fun n ↦
      LinearMap.trace R (homogeneousSubmodule R M n) (homogeneousSubmoduleMapₛₗ f n)) =
      ∏ i, PowerSeries.mk fun n ↦ a i ^ n :=
    calc _ = PowerSeries.map (MvPolynomial.eval a)
          (PowerSeries.mk fun n ↦ MvPolynomial.hsymm κ R n) := by
          ext n
          simp [b.trace_homogeneousSubmoduleMapₛₗ_of_apply f a hf, TauCeti.eval_hsymm]
      _ = _ := by
          rw [TauCeti.mk_hsymm_eq_prod_mk_pow, map_prod]
          congr! 1 with i
          ext n
          simp
  rw [hmk, hrev, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ ↦ TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (a i)

end CommRing

end TauCeti.SymmetricAlgebra

namespace Module.End

open TauCeti.SymmetricAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The graded trace formula for a diagonalizable endomorphism** of a finite-dimensional vector
space, one whose eigenspaces span: `(∑ₙ tr(f | Symⁿ V) tⁿ) * det(1 - t f) = 1`. -/
theorem mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_iSup_eigenspace_eq_top
    (f : Module.End K V) (h : ⨆ μ, eigenspace f μ = ⊤) :
    PowerSeries.mk (fun n ↦
        LinearMap.trace K (homogeneousSubmodule K V n) (homogeneousSubmoduleMapₛₗ f n)) *
      (f.charpoly.reverse : PowerSeries K) = 1 := by
  classical
  -- An eigenbasis, collected from the decomposition of `V` into eigenspaces of `f`, following the
  -- construction in Mathlib's `Mathlib/Algebra/Lie/CartanCriterion.lean`.
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep h
  exact (hint.collectedBasis fun μ ↦ finBasis K (f.eigenspace μ))
    |>.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_apply f Sigma.fst
    fun i ↦ Module.End.mem_eigenspace_iff.mp (hint.collectedBasis_mem _ i)

/-- **The graded trace formula for a semisimple endomorphism** of a finite-dimensional vector
space over an algebraically closed field: `(∑ₙ tr(f | Symⁿ V) tⁿ) * det(1 - t f) = 1`. -/
theorem IsSemisimple.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly
    [IsAlgClosed K] {f : Module.End K V} (hf : f.IsSemisimple) :
    PowerSeries.mk (fun n ↦
        LinearMap.trace K (homogeneousSubmodule K V n) (homogeneousSubmoduleMapₛₗ f n)) *
      (f.charpoly.reverse : PowerSeries K) = 1 :=
  mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_iSup_eigenspace_eq_top f
    hf.iSup_eigenspace_eq_top

end Module.End
