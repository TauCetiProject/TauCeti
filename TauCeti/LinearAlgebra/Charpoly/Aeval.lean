/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.Polynomial.Tower
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots

/-!
# Characteristic roots of a polynomial in an endomorphism

Let `f` be an endomorphism of a finite free module `M` over a commutative ring `R`, and let `p`
be a polynomial over `R`. If the characteristic polynomial of `f` splits over a domain `S`, so
that `f` has characteristic roots `α₁, …, α_d` in `S`, counted with algebraic multiplicity, then
the characteristic roots of `p(f)` in `S` are `p(α₁), …, p(α_d)`, again with multiplicity. In
particular the characteristic roots of `f ^ r` are the `α_i ^ r`. This is the basis-free form of
the spectral mapping theorem `Matrix.charpoly_aeval_eq_prod_roots_charpoly_of_splits`, with the
roots read in an arbitrary domain over `R`, such as an algebraic closure of a field of
coefficients.

The splitting hypothesis cannot be dropped: a rotation by a quarter turn of `ℚ²` has no rational
characteristic roots, while its square `-1` has the double root `-1`.

These are the statements used to read the eigenvalues of a power `F ^ r` of a Frobenius
endomorphism, the geometric Frobenius over an extension of degree `r` of a finite field, from
those of `F`.

## Main results

* `LinearMap.map_charpoly_aeval_eq_prod_aroots`: over `S`, the characteristic polynomial of `p(f)`
  is `∏ (X - p(α))` over the characteristic roots `α` of `f` in `S`.
* `LinearMap.aroots_charpoly_aeval`: the characteristic roots of `p(f)` in `S` are the `p(α)`.
* `LinearMap.aroots_charpoly_pow`: the characteristic roots of `f ^ r` in `S` are the `α ^ r`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (1.5.1).
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M S : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [CommRing S] [IsDomain S] [Algebra R S]

/-- **Spectral mapping for characteristic polynomials.** If the characteristic polynomial of an
endomorphism `f` of a finite free module splits over a domain `S`, then over `S` the
characteristic polynomial of `p(f)` is `∏ (X - p(α))` over the characteristic roots `α` of `f` in
`S`, counted with algebraic multiplicity. -/
theorem map_charpoly_aeval_eq_prod_aroots (f : Module.End R M)
    (hf : (f.charpoly.map (algebraMap R S)).Splits) (p : R[X]) :
    (aeval f p).charpoly.map (algebraMap R S) =
      ((f.charpoly.aroots S).map fun α ↦ X - C (aeval α p)).prod := by
  let b := Module.Free.chooseBasis R M
  -- In the basis `b`, `p(f)` becomes `p(A)` for the matrix `A` of `f`, and its image over `S`
  -- is `p(A_S)` for the image `A_S` of `A`, to which the matrix spectral mapping theorem applies.
  have hb (g : Module.End R M) : toMatrixAlgEquiv b g = toMatrix b b g := by
    ext i j
    rw [toMatrixAlgEquiv_apply, toMatrix_apply]
  have hfA :
      f.charpoly.map (algebraMap R S) = ((toMatrix b b f).map (algebraMap R S)).charpoly := by
    rw [Matrix.charpoly_map, charpoly_toMatrix]
  have hpA : (toMatrix b b (aeval f p)).map (algebraMap R S) =
      aeval ((toMatrix b b f).map (algebraMap R S)) (p.map (algebraMap R S)) := by
    rw [aeval_map_algebraMap, ← hb, ← hb, ← aeval_algHom_apply]
    have h := aeval_algHom_apply (Algebra.ofId R S).mapMatrix (toMatrixAlgEquiv b f) p
    rwa [AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, _root_.funext (Algebra.ofId_apply S),
      eq_comm] at h
  rw [← charpoly_toMatrix (aeval f p) b, ← Matrix.charpoly_map, hpA,
    Matrix.charpoly_aeval_eq_prod_roots_charpoly_of_splits (hfA ▸ hf), ← hfA]
  simp [aroots, eval_map_algebraMap]

/-- **Spectral mapping for characteristic roots.** If the characteristic polynomial of an
endomorphism `f` of a finite free module splits over a domain `S`, then the characteristic roots
of `p(f)` in `S` are the values `p(α)` at the characteristic roots `α` of `f` in `S`, counted with
algebraic multiplicity. -/
theorem aroots_charpoly_aeval (f : Module.End R M) (hf : (f.charpoly.map (algebraMap R S)).Splits)
    (p : R[X]) :
    (aeval f p).charpoly.aroots S = (f.charpoly.aroots S).map fun α ↦ aeval α p := by
  rw [aroots, map_charpoly_aeval_eq_prod_aroots f hf]
  simpa [Multiset.map_map, Function.comp_def] using
    roots_multiset_prod_X_sub_C ((f.charpoly.aroots S).map fun α ↦ aeval α p)

/-- If the characteristic polynomial of an endomorphism `f` of a finite free module splits over a
domain `S`, then the characteristic roots of `f ^ r` in `S` are the `r`-th powers of those of `f`,
counted with algebraic multiplicity. -/
theorem aroots_charpoly_pow (f : Module.End R M) (hf : (f.charpoly.map (algebraMap R S)).Splits)
    (r : ℕ) : (f ^ r).charpoly.aroots S = (f.charpoly.aroots S).map (· ^ r) := by
  simpa using aroots_charpoly_aeval f hf (X ^ r)

end LinearMap
