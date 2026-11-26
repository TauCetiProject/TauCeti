/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis

/-!
# The characteristic polynomial of an isometry of a symplectic form

Let `B` be a nondegenerate alternating bilinear form on a vector space `V` of finite dimension
`2 g` over a field, and let `f` be an isometry of `B`, `B (f x) (f y) = B x y`. In a symplectic
basis of `B` (`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`) the matrix of `f` is
symplectic (`TauCeti.BilinForm.IsIsometry.toMatrix_mem_symplecticGroup`), so the identities of
`TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic` for the reversed characteristic polynomial
`p (t) = det (1 - t f)` hold basis-free:

* `p` is the characteristic polynomial `det (t - f)`
  (`TauCeti.BilinForm.IsIsometry.reverse_charpoly_eq_charpoly`), hence self-reciprocal,
  `t ^ (2 g) p (1 / t) = p (t)` (`TauCeti.BilinForm.IsIsometry.reflect_reverse_charpoly`);
* `p' (1) = g det (1 - f)` (`TauCeti.BilinForm.IsIsometry.derivative_eval_one_reverse_charpoly`);
* the coefficient of `t ^ a` in `p (t) / (1 - t) ^ 2` is `det (1 - f) (a + 1 - g)` for every
  `a ≥ 2 g - 1` (`TauCeti.BilinForm.IsIsometry.coeff_coe_reverse_charpoly_mul_mk_one_sq`).

The action on the first cohomology of a closed oriented surface of a self-map of degree one is an
isometry of the cup pairing, and `p (t) / (1 - t) ^ 2` is then its Lefschetz zeta function; these
identities compute its coefficients.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III (symplectic groups).
-/

public section

open Module Polynomial

namespace TauCeti.BilinForm.IsIsometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {f : V →ₗ[K] V}

/-- In a symplectic basis of a nondegenerate alternating form, indexed by `Fin m ⊕ Fin m` with
`dim V = 2 m`, the matrix of an isometry is symplectic. -/
private theorem exists_toMatrix_mem_symplecticGroup (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hf : IsIsometry B f) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V), finrank K V = 2 * m ∧
      LinearMap.toMatrix b b f ∈ Matrix.symplecticGroup (Fin m) K := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  exact ⟨m, b, by rw [finrank_eq_two_mul_card_of_basis_sum b, Fintype.card_fin],
    hf.toMatrix_mem_symplecticGroup b hb⟩

/-- **The reversed characteristic polynomial of a symplectic isometry is its characteristic
polynomial**: for an isometry `f` of a nondegenerate alternating form on a finite-dimensional
space, `det (1 - t f) = det (t - f)`. -/
theorem reverse_charpoly_eq_charpoly (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hf : IsIsometry B f) : f.charpoly.reverse = f.charpoly := by
  obtain ⟨m, b, -, hA⟩ := hf.exists_toMatrix_mem_symplecticGroup hB hnd
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.reverse_charpoly,
    SymplecticGroup.charpolyRev_eq_charpoly hA]

/-- **Self-reciprocity**: for an isometry `f` of a nondegenerate alternating form on a space of
dimension `d`, the polynomial `p (t) = det (1 - t f)` satisfies `t ^ d p (1 / t) = p (t)`. -/
theorem reflect_reverse_charpoly (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hf : IsIsometry B f) : f.charpoly.reverse.reflect (finrank K V) = f.charpoly.reverse := by
  obtain ⟨m, b, hm, hA⟩ := hf.exists_toMatrix_mem_symplecticGroup hB hnd
  rw [hm, ← LinearMap.charpoly_toMatrix f b, Matrix.reverse_charpoly]
  simpa using SymplecticGroup.reflect_charpolyRev hA

/-- **Reciprocal-polynomial identity**: for an isometry `f` of a nondegenerate alternating form on
a space of dimension `2 g`, the polynomial `p (t) = det (1 - t f)` satisfies
`p' (1) = g det (1 - f)`. -/
theorem derivative_eval_one_reverse_charpoly (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hf : IsIsometry B f) :
    f.charpoly.reverse.derivative.eval 1 = ((finrank K V / 2 : ℕ) : K) * LinearMap.det (1 - f) := by
  obtain ⟨m, b, hm, hA⟩ := hf.exists_toMatrix_mem_symplecticGroup hB hnd
  rw [hm, Nat.mul_div_cancel_left m two_pos, ← LinearMap.charpoly_toMatrix f b,
    Matrix.reverse_charpoly, SymplecticGroup.derivative_eval_one_charpolyRev hA, Fintype.card_fin,
    ← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]

/-- **Coarse coefficients**: for an isometry `f` of a nondegenerate alternating form on a space of
dimension `2 g`, the coefficient of `t ^ a` in `det (1 - t f) / (1 - t) ^ 2` is
`det (1 - f) (a + 1 - g)` for every `a ≥ 2 g - 1`. -/
theorem coeff_coe_reverse_charpoly_mul_mk_one_sq (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hf : IsIsometry B f) {a : ℕ} (ha : finrank K V ≤ a + 1) :
    PowerSeries.coeff a ((f.charpoly.reverse : PowerSeries K) * PowerSeries.mk 1 ^ 2) =
      LinearMap.det (1 - f) * ((a : K) + 1 - ((finrank K V / 2 : ℕ) : K)) := by
  obtain ⟨m, b, hm, hA⟩ := hf.exists_toMatrix_mem_symplecticGroup hB hnd
  rw [hm, Nat.mul_div_cancel_left m two_pos, ← LinearMap.charpoly_toMatrix f b,
    Matrix.reverse_charpoly, ← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]
  rw [hm, ← Fintype.card_fin m] at ha
  simpa using SymplecticGroup.coeff_coe_charpolyRev_mul_mk_one_sq hA ha

end TauCeti.BilinForm.IsIsometry
