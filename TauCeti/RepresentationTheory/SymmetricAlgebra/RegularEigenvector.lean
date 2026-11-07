/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Charpoly.Dual
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.RegularEigenvector
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# Invariant degrees and regular eigenvectors

Let `g` act on `V` with eigenvector `v` and unit eigenvalue `c`. If homogeneous invariant
polynomial functions `f i` have nonzero Jacobian at `v`, then the characteristic polynomial
of `g` is `∏ᵢ (X - c⁻¹ ^ (d i - 1))`, where `d i` are their degrees. Thus the degree list
computes all eigenvalues, with multiplicity, not merely a set of possible eigenvalues.

The polynomial functions are `Sym(V*)` with the contragredient action. The inverse in the
formula is essential: choosing a regular eigenvector of eigenvalue `ζ⁻¹` gives the familiar
eigenvalues `ζ ^ (d i - 1)`. No finite-group, reflection-generation, or characteristic-zero
hypothesis is needed for this differential calculation, which works over any domain on a
finite free module. Existence of the eigenvector and nonvanishing of the Jacobian at it are
separate geometric questions.

## References

* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974),
  159–198, §4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.17.
-/

public section

namespace Representation

open SymmetricAlgebra TauCeti.SymmetricAlgebra Polynomial

variable {K G V n : Type*} [CommRing K] [IsDomain K] [Group G] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] [Fintype n] [DecidableEq n]

/-- At an eigenvector where a homogeneous invariant system has nonzero Jacobian, its degrees
minus one give the eigenvalues with multiplicity, as inverse powers of the eigenvalue of the
point. The invariants need not be assumed to generate the invariant algebra. -/
theorem charpoly_eq_prod_of_eigenvector_of_jacobian_ne_zero
    (ρ : Representation K G V) (b : Module.Basis n K (Module.Dual K V))
    {f : n → SymmetricAlgebra K (Module.Dual K V)} (d : n → ℕ)
    (hf : ∀ i, f i ∈ homogeneousSubmodule K (Module.Dual K V) (d i))
    (hinv : ∀ i, f i ∈ ρ.dual.symmetricAlgebraInvariants)
    (g : G) (v : V) (c : Kˣ) (hv : ρ g v = (c : K) • v)
    (hJ : lift (Module.Dual.eval K V v) (jacobian b f) ≠ 0) :
    (ρ g).charpoly = ∏ i, (X - C ((↑(c⁻¹) : K) ^ (d i - 1))) := by
  have hfixed (i : n) : SymmetricAlgebra.map K (ρ g).dualMap (f i) = f i := by
    simpa only [symmetricAlgebra_apply, dual_apply, inv_inv, LinearMap.dualMap_def] using
      (ρ.dual.mem_symmetricAlgebraInvariants _).1 (hinv i) g⁻¹
  have heigen : Module.Dual.eval K V v ∘ₗ (ρ g).dualMap =
      (c : K) • Module.Dual.eval K V v := by
    ext φ
    simp [hv]
  simpa only [LinearMap.charpoly_dualMap] using
    (ρ g).dualMap.charpoly_eq_prod_of_map_eq_self_of_jacobian_ne_zero
      b d hf hfixed (Module.Dual.eval K V v) c heigen hJ

end Representation
