/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SymmetricAlgebra.RegularEigenvector
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Exponents
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Coprime invariant exponents from a rational characteristic polynomial

Let `g` in a linear representation have a nonzero eigenvector `v` with primitive `h`-th
root eigenvalue `c`. Suppose homogeneous invariant polynomial functions `f i` have nonzero
Jacobian at `v`. Their degrees determine the characteristic polynomial through the
regular-eigenvector calculation. If that characteristic polynomial is defined over `ℚ`,
cyclotomic conjugacy forces every residue coprime to `h` to occur among the invariant
exponents `d i - 1`, provided these exponents lie in `[0, h)`.

This isolates the arithmetic implication needed for crystallographic reflection
representations. Rationality can be supplied by an integral matrix for the same operator.
The statement does not construct a regular eigenvector, bound the invariant degrees, or
identify the order of a Coxeter element. Those are separate geometric inputs. Without
rationality the implication is false for general finite real reflection groups.

The coefficient ring can be any domain that is a rational algebra, and the representation
is finite free. The invariant system need not generate the invariant algebra; nonvanishing
of its Jacobian is the hypothesis used by the differential calculation.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.17.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974),
  159–198, §4.
-/

public section

open Polynomial SymmetricAlgebra TauCeti.SymmetricAlgebra

namespace Representation

variable {K G V n : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K] [Group G]
  [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
  [Fintype n] [DecidableEq n]

/-- At a nonzero primitive-root eigenvector where a homogeneous invariant system has nonzero
Jacobian, a rational characteristic polynomial forces every coprime residue to occur among
the invariant degrees minus one, if all these exponents are less than the root order. -/
theorem exists_degree_sub_one_eq_of_eigenvector_of_jacobian_ne_zero
    (ρ : Representation K G V) (b : Module.Basis n K (Module.Dual K V))
    {f : n → SymmetricAlgebra K (Module.Dual K V)} (d : n → ℕ)
    (hf : ∀ i, f i ∈ homogeneousSubmodule K (Module.Dual K V) (d i))
    (hinv : ∀ i, f i ∈ ρ.dual.symmetricAlgebraInvariants)
    (g : G) (v : V) (c : Kˣ) {h : ℕ}
    (hc : IsPrimitiveRoot (c : K) h) (hv : ρ g v = (c : K) • v) (hv0 : v ≠ 0)
    (hJ : lift (Module.Dual.eval K V v) (jacobian b f) ≠ 0)
    (hd : ∀ i, d i - 1 < h) {p : ℚ[X]}
    (hp : p.map (algebraMap ℚ K) = (ρ g).charpoly)
    {a : ℕ} (ha : a < h) (hcop : a.Coprime h) : ∃ i, d i - 1 = a := by
  have heigen : Module.End.HasEigenvector (ρ g) (c : K) v :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  have hroot : (p.map (algebraMap ℚ K)).IsRoot (c : K) := by
    rw [hp, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector heigen
  have hprod := ρ.charpoly_eq_prod_of_eigenvector_of_jacobian_ne_zero b d hf hinv g v c hv hJ
  have hcinv : IsPrimitiveRoot (↑(c⁻¹) : K) h :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.coe_units_iff.mp hc).inv
  exact IsPrimitiveRoot.exists_eq_of_isRoot_of_map_eq_prod hcinv hc hroot hd
    (hp.trans hprod) ha hcop

end Representation
