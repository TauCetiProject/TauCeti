/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Partial derivatives in a symmetric algebra

A linear form `φ` on a module `M` over a commutative semiring `R` extends uniquely to a derivation
`SymmetricAlgebra.pderiv φ` of the symmetric algebra `Sym M`, sending each generator `ι m` to
the scalar `φ m`. For the polynomial functions `Sym(V*)` on a vector space `V`, the derivative
along the evaluation at `v ∈ V` is the directional derivative along `v`. In the coordinates of a
basis `b` of `M`, the derivative along the coordinate form `b.coord j` is Mathlib's partial
derivative `MvPolynomial.pderiv j` (`SymmetricAlgebra.equivMvPolynomial_pderiv_coord`).

## Main definitions

* `SymmetricAlgebra.pderiv`: the derivative of `Sym M` along a linear form on `M`.

## Main results

* `SymmetricAlgebra.pderiv_map`: the chain rule for the derivatives along linear forms.
* `SymmetricAlgebra.pderiv_mem_homogeneousSubmodule`: a derivative lowers degrees by one.
* `SymmetricAlgebra.lift_pderiv_comp_of_map_eq_self`: the scaled chain rule for a homogeneous
  fixed polynomial evaluated at an eigenpoint.
* `SymmetricAlgebra.pderiv_eq_sum`: a derivative along a linear form expands along the
  derivatives along the coordinate forms of a finite basis.
* `SymmetricAlgebra.equivMvPolynomial_pderiv_coord`: in coordinates, the derivatives along the
  coordinate forms are the partial derivatives of polynomials.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  Chapter 3 (partial derivatives of polynomial functions).
-/

public section

open TauCeti.SymmetricAlgebra

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The derivative of `Sym M` along a linear form `φ` on `M`: the derivation sending each
generator `ι m` to the scalar `φ m`. In the coordinates of a basis `b` of `M`, the derivative
along the coordinate form `b.coord j` is the partial derivative in the variable `b j`. -/
noncomputable def pderiv :
    Module.Dual R M →ₗ[R] Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  mkDerivation ∘ₗ LinearMap.llcomp R M R _ (Algebra.linearMap R (SymmetricAlgebra R M))

/-- The derivative along `φ` sends the generator `ι m` to the scalar `φ m`. -/
@[simp]
theorem pderiv_ι (φ : Module.Dual R M) (m : M) :
    pderiv φ (ι R M m) = algebraMap R (SymmetricAlgebra R M) (φ m) := by
  simp [pderiv]

/-- **The chain rule.** Differentiating the image of `p` under the map induced by `g : M → N`
along `φ` is the image of the derivative of `p` along `φ ∘ g`. -/
theorem pderiv_map {N : Type*} [AddCommMonoid N] [Module R N] (g : M →ₗ[R] N)
    (φ : Module.Dual R N) (p : SymmetricAlgebra R M) :
    pderiv φ (map R g p) = map R g (pderiv (φ ∘ₗ g) p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | mul a b ha hb => simp [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- A derivative along a linear form lowers degrees by one: it sends the degree-`n` part of
`Sym M` to the degree-`(n - 1)` part. -/
theorem pderiv_mem_homogeneousSubmodule (φ : Module.Dual R M) {n : ℕ}
    {p : SymmetricAlgebra R M} (hp : p ∈ homogeneousSubmodule R M n) :
    pderiv φ p ∈ homogeneousSubmodule R M (n - 1) := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨y, rfl⟩ := hm
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_ι, mul_comm x,
      ← Algebra.smul_def]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hx)
    cases i with
    | zero =>
      obtain ⟨r, rfl⟩ : ∃ r, algebraMap R _ r = x :=
        ⟨_, algebraMap_homogeneousSubmoduleZeroEquiv_apply R M ⟨x, hx⟩⟩
      simp
    | succ j => simpa [add_comm] using SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule R M y) ih

/-- The differential of a homogeneous fixed polynomial at an eigenpoint satisfies the
scaled chain rule. No nonzero-Jacobian or invertibility hypothesis is needed here. -/
theorem lift_pderiv_comp_of_map_eq_self (p : SymmetricAlgebra R M)
    {d : ℕ} (hp : p ∈ homogeneousSubmodule R M d) {g : M →ₗ[R] M}
    (hg : map R g p = p) (x : Module.Dual R M) {c : R}
    (hx : x ∘ₗ g = c • x) (φ : Module.Dual R M) :
    lift x (pderiv φ p) = c ^ (d - 1) * lift x (pderiv (φ ∘ₗ g) p) := by
  have heval : (lift x).comp (map R g) = lift (c • x) := by
    ext m
    simpa using DFunLike.congr_fun hx m
  calc
    lift x (pderiv φ p) = lift x (map R g (pderiv (φ ∘ₗ g) p)) := by
      rw [← pderiv_map, hg]
    _ = lift (c • x) (pderiv (φ ∘ₗ g) p) := DFunLike.congr_fun heval _
    _ = _ := lift_smul_of_mem_homogeneousSubmodule R M x c
      (pderiv_mem_homogeneousSubmodule _ hp)

/-- A derivative along a linear form `φ` expands along the derivatives along the coordinate forms
of a finite basis `b`, with coefficients the values `φ (b j)`. -/
theorem pderiv_eq_sum {n : Type*} [Fintype n] (b : Module.Basis n R M) (φ : Module.Dual R M)
    (p : SymmetricAlgebra R M) :
    pderiv φ p = ∑ j, algebraMap R _ (φ (b j)) * pderiv (b.coord j) p := by
  conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]
  simp [-Module.Basis.sum_dual_apply_smul_coord, Algebra.smul_def]

/-- In the coordinates of a basis `b`, the derivative along the coordinate form `b.coord i` is
Mathlib's partial derivative `MvPolynomial.pderiv i` in the variable `i`. -/
theorem equivMvPolynomial_pderiv_coord {n : Type*} (b : Module.Basis n R M)
    (i : n) (p : SymmetricAlgebra R M) :
    equivMvPolynomial b (pderiv (b.coord i) p) = MvPolynomial.pderiv i (equivMvPolynomial b p) := by
  classical
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x =>
    -- Both sides are the constant polynomial with value the `i`-th coordinate of `x`.
    simp [Module.Basis.constr_apply, map_finsuppSum, Pi.single_apply, MvPolynomial.smul_eq_C_mul,
      Finsupp.sum_ite_eq']
  | mul a c ha hc => simp [Derivation.leibniz, ha, hc]
  | add a c ha hc => simp [ha, hc]


end SymmetricAlgebra
