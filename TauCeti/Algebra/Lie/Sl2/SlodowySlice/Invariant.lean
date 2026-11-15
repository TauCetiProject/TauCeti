/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.Sl2.SlodowySlice.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-!
# Invariant polynomial functions on the Slodowy slice

Let `(h, e, f)` be an `sl₂` triple in a finite-dimensional Lie algebra `L` over a field `K` of
characteristic zero. The adjoint quotient restricted to the Slodowy slice `S = e + ker (ad f)` is
the family of invariant polynomial functions `p ∈ S(L*)^L` restricted to `S`. This file shows that
these restrictions are graded for the contracting action `c • x = c ^ 2 • Ad (λ c⁻¹) x`
(`IsSl2Triple.contractingAction`):

* a polynomial function `p`, homogeneous of degree `d` and killed by the coadjoint action of `h`,
  satisfies `p (c • x) = c ^ (2 * d) * p x` for every unit `c` and every `x : L`
  (`IsSl2Triple.lift_eval_contractingAction_apply`);
* consequently, for a point `x = e + ∑ₙ vₙ` with `vₙ` of weight `-n` for `ad h`, such as a point
  of the slice (`IsSl2Triple.exists_contractingAction_eq`), the polynomial curve
  `c ↦ e + ∑ₙ c ^ (n + 2) • vₙ` satisfies `p (e + ∑ₙ c ^ (n + 2) • vₙ) = c ^ (2 * d) * p x` for
  *every* `c ∈ K`, including `c = 0`, where the curve passes through `e`
  (`IsSl2Triple.lift_eval_add_sum_pow_smul`).

Informally: the contracting action has the positive weights `n + 2` on the weight spaces of
`ker (ad f)`, and the second statement says that, along these weights, the restriction of a
homogeneous invariant of degree `d` to the slice has weighted degree `2 * d`. Taking `p` of
positive degree with `p x = 0`, the whole curve, including its limit `e`, stays in the zero locus
of `p`; so the contraction of the slice to `e` restricts to the zero fibre of the adjoint
quotient on the slice.

The key input is that a polynomial function killed by `h` is invariant under the grading
automorphisms `Ad (λ s)` (`TauCeti.SymmetricAlgebra.lift_eval_gradingAut_apply`), so only the
scalar factor `c ^ 2` of the contracting action moves its values.

## Main results

* `IsSl2Triple.lift_eval_contractingAction_apply`: invariant polynomial functions of degree `d`
  scale by `c ^ (2 * d)` under the contracting action.
* `IsSl2Triple.lift_eval_add_sum_pow_smul`: the same scaling along the polynomial contraction
  curves, for every scalar `c`.

## References

* P. Slodowy, *Simple Singularities and Simple Algebraic Groups*, Lecture Notes in Mathematics
  815, Springer, 1980, §7.4.
* W. L. Gan and V. Ginzburg, *Quantization of Slodowy slices*, Int. Math. Res. Not. 2002,
  no. 5, 243–255, §2.
-/

public section

open LieAlgebra LieModule Module _root_.SymmetricAlgebra TauCeti.SymmetricAlgebra

namespace IsSl2Triple

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {h e f : L}

/-- **Invariant polynomial functions are graded for the contracting action.** If `p ∈ S(L*)` is
homogeneous of degree `d` and killed by the coadjoint action of `h`, for instance a homogeneous
invariant polynomial function, then `p (c • x) = c ^ (2 * d) * p x` for the contracting action of
every unit `c` on every `x : L`. -/
theorem lift_eval_contractingAction_apply (t : IsSl2Triple h e f) {d : ℕ}
    {p : _root_.SymmetricAlgebra K (Dual K L)} (hp : p ∈ homogeneousSubmodule K (Dual K L) d)
    (hph : lieModuleDerivation K L (Dual K L) h p = 0) (c : Kˣ) (x : L) :
    lift (Dual.eval K L (t.contractingAction c x)) p =
      (c : K) ^ (2 * d) * lift (Dual.eval K L x) p := by
  rw [t.contractingAction_apply (ad_eq_toEnd K L ▸
    TauCeti.isInternal_eigenspace_toEnd_intCast (M := L) t),
    map_smul]
  refine (lift_smul_of_mem_homogeneousSubmodule (f := Dual.eval K L _) (hp := hp) ..).trans ?_
  rw [lift_eval_gradingAut_apply _ hph, smul_eq_mul, pow_mul]

/-- **Invariant polynomial functions along the contraction curves.** Let `x = e + ∑ₙ vₙ` with
`vₙ` in the eigenspace of `ad h` of weight `-n`; by `IsSl2Triple.exists_contractingAction_eq`
every point of the Slodowy slice has this form. If `p ∈ S(L*)` is homogeneous of degree `d` and
killed by the coadjoint action of `h`, then `p (e + ∑ₙ c ^ (n + 2) • vₙ) = c ^ (2 * d) * p x` for
every `c ∈ K`. For units `c` the left side is `p (c • x)` for the contracting action; at `c = 0` the
curve passes through `e`. -/
theorem lift_eval_add_sum_pow_smul (t : IsSl2Triple h e f) {v : ℕ →₀ L}
    (hv : ∀ n : ℕ, v n ∈ (ad K L h).eigenspace (-(n : K))) {d : ℕ}
    {p : _root_.SymmetricAlgebra K (Dual K L)} (hp : p ∈ homogeneousSubmodule K (Dual K L) d)
    (hph : lieModuleDerivation K L (Dual K L) h p = 0) (c : K) :
    lift (Dual.eval K L (e + v.sum fun n w ↦ c ^ (n + 2) • w)) p =
      c ^ (2 * d) * lift (Dual.eval K L (e + v.sum fun _ w ↦ w)) p := by
  classical
  set x := e + v.sum fun _ w ↦ w
  -- The polynomial curve in `L` whose value at `c` is `e + ∑ₙ c ^ (n + 2) • vₙ`, read through the
  -- linear functionals on `L`.
  let φ : Dual K L →ₗ[K] Polynomial K :=
    Polynomial.monomial 0 ∘ₗ Dual.eval K L e +
      ∑ n ∈ v.support, Polynomial.monomial (n + 2) ∘ₗ Dual.eval K L (v n)
  have hφ (c : K) : (Polynomial.aeval c).comp (lift φ) =
      lift (Dual.eval K L (e + v.sum fun n w ↦ c ^ (n + 2) • w)) := by
    refine algHom_ext (LinearMap.ext fun ψ ↦ ?_)
    simp [φ, Finsupp.sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]
  -- For units `c` the curve is the contracting action, so the two polynomials agree at every
  -- nonzero scalar, hence everywhere.
  have hunit (c : Kˣ) :
      (e + v.sum fun n w ↦ (c : K) ^ (n + 2) • w) = t.contractingAction c x := by
    simp only [x, map_add, contractingAction_apply_e, Finsupp.sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [t.contractingAction_apply_of_mem c (j := -n) (by simpa using hv n), sub_neg_eq_add,
      add_comm]
    norm_cast
  have hpoly : lift φ p = Polynomial.C (lift (Dual.eval K L x) p) * Polynomial.X ^ (2 * d) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton 0).infinite_compl.mono
      fun c hc ↦ ?_)
    have hc : c ≠ 0 := Set.mem_compl_singleton_iff.1 hc
    have h := congr($(hφ c) p)
    rw [AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval] at h
    rw [Set.mem_ofPred_eq, h, ← Units.val_mk0 hc, hunit, t.lift_eval_contractingAction_apply hp hph,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have h := congr($(hφ c) p)
  rw [AlgHom.comp_apply, hpoly, Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [← h, mul_comm]

end IsSl2Triple
