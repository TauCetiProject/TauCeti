/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.TaylorExp
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Polynomial flows of locally nilpotent derivations

Evaluating the Taylor expansion of a locally nilpotent derivation at a scalar gives an
algebra endomorphism. These endomorphisms satisfy the additive parameter law, and hence
are automorphisms, with inverse given by the negative parameter. No uniform nilpotence
bound on the coordinate ring is required.

For invariant vector fields on affine groups this is the coordinate-ring flow used to
construct algebraic one-parameter subgroups.

## References

* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Chapter 1.

The polynomial expansion is `Derivation.taylorExpPolynomial`; the parameter law uses
Mathlib's `IsNilpotent.exp_add_of_commute` on the kernel of a sufficiently high iterate.
-/

public section

namespace Derivation

open Polynomial Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra ℚ A]
variable (D : Derivation R A A) (hD : ∀ a, ∃ n, D^[n] a = 0)

/-- The polynomial flow at parameter `r` of a locally nilpotent derivation. -/
noncomputable def taylorExpAt (r : R) : A →ₐ[R] A :=
  ((aeval (algebraMap R A r)).restrictScalars R).comp (D.taylorExpPolynomial hD)

/-- The flow is obtained by evaluating the Taylor polynomial at the parameter. -/
theorem taylorExpAt_apply (r : R) (a : A) :
    D.taylorExpAt hD r a = aeval (algebraMap R A r) (D.taylorExpPolynomial hD a) :=
  (rfl)

/-- Any iterate killing an element gives a finite formula for its polynomial flow. -/
theorem taylorExpAt_apply_eq_sum (r : R) {a : A} {n : ℕ} (hn : D^[n] a = 0) :
    D.taylorExpAt hD r a = ∑ i ∈ range n, (i.factorial : ℚ)⁻¹ • (r ^ i • D^[i] a) := by
  rw [taylorExpAt_apply, aeval_taylorExpPolynomial_eq_sum D hD _ hn]
  simp [Algebra.smul_def, mul_comm, mul_assoc]

/-- At zero the polynomial flow is the identity. -/
@[simp]
theorem taylorExpAt_zero : D.taylorExpAt hD 0 = AlgHom.id R A := by
  ext a
  simp [taylorExpAt_apply, ← Polynomial.coeff_zero_eq_eval_zero]

/-- At one the polynomial flow is the Taylor exponential. -/
@[simp]
theorem taylorExpAt_one : D.taylorExpAt hD 1 = D.taylorExp hD := by
  ext a
  simp [taylorExpAt_apply]

private theorem taylorExpAt_eq_exp_restrict (r : R) {n : ℕ}
    (K : Submodule ℚ A)
    (hstable : ∀ a ∈ K, (r • D).toLinearMap.toAddMonoidHom.toRatLinearMap a ∈ K)
    (hnil : (((r • D).toLinearMap.toAddMonoidHom.toRatLinearMap).restrict hstable) ^ n = 0)
    (a : K) (ha : D^[n] a = 0) :
    D.taylorExpAt hD r a =
      ((IsNilpotent.exp
        (((r • D).toLinearMap.toAddMonoidHom.toRatLinearMap).restrict hstable)) a : A) := by
  rw [taylorExpAt_apply_eq_sum D hD r ha, IsNilpotent.exp_eq_sum hnil,
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  apply sum_congr rfl
  intro i _
  rw [Module.End.pow_restrict, LinearMap.restrict_apply]
  simp only [Module.End.pow_apply, AddMonoidHom.coe_toRatLinearMap,
    LinearMap.toAddMonoidHom_coe, coeFn_coe, iterate_smul_apply]

/-- Flowing for `s` and then for `r` is flowing for `r + s`. -/
theorem taylorExpAt_add (r s : R) :
    D.taylorExpAt hD (r + s) = (D.taylorExpAt hD r).comp (D.taylorExpAt hD s) := by
  -- Rational linearity follows from additivity. Restrict to the rational kernel of an
  -- iterate killing the input, so Mathlib's nilpotent exponential applies for any base ring.
  ext a
  obtain ⟨n, hn⟩ := hD a
  let f := D.toLinearMap.toAddMonoidHom.toRatLinearMap
  let K := LinearMap.ker (f ^ n)
  have hmem (x : A) : x ∈ K ↔ D^[n] x = 0 := by
    simp only [K, LinearMap.mem_ker, Module.End.pow_apply, f,
      AddMonoidHom.coe_toRatLinearMap, LinearMap.toAddMonoidHom_coe, coeFn_coe]
  have hstable (t : R) : ∀ x ∈ K, (t • D) x ∈ K := by
    intro x hx
    rw [hmem] at hx ⊢
    rw [smul_apply, ← coeFn_coe, ← Module.End.pow_apply, LinearMap.map_smul,
      Module.End.pow_apply, coeFn_coe, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply', hx, map_zero, smul_zero]
  let g (t : R) : Module.End ℚ K :=
    ((t • D).toLinearMap.toAddMonoidHom.toRatLinearMap).restrict (hstable t)
  have hg_apply (t : R) :
      Function.Semiconj (fun y : K => (y : A)) (g t) (t • D) := fun _ => rfl
  have hpow (t : R) (i : ℕ) (y : K) : ((g t ^ i) y : A) = (t • D)^[i] y := by
    simpa only [Module.End.pow_apply, coe_smul] using (hg_apply t).iterate_right i y
  have hnil (t : R) : g t ^ n = 0 := by
    ext x
    simp only [hpow, iterate_smul_apply, (hmem x).mp x.property, smul_zero,
      LinearMap.zero_apply, ZeroMemClass.coe_zero]
  let x : K := ⟨a, (hmem a).mpr hn⟩
  have heq (t : R) (y : K) :
      D.taylorExpAt hD t y = ((IsNilpotent.exp (g t)) y : A) :=
    taylorExpAt_eq_exp_restrict D hD t K (hstable t) (hnil t) y ((hmem y).mp y.property)
  have hc : Commute (g r) (g s) := by
    ext y
    simp [Module.End.mul_apply, g, smul_smul, mul_comm]
  have hg : g (r + s) = g r + g s := by
    ext y
    simp [g, add_smul]
  have h := IsNilpotent.exp_add_of_commute (A := Module.End ℚ K) hc ⟨n, hnil r⟩ ⟨n, hnil s⟩
  rw [← hg] at h
  have hv := congrArg (fun k : Module.End ℚ K => (k x : A)) h
  simpa only [Module.End.mul_apply, ← heq, AlgHom.comp_apply] using hv

/-- Evaluating the polynomial flow at `r` is the Taylor exponential of `r • D`. -/
theorem taylorExpAt_eq_taylorExp_smul (r : R) :
    D.taylorExpAt hD r = (r • D).taylorExp (D.exists_iterate_smul_eq_zero hD r) := by
  ext a
  obtain ⟨n, hn⟩ := hD a
  rw [taylorExpAt_apply_eq_sum D hD r hn,
    taylorExp_apply_eq_sum _ _ (n := n) (by rw [iterate_smul_apply, hn, smul_zero])]
  simp only [iterate_smul_apply]

/-- The flow at any parameter is an algebra automorphism; the inverse is the flow at
its negative. -/
noncomputable def taylorExpAtEquiv (r : R) : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (D.taylorExpAt hD r) (D.taylorExpAt hD (-r))
    (by rw [← taylorExpAt_add, add_neg_cancel, taylorExpAt_zero])
    (by rw [← taylorExpAt_add, neg_add_cancel, taylorExpAt_zero])

/-- The flow automorphism applies by evaluating the Taylor polynomial. -/
@[simp]
theorem taylorExpAtEquiv_apply (r : R) (a : A) :
    D.taylorExpAtEquiv hD r a = D.taylorExpAt hD r a := (rfl)

/-- The inverse flow automorphism applies with the negative parameter. -/
@[simp]
theorem taylorExpAtEquiv_symm_apply (r : R) (a : A) :
    (D.taylorExpAtEquiv hD r).symm a = D.taylorExpAt hD (-r) a := (rfl)

end Derivation
