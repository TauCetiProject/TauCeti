/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.Analysis.Calculus.DSlope.Iterate
public import TauCeti.Analysis.Meromorphic.Germ

/-!
# Finite principal parts of meromorphic functions

Let `𝕜` be a nontrivially normed field and `a : 𝕜`. A function meromorphic at `a` has a pole of
finite order there: near `a`, but off `a`, it is `(z - a)⁻ⁿ h z` for some `n` and some `h`
analytic at `a`. Splitting the convergent Taylor expansion of `h` at `a` as
`h z = ∑ j < n, c j (z - a) ^ j + (z - a) ^ n q z`, with `q` analytic at `a`, gives
`(z - a)⁻ⁿ h z = P((z - a)⁻¹) + q z` for the polynomial `P = ∑ j < n, c j X ^ (n - j)` without
constant term: a finite principal part plus a function analytic at `a`.

The principal part is unique: a polynomial `P` without constant term for which
`z ↦ P((z - a)⁻¹)` has a limit at `a` along the punctured neighbourhoods is zero, because a
polynomial of positive degree tends to infinity at infinity.

The functions `z ↦ P((z - a)⁻¹)` are meromorphic at `a`, and their punctured germs form the image
of the ring homomorphism `TauCeti.meromorphicGerms.evalInvSub a`. The splitting of a meromorphic
germ into its principal part and a holomorphic germ is assembled in
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.PrincipalPart`.

## Main results

* `MeromorphicAt.eval_polynomial`: a polynomial in a meromorphic function is meromorphic.
* `HasFPowerSeriesAt.inv_pow_mul_eq_eval_inv_sub_add`: the Taylor splitting of
  `(z - a)⁻ⁿ h z` into a principal part and an analytic remainder.
* `MeromorphicAt.exists_eventuallyEq_eval_inv_sub_add`: every function meromorphic at `a` is,
  near `a`, a finite principal part plus a function analytic at `a`.
* `Polynomial.eq_zero_of_tendsto_eval_inv_sub`: uniqueness of the principal part.
* `TauCeti.meromorphicGerms.evalInvSub`: the ring homomorphism `P ↦ P((z - a)⁻¹)` to
  meromorphic germs.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 4, §3.1.
-/

public section

open Filter Function Polynomial Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-- A polynomial in a function meromorphic at `x` is meromorphic at `x`. -/
theorem MeromorphicAt.eval_polynomial {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) (P : 𝕜'[X]) :
    MeromorphicAt (fun z ↦ P.eval (f z)) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    fun_prop
  | monomial n c =>
    simp only [eval_monomial]
    fun_prop

/-- The polynomial `∑ j < n, c j X ^ (n - j)` has no constant term. -/
theorem TauCeti.coeff_zero_sum_range_monomial_sub {R : Type*} [Semiring R] (n : ℕ)
    (c : ℕ → R) : (∑ j ∈ Finset.range n, monomial (n - j) (c j)).coeff 0 = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have := Finset.mem_range.1 hj
  rw [coeff_monomial, ite_eq_right_iff]
  omega

/-- **Taylor splitting of a pole.** If `h` has the power series `p` at `a`, then off `a`,
`(z - a)⁻ⁿ h z` is the finite principal part `∑ j < n, p.coeff j (z - a)⁻⁽ⁿ⁻ʲ⁾` plus the
`n`-th iterated divided slope of `h` at `a`, which is analytic at `a`. -/
theorem HasFPowerSeriesAt.inv_pow_mul_eq_eval_inv_sub_add {h : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} (hp : HasFPowerSeriesAt h p a) (n : ℕ) {z : 𝕜}
    (hz : z ≠ a) :
    ((z - a) ^ n)⁻¹ * h z =
      (∑ j ∈ Finset.range n, monomial (n - j) (p.coeff j)).eval (z - a)⁻¹ +
        (swap dslope a)^[n] h z := by
  have hza : z - a ≠ 0 := sub_ne_zero.2 hz
  conv_lhs => rw [← TauCeti.sum_range_pow_smul_iterate_dslope_add h a z n]
  rw [mul_add, Finset.mul_sum, eval_finsetSum, smul_eq_mul,
    inv_mul_cancel_left₀ (pow_ne_zero n hza)]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eval_monomial, hp.iterate_dslope_eq_coeff, smul_eq_mul, inv_pow,
    ← Nat.sub_add_cancel (Finset.mem_range.1 hj).le, pow_add, Nat.add_sub_cancel]
  field_simp

/-- Every function meromorphic at `a` is, on a punctured neighbourhood of `a`, a finite principal
part `P((z - a)⁻¹)`, for a polynomial `P` without constant term, plus a function analytic at
`a`. -/
theorem MeromorphicAt.exists_eventuallyEq_eval_inv_sub_add {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    ∃ P : 𝕜[X], P.coeff 0 = 0 ∧ ∃ r : 𝕜 → 𝕜, AnalyticAt 𝕜 r a ∧
      f =ᶠ[𝓝[≠] a] fun z ↦ P.eval (z - a)⁻¹ + r z := by
  obtain ⟨n, p, hp⟩ := hf
  refine ⟨_, TauCeti.coeff_zero_sum_range_monomial_sub n p.coeff, _,
    (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← hp.inv_pow_mul_eq_eval_inv_sub_add n hz, smul_eq_mul,
    inv_mul_cancel_left₀ (pow_ne_zero n (sub_ne_zero.2 hz))]

/-- The norm of `P((z - a)⁻¹)` tends to infinity as `z` tends to `a`, for a polynomial `P` of
positive degree. -/
theorem Polynomial.tendsto_norm_eval_inv_sub_atTop (P : 𝕜[X]) (hP : 0 < P.degree) (a : 𝕜) :
    Tendsto (fun z ↦ ‖P.eval (z - a)⁻¹‖) (𝓝[≠] a) atTop := by
  refine P.tendsto_norm_atTop hP (tendsto_norm_inv_nhdsNE_zero_atTop.comp ?_)
  have h : Tendsto (fun z ↦ z - a) (𝓝 a) (𝓝 0) := by
    simpa using (continuous_sub_right a).tendsto a
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall fun z hz ↦ sub_ne_zero.2 hz)

/-- **Uniqueness of principal parts.** If `P` has no constant term and `P((z - a)⁻¹)` has a limit
as `z` tends to `a` off `a`, then `P = 0`. -/
theorem Polynomial.eq_zero_of_tendsto_eval_inv_sub (P : 𝕜[X]) (hP : P.coeff 0 = 0) {c : 𝕜}
    (h : Tendsto (fun z ↦ P.eval (z - a)⁻¹) (𝓝[≠] a) (𝓝 c)) : P = 0 := by
  by_contra hne
  have hdeg : 0 < P.degree := not_le.1 fun hle ↦ hne (by rw [eq_C_of_degree_le_zero hle, hP, C_0])
  exact not_tendsto_atTop_of_tendsto_nhds h.norm (P.tendsto_norm_eval_inv_sub_atTop hdeg a)

namespace TauCeti.meromorphicGerms

variable (a) in
/-- The ring homomorphism sending a polynomial `P` to the meromorphic germ at `a` of
`z ↦ P((z - a)⁻¹)`. On polynomials without constant term its values are the finite principal
parts at `a`. -/
noncomputable def evalInvSub : 𝕜[X] →+* meromorphicGerms 𝕜 a :=
  ((Germ.coeRingHom (𝓝[≠] a)).comp (RingHom.pi fun z ↦ evalRingHom (z - a)⁻¹)).codRestrict _
    fun P ↦ coe_mem_meromorphicGerms.2 <|
      ((MeromorphicAt.id a).sub (MeromorphicAt.const a a)).inv.eval_polynomial P

@[simp]
theorem coe_evalInvSub (P : 𝕜[X]) :
    (evalInvSub a P : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ P.eval (z - a)⁻¹ : 𝕜 → 𝕜) :=
  (rfl)

end TauCeti.meromorphicGerms
