/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Contour.MeromorphicLaurent
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm
import TauCeti.Analysis.Contour.Residue.Theorem

/-!
# Principal parts and regular parts of meromorphic germs

Let `a : ℂ`, let `𝒪_a` be the stalk at `a` of the holomorphic structure sheaf of `ℂ` and let
`K_a = meromorphicGerms ℂ a` be the field of meromorphic germs at `a` on punctured neighbourhoods,
which contains `𝒪_a` through `TauCeti.holomorphicStructureSheaf.toMeromorphicGerms`.

Every meromorphic germ `φ` splits uniquely as a holomorphic germ plus a finite Laurent tail:
`φ = q + ∑_{1 ≤ k ≤ N} c_k (z - a)⁻ᵏ`. This file records the tail as a polynomial in
`(z - a)⁻¹` without constant term, the **principal part**
`TauCeti.meromorphicGerms.principalPart a φ : ℂ[X]`, so that `c_k` is its coefficient of `X ^ k`,
and the holomorphic germ `q` as the **regular part**
`TauCeti.meromorphicGerms.regularPart a φ ∈ 𝒪_a`. Both are additive maps.

Being defined on germs, the two parts do not depend on the representative of `φ`, on the
punctured neighbourhood on which it is given, or on the length `N` of an expansion: this is the
uniqueness theorem `principalPart_eq_and_regularPart_eq_iff`, which characterizes the pair by the
decomposition. Uniqueness reduces to `TauCeti.Contour.laurent_coeff_unique`: a finite Laurent tail
which is continuous at `a` vanishes.

Existence is Taylor's theorem. If `φ` is represented by `h(z) / (z - a)^N` with `h` analytic at
`a`, split the Taylor expansion of `h` as `h(z) = ∑_{j < N} c_j (z - a)^j + (z - a)^N q(z)`. Then
`principalPart_eq_sum_of_coe_eq` identifies the principal part with
`∑_{j < N} c_j X^(N - j)`, where `c_j = h⁽ʲ⁾(a) / j!`, and
`coe_toMeromorphicGerms_regularPart_of_coe_eq` identifies the regular part with the germ of `q`.
Every meromorphic germ has such a representative, by definition of `MeromorphicAt`.

The regular germs are exactly those with vanishing principal part
(`principalPart_eq_zero_iff`), and on them `regularPart` inverts `toMeromorphicGerms`
(`regularPart_toMeromorphicGerms`).

The coefficients are computed from any representative `f` of `φ`: the coefficient of
`X ^ (k + 1)` is the residue at `a` of `(z - a)^k f(z)` (`coeff_principalPart_succ`), so the
coefficient of `X` is the residue of `f` (`coeff_principalPart_one`), and by the residue theorem
it is `(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a)^k f(z) dz` for every sufficiently small `ρ > 0`
(`coeff_principalPart_succ_eq_circleIntegral`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 4, §§3.2–3.3 and
  Chapter 5, §1.3.
-/

public noncomputable section

open Complex Filter Polynomial Real Topology
open scoped ContDiff Manifold

namespace TauCeti.meromorphicGerms

open holomorphicStructureSheaf

variable {a : ℂ}

/-! ### Finite Laurent tails as polynomials in `(z - a)⁻¹` -/

/-- A polynomial without constant term, evaluated at `(z - a)⁻¹`, is the finite Laurent tail with
its coefficients. -/
private theorem eval_inv_sub_eq_sum {P : ℂ[X]} (hP : P.coeff 0 = 0) (z : ℂ) :
    P.eval (z - a)⁻¹ = ∑ k : Fin P.natDegree, P.coeff (k + 1) / (z - a) ^ (k.val + 1) := by
  rw [eval_eq_sum_range, Finset.sum_range_succ', hP, zero_mul, add_zero,
    ← Fin.sum_univ_eq_sum_range]
  simp [div_eq_mul_inv]

/-- The zero-padded coefficients of the Laurent tail of a polynomial are its coefficients. -/
private theorem dite_coeff_succ (P : ℂ[X]) (k : ℕ) :
    (if hk : k < P.natDegree then P.coeff ((⟨k, hk⟩ : Fin P.natDegree).val + 1) else 0) =
      P.coeff (k + 1) := by
  split_ifs with hk
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Two polynomials without constant term whose evaluations at `(z - a)⁻¹` differ, on a punctured
neighbourhood of `a`, by functions continuous at `a` are equal. -/
private theorem eq_of_eventuallyEq_add_eval {P Q : ℂ[X]} (hP : P.coeff 0 = 0) (hQ : Q.coeff 0 = 0)
    {g h : ℂ → ℂ} (hg : ContinuousAt g a) (hh : ContinuousAt h a)
    (heq : ∀ᶠ z in 𝓝[≠] a, g z + P.eval (z - a)⁻¹ = h z + Q.eval (z - a)⁻¹) : P = Q := by
  ext (_ | k)
  · rw [hP, hQ]
  · have := Contour.laurent_coeff_unique hg hh
      (heq.mono fun z hz ↦ by rwa [eval_inv_sub_eq_sum hP, eval_inv_sub_eq_sum hQ] at hz) k
    rwa [dite_coeff_succ, dite_coeff_succ] at this

/-- **Taylor splitting.** If `h` is analytic at `a`, then on a punctured neighbourhood of `a`,
`h(z) / (z - a)^N` is the evaluation at `(z - a)⁻¹` of `∑_{j < N} (h⁽ʲ⁾(a) / j!) X^(N - j)` plus
`(h(z) - ∑_{j < N} (h⁽ʲ⁾(a) / j!) (z - a)^j) / (z - a)^N`, a function which agrees near `a` with a
function analytic at `a`. -/
private theorem exists_analyticAt_eventuallyEq_div_pow {h : ℂ → ℂ} (hh : AnalyticAt ℂ h a)
    (N : ℕ) : ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧
      (∀ᶠ z in 𝓝[≠] a, q z =
        (h z - ∑ j ∈ Finset.range N, iteratedDeriv j h a / (j.factorial : ℂ) * (z - a) ^ j) /
          (z - a) ^ N) ∧
      ∀ᶠ z in 𝓝[≠] a, h z / (z - a) ^ N = q z +
        (∑ j ∈ Finset.range N, C (iteratedDeriv j h a / (j.factorial : ℂ)) * X ^ (N - j)).eval
          (z - a)⁻¹ := by
  have hh' : AnalyticAt ℂ (fun w ↦ h (w + a)) 0 := by
    rw [← zero_add a] at hh
    exact hh.comp_of_eq (by fun_prop) rfl
  obtain ⟨F, hF, hFeq⟩ := hh'.exists_eventuallyEq_sum_add_pow_mul N
  have hsub : Tendsto (fun z ↦ z - a) (𝓝[≠] a) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_sub_right a).tendsto a)
  have hderiv (j : ℕ) : iteratedDeriv j (fun w ↦ h (w + a)) 0 = iteratedDeriv j h a := by
    simp [iteratedDeriv_comp_add_const]
  have htaylor : ∀ᶠ z in 𝓝[≠] a, h z = (∑ j ∈ Finset.range N,
      iteratedDeriv j h a / (j.factorial : ℂ) * (z - a) ^ j) + (z - a) ^ N * F (z - a) := by
    filter_upwards [hsub.eventually hFeq] with z hz
    simp only [hderiv, sub_add_cancel, smul_eq_mul] at hz
    rw [hz]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  refine ⟨fun z ↦ F (z - a), hF.comp_of_eq (by fun_prop) (sub_self a), ?_, ?_⟩
  · filter_upwards [htaylor, self_mem_nhdsWithin] with z hz hza
    have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
    rw [hz, add_sub_cancel_left, mul_div_cancel_left₀ _ (pow_ne_zero N hza')]
  · filter_upwards [htaylor, self_mem_nhdsWithin] with z hz hza
    have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [hz, add_div, mul_div_cancel_left₀ _ (pow_ne_zero N hza'), add_comm, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjN : j ≤ N := (Finset.mem_range.1 hj).le
    rw [← Nat.sub_add_cancel hjN, pow_add, Nat.add_sub_cancel, inv_pow]
    field_simp

/-- The polynomial `∑_{j < N} c_j X^(N - j)` has no constant term. -/
private theorem coeff_sum_C_mul_X_pow_sub_zero (N : ℕ) (c : ℕ → ℂ) :
    (∑ j ∈ Finset.range N, C (c j) * X ^ (N - j)).coeff 0 = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have := Finset.mem_range.1 hj
  rw [coeff_C_mul_X_pow, ite_eq_right_iff]
  omega

/-- Every meromorphic germ at `a` is a holomorphic germ plus the evaluation at `(z - a)⁻¹` of a
polynomial without constant term. -/
private theorem exists_coe_eq_add_eval (φ : meromorphicGerms ℂ a) :
    ∃ P : ℂ[X], P.coeff 0 = 0 ∧ ∃ s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a,
      (φ : Germ (𝓝[≠] a) ℂ) =
        (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) + ↑(fun z ↦ P.eval (z - a)⁻¹) := by
  obtain ⟨f, ⟨N, hN⟩, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  obtain ⟨q, hq, -, hdecomp⟩ := exists_analyticAt_eventuallyEq_div_pow hN N
  obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hq
  refine ⟨∑ j ∈ Finset.range N,
    C (iteratedDeriv j (fun z ↦ (z - a) ^ N • f z) a / (j.factorial : ℂ)) * X ^ (N - j),
    coeff_sum_C_mul_X_pow_sub_zero N _, s, ?_⟩
  rw [← hφ, hs, ← Germ.coe_add, Germ.coe_eq]
  filter_upwards [hdecomp, self_mem_nhdsWithin] with z hz hza
  rw [Pi.add_apply, ← hz, smul_eq_mul, mul_div_cancel_left₀ _ (pow_ne_zero N (sub_ne_zero.2 hza))]

/-- Two decompositions of a meromorphic germ as a holomorphic germ plus the evaluation at
`(z - a)⁻¹` of a polynomial without constant term coincide. -/
private theorem eq_and_eq_of_coe_add_eval_eq {P Q : ℂ[X]} (hP : P.coeff 0 = 0)
    (hQ : Q.coeff 0 = 0) {s t : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a}
    (h : (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) + ↑(fun z ↦ P.eval (z - a)⁻¹) =
      (toMeromorphicGerms a t : Germ (𝓝[≠] a) ℂ) + ↑(fun z ↦ Q.eval (z - a)⁻¹)) :
    P = Q ∧ s = t := by
  obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq a s
  obtain ⟨k, hk, hkt⟩ := exists_toFilterGerm_eq a t
  rw [coe_toMeromorphicGerms, coe_toMeromorphicGerms, hgs, hkt, ← Germ.coe_add, ← Germ.coe_add,
    Germ.coe_eq] at h
  have hPQ : P = Q := eq_of_eventuallyEq_add_eval hP hQ hg.self_of_nhds.continuousAt
    hk.self_of_nhds.continuousAt h
  subst hPQ
  refine ⟨rfl, toMeromorphicGerms_injective a (Subtype.ext ?_)⟩
  rw [coe_toMeromorphicGerms, coe_toMeromorphicGerms, hgs, hkt, Germ.coe_eq]
  filter_upwards [h] with z hz
  exact add_right_cancel hz

private theorem coe_eval_zero : (↑(fun z ↦ (0 : ℂ[X]).eval (z - a)⁻¹) : Germ (𝓝[≠] a) ℂ) = 0 := by
  rw [← Germ.coe_zero, Germ.coe_eq]
  exact .of_forall fun _ ↦ eval_zero

private theorem coe_eval_add (P Q : ℂ[X]) :
    (↑(fun z ↦ (P + Q).eval (z - a)⁻¹) : Germ (𝓝[≠] a) ℂ) =
      ↑(fun z ↦ P.eval (z - a)⁻¹) + ↑(fun z ↦ Q.eval (z - a)⁻¹) := by
  rw [← Germ.coe_add, Germ.coe_eq]
  exact .of_forall fun _ ↦ eval_add

/-- The polynomial part of a chosen decomposition of `φ`; see `principalPart`. -/
private def principalPartAux (φ : meromorphicGerms ℂ a) : ℂ[X] :=
  (exists_coe_eq_add_eval φ).choose

/-- The holomorphic part of a chosen decomposition of `φ`; see `regularPart`. -/
private def regularPartAux (φ : meromorphicGerms ℂ a) :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a :=
  (exists_coe_eq_add_eval φ).choose_spec.2.choose

private theorem coeff_principalPartAux_zero (φ : meromorphicGerms ℂ a) :
    (principalPartAux φ).coeff 0 = 0 :=
  (exists_coe_eq_add_eval φ).choose_spec.1

private theorem coe_eq_regularPartAux_add (φ : meromorphicGerms ℂ a) :
    (φ : Germ (𝓝[≠] a) ℂ) = (toMeromorphicGerms a (regularPartAux φ) : Germ (𝓝[≠] a) ℂ) +
      ↑(fun z ↦ (principalPartAux φ).eval (z - a)⁻¹) :=
  (exists_coe_eq_add_eval φ).choose_spec.2.choose_spec

private theorem principalPartAux_eq_and_regularPartAux_eq {φ : meromorphicGerms ℂ a} {P : ℂ[X]}
    (hP : P.coeff 0 = 0) {s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a}
    (h : (φ : Germ (𝓝[≠] a) ℂ) =
      (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) + ↑(fun z ↦ P.eval (z - a)⁻¹)) :
    principalPartAux φ = P ∧ regularPartAux φ = s :=
  eq_and_eq_of_coe_add_eval_eq (coeff_principalPartAux_zero φ) hP
    ((coe_eq_regularPartAux_add φ).symm.trans h)

private theorem principalPartAux_zero_and_regularPartAux_zero :
    principalPartAux (0 : meromorphicGerms ℂ a) = 0 ∧
      regularPartAux (0 : meromorphicGerms ℂ a) = 0 :=
  principalPartAux_eq_and_regularPartAux_eq (coeff_zero 0) <| by
    rw [coe_eval_zero, map_zero, ZeroMemClass.coe_zero, add_zero]

private theorem principalPartAux_add_and_regularPartAux_add (φ ψ : meromorphicGerms ℂ a) :
    principalPartAux (φ + ψ) = principalPartAux φ + principalPartAux ψ ∧
      regularPartAux (φ + ψ) = regularPartAux φ + regularPartAux ψ :=
  principalPartAux_eq_and_regularPartAux_eq
    (by rw [coeff_add, coeff_principalPartAux_zero, coeff_principalPartAux_zero, add_zero]) <| by
    rw [coe_eval_add, map_add, Subring.coe_add, Subring.coe_add, coe_eq_regularPartAux_add φ,
      coe_eq_regularPartAux_add ψ, add_add_add_comm]

/-! ### The principal part and the regular part -/

variable (a) in
/-- The **principal part** of a meromorphic germ `φ` at `a`: the unique polynomial `P` without
constant term such that `φ` minus the germ of `z ↦ P((z - a)⁻¹)` is holomorphic at `a`. Its
coefficient of `X ^ k` is the Laurent coefficient of `φ` of order `-k`. -/
def principalPart : meromorphicGerms ℂ a →+ ℂ[X] where
  toFun := principalPartAux
  map_zero' := principalPartAux_zero_and_regularPartAux_zero.1
  map_add' φ ψ := (principalPartAux_add_and_regularPartAux_add φ ψ).1

variable (a) in
/-- The **regular part** of a meromorphic germ `φ` at `a`: the unique holomorphic germ `q` at `a`
such that `φ - q` is the germ of `z ↦ P((z - a)⁻¹)` for a polynomial `P` without constant term
(namely the principal part of `φ`). -/
def regularPart :
    meromorphicGerms ℂ a →+ (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a where
  toFun := regularPartAux
  map_zero' := principalPartAux_zero_and_regularPartAux_zero.2
  map_add' φ ψ := (principalPartAux_add_and_regularPartAux_add φ ψ).2

/-- The principal part of a meromorphic germ has no constant term. -/
@[simp]
theorem coeff_principalPart_zero (φ : meromorphicGerms ℂ a) : (principalPart a φ).coeff 0 = 0 :=
  coeff_principalPartAux_zero φ

/-- **The Laurent decomposition of a meromorphic germ**: a meromorphic germ is its regular part
plus the germ of its principal part evaluated at `(z - a)⁻¹`. -/
theorem coe_eq_regularPart_add_principalPart (φ : meromorphicGerms ℂ a) :
    (φ : Germ (𝓝[≠] a) ℂ) = (toMeromorphicGerms a (regularPart a φ) : Germ (𝓝[≠] a) ℂ) +
      ↑(fun z ↦ (principalPart a φ).eval (z - a)⁻¹) :=
  coe_eq_regularPartAux_add φ

/-- **Uniqueness of the Laurent decomposition.** A polynomial `P` and a holomorphic germ `s` are
the principal and regular parts of a meromorphic germ `φ` exactly when `P` has no constant term
and `φ` is `s` plus the germ of `z ↦ P((z - a)⁻¹)`. In particular the two parts do not depend on
the length of a finite Laurent expansion of `φ` or on the representative used to compute it. -/
theorem principalPart_eq_and_regularPart_eq_iff {φ : meromorphicGerms ℂ a} {P : ℂ[X]}
    {s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a} :
    principalPart a φ = P ∧ regularPart a φ = s ↔ P.coeff 0 = 0 ∧
      (φ : Germ (𝓝[≠] a) ℂ) =
        (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) + ↑(fun z ↦ P.eval (z - a)⁻¹) := by
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨coeff_principalPart_zero φ, coe_eq_regularPart_add_principalPart φ⟩
  · rintro ⟨hP, h⟩
    exact principalPartAux_eq_and_regularPartAux_eq hP h

/-- A holomorphic germ has no principal part. -/
@[simp]
theorem principalPart_toMeromorphicGerms
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    principalPart a (toMeromorphicGerms a s) = 0 :=
  (principalPart_eq_and_regularPart_eq_iff.2 ⟨coeff_zero 0, by rw [coe_eval_zero, add_zero]⟩).1

/-- A holomorphic germ is its own regular part: `regularPart a` is a left inverse of
`toMeromorphicGerms a`. -/
@[simp]
theorem regularPart_toMeromorphicGerms
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    regularPart a (toMeromorphicGerms a s) = s :=
  (principalPart_eq_and_regularPart_eq_iff.2 ⟨coeff_zero 0, by rw [coe_eval_zero, add_zero]⟩).2

/-- The regular meromorphic germs, those coming from holomorphic germs, are exactly those whose
principal part vanishes. -/
theorem principalPart_eq_zero_iff {φ : meromorphicGerms ℂ a} :
    principalPart a φ = 0 ↔ φ ∈ (toMeromorphicGerms a).range := by
  refine ⟨fun h ↦ ⟨regularPart a φ, Subtype.ext ?_⟩, ?_⟩
  · rw [coe_eq_regularPart_add_principalPart φ, h]
    rw [coe_eval_zero, add_zero]
  · rintro ⟨s, rfl⟩
    exact principalPart_toMeromorphicGerms s

/-! ### The Taylor splitting, residues and contour integrals -/

/-- **The principal part from a Taylor expansion.** If a meromorphic germ `φ` is represented by
`h(z) / (z - a)^N` with `h` analytic at `a`, its principal part is
`∑_{j < N} (h⁽ʲ⁾(a) / j!) X^(N - j)`: the Laurent coefficient of order `-k`, for `1 ≤ k ≤ N`, is the
Taylor coefficient of `h` of order `N - k`. -/
theorem principalPart_eq_sum_of_coe_eq {φ : meromorphicGerms ℂ a} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h a) {N : ℕ} (hφ : (φ : Germ (𝓝[≠] a) ℂ) = ↑(fun z ↦ h z / (z - a) ^ N)) :
    principalPart a φ =
      ∑ j ∈ Finset.range N, C (iteratedDeriv j h a / (j.factorial : ℂ)) * X ^ (N - j) := by
  obtain ⟨q, hq, -, hdecomp⟩ := exists_analyticAt_eventuallyEq_div_pow hh N
  obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hq
  refine (principalPart_eq_and_regularPart_eq_iff (s := s).2
    ⟨coeff_sum_C_mul_X_pow_sub_zero N _, ?_⟩).1
  rw [hφ, hs, ← Germ.coe_add, Germ.coe_eq]
  exact hdecomp

/-- **The regular part from a Taylor expansion.** If a meromorphic germ `φ` is represented by
`h(z) / (z - a)^N` with `h` analytic at `a`, its regular part is the holomorphic germ represented,
off `a`, by `(h(z) - ∑_{j < N} (h⁽ʲ⁾(a) / j!) (z - a)^j) / (z - a)^N`, the remainder of the Taylor
expansion of `h` to order `N` divided by `(z - a)^N`. -/
theorem coe_toMeromorphicGerms_regularPart_of_coe_eq {φ : meromorphicGerms ℂ a} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h a) {N : ℕ} (hφ : (φ : Germ (𝓝[≠] a) ℂ) = ↑(fun z ↦ h z / (z - a) ^ N)) :
    (toMeromorphicGerms a (regularPart a φ) : Germ (𝓝[≠] a) ℂ) =
      ↑(fun z ↦ (h z - ∑ j ∈ Finset.range N,
        iteratedDeriv j h a / (j.factorial : ℂ) * (z - a) ^ j) /
        (z - a) ^ N) := by
  obtain ⟨q, hq, hqeq, hdecomp⟩ := exists_analyticAt_eventuallyEq_div_pow hh N
  obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hq
  have hreg := (principalPart_eq_and_regularPart_eq_iff (s := s).2
    ⟨coeff_sum_C_mul_X_pow_sub_zero N _, by
      rw [hφ, hs, ← Germ.coe_add, Germ.coe_eq]
      exact hdecomp⟩).2
  rw [hreg, hs, Germ.coe_eq]
  exact hqeq

/-- **Laurent coefficients as residues.** The coefficient of `X ^ (k + 1)` in the principal part
of a meromorphic germ, its Laurent coefficient of order `-(k + 1)`, is the residue at `a` of
`(z - a)^k f(z)` for any representative `f`. -/
theorem coeff_principalPart_succ {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) (k : ℕ) :
    (principalPart a φ).coeff (k + 1) = Contour.residue (fun z ↦ (z - a) ^ k * f z) a := by
  obtain ⟨N, hN⟩ := coe_mem_meromorphicGerms.1 (hφ ▸ φ.2)
  -- Write `f` as `h(z) / (z - a)^(N + k + 1)` with `h` analytic at `a`; both sides are then the
  -- Taylor coefficient of `h` of order `N`.
  have hh : AnalyticAt ℂ (fun z ↦ (z - a) ^ (k + 1) * ((z - a) ^ N • f z)) a :=
    ((analyticAt_id.sub analyticAt_const).pow _).mul hN
  have hφh : (φ : Germ (𝓝[≠] a) ℂ) = ↑(fun z ↦
      (z - a) ^ (k + 1) * ((z - a) ^ N • f z) / (z - a) ^ (N + (k + 1))) := by
    rw [hφ, Germ.coe_eq]
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 hz
    rw [smul_eq_mul, pow_add]
    field_simp
    ring
  rw [principalPart_eq_sum_of_coe_eq hh hφh, finsetSum_coeff, Finset.sum_eq_single N,
    coeff_C_mul_X_pow,
    Contour.residue_eq_of_eventuallyEq_zpow_smul (n := -((N + 1 : ℕ) : ℤ)) (by omega) hh]
  · simp only [Nat.add_sub_cancel_left, ↓reduceIte]
    congr <;> omega
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 hz
    rw [zpow_neg, zpow_natCast, smul_eq_mul, smul_eq_mul, pow_succ]
    field_simp
    ring
  · intro j _ hjN
    rw [coeff_C_mul_X_pow, ite_eq_right_iff]
    omega
  · intro hN
    exact absurd (Finset.mem_range.2 (by omega)) hN

/-- The coefficient of `X` in the principal part of a meromorphic germ is the residue at `a` of
any of its representatives. -/
theorem coeff_principalPart_one {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) : (principalPart a φ).coeff 1 = Contour.residue f a := by
  simpa using coeff_principalPart_succ hφ 0

/-- **Laurent coefficients as contour integrals.** For every sufficiently small radius `ρ > 0`,
the coefficient of `X ^ (k + 1)` in the principal part of a meromorphic germ, its Laurent
coefficient of order `-(k + 1)`, is `(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a)^k f(z) dz` for any
representative `f`. -/
theorem coeff_principalPart_succ_eq_circleIntegral {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) (k : ℕ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (principalPart a φ).coeff (k + 1) =
      (2 * π * I)⁻¹ * ∮ z in C(a, ρ), (z - a) ^ k * f z := by
  have hF : MeromorphicAt (fun z ↦ (z - a) ^ k * f z) a :=
    ((analyticAt_id.sub analyticAt_const).pow k).meromorphicAt.mul
      (coe_mem_meromorphicGerms.1 (hφ ▸ φ.2))
  obtain ⟨ε, hε, hεF⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hF.eventually_analyticAt)
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ ⟨hρ, hρε⟩
  have han {z : ℂ} (hz : z ∈ Metric.closedBall a ρ) (hza : z ≠ a) :
      AnalyticAt ℂ (fun z ↦ (z - a) ^ k * f z) z :=
    hεF ((Metric.mem_closedBall.1 hz).trans_lt hρε) hza
  rw [Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hρ {a} (fun z hz ↦ ?_)
    (by simpa using Metric.mem_ball_self (x := a) hρ) (fun z hz hneg ↦ ?_), Finset.sum_singleton,
    ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul, coeff_principalPart_succ hφ k]
  · rcases eq_or_ne z a with rfl | hza
    · exact hF
    · exact (han hz hza).meromorphicAt
  · by_contra hza
    exact (han hz (by simpa using hza)).meromorphicOrderAt_nonneg.not_gt hneg

end TauCeti.meromorphicGerms
