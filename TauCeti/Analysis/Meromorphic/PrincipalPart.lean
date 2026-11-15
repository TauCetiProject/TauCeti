/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Algebra.Polynomial.BigOperators
public import TauCeti.Analysis.Analytic.ExtractZeros
public import TauCeti.Analysis.Calculus.DSlope.Basic
public import TauCeti.Analysis.Meromorphic.Germ

/-!
# The principal part of a meromorphic germ

Let `𝕜` be a nontrivially normed field and `a : 𝕜`. A meromorphic germ `φ` at `a` splits uniquely
as `φ = P((z - a)⁻¹) + g`, where `P` is a polynomial without constant term and `g` is the germ of a
function analytic at `a`. The polynomial `P` is the *principal part*
`TauCeti.meromorphicGerms.principalPart φ`; writing `P = Σ_{k ≥ 1} P_k X ^ k`, the germ `φ` has the
finite principal part `Σ_k P_k (z - a) ^ (-k)` and a regular remainder.

Concretely, if `φ` is represented by `(z - a)⁻ᴺ h z` with `h` analytic at `a`, Taylor's formula
with divided-difference remainder `TauCeti.sum_add_pow_sub_smul_iterate_dslope` splits
`h z = Σ_{j<N} c_j (z - a) ^ j + (z - a) ^ N q z`, where `c_j` are the Taylor coefficients of `h` at
`a` and `q = (swap dslope a)^[N] h` is analytic at `a`. Dividing by `(z - a) ^ N` gives the
principal part `Σ_{j<N} c_j X ^ (N - j)` and the regular remainder `q`
(`TauCeti.meromorphicGerms.principalPart_eq_sum_coeff` and
`TauCeti.meromorphicGerms.coe_sub_evalInvSub_principalPart`).

Uniqueness rests on the order computation `TauCeti.meromorphicOrderAt_eval_inv_sub`: a nonzero
polynomial `P` in `(z - a)⁻¹` has order `-P.natDegree` at `a`, so when `P` has no constant term it
has a pole at `a` and is not the germ of an analytic function. Hence the principal part depends
only on the germ, not on the exponent `N`, the representative or the neighbourhood used to compute
it, and it is linear over `𝕜`.

Over `ℂ` the regular remainder is a germ of the holomorphic structure sheaf; that version of the
splitting is `TauCeti.holomorphicStructureSheaf.regularPart` in
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm`.

## Main declarations

* `Polynomial.meromorphicAt_eval_inv_sub`: a polynomial in `(z - a)⁻¹` is meromorphic at `a`.
* `TauCeti.meromorphicOrderAt_eval_inv_sub`: the order at `a` of `z ↦ P((z - a)⁻¹)`.
* `TauCeti.meromorphicGerms.evalInvSub`: the ring homomorphism `P ↦ P((z - a)⁻¹)` into the
  meromorphic germs at `a`; it is injective (`evalInvSub_injective`).
* `TauCeti.meromorphicGerms.principalPart`: the principal part, a `𝕜`-linear map to polynomials.
* `TauCeti.meromorphicGerms.principalPart_eq_iff`: its characterization: `principalPart φ = P`
  exactly when `P` has no constant term and `φ - P((z - a)⁻¹)` has an analytic representative.
* `TauCeti.meromorphicGerms.principalPart_eq_zero_iff`: the principal part vanishes exactly on the
  germs of analytic functions.
* `TauCeti.meromorphicGerms.natDegree_principalPart_mk_le`: a pole bound bounds the degree of the
  principal part.
* `TauCeti.meromorphicGerms.principalPart_eq_sum_coeff`: the principal part of
  `(z - a)⁻ᴺ h z` through the Taylor coefficients of `h`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 4, Section 3.
-/

public noncomputable section

open Filter Function Polynomial Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-! ### Polynomials in the inverse coordinate -/

/-- A polynomial in the inverse coordinate `(z - a)⁻¹` is meromorphic at `a`. -/
theorem _root_.Polynomial.meromorphicAt_eval_inv_sub (P : 𝕜[X]) (a : 𝕜) :
    MeromorphicAt (fun z ↦ P.eval (z - a)⁻¹) a := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [eval_add]
    exact hP.add hQ
  | monomial n c =>
    simp only [eval_monomial]
    exact (MeromorphicAt.const c a).mul (((MeromorphicAt.id a).sub (.const a a)).inv.pow n)

/-- A nonzero polynomial `P` in the inverse coordinate has order `-P.natDegree` at `a`: off `a` it
is `(z - a) ^ (-P.natDegree)` times the reversed polynomial `P.reverse` evaluated at `z - a`, whose
value at `a` is the leading coefficient of `P`. -/
theorem meromorphicOrderAt_eval_inv_sub {P : 𝕜[X]} (hP : P ≠ 0) (a : 𝕜) :
    meromorphicOrderAt (fun z ↦ P.eval (z - a)⁻¹) a = ((-P.natDegree : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff (meromorphicAt_eval_inv_sub P a)]
  refine ⟨fun z ↦ P.reverse.eval (z - a),
    (AnalyticOnNhd.eval_polynomial P.reverse).comp (by fun_prop) (fun _ _ ↦ Set.mem_univ _) a
      (Set.mem_univ _), ?_, ?_⟩
  · beta_reduce
    rwa [sub_self, ← coeff_zero_eq_eval_zero, coeff_zero_reverse, Ne, leadingCoeff_eq_zero]
  · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
    let := invertibleOfNonzero (inv_ne_zero (sub_ne_zero.2 hz))
    have h := eval₂_reverse_mul_pow (RingHom.id 𝕜) (z - a)⁻¹ P
    rw [invOf_eq_inv, inv_inv, eval₂_id, eval₂_id] at h
    rw [← h, smul_eq_mul, zpow_neg, zpow_natCast, inv_pow, mul_comm]

/-- A polynomial without constant term in the inverse coordinate `(z - a)⁻¹` agrees with a function
analytic at `a` on a punctured neighbourhood of `a` only if it is zero: otherwise it has a pole at
`a`. -/
theorem eq_zero_of_eval_inv_sub_eventuallyEq {P : 𝕜[X]} (hP : P.coeff 0 = 0) {g : 𝕜 → 𝕜}
    (hg : AnalyticAt 𝕜 g a) (h : (fun z ↦ P.eval (z - a)⁻¹) =ᶠ[𝓝[≠] a] g) : P = 0 := by
  by_contra hP0
  have hord := hg.meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr h, meromorphicOrderAt_eval_inv_sub hP0] at hord
  have hd : P.natDegree = 0 := by
    have : (0 : ℤ) ≤ -(P.natDegree : ℤ) := mod_cast hord
    omega
  exact hP0 (by rw [eq_C_of_natDegree_eq_zero hd, hP, C_0])

/-- **Principal part splitting of `(z - a)⁻ᴺ h`.** For every function `h` and every `N`, off `a`,
`(z - a)⁻ᴺ h z = P((z - a)⁻¹) + q z` with `P = Σ_{j<N} c_j X ^ (N - j)`, where
`c_j = (swap dslope a)^[j] h a` and `q = (swap dslope a)^[N] h`. -/
theorem inv_pow_sub_mul_eq_eval_inv_sub_add (h : 𝕜 → 𝕜) (N : ℕ) {z : 𝕜} (hz : z ≠ a) :
    ((z - a) ^ N)⁻¹ * h z =
      (∑ j ∈ Finset.range N, C ((swap dslope a)^[j] h a) * X ^ (N - j)).eval (z - a)⁻¹ +
        (swap dslope a)^[N] h z := by
  have hz' : z - a ≠ 0 := sub_ne_zero.2 hz
  conv_lhs => rw [← sum_add_pow_sub_smul_iterate_dslope h a z N]
  rw [mul_add, Finset.mul_sum, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero N hz'),
    eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjN : (z - a) ^ N = (z - a) ^ j * (z - a) ^ (N - j) := by
    rw [← pow_add, Nat.add_sub_cancel' (Finset.mem_range.1 hj).le]
  rw [eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul, hjN, inv_pow]
  field_simp

namespace meromorphicGerms

/-! ### Evaluation at the inverse coordinate -/

variable (a) in
/-- Evaluation at the inverse coordinate: the polynomial `P` gives the meromorphic germ of
`z ↦ P((z - a)⁻¹)` at `a`. -/
def evalInvSub : 𝕜[X] →+* meromorphicGerms 𝕜 a :=
  ((Germ.coeRingHom (𝓝[≠] a)).comp (RingHom.pi fun z ↦ evalRingHom (z - a)⁻¹)).codRestrict _
    fun P ↦ coe_mem_meromorphicGerms.2 (meromorphicAt_eval_inv_sub P a)

@[simp]
theorem _root_.Polynomial.coe_evalInvSub (P : 𝕜[X]) :
    (evalInvSub a P : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ P.eval (z - a)⁻¹ : 𝕜 → 𝕜) :=
  (rfl)

/-- Distinct polynomials in the inverse coordinate have distinct germs at `a`. -/
theorem evalInvSub_injective : Injective (evalInvSub (𝕜 := 𝕜) a) := by
  refine (injective_iff_map_eq_zero _).2 fun P hP ↦ ?_
  by_contra hP0
  have h := meromorphicOrderAt_eval_inv_sub hP0 a
  have hP' := congrArg Subtype.val hP
  rw [coe_evalInvSub, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq] at hP'
  rw [meromorphicOrderAt_eq_top_iff.2 hP'] at h
  exact WithTop.top_ne_coe h

/-! ### The principal part -/

/-- Every meromorphic germ is a polynomial without constant term in `(z - a)⁻¹` plus the germ of
a function analytic at `a`. -/
private theorem exists_principalPart (φ : meromorphicGerms 𝕜 a) :
    ∃ P : 𝕜[X], P.coeff 0 = 0 ∧ ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g a ∧
      ((φ - evalInvSub a P : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g := by
  obtain ⟨f, ⟨N, hN⟩, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  refine ⟨_, coeff_zero_sum_C_mul_X_pow_sub
    (fun j ↦ (swap dslope a)^[j] (fun z ↦ (z - a) ^ N • f z) a) N, _,
    hN.iterate_dslope (a := a) N, ?_⟩
  rw [AddSubgroupClass.coe_sub, ← hφ, coe_evalInvSub, ← Germ.coe_sub, Germ.coe_eq]
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
  rw [Pi.sub_apply, sub_eq_iff_eq_add', ← inv_pow_sub_mul_eq_eval_inv_sub_add _ N hz,
    smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero N (sub_ne_zero.2 hz))]

/-- The polynomial part of a splitting of a meromorphic germ is unique. -/
private theorem eq_of_coe_sub_evalInvSub_eq {φ : meromorphicGerms 𝕜 a} {P Q : 𝕜[X]}
    (hP : P.coeff 0 = 0) (hQ : Q.coeff 0 = 0) {g g' : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g a)
    (hg' : AnalyticAt 𝕜 g' a)
    (hφP : ((φ - evalInvSub a P : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g)
    (hφQ : ((φ - evalInvSub a Q : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g') : P = Q := by
  refine sub_eq_zero.1 <| eq_zero_of_eval_inv_sub_eventuallyEq (by rw [coeff_sub, hP, hQ, sub_zero])
    (hg'.sub hg) (Germ.coe_eq.1 ?_)
  rw [← coe_evalInvSub, Germ.coe_sub, ← hφP, ← hφQ, ← AddSubgroupClass.coe_sub, map_sub]
  congr 1
  abel

/-- The principal part of a meromorphic germ `φ` at `a`: the unique polynomial `P` without
constant term such that `φ - P((z - a)⁻¹)` is the germ of a function analytic at `a`. It is
linear over `𝕜`. -/
def principalPart : meromorphicGerms 𝕜 a →ₗ[𝕜] 𝕜[X] where
  toFun φ := (exists_principalPart φ).choose
  map_add' φ ψ := by
    obtain ⟨hP, g, hg, hgφ⟩ := (exists_principalPart (φ + ψ)).choose_spec
    obtain ⟨hP₁, g₁, hg₁, hgφ₁⟩ := (exists_principalPart φ).choose_spec
    obtain ⟨hP₂, g₂, hg₂, hgφ₂⟩ := (exists_principalPart ψ).choose_spec
    refine eq_of_coe_sub_evalInvSub_eq hP (by rw [coeff_add, hP₁, hP₂, add_zero]) hg
      (hg₁.add hg₂) hgφ ?_
    rw [map_add, add_sub_add_comm, AddMemClass.coe_add, hgφ₁, hgφ₂]
    rfl
  map_smul' c φ := by
    obtain ⟨hP, g, hg, hgφ⟩ := (exists_principalPart (c • φ)).choose_spec
    obtain ⟨hP₁, g₁, hg₁, hgφ₁⟩ := (exists_principalPart φ).choose_spec
    refine eq_of_coe_sub_evalInvSub_eq (Q := c • (exists_principalPart φ).choose)
      hP (by rw [AddMonoidAlgebra.coeff_smul_apply, hP₁, smul_zero]) hg (hg₁.const_smul (c := c))
      hgφ ?_
    have heval : evalInvSub a (c • (exists_principalPart φ).choose) =
        c • evalInvSub a (exists_principalPart φ).choose := by
      apply Subtype.ext
      simp only [coe_evalInvSub, coe_smul, ← Germ.coe_smul]
      congr 1
      funext z
      simp [Polynomial.smul_eq_C_mul]
    rw [heval, ← smul_sub, coe_smul, hgφ₁, Germ.coe_smul]

/-- The principal part has no constant term. -/
@[simp]
theorem coeff_zero_principalPart (φ : meromorphicGerms 𝕜 a) : (principalPart φ).coeff 0 = 0 :=
  (exists_principalPart φ).choose_spec.1

/-- Subtracting its principal part from a meromorphic germ leaves the germ of an analytic
function. -/
theorem exists_analyticAt_coe_sub_evalInvSub_principalPart (φ : meromorphicGerms 𝕜 a) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g a ∧
      ((φ - evalInvSub a (principalPart φ) : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g :=
  (exists_principalPart φ).choose_spec.2

/-- **Characterization of the principal part.** `principalPart φ = P` exactly when `P` has no
constant term and `φ - P((z - a)⁻¹)` is the germ of a function analytic at `a`. -/
theorem principalPart_eq_iff {φ : meromorphicGerms 𝕜 a} {P : 𝕜[X]} :
    principalPart φ = P ↔ P.coeff 0 = 0 ∧ ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g a ∧
      ((φ - evalInvSub a P : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g := by
  refine ⟨?_, fun ⟨hP, g, hg, hgφ⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨coeff_zero_principalPart φ, exists_analyticAt_coe_sub_evalInvSub_principalPart φ⟩
  · obtain ⟨g', hg', hgφ'⟩ := exists_analyticAt_coe_sub_evalInvSub_principalPart φ
    exact eq_of_coe_sub_evalInvSub_eq (coeff_zero_principalPart φ) hP hg' hg hgφ' hgφ

/-- The principal part of a polynomial in the inverse coordinate is the polynomial with its
constant term removed. -/
@[simp]
theorem principalPart_evalInvSub {P : 𝕜[X]} :
    principalPart (evalInvSub a P) = P - C (P.coeff 0) :=
  principalPart_eq_iff.2 ⟨by simp, fun _ ↦ P.coeff 0, analyticAt_const, by
    rw [map_sub, sub_sub_cancel, coe_evalInvSub]
    simp_rw [eval_C]⟩

/-- A polynomial without constant term in the inverse coordinate is its own principal part. -/
theorem principalPart_evalInvSub_of_coeff_zero {P : 𝕜[X]} (hP : P.coeff 0 = 0) :
    principalPart (evalInvSub a P) = P := by
  rw [principalPart_evalInvSub, hP, C_0, sub_zero]

/-- The principal part of a meromorphic germ vanishes exactly when the germ is that of a function
analytic at `a`. -/
theorem principalPart_eq_zero_iff {φ : meromorphicGerms 𝕜 a} :
    principalPart φ = 0 ↔ ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g a ∧ (φ : Germ (𝓝[≠] a) 𝕜) = g := by
  simp [principalPart_eq_iff]

/-- The principal part of the germ of a function meromorphic at `a` vanishes exactly when the
function has nonnegative order at `a`. -/
theorem principalPart_mk_eq_zero_iff {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) :
    principalPart (mk f hf) = 0 ↔
      0 ≤ meromorphicOrderAt f a := by
  simp_rw [principalPart_eq_zero_iff, coe_mk, hf.meromorphicOrderAt_nonneg_iff, Germ.coe_eq]

/-- A pole bound bounds the degree of the principal part. The constant term of the principal
part is zero, so a removable singularity contributes the zero polynomial. -/
theorem natDegree_principalPart_mk_le {f : 𝕜 → 𝕜} (hf : MeromorphicAt f a) {N : ℕ}
    (hN : ((-N : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    (principalPart (mk f hf)).natDegree ≤ N := by
  let P := principalPart (mk f hf)
  by_cases hP : P = 0
  · simp [P, hP]
  obtain ⟨g, hg, hfg⟩ := exists_analyticAt_coe_sub_evalInvSub_principalPart (mk f hf)
  rw [AddSubgroupClass.coe_sub, coe_mk, coe_evalInvSub, ← Germ.coe_sub] at hfg
  have hfg' : f =ᶠ[𝓝[≠] a] (fun z ↦ P.eval (z - a)⁻¹) + g := by
    have := Germ.coe_eq.1 hfg
    filter_upwards [this] with z hz
    exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
  have hord : meromorphicOrderAt f a = ((-P.natDegree : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr hfg']
    apply (meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt ?_).trans
      (meromorphicOrderAt_eval_inv_sub hP a)
    rw [meromorphicOrderAt_eval_inv_sub hP a]
    have hdeg : 0 < P.natDegree := Nat.pos_of_ne_zero fun h ↦ hP <| by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h]
      simp [P]
    exact lt_of_lt_of_le (by exact_mod_cast neg_neg_of_pos (Int.natCast_pos.mpr hdeg))
      hg.meromorphicOrderAt_nonneg
  rw [hord, WithTop.coe_le_coe] at hN
  exact_mod_cast neg_le_neg_iff.mp hN

/-- **The principal part through Taylor coefficients.** If `φ` is the germ of `(z - a)⁻ᴺ h z`,
where `h` has the power series `p` at `a`, then the principal part of `φ` is
`Σ_{j<N} p.coeff j • X ^ (N - j)`: the Taylor coefficients of `h` of degree below `N`. -/
theorem principalPart_eq_sum_coeff {φ : meromorphicGerms 𝕜 a} {h : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} (hp : HasFPowerSeriesAt h p a) {N : ℕ}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜)) :
    principalPart φ = ∑ j ∈ Finset.range N, C (p.coeff j) * X ^ (N - j) := by
  simp_rw [← hp.iterate_dslope_apply_eq_coeff]
  refine principalPart_eq_iff.2 ⟨coeff_zero_sum_C_mul_X_pow_sub _ N, _,
    hp.analyticAt.iterate_dslope (a := a) N, ?_⟩
  rw [AddSubgroupClass.coe_sub, hφ, coe_evalInvSub, ← Germ.coe_sub, Germ.coe_eq]
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
  rw [Pi.sub_apply, inv_pow_sub_mul_eq_eval_inv_sub_add _ N hz, add_sub_cancel_left]

/-- **The regular remainder through divided differences.** If `φ` is the germ of `(z - a)⁻ᴺ h z`
with `h` analytic at `a`, then `φ` minus its principal part is the germ of the analytic function
`(swap dslope a)^[N] h`, the remainder in Taylor's formula
`h z = Σ_{j<N} c_j (z - a) ^ j + (z - a) ^ N (swap dslope a)^[N] h z`. -/
theorem coe_sub_evalInvSub_principalPart {φ : meromorphicGerms 𝕜 a} {h : 𝕜 → 𝕜}
    (hh : AnalyticAt 𝕜 h a) {N : ℕ}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜)) :
    ((φ - evalInvSub a (principalPart φ) : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (swap dslope a)^[N] h := by
  obtain ⟨p, hp⟩ := hh
  rw [principalPart_eq_sum_coeff hp hφ, AddSubgroupClass.coe_sub, hφ, coe_evalInvSub,
    ← Germ.coe_sub, Germ.coe_eq]
  simp_rw [← hp.iterate_dslope_apply_eq_coeff]
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
  rw [Pi.sub_apply, inv_pow_sub_mul_eq_eval_inv_sub_add _ N hz, add_sub_cancel_left]

end meromorphicGerms

end TauCeti
