/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Analysis.Complex.Runge.Operator
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.LogLinearFactor
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.Approximation

/-!
# Zero-free Runge approximation

Let `(Ω, K)` be a Runge compact pair in `ℂ` (`TauCeti.IsRungeCompactPair`): `K` is a compact
subset of the open set `Ω` and no connected component of `Ω \ K` is relatively compact in `Ω`.
Ordinary Runge approximation (`TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt`)
approximates a function holomorphic near `K` by functions holomorphic on `Ω`, but says nothing
about the zeros of the approximants away from `K`. This file proves that a function holomorphic
and nowhere zero near `K` is a uniform limit on `K` of functions holomorphic and nowhere zero on
all of `Ω` (`TauCeti.IsRungeCompactPair.exists_differentiableOn_ne_zero_norm_sub_lt`). This is the
approximation step behind the construction of holomorphic functions with prescribed zeros on
arbitrary open subsets of the plane.

The approximation follows from a factorization: near `K`, a nowhere-zero holomorphic function is a
function holomorphic and nowhere zero on `Ω` times the exponential of a holomorphic function
(`TauCeti.IsRungeCompactPair.exists_eqOn_mul_exp`). Approximating the exponent by scalar Runge and
exponentiating then keeps the approximant zero-free on `Ω`.

## Main results

* `TauCeti.IsRungeCompactPair.exists_eqOn_mul_exp`: the factorization above.
* `TauCeti.IsRungeCompactPair.exists_differentiableOn_ne_zero_norm_sub_lt`: zero-free Runge
  approximation.

## Implementation notes

For the factorization, the discretized Cauchy–Pompeiu formula
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`) approximates the function on `K` by a
rational function with poles off `K`. Close enough, the quotient of the two has a principal
logarithm near `K`, so only the rational function needs factoring. Its numerator splits into
linear factors `z - b` with `b ∉ K`. When the component of `b` in `Kᶜ` is bounded, filledness of `K`
in `Ω` puts a point `a ∉ Ω` in that component, and `z - b` is `z - a`, a nowhere-zero function on
`Ω`, times an exponential near `K`. When the component is unbounded, `z - b` is itself an
exponential near `K`. These two logarithms are supplied by
`TauCeti.exists_eqOn_sub_mul_exp_of_mem_connectedComponentIn` and
`TauCeti.exists_eqOn_sub_exp_of_notMem_filledHull` respectively.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Lemma 15.1 and Proposition 15.2.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Complex Metric Polynomial Set
open scoped Topology

namespace TauCeti

variable {K Ω : Set ℂ}

/-- Near `K`, the function `v` is a function holomorphic and nowhere zero on `Ω` times the
exponential of a function holomorphic on an open neighbourhood of `K`. -/
private def IsUnitMulExpNear (Ω K : Set ℂ) (v : ℂ → ℂ) : Prop :=
  ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ (∀ z ∈ Ω, H z ≠ 0) ∧
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ W ∧
      EqOn v (fun z ↦ H z * exp (ℓ z)) W

private theorem IsUnitMulExpNear.congr {v w : ℂ → ℂ} (hv : IsUnitMulExpNear Ω K v)
    {W : Set ℂ} (hW : IsOpen W) (hKW : K ⊆ W) (h : EqOn v w W) : IsUnitMulExpNear Ω K w := by
  obtain ⟨H, hH, hH0, W', hW', hKW', ℓ, hℓ, heq⟩ := hv
  exact ⟨H, hH, hH0, W ∩ W', hW.inter hW', subset_inter hKW hKW', ℓ, hℓ.mono inter_subset_right,
    fun z hz ↦ (h hz.1).symm.trans (heq hz.2)⟩

private theorem IsUnitMulExpNear.mul {v w : ℂ → ℂ} (hv : IsUnitMulExpNear Ω K v)
    (hw : IsUnitMulExpNear Ω K w) : IsUnitMulExpNear Ω K fun z ↦ v z * w z := by
  obtain ⟨H₁, hH₁, hH₁0, W₁, hW₁, hKW₁, ℓ₁, hℓ₁, h₁⟩ := hv
  obtain ⟨H₂, hH₂, hH₂0, W₂, hW₂, hKW₂, ℓ₂, hℓ₂, h₂⟩ := hw
  refine ⟨fun z ↦ H₁ z * H₂ z, hH₁.mul hH₂, fun z hz ↦ mul_ne_zero (hH₁0 z hz) (hH₂0 z hz),
    W₁ ∩ W₂, hW₁.inter hW₂, subset_inter hKW₁ hKW₂, fun z ↦ ℓ₁ z + ℓ₂ z,
    (hℓ₁.mono inter_subset_left).add (hℓ₂.mono inter_subset_right), fun z hz ↦ ?_⟩
  have e₁ := h₁ hz.1
  have e₂ := h₂ hz.2
  simp only at e₁ e₂ ⊢
  rw [e₁, e₂, exp_add]
  ring

private theorem IsUnitMulExpNear.inv {v : ℂ → ℂ} (hv : IsUnitMulExpNear Ω K v) :
    IsUnitMulExpNear Ω K fun z ↦ (v z)⁻¹ := by
  obtain ⟨H, hH, hH0, W, hW, hKW, ℓ, hℓ, h⟩ := hv
  refine ⟨fun z ↦ (H z)⁻¹, hH.inv hH0, fun z hz ↦ inv_ne_zero (hH0 z hz), W, hW, hKW,
    fun z ↦ -ℓ z, hℓ.neg, fun z hz ↦ ?_⟩
  have e := h hz
  simp only at e ⊢
  rw [e, exp_neg, mul_inv]

private theorem isUnitMulExpNear_const {c : ℂ} (hc : c ≠ 0) :
    IsUnitMulExpNear Ω K fun _ ↦ c :=
  ⟨fun _ ↦ c, differentiableOn_const c, fun _ _ ↦ hc, univ, isOpen_univ, subset_univ K,
    fun _ ↦ 0, differentiableOn_const 0, fun z _ ↦ by simp⟩

private theorem isUnitMulExpNear_exp {W : Set ℂ} (hW : IsOpen W) (hKW : K ⊆ W) {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ W) : IsUnitMulExpNear Ω K fun z ↦ exp (ℓ z) :=
  ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ _ ↦ one_ne_zero, W, hW, hKW, ℓ, hℓ,
    fun z _ ↦ by simp⟩

/-- A linear factor whose root avoids `K` is, near `K`, a nowhere-zero holomorphic function on `Ω`
times an exponential: `z - a` with `a ∉ Ω` in the component of the root when that component is
bounded, and the constant `1` otherwise. -/
private theorem IsRungeCompactPair.isUnitMulExpNear_sub (hRunge : IsRungeCompactPair Ω K)
    {b : ℂ} (hb : b ∉ K) : IsUnitMulExpNear Ω K fun z ↦ z - b := by
  obtain ⟨hΩ, hK, hKΩ, hfill⟩ := isRungeCompactPair_iff.mp hRunge
  by_cases hbH : b ∈ filledHull K
  · obtain ⟨a, ha, haΩ⟩ := not_subset.mp
      ((isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset hK.isClosed hΩ
        hKΩ).mp hfill b ⟨hbH, hb⟩)
    have hba : b ∈ connectedComponentIn Kᶜ a := by
      rw [← connectedComponentIn_eq ha]
      exact mem_connectedComponentIn hb
    obtain ⟨W, hW, hKW, ℓ, hℓ, heq⟩ :=
      exists_eqOn_sub_mul_exp_of_mem_connectedComponentIn hK.isClosed hba
    exact ⟨fun z ↦ z - a, differentiableOn_id.sub_const a,
      fun z hz ↦ sub_ne_zero.mpr fun h ↦ haΩ (h ▸ hz), W, hW, hKW, ℓ, hℓ, heq⟩
  · obtain ⟨W, hW, hKW, ℓ, hℓ, heq⟩ := exists_eqOn_sub_exp_of_notMem_filledHull hK hbH
    exact (isUnitMulExpNear_exp hW hKW hℓ).congr hW hKW heq.symm

/-- A polynomial without zeros on `K` is, near `K`, a nowhere-zero holomorphic function on `Ω`
times an exponential: it is a product of linear factors with roots off `K`. -/
private theorem IsRungeCompactPair.isUnitMulExpNear_eval (hRunge : IsRungeCompactPair Ω K)
    (hKne : K.Nonempty) (p : ℂ[X]) (hp : ∀ z ∈ K, p.eval z ≠ 0) :
    IsUnitMulExpNear Ω K fun z ↦ p.eval z := by
  have hprod (s : Multiset ℂ) (hs : ∀ β ∈ s, β ∉ K) :
      IsUnitMulExpNear Ω K fun z ↦ (s.map fun β ↦ z - β).prod := by
    induction s using Multiset.induction_on with
    | empty => simpa using isUnitMulExpNear_const one_ne_zero
    | cons β s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (hRunge.isUnitMulExpNear_sub (hs β (Multiset.mem_cons_self β s))).mul
        (ih fun γ hγ ↦ hs γ (Multiset.mem_cons_of_mem hγ))
  have heval (z : ℂ) : p.eval z = p.leadingCoeff * (p.roots.map fun β ↦ z - β).prod :=
    (IsAlgClosed.splits p).eval_eq_prod_roots z
  obtain ⟨z₀, hz₀⟩ := hKne
  have hlc : p.leadingCoeff ≠ 0 := fun h ↦ hp z₀ hz₀ (by simp [heval, h])
  exact ((isUnitMulExpNear_const hlc).mul
    (hprod p.roots fun β hβ hβK ↦ hp β hβK (isRoot_of_mem_roots hβ))).congr isOpen_univ
    (subset_univ K) fun z _ ↦ (heval z).symm

/-- A rational function `∑ i, a i * (z - ζ i)⁻¹` with poles `ζ i ∉ K` and without zeros on `K` is,
near `K`, a nowhere-zero holomorphic function on `Ω` times an exponential: it is the quotient of two
polynomials without zeros on `K`. -/
private theorem IsRungeCompactPair.isUnitMulExpNear_sum_mul_inv_sub
    (hRunge : IsRungeCompactPair Ω K) (hKne : K.Nonempty) {N : ℕ} (ζ a : Fin N → ℂ)
    (hζ : ∀ i, ζ i ∉ K) (hr0 : ∀ z ∈ K, ∑ i, a i * (z - ζ i)⁻¹ ≠ 0) :
    IsUnitMulExpNear Ω K fun z ↦ ∑ i, a i * (z - ζ i)⁻¹ := by
  have hZ : IsOpen (range ζ)ᶜ := (finite_range ζ).isClosed.isOpen_compl
  have hKZ : K ⊆ (range ζ)ᶜ := by
    rintro z hz ⟨i, rfl⟩
    exact hζ i hz
  have hsub0 {z : ℂ} (hz : z ∈ (range ζ)ᶜ) (i : Fin N) : z - ζ i ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hz ⟨i, h.symm⟩
  let q : ℂ[X] := ∏ i, (X - C (ζ i))
  let p : ℂ[X] := ∑ i, C (a i) * ∏ k ∈ Finset.univ.erase i, (X - C (ζ k))
  have hq (z : ℂ) : q.eval z = ∏ i, (z - ζ i) := by simp [q, eval_prod]
  have hq0 {z : ℂ} (hz : z ∈ (range ζ)ᶜ) : q.eval z ≠ 0 := by
    rw [hq]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hsub0 hz i
  have hpq {z : ℂ} (hz : z ∈ (range ζ)ᶜ) :
      p.eval z = (∑ i, a i * (z - ζ i)⁻¹) * q.eval z := by
    simp only [p, hq, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ z - ζ k) (Finset.mem_univ i)]
    have := hsub0 hz i
    field_simp
  have hp0 (z : ℂ) (hz : z ∈ K) : p.eval z ≠ 0 := by
    rw [hpq (hKZ hz)]
    exact mul_ne_zero (hr0 z hz) (hq0 (hKZ hz))
  exact ((hRunge.isUnitMulExpNear_eval hKne p hp0).mul
    (hRunge.isUnitMulExpNear_eval hKne q fun z hz ↦ hq0 (hKZ hz)).inv).congr hZ hKZ
    fun z hz ↦ by simp only [hpq hz, mul_inv_cancel_right₀ (hq0 hz)]

/-- If `r` is near `K` a nowhere-zero holomorphic function on `Ω` times an exponential, then so is
every `u` holomorphic and nowhere zero near `K` with `‖u - r‖ < ‖u‖` on `K`: the quotient `r / u`
takes values in the disc of radius one about `1` near `K`, where the principal logarithm is
holomorphic. -/
private theorem IsUnitMulExpNear.of_norm_sub_lt {u r : ℂ → ℂ} (hr : IsUnitMulExpNear Ω K r)
    {W₀ : Set ℂ} (hW₀ : IsOpen W₀) (hKW₀ : K ⊆ W₀) (hu : DifferentiableOn ℂ u W₀)
    (hu0 : ∀ z ∈ W₀, u z ≠ 0) (hrd : DifferentiableOn ℂ r W₀)
    (hur : ∀ z ∈ K, ‖u z - r z‖ < ‖u z‖) : IsUnitMulExpNear Ω K u := by
  have hhd : DifferentiableOn ℂ (fun z ↦ r z / u z) W₀ := hrd.div hu hu0
  let W := W₀ ∩ (fun z ↦ r z / u z) ⁻¹' ball 1 1
  have hW : IsOpen W := hhd.continuousOn.isOpen_inter_preimage hW₀ isOpen_ball
  have hKW : K ⊆ W := fun z hz ↦ by
    refine ⟨hKW₀ hz, ?_⟩
    have hu0z : u z ≠ 0 := hu0 z (hKW₀ hz)
    rw [mem_preimage, mem_ball, dist_eq_norm, div_sub_one hu0z, norm_div,
      div_lt_one (norm_pos_iff.mpr hu0z), norm_sub_rev]
    exact hur z hz
  have hslit (z : ℂ) (hz : z ∈ W) : r z / u z ∈ slitPlane := ball_one_subset_slitPlane hz.2
  exact (hr.mul (isUnitMulExpNear_exp hW hKW ((hhd.mono inter_subset_left).clog hslit).neg)).congr
    hW hKW fun z hz ↦ by
      have hrz : r z ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero (hslit z hz))).1
      simp only [Pi.neg_apply, exp_neg, exp_log (slitPlane_ne_zero (hslit z hz)), inv_div]
      field_simp

/-- **Logarithmic factorization near a Runge compact.** Let `(Ω, K)` be a Runge compact pair and
let `u` be holomorphic on an open neighbourhood `U` of `K` and nowhere zero on `K`. Then there are
a function `H` holomorphic and nowhere zero on `Ω` and a function `ℓ` holomorphic on an open
neighbourhood `W` of `K` with `u = H * exp ℓ` on `W`. -/
theorem IsRungeCompactPair.exists_eqOn_mul_exp (hRunge : IsRungeCompactPair Ω K) {U : Set ℂ}
    (hU : IsOpen U) (hKU : K ⊆ U) {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u U)
    (hu0 : ∀ z ∈ K, u z ≠ 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ (∀ z ∈ Ω, H z ≠ 0) ∧
      ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ W ∧
        EqOn u (fun z ↦ H z * exp (ℓ z)) W := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨fun _ ↦ 1, differentiableOn_const 1, fun _ _ ↦ one_ne_zero, ∅, isOpen_empty,
      empty_subset _, fun _ ↦ 0, differentiableOn_empty, fun _ hz ↦ hz.elim⟩
  -- Shrink `U` to a neighbourhood `V` of `K` with compact closure on which `u` has no zeros.
  have hK := hRunge.isCompact
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK
    (hu.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton) fun z hz ↦ ⟨hKU hz, hu0 z hz⟩
  have hVU' : V ⊆ U := subset_closure.trans (hVU.trans inter_subset_left)
  have hV0 (z : ℂ) (hz : z ∈ V) : u z ≠ 0 := (hVU (subset_closure hz)).2
  obtain ⟨M, hM⟩ := hVc.exists_bound_of_continuousOn
    (hu.continuousOn.mono (hVU.trans inter_subset_left))
  -- Approximate `u` on `K` by a rational function `r` with poles `ζ i ∉ K` and error at most
  -- half the minimum `‖u z₀‖` of `‖u‖` on `K`.
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (hu.continuousOn.mono (hKV.trans hVU')).norm
  have hη : 0 < ‖u z₀‖ := norm_pos_iff.mpr (hu0 z₀ hz₀)
  have hMpos : 0 < M := hη.trans_le (hM z₀ (subset_closure (hKV hz₀)))
  obtain ⟨N, ζ, c, hζ, happrox⟩ := IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le.{0} hK hV
    hKV (ε := ‖u z₀‖ / 2 / M) (by positivity)
  let r : ℂ → ℂ := fun z ↦ ∑ i, c i * u (ζ i) * (z - ζ i)⁻¹
  have hur (z : ℂ) (hz : z ∈ K) : ‖u z - r z‖ < ‖u z‖ := by
    have h := happrox u M (hu.mono hVU') (fun z hz ↦ hM z (subset_closure hz)) z hz
    have hsum : ∑ i, (c i * (z - ζ i)⁻¹) • u (ζ i) = r z :=
      Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_right_comm]
    rw [hsum, div_mul_cancel₀ _ hMpos.ne'] at h
    linarith [isMinOn_iff.mp hmin z hz]
  have hr0 (z : ℂ) (hz : z ∈ K) : r z ≠ 0 := fun h ↦ by
    simpa [h] using hur z hz
  -- `r` factors, and `u / r` has a logarithm near `K`.
  have hZ : IsOpen (V ∩ (range ζ)ᶜ) := hV.inter (finite_range ζ).isClosed.isOpen_compl
  have hKZ : K ⊆ V ∩ (range ζ)ᶜ := fun z hz ↦ ⟨hKV hz, by
    rintro ⟨i, rfl⟩
    exact (hζ i).2 hz⟩
  have hrd : DifferentiableOn ℂ r (V ∩ (range ζ)ᶜ) :=
    DifferentiableOn.fun_sum fun i _ ↦ (differentiableOn_const _).mul
      ((differentiableOn_id.sub_const _).inv fun z hz ↦ sub_ne_zero.mpr fun h ↦ hz.2 ⟨i, h.symm⟩)
  exact (hRunge.isUnitMulExpNear_sum_mul_inv_sub hKne ζ (fun i ↦ c i * u (ζ i))
    (fun i ↦ (hζ i).2) hr0).of_norm_sub_lt hZ hKZ (hu.mono (inter_subset_left.trans hVU'))
    (fun z hz ↦ hV0 z hz.1) hrd hur

/-- **Zero-free Runge approximation.** Let `(Ω, K)` be a Runge compact pair and let `u` be
holomorphic on an open neighbourhood `U` of `K` and nowhere zero on `K`. Then `u` is uniformly
approximable on `K` by functions holomorphic and nowhere zero on all of `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_ne_zero_norm_sub_lt
    (hRunge : IsRungeCompactPair Ω K) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ K, u z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, g z ≠ 0) ∧ ∀ z ∈ K, ‖u z - g z‖ < ε := by
  -- Write `u = H * exp ℓ` near `K` and approximate the exponent `ℓ` by scalar Runge.
  obtain ⟨H, hH, hH0, W, hW, hKW, ℓ, hℓ, heq⟩ := hRunge.exists_eqOn_mul_exp hU hKU hu hu0
  obtain ⟨M, hM⟩ := hRunge.isCompact.exists_bound_of_continuousOn (hu.continuousOn.mono hKU)
  have hB : 0 < |M| + 1 := by positivity
  obtain ⟨L, hL, hLℓ⟩ := hRunge.exists_differentiableOn_norm_sub_lt hW hKW hℓ
    (ε := min 1 (ε / (2 * (|M| + 1)))) (by positivity)
  refine ⟨fun z ↦ H z * exp (L z), hH.mul hL.cexp,
    fun z hz ↦ mul_ne_zero (hH0 z hz) (exp_ne_zero _), fun z hz ↦ ?_⟩
  have hd : ‖L z - ℓ z‖ < min 1 (ε / (2 * (|M| + 1))) := by
    rw [norm_sub_rev]
    exact hLℓ z hz
  have hsplit : u z - H z * exp (L z) = -u z * (exp (L z - ℓ z) - 1) := by
    have e := heq (hKW hz)
    simp only at e
    rw [e, exp_sub]
    field_simp
    ring
  calc ‖u z - H z * exp (L z)‖ = ‖u z‖ * ‖exp (L z - ℓ z) - 1‖ := by
        rw [hsplit, norm_mul, norm_neg]
    _ ≤ (|M| + 1) * (2 * ‖L z - ℓ z‖) :=
        mul_le_mul ((hM z hz).trans ((le_abs_self M).trans (by linarith)))
          (norm_exp_sub_one_le (hd.le.trans (min_le_left _ _))) (norm_nonneg _) hB.le
    _ < (|M| + 1) * (2 * (ε / (2 * (|M| + 1)))) := by
        gcongr
        exact hd.trans_le (min_le_right _ _)
    _ = ε := by field_simp

end TauCeti
