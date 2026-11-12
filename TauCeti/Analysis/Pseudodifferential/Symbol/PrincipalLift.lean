/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Continuous lifts of principal symbols

Every homogeneous symbol `a` of degree `m` on `ℝⁿ` is the principal symbol of a classical symbol
of order `m`, namely of its cut-off term `χ(ξ) a(x, ξ)` for a frequency cutoff `χ`
(`TauCeti.ClassicalSymbol.ofHomogeneous`). This file shows that this lift is continuous, so that
continuous families and homotopies of principal symbols lift to continuous families of full
symbols, with a prescribed full symbol at one parameter value.

The homogeneous symbols of degree `m` carry the C^∞ topology on compact sets of positions times
the unit sphere of frequencies: for a compact set `K` and words `α`, `β` of coordinate indices,
the seminorm `TauCeti.HomogeneousSymbol.seminorm K α β a` is the best constant `C` in

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for `x ∈ K` and `ξ ≠ 0`.

Since `∂_x^α ∂_ξ^β a` is homogeneous of degree `m - |β|`, this is the supremum of
`‖∂_x^α ∂_ξ^β a(x, ξ)‖` over `x ∈ K` and `‖ξ‖ = 1`
(`TauCeti.HomogeneousSymbol.seminorm_le_iff_norm_eq_one`).

## Main results

* `TauCeti.HomogeneousSymbol.seminorm`, `TauCeti.HomogeneousSymbol.withSeminorms`: the seminorms
  and the locally convex topology they induce on the homogeneous symbols of degree `m`; it is
  Hausdorff (`TauCeti.HomogeneousSymbol.instT1Space`).
* `TauCeti.HomogeneousSymbol.exists_seminorm_cutoffSymbol_le`: the seminorm `p_{K,α,β}` of the
  cut-off term `χ(ξ) a(x, ξ)` in the symbol class `S^m_{1,0}` is bounded by finitely many
  seminorms `p_{K,α,β'}(a)` with `|β'| ≤ |β|`, with a constant depending only on `χ`, `m` and `β`.
* `TauCeti.HomogeneousSymbol.cutoffSymbolCLM`: the cut-off term as a continuous linear map from
  the homogeneous symbols of degree `m` to the symbols of order `m`.
* `TauCeti.ClassicalSymbol.replacePrincipal`: the classical symbol `b + χ(ξ) (a - b_m)(x, ξ)`
  obtained from `b` by replacing its principal symbol with `a`. It keeps the lower order terms
  and, for the same cutoff, the remainders after `N ≥ 1` terms
  (`TauCeti.ClassicalSymbol.term_replacePrincipal_succ`,
  `TauCeti.ClassicalSymbol.remainder_replacePrincipal_succ`), and its full symbol depends
  continuously on `a` (`TauCeti.ClassicalSymbol.continuous_toSymbol_replacePrincipal`).
* `TauCeti.ClassicalSymbol.exists_lift_of_continuous`: **continuous lifts with a prescribed
  initial value.** A continuous family `t ↦ a_t` of homogeneous symbols of degree `m` is the
  family of principal symbols of classical symbols `b_t` whose full symbols depend continuously
  on `t`, with `b_{t₀}` any prescribed classical symbol with principal symbol `a_{t₀}`.

## Implementation notes

A homogeneous symbol is not smooth at the zero frequency, so the Leibniz rule for the cut-off
term is applied, near a frequency `ξ₀ ≠ 0`, to the smooth function `ψ(ξ) a(x, ξ)`, where `ψ` is a
dilated frequency cutoff equal to `1` near `ξ₀` and to `0` near the zero frequency; it has the same
mixed derivatives as `a` at `ξ₀`. The derivatives of `χ` of positive order vanish outside the
annulus `1 ≤ ‖ξ‖ ≤ 2`, where `‖ξ‖` and `⟨ξ⟩` are comparable, and `χ` itself vanishes on the unit
ball.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2: the quantization of
  principal symbols by frequency cutoffs.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology
open TopologicalSpace (Compacts)
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-! ### Smooth functions with the mixed derivatives of a homogeneous symbol -/

section Localize

/-- The product `ψ(ξ) a(x, ξ)` of a homogeneous symbol with a dilated frequency cutoff `ψ`, equal to
`1` near `ξ₀` and to `0` near the zero frequency: a smooth function with the same germ as `a` at
every `(x, ξ₀)` with `ξ₀ ≠ 0`. -/
private def localize (ξ₀ : CoordinateSpace n)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
  fun p => (default : FrequencyCutoff (CoordinateSpace n)) ((‖ξ₀‖ / 4)⁻¹ • p.2) • a.coefficient p

private theorem contDiff_localize (ξ₀ : CoordinateSpace n)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ContDiff ℝ ∞ (localize ξ₀ a) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases eq_or_ne p.2 0 with h | h
  · -- Near the zero frequency the dilated cutoff, hence the product, vanishes identically.
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    exact FrequencyCutoff.comp_inv_smul_snd_smul_eventuallyEq_zero default (‖ξ₀‖ / 4)
      a.coefficient (by simp [h])
  · exact ((FrequencyCutoff.contDiff_comp_inv_smul_snd _ _).contDiffAt).smul
      (a.contDiffAt_coefficient h)

private theorem localize_eventuallyEq {ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (x : CoordinateSpace n) :
    localize ξ₀ a =ᶠ[𝓝 (x, ξ₀)] a.coefficient := by
  have hn : 0 < ‖ξ₀‖ := norm_pos_iff.2 hξ₀
  have h2 : 2 < ‖(‖ξ₀‖ / 4)⁻¹ • ξ₀‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_div, div_mul_cancel₀ _ hn.ne']
    norm_num
  have hc : Continuous fun q : CoordinateSpace n × CoordinateSpace n => (‖ξ₀‖ / 4)⁻¹ • q.2 := by
    fun_prop
  filter_upwards [((default : FrequencyCutoff (CoordinateSpace n)).eventuallyEq_one_of_two_lt_norm
    h2).comp_tendsto hc.continuousAt] with q hq
  simp only [Function.comp_apply, Pi.one_apply] at hq
  simp only [localize, hq, one_smul]

private theorem localize_add (ξ₀ : CoordinateSpace n)
    (a b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    localize ξ₀ (a + b) = localize ξ₀ a + localize ξ₀ b := by
  funext p
  simp [localize, smul_add]

/-- At a nonzero frequency, the mixed derivatives of homogeneous symbols are additive. -/
private theorem mixedDeriv_coefficient_add
    (a b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (α β : List (Fin n))
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    mixedDeriv α β (a + b).coefficient x ξ =
      mixedDeriv α β a.coefficient x ξ + mixedDeriv α β b.coefficient x ξ := by
  rw [← (localize_eventuallyEq hξ (a + b) x).mixedDeriv_eq,
    ← (localize_eventuallyEq hξ a x).mixedDeriv_eq, ← (localize_eventuallyEq hξ b x).mixedDeriv_eq,
    localize_add, mixedDeriv_add (contDiff_localize ξ a) (contDiff_localize ξ b)]

end Localize

/-! ### The seminorms -/

section Seminorm

/-- The admissible constants in the estimate of `∂_x^α ∂_ξ^β a` on `K`. -/
private def bounds (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤ c * ‖ξ‖ ^ (m - β.length)}

private theorem bounds_nonempty (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (bounds K α β a).Nonempty :=
  let ⟨C, hC, h⟩ := a.exists_norm_mixedDeriv_le K.isCompact α β
  ⟨C, hC, h⟩

/-- The best constant in the estimate of `∂_x^α ∂_ξ^β a` on `K`. -/
private def seminormAux (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) : ℝ :=
  sInf (bounds K α β a)

private theorem seminormAux_nonneg (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    0 ≤ seminormAux K α β a :=
  le_csInf (bounds_nonempty K α β a) fun _ hc => hc.1

private theorem le_seminormAux (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤ seminormAux K α β a * ‖ξ‖ ^ (m - β.length) := by
  have hw : 0 < ‖ξ‖ ^ (m - β.length) := Real.rpow_pos_of_pos (norm_pos_iff.2 hξ) _
  rw [← div_le_iff₀ hw]
  exact le_csInf (bounds_nonempty K α β a) fun c hc => (div_le_iff₀ hw).2 (hc.2 x hx ξ hξ)

private theorem seminormAux_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length)) :
    seminormAux K α β a ≤ C :=
  csInf_le ⟨0, fun _ hc => hc.1⟩ ⟨hC, h⟩

/-- The seminorm `p_{K,α,β}` on the homogeneous symbols of degree `m`: the best constant `C` in
the estimate `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for all positions `x ∈ K` and all
nonzero frequencies `ξ`. It is the supremum of `‖∂_x^α ∂_ξ^β a‖` over `K` times the unit sphere
(`HomogeneousSymbol.seminorm_le_iff_norm_eq_one`). -/
protected def seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    Seminorm ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  Seminorm.ofSMulLE (seminormAux K α β)
    (le_antisymm (seminormAux_le_bound K α β 0 le_rfl fun _ _ _ _ => by simp)
      (seminormAux_nonneg K α β 0))
    (fun a b => seminormAux_le_bound K α β _
      (add_nonneg (seminormAux_nonneg K α β a) (seminormAux_nonneg K α β b)) fun x hx ξ hξ => by
        rw [mixedDeriv_coefficient_add a b α β x hξ, add_mul]
        exact (norm_add_le _ _).trans
          (add_le_add (le_seminormAux K α β a hx hξ) (le_seminormAux K α β b hx hξ)))
    (fun c a => seminormAux_le_bound K α β _
      (mul_nonneg (norm_nonneg c) (seminormAux_nonneg K α β a)) fun x hx ξ hξ => by
        rw [coefficient_smul, mixedDeriv_const_smul, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_seminormAux K α β a hx hξ) (norm_nonneg c))

/-- The seminorm `p_{K,α,β}(a)` bounds `‖∂_x^α ∂_ξ^β a(x, ξ)‖ / ‖ξ‖ ^ (m - |β|)` for `x ∈ K`
and `ξ ≠ 0`. -/
theorem le_seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      HomogeneousSymbol.seminorm K α β a * ‖ξ‖ ^ (m - β.length) :=
  le_seminormAux K α β a hx hξ

/-- A constant in the estimate of `∂_x^α ∂_ξ^β a` on `K` bounds the seminorm `p_{K,α,β}(a)`. -/
theorem seminorm_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length)) :
    HomogeneousSymbol.seminorm K α β a ≤ C :=
  seminormAux_le_bound K α β a hC h

/-- The seminorm `p_{K,α,β}(a)` is at most `C ≥ 0` exactly when `C` is a constant in the estimate
of `∂_x^α ∂_ξ^β a` on `K`. -/
theorem seminorm_le_iff {K : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} {C : ℝ} (hC : 0 ≤ C) :
    HomogeneousSymbol.seminorm K α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length) := by
  refine ⟨fun h x hx ξ hξ => (le_seminorm K α β a hx hξ).trans ?_, seminorm_le_bound K α β a hC⟩
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (norm_nonneg ξ) _)

/-- **The seminorms are the C^∞ seminorms on the unit sphere.** The seminorm `p_{K,α,β}(a)` is at
most `C ≥ 0` exactly when `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C` for `x ∈ K` and `‖ξ‖ = 1`. -/
theorem seminorm_le_iff_norm_eq_one {K : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} {C : ℝ} (hC : 0 ≤ C) :
    HomogeneousSymbol.seminorm K α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ, ‖ξ‖ = 1 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C := by
  rw [seminorm_le_iff hC]
  refine ⟨fun h x hx ξ hξ => by simpa [hξ] using h x hx ξ (norm_ne_zero_iff.1 (by simp [hξ])),
    fun h x hx ξ hξ => ?_⟩
  -- Rescale `ξ` to the unit sphere and use the homogeneity of `∂_x^α ∂_ξ^β a`.
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hs : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hξ' : ξ = ‖ξ‖ • ‖ξ‖⁻¹ • ξ := (smul_inv_smul₀ hn.ne' ξ).symm
  have hu : ‖ξ‖⁻¹ • ξ ≠ 0 := norm_ne_zero_iff.1 (by rw [hs]; exact one_ne_zero)
  rw [hξ', mixedDeriv_coefficient_smul_frequency a α β x hu hn, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hn.le _), ← hξ', mul_comm]
  exact mul_le_mul_of_nonneg_right (h x hx _ hs) (Real.rpow_nonneg hn.le _)

end Seminorm

/-! ### The topology -/

section Topology

variable (n V W m) in
/-- The family of all seminorms `p_{K,α,β}` on the homogeneous symbols of degree `m`, indexed by
the compact sets `K` of positions and the words `α`, `β` of coordinate indices. -/
def seminormFamily :
    SeminormFamily ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
      (Compacts (CoordinateSpace n) × List (Fin n) × List (Fin n)) :=
  fun i => HomogeneousSymbol.seminorm i.1 i.2.1 i.2.2

@[simp]
theorem seminormFamily_apply (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    seminormFamily n V W m (K, α, β) = HomogeneousSymbol.seminorm K α β := (rfl)

/-- The topology of the homogeneous symbols of degree `m`: the locally convex topology of the
seminorms `p_{K,α,β}`, that is, of uniform convergence of all mixed derivatives on compact sets of
positions times the unit sphere of frequencies. -/
instance instTopologicalSpace :
    TopologicalSpace (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  (seminormFamily n V W m).moduleFilterBasis.topology'

/-- The topology of the homogeneous symbols is induced by the seminorms `p_{K,α,β}`. -/
theorem withSeminorms : WithSeminorms (seminormFamily n V W m) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup :
    IsTopologicalAddGroup (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  (seminormFamily n V W m).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul :
    ContinuousSMul ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  withSeminorms.continuousSMul

instance instLocallyConvexSpace :
    LocallyConvexSpace ℝ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  withSeminorms.toLocallyConvexSpace

/-- The homogeneous symbols form a T1, hence Hausdorff, space: the seminorms `p_{K,[],[]}` over
the singletons `K = {x}` separate them. -/
instance instT1Space :
    T1Space (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) := by
  refine withSeminorms.T1_of_separating fun a ha => ?_
  obtain ⟨x, ξ, hξ, hxξ⟩ : ∃ x ξ, ξ ≠ 0 ∧ a.coefficient (x, ξ) ≠ 0 := by
    by_contra! h
    exact ha (ext_of_ne_zero fun x ξ hξ => by simpa using h x ξ hξ)
  refine ⟨({x}, [], []), fun h0 => hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := le_seminorm {x} [] [] a rfl hξ
  rwa [← seminormFamily_apply, h0, zero_mul, mixedDeriv_nil_nil] at h

end Topology

/-! ### The cut-off term depends continuously on the homogeneous symbol -/

section Cutoff

/-- On the region `1 ≤ ‖ξ‖`, a derivative of order `i ≤ k` of a frequency cutoff, times the weight
`‖ξ‖ ^ (m - (k - i))` of the remaining frequency derivatives, is bounded by the weight
`⟨ξ⟩ ^ (m - k)`: the derivatives of positive order vanish outside the annulus `1 ≤ ‖ξ‖ ≤ 2`. -/
private theorem norm_iteratedFDeriv_mul_rpow_le (χ : FrequencyCutoff (CoordinateSpace n))
    {i k : ℕ} (hik : i ≤ k) {B : ℝ} (hB : ∀ η, ‖iteratedFDeriv ℝ i χ η‖ ≤ B) (m : ℝ)
    {ξ : CoordinateSpace n} (hξ : 1 ≤ ‖ξ‖) :
    ‖iteratedFDeriv ℝ i χ ξ‖ * ‖ξ‖ ^ (m - ↑(k - i)) ≤
      B * (2 ^ k * 2 ^ (|m - k| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) := by
  have hn : 0 < ‖ξ‖ := one_pos.trans_le hξ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ξ)
  have hpow : ‖ξ‖ ^ (m - ↑(k - i)) = ‖ξ‖ ^ (m - k) * ‖ξ‖ ^ i := by
    rw [Nat.cast_sub hik, ← Real.rpow_natCast, ← Real.rpow_add hn]
    ring_nf
  have hw := norm_rpow_le_one_add_norm_sq_rpow hξ (m - k)
  by_cases hD : iteratedFDeriv ℝ i χ ξ = 0
  · rw [hD, norm_zero, zero_mul]
    positivity
  -- A nonzero derivative of positive order forces `‖ξ‖ < 2`, so `‖ξ‖ ^ i ≤ 2 ^ k` in all cases.
  have hi : ‖ξ‖ ^ i ≤ 2 ^ k := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using one_le_pow₀ (one_le_two : (1 : ℝ) ≤ 2)
    · have h2 : ‖ξ‖ < 2 := lt_of_not_ge fun h =>
        hD (χ.iteratedFDeriv_eq_zero_of_two_le_norm hi.ne' h)
      exact (pow_le_pow_left₀ hn.le h2.le i).trans (pow_le_pow_right₀ one_le_two hik)
  rw [hpow]
  calc ‖iteratedFDeriv ℝ i χ ξ‖ * (‖ξ‖ ^ (m - k) * ‖ξ‖ ^ i)
      ≤ B * (2 ^ (|m - k| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) * 2 ^ k) := by
        gcongr
        exact hB ξ
    _ = B * (2 ^ k * 2 ^ (|m - k| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2)) := by ring

/-- **Seminorm estimate for the cut-off term.** For a frequency cutoff `χ`, the seminorm
`p_{K,α,β}` of the symbol `χ(ξ) a(x, ξ)` of order `m` is at most a constant times the sum of the
seminorms `p_{K,α,β'}(a)` of the homogeneous symbol `a` over all words `β'` with `|β'| ≤ |β|`.
The constant depends only on `χ`, `m` and `β`. -/
theorem exists_seminorm_cutoffSymbol_le (χ : FrequencyCutoff (CoordinateSpace n))
    (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m,
      Symbol.seminorm K α β (cutoffSymbol χ a) ≤
        C * ∑ i ∈ Finset.range (β.length + 1), ∑ w : Fin (β.length - i) → Fin n,
          HomogeneousSymbol.seminorm K α (List.ofFn w) a := by
  set k := β.length
  choose B hB using fun i => χ.exists_bound_iteratedFDeriv (E := CoordinateSpace n) i
  have hB0 (i : ℕ) : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
  set D : ℝ := 2 ^ k * 2 ^ (|m - k| / 2)
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * D,
    Finset.sum_nonneg fun i _ => by have := hB0 i; positivity, fun a => ?_⟩
  set S := ∑ i ∈ Finset.range (k + 1), ∑ w : Fin (k - i) → Fin n,
    HomogeneousSymbol.seminorm K α (List.ofFn w) a
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  refine Symbol.seminorm_le_bound K α β _
    (mul_nonneg (Finset.sum_nonneg fun i _ => by have := hB0 i; positivity) hS) fun x hx ξ => ?_
  rcases lt_or_ge ‖ξ‖ 1 with hξ | hξ
  · -- On the unit ball the cut-off term vanishes near `(x, ξ)`.
    have h0 : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [continuous_snd.continuousAt.eventually
        (χ.eventuallyEq_zero_of_norm_lt_one hξ)] with q hq
      simp [hq]
    rw [h0.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => by have := hB0 i; positivity) hS)
      (rpow_weight_pos ξ _).le
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (one_pos.trans_le hξ)
  -- Near `(x, ξ)`, replace `a` by the smooth function `localize ξ a` and apply the Leibniz rule.
  have heq : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] fun p => χ p.2 • localize ξ a p := by
    filter_upwards [localize_eventuallyEq hξ0 a x] with q hq
    rw [coefficient_cutoffSymbol, hq]
  rw [heq.mixedDeriv_eq]
  refine (norm_mixedDeriv_comp_snd_smul_le χ.contDiff (contDiff_localize ξ a) α β x ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  -- The frequency derivatives of `a` of order `k - i`.
  have hsum : ∑ w : Fin (k - i) → Fin n, ‖mixedDeriv α (List.ofFn w) (localize ξ a) x ξ‖ ≤
      S * ‖ξ‖ ^ (m - ↑(k - i)) := by
    calc ∑ w : Fin (k - i) → Fin n, ‖mixedDeriv α (List.ofFn w) (localize ξ a) x ξ‖
        ≤ ∑ w : Fin (k - i) → Fin n,
            HomogeneousSymbol.seminorm K α (List.ofFn w) a * ‖ξ‖ ^ (m - ↑(k - i)) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [(localize_eventuallyEq hξ0 a x).mixedDeriv_eq]
          simpa using le_seminorm K α (List.ofFn w) a hx hξ0
      _ = (∑ w : Fin (k - i) → Fin n, HomogeneousSymbol.seminorm K α (List.ofFn w) a) *
            ‖ξ‖ ^ (m - ↑(k - i)) := (Finset.sum_mul ..).symm
      _ ≤ S * ‖ξ‖ ^ (m - ↑(k - i)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg ξ) _)
          exact Finset.single_le_sum (f := fun i => ∑ w : Fin (k - i) → Fin n,
            HomogeneousSymbol.seminorm K α (List.ofFn w) a)
            (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) hi
  have hχ := norm_iteratedFDeriv_mul_rpow_le χ hik (hB i) m hξ
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ ξ‖ *
        ∑ w : Fin (k - i) → Fin n, ‖mixedDeriv α (List.ofFn w) (localize ξ a) x ξ‖
      ≤ (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ ξ‖ * (S * ‖ξ‖ ^ (m - ↑(k - i))) := by
        gcongr
    _ = (k.choose i : ℝ) * S * (‖iteratedFDeriv ℝ i χ ξ‖ * ‖ξ‖ ^ (m - ↑(k - i))) := by ring
    _ ≤ (k.choose i : ℝ) * S * (B i * (D * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))) := by
        gcongr
    _ = (k.choose i : ℝ) * B i * D * S * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) := by ring

variable (V W m) in
/-- **Continuity of the cut-off term.** The symbol `χ(ξ) a(x, ξ)` of order `m` depends
continuously on the homogeneous symbol `a` of degree `m`. -/
theorem continuous_cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n)) :
    Continuous (cutoffSymbol (V := V) (W := W) (m := m) χ) := by
  refine WithSeminorms.continuous_of_isBounded withSeminorms Symbol.withSeminorms _
    (.of_real fun ⟨K, α, β⟩ => ?_)
  classical
  obtain ⟨C, hC, h⟩ := exists_seminorm_cutoffSymbol_le (V := V) (W := W) (m := m) χ K α β
  set k := β.length
  -- The finitely many seminorms `p_{K,α,β'}` with `|β'| ≤ |β|`, and their number.
  let s : Finset (Compacts (CoordinateSpace n) × List (Fin n) × List (Fin n)) :=
    (Finset.range (k + 1)).biUnion fun i =>
      Finset.univ.image fun w : Fin (k - i) → Fin n => (K, α, List.ofFn w)
  set N : ℝ := ∑ i ∈ Finset.range (k + 1), (Fintype.card (Fin (k - i) → Fin n) : ℝ)
  refine ⟨s, C * N, fun a => ?_⟩
  rw [Symbol.seminormFamily_apply, mul_assoc]
  refine (h a).trans (mul_le_mul_of_nonneg_left ?_ hC)
  calc ∑ i ∈ Finset.range (k + 1), ∑ w : Fin (k - i) → Fin n,
        HomogeneousSymbol.seminorm K α (List.ofFn w) a
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ _w : Fin (k - i) → Fin n,
          (s.sup (seminormFamily n V W m)) a := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => ?_
        rw [← seminormFamily_apply]
        exact Seminorm.le_finset_sup_apply
          (Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩⟩)
    _ = N * (s.sup (seminormFamily n V W m)) a := by
        simp [N, Finset.sum_mul, Finset.card_univ]

/-- The cut-off term `a ↦ χ(ξ) a(x, ξ)` as a continuous linear map from the homogeneous symbols of
degree `m` to the symbols of order `m`. -/
def cutoffSymbolCLM (χ : FrequencyCutoff (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →L[ℂ] Symbol n V W m where
  toLinearMap := cutoffSymbol χ
  cont := continuous_cutoffSymbol V W m χ

@[simp]
theorem cutoffSymbolCLM_apply (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    cutoffSymbolCLM χ a = cutoffSymbol χ a := (rfl)

end Cutoff

end HomogeneousSymbol

/-! ### Replacing the principal symbol of a classical symbol -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n)) (b : ClassicalSymbol n V W m)
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

/-- The classical symbol obtained from `b` by replacing its principal symbol with `a`:
`b + χ(ξ) (a - b_m)(x, ξ)`. It has principal symbol `a` and the lower order terms of `b`. -/
def replacePrincipal : ClassicalSymbol n V W m :=
  b + ofHomogeneous χ (a - b.principal)

@[simp]
theorem toSymbol_replacePrincipal :
    (b.replacePrincipal χ a).toSymbol = b.toSymbol + cutoffSymbol χ (a - b.principal) := by
  simp [replacePrincipal]

@[simp]
theorem principal_replacePrincipal : (b.replacePrincipal χ a).principal = a := by
  simp [replacePrincipal, principal_add]

@[simp]
theorem term_replacePrincipal_succ (j : ℕ) :
    (b.replacePrincipal χ a).term (j + 1) = b.term (j + 1) := by
  simp [replacePrincipal]

/-- Replacing the principal symbol does not change the remainders after `N ≥ 1` terms for the
cutoff `χ` used in the replacement. -/
theorem remainder_replacePrincipal_succ (N : ℕ) :
    (b.replacePrincipal χ a).remainder χ (N + 1) = b.remainder χ (N + 1) := by
  ext1
  funext p
  have h0 : ((b.replacePrincipal χ a).term 0).coefficient p = a.coefficient p := by
    rw [← coefficient_principal, principal_replacePrincipal]
  rw [coefficient_remainder, coefficient_remainder, Finset.sum_range_succ',
    Finset.sum_range_succ', h0]
  simp [← coefficient_principal]
  abel

@[simp]
theorem replacePrincipal_principal : b.replacePrincipal χ b.principal = b := by
  simp [replacePrincipal]

/-- The full symbol of `b.replacePrincipal χ a` depends continuously on `a`. -/
theorem continuous_toSymbol_replacePrincipal :
    Continuous fun a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m =>
      (b.replacePrincipal χ a).toSymbol := by
  simp only [toSymbol_replacePrincipal]
  exact continuous_const.add
    ((continuous_cutoffSymbol V W m χ).comp (continuous_id.sub continuous_const))

/-- **Continuous lifts of principal symbols with a prescribed initial value.** Let `t ↦ a_t` be a
continuous family of homogeneous symbols of degree `m`, and `b₀` a classical symbol whose principal
symbol is `a_{t₀}`. Then there are classical symbols `b_t` with principal symbols `a_t`, full
symbols depending continuously on `t`, and `b_{t₀} = b₀`; their lower order terms do not depend on
`t`. -/
theorem exists_lift_of_continuous {T : Type*} [TopologicalSpace T]
    {a : T → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (ha : Continuous a)
    {t₀ : T} {b₀ : ClassicalSymbol n V W m} (hb₀ : b₀.principal = a t₀) :
    ∃ b' : T → ClassicalSymbol n V W m, Continuous (fun t => (b' t).toSymbol) ∧
      (∀ t, (b' t).principal = a t) ∧ b' t₀ = b₀ ∧ ∀ t j, (b' t).term (j + 1) = b₀.term (j + 1) :=
  have χ : FrequencyCutoff (CoordinateSpace n) := default
  ⟨fun t => b₀.replacePrincipal χ (a t), (continuous_toSymbol_replacePrincipal χ b₀).comp ha,
    fun t => principal_replacePrincipal χ b₀ (a t), by simp [← hb₀],
    fun t j => term_replacePrincipal_succ χ b₀ (a t) j⟩

end ClassicalSymbol

end TauCeti
