/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Seminorm.WeightedSup
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The topology of the homogeneous symbols

The homogeneous symbols of degree `m` on `ℝⁿ` carry the C^∞ topology on compact sets of positions
times the unit sphere of frequencies: for a compact set `K` and words `α`, `β` of coordinate
indices, the seminorm `TauCeti.HomogeneousSymbol.seminorm K α β a` is the best constant `C` in

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for `x ∈ K` and `ξ ≠ 0`.

Since `∂_x^α ∂_ξ^β a` is homogeneous of degree `m - |β|`, this is the supremum of
`‖∂_x^α ∂_ξ^β a(x, ξ)‖` over `x ∈ K` and `‖ξ‖ = 1`
(`TauCeti.HomogeneousSymbol.seminorm_le_iff_norm_eq_one`). The cut-off term `χ(ξ) a(x, ξ)`, which
lifts a homogeneous symbol to a symbol of order `m`, depends continuously on `a` in this topology.

## Main results

* `TauCeti.HomogeneousSymbol.seminorm`, `TauCeti.HomogeneousSymbol.withSeminorms`: the seminorms
  and the locally convex topology they induce on the homogeneous symbols of degree `m`; it is
  Hausdorff (`TauCeti.HomogeneousSymbol.instT1Space`).
* `TauCeti.HomogeneousSymbol.exists_seminorm_cutoffSymbol_le`: the seminorm `p_{K,α,β}` of the
  cut-off term `χ(ξ) a(x, ξ)` in the symbol class `S^m_{1,0}` is bounded by finitely many
  seminorms `p_{K,α,β'}(a)` with `|β'| ≤ |β|`, with a constant depending only on `χ`, `m` and `β`.
* `TauCeti.HomogeneousSymbol.cutoffSymbolCLM`: the cut-off term as a continuous linear map from
  the homogeneous symbols of degree `m` to the symbols of order `m`.

## Implementation notes

The seminorms are the best constants `Seminorm.weightedSup` of the weighted estimates above, like
the seminorms `TauCeti.Symbol.seminorm` of the symbol classes.

A homogeneous symbol is not smooth at the zero frequency, so the Leibniz rule for the cut-off
term is applied, near a frequency `ξ₀ ≠ 0`, to a smooth function with the same germ as `a`
(`TauCeti.HomogeneousSymbol.exists_contDiff_eventuallyEq_coefficient`). The derivatives of `χ` of
positive order vanish outside the annulus `1 ≤ ‖ξ‖ ≤ 2`, where `‖ξ‖` and `⟨ξ⟩` are comparable,
and `χ` itself vanishes on the unit ball.

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2: the quantization of
  principal symbols by frequency cutoffs.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology
open TopologicalSpace (Compacts)

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-! ### The seminorms -/

section Seminorm

/-- The mixed derivative `a ↦ ∂_x^α ∂_ξ^β a(x, ξ)` at a nonzero frequency, as a linear map. -/
private def mixedDerivLinearMap (α β : List (Fin n)) (x : CoordinateSpace n)
    (ξ : {ξ : CoordinateSpace n // ξ ≠ 0}) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] V →L[ℂ] W where
  toFun a := mixedDeriv α β a.coefficient x ξ
  map_add' a b := mixedDeriv_coefficient_add a b α β x ξ.2
  map_smul' c a := by
    rw [coefficient_smul, mixedDeriv_const_smul, RingHom.id_apply]

/-- The seminorm `p_{K,α,β}` on the homogeneous symbols of degree `m`: the best constant `C` in
the estimate `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` for all positions `x ∈ K` and all
nonzero frequencies `ξ`. It is the supremum of `‖∂_x^α ∂_ξ^β a‖` over `K` times the unit sphere
(`HomogeneousSymbol.seminorm_le_iff_norm_eq_one`). -/
protected def seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    Seminorm ℂ (HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :=
  Seminorm.weightedSup
    (fun i : K × {ξ : CoordinateSpace n // ξ ≠ 0} => mixedDerivLinearMap α β i.1 i.2)
    (fun i => ‖(i.2 : CoordinateSpace n)‖ ^ (m - β.length))
    (fun i => Real.rpow_pos_of_pos (norm_pos_iff.2 i.2.2) _)

/-- Every homogeneous symbol satisfies the weighted estimates defining
`HomogeneousSymbol.seminorm K α β`. -/
private theorem exists_bound_mixedDerivLinearMap (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ∃ C, ∀ i : K × {ξ : CoordinateSpace n // ξ ≠ 0},
      ‖mixedDerivLinearMap α β i.1 i.2 a‖ ≤ C * ‖(i.2 : CoordinateSpace n)‖ ^ (m - β.length) :=
  let ⟨C, _, h⟩ := a.exists_norm_mixedDeriv_le K.isCompact α β
  ⟨C, fun i => h i.1 i.1.2 i.2 i.2.2⟩

/-- The seminorm `p_{K,α,β}(a)` bounds `‖∂_x^α ∂_ξ^β a(x, ξ)‖ / ‖ξ‖ ^ (m - |β|)` for `x ∈ K`
and `ξ ≠ 0`. -/
theorem le_seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      HomogeneousSymbol.seminorm K α β a * ‖ξ‖ ^ (m - β.length) :=
  Seminorm.norm_le_weightedSup
    (fun i : K × {ξ : CoordinateSpace n // ξ ≠ 0} => mixedDerivLinearMap α β i.1 i.2) _ _
    (exists_bound_mixedDerivLinearMap K α β) a (⟨x, hx⟩, ⟨ξ, hξ⟩)

/-- A constant in the estimate of `∂_x^α ∂_ξ^β a` on `K` bounds the seminorm `p_{K,α,β}(a)`. -/
theorem seminorm_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length)) :
    HomogeneousSymbol.seminorm K α β a ≤ C :=
  Seminorm.weightedSup_le _ _ _ hC fun i => h i.1 i.1.2 i.2 i.2.2

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
  have hu : ‖ξ‖⁻¹ • ξ ≠ 0 := norm_ne_zero_iff.1 (by rw [hs]; exact one_ne_zero)
  have hscale : mixedDeriv α β a.coefficient x ξ =
      ‖ξ‖ ^ (m - β.length) • mixedDeriv α β a.coefficient x (‖ξ‖⁻¹ • ξ) := by
    rw [← mixedDeriv_coefficient_smul_frequency a α β x hu hn, smul_inv_smul₀ hn.ne']
  rw [hscale, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _), mul_comm]
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
  -- The constant in front of `∑_{|β'| = k - i} p_{K,α,β'}(a)`.
  set c : ℕ → ℝ := fun i => k.choose i * (B i * 5 ^ ((i : ℝ) / 2)) * 2 ^ (|m - ↑(k - i)| / 2)
  have hc (i : ℕ) : 0 ≤ c i := by have := hB0 i; positivity
  refine ⟨∑ i ∈ Finset.range (k + 1), c i, Finset.sum_nonneg fun i _ => hc i, fun a => ?_⟩
  set S := ∑ i ∈ Finset.range (k + 1), ∑ w : Fin (k - i) → Fin n,
    HomogeneousSymbol.seminorm K α (List.ofFn w) a
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  refine Symbol.seminorm_le_bound K α β _
    (mul_nonneg (Finset.sum_nonneg fun i _ => hc i) hS) fun x hx ξ => ?_
  rcases lt_or_ge ‖ξ‖ 1 with hξ | hξ
  · -- On the unit ball the cut-off term vanishes near `(x, ξ)`.
    have h0 : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [continuous_snd.continuousAt.eventually
        (χ.eventuallyEq_zero_of_norm_lt_one hξ)] with q hq
      simp [hq]
    rw [h0.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hc i) hS) (rpow_weight_pos ξ _).le
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (one_pos.trans_le hξ)
  -- Near `(x, ξ)`, replace `a` by a smooth function `f` with the same germ and apply the Leibniz
  -- rule. The derivatives of `χ` of positive order vanish outside `‖ξ‖ < 2`, where `⟨ξ⟩ ≤ √5`.
  obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventuallyEq_coefficient hξ0
  have heq : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] fun p => χ p.2 • f p := by
    filter_upwards [hfa x] with q hq
    rw [coefficient_cutoffSymbol, hq]
  rw [heq.mixedDeriv_eq]
  refine (norm_mixedDeriv_comp_snd_smul_le_mul_rpow_weight χ.contDiff hf
    (m := m) (B := fun i => B i * 5 ^ ((i : ℝ) / 2))
    (D := fun w => 2 ^ (|m - w.length| / 2) * HomogeneousSymbol.seminorm K α w a)
    (fun i => ?_) (fun w => ?_) β).trans ?_
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using hB 0 ξ
    by_cases h2 : 2 ≤ ‖ξ‖
    · rw [χ.iteratedFDeriv_eq_zero_of_two_le_norm hi.ne' h2, norm_zero, zero_mul]
      exact mul_nonneg (hB0 i) (by positivity)
    exact mul_le_mul (hB i ξ) (Real.rpow_le_rpow (by positivity)
      (by nlinarith [norm_nonneg ξ, not_le.1 h2]) (by positivity)) (by positivity) (hB0 i)
  · rw [(hfa x).mixedDeriv_eq, mul_comm (2 ^ _), mul_assoc]
    exact (le_seminorm K α w a hx hξ0).trans (mul_le_mul_of_nonneg_left
      (norm_rpow_le_one_add_norm_sq_rpow hξ _) (apply_nonneg _ _))
  refine mul_le_mul_of_nonneg_right ?_ (rpow_weight_pos ξ _).le
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp_rw [List.length_ofFn, ← Finset.mul_sum]
  refine (mul_assoc _ _ _).symm.trans_le (mul_le_mul_of_nonneg_left ?_ (hc i))
  exact Finset.single_le_sum (f := fun i => ∑ w : Fin (k - i) → Fin n,
    HomogeneousSymbol.seminorm K α (List.ofFn w) a)
    (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) hi

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

end TauCeti
