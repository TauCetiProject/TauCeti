/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# Differential operators as classical pseudodifferential operators

A differential operator `P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` on `ℝⁿ` with smooth coefficients
`bᵢ : ℝⁿ → (V →L[ℂ] W)` has the polynomial left Fourier symbol
`TauCeti.differentialSymbol s v b (x, ξ) = ∑ i ∈ s, (∏ j, i ⟪ξ, vᵢⱼ⟫) • bᵢ(x)`. This file shows
that this symbol is a classical symbol of order `m` as soon as every summand has order at most
`m`, so that differential operators belong to the classical calculus: ellipticity, the
composition expansion and the parametrix construction apply to them. Only the local symbol
estimates are claimed; no bound on the coefficients uniform in the position is required.

The summands have homogeneous degrees, so each is a classical symbol with a single homogeneous
term (`TauCeti.ClassicalSymbol.ofContDiffHomogeneous`), and the operator is their sum after the
integer-step order inclusions.

For the differential symbol of order `m`:

* `TauCeti.ClassicalSymbol.ofDifferentialSymbol`: the classical symbol of order `m`, with full
  symbol `differentialSymbol s v b`
  (`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol`);
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol`: its quantization is the
  differential operator itself on Schwartz input, with no smoothing remainder;
* `TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`: its homogeneous term of degree
  `m - j` is the part of the symbol made of the summands of order `m - j`; in particular the
  principal symbol (`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialSymbol`) is the
  sum of the top-order summands, in the angular-frequency convention `σ(∂_v) = i ⟪ξ, v⟫`;
* `TauCeti.ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol`: compactly
  supported coefficients give a symbol with compact spatial support;
* `TauCeti.ClassicalSymbol.negLaplacian`: the classical symbol of the negative Laplacian
  `-∑ⱼ ∂ⱼ²`, with full symbol `‖ξ‖²` (`TauCeti.ClassicalSymbol.coefficient_toSymbol_negLaplacian`)
  and principal symbol `HomogeneousSymbol.normRpow _ _ V 2`
  (`TauCeti.ClassicalSymbol.principal_negLaplacian`); it is elliptic
  (`TauCeti.ClassicalSymbol.isElliptic_negLaplacian`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.1)–(1.4) and (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

open HomogeneousSymbol

/-! ### Differential operators -/

namespace ClassicalSymbol

variable {ι : Type*} {k : ι → ℕ}

/-- The classical symbol of order `m` of the differential operator
`u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` with smooth coefficients `bᵢ`, where the summand `i` has order
`k i ≤ m`. Its full symbol is the polynomial `TauCeti.differentialSymbol s v b`
(`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol`), and its homogeneous term of
degree `m - j` collects the summands of order `m - j`
(`TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`). -/
def ofDifferentialSymbol (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ m) : ClassicalSymbol n V W m :=
  ∑ i ∈ s.attach, inclusion (m - k i) (by rw [Nat.cast_sub (hk i i.2)]; ring)
    (ofContDiffHomogeneous (m := k i) (differentialSymbol {i.1} v b)
      (contDiff_differentialSymbol _ v fun j hj ↦ Finset.mem_singleton.1 hj ▸ hb i i.2)
      fun x ξ _ t _ ↦ by
        rw [Real.rpow_natCast]
        exact differentialSymbol_smul_snd _ v b (fun j hj ↦ by rw [Finset.mem_singleton.1 hj])
          x ξ t)

variable (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
  (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
  (hk : ∀ i ∈ s, k i ≤ m)

/-- The full symbol of `ClassicalSymbol.ofDifferentialSymbol` is the polynomial differential
symbol. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialSymbol :
    (ofDifferentialSymbol m s v b hb hk).toSymbol.coefficient = differentialSymbol s v b := by
  funext p
  simp only [ofDifferentialSymbol, toSymbol_sum, Symbol.coefficient_sum, Finset.sum_apply,
    toSymbol_inclusion,
    Symbol.coefficient_inclusion, toSymbol_ofContDiffHomogeneous,
    Symbol.coefficient_ofContDiffHomogeneous]
  rw [Finset.sum_attach s fun i ↦ differentialSymbol {i} v b p, differentialSymbol_def]
  exact Finset.sum_congr rfl fun i _ ↦ differentialSymbol_singleton i v b p

/-- **Differential operators are pseudodifferential operators.** On Schwartz input, the
quantization of the classical symbol of a differential operator is the differential operator,
with no smoothing remainder. -/
theorem quantizeSchwartzValue_ofDifferentialSymbol [CompleteSpace V] [CompleteSpace W]
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialSymbol m s v b hb hk).toSymbol.coefficient u x =
      ∑ i ∈ s, b i x (∂^{v i} u x) := by
  rw [coefficient_toSymbol_ofDifferentialSymbol, quantizeSchwartzValue_differentialSymbol]

/-- The homogeneous term of degree `m - j` of the classical symbol of a differential operator is,
away from `ξ = 0`, the differential symbol of its summands of order `m - j`. -/
theorem coefficient_term_ofDifferentialSymbol (j : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((ofDifferentialSymbol m s v b hb hk).term j).coefficient (x, ξ) =
      differentialSymbol {i ∈ s | k i + j = m} v b (x, ξ) := by
  simp only [ofDifferentialSymbol, term_sum, coefficient_sum, Finset.sum_apply]
  rw [differentialSymbol_def, Finset.sum_filter, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hki := hk i i.2
  rw [term_inclusion]
  split_ifs with hj hkj hkj
  · -- The summand `i` has order `m - j`: its term of degree `m - j` is its principal symbol.
    rw [coefficient_castDegree, coefficient_congr_index (ofContDiffHomogeneous _ _ _).term
      (show j - (m - k i) = 0 by omega), ← coefficient_principal, principal_ofContDiffHomogeneous,
      coefficient_mk'_of_ne_zero _ _ _ hξ, differentialSymbol_singleton]
  · -- Otherwise the summand only contributes to the terms of other degrees.
    obtain ⟨l, hl⟩ : ∃ l, j - (m - k i) = l + 1 := ⟨j - (m - k i) - 1, by omega⟩
    rw [coefficient_castDegree, coefficient_congr_index (ofContDiffHomogeneous _ _ _).term hl,
      term_ofContDiffHomogeneous_succ, coefficient_zero, Pi.zero_apply]
  · omega
  · rw [coefficient_zero, Pi.zero_apply]

/-- The principal symbol of the classical symbol of a differential operator of order `m` is,
away from `ξ = 0`, the differential symbol of its summands of order exactly `m`. In particular
`σ(∂_v)(ξ) = i ⟪ξ, v⟫`. -/
theorem coefficient_principal_ofDifferentialSymbol {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialSymbol m s v b hb hk).principal.coefficient (x, ξ) =
      differentialSymbol {i ∈ s | k i = m} v b (x, ξ) := by
  rw [coefficient_principal, coefficient_term_ofDifferentialSymbol m s v b hb hk 0 hξ]
  simp

/-- Compactly supported coefficients give a classical symbol with compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol
    (hbc : ∀ i ∈ s, HasCompactSupport (b i)) :
    (ofDifferentialSymbol m s v b hb hk).toSymbol.HasCompactSpatialSupport := by
  refine Symbol.hasCompactSpatialSupport_iff.2
    ⟨⋃ i ∈ s, tsupport (b i), s.isCompact_biUnion fun i hi ↦ hbc i hi, fun x hx ξ ↦ ?_⟩
  rw [coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_def]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (Set.mem_biUnion hi h), smul_zero]

/-! ### The Laplacian -/

variable (n V) in
/-- The classical symbol of order `2` of the negative Laplacian `-Δ = -∑ⱼ ∂ⱼ²` on `V`-valued
functions on `ℝⁿ`. -/
def negLaplacian : ClassicalSymbol n V V 2 :=
  ofDifferentialSymbol (k := fun _ : Fin n ↦ 2) 2 Finset.univ
    (fun j _ ↦ EuclideanSpace.single j 1) (fun _ _ ↦ -ContinuousLinearMap.id ℂ V)
    (fun _ _ ↦ contDiff_const) fun _ _ ↦ le_rfl

/-- The differential symbol of `-∑ⱼ ∂ⱼ²` is `‖ξ‖²`. -/
private theorem differentialSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol (k := fun _ : Fin n ↦ 2) Finset.univ (fun j _ ↦ EuclideanSpace.single j 1)
      (fun _ _ ↦ -ContinuousLinearMap.id ℂ V) p = ‖p.2‖ ^ 2 • ContinuousLinearMap.id ℂ V := by
  rw [differentialSymbol_def, EuclideanSpace.real_norm_sq_eq, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Complex.coe_smul, smul_neg, ← neg_smul]
  congr 1
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_pow, Complex.I_sq]
  push_cast
  ring

/-- The full symbol of the negative Laplacian is `‖ξ‖²`. -/
@[simp]
theorem coefficient_toSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    (negLaplacian n V).toSymbol.coefficient p = ‖p.2‖ ^ 2 • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_negLaplacian]

/-- The negative Laplacian is the sum of the negative second derivatives on Schwartz input. -/
theorem quantizeSchwartzValue_negLaplacian [CompleteSpace V] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (negLaplacian n V).toSymbol.coefficient u x =
      -∑ j : Fin n, ∂^{fun _ : Fin 2 ↦ EuclideanSpace.single j (1 : ℝ)} u x := by
  rw [negLaplacian, quantizeSchwartzValue_ofDifferentialSymbol]
  simp

/-- The principal symbol of the negative Laplacian is `‖ξ‖²`. -/
@[simp]
theorem principal_negLaplacian :
    (negLaplacian n V).principal = normRpow (CoordinateSpace n) (CoordinateSpace n) V 2 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [negLaplacian, coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
      Finset.filter_true_of_mem fun _ _ ↦ rfl, differentialSymbol_negLaplacian,
      coefficient_normRpow_of_ne_zero _ _ _ hξ, Real.rpow_two]

/-- **The Laplacian is elliptic.** -/
theorem isElliptic_negLaplacian : (negLaplacian n V).IsElliptic := by
  refine isElliptic_def.2 <| HomogeneousSymbol.isElliptic_iff.2 fun x ξ hξ ↦ ?_
  rw [principal_negLaplacian, coefficient_normRpow_of_ne_zero _ _ _ hξ, ← Complex.coe_smul,
    ContinuousLinearMap.isInvertible_smul_iff (by simpa using hξ)]
  simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)

end ClassicalSymbol

end TauCeti
