/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# The topology of the symbol classes `S^m_{1,0}`

For a compact set `K` of positions and words `α`, `β` of coordinate indices, the seminorm
`TauCeti.Symbol.seminorm K α β a` of a symbol `a` of order `m` is the best constant `C` in the
estimate

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`,

which the definition of `TauCeti.Symbol` asserts to be finite. These seminorms make
`TauCeti.Symbol n V W m` a locally convex topological vector space over `ℂ`; it is Hausdorff and,
since the closed balls of integer radius already define the same topology
(`TauCeti.Symbol.withSeminorms_closedBall`), first countable. Convergence in this topology is
convergence of all mixed derivatives, uniformly for positions in compact sets after division by
the weight `⟨ξ⟩^(m - |β|)`. Continuity of a parameter family `t ↦ a_t` of symbols, as used for
continuous symbol homotopies and parametric asymptotic sums, is continuity into this space.

The main results are:

* `TauCeti.Symbol.le_seminorm`, `TauCeti.Symbol.seminorm_le_iff`: the seminorm is the best
  constant of the estimate;
* `TauCeti.Symbol.withSeminorms`: the topology on `TauCeti.Symbol n V W m` is the one induced by
  the family `TauCeti.Symbol.seminormFamily` of all these seminorms;
* `TauCeti.Symbol.continuous_inclusion`, `TauCeti.Symbol.continuous_frequencyDeriv`,
  `TauCeti.Symbol.continuous_spatialDeriv`: order inclusions and derivatives are continuous, with
  the exact seminorm identities `TauCeti.Symbol.seminorm_frequencyDeriv` and
  `TauCeti.Symbol.seminorm_spatialDeriv`;
* `TauCeti.Symbol.inclusionCLM`, `TauCeti.Symbol.frequencyDerivCLM`,
  `TauCeti.Symbol.spatialDerivCLM`: these operations as continuous linear maps;
* `TauCeti.Symbol.mixedDerivCLM`, `TauCeti.Symbol.continuous_mixedDeriv`: every mixed derivative
  at a point is a continuous linear function of the symbol;
* `TauCeti.Symbol.isUniform_iff_bddAbove_seminorm`: a symbol is uniform exactly when its seminorms
  are bounded independently of the compact set.
* `TauCeti.Symbol.seminorm_comp_le`: the Leibniz estimate bounding the seminorms of a composition
  `b ∘ a` by sums of products of seminorms of `b` and `a`;
* `TauCeti.Symbol.continuous_comp`: composition of symbols is jointly continuous, so the
  composition of two continuous parameter families is continuous (`Continuous.symbol_comp`);
  with one factor fixed it is a continuous linear map (`TauCeti.Symbol.compLeftCLM`,
  `TauCeti.Symbol.compRightCLM`).

On a nonempty compact set, the constant symbol `T` has seminorm `‖T‖` without derivatives; with
any derivative its seminorms vanish (`TauCeti.Symbol.seminorm_const_nil_nil`,
`TauCeti.Symbol.seminorm_const_eq_zero`).

The seminorms are set up following Mathlib's seminorms of the Schwartz space
(`SchwartzMap.seminorm`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Definition 7.8.1:
  symbol classes with constants depending on a compact set of positions, whose best constants
  are the seminorms used here.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
-/

public section

noncomputable section

open TopologicalSpace (Compacts)

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

section Seminorm

/-- The admissible constants in the estimate of `∂_x^α ∂_ξ^β a` on `K`. -/
private def bounds (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ x ∈ K, ∀ ξ,
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤ c * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)}

private theorem bounds_nonempty (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) : (bounds K α β a).Nonempty :=
  let ⟨C, hC, h⟩ := a.exists_bound K K.isCompact α β
  ⟨C, hC, h⟩

private theorem bounds_bddBelow (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) : BddBelow (bounds K α β a) :=
  ⟨0, fun _ hc => hc.1⟩

/-- The best constant in the estimate of `∂_x^α ∂_ξ^β a` on `K`. -/
private def seminormAux (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) : ℝ :=
  sInf (bounds K α β a)

private theorem seminormAux_nonneg (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) : 0 ≤ seminormAux K α β a :=
  le_csInf (bounds_nonempty K α β a) fun _ hc => hc.1

private theorem le_seminormAux (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      seminormAux K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  have hw := rpow_weight_pos ξ (m - β.length)
  rw [← div_le_iff₀ hw]
  exact le_csInf (bounds_nonempty K α β a) fun c hc => (div_le_iff₀ hw).2 (hc.2 x hx ξ)

private theorem seminormAux_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :
    seminormAux K α β a ≤ C :=
  csInf_le (bounds_bddBelow K α β a) ⟨hC, h⟩

private theorem seminormAux_zero (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    seminormAux K α β (0 : Symbol n V W m) = 0 :=
  le_antisymm (seminormAux_le_bound K α β 0 le_rfl fun _ _ _ => by simp)
    (seminormAux_nonneg K α β 0)

private theorem seminormAux_add_le (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a b : Symbol n V W m) :
    seminormAux K α β (a + b) ≤ seminormAux K α β a + seminormAux K α β b :=
  seminormAux_le_bound K α β _ (add_nonneg (seminormAux_nonneg K α β a)
    (seminormAux_nonneg K α β b)) fun x hx ξ => by
      rw [coefficient_add]
      exact norm_mixedDeriv_add_le a.contDiff_coefficient b.contDiff_coefficient
        (le_seminormAux K α β a hx ξ) (le_seminormAux K α β b hx ξ)

private theorem seminormAux_smul_le (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (c : ℂ) (a : Symbol n V W m) : seminormAux K α β (c • a) ≤ ‖c‖ * seminormAux K α β a :=
  seminormAux_le_bound K α β _ (mul_nonneg (norm_nonneg c) (seminormAux_nonneg K α β a))
    fun x hx ξ => by
      rw [coefficient_smul]
      exact norm_mixedDeriv_smul_le c (le_seminormAux K α β a hx ξ)

/-- The seminorm `p_{K,α,β}` on the symbols of order `m`: the best constant `C` in the estimate
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for all positions `x ∈ K` and all frequencies `ξ`,
where `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)`. -/
protected def seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    Seminorm ℂ (Symbol n V W m) :=
  Seminorm.ofSMulLE (seminormAux K α β) (seminormAux_zero K α β) (seminormAux_add_le K α β)
    (seminormAux_smul_le K α β)

/-- The seminorm `p_{K,α,β}(a)` bounds `‖∂_x^α ∂_ξ^β a(x, ξ)‖ / ⟨ξ⟩^(m - |β|)` for `x ∈ K`. -/
theorem le_seminorm (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      Symbol.seminorm K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) :=
  le_seminormAux K α β a hx ξ

/-- A constant in the estimate of `∂_x^α ∂_ξ^β a` on `K` bounds the seminorm `p_{K,α,β}(a)`. -/
theorem seminorm_le_bound (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (a : Symbol n V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :
    Symbol.seminorm K α β a ≤ C :=
  seminormAux_le_bound K α β a hC h

/-- The seminorm `p_{K,α,β}(a)` is at most `C ≥ 0` exactly when `C` is a constant in the estimate
of `∂_x^α ∂_ξ^β a` on `K`. -/
theorem seminorm_le_iff {K : Compacts (CoordinateSpace n)} {α β : List (Fin n)}
    {a : Symbol n V W m} {C : ℝ} (hC : 0 ≤ C) :
    Symbol.seminorm K α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  refine ⟨fun h x hx ξ => (le_seminorm K α β a hx ξ).trans ?_, seminorm_le_bound K α β a hC⟩
  exact mul_le_mul_of_nonneg_right h (rpow_weight_pos ξ _).le

/-- The seminorm `p_{K,[],[]}(a)` bounds `‖a(x, ξ)‖ / ⟨ξ⟩^m` for `x ∈ K`. -/
theorem norm_coefficient_le_seminorm (K : Compacts (CoordinateSpace n)) (a : Symbol n V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    ‖a.coefficient (x, ξ)‖ ≤ Symbol.seminorm K [] [] a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  simpa using le_seminorm K [] [] a hx ξ

/-- The seminorms are monotone in the compact set. -/
theorem seminorm_mono {K L : Compacts (CoordinateSpace n)} (hKL : K ≤ L) (α β : List (Fin n))
    (a : Symbol n V W m) : Symbol.seminorm K α β a ≤ Symbol.seminorm L α β a :=
  seminorm_le_bound K α β a (apply_nonneg _ _) fun _ hx ξ => le_seminorm L α β a (hKL hx) ξ

/-- Viewing a symbol of order `m` as one of order `m' ≥ m` does not increase its seminorms. -/
theorem seminorm_inclusion_le (h : m ≤ m') (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) (a : Symbol n V W m) :
    Symbol.seminorm K α β (inclusion h a) ≤ Symbol.seminorm K α β a := by
  refine seminorm_le_bound K α β _ (apply_nonneg _ _) fun x hx ξ => ?_
  rw [coefficient_inclusion]
  refine (le_seminorm K α β a hx ξ).trans (mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _))
  exact rpow_weight_le_rpow_weight ξ (by linarith)

/-- The seminorms of the frequency derivative `∂_{ξ_j} a` are seminorms of `a` with one more
frequency derivative. -/
@[simp]
theorem seminorm_frequencyDeriv (j : Fin n) (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) (a : Symbol n V W m) :
    Symbol.seminorm K α β (frequencyDeriv j a) = Symbol.seminorm K α (β ++ [j]) a := by
  refine le_antisymm (seminorm_le_bound K α β _ (apply_nonneg _ _) fun x hx ξ => ?_)
    (seminorm_le_bound K α _ a (apply_nonneg _ _) fun x hx ξ => ?_)
  · rw [mixedDeriv_frequencyDeriv, order_sub_one_sub_length m β j]
    exact le_seminorm K α (β ++ [j]) a hx ξ
  · rw [← mixedDeriv_frequencyDeriv, ← order_sub_one_sub_length m β j]
    exact le_seminorm K α β (frequencyDeriv j a) hx ξ

/-- The seminorms of the spatial derivative `∂_{x_j} a` are seminorms of `a` with one more
position derivative. -/
@[simp]
theorem seminorm_spatialDeriv (j : Fin n) (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) (a : Symbol n V W m) :
    Symbol.seminorm K α β (spatialDeriv j a) = Symbol.seminorm K (α ++ [j]) β a := by
  refine le_antisymm (seminorm_le_bound K α β _ (apply_nonneg _ _) fun x hx ξ => ?_)
    (seminorm_le_bound K _ β a (apply_nonneg _ _) fun x hx ξ => ?_)
  · rw [mixedDeriv_spatialDeriv]
    exact le_seminorm K (α ++ [j]) β a hx ξ
  · rw [← mixedDeriv_spatialDeriv]
    exact le_seminorm K α β (spatialDeriv j a) hx ξ

/-- On a nonempty compact set, the constant symbol `T` has seminorm `‖T‖` without derivatives. -/
@[simp]
theorem seminorm_const_nil_nil {K : Compacts (CoordinateSpace n)}
    (hK : (K : Set (CoordinateSpace n)).Nonempty)
    (T : V →L[ℂ] W) : Symbol.seminorm K [] [] (const T : Symbol n V W 0) = ‖T‖ := by
  obtain ⟨x, hx⟩ := hK
  refine le_antisymm (seminorm_le_bound K [] [] _ (norm_nonneg T) fun y _ ξ => by simp) ?_
  simpa using norm_coefficient_le_seminorm K (const T : Symbol n V W 0) hx 0

/-- Every seminorm of the constant symbol `T` involving a derivative vanishes. -/
@[simp]
theorem seminorm_const_eq_zero {α β : List (Fin n)} (h : α ≠ [] ∨ β ≠ [])
    (K : Compacts (CoordinateSpace n)) (T : V →L[ℂ] W) :
    Symbol.seminorm K α β (const T : Symbol n V W 0) = 0 := by
  refine le_antisymm (seminorm_le_bound K α β _ le_rfl fun x _ ξ => ?_) (apply_nonneg _ _)
  have hc : (const T : Symbol n V W 0).coefficient =
      fun p => (fun _ : CoordinateSpace n => T) p.1 :=
    funext (coefficient_const T)
  have hd : mixedDeriv α β (const T : Symbol n V W 0).coefficient x ξ = 0 := by
    rw [hc]
    rcases eq_or_ne β [] with rfl | hβ
    · rw [mixedDeriv_nil_comp_fst (fun _ : CoordinateSpace n => T),
        coordinateDeriv_const T (h.resolve_right (by simp)), Pi.zero_apply]
    · exact mixedDeriv_comp_fst (fun _ : CoordinateSpace n => T) α hβ x ξ
  rw [hd, norm_zero, zero_mul]

/-- A symbol satisfies its estimates uniformly in the position exactly when each of its
seminorms `p_{K,α,β}` is bounded independently of the compact set `K`. -/
theorem isUniform_iff_bddAbove_seminorm {a : Symbol n V W m} :
    a.IsUniform ↔ ∀ α β : List (Fin n), BddAbove (Set.range fun K => Symbol.seminorm K α β a) := by
  refine ⟨fun h α β => ?_, fun h => isUniform_iff.2 fun α β => ?_⟩
  · obtain ⟨C, hC, hCa⟩ := isUniform_iff.1 h α β
    exact ⟨C, Set.forall_mem_range.2 fun K =>
      seminorm_le_bound K α β a hC fun x _ ξ => hCa x ξ⟩
  · obtain ⟨C, hC⟩ := h α β
    refine ⟨max C 0, le_max_right _ _, fun x ξ => (le_seminorm {x} α β a rfl ξ).trans ?_⟩
    refine mul_le_mul_of_nonneg_right ((hC ⟨{x}, rfl⟩).trans (le_max_left _ _)) ?_
    exact (rpow_weight_pos ξ _).le

end Seminorm

section Topology

variable (n V W m) in
/-- The family of all seminorms `p_{K,α,β}` on the symbols of order `m`, indexed by the compact
sets `K` of positions and the words `α`, `β` of coordinate indices. -/
def seminormFamily :
    SeminormFamily ℂ (Symbol n V W m)
      (Compacts (CoordinateSpace n) × List (Fin n) × List (Fin n)) :=
  fun i => Symbol.seminorm i.1 i.2.1 i.2.2

@[simp]
theorem seminormFamily_apply (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    seminormFamily n V W m (K, α, β) = Symbol.seminorm K α β := (rfl)

/-- The topology of the symbol class: the locally convex topology of the seminorms
`p_{K,α,β}`. -/
instance instTopologicalSpace : TopologicalSpace (Symbol n V W m) :=
  (seminormFamily n V W m).moduleFilterBasis.topology'

/-- The topology of the symbol class is induced by the seminorms `p_{K,α,β}`. -/
theorem withSeminorms : WithSeminorms (seminormFamily n V W m) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (Symbol n V W m) :=
  (seminormFamily n V W m).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℂ (Symbol n V W m) :=
  withSeminorms.continuousSMul

instance instUniformSpace : UniformSpace (Symbol n V W m) :=
  fast_instance% (seminormFamily n V W m).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup (Symbol n V W m) :=
  (seminormFamily n V W m).addGroupFilterBasis.isUniformAddGroup

instance instPolynormableSpace : PolynormableSpace ℂ (Symbol n V W m) :=
  withSeminorms.toPolynormableSpace

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (Symbol n V W m) :=
  withSeminorms.toLocallyConvexSpace

/-- The symbol class is T1, hence Hausdorff: the seminorms `p_{K,α,β}` separate symbols. -/
instance instT1Space : T1Space (Symbol n V W m) := by
  refine withSeminorms.T1_of_separating fun a ha => ?_
  obtain ⟨⟨x, ξ⟩, hxξ⟩ : ∃ p, a.coefficient p ≠ 0 := by
    by_contra! h
    exact ha (Symbol.ext (funext h))
  refine ⟨({x}, [], []), fun h0 => hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := norm_coefficient_le_seminorm {x} a rfl ξ
  rwa [← seminormFamily_apply, h0, zero_mul] at h

/-- The seminorms over the closed balls `closedBall 0 k` of natural radius `k` already induce the
topology of the symbol class. -/
theorem withSeminorms_closedBall :
    WithSeminorms fun i : ℕ × List (Fin n) × List (Fin n) =>
      (Symbol.seminorm ⟨Metric.closedBall 0 i.1, isCompact_closedBall 0 i.1⟩ i.2.1 i.2.2 :
        Seminorm ℂ (Symbol n V W m)) := by
  refine withSeminorms.congr (fun ⟨k, α, β⟩ => ⟨{(⟨_, isCompact_closedBall 0 k⟩, α, β)}, 1,
    by simp⟩) fun ⟨K, α, β⟩ => ?_
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
  refine ⟨{(⌈r⌉₊, α, β)}, 1, fun a => ?_⟩
  simp only [Finset.sup_singleton, one_smul, Seminorm.comp_id, seminormFamily_apply]
  exact seminorm_mono (hr.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil r))) α β a

instance instFirstCountableTopology : FirstCountableTopology (Symbol n V W m) :=
  withSeminorms_closedBall.firstCountableTopology

/-- Order inclusions are continuous. -/
theorem continuous_inclusion (h : m ≤ m') :
    Continuous (inclusion (n := n) (V := V) (W := W) h) :=
  WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms _
    fun ⟨K, α, β⟩ => ⟨{(K, α, β)}, 1, fun a => by
      simpa using seminorm_inclusion_le h K α β a⟩

/-- The order inclusion `inclusion h` as a continuous linear map. -/
def inclusionCLM (h : m ≤ m') : Symbol n V W m →L[ℂ] Symbol n V W m' where
  toLinearMap := inclusion h
  cont := continuous_inclusion h

@[simp]
theorem inclusionCLM_apply (h : m ≤ m') (a : Symbol n V W m) :
    inclusionCLM h a = inclusion h a := (rfl)

/-- Frequency derivatives are continuous. -/
theorem continuous_frequencyDeriv (j : Fin n) :
    Continuous (frequencyDeriv (n := n) (V := V) (W := W) (m := m) j) :=
  WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms _
    fun ⟨K, α, β⟩ => ⟨{(K, α, β ++ [j])}, 1, fun a => by simp⟩

/-- The frequency derivative `frequencyDeriv j` as a continuous linear map. -/
def frequencyDerivCLM (j : Fin n) : Symbol n V W m →L[ℂ] Symbol n V W (m - 1) where
  toLinearMap := frequencyDeriv j
  cont := continuous_frequencyDeriv j

@[simp]
theorem frequencyDerivCLM_apply (j : Fin n) (a : Symbol n V W m) :
    frequencyDerivCLM j a = frequencyDeriv j a := (rfl)

/-- Spatial derivatives are continuous. -/
theorem continuous_spatialDeriv (j : Fin n) :
    Continuous (spatialDeriv (n := n) (V := V) (W := W) (m := m) j) :=
  WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms _
    fun ⟨K, α, β⟩ => ⟨{(K, α ++ [j], β)}, 1, fun a => by simp⟩

/-- The spatial derivative `spatialDeriv j` as a continuous linear map. -/
def spatialDerivCLM (j : Fin n) : Symbol n V W m →L[ℂ] Symbol n V W m where
  toLinearMap := spatialDeriv j
  cont := continuous_spatialDeriv j

@[simp]
theorem spatialDerivCLM_apply (j : Fin n) (a : Symbol n V W m) :
    spatialDerivCLM j a = spatialDeriv j a := (rfl)

variable (n V W m) in
/-- The mixed derivative `a ↦ ∂_x^α ∂_ξ^β a(x, ξ)` at a fixed point, as a continuous linear map
on the symbols of order `m`; in particular the value `a ↦ a(x, ξ)` for `α = β = []`. -/
def mixedDerivCLM (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    Symbol n V W m →L[ℂ] V →L[ℂ] W :=
  let L : Symbol n V W m →ₗ[ℂ] V →L[ℂ] W :=
    { toFun a := mixedDeriv α β a.coefficient x ξ
      map_add' a b := mixedDeriv_add a.contDiff_coefficient b.contDiff_coefficient α β x ξ
      map_smul' c a := mixedDeriv_const_smul a.contDiff_coefficient c α β x ξ }
  { toLinearMap := L
    cont := WithSeminorms.continuous_of_isBounded withSeminorms (norm_withSeminorms ℂ _) L
      (Seminorm.IsBounded.of_real fun _ => ⟨{({x}, α, β)},
        (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2), fun a => by
          simpa [L, mul_comm] using le_seminorm {x} α β a rfl ξ⟩) }

@[simp]
theorem mixedDerivCLM_apply (α β : List (Fin n)) (x ξ : CoordinateSpace n) (a : Symbol n V W m) :
    mixedDerivCLM n V W m α β x ξ a = mixedDeriv α β a.coefficient x ξ := (rfl)

/-- Every mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)` at a fixed point is a continuous function of the
symbol `a`; in particular so is the value `a(x, ξ)`. -/
theorem continuous_mixedDeriv (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    Continuous fun a : Symbol n V W m => mixedDeriv α β a.coefficient x ξ :=
  (mixedDerivCLM n V W m α β x ξ).continuous

end Topology

section Comp

open Filter Topology

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- The Leibniz estimate for the seminorms of a composition: `p_{K,α,β}(b ∘ a)` is at most the sum,
over the splittings of `α` and `β` into complementary subwords, of the products
`p_{K,α₁,β₁}(b) p_{K,α₂,β₂}(a)`. -/
theorem seminorm_comp_le (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    (b : Symbol n W U m') (a : Symbol n V W m) :
    Symbol.seminorm K α β (b.comp a) ≤
      (β.sublists'.revzip.map fun t => (α.sublists'.revzip.map fun s =>
        Symbol.seminorm K s.1 t.1 b * Symbol.seminorm K s.2 t.2 a).sum).sum := by
  refine seminorm_le_bound K α β _ (List.sum_nonneg fun _ h => ?_) fun x hx ξ => ?_
  · obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
    exact List.sum_nonneg fun _ h' => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h'
      exact mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  · have hc : (b.comp a).coefficient = fun p => (b.coefficient p).comp (a.coefficient p) :=
      funext (coefficient_comp b a)
    rw [hc]
    exact norm_mixedDeriv_comp_le b.contDiff_coefficient a.contDiff_coefficient
      (fun s t => le_seminorm K s t b hx ξ) (fun s t => le_seminorm K s t a hx ξ) α β

/-- If all products `p_{K,α₁,β₁}(b_i) p_{K,α₂,β₂}(a_i)` tend to zero, then so does
`p_{K,α,β}(b_i ∘ a_i)`, by the Leibniz estimate `seminorm_comp_le`. -/
private theorem tendsto_seminorm_comp {ι : Type*} {l : Filter ι} (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) {b : ι → Symbol n W U m'} {a : ι → Symbol n V W m}
    (h : ∀ s₁ t₁ s₂ t₂, Tendsto (fun i =>
      Symbol.seminorm K s₁ t₁ (b i) * Symbol.seminorm K s₂ t₂ (a i)) l (𝓝 0)) :
    Tendsto (fun i => Symbol.seminorm K α β ((b i).comp (a i))) l (𝓝 0) := by
  refine squeeze_zero (fun _ => apply_nonneg _ _) (fun i => seminorm_comp_le K α β (b i) (a i)) ?_
  have := tendsto_list_sum (a := fun _ => (0 : ℝ)) β.sublists'.revzip fun t _ => by
    simpa using tendsto_list_sum (a := fun _ => (0 : ℝ)) α.sublists'.revzip
      fun s _ => h s.1 t.1 s.2 t.2
  simpa using this

/-- Composition of symbols is jointly continuous for the symbol topologies. -/
theorem continuous_comp :
    Continuous fun p : Symbol n W U m' × Symbol n V W m => p.1.comp p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, withSeminorms.tendsto_nhds]
  rintro ⟨K, α, β⟩ ε hε
  have hb : ∀ s t, Tendsto (fun p : Symbol n W U m' × Symbol n V W m =>
      Symbol.seminorm K s t (p.1 - p₀.1)) (𝓝 p₀) (𝓝 0) := fun s t =>
    ((withSeminorms.continuous_seminorm (K, s, t)).comp
      (continuous_fst.sub continuous_const)).tendsto' p₀ 0 (by simp)
  have ha : ∀ s t, Tendsto (fun p : Symbol n W U m' × Symbol n V W m =>
      Symbol.seminorm K s t (p.2 - p₀.2)) (𝓝 p₀) (𝓝 0) := fun s t =>
    ((withSeminorms.continuous_seminorm (K, s, t)).comp
      (continuous_snd.sub continuous_const)).tendsto' p₀ 0 (by simp)
  -- `b ∘ a - b₀ ∘ a₀ = (b - b₀) ∘ (a - a₀) + (b - b₀) ∘ a₀ + b₀ ∘ (a - a₀)`.
  have h₁ := tendsto_seminorm_comp K α β fun s₁ t₁ s₂ t₂ => by
    simpa using (hb s₁ t₁).mul (ha s₂ t₂)
  have h₂ := tendsto_seminorm_comp K α β (a := fun _ => p₀.2) fun s₁ t₁ s₂ t₂ => by
    simpa using (hb s₁ t₁).mul_const (Symbol.seminorm K s₂ t₂ p₀.2)
  have h₃ := tendsto_seminorm_comp K α β (b := fun _ => p₀.1) fun s₁ t₁ s₂ t₂ => by
    simpa using (ha s₂ t₂).const_mul (Symbol.seminorm K s₁ t₁ p₀.1)
  have key : Tendsto (fun p : Symbol n W U m' × Symbol n V W m =>
      Symbol.seminorm K α β (p.1.comp p.2 - p₀.1.comp p₀.2)) (𝓝 p₀) (𝓝 0) := by
    refine squeeze_zero (fun _ => apply_nonneg _ _) (fun p => ?_) (by
      simpa using (h₁.add h₂).add h₃)
    have hp : p.1.comp p.2 - p₀.1.comp p₀.2 =
        (p.1 - p₀.1).comp (p.2 - p₀.2) + (p.1 - p₀.1).comp p₀.2 + p₀.1.comp (p.2 - p₀.2) := by
      simp only [sub_comp, comp_sub]
      abel
    rw [hp]
    exact (map_add_le_add _ _ _).trans (add_le_add_left (map_add_le_add _ _ _) _)
  simpa using (tendsto_order.1 key).2 ε hε

/-- Composition on the left with a fixed symbol `b`, `a ↦ b ∘ a`, as a continuous linear map. -/
def compLeftCLM (b : Symbol n W U m') : Symbol n V W m →L[ℂ] Symbol n V U (m' + m) where
  toFun a := b.comp a
  map_add' := comp_add b
  map_smul' c a := comp_smul c b a
  cont := continuous_comp.comp (continuous_const.prodMk continuous_id)

@[simp]
theorem compLeftCLM_apply (b : Symbol n W U m') (a : Symbol n V W m) :
    compLeftCLM b a = b.comp a := (rfl)

/-- Composition on the right with a fixed symbol `a`, `b ↦ b ∘ a`, as a continuous linear map. -/
def compRightCLM (a : Symbol n V W m) : Symbol n W U m' →L[ℂ] Symbol n V U (m' + m) where
  toFun b := b.comp a
  map_add' b₁ b₂ := add_comp b₁ b₂ a
  map_smul' c b := smul_comp c b a
  cont := continuous_comp.comp (continuous_id.prodMk continuous_const)

@[simp]
theorem compRightCLM_apply (a : Symbol n V W m) (b : Symbol n W U m') :
    compRightCLM a b = b.comp a := (rfl)

/-- The pointwise composition of two continuous families of symbols is a continuous family of
symbols. -/
@[continuity, fun_prop]
theorem _root_.Continuous.symbol_comp {X : Type*} [TopologicalSpace X] {b : X → Symbol n W U m'}
    {a : X → Symbol n V W m} (hb : Continuous b) (ha : Continuous a) :
    Continuous fun x => (b x).comp (a x) :=
  continuous_comp.comp (hb.prodMk ha)

end Comp

end Symbol

end TauCeti
