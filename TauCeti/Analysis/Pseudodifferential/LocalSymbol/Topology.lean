/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The topology of the symbol classes on an open set of positions

For an open set `U ⊆ ℝⁿ`, a compact set `K ⊆ U` of positions and words `α`, `β` of coordinate
indices, the seminorm `TauCeti.LocalSymbol.seminorm K hK α β a` of a symbol `a` of order `m` on
`U × ℝⁿ` (`TauCeti.LocalSymbol`) is the best constant `C` in the estimate

`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for `x ∈ K` and all `ξ`,

which the definition of `TauCeti.LocalSymbol` asserts to be finite. Only compact sets inside `U`
are allowed: near the boundary of `U` a local symbol need not be bounded, as `1 / x₁` on the
half-space `x₁ > 0` shows. These seminorms make `TauCeti.LocalSymbol U V W m` a Hausdorff locally
convex topological vector space over `ℂ`. Convergence in this topology is convergence of all
mixed derivatives, uniformly for positions in compact subsets of `U` after division by the weight
`⟨ξ⟩^(m - |β|)`. These are the symbol topologies of the full symbols of pseudodifferential
operators read in a chart, in which continuity of a parameter family of local symbols is
expressed.

The topology is compatible with the comparison maps of `TauCeti.LocalSymbol`:

* `TauCeti.LocalSymbol.seminorm_restrict` and `TauCeti.Symbol.seminorm_restrict`: restriction to
  a smaller open set, and restriction of a symbol on `ℝⁿ`, preserve the seminorms of the compact
  sets inside the smaller domain, so these restrictions are continuous
  (`TauCeti.LocalSymbol.restrictCLM`, `TauCeti.Symbol.restrictCLM`);
* `TauCeti.Symbol.restrictTopCLE`: over all of `ℝⁿ` the local symbols are the symbols on
  `ℝⁿ × ℝⁿ` with their topology (`TauCeti.Symbol.seminorm_restrictTopEquiv`);
* `TauCeti.LocalSymbol.exists_seminorm_extend_le`: the seminorms of the cut-off extension
  `ψ(x) a(x, ξ)` on a compact set `K` are controlled by seminorms of `a` on a compact subset of
  `U` containing `K ∩ tsupport ψ`, so extension by a cutoff is continuous
  (`TauCeti.LocalSymbol.extendCLM`); it does not change the seminorms on a compact set near which
  `ψ = 1` (`TauCeti.LocalSymbol.seminorm_extend_of_eventuallyEq_one`);
* `TauCeti.LocalSymbol.inclusionCLM`: the order inclusions are continuous.

Consequently a family of local symbols is continuous exactly when its cut-off extensions by all
compactly supported cutoffs are continuous families of symbols on `ℝⁿ`
(`TauCeti.LocalSymbol.continuous_iff_forall_continuous_extend`). This reduces continuity questions
for local symbols, for instance for parameter families or after a change of chart, to the global
symbol class `TauCeti.Symbol n V W m`.

Every mixed derivative at a point of `U` is a continuous linear function of the local symbol
(`TauCeti.LocalSymbol.mixedDerivCLM`, `TauCeti.LocalSymbol.continuous_mixedDeriv`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Definition 7.8.1:
  symbol classes on an open set with constants depending on a compact set of positions, whose
  best constants are the seminorms used here.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open TopologicalSpace (Compacts)
open scoped ContDiff Topology
open Set Filter

namespace TauCeti

variable {n : ℕ}

namespace LocalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m m' : ℝ}

section Seminorm

/-- A cutoff equal to `1` near the compact set `K ⊆ U`, with compact support inside `U`. -/
private theorem exists_cutoff {K : Compacts (CoordinateSpace n)}
    (hK : (K : Set (CoordinateSpace n)) ⊆ U) :
    ∃ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ U ∧ ∀ x ∈ K, ψ =ᶠ[𝓝 x] 1 :=
  let ⟨ψ, hψ, _, hψ1, _, hψU⟩ := K.isCompact.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hK
  ⟨ψ, hψ, hψU, hψ1⟩

/-- The seminorm `p_{K,α,β}` on the symbols of order `m` on `U`, for a compact set `K ⊆ U`: the
best constant `C` in the estimate `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)` for all positions
`x ∈ K` and all frequencies `ξ`, where `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)` (`le_seminorm`,
`seminorm_le_bound`). It is the corresponding seminorm of the cut-off extension of `a` by a cutoff
equal to `1` near `K`, which does not depend on the cutoff
(`seminorm_extend_of_eventuallyEq_one`). -/
protected def seminorm (K : Compacts (CoordinateSpace n))
    (hK : (K : Set (CoordinateSpace n)) ⊆ U) (α β : List (Fin n)) :
    Seminorm ℂ (LocalSymbol U V W m) :=
  (Symbol.seminorm K α β).comp
    (extend _ (exists_cutoff hK).choose_spec.1 (exists_cutoff hK).choose_spec.2.1)

/-- On `K`, the mixed derivatives of `a` are those of the cut-off extension defining
`LocalSymbol.seminorm`. -/
private theorem mixedDeriv_extend_cutoff {K : Compacts (CoordinateSpace n)}
    (hK : (K : Set (CoordinateSpace n)) ⊆ U) (α β : List (Fin n)) (a : LocalSymbol U V W m)
    {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    mixedDeriv α β (extend _ (exists_cutoff hK).choose_spec.1
      (exists_cutoff hK).choose_spec.2.1 a).coefficient x ξ = mixedDeriv α β a.coefficient x ξ :=
  mixedDeriv_extend_of_eventuallyEq_one _ _ ((exists_cutoff hK).choose_spec.2.2 x hx) α β a ξ

variable {K L : Compacts (CoordinateSpace n)}

/-- The seminorm `p_{K,α,β}(a)` bounds `‖∂_x^α ∂_ξ^β a(x, ξ)‖ / ⟨ξ⟩^(m - |β|)` for `x ∈ K`. -/
theorem le_seminorm (hK : (K : Set (CoordinateSpace n)) ⊆ U) (α β : List (Fin n))
    (a : LocalSymbol U V W m) {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      LocalSymbol.seminorm K hK α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  rw [← mixedDeriv_extend_cutoff hK α β a hx ξ]
  exact Symbol.le_seminorm K α β _ hx ξ

/-- A constant in the estimate of `∂_x^α ∂_ξ^β a` on `K` bounds the seminorm `p_{K,α,β}(a)`. -/
theorem seminorm_le_bound (hK : (K : Set (CoordinateSpace n)) ⊆ U) (α β : List (Fin n))
    (a : LocalSymbol U V W m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :
    LocalSymbol.seminorm K hK α β a ≤ C :=
  Symbol.seminorm_le_bound K α β _ hC fun x hx ξ => by
    rw [mixedDeriv_extend_cutoff hK α β a hx ξ]
    exact h x hx ξ

/-- The seminorm `p_{K,α,β}(a)` is at most `C ≥ 0` exactly when `C` is a constant in the estimate
of `∂_x^α ∂_ξ^β a` on `K`. -/
theorem seminorm_le_iff {hK : (K : Set (CoordinateSpace n)) ⊆ U} {α β : List (Fin n)}
    {a : LocalSymbol U V W m} {C : ℝ} (hC : 0 ≤ C) :
    LocalSymbol.seminorm K hK α β a ≤ C ↔ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  refine ⟨fun h x hx ξ => (le_seminorm hK α β a hx ξ).trans ?_, seminorm_le_bound hK α β a hC⟩
  exact mul_le_mul_of_nonneg_right h (rpow_weight_pos ξ _).le

/-- The seminorm `p_{K,[],[]}(a)` bounds `‖a(x, ξ)‖ / ⟨ξ⟩^m` for `x ∈ K`. -/
theorem norm_coefficient_le_seminorm (hK : (K : Set (CoordinateSpace n)) ⊆ U)
    (a : LocalSymbol U V W m) {x : CoordinateSpace n} (hx : x ∈ K) (ξ : CoordinateSpace n) :
    ‖a.coefficient (x, ξ)‖ ≤ LocalSymbol.seminorm K hK [] [] a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  simpa using le_seminorm hK [] [] a hx ξ

/-- The seminorms are monotone in the compact set. -/
theorem seminorm_mono (hK : (K : Set (CoordinateSpace n)) ⊆ U)
    (hL : (L : Set (CoordinateSpace n)) ⊆ U) (hKL : K ≤ L) (α β : List (Fin n))
    (a : LocalSymbol U V W m) :
    LocalSymbol.seminorm K hK α β a ≤ LocalSymbol.seminorm L hL α β a :=
  seminorm_le_bound hK α β a (apply_nonneg _ _) fun _ hx ξ => le_seminorm hL α β a (hKL hx) ξ

/-- Viewing a symbol of order `m` on `U` as one of order `m' ≥ m` does not increase its
seminorms. -/
theorem seminorm_inclusion_le (h : m ≤ m') (hK : (K : Set (CoordinateSpace n)) ⊆ U)
    (α β : List (Fin n)) (a : LocalSymbol U V W m) :
    LocalSymbol.seminorm K hK α β (inclusion h a) ≤ LocalSymbol.seminorm K hK α β a := by
  refine seminorm_le_bound hK α β _ (apply_nonneg _ _) fun x hx ξ => ?_
  rw [coefficient_inclusion]
  refine (le_seminorm hK α β a hx ξ).trans (mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _))
  exact rpow_weight_le_rpow_weight ξ (by linarith)

/-- The seminorms on `K` only depend on the mixed derivatives at the positions of `K`, so local
symbols on different open sets containing `K` can be compared. -/
theorem seminorm_congr {a : LocalSymbol U V W m} {b : LocalSymbol U' V W m}
    (hK : (K : Set (CoordinateSpace n)) ⊆ U) (hK' : (K : Set (CoordinateSpace n)) ⊆ U')
    {α β : List (Fin n)}
    (h : ∀ x ∈ K, ∀ ξ, mixedDeriv α β a.coefficient x ξ = mixedDeriv α β b.coefficient x ξ) :
    LocalSymbol.seminorm K hK α β a = LocalSymbol.seminorm K hK' α β b := by
  refine le_antisymm (seminorm_le_bound hK α β a (apply_nonneg _ _) fun x hx ξ => ?_)
    (seminorm_le_bound hK' α β b (apply_nonneg _ _) fun x hx ξ => ?_)
  · rw [h x hx ξ]
    exact le_seminorm hK' α β b hx ξ
  · rw [← h x hx ξ]
    exact le_seminorm hK α β a hx ξ

/-- Restricting a local symbol to a smaller open set `U'` does not change its seminorms on the
compact subsets of `U'`. -/
@[simp]
theorem seminorm_restrict (h : U' ≤ U) (hK : (K : Set (CoordinateSpace n)) ⊆ U')
    (α β : List (Fin n)) (a : LocalSymbol U V W m) :
    LocalSymbol.seminorm K hK α β (restrict h a) = LocalSymbol.seminorm K (hK.trans h) α β a :=
  seminorm_congr _ _ fun x hx ξ => by
    rw [coefficient_restrict, mixedDeriv_indicator_prod_univ_of_mem U'.isOpen (hK hx)]

/-- The local symbol on `⊤` corresponding to a symbol on `ℝⁿ` has the same seminorms. -/
@[simp]
theorem _root_.TauCeti.Symbol.seminorm_restrictTopEquiv
    (hK : (K : Set (CoordinateSpace n)) ⊆ (⊤ : TopologicalSpace.Opens (CoordinateSpace n)))
    (α β : List (Fin n)) (a : Symbol n V W m) :
    LocalSymbol.seminorm K hK α β (Symbol.restrictTopEquiv a) = Symbol.seminorm K α β a := by
  refine le_antisymm (LocalSymbol.seminorm_le_bound hK α β _ (apply_nonneg _ _) fun x hx ξ => ?_)
    (Symbol.seminorm_le_bound K α β a (apply_nonneg _ _) fun x hx ξ => ?_)
  · rw [Symbol.coefficient_restrictTopEquiv_apply]
    exact Symbol.le_seminorm K α β a hx ξ
  · rw [← Symbol.coefficient_restrictTopEquiv_apply]
    exact LocalSymbol.le_seminorm hK α β _ hx ξ

/-- The symbol on `ℝⁿ` corresponding to a local symbol on `⊤` has the same seminorms. -/
@[simp]
theorem _root_.TauCeti.Symbol.seminorm_restrictTopEquiv_symm (α β : List (Fin n))
    (a : LocalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    Symbol.seminorm K α β (Symbol.restrictTopEquiv.symm a) =
      LocalSymbol.seminorm K (fun x _ => TopologicalSpace.Opens.mem_top x) α β a := by
  rw [← Symbol.seminorm_restrictTopEquiv (fun x _ => TopologicalSpace.Opens.mem_top x),
    LinearEquiv.apply_symm_apply]

/-- Restricting a symbol on `ℝⁿ` to an open set `U` does not change its seminorms on the compact
subsets of `U`. -/
@[simp]
theorem _root_.TauCeti.Symbol.seminorm_restrict (hK : (K : Set (CoordinateSpace n)) ⊆ U)
    (α β : List (Fin n)) (a : Symbol n V W m) :
    LocalSymbol.seminorm K hK α β (a.restrict U) = Symbol.seminorm K α β a := by
  rw [← Symbol.restrict_restrictTopEquiv le_top, LocalSymbol.seminorm_restrict,
    Symbol.seminorm_restrictTopEquiv]

end Seminorm

section Topology

variable (U V W m) in
/-- The family of all seminorms `p_{K,α,β}` on the symbols of order `m` on `U`, indexed by the
compact sets `K ⊆ U` of positions and the words `α`, `β` of coordinate indices. -/
def seminormFamily :
    SeminormFamily ℂ (LocalSymbol U V W m)
      ({K : Compacts (CoordinateSpace n) // (K : Set (CoordinateSpace n)) ⊆ U} ×
        List (Fin n) × List (Fin n)) :=
  fun i => LocalSymbol.seminorm i.1.val i.1.property i.2.1 i.2.2

@[simp]
theorem seminormFamily_apply (K : Compacts (CoordinateSpace n))
    (hK : (K : Set (CoordinateSpace n)) ⊆ U) (α β : List (Fin n)) :
    seminormFamily U V W m (⟨K, hK⟩, α, β) = LocalSymbol.seminorm K hK α β := (rfl)

/-- The topology of the symbol class on `U`: the locally convex topology of the seminorms
`p_{K,α,β}` for the compact sets `K ⊆ U`. -/
instance instTopologicalSpace : TopologicalSpace (LocalSymbol U V W m) :=
  (seminormFamily U V W m).moduleFilterBasis.topology'

/-- The topology of the symbol class on `U` is induced by the seminorms `p_{K,α,β}`. -/
theorem withSeminorms : WithSeminorms (seminormFamily U V W m) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (LocalSymbol U V W m) :=
  (seminormFamily U V W m).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℂ (LocalSymbol U V W m) :=
  withSeminorms.continuousSMul

instance instUniformSpace : UniformSpace (LocalSymbol U V W m) :=
  fast_instance% (seminormFamily U V W m).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup (LocalSymbol U V W m) :=
  (seminormFamily U V W m).addGroupFilterBasis.isUniformAddGroup

instance instPolynormableSpace : PolynormableSpace ℂ (LocalSymbol U V W m) :=
  withSeminorms.toPolynormableSpace

instance instLocallyConvexSpace : LocallyConvexSpace ℝ (LocalSymbol U V W m) :=
  withSeminorms.toLocallyConvexSpace

/-- The symbol class on `U` is T1, hence Hausdorff: the seminorms `p_{K,α,β}` separate local
symbols, since a local symbol is determined by its values at the positions of `U`. -/
instance instT1Space : T1Space (LocalSymbol U V W m) := by
  refine withSeminorms.T1_of_separating fun a ha => ?_
  obtain ⟨x, hx, ξ, hxξ⟩ : ∃ x ∈ U, ∃ ξ, a.coefficient (x, ξ) ≠ 0 := by
    by_contra! h
    exact ha (ext_of_mem fun x hx ξ => by simp [h x hx ξ])
  have hxU : ((({x} : Compacts (CoordinateSpace n))) : Set (CoordinateSpace n)) ⊆ U := by
    simpa using hx
  refine ⟨(⟨{x}, hxU⟩, [], []), fun h0 => hxξ (norm_le_zero_iff.1 ?_)⟩
  have h := norm_coefficient_le_seminorm hxU a rfl ξ
  rwa [← seminormFamily_apply, h0, zero_mul] at h

/-- Order inclusions are continuous. -/
theorem continuous_inclusion (h : m ≤ m') :
    Continuous (inclusion (U := U) (V := V) (W := W) h) :=
  WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms _
    fun ⟨⟨K, hK⟩, α, β⟩ => ⟨{(⟨K, hK⟩, α, β)}, 1, fun a => by
      simpa using seminorm_inclusion_le h hK α β a⟩

/-- The order inclusion `inclusion h` as a continuous linear map. -/
def inclusionCLM (h : m ≤ m') : LocalSymbol U V W m →L[ℂ] LocalSymbol U V W m' where
  toLinearMap := inclusion h
  cont := continuous_inclusion h

@[simp]
theorem inclusionCLM_apply (h : m ≤ m') (a : LocalSymbol U V W m) :
    inclusionCLM h a = inclusion h a := (rfl)

/-- Restriction to a smaller open set is continuous. -/
theorem continuous_restrict (h : U' ≤ U) :
    Continuous (restrict (V := V) (W := W) (m := m) h) :=
  WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms _
    fun ⟨⟨K, hK⟩, α, β⟩ => ⟨{(⟨K, hK.trans h⟩, α, β)}, 1, fun a => by simp⟩

/-- The restriction `restrict h` to a smaller open set as a continuous linear map. -/
def restrictCLM (h : U' ≤ U) : LocalSymbol U V W m →L[ℂ] LocalSymbol U' V W m where
  toLinearMap := restrict h
  cont := continuous_restrict h

@[simp]
theorem restrictCLM_apply (h : U' ≤ U) (a : LocalSymbol U V W m) :
    restrictCLM h a = restrict h a := (rfl)

end Topology

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)
  {K L : Compacts (CoordinateSpace n)}

/-- **Seminorm estimate for the cut-off extension.** The seminorm `p_{K,α,β}` of the extension
`ψ(x) a(x, ξ)` of a local symbol `a` is at most a constant, independent of `a`, times the sum of
the seminorms `p_{L,w,β}(a)` over the words `w` of length at most `|α|`, for any compact set
`L ⊆ U` containing `K ∩ tsupport ψ`. -/
theorem exists_seminorm_extend_le (hL : (L : Set (CoordinateSpace n)) ⊆ U)
    (hKL : (K : Set (CoordinateSpace n)) ∩ tsupport ψ ⊆ L) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : LocalSymbol U V W m, Symbol.seminorm K α β (extend ψ hψ hψU a) ≤
      C * ∑ i ∈ Finset.range (α.length + 1), ∑ w : Fin (α.length - i) → Fin n,
        LocalSymbol.seminorm L hL (List.ofFn w) β a := by
  choose B hB using fun i : ℕ => L.isCompact.exists_bound_of_continuousOn
    (hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) (m := i)).continuousOn
  have hc : ∀ i, 0 ≤ (α.length.choose i : ℝ) * max (B i) 0 := fun i => by positivity
  refine ⟨∑ i ∈ Finset.range (α.length + 1), (α.length.choose i : ℝ) * max (B i) 0,
    Finset.sum_nonneg fun i _ => hc i,
    fun a => Symbol.seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_⟩
  have hS : ∀ i, 0 ≤ ∑ w : Fin (α.length - i) → Fin n,
      LocalSymbol.seminorm L hL (List.ofFn w) β a :=
    fun i => Finset.sum_nonneg fun w _ => apply_nonneg _ _
  have hw := (rpow_weight_pos ξ (m - β.length)).le
  rw [show (extend ψ hψ hψU a).coefficient = fun p => ψ p.1 • a.coefficient p from
    funext (coefficient_extend hψ hψU a)]
  by_cases hxψ : x ∈ tsupport ψ
  · have hxL : x ∈ L := hKL ⟨hx, hxψ⟩
    refine (a.norm_mixedDeriv_cutoff_smul_le hψ (hL hxL) α β ξ).trans ?_
    -- Bound each term of the Leibniz expansion, then each coefficient by the sum of all of them.
    calc _ ≤ ∑ i ∈ Finset.range (α.length + 1), (α.length.choose i : ℝ) * max (B i) 0 *
          ((∑ w : Fin (α.length - i) → Fin n, LocalSymbol.seminorm L hL (List.ofFn w) β a) *
            (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hD : ‖iteratedFDeriv ℝ i ψ x‖ ≤ max (B i) 0 :=
            (hB i x hxL).trans (le_max_left _ _)
          have hsum : ∑ w : Fin (α.length - i) → Fin n,
              ‖mixedDeriv (List.ofFn w) β a.coefficient x ξ‖ ≤
                (∑ w : Fin (α.length - i) → Fin n,
                  LocalSymbol.seminorm L hL (List.ofFn w) β a) *
                    (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
            rw [Finset.sum_mul]
            exact Finset.sum_le_sum fun w _ => le_seminorm hL _ β a hxL ξ
          gcongr
      _ ≤ ∑ i ∈ Finset.range (α.length + 1),
            (∑ j ∈ Finset.range (α.length + 1), (α.length.choose j : ℝ) * max (B j) 0) *
              ((∑ w : Fin (α.length - i) → Fin n, LocalSymbol.seminorm L hL (List.ofFn w) β a) *
                (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun j _ => hc j) hi) (mul_nonneg (hS i) hw)
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  · rw [mixedDeriv_comp_fst_smul_eq_zero_of_notMem_tsupport (a := a.coefficient) hxψ, norm_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hc i)
      (Finset.sum_nonneg fun i _ => hS i)) hw

/-- The cut-off extension `ψ(x) a(x, ξ)` of a local symbol has the same seminorms as `a` on a
compact set `K ⊆ U` near which `ψ = 1`. -/
theorem seminorm_extend_of_eventuallyEq_one (hK : (K : Set (CoordinateSpace n)) ⊆ U)
    (h1 : ∀ x ∈ K, ψ =ᶠ[𝓝 x] 1) (α β : List (Fin n)) (a : LocalSymbol U V W m) :
    Symbol.seminorm K α β (extend ψ hψ hψU a) = LocalSymbol.seminorm K hK α β a := by
  rw [← Symbol.seminorm_restrictTopEquiv (fun x _ => TopologicalSpace.Opens.mem_top x)]
  exact seminorm_congr _ _ fun x hx ξ => by
    rw [Symbol.coefficient_restrictTopEquiv_apply,
      mixedDeriv_extend_of_eventuallyEq_one hψ hψU (h1 x hx)]

/-- Extension by a cutoff is continuous. -/
theorem continuous_extend :
    Continuous (extend (V := V) (W := W) (m := m) ψ hψ hψU) := by
  refine WithSeminorms.continuous_of_isBounded withSeminorms Symbol.withSeminorms _
    (Seminorm.IsBounded.of_real fun ⟨K, α, β⟩ => ?_)
  classical
  -- The seminorms on `K` of the extension are controlled on `L = K ∩ tsupport ψ ⊆ U`.
  set L : Compacts (CoordinateSpace n) :=
    ⟨(K : Set (CoordinateSpace n)) ∩ tsupport ψ, K.isCompact.inter_right (isClosed_tsupport ψ)⟩
  have hL : (L : Set (CoordinateSpace n)) ⊆ U := inter_subset_right.trans hψU
  obtain ⟨C, hC, hCa⟩ := exists_seminorm_extend_le hψ hψU (V := V) (W := W) (m := m) hL
    subset_rfl α β
  set s : Finset ({K : Compacts (CoordinateSpace n) // (K : Set (CoordinateSpace n)) ⊆ U} ×
      List (Fin n) × List (Fin n)) :=
    ((Finset.range (α.length + 1)).biUnion fun i => Finset.univ.image
      fun w : Fin (α.length - i) → Fin n => List.ofFn w).image fun γ => (⟨L, hL⟩, γ, β)
  have hs : ∀ i ∈ Finset.range (α.length + 1), ∀ w : Fin (α.length - i) → Fin n,
      (⟨L, hL⟩, List.ofFn w, β) ∈ s := fun i hi w =>
    Finset.mem_image.2 ⟨List.ofFn w, Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2
      ⟨w, Finset.mem_univ w, rfl⟩⟩, rfl⟩
  set N : ℝ := ∑ i ∈ Finset.range (α.length + 1), (Fintype.card (Fin (α.length - i) → Fin n) : ℝ)
  refine ⟨s, C * N, fun a => ?_⟩
  have hsum : ∑ i ∈ Finset.range (α.length + 1), ∑ w : Fin (α.length - i) → Fin n,
      LocalSymbol.seminorm L hL (List.ofFn w) β a ≤ N * s.sup (seminormFamily U V W m) a := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    calc _ ≤ ∑ _w : Fin (α.length - i) → Fin n, s.sup (seminormFamily U V W m) a :=
          Finset.sum_le_sum fun w _ => Seminorm.le_finset_sup_apply (hs i hi w)
      _ = _ := by simp
  rw [Symbol.seminormFamily_apply, mul_assoc]
  exact (hCa a).trans (mul_le_mul_of_nonneg_left hsum hC)

/-- Extension by a cutoff as a continuous linear map from the symbols on `U` to the symbols on
`ℝⁿ`. -/
def extendCLM : LocalSymbol U V W m →L[ℂ] Symbol n V W m where
  toLinearMap := extend ψ hψ hψU
  cont := continuous_extend hψ hψU

@[simp]
theorem extendCLM_apply (a : LocalSymbol U V W m) :
    extendCLM hψ hψU a = extend ψ hψ hψU a := (rfl)

/-- **Continuity through cut-off extensions.** A family of local symbols on `U`, parametrized by a
topological space, is continuous exactly when its cut-off extensions `ψ(x) a_t(x, ξ)` are
continuous families of symbols on `ℝⁿ` for all compactly supported cutoffs `ψ` whose support is
contained in `U`. -/
theorem continuous_iff_forall_continuous_extend {X : Type*} [TopologicalSpace X]
    {f : X → LocalSymbol U V W m} :
    Continuous f ↔ ∀ (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U),
      HasCompactSupport ψ → Continuous fun t => extend ψ hψ hψU (f t) := by
  refine ⟨fun hf ψ hψ hψU _ => (continuous_extend hψ hψU).comp hf, fun h => ?_⟩
  refine continuous_iff_continuousAt.2 fun t₀ => (withSeminorms.tendsto_nhds f (f t₀)).2 ?_
  rintro ⟨⟨K, hK⟩, α, β⟩ ε hε
  -- Choose a cutoff equal to `1` near `K`, whose extension then has the seminorms of `f t` on `K`.
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψU⟩ :=
    K.isCompact.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hK
  filter_upwards [(Symbol.withSeminorms.tendsto_nhds _ _).1
    ((h ψ hψ hψU hψc).tendsto t₀) (K, α, β) ε hε] with t ht
  rwa [Symbol.seminormFamily_apply, ← map_sub,
    seminorm_extend_of_eventuallyEq_one hψ hψU hK hψ1] at ht

end Extend

section MixedDeriv

variable {x : CoordinateSpace n}

/-- At a position `x ∈ U`, the mixed derivatives of a local symbol are those of its extension by a
cutoff equal to `1` near `x`. -/
private theorem exists_mixedDeriv_eq_extend (hx : x ∈ U) (α β : List (Fin n))
    (ξ : CoordinateSpace n) :
    ∃ (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U),
      ∀ a : LocalSymbol U V W m, mixedDeriv α β a.coefficient x ξ =
        Symbol.mixedDerivCLM n V W m α β x ξ (extend ψ hψ hψU a) := by
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen (singleton_subset_iff.2 hx)
  exact ⟨ψ, hψ, hψU, fun a => by
    rw [Symbol.mixedDerivCLM_apply, mixedDeriv_extend_of_eventuallyEq_one hψ hψU (hψ1 x rfl)]⟩

variable (V W m) in
/-- The mixed derivative `a ↦ ∂_x^α ∂_ξ^β a(x, ξ)` at a point with `x ∈ U`, as a continuous linear
map on the local symbols of order `m`; in particular the value `a ↦ a(x, ξ)` for `α = β = []`. -/
def mixedDerivCLM (hx : x ∈ U) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    LocalSymbol U V W m →L[ℂ] V →L[ℂ] W where
  toFun a := mixedDeriv α β a.coefficient x ξ
  map_add' a b := by
    obtain ⟨ψ, hψ, hψU, h⟩ := exists_mixedDeriv_eq_extend (V := V) (W := W) (m := m) hx α β ξ
    simp only [h, map_add]
  map_smul' c a := by
    obtain ⟨ψ, hψ, hψU, h⟩ := exists_mixedDeriv_eq_extend (V := V) (W := W) (m := m) hx α β ξ
    simp only [h, map_smul, RingHom.id_apply]
  cont := by
    obtain ⟨ψ, hψ, hψU, h⟩ := exists_mixedDeriv_eq_extend (V := V) (W := W) (m := m) hx α β ξ
    simp_rw [h]
    exact (Symbol.mixedDerivCLM n V W m α β x ξ).continuous.comp (continuous_extend hψ hψU)

@[simp]
theorem mixedDerivCLM_apply (hx : x ∈ U) (α β : List (Fin n)) (ξ : CoordinateSpace n)
    (a : LocalSymbol U V W m) :
    mixedDerivCLM V W m hx α β ξ a = mixedDeriv α β a.coefficient x ξ := (rfl)

/-- Every mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)` at a point with `x ∈ U` is a continuous function
of the local symbol `a`; in particular so is the value `a(x, ξ)`. -/
theorem continuous_mixedDeriv (hx : x ∈ U) (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    Continuous fun a : LocalSymbol U V W m => mixedDeriv α β a.coefficient x ξ :=
  (mixedDerivCLM V W m hx α β ξ).continuous

end MixedDeriv

end LocalSymbol

namespace Symbol

variable {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  {K : Compacts (CoordinateSpace n)}

/-- Restriction of symbols on `ℝⁿ` to an open set is continuous. -/
theorem continuous_restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    Continuous (restrict (V := V) (W := W) (m := m) U) :=
  WithSeminorms.continuous_of_isBounded withSeminorms LocalSymbol.withSeminorms _
    fun ⟨⟨K, hK⟩, α, β⟩ => ⟨{(K, α, β)}, 1, fun a => by simp⟩

/-- The restriction `restrict U` of symbols on `ℝⁿ` to an open set as a continuous linear map. -/
def restrictCLM (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    Symbol n V W m →L[ℂ] LocalSymbol U V W m where
  toLinearMap := restrict U
  cont := continuous_restrict U

@[simp]
theorem restrictCLM_apply (U : TopologicalSpace.Opens (CoordinateSpace n)) (a : Symbol n V W m) :
    restrictCLM U a = a.restrict U := (rfl)

/-- Over all of `ℝⁿ`, the local symbols are the symbols on `ℝⁿ × ℝⁿ` with their topology:
`restrictTopEquiv` as a continuous linear equivalence. -/
def restrictTopCLE :
    Symbol n V W m ≃L[ℂ] LocalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toLinearEquiv := restrictTopEquiv
  continuous_toFun := WithSeminorms.continuous_of_isBounded withSeminorms
    LocalSymbol.withSeminorms restrictTopEquiv.toLinearMap
    fun ⟨⟨K, hK⟩, α, β⟩ => ⟨{(K, α, β)}, 1, fun a => by simp⟩
  continuous_invFun := WithSeminorms.continuous_of_isBounded LocalSymbol.withSeminorms
    withSeminorms restrictTopEquiv.symm.toLinearMap
    fun ⟨K, α, β⟩ => ⟨{(⟨K, fun x _ => TopologicalSpace.Opens.mem_top x⟩, α, β)}, 1,
      fun a => by
        simp only [seminormFamily_apply, Seminorm.comp_apply, LinearEquiv.coe_coe,
          seminorm_restrictTopEquiv_symm, Finset.sup_singleton, one_smul]
        exact le_rfl⟩

@[simp]
theorem restrictTopCLE_apply (a : Symbol n V W m) : restrictTopCLE a = restrictTopEquiv a := (rfl)

@[simp]
theorem restrictTopCLE_symm_apply
    (a : LocalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    restrictTopCLE.symm a = restrictTopEquiv.symm a := (rfl)

end Symbol

end TauCeti
