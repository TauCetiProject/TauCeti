/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Sequential

/-!
# Elliott's approximate intertwining of sequential C⋆-systems

Given two sequential inductive systems of (possibly non-unital) C⋆-algebras
`A₀ →[α₀] A₁ →[α₁] ⋯` and `B₀ →[β₀] B₁ →[β₁] ⋯` with possibly non-injective connecting maps and
compatible colimit cocones `ιA : ∀ n, A n →⋆ₙₐ[ℂ] C` and `ιB : ∀ n, B n →⋆ₙₐ[ℂ] D`, Elliott's
approximate-intertwining criterion produces a `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D` from stage maps
`φ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ n : B n →⋆ₙₐ[ℂ] A n` whose triangles commute up to summable
errors on propagating stagewise-dense sets `F n ⊆ A n` and `G n ⊆ B n`.

The construction factors through a one-sided approximate-cocone theorem
(`IsApproximateCocone.hom`), which builds a `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D` with a quantitative
tail-error bound whenever stage maps `ξ n : A n →⋆ₙₐ[ℂ] D` satisfy
`‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n` on `F n` with `Summable τ`, descending the pointwise limit
cocone via the exact universal lift `IsSeqColimitCocone.lift`. Applying `IsApproximateCocone.hom`
in both directions and checking the two composite identities on dense stage elements yields
`IsApproximateIntertwining.equiv` together with its forward and backward tail estimates. When the
stages are separable, `denseSeed` supplies canonical finite diagonal subsets discharging asymptotic
stagewise density (`exists_approx_of_denseSeed_subset`).

## Main definitions and results

* `TauCeti.denseSeed` and `TauCeti.exists_approx_of_denseSeed_subset`: finite diagonal seed sets on
  separable stages whose forward supersets asymptotically approximate every stage element.
* `TauCeti.IsApproximateCocone` and `TauCeti.IsApproximateCocone.hom`: one-sided limit
  `⋆`-homomorphism from an approximate cocone, with uniqueness (`hom_unique`,
  `comp_hom_eq_of_norm_sub_le`) and tail estimate `IsApproximateCocone.norm_hom_sub_le`.
* `TauCeti.IsApproximateIntertwining` and `TauCeti.IsApproximateIntertwining.equiv`: two-sided
  approximate intertwining inducing `C ≃⋆ₐ[ℂ] D`, with one-sided cocones
  `isApproximateCocone_forward` and `isApproximateCocone_backward`, uniqueness `equiv_unique`,
  and forward/backward tail estimates `norm_equiv_sub_le` and `norm_equiv_symm_sub_le`.

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  443 (1993), Theorem 2.1.
* M. Rørdam, *Classification of Nuclear C⋆-Algebras*, Encyclopaedia of Mathematical Sciences 126,
  Springer (2002), §2.3, Proposition 2.3.2.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section DenseSeed

variable {X : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (X n)]
  [∀ n, TopologicalSpace.SeparableSpace (X n)]

open Classical in
/-- Finite diagonal seed at stage `m` collecting the `(m - i)`-th term of a countable dense
sequence in each earlier stage `i ≤ m` pushed forward to `X m` along `seqTransHom`. -/
noncomputable def denseSeed (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1)) (m : ℕ) : Finset (X m) :=
  (Finset.Iic m).attach.image fun i ↦
    seqTransHom γ (Finset.mem_Iic.mp i.property) (TopologicalSpace.denseSeq (X i.val) (m - i.val))

/-- Membership characterization for `denseSeed γ m`. -/
theorem mem_denseSeed_iff (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1)) {m : ℕ} {x : X m} :
    x ∈ denseSeed γ m ↔
      ∃ (i : ℕ) (h : i ≤ m),
        seqTransHom γ h (TopologicalSpace.denseSeq (X i) (m - i)) = x := by
  classical
  simp only [denseSeed, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_Iic]

/-- The pushed dense-sequence term from stage `i ≤ m` belongs to `denseSeed γ m`. -/
theorem seqTransHom_denseSeq_mem_denseSeed (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1)) {i m : ℕ}
    (h : i ≤ m) :
    seqTransHom γ h (TopologicalSpace.denseSeq (X i) (m - i)) ∈ denseSeed γ m :=
  (mem_denseSeed_iff γ).mpr ⟨i, h, rfl⟩

/-- Any family of stage subsets `H m ⊆ X m` containing `denseSeed γ m` at every stage
asymptotically approximates every stage element along `seqTransHom γ`. -/
theorem exists_approx_of_denseSeed_subset (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1))
    {H : ∀ n, Set (X n)} (hseed : ∀ m, (denseSeed γ m : Set (X m)) ⊆ H m)
    (n : ℕ) (x : X n) (r : ℝ) (hr : 0 < r) :
    ∃ k, ∃ y ∈ H (n + k), ‖seqTransHom γ (Nat.le_add_right n k) x - y‖ < r := by
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq (X n)) x r hr
  refine ⟨k, seqTransHom γ (Nat.le_add_right n k) (TopologicalSpace.denseSeq (X n) k), ?_, ?_⟩
  · apply hseed (n + k)
    simpa only [Finset.mem_coe, Nat.add_sub_cancel_left] using
      seqTransHom_denseSeq_mem_denseSeed γ (Nat.le_add_right n k)
  · rw [← map_sub]
    refine (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt ?_
    simpa only [dist_eq_norm] using hk

end DenseSeed

section ApproximateCocone

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
  {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- Stage maps `ξ : ∀ n, A n →⋆ₙₐ[ℂ] D` form an *approximate cocone* on a sequential C⋆-system
`(A, α)` relative to propagating subsets `F n ⊆ A n` and summable step tolerances `τ : ℕ → ℝ` when
every stage element can be approximated to arbitrary accuracy in some later `F (n + k)` and
`‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n` on `F n`. -/
structure IsApproximateCocone (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D)
    (F : ∀ n, Set (A n)) (τ : ℕ → ℝ) : Prop where
  /-- Forward propagation of the approximating subsets along `α`. -/
  mapsTo (n : ℕ) ⦃a : A n⦄ : a ∈ F n → α n a ∈ F (n + 1)
  /-- Asymptotic stagewise density of `(F n)` along `α`. -/
  approx (n : ℕ) (a : A n) (ε : ℝ) :
    0 < ε → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < ε
  /-- Stepwise Cauchy estimate on `F n`. -/
  norm_sub_le (n : ℕ) ⦃a : A n⦄ : a ∈ F n → ‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n
  /-- Summability of the step tolerances. -/
  summable : Summable τ

namespace IsApproximateCocone

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}
  {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D} {F : ∀ n, Set (A n)} {τ : ℕ → ℝ}

/-- Absolute-stage evaluation sequence `m ↦ ξ m (seqTransHom α h a)` (zero for `m < n`), avoiding
dependent index casts when comparing elements from different stages. -/
private noncomputable def evalAt (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D)
    {n : ℕ} (a : A n) (m : ℕ) : D :=
  if h : n ≤ m then ξ m (seqTransHom α h a) else 0

private theorem evalAt_of_le {n m : ℕ} (h : n ≤ m) (a : A n) :
    evalAt α ξ a m = ξ m (seqTransHom α h a) := by
  simp [evalAt, h]

private theorem evalAt_add (n k : ℕ) (a : A n) :
    evalAt α ξ a (n + k) = ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a) := by
  simp [evalAt]

private theorem evalAt_eventuallyEq_seqTransHom {m n : ℕ} (h : m ≤ n) (a : A m) :
    evalAt α ξ (seqTransHom α h a) =ᶠ[atTop] evalAt α ξ a := by
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [evalAt_of_le hk, evalAt_of_le (h.trans hk), seqTransHom_comp_apply]

private theorem dist_step_le (hc : IsApproximateCocone α ξ F τ) {n : ℕ} {a : A n}
    (ha : a ∈ F n) (k : ℕ) :
    dist (ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      (ξ (n + (k + 1)) (seqTransHom α (Nat.le_add_right n (k + 1)) a)) ≤ τ (n + k) := by
  rw [dist_eq_norm, norm_sub_rev, seqTransHom_succ α (Nat.le_add_right n k)]
  exact hc.norm_sub_le (n + k) (seqTransHom_mem hc.mapsTo (Nat.le_add_right n k) ha)

private theorem cauchySeq_offset_of_mem (hc : IsApproximateCocone α ξ F τ) {n : ℕ} {x : A n}
    (hx : x ∈ F n) :
    CauchySeq (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) x)) :=
  cauchySeq_of_dist_le_of_summable (fun k ↦ τ (n + k)) (hc.dist_step_le hx)
    (hc.summable.comp_injective (add_right_injective n))

private theorem cauchySeq_evalAt_of_mem (hc : IsApproximateCocone α ξ F τ) {n : ℕ} {x : A n}
    (hx : x ∈ F n) : CauchySeq (evalAt α ξ x) := by
  have h : evalAt α ξ x ∘ (· + n) =
      fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) x) := by
    ext k
    rw [Function.comp_apply, Nat.add_comm k n, evalAt_add]
  rw [CauchySeq, ← map_add_atTop_eq_nat n, map_map, h, ← CauchySeq]
  exact hc.cauchySeq_offset_of_mem hx

private theorem cauchySeq_evalAt (hc : IsApproximateCocone α ξ F τ) (n : ℕ) (a : A n) :
    CauchySeq (evalAt α ξ a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨k₀, x, hxF, hax⟩ := hc.approx n a (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ :=
    Metric.cauchySeq_iff.mp (hc.cauchySeq_evalAt_of_mem hxF) (ε / 3) (by positivity)
  refine ⟨max (n + k₀) N₀, fun p hp q hq ↦ ?_⟩
  have hclose (r : ℕ) (hr : max (n + k₀) N₀ ≤ r) :
      dist (evalAt α ξ a r) (evalAt α ξ x r) < ε / 3 := by
    have hnkr : n + k₀ ≤ r := (le_max_left _ _).trans hr
    rw [evalAt_of_le ((Nat.le_add_right n k₀).trans hnkr), evalAt_of_le hnkr,
      ← seqTransHom_comp_apply α (Nat.le_add_right n k₀) hnkr a, dist_eq_norm,
      ← map_sub, ← map_sub]
    exact (le_trans (NonUnitalStarAlgHom.norm_apply_le _ _)
      (NonUnitalStarAlgHom.norm_apply_le _ _)).trans_lt hax
  calc
    dist (evalAt α ξ a p) (evalAt α ξ a q)
      ≤ dist (evalAt α ξ a p) (evalAt α ξ x p) +
        dist (evalAt α ξ x p) (evalAt α ξ x q) +
        dist (evalAt α ξ x q) (evalAt α ξ a q) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add (hclose p hp)
        (hN₀ p ((le_max_right _ _).trans hp) q ((le_max_right _ _).trans hq)))
        (by rw [dist_comm]; exact hclose q hq)
    _ = ε := by ring

private noncomputable def stageLim (hc : IsApproximateCocone α ξ F τ) {n : ℕ} (a : A n) : D :=
  (cauchySeq_tendsto_of_complete (hc.cauchySeq_evalAt n a)).choose

private theorem tendsto_evalAt_stageLim (hc : IsApproximateCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (evalAt α ξ a) atTop (𝓝 (hc.stageLim a)) :=
  (cauchySeq_tendsto_of_complete (hc.cauchySeq_evalAt n a)).choose_spec

/-- Stagewise limit `⋆`-homomorphism `A n →⋆ₙₐ[ℂ] D` constructed from an approximate cocone. -/
private noncomputable def stageHom (hc : IsApproximateCocone α ξ F τ) (n : ℕ) : A n →⋆ₙₐ[ℂ] D where
  toFun a := hc.stageLim a
  map_zero' := tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n 0) <| by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_add' a b := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (a + b))
      (((hc.tendsto_evalAt_stageLim n a).add (hc.tendsto_evalAt_stageLim n b)).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_mul' a b := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (a * b))
      (((hc.tendsto_evalAt_stageLim n a).mul (hc.tendsto_evalAt_stageLim n b)).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_smul' c a := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (c • a))
      (((hc.tendsto_evalAt_stageLim n a).const_smul c).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_star' a := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (star a))
      ((hc.tendsto_evalAt_stageLim n a).star.congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm, map_star]

private theorem tendsto_evalAt_stageHom (hc : IsApproximateCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (evalAt α ξ a) atTop (𝓝 (hc.stageHom n a)) :=
  hc.tendsto_evalAt_stageLim n a

private theorem tendsto_stageHom (hc : IsApproximateCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (hc.stageHom n a)) := by
  simpa only [Function.comp_def, id_eq, evalAt_add] using
    (hc.tendsto_evalAt_stageHom n a).comp (tendsto_id.nonneg_add_atTop fun _ ↦ Nat.zero_le n)

private theorem stageHom_seqTransHom (hc : IsApproximateCocone α ξ F τ) {m n : ℕ} (h : m ≤ n)
    (a : A m) : hc.stageHom n (seqTransHom α h a) = hc.stageHom m a :=
  tendsto_nhds_unique (hc.tendsto_evalAt_stageHom n _)
    ((hc.tendsto_evalAt_stageHom m a).congr' (evalAt_eventuallyEq_seqTransHom h a).symm)

private theorem stageHom_comp (hc : IsApproximateCocone α ξ F τ) (n : ℕ) :
    (hc.stageHom (n + 1)).comp (α n) = hc.stageHom n := by
  ext a
  simpa only [NonUnitalStarAlgHom.comp_apply, seqTransHom_le_succ] using
    hc.stageHom_seqTransHom (Nat.le_succ n) a

/-- The `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D` induced by an approximate cocone on a sequential colimit
cocone. -/
noncomputable def hom (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι) :
    C →⋆ₙₐ[ℂ] D :=
  hι.lift hc.stageHom hc.stageHom_comp

/-- On every stage element `a : A n`, the forward images `ξ (n + k) (seqTransHom α _ a)` converge
in norm to `hc.hom hι (ι n a)`. -/
theorem tendsto_hom (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι)
    (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (hc.hom hι (ι n a))) := by
  rw [hom, hι.lift_apply]
  exact hc.tendsto_stageHom n a

/-- Uniqueness of the limit `⋆`-homomorphism induced by an approximate cocone. -/
theorem hom_unique (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι)
    {Φ : C →⋆ₙₐ[ℂ] D}
    (hΦ : ∀ n a, Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (Φ (ι n a)))) :
    Φ = hc.hom hι :=
  hι.hom_ext fun n a ↦ tendsto_nhds_unique (hΦ n a) (hc.tendsto_hom hι n a)

/-- Quantitative tail-error bound: on `a ∈ F n`, `hc.hom hι (ι n a)` is within `∑' k, τ (n + k)`
of the stage map `ξ n a`. -/
theorem norm_hom_sub_le (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι)
    {n : ℕ} {a : A n} (ha : a ∈ F n) :
    ‖hc.hom hι (ι n a) - ξ n a‖ ≤ ∑' k, τ (n + k) := by
  have h0 : ξ (n + 0) (seqTransHom α (Nat.le_add_right n 0) a) = ξ n a := by simp
  rw [norm_sub_rev, ← dist_eq_norm, ← h0]
  exact dist_le_tsum_of_dist_le_of_tendsto₀ (fun k ↦ τ (n + k)) (hc.dist_step_le ha)
    (hc.summable.comp_injective (add_right_injective n)) (hc.tendsto_hom hι n a)

/-- Postcomposing `hc.hom hι` with `Ψ` equals `Θ` whenever `Ψ (ξ n a)` approximates `Θ (ι n a)` on
`F n` within a vanishing error `r n → 0`. -/
theorem comp_hom_eq_of_norm_sub_le {E : Type*} [NonUnitalCStarAlgebra E]
    (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι)
    {Ψ : D →⋆ₙₐ[ℂ] E} {Θ : C →⋆ₙₐ[ℂ] E} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ n ⦃a⦄, a ∈ F n → ‖Ψ (ξ n a) - Θ (ι n a)‖ ≤ r n) :
    Ψ.comp (hc.hom hι) = Θ := by
  refine hι.hom_ext_of_approx hc.approx fun m x hx ↦ ?_
  have hlim₁ : Tendsto
      (fun k ↦ Ψ (ξ (m + k) (seqTransHom α (Nat.le_add_right m k) x)))
      atTop (𝓝 (Ψ (hc.hom hι (ι m x)))) :=
    (map_continuous Ψ).continuousAt.tendsto.comp (hc.tendsto_hom hι m x)
  have hlim₂ : Tendsto
      (fun k ↦ Ψ (ξ (m + k) (seqTransHom α (Nat.le_add_right m k) x)))
      atTop (𝓝 (Θ (ι m x))) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (a := fun k ↦ r (m + k)) (fun k ↦ ?_)
      (hr.comp (tendsto_id.nonneg_add_atTop fun _ ↦ Nat.zero_le m))
    rw [← hι.comp_seqTransHom_apply (Nat.le_add_right m k) x]
    exact hbound (m + k) (seqTransHom_mem hc.mapsTo (Nat.le_add_right m k) hx)
  exact tendsto_nhds_unique hlim₁ hlim₂

end IsApproximateCocone

end ApproximateCocone

section Intertwining

variable {A B : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)] [∀ n, NonUnitalCStarAlgebra (B n)]
  {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- An *approximate intertwining* between sequential C⋆-systems `(A, α)` and `(B, β)` consists of
stage maps `φ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ n : B n →⋆ₙₐ[ℂ] A n`, propagating subsets
`F n ⊆ A n` and `G n ⊆ B n` that asymptotically approximate every stage element, and summable
triangle tolerances `δ, ε : ℕ → ℝ` bounding `‖ψ (n + 1) (φ n a) - α n a‖ ≤ δ n` on `F n` and
`‖φ n (ψ n b) - β n b‖ ≤ ε n` on `G n` (Rørdam, *Classification of Nuclear C⋆-Algebras*,
Proposition 2.3.2). -/
structure IsApproximateIntertwining
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (F : ∀ n, Set (A n)) (G : ∀ n, Set (B n)) (δ ε : ℕ → ℝ) : Prop where
  /-- Forward propagation of `F` along `α`. -/
  mapsTo_α (n : ℕ) ⦃a : A n⦄ : a ∈ F n → α n a ∈ F (n + 1)
  /-- Forward propagation of `G` along `β`. -/
  mapsTo_β (n : ℕ) ⦃b : B n⦄ : b ∈ G n → β n b ∈ G (n + 1)
  /-- Propagation from `F n` into `G (n + 1)` under `φ n`. -/
  mapsTo_φ (n : ℕ) ⦃a : A n⦄ : a ∈ F n → φ n a ∈ G (n + 1)
  /-- Propagation from `G n` into `F n` under `ψ n`. -/
  mapsTo_ψ (n : ℕ) ⦃b : B n⦄ : b ∈ G n → ψ n b ∈ F n
  /-- Asymptotic stagewise density of `(F n)` along `α`. -/
  approx_A (n : ℕ) (a : A n) (r : ℝ) :
    0 < r → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < r
  /-- Asymptotic stagewise density of `(G n)` along `β`. -/
  approx_B (n : ℕ) (b : B n) (r : ℝ) :
    0 < r → ∃ k, ∃ y ∈ G (n + k), ‖seqTransHom β (Nat.le_add_right n k) b - y‖ < r
  /-- Upper-triangle commutation estimate on `F n`. -/
  norm_ψ_φ_sub_le (n : ℕ) ⦃a : A n⦄ : a ∈ F n → ‖ψ (n + 1) (φ n a) - α n a‖ ≤ δ n
  /-- Lower-triangle commutation estimate on `G n`. -/
  norm_φ_ψ_sub_le (n : ℕ) ⦃b : B n⦄ : b ∈ G n → ‖φ n (ψ n b) - β n b‖ ≤ ε n
  /-- Summability of the upper-triangle tolerances `δ`. -/
  summable_δ : Summable δ
  /-- Summability of the lower-triangle tolerances `ε`. -/
  summable_ε : Summable ε

namespace IsApproximateIntertwining

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
  {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}
  {φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)} {ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n}
  {F : ∀ n, Set (A n)} {G : ∀ n, Set (B n)} {δ ε : ℕ → ℝ}

private theorem norm_cocone_sub_le {X : Type*} [NonUnitalCStarAlgebra X]
    {Y : ℕ → Type*} [∀ m, NonUnitalCStarAlgebra (Y m)] {E : Type*} [NonUnitalCStarAlgebra E]
    {γ : ∀ m, Y m →⋆ₙₐ[ℂ] Y (m + 1)} {ι : ∀ m, Y m →⋆ₙₐ[ℂ] E}
    (hι : IsSeqColimitCocone γ ι) (m : ℕ) (f : X →⋆ₙₐ[ℂ] Y (m + 1)) (x z : X) (y : Y m) :
    ‖ι (m + 1) (f x) - ι m y‖ ≤ ‖z - x‖ + ‖f z - γ m y‖ := by
  rw [← hι.comp_apply m y, ← map_sub]
  refine (NonUnitalStarAlgHom.norm_apply_le _ _).trans ?_
  calc
    ‖f x - γ m y‖ ≤ ‖f x - f z‖ + ‖f z - γ m y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖z - x‖ + ‖f z - γ m y‖ := by
      rw [← map_sub, norm_sub_rev z]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- The forward stage maps `(ιB (n + 1)).comp (φ n)` form an approximate cocone on `(A, α)` with
step error `δ n + ε (n + 1)`. -/
theorem isApproximateCocone_forward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιB : IsSeqColimitCocone β ιB) :
    IsApproximateCocone α (fun n ↦ (ιB (n + 1)).comp (φ n)) F (fun n ↦ δ n + ε (n + 1)) where
  mapsTo := h.mapsTo_α
  approx := h.approx_A
  summable := h.summable_δ.add ((summable_nat_add_iff 1).mpr h.summable_ε)
  norm_sub_le n a ha :=
    (norm_cocone_sub_le hιB (n + 1) (φ (n + 1)) (α n a) (ψ (n + 1) (φ n a)) (φ n a)).trans
      (add_le_add (h.norm_ψ_φ_sub_le n ha) (h.norm_φ_ψ_sub_le (n + 1) (h.mapsTo_φ n ha)))

/-- The backward stage maps `(ιA n).comp (ψ n)` form an approximate cocone on `(B, β)` with step
error `ε n + δ n`. -/
theorem isApproximateCocone_backward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) :
    IsApproximateCocone β (fun n ↦ (ιA n).comp (ψ n)) G (fun n ↦ ε n + δ n) where
  mapsTo := h.mapsTo_β
  approx := h.approx_B
  summable := h.summable_ε.add h.summable_δ
  norm_sub_le n b hb :=
    (norm_cocone_sub_le hιA n (ψ (n + 1)) (β n b) (φ n (ψ n b)) (ψ n b)).trans
      (add_le_add (h.norm_φ_ψ_sub_le n hb) (h.norm_ψ_φ_sub_le n (h.mapsTo_ψ n hb)))

private theorem comp_hom_eq_of_isApproximateCocone {E : Type*} [NonUnitalCStarAlgebra E]
    {σ : ℕ → ℕ} {η : ∀ n, A n →⋆ₙₐ[ℂ] B (σ n)} {ξ : ∀ m, B m →⋆ₙₐ[ℂ] E}
    {τ₁ τ₂ ν : ℕ → ℝ} {Θ : C →⋆ₙₐ[ℂ] E}
    (hc₁ : IsApproximateCocone α (fun n ↦ (ιB (σ n)).comp (η n)) F τ₁)
    (hιA : IsSeqColimitCocone α ιA)
    (hc₂ : IsApproximateCocone β ξ G τ₂)
    (hιB : IsSeqColimitCocone β ιB)
    (hσ : Tendsto σ atTop atTop)
    (hmaps : ∀ n ⦃a⦄, a ∈ F n → η n a ∈ G (σ n))
    (hν : Tendsto ν atTop (𝓝 0))
    (htri : ∀ n ⦃a⦄, a ∈ F n → ‖ξ (σ n) (η n a) - Θ (ιA n a)‖ ≤ ν n) :
    (hc₂.hom hιB).comp (hc₁.hom hιA) = Θ := by
  have htail : Tendsto (fun m ↦ ∑' j, τ₂ (m + j)) atTop (𝓝 0) :=
    (_root_.tendsto_sum_nat_add τ₂).congr fun m ↦ tsum_congr fun j ↦ congrArg τ₂ (Nat.add_comm j m)
  refine hc₁.comp_hom_eq_of_norm_sub_le hιA
    (r := fun n ↦ (∑' j, τ₂ (σ n + j)) + ν n)
    (by simpa only [Function.comp_def, add_zero] using (htail.comp hσ).add hν) fun n a ha ↦ ?_
  simpa only [NonUnitalStarAlgHom.comp_apply] using
    (norm_sub_le_norm_sub_add_norm_sub
      (hc₂.hom hιB (ιB (σ n) (η n a))) (ξ (σ n) (η n a)) (Θ (ιA n a))).trans
      (add_le_add (hc₂.norm_hom_sub_le hιB (hmaps n ha)) (htri n ha))

private theorem backward_comp_forward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) :
    ((h.isApproximateCocone_backward hιA).hom hιB).comp
      ((h.isApproximateCocone_forward hιB).hom hιA) = .id ℂ C := by
  refine comp_hom_eq_of_isApproximateCocone (σ := fun n ↦ n + 1)
    (h.isApproximateCocone_forward hιB) hιA (h.isApproximateCocone_backward hιA) hιB
    (tendsto_add_atTop_nat 1) h.mapsTo_φ h.summable_δ.tendsto_atTop_zero fun n a ha ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq]
  rw [← hιA.comp_apply n a, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (h.norm_ψ_φ_sub_le n ha)

private theorem forward_comp_backward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) :
    ((h.isApproximateCocone_forward hιB).hom hιA).comp
      ((h.isApproximateCocone_backward hιA).hom hιB) = .id ℂ D := by
  refine comp_hom_eq_of_isApproximateCocone (σ := fun n ↦ n)
    (h.isApproximateCocone_backward hιA) hιB (h.isApproximateCocone_forward hιB) hιA
    tendsto_id h.mapsTo_ψ h.summable_ε.tendsto_atTop_zero fun n b hb ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq]
  rw [← hιB.comp_apply n b, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (h.norm_φ_ψ_sub_le n hb)

/-- Elliott's approximate-intertwining `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D` constructed from mutually
inverse forward and backward approximate cocones (Rørdam, Proposition 2.3.2). -/
noncomputable def equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) : C ≃⋆ₐ[ℂ] D :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    ((h.isApproximateCocone_forward hιB).hom hιA)
    ((h.isApproximateCocone_backward hιA).hom hιB)
    (h.backward_comp_forward hιA hιB)
    (h.forward_comp_backward hιA hιB)

@[simp]
theorem toNonUnitalStarAlgHom_equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) :
    (h.equiv hιA hιB).toNonUnitalStarAlgHom = (h.isApproximateCocone_forward hιB).hom hιA :=
  StarAlgEquiv.toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom ..

@[simp]
theorem toNonUnitalStarAlgHom_equiv_symm (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) :
    (h.equiv hιA hιB).symm.toNonUnitalStarAlgHom =
      (h.isApproximateCocone_backward hιA).hom hιB :=
  StarAlgEquiv.toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom ..

/-- Forward stagewise convergence characterizing `IsApproximateIntertwining.equiv`. -/
theorem tendsto_equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ιB (n + k + 1) (φ (n + k) (seqTransHom α (Nat.le_add_right n k) a)))
      atTop (𝓝 (h.equiv hιA hιB (ιA n a))) := by
  rw [← StarAlgEquiv.toNonUnitalStarAlgHom_apply, h.toNonUnitalStarAlgHom_equiv]
  exact (h.isApproximateCocone_forward hιB).tendsto_hom hιA n a

/-- Backward stagewise convergence characterizing `(IsApproximateIntertwining.equiv).symm`. -/
theorem tendsto_equiv_symm (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) (n : ℕ) (b : B n) :
    Tendsto (fun k ↦ ιA (n + k) (ψ (n + k) (seqTransHom β (Nat.le_add_right n k) b)))
      atTop (𝓝 ((h.equiv hιA hιB).symm (ιB n b))) := by
  rw [← StarAlgEquiv.toNonUnitalStarAlgHom_apply, h.toNonUnitalStarAlgHom_equiv_symm]
  exact (h.isApproximateCocone_backward hιA).tendsto_hom hιB n b

/-- Uniqueness of the `⋆`-isomorphism induced by an approximate intertwining. -/
theorem equiv_unique (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB)
    {θ : C ≃⋆ₐ[ℂ] D}
    (hθ : ∀ n a, Tendsto
      (fun k ↦ ιB (n + k + 1) (φ (n + k) (seqTransHom α (Nat.le_add_right n k) a)))
      atTop (𝓝 (θ (ιA n a)))) :
    θ = h.equiv hιA hιB := by
  have heq : θ.toNonUnitalStarAlgHom = (h.equiv hιA hιB).toNonUnitalStarAlgHom := by
    rw [h.toNonUnitalStarAlgHom_equiv]
    exact (h.isApproximateCocone_forward hιB).hom_unique hιA hθ
  ext x
  exact DFunLike.congr_fun heq x

/-- Quantitative forward tail-error bound: on `a ∈ F n`, `h.equiv hιA hιB (ιA n a)` is within
`∑' k, (δ (n + k) + ε (n + k + 1))` of `ιB (n + 1) (φ n a)`. -/
theorem norm_equiv_sub_le (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) {n : ℕ} {a : A n}
    (ha : a ∈ F n) :
    ‖h.equiv hιA hιB (ιA n a) - ιB (n + 1) (φ n a)‖ ≤ ∑' k, (δ (n + k) + ε (n + k + 1)) := by
  rw [← StarAlgEquiv.toNonUnitalStarAlgHom_apply, h.toNonUnitalStarAlgHom_equiv]
  exact (h.isApproximateCocone_forward hιB).norm_hom_sub_le hιA ha

/-- Quantitative backward tail-error bound: on `b ∈ G n`, `(h.equiv hιA hιB).symm (ιB n b)` is
within `∑' k, (ε (n + k) + δ (n + k))` of `ιA n (ψ n b)`. -/
theorem norm_equiv_symm_sub_le (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB) {n : ℕ} {b : B n}
    (hb : b ∈ G n) :
    ‖(h.equiv hιA hιB).symm (ιB n b) - ιA n (ψ n b)‖ ≤ ∑' k, (ε (n + k) + δ (n + k)) := by
  rw [← StarAlgEquiv.toNonUnitalStarAlgHom_apply, h.toNonUnitalStarAlgHom_equiv_symm]
  exact (h.isApproximateCocone_backward hιA).norm_hom_sub_le hιB hb

end IsApproximateIntertwining

end Intertwining

end TauCeti
