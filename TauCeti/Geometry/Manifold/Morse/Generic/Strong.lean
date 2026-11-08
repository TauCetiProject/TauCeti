/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Generic.Relative
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong
import TauCeti.Algebra.Order.Group.Bounds
import TauCeti.Analysis.SpecificLimits.HalfPowSucc
import TauCeti.Geometry.Manifold.ContMDiffMap.CompactExhaustion
import TauCeti.Geometry.Manifold.Exhaustion
import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Morse approximation in the strong Whitney topology

On a boundaryless finite-dimensional Hausdorff sigma-compact manifold `M`, every smooth function
`f : M → ℝ` is a limit of Morse functions in the strong Whitney topology
(`TauCeti.dense_setOf_isMorse_manifoldStrongWhitney`). More precisely, for every strong `C^k`
neighbourhood `c.ball f` of `f` and every continuous positive tolerance `ε`, there is a Morse
function `g ∈ c.ball f` with `|g - f| < ε` everywhere; if `f` is already Morse on an open
neighbourhood of a closed set `C`, then `g` can be chosen equal to `f` near `C`
(`ContMDiffMap.exists_isMorse_mem_ball_sub_compl`). With `ε = 1` the approximation keeps a proper
function proper, with no separate sigma-compactness hypothesis needed because a proper map into
`ℝ` already makes `M` sigma-compact (`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`), and so
every boundaryless finite-dimensional Hausdorff sigma-compact manifold carries a proper Morse
function bounded below (`TauCeti.exists_isMorse_isProperMap_bddBelow`).

The proof runs the relative compact approximation
`ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl` along a compact exhaustion
`L 0 = ∅ ⊆ L 1 ⊆ ⋯` of `M`. At stage `r` the current function, already Morse on `L r`, is made
Morse on `L (r + 1)` by a compactly supported perturbation inside `interior (L (r + 2)) \ L (r - 1)`
and away from `C`. Each point lies in only finitely many of these supports, so the perturbations
stabilize near every point and their limit is smooth and Morse. The perturbation at stage `r`
is chosen within the fraction `2⁻⁽ʳ⁺¹⁾` of the prescribed tolerances on the finitely many members
of the strong control meeting `L (r + 2)`, and within `2⁻⁽ʳ⁺¹⁾ ε` on `L (r + 2)`, so the
accumulated perturbation stays inside the prescribed neighbourhood. Since the supports are locally
finite, no convergence of infinitely many perturbations or Baire category argument is needed.

## Main results

* `ContMDiffMap.exists_isMorse_mem_ball_sub_compl`: relative Morse approximation in a strong
  `C^k` neighbourhood with a global `C⁰` tolerance.
* `TauCeti.dense_setOf_isMorse_manifoldStrongWhitney`: **Morse functions are dense** in the strong
  Whitney topology.
* `ContMDiffMap.exists_isMorse_isProperMap_mem_ball`: relative proper Morse approximation within
  `C⁰` distance `1`.
* `TauCeti.exists_isMorse_isProperMap_bddBelow`: every such manifold carries a proper Morse
  function which is bounded below.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1, for the strong topology, and Chapter 6, §1, where Morse functions are shown to
  be dense in it.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §6, Corollary 6.8, for the existence of a Morse function with compact sublevels.
-/

public section

open Filter Set Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- One stage of the strong Morse approximation. A function `φ` which is Morse on `K₀` and agrees
with `f` near `C`, where `f` is Morse on a neighbourhood `V` of `C`, is made Morse on a compact
set `K₁` by a perturbation in a prescribed neighbourhood of `φ`. The perturbation is supported
away from `C`, in an open set `W` containing the part of `K₁` outside `interior K₀`. -/
private theorem exists_isMorseOn_tsupport_sub_inter_compl (f φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V) (hfV : IsMorseOn I f V)
    (hφC : tsupport (fun x ↦ φ x - f x) ⊆ Cᶜ) {K₀ K₁ W : Set M} (hφ : IsMorseOn I φ K₀)
    (hK₁ : IsCompact K₁) (hW : IsOpen W) (hK : K₁ \ W ⊆ interior K₀)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 φ) :
    ∃ ψ ∈ 𝒰, IsMorseOn I ψ K₁ ∧ tsupport (fun x ↦ ψ x - φ x) ⊆ W ∩ Cᶜ := by
  have hO : IsOpen (tsupport fun x ↦ φ x - f x)ᶜ := (isClosed_tsupport _).isOpen_compl
  -- Near `C` the function `φ` is still `f`, hence Morse.
  have hφV : IsMorseOn I φ (V ∩ (tsupport fun x ↦ φ x - f x)ᶜ) :=
    (hfV.mono inter_subset_left).congr (hV.inter hO) fun x hx ↦
      sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun y ↦ φ y - f y) hx.2)
  have hφV' : IsMorseOn I φ (V ∩ (tsupport fun x ↦ φ x - f x)ᶜ ∪ interior K₀) :=
    isMorseOn_of_forall_exists_mem_nhds fun x hx ↦ hx.elim
      (fun hx ↦ ⟨_, (hV.inter hO).mem_nhds hx, hφV⟩)
      (fun hx ↦ ⟨_, isOpen_interior.mem_nhds hx, hφ.mono interior_subset⟩)
  have hsub : K₁ ∩ (C ∪ Wᶜ) ⊆ V ∩ (tsupport fun x ↦ φ x - f x)ᶜ ∪ interior K₀ := by
    rintro x ⟨hxK, hxC | hxW⟩
    · exact Or.inl ⟨hCV hxC, fun hx ↦ hφC hx hxC⟩
    · exact Or.inr (hK ⟨hxK, hxW⟩)
  obtain ⟨ψ, hψ𝒰, hψ, -, hψs⟩ := φ.exists_isMorseOn_hasCompactSupport_sub_compl hK₁
    (hC.union hW.isClosed_compl) ((hV.inter hO).union isOpen_interior) hsub hφV' h𝒰
  refine ⟨ψ, hψ𝒰, hψ, hψs.trans ?_⟩
  rw [compl_union, compl_compl, inter_comm]

open ContMDiffMap in
/-- One stage of the strong Morse approximation along a compact exhaustion `L`. The function `φ`,
Morse on `L r` and equal to `f` near `C`, is made Morse on `L (r + 1)` by a perturbation supported
in `interior (L (r + 2)) \ L (r - 1)` away from `C`, small in the seminorms `p i` for the finitely
many `i` with `A i` meeting `L (r + 2)` (the bound is `t i * w r`), and small on `L (r + 2)` (the
bound is `ε x * w r`). -/
private theorem exists_isMorseOn_stage (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {C V : Set M} (hC : IsClosed C)
    (hV : IsOpen V) (hCV : C ⊆ V) (hfV : IsMorseOn I f V) {ι : Type*} (A : ι → Set M)
    (p : ι → Seminorm ℝ C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hfin : ∀ K, IsCompact K → {i | (A i ∩ K).Nonempty}.Finite)
    (hp : ∀ i (φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {δ : ℝ}, 0 < δ → ∀ᶠ ψ in 𝓝 φ, p i (ψ - φ) < δ)
    (L : CompactExhaustion M) (hLpred : ∀ r, L (r - 1) ⊆ interior (L r)) {ε : M → ℝ}
    (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x) {w : ℕ → ℝ} (hw : ∀ r, 0 < w r) (r : ℕ)
    (φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (hφ : IsMorseOn I φ (L r))
    (hφC : tsupport (fun x ↦ φ x - f x) ⊆ Cᶜ) :
    ∃ ψ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯,
      ((∀ i, (A i ∩ L (r + 2)).Nonempty → p i (ψ - φ) < t i * w r) ∧
        ∀ x ∈ L (r + 2), |ψ x - φ x| < ε x * w r) ∧ IsMorseOn I ψ (L (r + 1)) ∧
      tsupport (fun x ↦ ψ x - φ x) ⊆ (interior (L (r + 2)) \ L (r - 1)) ∩ Cᶜ := by
  have h𝒰 : ∀ᶠ ψ in 𝓝 φ,
      (∀ i, (A i ∩ L (r + 2)).Nonempty → p i (ψ - φ) < t i * w r) ∧
        ∀ x ∈ L (r + 2), |ψ x - φ x| < ε x * w r := by
    refine ((Filter.eventually_all_finite (hfin _ (L.isCompact _))).2 fun i _ ↦ ?_).and ?_
    · exact hp i φ (mul_pos (ht i) (hw r))
    · exact (eventually_forall_dist_lt φ (L.isCompact _) (δ := fun x ↦ ε x * w r)
        (hε.mul continuous_const) fun x _ ↦ mul_pos (hε₀ x) (hw r)).mono fun ψ hψ x hx ↦ by
          simpa only [Real.dist_eq] using hψ x hx
  -- Off `interior (L (r + 2)) \ L (r - 1)`, the part of `L (r + 1)` lies in `interior (L r)`.
  have hK : L (r + 1) \ (interior (L (r + 2)) \ L (r - 1)) ⊆ interior (L r) := fun x hx ↦
    hLpred r (not_not.mp fun h ↦ hx.2 ⟨L.subset_interior_succ _ hx.1, h⟩)
  obtain ⟨ψ, hψ𝒰, hψ, hψs⟩ := exists_isMorseOn_tsupport_sub_inter_compl f φ hC hV hCV hfV hφC hφ
    (L.isCompact (r + 1)) (isOpen_interior.sdiff (L.isCompact _).isClosed) hK h𝒰
  exact ⟨ψ, hψ𝒰, hψ, hψs⟩

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- Iterating a stage. If every function `φ`, Morse on `L r` and equal to `f` near `C`, admits a
stage `ψ` (related to `φ` by `Q r`) which is Morse on `L (r + 1)` and differs from `φ` by a
perturbation supported in `interior (L (r + 2)) \ L (r - 1)` away from `C`, then there is a
sequence `F` starting at `f` all of whose stages are of this kind. -/
private theorem exists_stages_of_step (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {C : Set M} (L : CompactExhaustion M)
    (hL0 : L 0 = ∅) (Q : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ → Prop)
    (step : ∀ (r : ℕ) (φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯), IsMorseOn I φ (L r) →
      tsupport (fun x ↦ φ x - f x) ⊆ Cᶜ → ∃ ψ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, Q r φ ψ ∧
        IsMorseOn I ψ (L (r + 1)) ∧
        tsupport (fun x ↦ ψ x - φ x) ⊆ (interior (L (r + 2)) \ L (r - 1)) ∩ Cᶜ) :
    ∃ F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, F 0 = f ∧ (∀ r, Q r (F r) (F (r + 1))) ∧
      (∀ r, IsMorseOn I (F r) (L r) ∧ tsupport (fun x ↦ F r x - f x) ⊆ Cᶜ) ∧
      ∀ r, tsupport (fun x ↦ F (r + 1) x - F r x) ⊆ (interior (L (r + 2)) \ L (r - 1)) ∩ Cᶜ := by
  choose! next hnext_Q hnext_morse hnext_supp using step
  let F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := fun r ↦ Nat.rec f (fun r φ ↦ next r φ) r
  have hF : ∀ r, F (r + 1) = next r (F r) := fun r ↦ rfl
  have hFinv : ∀ r, IsMorseOn I (F r) (L r) ∧ tsupport (fun x ↦ F r x - f x) ⊆ Cᶜ := by
    intro r
    induction r with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hL0]
        exact isMorseOn_empty
      · simp [F]
    | succ r ih =>
      refine ⟨hF r ▸ hnext_morse r _ ih.1 ih.2, ?_⟩
      have hsub : (fun x ↦ F (r + 1) x - f x) =
          (fun x ↦ F (r + 1) x - F r x) + fun x ↦ F r x - f x := by
        ext x
        simp
      rw [hsub]
      refine (tsupport_add _ _).trans (union_subset ?_ ih.2)
      rw [hF]
      exact (hnext_supp r _ ih.1 ih.2).trans inter_subset_right
  exact ⟨F, rfl, fun r ↦ hF r ▸ hnext_Q r _ (hFinv r).1 (hFinv r).2, hFinv,
    fun r ↦ hF r ▸ hnext_supp r _ (hFinv r).1 (hFinv r).2⟩

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- The limit `g` of the stages is Morse and agrees with `f` near `C`. -/
private theorem isMorse_tsupport_of_stages (L : CompactExhaustion M) {C : Set M}
    (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (hgF : ∀ N, EqOn g (F (N + 1)) (L N))
    (hFinv : ∀ r, IsMorseOn I (F r) (L r) ∧ tsupport (fun x ↦ F r x - f x) ⊆ Cᶜ) :
    IsMorse I g ∧ tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  refine ⟨?_, ?_⟩
  · -- Near each point `g` agrees with a function which is Morse there.
    refine isMorseOn_univ.mp (isMorseOn_of_forall_exists_mem_nhds fun x _ ↦ ?_)
    obtain ⟨N, hN⟩ := L.exists_mem_nhds x
    exact ⟨interior (L N), interior_mem_nhds.mpr hN,
      ((hFinv (N + 1)).1.mono (interior_subset.trans (L.subset_succ N))).congr isOpen_interior
        fun y hy ↦ hgF N (interior_subset hy)⟩
  · -- Near `C` every stage, hence `g`, agrees with `f`.
    intro x hx hxC
    obtain ⟨N, hN⟩ := L.exists_mem_nhds x
    have hx' : x ∉ tsupport fun y ↦ F (N + 1) y - f y := fun h ↦ (hFinv (N + 1)).2 h hxC
    refine notMem_tsupport_iff_eventuallyEq.mpr ?_ hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx', hN] with y hy hyN
    simpa [hgF N hyN] using hy

section SigmaCompact

variable [SigmaCompactSpace M]

/-- The strong Morse approximation, for an abstract family of seminorms `p i` with compact
supports `A i`, locally finite in the sense that only finitely many meet each compact set. The
function `g` is within `t i` of `f` for `p i`, within `ε` of `f` pointwise, Morse, and equal to
`f` near `C`. -/
private theorem exists_isMorse_of_seminorms (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {C V : Set M}
    (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V) (hfV : IsMorseOn I f V) {ι : Type*}
    (A : ι → Set M) (p : ι → Seminorm ℝ C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {t : ι → ℝ} (ht : ∀ i, 0 < t i)
    (hfin : ∀ K, IsCompact K → {i | (A i ∩ K).Nonempty}.Finite)
    (hp : ∀ i (φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {δ : ℝ}, 0 < δ → ∀ᶠ ψ in 𝓝 φ, p i (ψ - φ) < δ)
    (hA : ∀ i, IsCompact (A i))
    (hp0 : ∀ i (u : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯), (∀ y ∈ A i, (u : M → ℝ) =ᶠ[𝓝 y] 0) → p i u = 0)
    {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ i, p i (g - f) < t i) ∧ IsMorse I g ∧
      (∀ x, |g x - f x| < ε x) ∧ tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- A compact exhaustion starting with the empty set.
  let L := (CompactExhaustion.choice M).shiftr
  have hL0 : L 0 = ∅ := rfl
  have hLpred : ∀ r, L (r - 1) ⊆ interior (L r) := by
    rintro (_ | r)
    · simp [hL0]
    · exact L.subset_interior_succ r
  -- The weights `2⁻⁽ʳ⁺¹⁾` allotted to the successive stages sum to at most `1`.
  let w : ℕ → ℝ := fun r ↦ (1 / 2) ^ (r + 1)
  have hw : ∀ r, 0 < w r := fun r ↦ by positivity
  obtain ⟨F, hF0, hFQ, hFinv, hFsupp⟩ := exists_stages_of_step f L hL0 _
    (exists_isMorseOn_stage f hC hV hCV hfV A p ht hfin hp L hLpred hε hε₀ hw)
  have hsupp : ∀ r, tsupport (fun x ↦ F (r + 1) x - F r x) ⊆ interior (L (r + 2)) := fun r ↦
    (hFsupp r).trans (inter_subset_left.trans sdiff_subset)
  -- The stages stabilize: stage `r + 1` changes nothing on `L r`, so they have a smooth limit.
  obtain ⟨g, hgF⟩ := ContMDiffMap.exists_eqOn_of_eqOn_compactExhaustion L F fun r x hx ↦
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ F (r + 1 + 1) y - F (r + 1) y) fun h ↦ (hFsupp (r + 1) h).1.2 hx)
  obtain ⟨hgm, hgs⟩ := isMorse_tsupport_of_stages L f F g hgF hFinv
  subst hF0
  exact ⟨g, fun i ↦ L.seminorm_sub_lt_of_stages (p i) (hA i) (hp0 i) (ht i) hw
      (fun N ↦ sum_half_pow_succ_le_one N) F g hgF hsupp fun r hi ↦ (hFQ r).1 i hi,
    hgm, L.abs_sub_lt_of_stages hε₀ hw (fun N ↦ sum_half_pow_succ_le_one N) F g hgF hsupp
      fun r ↦ (hFQ r).2, hgs⟩

open ContMDiffMap in
/-- **Relative Morse approximation in the strong Whitney topology.** Every strong `C^k`
neighbourhood `c.ball f` of a smooth function `f` contains a Morse function `g` which is within a
prescribed continuous positive tolerance `ε` of `f` everywhere. If `f` is Morse on an open
neighbourhood `V` of a closed set `C`, then `g` can be chosen to agree with `f` on a
neighbourhood of `C`. -/
theorem _root_.ContMDiffMap.exists_isMorse_mem_ball_sub_compl (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (c : StrongCkControl I M ∞) {ε : M → ℝ} (hε : Continuous ε) (hε₀ : ∀ x, 0 < ε x)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V) (hfV : IsMorseOn I f V) :
    ∃ g ∈ c.ball f, IsMorse I g ∧ (∀ x, |g x - f x| < ε x) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  -- The points of `M` represented by the members of the strong control, and its seminorms.
  let A : c.ι → Set M := fun i ↦ (extChartAt I (c.center i)).symm ''
    (Subtype.val '' (c.compact i : Set (extChartAt I (c.center i)).target))
  have hA : ∀ i, IsCompact (A i) := fun i ↦
    ((c.compact i).isCompact.image continuous_subtype_val).image_of_continuousOn
      ((continuousOn_extChartAt_symm (c.center i)).mono (by rintro _ ⟨z, -, rfl⟩; exact z.2))
  let p : c.ι → Seminorm ℝ C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := fun i ↦
    chartCkSeminorm (c.center i) (c.compact i) c.order c.order_le
  obtain ⟨g, hgp, hgm, hgε, hgs⟩ := exists_isMorse_of_seminorms f hC hV hCV hfV A p
    c.tolerance_pos (fun K hK ↦ c.locallyFinite.finite_nonempty_inter_compact hK)
    (fun i φ δ hδ ↦ eventually_of_mem (ball_chartCkSeminorm_mem_nhds _ _ _ _ φ hδ) fun ψ hψ ↦
      (Seminorm.mem_ball _).mp hψ) hA
    (fun i u hu ↦ chartCkSeminorm_eq_zero_of_eventuallyEq_zero _ _ _ _ fun z hz ↦
      hu _ ⟨z, ⟨z, hz, rfl⟩, rfl⟩) hε hε₀
  exact ⟨g, StrongCkControl.mem_ball.mpr hgp, hgm, hgε, hgs⟩

open scoped TauCeti.ManifoldStrongWhitney in
/-- **Morse functions are dense in the strong Whitney topology** on the smooth functions of a
boundaryless finite-dimensional Hausdorff sigma-compact manifold. -/
theorem dense_setOf_isMorse_manifoldStrongWhitney :
    Dense {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ | IsMorse I f} := by
  intro f
  refine (mem_closure_iff_nhds_basis
    (ContMDiffMap.hasBasis_nhds_manifoldStrongWhitney f)).mpr fun c _ ↦ ?_
  obtain ⟨g, hg, hgm, -⟩ := f.exists_isMorse_mem_ball_sub_compl c continuous_const
    (fun _ ↦ one_pos) isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hgm, hg⟩

end SigmaCompact

/-- **Proper Morse approximation.** A proper smooth function `f`, already Morse on an open
neighbourhood `V` of a closed set `C`, is approximated in every strong `C^k` neighbourhood by
proper Morse functions within distance `1` of `f` and agreeing with `f` near `C`. In particular a
lower bound for `f` gives one for the approximation. -/
theorem _root_.ContMDiffMap.exists_isMorse_isProperMap_mem_ball (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (c : ContMDiffMap.StrongCkControl I M ∞) (hf : IsProperMap f)
    {C V : Set M} (hC : IsClosed C) (hV : IsOpen V) (hCV : C ⊆ V) (hfV : IsMorseOn I f V) :
    ∃ g ∈ c.ball f, IsMorse I g ∧ IsProperMap g ∧ (∀ x, |g x - f x| < 1) ∧
      tsupport (fun x ↦ g x - f x) ⊆ Cᶜ := by
  have : SigmaCompactSpace M := hf.sigmaCompactSpace
  obtain ⟨g, hg, hgm, hgf, hgs⟩ := f.exists_isMorse_mem_ball_sub_compl c continuous_const
    (fun _ ↦ one_pos) hC hV hCV hfV
  refine ⟨g, hg, hgm, hf.of_dist_le g.contMDiff.continuous (C := 1) fun x ↦ ?_, hgf, hgs⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact (hgf x).le

/-- **Existence of proper Morse functions.** A boundaryless finite-dimensional Hausdorff
sigma-compact manifold carries a proper Morse function which is bounded below. -/
theorem exists_isMorse_isProperMap_bddBelow [SigmaCompactSpace M] :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsMorse I g ∧ IsProperMap g ∧ BddBelow (range g) := by
  obtain ⟨f, hf, hf₀⟩ := exists_contMDiffMap_isProperMap_nonneg (M := M) I
  obtain ⟨g, -, hgm, hgp, hgf, -⟩ :=
    f.exists_isMorse_isProperMap_mem_ball ContMDiffMap.StrongCkControl.empty hf
      isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  exact ⟨g, hgm, hgp,
    BddBelow.range_of_abs_sub_le ⟨0, forall_mem_range.2 hf₀⟩ fun x ↦ (hgf x).le⟩

end TauCeti
