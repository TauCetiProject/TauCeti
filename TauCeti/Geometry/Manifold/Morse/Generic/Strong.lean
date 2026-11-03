/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Generic.Relative
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.CompactExhaustion
import TauCeti.Geometry.Manifold.Exhaustion
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
function proper (`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`), and so every such manifold
carries a proper Morse function bounded below (`TauCeti.exists_isMorse_isProperMap_bddBelow`).

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
* `ContMDiffMap.exists_isMorse_isProperMap_mem_ball`: a proper function is approximated by proper
  Morse functions within `C⁰` distance `1`.
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

variable [SigmaCompactSpace M]

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
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- A compact exhaustion starting with the empty set.
  let L := (CompactExhaustion.choice M).shiftr
  have hL0 : L 0 = ∅ := rfl
  have hLpred : ∀ r, L (r - 1) ⊆ interior (L r) := by
    rintro (_ | r)
    · simp [hL0]
    · exact L.subset_interior_succ r
  -- The points of `M` represented by the members of the strong control, and its seminorms.
  let A : c.ι → Set M := fun i ↦ (extChartAt I (c.center i)).symm ''
    (Subtype.val '' (c.compact i : Set (extChartAt I (c.center i)).target))
  have hA : ∀ i, IsCompact (A i) := fun i ↦
    ((c.compact i).isCompact.image continuous_subtype_val).image_of_continuousOn
      ((continuousOn_extChartAt_symm (c.center i)).mono (by rintro _ ⟨z, -, rfl⟩; exact z.2))
  let p : c.ι → Seminorm ℝ C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := fun i ↦
    chartCkSeminorm (c.center i) (c.compact i) c.order c.order_le
  have hp0 : ∀ i (u : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯), (∀ y ∈ A i, (u : M → ℝ) =ᶠ[𝓝 y] 0) → p i u = 0 :=
    fun i u hu ↦ chartCkSeminorm_eq_zero_of_eventuallyEq_zero _ _ _ _ fun z hz ↦
      hu _ ⟨z, ⟨z, hz, rfl⟩, rfl⟩
  -- The weights `2⁻⁽ʳ⁺¹⁾` allotted to the successive stages sum to at most `1`.
  let w : ℕ → ℝ := fun r ↦ (1 / 2) ^ (r + 1)
  have hw : ∀ r, 0 < w r := fun r ↦ by positivity
  have hwsum : ∀ N, ∑ r ∈ Finset.range N, w r ≤ 1 := fun N ↦ by
    have h := sum_geometric_two_le N
    have hw' : ∑ r ∈ Finset.range N, w r = 1 / 2 * ∑ r ∈ Finset.range N, (1 / 2 : ℝ) ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ pow_succ' _ _
    linarith
  -- One stage: make the function Morse on `L (r + 1)` by a perturbation supported in
  -- `interior (L (r + 2)) \ L (r - 1)` away from `C`, and small on `L (r + 2)`.
  have step : ∀ (r : ℕ) (φ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯), IsMorseOn I φ (L r) →
      tsupport (fun x ↦ φ x - f x) ⊆ Cᶜ → ∃ ψ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯,
        (∀ i, (A i ∩ L (r + 2)).Nonempty → p i (ψ - φ) < c.tolerance i * w r) ∧
        (∀ x ∈ L (r + 2), |ψ x - φ x| < ε x * w r) ∧ IsMorseOn I ψ (L (r + 1)) ∧
        tsupport (fun x ↦ ψ x - φ x) ⊆ (interior (L (r + 2)) \ L (r - 1)) ∩ Cᶜ := by
    intro r φ hφ hφC
    have hfin : {i | (A i ∩ L (r + 2)).Nonempty}.Finite :=
      c.locallyFinite.finite_nonempty_inter_compact (L.isCompact _)
    have h𝒰 : ∀ᶠ ψ in 𝓝 φ,
        (∀ i, (A i ∩ L (r + 2)).Nonempty → p i (ψ - φ) < c.tolerance i * w r) ∧
          ∀ x ∈ L (r + 2), |ψ x - φ x| < ε x * w r := by
      refine ((Filter.eventually_all_finite hfin).2 fun i _ ↦ ?_).and ?_
      · exact eventually_of_mem (ball_chartCkSeminorm_mem_nhds _ _ _ _ φ
          (mul_pos (c.tolerance_pos i) (hw r))) fun ψ hψ ↦ (Seminorm.mem_ball _).mp hψ
      · exact (eventually_forall_dist_lt φ (L.isCompact _) (δ := fun x ↦ ε x * w r)
          (hε.mul continuous_const) fun x _ ↦ mul_pos (hε₀ x) (hw r)).mono fun ψ hψ x hx ↦ by
            simpa only [Real.dist_eq] using hψ x hx
    -- Off `interior (L (r + 2)) \ L (r - 1)`, the part of `L (r + 1)` lies in `interior (L r)`.
    have hK : L (r + 1) \ (interior (L (r + 2)) \ L (r - 1)) ⊆ interior (L r) := fun x hx ↦
      hLpred r (not_not.mp fun h ↦ hx.2 ⟨L.subset_interior_succ _ hx.1, h⟩)
    obtain ⟨ψ, hψ𝒰, hψ, hψs⟩ := exists_isMorseOn_tsupport_sub_inter_compl f φ hC hV hCV hfV hφC hφ
      (L.isCompact (r + 1)) (isOpen_interior.sdiff (L.isCompact _).isClosed) hK h𝒰
    exact ⟨ψ, hψ𝒰.1, hψ𝒰.2, hψ, hψs⟩
  -- Iterate the stages.
  choose! next hnext_p hnext_ε hnext_morse hnext_supp using step
  let F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := fun r ↦ Nat.rec f (fun r φ ↦ next r φ) r
  have hF : ∀ r, F (r + 1) = next r (F r) := fun r ↦ rfl
  have hFinv : ∀ r, IsMorseOn I (F r) (L r) ∧ tsupport (fun x ↦ F r x - f x) ⊆ Cᶜ := by
    intro r
    induction r with
    | zero =>
      refine ⟨isMorseOn_empty, ?_⟩
      simp [F]
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
  have hD_p : ∀ r i, (A i ∩ L (r + 2)).Nonempty → p i (F (r + 1) - F r) < c.tolerance i * w r :=
    fun r ↦ hF r ▸ hnext_p r _ (hFinv r).1 (hFinv r).2
  have hD_ε : ∀ r, ∀ x ∈ L (r + 2), |F (r + 1) x - F r x| < ε x * w r :=
    fun r ↦ hF r ▸ hnext_ε r _ (hFinv r).1 (hFinv r).2
  have hD_supp : ∀ r, tsupport (fun x ↦ F (r + 1) x - F r x) ⊆
      (interior (L (r + 2)) \ L (r - 1)) ∩ Cᶜ :=
    fun r ↦ hF r ▸ hnext_supp r _ (hFinv r).1 (hFinv r).2
  have hD_zero : ∀ r x, x ∉ interior (L (r + 2)) \ L (r - 1) → F (r + 1) x = F r x :=
    fun r x hx ↦ sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ F (r + 1) y - F r y) fun h ↦ hx (hD_supp r h).1)
  -- The stages stabilize: stage `r + 1` changes nothing on `L r`, so they have a smooth limit.
  obtain ⟨g, hgF⟩ := ContMDiffMap.exists_eqOn_of_eqOn_compactExhaustion L F fun r x hx ↦
    hD_zero (r + 1) x fun h ↦ h.2 hx
  -- Telescoping the perturbations up to stage `N`.
  have htel : ∀ N x, F N x - f x = ∑ r ∈ Finset.range N, (F (r + 1) x - F r x) := fun N x ↦
    (Finset.sum_range_sub (fun r ↦ F r x) N).symm
  refine ⟨g, StrongCkControl.mem_ball.mpr fun i ↦ ?_, ?_, fun x ↦ ?_, ?_⟩
  · -- Only the stages up to `N + 1` affect the `i`th member of the control.
    -- `p i` is the `i`th seminorm of the control, by definition.
    change p i (g - f) < c.tolerance i
    obtain ⟨N, hN⟩ := L.exists_superset_of_isCompact (hA i)
    have hzero : p i (g - F (N + 2)) = 0 := hp0 i _ fun y hy ↦ by
      filter_upwards [mem_interior_iff_mem_nhds.mp (L.subset_interior_succ N (hN hy))] with z hz
      simp [hgF (N + 1) hz]
    have hsum : F (N + 2) - f = ∑ r ∈ Finset.range (N + 2), (F (r + 1) - F r) :=
      (Finset.sum_range_sub F (N + 2)).symm
    have hterm : ∀ r ∈ Finset.range (N + 2), p i (F (r + 1) - F r) < c.tolerance i * w r := by
      intro r _
      by_cases hi : (A i ∩ L (r + 2)).Nonempty
      · exact hD_p r i hi
      · rw [hp0 i _ fun y hy ↦ ?_]
        · exact mul_pos (c.tolerance_pos i) (hw r)
        · have hy' : y ∉ tsupport fun x ↦ F (r + 1) x - F r x := fun h ↦
            hi ⟨y, hy, interior_subset (hD_supp r h).1.1⟩
          simpa [Pi.sub_def] using notMem_tsupport_iff_eventuallyEq.mp hy'
    calc p i (g - f) = p i ((F (N + 2) - f) + (g - F (N + 2))) := by congr 1; abel
      _ ≤ p i (F (N + 2) - f) + p i (g - F (N + 2)) := map_add_le_add _ _ _
      _ = p i (∑ r ∈ Finset.range (N + 2), (F (r + 1) - F r)) := by rw [hzero, add_zero, hsum]
      _ ≤ ∑ r ∈ Finset.range (N + 2), p i (F (r + 1) - F r) :=
        Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
      _ < ∑ r ∈ Finset.range (N + 2), c.tolerance i * w r :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hterm
      _ ≤ c.tolerance i := by
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (c.tolerance_pos i).le (hwsum _)
  · -- Near each point `g` agrees with a function which is Morse there.
    refine isMorseOn_univ.mp (isMorseOn_of_forall_exists_mem_nhds fun x _ ↦ ?_)
    obtain ⟨N, hN⟩ := L.exists_mem_nhds x
    exact ⟨interior (L N), interior_mem_nhds.mpr hN,
      ((hFinv (N + 1)).1.mono (interior_subset.trans (L.subset_succ N))).congr isOpen_interior
        fun y hy ↦ hgF N (interior_subset hy)⟩
  · -- The perturbations up to stage `N` add up to less than `ε x` at `x ∈ L N`.
    obtain ⟨N, hN⟩ := L.exists_mem x
    have hterm : ∀ r ∈ Finset.range (N + 1), |F (r + 1) x - F r x| < ε x * w r := by
      intro r _
      by_cases hx : x ∈ L (r + 2)
      · exact hD_ε r x hx
      · rw [hD_zero r x fun h ↦ hx (interior_subset h.1), sub_self, abs_zero]
        exact mul_pos (hε₀ x) (hw r)
    calc |g x - f x| = |∑ r ∈ Finset.range (N + 1), (F (r + 1) x - F r x)| := by
          rw [hgF N hN, htel (N + 1) x]
      _ ≤ ∑ r ∈ Finset.range (N + 1), |F (r + 1) x - F r x| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ r ∈ Finset.range (N + 1), ε x * w r := Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hterm
      _ ≤ ε x := by
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (hε₀ x).le (hwsum _)
  · -- Near `C` every stage, hence `g`, agrees with `f`.
    intro x hx hxC
    obtain ⟨N, hN⟩ := L.exists_mem_nhds x
    have hx' : x ∉ tsupport fun y ↦ F (N + 1) y - f y := fun h ↦ (hFinv (N + 1)).2 h hxC
    refine notMem_tsupport_iff_eventuallyEq.mpr ?_ hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx', hN] with y hy hyN
    simpa [hgF N hyN] using hy

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

/-- **Proper Morse approximation.** A proper smooth function `f` is approximated, in every strong
`C^k` neighbourhood, by proper Morse functions within distance `1` of `f`. In particular a lower
bound for `f` gives one for the approximation. -/
theorem _root_.ContMDiffMap.exists_isMorse_isProperMap_mem_ball (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (c : ContMDiffMap.StrongCkControl I M ∞) (hf : IsProperMap f) :
    ∃ g ∈ c.ball f, IsMorse I g ∧ IsProperMap g ∧ ∀ x, |g x - f x| < 1 := by
  obtain ⟨g, hg, hgm, hgf, -⟩ := f.exists_isMorse_mem_ball_sub_compl c continuous_const
    (fun _ ↦ one_pos) isClosed_empty isOpen_empty (subset_refl _) isMorseOn_empty
  refine ⟨g, hg, hgm, hf.of_dist_le g.contMDiff.continuous (C := 1) fun x ↦ ?_, hgf⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact (hgf x).le

/-- **Existence of proper Morse functions.** A boundaryless finite-dimensional Hausdorff
sigma-compact manifold carries a proper Morse function which is bounded below. -/
theorem exists_isMorse_isProperMap_bddBelow :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsMorse I g ∧ IsProperMap g ∧ BddBelow (range g) := by
  obtain ⟨f, hf, hf₀⟩ := exists_contMDiffMap_isProperMap_nonneg (M := M) I
  obtain ⟨g, -, hgm, hgp, hgf⟩ :=
    f.exists_isMorse_isProperMap_mem_ball ContMDiffMap.StrongCkControl.empty hf
  refine ⟨g, hgm, hgp, ⟨-1, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  linarith [(abs_lt.mp (hgf x)).1, hf₀ x]

end TauCeti
