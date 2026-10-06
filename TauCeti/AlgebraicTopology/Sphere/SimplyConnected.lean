/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.AlgebraicTopology.Sphere.Puncture
import Mathlib.Analysis.Convex.Combination

/-!
# Spheres are simply connected above rank two

Every sphere of nonnegative radius in a real normed space `E` with `2 < Module.rank ℝ E` is
simply connected; in particular `Sⁿ` is simply connected for `2 ≤ n`.
Spheres of positive radius are obtained from the unit sphere by dilation and translation;
a sphere of radius zero is a singleton.

The proof is the classical one, in the form that avoids any smoothing or simplicial
approximation. A loop `γ` is compared with the radial projection of the piecewise-linear
interpolation through the `N + 1` values `γ(k/N)`, where `N` is chosen so fine that
`‖γ s - γ t‖ < 1` whenever `|s - t| ≤ 1/N`.
That comparison loop is written as a single global formula rather than by gluing pieces: it is
the radial projection to the sphere of

  `L t = ∑ k ≤ N, Λ k t • γ (k/N)`,   `Λ k t = max 0 (1 - |N * t - k|)`,

the piecewise linear interpolation of the nodes through the hat functions of the subdivision.
Two facts about `L` do all the work. Since `Λ k t ≠ 0` forces `|N * t - k| < 1`, every
contributing node is within distance one of `γ t`. The nonnegative hat functions sum to one, so
`‖L t - γ t‖ < 1`; consequently the straight-line homotopy from `γ t` to `L t` never meets the
origin, and its radial projection is a homotopy of loops on the sphere. Also `Λ k t ≠ 0` forces
`k` to be `⌊N t⌋` or `⌊N t⌋ + 1`, so `L t` lies in the span of two of the nodes.
A finite family of proper subspaces of `E` cannot cover `E`
(`Submodule.exists_forall_notMem_of_forall_ne_top`), and each two-vector span is proper
because the rank exceeds two, so the projected loop omits a point of the sphere. Loops
omitting a point are null-homotopic by `Path.homotopic_refl_of_notMem_range`.

Rank two is genuinely the boundary: the circle is not simply connected.

## Main declarations

* `Path.exists_homotopic_notMem_range`: every path on the unit sphere is homotopic to a
  path with the same endpoints that omits a point of the sphere.
* `TauCeti.simplyConnectedSpace_sphere`: spheres of nonnegative radius in real normed spaces
  of rank greater than two are simply connected.
* `TauCeti.simplyConnectedSpace_sphere_euclideanSpace`: the case of `Sⁿ` for `2 ≤ n`.
* `TauCeti.simplyConnectedSpace_sphere_euclideanSpace_complex`: the case of the unit sphere
  `S²ᵏ⁺¹` of `ℂᵏ⁺¹` for `1 ≤ k`.

## References

Simple connectivity of the covering sphere gives the fundamental groups of real projective
spaces and lens spaces through their covering maps.
Hatcher, *Algebraic Topology*, Corollary 1.15 gives the classical theorem; the hat-function
interpolation and finite-span avoidance argument used here is this repository's own arrangement.
-/

public section

noncomputable section

open Metric NormedSpace
open scoped unitInterval

namespace TauCeti

section Interpolation

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th hat-function formula for a subdivision into `N` equal parts. -/
private def hatFunction (N k : ℕ) (t : I) : ℝ := max 0 (1 - |(N : ℝ) * (t : ℝ) - (k : ℝ)|)

/-- The `k`-th subdivision node, clamped to the unit interval. -/
private def nodeParam (N k : ℕ) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((k : ℝ) / (N : ℝ))

/-- The piecewise linear interpolation of the nodes `node 0, …, node N` through the hat
functions of the subdivision of the unit interval into `N` equal parts. -/
private def nodeInterp {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (N : ℕ) (node : ℕ → E) (t : I) : E :=
  ∑ k ∈ Finset.range (N + 1), hatFunction N k t • node k

private theorem hatFunction_nonneg (N k : ℕ) (t : I) : 0 ≤ hatFunction N k t := le_max_left _ _

private theorem continuous_hatFunction (N k : ℕ) : Continuous (hatFunction N k) := by
  unfold hatFunction
  fun_prop

/-- The hat function of the `k`-th node vanishes unless `N * t` is within `1` of `k`. -/
private theorem abs_lt_one_of_hatFunction_ne_zero {N k : ℕ} {t : I} (h : hatFunction N k t ≠ 0) :
    |(N : ℝ) * (t : ℝ) - (k : ℝ)| < 1 := by
  by_contra hc
  push Not at hc
  exact h (max_eq_left (by linarith))

private theorem floor_bounds (N : ℕ) (t : I) :
    (((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (t : ℝ)) ∧
      (N : ℝ) * (t : ℝ) < ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) + 1 := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (unitInterval.nonneg t)
  exact ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩

/-- A node with nonzero hat weight is less than one mesh width from the parameter. -/
private theorem dist_nodeParam_lt_of_hatFunction_ne_zero {N k : ℕ} {t : I}
    (hN : 0 < N) (h : hatFunction N k t ≠ 0) : dist t (nodeParam N k) < 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have habs := abs_lt_one_of_hatFunction_ne_zero h
  have hdiff : |(t : ℝ) - (k : ℝ) / (N : ℝ)| < 1 / (N : ℝ) := by
    have hrw : (t : ℝ) - (k : ℝ) / (N : ℝ) =
        ((N : ℝ) * (t : ℝ) - (k : ℝ)) / (N : ℝ) := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hNR]
    exact (div_lt_div_iff_of_pos_right hNR).mpr habs
  rw [Subtype.dist_eq, Real.dist_eq]
  calc
    |(t : ℝ) - (nodeParam N k : ℝ)| =
        |(Set.projIcc (0 : ℝ) 1 zero_le_one (t : ℝ) : ℝ) -
          (Set.projIcc (0 : ℝ) 1 zero_le_one ((k : ℝ) / (N : ℝ)) : ℝ)| := by
            rw [Set.projIcc_val]
            rfl
    _ ≤ |(t : ℝ) - (k : ℝ) / (N : ℝ)| :=
      Set.abs_projIcc_sub_projIcc zero_le_one
    _ < 1 / (N : ℝ) := hdiff

/-- The only hat functions that do not vanish at `t` are those of the two nodes straddling `t`. -/
private theorem eq_floor_or_of_hatFunction_ne_zero {N k : ℕ} {t : I}
    (h : hatFunction N k t ≠ 0) :
    k = ⌊(N : ℝ) * (t : ℝ)⌋₊ ∨ k = ⌊(N : ℝ) * (t : ℝ)⌋₊ + 1 := by
  obtain ⟨h1, h2⟩ := floor_bounds N t
  have habs := abs_lt.mp (abs_lt_one_of_hatFunction_ne_zero h)
  have hk1 : (k : ℝ) < ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) + 2 := by linarith [habs.1]
  have hk2 : ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) < (k : ℝ) + 1 := by linarith [habs.2]
  have hk1' : k < ⌊(N : ℝ) * (t : ℝ)⌋₊ + 2 := by exact_mod_cast hk1
  have hk2' : ⌊(N : ℝ) * (t : ℝ)⌋₊ < k + 1 := by exact_mod_cast hk2
  omega

/-- The hat weights form a partition of unity on the unit interval. -/
private theorem sum_hatFunction_eq_one (N : ℕ) (t : I) :
    ∑ k ∈ Finset.range (N + 1), hatFunction N k t = 1 := by
  set r : ℝ := (N : ℝ) * (t : ℝ) with hr
  set m : ℕ := ⌊(N : ℝ) * (t : ℝ)⌋₊ with hm
  obtain ⟨h1, h2⟩ := floor_bounds N t
  have hrle : r ≤ N := by
    rw [hr]
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) (unitInterval.le_one t)
  have hmle : m ≤ N := by
    have : (m : ℝ) ≤ N := h1.trans hrle
    exact_mod_cast this
  by_cases hmN : m = N
  · have hNr : (N : ℝ) ≤ r :=
      calc
        (N : ℝ) = (m : ℝ) := by rw [hmN]
        _ = ((⌊(N : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) := by rw [hm]
        _ ≤ (N : ℝ) * (t : ℝ) := h1
        _ = r := hr.symm
    have hrN : r = N := le_antisymm hrle hNr
    have hhatm : hatFunction N m t = 1 := by
      unfold hatFunction
      have harg : (N : ℝ) * (t : ℝ) - (m : ℝ) = 0 := by
        rw [← hr, hrN, hmN]
        simp
      rw [harg]
      norm_num
    rw [Finset.sum_eq_single m]
    · exact hhatm
    · intro k hk hkm
      by_contra hk0
      rcases eq_floor_or_of_hatFunction_ne_zero hk0 with h | h
      · exact hkm (by simpa [hm] using h)
      · have hklt := Finset.mem_range.mp hk
        omega
    · exact fun hm => (hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hmle))).elim
  · have hm_lt : m < N := lt_of_le_of_ne hmle hmN
    have hsubset : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (N + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hzero : ∀ k ∈ Finset.range (N + 1), k ∉ ({m, m + 1} : Finset ℕ) →
        hatFunction N k t = 0 := by
      intro k _ hk
      by_contra hk0
      rcases eq_floor_or_of_hatFunction_ne_zero hk0 with h | h <;>
        exact hk (by simp [hm, h])
    have hrestrict := Finset.sum_subset hsubset hzero
    have hhatm : hatFunction N m t = 1 - (r - m) := by
      unfold hatFunction
      rw [← hr,
        abs_of_nonneg (by simpa [hr, hm] using h1), max_eq_right (by linarith [h2])]
    have hhatnext : hatFunction N (m + 1) t = r - m := by
      unfold hatFunction
      rw [← hr, Nat.cast_add, Nat.cast_one]
      rw [abs_of_nonpos (by simpa [hr, hm] using h2.le), max_eq_right (by linarith [h1])]
      ring
    rw [← hrestrict]
    simp [hhatm, hhatnext]

private theorem hatFunction_zero_self (N : ℕ) : hatFunction N 0 (0 : I) = 1 := by
  simp [hatFunction]

private theorem hatFunction_zero_of_ne (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    hatFunction N k (0 : I) = 0 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have habs : |(N : ℝ) * ((0 : I) : ℝ) - (k : ℝ)| = (k : ℝ) := by
    rw [Set.Icc.coe_zero, mul_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg k)]
  simp only [hatFunction, habs]
  exact max_eq_left (by linarith)

private theorem hatFunction_one_self (N : ℕ) : hatFunction N N (1 : I) = 1 := by
  simp [hatFunction]

private theorem hatFunction_one_of_ne {N k : ℕ} (hkN : k ≤ N) (hk : k ≠ N) :
    hatFunction N k (1 : I) = 0 := by
  have h1 : (k : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_ne hkN hk)
  have habs : |(N : ℝ) * ((1 : I) : ℝ) - (k : ℝ)| = (N : ℝ) - (k : ℝ) := by
    rw [Set.Icc.coe_one, mul_one, abs_of_nonneg (by linarith)]
  simp only [hatFunction, habs]
  exact max_eq_left (by linarith)

private theorem continuous_nodeInterp (N : ℕ) (node : ℕ → E) :
    Continuous (nodeInterp N node) :=
  continuous_finsetSum _ fun k _ => (continuous_hatFunction N k).smul continuous_const

private theorem nodeInterp_zero {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (N : ℕ) (node : ℕ → E) : nodeInterp N node 0 = node 0 := by
  rw [nodeInterp, Finset.sum_eq_single 0]
  · rw [hatFunction_zero_self, one_smul]
  · exact fun k _ hk => by rw [hatFunction_zero_of_ne N hk, zero_smul]
  · exact fun hc => absurd (Finset.mem_range.mpr (Nat.succ_pos N)) hc

private theorem nodeInterp_one {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (N : ℕ) (node : ℕ → E) : nodeInterp N node 1 = node N := by
  rw [nodeInterp, Finset.sum_eq_single N]
  · rw [hatFunction_one_self, one_smul]
  · exact fun k hk hkN => by
      rw [hatFunction_one_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkN, zero_smul]
  · exact fun hc => absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) hc

/-- The interpolation at `t` lies in the span of the two nodes straddling `t`. -/
private theorem nodeInterp_mem_span {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (N : ℕ) (node : ℕ → E) (t : I) :
    nodeInterp N node t ∈
      Submodule.span ℝ {node ⌊(N : ℝ) * (t : ℝ)⌋₊, node (⌊(N : ℝ) * (t : ℝ)⌋₊ + 1)} := by
  rw [nodeInterp]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : hatFunction N k t = 0
  · simp [hk]
  · refine Submodule.smul_mem _ _ ?_
    rcases eq_floor_or_of_hatFunction_ne_zero hk with h | h <;>
      exact h ▸ Submodule.subset_span (by simp)

/-- If every node with nonzero weight is within distance one of `a`, then so is their
hat-function interpolation. -/
private theorem norm_nodeInterp_sub_lt_one {N : ℕ} {node : ℕ → E} {a : E} (t : I)
    (h : ∀ k, hatFunction N k t ≠ 0 → ‖a - node k‖ < 1) :
    ‖nodeInterp N node t - a‖ < 1 := by
  classical
  let nodes := (Finset.range (N + 1)).filter fun k => hatFunction N k t ≠ 0
  have hsum : ∑ k ∈ nodes, hatFunction N k t = 1 := by
    simpa only [nodes, Finset.sum_filter_ne_zero] using sum_hatFunction_eq_one N t
  have hinterp : nodeInterp N node t = ∑ k ∈ nodes, hatFunction N k t • node k := by
    dsimp [nodeInterp, nodes]
    symm
    apply Finset.sum_filter_of_ne
    intro k _ hk hzero
    exact hk (by simp [hzero])
  have hmem : (∑ k ∈ nodes, hatFunction N k t • node k) ∈ ball a 1 := by
    refine (convex_ball a 1).sum_mem (fun k _ => hatFunction_nonneg N k t) hsum ?_
    intro k hk
    simpa [mem_ball, dist_eq_norm, norm_sub_rev] using h k (Finset.mem_filter.mp hk).2
  simpa [← hinterp, mem_ball, dist_eq_norm] using hmem

end Interpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every path on the unit sphere of a real normed space of rank greater than two is
homotopic, with fixed endpoints, to a path that omits a point of the sphere. -/
theorem _root_.Path.exists_homotopic_notMem_range {x y : sphere (0 : E) 1}
    (γ : Path x y) (h : 2 < Module.rank ℝ E) :
    ∃ γ' : Path x y, γ.Homotopic γ' ∧ ∃ p : sphere (0 : E) 1, p ∉ Set.range γ' := by
  classical
  have hγnorm : ∀ t, ‖((γ t : sphere (0 : E) 1) : E)‖ = 1 := fun t =>
    mem_sphere_zero_iff_norm.mp (γ t).2
  have hγcont : Continuous fun t : I => ((γ t : sphere (0 : E) 1) : E) :=
    continuous_subtype_val.comp γ.continuous
  -- Choose a subdivision so fine that the path moves by less than `1` across each step.
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hγcont) 1 one_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := N₀ + 1 with hNdef
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNδ : 1 / (N : ℝ) < δ := by rw [hNdef]; push_cast; exact hN₀
  -- The nodes of the subdivision, and the piecewise linear interpolation through them.
  set node : ℕ → E := fun k => ((γ (nodeParam N k) : sphere (0 : E) 1) : E) with hnode
  have hfloor_le : ∀ t : I, ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ N := by
    intro t
    calc ⌊(N : ℝ) * (t : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ :=
          Nat.floor_mono (mul_le_of_le_one_right hNR.le (unitInterval.le_one t))
      _ = N := Nat.floor_natCast N
  -- Every node alive at `t` is close to `γ t`.
  have hclose : ∀ (t : I) (k : ℕ), hatFunction N k t ≠ 0 →
      ‖((γ t : sphere (0 : E) 1) : E) - node k‖ < 1 := by
    intro t k hk
    have hdist := dist_nodeParam_lt_of_hatFunction_ne_zero (N := N) (Nat.succ_pos N₀) hk
    have := hδ' (hdist.trans hNδ)
    rwa [dist_eq_norm] at this
  have hLclose : ∀ t : I,
      ‖nodeInterp N node t - ((γ t : sphere (0 : E) 1) : E)‖ < 1 := fun t =>
    norm_nodeInterp_sub_lt_one t (fun k hk => hclose t k hk)
  have hLne : ∀ t : I, nodeInterp N node t ≠ 0 := by
    intro t ht
    have hlt := hLclose t
    rw [ht, zero_sub, norm_neg, hγnorm t] at hlt
    exact lt_irrefl 1 hlt
  -- The interpolation matches the path at both ends of the interval.
  have hnodeParam0 : nodeParam N 0 = (0 : I) := Subtype.ext (by simp [nodeParam])
  have hnodeParamN : nodeParam N N = (1 : I) :=
    Subtype.ext (by simp [nodeParam])
  have hL0 : nodeInterp N node 0 = ((x : sphere (0 : E) 1) : E) := by
    simp only [nodeInterp_zero, hnode, hnodeParam0, γ.source]
  have hL1 : nodeInterp N node 1 = ((y : sphere (0 : E) 1) : E) := by
    simp only [nodeInterp_one, hnode, hnodeParamN, γ.target]
  -- The comparison path.
  have hcontL : Continuous (nodeInterp N node) := continuous_nodeInterp N node
  let Lsphere := normalizeToSphere (nodeInterp N node) hcontL hLne
  have hx1 : ‖((x : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  let γ' : Path x y :=
    { toFun := Lsphere
      continuous_toFun := Lsphere.continuous
      source' := Subtype.ext (by
        rw [coe_normalizeToSphere_apply, hL0, normalize_eq_self_of_norm_eq_one hx1])
      target' := Subtype.ext (by
        rw [coe_normalizeToSphere_apply, hL1,
          normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp y.2)]) }
  -- The straight-line homotopy between the path and the comparison path misses the origin.
  have hGne : ∀ z : I × I,
      (1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E) + (z.1 : ℝ) • nodeInterp N node z.2
        ≠ 0 := by
    intro z hz
    have hmem := (convex_ball ((γ z.2 : sphere (0 : E) 1) : E) 1)
      (by simp : ((γ z.2 : sphere (0 : E) 1) : E) ∈ ball (γ z.2 : E) 1)
      (by simpa [mem_ball, dist_eq_norm] using hLclose z.2)
      (sub_nonneg.mpr (unitInterval.le_one z.1)) (unitInterval.nonneg z.1)
      (sub_add_cancel 1 (z.1 : ℝ))
    simp [hz, mem_ball, hγnorm] at hmem
  have hsquare : γ.Homotopic γ' :=
    γ.homotopic_of_segment_ne_zero γ' (nodeInterp N node) hcontL
      (fun t => coe_normalizeToSphere_apply (nodeInterp N node) hcontL hLne t) hL0 hL1 hGne
  -- The comparison path lives in finitely many planes, which cannot cover `E`.
  have hVne : ∀ m : Fin (N + 1),
      Submodule.span ℝ ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E) ≠ ⊤ := by
    intro m htop
    have hcard : Cardinal.mk ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E) ≤ 2 :=
      calc
        _ ≤ Cardinal.mk ({node ((m : ℕ) + 1)} : Set E) + 1 := Cardinal.mk_insert_le
        _ = 2 := by simp [one_add_one_eq_two]
    have hdim := (rank_span_le (R := ℝ) ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E)).trans hcard
    rw [htop, rank_top] at hdim
    exact h.not_ge hdim
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun m : Fin (N + 1) => Submodule.span ℝ ({node (m : ℕ), node ((m : ℕ) + 1)} : Set E)) hVne
  have hw0 : w ≠ 0 := fun h0 => hw ⟨0, Nat.succ_pos N⟩ (h0 ▸ Submodule.zero_mem _)
  refine ⟨γ', hsquare, ⟨normalize w, mem_sphere_zero_iff_norm.mpr (norm_normalize hw0)⟩, ?_⟩
  rintro ⟨t, ht⟩
  have hteq : normalize (nodeInterp N node t) = normalize w :=
    (coe_normalizeToSphere_apply (nodeInterp N node) hcontL hLne t).symm.trans
      (congrArg Subtype.val ht)
  have hwmem : w ∈
      Submodule.span ℝ ({node ⌊(N : ℝ) * (t : ℝ)⌋₊, node (⌊(N : ℝ) * (t : ℝ)⌋₊ + 1)} : Set E) := by
    have hwrite : w = (‖w‖ * ‖nodeInterp N node t‖⁻¹) • nodeInterp N node t :=
      calc w = ‖w‖ • normalize w := (norm_smul_normalize w).symm
        _ = ‖w‖ • normalize (nodeInterp N node t) := by rw [hteq]
        _ = (‖w‖ * ‖nodeInterp N node t‖⁻¹) • nodeInterp N node t := by
              rw [NormedSpace.normalize, smul_smul]
    rw [hwrite]
    exact Submodule.smul_mem _ _ (nodeInterp_mem_span N node t)
  exact hw ⟨⌊(N : ℝ) * (t : ℝ)⌋₊, Nat.lt_succ_of_le (hfloor_le t)⟩ hwmem

/-- Every sphere of nonnegative radius in a real normed space of rank greater than two is
simply connected. -/
theorem simplyConnectedSpace_sphere (h : 2 < Module.rank ℝ E) (c : E) {r : ℝ}
    (hr : 0 ≤ r) : SimplyConnectedSpace (sphere c r) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [sphere_zero]
    infer_instance
  have hsunit : SimplyConnectedSpace (sphere (0 : E) 1) := by
    have hpc : PathConnectedSpace (sphere (0 : E) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere (Cardinal.one_lt_two.trans h) 0 zero_le_one)
    refine simply_connected_iff_loops_nullhomotopic.mpr ⟨hpc, fun x γ => ?_⟩
    obtain ⟨γ', hγγ', p, hp⟩ := γ.exists_homotopic_notMem_range h
    exact hγγ'.trans (γ'.homotopic_refl_of_notMem_range hp)
  let e : sphere (0 : E) 1 ≃ₜ sphere c r :=
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight c)).subtype fun x => by
      simp [mem_sphere_iff_norm, Homeomorph.smulOfNeZero_apply,
        norm_smul, Real.norm_eq_abs, abs_of_pos hr, hr.ne']
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- **The `n`-sphere is simply connected for `2 ≤ n`.** -/
theorem simplyConnectedSpace_sphere_euclideanSpace {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  refine simplyConnectedSpace_sphere ?_ 0 zero_le_one
  have hrank : Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = ((n + 1 : ℕ) : Cardinal) := by
    simp [← Module.finrank_eq_rank]
  rw [hrank]
  exact_mod_cast (by omega : 2 < n + 1)

/-- **The unit sphere `S²ᵏ⁺¹` of `ℂᵏ⁺¹` is simply connected for `1 ≤ k`.** -/
theorem simplyConnectedSpace_sphere_euclideanSpace_complex {k : ℕ} (hk : 1 ≤ k) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1) := by
  refine simplyConnectedSpace_sphere ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_real_of_complex, finrank_euclideanSpace_fin,
    Nat.ofNat_lt_cast]
  omega

end TauCeti

end
