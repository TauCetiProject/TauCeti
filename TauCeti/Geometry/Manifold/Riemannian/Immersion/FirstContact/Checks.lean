/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.FirstContact.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Checks for the first-contact lemma

Throughout, `e` is a unit vector and the barrier is the hyperplane `S_t = {⟪e, y⟫ = t}`, the
graph of `0` over all of `e^⊥` translated by `t e`.

* **The sphere.** For the unit sphere of a space of dimension at least two and `T = 2`, the
  hyperplane `S_t` with `t ≥ 0` meets the sphere exactly when `t ≤ 1`. The first-contact lemma
  gives the largest contact time `t₀ = 1`, attained only at the pole `e`, where the sphere lies
  below `S_1` and is tangent to it.
* **Boundedness is needed.** The graph `f(k) = k + (1 - exp(-‖k‖²)) e` over `e^⊥` is proper and
  meets `S_t`, `t ≥ 0`, exactly when `t < 1`, in the sphere `‖k‖² = -log(1 - t)`. The union of
  these contact sets is unbounded, and there is no largest contact time in `[0, 2]`.

## References

* O. Chodosh, *Introduction to minimal surfaces*, proof of Theorem 20.1.
-/

public noncomputable section

open Filter Function Manifold Metric Module Set Topology
open scoped InnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : F}

private theorem heightAboveGraph_zero (y : F) :
    heightAboveGraph e (fun _ ↦ 0) y = ⟪e, y⟫_ℝ := by
  rw [heightAboveGraph_def, sub_zero]

/-- A point lies on the hyperplane `S_t` exactly when `⟪e, y⟫ = t`. -/
theorem mem_translatedGraph_univ_zero_iff (he : ‖e‖ = 1) {t : ℝ} {y : F} :
    y ∈ translatedGraph e univ (fun _ ↦ 0) t ↔ ⟪e, y⟫_ℝ = t := by
  rw [mem_translatedGraph_iff he, heightAboveGraph_zero]
  simp

/-- The barrier over the empty frontier of `e^⊥` is empty. -/
theorem translatedGraph_frontier_univ (g : (ℝ ∙ e)ᗮ → ℝ) (t : ℝ) :
    translatedGraph e (frontier univ) g t = ∅ := by
  rw [translatedGraph_def, frontier_univ, image_empty]

/-- A unit vector orthogonal to `e` exists when `F` has dimension at least two. -/
private theorem exists_norm_eq_one_mem_orthogonal [FiniteDimensional ℝ F] (he : ‖e‖ = 1)
    (hF : 2 ≤ finrank ℝ F) : ∃ w : (ℝ ∙ e)ᗮ, ‖(w : F)‖ = 1 := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (he ▸ one_ne_zero)
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
  rw [finrank_span_singleton he0] at h
  have hK : (ℝ ∙ e)ᗮ ≠ ⊥ := fun hb ↦ by
    rw [hb, finrank_bot] at h
    omega
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  exact ⟨⟨‖k‖⁻¹ • k, Submodule.smul_mem _ _ hk⟩, norm_smul_inv_norm hk0⟩

/-- Adding a multiple of `e` to a vector of `e^⊥` does not decrease its norm. -/
private theorem norm_le_norm_add_smul (k : (ℝ ∙ e)ᗮ) (c : ℝ) : ‖(k : F)‖ ≤ ‖(k : F) + c • e‖ := by
  have hk : ⟪(k : F), e⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 k.property
  have h : ‖(k : F)‖ ^ 2 ≤ ‖(k : F) + c • e‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hk]
    nlinarith [sq_nonneg ‖c • e‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ### The sphere -/

section Sphere

variable [FiniteDimensional ℝ F] {n : ℕ} [Fact (finrank ℝ F = n + 1)]

local notation "S" => sphere (0 : F) 1
local notation "ι" => (Subtype.val : S → F)

/-- **Contact times for the sphere.** For `t ≥ 0`, the hyperplane `S_t` meets the unit sphere
exactly when `t ≤ 1`. -/
theorem nonempty_translatedGraph_inter_range_coe_sphere_iff (hn : 1 ≤ n) (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (translatedGraph e univ (fun _ ↦ 0) t ∩ range ι).Nonempty ↔ t ≤ 1 := by
  constructor
  · rintro ⟨_, hy, x, rfl⟩
    rw [mem_translatedGraph_univ_zero_iff he] at hy
    have hx : ‖(x : F)‖ = 1 := by simp
    calc t = ⟪e, (x : F)⟫_ℝ := hy.symm
      _ ≤ ‖e‖ * ‖(x : F)‖ := real_inner_le_norm _ _
      _ = 1 := by rw [he, hx, one_mul]
  · intro ht1
    obtain ⟨w, hw⟩ := exists_norm_eq_one_mem_orthogonal he
      (by rw [(Fact.out : finrank ℝ F = n + 1)]; omega)
    have hew : ⟪e, (w : F)⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.property
    set y : F := t • e + √(1 - t ^ 2) • (w : F)
    have hs : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
    have hy : ‖y‖ = 1 := by
      have h2 : ‖y‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hew, norm_smul,
          norm_smul, he, hw, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
          sq_abs, hs]
        ring
      nlinarith [norm_nonneg y]
    refine ⟨y, (mem_translatedGraph_univ_zero_iff he).2 ?_, ⟨y, by simpa using hy⟩, rfl⟩
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hew,
      real_inner_self_eq_norm_sq, he]
    ring

/-- **First contact of a hyperplane with the sphere.** For the hyperplanes `S_t = {⟪e, y⟫ = t}`
and `T = 2`, the first-contact lemma gives the largest contact time `t₀ = 1`; the only contact
point is the pole `e`, where the sphere lies below `S_1` and is tangent to it. -/
theorem firstContact_sphere (hn : 1 ≤ n) (he : ‖e‖ = 1) :
    ∃ t₀ ∈ Ico (0 : ℝ) 2, t₀ = 1 ∧
      (∀ x : S, ι x ∈ translatedGraph e univ (fun _ ↦ 0) t₀ ↔ (x : F) = e) ∧
      ∀ x : S, ι x ∈ translatedGraph e univ (fun _ ↦ 0) t₀ →
        (∀ᶠ y : S in 𝓝 x, ⟪e, (y : F)⟫_ℝ ≤ t₀) ∧ ∀ v, ⟪e, mvfderiv (𝓡 n) ι x v⟫_ℝ = 0 := by
  have : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  have hiff (t : ℝ) (ht : 0 ≤ t) :=
    nonempty_translatedGraph_inter_range_coe_sphere_iff (e := e) hn he ht
  obtain ⟨t₀, ht₀, hne, hmax, hside⟩ := exists_firstContact_tangent (I := 𝓡 n) (T := 2)
    continuous_subtypeVal.isProperMap he isClosed_univ continuousOn_const (by norm_num)
    (by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, hiff 2 (by norm_num)]
      norm_num)
    ((hiff 0 le_rfl).2 zero_le_one)
    (fun t _ ↦ by rw [translatedGraph_frontier_univ]; exact empty_disjoint _)
    ((isBounded_closedBall (x := (0 : F)) (r := 1)).subset fun y hy ↦ by
      obtain ⟨-, -, -, x, rfl⟩ := mem_iUnion₂.1 hy
      exact sphere_subset_closedBall x.property)
    ((contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero) (differentiableOn_const 0)
  have h1 : t₀ = 1 := le_antisymm ((hiff t₀ ht₀.1).1 hne)
    (hmax 1 ⟨zero_le_one, by norm_num⟩ ((hiff 1 zero_le_one).2 le_rfl))
  refine ⟨t₀, ht₀, h1, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have hx : ‖(x : F)‖ = 1 := by simp
    rw [mem_translatedGraph_univ_zero_iff he, h1, inner_eq_one_iff_of_norm_eq_one he hx, eq_comm]
  · obtain ⟨-, hev, htan⟩ := hside x hx
    refine ⟨hev.mono fun y hy ↦ by rwa [heightAboveGraph_zero] at hy, fun v ↦ ?_⟩
    rw [htan v]
    simp

end Sphere

/-! ### A graph with no last contact -/

section NoLastContact

variable [FiniteDimensional ℝ F]

/-- The graph `k ↦ k + (1 - exp(-‖k‖²)) e` over `e^⊥`. -/
def bumpGraph (e : F) (k : (ℝ ∙ e)ᗮ) : F := (k : F) + (1 - Real.exp (-‖(k : F)‖ ^ 2)) • e

omit [FiniteDimensional ℝ F] in
/-- The height of the graph `bumpGraph e` above `e^⊥` is `1 - exp(-‖k‖²)`. -/
theorem heightAboveGraph_bumpGraph (he : ‖e‖ = 1) (k : (ℝ ∙ e)ᗮ) :
    heightAboveGraph e (fun _ ↦ 0) (bumpGraph e k) = 1 - Real.exp (-‖(k : F)‖ ^ 2) := by
  rw [bumpGraph, heightAboveGraph_add_smul he, sub_zero]

/-- The graph `bumpGraph e` is a proper map. -/
theorem isProperMap_bumpGraph : IsProperMap (bumpGraph e) := by
  have hc : Continuous (bumpGraph e) := by
    unfold bumpGraph
    fun_prop
  refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun C hC ↦ ?_⟩
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  refine isCompact_of_isClosed_isBounded (hC.isClosed.preimage hc)
    (isBounded_closedBall (x := 0) (r := R) |>.subset fun k hk ↦ ?_)
  have h := mem_closedBall_zero_iff.1 (hR hk)
  rw [mem_closedBall_zero_iff]
  exact (norm_le_norm_add_smul k _).trans h

omit [FiniteDimensional ℝ F] in
/-- **Contact times of the bump graph.** For `t < 1`, `bumpGraph e k` lies on `S_t` exactly when
`‖k‖² = -log(1 - t)`. -/
theorem bumpGraph_mem_translatedGraph_iff (he : ‖e‖ = 1) {t : ℝ} (ht : t < 1)
    (k : (ℝ ∙ e)ᗮ) :
    bumpGraph e k ∈ translatedGraph e univ (fun _ ↦ 0) t ↔
      ‖(k : F)‖ ^ 2 = -Real.log (1 - t) := by
  rw [mem_translatedGraph_iff he, heightAboveGraph_bumpGraph he]
  simp only [mem_univ, true_and]
  constructor
  · intro h
    rw [← h, sub_sub_cancel, Real.log_exp, neg_neg]
  · intro h
    rw [h, neg_neg, Real.exp_log (by linarith)]
    ring

/-- For `t ≥ 0`, the hyperplane `S_t` meets the bump graph exactly when `t < 1`. -/
theorem nonempty_translatedGraph_inter_range_bumpGraph_iff (he : ‖e‖ = 1)
    (hF : 2 ≤ finrank ℝ F) {t : ℝ} (ht : 0 ≤ t) :
    (translatedGraph e univ (fun _ ↦ 0) t ∩ range (bumpGraph e)).Nonempty ↔ t < 1 := by
  constructor
  · rintro ⟨_, hy, k, rfl⟩
    rw [mem_translatedGraph_iff he, heightAboveGraph_bumpGraph he] at hy
    rw [← hy.2]
    linarith [Real.exp_pos (-‖(k : F)‖ ^ 2)]
  · intro ht1
    obtain ⟨w, hw⟩ := exists_norm_eq_one_mem_orthogonal he hF
    have hl : 0 ≤ -Real.log (1 - t) :=
      neg_nonneg.2 (Real.log_nonpos (by linarith) (by linarith))
    refine ⟨_, (bumpGraph_mem_translatedGraph_iff he ht1 (√(-Real.log (1 - t)) • w)).2 ?_,
      mem_range_self _⟩
    rw [Submodule.coe_smul, norm_smul, hw, mul_one, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hl]

/-- **Boundedness is needed for a first contact.** For the bump graph and `T = 2`, the union of
the contact sets `S_t ∩ f(e^⊥)`, `t ∈ [0, 2]`, is unbounded, and there is no largest contact
time. -/
theorem not_isBounded_and_not_exists_firstContact_bumpGraph (he : ‖e‖ = 1)
    (hF : 2 ≤ finrank ℝ F) :
    ¬Bornology.IsBounded
        (⋃ t ∈ Icc (0 : ℝ) 2, translatedGraph e univ (fun _ ↦ 0) t ∩ range (bumpGraph e)) ∧
      ¬∃ t₀ ∈ Icc (0 : ℝ) 2,
        (translatedGraph e univ (fun _ ↦ 0) t₀ ∩ range (bumpGraph e)).Nonempty ∧
        ∀ t ∈ Icc (0 : ℝ) 2,
          (translatedGraph e univ (fun _ ↦ 0) t ∩ range (bumpGraph e)).Nonempty → t ≤ t₀ := by
  have hiff (t : ℝ) (ht : 0 ≤ t) := nonempty_translatedGraph_inter_range_bumpGraph_iff he hF ht
  refine ⟨fun hb ↦ ?_, fun ⟨t₀, ht₀, hne, hmax⟩ ↦ ?_⟩
  · obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    obtain ⟨w, hw⟩ := exists_norm_eq_one_mem_orthogonal he hF
    set k : (ℝ ∙ e)ᗮ := (|R| + 1) • w
    have hk : bumpGraph e k ∈ ⋃ t ∈ Icc (0 : ℝ) 2,
        translatedGraph e univ (fun _ ↦ 0) t ∩ range (bumpGraph e) := by
      have hpos := Real.exp_pos (-‖(k : F)‖ ^ 2)
      have hle := Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg ‖(k : F)‖))
      refine mem_iUnion₂.2 ⟨1 - Real.exp (-‖(k : F)‖ ^ 2), ⟨by linarith, by linarith⟩, ?_,
        mem_range_self k⟩
      rw [mem_translatedGraph_iff he, heightAboveGraph_bumpGraph he]
      exact ⟨mem_univ _, rfl⟩
    have h1 := mem_closedBall_zero_iff.1 (hR hk)
    have h2 := norm_le_norm_add_smul k (1 - Real.exp (-‖(k : F)‖ ^ 2))
    have h3 : ‖(k : F)‖ = |R| + 1 := by
      rw [Submodule.coe_smul, norm_smul, hw, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [bumpGraph] at h1
    linarith [le_abs_self R]
  · have ht₀1 := (hiff t₀ ht₀.1).1 hne
    have h := hmax ((t₀ + 1) / 2) ⟨by linarith [ht₀.1], by linarith⟩
      ((hiff ((t₀ + 1) / 2) (by linarith [ht₀.1])).2 (by linarith))
    linarith

end NoLastContact

end TauCeti
