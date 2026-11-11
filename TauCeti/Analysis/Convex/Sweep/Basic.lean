/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Module
public import TauCeti.Analysis.Convex.Recession.Basic

/-!
# Transverse sweeps

The sweep of a set `P` in the direction `n` is `P - ℝ≥0 • n`. When `n` is
outside the affine direction of `P`, a normalized linear height recovers both
prism coordinates. Sweeps commute with adding unrestricted coordinates, as needed
when comparing projected wall supports with their cylinders.

Adapted from `Mei/Geometry/Convex/Sweep.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

namespace Set

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The negative ray sweep of a set. -/
def sweep (P : Set V) (n : V) : Set V :=
  {y | ∃ x ∈ P, ∃ t : ℝ, 0 ≤ t ∧ y = x - t • n}

/-- The sweep consists of base points translated by nonpositive multiples of `n`. -/
theorem sweep_def (P : Set V) (n : V) :
    sweep P n = {y | ∃ x ∈ P, ∃ t : ℝ, 0 ≤ t ∧ y = x - t • n} := (rfl)

/-- A point belongs to the sweep exactly when it has base and nonnegative ray coordinates. -/
@[simp]
theorem mem_sweep_iff_exists {P : Set V} {n y : V} :
    y ∈ sweep P n ↔ ∃ x ∈ P, ∃ t : ℝ, 0 ≤ t ∧ y = x - t • n := (Iff.rfl)

/-- A point belongs to a sweep exactly when moving it forward along the ray
reaches the base at a nonnegative time. -/
theorem mem_sweep_iff {P : Set V} {n y : V} :
    y ∈ sweep P n ↔ ∃ t : ℝ, 0 ≤ t ∧ y + t • n ∈ P := by
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    exact ⟨t, ht, by simpa using hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨y + t • n, hx, t, ht, by simp⟩

/-- A zero sweeping vector leaves the base unchanged. -/
@[simp]
theorem sweep_zero (P : Set V) : sweep P (0 : V) = P := by
  ext y
  simp only [mem_sweep_iff, smul_zero, add_zero]
  exact ⟨fun h => h.choose_spec.2, fun h => ⟨0, le_rfl, h⟩⟩

/-- Every base point belongs to its sweep with ray parameter zero. -/
theorem subset_sweep (P : Set V) (n : V) : P ⊆ sweep P n := by
  intro x hx
  exact ⟨x, hx, 0, le_rfl, by simp⟩

/-- Sweeping preserves inclusions. -/
theorem sweep_mono {P Q : Set V} (h : P ⊆ Q) (n : V) : sweep P n ⊆ sweep Q n := by
  rintro y ⟨x, hx, t, ht, he⟩
  exact ⟨x, h hx, t, ht, he⟩

/-- Sweeping a cylinder only changes its base. The unrestricted coordinate absorbs
every second component of the sweeping vector, including when the first is zero. -/
@[simp]
theorem sweep_prod_univ {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set V) (n : V × E) :
    sweep (P ×ˢ (Set.univ : Set E)) n = sweep P n.1 ×ˢ Set.univ := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, he⟩
    exact ⟨⟨x.1, hx.1, t, ht, congrArg Prod.fst he⟩, Set.mem_univ _⟩
  · rintro ⟨⟨x, hx, t, ht, he⟩, _⟩
    refine ⟨(x, y.2 + t • n.2), ⟨hx, Set.mem_univ _⟩, t, ht, ?_⟩
    exact Prod.ext he (by simp)

/-- The empty base has empty sweep. -/
@[simp]
theorem sweep_empty (n : V) : sweep (∅ : Set V) n = ∅ := by
  ext y
  simp [sweep]

/-- Positive rescaling of the sweeping vector does not change the swept support. -/
@[simp]
theorem sweep_smul_of_pos (P : Set V) (n : V) {a : ℝ} (ha : 0 < a) :
    sweep P (a • n) = sweep P n := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    exact ⟨x, hx, t * a, mul_nonneg ht ha.le, by rw [mul_smul]⟩
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨x, hx, t / a, div_nonneg ht ha.le, ?_⟩
    rw [smul_smul, div_mul_cancel₀ _ ha.ne']

/-- Every sweep is stable under further translation in its negative direction. -/
theorem sub_smul_mem_sweep {P : Set V} {n y : V} (hy : y ∈ sweep P n)
    {s : ℝ} (hs : 0 ≤ s) : y - s • n ∈ sweep P n := by
  obtain ⟨x, hx, t, ht, rfl⟩ := hy
  refine ⟨x, hx, t + s, add_nonneg ht hs, ?_⟩
  module

/-- A transverse direction admits a linear height constant on the base. -/
theorem exists_sweep_height {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), f n = 1 ∧ ∀ x ∈ P, f x = c := by
  obtain ⟨f, hfn, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨p, hp⟩ := hP
  refine ⟨(f n)⁻¹ • f, (f n)⁻¹ * f p, ?_, ?_⟩
  · simp [hfn]
  · intro x hx
    have h : f (x - p) = 0 := by
      have hmem : f (x - p) ∈ (vectorSpan ℝ P).map f :=
        Submodule.mem_map_of_mem (vsub_mem_vectorSpan ℝ hx hp)
      rwa [hf, Submodule.mem_bot] at hmem
    have heq : f x = f p := sub_eq_zero.mp (by simpa only [map_sub] using h)
    simp [heq]

/-- Membership via the uniquely determined base point and nonnegative height. -/
theorem mem_sweep_iff_of_height {P : Set V} {n y : V} (f : V →ₗ[ℝ] ℝ) (c : ℝ)
    (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c) :
    y ∈ sweep P n ↔ f y ≤ c ∧ y + (c - f y) • n ∈ P := by
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    have he : f (x - t • n) = c - t := by simp [hfP x hx, hfn]
    rw [he]
    refine ⟨sub_le_self _ ht, ?_⟩
    convert hx using 1
    module
  · rintro ⟨hy, hx⟩
    refine ⟨y + (c - f y) • n, hx, c - f y, sub_nonneg.mpr hy, ?_⟩
    module

/-- Transverse sweeps have unique base and ray coordinates. -/
theorem sweep_coordinates_unique {P : Set V} {n : V} (hn : n ∉ vectorSpan ℝ P)
    {x x' : V} (hx : x ∈ P) (hx' : x' ∈ P) {t t' : ℝ}
    (h : x - t • n = x' - t' • n) : x = x' ∧ t = t' := by
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hx⟩ hn
  have hheight := congrArg f h
  simp only [map_sub, map_smul, hfP x hx, hfP x' hx', hfn, smul_eq_mul,
    mul_one, sub_right_inj] at hheight
  subst t'
  exact ⟨sub_left_inj.mp h, rfl⟩

/-- The prism parameterization of a transverse sweep is a bijection. -/
noncomputable def sweepEquiv (P : Set V) (n : V)
    (hn : n ∉ vectorSpan ℝ P) :
    (P × {t : ℝ // 0 ≤ t}) ≃ sweep P n :=
  Equiv.ofBijective
    (fun z => ⟨z.1.1 - z.2.1 • n, z.1.1, z.1.2, z.2.1, z.2.2, rfl⟩)
    ⟨by
      intro z w h
      have he := sweep_coordinates_unique hn z.1.2 w.1.2 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2), by
      rintro ⟨y, x, hx, t, ht, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨t, ht⟩), rfl⟩⟩

/-- The prism equivalence evaluates by subtracting the ray parameter. -/
@[simp]
theorem sweepEquiv_apply (P : Set V) (n : V) (hn : n ∉ vectorSpan ℝ P)
    (z : P × {t : ℝ // 0 ≤ t}) :
    (sweepEquiv P n hn z : V) = z.1.1 - z.2.1 • n := (rfl)

/-- A normalized height gives the inverse prism coordinates explicitly. -/
theorem sweepEquiv_symm_apply {P : Set V} {n : V} (hn : n ∉ vectorSpan ℝ P)
    (f : V →ₗ[ℝ] ℝ) (c : ℝ) (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c)
    (y : sweep P n) :
    (sweepEquiv P n hn).symm y =
      (⟨(y : V) + (c - f y) • n, ((mem_sweep_iff_of_height f c hfn hfP).mp y.property).2⟩,
       ⟨c - f y, sub_nonneg.mpr ((mem_sweep_iff_of_height f c hfn hfP).mp y.property).1⟩) := by
  apply (sweepEquiv P n hn).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply, sweepEquiv_apply]
  module

/-- Every positive translate of a base point leaves the entire sweep. -/
theorem positive_translate_notMem_sweep {P : Set V} {n x : V}
    (hn : n ∉ vectorSpan ℝ P) (hx : x ∈ P) {t : ℝ} (ht : 0 < t) :
    x + t • n ∉ sweep P n := by
  obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height ⟨x, hx⟩ hn
  intro h
  have hle := ((mem_sweep_iff_of_height f c hfn hfP).mp h).1
  have : c + t ≤ c := by simpa [hfP x hx, hfn] using hle
  exact (not_le_of_gt (lt_add_of_pos_right c ht)) this

/-- The positive sweeping vector is not a recession direction. -/
theorem notMem_recessionCone_sweep {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    n ∉ recessionCone ℝ (sweep P n) := by
  rw [mem_recessionCone]
  intro h
  obtain ⟨x, hx⟩ := hP
  exact positive_translate_notMem_sweep hn hx zero_lt_one
    (h x (subset_sweep P n hx) 1 zero_le_one)

/-- A sweep of a nonempty set is nonempty. -/
theorem sweep_nonempty {P : Set V} (hP : P.Nonempty) (n : V) :
    (sweep P n).Nonempty := hP.mono (subset_sweep P n)

/-- Subdivision covers remain covers under sweeping. -/
theorem sweep_iUnion {ι : Sort*} (P : ι → Set V) (n : V) :
    sweep (⋃ i, P i) n = ⋃ i, sweep (P i) n := by
  ext y
  simp only [sweep, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hx⟩, t, ht, he⟩
    exact ⟨i, x, hx, t, ht, he⟩
  · rintro ⟨i, x, hx, t, ht, he⟩
    exact ⟨x, ⟨i, hx⟩, t, ht, he⟩

/-- On a transverse common base sweeping creates no new intersections. -/
theorem sweep_inter {P Q : Set V} {n : V} (hn : n ∉ vectorSpan ℝ (P ∪ Q)) :
    sweep P n ∩ sweep Q n = sweep (P ∩ Q) n := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, t, ht, he⟩, ⟨x', hx', t', ht', he'⟩⟩
    have hxx := (sweep_coordinates_unique hn (Or.inl hx) (Or.inr hx')
      (he.symm.trans he')).1
    exact ⟨x, ⟨hx, hxx ▸ hx'⟩, t, ht, he⟩
  · rintro ⟨x, ⟨hx, hx'⟩, t, ht, he⟩
    exact ⟨⟨x, hx, t, ht, he⟩, ⟨x, hx', t, ht, he⟩⟩

/-- A base cell meets a swept cell only along their original intersection when
both bases lie in a common transverse affine subspace. -/
theorem inter_sweep_of_transverse {P Q : Set V} {n : V}
    (hn : n ∉ vectorSpan ℝ (P ∪ Q)) : P ∩ sweep Q n = P ∩ Q := by
  ext y
  constructor
  · rintro ⟨hy, x, hx, t, ht, he⟩
    have hxy := sweep_coordinates_unique hn (Or.inl hy) (Or.inr hx)
      (t := 0) (t' := t) (by simpa using he)
    exact ⟨hy, hxy.1 ▸ hx⟩
  · exact fun hy => ⟨hy.1, subset_sweep Q n hy.2⟩

/-- Sweeping subsets of a common transverse base identifies no distinct supports. -/
theorem sweep_eq_sweep_iff_of_subset {P Q B : Set V} {n : V}
    (hn : n ∉ vectorSpan ℝ B) (hP : P ⊆ B) (hQ : Q ⊆ B) :
    sweep P n = sweep Q n ↔ P = Q := by
  constructor
  · intro he
    have hbase (S : Set V) (hS : S ⊆ B) : B ∩ sweep S n = S := by
      rw [inter_sweep_of_transverse (fun hm => hn (vectorSpan_mono ℝ
        (Set.union_subset le_rfl hS) hm)), Set.inter_eq_right.mpr hS]
    rw [← hbase P hP, he, hbase Q hQ]
  · rintro rfl
    rfl

/-- The direction of a nonempty sweep gains exactly the sweeping line. -/
theorem vectorSpan_sweep {P : Set V} (hP : P.Nonempty) (n : V) :
    vectorSpan ℝ (sweep P n) = vectorSpan ℝ P ⊔ Submodule.span ℝ {n} := by
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x, hx, t, ht, rfl⟩ := ha
    obtain ⟨y, hy, s, hs, rfl⟩ := hb
    have hbase : x - y ∈ vectorSpan ℝ P ⊔ Submodule.span ℝ {n} :=
      (le_sup_left : vectorSpan ℝ P ≤ _)
        (vsub_mem_vectorSpan ℝ hx hy)
    have hn : n ∈ vectorSpan ℝ P ⊔ Submodule.span ℝ {n} :=
      (le_sup_right : Submodule.span ℝ {n} ≤ _)
        (Submodule.subset_span (Set.mem_singleton n))
    have hh := (vectorSpan ℝ P ⊔ Submodule.span ℝ {n}).add_mem hbase
      ((vectorSpan ℝ P ⊔ Submodule.span ℝ {n}).smul_mem (s - t) hn)
    simp only [vsub_eq_sub]
    have he : (x - t • n) - (y - s • n) = x - y + (s - t) • n := by module
    rw [he]
    exact hh
  · apply sup_le (vectorSpan_mono ℝ (subset_sweep P n))
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨x, hx⟩ := hP
    have hy : x - n ∈ sweep P n := ⟨x, hx, 1, zero_le_one, by simp⟩
    simpa using vsub_mem_vectorSpan ℝ (subset_sweep P n hx) hy

/-- The affine dimension of a nonempty transverse sweep increases by one. -/
theorem finrank_sweep [FiniteDimensional ℝ V] {P : Set V} {n : V} (hP : P.Nonempty)
    (hn : n ∉ vectorSpan ℝ P) :
    Module.finrank ℝ (vectorSpan ℝ (sweep P n)) =
      Module.finrank ℝ (vectorSpan ℝ P) + 1 := by
  rw [vectorSpan_sweep hP n]
  exact Submodule.finrank_sup_span_singleton hn

/-- A swept affine span contains precisely the lines parallel to the sweeping
vector through the original affine span. Empty bases are allowed. -/
@[simp]
theorem mem_affineSpan_sweep_iff (P : Set V) (n y : V) :
    y ∈ affineSpan ℝ (sweep P n) ↔ ∃ t : ℝ, y + t • n ∈ affineSpan ℝ P := by
  obtain hP | ⟨x, hx⟩ := P.eq_empty_or_nonempty
  · simp [hP, AffineSubspace.notMem_bot]
  have hxP := subset_affineSpan ℝ P hx
  have hxS := subset_affineSpan ℝ (sweep P n) (subset_sweep P n hx)
  have hdir := vectorSpan_sweep ⟨x, hx⟩ n
  constructor
  · intro hy
    have hdiff := (affineSpan ℝ (sweep P n)).vsub_mem_direction hy hxS
    rw [direction_affineSpan, hdir] at hdiff
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hdiff
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨-t, ?_⟩
    have hmem := (affineSpan ℝ P).vadd_mem_of_mem_direction
      (by simpa only [direction_affineSpan] using hu) hxP
    simp only [vsub_eq_sub] at huv
    rw [← sub_add_cancel y x, ← huv]
    convert hmem using 1
    simp only [vadd_eq_add]
    module
  · rintro ⟨t, ht⟩
    have htS := affineSpan_mono ℝ (subset_sweep P n) ht
    have hn : n ∈ (affineSpan ℝ (sweep P n)).direction := by
      rw [direction_affineSpan, hdir]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self n)
    have hmem := (affineSpan ℝ (sweep P n)).vadd_mem_of_mem_direction
      ((affineSpan ℝ (sweep P n)).direction.smul_mem (-t) hn) htS
    convert hmem using 1
    simp only [vadd_eq_add]
    module

/-- Sweeping a set of codimension at least two has proper affine span.
Only nonempty bases need a dimension bound. -/
theorem affineSpan_sweep_ne_top [FiniteDimensional ℝ V] (P : Set V) (n : V)
    (hdim : P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V) :
    affineSpan ℝ (sweep P n) ≠ ⊤ := by
  obtain rfl | hP := P.eq_empty_or_nonempty
  · simp
  have hle : Module.finrank ℝ (vectorSpan ℝ (sweep P n)) ≤
      Module.finrank ℝ (vectorSpan ℝ P) + 1 := by
    by_cases hn : n ∈ vectorSpan ℝ P
    · rw [vectorSpan_sweep hP n,
        sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hn))]
      omega
    · exact (finrank_sweep hP hn).le
  intro htop
  rw [← direction_affineSpan, htop, AffineSubspace.direction_top,
    finrank_top] at hle
  exact (not_le_of_gt (hdim hP)) hle

end Algebra

end Set

namespace Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Sweeping a convex base preserves convexity. -/
theorem sweep {P : Set V} (hP : Convex ℝ P) (n : V) :
    Convex ℝ (Set.sweep P n) := by
  rintro _ ⟨x, hx, t, ht, rfl⟩ _ ⟨y, hy, s, hs, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hP hx hy ha hb hab, a * t + b * s,
    add_nonneg (mul_nonneg ha ht) (mul_nonneg hb hs), ?_⟩
  module

end Convex
