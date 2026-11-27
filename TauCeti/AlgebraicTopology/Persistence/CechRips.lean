/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Analysis.InnerProductSpace.Jung

/-!
# Čech and Vietoris–Rips complexes

For a family of points `x : ι → E` in a pseudometric space and a scale `r : ℝ`, the
Vietoris–Rips complex `ripsComplex x r` has as faces the nonempty finite sets of indices whose
points have pairwise distances at most `2 r`, and the (ambient) Čech complex `cechComplex x r`
those whose points lie in a common closed ball of radius `r`, with centre anywhere in `E`
(Dey–Wang, *Computational Topology for Data Analysis*, Defs 2.9 and 2.10; Edelsbrunner–Harer,
*Computational Topology*, §III.2). Both grow with `r`, and both are empty for `r < 0`.

## Main results

* `TauCeti.cechComplex_le_ripsComplex_le`: `Čech(r) ⊆ Rips(r) ⊆ Čech(2 r)` in every
  pseudometric space.
* `TauCeti.ripsComplex_le_cechComplex_sqrt_two`: **the Vietoris–Rips lemma**,
  `Rips(r) ⊆ Čech(√2 r)` in every real inner product space, from Jung's theorem
  `TauCeti.exists_mem_convexHull_dist_le_div_sqrt_two`.
* `TauCeti.pair_mem_cechComplex_iff`: in a real normed affine space the two complexes have the
  same edges: `{a, b}` is a Čech face at scale `r` iff `d(x a, x b) ≤ 2 r`.

## Attribution

The Vietoris–Rips lemma is adapted from lean-CKSD, `CKSD/Geometry/Persistence/CechRips.lean`
(`CKSD.cech_rips_inclusions`), by the author, with AI assistance (Claude); it is restated here for
the complexes of an indexed family in any real inner product space.
-/

public section

namespace TauCeti

variable {ι E : Type*}

section PseudoMetric

variable [PseudoMetricSpace E]

/-- The Vietoris–Rips complex of a family of points: faces of diameter at most `2 r`. -/
def ripsComplex (x : ι → E) (r : ℝ) : PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ ∀ a ∈ σ, ∀ b ∈ σ, dist (x a) (x b) ≤ 2 * r}
  isRelLowerSet_faces := fun _ hσ =>
    ⟨hσ.1, fun _ hτσ hτ => ⟨hτ, fun a ha b hb => hσ.2 a (hτσ ha) b (hτσ hb)⟩⟩

/-- The (ambient) Čech complex: faces whose closed balls of radius `r` meet. -/
def cechComplex (x : ι → E) (r : ℝ) : PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ ∃ z, ∀ a ∈ σ, dist (x a) z ≤ r}
  isRelLowerSet_faces := fun _ hσ =>
    ⟨hσ.1, fun _ hτσ hτ => ⟨hτ, hσ.2.imp fun _ hz a ha => hz a (hτσ ha)⟩⟩

variable {x : ι → E} {r : ℝ} {σ : Finset ι}

/-- A face of the Vietoris–Rips complex is a nonempty finite set of indices whose points have
pairwise distances at most `2 r`. -/
@[simp]
theorem mem_ripsComplex :
    σ ∈ ripsComplex x r ↔ σ.Nonempty ∧ ∀ a ∈ σ, ∀ b ∈ σ, dist (x a) (x b) ≤ 2 * r :=
  Iff.rfl

/-- A face of the Čech complex is a nonempty finite set of indices whose points lie in a common
closed ball of radius `r`. -/
@[simp]
theorem mem_cechComplex : σ ∈ cechComplex x r ↔ σ.Nonempty ∧ ∃ z, ∀ a ∈ σ, dist (x a) z ≤ r :=
  Iff.rfl

/-- The Vietoris–Rips complexes grow with the scale. -/
theorem ripsComplex_mono (x : ι → E) : Monotone (ripsComplex x) := fun _ _ h _ hσ =>
  ⟨hσ.1, fun a ha b hb => (hσ.2 a ha b hb).trans (by linarith)⟩

/-- The Čech complexes grow with the scale. -/
theorem cechComplex_mono (x : ι → E) : Monotone (cechComplex x) := fun _ _ h _ hσ =>
  ⟨hσ.1, hσ.2.imp fun _ hz a ha => (hz a ha).trans h⟩

/-- A vertex is a face of the Vietoris–Rips complex exactly at nonnegative scales. -/
@[simp high]
theorem singleton_mem_ripsComplex {a : ι} : {a} ∈ ripsComplex x r ↔ 0 ≤ r := by
  simp

/-- A vertex is a face of the Čech complex exactly at nonnegative scales. -/
@[simp high]
theorem singleton_mem_cechComplex {a : ι} : {a} ∈ cechComplex x r ↔ 0 ≤ r :=
  ⟨fun ⟨_, z, hz⟩ => dist_nonneg.trans (hz a (Finset.mem_singleton_self a)),
    fun hr => ⟨Finset.singleton_nonempty a, x a, by simpa using hr⟩⟩

/-- At a negative scale the Vietoris–Rips complex has no faces. -/
@[simp]
theorem ripsComplex_eq_bot (hr : r < 0) : ripsComplex x r = ⊥ :=
  eq_bot_iff.2 fun _ ⟨⟨a, ha⟩, h⟩ => by linarith [h a ha a ha, dist_self (x a)]

/-- At a negative scale the Čech complex has no faces. -/
@[simp]
theorem cechComplex_eq_bot (hr : r < 0) : cechComplex x r = ⊥ :=
  eq_bot_iff.2 fun _ ⟨⟨a, ha⟩, z, hz⟩ => by linarith [hz a ha, dist_nonneg (x := x a) (y := z)]

/-- **Čech and Rips complexes interleave** in every metric space:
`Čech(r) ⊆ Rips(r) ⊆ Čech(2 r)`. -/
theorem cechComplex_le_ripsComplex_le (x : ι → E) (r : ℝ) :
    cechComplex x r ≤ ripsComplex x r ∧ ripsComplex x r ≤ cechComplex x (2 * r) := by
  refine ⟨fun σ ⟨hσ, z, hz⟩ => ⟨hσ, fun a ha b hb => ?_⟩, fun σ ⟨⟨b, hb⟩, h⟩ =>
    ⟨⟨b, hb⟩, x b, fun a ha => h a ha b hb⟩⟩
  linarith [dist_triangle_right (x a) (x b) z, hz a ha, hz b hb]

/-- An edge is a face of the Vietoris–Rips complex at scale `r` iff its length is at most
`2 r`. -/
@[simp high]
theorem pair_mem_ripsComplex_iff [DecidableEq ι] {a b : ι} :
    {a, b} ∈ ripsComplex x r ↔ dist (x a) (x b) ≤ 2 * r := by
  refine ⟨fun h => h.2 a (by simp) b (by simp), fun h => ⟨Finset.insert_nonempty _ _, ?_⟩⟩
  have hr : 0 ≤ 2 * r := dist_nonneg.trans h
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, dist_self,
    dist_comm (x b) (x a)]
  exact ⟨⟨hr, h⟩, h, hr⟩

end PseudoMetric

/-- In a real normed affine space, an edge is a face of the Čech complex at scale `r` iff its
length is at most `2 r`, as for the Vietoris–Rips complex: the midpoint is a common centre. -/
theorem pair_mem_cechComplex_iff {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace E] [NormedAddTorsor V E] [DecidableEq ι] {x : ι → E} {r : ℝ} {a b : ι} :
    {a, b} ∈ cechComplex x r ↔ dist (x a) (x b) ≤ 2 * r := by
  refine ⟨fun h => pair_mem_ripsComplex_iff.1 ((cechComplex_le_ripsComplex_le x r).1 h),
    fun h => ⟨Finset.insert_nonempty _ _, midpoint ℝ (x a) (x b), ?_⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    dist_left_midpoint (𝕜 := ℝ), dist_right_midpoint (𝕜 := ℝ)]
  constructor <;> norm_num <;> linarith

/-- **The Vietoris–Rips lemma** in a real inner product space: `Rips(r) ⊆ Čech(√2 r)`. -/
theorem ripsComplex_le_cechComplex_sqrt_two [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ι → E) (r : ℝ) : ripsComplex x r ≤ cechComplex x (Real.sqrt 2 * r) := by
  classical
  intro σ ⟨hσ, h⟩
  obtain ⟨z, -, hz⟩ := exists_mem_convexHull_dist_le_div_sqrt_two (hσ.image x)
    (δ := 2 * r) (by simpa using h)
  refine ⟨hσ, z, fun a ha => (hz (x a) (Finset.mem_image_of_mem x ha)).trans_eq ?_⟩
  rw [mul_div_right_comm, Real.div_sqrt]

end TauCeti
