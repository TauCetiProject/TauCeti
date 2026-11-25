/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# Adjacent separation on annular polar sectors

On an angular interval, each positive deck shift factors into adjacent shifts inside the
sector. Summing the adjacent separations therefore detects collisions of the graph. Conversely,
for a continuous height the intermediate value theorem gives one strict sign on the overlap.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open Set

/-- The portion of the polar cover with radius in `(r,R)` and angle in `I`. -/
def annularSector (r R : ℝ) (I : Set ℝ) : Set PolarPoint :=
  {p | radius p ∈ Ioo r R ∧ angle p ∈ I}

@[simp, grind =] theorem mem_annularSector_iff {r R : ℝ} {I : Set ℝ} {p : PolarPoint} :
    p ∈ annularSector r R I ↔ radius p ∈ Ioo r R ∧ angle p ∈ I := Iff.rfl

/-- Deck overlap leaves the radial interval unchanged and intersects the angular set with
its translate. -/
@[grind =] theorem overlap_annularSector (r R : ℝ) (I : Set ℝ) (k : ℤ) :
    overlap (annularSector r R I) k =
      annularSector r R (I ∩ (fun θ ↦ θ + (k : ℝ) * (2 * Real.pi)) ⁻¹' I) := by
  ext p
  simp [and_left_comm, and_assoc]

/-- Every deck overlap of an annular angular interval is preconnected. -/
theorem isPreconnected_overlap_annularSector (r R : ℝ) {I : Set ℝ} (hI : I.OrdConnected)
    (k : ℤ) : IsPreconnected (overlap (annularSector r R I) k) := by
  let J := I ∩ (fun θ ↦ θ + (k : ℝ) * (2 * Real.pi)) ⁻¹' I
  have hJ : J.OrdConnected := hI.inter (hI.preimage_mono fun _ _ h ↦ add_le_add_left h _)
  rw [overlap_annularSector]
  have hval : Topology.IsInducing (Subtype.val : PolarPoint → ℝ × ℝ) :=
    Topology.IsInducing.subtypeVal (t := {p : ℝ × ℝ | 0 < p.1})
  apply (hval.isPreconnected_image (s := annularSector r R J)).mp
  have himage : Subtype.val '' annularSector r R J = (Ioi 0 ∩ Ioo r R) ×ˢ J := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simp only [mem_annularSector_iff, radius_def, angle_def] at hp
      exact ⟨⟨p.property, hp.1⟩, hp.2⟩
    · rintro ⟨⟨hρ, hρ'⟩, hθ⟩
      refine ⟨⟨x, hρ⟩, ?_, rfl⟩
      simpa only [mem_annularSector_iff, radius_def, angle_def] using And.intro hρ' hθ
  rw [himage]
  exact (inferInstance : (Ioi 0 ∩ Ioo r R).OrdConnected).isPreconnected.prod hJ.isPreconnected

/-- Each intermediate positive turn stays in an annular sector with interval angular set. -/
theorem deckShift_mem_annularSector_of_le {r R : ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    {p : PolarPoint} {n j : ℕ} (hp : p ∈ overlap (annularSector r R I) n) (hj : j ≤ n) :
    deckShift j p ∈ annularSector r R I := by
  obtain ⟨h₀, hn⟩ := mem_overlap_iff.mp hp
  obtain ⟨hρ, hθ⟩ := mem_annularSector_iff.mp h₀
  have hnθ := (mem_annularSector_iff.mp hn).2
  apply mem_annularSector_iff.mpr
  refine ⟨by simpa only [radius_deckShift] using hρ, hI.out hθ hnθ ?_⟩
  simp only [mem_Icc, angle_deckShift, Int.cast_natCast, le_add_iff_nonneg_right,
    add_le_add_iff_left]
  exact ⟨by positivity, mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)⟩

/-- One strict sign for adjacent separation implies injectivity on an annular angular
interval, for an arbitrary height function. -/
theorem injOn_graph_annularSector_of_separation_sign {r R : ℝ} {I : Set ℝ}
    (hI : I.OrdConnected) {u : PolarPoint → ℝ}
    (hs : (∀ p ∈ overlap (annularSector r R I) 1, 0 < separation u 1 p) ∨
      (∀ p ∈ overlap (annularSector r R I) 1, separation u 1 p < 0)) :
    InjOn (graph u) (annularSector r R I) := by
  have hpos (n : ℕ) (hn : n ≠ 0) (p : PolarPoint) (hp : p ∈ overlap (annularSector r R I) n) :
      separation u n p ≠ 0 := by
    have hstep (j : ℕ) (hj : j ∈ Finset.range n) :
        deckShift j p ∈ overlap (annularSector r R I) 1 := by
      have hjn := Finset.mem_range.mp hj
      refine mem_overlap_iff.mpr ⟨deckShift_mem_annularSector_of_le hI hp hjn.le, ?_⟩
      rw [← deckShift_add, ← Nat.cast_succ]
      exact deckShift_mem_annularSector_of_le hI hp hjn
    rw [separation_natCast_eq_sum]
    rcases hs with h | h
    · exact (Finset.sum_pos (fun j hj ↦ h _ (hstep j hj)) (Finset.nonempty_range_iff.mpr hn)).ne'
    · exact (Finset.sum_neg (fun j hj ↦ h _ (hstep j hj)) (Finset.nonempty_range_iff.mpr hn)).ne
  apply (graph_injOn_iff _ _).mpr
  intro k hk p hp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact hpos n (by omega) p hp
  · have hrev := hpos n (by omega) (deckShift (-(n : ℤ)) p)
        (mem_overlap_iff.mpr ⟨(mem_overlap_iff.mp hp).2, by simpa using (mem_overlap_iff.mp hp).1⟩)
    have hneg := separation_neg_deckShift u (-(n : ℤ)) p
    rw [neg_neg] at hneg
    exact neg_ne_zero.mp (hneg ▸ hrev)

/-- A continuous polar graph on an annular angular interval is injectively parametrized
exactly when the adjacent separation is strictly positive everywhere or strictly negative
everywhere on its overlap. This includes the empty-overlap case. -/
theorem injOn_graph_annularSector_iff_separation_sign {r R : ℝ} {I : Set ℝ}
    (hI : I.OrdConnected) {u : PolarPoint → ℝ} (hu : ContinuousOn u (annularSector r R I)) :
    InjOn (graph u) (annularSector r R I) ↔
      (∀ p ∈ overlap (annularSector r R I) 1, 0 < separation u 1 p) ∨
      (∀ p ∈ overlap (annularSector r R I) 1, separation u 1 p < 0) := by
  refine ⟨fun hi ↦ ?_, injOn_graph_annularSector_of_separation_sign hI⟩
  have hne := (graph_injOn_iff _ _).mp hi 1 one_ne_zero
  by_cases h : ∀ p ∈ overlap (annularSector r R I) 1, 0 < separation u 1 p
  · exact Or.inl h
  · push Not at h
    obtain ⟨p, hp, hpw⟩ := h
    refine Or.inr fun q hq ↦ lt_of_not_ge fun hqw ↦ ?_
    obtain ⟨z, hz, hwz⟩ := (isPreconnected_overlap_annularSector r R hI 1).intermediate_value
      hp hq (continuousOn_separation hu 1) (mem_Icc.mpr ⟨hpw, hqw⟩)
    exact hne z hz hwz

end TauCeti.PolarGraph
