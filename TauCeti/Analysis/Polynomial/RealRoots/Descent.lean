/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Analytic.FiniteFamily
public import TauCeti.Analysis.Polynomial.Conjugation

/-!
# Real descent of finite root labellings

A finite continuous complete labelling of the complex roots of a real polynomial family
with persistent collisions descends to the labels real at the central parameter. Analyticity
of their real parts gives analytic real sections. A complete root multiset and a locally
constant collision relation also give constant multiplicities; removing repeated labels
then yields strictly ordered sections on one common open neighborhood.

These results allow repeated labels and empty root families. They require neither monicity
nor continuity of the polynomial coefficients, and apply to arbitrary real normed parameter
spaces. Preparation of the complex labels and their collision relation is separate.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {B ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {F : B → ℝ[X]} {r : ι → B → ℂ} {b₀ : B}

/-- Descend a finite continuous complete complex root labelling with persistent central
collisions to analytic real sections, retaining repeated labels. Only the real parts need
be analytic; the selected sections agree with their complex labels near the center. -/
theorem exists_analyticAt_real_roots_of_persistent_collisions [Finite ι]
    (hr : ∀ i, ContinuousAt (r i) b₀)
    (hre : ∀ i, AnalyticAt ℝ (fun b ↦ (r i b).re) b₀)
    (hroot : ∀ᶠ b in 𝓝 b₀, ∀ z, ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔
      ∃ i, r i b = z)
    (hcollision : ∀ i j, r j b₀ = r i b₀ → r j =ᶠ[𝓝 b₀] r i) :
    ∃ s : {i : ι // (r i b₀).im = 0} → B → ℝ,
      (∀ i, AnalyticAt ℝ (s i) b₀) ∧
      ∀ᶠ b in 𝓝 b₀, (∀ i, (s i b : ℂ) = r i.val b) ∧
        ∀ z, (F b).IsRoot z ↔ ∃ i, s i b = z := by
  have hlabels := eventually_root_im_eq_zero_iff_of_persistent_collisions hr hroot hcollision
  let s : {i : ι // (r i b₀).im = 0} → B → ℝ := fun i b ↦ (r i.val b).re
  refine ⟨s, fun i ↦ hre i.val, ?_⟩
  filter_upwards [hlabels, hroot] with b hb hRb
  have hsr (i : {i : ι // (r i b₀).im = 0}) : (s i b : ℂ) = r i.val b :=
    Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ((hb i.val).mpr i.property))
  refine ⟨hsr, fun z ↦ ?_⟩
  rw [← isRoot_map_iff (algebraMap ℝ ℂ).injective, hRb]
  constructor
  · rintro ⟨i, hi⟩
    have him : (r i b₀).im = 0 := (hb i).mp (by simp [hi])
    exact ⟨⟨i, him⟩, Complex.ofReal_injective ((hsr ⟨i, him⟩).trans hi)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, (hsr i).symm.trans (congrArg (fun z : ℝ ↦ (z : ℂ)) hi)⟩

/-- A finite complete root multiset with locally constant collisions gives strictly ordered
analytic real root sections with constant positive multiplicities. The real parts of the
continuous labels need be analytic only at the central parameter. Nonzeroness is retained
on the resulting neighborhood, including when there are no real roots. -/
theorem exists_analyticOnNhd_ordered_real_roots_of_persistent_collisions [Fintype ι]
    (hr : ∀ i, ContinuousAt (r i) b₀)
    (hre : ∀ i, AnalyticAt ℝ (fun b ↦ (r i b).re) b₀)
    (hroots : ∀ᶠ b in 𝓝 b₀, ((F b).map (algebraMap ℝ ℂ)).roots =
      Finset.univ.val.map (fun i ↦ r i b))
    (hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0)
    (hcollision : ∀ᶠ b in 𝓝 b₀, ∀ i j,
      r i b = r j b ↔ r i b₀ = r j b₀) :
    ∃ k : ℕ, ∃ s : Fin k → B → ℝ, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      (∀ b ∈ U, F b ≠ 0) ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ b ∈ U, StrictMono (fun i ↦ s i b)) ∧
      (∀ b ∈ U, ∀ z, (F b).IsRoot z ↔ ∃ i, s i b = z) ∧
      (∀ i, 0 < (F b₀).rootMultiplicity (s i b₀)) ∧
      ∀ b ∈ U, ∀ i,
        (F b).rootMultiplicity (s i b) = (F b₀).rootMultiplicity (s i b₀) := by
  classical
  have hroot : ∀ᶠ b in 𝓝 b₀, ∀ z,
      ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔ ∃ i, r i b = z := by
    filter_upwards [hroots, hF] with b hb hFb z
    rw [← mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 hFb), hb]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  obtain ⟨f, hf, hfr⟩ := exists_analyticAt_real_roots_of_persistent_collisions hr hre hroot
    (fun i j hji ↦ hcollision.mono fun b hb ↦ (hb j i).2 hji)
  have heq (i j : {i : ι // (r i b₀).im = 0})
      (hij : f i b₀ = f j b₀) : f i =ᶠ[𝓝 b₀] f j := by
    have hc : r i.val b₀ = r j.val b₀ := by
      rw [← hfr.self_of_nhds.1 i, ← hfr.self_of_nhds.1 j, hij]
    filter_upwards [hfr, hcollision] with b hb hbc
    apply Complex.ofReal_injective
    rw [hb.1 i, hb.1 j]
    exact (hbc i.val j.val).2 hc
  obtain ⟨k, e, V, hV, hbV, hs, horder⟩ :=
    exists_analyticOnNhd_strictMono_range_eq hf heq
  have hmult := eventually_rootMultiplicity_eq_of_roots_eq_map hroots.self_of_nhds hroots
    (hcollision.mono fun b hb i _ j _ ↦ hb i j)
  have hm : ∀ᶠ b in 𝓝 b₀, ∀ i,
      (F b).rootMultiplicity (f (e i) b) =
        (F b₀).rootMultiplicity (f (e i) b₀) := by
    filter_upwards [hfr, hmult] with b hb hmb i
    rw [eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective,
      eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective (f (e i) b₀),
      Complex.coe_algebraMap, hb.1 (e i), hfr.self_of_nhds.1 (e i)]
    exact hmb (e i).val (Finset.mem_univ _)
  obtain ⟨U, hU, hopen, hbU⟩ := eventually_nhds_iff.1
    (Filter.Eventually.and (hV.mem_nhds hbV) (hF.and (hfr.and hm)))
  refine ⟨k, fun i ↦ f (e i), U, hopen, hbU,
    fun b hb ↦ (hU b hb).2.1,
    fun i ↦ (hs i).mono fun b hb ↦ (hU b hb).1,
    fun b hb ↦ (horder b (hU b hb).1).1, ?_, ?_,
    fun b hb ↦ (hU b hb).2.2.2⟩
  · intro b hb z
    rw [(hU b hb).2.2.1.2 z]
    exact (congrArg (z ∈ ·) (horder b (hU b hb).1).2).symm.to_iff
  · intro i
    apply (rootMultiplicity_pos hF.self_of_nhds).2
    exact hfr.self_of_nhds.2 _ |>.2 ⟨e i, rfl⟩

end TauCeti
