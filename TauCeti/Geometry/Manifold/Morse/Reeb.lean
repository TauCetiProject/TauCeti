/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Geometry.Manifold.Morse.Sublevel

/-!
# Reeb's sphere theorem

**Reeb's theorem** (Milnor, *Morse Theory*, Theorem 4.1): if a compact manifold `M` of dimension
`n` carries a Morse function with exactly two critical points, then `M` is homeomorphic to the
sphere `Sⁿ`. The conclusion is a homeomorphism, not a diffeomorphism: Milnor's exotic `7`-spheres
carry such functions.

The two critical points are the global minimum `x₀` and the global maximum `x₁` of `f`. Following
Milnor, for small `r > 0` the sublevel `{f ≤ f x₀ + r²}` and the superlevel `{f ≥ f x₁ - r²}` are
closed discs, by the Morse lemma at the nondegenerate extrema
(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_sublevel_homeomorph_closedBall`), and the
band between them contains no critical point, so the sublevel `{f ≤ f x₁ - r²}` is homeomorphic to
the small disc `{f ≤ f x₀ + r²}` by a homeomorphism carrying boundary level onto boundary level
(`TauCeti.exists_sublevelHomeomorph`). So `M` is the union of two closed discs meeting along their
boundary spheres, which is a sphere (`TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`).

If `f x₀ = f x₁` the function is constant, every point is a critical point, so `M` has exactly
two points, and a nondegenerate critical point that is both a local minimum and a local maximum
forces `n = 0`. Then `M` is the two-point sphere `S⁰`; no connectedness or dimension hypothesis is
needed.

## Main results

* `TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`: **Reeb's theorem**.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1.
* G. Reeb, *Sur les points singuliers d'une forme de Pfaff complètement intégrable ou d'une
  fonction numérique*, C. R. Acad. Sci. Paris 222 (1946), 847–849.
-/

public section

open Set Metric Module Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- Reeb's theorem when the minimum and the maximum differ: `M` is the union of a small disc
around the maximum and the sublevel below it, which the descending flow identifies with a small
disc around the minimum. -/
private theorem IsMorse.nonempty_homeomorph_sphere_of_lt (hf : IsMorse I f) {x₀ x₁ : M}
    (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  have hsmooth : ∀ᶠ y in 𝓝 x₀, ContMDiffAt I 𝓘(ℝ) ∞ f y := .of_forall fun y ↦ hf.contMDiff y
  have hsmooth' : ∀ᶠ y in 𝓝 x₁, ContMDiffAt I 𝓘(ℝ) ∞ (-f) y :=
    .of_forall fun y ↦ contDiff_neg.contMDiff.contMDiffAt.comp y (hf.contMDiff y)
  -- The minimum and the maximum are the only points with their values.
  have hmin (y : M) (hy : f y ≤ f x₀) : y = x₀ := by
    have hy' : IsMinOn f univ y := isMinOn_univ_iff.2 fun z ↦ hy.trans (hx₀ (mem_univ z))
    refine (hcrit y (hy'.isLocalMin univ_mem).mem_criticalPoints).resolve_right ?_
    rintro rfl
    linarith
  have hmax (y : M) (hy : (-f) y ≤ (-f) x₁) : y = x₁ := by
    simp only [Pi.neg_apply, neg_le_neg_iff] at hy
    have hy' : IsMaxOn f univ y := isMaxOn_univ_iff.2 fun z ↦ (hx₁ (mem_univ z)).trans hy
    refine (hcrit y (hy'.isLocalMax univ_mem).mem_criticalPoints).resolve_left ?_
    rintro rfl
    linarith
  -- Small sublevels at the minimum and small superlevels at the maximum are discs.
  obtain ⟨R₀, hR₀, he₀⟩ :=
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      ((hx₀.isLocalMin univ_mem).mem_criticalPoints)).exists_sublevel_homeomorph_closedBall
      hsmooth (isClosed_le hfc continuous_const).isCompact hfc.continuousOn hlt hmin
  obtain ⟨R₁, hR₁, he₁⟩ :=
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      ((hx₁.isLocalMax univ_mem).mem_criticalPoints)).neg.exists_sublevel_homeomorph_closedBall
      hsmooth' (isClosed_le hfc.neg continuous_const).isCompact hfc.neg.continuousOn
      (a := -f x₀) (by simpa using hlt) hmax
  -- Choose a common radius `r` with `f x₀ + r² < f x₁ - r²`.
  obtain ⟨r, ⟨hrR₀, hrR₁, hr2⟩, hr⟩ : ∃ r, (r < R₀ ∧ r < R₁ ∧ 2 * r ^ 2 < f x₁ - f x₀) ∧ 0 < r :=
    (((gt_mem_nhds hR₀).and ((gt_mem_nhds hR₁).and
      ((by fun_prop : Continuous fun r : ℝ ↦ 2 * r ^ 2).tendsto 0 |>.eventually_lt_const
        (by simpa using sub_pos.2 hlt)))).filter_mono nhdsWithin_le_nhds |>.and
      self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))
  have hr2' : 0 < r ^ 2 := by positivity
  -- The band between the two discs contains no critical point.
  have hreg (x : M) (ha : f x₀ + r ^ 2 ≤ f x) (hb : f x ≤ f x₁ - r ^ 2) :
      mfderiv I 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    rcases hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  obtain ⟨e, he⟩ := exists_sublevelHomeomorph hf.contMDiff (by linarith)
    (isClosed_Icc.preimage hfc).isCompact hreg
  obtain ⟨e₀, he₀⟩ := he₀ r hr.le hrR₀
  obtain ⟨e₁, he₁⟩ := he₁ r hr.le hrR₁
  -- Rescale the discs of radius `r` to unit discs; the boundary values are those at radius `r`.
  let S : closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) r ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 :=
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).subtype fun v ↦ by
      simp [norm_smul, abs_of_pos hr, inv_mul_le_iff₀ hr]
  have hS (c : ℝ) (v : closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) r) :
      c + ‖(v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ ^ 2 = c + r ^ 2 ↔
        ‖(S v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ = 1 := by
    rw [add_right_inj, sq_eq_sq₀ (norm_nonneg _) hr.le]
    simp [S, norm_smul, abs_of_pos hr, inv_mul_eq_one₀ hr.ne', eq_comm]
  -- `M` is covered by the sublevel `A` and the superlevel `B` at `f x₁ - r²`.
  let A : Set M := {x | f x ≤ f x₁ - r ^ 2}
  let B : Set M := {x | f x₁ - r ^ 2 ≤ f x}
  let eA : A ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 :=
    (e.trans e₀).trans S
  let eB₀ : B ≃ₜ {y // (-f) y ≤ (-f) x₁ + r ^ 2} :=
    (Homeomorph.refl M).subtype fun x ↦ by
      simp only [B, mem_ofPred_eq, Homeomorph.refl_apply, id_eq, Pi.neg_apply]
      constructor <;> intro <;> linarith
  let eB : B ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 :=
    (eB₀.trans e₁).trans S
  refine nonempty_homeomorph_sphere_of_union_closedBall (by simp)
    (isClosed_le hfc continuous_const) (isClosed_le continuous_const hfc)
    (eq_univ_of_forall fun x ↦ le_total (f x) (f x₁ - r ^ 2)) eA eB (fun x ↦ ?_) (fun x ↦ ?_)
  · have hx : (x : M) ∈ B ↔ f x = f x₁ - r ^ 2 := ⟨fun h ↦ le_antisymm x.2 h, fun h ↦ h.ge⟩
    rw [hx, ← he x, he₀ (e x)]
    simpa only [eA, Homeomorph.trans_apply] using hS _ _
  · have hx : (x : M) ∈ A ↔ f x = f x₁ - r ^ 2 := ⟨fun h ↦ le_antisymm h x.2, fun h ↦ h.le⟩
    have h₁ := he₁ (eB₀ x)
    have hx₀ : ((eB₀ x : {y // (-f) y ≤ (-f) x₁ + r ^ 2}) : M) = x := by simp [eB₀]
    rw [hx₀] at h₁
    simp only [Pi.neg_apply] at h₁
    have hneg : f x = f x₁ - r ^ 2 ↔ -f x = -f x₁ + r ^ 2 := by
      constructor <;> intro <;> linarith
    rw [hx, hneg, h₁]
    simpa only [eB, Homeomorph.trans_apply] using hS _ _

/-- **Reeb's theorem** (Milnor, *Morse Theory*, Theorem 4.1). A compact boundaryless manifold
modelled on a real vector space of dimension `n` which carries a Morse function with exactly two
critical points is homeomorphic to the sphere `Sⁿ`. -/
theorem IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two (hf : IsMorse I f)
    (h2 : totalCriticalCount I f = 2) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) := by
  obtain ⟨p, q, hpq, hpq'⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  have hfc : Continuous f := hf.contMDiff.continuous
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  · refine hf.nonempty_homeomorph_sphere_of_lt hx₀ hx₁ hlt fun x hx ↦ ?_
    have h₀ := (hx₀.isLocalMin univ_mem).mem_criticalPoints (I := I)
    have h₁ := (hx₁.isLocalMax univ_mem).mem_criticalPoints (I := I)
    have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
    rw [hpq', mem_insert_iff, mem_singleton_iff] at hx h₀ h₁
    grind
  -- A constant function: every point is critical, so `M = {p, q}`, and `M` is `0`-dimensional.
  have hall (x : M) : f x = f x₀ :=
    le_antisymm (hconst ▸ hx₁ (mem_univ x)) (hx₀ (mem_univ x))
  have hcrit (x : M) : x ∈ criticalPoints I f :=
    ((isMinOn_univ_iff.2 fun y ↦ by rw [hall x, hall y]).isLocalMin univ_mem).mem_criticalPoints
  have hE : finrank ℝ E = 0 := by
    have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (hcrit p)
    have hmin : IsLocalMin f p := .of_forall fun y ↦ by rw [hall p, hall y]
    have hmin' : IsLocalMin (-f) p := .of_forall fun y ↦ by simp [hall p, hall y]
    have h₀ := manifoldMorseIndex_eq_zero_of_isLocalMin
      ((hf.contMDiff p).of_le (by norm_cast)) hmin
    have h₀' := manifoldMorseIndex_eq_zero_of_isLocalMin (f := -f)
      ((contDiff_neg.contMDiff.contMDiffAt.comp p (hf.contMDiff p)).of_le (by norm_cast)) hmin'
    have := hnd.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  -- The discs are points, the single points `p` and `q`.
  have : Subsingleton (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    finrank_zero_iff.1 (by rw [finrank_euclideanSpace_fin, hE])
  have : Unique (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) :=
    { default := ⟨0, by simp⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }
  have hnorm (v : closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1) :
      ‖(v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ ≠ 1 := by
    simp [Subsingleton.elim (v : EuclideanSpace ℝ (Fin (finrank ℝ E))) 0]
  refine nonempty_homeomorph_sphere_of_union_closedBall (A := {p}) (B := {q})
    (F := EuclideanSpace ℝ (Fin (finrank ℝ E))) (by simp)
    isClosed_singleton isClosed_singleton
    (eq_univ_of_forall fun x ↦ by
      have hx := hcrit x
      rw [hpq', insert_eq] at hx
      exact hx)
    (Homeomorph.homeomorphOfUnique _ _) (Homeomorph.homeomorphOfUnique _ _)
    (fun x ↦ ?_) (fun x ↦ ?_)
  · simpa [mem_singleton_iff.1 x.2, hpq] using hnorm _
  · simpa [mem_singleton_iff.1 x.2, hpq.symm] using hnorm _

end TauCeti
