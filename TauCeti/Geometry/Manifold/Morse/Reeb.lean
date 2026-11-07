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

/-- Two positive radii and a positive gap admit a common smaller positive radius whose double
square fits in the gap. -/
theorem exists_pos_lt_lt_two_mul_sq_lt {R₀ R₁ d : ℝ} (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) (hd : 0 < d) :
    ∃ r, (r < R₀ ∧ r < R₁ ∧ 2 * r ^ 2 < d) ∧ 0 < r :=
  (((gt_mem_nhds hR₀).and ((gt_mem_nhds hR₁).and
    ((by fun_prop : Continuous fun r : ℝ ↦ 2 * r ^ 2).tendsto 0 |>.eventually_lt_const
      (by simpa using hd)))).filter_mono nhdsWithin_le_nhds |>.and
    self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))

/-- The closed ball of radius `r > 0` is homeomorphic to the unit closed ball by a rescaling that
carries the boundary sphere onto the boundary sphere. -/
theorem exists_homeomorph_closedBall_one_norm_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {r : ℝ} (hr : 0 < r) :
    ∃ S : closedBall (0 : V) r ≃ₜ closedBall (0 : V) 1,
      ∀ v : closedBall (0 : V) r, ‖(S v : V)‖ = 1 ↔ ‖(v : V)‖ = r := by
  refine ⟨(Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')).subtype fun v ↦ by
    simp [norm_smul, abs_of_pos hr, inv_mul_le_iff₀ hr], fun v ↦ ?_⟩
  simp [norm_smul, abs_of_pos hr, inv_mul_eq_one₀ hr.ne', eq_comm]

/-- Reeb's theorem when the minimum and the maximum differ: `M` is the union of a small disc
around the maximum and the sublevel below it, which the descending flow identifies with a small
disc around the minimum. -/
private theorem IsMorse.nonempty_homeomorph_sphere_of_lt (hf : IsMorse I f) {x₀ x₁ : M}
    (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  have hsmooth : ∀ᶠ y in 𝓝 x₀, ContMDiffAt I 𝓘(ℝ) ∞ f y := .of_forall fun y ↦ hf.contMDiff y
  -- The minimum and the maximum are the only points with their values.
  have hmin (y : M) (hy : f y ≤ f x₀) : y = x₀ := hx₀.eq_of_le_of_two_criticalPoints hlt hcrit hy
  have hmax (y : M) (hy : f x₁ ≤ f y) : y = x₁ := hx₁.eq_of_le_of_two_criticalPoints hlt hcrit hy
  -- Small sublevels at the minimum and small superlevels at the maximum are discs.
  obtain ⟨R₀, hR₀, he₀⟩ :=
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      ((hx₀.isLocalMin univ_mem).mem_criticalPoints)).exists_sublevel_homeomorph_closedBall
      hsmooth (isClosed_le hfc continuous_const).isCompact hfc.continuousOn hlt hmin
  obtain ⟨R₁, hR₁, he₁⟩ :=
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      ((hx₁.isLocalMax univ_mem).mem_criticalPoints)).exists_superlevel_homeomorph_closedBall
      (.of_forall fun y ↦ hf.contMDiff y) (isClosed_le continuous_const hfc).isCompact
      hfc.continuousOn (a := f x₀) hlt hmax
  obtain ⟨r, ⟨hrR₀, hrR₁, hr2⟩, hr⟩ :=
    exists_pos_lt_lt_two_mul_sq_lt hR₀ hR₁ (sub_pos.2 hlt)
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
  obtain ⟨S, hS'⟩ := exists_homeomorph_closedBall_one_norm_eq
    (V := EuclideanSpace ℝ (Fin (finrank ℝ E))) hr
  have hS (c : ℝ) (v : closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) r) :
      c + ‖(v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ ^ 2 = c + r ^ 2 ↔
        ‖(S v : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ = 1 := by
    rw [add_right_inj, sq_eq_sq₀ (norm_nonneg _) hr.le]
    exact (hS' v).symm
  -- `M` is covered by the sublevel `A` and the superlevel `B` at `f x₁ - r²`.
  let A : Set M := {x | f x ≤ f x₁ - r ^ 2}
  let B : Set M := {x | f x₁ - r ^ 2 ≤ f x}
  let eA : A ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 :=
    (e.trans e₀).trans S
  let eB : B ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 := e₁.trans S
  refine nonempty_homeomorph_sphere_of_union_closedBall (by simp)
    (isClosed_le hfc continuous_const) (isClosed_le continuous_const hfc)
    (eq_univ_of_forall fun x ↦ le_total (f x) (f x₁ - r ^ 2)) eA eB (fun x ↦ ?_) (fun x ↦ ?_)
  · have hx : (x : M) ∈ B ↔ f x = f x₁ - r ^ 2 := ⟨fun h ↦ le_antisymm x.2 h, fun h ↦ h.ge⟩
    rw [hx, ← he x, he₀ (e x)]
    simpa only [eA, Homeomorph.trans_apply] using hS _ _
  · have hx : (x : M) ∈ A ↔ f x = f x₁ - r ^ 2 := ⟨fun h ↦ le_antisymm h x.2, fun h ↦ h.le⟩
    have h₁ := he₁ x
    have hneg : f x = f x₁ - r ^ 2 ↔ ‖(e₁ x : EuclideanSpace ℝ (Fin (finrank ℝ E)))‖ = r := by
      rw [h₁, ← sq_eq_sq₀ (norm_nonneg _) hr.le]
      constructor <;> intro <;> linarith
    rw [hx, hneg]
    simpa only [eB, Homeomorph.trans_apply] using (hS' (e₁ x)).symm

/-- **Reeb's theorem** (Milnor, *Morse Theory*, Theorem 4.1). A compact boundaryless manifold
modelled on a real vector space of dimension `n` which carries a Morse function with exactly two
critical points is homeomorphic to the sphere `Sⁿ`. -/
theorem IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two (hf : IsMorse I f)
    (h2 : totalCriticalCount I f = 2) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) := by
  obtain ⟨p, q, hx₀, hx₁, hpq, hpq', hlt | ⟨hall, huniv⟩⟩ :=
    exists_isMinOn_isMaxOn_of_totalCriticalCount_eq_two (I := I) hf.contMDiff.continuous h2
  · exact hf.nonempty_homeomorph_sphere_of_lt hx₀ hx₁ hlt fun x hx ↦ by rwa [hpq'] at hx
  -- A constant function: every point is critical, so `M = {p, q}`, and `M` is `0`-dimensional.
  have hcrit (x : M) : x ∈ criticalPoints I f := huniv ▸ mem_univ x
  have hE : finrank ℝ E = 0 := by
    have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (hcrit p)
    have hmin : IsLocalMin f p := .of_forall fun y ↦ by rw [hall y]
    have hmin' : IsLocalMin (-f) p := .of_forall fun y ↦ by simp [hall y]
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
