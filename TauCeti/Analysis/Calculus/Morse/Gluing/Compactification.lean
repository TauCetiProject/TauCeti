/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Compactifying local glued Morse trajectories

Record a trajectory through a split hyperbolic box by its entrance and exit points.
When these lie on transverse Lipschitz discs, their pairs form a half-open arc. Its closure
adds exactly the broken pair `((g 0, 0), (0, k 0))` and is homeomorphic to a closed interval.
The inverse coordinate is the norm of the expanding entrance coordinate divided by the
box radius. Thus the topology remembers both halves of a broken trajectory.

The contraction construction in
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image` supplies every unbroken
trajectory, not just a family approaching the broken one. Here it yields a topological boundary
chart for the local gluing problem. This does not compactify global trajectory spaces or
assert smoothness of the gluing chart.

## Main results

* `TauCeti.closure_splitGluingPairs`: precisely one broken pair is added.
* `TauCeti.exists_homeomorph_closure_splitGluingPairs`: a closed interval chart with explicit
  inverse coordinate and broken endpoint.
* `TauCeti.isCompact_closure_splitGluingPairs`: compactness of the paired local gluing space.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing with a pseudo-gradient linear near critical points).
-/

public section

open Function Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {ε r₀ : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ}

/-- Entrance and exit pairs of unbroken trajectories through the split box, with entrance
on the graph of `g`, exit on the graph of `k`, and gluing parameter at most `r₀`. -/
def splitGluingPairs (ε r₀ : ℝ) (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ) :
    Set (WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)) :=
  {p | p.1 ∈ (splitPassage ε).source ∧ ‖p.1.snd‖ ≤ r₀ * ε ∧
    p.1.fst = g p.1.snd ∧ p.2 = splitPassage ε p.1 ∧ p.2.snd = k p.2.fst}

/-- The entrance and exit conditions defining the unbroken gluing pairs. -/
@[simp]
theorem mem_splitGluingPairs {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} :
    p ∈ splitGluingPairs ε r₀ g k ↔
      p.1 ∈ (splitPassage ε).source ∧ ‖p.1.snd‖ ≤ r₀ * ε ∧
        p.1.fst = g p.1.snd ∧ p.2 = splitPassage ε p.1 ∧ p.2.snd = k p.2.fst :=
  Iff.rfl

/-- Extend the paired gluing parametrization continuously to parameter zero. The norm
coordinate recovers the parameter even at the broken pair. -/
private theorem exists_splitGluingPairs_parametrization [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ),
      ContinuousOn F (Icc 0 r₀) ∧ F '' Ioc 0 r₀ = splitGluingPairs ε r₀ g k ∧
      F 0 = (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) ∧
      ∀ r ∈ Icc 0 r₀, ‖(F r).1.snd‖ / ε = r := by
  obtain ⟨w, hw, hw₀, hwnorm, himage⟩ :=
    exists_setOf_mem_splitPassage_source_graph_eq_image hg hgε hk hkε hε hr₀₁ hK
  -- Pair the entrance parametrization with its exit formula; both remain continuous at zero.
  let v : ℝ → Eᵤ := fun r ↦ r • w r
  let a : ℝ → Eₛ := fun r ↦ g (v r)
  let F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) :=
    fun r ↦ (WithLp.toLp 2 (a r, v r), WithLp.toLp 2 (r • a r, w r))
  have hv : ContinuousOn v (Icc 0 r₀) := continuousOn_id.smul hw.continuousOn
  have hvball : MapsTo v (Icc 0 r₀) (closedBall 0 (r₀ * ε)) := by
    intro r hr
    simp only [mem_closedBall_zero_iff, v]
    rw [norm_smul, Real.norm_of_nonneg hr.1, hwnorm r hr]
    exact mul_le_mul_of_nonneg_right hr.2 hε.le
  have ha : ContinuousOn a (Icc 0 r₀) := hg.continuousOn.comp hv hvball
  have hF : ContinuousOn F (Icc 0 r₀) :=
    ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn (ha.prodMk hv)).prodMk
      ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn
        ((continuousOn_id.smul ha).prodMk hw.continuousOn))
  have hpass (r : ℝ) (hr : r ∈ Ioc 0 r₀) : (F r).2 = splitPassage ε (F r).1 :=
     (splitPassage_toLp_smul (a r) (hwnorm r (Ioc_subset_Icc_self hr)) hε hr.1).symm
  have hnorm (r : ℝ) (hr : r ∈ Icc 0 r₀) : ‖(F r).1.snd‖ / ε = r := by
    simp only [F, WithLp.toLp_snd, v, norm_smul, Real.norm_of_nonneg hr.1, hwnorm r hr]
    exact mul_div_cancel_right₀ r hε.ne'
  refine ⟨F, hF, ?_, by simp [F, a, v, hw₀], hnorm⟩
  -- The existing surjectivity theorem for entrance points also captures every exit pair.
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hentry : (F r).1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
        z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} := by
      rw [himage]
      exact ⟨r, hr, rfl⟩
    exact ⟨hentry.1, hentry.2.1, hentry.2.2.1, hpass r hr,
      by rw [hpass r hr]; exact hentry.2.2.2⟩
  · rintro ⟨hsrc, hbound, hgraph, hexit, hkgraph⟩
    have hentry : p.1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
        z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} :=
      ⟨hsrc, hbound, hgraph, by rwa [← hexit]⟩
    rw [himage] at hentry
    obtain ⟨r, hr, heq⟩ := hentry
    refine ⟨r, hr, Prod.ext heq ?_⟩
    rw [hpass r hr]
    exact (congrArg (splitPassage ε) heq).trans hexit.symm

variable [CompleteSpace Eᵤ]
  (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
  (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
  (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
  (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
  (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)

include hg hgε hk hkε hε hr₀ hr₀₁ hK

/-- The closure of the unbroken entrance/exit pairs adds exactly the pair of stable entrance
and unstable exit points of the broken trajectory. No other limiting configurations occur. -/
theorem closure_splitGluingPairs :
    closure (splitGluingPairs ε r₀ g k) =
      insert (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) (splitGluingPairs ε r₀ g k) := by
  obtain ⟨F, hF, himage, hF₀, -⟩ :=
    exists_splitGluingPairs_parametrization hg hgε hk hkε hε hr₀₁ hK
  have hclosure : closure (F '' Ioc 0 r₀) = F '' Icc 0 r₀ := by
    refine subset_antisymm
      (closure_minimal (image_mono Ioc_subset_Icc_self)
        (isCompact_Icc.image_of_continuousOn hF).isClosed)
      ?_
    have h := ContinuousOn.image_closure (s := Ioc 0 r₀) (f := F)
      (by rwa [closure_Ioc hr₀.ne])
    simpa only [closure_Ioc hr₀.ne] using h
  rw [← himage, hclosure, ← Ioc_insert_left hr₀.le, image_insert_eq, hF₀]

/-- The local compactified gluing space is a closed interval. Its inverse gluing coordinate
is the expanding entrance norm divided by the box radius, and parameter zero is the broken
trajectory. The assertion includes all unbroken pairs in the prescribed range. -/
theorem exists_homeomorph_closure_splitGluingPairs :
    ∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k),
      (∀ p, (e.symm p : ℝ) = ‖p.val.1.snd‖ / ε) ∧
      (e ⟨0, by constructor <;> linarith⟩).val =
        (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) := by
  obtain ⟨F, hF, himage, hF₀, hcoord⟩ :=
    exists_splitGluingPairs_parametrization hg hgε hk hkε hε hr₀₁ hK
  have hclosure : closure (splitGluingPairs ε r₀ g k) = F '' Icc 0 r₀ := by
    rw [closure_splitGluingPairs hg hgε hk hkε hε hr₀ hr₀₁ hK, ← himage,
      ← hF₀, ← image_insert_eq, Ioc_insert_left hr₀.le]
  let f : Icc (0 : ℝ) r₀ → closure (splitGluingPairs ε r₀ g k) :=
    fun r ↦ ⟨F r, by rw [hclosure]; exact mem_image_of_mem F r.property⟩
  have hf : Continuous f := hF.domRestrict.codRestrict _
  have hsurj : Surjective f := by
    rintro ⟨p, hp⟩
    rw [hclosure] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact ⟨⟨r, hr⟩, rfl⟩
  have hleft (r : Icc (0 : ℝ) r₀) : ‖(f r).val.1.snd‖ / ε = r := hcoord r r.property
  let inv : closure (splitGluingPairs ε r₀ g k) → Icc (0 : ℝ) r₀ := fun p ↦
    ⟨‖p.val.1.snd‖ / ε, by obtain ⟨r, rfl⟩ := hsurj p; rw [hleft]; exact r.property⟩
  have hleftinv : LeftInverse inv f := fun r ↦ Subtype.ext (hleft r)
  let e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k) :=
    { toFun := f
      invFun := inv
      left_inv := hleftinv
      right_inv := hleftinv.rightInverse_of_surjective hsurj
      continuous_toFun := hf
      continuous_invFun := by
        fun_prop }
  exact ⟨e, fun _ ↦ rfl, hF₀⟩

/-- The closure of the paired local gluing space is compact, even when the stable and
unstable ambient spaces are infinite dimensional. -/
theorem isCompact_closure_splitGluingPairs :
    IsCompact (closure (splitGluingPairs ε r₀ g k)) := by
  obtain ⟨e, -, -⟩ :=
    exists_homeomorph_closure_splitGluingPairs hg hgε hk hkε hε hr₀ hr₀₁ hK
  exact isCompact_iff_compactSpace.mpr e.compactSpace

end TauCeti
