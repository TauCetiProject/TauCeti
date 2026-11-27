/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.LocalCoefficient
public import TauCeti.Geometry.Manifold.Morse.DG.DegreeZero

/-!
# The DG Morse complex with coefficients in a classical local system

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X` satisfying the Morse–Smale condition, and let `S` be a twisting chain system
on the spaces `L(x, y)` of broken trajectories, recorded on levels `c`. Its Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) evaluates the chains of `S` into the chains
on the Moore loops of a space `Y` at `y₀`, through a map `θ : M → Y` sending every critical point
to `y₀`. A classical local system `L` on `Y` is a DG local system concentrated in degree zero
(`TauCeti.classicalDGLocalSystem`), on which a chain of loops acts through its degree-zero part
(`TauCeti.classicalAction`). This file shows that the DG Morse complex with coefficients in `L`
is the Morse complex with coefficients in the pullback `θ^* L`, whose boundary transports along
the trajectories (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`).

* **Moore paths of records trace the trajectories.** The Moore path of the record of a trajectory,
  parametrized by the values of `f` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath`), is a
  reparametrization of the path traced by the trajectory (`Flow.connectingPath`), so the two are
  homotopic (`IsAdaptedPseudoGradient.homotopic_toPath_morseLevelPath`). Mapped by `θ`, the loop
  of a record has the image of the path class of its trajectory as class
  (`IsAdaptedPseudoGradient.mk_toPath_morseLoopEvaluation`).
* **Trajectory spaces of index difference one.** For `ind x = ind y + 1` the trajectory space
  from `x` to `y` is in bijection with the middle-level slice of trajectories
  (`IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceEquivSlice`), on which the
  classical Morse boundary is defined, by reading off the point of a record on the middle level.
* **The degree-zero entries act by transport.** The entry of the Barraud–Cornea cocycle at
  `(x, y)` acts on `L(y₀)` as the sum of the transports along the images under `θ` of the
  trajectories from `x` to `y`, weighted by their coefficients in the `0`-chain of `S`
  (`IsAdaptedPseudoGradient.IsMorseSmale.classicalAction_barraudCorneaCocycle_m`).
* **Classical recovery.** If `S` is graded by the Morse index and gives each trajectory of index
  difference one its sign, the entry at `(x, y)` acts as the component from `x` to `y` of the Morse
  boundary with coefficients in `θ^* L`, read through the identifications `L(y₀) ≅ L(θ x)`
  (`IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap`).
  Entries between critical points whose indices do not differ by one have nonzero degree and act by
  zero. In characteristic two every sign is `1`, so the hypothesis is that `S` gives every
  trajectory the coefficient `1`
  (`IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo`).

Since the twisted differential with coefficients concentrated in degree zero is the action of the
entries of the cocycle (`TauCeti.twistedDifferential_trivialGrading_apply`), the DG Morse complex
with coefficients in `L` has the differential of the Morse complex with coefficients in `θ^* L`.
When `θ` is homotopic to the identity, as for the collapse of a tree through the critical points,
`θ^* L` is isomorphic to `L`, so this is the Morse complex with coefficients in `L`.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceEquivSlice`: the
  bijection from a trajectory space of index difference one onto the middle-level slice.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `homotopic_toPath_morseLevelPath`: the Moore path of the record of a trajectory is homotopic to
  the path traced by the trajectory.
* `mk_toPath_morseLoopEvaluation`: the loop of the record of a trajectory has as class the image of
  the class of the trajectory.
* `IsMorseSmale.mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass`: the same, through the
  middle-level slice.
* `IsMorseSmale.classicalAction_barraudCorneaCocycle_m`: the entries of index difference one act on
  a classical local system by the weighted transports along the trajectories.
* `IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap`,
  `IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo`:
  classical recovery, over any ring for the oriented chain system and in characteristic two.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.
-/

public section

open MulOpposite Set unitInterval
open scoped ContDiff Manifold

universe u w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p r y : M} {c : ι → ℝ} {w : ι → M}

/-- On the record `w` of the trajectory through `y` from `p` to `r`, the point on the level of a
point `m` of that trajectory, or of one of its ends, is `m`: the case of one component of
`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint_eq`. -/
private theorem morseLevelPoint_eq_of_orbit (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r)
    (hw : ∀ i, f (w i) = c i ∧ ∃ t, hX.flow t y = w i) {m : M}
    (hm : m = p ∨ m = r ∨ ∃ t, hX.flow t y = m) : hX.morseLevelPoint p r c w (f m) = m := by
  refine hX.morseLevelPoint_eq (k := 1) (x := ![p, r]) (z := ![y]) hf hdense rfl rfl
    (fun j ↦ by fin_cases j; exacts [hp, hr]) (fun j ↦ by fin_cases j; exact hpr)
    (fun j ↦ by fin_cases j; exact hy) (fun i ↦ ⟨(hw i).1, 0, (hw i).2⟩) ?_
  rcases hm with rfl | rfl | ⟨t, rfl⟩
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr ⟨0, t, rfl⟩

/-- **The Moore path of the record of a trajectory traces the trajectory.** Let `w` record, on
levels dense between `f r` and `f p`, the trajectory through `y` from the critical point `p` to the
critical point `r ≠ p`. Then its Moore path, read on the unit interval, is homotopic to the path
traced by the trajectory (`Flow.connectingPath`). -/
theorem homotopic_toPath_morseLevelPath (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r)
    (w : hX.morseBrokenTrajectoryRecords p r c) (hw : ∀ i, ∃ t, hX.flow t y = (w : ι → M) i) :
    ((hX.morseLevelPath hf hdense w).toPath.cast (hX.source_morseLevelPath hf hdense w).symm
      (hX.target_morseLevelPath hf hdense w).symm).Homotopic (Flow.connectingPath hy.1 hy.2) := by
  set γ := Flow.connectingPath hy.1 hy.2
  set δ := (hX.morseLevelPath hf hdense w).toPath.cast (hX.source_morseLevelPath hf hdense w).symm
    (hX.target_morseLevelPath hf hdense w).symm
  have hL : 0 < f p - f r :=
    sub_pos.2 (hX.value_lt_of_mem_morseBrokenTrajectoryRecords hpr w.property)
  -- The drop of the value of `f` along `γ`, as a fraction of the total drop.
  let ρ : I → I := fun s ↦ projIcc 0 1 zero_le_one ((f p - f (γ s)) / (f p - f r))
  have hρ : Continuous ρ := continuous_projIcc.comp
    ((continuous_const.sub (hf.contMDiff.continuous.comp γ.continuous)).div_const _)
  have hρ₀ : ρ 0 = 0 := by simp [ρ]
  have hρ₁ : ρ 1 = 1 := by simp [ρ, div_self hL.ne']
  -- Every point of `γ` is an end or a point of the trajectory through `y`.
  have hγ (s : I) : γ s = p ∨ γ s = r ∨ ∃ t, hX.flow t y = γ s := by
    rcases eq_or_ne s 0 with rfl | h0
    · exact Or.inl γ.source
    rcases eq_or_ne s 1 with rfl | h1
    · exact Or.inr (Or.inl γ.target)
    refine Or.inr (Or.inr ⟨_, (Flow.connectingPath_apply_of_mem_Ioo hy.1 hy.2
      ⟨unitInterval.pos_iff_ne_zero.2 h0, unitInterval.lt_one_iff_ne_one.2 h1⟩).symm⟩)
  have hreparam : δ.reparam ρ hρ hρ₀ hρ₁ = γ := by
    ext s
    obtain ⟨_, _, _, -, -, -, -, -, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 w.property
    have hm := hX.morseLevelPoint_eq_of_orbit hf hdense hp hr hpr hy
      (fun i ↦ ⟨(hrec i).1, hw i⟩) (hγ s)
    simp only [Path.coe_reparam, Function.comp_apply, δ, Path.cast_coe, MoorePath.toPath_apply,
      morseLevelPath_apply, length_morseLevelPath, ρ]
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hL.le, coe_toNNReal]
    -- The fraction of the drop is clamped to `[0, 1]`; at either clamp, `γ s` is an end.
    rcases le_or_gt ((f p - f (γ s)) / (f p - f r)) 0 with h₀ | h₀
    · rw [projIcc_of_le_left _ h₀, Subtype.coe_mk, mul_zero, sub_zero,
        hX.morseLevelPoint_of_apply_le le_rfl, ← hm,
        hX.morseLevelPoint_of_apply_le (by linarith [(div_le_iff₀ hL).1 h₀])]
    rcases le_or_gt 1 ((f p - f (γ s)) / (f p - f r)) with h₁ | h₁
    · rw [projIcc_of_right_le _ h₁, Subtype.coe_mk, mul_one, sub_sub_cancel,
        hX.morseLevelPoint_of_le_apply w.property le_rfl, ← hm,
        hX.morseLevelPoint_of_le_apply w.property (by linarith [(one_le_div hL).1 h₁])]
    rw [projIcc_of_mem _ ⟨h₀.le, h₁.le⟩, Subtype.coe_mk, mul_div_cancel₀ _ hL.ne', sub_sub_cancel,
      hm]
  exact ⟨(Path.Homotopy.reparam δ ρ hρ hρ₀ hρ₁).cast rfl hreparam⟩

variable {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}

/-- **The loop of the record of a trajectory is the image of the trajectory.** Let `w` record the
trajectory through `z` from the critical point `x` to the critical point `y ≠ x`. Its loop at `y₀`,
the Moore path of `w` mapped by `θ` (`TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation`), has as
homotopy class the image under `θ` of the class of the path traced by the trajectory. -/
theorem mk_toPath_morseLoopEvaluation (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : (x : M) ≠ y)
    (w : hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) {z : M}
    (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y)
    (hw : ∀ i, ∃ t, hX.flow t z = w.val i) :
    Path.Homotopic.Quotient.mk (hX.morseLoopEvaluation hf hdense hθ x y w).toPath =
      ((Path.Homotopic.Quotient.mk (Flow.connectingPath hz.1 hz.2)).map θ).cast (hθ x).symm
        (hθ y).symm := by
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)
  have hloop : (hX.morseLoopEvaluation hf hdense hθ x y w).toPath =
      ((((hX.morseLevelPath hf hdense' w).toPath.cast (hX.source_morseLevelPath hf hdense' w).symm
        (hX.target_morseLevelPath hf hdense' w).symm).map θ.continuous).cast (hθ x).symm
          (hθ y).symm) := by
    ext s
    simp [MooreLoopSpace.toPath_apply]
  rw [hloop, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map,
    Path.Homotopic.Quotient.eq.2 (hX.homotopic_toPath_morseLevelPath hf hdense'
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hxy hz w hw)]

/-! ### Trajectory spaces of index difference one and the middle-level slice -/

section Slice

variable {x y : M} {a : ℝ}

/-- The record on the levels of `c` of the trajectory through `z`: its points where the orbit of
`z` crosses the levels. -/
private noncomputable def sliceRecord (hX : IsAdaptedPseudoGradient f X) (c : ι → ℝ) (z : M) :
    ι → M :=
  fun i ↦ hX.flow (Flow.levelCrossingTime hX.flow f (c i) z) z

private theorem sliceRecord_spec (hxy : x ≠ y) {z : M}
    (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y) (hc : ∀ i, c i ∈ Ioo (f y) (f x))
    (i : ι) : f (sliceRecord hX c z i) = c i ∧ ∃ t, hX.flow t z = sliceRecord hX c z i :=
  ⟨Flow.apply_flow_levelCrossingTime
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hxy hz (hc i).1 (hc i).2).exists,
    _, rfl⟩

/-- On a level strictly between the values at its ends, a trajectory from `x` to `y` through `z`
has a point of `W^u(x) ∩ W^s(y)`. -/
private theorem exists_flow_mem_level (hxy : x ≠ y)
    {z : M} (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y) (ha : a ∈ Ioo (f y) (f x)) :
    ∃ t, f (hX.flow t z) = a ∧ hX.flow t z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y :=
  let ⟨t, ht, _⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hxy hz ha.1 ha.2
  ⟨t, ht, hX.flow.isInvariant_unstableSet_inter_stableSet x y t hz⟩

/-- The points of the middle-level slice lie on trajectories from `x` to `y`. -/
private theorem mem_inter_of_mem_morseTrajectorySlice {z : M}
    (hz : z ∈ hX.morseTrajectorySlice x y) :
    z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y :=
  ⟨(hX.mem_morseTrajectorySlice.1 hz).1, (hX.mem_morseTrajectorySlice.1 hz).2.1⟩

end Slice

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
private theorem ne_of_morseIndex_eq_add_one {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    (x : M) ≠ y := fun hxy ↦ by
  rw [Subtype.coe_injective hxy] at hind
  omega

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {x y : criticalPoints 𝓘(ℝ, E) f}
  (hdense : Ioo (f y) (f x) ⊆ closure (range c))
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)

include h hf hdense hind in
/-- In index difference one, the point on the middle level of a trajectory record lies in the
middle-level slice, and the record is the record of the trajectory through it. -/
private theorem morseLevelPoint_mid_spec (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w ((f x + f y) / 2) ∈
        hX.morseTrajectorySlice x y ∧
      ∀ i, ∃ t, hX.flow t (hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w
        ((f x + f y) / 2)) = w.val i := by
  have hx := mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property
  have hy := mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo hdense
  obtain ⟨hxy, hwB⟩ := hX.mem_morseBrokenTrajectorySpace.1 w.property
  obtain ⟨z, hz, hwz⟩ := hX.mem_morseTrajectoryRecords.1
    ((h.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords hf hx hy hxy hind.le).subset
      w.property)
  have hlt := hX.value_lt_of_mem_morseBrokenTrajectoryRecords hxy hwB
  obtain ⟨t, ht, hmem⟩ := exists_flow_mem_level hxy hz (a := (f x + f y) / 2)
    ⟨by linarith, by linarith⟩
  have hm := hX.morseLevelPoint_eq_of_orbit hf hdense' hx hy hxy hz hwz (Or.inr (Or.inr ⟨t, rfl⟩))
  rw [ht] at hm
  rw [hm]
  refine ⟨hX.mem_morseTrajectorySlice.2 ⟨hmem.1, hmem.2, ht⟩, fun i ↦ ?_⟩
  obtain ⟨s, hs⟩ := (hwz i).2
  exact ⟨s - t, by rw [← Flow.map_add, sub_add_cancel, hs]⟩

/-- **The trajectories of index difference one are their points on the middle level.** Under the
Morse–Smale condition, for critical points `x` and `y` with `ind x = ind y + 1` and levels of `c`
dense between `f y` and `f x`, reading off the point on the middle level `(f x + f y) / 2` is a
bijection from the trajectory space from `x` to `y` onto the middle-level slice of trajectories
from `x` to `y` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice`), on which the Morse
boundary is defined. -/
noncomputable def morseBrokenTrajectorySpaceEquivSlice :
    hX.morseBrokenTrajectorySpace c x y ≃ hX.morseTrajectorySlice x y where
  toFun w := ⟨_, (morseLevelPoint_mid_spec h hf hdense hind w).1⟩
  invFun z := ⟨sliceRecord hX ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) z,
    hX.mem_morseBrokenTrajectorySpace.2 ⟨ne_of_morseIndex_eq_add_one hind,
      hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) (ne_of_morseIndex_eq_add_one hind) _
        (hX.mem_morseTrajectoryRecords.2
          ⟨z, mem_inter_of_mem_morseTrajectorySlice z.property,
            sliceRecord_spec (ne_of_morseIndex_eq_add_one hind)
              (mem_inter_of_mem_morseTrajectorySlice z.property) fun i ↦ i.property⟩)⟩⟩
  left_inv w := by
    obtain ⟨hm, hwm⟩ := morseLevelPoint_mid_spec h hf hdense hind w
    have hxy := ne_of_morseIndex_eq_add_one hind
    have hm' := mem_inter_of_mem_morseTrajectorySlice hm
    obtain ⟨_, _, _, -, -, -, -, -, hrec⟩ :=
      hX.mem_morseBrokenTrajectoryRecords.1 (hX.mem_morseBrokenTrajectorySpace.1 w.property).2
    refine Subtype.ext (funext fun i ↦ ?_)
    -- Both points lie on the orbit of the middle point, on the level `c i`.
    obtain ⟨t, ht⟩ := hwm i
    have hci := i.property
    obtain ⟨τ, -, hτ⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hxy hm' hci.1
      hci.2
    have h₁ := hτ (Flow.levelCrossingTime hX.flow f ((c ⁻¹' Ioo (f y) (f x)).domRestrict c i) _)
      (sliceRecord_spec (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c) hxy hm' (fun i ↦ i.property)
        i).1
    have h₂ := hτ t (by beta_reduce; rw [ht]; exact (hrec i).1)
    simp only [sliceRecord] at h₁ ⊢
    rw [h₁, ← h₂, ht]
  right_inv z := by
    have hxy := ne_of_morseIndex_eq_add_one hind
    have hz := hX.mem_morseTrajectorySlice.1 z.property
    refine Subtype.ext ?_
    simp only
    rw [← hz.2.2]
    exact hX.morseLevelPoint_eq_of_orbit hf (subset_closure_range_domRestrict_preimage isOpen_Ioo
      hdense) (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hxy ⟨hz.1, hz.2.1⟩
      (sliceRecord_spec hxy ⟨hz.1, hz.2.1⟩ fun i ↦ i.property)
      (Or.inr (Or.inr ⟨0, Flow.map_zero_apply _ _⟩))

/-- The point on the middle level of a trajectory of index difference one. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceEquivSlice_apply (w : hX.morseBrokenTrajectorySpace c x y) :
    (h.morseBrokenTrajectorySpaceEquivSlice hf hdense hind w : M) =
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w ((f x + f y) / 2) :=
  (rfl)

/-- A trajectory record of index difference one records the trajectory through its point on the
middle level. -/
theorem exists_flow_morseBrokenTrajectorySpaceEquivSlice (w : hX.morseBrokenTrajectorySpace c x y)
    (i : c ⁻¹' Ioo (f y) (f x)) :
    ∃ t, hX.flow t (h.morseBrokenTrajectorySpaceEquivSlice hf hdense hind w) = w.val i :=
  (morseLevelPoint_mid_spec h hf hdense hind w).2 i

/-- **The loop of a trajectory of index difference one is the image of the trajectory.** Under the
Morse–Smale condition, for `ind x = ind y + 1`, the loop at `y₀` of a point `w` of the trajectory
space from `x` to `y` has as homotopy class the image under `θ` of the path class
`TauCeti.IsAdaptedPseudoGradient.trajectoryPathClass` of the corresponding point of the
middle-level slice, along which the Morse boundary with local coefficients transports. -/
theorem mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass
    (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (w : hX.morseBrokenTrajectorySpace c x y) :
    Path.Homotopic.Quotient.mk (hX.morseLoopEvaluation hf hdense' hθ x y
        (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)).toPath =
      ((hX.trajectoryPathClass (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w)).map
        θ).cast (hθ x).symm (hθ y).symm := by
  rw [trajectoryPathClass_def]
  exact hX.mk_toPath_morseLoopEvaluation hf hdense' hθ (ne_of_morseIndex_eq_add_one hind)
    (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)
    (mem_inter_of_mem_morseTrajectorySlice
      (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w).property)
    (h.exists_flow_morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w)

section ClassicalAction

variable {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}

/-- **Between consecutive indices the Barraud–Cornea cocycle acts on a classical local system by
transport along the trajectories.** Under the Morse–Smale condition, let `ind x = ind y + 1`, and
let `L` be a local system on `Y`, read at `y₀` as a DG local system in degree zero
(`TauCeti.classicalDGLocalSystem`). The entry at `(x, y)` of the Barraud–Cornea cocycle of a
twisting chain system `S` acts on the fibre `L(y₀)` as the sum, over the trajectories from `x` to
`y` read on the middle-level slice, of the transports along their images under `θ`, weighted by
the coefficients of the trajectories in the `0`-chain of `S`. -/
theorem classicalAction_barraudCorneaCocycle_m (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      ∑ᶠ z : hX.morseTrajectorySlice x y,
        NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)
            ((h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hind).symm z) •
          (LocalCoefficientSystem.transport L
            (((hX.trajectoryPathClass z).map θ).cast (hθ x).symm (hθ y).symm)).toLinearMap := by
  set e := h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hind
  -- A Moore loop acts on the fibre by the transport along its class.
  have hF (w : hX.morseBrokenTrajectorySpace c x y) :
      (L.fiberRightAction (MooreLoopSpace.fundamentalGroupHom y₀ (hX.morseLoopEvaluation hf hdense
        hθ x y (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)))).unop =
      (LocalCoefficientSystem.transport L
        (((hX.trajectoryPathClass (e w)).map θ).cast (hθ x).symm (hθ y).symm)).toLinearMap := by
    rw [← h.mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass hf hind hdense hθ w]
    ext v
    rw [MooreLoopSpace.fundamentalGroupHom_apply, LocalCoefficientSystem.fiberRightAction_apply,
      unop_op, inv_inv, LocalCoefficientSystem.monodromyRepresentation_apply, LinearEquiv.coe_coe,
      LocalCoefficientSystem.transport_apply]
  rw [classicalAction_op_apply, loopChainToGroupAlgebra_barraudCorneaCocycle_m, map_finsuppSum]
  simp only [MonoidAlgebra.lift_single]
  rw [MulOpposite.unop_finsuppSum]
  simp only [MulOpposite.unop_smul, hF, Finsupp.sum]
  rw [← finsum_eq_sum_of_support_subset _
    (s := (NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)).support) fun w hw ↦ ?_,
    ← finsum_comp_equiv e.symm]
  · simp only [Equiv.apply_symm_apply]
  · simpa using left_ne_zero_of_smul hw

/-- Transport along a path class whose ends are moved by equalities is the transport along the
class, conjugated by the transports along the constant classes that move the ends. -/
private theorem transport_cast {Z : TopCat.{u}} (L : LocalCoefficientSystem.{u, u, w} R Z)
    {a b a' b' : Z} (P : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    (LocalCoefficientSystem.transport L (P.cast ha hb)).toLinearMap =
      (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl b').cast rfl hb.symm)).symm.toLinearMap ∘ₗ
        (LocalCoefficientSystem.transport L P).toLinearMap ∘ₗ
          (LocalCoefficientSystem.transport L
            ((Path.Homotopic.Quotient.refl a').cast rfl ha.symm)).toLinearMap := by
  subst ha hb
  ext v
  simp

/-- **Classical recovery.** Under the Morse–Smale condition, let the index of the twisting chain
system `S` be the Morse index, and let `S` give each trajectory between critical points of
consecutive index its sign for the orientations `𝔬` in its `0`-chain, as the fundamental chains
of the oriented trajectory spaces of index difference one do. Then, for a local system `L` on `Y`
read at `y₀` as a DG local system in degree zero, the entry at `(x, y)` of the Barraud–Cornea
cocycle acts on `L(y₀)` as the component from `x` to `y` of the Morse boundary of `f` with
coefficients in the pullback `θ^* L` (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`),
read through the identifications `L(y₀) ≅ L(θ x)` along `θ x = y₀`. So the DG Morse complex with
coefficients in a classical local system is the Morse complex with local coefficients. -/
theorem classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝔬 : MorseOrientation f X)
    (hS : ∀ (x y : criticalPoints 𝓘(ℝ, E) f)
      (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
      (w : hX.morseBrokenTrajectorySpace c x y),
      NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w =
        hX.trajectorySign (𝔬.chart x) (𝔬.chart y) (𝔬.orientation x) (𝔬.orientation y) hxy
          (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w))
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) (x y : criticalPoints 𝓘(ℝ, E) f) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ
        hX.twistedMorseBoundaryMap 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) x y ∘ₗ
          (LocalCoefficientSystem.transport L
            ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap := by
  by_cases hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1
  · have := (h.finite_morseTrajectorySlice hf hxy).to_subtype
    -- Conjugating by the identifications of the fibres is additive.
    let φ : ((((LocalCoefficientSystem.pullback (X := TopCat.of M) (Y := TopCat.of Y) θ).obj L).obj
          (FundamentalGroupoid.mk (x : M))) →ₗ[R]
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) (Y := TopCat.of Y) θ).obj L).obj
          (FundamentalGroupoid.mk (y : M))) →+
          Module.End R (L.obj (FundamentalGroupoid.mk y₀)) :=
      AddMonoidHom.mk' (fun g ↦ (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ g ∘ₗ
            (LocalCoefficientSystem.transport L
              ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap)
        -- The pulled-back fibres are fibres of `L` only up to unfolding the pullback, which `simp`
        -- does not see through; the composite is additive by `map_add` of the outer map.
        fun g g' ↦ LinearMap.ext fun v ↦ (map_add (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm _ _ :)
    rw [h.classicalAction_barraudCorneaCocycle_m hf hdense hθ hc S L hxy,
      twistedMorseBoundaryMap_of_morseIndex_eq_add_one hxy]
    change _ = φ _
    rw [map_finsum φ (Set.toFinite _)]
    refine finsum_congr fun z ↦ ?_
    rw [map_zsmul, hS x y hxy, Equiv.apply_symm_apply, Int.cast_smul_eq_zsmul]
    congr 1
    simp only [φ, AddMonoidHom.mk'_apply, LocalCoefficientSystem.pullback_transport]
    exact transport_cast L _ (hθ x).symm (hθ y).symm
  · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hxy,
      classicalAction_eq_zero L (loopChainToGroupAlgebra_eq_zero_of_mem (i := ind y - ind x + 1)
        (by rw [hind, hind]; omega) ((hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded x y))]
    ext
    exact (map_zero (LocalCoefficientSystem.transport L
      ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm).symm

/-- **Classical recovery modulo two.** In characteristic two the signs of the trajectories are
`1`. So if the `0`-chains of `S` give every trajectory between critical points of consecutive
index the coefficient `1`, as the mod-two fundamental chains of the finite trajectory spaces do,
the Barraud–Cornea cocycle acts on a classical local system as the Morse boundary with
coefficients in the pullback, for every choice of orientations. -/
theorem classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo [CharP R 2]
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (hS : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1 →
        ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w = 1)
    (𝔬 : MorseOrientation f X) (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y))
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ
        hX.twistedMorseBoundaryMap 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) x y ∘ₗ
          (LocalCoefficientSystem.transport L
            ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap := by
  refine h.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap hf hdense hθ hc hind S
    𝔬 (fun x y hxy w ↦ ?_) L x y
  rw [hS x y hxy w]
  rcases trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart x) (𝔬.coord_mfderiv_chart y)
    (op := 𝔬.orientation x) (oq := 𝔬.orientation y) (hpq := hxy) h hf
    (mem_inter_of_mem_morseTrajectorySlice
      (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w).property) with hs | hs <;>
    rw [hs]
  · exact Int.cast_one.symm
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

end ClassicalAction

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
