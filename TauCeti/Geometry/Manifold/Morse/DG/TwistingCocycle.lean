/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath

/-!
# The Barraud–Cornea cocycle of the compactified Morse trajectory spaces

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f`. Fix a dense set `L` of levels containing no level of a critical point; a countable
one exists (`TauCeti.IsMorse.exists_countable_dense_forall_apply_notMem`). For critical points `x`
and `y`, the compactified space of trajectories from `x` to `y` is the space of records of broken
trajectories from `x` to `y` on the levels of `L` strictly between `f y` and `f x`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`).

These spaces, indexed by the critical points, carry the structure on which twisting chain systems
(`TauCeti.TwistingChainSystem`) and their Moore-loop cocycles
(`TauCeti.TwistingChainSystem.mooreTwistingCocycle`) are built:

* **composition maps** `𝓜(x, y) × 𝓜(y, z) → 𝓜(x, z)`, concatenating broken trajectories at `y`
  (`TauCeti.IsAdaptedPseudoGradient.morseRecordsComp`). They are associative
  (`TauCeti.IsAdaptedPseudoGradient.morseRecordsComp_assoc`), which is what makes the twisting sum
  of a family of chains on these spaces a cycle
  (`TauCeti.cubicalChainDifferential_twistingChainSum`);
* **evaluations into Moore paths** from `x` to `y`, parametrizing a broken trajectory by the values
  of `f` (`TauCeti.IsAdaptedPseudoGradient.morseRecordsEval`), which take composition to
  concatenation of Moore paths
  (`TauCeti.IsAdaptedPseudoGradient.morseRecordsEval_morseRecordsComp`).

So every twisting chain system on the compactified trajectory spaces, together with a map
`θ : M → Y` sending all critical points to one point `y₀`, gives a twisting cocycle over the
cubical chains `C^□_*(Ω_{y₀} Y)` on the Moore loops of `Y`
(`TauCeti.TwistingChainSystem.morseTwistingCocycle`). Its entry at `(x, y)` is the push-forward of
the chain of `(x, y)` along the evaluation of broken trajectories into Moore paths, followed by
`θ`. For a representing chain system, whose chains are fundamental chains relative to the boundary
(`TauCeti.TwistingChainSystem.IsRepresenting`), and for `θ` the collapse of an embedded tree through
the critical points, this is the Barraud–Cornea cocycle, which twists the Morse complex with
coefficients in a DG local system.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseRecordsComp`: the composition maps of the compactified
  trajectory spaces between critical points.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordsEval`: their evaluation into Moore paths.
* `TauCeti.TwistingChainSystem.morseTwistingCocycle`: the twisting cocycle over the Moore loops of
  a twisting chain system on the compactified trajectory spaces.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.morseRecordsComp_assoc`: the composition maps are associative.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordsEval_morseRecordsComp`: the evaluation into Moore
  paths takes composition to concatenation.
* `TauCeti.TwistingChainSystem.morseTwistingCocycle_m`: the entries of the twisting cocycle.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L : Set ℝ}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

section Comp

variable (hL : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∉ L)

/-- **The composition maps of the compactified trajectory spaces**: for critical points `x`, `y`
and `z`, the concatenation at `y` of broken trajectories from `x` to `y` and from `y` to `z`,
recorded on the levels of a set `L` containing no level of a critical point. -/
def morseRecordsComp (x y z : criticalPoints 𝓘(ℝ, E) f) :
    C(↥(hX.morseBrokenTrajectoryRecords x y (Subtype.val : ↥(L ∩ Ioo (f y) (f x)) → ℝ)) ×
        ↥(hX.morseBrokenTrajectoryRecords y z (Subtype.val : ↥(L ∩ Ioo (f z) (f y)) → ℝ)),
      ↥(hX.morseBrokenTrajectoryRecords x z (Subtype.val : ↥(L ∩ Ioo (f z) (f x)) → ℝ))) :=
  hX.morseBrokenTrajectoryConcat (hL y y.property)

/-- The composition maps are the concatenation of broken trajectories. -/
@[simp]
theorem morseRecordsComp_apply (x y z : criticalPoints 𝓘(ℝ, E) f)
    (w : ↥(hX.morseBrokenTrajectoryRecords x y (Subtype.val : ↥(L ∩ Ioo (f y) (f x)) → ℝ)) ×
      ↥(hX.morseBrokenTrajectoryRecords y z (Subtype.val : ↥(L ∩ Ioo (f z) (f y)) → ℝ))) :
    hX.morseRecordsComp hL x y z w = hX.morseBrokenTrajectoryConcat (hL y y.property) w :=
  (rfl)

/-- **The composition maps of the compactified trajectory spaces are associative**, in the form
required of the composition maps of a twisting chain system
(`TauCeti.cubicalChainDifferential_twistingChainSum`). -/
theorem morseRecordsComp_assoc {x y : criticalPoints 𝓘(ℝ, E) f} (w z : criticalPoints 𝓘(ℝ, E) f)
    (a : ↥(hX.morseBrokenTrajectoryRecords x w (Subtype.val : ↥(L ∩ Ioo (f w) (f x)) → ℝ)))
    (b : ↥(hX.morseBrokenTrajectoryRecords w z (Subtype.val : ↥(L ∩ Ioo (f z) (f w)) → ℝ)))
    (c : ↥(hX.morseBrokenTrajectoryRecords z y (Subtype.val : ↥(L ∩ Ioo (f y) (f z)) → ℝ))) :
    hX.morseRecordsComp hL x z y (hX.morseRecordsComp hL x w z (a, b), c) =
      hX.morseRecordsComp hL x w y (a, hX.morseRecordsComp hL w z y (b, c)) :=
  hX.morseBrokenTrajectoryConcat_assoc _ _ a b c

end Comp

section Eval

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The levels of a dense set `L` strictly between `a` and `b` are dense between `a` and `b`. -/
private theorem subset_closure_range_subtypeVal (hdense : Dense L) (a b : ℝ) :
    Ioo a b ⊆ closure (range (Subtype.val : ↥(L ∩ Ioo a b) → ℝ)) := by
  rw [Subtype.range_coe, inter_comm]
  exact hdense.open_subset_closure_inter isOpen_Ioo

/-- **The evaluation of the compactified trajectory spaces into Moore paths**: a broken trajectory
from `p` to `r`, recorded on the levels of a dense set `L`, is sent to the Moore path of length
`f p - f r` whose point at time `t` is its point on the level `f p - t`. -/
def morseRecordsEval (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Dense L) (p r : M) :
    C(↥(hX.morseBrokenTrajectoryRecords p r (Subtype.val : ↥(L ∩ Ioo (f r) (f p)) → ℝ)),
      MoorePath M) :=
  hX.morseLevelPath hf (subset_closure_range_subtypeVal hdense _ _)

variable (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Dense L) {p r : M}
  (w : ↥(hX.morseBrokenTrajectoryRecords p r (Subtype.val : ↥(L ∩ Ioo (f r) (f p)) → ℝ)))

/-- The point at time `t` of the Moore path of a broken trajectory is its point on the level
`f p - t`. -/
@[simp]
theorem morseRecordsEval_apply (t : ℝ≥0) :
    hX.morseRecordsEval hf hdense p r w t =
      hX.morseLevelPoint p r Subtype.val (w : ↥(L ∩ Ioo (f r) (f p)) → M) (f p - t) :=
  hX.morseLevelPath_apply hf _ w t

/-- The Moore path of a broken trajectory from `p` to `r` has length `f p - f r`. -/
@[simp]
theorem length_morseRecordsEval :
    (hX.morseRecordsEval hf hdense p r w).length = (f p - f r).toNNReal :=
  hX.length_morseLevelPath hf _ w

/-- The Moore path of a broken trajectory from `p` to `r` starts at `p`. -/
@[simp]
theorem source_morseRecordsEval : (hX.morseRecordsEval hf hdense p r w).source = p :=
  hX.source_morseLevelPath hf _ w

/-- The Moore path of a broken trajectory from `p` to `r` ends at `r`. -/
@[simp]
theorem target_morseRecordsEval : (hX.morseRecordsEval hf hdense p r w).target = r :=
  hX.target_morseLevelPath hf _ w

variable (hL : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∉ L)

/-- **Evaluation into Moore paths takes composition to concatenation**: the Moore path of the
concatenation of broken trajectories from `x` to `y` and from `y` to `z` is the concatenation of
their Moore paths. -/
theorem morseRecordsEval_morseRecordsComp (x y z : criticalPoints 𝓘(ℝ, E) f)
    (u : ↥(hX.morseBrokenTrajectoryRecords x y (Subtype.val : ↥(L ∩ Ioo (f y) (f x)) → ℝ)))
    (v : ↥(hX.morseBrokenTrajectoryRecords y z (Subtype.val : ↥(L ∩ Ioo (f z) (f y)) → ℝ))) :
    hX.morseRecordsEval hf hdense x z (hX.morseRecordsComp hL x y z (u, v)) =
      (hX.morseRecordsEval hf hdense x y u).trans (hX.morseRecordsEval hf hdense y z v)
        (by rw [target_morseRecordsEval, source_morseRecordsEval]) :=
  hX.morseLevelPath_morseBrokenTrajectoryConcat hf (hL y y.property) _ _ _ (u, v)

end Eval

end IsAdaptedPseudoGradient

namespace TwistingChainSystem

variable [Fintype (criticalPoints 𝓘(ℝ, E) f)] {R : Type*} [CommRing R]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ} {hX : IsAdaptedPseudoGradient f X}
  {hL : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∉ L}
  {Y : Type*} [TopologicalSpace Y] {y₀ : Y} {θ : C(M, Y)}

/-- **The twisting cocycle over the Moore loops of a twisting chain system on the compactified
Morse trajectory spaces.** Evaluate the broken trajectories from `x` to `y` into Moore paths from
`x` to `y`, parametrized by the values of `f`
(`TauCeti.IsAdaptedPseudoGradient.morseRecordsEval`), and map them to Moore loops at `y₀` along a
map `θ : M → Y` sending every critical point to `y₀`. The push-forwards of the chains of `S` along
these evaluations form a twisting cocycle over `C^□_*(Ω_{y₀} Y; R)`. When `S` is a representing
chain system and `θ` is the collapse `M → M / T` of an embedded tree `T` through the critical
points, or its composite with a homotopy inverse `M / T → M`, this is the Barraud–Cornea cocycle. -/
def morseTwistingCocycle (S : TwistingChainSystem ind (hX.morseRecordsComp hL) R)
    (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Dense L) (hθ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, θ x = y₀) :
    TwistingCocycle (R := R) (A := loopChainAlgebra Y y₀ R)
      (cubicalChainGrading (MooreLoopSpace Y y₀) R)
      (cubicalChainDifferential (MooreLoopSpace Y y₀) R) (criticalPoints 𝓘(ℝ, E) f) ind :=
  S.mooreTwistingCocycle
    (e := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ hX.morseRecordsEval hf hdense x y)
    (fun _ _ u ↦ hX.source_morseRecordsEval hf hdense u)
    (fun _ _ u ↦ hX.target_morseRecordsEval hf hdense u) (fun x ↦ hθ x x.property)
    (hX.morseRecordsEval_morseRecordsComp hf hdense hL)

/-- **The entries of the twisting cocycle**: the entry at `(x, y)` is the push-forward of the chain
of `S` along the evaluation sending a broken trajectory from `x` to `y` to the image under `θ` of
its Moore path, a Moore loop at `y₀`. -/
@[simp]
theorem morseTwistingCocycle_m (S : TwistingChainSystem ind (hX.morseRecordsComp hL) R)
    (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Dense L) (hθ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (S.morseTwistingCocycle hf hdense hθ).m x y = cubicalChainSumMap R
      (mooreLoopEvaluation (e := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
          hX.morseRecordsEval hf hdense x y)
        (fun _ _ u ↦ hX.source_morseRecordsEval hf hdense u)
        (fun _ _ u ↦ hX.target_morseRecordsEval hf hdense u) (fun x ↦ hθ x x.property) x y)
      (S.chain x y) :=
  S.mooreTwistingCocycle_m _ _ _ _ x y

end TwistingChainSystem

end TauCeti
