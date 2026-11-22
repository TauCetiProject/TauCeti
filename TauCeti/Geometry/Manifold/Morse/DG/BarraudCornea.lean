/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath

/-!
# The Barraud–Cornea cocycle of a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`. Index the critical points of `f` by `P = criticalPoints 𝓘(ℝ, E) f`, and record
the broken trajectories from `x` to `y` by their points on the levels of a family `c` between `f y`
and `f x` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`). Under the Morse–Smale
condition these records form the compactified space `L(x, y)` of trajectories from `x` to `y`.
When the levels of `c` avoid the critical values, concatenation of broken trajectories at a
critical point `y` (`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`) gives the composition maps
`L(x, y) × L(y, z) → L(x, z)` of a twisting chain system on these spaces.

A broken trajectory from `x` to `y`, parametrized by the values of `f`, is a Moore path from `x` to
`y` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath`). To obtain loops, map it by a map
`θ : M → Y` which sends every critical point to one point `y₀`. In the construction of Barraud and
Cornea, `Y = M` and `θ` is the composite of the collapse of an embedded tree through the critical
points and a homotopy inverse of that collapse, a map homotopic to the identity which sends all
the critical points to one point. Such a map exists on every path-connected manifold, in every
dimension (`Set.Finite.exists_homotopic_id_forall_apply_eq`, applied to the finite set of critical
points, `TauCeti.IsMorse.finite_criticalPoints`). This gives the evaluation of the compactified
spaces of trajectories into the Moore loops at `y₀`
(`TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation`), multiplicative along the concatenation of
broken trajectories (`TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation_morseRecordsConcat`).

Every twisting chain system on the compactified spaces of trajectories, in particular a representing
chain system of fundamental chains relative to the boundary, is therefore carried to a twisting
cocycle with values in the chains `C^□_*(Ω_{y₀} Y; R)` on the Moore loop space
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`): this is the Barraud–Cornea cocycle, whose
entry at `(x, y)` is the push-forward of the chain of `L(x, y)` along the evaluation into loops
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_m`). Barraud, Damian, Humilière and Oancea
define the Morse complex of `f` with coefficients in a DG local system on `Y` as the twisted complex
of this cocycle.

The levels `c` only need to avoid the critical values and to be dense between any two of them. Since
a Morse function on a compact manifold has finitely many critical values, the inclusion of the set
of regular values into `ℝ` is such a family.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation`: the evaluation of the compactified space
  of trajectories from `x` to `y` into the Moore loops at `y₀`.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`: the twisting cocycle over
  `C^□_*(Ω_{y₀} Y; R)` of a twisting chain system on the compactified spaces of trajectories.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.toMoorePath_morseLoopEvaluation`: the loop of a recorded broken
  trajectory is its Moore path mapped by `θ`.
* `TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation_morseRecordsConcat`: the evaluation into
  loops takes concatenation of broken trajectories to the product of Moore loops.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_m`: the entries of the Barraud–Cornea
  cocycle.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and §5.2.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)

/-! ### The evaluation into Moore loops -/

/-- **The evaluation of the compactified spaces of trajectories into Moore loops.** A broken
trajectory from the critical point `x` to the critical point `y`, recorded on the levels of `c`,
runs along a Moore path from `x` to `y`, parametrized by the values of `f`. Mapped by `θ`, which
sends every critical point to `y₀`, it is a Moore loop at `y₀`. -/
noncomputable def morseLoopEvaluation (x y : criticalPoints 𝓘(ℝ, E) f) :
    C(hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c),
      MooreLoopSpace Y y₀) :=
  mooreLoopEvaluation (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
    (e := fun x y ↦ hX.morseLevelPath hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)))
    (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..) hθ x y

/-- The Moore loop of a recorded broken trajectory is its Moore path, parametrized by the values of
`f`, mapped by `θ`. -/
@[simp]
theorem toMoorePath_morseLoopEvaluation (x y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) :
    (hX.morseLoopEvaluation hf hdense hθ x y w).toMoorePath =
      (hX.morseLevelPath hf
        (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)) w).map θ :=
  toMoorePath_mooreLoopEvaluation ..

/-- **The evaluation into Moore loops is multiplicative along the concatenation of broken
trajectories**, for levels avoiding the critical values: the loop of the concatenation at `y` of a
broken trajectory from `x` to `y` and one from `y` to `z` is the product of their loops. -/
theorem morseLoopEvaluation_morseRecordsConcat
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) (x y z : criticalPoints 𝓘(ℝ, E) f)
    (u : hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c))
    (v : hX.morseBrokenTrajectoryRecords y z ((c ⁻¹' Ioo (f z) (f y)).domRestrict c)) :
    hX.morseLoopEvaluation hf hdense hθ x z (hX.morseRecordsConcat (fun i ↦ hc i y) (u, v)) =
      hX.morseLoopEvaluation hf hdense hθ x y u * hX.morseLoopEvaluation hf hdense hθ y z v :=
  MooreLoopSpace.ext <| by
    simp [hX.morseLevelPath_morseRecordsConcat hf (hdense x z) (fun i ↦ hc i y) (u, v)]

/-! ### The Barraud–Cornea cocycle -/

variable {R : Type*} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-- **The Barraud–Cornea cocycle** of a twisting chain system `S` on the compactified spaces of
trajectories between the critical points of `f`, graded by `ind`, with composition maps the
concatenation of broken trajectories: the push-forwards of its chains along the evaluation into
the Moore loops at `y₀` form a twisting cocycle over `C^□_*(Ω_{y₀} Y; R)`. When `ind` is the Morse
index, `S` is a representing chain system and `θ : M → M` is homotopic to the identity, this is the
twisting cocycle of Barraud and Cornea. -/
noncomputable def barraudCorneaCocycle
    (S : TwistingChainSystem ind
      (fun x y z ↦ hX.morseRecordsConcat (p := x) (q := y) (r := z) fun i ↦ hc i y) R) :
    TwistingCocycle (R := R) (A := loopChainAlgebra Y y₀ R)
      (cubicalChainGrading (MooreLoopSpace Y y₀) R)
      (cubicalChainDifferential (MooreLoopSpace Y y₀) R) (criticalPoints 𝓘(ℝ, E) f) ind :=
  S.twistingCocycle (hX.morseLoopEvaluation hf hdense hθ)
    (fun x y z u v ↦ hX.morseLoopEvaluation_morseRecordsConcat hf hdense hθ hc x y z u v)

/-- The entry of the Barraud–Cornea cocycle at `(x, y)` is the push-forward of the chain of the
compactified space of trajectories from `x` to `y` along its evaluation into Moore loops. -/
@[simp]
theorem barraudCorneaCocycle_m
    (S : TwistingChainSystem ind
      (fun x y z ↦ hX.morseRecordsConcat (p := x) (q := y) (r := z) fun i ↦ hc i y) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.barraudCorneaCocycle hf hdense hθ hc S).m x y =
      cubicalChainSumMap R (hX.morseLoopEvaluation hf hdense hθ x y) (S.chain x y) :=
  S.twistingCocycle_m _ x y

end IsAdaptedPseudoGradient

end TauCeti
