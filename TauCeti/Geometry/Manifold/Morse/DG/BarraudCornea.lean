/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Order.OrderClosed

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
the critical points to one point. Such a map, even homotopic to the identity relative to `y₀`,
exists on every preconnected manifold, in every dimension
(`Set.Finite.exists_homotopicRel_id_apply_eq`, applied to the finite set of critical points,
`TauCeti.IsMorse.finite_criticalPoints`). This gives the evaluation of the compactified
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

## Trajectory spaces with boundary

Two representing chain systems are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`) when the composition maps are
associative and land in the boundary of the target space. The space `L(x, x)` of records from a
critical point to itself is the single empty record, and concatenation with it is the identity of
`L(x, y)`, which does not land in the boundary. The **trajectory space**
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySpace`) is therefore `L(x, y)` for `x ≠ y` and
empty for `x = y`, as for the moduli spaces of Morse theory. Its **boundary**
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryBoundary`) is made of the broken trajectories that
are not unbroken. Concatenation at a critical point
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat`, the restriction of `morseRecordsConcat`)
is associative (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat_assoc`) and lands in the
boundary when some level lies between the ends of the first factor
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat_mem_morseTrajectoryBoundary`). Indexed by
the critical points (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryComp`), these are the
hypotheses `hι` and `hA` of `TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. A
twisting chain system on the trajectory spaces is carried to a twisting cocycle over
`C^□_*(Ω_{y₀} Y; R)` (`TauCeti.IsAdaptedPseudoGradient.morseTwistingCocycle`) whose entries are the
push-forwards of its chains along the restriction of `morseLoopEvaluation`.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation`: the evaluation of the compactified space
  of trajectories from `x` to `y` into the Moore loops at `y₀`.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`: the twisting cocycle over
  `C^□_*(Ω_{y₀} Y; R)` of a twisting chain system on the compactified spaces of trajectories.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySpace`,
  `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryBoundary`: the trajectory spaces and their
  boundaries.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat`,
  `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryComp`: concatenation of broken trajectories on the
  trajectory spaces, and the composition maps indexed by the critical points.
* `TauCeti.IsAdaptedPseudoGradient.morseTwistingCocycle`: the twisting cocycle over
  `C^□_*(Ω_{y₀} Y; R)` of a twisting chain system on the trajectory spaces.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.toMoorePath_morseLoopEvaluation`: the loop of a recorded broken
  trajectory is its Moore path mapped by `θ`.
* `TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation_morseRecordsConcat`: the evaluation into
  loops takes concatenation of broken trajectories to the product of Moore loops.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_m`: the entries of the Barraud–Cornea
  cocycle.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryComp_assoc`,
  `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryComp_mem_morseTrajectoryBoundary`: the composition
  maps of the trajectory spaces are associative and land in the boundary.
* `TauCeti.IsAdaptedPseudoGradient.morseTwistingCocycle_m`: the entries of the twisting cocycle of a
  twisting chain system on the trajectory spaces.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
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

/-! ### The trajectory spaces with boundary -/

section Spaces

variable (hX : IsAdaptedPseudoGradient f X) (c : ι → ℝ)

/-- **The trajectory space from `x` to `y`**: empty if `x = y`, and otherwise the records of the
broken trajectories from `x` to `y` on the levels of `c` strictly between `f y` and `f x`. -/
def morseTrajectorySpace (x y : M) : Set (c ⁻¹' Ioo (f y) (f x) → M) :=
  {w | x ≠ y ∧ w ∈ hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)}

/-- **The boundary of the trajectory space from `x` to `y`**: its broken trajectories that are not
unbroken. -/
def morseTrajectoryBoundary (x y : M) : Set (hX.morseTrajectorySpace c x y) :=
  {w | (w : c ⁻¹' Ioo (f y) (f x) → M) ∉
    hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)}

variable {hX c}

/-- Membership in a trajectory space. -/
@[simp]
theorem mem_morseTrajectorySpace {x y : M} {w : c ⁻¹' Ioo (f y) (f x) → M} :
    w ∈ hX.morseTrajectorySpace c x y ↔
      x ≠ y ∧ w ∈ hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  Iff.rfl

/-- Membership in the boundary of a trajectory space. -/
@[simp]
theorem mem_morseTrajectoryBoundary {x y : M} {w : hX.morseTrajectorySpace c x y} :
    w ∈ hX.morseTrajectoryBoundary c x y ↔ (w : c ⁻¹' Ioo (f y) (f x) → M) ∉
      hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  Iff.rfl

/-- The trajectory space from a point to itself is empty. -/
@[simp]
theorem morseTrajectorySpace_self (x : M) : hX.morseTrajectorySpace c x x = ∅ :=
  eq_empty_of_forall_notMem fun _ hw ↦ hw.1 rfl

/-- The trajectory space from `x` to `y` is contained in the records of broken trajectories from `x`
to `y`. -/
theorem morseTrajectorySpace_subset (x y : M) :
    hX.morseTrajectorySpace c x y ⊆
      hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  fun _ hw ↦ hw.2

/-- Along a trajectory space, `f` decreases strictly from the source to the target. -/
theorem value_lt_of_mem_morseTrajectorySpace {x y : M} {w : c ⁻¹' Ioo (f y) (f x) → M}
    (hw : w ∈ hX.morseTrajectorySpace c x y) : f y < f x :=
  hX.value_lt_of_mem_morseBrokenTrajectoryRecords hw.1 hw.2

variable {x z y : M}

/-- **Concatenation of broken trajectories at `z`** on the trajectory spaces: the restriction of
`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`. It needs no level of `c` to be the level of
`z`, which holds when `z` is a critical point and the levels are regular values. -/
noncomputable def morseTrajectoryConcat (hz : ∀ i, c i ≠ f z) :
    C(hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y,
      hX.morseTrajectorySpace c x y) where
  toFun w := ⟨hX.morseRecordsConcat hz (inclusion (morseTrajectorySpace_subset x z) w.1,
      inclusion (morseTrajectorySpace_subset z y) w.2),
    fun h ↦ ((value_lt_of_mem_morseTrajectorySpace w.2.property).trans
      (value_lt_of_mem_morseTrajectorySpace w.1.property)).ne' (congrArg f h),
    Subtype.property _⟩
  continuous_toFun := (continuous_subtypeVal.comp <| (hX.morseRecordsConcat hz).continuous.comp
    ((continuous_inclusion _).prodMap (continuous_inclusion _))).subtype_mk _

/-- The record underlying a concatenation is the concatenation of the records. -/
@[simp]
theorem coe_morseTrajectoryConcat_apply (hz : ∀ i, c i ≠ f z)
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    (hX.morseTrajectoryConcat hz w : c ⁻¹' Ioo (f y) (f x) → M) =
      concatLevelRecords c hz w.1.val w.2.val :=
  hX.coe_morseRecordsConcat hz _

/-- **Concatenation of broken trajectories is associative.** -/
theorem morseTrajectoryConcat_assoc {s : M} (hz : ∀ i, c i ≠ f z) (hs : ∀ i, c i ≠ f s)
    (a : hX.morseTrajectorySpace c x z) (b : hX.morseTrajectorySpace c z s)
    (d : hX.morseTrajectorySpace c s y) :
    hX.morseTrajectoryConcat hs (hX.morseTrajectoryConcat hz (a, b), d) =
      hX.morseTrajectoryConcat hz (a, hX.morseTrajectoryConcat hs (b, d)) :=
  Subtype.ext <| by
    simpa only [coe_morseTrajectoryConcat_apply] using
      concatLevelRecords_assoc hz hs (value_lt_of_mem_morseTrajectorySpace b.property).le _ _ _

/-- **Concatenations lie in the boundary.** If some level of `c` lies strictly between `f z` and
`f x`, no concatenation of broken trajectories from `x` to `z` and from `z` to `y` is unbroken. -/
theorem morseTrajectoryConcat_mem_morseTrajectoryBoundary (hz : ∀ i, c i ≠ f z)
    (hlevel : ∃ i, c i ∈ Ioo (f z) (f x))
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryConcat hz w ∈ hX.morseTrajectoryBoundary c x y := by
  obtain ⟨_, hi₀⟩ := hlevel
  rw [mem_morseTrajectoryBoundary, coe_morseTrajectoryConcat_apply]
  exact hX.concatLevelRecords_notMem_morseTrajectoryRecords hz
    w.1.property.2 w.2.property.2 w.2.property.1 hi₀

end Spaces

/-! ### The composition maps of the trajectory spaces -/

section Comp

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ}
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-- **The composition maps of the trajectory spaces**, indexed by the critical points of `f`:
concatenation at the middle critical point. -/
noncomputable def morseTrajectoryComp (x y z : criticalPoints 𝓘(ℝ, E) f) :
    C(hX.morseTrajectorySpace c x y × hX.morseTrajectorySpace c y z,
      hX.morseTrajectorySpace c x z) :=
  hX.morseTrajectoryConcat fun i ↦ hc i y

/-- The record underlying a composite is the concatenation of the records. -/
@[simp]
theorem coe_morseTrajectoryComp_apply (x y z : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseTrajectorySpace c x y × hX.morseTrajectorySpace c y z) :
    (hX.morseTrajectoryComp hc x y z w : c ⁻¹' Ioo (f z) (f x) → M) =
      concatLevelRecords c (fun i ↦ hc i y) w.1.val w.2.val :=
  hX.coe_morseTrajectoryConcat_apply _ w

/-- The composition maps are associative, in the form of the hypothesis `hι` of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseTrajectoryComp_assoc (x w z y : criticalPoints 𝓘(ℝ, E) f)
    (a : hX.morseTrajectorySpace c x w) (b : hX.morseTrajectorySpace c w z)
    (d : hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryComp hc x z y (hX.morseTrajectoryComp hc x w z (a, b), d) =
      hX.morseTrajectoryComp hc x w y (a, hX.morseTrajectoryComp hc w z y (b, d)) :=
  hX.morseTrajectoryConcat_assoc _ _ a b d

/-- The composition maps take values in the boundary, in the form of the hypothesis `hA` of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseTrajectoryComp_mem_morseTrajectoryBoundary
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (x z y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryComp hc x z y w ∈ hX.morseTrajectoryBoundary c x y :=
  hX.morseTrajectoryConcat_mem_morseTrajectoryBoundary _
    (exists_mem_Ioo_of_Ioo_subset_closure_range (value_lt_of_mem_morseTrajectorySpace w.1.property)
      (hdense x z)) w

end Comp

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
  mooreLoopEvaluation_mul _ _ hθ
    (fun x z y u v ↦ hX.morseLevelPath_morseRecordsConcat hf (hdense x y) (fun i ↦ hc i z) (u, v))
    x y z u v

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
  S.mooreTwistingCocycle (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
    (e := fun x y ↦ hX.morseLevelPath hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)))
    (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..) hθ
    fun x z y u v ↦ hX.morseLevelPath_morseRecordsConcat hf (hdense x y) (fun i ↦ hc i z) (u, v)

/-- The entry of the Barraud–Cornea cocycle at `(x, y)` is the push-forward of the chain of the
compactified space of trajectories from `x` to `y` along its evaluation into Moore loops. -/
@[simp]
theorem barraudCorneaCocycle_m
    (S : TwistingChainSystem ind
      (fun x y z ↦ hX.morseRecordsConcat (p := x) (q := y) (r := z) fun i ↦ hc i y) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.barraudCorneaCocycle hf hdense hθ hc S).m x y =
      cubicalChainSumMap R (hX.morseLoopEvaluation hf hdense hθ x y) (S.chain x y) :=
  S.mooreTwistingCocycle_m _ _ hθ _ x y

/-! ### The twisting cocycle on the trajectory spaces with boundary -/

/-- **The twisting cocycle of a twisting chain system on the trajectory spaces**: the push-forwards
of the chains of `S` along the restrictions of `morseLoopEvaluation` to the trajectory spaces form a
twisting cocycle over `C^□_*(Ω_{y₀} Y; R)`. When `ind` is the Morse index, `S` is a representing
chain system and `θ : M → M` is homotopic to the identity, this is the twisting cocycle of Barraud
and Cornea, and the twisting cocycles of two representing chain systems are related through
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
noncomputable def morseTwistingCocycle (S : TwistingChainSystem ind (hX.morseTrajectoryComp hc) R) :
    TwistingCocycle (R := R) (A := loopChainAlgebra Y y₀ R)
      (cubicalChainGrading (MooreLoopSpace Y y₀) R)
      (cubicalChainDifferential (MooreLoopSpace Y y₀) R) (criticalPoints 𝓘(ℝ, E) f) ind :=
  S.mooreTwistingCocycle (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
    (e := fun x y ↦ (hX.morseLevelPath hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp
        (ContinuousMap.inclusion (morseTrajectorySpace_subset _ _)))
    (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..) hθ
    fun x z y u v ↦ hX.morseLevelPath_morseRecordsConcat hf (hdense x y) (fun i ↦ hc i z)
      (inclusion (morseTrajectorySpace_subset _ _) u, inclusion (morseTrajectorySpace_subset _ _) v)

/-- The entry at `(x, y)` of the twisting cocycle of a twisting chain system on the trajectory
spaces is the push-forward of its chain along the evaluation into Moore loops. -/
@[simp]
theorem morseTwistingCocycle_m (S : TwistingChainSystem ind (hX.morseTrajectoryComp hc) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseTwistingCocycle hf hdense hθ hc S).m x y =
      cubicalChainSumMap R ((hX.morseLoopEvaluation hf hdense hθ x y).comp
        (ContinuousMap.inclusion (morseTrajectorySpace_subset _ _))) (S.chain x y) :=
  (S.mooreTwistingCocycle_m _ _ hθ _ x y).trans <|
    congrArg (cubicalChainSumMap R · (S.chain x y)) <| ContinuousMap.ext fun _ ↦
      MooreLoopSpace.ext <| by simp

end IsAdaptedPseudoGradient

end TauCeti
