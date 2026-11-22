/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Order.OrderClosed

/-!
# The Barraud–Cornea cocycle of a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f`, and `c i`, for `i` in a type `ι`, levels of `f` containing no critical value. This
file assembles the compactified trajectory spaces of `f` into the input of a twisting chain system
(`TauCeti.TwistingChainSystem`), and turns every twisting chain system on them into a twisting
cocycle over the chains on the Moore loops of `M`, the Barraud–Cornea cocycle.

* **The spaces.** The trajectory space from `x` to `y`
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySpace`) is empty when `x = y`, and otherwise
  consists of the records of the broken trajectories from `x` to `y` on the levels of `c` between
  `f y` and `f x`. Under the Morse–Smale condition, for countably many levels dense between the
  critical values, these are the compactified spaces of trajectories
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords`). Their
  **boundary** (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryBoundary`) is made of the broken
  trajectories that are not unbroken. The trajectory space from a critical point to itself is empty
  rather than the single empty record, so that, as for the moduli spaces of Morse theory, the
  composition maps through `x` or `y` do not reach the interior.
* **The composition maps.** Concatenation at a critical point `z`
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat`) maps the trajectory spaces from `x` to
  `z` and from `z` to `y` to that from `x` to `y`. It is associative
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat_assoc`) and lands in the boundary
  when some level lies between `f z` and `f x`
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryConcat_mem_morseTrajectoryBoundary`).
  These are the hypotheses `hι` and `hA` under which two representing chain systems are joined by
  a homotopy (`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`).
* **The evaluation.** When the levels are dense between the critical values, a broken trajectory
  read on the levels of `f` is a Moore path from `x` to `y`
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPath`), and the path of a concatenation is the
  concatenation of the paths
  (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPath_morseTrajectoryConcat`).

Indexing these spaces by the critical points of `f`, with the composition maps
`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryComp`, a twisting chain system `S` is a family of
cubical chains of the trajectory spaces satisfying the twisting equation; a representing chain
system of Barraud and Cornea is one whose chains are fundamental chains relative to the boundary.
Choose a map `θ : M → Y` sending every critical point to one point `y₀`, such as the self-map of
`M` homotopic to the identity relative to `y₀` of `Set.Finite.exists_homotopicRel_id_apply_eq`,
which does the work of the collapse of a tree through the critical points. Evaluating the chains
into Moore paths and then along `θ` into Moore loops at `y₀` gives the twisting cocycle
`TauCeti.IsAdaptedPseudoGradient.morseTwistingCocycle` over the chains `C^□_*(Ω_{y₀} Y; R)`, through
`TauCeti.TwistingChainSystem.mooreTwistingCocycle`. Applied to a representing chain system it is
the Barraud–Cornea cocycle, which twists the Morse complex of `f` by DG local systems on `Y`.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectorySpace`, `morseTrajectoryBoundary`: the trajectory spaces and their boundaries.
* `morseTrajectoryConcat`: concatenation of broken trajectories at a critical point.
* `morseTrajectoryPath`: the Moore path of a broken trajectory.
* `morseTrajectoryComp`: the composition maps of the trajectory spaces indexed by the critical
  points.
* `morseTwistingCocycle`: the twisting cocycle over the Moore loops of a twisting chain system on
  the trajectory spaces.

## Main results

* `morseTrajectoryConcat_assoc`: concatenation is associative.
* `morseTrajectoryConcat_mem_morseTrajectoryBoundary`: concatenations lie in the boundary.
* `morseTrajectoryPath_morseTrajectoryConcat`: the Moore path of a concatenation is the
  concatenation of the Moore paths.
* `morseTwistingCocycle_m`: the entries of the cocycle are the push-forwards of the chains into
  the Moore loops.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
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

variable (hX : IsAdaptedPseudoGradient f X) (c : ι → ℝ)

/-! ### The trajectory spaces and their composition maps -/

section Spaces

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

/-- Along a trajectory space, `f` decreases strictly from the source to the target. -/
theorem value_lt_of_mem_morseTrajectorySpace {x y : M} {w : c ⁻¹' Ioo (f y) (f x) → M}
    (hw : w ∈ hX.morseTrajectorySpace c x y) : f y < f x :=
  hX.value_lt_of_mem_morseBrokenTrajectoryRecords hw.1 hw.2

variable {x z y : M}

/-- **Concatenation of broken trajectories at `z`**, as a continuous map from the trajectory
spaces from `x` to `z` and from `z` to `y` to the trajectory space from `x` to `y`. It needs no
level of `c` to be the level of `z`, which holds when `z` is a critical point and the levels are
regular values. -/
noncomputable def morseTrajectoryConcat (hz : ∀ i, c i ≠ f z) :
    C(hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y,
      hX.morseTrajectorySpace c x y) where
  toFun w := ⟨concatLevelRecords c hz w.1.val w.2.val,
    fun h ↦ ((value_lt_of_mem_morseTrajectorySpace w.2.property).trans
      (value_lt_of_mem_morseTrajectorySpace w.1.property)).ne' (congrArg f h),
    hX.concatLevelRecords_mem hz w.1.property.2 w.2.property.2⟩
  continuous_toFun := ((continuous_concatLevelRecords hz).comp
    (continuous_subtypeVal.prodMap continuous_subtypeVal)).subtype_mk _

/-- The record underlying a concatenation is the concatenation of the records. -/
@[simp]
theorem coe_morseTrajectoryConcat_apply (hz : ∀ i, c i ≠ f z)
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    (hX.morseTrajectoryConcat hz w : c ⁻¹' Ioo (f y) (f x) → M) =
      concatLevelRecords c hz w.1.val w.2.val :=
  (rfl)

/-- **Concatenation of broken trajectories is associative.** -/
theorem morseTrajectoryConcat_assoc {s : M} (hz : ∀ i, c i ≠ f z) (hs : ∀ i, c i ≠ f s)
    (a : hX.morseTrajectorySpace c x z) (b : hX.morseTrajectorySpace c z s)
    (d : hX.morseTrajectorySpace c s y) :
    hX.morseTrajectoryConcat hs (hX.morseTrajectoryConcat hz (a, b), d) =
      hX.morseTrajectoryConcat hz (a, hX.morseTrajectoryConcat hs (b, d)) :=
  Subtype.ext <|
    concatLevelRecords_assoc hz hs (value_lt_of_mem_morseTrajectorySpace b.property).le _ _ _

/-- **Concatenations lie in the boundary.** If some level of `c` lies strictly between `f z` and
`f x`, no concatenation of broken trajectories from `x` to `z` and from `z` to `y` is unbroken. -/
theorem morseTrajectoryConcat_mem_morseTrajectoryBoundary (hz : ∀ i, c i ≠ f z)
    (hlevel : ∃ i, c i ∈ Ioo (f z) (f x))
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryConcat hz w ∈ hX.morseTrajectoryBoundary c x y :=
  hlevel.elim fun _ hi₀ ↦ hX.concatLevelRecords_notMem_morseTrajectoryRecords hz
    w.1.property.2 w.2.property.2 w.2.property.1 hi₀

end Spaces

/-! ### Evaluation into Moore paths -/

section Path

variable {hX c} {x z y : M}

/-- **The Moore path of a broken trajectory**: for levels of `c` dense between `f y` and `f x`, the
Moore path of length `f x - f y` from `x` to `y` whose point at time `t` is the point of the broken
trajectory on the level `f x - t` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath`). -/
noncomputable def morseTrajectoryPath (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f y) (f x) ⊆ closure (range c)) :
    C(hX.morseTrajectorySpace c x y, MoorePath M) :=
  (hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo hdense)).comp
    ⟨fun w ↦ ⟨w.val, w.property.2⟩, continuous_subtypeVal.subtype_mk _⟩

variable (hf : IsMorse 𝓘(ℝ, E) f)

/-- The point at time `t` of the Moore path of a broken trajectory from `x` is its point on the
level `f x - t`. -/
@[simp]
theorem morseTrajectoryPath_apply (hdense : Ioo (f y) (f x) ⊆ closure (range c))
    (w : hX.morseTrajectorySpace c x y) (t : NNReal) :
    hX.morseTrajectoryPath hf hdense w t =
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w (f x - t) :=
  hX.morseLevelPath_apply hf _ ⟨w.val, w.property.2⟩ t

/-- The Moore path of a broken trajectory from `x` starts at `x`. -/
@[simp]
theorem source_morseTrajectoryPath (hdense : Ioo (f y) (f x) ⊆ closure (range c))
    (w : hX.morseTrajectorySpace c x y) : (hX.morseTrajectoryPath hf hdense w).source = x :=
  hX.source_morseLevelPath hf _ _

/-- The Moore path of a broken trajectory to `y` ends at `y`. -/
@[simp]
theorem target_morseTrajectoryPath (hdense : Ioo (f y) (f x) ⊆ closure (range c))
    (w : hX.morseTrajectorySpace c x y) : (hX.morseTrajectoryPath hf hdense w).target = y :=
  hX.target_morseLevelPath hf _ _

/-- **The Moore path of a concatenation is the concatenation of the Moore paths.** -/
theorem morseTrajectoryPath_morseTrajectoryConcat (hdense : Ioo (f y) (f x) ⊆ closure (range c))
    (hdense₁ : Ioo (f z) (f x) ⊆ closure (range c)) (hdense₂ : Ioo (f y) (f z) ⊆ closure (range c))
    (hz : ∀ i, c i ≠ f z) (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryPath hf hdense (hX.morseTrajectoryConcat hz w) =
      (hX.morseTrajectoryPath hf hdense₁ w.1).trans (hX.morseTrajectoryPath hf hdense₂ w.2)
        (by rw [target_morseTrajectoryPath, source_morseTrajectoryPath]) := by
  -- As a record of a broken trajectory, the concatenation is `morseRecordsConcat`.
  have h : (⟨(hX.morseTrajectoryConcat hz w).val, (hX.morseTrajectoryConcat hz w).property.2⟩ :
      hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) =
        hX.morseRecordsConcat hz (⟨w.1.val, w.1.property.2⟩, ⟨w.2.val, w.2.property.2⟩) :=
    Subtype.ext <| (coe_morseTrajectoryConcat_apply hz w).trans
      (hX.coe_morseRecordsConcat hz (⟨w.1.val, w.1.property.2⟩, ⟨w.2.val, w.2.property.2⟩)).symm
  have h' := hX.morseLevelPath_morseRecordsConcat hf hdense hz
    (⟨w.1.val, w.1.property.2⟩, ⟨w.2.val, w.2.property.2⟩)
  rw [← h] at h'
  -- `morseTrajectoryPath` is by definition `morseLevelPath` of the underlying record.
  exact h'

end Path

/-! ### The twisting cocycle -/

section Cocycle

variable {c} (hc : ∀ i, ∀ z ∈ criticalPoints 𝓘(ℝ, E) f, c i ≠ f z)

/-- **The composition maps of the trajectory spaces**, indexed by the critical points of `f`:
concatenation at the middle critical point. -/
noncomputable def morseTrajectoryComp (x y z : criticalPoints 𝓘(ℝ, E) f) :
    C(hX.morseTrajectorySpace c x y × hX.morseTrajectorySpace c y z,
      hX.morseTrajectorySpace c x z) :=
  hX.morseTrajectoryConcat fun i ↦ hc i y y.property

/-- The record underlying a composite is the concatenation of the records. -/
@[simp]
theorem coe_morseTrajectoryComp_apply (x y z : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseTrajectorySpace c x y × hX.morseTrajectorySpace c y z) :
    (hX.morseTrajectoryComp hc x y z w : c ⁻¹' Ioo (f z) (f x) → M) =
      concatLevelRecords c (fun i ↦ hc i y y.property) w.1.val w.2.val :=
  (rfl)

/-- The composition maps are associative, in the form of the hypothesis of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseTrajectoryComp_assoc (x w z y : criticalPoints 𝓘(ℝ, E) f)
    (a : hX.morseTrajectorySpace c x w) (b : hX.morseTrajectorySpace c w z)
    (d : hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryComp hc x z y (hX.morseTrajectoryComp hc x w z (a, b), d) =
      hX.morseTrajectoryComp hc x w y (a, hX.morseTrajectoryComp hc w z y (b, d)) :=
  hX.morseTrajectoryConcat_assoc _ _ a b d

/-- The composition maps take values in the boundary, in the form of the hypothesis of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseTrajectoryComp_mem_morseTrajectoryBoundary
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (x z y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseTrajectorySpace c x z × hX.morseTrajectorySpace c z y) :
    hX.morseTrajectoryComp hc x z y w ∈ hX.morseTrajectoryBoundary c x y :=
  hX.morseTrajectoryConcat_mem_morseTrajectoryBoundary _
    (exists_mem_Ioo_of_Ioo_subset_closure_range (value_lt_of_mem_morseTrajectorySpace w.1.property)
      (hdense x z)) w

variable [Fintype (criticalPoints 𝓘(ℝ, E) f)] {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}
  {R : Type*} [CommRing R] (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type*} [TopologicalSpace Y] {y₀ : Y} {θ : C(M, Y)}
  (hθ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, θ x = y₀)

/-- **The twisting cocycle of a twisting chain system on the trajectory spaces of a Morse
function**: the chains `s x y` of the trajectory spaces, evaluated into Moore paths from `x` to `y`
by reading broken trajectories on the levels of `f`, then into Moore loops at `y₀` along a map
`θ : M → Y` sending every critical point to `y₀`, form a twisting cocycle over the chains
`C^□_*(Ω_{y₀} Y; R)` on the Moore loops. When `S` is a representing chain system, `ind` the Morse
index and `θ` homotopic to the identity, this is the Barraud–Cornea cocycle. -/
noncomputable def morseTwistingCocycle (S : TwistingChainSystem ind (hX.morseTrajectoryComp hc) R) :
    TwistingCocycle (R := R) (A := loopChainAlgebra Y y₀ R)
      (cubicalChainGrading (MooreLoopSpace Y y₀) R)
      (cubicalChainDifferential (MooreLoopSpace Y y₀) R) (criticalPoints 𝓘(ℝ, E) f) ind :=
  S.mooreTwistingCocycle (c := Subtype.val)
    (e := fun x y ↦ hX.morseTrajectoryPath hf (hdense x y))
    (fun _ _ ↦ source_morseTrajectoryPath hf _) (fun _ _ ↦ target_morseTrajectoryPath hf _)
    (fun x ↦ hθ x x.property)
    fun _ _ _ u v ↦ morseTrajectoryPath_morseTrajectoryConcat hf _ _ _ _ (u, v)

/-- The entries of the twisting cocycle of a twisting chain system on the trajectory spaces are
the push-forwards of its chains along the evaluations into Moore loops. -/
@[simp]
theorem morseTwistingCocycle_m (S : TwistingChainSystem ind (hX.morseTrajectoryComp hc) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseTwistingCocycle hc hf hdense hθ S).m x y =
      cubicalChainSumMap R
        (mooreLoopEvaluation (c := Subtype.val)
          (e := fun x y ↦ hX.morseTrajectoryPath hf (hdense x y))
          (fun _ _ ↦ source_morseTrajectoryPath hf _) (fun _ _ ↦ target_morseTrajectoryPath hf _)
          (fun x ↦ hθ x x.property) x y)
        (S.chain x y) :=
  S.mooreTwistingCocycle_m _ _ _ _ x y

end Cocycle

end IsAdaptedPseudoGradient

end TauCeti
