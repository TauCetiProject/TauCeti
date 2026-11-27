/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.Topology.PathSpace.Moore.Track
import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Prism

/-!
# Changing the collapse map of a twisting cocycle over the Moore loops

Let `M x y` be spaces indexed by pairs of elements of `P`, with composition maps
`ι x z y : M x z × M z y → M x y`, evaluated into Moore paths `e x y : M x y → P_{c x → c y} B`
which concatenate along `ι`, as for the compactified trajectory spaces of a Morse function. A map
`θ : B → X` sending every `c x` to `x₀` turns these paths into Moore loops at `x₀`
(`TauCeti.mooreLoopEvaluation`), and a twisting chain system on the `M x y` into a twisting cocycle
over `C^□_*(Ω_{x₀} X)` (`TauCeti.TwistingChainSystem.mooreTwistingCocycle`). For the trajectory
spaces of a Morse function, with `θ` the collapse of a tree through the critical points, this is
the Barraud–Cornea cocycle. This file compares the cocycles of two such maps `θ₀` and `θ₁` joined by
a homotopy `H`, such as the collapses of two trees.

The comparison lives on the spaces of points of `M x y` with a **marked time** on their paths,
`markedSpace e x y = {(u, τ) | τ ≤ length (e x y u)}`, the analogue of the continuation trajectories
of a constant homotopy of Morse functions. A breaking of a marked point puts the mark on one of the
two pieces, which gives the composition maps
`markedLeft : M x z × markedSpace e z y → markedSpace e x y`, `(u, (v, τ)) ↦ (ι (u, v), ℓ(u) + τ)`,
and `markedRight : markedSpace e x z × M z y → markedSpace e x y`, `((u, τ), v) ↦ (ι (u, v), τ)`,
where `ℓ(u)` is the length of `e x z u` (`TauCeti.markedLeft`, `TauCeti.markedRight`). When `ι` is
associative, so are they (`TauCeti.markedLeft_assoc`, `TauCeti.markedRight_markedLeft`,
`TauCeti.markedRight_assoc`), as the boundary of a continuation chain system requires.

A twisting chain system `S` on the `M x y` has no chains for the stationary trajectories from `x`
to itself, which the continuation trajectories of a constant homotopy contain. They enter as the
point `(u, 0)` (`TauCeti.markStart`) or `(u, ℓ(u))` (`TauCeti.markEnd`) of the marked space,
obtained when a mark is broken off at the start or at the end of `u`. A **marked homotopy** of `S`
(`TauCeti.TwistingChainSystem.MarkedHomotopy`) is a family of chains `η x y` of the marked spaces,
of dimension `ind x - ind y`, with

`∂ η x y = (markEnd)_* s x y - (markStart)_* s x y + Σ_z (markedLeft)_* (s x z × η z y)
  + Σ_z (-1) ^ (ind x - ind z - 1) • (markedRight)_* (η x z × s z y)`,

the continuation equation from `S` to itself with these stationary trajectories added. Every
twisting chain system for associative composition maps has one
(`TauCeti.TwistingChainSystem.nonempty_markedHomotopy`), with no condition on the spaces `M x y`:
the chains are built by induction on `ind x - ind y`, as prisms of the contraction
`((u, τ), t) ↦ (u, t τ)` of the marked space onto the points marked at the start, along which the
mark is forgotten.

A marked point `(u, τ)` is evaluated to the Moore loop that follows `θ₀ ∘ e x y u` up to the
time `τ`, then the track `t ↦ H (t, e x y u τ)` of the homotopy, then `θ₁ ∘ e x y u` after `τ`
(`TauCeti.markedLoopEvaluation`, built from `TauCeti.MoorePath.mapSplit`). Along the composition
maps it is multiplicative for the evaluation by `θ₀` on the left and by `θ₁` on the right
(`TauCeti.markedLoopEvaluation_markedLeft`, `TauCeti.markedLoopEvaluation_markedRight`). A point
marked at the start is evaluated to the track `γ_x` of `H` at `c x` followed by its loop under
`θ₁`, and a point marked at the end to its loop under `θ₀` followed by `γ_y`
(`TauCeti.markedLoopEvaluation_markStart`, `TauCeti.markedLoopEvaluation_markEnd`). So the point
chains `[γ_x]` on the diagonal plus the push-forwards of a marked homotopy form a continuation
cocycle from the twisting cocycle of `S` for `θ₀` to that for `θ₁`
(`TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle`). The twisted complexes of the
two cocycles, with coefficients in any DG local system, are therefore related by a continuation
map whose diagonal entries are the point chains of the tracks, loops which are units of
`H₀(Ω_{x₀} X) = R[π₁(X, x₀)]`.

No condition is imposed on `H` at the points `c x`: its tracks there are Moore loops at `x₀` of
length one, constant when `H` fixes these points.

## Main definitions

* `TauCeti.markedSpace e x y`: the points of `M x y` with a marked time on their paths.
* `TauCeti.markedLeft`, `TauCeti.markedRight`: the composition maps of the marked spaces.
* `TauCeti.markStart`, `TauCeti.markEnd`: a point marked at the start or at the end of its path.
* `TauCeti.TwistingChainSystem.MarkedHomotopy`: the marked homotopies of a twisting chain system.
* `TauCeti.markedLoopEvaluation`: the evaluation of the marked spaces into Moore loops, switching
  from `θ₀` to `θ₁` at the marked time.
* `TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle`: the continuation cocycle
  between the twisting cocycles over the Moore loops of the two maps.

## Main results

* `TauCeti.TwistingChainSystem.nonempty_markedHomotopy`: every twisting chain system for
  associative composition maps has a marked homotopy.
* `TauCeti.markedLoopEvaluation_markedLeft`, `TauCeti.markedLoopEvaluation_markedRight`: the
  evaluation of the marked spaces is multiplicative along the composition maps.
* `TauCeti.markedLoopEvaluation_markStart`, `TauCeti.markedLoopEvaluation_markEnd`: the evaluation
  of the points marked at the ends.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, the cubical prism.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti

variable {P : Type*} {M : P → P → Type*} [∀ x y, TopologicalSpace (M x y)] {B : Type*}
  [TopologicalSpace B]

/-! ### The marked spaces and their composition maps -/

/-- The points `u` of `M x y` together with a **marked time** `τ` on their Moore paths `e x y u`,
`τ ≤ length (e x y u)`. -/
def markedSpace (e : ∀ x y, C(M x y, MoorePath B)) (x y : P) : Set (M x y × ℝ≥0) :=
  {p | p.2 ≤ (e x y p.1).length}

@[simp]
theorem mem_markedSpace {e : ∀ x y, C(M x y, MoorePath B)} {x y : P} {p : M x y × ℝ≥0} :
    p ∈ markedSpace e x y ↔ p.2 ≤ (e x y p.1).length :=
  Iff.rfl

variable {e : ∀ x y, C(M x y, MoorePath B)} {ι : ∀ x y z, C(M x y × M y z, M x z)}
  (hl : ∀ x z y u v, (e x y (ι x z y (u, v))).length = (e x z u).length + (e z y v).length)

/-- The **composition map marking the second piece**: a point `u` of `M x z` followed by a point
`v` of `M z y` marked at time `τ` gives `ι (u, v)`, marked at the time `ℓ(u) + τ` at which its path
reaches the mark of `v`. -/
def markedLeft (x z y : P) : C(M x z × markedSpace e z y, markedSpace e x y) where
  toFun p := ⟨(ι x z y (p.1, p.2.val.1), (e x z p.1).length + p.2.val.2), by
    simp only [mem_markedSpace, hl]
    exact add_le_add le_rfl (mem_markedSpace.1 p.2.property)⟩
  continuous_toFun := by fun_prop

/-- The **composition map marking the first piece**: a point `u` of `M x z` marked at time `τ`
followed by a point `v` of `M z y` gives `ι (u, v)`, marked at the same time `τ`. -/
def markedRight (x z y : P) : C(markedSpace e x z × M z y, markedSpace e x y) where
  toFun p := ⟨(ι x z y (p.1.val.1, p.2), p.1.val.2), by
    simp only [mem_markedSpace, hl]
    exact (mem_markedSpace.1 p.1.property).trans le_self_add⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_markedLeft (x z y : P) (u : M x z) (v : markedSpace e z y) :
    (markedLeft hl x z y (u, v) : M x y × ℝ≥0) =
      (ι x z y (u, v.val.1), (e x z u).length + v.val.2) :=
  (rfl)

@[simp]
theorem coe_markedRight (x z y : P) (u : markedSpace e x z) (v : M z y) :
    (markedRight hl x z y (u, v) : M x y × ℝ≥0) = (ι x z y (u.val.1, v), u.val.2) :=
  (rfl)

variable (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
  ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
include hι

/-- The composition map marking the second piece is associative with `ι`. -/
theorem markedLeft_assoc (x w z y : P) (a : M x w) (b : M w z) (c : markedSpace e z y) :
    markedLeft hl x z y (ι x w z (a, b), c) = markedLeft hl x w y (a, markedLeft hl w z y (b, c)) :=
  Subtype.ext <| Prod.ext (hι ..) <| by simp [hl, add_assoc]

/-- Marking the middle piece of a triple composition does not depend on the order of the
compositions. -/
theorem markedRight_markedLeft (x w z y : P) (a : M x w) (b : markedSpace e w z) (c : M z y) :
    markedRight hl x z y (markedLeft hl x w z (a, b), c) =
      markedLeft hl x w y (a, markedRight hl w z y (b, c)) :=
  Subtype.ext <| Prod.ext (hι ..) rfl

/-- The composition map marking the first piece is associative with `ι`. -/
theorem markedRight_assoc (x w z y : P) (a : markedSpace e x w) (b : M w z) (c : M z y) :
    markedRight hl x z y (markedRight hl x w z (a, b), c) =
      markedRight hl x w y (a, ι w z y (b, c)) :=
  Subtype.ext <| Prod.ext (hι ..) rfl

omit hι

/-! ### Marked homotopies of twisting chain systems -/

variable (e) in
/-- A point of `M x y` **marked at the start** of its path, at time `0`. -/
def markStart (x y : P) : C(M x y, markedSpace e x y) where
  toFun u := ⟨(u, 0), mem_markedSpace.2 bot_le⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _

variable (e) in
/-- A point of `M x y` **marked at the end** of its path, at its length. -/
def markEnd (x y : P) : C(M x y, markedSpace e x y) where
  toFun u := ⟨(u, (e x y u).length), mem_markedSpace.2 le_rfl⟩
  continuous_toFun :=
    (continuous_id.prodMk (MoorePath.continuous_length.comp (e x y).continuous)).subtype_mk _

@[simp]
theorem coe_markStart (x y : P) (u : M x y) :
    (markStart e x y u : M x y × ℝ≥0) = (u, 0) :=
  (rfl)

@[simp]
theorem coe_markEnd (x y : P) (u : M x y) :
    (markEnd e x y u : M x y × ℝ≥0) = (u, (e x y u).length) :=
  (rfl)

namespace TwistingChainSystem

variable [Fintype P] {ind : P → ℤ} {R : Type*} [CommRing R]

/-- A **marked homotopy** of a twisting chain system `S`: chains `η x y` of the marked spaces, of
cohomological degree `ind y - ind x`, satisfying

`∂ η x y = (markEnd)_* s x y - (markStart)_* s x y + Σ_z (markedLeft)_* (s x z × η z y)
  + Σ_z (-1) ^ (ind x - ind z - 1) • (markedRight)_* (η x z × s z y)`.

This is the continuation equation from `S` to itself on the marked spaces, completed on the
diagonal by a point for each `x`, the stationary trajectory: breaking a marked point at its mark
leaves the point of `M x y` marked at the end or at the start, with the stationary trajectory as
the other piece. Pushed forward to the Moore loops, the two extra terms are the products with the
tracks of a homotopy of collapse maps at the points `c x`
(`TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle`). -/
structure MarkedHomotopy (S : TwistingChainSystem ind ι R) where
  /-- The chain of the marked space of `(x, y)`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (markedSpace e x y) R
  /-- Each chain is homogeneous, of cohomological degree `ind y - ind x`. -/
  mem_graded : ∀ x y, chain x y ∈ cubicalChainGrading (markedSpace e x y) R (ind y - ind x)
  /-- The homotopy equation. -/
  homotopy : ∀ x y, cubicalChainDifferential (markedSpace e x y) R (chain x y) =
    cubicalChainSumMap R (markEnd e x y) (S.chain x y) -
        cubicalChainSumMap R (markStart e x y) (S.chain x y) +
      continuationChainSum ind ind (markedLeft hl) (markedRight hl) R S.chain S.chain chain x y

namespace MarkedHomotopy

variable {S : TwistingChainSystem ind ι R}

@[ext]
theorem ext {T₁ T₂ : S.MarkedHomotopy hl} (h : ∀ x y, T₁.chain x y = T₂.chain x y) :
    T₁ = T₂ := by
  cases T₁; cases T₂
  congr
  funext x y
  exact h x y

/-- The chain of `(x, y)` vanishes when `ind x < ind y`. -/
theorem chain_eq_zero_of_lt (T : S.MarkedHomotopy hl) {x y : P} (hxy : ind x < ind y) :
    T.chain x y = 0 :=
  eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (T.mem_graded x y)

end MarkedHomotopy

/-! ### Existence of marked homotopies -/

variable (S : TwistingChainSystem ind ι R)

omit [Fintype P] in
variable (e) in
/-- Forgetting the mark of a marked point. -/
private def forgetMark (x y : P) : C(markedSpace e x y, M x y) :=
  ContinuousMap.fst.comp (ContinuousMap.subtypeVal (markedSpace e x y))

omit [Fintype P] in
/-- The homotopy `((u, τ), t) ↦ (u, t τ)` from marking every point at the start to the identity of
the marked space; it does not move the point `u` of `M x y`. -/
private def markedSpaceContraction (x y : P) :
    ((markStart e x y).comp (forgetMark e x y)).Homotopy (ContinuousMap.id (markedSpace e x y))
    where
  toFun p := ⟨(p.2.val.1, unitInterval.toNNReal p.1 * p.2.val.2), mem_markedSpace.2 <|
    (mul_le_of_le_one_left bot_le (by
      rw [← NNReal.coe_le_coe, unitInterval.coe_toNNReal, NNReal.coe_one]
      exact p.1.property.2)).trans (mem_markedSpace.1 p.2.property)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
    exact (unitInterval.toNNReal_continuous.comp continuous_fst).mul (by fun_prop)
  map_zero_left p := Subtype.ext <| Prod.ext rfl <| by simp [forgetMark]
  map_one_left p := Subtype.ext <| Prod.ext rfl <| by simp

/-- The boundary of the right-hand side of the marked homotopy equation vanishes, once the equation
holds at the pairs of smaller index difference. -/
private theorem cubicalChainDifferential_markedHomotopySum
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    {η : ∀ x y, normalizedCubicalChainAlgebra (markedSpace e x y) R}
    (hη : ∀ x y, η x y ∈ cubicalChainGrading (markedSpace e x y) R (ind y - ind x)) {x y : P}
    (hd : ∀ x' y', ind y - ind x < ind y' - ind x' →
      cubicalChainDifferential (markedSpace e x' y') R (η x' y') =
        cubicalChainSumMap R (markEnd e x' y') (S.chain x' y') -
            cubicalChainSumMap R (markStart e x' y') (S.chain x' y') +
          continuationChainSum ind ind (markedLeft hl) (markedRight hl) R S.chain S.chain η x' y') :
    cubicalChainDifferential (markedSpace e x y) R
      (cubicalChainSumMap R (markEnd e x y) (S.chain x y) -
          cubicalChainSumMap R (markStart e x y) (S.chain x y) +
        continuationChainSum ind ind (markedLeft hl) (markedRight hl) R S.chain S.chain η x y) =
      0 := by
  -- Breaking a point marked at an end, or a point marked at the break, in the three ways the
  -- three kinds of terms do.
  have hA (z : P) : cubicalChainSumMap R (markEnd e x y)
      (cubicalChainSumPairing R (ι x z y) (S.chain x z) (S.chain z y)) =
        cubicalChainSumPairing R (markedLeft hl x z y) (S.chain x z)
          (cubicalChainSumMap R (markEnd e z y) (S.chain z y)) := by
    rw [cubicalChainSumMap_cubicalChainSumPairing_of_comp (f' := markedLeft hl x z y)
      (h := ContinuousMap.id (M x z)) (h' := markEnd e z y)
      (fun u v ↦ Subtype.ext <| Prod.ext rfl (hl ..)), cubicalChainSumMap_id, LinearMap.id_apply]
  have hB (z : P) : cubicalChainSumPairing R (markedLeft hl x z y) (S.chain x z)
      (cubicalChainSumMap R (markStart e z y) (S.chain z y)) =
        cubicalChainSumPairing R (markedRight hl x z y)
          (cubicalChainSumMap R (markEnd e x z) (S.chain x z)) (S.chain z y) := by
    have h₁ := cubicalChainSumPairing_comp_prodMap (markedLeft hl x z y) (ContinuousMap.id (M x z))
      (markStart e z y) (S.chain x z) (S.chain z y)
    have h₂ := cubicalChainSumPairing_comp_prodMap (markedRight hl x z y) (markEnd e x z)
      (ContinuousMap.id (M z y)) (S.chain x z) (S.chain z y)
    rw [cubicalChainSumMap_id, LinearMap.id_apply] at h₁ h₂
    rw [← h₁, ← h₂]
    exact congrArg (fun f ↦ cubicalChainSumPairing R f (S.chain x z) (S.chain z y))
      (ContinuousMap.ext fun ⟨u, v⟩ ↦ Subtype.ext <| by simp)
  have hC (z : P) : cubicalChainSumMap R (markStart e x y)
      (cubicalChainSumPairing R (ι x z y) (S.chain x z) (S.chain z y)) =
        cubicalChainSumPairing R (markedRight hl x z y)
          (cubicalChainSumMap R (markStart e x z) (S.chain x z)) (S.chain z y) := by
    rw [cubicalChainSumMap_cubicalChainSumPairing_of_comp (f' := markedRight hl x z y)
      (h := markStart e x z) (h' := ContinuousMap.id (M z y)) (fun u v ↦ Subtype.ext <| by simp),
      cubicalChainSumMap_id, LinearMap.id_apply]
  have hσ (z : P) : (ind z - ind x + 1).negOnePow = -(ind x - ind z).negOnePow :=
    Int.negOnePow_eq_neg_of_odd_sub ⟨ind z - ind x, by ring⟩
  have hε (z : P) : (ind x - ind z - 1).negOnePow = -(ind x - ind z).negOnePow :=
    Int.negOnePow_eq_neg_of_odd_sub ⟨-1, by ring⟩
  rw [map_add, map_sub, cubicalChainDifferential_cubicalChainSumMap,
    cubicalChainDifferential_cubicalChainSumMap, S.twisting,
    cubicalChainDifferential_continuationChainSum_of_eq_add S S
      (e := fun x y ↦ cubicalChainSumMap R (markEnd e x y) (S.chain x y) -
        cubicalChainSumMap R (markStart e x y) (S.chain x y)) hη
      (fun x y ↦ sub_mem (cubicalChainSumMap_mem _ (S.mem_graded x y))
        (cubicalChainSumMap_mem _ (S.mem_graded x y)))
      (fun w z ↦ markedLeft_assoc hl hι x w z y) (fun w z ↦ markedRight_markedLeft hl hι x w z y)
      (fun w z ↦ markedRight_assoc hl hι x w z y)
      (fun z _ _ ↦ hd z y (by omega)) (fun z _ _ ↦ hd x z (by omega))]
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, map_sub, LinearMap.sub_apply,
    smul_sub, Finset.sum_sub_distrib, hA, hB, hC, hσ, hε, Units.neg_smul, Finset.sum_neg_distrib]
  abel

/-- Forgetting the mark pushes the right-hand side of the marked homotopy equation to zero, once
it pushes the chains of smaller index difference to zero: marking at an end and then forgetting the
mark is the identity, and forgetting the mark after a composition map of the marked spaces is `ι`
after forgetting the mark of the marked piece, both by definition. -/
private theorem cubicalChainSumMap_forgetMark_markedHomotopySum
    {η : ∀ x y, normalizedCubicalChainAlgebra (markedSpace e x y) R} {x y : P}
    (hd : ∀ x' y', ind y - ind x < ind y' - ind x' →
      cubicalChainSumMap R (forgetMark e x' y') (η x' y') = 0) :
    cubicalChainSumMap R (forgetMark e x y)
      (cubicalChainSumMap R (markEnd e x y) (S.chain x y) -
          cubicalChainSumMap R (markStart e x y) (S.chain x y) +
        continuationChainSum ind ind (markedLeft hl) (markedRight hl) R S.chain S.chain η x y) =
      0 := by
  have hforget (j : C(M x y, markedSpace e x y)) (hj : (forgetMark e x y).comp j =
      ContinuousMap.id _) : cubicalChainSumMap R (forgetMark e x y)
        (cubicalChainSumMap R j (S.chain x y)) = S.chain x y := by
    rw [← LinearMap.comp_apply, ← cubicalChainSumMap_comp, hj, cubicalChainSumMap_id,
      LinearMap.id_apply]
  rw [map_add, map_sub, hforget _ rfl, hforget _ rfl, sub_self, zero_add,
    cubicalChainSumMap_continuationChainSum_of_comp (κ₂ := ι) (κ₂' := ι) (forgetMark e)
      (fun z u v ↦ rfl) (fun z u v ↦ rfl),
    continuationChainSum_congr (ν' := 0) S.mem_graded S.mem_graded
      (fun z hz ↦ hd z y (by omega)) fun z hz ↦ hd x z (by omega)]
  simp [continuationChainSum_def]

/-- **Marked homotopies exist**: every twisting chain system for associative composition maps has
a marked homotopy, with no condition on the spaces `M x y`. -/
theorem nonempty_markedHomotopy
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c))) :
    Nonempty (S.MarkedHomotopy hl) := by
  -- The chains are built by induction on the index difference, together with the condition that
  -- forgetting the mark pushes them to zero on `M x y`. The right-hand side of the homotopy
  -- equation is then a cycle (by the twisting equation and the associativity of the composition
  -- maps) which forgetting the mark pushes to zero. The marked space retracts onto the points
  -- marked at the start by `((u, τ), t) ↦ (u, t τ)`, along which the mark is forgotten at every
  -- time, so the prism of this homotopy is a chain with that boundary, again pushed to zero when
  -- the mark is forgotten.
  refine (exists_forall_mem_cubicalChainGrading_of_forall_exists
    (deg := fun x y ↦ ind y - ind x)
    (fun η x y c ↦ cubicalChainDifferential (markedSpace e x y) R c =
        cubicalChainSumMap R (markEnd e x y) (S.chain x y) -
            cubicalChainSumMap R (markStart e x y) (S.chain x y) +
          continuationChainSum ind ind (markedLeft hl) (markedRight hl) R S.chain S.chain η x y ∧
      cubicalChainSumMap R (forgetMark e x y) c = 0)
    (fun η η' x y c _ _ hηη' hc ↦ by
      rwa [← continuationChainSum_congr (ν := η) (ν' := η') S.mem_graded S.mem_graded
        (fun z hz ↦ hηη' z y (by omega)) fun z hz ↦ hηη' x z (by omega)])
    fun η x y hη hd ↦ ?_).elim fun η ⟨hη, hV⟩ ↦ ⟨⟨η, hη, fun x y ↦ (hV x y).1⟩⟩
  by_cases hxy : ind x ≤ ind y
  · -- In nonnegative degree the chain vanishes, and so does the right-hand side.
    refine ⟨0, zero_mem _, ?_, map_zero _⟩
    rw [S.chain_eq_zero_of_le hxy, continuationChainSum_eq_zero_of_le S.mem_graded S.mem_graded hη
      hxy]
    simp
  have hZ := cubicalChainSumMap_forgetMark_markedHomotopySum hl S (x := x) (y := y)
    fun x' y' h ↦ (hd x' y' h).2
  -- The prism of the contraction fills the right-hand side, and forgetting the mark kills it:
  -- the contraction does not move the point of `M x y`, by definition.
  obtain ⟨c, hc, hdc, hφc⟩ := exists_cubicalChainDifferential_eq_sub_of_homotopy
    (markedSpaceContraction x y) (φ := forgetMark e x y) (fun t p ↦ rfl)
    (add_mem (sub_mem (cubicalChainSumMap_mem _ (S.mem_graded x y))
      (cubicalChainSumMap_mem _ (S.mem_graded x y)))
      (continuationChainSum_mem S.chain S.chain η S.mem_graded S.mem_graded hη x y))
    (cubicalChainDifferential_markedHomotopySum hl S hι hη fun x' y' h ↦ (hd x' y' h).1)
  refine ⟨c, by rwa [add_sub_cancel_right] at hc, ?_, hφc⟩
  rw [hdc, cubicalChainSumMap_id, LinearMap.id_apply, cubicalChainSumMap_comp,
    LinearMap.comp_apply, hZ, map_zero, sub_zero]

end TwistingChainSystem

/-! ### The evaluation of the marked spaces into Moore loops -/

variable {X : Type*} [TopologicalSpace X] {x₀ : X} {c : P → B}
  (he₀ : ∀ x y u, (e x y u).source = c x) (he₁ : ∀ x y u, (e x y u).target = c y)
  (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
    (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))
  {θ₀ θ₁ : C(B, X)} (hθ₀ : ∀ x, θ₀ (c x) = x₀) (hθ₁ : ∀ x, θ₁ (c x) = x₀) (H : θ₀.Homotopy θ₁)

include he in
/-- When the evaluation into Moore paths takes the composition maps to concatenations, the lengths
of the paths add up along the composition maps, as the composition maps of the marked spaces
require. -/
theorem length_eq_add_of_eq_trans (x z y : P) (u : M x z) (v : M z y) :
    (e x y (ι x z y (u, v))).length = (e x z u).length + (e z y v).length := by
  rw [he, MoorePath.length_trans]

/-- **The evaluation of the marked spaces into Moore loops**: a point `u` of `M x y` marked at
time `τ` goes to the Moore loop at `x₀` that follows `θ₀ ∘ e x y u` up to time `τ`, then the
track `t ↦ H (t, e x y u τ)` of the homotopy, then `θ₁ ∘ e x y u` from time `τ` on. -/
def markedLoopEvaluation (x y : P) : C(markedSpace e x y, MooreLoopSpace X x₀) where
  toFun p := ⟨(e x y p.val.1).mapSplit H p.val.2, by simp [he₀, hθ₀], by simp [he₁, hθ₁]⟩
  continuous_toFun := MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <| by
    simp only [Function.comp_def]
    fun_prop

/-- The Moore path underlying the evaluation of a marked point. -/
@[simp]
theorem toMoorePath_markedLoopEvaluation (x y : P) (p : markedSpace e x y) :
    (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y p).toMoorePath =
      (e x y p.val.1).mapSplit H p.val.2 :=
  (rfl)

include he

/-- **The evaluation of a mark on the second piece**: it is the loop of the first piece mapped by
`θ₀`, followed by the evaluation of the marked second piece. -/
theorem markedLoopEvaluation_markedLeft (x z y : P) (u : M x z) (v : markedSpace e z y) :
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y
        (markedLeft (length_eq_add_of_eq_trans he₀ he₁ he) x z y (u, v)) =
      mooreLoopEvaluation he₀ he₁ hθ₀ x z u * markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H z y v :=
  MooreLoopSpace.ext <| by
    simp [he, MoorePath.mapSplit_trans_length_add, MooreLoopSpace.toMoorePath_mul]

/-- **The evaluation of a mark on the first piece**: it is the evaluation of the marked first
piece, followed by the loop of the second piece mapped by `θ₁`. -/
theorem markedLoopEvaluation_markedRight (x z y : P) (u : markedSpace e x z) (v : M z y) :
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y
        (markedRight (length_eq_add_of_eq_trans he₀ he₁ he) x z y (u, v)) =
      markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x z u * mooreLoopEvaluation he₀ he₁ hθ₁ z y v :=
  MooreLoopSpace.ext <| by
    simp [he, MoorePath.mapSplit_trans_of_le _ _ _ _ (mem_markedSpace.1 u.property),
      MooreLoopSpace.toMoorePath_mul]

omit he in
/-- **The evaluation of a point marked at the start** is the track of the homotopy at `c x`,
followed by the loop of the point mapped by `θ₁`. -/
theorem markedLoopEvaluation_markStart (x y : P) (u : M x y) :
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y (markStart e x y u) =
      H.mooreTrackLoop (hθ₀ x) (hθ₁ x) * mooreLoopEvaluation he₀ he₁ hθ₁ x y u :=
  MooreLoopSpace.ext <| by simp [he₀]

omit he in
/-- **The evaluation of a point marked at the end** is the loop of the point mapped by `θ₀`,
followed by the track of the homotopy at `c y`. -/
theorem markedLoopEvaluation_markEnd (x y : P) (u : M x y) :
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y (markEnd e x y u) =
      mooreLoopEvaluation he₀ he₁ hθ₀ x y u * H.mooreTrackLoop (hθ₀ y) (hθ₁ y) :=
  MooreLoopSpace.ext <| by simp [he₁]

/-! ### The continuation cocycle of a homotopy of collapse maps -/

namespace TwistingChainSystem.MarkedHomotopy

variable [Fintype P] [DecidableEq P] {ind : P → ℤ} {R : Type*} [CommRing R]
  {S : TwistingChainSystem ind ι R}

/-- **The continuation cocycle of a homotopy of collapse maps.** Let `T` be a marked homotopy of
the twisting chain system `S`. The point chains `[γ_x]` of the tracks `γ_x` of the homotopy `H` at
the points `c x` on the diagonal, plus the push-forwards of the chains of `T` along the evaluation
of the marked spaces, which switches from `θ₀` to `θ₁` at the mark through `H`, form a continuation
cocycle from the twisting cocycle of `S` over the Moore loops for `θ₀` to the one for `θ₁`. -/
def mooreHomotopyCocycle (T : S.MarkedHomotopy (length_eq_add_of_eq_trans he₀ he₁ he)) :
    ContinuationCocycle (S.mooreTwistingCocycle he₀ he₁ hθ₀ he)
      (S.mooreTwistingCocycle he₀ he₁ hθ₁ he) where
  ν x y := Matrix.diagonal (fun x ↦ cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x))) x y +
    cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y) (T.chain x y)
  mem_graded x y := by
    refine add_mem ?_ (cubicalChainSumMap_mem _ (T.mem_graded x y))
    rw [Matrix.diagonal_apply]
    split_ifs with hxy
    · subst hxy
      rw [sub_self]
      exact cubicalChainPoint_mem _
    · exact zero_mem _
  continuation x y := by
    -- The diagonal of tracks is a cycle; with the twisting cocycles it contributes the products
    -- `m₀ x y * [γ_y]` and `-[γ_x] * m₁ x y`, the push-forwards of the points marked at the end
    -- and at the start.
    set D := Matrix.diagonal fun x ↦ cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x))
    have hd : cubicalChainDifferential _ R (D x y) = 0 := by
      simp only [D, Matrix.diagonal_apply]
      split_ifs
      · exact cubicalChainDifferential_cubicalChainPoint _
      · exact map_zero _
    have hl : ∑ z, cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₀ x z) (S.chain x z) *
        D z y = cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₀ x y) (S.chain x y) *
          cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ y) (hθ₁ y)) := by
      simp [D, Matrix.diagonal_apply]
    have hr : ∑ z, (ind x - ind z - 1).negOnePow •
        (D x z * cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₁ z y) (S.chain z y)) =
          -(cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x)) *
            cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₁ x y) (S.chain x y)) := by
      simp [D, Matrix.diagonal_apply]
    have hEnd : cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y)
        (cubicalChainSumMap R (markEnd e x y) (S.chain x y)) =
          cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₀ x y) (S.chain x y) *
            cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ y) (hθ₁ y)) := by
      rw [← LinearMap.comp_apply, ← cubicalChainSumMap_comp]
      exact (cubicalChainSumMap_mul_cubicalChainPoint _
        (q := (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y).comp (markEnd e x y))
        (fun u ↦ markedLoopEvaluation_markEnd he₀ he₁ hθ₀ hθ₁ H x y u) (S.chain x y)).symm
    have hStart : cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y)
        (cubicalChainSumMap R (markStart e x y) (S.chain x y)) =
          cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x)) *
            cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ₁ x y) (S.chain x y) := by
      rw [← LinearMap.comp_apply, ← cubicalChainSumMap_comp]
      exact (cubicalChainPoint_mul_cubicalChainSumMap _
        (q := (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y).comp (markStart e x y))
        (fun u ↦ markedLoopEvaluation_markStart he₀ he₁ hθ₀ hθ₁ H x y u) (S.chain x y)).symm
    rw [map_add, hd, zero_add, cubicalChainDifferential_cubicalChainSumMap, T.homotopy, map_add,
      map_sub, hEnd, hStart, cubicalChainSumMap_continuationChainSum
        (markedLoopEvaluation_markedLeft he₀ he₁ he hθ₀ hθ₁ H x · y)
        (markedLoopEvaluation_markedRight he₀ he₁ he hθ₀ hθ₁ H x · y)]
    simp only [mooreTwistingCocycle_m, mul_add, add_mul, smul_add, Finset.sum_add_distrib, hl, hr]
    abel

/-- The entries of the continuation cocycle of a homotopy of collapse maps: the point chain of the
track at `c x` on the diagonal, plus the push-forward of the chain of the marked homotopy. -/
@[simp]
theorem mooreHomotopyCocycle_ν (T : S.MarkedHomotopy (length_eq_add_of_eq_trans he₀ he₁ he))
    (x y : P) :
    (T.mooreHomotopyCocycle he₀ he₁ he hθ₀ hθ₁ H).ν x y =
      Matrix.diagonal (fun x ↦ cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x))) x y +
        cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y) (T.chain x y) :=
  (rfl)

end TwistingChainSystem.MarkedHomotopy

end TauCeti
