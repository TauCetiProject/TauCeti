/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.MooreEvaluation
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.Topology.PathSpace.Moore.Track

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

A marked point `(u, τ)` is evaluated to the Moore loop that follows `θ₀ ∘ e x y u` up to the
time `τ`, then the track `t ↦ H (t, e x y u τ)` of the homotopy, then `θ₁ ∘ e x y u` after `τ`
(`TauCeti.markedLoopEvaluation`, built from `TauCeti.MoorePath.mapSplit`). Along the composition
maps it is multiplicative for the evaluation by `θ₀` on the left and by `θ₁` on the right
(`TauCeti.markedLoopEvaluation_markedLeft`, `TauCeti.markedLoopEvaluation_markedRight`). These are
exactly the laws under which a continuation chain system on the marked spaces, from a twisting
chain system `S` to itself, pushes forward to a continuation cocycle from the twisting cocycle of
`S` for `θ₀` to that for `θ₁`
(`TauCeti.ContinuationChainSystem.mooreHomotopyCocycle`). So the twisted complexes of the two
cocycles, with coefficients in any DG local system, are related by a continuation map.

No condition is imposed on `H` at the points `c x`: its tracks there are Moore loops at `x₀` of
length one, constant when `H` fixes these points.

## Main definitions

* `TauCeti.markedSpace e x y`: the points of `M x y` with a marked time on their paths.
* `TauCeti.markedLeft`, `TauCeti.markedRight`: the composition maps of the marked spaces.
* `TauCeti.markedLoopEvaluation`: the evaluation of the marked spaces into Moore loops, switching
  from `θ₀` to `θ₁` at the marked time.
* `TauCeti.ContinuationChainSystem.mooreHomotopyCocycle`: the continuation cocycle between the
  twisting cocycles over the Moore loops of the two maps.

## Main results

* `TauCeti.markedLoopEvaluation_markedLeft`, `TauCeti.markedLoopEvaluation_markedRight`: the
  evaluation of the marked spaces is multiplicative along the composition maps.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
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

/-! ### The evaluation of the marked spaces into Moore loops -/

variable {X : Type*} [TopologicalSpace X] {x₀ : X} {c : P → B}
  (he₀ : ∀ x y u, (e x y u).source = c x) (he₁ : ∀ x y u, (e x y u).target = c y)
  (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
    (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))
  {θ₀ θ₁ : C(B, X)} (hθ₀ : ∀ x, θ₀ (c x) = x₀) (hθ₁ : ∀ x, θ₁ (c x) = x₀) (H : θ₀.Homotopy θ₁)

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
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y (markedLeft hl x z y (u, v)) =
      mooreLoopEvaluation he₀ he₁ hθ₀ x z u * markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H z y v :=
  MooreLoopSpace.ext <| by
    simp [he, MoorePath.mapSplit_trans_length_add, MooreLoopSpace.toMoorePath_mul]

/-- **The evaluation of a mark on the first piece**: it is the evaluation of the marked first
piece, followed by the loop of the second piece mapped by `θ₁`. -/
theorem markedLoopEvaluation_markedRight (x z y : P) (u : markedSpace e x z) (v : M z y) :
    markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y (markedRight hl x z y (u, v)) =
      markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x z u * mooreLoopEvaluation he₀ he₁ hθ₁ z y v :=
  MooreLoopSpace.ext <| by
    simp [he, MoorePath.mapSplit_trans_of_le _ _ _ _ (mem_markedSpace.1 u.property),
      MooreLoopSpace.toMoorePath_mul]

/-! ### The continuation cocycle of a homotopy of collapse maps -/

namespace ContinuationChainSystem

variable [Fintype P] {ind : P → ℤ} {R : Type*} [CommRing R] {S : TwistingChainSystem ind ι R}

/-- **The continuation cocycle of a homotopy of collapse maps.** Let `T` be a continuation chain
system from the twisting chain system `S` to itself on the marked spaces, with the composition
maps that put the mark on one of the two pieces. Its push-forwards along the evaluation of the
marked spaces, which switches from `θ₀` to `θ₁` at the mark through the homotopy `H`, form a
continuation cocycle from the twisting cocycle of `S` over the Moore loops for `θ₀` to the one
for `θ₁`. -/
def mooreHomotopyCocycle (T : ContinuationChainSystem (markedLeft hl) (markedRight hl) S S) :
    ContinuationCocycle (S.mooreTwistingCocycle he₀ he₁ hθ₀ he)
      (S.mooreTwistingCocycle he₀ he₁ hθ₁ he) where
  ν x y := cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y) (T.chain x y)
  mem_graded x y := cubicalChainSumMap_mem _ (T.mem_graded x y)
  continuation x y := by
    simpa only [continuationCocycle_ν, TwistingChainSystem.twistingCocycle_m,
      TwistingChainSystem.mooreTwistingCocycle_m] using
      (T.continuationCocycle (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H)
        (mooreLoopEvaluation_mul he₀ he₁ hθ₀ he) (mooreLoopEvaluation_mul he₀ he₁ hθ₁ he)
        (markedLoopEvaluation_markedLeft hl he₀ he₁ he hθ₀ hθ₁ H)
        (markedLoopEvaluation_markedRight hl he₀ he₁ he hθ₀ hθ₁ H)).continuation x y

/-- The entries of the continuation cocycle of a homotopy of collapse maps are the push-forwards of
the chains along the evaluation of the marked spaces. -/
@[simp]
theorem mooreHomotopyCocycle_ν (T : ContinuationChainSystem (markedLeft hl) (markedRight hl) S S)
    (x y : P) :
    (T.mooreHomotopyCocycle hl he₀ he₁ he hθ₀ hθ₁ H).ν x y =
      cubicalChainSumMap R (markedLoopEvaluation he₀ he₁ hθ₀ hθ₁ H x y) (T.chain x y) :=
  (rfl)

end ContinuationChainSystem

end TauCeti
