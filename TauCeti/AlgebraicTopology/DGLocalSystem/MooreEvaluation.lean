/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TwistingChainSystem

/-!
# Evaluating twisting chain systems into Moore loops

Let `P` be a set of indices, and let `M x y` be spaces indexed by pairs of elements of `P`, with
composition maps `ι x z y : M x z × M z y → M x y`. The basic example is the family of compactified
spaces of connecting trajectories of a Morse function on a space `B`, where `ι x z y` includes the
broken trajectories through `z` into the boundary of `M x y`.

Let each `x ∈ P` sit at a point `c x` of `B`, for instance the critical points. A broken trajectory
runs along a path from `c x` to `c y`: this gives evaluation maps `e x y : M x y → P_{c x → c y} B`
into Moore paths, and since trajectories are parametrized by length, concatenating at a breaking
point is concatenation of Moore paths,

`e x y (ι x z y (u, v)) = e x z u · e z y v`.

To obtain loops, compose with a map `θ : B → X` sending every `c x` to one point `x₀`, such as the
collapse of a tree in `B` through the critical points. The images `θ ∘ e x y` are Moore loops at
`x₀` (`TauCeti.mooreLoopEvaluation`), and they are multiplicative along the composition maps
(`TauCeti.mooreLoopEvaluation_mul`). So every twisting chain system on the `M x y` gives a twisting
cocycle over the chains `C^□_*(Ω_{x₀} X; R)` on the Moore loop space
(`TauCeti.TwistingChainSystem.mooreTwistingCocycle`). Applied to a representing chain system, with
`e` the trajectory evaluation and `θ` the collapse of a tree through the critical points, this is
the Barraud–Cornea cocycle: evaluate into Moore paths, then into `C_*(Ω X)`.

## Main definitions

* `TauCeti.mooreLoopEvaluation`: the evaluation `M x y → Ω_{x₀} X`, `u ↦ θ ∘ e x y u`.
* `TauCeti.TwistingChainSystem.mooreTwistingCocycle`: the twisting cocycle over
  `C^□_*(Ω_{x₀} X; R)` of a twisting chain system.

## Main results

* `TauCeti.mooreLoopEvaluation_mul`: the evaluation into Moore loops is multiplicative along the
  composition maps.
* `TauCeti.TwistingChainSystem.mooreTwistingCocycle_m`: the entries of the cocycle over the Moore
  loops.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

namespace TauCeti

variable {R : Type*} [CommRing R] {P : Type*} {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {x₀ : X} {c : P → B} {e : ∀ x y, C(M x y, MoorePath B)}
  (he₀ : ∀ x y u, (e x y u).source = c x) (he₁ : ∀ x y u, (e x y u).target = c y)
  {θ : C(B, X)} (hθ : ∀ x, θ (c x) = x₀)

/-- The **evaluation of `M x y` into Moore loops**: the Moore path `e x y u` from `c x` to `c y`,
mapped along `θ : B → X`, which sends every `c x` to `x₀`. -/
def mooreLoopEvaluation (x y : P) : C(M x y, MooreLoopSpace X x₀) where
  toFun u := ⟨(e x y u).map θ, by simp [he₀, hθ], by simp [he₁, hθ]⟩
  continuous_toFun := MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    (MoorePath.continuous_map θ).comp (e x y).continuous

/-- The Moore path underlying the evaluation of a point of `M x y`. -/
@[simp]
theorem toMoorePath_mooreLoopEvaluation (x y : P) (u : M x y) :
    (mooreLoopEvaluation he₀ he₁ hθ x y u).toMoorePath = (e x y u).map θ :=
  (rfl)

/-- **The evaluation into Moore loops is multiplicative along the composition maps**, as soon as
the evaluation into Moore paths takes the composition maps to concatenations. -/
theorem mooreLoopEvaluation_mul {ι : ∀ x y z, C(M x y × M y z, M x z)}
    (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
      (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))
    (x z y : P) (u : M x z) (v : M z y) :
    mooreLoopEvaluation he₀ he₁ hθ x y (ι x z y (u, v)) =
      mooreLoopEvaluation he₀ he₁ hθ x z u * mooreLoopEvaluation he₀ he₁ hθ z y v :=
  MooreLoopSpace.ext <| by simp [he]

namespace TwistingChainSystem

variable [Fintype P] {ι : ∀ x y z, C(M x y × M y z, M x z)}
  (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
    (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))

/-- **The twisting cocycle over the Moore loops of a twisting chain system** whose spaces are
evaluated into Moore paths, concatenating along the composition maps, and then collapsed to loops at
`x₀` by `θ`. When `S` is a representing chain system on the trajectory spaces of a Morse function,
`e` is the evaluation of trajectories into Moore paths, and `θ` is the collapse of a tree through
the critical points, this is the Barraud–Cornea cocycle with values in `C^□_*(Ω_{x₀} X; R)`. -/
def mooreTwistingCocycle (S : TwistingChainSystem ind ι R) :
    TwistingCocycle (R := R) (A := loopChainAlgebra X x₀ R)
      (cubicalChainGrading (MooreLoopSpace X x₀) R)
      (cubicalChainDifferential (MooreLoopSpace X x₀) R) P ind :=
  S.twistingCocycle (mooreLoopEvaluation he₀ he₁ hθ) (mooreLoopEvaluation_mul he₀ he₁ hθ he)

/-- The entries of the twisting cocycle over the Moore loops are the push-forwards of the chains
along the evaluations into Moore loops. -/
@[simp]
theorem mooreTwistingCocycle_m (S : TwistingChainSystem ind ι R) (x y : P) :
    (S.mooreTwistingCocycle he₀ he₁ hθ he).m x y =
      cubicalChainSumMap R (mooreLoopEvaluation he₀ he₁ hθ x y) (S.chain x y) :=
  S.twistingCocycle_m _ x y

end TwistingChainSystem

end TauCeti
