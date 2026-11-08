/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ChainSystem

/-!
# Twisting cocycles from evaluation into Moore paths

Let `P` be a finite set graded by `ind`, with spaces `M x y` and face maps
`ι x z y : M x z × M z y → M x y`, and let each `x ∈ P` sit at a point `c x` of a space `B`. For the
compactified trajectory spaces of a Morse function on `B`, with `c x` the critical points, a broken
trajectory runs along a path from `c x` to `c y`: this gives evaluation maps
`e x y : M x y → P_{c x → c y} B` into Moore paths, and since trajectories are parametrized by
length, concatenating at a breaking point is concatenation of Moore paths,

`e x y (ι x z y (u, v)) = e x z u · e z y v`.

To obtain loops, compose with a map `θ : B → X` sending every `c x` to one point `x₀`, such as the
collapse of a tree in `B` through the critical points. The images `θ ∘ e x y` are Moore loops at
`x₀`, and they are multiplicative along the faces
(`TauCeti.mooreLoopEvaluation_mul`). So every product-face chain system on the `M x y` gives a
twisting cocycle over the chains `C_*(Ω_{x₀} X)` on the Moore loop space
(`TauCeti.ProductFaceChainSystem.mooreTwistingCocycle`). This is the construction of the
Barraud–Cornea cocycle from a representing chain system: evaluate into Moore paths, then into
`C_*(Ω X)`.

## Main definitions

* `TauCeti.mooreLoopEvaluation`: the evaluation `M x y → Ω_{x₀} X`, `u ↦ θ ∘ e x y u`.
* `TauCeti.ProductFaceChainSystem.mooreTwistingCocycle`: the twisting cocycle over
  `C_*(Ω_{x₀} X)` of a product-face chain system.

## Main results

* `TauCeti.mooreLoopEvaluation_mul`: the evaluation is multiplicative along the faces.
* `TauCeti.ProductFaceChainSystem.mooreTwistingCocycle_m`: the entries of the cocycle.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
-/

public section

noncomputable section

namespace TauCeti

universe uP uM uR

variable {R : Type uR} [CommRing R] {P : Type uP} {ind : P → ℤ} {M : P → P → Type uM}
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

/-- **The evaluation into Moore loops is multiplicative along the faces**, as soon as the evaluation
into Moore paths takes the faces to concatenations. -/
theorem mooreLoopEvaluation_mul {ι : ∀ x z y, C(M x z × M z y, M x y)}
    (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
      (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))
    (x z y : P) (u : M x z) (v : M z y) :
    mooreLoopEvaluation he₀ he₁ hθ x y (ι x z y (u, v)) =
      mooreLoopEvaluation he₀ he₁ hθ x z u * mooreLoopEvaluation he₀ he₁ hθ z y v :=
  MooreLoopSpace.ext <| by simp [he]

namespace ProductFaceChainSystem

variable [Fintype P] {ι : ∀ x z y, C(M x z × M z y, M x y)}
  (he : ∀ x z y u v, e x y (ι x z y (u, v)) =
    (e x z u).trans (e z y v) ((he₁ x z u).trans (he₀ z y v).symm))

/-- **The twisting cocycle over the Moore loops of a product-face chain system** whose spaces are
evaluated into Moore paths, concatenating along the faces, and then collapsed to loops at `x₀` by
`θ`. For the trajectory spaces of a Morse function this is the Barraud–Cornea cocycle with values
in `C_*(Ω_{x₀} X)`. -/
def mooreTwistingCocycle (s : ProductFaceChainSystem R ind ι) :
    TwistingCocycle (R := R) (A := loopChainAlgebra X x₀ R)
      (cubicalChainGrading (MooreLoopSpace X x₀) R)
      (cubicalChainDifferential (MooreLoopSpace X x₀) R) P ind :=
  s.twistingCocycle (mooreLoopEvaluation he₀ he₁ hθ) (mooreLoopEvaluation_mul he₀ he₁ hθ he)

/-- The entries of the twisting cocycle over the Moore loops are the push-forwards of the chains
along the evaluations into Moore loops. -/
@[simp]
theorem mooreTwistingCocycle_m (s : ProductFaceChainSystem R ind ι) (x y : P) :
    (s.mooreTwistingCocycle he₀ he₁ hθ he).m x y =
      cubicalChainPushforward R (mooreLoopEvaluation he₀ he₁ hθ x y) (s.chain x y) :=
  s.twistingCocycle_m _ _ x y

end ProductFaceChainSystem

end TauCeti
