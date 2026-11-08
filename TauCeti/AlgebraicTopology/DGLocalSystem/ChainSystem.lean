/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Twisted.Map

/-!
# Twisting cocycles of product-face chain systems

Let `P` be a finite set graded by `ind : P → ℤ`, and let `M x y` be spaces indexed by pairs of
elements of `P`, with **face maps** `ι x z y : M x z × M z y → M x y`. The basic example is the
family of compactified spaces of connecting trajectories of a Morse function, where `ι x z y`
includes the broken trajectories through `z` into the boundary of `M x y`.

A **product-face chain system** (`TauCeti.ProductFaceChainSystem`) is a family of normalized
cubical chains `s x y` on `M x y`, of dimension `ind x - ind y - 1`, whose boundaries decompose
along the faces:

`∂ s x y = Σ_z (-1) ^ (ind x - ind z) ι_* (s x z × s z y)`.

A representing chain system of Barraud and Cornea is such a system in which, moreover, each
`s x y` represents the fundamental class of `M x y` relative to its boundary.

Let `G` be a topological monoid, for instance a Moore loop space, and let `q x y : M x y → G` be
**multiplicative** evaluation maps: `q x y (ι x z y (u, v)) = q x z u * q z y v`. Pushing the
chains forward gives a matrix `q_* s x y` in the DG algebra `C_*(G)` of normalized cubical chains
with the Pontryagin product. Since the push-forward commutes with boundaries and turns the face
pairings into Pontryagin products, the matrix is a twisting cocycle
(`TauCeti.ProductFaceChainSystem.twistingCocycle`). The construction is natural in `G`: composing
the evaluation maps with a continuous monoid homomorphism `φ` maps the twisting cocycle along the
DG algebra morphism induced by `φ` (`TauCeti.ProductFaceChainSystem.twistingCocycle_comp`).

The evaluations come from Moore paths. Let each `x ∈ P` sit at a point `c x` of a space `B`. For
the compactified trajectory spaces of a Morse function on `B`, with `c x` the critical points, a
broken trajectory runs along a path from `c x` to `c y`: this gives evaluation maps
`e x y : M x y → P_{c x → c y} B` into Moore paths, and since trajectories are parametrized by
length, concatenating at a breaking point is concatenation of Moore paths,

`e x y (ι x z y (u, v)) = e x z u · e z y v`.

To obtain loops, compose with a map `θ : B → X` sending every `c x` to one point `x₀`, such as the
collapse of a tree in `B` through the critical points. The images `θ ∘ e x y` are Moore loops at
`x₀`, and they are multiplicative along the faces
(`TauCeti.mooreLoopEvaluation_mul`). So every product-face chain system on the `M x y` gives a
twisting cocycle over the chains `C_*(Ω_{x₀} X)` on the Moore loop space
(`TauCeti.ProductFaceChainSystem.mooreTwistingCocycle`). Applied to a representing chain system,
this is the construction of the Barraud–Cornea cocycle: evaluate into Moore paths, then into
`C_*(Ω X)`.

## Main definitions

* `TauCeti.ProductFaceChainSystem`: chains whose boundaries decompose along product faces.
* `TauCeti.ProductFaceChainSystem.twistingCocycle`: the twisting cocycle obtained by evaluation.
* `TauCeti.mooreLoopEvaluation`: the evaluation `M x y → Ω_{x₀} X`, `u ↦ θ ∘ e x y u`.
* `TauCeti.ProductFaceChainSystem.mooreTwistingCocycle`: the twisting cocycle over
  `C_*(Ω_{x₀} X)` of a product-face chain system.

## Main results

* `TauCeti.ProductFaceChainSystem.twistingCocycle_m`: the entries of the evaluated cocycle.
* `TauCeti.ProductFaceChainSystem.twistingCocycle_comp`: naturality in the monoid.
* `TauCeti.mooreLoopEvaluation_mul`: the evaluation into Moore loops is multiplicative along the
  faces.
* `TauCeti.ProductFaceChainSystem.mooreTwistingCocycle_m`: the entries of the cocycle over the
  Moore loops.

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

universe uP uM uR

/-! ### Product-face chain systems -/

section Cocycle

variable {R : Type uR} [CommRing R] {P : Type uP} [Fintype P] {ind : P → ℤ}
  {M : P → P → Type uM} [∀ x y, TopologicalSpace (M x y)]

variable (R ind) in
/-- A **product-face chain system** for the face maps `ι x z y : M x z × M z y → M x y`: normalized
cubical chains `s x y` on `M x y`, of dimension `ind x - ind y - 1` (cohomological degree
`ind y - ind x + 1`), whose boundaries decompose along the faces,
`∂ s x y = Σ_z (-1) ^ (ind x - ind z) ι_* (s x z × s z y)`.

For the compactified trajectory spaces of a Morse function, with `ι` the inclusion of broken
trajectories, a representing chain system of Barraud and Cornea is such a system whose chains
moreover represent the fundamental classes of the trajectory spaces relative to their boundaries.
-/
@[ext]
structure ProductFaceChainSystem (ι : ∀ x z y, C(M x z × M z y, M x y)) where
  /-- The chain on `M x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (M x y) R
  /-- The chain on `M x y` has dimension `ind x - ind y - 1`. -/
  chain_mem : ∀ x y, chain x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)
  /-- The boundary of each chain is the signed sum of the products of chains along the faces. -/
  differential_chain : ∀ x y, cubicalChainDifferential (M x y) R (chain x y) =
    ∑ z, (ind x - ind z).negOnePow • cubicalChainCross R (ι x z y) (chain x z) (chain z y)

namespace ProductFaceChainSystem

variable {ι : ∀ x z y, C(M x z × M z y, M x y)}

/-- The chains of a product-face chain system vanish when `ind x ≤ ind y`: they would have negative
dimension. -/
theorem chain_eq_zero_of_le (s : ProductFaceChainSystem R ind ι) {x y : P} (hxy : ind x ≤ ind y) :
    s.chain x y = 0 := by
  rcases (mem_cubicalChainGrading_iff _ R).1 (s.chain_mem x y) with h | ⟨n, c, hn, -⟩
  · exact h
  · omega

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]

/-- **The twisting cocycle of a product-face chain system.** Evaluation maps
`q x y : M x y → G` into a topological monoid that are multiplicative along the faces,
`q x y (ι x z y (u, v)) = q x z u * q z y v`, push the chain system forward to a twisting cocycle
`q_* s x y` over the DG algebra `C_*(G)`. When `s` is a representing chain system on the
trajectory spaces of a Morse function (its chains represent the fundamental classes relative to
the boundaries) and `q` evaluates into the Moore loop space, this is the Barraud–Cornea
cocycle. -/
def twistingCocycle (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) :
    TwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R) (cubicalChainGrading G R)
      (cubicalChainDifferential G R) P ind :=
  .ofNonpos (fun x y ↦ cubicalChainPushforward R (q x y) (s.chain x y))
    (fun x y ↦ cubicalChainPushforward_mem (q x y) (s.chain_mem x y))
    (fun x y ↦ by
      rw [cubicalChainDifferential_cubicalChainPushforward, s.differential_chain, map_sum]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [map_zsmul_unit, cubicalChainPushforward_cubicalChainCross (ι x z y) (hq x z y)])
    fun _ ↦ cubicalChainGrading_eq_bot_of_pos G R

/-- The entries of the twisting cocycle of a product-face chain system are the push-forwards of
its chains. -/
@[simp]
theorem twistingCocycle_m (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) (x y : P) :
    (s.twistingCocycle q hq).m x y = cubicalChainPushforward R (q x y) (s.chain x y) := by
  rw [twistingCocycle, TwistingCocycle.ofNonpos_m]

/-- **Naturality of the twisting cocycle in the monoid.** Composing multiplicative evaluation maps
with a continuous monoid homomorphism `φ` maps the twisting cocycle along the DG algebra morphism
`C_*(φ)`. -/
theorem twistingCocycle_comp {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']
    (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) (φ : G →ₜ* G') :
    s.twistingCocycle (fun x y ↦ φ.toContinuousMap.comp (q x y))
        (fun x z y u v ↦ by simp [hq]) =
      (s.twistingCocycle q hq).map (cubicalChainDGAlgHom R φ) := by
  refine TwistingCocycle.ext fun x y ↦ ?_
  rw [twistingCocycle_m, TwistingCocycle.map_m, twistingCocycle_m, cubicalChainPushforward_comp]
  exact (cubicalChainDGAlgHom_apply_eq_cubicalChainPushforward φ _).symm

end ProductFaceChainSystem

end Cocycle

/-! ### Evaluation into Moore loops -/

section Moore

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
`θ`. When `s` is a representing chain system on the trajectory spaces of a Morse function, this is
the Barraud–Cornea cocycle with values in `C_*(Ω_{x₀} X)`. -/
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

end Moore

end TauCeti
