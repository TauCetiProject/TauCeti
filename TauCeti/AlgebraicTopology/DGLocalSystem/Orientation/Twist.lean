/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character

/-!
# The orientation twist on the free loop space

Let `V → Q` be a real vector bundle, and let `o_V` be the sign local system of its orientation
double cover, the rank-one DG local system on which a Moore loop acts by `+1` or `-1` according
as transport along it preserves or reverses the orientations of the fibre. On the free loop space
`𝓛Q`, the exponent `w(γ)` of a free loop `γ` is `0` when `V` pulled back to the circle along `γ`
is orientable and `-1` otherwise
(`TauCeti.VectorBundleOrientationCover.freeLoopSignExponent_eq_zero_iff_exists_lift`,
`TauCeti.VectorBundleOrientationCover.freeLoopSignExponent_eq_neg_one_iff_not_exists_lift`).
The **orientation twist** of `V` at a free loop `γ₀` is the rank-one local system

`ev₀^*(o_V⁻¹) ⊗ ev₀^*(o_V^{-w(γ₀)})`

on `(𝓛Q, γ₀)` (`TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`): the sign twist
`IsCoveringMap.freeLoopSignTwist` of the orientation double cover, whose general covering-space
API (the tensor formula, its value on each kind of component and the action of a loop of free
loops) lives in `TauCeti.AlgebraicTopology.DGLocalSystem.Sign`. An oriented bundle has trivial
orientation twist (`TauCeti.VectorBundleOrientation.freeLoopOrientationTwist_eq_one`).

For the tangent bundle `V = TQ` of a manifold `Q` this is the factor
`ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀` of
Barraud–Damian–Humilière–Oancea on the free loop space of `Q`, which enters their Viterbo
isomorphism with DG coefficients for the cotangent bundle `T^*Q`; `η₀` is its tensor product with
the rank-one local system on `𝓛Q` transgressing the second Stiefel–Whitney class of `TQ`.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`: the orientation twist of a real
  vector bundle.

## Main results

* `TauCeti.VectorBundleOrientation.freeLoopOrientationTwist_eq_one`: an oriented bundle has
  trivial orientation twist.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, EMS (2015), §§5–6 (the local system on the free
  loop space in the Viterbo isomorphism).
-/

public section

noncomputable section

open TauCeti

namespace TauCeti.VectorBundleOrientationCover

open Module

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- **The orientation twist of a real vector bundle** `E → B` of rank `card ι` on the free loop
space of `B`, at the free loop `γ₀`: the sign twist of its orientation double cover. A free
loop has exponent `0` when `E` pulled back along it is orientable, that is, when transport along
it preserves the orientations of the fibre, and `-1` otherwise. For the tangent bundle of a
manifold `Q` this is the factor `ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀`
of Barraud–Damian–Humilière–Oancea. -/
def freeLoopOrientationTwist (hι : Fintype.card ι = finrank ℝ F) (γ₀ : MooreFreeLoopSpace B) :
    RankOneLocalSystem (MooreFreeLoopSpace B) γ₀ R :=
  (isCoveringMap_proj (F := F) (E := E) hι).freeLoopSignTwist R (finite_fiber hι) γ₀

variable {F E R}

/-- The orientation twist of a real vector bundle is the sign twist of its orientation
double cover. -/
theorem freeLoopOrientationTwist_def (hι : Fintype.card ι = finrank ℝ F)
    (γ₀ : MooreFreeLoopSpace B) :
    freeLoopOrientationTwist F E R hι γ₀ =
      (isCoveringMap_proj (F := F) (E := E) hι).freeLoopSignTwist R (finite_fiber hι) γ₀ :=
  (rfl)

end TauCeti.VectorBundleOrientationCover

namespace TauCeti.VectorBundleOrientation

open Module VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- **An oriented bundle has trivial orientation twist.** -/
theorem freeLoopOrientationTwist_eq_one (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (γ₀ : MooreFreeLoopSpace B) :
    freeLoopOrientationTwist F E R hι γ₀ = 1 :=
  (isCoveringMap_proj hι).freeLoopSignTwist_eq_one (finite_fiber hι) <| by
    rw [← orientationCharacter_eq_signCharacter hι]
    exact MonoidHom.ext (o.orientationCharacter_eq_one hι)

end TauCeti.VectorBundleOrientation
