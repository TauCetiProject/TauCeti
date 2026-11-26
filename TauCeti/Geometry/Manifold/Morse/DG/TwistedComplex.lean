/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Invertible
public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ChainSystemHomotopy
public import TauCeti.Geometry.Manifold.Morse.DG.BarraudCornea

/-!
# The DG Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and let `S` be a twisting chain system on the spaces of broken trajectories
between the critical points of `f`, graded by the Morse index. Evaluating its chains into the Moore
loops of a space `Y` at `y₀`, through a map `θ : M → Y` sending every critical point to `y₀`, gives
the Barraud–Cornea cocycle (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) over the chain
algebra `C^□_*(Ω_{y₀} Y; R)`. For a DG local system `𝓕` on `(Y, y₀)`, a right DG module over that
algebra, the **DG Morse complex** `𝓕 ⊗ ⟨Crit f⟩` is the twisted complex of this cocycle
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`), with differential
`D(α ⊗ x) = dα ⊗ x + (-1)^{|α|} Σ_y α · m(x, y) ⊗ y`. When `S` is a representing chain system
of the fundamental classes rel boundary and `θ` is the collapse of a tree through the critical
points, a map `M → M` homotopic to the identity, this is the complex whose cohomology, read in the
homological grading `C_n = C^{-n}`, is the Morse homology `H_*(M; 𝓕)` with DG coefficients of
Barraud, Damian, Humilière and Oancea.

Homotopic chain systems give isomorphic DG Morse complexes, by an isomorphism specified by the
homotopy. A homotopy `T` from `S` to `S'` (`TauCeti.TwistingChainSystem.Homotopy`) pushes forward
to the continuation cocycle `1 + q_* h` between the two Barraud–Cornea cocycles
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaContinuationCocycle`). Under the Morse–Smale
condition the trajectory spaces between distinct critical points of equal index are empty
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_empty_of_le`), so
the chains of `T` vanish there, the continuation cocycle is unitriangular for the order by index,
and its continuation map is an isomorphism of DG Morse complexes
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy`); for the zero homotopy it is the
identity (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy_refl`). Two representing
chain systems of the same relative classes are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`) as soon as the trajectory spaces
satisfy that theorem's injectivity hypothesis on relative homology, which holds for compact
manifolds with corners of the right dimension.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`: the DG Morse complex of a twisting chain
  system on the trajectory spaces, with coefficients in a DG local system.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaContinuationCocycle`: the continuation cocycle
  between the Barraud–Cornea cocycles of two homotopic chain systems.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy`: the continuation isomorphism of
  DG Morse complexes induced by a homotopy of chain systems.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.isUnit_barraudCorneaContinuationCocycle`: under the
  Morse–Smale condition, the continuation cocycle of a homotopy is invertible.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy_refl`: the continuation isomorphism
  of the zero homotopy is the identity.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.1.
-/

public section

noncomputable section

open CategoryTheory Set
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
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

variable {R : Type*} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]

/-! ### The DG Morse complex -/

section Complex

variable {S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
  (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The DG Morse complex** `𝓕 ⊗ ⟨Crit f⟩` of a twisting chain system `S` on the trajectory spaces
of `f`, graded by the Morse index, with coefficients in a DG local system `𝓕` on `(Y, y₀)`: the
twisted complex of the Barraud–Cornea cocycle of `S`. Its body is exposed so that the
continuation maps of twisted complexes are morphisms of DG Morse complexes. -/
@[expose] def dgMorseComplex (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
      (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝓕 : DGLocalSystem Y y₀ R) :=
  (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedCochainComplex 𝓕.differential
    𝓕.isDGRightModule

/-- The DG Morse complex is the twisted complex of the Barraud–Cornea cocycle. -/
theorem dgMorseComplex_def (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplex hf hdense hθ hc S 𝓕 =
      (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedCochainComplex 𝓕.differential
        𝓕.isDGRightModule :=
  (rfl)

end Complex

variable [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]

/-! ### The continuation cocycle of a homotopy of chain systems -/

section Continuation

variable {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}
  {S S' : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The continuation cocycle of a homotopy of chain systems** between the Barraud–Cornea
cocycles of `S` and `S'`: the matrix `1 + q_* h` of push-forwards of the chains `h` of a homotopy
from `S` to `S'` along the evaluation `q` of the trajectory spaces into Moore loops. -/
def barraudCorneaContinuationCocycle (T : S.Homotopy S') :
    ContinuationCocycle (hX.barraudCorneaCocycle hf hdense hθ hc S)
      (hX.barraudCorneaCocycle hf hdense hθ hc S') :=
  let ν := T.continuationCocycle _
    (hX.morseLoopEvaluation_comp_inclusion_morseBrokenTrajectorySpaceComp hf hdense hθ hc)
  { ν := ν.ν
    mem_graded := ν.mem_graded
    continuation := fun x y ↦ by
      simpa only [barraudCorneaCocycle_m, TwistingChainSystem.twistingCocycle_m] using
        ν.continuation x y }

/-- The entries of the continuation cocycle of a homotopy `T` are `1 + q_* h`: the Kronecker symbol
plus the push-forward of the chain of `T` along the evaluation into Moore loops. -/
@[simp]
theorem barraudCorneaContinuationCocycle_ν (T : S.Homotopy S') (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).ν x y =
      (1 : Matrix _ _ (loopChainAlgebra Y y₀ R)) x y +
        cubicalChainSumMap R ((hX.morseLoopEvaluation hf hdense hθ x y).comp
          (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _))) (T.chain x y) :=
  TwistingChainSystem.Homotopy.continuationCocycle_ν ..

/-- The continuation cocycle of the zero homotopy is the Kronecker cocycle. -/
@[simp]
theorem barraudCorneaContinuationCocycle_refl :
    hX.barraudCorneaContinuationCocycle hf hdense hθ hc (TwistingChainSystem.Homotopy.refl S) =
      .refl (loopChain_isDGAlgebra Y y₀ R).map_one_eq_zero _ := by
  ext x y
  simp

end Continuation

/-! ### Independence of the chain system -/

section Invariance

variable {S S' : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
  (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The continuation cocycle of a homotopy is invertible** under the Morse–Smale condition, for
chain systems graded by the Morse index: the trajectory spaces between critical points of equal
index are empty, so the chains of the homotopy vanish there and the cocycle is unitriangular
(`TauCeti.TwistingChainSystem.Homotopy.isUnit_continuationCocycle`). -/
theorem isUnit_barraudCorneaContinuationCocycle (hMS : hX.IsMorseSmale) (T : S.Homotopy S') :
    IsUnit (Matrix.of (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).ν) :=
  T.isUnit_continuationCocycle
    (hX.morseLoopEvaluation_comp_inclusion_morseBrokenTrajectorySpaceComp hf hdense hθ hc)
    fun x y heq ↦ by
      have : IsEmpty (hX.morseBrokenTrajectorySpace c x y) := by
        rw [hMS.morseBrokenTrajectorySpace_eq_empty_of_le hf (by exact_mod_cast heq.le)]
        infer_instance
      exact Subsingleton.elim _ _

/-- **The continuation isomorphism of DG Morse complexes** induced by a homotopy `T` from the chain
system `S` to `S'`, under the Morse–Smale condition: the continuation map of
`barraudCorneaContinuationCocycle T`, with inverse the continuation map of its inverse matrix. So
homotopic chain systems give isomorphic DG Morse complexes, by an isomorphism specified by the
homotopy. -/
def dgMorseComplexIsoOfHomotopy (hMS : hX.IsMorseSmale) (T : S.Homotopy S')
    (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplex hf hdense hθ hc S 𝓕 ≅ hX.dgMorseComplex hf hdense hθ hc S' 𝓕 :=
  (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).continuationIsoOfIsUnit
    (hX.isUnit_barraudCorneaContinuationCocycle hf hdense hθ hc hMS T) 𝓕.isDGRightModule

/-- The continuation isomorphism of a homotopy is the continuation map of its continuation
cocycle. -/
@[simp]
theorem dgMorseComplexIsoOfHomotopy_hom (hMS : hX.IsMorseSmale) (T : S.Homotopy S')
    (𝓕 : DGLocalSystem Y y₀ R) :
    (hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc hMS T 𝓕).hom =
      (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).continuationHom
        𝓕.isDGRightModule :=
  ContinuationCocycle.continuationIsoOfIsUnit_hom ..

/-- The inverse of the continuation isomorphism of a homotopy is the continuation map of the
inverse matrix of its continuation cocycle. -/
@[simp]
theorem dgMorseComplexIsoOfHomotopy_inv (hMS : hX.IsMorseSmale) (T : S.Homotopy S')
    (𝓕 : DGLocalSystem Y y₀ R) :
    (hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc hMS T 𝓕).inv =
      ContinuationCocycle.continuationHom
        ((hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).inverse
          (loopChain_isDGAlgebra Y y₀ R)
          ↑(hX.isUnit_barraudCorneaContinuationCocycle hf hdense hθ hc hMS T).unit⁻¹
          (hX.isUnit_barraudCorneaContinuationCocycle hf hdense hθ hc hMS T).mul_val_inv
          (hX.isUnit_barraudCorneaContinuationCocycle hf hdense hθ hc hMS T).val_inv_mul)
        𝓕.isDGRightModule :=
  ContinuationCocycle.continuationIsoOfIsUnit_inv ..

/-- The continuation isomorphism of the zero homotopy is the identity. -/
@[simp]
theorem dgMorseComplexIsoOfHomotopy_refl (hMS : hX.IsMorseSmale) (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc hMS (TwistingChainSystem.Homotopy.refl S) 𝓕 =
      Iso.refl _ := by
  ext : 1
  rw [dgMorseComplexIsoOfHomotopy_hom, barraudCorneaContinuationCocycle_refl,
    ContinuationCocycle.continuationHom_refl, Iso.refl_hom]
  -- `dgMorseComplex` is by definition the twisted complex, so the two identities agree.
  rfl

end Invariance

end IsAdaptedPseudoGradient

end TauCeti
