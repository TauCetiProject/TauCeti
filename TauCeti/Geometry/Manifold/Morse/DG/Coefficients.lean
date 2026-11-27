/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.DGLocalSystem.Transport
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex

/-!
# The DG Morse complex is functorial in its coefficients

Let `f` be a Morse function on a compact boundaryless manifold `M` with an adapted
pseudo-gradient, and `S` a twisting chain system on its trajectory spaces, evaluated into the
Moore loops of a space `Y` at `y₀`. The DG Morse complex `𝓕 ⊗ ⟨Crit f⟩`
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) is defined for every DG local system `𝓕` on
`(Y, y₀)`. This file makes it a functor of `𝓕`
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctor`): a morphism of DG local systems acts on
the coefficients of every critical point, which commutes with the twisted differential.

Two properties of DG Morse homology `H_*(M; 𝓕)` of Barraud, Damian, Humilière and Oancea follow.

* **Invariance under quasi-isomorphisms of DG local systems.** A quasi-isomorphism `𝓕 → 𝓖`
  induces a quasi-isomorphism of DG Morse complexes
  (`TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexFunctor_map`), since the Barraud–Cornea
  cocycle is a twisting cocycle on the finite set of critical points, hence semi-free
  (`TauCeti.TwistingCocycle.quasiIso_twistedCochainComplexMap`). For a map `p : E' → Y` with a
  transitive Moore lifting function `Φ`, transport `C_*(F') → C_*(F)_Φ` is a quasi-isomorphism of
  DG local systems (`TauCeti.isQuasiIso_transportLocalSystemHom`), so the DG Morse complexes with
  coefficients in the chains on the fibre of the Moore-path replacement and in the chains on the
  fibre of `p` are quasi-isomorphic
  (`TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexFunctor_map_transportLocalSystemHom`).
  So transport does not change DG Morse homology, which is what the transport step of the
  fibration theorem `H_*(Y; C_*(F')) ≅ H_*(E')` uses to pass from fibrations with a transitive
  lifting function to all Hurewicz fibrations.
* **Naturality of the independence of the chain system.** Under the Morse–Smale condition, a
  homotopy `T` of chain systems gives an isomorphism of DG Morse complexes
  (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy`). It acts on the critical points
  only, so it is natural in the coefficients: these isomorphisms form a natural isomorphism of
  functors (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctorIsoOfHomotopy`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctor`: the DG Morse complex as a functor of the
  DG local system.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctorIsoOfHomotopy`: the natural isomorphism of
  DG Morse complex functors induced by a homotopy of chain systems.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexFunctor_map`: quasi-isomorphisms of DG
  local systems induce quasi-isomorphisms of DG Morse complexes.
* `TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexFunctor_map_transportLocalSystemHom`:
  transport along a transitive lifting function induces a quasi-isomorphism of DG Morse
  complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5–7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.1.
-/

public section

noncomputable section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

universe uM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  [Fintype (criticalPoints 𝓘(ℝ, E) f)]

section Coefficients

variable {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) {R : Type*} [CommRing R]

/-! ### The DG Morse complex functor -/

section Functor

variable (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
  (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)

/-- **The DG Morse complex as a functor of the coefficients**: a DG local system `𝓕` on `(Y, y₀)`
goes to the DG Morse complex `𝓕 ⊗ ⟨Crit f⟩` of the chain system `S`, and a morphism of DG local
systems acts on the coefficient of every critical point. -/
@[expose] def dgMorseComplexFunctor :
    DGLocalSystem.{uM} Y y₀ R ⥤ CochainComplex (ModuleCat R) ℤ where
  obj 𝓕 := hX.dgMorseComplex hf hdense hθ hc S 𝓕
  map {𝓕 𝓖} φ := (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedCochainComplexMap
    𝓕.isDGRightModule 𝓖.isDGRightModule φ
  map_id _ := TwistingCocycle.twistedCochainComplexMap_id _ _
  map_comp φ ψ := TwistingCocycle.twistedCochainComplexMap_comp _ _ _ _ φ ψ

/-- The DG Morse complex functor sends a DG local system to its DG Morse complex. -/
@[simp]
theorem dgMorseComplexFunctor_obj (𝓕 : DGLocalSystem.{uM} Y y₀ R) :
    (hX.dgMorseComplexFunctor hf hdense hθ hc S).obj 𝓕 = hX.dgMorseComplex hf hdense hθ hc S 𝓕 :=
  (rfl)

/-- A morphism of DG local systems acts on the DG Morse complexes through the morphism of twisted
complexes of the Barraud–Cornea cocycle. -/
@[simp]
theorem dgMorseComplexFunctor_map {𝓕 𝓖 : DGLocalSystem.{uM} Y y₀ R} (φ : 𝓕 ⟶ 𝓖) :
    (hX.dgMorseComplexFunctor hf hdense hθ hc S).map φ =
      (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedCochainComplexMap
        𝓕.isDGRightModule 𝓖.isDGRightModule φ :=
  (rfl)

/-- **DG Morse homology is invariant under quasi-isomorphisms of DG local systems**: a
quasi-isomorphism `𝓕 → 𝓖` induces a quasi-isomorphism of DG Morse complexes. -/
theorem quasiIso_dgMorseComplexFunctor_map {𝓕 𝓖 : DGLocalSystem.{uM} Y y₀ R} {φ : 𝓕 ⟶ 𝓖}
    (hφ : DGRightModuleCat.IsQuasiIso φ) :
    QuasiIso ((hX.dgMorseComplexFunctor hf hdense hθ hc S).map φ) :=
  (hX.barraudCorneaCocycle hf hdense hθ hc S).quasiIso_twistedCochainComplexMap _ _ hφ

end Functor

/-! ### Naturality of the independence of the chain system -/

section Invariance

variable [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]
  {S S' : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The continuation isomorphisms of a homotopy of chain systems are natural in the
coefficients**: under the Morse–Smale condition, the isomorphisms
`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexIsoOfHomotopy` induced by a homotopy `T` from `S`
to `S'` form a natural isomorphism between the DG Morse complex functors of `S` and `S'`. -/
@[simps!]
def dgMorseComplexFunctorIsoOfHomotopy (hMS : hX.IsMorseSmale) (T : S.Homotopy S') :
    hX.dgMorseComplexFunctor.{uM} hf hdense hθ hc S ≅
      hX.dgMorseComplexFunctor hf hdense hθ hc S' :=
  NatIso.ofComponents (fun 𝓕 ↦ hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc hMS T 𝓕)
    fun {𝓕 𝓖} φ ↦ by
      simp only [dgMorseComplexFunctor_map, dgMorseComplexIsoOfHomotopy_hom]
      exact (ContinuationCocycle.continuationHom_twistedCochainComplexMap _ _
        (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T) φ).symm

end Invariance

end Coefficients

/-! ### Transport along a transitive lifting function -/

section Transport

universe u

variable {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) {R : Type u} [CommRing R]
  (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
  {E' : Type u} [TopologicalSpace E'] {p : C(E', Y)} {Φ : MooreLiftingFunction p}

/-- **Transport along a transitive lifting function induces a quasi-isomorphism of DG Morse
complexes**: for a map `p : E' → Y` with a transitive Moore lifting function `Φ`, the DG Morse
complex with coefficients in the chains `C_*(F')` on the fibre of the Moore-path replacement of `p`
is quasi-isomorphic, through transport, to the DG Morse complex with coefficients in the chains
`C_*(F)_Φ` on the fibre of `p`. -/
theorem quasiIso_dgMorseComplexFunctor_map_transportLocalSystemHom (hΦ : Φ.IsTransitive) :
    QuasiIso ((hX.dgMorseComplexFunctor hf hdense hθ hc S).map (transportLocalSystemHom hΦ y₀)) :=
  hX.quasiIso_dgMorseComplexFunctor_map hf hdense hθ hc S (isQuasiIso_transportLocalSystemHom hΦ y₀)

end Transport

end IsAdaptedPseudoGradient

end TauCeti
