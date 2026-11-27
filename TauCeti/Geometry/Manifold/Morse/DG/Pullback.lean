/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Map
public import TauCeti.AlgebraicTopology.DGLocalSystem.BaseChange
public import TauCeti.Geometry.Manifold.Morse.DG.Coefficients

/-!
# The DG Morse complex with pulled-back coefficients

Let `f` be a Morse function on a compact boundaryless manifold `M` with an adapted
pseudo-gradient, and `S` a twisting chain system on its trajectory spaces. The Barraud–Cornea
cocycle of `S` (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) evaluates the broken
trajectories into the Moore loops of a space `Y` at `y₀`, through a map `θ : M → Y` sending every
critical point to `y₀`, and the DG Morse complex `𝓕 ⊗ ⟨Crit f⟩`
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) is defined for DG local systems `𝓕` on
`(Y, y₀)`. This file shows that both are natural in the target `Y`.

For a based map `g : (Y, y₀) → (Y', y₁)`, the composite `g ∘ θ` sends every critical point to
`y₁`, and:

* the Barraud–Cornea cocycle for `g ∘ θ` is the image of the one for `θ` under the morphism
  `C_*(Ωg) : C_*(Ω_{y₀} Y) → C_*(Ω_{y₁} Y')` of chain algebras
  (`TauCeti.IsAdaptedPseudoGradient.map_loopChainMap_barraudCorneaCocycle`), and likewise for the
  continuation cocycles of homotopies of chain systems;
* hence, for a DG local system `𝓖` on `(Y', y₁)`, the DG Morse complex for `θ` with coefficients
  in the pullback `g^* 𝓖` (restriction of scalars along `C_*(Ωg)`) is isomorphic to the DG Morse
  complex for `g ∘ θ` with coefficients in `𝓖`, through the identity of the underlying functions
  (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexPullbackIso`). These isomorphisms are natural in
  `𝓖` (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctorPullbackIso`) and commute with the
  continuation isomorphisms of homotopies of chain systems
  (`dgMorseComplexPullbackIso_hom_comp_dgMorseComplexIsoOfHomotopy_hom`).

So the DG Morse complex with pulled-back coefficients `g^* 𝓖` is the twisted complex of `𝓖`
itself with the pushed-forward cocycle. This is how Barraud, Damian, Humilière and Oancea read
the source of a direct map `g_* : H_*(M; g^* 𝓖) → H_*(Y'; 𝓖)` for a map `g : M → Y'` of
manifolds: once both sides are twisted complexes of the same DG local system `𝓖`, the direct map
is a continuation map between their cocycles. That continuation map, which counts trajectories of
a pair of Morse functions, is not constructed here.

For fibrations, pulling back the fibration and pulling back its DG local system agree up to
quasi-isomorphism (`TauCeti.isQuasiIso_fibrationLocalSystemSquareMap`). Combined with the above,
for a Hurewicz fibration `p' : E' → Y'`, the DG Morse complex for `θ` with coefficients in the
chains on the fibre of the Moore-path replacement of the base change `Y ×_{Y'} E' → Y` is
quasi-isomorphic to the DG Morse complex for `g ∘ θ` with coefficients in the chains on the fibre
of the Moore-path replacement of `p'`
(`quasiIso_dgMorseComplexFunctor_map_fibrationLocalSystemSquareMap_pullbackSnd_comp`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexPullbackIso`: the isomorphism between the DG
  Morse complex for `θ` with pulled-back coefficients and the DG Morse complex for `g ∘ θ`.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexFunctorPullbackIso`: its naturality in the
  coefficients, as an isomorphism of functors.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `map_loopChainMap_barraudCorneaCocycle`: the Barraud–Cornea cocycle is natural in the target of
  the evaluation.
* `twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f`: `dgMorseComplexPullbackIso` is
  the identity of the underlying functions on the critical points.
* `dgMorseComplexPullbackIso_hom_comp_dgMorseComplexIsoOfHomotopy_hom`: the isomorphisms commute
  with the continuation isomorphisms of homotopies of chain systems.
* `quasiIso_dgMorseComplexFunctor_map_fibrationLocalSystemSquareMap_comp`: a map of Hurewicz
  fibrations over `g` that is a homotopy equivalence on the fibres induces a quasi-isomorphism of
  DG Morse complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 7 and 9.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.1.
-/

public section

noncomputable section

open CategoryTheory Set
open scoped ContDiff ContinuousMap Manifold

namespace TauCeti

universe uM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))

section Target

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y'] {θ : C(M, Y)} {y₀ : Y}
  {y₁ : Y'} (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (g : C(Y, Y')) (hg : g y₀ = y₁)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
include hθ hg in
/-- If `θ` sends every critical point to `y₀` and `g` sends `y₀` to `y₁`, then `g ∘ θ` sends every
critical point to `y₁`. -/
theorem _root_.TauCeti.comp_apply_criticalPoints_eq (x : criticalPoints 𝓘(ℝ, E) f) :
    g.comp θ x = y₁ := by
  rw [ContinuousMap.comp_apply, hθ, hg]

/-- **The evaluation into Moore loops is natural in the target**: evaluating the broken
trajectories through `g ∘ θ` is evaluating them through `θ` and then applying `Ωg`. -/
theorem morseLoopEvaluation_comp (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseLoopEvaluation hf hdense (θ := g.comp θ)
        (comp_apply_criticalPoints_eq hθ g hg) x y =
      (MooreLoopSpace.map g hg).toContinuousMap.comp (hX.morseLoopEvaluation hf hdense hθ x y) :=
  ContinuousMap.ext fun _ ↦ MooreLoopSpace.ext <| by simp [MoorePath.map_map]

variable (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) {R : Type*} [CommRing R]
  [Fintype (criticalPoints 𝓘(ℝ, E) f)]

/-- **The Barraud–Cornea cocycle is natural in the target**: the cocycle of `S` for `g ∘ θ` is the
image of the cocycle for `θ` under the morphism `C_*(Ωg)` of chain algebras. -/
theorem map_loopChainMap_barraudCorneaCocycle {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    (hX.barraudCorneaCocycle hf hdense hθ hc S).map (loopChainMap R g hg) =
      hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
        (comp_apply_criticalPoints_eq hθ g hg) hc S :=
  TwistingCocycle.ext fun x y ↦ by
    rw [TwistingCocycle.map_m, barraudCorneaCocycle_m, barraudCorneaCocycle_m, loopChainMap_apply,
      ← LinearMap.comp_apply, ← cubicalChainSumMap_comp,
      hX.morseLoopEvaluation_comp hf hdense hθ g hg, ContinuousMap.comp_assoc]

/-- **The continuation cocycle of a homotopy of chain systems is natural in the target**: its
entries for `g ∘ θ` are the images of its entries for `θ` under `C_*(Ωg)`. -/
theorem loopChainMap_barraudCorneaContinuationCocycle_ν
    [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}
    {S S' : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R} (T : S.Homotopy S')
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    loopChainMap R g hg ((hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).ν x y) =
      (hX.barraudCorneaContinuationCocycle hf hdense (θ := g.comp θ)
        (comp_apply_criticalPoints_eq hθ g hg) hc T).ν x y := by
  rw [barraudCorneaContinuationCocycle_ν, barraudCorneaContinuationCocycle_ν, map_add,
    loopChainMap_apply R g hg (cubicalChainSumMap R _ _), ← LinearMap.comp_apply,
    ← cubicalChainSumMap_comp, hX.morseLoopEvaluation_comp hf hdense hθ g hg,
    ContinuousMap.comp_assoc, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-! ### The DG Morse complex with pulled-back coefficients -/

variable (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
  (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)

/-- **The DG Morse complex with pulled-back coefficients**: for a based map
`g : (Y, y₀) → (Y', y₁)` and a DG local system `𝓖` on `(Y', y₁)`, the DG Morse complex of `S`
for `θ` with coefficients in the pullback `g^* 𝓖` is isomorphic to the DG Morse complex of `S`
for `g ∘ θ` with coefficients in `𝓖`. The isomorphism is the identity of the underlying functions
on the critical points (`twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f`). -/
def dgMorseComplexPullbackIso (𝓖 : DGLocalSystem.{uM} Y' y₁ R) :
    hX.dgMorseComplex hf hdense hθ hc S ((DGLocalSystem.pullback R g hg).obj 𝓖) ≅
      hX.dgMorseComplex hf hdense (θ := g.comp θ)
        (comp_apply_criticalPoints_eq hθ g hg) hc S 𝓖 :=
  (hX.dgMorseComplexFunctor hf hdense hθ hc S).mapIso
      (DGRightModuleCat.restrictScalarsObjIso (loopChainMap R g hg) 𝓖) ≪≫
    (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedCochainComplexRestrictScalarsIso
      (loopChainMap R g hg) 𝓖.isDGRightModule ≪≫
    eqToIso (congrArg (TwistingCocycle.twistedCochainComplex · 𝓖.differential 𝓖.isDGRightModule)
      (hX.map_loopChainMap_barraudCorneaCocycle hf hdense hθ g hg hc S))

/-- The isomorphism `dgMorseComplexPullbackIso` is the identity of the underlying functions on the
critical points. -/
@[simp]
theorem twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f
    (𝓖 : DGLocalSystem.{uM} Y' y₁ R) (n : ℤ)
    (a : (hX.dgMorseComplex hf hdense hθ hc S ((DGLocalSystem.pullback R g hg).obj 𝓖)).X n) :
    (twistedCochainComplexXEquiv
        (hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
          (comp_apply_criticalPoints_eq hθ g hg) hc S).mem_graded
        (hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
          (comp_apply_criticalPoints_eq hθ g hg) hc S).twisting
        𝓖.isDGRightModule n
        (((hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).hom.f n).hom a) :
          criticalPoints 𝓘(ℝ, E) f → 𝓖) =
      fun x ↦ DGRightModuleCat.restrictScalarsEquiv (loopChainMap R g hg) 𝓖
        ((twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
          (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
          ((DGLocalSystem.pullback R g hg).obj 𝓖).isDGRightModule n a).val x) := by
  funext x
  set m := hX.barraudCorneaCocycle hf hdense hθ hc S
  set e := DGRightModuleCat.restrictScalarsObjIso (loopChainMap R g hg) 𝓖
  -- Stated for an arbitrary DG local system `N`, so that instance search finds the compatibility of
  -- the action with the grading of `N`, which it does not see on the restricted object itself.
  have hA := fun {N : DGLocalSystem.{uM} Y y₀ R}
      (φ : (DGLocalSystem.pullback R g hg).obj 𝓖 ⟶ N) ↦
    m.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply _ _ φ n a
  have hB := m.twistedCochainComplexXEquiv_restrictScalarsXEquiv (loopChainMap R g hg)
    𝓖.isDGRightModule n ((((hX.dgMorseComplexFunctor hf hdense hθ hc S).map e.hom).f n).hom a)
  have hC := TwistingCocycle.twistedCochainComplexXEquiv_eqToHom_f
    𝓖.differential (hX.map_loopChainMap_barraudCorneaCocycle hf hdense hθ g hg hc S)
    𝓖.isDGRightModule n
    (((m.twistedCochainComplexRestrictScalarsIso (loopChainMap R g hg) 𝓖.isDGRightModule).hom.f
      n).hom ((((hX.dgMorseComplexFunctor hf hdense hθ hc S).map e.hom).f n).hom a))
  have hR := m.twistedCochainComplexRestrictScalarsIso_hom_f_apply (loopChainMap R g hg)
    𝓖.isDGRightModule n ((((hX.dgMorseComplexFunctor hf hdense hθ hc S).map e.hom).f n).hom a)
  refine (congrFun hC x).trans ?_
  refine (congrArg (fun v ↦ (twistedCochainComplexXEquiv (m.map (loopChainMap R g hg)).mem_graded
    (m.map (loopChainMap R g hg)).twisting 𝓖.isDGRightModule n v : _ → 𝓖) x) hR).trans ?_
  refine (congrFun hB x).trans ?_
  rw [restrictScalarsPiEquiv_apply]
  have h' := congrFun (hA e.hom) x
  rw [Function.comp_apply, DGRightModuleCat.restrictScalarsObjIso_hom_apply] at h'
  exact congrArg DGRightModule.RestrictScalars.val h'

/-- The inverse of `dgMorseComplexPullbackIso` is the identity of the underlying functions on the
critical points. -/
@[simp]
theorem twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_inv_f
    (𝓖 : DGLocalSystem.{uM} Y' y₁ R) (n : ℤ)
    (a : (hX.dgMorseComplex hf hdense (θ := g.comp θ)
      (comp_apply_criticalPoints_eq hθ g hg) hc S 𝓖).X n) :
    (twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
        (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
        ((DGLocalSystem.pullback R g hg).obj 𝓖).isDGRightModule n
        (((hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).inv.f n).hom a) :
          criticalPoints 𝓘(ℝ, E) f → (DGLocalSystem.pullback R g hg).obj 𝓖) =
      fun x ↦ (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R g hg) 𝓖).symm
        ((twistedCochainComplexXEquiv
          (hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
            (comp_apply_criticalPoints_eq hθ g hg) hc S).mem_graded
          (hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
            (comp_apply_criticalPoints_eq hθ g hg) hc S).twisting
          𝓖.isDGRightModule n a).val x) := by
  have h := hX.twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f hf hdense hθ g hg hc S
    𝓖 n (((hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).inv.f n).hom a)
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, ModuleCat.id_apply] at h
  funext x
  rw [h]
  exact ((DGRightModuleCat.restrictScalarsEquiv (loopChainMap R g hg) 𝓖).symm_apply_apply _).symm

/-- **The pulled-back DG Morse complexes are natural in the coefficients**: the isomorphisms
`dgMorseComplexPullbackIso` form an isomorphism between the DG Morse complex functor for `θ`
precomposed with the pullback along `g` and the DG Morse complex functor for `g ∘ θ`. -/
def dgMorseComplexFunctorPullbackIso :
    DGLocalSystem.pullback.{uM} R g hg ⋙ hX.dgMorseComplexFunctor hf hdense hθ hc S ≅
      hX.dgMorseComplexFunctor hf hdense (θ := g.comp θ)
        (comp_apply_criticalPoints_eq hθ g hg) hc S :=
  NatIso.ofComponents (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S) fun {𝓖 𝓗} φ ↦
    TwistingCocycle.twistedCochainComplex_hom_ext _ _ fun n a ↦ by
      have h₁ := hX.twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f hf hdense hθ g hg
        hc S 𝓗 n ((((hX.dgMorseComplexFunctor hf hdense hθ hc S).map
          ((DGLocalSystem.pullback R g hg).map φ)).f n).hom a)
      have h₂ := TwistingCocycle.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply
        _ _ (hX.barraudCorneaCocycle hf hdense hθ hc S) ((DGLocalSystem.pullback R g hg).map φ) n a
      have h₃ := TwistingCocycle.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply
        _ _ (hX.barraudCorneaCocycle hf hdense (θ := g.comp θ)
          (comp_apply_criticalPoints_eq hθ g hg) hc S)
        φ n (((hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).hom.f n).hom a)
      have h₄ := hX.twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f hf hdense hθ g hg
        hc S 𝓖 n a
      refine h₁.trans (Eq.trans ?_ ((congrArg (φ ∘ ·) h₄).symm.trans h₃.symm))
      funext x
      exact (congrArg _ (congrFun h₂ x)).trans (DGRightModuleCat.restrictScalars_map_apply _ φ _)

/-- The components of `dgMorseComplexFunctorPullbackIso` are the isomorphisms
`dgMorseComplexPullbackIso`. -/
@[simp]
theorem dgMorseComplexFunctorPullbackIso_app (𝓖 : DGLocalSystem.{uM} Y' y₁ R) :
    (hX.dgMorseComplexFunctorPullbackIso hf hdense hθ g hg hc S).app 𝓖 =
      hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖 := by
  ext1
  -- `NatIso.ofComponents_hom_app` does not match syntactically: the components are stated with
  -- `dgMorseComplex`, the functors with their objects; the two agree by definition.
  rw [dgMorseComplexFunctorPullbackIso]
  rfl

/-- **The pulled-back DG Morse complexes commute with the independence of the chain system**:
under the Morse–Smale condition, the continuation isomorphisms of a homotopy `T` of chain systems
for `θ`, with pulled-back coefficients, and for `g ∘ θ` correspond under
`dgMorseComplexPullbackIso`. -/
@[reassoc]
theorem dgMorseComplexPullbackIso_hom_comp_dgMorseComplexIsoOfHomotopy_hom
    [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] (hMS : hX.IsMorseSmale)
    {S' : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
      (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R}
    (T : S.Homotopy S') (𝓖 : DGLocalSystem.{uM} Y' y₁ R) :
    (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).hom ≫
        (hX.dgMorseComplexIsoOfHomotopy hf hdense (θ := g.comp θ)
          (comp_apply_criticalPoints_eq hθ g hg) hc hMS T 𝓖).hom =
      (hX.dgMorseComplexIsoOfHomotopy hf hdense hθ hc hMS T
          ((DGLocalSystem.pullback R g hg).obj 𝓖)).hom ≫
        (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S' 𝓖).hom := by
  rw [dgMorseComplexIsoOfHomotopy_hom, dgMorseComplexIsoOfHomotopy_hom]
  refine TwistingCocycle.twistedCochainComplex_hom_ext _ _ fun n a ↦ ?_
  have h₁ := (hX.barraudCorneaContinuationCocycle hf hdense (θ := g.comp θ)
    (comp_apply_criticalPoints_eq hθ g hg) hc T).continuationHom_f_apply
      𝓖.isDGRightModule n
        (((hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S 𝓖).hom.f n).hom a)
  have h₂ := (hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).continuationHom_f_apply
    ((DGLocalSystem.pullback R g hg).obj 𝓖).isDGRightModule n a
  have h₃ := hX.twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f hf hdense hθ g hg hc
    S' 𝓖 n ((((hX.barraudCorneaContinuationCocycle hf hdense hθ hc T).continuationHom
      ((DGLocalSystem.pullback R g hg).obj 𝓖).isDGRightModule).f n).hom a)
  have h₄ := hX.twistedCochainComplexXEquiv_dgMorseComplexPullbackIso_hom_f hf hdense hθ g hg hc
    S 𝓖 n a
  refine h₁.trans ((congrArg (continuationMap R 𝓖 _) h₄).trans (Eq.trans ?_ h₃.symm))
  funext y
  rw [congrFun h₂]
  simp only [continuationMap_apply, map_sum, DGRightModuleCat.restrictScalarsEquiv_smul,
    MulOpposite.unop_op,
    hX.loopChainMap_barraudCorneaContinuationCocycle_ν hf hdense hθ g hg hc T]

end Target

/-! ### Pulled-back fibrations -/

section Fibration

universe u

variable {Y Y' : Type u} [TopologicalSpace Y] [TopologicalSpace Y'] {θ : C(M, Y)} {y₀ : Y}
  {y₁ : Y'} (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (g : C(Y, Y')) (hg : g y₀ = y₁)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) {R : Type u} [CommRing R]
  [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)

/-- **A map of Hurewicz fibrations induces a quasi-isomorphism of DG Morse complexes** when it is
a homotopy equivalence on the fibres: for a commutative square `p' ∘ h = g ∘ p` of Hurewicz
fibrations `p : E → Y` and `p' : E' → Y'`, the DG Morse complex for `θ` with coefficients in the
chains `C_*(F'_p)` on the fibre of the Moore-path replacement of `p` is quasi-isomorphic to the DG
Morse complex for `g ∘ θ` with coefficients in `C_*(F'_{p'})`, through the morphism induced by the
square followed by `dgMorseComplexPullbackIso`. -/
theorem quasiIso_dgMorseComplexFunctor_map_fibrationLocalSystemSquareMap_comp {E E' : Type u}
    [TopologicalSpace E] [TopologicalSpace E'] {p : C(E, Y)} {p' : C(E', Y')}
    (hp : IsHurewiczFibration.{u} p) (hp' : IsHurewiczFibration.{u} p') (h : C(E, E'))
    (hsq : p'.comp h = g.comp p) (e : {x // p x = y₀} ≃ₕ {x // p' x = y₁})
    (he : ∀ x, (e x : E') = h x) :
    QuasiIso ((hX.dgMorseComplexFunctor hf hdense hθ hc S).map
        (fibrationLocalSystemSquareMap R h g hsq hg) ≫
      (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S (fibrationLocalSystem R p' y₁)).hom) :=
  quasiIso_comp _ _
    (hφ := hX.quasiIso_dgMorseComplexFunctor_map hf hdense hθ hc S
      (isQuasiIso_fibrationLocalSystemSquareMap hp hp' h g hsq hg e he))
    -- Elaborated without the expected type: there the source of the isomorphism is an object of
    -- `dgMorseComplexFunctor`, which is `dgMorseComplex` only after unfolding the functor, so
    -- instance search does not see that its `hom` is an isomorphism.
    (hφ' := (quasiIso_of_isIso
      (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S (fibrationLocalSystem R p' y₁)).hom :))

/-- **DG Morse homology of a pulled-back fibration**: for a Hurewicz fibration `p' : E' → Y'` and
a based map `g : (Y, y₀) → (Y', y₁)`, the DG Morse complex for `θ` with coefficients in the chains
on the fibre of the Moore-path replacement of the base change `Y ×_{Y'} E' → Y` is
quasi-isomorphic to the DG Morse complex for `g ∘ θ` with coefficients in `C_*(F'_{p'})`. -/
theorem quasiIso_dgMorseComplexFunctor_map_fibrationLocalSystemSquareMap_pullbackSnd_comp
    {E' : Type u} [TopologicalSpace E'] {p' : C(E', Y')} (hp' : IsHurewiczFibration.{u} p') :
    QuasiIso ((hX.dgMorseComplexFunctor hf hdense hθ hc S).map
        (fibrationLocalSystemSquareMap R
          (p := (TopCat.pullbackFst (TopCat.ofHom g) (TopCat.ofHom p')).hom) (p' := p')
          (TopCat.pullbackSnd (TopCat.ofHom g) (TopCat.ofHom p')).hom g
          (ContinuousMap.ext fun x ↦ x.property.symm) hg) ≫
      (hX.dgMorseComplexPullbackIso hf hdense hθ g hg hc S
        (fibrationLocalSystem R p' y₁)).hom) := by
  subst hg
  exact quasiIso_comp _ _
    (hφ := hX.quasiIso_dgMorseComplexFunctor_map hf hdense hθ hc S
      (isQuasiIso_fibrationLocalSystemSquareMap_pullbackSnd hp' g y₀))
    -- Elaborated without the expected type, as in
    -- `quasiIso_dgMorseComplexFunctor_map_fibrationLocalSystemSquareMap_comp`.
    (hφ' := (quasiIso_of_isIso
      (hX.dgMorseComplexPullbackIso hf hdense hθ g rfl hc S (fibrationLocalSystem R p' _)).hom :))

end Fibration

end IsAdaptedPseudoGradient

end TauCeti
