/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# Homology with coefficients in the orientation system over a trivializing set

Let `E → B` be a real vector bundle with orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), and let `e` be a trivialization of the
atlas. Over its base set the orientations of the fibres which `e` reads as a fixed orientation `ω`
of the model fibre form a continuous section of the orientation double cover, so evaluating at them
trivializes `o(E)` pulled back along any map `g` into the base set
(`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`). For a pair `(X, A)` and such a
map `g : X → B`, this identifies the relative homology of `(X, A)` with coefficients in `g^*o(E)`
with its ordinary relative homology with coefficients in `R`
(`TauCeti.VectorBundleOrientationCover.twistedHomologyPullbackSignLocalSystemIso`), naturally in
maps of pairs
(`twistedHomologyMap_twistedHomologyPullbackSignLocalSystemIso_hom`).
Reversing `ω` negates the identification.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.twistedHomologyPullbackSignLocalSystemIso`:
  `Hₙ(X, A; g^*o(E)) ≅ Hₙ(X, A; R)` for `g` with values in the base set of a trivialization.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficient systems, and homology with
  coefficients in a trivial system).
-/

public noncomputable section

open Bundle CategoryTheory Module

universe u

namespace TauCeti.VectorBundleOrientationCover

variable {R : Type u} [Ring R] {B : Type u} [TopologicalSpace B] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type u} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  (hι : Fintype.card ι = finrank ℝ F)

variable (R) in
/-- Over a map `g` from the ambient space of a pair to the base set of a trivialization `e` of the
atlas, the trivialization of the pulled-back orientation local system identifies homology with
coefficients in it with ordinary homology. -/
def twistedHomologyPullbackSignLocalSystemIso (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) (P : TopPair.{u})
    (g : C(P.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet) (n : ℕ) :
    P.twistedHomology ((LocalCoefficientSystem.pullback g).obj (signLocalSystem F E R hι)) n ≅
      P.singularHomology (ModuleCat.of R R) n :=
  asIso (P.twistedHomologyCoefficientMap (pullbackSignLocalSystemIso R hι e ω g hg).hom n) ≪≫
    P.twistedHomologyConstantIso (ModuleCat.of R R) n

/-- Two trivializations and orientations of the model fibre which pull back to the same
orientations of the fibres over `g` give the same identification of homology with coefficients in
the pulled-back orientation local system with ordinary homology. -/
theorem twistedHomologyPullbackSignLocalSystemIso_congr {e e' : Trivialization F (π F E)}
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {ω ω' : Orientation ℝ F ι}
    (P : TopPair.{u}) (g : C(P.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet)
    (hg' : ∀ y, g y ∈ e'.baseSet)
    (h : ∀ y, (e'.mapOrientation ι (hg' y)).symm ω' = (e.mapOrientation ι (hg y)).symm ω)
    (n : ℕ) :
    twistedHomologyPullbackSignLocalSystemIso R hι e' ω' P g hg' n =
      twistedHomologyPullbackSignLocalSystemIso R hι e ω P g hg n := by
  simp only [twistedHomologyPullbackSignLocalSystemIso,
    pullbackSignLocalSystemIso_congr hι g hg hg' h]

/-- Reversing the orientation of the model fibre negates the identification of homology with
coefficients in the pulled-back orientation local system with ordinary homology. -/
theorem twistedHomologyPullbackSignLocalSystemIso_neg_hom (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) (P : TopPair.{u})
    (g : C(P.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet) (n : ℕ) :
    (twistedHomologyPullbackSignLocalSystemIso R hι e (-ω) P g hg n).hom =
      -(twistedHomologyPullbackSignLocalSystemIso R hι e ω P g hg n).hom := by
  simp only [twistedHomologyPullbackSignLocalSystemIso, Iso.trans_hom, asIso_hom,
    pullbackSignLocalSystemIso_neg_hom, TopPair.twistedHomologyCoefficientMap_neg,
    Preadditive.neg_comp]

/-- The identification of homology with coefficients in the pulled-back orientation local system
with ordinary homology is natural in maps of pairs. -/
theorem twistedHomologyMap_twistedHomologyPullbackSignLocalSystemIso_hom
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (ω : Orientation ℝ F ι)
    {P Q : TopPair.{u}} (f : P ⟶ Q) (g : C(Q.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet)
    (n : ℕ) :
    TopPair.twistedHomologyMap f ((LocalCoefficientSystem.pullback g).obj
        (signLocalSystem F E R hι)) n ≫
      (twistedHomologyPullbackSignLocalSystemIso R hι e ω Q g hg n).hom =
    P.twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst f).hom g).inv.app
          (signLocalSystem F E R hι)) n ≫
      (twistedHomologyPullbackSignLocalSystemIso R hι e ω P (g.comp (TopPair.Hom.fst f).hom)
        (fun _ ↦ hg _) n).hom ≫
      P.singularHomologyMap f (ModuleCat.of R R) n := by
  simp only [twistedHomologyPullbackSignLocalSystemIso, Iso.trans_hom, asIso_hom,
    TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  -- Both trivializations evaluate over `y` at the orientation that `e` reads as `ω`.
  have h : (LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).map
        (pullbackSignLocalSystemIso R hι e ω g hg).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst f).hom (ModuleCat.of R R)).hom =
      (LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst f).hom g).inv.app
          (signLocalSystem F E R hι) ≫
        (pullbackSignLocalSystemIso R hι e ω (g.comp (TopPair.Hom.fst f).hom)
          (fun _ ↦ hg _)).hom := by
    ext ⟨y⟩ a
    simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app,
      LocalCoefficientSystem.pullbackConstantIso_hom_app,
      LocalCoefficientSystem.pullbackCompIso_inv_app_app]
    exact (pullbackSignLocalSystemIso_hom_app_apply hι e ω g hg ((TopPair.Hom.fst f) y) a).trans
      (pullbackSignLocalSystemIso_hom_app_apply hι e ω (g.comp (TopPair.Hom.fst f).hom)
        (fun _ ↦ hg _) y a).symm
  simp only [h, TopPair.twistedHomologyCoefficientMap_comp, Category.assoc]

end TauCeti.VectorBundleOrientationCover
