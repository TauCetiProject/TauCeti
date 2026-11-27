/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Tensor
public import TauCeti.AlgebraicTopology.LocalCoefficient.UniversalCover
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character

/-!
# Twisting a local system by the orientation character

Let `E → B` be a real vector bundle of rank `card ι` over a path-connected, locally
path-connected, semilocally simply connected space `B` with a basepoint `b`, and let `k` be a
commutative ring. The orientation character `w₁ : π₁(B, b) →* ℤˣ` of `E`
(`TauCeti.VectorBundleOrientationCover.orientationCharacter`), read in `kˣ`, gives the rank-one
representation `k_{w₁}` of `π₁(B, b)` on `k`. This file identifies the local systems that
`k_{w₁}` and its tensor products produce on `B` through the universal cover
(`IsQuotientCoveringMap.associatedLocalSystem` for `TauCeti.UniversalCover.projTopHom`):

* The monodromy representation of the orientation local system `o(E)` at `b` is `k_{w₁}`, by
  evaluation at an orientation `o` of the fibre `E_b`
  (`TauCeti.VectorBundleOrientationCover.monodromySignLocalSystemIso`): transport around a loop
  `g` multiplies by `w₁(g)`.
* Hence `L_{k_{w₁}} ≅ o(E)`
  (`TauCeti.VectorBundleOrientationCover.associatedLocalSystemOrientationCharacterIso`).
* For every local system `L` on `B`, with monodromy representation `D_L` on `L_b`,

  `L_{D_L ⊗ k_{w₁}} ≅ L ⊗ o(E)`

  (`TauCeti.VectorBundleOrientationCover.associatedLocalSystemTensorOrientationCharacterIso`),
  naturally in `L`
  (`associatedLocalSystemTensorOrientationCharacterIso_hom_naturality`). This combines the
  identification `L_{D_L} ≅ L` (`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`) with
  the tensor law `L_{A ⊗ A'} ≅ L_A ⊗ L_{A'}`
  (`IsQuotientCoveringMap.associatedLocalSystemTensorIso`).

The equivariant descent of the Thom isomorphism along a cover of the base that lifts to the
orientation double cover equivariantly for a character `ρ`
(`TauCeti.quotientTwistedHomologyThomIso`) has as its target the homology of the base with
coefficients in `L_{D ⊗ k_ρ}`. For the universal cover, `ρ = w₁` and `D = D_L`, the last
isomorphism identifies these coefficients with `L ⊗ o(E)`, the coefficients of the Thom isomorphism
`H_{q + r}(E, E₀; π^*L) ≅ H_q(B; L ⊗ o(E))` with arbitrary local coefficients; that Thom
isomorphism itself is not stated here. No orientation of `E` and no hypothesis on `2` in `k` is
needed. The identifications involving `o(E)` depend on the chosen orientation `o` of `E_b`: the
opposite orientation changes them by the sign `-1`.

Representations and their associated local systems need the fundamental group, the space and the
ring in one universe, so the base, the fibres and the ring lie in a common universe here.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.monodromySignLocalSystemIso`: the monodromy of `o(E)` is the
  orientation character.
* `TauCeti.VectorBundleOrientationCover.associatedLocalSystemOrientationCharacterIso`:
  `L_{k_{w₁}} ≅ o(E)`.
* `TauCeti.VectorBundleOrientationCover.associatedLocalSystemTensorOrientationCharacterIso`:
  `L_{D_L ⊗ k_{w₁}} ≅ L ⊗ o(E)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (local
  coefficient systems and modules over the group ring of `π₁`).
-/

public section

noncomputable section

open Bundle CategoryTheory Module MonoidalCategory

namespace TauCeti.VectorBundleOrientationCover

universe u

variable {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type u} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type u) [CommRing k]

/-! ### The monodromy of the orientation local system -/

/-- **The monodromy of the orientation local system is the orientation character.** Evaluation at
an orientation `o` of the fibre `E_b` identifies the monodromy representation of `o(E)` at `b` with
the rank-one representation of `π₁(B, b)` on `k` given by the orientation character `w₁`, read in
`kˣ`: transport around a loop `g` multiplies by `w₁(g)` (`signLocalSystemFiberEquiv_map_asHom`). -/
def monodromySignLocalSystemIso {b : B} (o : Orientation ℝ (E b) ι) :
    (LocalCoefficientSystem.monodromyFunctor k (TopCat.of B) b).obj (signLocalSystem F E k hι) ≅
      Rep.of (Representation.ofLinearCharacter
        ((Units.map (Int.castRingHom k).toMonoidHom).comp (orientationCharacter F E hι b))) :=
  Rep.mkIso (Representation.Equiv.mk (signLocalSystemFiberEquiv hι o) fun g ↦ by
    ext f
    exact (signLocalSystemFiberEquiv_map_asHom hι o g f).trans (by simp))

/-- The identification of the monodromy of `o(E)` with the orientation character is evaluation at
the chosen orientation. -/
-- Not a simp lemma: `simp` rewrites the carrier of the monodromy representation first.
theorem monodromySignLocalSystemIso_hom_apply {b : B} (o : Orientation ℝ (E b) ι)
    (f : (signLocalSystem F E k hι).obj (FundamentalGroupoid.mk b)) :
    (monodromySignLocalSystemIso hι k o).hom f = signLocalSystemFiberEquiv hι o f :=
  (rfl)

/-- The inverse identification of the orientation character with the monodromy of `o(E)` sends
`r` to the element of the fibre whose value at the chosen orientation is `r`. -/
-- Not a simp lemma: `simp` rewrites the carrier of the monodromy representation first.
theorem monodromySignLocalSystemIso_inv_apply {b : B} (o : Orientation ℝ (E b) ι) (r : k) :
    (monodromySignLocalSystemIso hι k o).inv r = (signLocalSystemFiberEquiv hι o).symm r :=
  (rfl)

/-! ### The orientation local system through the universal cover -/

variable [LocallyPathConnectedSpace B] [PathConnectedSpace B] [SemilocallySimplyConnectedSpace B]

/-- **The orientation local system is associated to the orientation character.** Through the
universal cover of `B`, the local system associated to the rank-one representation `k_{w₁}` of
`π₁(B, b)` given by the orientation character is the orientation local system `o(E)`. The
isomorphism depends on the orientation `o` of `E_b`: it is the identification of every local
system with the one associated to its monodromy
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`), after
`monodromySignLocalSystemIso`. -/
def associatedLocalSystemOrientationCharacterIso {b : B} (o : Orientation ℝ (E b) ι) :
    (UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b).associatedLocalSystem k
        (Rep.of (Representation.ofLinearCharacter
          ((Units.map (Int.castRingHom k).toMonoidHom).comp (orientationCharacter F E hι b)))) ≅
      signLocalSystem F E k hι :=
  ((UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b
      ).associatedLocalSystemFunctor k).mapIso (monodromySignLocalSystemIso hι k o).symm ≪≫
    UniversalCover.associatedLocalSystemMonodromyIso (X := TopCat.of B) b k
      (signLocalSystem F E k hι)

/-- In the coordinates of a sheet `e` of the universal cover, a path class from `b`, the
isomorphism `L_{k_{w₁}} ≅ o(E)` is the identity of `k`, read on `o(E)` by transport back along `e`
followed by evaluation at the chosen orientation `o`. -/
@[reassoc]
theorem associatedLocalSystemOrientationCharacterIso_hom_app_comp {b : B}
    (o : Orientation ℝ (E b) ι) {x : FundamentalGroupoid (TopCat.of B)}
    (e : UniversalCover.projTopHom (X := TopCat.of B) b ⁻¹' {x.as}) :
    (associatedLocalSystemOrientationCharacterIso hι k o).hom.app x ≫
        (UniversalCover.sheetCoordinates k (signLocalSystem F E k hι) e).hom ≫
          ModuleCat.ofHom (signLocalSystemFiberEquiv hι o).toLinearMap =
      ((UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b
        ).associatedLocalSystemFiberIso k _ e).hom := by
  rw [associatedLocalSystemOrientationCharacterIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, UniversalCover.associatedLocalSystemMonodromyIso_hom_app_comp_assoc,
    Functor.mapIso_hom, Iso.symm_hom, IsQuotientCoveringMap.associatedLocalSystemFunctor_map,
    IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_naturality_assoc]
  conv_rhs =>
    rw [← Category.comp_id (IsQuotientCoveringMap.associatedLocalSystemFiberIso _ _ _ e).hom]
  congr 1
  -- The inverse of `monodromySignLocalSystemIso` is the inverse of evaluation at `o`.
  ext
  exact (signLocalSystemFiberEquiv hι o).apply_symm_apply 1

/-! ### Twisting by the orientation character -/

/-- **Twisting by the orientation character tensors with the orientation local system.** For a
local system `L` on `B` with monodromy representation `D_L` on `L_b`, the local system associated
through the universal cover to `D_L ⊗ k_{w₁}`, the monodromy of `L` twisted by the orientation
character, is `L ⊗ o(E)`. This is the tensor law of associated local systems
(`IsQuotientCoveringMap.associatedLocalSystemTensorIso`) followed by `L_{D_L} ≅ L`
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`) and
`L_{k_{w₁}} ≅ o(E)` (`associatedLocalSystemOrientationCharacterIso`). -/
def associatedLocalSystemTensorOrientationCharacterIso {b : B} (o : Orientation ℝ (E b) ι)
    (L : LocalCoefficientSystem.{u, u, u} k (TopCat.of B)) :
    (UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b).associatedLocalSystem k
        ((LocalCoefficientSystem.monodromyFunctor k (TopCat.of B) b).obj L ⊗
          Rep.of (Representation.ofLinearCharacter
            ((Units.map (Int.castRingHom k).toMonoidHom).comp (orientationCharacter F E hι b)))) ≅
      L ⊗ signLocalSystem F E k hι :=
  (UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b
      ).associatedLocalSystemTensorIso k _ _ ≪≫
    (UniversalCover.associatedLocalSystemMonodromyIso (X := TopCat.of B) b k L ⊗ᵢ
      associatedLocalSystemOrientationCharacterIso hι k o)

/-- The isomorphism `L_{D_L ⊗ k_{w₁}} ≅ L ⊗ o(E)` is the tensor law of associated local systems
followed by the identifications of both factors. -/
theorem associatedLocalSystemTensorOrientationCharacterIso_hom {b : B}
    (o : Orientation ℝ (E b) ι) (L : LocalCoefficientSystem.{u, u, u} k (TopCat.of B)) :
    (associatedLocalSystemTensorOrientationCharacterIso hι k o L).hom =
      ((UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b
        ).associatedLocalSystemTensorIso k _ _).hom ≫
        ((UniversalCover.associatedLocalSystemMonodromyIso (X := TopCat.of B) b k L).hom ⊗ₘ
          (associatedLocalSystemOrientationCharacterIso hι k o).hom) :=
  (rfl)

/-- The isomorphism `L_{D_L ⊗ k_{w₁}} ≅ L ⊗ o(E)` is natural in the local system `L`. -/
@[reassoc]
theorem associatedLocalSystemTensorOrientationCharacterIso_hom_naturality {b : B}
    (o : Orientation ℝ (E b) ι) {L L' : LocalCoefficientSystem.{u, u, u} k (TopCat.of B)}
    (η : L ⟶ L') :
    (UniversalCover.isQuotientCoveringMap_projTopHom (X := TopCat.of B) b).associatedLocalSystemMap
        k ((LocalCoefficientSystem.monodromyFunctor k (TopCat.of B) b).map η ▷ _) ≫
      (associatedLocalSystemTensorOrientationCharacterIso hι k o L').hom =
    (associatedLocalSystemTensorOrientationCharacterIso hι k o L).hom ≫
      (η ▷ signLocalSystem F E k hι) := by
  rw [associatedLocalSystemTensorOrientationCharacterIso_hom,
    associatedLocalSystemTensorOrientationCharacterIso_hom, ← tensorHom_id, ← tensorHom_id,
    IsQuotientCoveringMap.associatedLocalSystemTensorIso_hom_naturality_assoc,
    IsQuotientCoveringMap.associatedLocalSystemMap_id, tensorHom_comp_tensorHom, Category.assoc,
    tensorHom_comp_tensorHom, UniversalCover.associatedLocalSystemMonodromyIso_hom_naturality,
    Category.id_comp, Category.comp_id]

end TauCeti.VectorBundleOrientationCover
