/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.LocalCoefficient.UniversalCover
public import TauCeti.Topology.VectorBundle.Thom.QuotientCovering.Basic

/-!
# Local systems on the total space through a pull-back along a quotient covering map

Let `f : X → B` be the quotient covering map of an action of a group `G`, let `E → B` be a fibre
bundle, and let `G` act on the total space `E'` of the pull-back `f^*E` over its action on `X`,
fixing the image of each point in the total space of `E`. Then `E' → E` is again a quotient
covering map for `G` (`TauCeti.isQuotientCoveringMap_pullbackThomPairMap_fst`), so a
representation `D` of `G` over a commutative ring `k` has an associated local system `L_D` on the
total space of `E` as well as one on `B`. This file identifies the first with the pull-back of the
second along the bundle projection `π : E → B`:

`L_D ≅ π^* L_D`

(`TauCeti.pullbackThomPairAssociatedLocalSystemIso`), and in the coordinates of a sheet `e` of
`E' → E` and of its image sheet of `X → B` it is the identity of `D`
(`TauCeti.pullbackThomPairAssociatedLocalSystemIso_hom_app_comp_fiberIso_hom`).

For the universal cover of a path-connected, locally path-connected, semilocally simply connected
base `B`, with `G = π₁(B, x₀)` acting on `f^*E` by `Bundle.Pullback.totalSpaceMulAction`, every
local system `L` on `B` is associated to its monodromy representation `L_{x₀}`
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`). So the local system on the total
space of `E` associated to `L_{x₀}` is `π^* L`
(`TauCeti.UniversalCover.thomPairAssociatedLocalSystemMonodromyIso`). Read in the coordinates of a
sheet `e` on the left and, on the right, by transport back to `L_{x₀}` along the path class of the
image sheet of the universal cover, it is the identity of `L_{x₀}`
(`TauCeti.UniversalCover.thomPairAssociatedLocalSystemMonodromyIso_hom_app_comp`). This is the
identification under which twisted homology of the Thom pair `(E, E₀)` with coefficients in the
local system associated to `L_{x₀}`, as computed from the deck action on the Thom pair of the
bundle pulled back to the universal cover (`TauCeti.quotientTwistedHomologyThomIso`), is twisted
homology with coefficients in `π^* L`.

## Main definitions and results

* `TauCeti.pullbackThomPairAssociatedLocalSystemIso`: `L_D ≅ π^* L_D` on the total space of `E`.
* `TauCeti.UniversalCover.thomPairAssociatedLocalSystemMonodromyIso`: `L_{L_{x₀}} ≅ π^* L` on the
  total space of `E`, through the universal cover of `B`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (local coefficient
  systems and modules over the group ring of `π₁`).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory

namespace TauCeti

universe u

-- The zeros of the fibres of the pull-back are read as in `TauCeti.pullbackThomPairMap`, so that
-- the Thom pair of the pull-back below is the source of that map.
attribute [local instance] pullbackFiberZero

section QuotientCovering

variable {B : Type u} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type u}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, AddCommMonoid (E b)] {X : Type u} [TopologicalSpace X] {f : C(X, B)} {G : Type u} [Group G]
  [MulAction G X] [MulAction G (TotalSpace F ((⇑f) *ᵖ E))] (k : Type u) [CommRing k]
  (hf : IsQuotientCoveringMap (TopCat.ofHom f) G)
  (hproj : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)), (g • z).proj = g • z.proj)
  (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)), Pullback.lift f (g • z) = Pullback.lift f z)

/-- **The local system on the total space associated through a pull-back is pulled back from the
base.** Let `f : X → B` be the quotient covering map of an action of a group `G`, and let `G` act on
the total space of `f^*E` over its action on `X`, fixing the image of each point in the total space
of `E`. For every representation `D` of `G`, the local system `L_D` on the total space of `E`
associated to the quotient covering map `f^*E → E` is the pull-back along the bundle projection
`π : E → B` of the local system `L_D` on `B` associated to `f`. -/
def pullbackThomPairAssociatedLocalSystemIso (D : Rep.{u} k G) :
    letI := pullbackThomPairFstMulAction F E f G
    (isQuotientCoveringMap_pullbackThomPairMap_fst (f := f) hf hproj hlift).associatedLocalSystem
        k D ≅
      (LocalCoefficientSystem.pullback (thomPairProj F E).hom).obj (hf.associatedLocalSystem k D) :=
  letI := pullbackThomPairFstMulAction F E f G
  -- The restriction of `D` along the identity of `G` is `D` itself (`Rep.res_id`).
  (isQuotientCoveringMap_pullbackThomPairMap_fst (f := f) hf hproj
    hlift).associatedLocalSystemBaseChangeIso k hf (φ := MonoidHom.id G)
    (thomPairProj F ((⇑f) *ᵖ E))
    (pullbackThomPairFstMulAction_thomPairProj_smul hproj) (thomPairProj F E)
    (pullbackThomPairMap_fst_comp_thomPairProj F E f) D

/-- In the coordinates of a sheet `e` of the quotient covering map `f^*E → E` and of its image sheet
of `f`, the isomorphism `L_D ≅ π^* L_D` is the identity of `D`. -/
theorem pullbackThomPairAssociatedLocalSystemIso_hom_app_comp_fiberIso_hom (D : Rep.{u} k G)
    {x : FundamentalGroupoid (thomPair F E).fst}
    (e : TopPair.Hom.fst (pullbackThomPairMap F E f) ⁻¹' {x.as})
    (e' : TopCat.ofHom f ⁻¹' {thomPairProj F E x.as}) (he : thomPairProj F ((⇑f) *ᵖ E) e = e') :
    letI := pullbackThomPairFstMulAction F E f G
    (pullbackThomPairAssociatedLocalSystemIso k hf hproj hlift D).hom.app x ≫
        (hf.associatedLocalSystemFiberIso k D e').hom =
      ((isQuotientCoveringMap_pullbackThomPairMap_fst (f := f) hf hproj
        hlift).associatedLocalSystemFiberIso k D e).hom := by
  let := pullbackThomPairFstMulAction F E f G
  rw [pullbackThomPairAssociatedLocalSystemIso,
    IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso_hom]
  exact ((isQuotientCoveringMap_pullbackThomPairMap_fst (f := f) hf hproj
    hlift).associatedLocalSystemMapOver_app_comp_fiberIso_hom k hf (φ := MonoidHom.id G)
    (thomPairProj F ((⇑f) *ᵖ E)) (pullbackThomPairFstMulAction_thomPairProj_smul hproj)
    (thomPairProj F E) (pullbackThomPairMap_fst_comp_thomPairProj F E f)
    (𝟙 (Rep.res (MonoidHom.id G) D)) e e' he).trans (Category.comp_id _)

end QuotientCovering

namespace UniversalCover

variable {B : TopCat.{u}} [LocallyPathConnectedSpace B] [PathConnectedSpace B]
  [SemilocallySimplyConnectedSpace B] (x₀ : B) {F : Type*} [TopologicalSpace F] {E : B → Type u}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, AddCommMonoid (E b)] (k : Type u) [CommRing k] (L : LocalCoefficientSystem.{u, u, u} k B)

/-- **The local system on the total space associated to the monodromy of `L` is `π^* L`.** Let `B`
be path-connected, locally path-connected and semilocally simply connected, let `E → B` be a fibre
bundle, and let the fundamental group `π₁(B, x₀)` act on the total space of the bundle pulled back
to the universal cover by deck transformations of base points
(`Bundle.Pullback.totalSpaceMulAction`). For every local system `L` on `B`, the local system on the
total space of `E` associated, through the quotient covering map of total spaces, to the monodromy
representation `L_{x₀}` of `L` is the pull-back `π^* L` along the bundle projection. -/
def thomPairAssociatedLocalSystemMonodromyIso :
    letI := Pullback.totalSpaceMulAction (F := F) (E := E) (f := ⇑(projTopHom x₀).hom)
      fun g p ↦ proj_smul g p
    letI := pullbackThomPairFstMulAction F E (projTopHom x₀).hom (FundamentalGroup B x₀)
    (isQuotientCoveringMap_pullbackThomPairMap_fst (isQuotientCoveringMap_projTopHom x₀)
      (Pullback.totalSpaceMulAction_proj_smul _) (Pullback.totalSpaceMulAction_lift_smul _)
      ).associatedLocalSystem k ((LocalCoefficientSystem.monodromyFunctor k B x₀).obj L) ≅
      (LocalCoefficientSystem.pullback (thomPairProj F E).hom).obj L :=
  letI := Pullback.totalSpaceMulAction (F := F) (E := E) (f := ⇑(projTopHom x₀).hom)
    fun g p ↦ proj_smul g p
  pullbackThomPairAssociatedLocalSystemIso k (isQuotientCoveringMap_projTopHom x₀)
      (Pullback.totalSpaceMulAction_proj_smul _) (Pullback.totalSpaceMulAction_lift_smul _) _ ≪≫
    (LocalCoefficientSystem.pullback (thomPairProj F E).hom).mapIso
      (associatedLocalSystemMonodromyIso x₀ k L)

/-- Read in the coordinates of a sheet `e` of the quotient covering map of total spaces on the left,
and on the right by transport back to `L_{x₀}` along the path class of the image sheet `e'` of the
universal cover (`TauCeti.UniversalCover.sheetCoordinates`), the isomorphism `L_{L_{x₀}} ≅ π^* L`
is the identity of `L_{x₀}`. -/
theorem thomPairAssociatedLocalSystemMonodromyIso_hom_app_comp
    {x : FundamentalGroupoid (thomPair F E).fst}
    (e : TopPair.Hom.fst (pullbackThomPairMap F E (projTopHom x₀).hom) ⁻¹' {x.as})
    (e' : projTopHom x₀ ⁻¹' {thomPairProj F E x.as})
    (he : thomPairProj F ((⇑(projTopHom x₀).hom) *ᵖ E) e = e') :
    letI := Pullback.totalSpaceMulAction (F := F) (E := E) (f := ⇑(projTopHom x₀).hom)
      fun g p ↦ proj_smul g p
    letI := pullbackThomPairFstMulAction F E (projTopHom x₀).hom (FundamentalGroup B x₀)
    (thomPairAssociatedLocalSystemMonodromyIso x₀ k L).hom.app x ≫
        (sheetCoordinates (x := (FundamentalGroupoid.map (thomPairProj F E).hom).obj x) k L
          e').hom =
      ((isQuotientCoveringMap_pullbackThomPairMap_fst (isQuotientCoveringMap_projTopHom x₀)
        (Pullback.totalSpaceMulAction_proj_smul _) (Pullback.totalSpaceMulAction_lift_smul _)
        ).associatedLocalSystemFiberIso k _ e).hom := by
  let := Pullback.totalSpaceMulAction (F := F) (E := E) (f := ⇑(projTopHom x₀).hom)
    fun g p ↦ proj_smul g p
  rw [← pullbackThomPairAssociatedLocalSystemIso_hom_app_comp_fiberIso_hom k
    (isQuotientCoveringMap_projTopHom x₀) (Pullback.totalSpaceMulAction_proj_smul _)
    (Pullback.totalSpaceMulAction_lift_smul _) _ e e' he,
    ← associatedLocalSystemMonodromyIso_hom_app_comp k L e']
  simp only [thomPairAssociatedLocalSystemMonodromyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom]
  -- The two composites differ only by reassociation, up to the definitional unfolding of the
  -- image `(FundamentalGroupoid.map π).obj x` of `x`.
  exact Category.assoc _ _ _

end UniversalCover

end TauCeti
