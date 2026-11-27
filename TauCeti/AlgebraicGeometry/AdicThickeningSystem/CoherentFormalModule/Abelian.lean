/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Colimits
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Spf
public import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Coherent formal modules on affine noetherian formal completions form an abelian category

The category of coherent formal modules on an adic thickening system has cokernels computed
levelwise, but kernels are not levelwise, since pullback along the transition maps is only right
exact: multiplication by `t` on `k⟦t⟧` is injective, while its reduction modulo `t` is zero. On the
formal spectrum `Spf A` of a noetherian adic ring the category is nevertheless abelian, because it
is equivalent to the abelian category of finite `A`-modules (`spfEquivFGModuleCat`, Stacks,
Lemma 30.23.1). The kernel of a morphism of coherent formal modules there is the system of
reductions `K ⧸ I ^ (n + 1) K` of the kernel `K` of the corresponding map of finite `A`-modules,
which can differ from the levelwise kernels, as the multiplication-by-`t` example shows.

Pullback along an isomorphism of adic thickening systems is an equivalence of categories of
coherent formal modules (`CoherentFormalModule.isEquivalence_pullback`), so the abelian structure
transports along such isomorphisms (`CoherentFormalModule.abelianOfIso`). Through the
identifications `spf I ≅ Spf R̂` of the system `Spec (R ⧸ I ^ (n + 1))` with the formal spectrum
of the `I`-adic completion `R̂` of `R`, and `X/V(I) ≅ spf J` of the formal completion of an affine
scheme with such a system, coherent formal modules form an abelian category on `spf I` for every
ideal `I` of a noetherian ring and on the formal completion `X/V(I)` of every affine locally
noetherian scheme `X` along any closed subscheme. This is the affine case of the statement that
coherent formal modules on the formal completion of a noetherian scheme form an abelian category
(Stacks, Lemma 30.23.2), to which the general case reduces by gluing kernels along an affine open
cover.

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.abelianOfIso`: the abelian
  structure on coherent formal modules transported along an isomorphism of adic thickening
  systems.

## Main results

* `Abelian (CoherentFormalModule (Spf A))` for an adic ring `A` with noetherian underlying ring.
* `Abelian (CoherentFormalModule (spf I))` for an ideal `I` of a noetherian ring.
* `Abelian (CoherentFormalModule (X.formalCompletion I))` for an affine locally noetherian scheme
  `X` and an ideal sheaf `I` on `X`.

## References

* [Stacks Project, Section 30.23](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

noncomputable section

variable {𝔛 𝔜 : AdicThickeningSystem.{u}}

/-- The abelian structure on coherent formal modules on `𝔛`, transported from that on an
isomorphic adic thickening system `𝔜` along the equivalence given by pullback along `e.inv`. It
extends the preadditive structure of `CoherentFormalModule 𝔛`. -/
@[instance_reducible]
def abelianOfIso (e : 𝔛 ≅ 𝔜) [Abelian (CoherentFormalModule 𝔜)] :
    Abelian (CoherentFormalModule 𝔛) :=
  abelianOfEquivalence (pullback e.inv)

/-- **Coherent formal modules on `Spf A` form an abelian category** for an adic ring `A` whose
underlying ring is noetherian, being equivalent to finite `A`-modules (`spfEquivFGModuleCat`). -/
instance (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    Abelian (CoherentFormalModule (Spf A)) :=
  abelianOfEquivalence (spfEquivFGModuleCat A).functor

/-- Coherent formal modules on the system `spf I` of the schemes `Spec (R ⧸ I ^ (n + 1))` form an
abelian category for an ideal `I` of a noetherian ring `R`: the system is the formal spectrum of
the `I`-adic completion of `R`, which is noetherian. -/
instance {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Abelian (CoherentFormalModule (spf I)) :=
  abelianOfIso (Spf.completionIso I (IsNoetherian.noetherian I)).symm

end

end TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry AdicThickeningSystem IdealSheafData

variable (X : Scheme.{u}) (I : X.IdealSheafData) [IsAffine X]

/-- **Coherent formal modules on the formal completion of an affine noetherian scheme form an
abelian category.** For an affine locally noetherian scheme `X` and an ideal sheaf `I`, the formal
completion `X/V(I)` is the formal spectrum of the completion of the noetherian ring `Γ(X, ⊤)` along
the ideal of `V(I)`, on which coherent formal modules are equivalent to finite modules. -/
noncomputable instance [IsLocallyNoetherian X] :
    Abelian (CoherentFormalModule (X.formalCompletion I)) :=
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  -- Under `X.isoSpec`, `I` corresponds to the ideal sheaf `K` on `Spec Γ(X, ⊤)`, which is cut out
  -- by an ideal of `Γ(X, ⊤)` since `Spec Γ(X, ⊤)` is affine.
  let K := I.comap X.isoSpec.inv
  let e := (ΓSpecIso (CommRingCat.of Γ(X, ⊤))).commRingCatIsoToRingEquiv
  let J : Ideal Γ(X, ⊤) := (equivOfIsAffine K).map e
  have hJ : ofIdealTop (J.map (ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv.hom) = K :=
    (congrArg ofIdealTop (Ideal.map_of_equiv e)).trans (equivOfIsAffine.symm_apply_apply K)
  CoherentFormalModule.abelianOfIso <| mapIso X.isoSpec
    (by rw [hJ, ← comap_comp, Iso.hom_inv_id, comap_id]) ≪≫ specIso J

end AlgebraicGeometry.Scheme.formalCompletion
