/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Exactness of flat pullback

Pullback along a flat morphism of schemes preserves monomorphisms between quasicoherent
module sheaves. Together with right exactness of pullback, this transports short exact
sequences of quasicoherent coefficients under flat base change.

The affine calculation uses `tildeFunctorCompPullbackIso` and Mathlib's finite-limit
preservation theorem for flat extension of scalars. No finiteness or Noetherian hypothesis
is needed.

## References

* [The Stacks Project, Tag 0250](https://stacks.math.columbia.edu/tag/0250),
  exactness of flat pullback on quasicoherent modules.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Flat pullback preserves monomorphisms of quasicoherent modules on a spectrum. -/
private theorem mono_pullback_specMap_of_flat (hφ : φ.hom.Flat)
    {M N : (Spec R).Modules} (g : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] :
    Mono ((pullback (Spec.map φ)).map g) := by
  let F := pullback (Spec.map φ)
  let G := moduleSpecΓFunctor (R := R)
  let c := fromTildeΓNatTrans (R := R)
  have : G.IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  have : PreservesFiniteLimits (ModuleCat.extendScalars φ.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : Mono ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).map (G.map g)) :=
    inferInstance
  let e := TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ
  have hm : Mono ((tilde.functor R ⋙ F).map (G.map g)) := by
    apply mono_of_mono_fac (e.hom.naturality (G.map g))
  have : IsIso (c.app M) := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso (c.app N) := isIso_fromTildeΓ_of_isQuasicoherent N
  have : IsIso (F.map (c.app N)) := inferInstance
  have hN : Mono (F.map (c.app N)) := IsIso.mono_of_iso _
  have hn : (tilde.functor R).map (G.map g) ≫ c.app N = c.app M ≫ g :=
    c.naturality g
  have : Mono (F.map (c.app M) ≫ F.map g) := by
    rw [← F.map_comp, ← hn]
    rw [F.map_comp]
    exact mono_comp' hm hN
  exact (mono_comp_iff_of_isIso (F.map (c.app M)) (F.map g)).mp inferInstance

variable {X Y : Scheme.{u}}

private theorem mono_pullback_map_of_flat_of_isAffine [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  let A := pullback Y.isoSpec.inv
  let B := pullback (Spec.map f.appTop)
  let C := pullback X.isoSpec.hom
  have : PreservesLimits C := X.isoSpec.hom.preservesLimits_pullback_of_isOpenImmersion
  have : Mono (B.map (A.map g)) :=
    mono_pullback_specMap_of_flat f.appTop f.flat_appTop (A.map g)
  have : Mono ((A ⋙ B ⋙ C).map g) :=
    inferInstanceAs (Mono (C.map (B.map (A.map g))))
  let e : A ⋙ B ⋙ C ≅ pullback f :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComp (Spec.map f.appTop) Y.isoSpec.inv) C ≪≫
      pullbackComp X.isoSpec.hom _ ≪≫ pullbackCongr (by
        rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])
  exact mono_of_mono_fac (e.inv.naturality g)

private theorem mono_pullback_map_of_flat_of_isAffineTarget [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  apply (mono_iff_of_isOpenCover X.isBasis_affineOpens.isOpenCover _).mpr
  intro U
  let V : X.Opens := U.1
  have : IsAffine V.toScheme := U.2
  have : Mono ((pullback (V.ι ≫ f)).map g) :=
    mono_pullback_map_of_flat_of_isAffine (V.ι ≫ f) g
  exact mono_of_mono_fac ((pullbackComp V.ι f).hom.naturality g)

/-- Pullback along a flat morphism preserves monomorphisms between quasicoherent sheaves.
Neither scheme needs to be affine or Noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.mono_pullback_map_of_flat
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  apply (mono_iff_of_isOpenCover (Y.isBasis_affineOpens.isOpenCover.comap f.base.hom) _).mpr
  intro U
  let V : Y.Opens := U.1
  have : IsAffine V.toScheme := U.2
  have hm : Mono ((pullback V.ι ⋙ pullback (f ∣_ V)).map g) :=
    mono_pullback_map_of_flat_of_isAffineTarget (f ∣_ V) ((pullback V.ι).map g)
  let e : pullback f ⋙ pullback (f ⁻¹ᵁ V).ι ≅
      pullback V.ι ⋙ pullback (f ∣_ V) :=
    pullbackComp _ f ≪≫ pullbackCongr (morphismRestrict_ι f V).symm ≪≫
      (pullbackComp (f ∣_ V) V.ι).symm
  have : IsIso (e.hom.app M) := inferInstance
  have hm' : Mono (e.hom.app M ≫ (pullback V.ι ⋙ pullback (f ∣_ V)).map g) :=
    mono_comp' (IsIso.mono_of_iso _) hm
  have hn : Mono ((pullback f ⋙ pullback (f ⁻¹ᵁ V).ι).map g ≫ e.hom.app N) :=
    (e.hom.naturality g).symm ▸ hm'
  exact @mono_of_mono _ _ _ _ _ _ _ hn

/-- Flat pullback carries a short exact sequence to a short exact sequence when its first two
terms are quasicoherent. No quasicoherence hypothesis on the third term is needed. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.shortExact_map_pullback_of_flat
    (f : X ⟶ Y) [Flat f] (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] : (S.map (pullback f)).ShortExact := by
  have := hS.mono_f
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (pullback f)).mp
    inferInstance S hS
  exact ShortComplex.ShortExact.mk' h.1 (f.mono_pullback_map_of_flat S.f) h.2

end

end AlgebraicGeometry.Scheme.Modules
