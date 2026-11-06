/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.ElementaryEtale.Basic
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Persistence of elementary étale localization

An open finite neighbourhood isolated over a point, whose distinguished point has unchanged
residue field over the original source, remains such a neighbourhood after a further base change
which preserves the residue field at the base point. In particular, the neighbourhoods in
elementary étale localization can be refined by further elementary étale neighbourhoods.

`Scheme.Hom.exists_finite_open_baseChange` gives the open in the new fibre product, its unique
point over the distinguished base point, and the unchanged residue field over the original source.
The base change need not be étale: only its residue field map at the distinguished point must be
an isomorphism.

## References

* [Stacks Project, Lemma 37.41.1](https://stacks.math.columbia.edu/tag/02LK),
  the persistence assertion for elementary étale neighbourhoods.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Given an open finite neighbourhood `V` whose unique point `v` over `u` has unchanged residue
field over `X`, any base change preserving the residue field at `u` yields such a neighbourhood
with a unique distinguished point and unchanged residue field over `X`. This is the persistence
assertion in Stacks, Lemma 37.41.1; neither the original nor the further base change needs to be
étale. -/
@[stacks 02LK "persistence under further elementary étale neighbourhoods"]
theorem Scheme.Hom.exists_finite_open_baseChange {X S U U' : Scheme.{u}}
    (f : X ⟶ S) (φ : U ⟶ S) (V : (pullback f φ).Opens) (v : V.toScheme) (u : U)
    [IsFinite (V.ι ≫ pullback.snd f φ)]
    (hv : (V.ι ≫ pullback.snd f φ) v = u)
    (hunique : ∀ w : V.toScheme, (V.ι ≫ pullback.snd f φ) w = u → w = v)
    [IsIso ((pullback.fst f φ).residueFieldMap (V.ι v))]
    (ψ : U' ⟶ U) (u' : U') (hu' : ψ u' = u) [IsIso (ψ.residueFieldMap u')] :
    ∃ (W : (pullback f (ψ ≫ φ)).Opens) (v' : W.toScheme),
      IsFinite (W.ι ≫ pullback.snd f (ψ ≫ φ)) ∧
      (W.ι ≫ pullback.fst f (ψ ≫ φ)) v' = (V.ι ≫ pullback.fst f φ) v ∧
      (W.ι ≫ pullback.snd f (ψ ≫ φ)) v' = u' ∧
      IsIso ((pullback.fst f (ψ ≫ φ)).residueFieldMap (W.ι v')) ∧
      ∀ w : W.toScheme, (W.ι ≫ pullback.snd f (ψ ≫ φ)) w = u' → w = v' := by
  let g := V.ι ≫ pullback.snd f φ
  -- The pullback of `V` is an open in the new fibre product by pullback pasting.
  let a := pullback.map g ψ (pullback.snd f φ) ψ V.ι (𝟙 U') (𝟙 U)
    (by simp [g]) (by simp)
  have : IsOpenImmersion a := Scheme.pullback_map_isOpenImmersion ..
  let j := a ≫ (pullbackLeftPullbackSndIso f φ ψ).hom
  have : IsOpenImmersion j := inferInstance
  have hjfst : j ≫ pullback.fst f (ψ ≫ φ) =
      pullback.fst g ψ ≫ V.ι ≫ pullback.fst f φ := by simp [j, a]
  have hjsnd : j ≫ pullback.snd f (ψ ≫ φ) = pullback.snd g ψ := by simp [j, a]
  obtain ⟨z, hzv, hzu⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := ψ)
    v u' (hv.trans hu'.symm)
  have : IsIso (ψ.residueFieldMap (pullback.snd g ψ z)) := hzu ▸ inferInstance
  have : IsIso ((pullback.fst g ψ).residueFieldMap z) :=
    Scheme.Pullback.isIso_residueFieldMap_fst (f := g) (g := ψ) z
  -- Uniqueness uses the old singleton fibre and the unchanged residue field of `ψ`.
  have hzunique (w : ↑(pullback g ψ)) (hw : pullback.snd g ψ w = u') : w = z := by
    have hwv : pullback.fst g ψ w = v := hunique _ <| by
      have h := congr($(pullback.condition (f := g) (g := ψ)) w)
      rw [Scheme.Hom.comp_apply (g := g), Scheme.Hom.comp_apply (g := ψ), hw, hu'] at h
      exact h
    exact Scheme.Pullback.eq_of_fst_eq_snd_eq_of_isIso
      (hwv.trans hzv.symm) (hw.trans hzu.symm)
  let W := j.opensRange
  have hfinite : IsFinite (W.ι ≫ pullback.snd f (ψ ≫ φ)) := by
    have : MorphismProperty.RespectsIso @IsFinite.{u} :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange j).hom, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjsnd]
    infer_instance
  let e : pullback g ψ ≅ W.toScheme := Scheme.Hom.isoOpensRange j
  have hej : e.hom ≫ W.ι = j := Scheme.Hom.isoOpensRange_hom_ι j
  have hejz : W.ι (e.hom z) = j z := by rw [← Scheme.Hom.comp_apply, hej]
  refine ⟨W, e.hom z, hfinite, ?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hej, hjfst,
      Scheme.Hom.comp_apply, hzv]
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hej, hjsnd]
    exact hzu
  · -- Cancel the residue field isomorphism of the open immersion `j`.
    have hr : IsIso ((pullback.fst f φ).residueFieldMap (V.ι (pullback.fst g ψ z))) := by
      rw [hzv]
      infer_instance
    have : IsIso ((j ≫ pullback.fst f (ψ ≫ φ)).residueFieldMap z) := by
      rw [Scheme.Hom.residueFieldMap_congr hjfst, isIso_comp_left_iff,
        Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' (IsIso.comp_isIso' hr inferInstance) inferInstance
    rw [hejz]
    exact j.isIso_residueFieldMap_of_comp (pullback.fst f (ψ ≫ φ)) z
  · intro w hw
    obtain ⟨t, rfl⟩ := (Scheme.homeoOfIso e).surjective w
    have htu : pullback.snd g ψ t = u' := by
      rw [Scheme.homeoOfIso_apply, ← Scheme.Hom.comp_apply, ← Category.assoc, hej,
        hjsnd] at hw
      exact hw
    exact congrArg e.hom (hzunique t htu)

end AlgebraicGeometry
