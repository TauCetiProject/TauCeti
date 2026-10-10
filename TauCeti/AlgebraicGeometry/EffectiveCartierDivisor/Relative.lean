/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.RingTheory.Flat.QuotientRegular
import TauCeti.Algebra.Regular.SMul

/-!
# Relative effective Cartier divisors

An effective Cartier divisor on `X` relative to `S` is an effective Cartier divisor whose
closed subscheme is flat over `S`. This file shows that relative effective Cartier divisors are
stable under arbitrary base change `T ⟶ S`, with no flatness assumption on `T ⟶ S` or on `X`
over `S`, so pullback along any `T ⟶ S` carries relative effective Cartier divisors on `X` over
`S` to relative effective Cartier divisors on `X ×_S T` over `T`. The base change may be taken
along any pullback square, which is what makes `T ↦ {relative effective Cartier divisors on
X ×_S T}` functorial in `T`.

Over affine opens `W ⊆ S` and `U ⊆ X` lying over it, a local equation `a` of the divisor is a
nonzerodivisor of `Γ(X, U)` with `Γ(X, U) ⧸ (a)` flat over `Γ(S, W)`. For an affine open `V` of
`T` over `W`, it therefore stays a nonzerodivisor in `Γ(X, U) ⊗[Γ(S, W)] Γ(T, V)`
(`Module.Flat.isSMulRegular_one_tmul_of_quotient_span_singleton`). There it is a local equation of
the pulled-back divisor on the open subscheme `Spec (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V))` of `X ×_S T`.

## Main results

* `Scheme.IdealSheafData.IsRelativeEffectiveCartier`: an effective Cartier divisor flat over
  the base.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_iff`: after arbitrary base change,
  relativity reduces to the effective Cartier condition on the pulled-back ideal.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap`: a relative effective Cartier
  divisor remains one after an arbitrary base change.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_flat`: it also remains one after
  pullback along a flat morphism `X' ⟶ X`, relative to the composite `X' ⟶ S`.
* `Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_isPullback`: base change along any
  pullback square, not only along the chosen fibre product `X ×_S T`.
* `Scheme.IdealSheafData.isRelativeEffectiveCartier_top`: the empty divisor is relative
  effective Cartier over every base.
* `Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_isEffectiveCartier`: over the spectrum of
  a field, every effective Cartier divisor is relative effective Cartier.

## References

* Stacks Project, *Divisors*, Relative effective Cartier divisors (stability under base change).
-/

public section

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- An effective Cartier divisor relative to `S` is an effective Cartier divisor whose closed
subscheme is flat over `S`. -/
def IsRelativeEffectiveCartier (I : X.IdealSheafData) (f : X ⟶ S) : Prop :=
  I.IsEffectiveCartier ∧ Flat (I.subschemeι ≫ f)

/-- A divisor is relative effective Cartier exactly when it is effective Cartier and its closed
subscheme is flat over the base. -/
theorem isRelativeEffectiveCartier_iff (I : X.IdealSheafData) (f : X ⟶ S) :
    I.IsRelativeEffectiveCartier f ↔ I.IsEffectiveCartier ∧ Flat (I.subschemeι ≫ f) :=
  Iff.rfl

/-- A relative effective Cartier divisor is an effective Cartier divisor on its ambient scheme. -/
theorem IsRelativeEffectiveCartier.isEffectiveCartier {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : I.IsEffectiveCartier :=
  hI.1

/-- The closed subscheme of a relative effective Cartier divisor is flat over the base. -/
theorem IsRelativeEffectiveCartier.flat {I : X.IdealSheafData} {f : X ⟶ S}
    (hI : I.IsRelativeEffectiveCartier f) : Flat (I.subschemeι ≫ f) :=
  hI.2

/-- If the original closed subscheme is flat over the base, its arbitrary base change is relative
effective Cartier if and only if the pulled-back ideal is effective Cartier. -/
theorem IsRelativeEffectiveCartier.comap_iff (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) [Flat (I.subschemeι ≫ f)] :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) ↔
      (I.comap (pullback.fst f g)).IsEffectiveCartier := by
  constructor
  · exact IsRelativeEffectiveCartier.isEffectiveCartier
  · exact fun h ↦ ⟨h, flat_comap_subschemeι_comp_snd I f g⟩

/-- **Relative effective Cartier divisors are stable under arbitrary base change.** If `I` is a
relative effective Cartier divisor on `X` over `S`, then for every morphism `g : T ⟶ S` its
pullback to `X ×_S T` is a relative effective Cartier divisor over `T`. Neither `g` nor `X ⟶ S`
need be flat. -/
theorem IsRelativeEffectiveCartier.comap {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).IsRelativeEffectiveCartier (pullback.snd f g) := by
  -- Flatness of the pulled-back subscheme is `comap_iff`. For the effective Cartier condition,
  -- each point `z` of `X ×_S T` lies in an open chart `Spec (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V))` on which
  -- the pulled-back ideal is generated by `a ⊗ 1` for a local equation `a` of `I`, and `a ⊗ 1`
  -- is a nonzerodivisor because `Γ(X, U) ⧸ (a)` is flat over `Γ(S, W)`.
  let _ : Flat (I.subschemeι ≫ f) := hI.flat
  rw [IsRelativeEffectiveCartier.comap_iff, isEffectiveCartier_iff_exists_isOpenImmersion]
  intro z
  -- Choose affine opens `W ⊆ S`, `U ⊆ f⁻¹ W` carrying an equation `a` of `I`, and `V ⊆ g⁻¹ W`,
  -- around the images of `z`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (pullback.fst f g z))) isOpen_univ
  replace hW : IsAffineOpen W := hW
  obtain ⟨U, hUW, hzU, a, ha, hUa⟩ :=
    hI.isEffectiveCartier.exists_eq_span_singleton_le (f ⁻¹ᵁ W) hzW
  have hU : IsAffineOpen U.1 := U.2
  have hzW' : g (pullback.snd f g z) ∈ W := by
    rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hzW' (g ⁻¹ᵁ W).isOpen
  replace hV : IsAffineOpen V := hV
  -- The fibre product of the three affine charts is `Spec (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V))`, and it
  -- is an open subscheme of `X ×_S T` containing `z`.
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let _ : Algebra Γ(S, W) Γ(T, V) := (g.appLE W V hVW).hom.toAlgebra
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W) Γ(X, U))) ≫ hW.fromSpec =
      hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hW hU hUW
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W) Γ(T, V))) ≫ hW.fromSpec =
      hV.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hW hV hVW
  let m := pullback.map _ _ f g hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂
  have : IsOpenImmersion m := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ e₁ e₂
  refine ⟨_, inferInstance, (pullbackSpecIso Γ(S, W) Γ(X, U) Γ(T, V)).inv ≫ m, inferInstance,
    ?_, (Scheme.ΓSpecIso _).inv (a ⊗ₜ 1), ?_, ?_⟩
  · have hz : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      exact ⟨by rwa [Set.mem_preimage, hU.range_fromSpec], by rwa [Set.mem_preimage,
        hV.range_fromSpec]⟩
    obtain ⟨w, rfl⟩ := hz
    exact ⟨(pullbackSpecIso Γ(S, W) Γ(X, U) Γ(T, V)).hom w, by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]⟩
  · -- The equation `a` stays a nonzerodivisor after base change, since `Γ(X, U) ⧸ (a)` is flat
    -- over `Γ(S, W)`.
    have hflat := I.flat_appLE_comp_ofHom_quotient_mk f hW U hUW
    rw [hUa] at hflat
    have : Module.Flat Γ(S, W) (Γ(X, U) ⧸ Ideal.span {a}) := by
      rw [← RingHom.flat_algebraMap_iff, IsScalarTower.algebraMap_eq Γ(S, W) Γ(X, U),
        Ideal.Quotient.algebraMap_eq]
      exact hflat
    have hreg := Module.Flat.isSMulRegular_one_tmul_of_quotient_span_singleton
      (R := Γ(S, W)) ha Γ(T, V)
    let t := (Algebra.TensorProduct.comm Γ(S, W) Γ(T, V) Γ(X, U)).toRingEquiv.trans
      (Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V)))).symm.commRingCatIsoToRingEquiv
    exact (TauCeti.isSMulRegular_map_iff t _).mpr hreg
  · have hφ : ((pullbackSpecIso Γ(S, W) Γ(X, U) Γ(T, V)).inv ≫ m) ≫ pullback.fst f g =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hU.fromSpec := by
      simp [m]
    rw [← comap_comp, hφ, comap_comp, comap_fromSpec_eq_ofIdealTop, comap_ofIdealTop, hUa]
    simp only [Ideal.map_span, Set.image_singleton]
    have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) ⟶
        CommRingCat.of (Γ(X, U) ⊗[Γ(S, W)] Γ(T, V)))).hom a)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Algebra.TensorProduct.includeLeftRingHom_apply] at h
    exact congrArg (fun r ↦ ofIdealTop (Ideal.span {r})) h.symm

/-- **Flat pullback of relative effective Cartier divisors.** If `I` is a relative effective
Cartier divisor on `X` over `S` and `g : X' ⟶ X` is flat, then the pullback of `I` to `X'` is a
relative effective Cartier divisor over `S` through `g ≫ f`. -/
theorem IsRelativeEffectiveCartier.comap_of_flat {X' : Scheme.{u}} {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) (g : X' ⟶ X) [Flat g] :
    (I.comap g).IsRelativeEffectiveCartier (g ≫ f) := by
  refine (isRelativeEffectiveCartier_iff _ _).mpr ⟨hI.isEffectiveCartier.comap g, ?_⟩
  -- The closed subscheme of the pullback is the base change of `I.subschemeι` along `g`, so its
  -- morphism to `S` factors through the flat base change of `g` and the flat `I.subschemeι ≫ f`.
  have := hI.flat
  rw [← comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
  infer_instance

/-- **Relative effective Cartier divisors are stable under base change along a pullback
square.** Given a pullback square with `g' : X' ⟶ X` over `g : T ⟶ S`, the pullback along `g'` of
a relative effective Cartier divisor on `X` over `S` is a relative effective Cartier divisor on
`X'` over `T`. -/
theorem IsRelativeEffectiveCartier.comap_of_isPullback {X' : Scheme.{u}} {I : X.IdealSheafData}
    {f : X ⟶ S} (hI : I.IsRelativeEffectiveCartier f) {g : T ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T}
    (h : IsPullback g' f' f g) : (I.comap g').IsRelativeEffectiveCartier f' := by
  have := (hI.comap g).comap_of_flat h.isoPullback.hom
  rwa [← comap_comp, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd] at this

/-- The empty closed subscheme is a relative effective Cartier divisor over every base. -/
@[simp]
theorem isRelativeEffectiveCartier_top (f : X ⟶ S) :
    (⊤ : X.IdealSheafData).IsRelativeEffectiveCartier f :=
  (isRelativeEffectiveCartier_iff _ _).mpr ⟨isEffectiveCartier_top X, inferInstance⟩

/-- Over the spectrum of a field, flatness over the base is automatic, so the relative effective
Cartier divisors are exactly the effective Cartier divisors. -/
@[simp]
theorem isRelativeEffectiveCartier_iff_isEffectiveCartier [Subsingleton S] [IsIntegral S]
    (I : X.IdealSheafData) (f : X ⟶ S) :
    I.IsRelativeEffectiveCartier f ↔ I.IsEffectiveCartier := by
  rw [isRelativeEffectiveCartier_iff]
  exact ⟨And.left, fun h ↦ ⟨h, inferInstance⟩⟩

end AlgebraicGeometry.Scheme.IdealSheafData
