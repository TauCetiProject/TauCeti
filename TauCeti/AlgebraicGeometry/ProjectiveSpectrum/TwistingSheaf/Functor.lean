/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic

/-!
# Functoriality of the twisting sheaves

Let `f : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism with `ℬ₊ ≤ 𝒜₊.map f`, so that Mathlib's
`AlgebraicGeometry.Proj.map f hf : Proj ℬ ⟶ Proj 𝒜` is defined. This file constructs the induced
morphism of twisting sheaves

`𝒪_{Proj 𝒜}(n) ⟶ (Proj.map f hf)_* 𝒪_{Proj ℬ}(n)`

(`AlgebraicGeometry.Proj.twistingSheafMap`), for every `n ∈ ℤ`. On sections it sends a local
fraction `x ↦ s x ∈ A_x` to `y ↦ f(s(f⁻¹ y)) ∈ B_y`, through the maps of localizations
`A_{f⁻¹ y} → B_y` induced by `f`; a fraction `r / s` goes to `f r / f s`. It is linear over the
map of structure sheaves of `Proj.map f hf`, compatible with the multiplication of sections of
twisting sheaves and with the sections `r / 1`, so the graded maps `A → ⨁ₙ Γ(Proj A, 𝒪(n))` are
natural in `f`. It is also compatible with composition of graded ring homomorphisms.

These maps are the transition maps for gluing the twisting sheaves of the charts
`Proj (⨁ n, Γ(Aₙ, U))` of a relative `Proj`, whose transition maps are `Proj.map` of restriction
of sections.

The construction follows Mathlib's `AlgebraicGeometry.Proj.comapStructureSheaf` in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` (Kenny Lau), which does the same for
the structure sheaf.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.localizationsMap f hf y`: the map of
  localizations `A_{f⁻¹ y} → B_y` at a point `y` of `Proj ℬ`.
* `AlgebraicGeometry.Proj.twistingSheaf.comap f hf hUV`: the map
  `Γ(U, 𝒪_{Proj 𝒜}(n)) → Γ(V, 𝒪_{Proj ℬ}(n))` for `V` contained in the preimage of `U`.
* `AlgebraicGeometry.Proj.twistingSheafMap f hf n`: the morphism of sheaves of modules
  `𝒪_{Proj 𝒜}(n) ⟶ (Proj.map f hf)_* 𝒪_{Proj ℬ}(n)`.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.comap_smul`: the map on sections is linear over the map of
  structure sheaves.
* `AlgebraicGeometry.Proj.twistingSheaf.comap_const`, `AlgebraicGeometry.Proj.comap_toTwistingSheaf`
  and `AlgebraicGeometry.Proj.twistingSheaf.comap_mul`: compatibility with fractions, with the
  sections `r / 1` and with multiplication.
* `AlgebraicGeometry.Proj.twistingSheafMap_comp` and `AlgebraicGeometry.Proj.twistingSheafMap_id`:
  compatibility with composition and identities.

## References

* The Stacks Project, Section 27.11, Functoriality of Proj.
-/

public section

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace HomogeneousIdeal ProjectiveSpectrum.TwistingSheaf

universe u

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {n : ℤ}

namespace ProjectiveSpectrum.TwistingSheaf

/-- The map of localizations `A_{f⁻¹ y} → B_y` induced by `f`, at a point `y` of `Proj ℬ`. -/
def localizationsMap (y : ProjectiveSpectrum ℬ) :
    Localizations 𝒜 (ProjectiveSpectrum.comap f hf y) →+* Localizations ℬ y :=
  Localization.localRingHom _ _ f rfl

/-- The map of localizations sends the fraction `r / s` to `f r / f s`. -/
@[simp]
theorem localizationsMap_mk (y : ProjectiveSpectrum ℬ) (r : A)
    (s : (ProjectiveSpectrum.comap f hf y).asHomogeneousIdeal.toIdeal.primeCompl) :
    localizationsMap f hf y (Localization.mk r s) = Localization.mk (f r) ⟨f s, s.2⟩ :=
  Localization.localRingHom_mk ..

/-- The maps of localizations `A_{f⁻¹ y} → B_y` restrict to the maps of homogeneous localizations
through which `Proj.map f hf` acts on the structure sheaves. Stated at a point of
`ProjectiveSpectrum ℬ`, where instance search finds that the ideal of `y` is prime, which it does
not for points of the underlying space of `Proj ℬ`. -/
theorem val_localRingHom (y : ProjectiveSpectrum ℬ)
    (a : HomogeneousLocalization.AtPrime 𝒜
      (ProjectiveSpectrum.comap f hf y).asHomogeneousIdeal.toIdeal) :
    (HomogeneousLocalization.localRingHom f _ _ rfl a).val = localizationsMap f hf y a.val :=
  HomogeneousLocalization.val_localRingHom a

/-- The maps of localizations are compatible with composition of graded ring homomorphisms. -/
theorem localizationsMap_comp (g : ℬ →+*ᵍ 𝒞) (hg : 𝒞₊ ≤ ℬ₊.map g) (z : ProjectiveSpectrum 𝒞) :
    localizationsMap (g.comp f) (irrelevant_le_map_comp hf hg) z =
      (localizationsMap g hg z).comp (localizationsMap f hf (ProjectiveSpectrum.comap g hg z)) :=
  Localization.localRingHom_comp _ _ _ _ rfl _ rfl

/-- The map of localizations induced by the identity is the identity. -/
@[simp]
theorem localizationsMap_id (x : ProjectiveSpectrum 𝒜)
    (a : Localizations 𝒜 (ProjectiveSpectrum.comap (GradedRingHom.id 𝒜) (by simp) x)) :
    localizationsMap (GradedRingHom.id 𝒜) (by simp) x a = a := by
  induction a using Localization.induction_on with
  | H x => exact localizationsMap_mk ..

variable {U : Opens (ProjectiveSpectrum.top 𝒜)} {V : Opens (ProjectiveSpectrum.top ℬ)}
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

/-- The pullback of a dependent function on `U` into the localizations along `f`: the value at
`y ∈ V` is the image of the value at `f⁻¹ y` under `A_{f⁻¹ y} → B_y`. -/
def comapFun (s : ∀ x : U, Localizations 𝒜 x.1) (y : V) : Localizations ℬ y.1 :=
  localizationsMap f hf y.1 (s ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩)

variable {f hf hUV} in
/-- The pullback of a local fraction of degree `n` is a local fraction of degree `n`. -/
theorem isLocallyFraction_comapFun {s : ∀ x : U, Localizations 𝒜 x.1}
    (hs : (isLocallyFraction 𝒜 n).pred s) :
    (isLocallyFraction ℬ n).pred (comapFun f hf hUV s) := by
  rintro ⟨y, hyV⟩
  obtain ⟨W, m, iWU, i, j, h, r, t, ht, w⟩ := hs ⟨ProjectiveSpectrum.comap f hf y, hUV hyV⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hyV⟩, homOfLE inf_le_right, i, j, h,
    ⟨f r, Graded.map_mem f r.2⟩, ⟨f t, Graded.map_mem f t.2⟩,
    fun z ↦ ht ⟨ProjectiveSpectrum.comap f hf z.1, z.2.1⟩, fun z ↦ ?_⟩
  exact (congrArg (localizationsMap f hf z.1) (w ⟨_, z.2.1⟩)).trans (localizationsMap_mk ..)

end ProjectiveSpectrum.TwistingSheaf

end universe_polymorphic

section universe_monomorphic

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {n : ℤ}

namespace Proj

namespace twistingSheaf

variable {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens}
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

/-- **Pullback of sections of twisting sheaves** along `Proj.map f hf : Proj ℬ ⟶ Proj 𝒜`: for
`V` contained in the preimage of `U`, the map `Γ(U, 𝒪_{Proj 𝒜}(n)) → Γ(V, 𝒪_{Proj ℬ}(n))`
applying the maps of localizations `A_{f⁻¹ y} → B_y` induced by `f` pointwise. -/
def comap : Γ(twistingSheaf 𝒜 n, U) →+ Γ(twistingSheaf ℬ n, V) where
  toFun s := ⟨comapFun f hf hUV s.1, isLocallyFraction_comapFun s.2⟩
  map_zero' := ext fun _ ↦ map_zero _
  map_add' _ _ := ext fun _ ↦ map_add _ _ _

/-- The value of a pulled-back section at `y` is the image of the value at `f⁻¹ y`. -/
@[simp]
theorem comap_apply (s : Γ(twistingSheaf 𝒜 n, U)) (y : V) :
    (comap f hf hUV s).1 y =
      localizationsMap f hf y.1 (s.1 ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩) :=
  (rfl)

/-- The pullback of sections commutes with restriction. -/
@[simp]
theorem res_comap {V' : (Proj ℬ).Opens} (i : V' ⟶ V) (s : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf ℬ n).presheaf.map i.op (comap f hf hUV s) =
      comap f hf (fun _ hy ↦ hUV (i.le hy)) s :=
  (rfl)

/-- Pulling back the restriction of a section is pulling back the section. -/
@[simp]
theorem comap_res {U' : (Proj 𝒜).Opens} (i : U' ⟶ U)
    (hU'V : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U'.1) (s : Γ(twistingSheaf 𝒜 n, U)) :
    comap f hf hU'V ((twistingSheaf 𝒜 n).presheaf.map i.op s) =
      comap f hf (fun _ hy ↦ i.le (hU'V hy)) s :=
  (rfl)

/-- The value at `y` of the image of a section `a` of the structure sheaf under `Proj.map f hf`,
in the localization `B_y`, is the image of the value of `a` at `f⁻¹ y`. This holds by unfolding
`Proj.map`, whose map of structure sheaves is Mathlib's `Proj.comapStructureSheaf`, applying
`HomogeneousLocalization.localRingHom` pointwise. -/
theorem val_map_appLE_apply (a : Γ(Proj 𝒜, U)) (y : V) :
    (((map f hf).appLE U V hUV a).1 y).val = localizationsMap f hf y.1 (a.1 ⟨_, hUV y.2⟩).val :=
  val_localRingHom f hf y.1 _

/-- **The pullback of sections is linear over the map of structure sheaves.** -/
theorem comap_smul (a : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 n, U)) :
    comap f hf hUV (a • s) = (map f hf).appLE U V hUV a • comap f hf hUV s :=
  ext fun _ ↦ ((comap_apply ..).trans <| (congrArg _ (smul_apply ..)).trans (map_mul ..)).trans <|
    (congrArg₂ (· * ·) (val_map_appLE_apply ..).symm (comap_apply ..).symm).trans
      (smul_apply ..).symm

/-- The pullback of a fraction `r / s` is the fraction `f r / f s`. -/
@[simp]
theorem comap_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) :
    comap f hf hUV (const h r s hr hs U hU) =
      const h (f r) (f s) (Graded.map_mem f hr) (Graded.map_mem f hs) V
        (hUV.trans fun _ hy ↦ hU hy) :=
  ext fun y ↦ (comap_apply ..).trans <| (congrArg _ (const_apply ..)).trans <|
    (localizationsMap_mk ..).trans
      (const_apply h (f r) (f s) (Graded.map_mem f hr) (Graded.map_mem f hs)
        (hUV.trans fun _ hy ↦ hU hy) y).symm

/-- The pullback of sections is multiplicative. -/
@[simp]
theorem comap_mul {m : ℤ} (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U)) :
    comap f hf hUV (mul 𝒜 U m n s t) = mul ℬ V m n (comap f hf hUV s) (comap f hf hUV t) :=
  ext fun _ ↦ (comap_apply ..).trans <| (congrArg _ (mul_apply ..)).trans <|
    (map_mul ..).trans <| (congrArg₂ (· * ·) (comap_apply ..).symm (comap_apply ..).symm).trans
      (mul_apply (comap f hf hUV s) (comap f hf hUV t) _).symm

end twistingSheaf

open twistingSheaf

/-- The sections `r / 1` pull back to the sections `f r / 1`: the graded maps
`A → ⨁ₙ Γ(Proj A, 𝒪(n))` are natural in `f`. -/
@[simp]
theorem comap_toTwistingSheaf {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens}
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1) {j : ℕ} (h : (j : ℤ) = n) (r : 𝒜 j) :
    comap f hf hUV (toTwistingSheaf 𝒜 h U r) =
      toTwistingSheaf ℬ h V ⟨f r, Graded.map_mem f r.2⟩ := by
  rw [toTwistingSheaf_eq_const, comap_const, toTwistingSheaf_eq_const]
  exact const_ext (by rw [map_one])

/-- **The morphism of twisting sheaves induced by a graded ring homomorphism**: the morphism
`𝒪_{Proj 𝒜}(n) ⟶ (Proj.map f hf)_* 𝒪_{Proj ℬ}(n)` of sheaves of modules on `Proj 𝒜`, given on
sections over `U` by `AlgebraicGeometry.Proj.twistingSheaf.comap`. -/
def twistingSheafMap (n : ℤ) :
    twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (map f hf)).obj (twistingSheaf ℬ n) where
  val :=
    { app U := ModuleCat.ofHom (X := (twistingSheaf 𝒜 n).val.obj U)
        (Y := ((Scheme.Modules.pushforward (map f hf)).obj (twistingSheaf ℬ n)).val.obj U)
        { toFun := comap f hf (U := U.unop) Set.Subset.rfl
          map_add' := map_add _
          map_smul' := comap_smul f hf Set.Subset.rfl }
      naturality _ := rfl }

/-- On sections over `U`, the morphism of twisting sheaves is the pullback of sections to the
preimage of `U`. -/
@[simp]
theorem twistingSheafMap_app (U : (Proj 𝒜).Opens) :
    Scheme.Modules.Hom.app (twistingSheafMap f hf n) U =
      AddCommGrpCat.ofHom (comap f hf (U := U) Set.Subset.rfl) :=
  (rfl)

/-- **The morphisms of twisting sheaves are compatible with composition**: under
`Proj.map (g.comp f) = Proj.map g ≫ Proj.map f`, the morphism induced by `g.comp f` is the
morphism induced by `f` followed by the pushforward of the morphism induced by `g`. -/
theorem twistingSheafMap_comp (g : ℬ →+*ᵍ 𝒞) (hg : 𝒞₊ ≤ ℬ₊.map g) (n : ℤ) :
    twistingSheafMap (g.comp f) (irrelevant_le_map_comp hf hg) n ≫
        (Scheme.Modules.pushforwardCongr (map_comp f g hf hg)).hom.app (twistingSheaf 𝒞 n) =
      twistingSheafMap f hf n ≫
        (Scheme.Modules.pushforward (map f hf)).map (twistingSheafMap g hg n) ≫
          (Scheme.Modules.pushforwardComp (map g hg) (map f hf)).hom.app (twistingSheaf 𝒞 n) := by
  ext U s : 3
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  -- The remaining identity and `eqToHom` restriction maps act trivially on values.
  exact twistingSheaf.ext fun z ↦ DFunLike.congr_fun (localizationsMap_comp f hf g hg z.1) _

/-- **The morphism of twisting sheaves induced by the identity is the identity**, under
`Proj.map (GradedRingHom.id 𝒜) = 𝟙 (Proj 𝒜)`. -/
theorem twistingSheafMap_id (n : ℤ) :
    twistingSheafMap (GradedRingHom.id 𝒜) (by simp) n ≫
        (Scheme.Modules.pushforwardCongr map_id).hom.app (twistingSheaf 𝒜 n) ≫
          (Scheme.Modules.pushforwardId (Proj 𝒜)).hom.app (twistingSheaf 𝒜 n) = 𝟙 _ := by
  ext U s : 3
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardId_hom_app_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_id, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  -- The remaining identity and `eqToHom` restriction maps act trivially on values.
  exact twistingSheaf.ext fun x ↦ localizationsMap_id x.1 _

end Proj

end universe_monomorphic

end AlgebraicGeometry
