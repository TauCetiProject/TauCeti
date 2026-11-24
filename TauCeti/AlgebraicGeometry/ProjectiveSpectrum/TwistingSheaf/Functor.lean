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
* `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.comapFun`: the pointwise pullback of
  localization-valued functions along a continuous map and a ring homomorphism contracting prime
  ideals. `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.isLocallyFraction_comapFun` proves
  preservation of local fractions with a specified degree change, and
  `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.comapFun_const` evaluates it on fractions;
  together they also give the pullback along `Proj A ≅ Proj A^{(d)}` for a Veronese subalgebra.
* `AlgebraicGeometry.Proj.twistingSheaf.comap f hf hUV`: the map
  `Γ(U, 𝒪_{Proj 𝒜}(n)) → Γ(V, 𝒪_{Proj ℬ}(n))` for `V` contained in the preimage of `U`.
* `AlgebraicGeometry.Proj.twistingSheafMap f hf n`: the morphism of sheaves of modules
  `𝒪_{Proj 𝒜}(n) ⟶ (Proj.map f hf)_* 𝒪_{Proj ℬ}(n)`.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.comap_smul`: the map on sections is linear over the map of
  structure sheaves.
* `AlgebraicGeometry.Proj.twistingSheaf.comap_const`, `AlgebraicGeometry.Proj.comap_toTwistingSheaf`
  and `AlgebraicGeometry.Proj.twistingSheaf.comap_mul`: compatibility with fractions, with the
  sections `r / 1` and with multiplication, with `AlgebraicGeometry.Proj.twistingSheafMap_app_mul`
  and `AlgebraicGeometry.Proj.res_twistingSheafMap_app_mul` the forms of the last for the
  morphism of twisting sheaves.
* `AlgebraicGeometry.Proj.twistingSheafMap_comp` and `AlgebraicGeometry.Proj.twistingSheafMap_id`:
  compatibility with composition and identities, with the sectionwise forms
  `AlgebraicGeometry.Proj.twistingSheafMap_app_apply_of_eq_comp` and
  `AlgebraicGeometry.Proj.twistingSheafMap_app_apply_of_eq_id` for graded homomorphisms only
  propositionally equal to a composite or to the identity.
* `AlgebraicGeometry.Proj.res_twistingSheafMap_app_res_of_comp_eq`: the morphisms along two equal
  composites agree on sections, up to restrictions to a common open.

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
    localizationsMap f hf y (Localization.mk r s) = Localization.mk (f r) ⟨f s, s.property⟩ :=
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

/-- The pullback of a dependent function on `U` into the localizations along a continuous map
`φ : Proj ℬ → Proj 𝒜` and a ring homomorphism `g : A →+* B` contracting the prime ideal of each
point `y` to that of `φ y`: the value at `y ∈ V` is the image of the value at `φ y` under the map
of localizations `A_{φ y} → B_y` induced by `g`. For `Proj.map f hf` this is `φ = f⁻¹` and
`g = f`. -/
def comapFun (φ : C(ProjectiveSpectrum.top ℬ, ProjectiveSpectrum.top 𝒜)) (g : A →+* B)
    (hφ : ∀ y, (φ y).asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap g)
    {U : Opens (ProjectiveSpectrum.top 𝒜)} {V : Opens (ProjectiveSpectrum.top ℬ)}
    (hUV : V.carrier ⊆ φ ⁻¹' U.carrier) (s : ∀ x : U, Localizations 𝒜 x.val) (y : V) :
    Localizations ℬ y.val :=
  Localization.localRingHom _ _ g (hφ y.val) (s ⟨φ y.val, hUV y.property⟩)

/-- The value of a pulled-back function is the image of its value at the corresponding point
under the induced map of localizations. -/
@[simp]
theorem comapFun_apply (φ : C(ProjectiveSpectrum.top ℬ, ProjectiveSpectrum.top 𝒜)) (g : A →+* B)
    (hφ : ∀ y, (φ y).asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap g)
    {U : Opens (ProjectiveSpectrum.top 𝒜)} {V : Opens (ProjectiveSpectrum.top ℬ)}
    (hUV : V.carrier ⊆ φ ⁻¹' U.carrier) (s : ∀ x : U, Localizations 𝒜 x.val) (y : V) :
    comapFun φ g hφ hUV s y =
      Localization.localRingHom _ _ g (hφ y.val) (s ⟨φ y.val, hUV y.property⟩) :=
  (rfl)

/-- If `g` sends `𝒜 i` into `ℬ (δ i)` for a map `δ : ℕ → ℕ` sending degree differences `n` to
`n'`, the pullback of a local fraction of degree `n` is a local fraction of degree `n'`. -/
theorem isLocallyFraction_comapFun {φ : C(ProjectiveSpectrum.top ℬ, ProjectiveSpectrum.top 𝒜)}
    {g : A →+* B}
    {hφ : ∀ y, (φ y).asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap g}
    {U : Opens (ProjectiveSpectrum.top 𝒜)} {V : Opens (ProjectiveSpectrum.top ℬ)}
    {hUV : V.carrier ⊆ φ ⁻¹' U.carrier} {δ : ℕ → ℕ} (hδ : ∀ i ⦃a : A⦄, a ∈ 𝒜 i → g a ∈ ℬ (δ i))
    {n' : ℤ} (hn : ∀ i j : ℕ, (j : ℤ) = i + n → (δ j : ℤ) = δ i + n')
    {s : ∀ x : U, Localizations 𝒜 x.val} (hs : (isLocallyFraction 𝒜 n).pred s) :
    (isLocallyFraction ℬ n').pred (comapFun φ g hφ hUV s) := by
  rintro ⟨y, hyV⟩
  obtain ⟨W, m, iWU, i, j, h, r, t, ht, w⟩ := hs ⟨φ y, hUV hyV⟩
  refine ⟨W.comap φ ⊓ V, ⟨m, hyV⟩, homOfLE inf_le_right, δ i, δ j, hn i j h,
    ⟨g r, hδ j r.property⟩, ⟨g t, hδ i t.property⟩,
    fun z hz ↦ ht ⟨φ z.val, z.property.1⟩ (by rw [hφ, Ideal.mem_comap]; exact hz), fun z ↦ ?_⟩
  exact (comapFun_apply ..).trans <|
    (congrArg (Localization.localRingHom _ _ g (hφ z.val)) (w ⟨_, z.property.1⟩)).trans
      (Localization.localRingHom_mk ..)

end ProjectiveSpectrum.TwistingSheaf

end universe_polymorphic

section universe_monomorphic

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {n : ℤ}

namespace ProjectiveSpectrum.TwistingSheaf

/-- If `g` sends `𝒜 i` into `ℬ (δ i)` for a map `δ : ℕ → ℕ` sending degree differences `n` to
`n'`, the pullback of the fraction `r / s` of degree `n` is the fraction `g r / g s` of degree
`n'`. -/
theorem comapFun_const {φ : C(ProjectiveSpectrum.top ℬ, ProjectiveSpectrum.top 𝒜)}
    {g : A →+* B}
    (hφ : ∀ y, (φ y).asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap g)
    {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens} (hUV : V.carrier ⊆ φ ⁻¹' U.carrier) {δ : ℕ → ℕ}
    (hδ : ∀ i ⦃a : A⦄, a ∈ 𝒜 i → g a ∈ ℬ (δ i)) {n' : ℤ}
    (hn : ∀ i j : ℕ, (j : ℤ) = i + n → (δ j : ℤ) = δ i + n') {i j : ℕ} (h : (j : ℤ) = i + n)
    (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) (hU : U ≤ Proj.basicOpen 𝒜 s) (y : V) :
    comapFun φ g hφ hUV (Proj.twistingSheaf.const h r s hr hs U hU).val y =
      (Proj.twistingSheaf.const (hn i j h) (g r) (g s) (hδ j hr) (hδ i hs) V
        fun z hz hsz ↦ hU (hUV hz) ((SetLike.ext_iff.mp (hφ z) s).mpr hsz)).val y :=
  -- `@`: instance search does not find that ideals of points of `Proj` are prime
  (comapFun_apply ..).trans (@Localization.localRingHom_mk ..)

end ProjectiveSpectrum.TwistingSheaf

namespace Proj

namespace twistingSheaf

variable {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens}
  (hUV : V.carrier ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.carrier)

/-- **Pullback of sections of twisting sheaves** along `Proj.map f hf : Proj ℬ ⟶ Proj 𝒜`: for
`V` contained in the preimage of `U`, the map `Γ(U, 𝒪_{Proj 𝒜}(n)) → Γ(V, 𝒪_{Proj ℬ}(n))`
applying the maps of localizations `A_{f⁻¹ y} → B_y` induced by `f` pointwise. -/
def comap : Γ(twistingSheaf 𝒜 n, U) →+ Γ(twistingSheaf ℬ n, V) where
  toFun s := ⟨comapFun (ProjectiveSpectrum.comap f hf) f (fun _ ↦ rfl) hUV s.val,
    isLocallyFraction_comapFun (δ := fun i ↦ i) (fun _ _ ha ↦ Graded.map_mem f ha) (fun _ _ h ↦ h)
      s.property⟩
  map_zero' := ext fun _ ↦ (comapFun_apply _ _ (fun _ ↦ rfl) hUV ..).trans (map_zero _)
  -- Section addition reduces pointwise here. `add_apply` does not unify with the codomain's
  -- inferred addition through the unexposed localization addition instance.
  map_add' _ _ := ext fun _ ↦ (comapFun_apply _ _ (fun _ ↦ rfl) hUV ..).trans
    ((map_add _ _ _).trans (congrArg₂ (· + ·) (comapFun_apply _ _ (fun _ ↦ rfl) hUV ..).symm
      (comapFun_apply _ _ (fun _ ↦ rfl) hUV ..).symm))

/-- The value of a pulled-back section at `y` is the image of the value at `f⁻¹ y`. -/
@[simp]
theorem comap_apply (s : Γ(twistingSheaf 𝒜 n, U)) (y : V) :
    (comap f hf hUV s).val y =
      localizationsMap f hf y.val (s.val (⟨ProjectiveSpectrum.comap f hf y.val,
          hUV y.property⟩ : U)) :=
  comapFun_apply _ _ (fun _ ↦ rfl) hUV ..

/-- The pullback of sections commutes with restriction. -/
@[simp]
theorem res_comap {V' : (Proj ℬ).Opens} (i : V' ⟶ V) (s : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf ℬ n).presheaf.map i.op (comap f hf hUV s) =
      comap f hf (fun _ hy ↦ hUV (i.le hy)) s :=
  (rfl)

/-- Pulling back the restriction of a section is pulling back the section. -/
@[simp]
theorem comap_res {U' : (Proj 𝒜).Opens} (i : U' ⟶ U)
    (hU'V : V.carrier ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U'.carrier) (s : Γ(twistingSheaf 𝒜 n,
        U)) :
    comap f hf hU'V ((twistingSheaf 𝒜 n).presheaf.map i.op s) =
      comap f hf (fun _ hy ↦ i.le (hU'V hy)) s :=
  (rfl)

/-- The value at `y` of the image of a section `a` of the structure sheaf under `Proj.map f hf`,
in the localization `B_y`, is the image of the value of `a` at `f⁻¹ y`. This holds by unfolding
`Proj.map`, whose map of structure sheaves is Mathlib's `Proj.comapStructureSheaf`, applying
`HomogeneousLocalization.localRingHom` pointwise. -/
theorem val_map_appLE_apply (a : Γ(Proj 𝒜, U)) (y : V) :
    (((map f hf).appLE U V hUV a).val y).val = localizationsMap f hf y.val (a.val ⟨_,
        hUV y.property⟩).val :=
  val_localRingHom f hf y.val _

/-- **The pullback of sections is linear over the map of structure sheaves.** -/
theorem comap_smul (a : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 n, U)) :
    comap f hf hUV (a • s) = (map f hf).appLE U V hUV a • comap f hf hUV s := by
  refine ext fun (y : V) ↦ ?_
  simp only [comap_apply, smul_apply, map_mul, val_map_appLE_apply]
  -- The two sides differ only in which `Opens` type the point `f⁻¹ y` is ascribed to.
  rfl

/-- The pullback of a fraction `r / s` is the fraction `f r / f s`. -/
@[simp]
theorem comap_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) :
    comap f hf hUV (const h r s hr hs U hU) =
      const h (f r) (f s) (Graded.map_mem f hr) (Graded.map_mem f hs) V
        (hUV.trans fun _ hy ↦ hU hy) :=
  ext <| comapFun_const (fun _ ↦ rfl) hUV (δ := fun i ↦ i) (fun _ _ ha ↦ Graded.map_mem f ha)
    (fun _ _ h ↦ h) h r s hr hs hU

/-- The pullback of sections is multiplicative. -/
@[simp]
theorem comap_mul {m : ℤ} (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U)) :
    comap f hf hUV (mul 𝒜 U m n s t) = mul ℬ V m n (comap f hf hUV s) (comap f hf hUV t) := by
  refine ext fun (y : V) ↦ ?_
  simp only [comap_apply, mul_apply, map_mul]

end twistingSheaf

open twistingSheaf

/-- The sections `r / 1` pull back to the sections `f r / 1`: the graded maps
`A → ⨁ₙ Γ(Proj A, 𝒪(n))` are natural in `f`. -/
@[simp]
theorem comap_toTwistingSheaf {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens}
    (hUV : V.carrier ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.carrier) {j : ℕ} (h : (j : ℤ) = n)
        (r : 𝒜 j) :
    comap f hf hUV (toTwistingSheaf 𝒜 h U r) =
      toTwistingSheaf ℬ h V ⟨f r, Graded.map_mem f r.property⟩ := by
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

/-- The morphisms of twisting sheaves send the sections `r / 1` to the sections `f r / 1`. -/
-- Not a simp lemma: `Scheme.Modules.pushforward_obj_obj` already rewrites its left-hand side.
theorem twistingSheafMap_app_toTwistingSheaf (U : (Proj 𝒜).Opens) {j : ℕ} (h : (j : ℤ) = n)
    (r : 𝒜 j) :
    (twistingSheafMap f hf n).app U (toTwistingSheaf 𝒜 h U r) =
      toTwistingSheaf ℬ h (map f hf ⁻¹ᵁ U) ⟨f r, Graded.map_mem f r.property⟩ :=
  comap_toTwistingSheaf f hf Set.Subset.rfl h r

/-- The morphisms of twisting sheaves are multiplicative on sections: they send the product of
sections of `𝒪(m)` and `𝒪(n)` to the product of their images. -/
theorem twistingSheafMap_app_mul {m : ℤ} (U : (Proj 𝒜).Opens) (s : Γ(twistingSheaf 𝒜 m, U))
    (t : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheafMap f hf (m + n)).app U (mul 𝒜 U m n s t) =
      mul ℬ (map f hf ⁻¹ᵁ U) m n ((twistingSheafMap f hf m).app U s)
        ((twistingSheafMap f hf n).app U t) :=
  comap_mul f hf Set.Subset.rfl s t

/-- The morphisms of twisting sheaves, followed by restriction to an open `V` of the preimage of
`U`, are multiplicative on sections. -/
theorem res_twistingSheafMap_app_mul {m : ℤ} (U : (Proj 𝒜).Opens) {V : (Proj ℬ).Opens}
    (e : V ⟶ map f hf ⁻¹ᵁ U) (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf ℬ (m + n)).presheaf.map e.op
        ((twistingSheafMap f hf (m + n)).app U (mul 𝒜 U m n s t)) =
      mul ℬ V m n ((twistingSheaf ℬ m).presheaf.map e.op ((twistingSheafMap f hf m).app U s))
        ((twistingSheaf ℬ n).presheaf.map e.op ((twistingSheafMap f hf n).app U t)) :=
  (congrArg ((twistingSheaf ℬ (m + n)).presheaf.map e.op)
    (twistingSheafMap_app_mul f hf U s t)).trans (twistingSheaf.res_mul _ _ _)

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
  exact twistingSheaf.ext fun z ↦ DFunLike.congr_fun (localizationsMap_comp f hf g hg z.val) _

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
  exact twistingSheaf.ext fun x ↦ localizationsMap_id x.val _

/-- **The morphisms of twisting sheaves are compatible with composition, on sections**: for a
graded ring homomorphism `h` equal to `g.comp f`, the image of a section under the morphism
induced by `h`, restricted along `(Proj.map f)⁻¹ (Proj.map g)⁻¹ V = (Proj.map h)⁻¹ V`, is its
image under the morphism induced by `f` followed by the one induced by `g`. -/
theorem twistingSheafMap_app_apply_of_eq_comp (g : ℬ →+*ᵍ 𝒞) (hg : 𝒞₊ ≤ ℬ₊.map g)
    (h : 𝒜 →+*ᵍ 𝒞) (hh : 𝒞₊ ≤ 𝒜₊.map h) (hgf : h = g.comp f) (n : ℤ) (V : (Proj 𝒜).Opens)
    (s : Γ(twistingSheaf 𝒜 n, V)) :
    (twistingSheaf 𝒞 n).presheaf.map
        (eqToHom (show map g hg ⁻¹ᵁ map f hf ⁻¹ᵁ V = map h hh ⁻¹ᵁ V by
          subst hgf; rw [map_comp f g hf hg]; rfl)).op ((twistingSheafMap h hh n).app V s) =
      (twistingSheafMap g hg n).app (map f hf ⁻¹ᵁ V) ((twistingSheafMap f hf n).app V s) := by
  subst hgf
  have := congr((Scheme.Modules.Hom.app $(twistingSheafMap_comp f hf g hg n) V).hom s)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_hom_app_app] at this
  -- the remaining composites are of maps whose sources and targets agree with those in the goal
  -- only definitionally, so `simp` cannot split them; they unfold to the goal
  exact this

/-- **The morphism of twisting sheaves induced by the identity is the identity, on sections**: for
a graded ring homomorphism `g` equal to the identity, the image of a section under the morphism
induced by `g`, restricted along `(Proj.map g)⁻¹ V = V`, is the section itself. -/
theorem twistingSheafMap_app_apply_of_eq_id (g : 𝒜 →+*ᵍ 𝒜) (hg : 𝒜₊ ≤ 𝒜₊.map g)
    (hgid : g = GradedRingHom.id 𝒜) (n : ℤ) (V : (Proj 𝒜).Opens) (s : Γ(twistingSheaf 𝒜 n, V)) :
    (twistingSheaf 𝒜 n).presheaf.map (eqToHom (show V = map g hg ⁻¹ᵁ V by
        subst hgid; rw [map_id]; rfl)).op ((twistingSheafMap g hg n).app V s) = s := by
  subst hgid
  have := congr((Scheme.Modules.Hom.app $(twistingSheafMap_id (𝒜 := 𝒜) n) V).hom s)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardId_hom_app_app, Scheme.Modules.Hom.id_app] at this
  -- the remaining composites are of maps whose sources and targets agree with those in the goal
  -- only definitionally, so `simp` cannot split them; they unfold to the goal
  exact this

variable {D ω : Type u} [CommRing D] [SetLike ω D] [AddSubgroupClass ω D] {𝒟 : ℕ → ω}
  [GradedRing 𝒟] in
/-- **The morphisms of twisting sheaves along two equal composites agree, on sections**: for graded
ring homomorphisms with `g.comp f = g'.comp f'`, the images of a section under the morphisms
induced by `f` and then `g`, and by `f'` and then `g'`, agree after restriction to a common open. -/
theorem res_twistingSheafMap_app_res_of_comp_eq (g : ℬ →+*ᵍ 𝒟) (hg : 𝒟₊ ≤ ℬ₊.map g)
    (f' : 𝒜 →+*ᵍ 𝒞) (hf' : 𝒞₊ ≤ 𝒜₊.map f') (g' : 𝒞 →+*ᵍ 𝒟) (hg' : 𝒟₊ ≤ 𝒞₊.map g')
    (e : g.comp f = g'.comp f') (n : ℤ) {U : (Proj 𝒜).Opens} {V : (Proj ℬ).Opens}
    {V' : (Proj 𝒞).Opens} {W : (Proj 𝒟).Opens} (i : W ⟶ map g hg ⁻¹ᵁ V) (j : V ⟶ map f hf ⁻¹ᵁ U)
    (i' : W ⟶ map g' hg' ⁻¹ᵁ V') (j' : V' ⟶ map f' hf' ⁻¹ᵁ U) (s : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf 𝒟 n).presheaf.map i.op ((twistingSheafMap g hg n).app V
      ((twistingSheaf ℬ n).presheaf.map j.op ((twistingSheafMap f hf n).app U s))) =
    (twistingSheaf 𝒟 n).presheaf.map i'.op ((twistingSheafMap g' hg' n).app V'
      ((twistingSheaf 𝒞 n).presheaf.map j'.op ((twistingSheafMap f' hf' n).app U s))) := by
  refine twistingSheaf.ext fun z ↦ ?_
  have k := DFunLike.congr_fun (localizationsMap_comp f hf g hg z.val) (s.val ⟨_, j.le
      (i.le z.property)⟩)
  have k' := DFunLike.congr_fun (localizationsMap_comp f' hf' g' hg' z.val)
    (s.val ⟨_, j'.le (i'.le z.property)⟩)
  -- the maps of localizations along the two equal composites agree
  have key : ∀ (h h' : 𝒜 →+*ᵍ 𝒟) (_ : h = h') (hh : 𝒟₊ ≤ 𝒜₊.map h) (hh' : 𝒟₊ ≤ 𝒜₊.map h')
      (p : ProjectiveSpectrum.comap h hh z.val ∈ U) (p' : ProjectiveSpectrum.comap h' hh' z.val ∈
          U),
      localizationsMap h hh z.val (s.val ⟨_, p⟩) = localizationsMap h' hh' z.val (s.val ⟨_, p'⟩)
          := by
    rintro h _ rfl _ _ _ _
    rfl
  exact (k.symm.trans (key _ _ e _ _ _ _)).trans k'

end Proj

end universe_monomorphic

end AlgebraicGeometry
