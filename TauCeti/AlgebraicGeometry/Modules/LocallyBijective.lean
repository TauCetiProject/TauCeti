/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.AffineScheme

/-!
# Locally bijective maps from presheaves of modules with localized sections

Let `X` be a scheme, `P` a presheaf of `𝒪_X`-modules and `M` an `𝒪_X`-module. A morphism
`φ : P ⟶ M` which is locally injective and locally surjective (for instance the unit of the
sheafification of `P`, when `M` is the sheafification of `P`) need not be bijective on sections.
It is bijective on the sections over the basic opens `D(f)` of an affine open `U` as soon as the
restrictions of `P` from `U` to the basic opens `D(f) ⊆ U` are localizations at the powers of `f`,
as they are for a quasi-coherent module (`Scheme.Modules.isLocalizedModule_basicOpenRestrict`).
No quasi-coherence of `M` is assumed: `M` inherits the localization property from `P`, so it is
quasi-coherent as soon as `P` has this property on the members of an affine open cover.

The input on the side of `U` is that a covering sieve of a basic open `D(f)` of an affine open `U`
contains the basic opens `D(g)` for a family of functions `g` whose ideal has `f` in its radical
(`AlgebraicGeometry.IsAffineOpen.mem_radical_span_setOf_basicOpen_mem_sieve`, in
`TauCeti.AlgebraicGeometry.AffineScheme`). Injectivity then follows by clearing denominators. For
surjectivity, a section of `M` over `D(f)` that vanishes on `D(f) ∩ D(g)` is killed by a power of
`g`: it comes locally from sections of `P` over finitely many `D(t)` covering `D(f)`, and these
are killed by powers of `g` by injectivity over `D(t) ∩ D(g)`. As in Hartshorne, Lemma II.5.3, a
section of `M` over `D(f)` is then multiplied into the image of `φ` by powers of the functions `g`
over whose basic opens it comes from `P`, hence by a power of `f`.

This computes the sections over affine opens of sheaves obtained by sheafifying a sectionwise
construction, such as the symmetric powers of a quasi-coherent module or the presheaf
`V ↦ Hⁿ(f⁻¹ V, F)` whose sheafification is a higher direct image, and shows that these sheaves are
quasi-coherent.

## Main declarations

* `AlgebraicGeometry.IsAffineOpen.bijective_app_basicOpen_of_isLocalizedModule`: a locally
  bijective morphism from a presheaf of modules whose restrictions to basic opens of an affine
  open `U` are localizations is bijective on the sections over every basic open of `U`;
* `AlgebraicGeometry.IsAffineOpen.bijective_app_of_isLocalizedModule`: the same over `U` itself;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyBijective`: the target of such a
  morphism is quasi-coherent when these restrictions are localizations on an affine open cover.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens}

variable {P : PresheafOfModulesOfCommRing.{u} X.presheaf} {M : X.Modules}

section

variable (hP : ∀ f : Γ(X, U),
  IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom)
include hP

/-- A section of `P` over `D(f)` vanishing on `D(f * g)` is killed by a power of `g`. -/
private lemma exists_pow_smul_eq_zero_of_map_eq_zero (f g : Γ(X, U))
    (w : P.obj (op (X.basicOpen f)))
    (hw : P.map (homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)).op w = 0) :
    ∃ n : ℕ, X.presheaf.map (homOfLE (X.basicOpen_le f)).op (g ^ n) • w = 0 := by
  have := hP (f * g)
  have := hP f
  obtain ⟨⟨c, _, k, rfl⟩, hc⟩ := (hP f).surj w
  let r := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
  -- the powers of `f` act on sections over `X.basicOpen f` through restriction
  change r (f ^ k) • w = P.map _ c at hc
  have h₁ : P.map (homOfLE (X.basicOpen_le (f * g))).op c = 0 := by
    rw [← homOfLE_comp ((X.basicOpen_mul f g).trans_le inf_le_left) (X.basicOpen_le f), op_comp,
      PresheafOfModules.map_comp_apply, ← hc, PresheafOfModules.map_smul, hw, smul_zero]
    -- the zero of the restricted-scalars module is the zero of the sections
    rfl
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers (f * g))
    (f := (P.map (homOfLE (X.basicOpen_le (f * g))).op).hom)).1 h₁
  have hn : (f * g) ^ n • c = 0 := hn
  refine ⟨n, IsLocalizedModule.smul_injective (P.map (homOfLE (X.basicOpen_le f)).op).hom
    (⟨f ^ (k + n), k + n, rfl⟩ : Submonoid.powers f) ?_⟩
  -- the powers of `f` act on sections over `X.basicOpen f` through restriction
  change r (f ^ (k + n)) • r (g ^ n) • w = r (f ^ (k + n)) • (0 : P.obj (op (X.basicOpen f)))
  rw [smul_zero, smul_smul, ← map_mul, show f ^ (k + n) * g ^ n = (f * g) ^ n * f ^ k by ring,
    map_mul, mul_smul, hc]
  exact ((P.map (homOfLE (X.basicOpen_le f)).op).hom.map_smul ((f * g) ^ n) c).symm.trans
    (by rw [hn, map_zero]; rfl)

/-- A locally injective morphism from `P` is injective on the sections over every basic open of
`U`. -/
private lemma injective_app_basicOpen (hU : IsAffineOpen U) (φ : P ⟶ M.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)] (f : Γ(X, U)) :
    Function.Injective (φ.app (op (X.basicOpen f))) := by
  have := hP f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map φ) x 0 (hx.trans (map_zero _).symm)
  -- `x` is killed by a power of every `g` with `X.basicOpen g` in the sieve, hence by a power of
  -- `f`, which acts invertibly
  let x' : (ModuleCat.restrictScalars (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
    (P.obj (op (X.basicOpen f))) := x
  have key : f ∈ ((⊥ : Submodule Γ(X, U) _).colon {x'}).radical := by
    rw [← Ideal.radical_idem]
    refine Ideal.radical_mono (Ideal.span_le.2 ?_)
      (hU.mem_radical_span_setOf_basicOpen_mem_sieve f hS)
    rintro g ⟨hg, hgx⟩
    have hgx : P.map (homOfLE hg).op x = 0 := hgx.trans (map_zero _)
    have hx₀ : P.map (homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)).op x = 0 := by
      rw [← homOfLE_comp ((X.basicOpen_mul f g).trans_le inf_le_right) hg, op_comp,
        PresheafOfModules.map_comp_apply, hgx]
      exact map_zero (P.map _).hom
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_map_eq_zero hP f g x hx₀
    exact ⟨n, Submodule.mem_colon_singleton.2 ((Submodule.mem_bot _).2 hn)⟩
  obtain ⟨n, hn⟩ := key
  exact IsLocalizedModule.smul_injective (P.map (homOfLE (X.basicOpen_le f)).op).hom
    (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    (((Submodule.mem_bot _).1 (Submodule.mem_colon_singleton.1 hn)).trans (smul_zero _).symm)

/-- On `D(t)` for `t` with `D(t) ⊆ D(f)`, a section of `M` over `D(f)` coming from `P` over `D(t)`
and vanishing on `D(f * g)` is killed by all large enough powers of `g`. -/
private lemma exists_forall_pow_smul_map_eq_zero (φ : P ⟶ M.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)] (hU : IsAffineOpen U) {f g t : Γ(X, U)}
    (htf : X.basicOpen t ≤ X.basicOpen f) (z : Γ(M, X.basicOpen f))
    (hz : M.presheaf.map (homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)).op z = 0)
    (w : P.obj (op (X.basicOpen t))) (hw : φ.app _ w = M.presheaf.map (homOfLE htf).op z) :
    ∃ m : ℕ, ∀ m' ≥ m, M.presheaf.map (homOfLE htf).op (g ^ m' • z) = 0 := by
  have htg : X.basicOpen (t * g) ≤ X.basicOpen (f * g) := by
    simp only [Scheme.basicOpen_mul]
    exact inf_le_inf_right _ htf
  let i := homOfLE ((X.basicOpen_mul t g).trans_le inf_le_left)
  have hwz : P.map i.op w = 0 := by
    apply injective_app_basicOpen hP hU φ (t * g)
    have h₁ : φ.app (op (X.basicOpen (t * g))) (P.map i.op w) =
        M.presheaf.map i.op (M.presheaf.map (homOfLE htf).op z) :=
      (PresheafOfModules.naturality_apply φ i.op w).trans (congrArg _ hw)
    have h₂ : M.presheaf.map i.op (M.presheaf.map (homOfLE htf).op z) = M.presheaf.map
        (homOfLE htg).op (M.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)).op z) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl
    rw [h₁, h₂, hz, map_zero]
    exact (map_zero (φ.app _).hom).symm
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_map_eq_zero hP t g w hwz
  refine ⟨n, fun m' hm' ↦ ?_⟩
  let r := X.presheaf.map (homOfLE (X.basicOpen_le t)).op
  have h₁ : M.presheaf.map (homOfLE htf).op (g ^ m' • z) = r (g ^ m') • φ.app _ w := by
    rw [M.basicOpen_smul_def, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    exact congrArg₂ (· • ·) rfl hw.symm
  have h₂ : (r (g ^ m') • w : P.obj (op (X.basicOpen t))) = 0 := by
    rw [← Nat.sub_add_cancel hm', pow_add, map_mul, mul_smul, hn, smul_zero]
  refine (h₁.trans ((φ.app _).hom.map_smul _ w).symm).trans ?_
  rw [h₂]
  exact map_zero (φ.app _).hom

/-- A section of `M` over `D(f)` vanishing on `D(f * g)` is killed by a power of `g`. -/
private lemma exists_pow_smul_eq_zero (φ : P ⟶ M.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)] (hU : IsAffineOpen U) (f g : Γ(X, U))
    (z : Γ(M, X.basicOpen f))
    (hz : M.presheaf.map (homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)).op z = 0) :
    ∃ n : ℕ, g ^ n • z = 0 := by
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map φ) z
  obtain ⟨N, hN⟩ := hU.mem_radical_span_setOf_basicOpen_mem_sieve f hS
  -- finitely many `D(t)` over which `z` comes from `P` cover `D(f)`
  obtain ⟨T, hTG, hNT⟩ := Submodule.mem_span_finite_of_mem_span hN
  have ht : ∀ t ∈ T, ∃ (h : X.basicOpen t ≤ X.basicOpen f) (m : ℕ), ∀ m' ≥ m,
      M.presheaf.map (homOfLE h).op (g ^ m' • z) = 0 := by
    intro t htT
    obtain ⟨htf, (w : P.obj (op (X.basicOpen t))), hw⟩ := hTG htT
    exact ⟨htf, exists_forall_pow_smul_map_eq_zero hP φ hU htf z hz w hw⟩
  choose! hle m hm using ht
  refine ⟨T.sup m, TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) (fun t : T ↦ X.basicOpen t.1)
    (X.basicOpen f) (fun t ↦ homOfLE (hle t.1 t.2)) ?_ _ _ fun t ↦ ?_⟩
  · simpa [iSup_subtype] using
      (hU.basicOpen_le_iSup_basicOpen_iff (s := ↑T) (f := f)).2 ⟨N, hNT⟩
  · rw [hm t.1 t.2 _ (Finset.le_sup t.2), map_zero]

end

variable (φ : P ⟶ M.val) (f : Γ(X, U))

/-- The sections of `φ` over the basic open `D(f)` of `f ∈ Γ(X, U)`, as a `Γ(X, U)`-linear map. -/
private def basicOpenAppLinear :
    (ModuleCat.restrictScalars (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
      (P.obj (op (X.basicOpen f))) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := φ.app (op (X.basicOpen f))
  map_add' := map_add _
  map_smul' _ x := (φ.app (op (X.basicOpen f))).hom.map_smul _ x

variable {f}

/-- If a section `s` of `M` over `D(f)` comes from `P` on some `D(g) ⊆ D(f)`, then a power of `g`
multiplies `s` into the image of `φ` over `D(f)`. -/
private lemma exists_pow_smul_mem_range (hP : ∀ f : Γ(X, U),
      IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)] (hU : IsAffineOpen U) {g : Γ(X, U)}
    (hg : X.basicOpen g ≤ X.basicOpen f) (s : Γ(M, X.basicOpen f))
    (b : P.obj (op (X.basicOpen g))) (hb : φ.app _ b = M.presheaf.map (homOfLE hg).op s) :
    ∃ n : ℕ, g ^ n • s ∈ LinearMap.range (basicOpenAppLinear φ f) := by
  have := hP g
  obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := (hP g).surj b
  let r := X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op
  let i₁ := homOfLE ((X.basicOpen_mul f g).trans_le inf_le_left)
  let i₂ := homOfLE ((X.basicOpen_mul f g).trans_le inf_le_right)
  -- the powers of `g` act on sections over `X.basicOpen g` through restriction
  change X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ k) • b =
    P.map (homOfLE (X.basicOpen_le g)).op a at hak
  let y := P.map (homOfLE (X.basicOpen_le f)).op a
  -- over `D(f * g)`, the image of `y` and `g ^ k • s` agree
  have e₁ : P.map i₁.op (P.map (homOfLE (X.basicOpen_le f)).op a) = r (g ^ k) • P.map i₂.op b := by
    -- both composites are the inclusion of `D(f * g)` into `U`, as morphisms of a preorder are
    -- unique
    rw [← PresheafOfModules.map_comp_apply,
      show (homOfLE (X.basicOpen_le f)).op ≫ i₁.op = (homOfLE (X.basicOpen_le g)).op ≫ i₂.op
        from rfl, PresheafOfModules.map_comp_apply, ← hak, PresheafOfModules.map_smul]
    congr 1
    exact (ConcreteCategory.comp_apply (X.presheaf.map (homOfLE (X.basicOpen_le g)).op)
      (X.presheaf.map i₂.op) (g ^ k)).symm.trans (by rw [← Functor.map_comp]; rfl)
  have e₂ : M.presheaf.map i₂.op (M.presheaf.map (homOfLE hg).op s) = M.presheaf.map i₁.op s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have e₃ : M.presheaf.map i₁.op (g ^ k • s) = r (g ^ k) • M.presheaf.map i₁.op s := by
    rw [M.basicOpen_smul_def, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  have hz : M.presheaf.map i₁.op (basicOpenAppLinear φ f y - g ^ k • s) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact ((PresheafOfModules.naturality_apply φ i₁.op _).symm.trans (congrArg _ e₁)).trans
      (((φ.app _).hom.map_smul _ _).trans ((congrArg _ ((PresheafOfModules.naturality_apply
        φ i₂.op b).trans ((congrArg _ hb).trans e₂))).trans e₃.symm))
  obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero hP φ hU f g _ hz
  refine ⟨m + k, g ^ m • y, ?_⟩
  rw [map_smul, pow_add, mul_smul]
  exact sub_eq_zero.1 ((smul_sub _ _ _).symm.trans hm)

variable [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map φ)]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map φ)]

/-- **Locally bijective maps are bijective over basic opens of affine opens.** Let `φ : P ⟶ M` be
a locally injective and locally surjective morphism from a presheaf of `𝒪_X`-modules to an
`𝒪_X`-module, and let `U` be an affine open such that the restrictions of `P` from `U` to the basic
opens `D(f) ⊆ U` are localizations at the powers of `f`. Then `φ` is bijective on sections over
every basic open `D(f)` of `U`. -/
theorem bijective_app_basicOpen_of_isLocalizedModule (hU : IsAffineOpen U)
    (hP : ∀ f : Γ(X, U),
      IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom)
    (f : Γ(X, U)) : Function.Bijective (φ.app (op (X.basicOpen f))) := by
  refine ⟨injective_app_basicOpen hP hU φ f, fun (s : Γ(M, X.basicOpen f)) ↦ ?_⟩
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map φ) s
  -- a power of every `g` with `D(g)` in the image sieve multiplies `s` into the image of `φ`,
  -- hence so does a power of `f`, which acts invertibly
  have key : f ∈ ((LinearMap.range (basicOpenAppLinear φ f)).colon {s}).radical := by
    rw [← Ideal.radical_idem]
    refine Ideal.radical_mono (Ideal.span_le.2 ?_)
      (hU.mem_radical_span_setOf_basicOpen_mem_sieve f hS)
    rintro g ⟨hg, (b : P.obj (op (X.basicOpen g))), hb⟩
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_range φ hP hU hg s b hb
    exact ⟨n, Submodule.mem_colon_singleton.2 hn⟩
  obtain ⟨n, hn⟩ := key
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 (Submodule.mem_colon_singleton.1 hn)
  have := hP f
  obtain ⟨y', rfl⟩ := ((Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units
    (P.map (homOfLE (X.basicOpen_le f)).op).hom (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))).2 y
  have hu := (M.isUnit_algebraMap_end_basicOpen f).pow n
  rw [← map_pow, Module.End.isUnit_iff] at hu
  exact ⟨y', hu.1 (((basicOpenAppLinear φ f).map_smul _ y').symm.trans hy)⟩

/-- **Locally bijective maps are bijective on affine opens.** Let `φ : P ⟶ M` be a locally
injective and locally surjective morphism from a presheaf of `𝒪_X`-modules to an `𝒪_X`-module, and
let `U` be an affine open such that the restrictions of `P` from `U` to the basic opens `D(f) ⊆ U`
are localizations at the powers of `f`. Then `φ` is bijective on sections over `U`. -/
theorem bijective_app_of_isLocalizedModule (hU : IsAffineOpen U)
    (hP : ∀ f : Γ(X, U),
      IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom) :
    Function.Bijective (φ.app (op U)) := by
  have h := hU.bijective_app_basicOpen_of_isLocalizedModule φ hP 1
  rwa [Scheme.basicOpen_one] at h

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {P : PresheafOfModulesOfCommRing.{u} X.presheaf} {M : X.Modules}

/-- **Quasi-coherence from a locally bijective map.** Let `φ : P ⟶ M` be a locally injective and
locally surjective morphism from a presheaf of `𝒪_X`-modules to an `𝒪_X`-module, for instance the
unit of the sheafification of `P`. If `X` is covered by affine opens `U i` such that the
restrictions of `P` from `U i` to the basic opens `D(f) ⊆ U i` are localizations at the powers of
`f`, then `M` is quasi-coherent. -/
theorem isQuasicoherent_of_isLocallyBijective (φ : P ⟶ M.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map φ)] {ι : Sort*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hP : ∀ i (f : Γ(X, U i)),
      IsLocalizedModule (.powers f) (P.map (homOfLE (X.basicOpen_le f)).op).hom) :
    M.IsQuasicoherent := by
  refine M.isQuasicoherent_of_isLocalizedModule U hU hcov fun i f ↦ ?_
  have := hP i f
  let e : P.obj (op (U i)) →ₗ[Γ(X, U i)] Γ(M, U i) := (φ.app (op (U i))).hom
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ e
    ((hU i).bijective_app_of_isLocalizedModule φ (hP i))).1 ?_
  rw [show M.basicOpenRestrict f ∘ₗ e = IsAffineOpen.basicOpenAppLinear φ f ∘ₗ
      (P.map (homOfLE (X.basicOpen_le f)).op).hom from
      LinearMap.ext fun x ↦ (M.basicOpenRestrict_apply f _).trans
        (PresheafOfModules.naturality_apply φ (homOfLE (X.basicOpen_le f)).op x).symm]
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _
    ((hU i).bijective_app_basicOpen_of_isLocalizedModule φ (hP i) f)).2 this

end AlgebraicGeometry.Scheme.Modules
