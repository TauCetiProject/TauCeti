/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.BaseChange
public import TauCeti.Algebra.Category.CommAlgCat.Localization
public import TauCeti.Algebra.Category.ModuleCat.Localization
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.CategoryTheory.Localization.Monoidal.Functor
public import TauCeti.RingTheory.Almost.Algebra
public import TauCeti.RingTheory.Localization.Module
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Inverting an element of `m` on almost modules and almost algebras

Let `S = (V, m)` be a basic setup and `ϖ ∈ m` (`ϖ` need not be a nonzerodivisor; in particular
`ϖ = 0` is allowed). Because `ϖ` annihilates every almost zero `V`-module, localizing `V`-modules
away from `ϖ` sends almost zero modules to zero modules and almost isomorphisms to isomorphisms.
Being exact, `ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ)` therefore factors uniquely (up
to canonical isomorphism) through an exact functor
`TauCeti.Almost.invert S hϖ : Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)`.

Along almostification `M ↦ M^a`, `invert S hϖ` recovers module localization `M ↦ M[1/ϖ]`, and
likewise extension of scalars `M ↦ V[1/ϖ] ⊗[V] M` (`TauCeti.Almost.toAlmostCompInvertIso`,
`TauCeti.Almost.toAlmostCompInvertExtendScalarsIso`). Using the counit isomorphism `(M_*)^a ≅ M`
and the unit isomorphism `M ≅ (M_!)^a`, every almost module `M` satisfies
`(invert S hϖ).obj M ≅ M_*[1/ϖ] ≅ M_![1/ϖ]` (`TauCeti.Almost.invertElementsIso`,
`TauCeti.Almost.invertShriekIso`). Since extension of scalars to `Localization.Away ϖ` is braided
monoidal, `invert S hϖ` inherits a braided strong monoidal structure
(`TauCeti.Almost.invertMonoidal`, `TauCeti.Almost.invertBraided`).

On almost algebras, `TauCeti.Almost.Algebra.invert S ϖ` sends `A` to the localized algebra
`A_*[1/ϖ]` in `CommAlgCat (Localization.Away ϖ)` and acts via `(Algebra.elements S).map` on
canonical numerators. When `ϖ ∈ m`, the unit `R → (R^a)_*` is an almost isomorphism, so
precomposing with almostification recovers ordinary algebra localization
(`TauCeti.Almost.Algebra.toAlmostCompInvertIso`, `TauCeti.Almost.Algebra.invertToAlmostObjEquiv`),
and `Algebra.invert S ϖ` is naturally isomorphic to the functor induced on commutative monoid
objects by `Almost.invert S hϖ` (`TauCeti.Almost.Algebra.invertIsoMapCommMon`).

Finally, combining `TauCeti.Almost.Module.exact_map_toAlmost_iff` with exactness of `invert S hϖ`,
after inverting `ϖ ∈ m`, a short complex of `V`-modules whose homology is almost zero becomes exact
at the middle term, and a homological complex whose homology is almost zero in every degree becomes
acyclic.

## Main definitions

* `TauCeti.Almost.invert`: the exact braided monoidal functor
  `Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)` for `hϖ : ϖ ∈ S.ideal`.
* `TauCeti.Almost.toAlmostCompInvertIso` and `TauCeti.Almost.toAlmostCompInvertExtendScalarsIso`:
  natural isomorphisms identifying `Module.toAlmost S ⋙ invert S hϖ` with module localization and
  with extension of scalars to `Localization.Away ϖ`.
* `TauCeti.Almost.invertElementsIso` and `TauCeti.Almost.invertShriekIso`: the identifications
  `(invert S hϖ).obj M ≅ M_*[1/ϖ]` and `(invert S hϖ).obj M ≅ M_![1/ϖ]`.
* `TauCeti.Almost.Algebra.invert`: the functor `Almost.Algebra S ⥤ CommAlgCat (Localization.Away ϖ)`
  sending `A` to `A_*[1/ϖ]`, with comparisons `TauCeti.Almost.Algebra.toAlmostCompInvertIso`,
  `TauCeti.Almost.Algebra.invertToAlmostObjEquiv`, and
  `TauCeti.Almost.Algebra.invertIsoMapCommMon`.

## Main results

* `TauCeti.Almost.BasicSetup.IsAlmostZero.subsingleton_of_isLocalizedModule` and
  `TauCeti.Almost.BasicSetup.IsAlmostIso.bijective_isLocalizedModule_map`: localizing at a
  submonoid meeting `m` kills almost zero modules and turns almost isomorphisms into bijections.
* `TauCeti.Almost.isZero_invert_toAlmost_obj_iff`, `TauCeti.Almost.isZero_invert_obj_iff`,
  `TauCeti.Almost.Algebra.subsingleton_invert_obj_iff`, and
  `TauCeti.Almost.Algebra.subsingleton_invert_toAlmost_obj_iff`: power-of-`ϖ` torsion
  characterizations of vanishing after inversion.
* `TauCeti.Almost.invertMonoidal` and `TauCeti.Almost.invertBraided`: `invert S hϖ` is braided
  strong monoidal.
* `TauCeti.Almost.not_faithful_invert_of_not_isAlmostZero_quotient`: `invert S hϖ` is not faithful
  whenever `V ⧸ (ϖ)` is not almost zero (in particular for valuation setups at any `ϖ ∈ m`).
* `TauCeti.Almost.exact_localizedModuleFunctor_of_isAlmostZero_homology`,
  `TauCeti.Almost.exact_extendScalars_away_of_isAlmostZero_homology`,
  `TauCeti.Almost.acyclic_localizedModuleFunctor_of_isAlmostZero_homology`, and
  `TauCeti.Almost.acyclic_extendScalars_away_of_isAlmostZero_homology`: short complexes with almost
  zero homology become exact at the middle term, and homological complexes with almost zero homology
  in every degree become acyclic, after inverting `ϖ ∈ m`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2 and §5.2,
  proof of Corollary 5.2.15.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Exercise 4.1.9.
* P. Scholze, J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Lecture 8, proof of
  Proposition 8.2.8.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct
open scoped ChangeOfRings MonObj

namespace TauCeti.Almost

/-! ### Module-level localization at a submonoid meeting `m` -/

namespace BasicSetup

variable {V : Type*} [CommRing V] {S : BasicSetup V}

/-- Localizing an almost zero `V`-module at any submonoid `P` containing an element `ϖ ∈ m` yields a
subsingleton module. -/
theorem IsAlmostZero.subsingleton_of_isLocalizedModule {M M' : Type*}
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup M'] [_root_.Module V M']
    (hM : S.IsAlmostZero M) {P : Submonoid V} {f : M →ₗ[V] M'} [IsLocalizedModule P f]
    {ϖ : V} (hϖP : ϖ ∈ P) (hϖ : ϖ ∈ S.ideal) :
    Subsingleton M' :=
  (IsLocalizedModule.subsingleton_iff P f).mpr fun m ↦ ⟨ϖ, hϖP, hM.smul_eq_zero hϖ m⟩

/-- Localizing an almost zero `V`-module away from `ϖ ∈ m` yields a subsingleton module. -/
theorem IsAlmostZero.subsingleton_of_isLocalizedModule_away {M M' : Type*}
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup M'] [_root_.Module V M']
    (hM : S.IsAlmostZero M) {ϖ : V} (hϖ : ϖ ∈ S.ideal) {f : M →ₗ[V] M'}
    [IsLocalizedModule.Away ϖ f] :
    Subsingleton M' :=
  hM.subsingleton_of_isLocalizedModule (f := f) (Submonoid.mem_powers ϖ) hϖ

/-- For an almost zero `V`-module `M` and `ϖ ∈ m`, `LocalizedModule.Away ϖ M` is subsingleton. -/
theorem IsAlmostZero.subsingleton_localizedModule_away {M : Type*}
    [AddCommGroup M] [_root_.Module V M] (hM : S.IsAlmostZero M) {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Subsingleton (LocalizedModule.Away ϖ M) :=
  hM.subsingleton_of_isLocalizedModule_away hϖ (f := LocalizedModule.mkLinearMap _ M)

/-- Base-changing an almost zero `V`-module to a `V`-algebra `W` in which `ϖ ∈ m` maps to a unit
gives a zero module. -/
theorem IsAlmostZero.subsingleton_tensorProduct {M : Type*} [AddCommGroup M] [_root_.Module V M]
    (hM : S.IsAlmostZero M) {ϖ : V} (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W]
    [_root_.Algebra V W] (hu : IsUnit (algebraMap V W ϖ)) : Subsingleton (W ⊗[V] M) := by
  obtain ⟨u, hu_eq⟩ := hu
  have hzero (x : W ⊗[V] M) : x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul w m =>
      calc w ⊗ₜ[V] m
          = (w * ↑u⁻¹ * algebraMap V W ϖ) ⊗ₜ[V] m := by
              rw [← hu_eq, mul_assoc, Units.inv_mul, mul_one]
        _ = (ϖ • (w * ↑u⁻¹)) ⊗ₜ[V] m := by
              rw [_root_.Algebra.smul_def, mul_comm (algebraMap V W ϖ)]
        _ = (w * ↑u⁻¹) ⊗ₜ[V] (ϖ • m) := TensorProduct.smul_tmul _ _ _
        _ = (w * ↑u⁻¹) ⊗ₜ[V] 0 := by rw [hM.smul_eq_zero hϖ m]
        _ = 0 := TensorProduct.tmul_zero _ _
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- Localizing at a submonoid `P` containing `ϖ ∈ m` makes a linear map with almost zero kernel
injective. -/
theorem IsAlmostZero.injective_localizedModule_map {M N : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] {P : Submonoid V} {f : M →ₗ[V] N}
    (h : S.IsAlmostZero (LinearMap.ker f)) {ϖ : V} (hϖP : ϖ ∈ P) (hϖ : ϖ ∈ S.ideal) :
    Function.Injective (LocalizedModule.map P f) :=
  (LinearMap.localizedMap_injective_iff_subsingleton_localized_ker P f).mpr
    (h.subsingleton_of_isLocalizedModule (f := LocalizedModule.mkLinearMap P _) hϖP hϖ)

/-- Localizing at a submonoid `P` containing `ϖ ∈ m` makes a linear map with almost zero cokernel
surjective. -/
theorem IsAlmostZero.surjective_localizedModule_map {M N : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] {P : Submonoid V} {f : M →ₗ[V] N}
    (h : S.IsAlmostZero (N ⧸ LinearMap.range f)) {ϖ : V} (hϖP : ϖ ∈ P) (hϖ : ϖ ∈ S.ideal) :
    Function.Surjective (LocalizedModule.map P f) :=
  (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker P f).mpr
    (h.subsingleton_of_isLocalizedModule (f := LocalizedModule.mkLinearMap P _) hϖP hϖ)

/-- Localizing an almost isomorphism at any submonoid `P` containing an element `ϖ ∈ m` produces a
bijection. -/
theorem IsAlmostIso.bijective_isLocalizedModule_map {M M' N N' : Type*}
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup M'] [_root_.Module V M']
    [AddCommGroup N] [_root_.Module V N] [AddCommGroup N'] [_root_.Module V N']
    {P : Submonoid V} (fM : M →ₗ[V] M') (fN : N →ₗ[V] N')
    [IsLocalizedModule P fM] [IsLocalizedModule P fN]
    {g : M →ₗ[V] N} (hg : S.IsAlmostIso g) {ϖ : V} (hϖP : ϖ ∈ P) (hϖ : ϖ ∈ S.ideal) :
    Function.Bijective (IsLocalizedModule.map P fM fN g) := by
  obtain ⟨h, hgh, hhg⟩ := hg.exists_comp_eq_smul_id hϖ
  have hleft :
      IsLocalizedModule.map P fN fM h ∘ₗ IsLocalizedModule.map P fM fN g =
        algebraMap V (_root_.Module.End V M') ϖ := by
    rw [← IsLocalizedModule.map_comp', hhg, map_smul, IsLocalizedModule.map_id]
    ext
    rfl
  have hright :
      IsLocalizedModule.map P fM fN g ∘ₗ IsLocalizedModule.map P fN fM h =
        algebraMap V (_root_.Module.End V N') ϖ := by
    rw [← IsLocalizedModule.map_comp', hgh, map_smul, IsLocalizedModule.map_id]
    ext
    rfl
  have hbijM := (_root_.Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units fM ⟨ϖ, hϖP⟩)
  have hbijN := (_root_.Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units fN ⟨ϖ, hϖP⟩)
  exact ⟨Function.Injective.of_comp (f := IsLocalizedModule.map P fN fM h)
      (by simpa [← LinearMap.coe_comp, hleft] using hbijM.1),
    Function.Surjective.of_comp (g := IsLocalizedModule.map P fN fM h)
      (by simpa [← LinearMap.coe_comp, hright] using hbijN.2)⟩

/-- Localizing an almost isomorphism away from `ϖ ∈ m` produces a bijection. -/
theorem IsAlmostIso.bijective_isLocalizedModule_map_away {M M' N N' : Type*}
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup M'] [_root_.Module V M']
    [AddCommGroup N] [_root_.Module V N] [AddCommGroup N'] [_root_.Module V N']
    {ϖ : V} (fM : M →ₗ[V] M') (fN : N →ₗ[V] N')
    [IsLocalizedModule.Away ϖ fM] [IsLocalizedModule.Away ϖ fN]
    {g : M →ₗ[V] N} (hg : S.IsAlmostIso g) (hϖ : ϖ ∈ S.ideal) :
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers ϖ) fM fN g) :=
  hg.bijective_isLocalizedModule_map fM fN (Submonoid.mem_powers ϖ) hϖ

/-- For an almost isomorphism `g : M →ₗ[V] N` and `ϖ ∈ m`, `LocalizedModule.map` at the powers of
`ϖ` is bijective. -/
theorem IsAlmostIso.bijective_localizedModule_map_powers {M N : Type*}
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup N] [_root_.Module V N]
    {g : M →ₗ[V] N} (hg : S.IsAlmostIso g) {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers ϖ) g) :=
  hg.bijective_isLocalizedModule_map_away (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) hϖ

private theorem lTensor_comp_eq_smul {V : Type*} [CommRing V] {ϖ : V}
    {W : Type*} [CommRing W] [_root_.Algebra V W]
    {A B : Type*} [AddCommGroup A] [_root_.Module V A] [AddCommGroup B] [_root_.Module V B]
    (g₁ : A →ₗ[V] B) (g₂ : B →ₗ[V] A) (hg : g₂ ∘ₗ g₁ = ϖ • LinearMap.id)
    (x : W ⊗[V] A) :
    g₂.lTensor W (g₁.lTensor W x) = algebraMap V W ϖ • x := by
  have hlin : ((g₂.lTensor W).comp (g₁.lTensor W)).restrictScalars V =
      ((algebraMap V W ϖ) • (LinearMap.id : W ⊗[V] A →ₗ[W] W ⊗[V] A)).restrictScalars V := by
    apply TensorProduct.ext'
    intro w a
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      LinearMap.smul_apply, LinearMap.id_apply]
    have ha : g₂ (g₁ a) = ϖ • a := LinearMap.congr_fun hg a
    rw [ha, ← TensorProduct.smul_tmul, _root_.Algebra.smul_def, ← smul_eq_mul,
      TensorProduct.smul_tmul']
  exact LinearMap.congr_fun hlin x

/-- Base-changing along a `V`-algebra `W` in which `ϖ ∈ m` maps to a unit turns an almost
isomorphism into a bijection. -/
theorem IsAlmostIso.bijective_lTensor {M N : Type*} [AddCommGroup M] [_root_.Module V M]
    [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N} (hf : S.IsAlmostIso f)
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W] [_root_.Algebra V W]
    (hu : IsUnit (algebraMap V W ϖ)) :
    Function.Bijective (f.lTensor W) := by
  obtain ⟨h, hgh, hhg⟩ := hf.exists_comp_eq_smul_id hϖ
  obtain ⟨u, hu_eq⟩ := hu
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y ↦ (↑u⁻¹ : W) • h.lTensor W y, ?_, ?_⟩
  · intro x
    have hl : h.lTensor W (f.lTensor W x) = (u : W) • x := by
      rw [lTensor_comp_eq_smul f h hhg x, hu_eq]
    dsimp only
    rw [hl, smul_smul, u.inv_mul, one_smul]
  · intro y
    have hr : f.lTensor W (h.lTensor W y) = (u : W) • y := by
      rw [lTensor_comp_eq_smul h f hgh y, hu_eq]
    dsimp only
    rw [← LinearMap.smul_lTensor, hr, smul_smul, u.inv_mul, one_smul]

/-- A composable pair `L → M → N` of `V`-linear maps that is almost exact at `M` becomes exact
after localizing at any submonoid `P` containing an element `ϖ ∈ m`. -/
theorem exact_isLocalizedModule_map (S : BasicSetup V) {L L' M M' N N' : Type*}
    [AddCommGroup L] [_root_.Module V L] [AddCommGroup L'] [_root_.Module V L']
    [AddCommGroup M] [_root_.Module V M] [AddCommGroup M'] [_root_.Module V M']
    [AddCommGroup N] [_root_.Module V N] [AddCommGroup N'] [_root_.Module V N']
    {P : Submonoid V} (fL : L →ₗ[V] L') (fM : M →ₗ[V] M') (fN : N →ₗ[V] N')
    [IsLocalizedModule P fL] [IsLocalizedModule P fM] [IsLocalizedModule P fN]
    {f : L →ₗ[V] M} {g : M →ₗ[V] N} (hgf : g ∘ₗ f = 0)
    (hexact : ∀ ε ∈ S.ideal, ∀ y ∈ LinearMap.ker g, ε • y ∈ LinearMap.range f)
    {ϖ : V} (hϖP : ϖ ∈ P) (hϖ : ϖ ∈ S.ideal) :
    Function.Exact (IsLocalizedModule.map P fL fM f) (IsLocalizedModule.map P fM fN g) := by
  intro y'
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective P fM y'
    rw [Function.uncurry_apply_pair, IsLocalizedModule.map_mk',
      IsLocalizedModule.mk'_eq_zero'] at hy
    obtain ⟨t, ht⟩ := hy
    have hker : (t : V) • y ∈ LinearMap.ker g := by
      simpa [Submonoid.smul_def] using ht
    obtain ⟨x, hx⟩ := hexact ϖ hϖ _ hker
    refine ⟨IsLocalizedModule.mk' fL x ((⟨ϖ, hϖP⟩ * t) * s), ?_⟩
    have hsmul : ϖ • (t : V) • y = (⟨ϖ, hϖP⟩ * t : P) • y := by
      rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    rw [Function.uncurry_apply_pair, IsLocalizedModule.map_mk', hx, hsmul,
      IsLocalizedModule.mk'_cancel_left]
  · rintro ⟨x', rfl⟩
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective P fL x'
    have hgf_apply : g (f x) = 0 := congr($hgf x)
    simp [IsLocalizedModule.map_mk', hgf_apply]

/-- A composable pair `L → M → N` of `V`-linear maps that is almost exact at `M` becomes exact
after localizing away from `ϖ ∈ m`. -/
theorem exact_localizedModule_map_powers (S : BasicSetup V) {L M N : Type*}
    [AddCommGroup L] [_root_.Module V L] [AddCommGroup M] [_root_.Module V M]
    [AddCommGroup N] [_root_.Module V N]
    {f : L →ₗ[V] M} {g : M →ₗ[V] N} (hgf : g ∘ₗ f = 0)
    (hexact : ∀ ε ∈ S.ideal, ∀ y ∈ LinearMap.ker g, ε • y ∈ LinearMap.range f)
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Function.Exact (LocalizedModule.map (Submonoid.powers ϖ) f)
      (LocalizedModule.map (Submonoid.powers ϖ) g) :=
  exact_isLocalizedModule_map S (LocalizedModule.mkLinearMap _ L)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) hgf hexact
    (Submonoid.mem_powers ϖ) hϖ

end BasicSetup

/-! ### The inversion functor `Almost.invert` on almost modules -/

section ModuleInvert

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- Localizing away from `ϖ ∈ m` in `ModuleCat` sends almost zero modules to zero objects. -/
theorem isZero_localizedModuleFunctor_obj_of_isAlmostZero {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (M : ModuleCat.{u} V) (hM : S.IsAlmostZero M) :
    IsZero ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).obj M) := by
  have : Subsingleton (LocalizedModule (Submonoid.powers ϖ) M) :=
    hM.subsingleton_of_isLocalizedModule_away hϖ (f := LocalizedModule.mkLinearMap _ _)
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    (M.localizedModuleIso (Submonoid.powers ϖ))

/-- **Inverting an element `ϖ ∈ m` on almost modules** (Gabber–Ramero §5.2, proof of Corollary
5.2.15; Bhatt §4.1, Exercise 4.1.9): the exact functor `ModuleCat.localizedModuleFunctor` at the
powers of `ϖ` kills almost zero modules, hence factors through the Serre quotient
`Almost.Module S`. -/
noncomputable def invert {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module S ⥤ ModuleCat.{u} (Localization.Away ϖ) :=
  Module.lift S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj_of_isAlmostZero S hϖ)

/-- Precomposing `invert S hϖ` with almostification recovers `ModuleCat.localizedModuleFunctor` at
the powers of `ϖ`. -/
noncomputable def toAlmostCompInvertIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ) :=
  Module.fac S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj_of_isAlmostZero S hϖ)

/-- `invert S hϖ` lifts `ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ)` along
`Module.toAlmost S`. -/
noncomputable instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Localization.Lifting (Module.toAlmost S) S.almostZero.isoModSerre
      (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)) (invert S hϖ) :=
  ⟨toAlmostCompInvertIso S hϖ⟩

/-- Precomposing `invert S hϖ` with almostification is naturally isomorphic to extension of scalars
along `V → Localization.Away ϖ`. -/
noncomputable def toAlmostCompInvertExtendScalarsIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)) :=
  toAlmostCompInvertIso S hϖ ≪≫
    ModuleCat.localizedModuleFunctorIsoExtendScalars (Submonoid.powers ϖ)

/-- `invert S hϖ` lifts `ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))` along
`Module.toAlmost S`. -/
noncomputable instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Localization.Lifting (Module.toAlmost S) S.almostZero.isoModSerre
      (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))) (invert S hϖ) :=
  ⟨toAlmostCompInvertExtendScalarsIso S hϖ⟩

/-- `invert S hϖ` preserves finite limits. -/
instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) : PreservesFiniteLimits (invert S hϖ) := by
  dsimp only [invert]
  infer_instance

/-- `invert S hϖ` preserves finite colimits. -/
instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) : PreservesFiniteColimits (invert S hϖ) := by
  dsimp only [invert]
  infer_instance

/-- `invert S hϖ` is an additive functor. -/
instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) : (invert S hϖ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Uniqueness of `invert S hϖ`: any functor `G` whose precomposition with `Module.toAlmost S` is
isomorphic to `ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ)` is canonically isomorphic to
`invert S hϖ`. -/
noncomputable def invertUniq {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (G : Module S ⥤ ModuleCat.{u} (Localization.Away ϖ))
    (e : Module.toAlmost S ⋙ G ≅ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)) :
    G ≅ invert S hϖ :=
  Module.liftUniq S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj_of_isAlmostZero S hϖ) G e

/-- On an almostification `M^a`, `(invert S hϖ).obj (M^a)` is canonically isomorphic to
`LocalizedModule.Away ϖ M`. -/
noncomputable def invertToAlmostObjIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) (M : ModuleCat.{u} V) :
    (invert S hϖ).obj ((Module.toAlmost S).obj M) ≅
      ModuleCat.of (Localization.Away ϖ) (LocalizedModule.Away ϖ M) :=
  (toAlmostCompInvertIso S hϖ).app M ≪≫ M.localizedModuleIso (Submonoid.powers ϖ)

/-- `invert S hϖ` is naturally isomorphic to almost elements followed by module localization away
from `ϖ`. -/
noncomputable def invertIsoElementsLocalized {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    invert S hϖ ≅
      Module.elements S ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ) :=
  (Functor.leftUnitor (invert S hϖ)).symm ≪≫
    Functor.isoWhiskerRight (asIso (Module.adjElements S).counit).symm (invert S hϖ) ≪≫
    Functor.associator (Module.elements S) (Module.toAlmost S) (invert S hϖ) ≪≫
    Functor.isoWhiskerLeft (Module.elements S) (toAlmostCompInvertIso S hϖ)

/-- For every almost module `M`, `(invert S hϖ).obj M` is canonically isomorphic to
`LocalizedModule.Away ϖ ((Module.elements S).obj M)` (`M_*[1/ϖ]`). -/
noncomputable def invertElementsIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) (M : Module S) :
    (invert S hϖ).obj M ≅
      ModuleCat.of (Localization.Away ϖ)
        (LocalizedModule.Away ϖ ((Module.elements S).obj M)) :=
  (invertIsoElementsLocalized S hϖ).app M ≪≫
    ((Module.elements S).obj M).localizedModuleIso (Submonoid.powers ϖ)

/-- `invert S hϖ` is naturally isomorphic to `Module.shriek S` followed by module localization away
from `ϖ`. -/
noncomputable def invertIsoShriekLocalized {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    invert S hϖ ≅
      Module.shriek S ⋙ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ) :=
  (Functor.leftUnitor (invert S hϖ)).symm ≪≫
    Functor.isoWhiskerRight (asIso (Module.adjShriek S).unit) (invert S hϖ) ≪≫
    Functor.associator (Module.shriek S) (Module.toAlmost S) (invert S hϖ) ≪≫
    Functor.isoWhiskerLeft (Module.shriek S) (toAlmostCompInvertIso S hϖ)

/-- For every almost module `M`, `(invert S hϖ).obj M` is canonically isomorphic to
`LocalizedModule.Away ϖ ((Module.shriek S).obj M)` (`M_![1/ϖ]`). -/
noncomputable def invertShriekIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) (M : Module S) :
    (invert S hϖ).obj M ≅
      ModuleCat.of (Localization.Away ϖ)
        (LocalizedModule.Away ϖ ((Module.shriek S).obj M)) :=
  (invertIsoShriekLocalized S hϖ).app M ≪≫
    ((Module.shriek S).obj M).localizedModuleIso (Submonoid.powers ϖ)

/-- The canonical comparison `M_! → M_*` induces the transition between `invertIsoShriekLocalized`
and `invertIsoElementsLocalized` after inverting `ϖ`. -/
theorem invertIsoShriekLocalized_hom_comp_whiskerRight {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (invertIsoShriekLocalized S hϖ).hom ≫
        Functor.whiskerRight (Module.shriekToElements S)
          (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)) =
      (invertIsoElementsLocalized S hϖ).hom := by
  ext1
  funext M
  have key := ((Module.adjElements S).homEquiv _ _).symm_apply_apply
    (inv ((Module.adjShriek S).unit.app M))
  rw [Adjunction.homEquiv_counit, ← Module.shriekToElements_app] at key
  dsimp only [Functor.id_obj] at key
  have hnat := (toAlmostCompInvertIso S hϖ).hom.naturality ((Module.shriekToElements S).app M)
  dsimp [invertIsoShriekLocalized, invertIsoElementsLocalized] at hnat ⊢
  simp only [Category.id_comp, Category.assoc]
  rw [← hnat, ← Category.assoc, ← (invert S hϖ).map_comp]
  congr 1
  apply congrArg (invert S hϖ).map
  apply (cancel_mono ((Module.adjElements S).counit.app M)).mp
  rw [Category.assoc, key, IsIso.hom_inv_id, ← NatTrans.comp_app, IsIso.inv_hom_id,
    NatTrans.id_app]
  rfl

private theorem naturality_comp_localizedModuleIso {C : Type*} [Category C] {ϖ : V}
    {F : C ⥤ ModuleCat.{u} (Localization.Away ϖ)} {G : C ⥤ ModuleCat.{u} V}
    (e : ∀ X : C, F.obj X ≅ (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).obj
      (G.obj X))
    (hnat : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (e Y).hom =
        (e X).hom ≫
          (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map (G.map f))
    {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (e Y ≪≫ (G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom =
      (e X ≪≫ (G.obj X).localizedModuleIso (Submonoid.powers ϖ)).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) (G.map f).hom) := by
  have h1 := hnat f
  have h2 : (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map (G.map f) ≫
        ((G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom =
      ((G.obj X).localizedModuleIso (Submonoid.powers ϖ)).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) (G.map f).hom) :=
    ModuleCat.localizedModuleIso_naturality (G.map f)
  calc F.map f ≫ (e Y).hom ≫ ((G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom
      = (F.map f ≫ (e Y).hom) ≫ ((G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom :=
          (Category.assoc _ _ _).symm
    _ = ((e X).hom ≫
            (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map (G.map f)) ≫
          ((G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom :=
          congrArg (· ≫ _) h1
    _ = (e X).hom ≫
          ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map (G.map f) ≫
            ((G.obj Y).localizedModuleIso (Submonoid.powers ϖ)).hom) :=
          Category.assoc _ _ _
    _ = (e X).hom ≫
          (((G.obj X).localizedModuleIso (Submonoid.powers ϖ)).hom ≫
            ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) (G.map f).hom)) :=
          congrArg (_ ≫ ·) h2
    _ = ((e X).hom ≫ ((G.obj X).localizedModuleIso (Submonoid.powers ϖ)).hom) ≫
          ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) (G.map f).hom) :=
          (Category.assoc _ _ _).symm

/-- Naturality of `invertToAlmostObjIso`: `(invert S hϖ).map (f^a)` acts as
`LocalizedModule.map` on `LocalizedModule.Away ϖ`. -/
@[reassoc]
theorem invert_map_toAlmost_comp_invertToAlmostObjIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : ModuleCat.{u} V} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map ((Module.toAlmost S).map f) ≫ (invertToAlmostObjIso S hϖ M₂).hom =
      (invertToAlmostObjIso S hϖ M₁).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) f.hom) :=
  naturality_comp_localizedModuleIso (F := Module.toAlmost S ⋙ invert S hϖ)
    (G := 𝟭 (ModuleCat.{u} V))
    (fun M ↦ (toAlmostCompInvertIso S hϖ).app M)
    (fun g ↦ (toAlmostCompInvertIso S hϖ).hom.naturality g) f

/-- Naturality of `invertElementsIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.elements S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertElementsIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertElementsIso S hϖ M₂).hom =
      (invertElementsIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.elements S).map f).hom) :=
  naturality_comp_localizedModuleIso (F := invert S hϖ) (G := Module.elements S)
    (fun M ↦ (invertIsoElementsLocalized S hϖ).app M)
    (fun g ↦ (invertIsoElementsLocalized S hϖ).hom.naturality g) f

/-- Naturality of `invertShriekIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.shriek S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertShriekIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertShriekIso S hϖ M₂).hom =
      (invertShriekIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.shriek S).map f).hom) :=
  naturality_comp_localizedModuleIso (F := invert S hϖ) (G := Module.shriek S)
    (fun M ↦ (invertIsoShriekLocalized S hϖ).app M)
    (fun g ↦ (invertIsoShriekLocalized S hϖ).hom.naturality g) f

/-! ### Degenerate cases, basic computations, and non-faithfulness -/

/-- `(invert S hϖ).obj (M^a)` is zero iff every element of `M` is annihilated by a power of `ϖ`. -/
theorem isZero_invert_toAlmost_obj_iff {ϖ : V} (hϖ : ϖ ∈ S.ideal) (M : ModuleCat.{u} V) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj M)) ↔
      ∀ x : M, ∃ n : ℕ, (ϖ ^ n) • x = 0 := by
  rw [(invertToAlmostObjIso S hϖ M).isZero_iff, ModuleCat.isZero_of_iff_subsingleton,
    LocalizedModule.subsingleton_iff]
  simp [Submonoid.mem_powers_iff]

/-- `(invert S hϖ).obj M` is zero iff every almost element of `M` is annihilated by a power of
`ϖ`. -/
theorem isZero_invert_obj_iff {ϖ : V} (hϖ : ϖ ∈ S.ideal) (M : Module S) :
    IsZero ((invert S hϖ).obj M) ↔
      ∀ x : (Module.elements S).obj M, ∃ n : ℕ, (ϖ ^ n) • x = 0 := by
  rw [(invertElementsIso S hϖ M).isZero_iff, ModuleCat.isZero_of_iff_subsingleton,
    LocalizedModule.subsingleton_iff]
  simp [Submonoid.mem_powers_iff]

/-- Inverting `0 ∈ m` sends every almost module to a zero object. -/
theorem isZero_invert_obj_zero (M : Module S) :
    IsZero ((invert S S.ideal.zero_mem).obj M) :=
  (isZero_invert_obj_iff S S.ideal.zero_mem M).mpr fun _ ↦ ⟨1, by simp⟩

/-- Inverting `ϖ ∈ m` kills the almostification of any `V`-module in which every element is
annihilated by a power of `ϖ`. -/
theorem isZero_invert_toAlmost_of_pow_smul_eq_zero {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (M : ModuleCat.{u} V) (hM : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj M)) :=
  (isZero_invert_toAlmost_obj_iff S hϖ M).mpr hM

/-- Inverting `ϖ ∈ m` sends `(V ⧸ (ϖ))^a` to a zero object. -/
theorem isZero_invert_toAlmost_quotient_span_singleton {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V (V ⧸ Ideal.span {ϖ})))) := by
  refine isZero_invert_toAlmost_of_pow_smul_eq_zero S hϖ _ fun x ↦ ⟨1, ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [pow_one, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right ϖ v)

/-- Inverting `ϖ ∈ m` sends `V^a` to the free rank-one `Localization.Away ϖ`-module
`Localization.Away ϖ`. -/
noncomputable def invertToAlmostRingIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V V)) ≅
      ModuleCat.of (Localization.Away ϖ) (Localization.Away ϖ) :=
  invertToAlmostObjIso S hϖ (ModuleCat.of V V) ≪≫
    (LocalizedModule.equivLocalization (Submonoid.powers ϖ)).toModuleIso

/-- Whenever `V ⧸ (ϖ)` is not almost zero (for example for `BasicSetup.ofValuationRing` and any
`ϖ ∈ m`), `(V ⧸ (ϖ))^a` is nonzero in `Almost.Module S` while `invert S hϖ` kills it, so
`invert S hϖ` is not faithful (Bhatt §4.1, Exercise 4.1.9). -/
theorem not_faithful_invert_of_not_isAlmostZero_quotient {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (hquot : ¬ S.IsAlmostZero (V ⧸ Ideal.span {ϖ})) :
    ¬ (invert S hϖ).Faithful := by
  intro hfaith
  let X := (Module.toAlmost S).obj (ModuleCat.of V (V ⧸ Ideal.span {ϖ}))
  have hX : ¬ IsZero X := by
    rwa [Module.isZero_toAlmost_obj_iff]
  apply hX
  rw [IsZero.iff_id_eq_zero]
  exact hfaith.map_injective
    ((isZero_invert_toAlmost_quotient_span_singleton S hϖ).eq_of_src _ _)

/-- When `ϖ ∈ m` is a unit of `V`, `S` is the classical setup and `V → Localization.Away ϖ` is a
ring isomorphism, so `invert S hϖ` is an equivalence of categories. -/
theorem isEquivalence_invert_of_isUnit {ϖ : V} (hϖ : ϖ ∈ S.ideal) (hu : IsUnit ϖ) :
    (invert S hϖ).IsEquivalence := by
  have hS : S = BasicSetup.classical V := BasicSetup.eq_classical_of_isUnit_mem hϖ hu
  subst hS
  let eR : V ≃+* Localization.Away ϖ :=
    (IsLocalization.atUnits V (Submonoid.powers ϖ) (S := Localization.Away ϖ)
      (by rintro _ ⟨n, rfl⟩; exact hu.pow n)).toRingEquiv
  have hext : (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))).IsEquivalence := by
    have : (ModuleCat.restrictScalars eR.toRingHom).IsEquivalence := inferInstance
    exact (ModuleCat.extendRestrictScalarsAdj
      eR.toRingHom).isEquivalence_left_of_isEquivalence_right
  have hcomp : (Module.toAlmost (BasicSetup.classical V) ⋙
      invert (BasicSetup.classical V) hϖ).IsEquivalence :=
    Functor.isEquivalence_of_iso (toAlmostCompInvertExtendScalarsIso _ hϖ).symm
  exact Functor.isEquivalence_of_comp_left (Module.toAlmost (BasicSetup.classical V))
    (invert (BasicSetup.classical V) hϖ)

/-- When `ϖ ∈ m` is a unit of `V`, restricting scalars along `V ≃ Localization.Away ϖ` after
`invert S hϖ` recovers `Module.elements S`. -/
noncomputable def invertCompRestrictScalarsIsoElementsOfIsUnit {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (hu : IsUnit ϖ) :
    invert S hϖ ⋙ ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)) ≅
      Module.elements S := by
  let eR : V ≃+* Localization.Away ϖ :=
    (IsLocalization.atUnits V (Submonoid.powers ϖ) (S := Localization.Away ϖ)
      (by rintro _ ⟨n, rfl⟩; exact hu.pow n)).toRingEquiv
  have : IsIso (ModuleCat.extendRestrictScalarsAdj eR.toRingHom).unit := by
    have : (ModuleCat.extendScalars eR.toRingHom).IsEquivalence :=
      (ModuleCat.extendRestrictScalarsAdj eR.toRingHom).isEquivalence_left_of_isEquivalence_right
    infer_instance
  let eId : ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ) ⋙
      ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)) ≅ 𝟭 (ModuleCat.{u} V) :=
    Functor.isoWhiskerRight (ModuleCat.localizedModuleFunctorIsoExtendScalars (Submonoid.powers ϖ))
      (ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ))) ≪≫
      (asIso (ModuleCat.extendRestrictScalarsAdj eR.toRingHom).unit).symm
  exact Functor.isoWhiskerRight (invertIsoElementsLocalized S hϖ)
      (ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ))) ≪≫
    Functor.associator (Module.elements S) _ _ ≪≫
    Functor.isoWhiskerLeft (Module.elements S) eId ≪≫
    Functor.rightUnitor (Module.elements S)

end ModuleInvert

/-! ### Symmetric monoidal structure on `Almost.invert` -/

section Monoidal

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- **Inverting `ϖ ∈ m` is a strong monoidal functor**, lifting the monoidal structure of
`ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))` along almostification. -/
noncomputable instance invertMonoidal {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (invert S hϖ).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (Module.toAlmost S) S.almostZero.isoModSerre
    (invert S hϖ) (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)))

/-- **Inverting `ϖ ∈ m` is a braided monoidal functor**, compatible with the symmetric braidings on
`Almost.Module S` and `ModuleCat (Localization.Away ϖ)`. -/
noncomputable instance invertBraided {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (invert S hϖ).Braided :=
  Localization.Monoidal.functorBraidedOfComp (Module.toAlmost S) S.almostZero.isoModSerre
    (invert S hϖ) (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)))

/-- The comparison `Module.toAlmost S ⋙ invert S hϖ ≅ ModuleCat.extendScalars ...` is monoidal. -/
instance isMonoidal_toAlmostCompInvertExtendScalarsIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    (toAlmostCompInvertExtendScalarsIso S hϖ).hom.IsMonoidal :=
  -- `toAlmostCompInvertExtendScalarsIso S hϖ` is the registered `Lifting.iso` for `extendScalars`.
  Localization.Monoidal.lifting_isMonoidal (Module.toAlmost S) S.almostZero.isoModSerre
    (invert S hϖ) (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)))

end Monoidal

/-! ### Inverting a scalar on almost algebras -/

namespace Algebra

open scoped ModuleCat.MonModuleEquivalenceAlgebra

attribute [local instance] ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- **Inverting a scalar `ϖ : V` on almost algebras**: sends an almost `V`-algebra `A` to the
localized `Localization.Away ϖ`-algebra `A_*[1/ϖ]`, and a morphism `f : A ⟶ B` to the localized map
induced by `(Algebra.elements S).map f`. -/
noncomputable def invert (ϖ : V) :
    Algebra S ⥤ CommAlgCat.{u} (Localization.Away ϖ) :=
  Algebra.elements S ⋙ CommAlgCat.localizationFunctor (Submonoid.powers ϖ)

/-- Object value of `Algebra.invert S ϖ` on `A`. -/
@[simp]
theorem invert_obj (ϖ : V) (A : Algebra S) :
    (invert S ϖ).obj A =
      (CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A) :=
  (rfl)

/-- `V`-algebra structure on `(Algebra.invert S ϖ).obj A`. -/
noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra V ((invert S ϖ).obj A) :=
  inferInstanceAs
    (_root_.Algebra V
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

/-- `(Algebra.elements S).obj A`-algebra structure on `(Algebra.invert S ϖ).obj A`. -/
noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra ((Algebra.elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (_root_.Algebra ((Algebra.elements S).obj A)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

/-- Compatibility of the `V`- and `(Algebra.elements S).obj A`-algebra structures on
`(Algebra.invert S ϖ).obj A`. -/
instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V ((Algebra.elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (IsScalarTower V ((Algebra.elements S).obj A)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

/-- Compatibility of the `V`- and `Localization.Away ϖ`-algebra structures on
`(Algebra.invert S ϖ).obj A`. -/
instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V (Localization.Away ϖ) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (IsScalarTower V (Localization.Away ϖ)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

/-- `(Algebra.invert S ϖ).obj A` is a localization of `(Algebra.elements S).obj A` at the image of
`Submonoid.powers ϖ`. -/
instance (ϖ : V) (A : Algebra S) :
    IsLocalization
      (_root_.Algebra.algebraMapSubmonoid ((Algebra.elements S).obj A) (Submonoid.powers ϖ))
      ((invert S ϖ).obj A) :=
  inferInstanceAs
    (IsLocalization
      (_root_.Algebra.algebraMapSubmonoid ((Algebra.elements S).obj A) (Submonoid.powers ϖ))
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

/-- On canonical numerators `algebraMap A_* (A_*[1/ϖ]) a`, `(Algebra.invert S ϖ).map f` is induced
by `(Algebra.elements S).map f`. -/
@[simp]
theorem invert_map_hom_algebraMap (ϖ : V) {A B : Algebra S}
    (f : A ⟶ B) (a : (Algebra.elements S).obj A) :
    ((invert S ϖ).map f).hom (algebraMap ((Algebra.elements S).obj A) ((invert S ϖ).obj A) a) =
      algebraMap ((Algebra.elements S).obj B) ((invert S ϖ).obj B)
        (((Algebra.elements S).map f).hom a) :=
  CommAlgCat.localizationFunctor_map_hom_algebraMap (Submonoid.powers ϖ)
    ((Algebra.elements S).map f) a

/-- On fractions `a / ϖ^n`, `(Algebra.invert S ϖ).map f` applies `(Algebra.elements S).map f` to
the numerator. -/
@[simp]
theorem invert_map_hom_mk' (ϖ : V) {A B : Algebra S}
    (f : A ⟶ B) (a : (Algebra.elements S).obj A) (m : Submonoid.powers ϖ) :
    ((invert S ϖ).map f).hom
        (IsLocalization.mk' ((invert S ϖ).obj A) a
          ⟨algebraMap V ((Algebra.elements S).obj A) m,
            _root_.Algebra.mem_algebraMapSubmonoid_of_mem m⟩) =
      IsLocalization.mk' ((invert S ϖ).obj B) (((Algebra.elements S).map f).hom a)
        ⟨algebraMap V ((Algebra.elements S).obj B) m,
          _root_.Algebra.mem_algebraMapSubmonoid_of_mem m⟩ :=
  CommAlgCat.localizationFunctor_map_hom_mk' (Submonoid.powers ϖ)
    ((Algebra.elements S).map f) a m

private theorem isIso_localizationFunctor_map_adj_unit_app {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (R : CommAlgCat.{u} V) :
    IsIso ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).map
      ((Algebra.adj S).unit.app R)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hbij := (Algebra.isAlmostIso_adj_unit_app S R).bijective_isLocalizedModule_map_away
    (IsScalarTower.toAlgHom V R
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj R)).toLinearMap
    (IsScalarTower.toAlgHom V ((Algebra.elements S).obj ((Algebra.toAlmost S).obj R))
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj
        ((Algebra.elements S).obj ((Algebra.toAlmost S).obj R)))).toLinearMap hϖ
  have heq := CommAlgCat.localizationFunctor_map_toLinearMap (Submonoid.powers ϖ)
    ((Algebra.adj S).unit.app R)
  have hlin :
      Function.Bijective
        (((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).map
          ((Algebra.adj S).unit.app R)).hom.toLinearMap.restrictScalars V) :=
    heq ▸ hbij
  exact hlin

/-- When `ϖ ∈ m`, precomposing `Algebra.invert S ϖ` with `Algebra.toAlmost S` recovers ordinary
localization of commutative `V`-algebras away from `ϖ`, because the unit `R → (R^a)_*` is an
almost isomorphism. -/
noncomputable def toAlmostCompInvertIso {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Algebra.toAlmost S ⋙ invert S ϖ ≅
      CommAlgCat.localizationFunctor (Submonoid.powers ϖ) :=
  have := isIso_localizationFunctor_map_adj_unit_app S hϖ
  NatIso.ofComponents
    (fun R ↦
      (asIso ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).map
        ((Algebra.adj S).unit.app R))).symm)
    fun {R R'} f ↦ by
      dsimp [invert]
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp,
        ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ((Algebra.adj S).unit.naturality f).symm

/-- Inverse component of `Algebra.toAlmostCompInvertIso` on canonical numerators
`algebraMap R _ r`. -/
theorem toAlmostCompInvertIso_inv_app_hom_algebraMap {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (R : CommAlgCat.{u} V) (r : R) :
    ((toAlmostCompInvertIso S hϖ).inv.app R).hom
        (algebraMap R ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj R) r) =
      algebraMap ((Algebra.elements S).obj ((Algebra.toAlmost S).obj R))
        ((invert S ϖ).obj ((Algebra.toAlmost S).obj R)) (((Algebra.adj S).unit.app R).hom r) :=
  CommAlgCat.localizationFunctor_map_hom_algebraMap (Submonoid.powers ϖ)
    ((Algebra.adj S).unit.app R) r

/-- Forward component of `Algebra.toAlmostCompInvertIso` on images of the unit `R → (R^a)_*`. -/
theorem toAlmostCompInvertIso_hom_app_hom_algebraMap_unit {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (R : CommAlgCat.{u} V) (r : R) :
    ((toAlmostCompInvertIso S hϖ).hom.app R).hom
        (algebraMap ((Algebra.elements S).obj ((Algebra.toAlmost S).obj R))
          ((invert S ϖ).obj ((Algebra.toAlmost S).obj R))
          (((Algebra.adj S).unit.app R).hom r)) =
      algebraMap R ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj R) r := by
  have h := congrArg
    (fun f ↦ f.hom (algebraMap R ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj R) r))
    ((toAlmostCompInvertIso S hϖ).inv_hom_id_app R)
  rwa [CommAlgCat.hom_comp, AlgHom.comp_apply, toAlmostCompInvertIso_inv_app_hom_algebraMap,
    CommAlgCat.hom_id, AlgHom.id_apply] at h

/-- When `ϖ` maps to a unit in `A_*`, inverting `ϖ` preserves the `V`-algebra `A_*` of almost
elements. -/
noncomputable def invertObjAlgEquivOfIsUnitAlgebraMap {ϖ : V} (A : Algebra S)
    (hu : IsUnit (algebraMap V ((Algebra.elements S).obj A) ϖ)) :
    (Algebra.elements S).obj A ≃ₐ[V] (invert S ϖ).obj A :=
  CommAlgCat.localizationFunctorObjAlgEquivOfIsUnit ((Algebra.elements S).obj A) <| by
    rintro _ ⟨n, rfl⟩
    rw [map_pow]
    exact hu.pow n

/-- `invertObjAlgEquivOfIsUnitAlgebraMap` acts as `algebraMap A_* _`. -/
@[simp]
theorem invertObjAlgEquivOfIsUnitAlgebraMap_apply {ϖ : V} (A : Algebra S)
    (hu : IsUnit (algebraMap V ((Algebra.elements S).obj A) ϖ))
    (a : (Algebra.elements S).obj A) :
    invertObjAlgEquivOfIsUnitAlgebraMap S A hu a =
      algebraMap ((Algebra.elements S).obj A) ((invert S ϖ).obj A) a :=
  CommAlgCat.localizationFunctorObjAlgEquivOfIsUnit_apply ((Algebra.elements S).obj A) _ a

/-- Inverting a unit `ϖ` of `V` preserves the `V`-algebra `A_*` of almost elements. -/
noncomputable def invertObjAlgEquivOfIsUnit {ϖ : V} (A : Algebra S) (hu : IsUnit ϖ) :
    (Algebra.elements S).obj A ≃ₐ[V] (invert S ϖ).obj A :=
  invertObjAlgEquivOfIsUnitAlgebraMap S A (hu.map _)

/-- `invertObjAlgEquivOfIsUnit` acts as `algebraMap A_* _`. -/
@[simp]
theorem invertObjAlgEquivOfIsUnit_apply {ϖ : V} (A : Algebra S) (hu : IsUnit ϖ)
    (a : (Algebra.elements S).obj A) :
    invertObjAlgEquivOfIsUnit S A hu a =
      algebraMap ((Algebra.elements S).obj A) ((invert S ϖ).obj A) a :=
  invertObjAlgEquivOfIsUnitAlgebraMap_apply S A (hu.map _) a

/-- `(Algebra.invert S ϖ).obj A` is a localization of `(Algebra.elements S).obj A` away from
`algebraMap V A_* ϖ`. -/
instance isLocalizationAway_invert_obj (ϖ : V) (A : Algebra S) :
    IsLocalization.Away (algebraMap V ((elements S).obj A) ϖ) ((invert S ϖ).obj A) := by
  unfold IsLocalization.Away
  rw [← _root_.Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- `(Algebra.invert S ϖ).obj A` is the zero ring iff a power of `ϖ` maps to `0` in `A_*`. -/
theorem subsingleton_invert_obj_iff (ϖ : V) (A : Algebra S) :
    Subsingleton ((invert S ϖ).obj A) ↔
      ∃ n : ℕ, algebraMap V ((elements S).obj A) (ϖ ^ n) = 0 := by
  rw [IsLocalization.subsingleton_iff (M := Submonoid.powers (algebraMap V ((elements S).obj A) ϖ))
    (S := (invert S ϖ).obj A)]
  simp [Submonoid.mem_powers_iff, map_pow]

/-- Inverting `0 : V` sends every almost algebra to the zero algebra. -/
instance subsingleton_invert_obj_zero (A : Algebra S) :
    Subsingleton ((invert S (0 : V)).obj A) :=
  (subsingleton_invert_obj_iff S 0 A).mpr ⟨1, by simp⟩

/-- An almost algebra whose unit element (equivalently every almost element) is annihilated by a
power of `ϖ` becomes the zero algebra after inverting `ϖ`. -/
theorem subsingleton_invert_obj_of_pow_smul_one_eq_zero {ϖ : V}
    {A : Algebra S} {n : ℕ} (h : ϖ ^ n • (1 : (Algebra.elements S).obj A) = 0) :
    Subsingleton ((invert S ϖ).obj A) :=
  (subsingleton_invert_obj_iff S ϖ A).mpr ⟨n, by simpa [_root_.Algebra.smul_def] using h⟩

/-- For `ϖ ∈ m`, `Algebra.invert S ϖ` is naturally isomorphic to the functor induced on
commutative monoid objects by the braided monoidal functor `Almost.invert S hϖ`. -/
noncomputable def invertIsoMapCommMon {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    invert S ϖ ≅
      (Almost.invert S hϖ).mapCommMon ⋙
        ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor :=
  let eExt :
      (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))).mapCommMon ≅
        (Module.toAlmost S).mapCommMon ⋙ (Almost.invert S hϖ).mapCommMon :=
    (Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).symm ≪≫
      Functor.mapCommMonCompIso
  let eLeft := Functor.isoWhiskerLeft (elements S)
    (CommAlgCat.localizationFunctorIsoExtendScalars (Submonoid.powers ϖ) ≪≫
      CommAlgCat.extendScalarsIsoMapCommMon V (Localization.Away ϖ))
  let eMid := Functor.isoWhiskerLeft (elements S)
    (Functor.isoWhiskerLeft ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse
      (Functor.isoWhiskerRight eExt ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor))
  let eRight := Functor.isoWhiskerRight (counitIso S)
    ((Almost.invert S hϖ).mapCommMon ⋙
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor) ≪≫
    Functor.leftUnitor _
  eLeft ≪≫ eMid ≪≫ eRight

/-- On canonical numerators `algebraMap A_* _ x`, `invertIsoMapCommMon` applies the inverse of
`toAlmostCompInvertExtendScalarsIso` followed by the counit of `Module.adjElements`. -/
@[simp]
theorem invertIsoMapCommMon_hom_app_algebraMap {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (A : Algebra S) (x : (elements S).obj A) :
    dsimp% only [CategoryTheory.Functor.comp_obj] ((invertIsoMapCommMon S hϖ).hom.app A)
        (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
      (Almost.invert S hϖ).map ((Module.adjElements S).counit.app A.X)
        ((toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
          (ModuleCat.of V ((elements S).obj A))
          ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) := by
  have hstep1 :
      ((CommAlgCat.localizationFunctorIsoExtendScalars (Submonoid.powers ϖ)).hom.app
          ((elements S).obj A))
          (algebraMap ((elements S).obj A)
            ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((elements S).obj A)) x) =
        (1 : Localization.Away ϖ) ⊗ₜ[V] x :=
    CommAlgCat.localizationFunctorIsoExtendScalars_hom_app_algebraMap (Submonoid.powers ϖ)
      ((elements S).obj A) x
  have hstep2 :
      ((CommAlgCat.extendScalarsIsoMapCommMon V (Localization.Away ϖ)).hom.app
          ((elements S).obj A))
          ((1 : Localization.Away ϖ) ⊗ₜ[V] x) =
        (1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x :=
    CommAlgCat.extendScalarsIsoMapCommMon_hom_app_tmul V (Localization.Away ϖ)
      ((elements S).obj A) 1 x
  have hstep3 :
      (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
          (((Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).symm ≪≫
            Functor.mapCommMonCompIso).hom.app
              (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A))))
          ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x) =
        (toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
          (ModuleCat.of V ((elements S).obj A))
          ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x) :=
    rfl
  have hstep4 :
      ((Almost.invert S hϖ).mapCommMon ⋙
          ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor).map
          ((counitIso S).hom.app A)
          ((toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
            (ModuleCat.of V ((elements S).obj A))
            ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) =
        (Almost.invert S hϖ).map ((Module.adjElements S).counit.app A.X)
          ((toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
            (ModuleCat.of V ((elements S).obj A))
            ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) := by
    have hc : ((counitIso S).hom.app A).hom.hom = (Module.adjElements S).counit.app A.X := by
      rw [counitIso_hom, adj_counit_app_hom_hom]
    exact (rfl :
        ((Almost.invert S hϖ).mapCommMon ⋙
            ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor).map
            ((counitIso S).hom.app A)
            ((toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
              (ModuleCat.of V ((elements S).obj A))
              ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) =
          (Almost.invert S hϖ).map ((counitIso S).hom.app A).hom.hom
            ((toAlmostCompInvertExtendScalarsIso S hϖ).inv.app
              (ModuleCat.of V ((elements S).obj A))
              ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x))).trans
      (congrArg (fun g ↦ (Almost.invert S hϖ).map g _) hc)
  have h0 :
      ((invertIsoMapCommMon S hϖ).hom.app A)
          (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
        ((Almost.invert S hϖ).mapCommMon ⋙
            ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor).map
            ((counitIso S).hom.app A)
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
            (((Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).symm ≪≫
              Functor.mapCommMonCompIso).hom.app
                (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A)))
            (((CommAlgCat.extendScalarsIsoMapCommMon V (Localization.Away ϖ)).hom.app
                ((elements S).obj A))
              (((CommAlgCat.localizationFunctorIsoExtendScalars (Submonoid.powers ϖ)).hom.app
                  ((elements S).obj A))
                (algebraMap ((elements S).obj A)
                  ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj
                    ((elements S).obj A)) x)))) :=
    rfl
  refine h0.trans ?_
  refine (congrArg _ (congrArg _ (congrArg _ hstep1))).trans ?_
  refine (congrArg _ (congrArg _ hstep2)).trans ?_
  refine (congrArg _ hstep3).trans hstep4

/-- For `ϖ ∈ m` and an honest commutative `V`-algebra `R`, `(Algebra.invert S ϖ).obj (R^a)` is
canonically isomorphic as a `Localization.Away ϖ`-algebra to `R[1/ϖ]`. -/
noncomputable def invertToAlmostObjEquiv {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) :
    ((invert S ϖ).obj ((toAlmost S).obj R)) ≃ₐ[Localization.Away ϖ]
      Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)) :=
  (CommAlgCat.algEquivOfIso
    ((toAlmostCompInvertIso S hϖ).app R ≪≫
      (CommAlgCat.localizationFunctorIsoExtendScalars (Submonoid.powers ϖ)).app R)).trans
    (Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) R)

/-- The inverse of `invertToAlmostObjEquiv` sends a canonical numerator `algebraMap R R[1/ϖ] r` to
the canonical numerator of `(adj S).unit.app R r` in `(R^a)_*[1/ϖ]`. -/
@[simp]
theorem invertToAlmostObjEquiv_symm_algebraMap {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (R : CommAlgCat.{u} V) (r : R) :
    (invertToAlmostObjEquiv S hϖ R).symm
        (algebraMap R (Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)))
          r) =
      algebraMap ((elements S).obj ((toAlmost S).obj R))
        ((invert S ϖ).obj ((toAlmost S).obj R)) (((adj S).unit.app R).hom r) := by
  have h1 : (Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) R).symm
      (algebraMap R (Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)))
        r) =
      (1 : Localization.Away ϖ) ⊗ₜ[V] r :=
    (AlgEquiv.symm_apply_eq _).mpr (Localization.tensorRightAlgEquiv_apply_one_tmul _ r).symm
  rw [invertToAlmostObjEquiv, AlgEquiv.symm_trans_apply, h1,
    CommAlgCat.algEquivOfIso_symm_apply, Iso.trans_inv, ConcreteCategory.comp_apply,
    Iso.app_inv, Iso.app_inv,
    CommAlgCat.localizationFunctorIsoExtendScalars_inv_app_one_tmul]
  exact toAlmostCompInvertIso_inv_app_hom_algebraMap S hϖ R r

-- Simplify top-down before `adj_unit_app_apply` expands `(adj S).unit.app R r` into a
-- `toSpanSingleton` morphism.
/-- `invertToAlmostObjEquiv` sends the canonical numerator of `(adj S).unit.app R r` in
`(R^a)_*[1/ϖ]` to `algebraMap R R[1/ϖ] r`. -/
@[simp↓]
theorem invertToAlmostObjEquiv_algebraMap_unit_app {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (R : CommAlgCat.{u} V) (r : R) :
    invertToAlmostObjEquiv S hϖ R
        (algebraMap ((elements S).obj ((toAlmost S).obj R))
          ((invert S ϖ).obj ((toAlmost S).obj R)) (((adj S).unit.app R).hom r)) =
      algebraMap R
        (Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ))) r := by
  rw [invertToAlmostObjEquiv, AlgEquiv.trans_apply, CommAlgCat.algEquivOfIso_apply,
    Iso.trans_hom, ConcreteCategory.comp_apply, Iso.app_hom, Iso.app_hom,
    toAlmostCompInvertIso_hom_app_hom_algebraMap_unit,
    CommAlgCat.localizationFunctorIsoExtendScalars_hom_app_algebraMap,
    Localization.tensorRightAlgEquiv_apply_one_tmul]

/-- For `ϖ ∈ m`, `(Algebra.invert S ϖ).obj (R^a)` is the zero ring iff a power of `ϖ` maps to `0`
in `R`. -/
theorem subsingleton_invert_toAlmost_obj_iff {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) :
    Subsingleton ((invert S ϖ).obj ((toAlmost S).obj R)) ↔
      ∃ n : ℕ, algebraMap V R (ϖ ^ n) = 0 := by
  rw [(invertToAlmostObjEquiv S hϖ R).toEquiv.subsingleton_congr,
    IsLocalization.subsingleton_iff
      (M := _root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ))]
  simp [_root_.Algebra.algebraMapSubmonoid_powers, Submonoid.mem_powers_iff, map_pow]

end Algebra

/-! ### Complexes with almost zero homology become exact after inverting `ϖ` -/

section Complexes

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- A short complex of `V`-modules with almost zero homology becomes exact after localizing away
from `ϖ ∈ m` (Scholze–Weinstein, *Berkeley lectures*, Lecture 8, proof of Proposition 8.2.8). -/
theorem exact_localizedModuleFunctor_of_isAlmostZero_homology {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {C : ShortComplex (ModuleCat.{u} V)} (hC : S.IsAlmostZero C.homology) :
    (C.map (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))).Exact := by
  have hex : ((C.map (Module.toAlmost S)).map (invert S hϖ)).Exact :=
    ((Module.exact_map_toAlmost_iff S C).mpr hC).map (invert S hϖ)
  exact ShortComplex.exact_of_iso (C.mapNatIso (toAlmostCompInvertIso S hϖ)) hex

/-- A short complex of `V`-modules with almost zero homology becomes exact after extending scalars
to `Localization.Away ϖ` for any `ϖ ∈ m`. -/
theorem exact_extendScalars_away_of_isAlmostZero_homology {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {C : ShortComplex (ModuleCat.{u} V)} (hC : S.IsAlmostZero C.homology) :
    (C.map (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ)))).Exact :=
  ShortComplex.exact_of_iso
    (C.mapNatIso (ModuleCat.localizedModuleFunctorIsoExtendScalars (Submonoid.powers ϖ)))
    (exact_localizedModuleFunctor_of_isAlmostZero_homology S hϖ hC)

/-- A homological complex of `V`-modules whose `i`-th homology is almost zero becomes exact at `i`
after localizing away from `ϖ ∈ m`. -/
theorem exactAt_localizedModuleFunctor_of_isAlmostZero_homology {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c} {i : I}
    (hK : S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).mapHomologicalComplex c).obj
      K).ExactAt i := by
  rw [Functor.mapHomologicalComplex_obj_exactAt_iff]
  exact exact_localizedModuleFunctor_of_isAlmostZero_homology S hϖ hK

/-- A homological complex of `V`-modules whose `i`-th homology is almost zero becomes exact at `i`
after extending scalars to `Localization.Away ϖ` for any `ϖ ∈ m`. -/
theorem exactAt_extendScalars_away_of_isAlmostZero_homology {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c} {i : I}
    (hK : S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.extendScalars
      (algebraMap V (Localization.Away ϖ))).mapHomologicalComplex c).obj K).ExactAt i := by
  rw [Functor.mapHomologicalComplex_obj_exactAt_iff]
  exact exact_extendScalars_away_of_isAlmostZero_homology S hϖ hK

/-- A homological complex of `V`-modules whose homology is almost zero in every degree becomes
acyclic after localizing away from `ϖ ∈ m`. -/
theorem acyclic_localizedModuleFunctor_of_isAlmostZero_homology {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c}
    (hK : ∀ i : I, S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).mapHomologicalComplex c).obj
      K).Acyclic :=
  fun i ↦ exactAt_localizedModuleFunctor_of_isAlmostZero_homology S hϖ (hK i)

/-- A homological complex of `V`-modules whose homology is almost zero in every degree becomes
acyclic after extending scalars to `Localization.Away ϖ` for any `ϖ ∈ m`. -/
theorem acyclic_extendScalars_away_of_isAlmostZero_homology {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c}
    (hK : ∀ i : I, S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.extendScalars
      (algebraMap V (Localization.Away ϖ))).mapHomologicalComplex c).obj K).Acyclic :=
  fun i ↦ exactAt_extendScalars_away_of_isAlmostZero_homology S hϖ (hK i)

end Complexes

end TauCeti.Almost
