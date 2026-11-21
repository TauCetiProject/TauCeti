/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Algebra
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
`TauCeti.Almost.invertShriekIso`). Base-changing `S` to a localization `W` away from `ϖ ∈ m` makes
the setup classical (`TauCeti.Almost.BasicSetup.baseChange_away_eq_classical`), so almost modules
and almost algebras over `W` identify with honest `W`-modules and `W`-algebras
(`TauCeti.Almost.Module.baseChangeAwayEquiv`, `TauCeti.Almost.Algebra.baseChangeAwayEquiv`). Since
extension of scalars to `Localization.Away ϖ` is braided monoidal, `invert S hϖ` inherits a braided
strong monoidal structure (`TauCeti.Almost.invertMonoidal`, `TauCeti.Almost.invertBraided`).

On almost algebras, `TauCeti.Almost.Algebra.invert S ϖ` sends `A` to the localized algebra
`A_*[1/ϖ]` in `CommAlgCat (Localization.Away ϖ)` and acts via `(Algebra.elements S).map` on
canonical numerators. When `ϖ ∈ m`, the unit `R → (R^a)_*` is an almost isomorphism, so
precomposing with almostification recovers ordinary algebra localization
(`TauCeti.Almost.Algebra.toAlmostCompInvertIso`, `TauCeti.Almost.Algebra.invertToAlmostObjEquiv`),
and `Algebra.invert S ϖ` is naturally isomorphic to the functor induced on commutative monoid
objects by `Almost.invert S hϖ` (`TauCeti.Almost.Algebra.invertIsoMapCommMon`).

Finally, combining `TauCeti.Almost.Module.exact_map_toAlmost_iff` with exactness of `invert S hϖ`,
any short complex or homological complex of `V`-modules whose homology is almost zero becomes
honestly exact (and acyclic) over `Localization.Away ϖ` after inverting `ϖ ∈ m`.

## Main definitions

* `TauCeti.Almost.invert`: the exact braided monoidal functor
  `Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)` for `hϖ : ϖ ∈ S.ideal`.
* `TauCeti.Almost.toAlmostCompInvertIso` and `TauCeti.Almost.toAlmostCompInvertExtendScalarsIso`:
  natural isomorphisms identifying `Module.toAlmost S ⋙ invert S hϖ` with module localization and
  with extension of scalars to `Localization.Away ϖ`.
* `TauCeti.Almost.invertElementsIso` and `TauCeti.Almost.invertShriekIso`: the identifications
  `(invert S hϖ).obj M ≅ M_*[1/ϖ]` and `(invert S hϖ).obj M ≅ M_![1/ϖ]`.
* `TauCeti.Almost.Module.baseChangeAwayEquiv` and `TauCeti.Almost.Algebra.baseChangeAwayEquiv`:
  equivalences identifying almost modules and almost algebras over `S.baseChange W` with honest
  `W`-modules and `W`-algebras when `W` is a localization away from `ϖ ∈ S.ideal`.
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
* `TauCeti.Almost.exactAt_localizedModuleFunctor_of_isAlmostZero_homology`,
  `TauCeti.Almost.exactAt_extendScalars_away_of_isAlmostZero_homology`,
  `TauCeti.Almost.acyclic_localizedModuleFunctor_of_isAlmostZero_homology`, and
  `TauCeti.Almost.acyclic_extendScalars_away_of_isAlmostZero_homology`: complexes with almost zero
  homology become exact and acyclic after inverting `ϖ ∈ m`.

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

/-- Base-changing an almost zero `V`-module to a localization `W` of `V` away from `ϖ ∈ m` gives a
zero module. -/
theorem IsAlmostZero.subsingleton_tensorProduct {M : Type*} [AddCommGroup M] [_root_.Module V M]
    (hM : S.IsAlmostZero M) {ϖ : V} (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W]
    [_root_.Algebra V W] [IsLocalization.Away ϖ W] : Subsingleton (W ⊗[V] M) :=
  hM.subsingleton_of_isLocalizedModule_away hϖ (f := TensorProduct.mk V W M 1)

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

/-- Base-changing along a localization `W` of `V` away from `ϖ ∈ m` turns an almost isomorphism
into a bijection. -/
theorem IsAlmostIso.bijective_lTensor {M N : Type*} [AddCommGroup M] [_root_.Module V M]
    [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N} (hf : S.IsAlmostIso f)
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W] [_root_.Algebra V W]
    [IsLocalization.Away ϖ W] :
    Function.Bijective (f.lTensor W) := by
  have hmap : f.lTensor W = IsLocalizedModule.map (Submonoid.powers ϖ)
      (TensorProduct.mk V W M 1) (TensorProduct.mk V W N 1) f := by
    refine IsLocalizedModule.ext (Submonoid.powers ϖ) (TensorProduct.mk V W M 1)
      (IsLocalizedModule.map_units (TensorProduct.mk V W N 1)) ?_
    ext x
    exact (IsLocalizedModule.map_apply (Submonoid.powers ϖ) (TensorProduct.mk V W M 1)
      (TensorProduct.mk V W N 1) f x).symm
  rw [hmap]
  exact hf.bijective_isLocalizedModule_map_away (TensorProduct.mk V W M 1)
    (TensorProduct.mk V W N 1) hϖ

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

/-- Naturality of `ModuleCat.localizedModuleIso`: `(localizedModuleFunctor T).map f` corresponds to
`LocalizedModule.map T f.hom`. -/
private theorem localizedModuleIso_naturality {T : Submonoid V} {M₁ M₂ : ModuleCat.{u} V}
    (f : M₁ ⟶ M₂) :
    (ModuleCat.localizedModuleFunctor.{u} T).map f ≫ (M₂.localizedModuleIso T).hom =
      (M₁.localizedModuleIso T).hom ≫ ModuleCat.ofHom (LocalizedModule.map T f.hom) := by
  rw [ModuleCat.localizedModuleFunctor_map]
  change ModuleCat.localizedModuleMap T f ≫ (M₂.localizedModuleIso T).hom =
    (M₁.localizedModuleIso T).hom ≫ ModuleCat.ofHom (LocalizedModule.map T f.hom)
  apply ModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective V
  apply IsLocalizedModule.linearMap_ext T (M₁.localizedModuleMkLinearMap T)
    (LocalizedModule.mkLinearMap T M₂)
  ext x
  change (M₂.localizedModuleIso T).hom
      ((IsLocalizedModule.mapExtendScalars T (M₁.localizedModuleMkLinearMap T)
        (M₂.localizedModuleMkLinearMap T) (Localization T) f.hom)
        (M₁.localizedModuleMkLinearMap T x)) =
    LocalizedModule.map T f.hom
      ((M₁.localizedModuleIso T).hom (M₁.localizedModuleMkLinearMap T x))
  calc (M₂.localizedModuleIso T).hom
        ((IsLocalizedModule.mapExtendScalars T (M₁.localizedModuleMkLinearMap T)
          (M₂.localizedModuleMkLinearMap T) (Localization T) f.hom)
          (M₁.localizedModuleMkLinearMap T x))
      = (M₂.localizedModuleIso T).hom (M₂.localizedModuleMkLinearMap T (f.hom x)) :=
        congrArg (M₂.localizedModuleIso T).hom
          (IsLocalizedModule.map_apply T (M₁.localizedModuleMkLinearMap T)
            (M₂.localizedModuleMkLinearMap T) f.hom x)
    _ = LocalizedModule.mk (f.hom x) 1 :=
        M₂.localizedModuleIso_hom_mkLinearMap T (f.hom x)
    _ = LocalizedModule.map T f.hom (LocalizedModule.mk x 1) :=
        (LocalizedModule.map_mk T f.hom x 1).symm
    _ = LocalizedModule.map T f.hom
          ((M₁.localizedModuleIso T).hom (M₁.localizedModuleMkLinearMap T x)) :=
        congrArg (LocalizedModule.map T f.hom)
          (M₁.localizedModuleIso_hom_mkLinearMap T x).symm

/-- Naturality of `invertToAlmostObjIso`: `(invert S hϖ).map (f^a)` acts as
`LocalizedModule.map` on `LocalizedModule.Away ϖ`. -/
@[reassoc]
theorem invert_map_toAlmost_comp_invertToAlmostObjIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : ModuleCat.{u} V} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map ((Module.toAlmost S).map f) ≫ (invertToAlmostObjIso S hϖ M₂).hom =
      (invertToAlmostObjIso S hϖ M₁).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) f.hom) := by
  calc (invert S hϖ).map ((Module.toAlmost S).map f) ≫ (invertToAlmostObjIso S hϖ M₂).hom
      = ((Module.toAlmost S ⋙ invert S hϖ).map f ≫ (toAlmostCompInvertIso S hϖ).hom.app M₂) ≫
          (M₂.localizedModuleIso (Submonoid.powers ϖ)).hom :=
        (Category.assoc _ _ _).symm
    _ = ((toAlmostCompInvertIso S hϖ).hom.app M₁ ≫
          (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map f) ≫
          (M₂.localizedModuleIso (Submonoid.powers ϖ)).hom :=
        congrArg (· ≫ _) ((toAlmostCompInvertIso S hϖ).hom.naturality f)
    _ = (toAlmostCompInvertIso S hϖ).hom.app M₁ ≫
          ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map f ≫
            (M₂.localizedModuleIso (Submonoid.powers ϖ)).hom) :=
        Category.assoc _ _ _
    _ = (toAlmostCompInvertIso S hϖ).hom.app M₁ ≫
          ((M₁.localizedModuleIso (Submonoid.powers ϖ)).hom ≫
            ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) f.hom)) :=
        congrArg (_ ≫ ·) (localizedModuleIso_naturality f)
    _ = (invertToAlmostObjIso S hϖ M₁).hom ≫
          ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) f.hom) :=
        (Category.assoc _ _ _).symm

/-- Naturality of `invertElementsIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.elements S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertElementsIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertElementsIso S hϖ M₂).hom =
      (invertElementsIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.elements S).map f).hom) := by
  calc (invert S hϖ).map f ≫ (invertElementsIso S hϖ M₂).hom
      = ((invert S hϖ).map f ≫ (invertIsoElementsLocalized S hϖ).hom.app M₂) ≫
          (((Module.elements S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom :=
        (Category.assoc _ _ _).symm
    _ = ((invertIsoElementsLocalized S hϖ).hom.app M₁ ≫
          (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map
            ((Module.elements S).map f)) ≫
          (((Module.elements S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom :=
        congrArg (· ≫ _) ((invertIsoElementsLocalized S hϖ).hom.naturality f)
    _ = (invertIsoElementsLocalized S hϖ).hom.app M₁ ≫
          ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map
              ((Module.elements S).map f) ≫
            (((Module.elements S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom) :=
        Category.assoc _ _ _
    _ = (invertIsoElementsLocalized S hϖ).hom.app M₁ ≫
          ((((Module.elements S).obj M₁).localizedModuleIso (Submonoid.powers ϖ)).hom ≫
            ModuleCat.ofHom
              (LocalizedModule.map (Submonoid.powers ϖ) ((Module.elements S).map f).hom)) :=
        congrArg (_ ≫ ·) (localizedModuleIso_naturality ((Module.elements S).map f))
    _ = (invertElementsIso S hϖ M₁).hom ≫
          ModuleCat.ofHom
            (LocalizedModule.map (Submonoid.powers ϖ) ((Module.elements S).map f).hom) :=
        (Category.assoc _ _ _).symm

/-- Naturality of `invertShriekIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.shriek S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertShriekIso_hom {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertShriekIso S hϖ M₂).hom =
      (invertShriekIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.shriek S).map f).hom) := by
  calc (invert S hϖ).map f ≫ (invertShriekIso S hϖ M₂).hom
      = ((invert S hϖ).map f ≫ (invertIsoShriekLocalized S hϖ).hom.app M₂) ≫
          (((Module.shriek S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom :=
        (Category.assoc _ _ _).symm
    _ = ((invertIsoShriekLocalized S hϖ).hom.app M₁ ≫
          (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map
            ((Module.shriek S).map f)) ≫
          (((Module.shriek S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom :=
        congrArg (· ≫ _) ((invertIsoShriekLocalized S hϖ).hom.naturality f)
    _ = (invertIsoShriekLocalized S hϖ).hom.app M₁ ≫
          ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).map
              ((Module.shriek S).map f) ≫
            (((Module.shriek S).obj M₂).localizedModuleIso (Submonoid.powers ϖ)).hom) :=
        Category.assoc _ _ _
    _ = (invertIsoShriekLocalized S hϖ).hom.app M₁ ≫
          ((((Module.shriek S).obj M₁).localizedModuleIso (Submonoid.powers ϖ)).hom ≫
            ModuleCat.ofHom
              (LocalizedModule.map (Submonoid.powers ϖ) ((Module.shriek S).map f).hom)) :=
        congrArg (_ ≫ ·) (localizedModuleIso_naturality ((Module.shriek S).map f))
    _ = (invertShriekIso S hϖ M₁).hom ≫
          ModuleCat.ofHom
            (LocalizedModule.map (Submonoid.powers ϖ) ((Module.shriek S).map f).hom) :=
        (Category.assoc _ _ _).symm

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
    IsZero ((invert S S.ideal.zero_mem).obj M) := by
  have : Subsingleton (LocalizedModule.Away (0 : V) ((Module.elements S).obj M)) :=
    LocalizedModule.subsingleton_iff.mpr fun m ↦ ⟨0, ⟨1, pow_one 0⟩, zero_smul V m⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (invertElementsIso S S.ideal.zero_mem M)

/-- Inverting `ϖ ∈ m` kills the almostification of any `V`-module in which every element is
annihilated by a power of `ϖ`. -/
theorem isZero_invert_toAlmost_of_pow_smul_eq_zero {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (M : ModuleCat.{u} V) (hM : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj M)) := by
  have : Subsingleton (LocalizedModule.Away ϖ M) :=
    LocalizedModule.subsingleton_iff.mpr fun m ↦
      let ⟨n, hn⟩ := hM m
      ⟨ϖ ^ n, ⟨n, rfl⟩, hn⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (invertToAlmostObjIso S hϖ M)

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
  have hS : S = BasicSetup.classical V := by
    ext1
    rw [BasicSetup.classical_ideal]
    exact S.ideal.eq_top_of_isUnit_mem hϖ hu
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

/-- After base-changing `S` to a localization `W` away from `ϖ ∈ m`, the setup becomes classical,
so almostification `ModuleCat W ⥤ Module (S.baseChange W)` is an equivalence of categories. -/
theorem Module.isEquivalence_toAlmost_baseChange_away (W : Type u) [CommRing W]
    [_root_.Algebra V W] {ϖ : V} [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    (Module.toAlmost (S.baseChange W)).IsEquivalence := by
  rw [S.baseChange_away_eq_classical W hϖ]
  infer_instance

/-- Base-changing `S` to a localization `W` away from `ϖ ∈ m` identifies almost `W`-modules with
honest `W`-modules via `Module.toAlmost (S.baseChange W)`. -/
noncomputable def Module.baseChangeAwayEquiv (W : Type u) [CommRing W] [_root_.Algebra V W]
    {ϖ : V} [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    ModuleCat.{u} W ≌ Module (S.baseChange W) :=
  have := Module.isEquivalence_toAlmost_baseChange_away S W hϖ
  (Module.toAlmost (S.baseChange W)).asEquivalence

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

/-- Inverting `0 : V` sends every almost algebra to the zero algebra. -/
instance subsingleton_invert_obj_zero (A : Algebra S) :
    Subsingleton ((invert S (0 : V)).obj A) :=
  CommAlgCat.subsingleton_localizationFunctor_obj_of_smul_one_eq_zero
    (A := (Algebra.elements S).obj A) (⟨1, pow_one 0⟩ : (0 : V) ∈ Submonoid.powers 0)
    (zero_smul V (1 : (Algebra.elements S).obj A))

/-- An almost algebra whose unit element (equivalently every almost element) is annihilated by a
power of `ϖ` becomes the zero algebra after inverting `ϖ`. -/
theorem subsingleton_invert_obj_of_pow_smul_one_eq_zero {ϖ : V}
    {A : Algebra S} {n : ℕ} (h : ϖ ^ n • (1 : (Algebra.elements S).obj A) = 0) :
    Subsingleton ((invert S ϖ).obj A) :=
  CommAlgCat.subsingleton_localizationFunctor_obj_of_smul_one_eq_zero
    (A := (Algebra.elements S).obj A) ⟨n, rfl⟩ h

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
  change IsLocalization (Submonoid.powers (algebraMap V ((elements S).obj A) ϖ))
    ((invert S ϖ).obj A)
  rw [← _root_.Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- `(Algebra.invert S ϖ).obj A` is the zero ring iff a power of `ϖ` maps to `0` in `A_*`. -/
theorem subsingleton_invert_obj_iff (ϖ : V) (A : Algebra S) :
    Subsingleton ((invert S ϖ).obj A) ↔
      ∃ n : ℕ, algebraMap V ((elements S).obj A) (ϖ ^ n) = 0 := by
  rw [IsLocalization.subsingleton_iff (M := Submonoid.powers (algebraMap V ((elements S).obj A) ϖ))
    (S := (invert S ϖ).obj A)]
  simp [Submonoid.mem_powers_iff, map_pow]

/-- After base-changing `S` to a localization `W` away from `ϖ ∈ m`, the setup becomes classical,
so almostification `CommAlgCat W ⥤ Algebra (S.baseChange W)` is an equivalence of categories. -/
theorem isEquivalence_toAlmost_baseChange_away (W : Type u) [CommRing W] [_root_.Algebra V W]
    {ϖ : V} [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    (toAlmost (S.baseChange W)).IsEquivalence := by
  rw [S.baseChange_away_eq_classical W hϖ]
  infer_instance

/-- Base-changing `S` to a localization `W` away from `ϖ ∈ m` identifies almost `W`-algebras with
honest commutative `W`-algebras via `Algebra.toAlmost (S.baseChange W)`. -/
noncomputable def baseChangeAwayEquiv (W : Type u) [CommRing W] [_root_.Algebra V W] {ϖ : V}
    [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    CommAlgCat.{u} W ≌ Algebra (S.baseChange W) :=
  have := isEquivalence_toAlmost_baseChange_away S W hϖ
  (toAlmost (S.baseChange W)).asEquivalence

/-- Component comparison morphism `(Localization.Away ϖ ⊗[V] A_*) → (Almost.invert S hϖ).obj A` of
commutative monoid objects. -/
private noncomputable def extendScalarsElementsToInvertCommMon {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (A : Algebra S) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))).mapCommMon.obj
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A)) ⟶
      (Almost.invert S hϖ).mapCommMon.obj A :=
  (Functor.mapCommMonCompIso.symm ≪≫
      Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).inv.app
    (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A)) ≫
    (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app A).hom

/-- Canonical `Localization M`-algebra equivalence between
`(CommAlgCat.localizationFunctor M).obj A` and `Localization (_root_.Algebra.algebraMapSubmonoid
A M)`, acting as the identity on canonical numerators from `A`. -/
private noncomputable def localizationFunctorObjAlgEquiv (M : Submonoid V)
    (A : CommAlgCat.{u} V) :
    ((CommAlgCat.localizationFunctor M).obj A) ≃ₐ[Localization M]
      Localization (_root_.Algebra.algebraMapSubmonoid A M) :=
  let e : ((CommAlgCat.localizationFunctor M).obj A) ≃ₐ[A]
      Localization (_root_.Algebra.algebraMapSubmonoid A M) :=
    IsLocalization.algEquiv (_root_.Algebra.algebraMapSubmonoid A M)
      ((CommAlgCat.localizationFunctor M).obj A)
      (Localization (_root_.Algebra.algebraMapSubmonoid A M))
  { e.toRingEquiv with
    commutes' := fun z ↦ by
      have h : e.toRingHom.comp
          (algebraMap (Localization M) ((CommAlgCat.localizationFunctor M).obj A)) =
          algebraMap (Localization M)
            (Localization (_root_.Algebra.algebraMapSubmonoid A M)) := by
        apply IsLocalization.ringHom_ext M
        ext v
        change e (algebraMap (Localization M) ((CommAlgCat.localizationFunctor M).obj A)
            (algebraMap V (Localization M) v)) =
          algebraMap (Localization M) (Localization (_root_.Algebra.algebraMapSubmonoid A M))
            (algebraMap V (Localization M) v)
        rw [← IsScalarTower.algebraMap_apply V (Localization M)
            ((CommAlgCat.localizationFunctor M).obj A) v,
          ← IsScalarTower.algebraMap_apply V (Localization M)
            (Localization (_root_.Algebra.algebraMapSubmonoid A M)) v,
          IsScalarTower.algebraMap_apply V A ((CommAlgCat.localizationFunctor M).obj A) v,
          IsScalarTower.algebraMap_apply V A
            (Localization (_root_.Algebra.algebraMapSubmonoid A M)) v,
          e.commutes]
      exact congr($h z) }

private noncomputable def localizationFunctorObjIso (M : Submonoid V) (A : CommAlgCat.{u} V) :
    (CommAlgCat.localizationFunctor M).obj A ≅ CommAlgCat.localizationObj M A :=
  CommAlgCat.isoMk (localizationFunctorObjAlgEquiv M A)

private theorem localizationFunctorObjAlgEquiv_algebraMap (M : Submonoid V) (A : CommAlgCat.{u} V)
    (a : A) :
    localizationFunctorObjAlgEquiv M A
        (algebraMap A ((CommAlgCat.localizationFunctor M).obj A) a) =
      algebraMap A (Localization (_root_.Algebra.algebraMapSubmonoid A M)) a :=
  (IsLocalization.algEquiv (_root_.Algebra.algebraMapSubmonoid A M)
    ((CommAlgCat.localizationFunctor M).obj A)
    (Localization (_root_.Algebra.algebraMapSubmonoid A M))).commutes a

private theorem localizationFunctorObjAlgEquiv_symm_algebraMap (M : Submonoid V)
    (A : CommAlgCat.{u} V) (a : A) :
    (localizationFunctorObjAlgEquiv M A).symm
        (algebraMap A (Localization (_root_.Algebra.algebraMapSubmonoid A M)) a) =
      algebraMap A ((CommAlgCat.localizationFunctor M).obj A) a :=
  (IsLocalization.algEquiv (_root_.Algebra.algebraMapSubmonoid A M)
    ((CommAlgCat.localizationFunctor M).obj A)
    (Localization (_root_.Algebra.algebraMapSubmonoid A M))).symm.commutes a

private theorem localizationFunctorObjIso_hom_algebraMap (M : Submonoid V) (A : CommAlgCat.{u} V)
    (a : A) :
    (localizationFunctorObjIso M A).hom.hom
        (algebraMap A ((CommAlgCat.localizationFunctor M).obj A) a) =
      algebraMap A (Localization (_root_.Algebra.algebraMapSubmonoid A M)) a :=
  localizationFunctorObjAlgEquiv_algebraMap M A a

/-- Component isomorphism identifying `(Algebra.invert S ϖ).obj A` with the commutative algebra
corresponding to `(Almost.invert S hϖ).mapCommMon.obj A`. -/
private noncomputable def invertObjIsoMapCommMonObj {ϖ : V} (hϖ : ϖ ∈ S.ideal) (A : Algebra S) :
    (invert S ϖ).obj A ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((Almost.invert S hϖ).mapCommMon.obj A) :=
  localizationFunctorObjIso (Submonoid.powers ϖ) ((elements S).obj A) ≪≫
    CommAlgCat.isoMk
      (Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)).symm ≪≫
    ModuleCat.extendScalarsCommAlgIso (Localization.Away ϖ) ((elements S).obj A) ≪≫
    ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.mapIso
      (((Functor.mapCommMonCompIso.symm ≪≫
          Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).app
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A))).symm ≪≫
        (Almost.invert S hϖ).mapCommMon.mapIso ((counitIso S).app A))

private theorem invertObjIsoMapCommMonObj_hom_algebraMap {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (A : Algebra S) (x : (elements S).obj A) :
    (invertObjIsoMapCommMonObj S hϖ A).hom
        (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
      (extendScalarsElementsToInvertCommMon S hϖ A).hom.hom
        ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x) := by
  have h1 : (localizationFunctorObjIso (Submonoid.powers ϖ) ((elements S).obj A)).hom.hom
      (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
      algebraMap ((elements S).obj A)
        (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A)
          (Submonoid.powers ϖ))) x :=
    localizationFunctorObjIso_hom_algebraMap (Submonoid.powers ϖ) ((elements S).obj A) x
  have h2 : algebraMap ((elements S).obj A)
        (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A)
          (Submonoid.powers ϖ))) x =
      Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)
        ((1 : Localization.Away ϖ) ⊗ₜ[V] x) :=
    (Localization.tensorRightAlgEquiv_apply_one_tmul (Submonoid.powers ϖ) x).symm
  change (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
      (extendScalarsElementsToInvertCommMon S hϖ A))
    ((ModuleCat.extendScalarsCommAlgIso (Localization.Away ϖ) ((elements S).obj A)).hom
      ((Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)).symm
        ((localizationFunctorObjIso (Submonoid.powers ϖ) ((elements S).obj A)).hom.hom
          (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x)))) = _
  rw [h1, h2, AlgEquiv.symm_apply_apply, ModuleCat.extendScalarsCommAlgIso_hom_tmul]
  exact ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_map_apply _ _

/-- For `ϖ ∈ m`, `Algebra.invert S ϖ` is naturally isomorphic to the functor induced on
commutative monoid objects by the braided monoidal functor `Almost.invert S hϖ`. -/
noncomputable def invertIsoMapCommMon {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    invert S ϖ ≅
      (Almost.invert S hϖ).mapCommMon ⋙
        ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor := by
  refine NatIso.ofComponents (invertObjIsoMapCommMonObj S hϖ) fun {A B} f ↦ ?_
  apply CommAlgCat.hom_ext
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A)
    (Submonoid.powers ϖ)) ?_
  ext x
  let G := ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))
  have hcounit :
      (Almost.invert S hϖ).mapCommMon.map ((toAlmost S).map ((elements S).map f)) ≫
        (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app B).hom =
      (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app A).hom ≫
        (Almost.invert S hϖ).mapCommMon.map f := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Almost.invert S hϖ).mapCommMon.map ((counitIso S).hom.naturality f)
  have hk :
      G.mapCommMon.map
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.map ((elements S).map f)) ≫
        extendScalarsElementsToInvertCommMon S hϖ B =
      extendScalarsElementsToInvertCommMon S hϖ A ≫ (Almost.invert S hϖ).mapCommMon.map f :=
    ((Functor.mapCommMonCompIso.symm ≪≫
        Functor.mapCommMonNatIso (toAlmostCompInvertExtendScalarsIso S hϖ)).inv.naturality_assoc
      _ _).trans ((congrArg (_ ≫ ·) hcounit).trans (Category.assoc _ _ _).symm)
  change (invertObjIsoMapCommMonObj S hϖ B).hom ((invert S ϖ).map f
      (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x)) =
    (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
      ((Almost.invert S hϖ).mapCommMon.map f))
      ((invertObjIsoMapCommMonObj S hϖ A).hom
        (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x))
  rw [invert_map_hom_algebraMap, invertObjIsoMapCommMonObj_hom_algebraMap,
    invertObjIsoMapCommMonObj_hom_algebraMap]
  exact congrArg
    (fun m ↦ m.hom.hom ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) hk

/-- For `ϖ ∈ m` and an honest commutative `V`-algebra `R`, `(Algebra.invert S ϖ).obj (R^a)` is
canonically isomorphic as a `Localization.Away ϖ`-algebra to `R[1/ϖ]`. -/
noncomputable def invertToAlmostObjEquiv {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) :
    ((invert S ϖ).obj ((toAlmost S).obj R)) ≃ₐ[Localization.Away ϖ]
      Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)) :=
  let e₁ : ((invert S ϖ).obj ((toAlmost S).obj R)) ≃ₐ[Localization.Away ϖ]
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj R) :=
    { ((toAlmostCompInvertIso S hϖ).hom.app R).hom with
      invFun := ((toAlmostCompInvertIso S hϖ).inv.app R).hom
      left_inv := fun x ↦
        ConcreteCategory.congr_hom ((toAlmostCompInvertIso S hϖ).hom_inv_id_app R) x
      right_inv := fun y ↦
        ConcreteCategory.congr_hom ((toAlmostCompInvertIso S hϖ).inv_hom_id_app R) y }
  e₁.trans (localizationFunctorObjAlgEquiv (Submonoid.powers ϖ) R)

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
  change ((toAlmostCompInvertIso S hϖ).inv.app R).hom
      ((localizationFunctorObjAlgEquiv (Submonoid.powers ϖ) R).symm
        (algebraMap R (Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)))
          r)) = _
  rw [localizationFunctorObjAlgEquiv_symm_algebraMap, toAlmostCompInvertIso_inv_app_hom_algebraMap]

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
  change localizationFunctorObjAlgEquiv (Submonoid.powers ϖ) R
      (((toAlmostCompInvertIso S hϖ).hom.app R).hom
        (algebraMap ((elements S).obj ((toAlmost S).obj R))
          ((invert S ϖ).obj ((toAlmost S).obj R)) (((adj S).unit.app R).hom r))) = _
  rw [toAlmostCompInvertIso_hom_app_hom_algebraMap_unit,
    localizationFunctorObjAlgEquiv_algebraMap]

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

/-- `invert S hϖ` preserves exactness of complexes of almost modules at each degree. -/
theorem exactAt_mapHomologicalComplex_invert {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) (C : HomologicalComplex (Module S) c) {i : I}
    (hC : C.ExactAt i) :
    (((invert S hϖ).mapHomologicalComplex c).obj C).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff] at hC ⊢
  exact hC.map (invert S hϖ)

/-- `invert S hϖ` sends acyclic complexes of almost modules to acyclic complexes of
`V[1/ϖ]`-modules. -/
theorem acyclic_mapHomologicalComplex_invert {I : Type*} {c : ComplexShape I}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) (C : HomologicalComplex (Module S) c) (hC : C.Acyclic) :
    (((invert S hϖ).mapHomologicalComplex c).obj C).Acyclic :=
  fun i ↦ exactAt_mapHomologicalComplex_invert S hϖ C (hC i)

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
