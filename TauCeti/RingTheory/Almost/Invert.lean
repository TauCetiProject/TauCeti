/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Algebra.Category.CommAlgCat.Localization
public import TauCeti.Algebra.Category.ModuleCat.Localization
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.CategoryTheory.Localization.Monoidal.Functor
public import TauCeti.RingTheory.Almost.Algebra
public import TauCeti.RingTheory.Localization.Module

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
(`TauCeti.Almost.Algebra.toAlmostCompInvertIso`).

Finally, a short complex or homological complex of `V`-modules is exact in `Almost.Module S` if and
only if its homology is almost zero, and any such complex becomes honestly exact over
`Localization.Away ϖ` after inverting `ϖ ∈ m`.

## Main definitions

* `TauCeti.Almost.invert`: the exact braided monoidal functor
  `Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)` for `hϖ : ϖ ∈ S.ideal`.
* `TauCeti.Almost.toAlmostCompInvertIso` and `TauCeti.Almost.toAlmostCompInvertExtendScalarsIso`:
  natural isomorphisms identifying `Module.toAlmost S ⋙ invert S hϖ` with module localization and
  with extension of scalars to `Localization.Away ϖ`.
* `TauCeti.Almost.invertElementsIso` and `TauCeti.Almost.invertShriekIso`: the identifications
  `(invert S hϖ).obj M ≅ M_*[1/ϖ]` and `(invert S hϖ).obj M ≅ M_![1/ϖ]`.
* `TauCeti.Almost.Algebra.invert`: the functor `Almost.Algebra S ⥤ CommAlgCat (Localization.Away ϖ)`
  sending `A` to `A_*[1/ϖ]`, with comparison `TauCeti.Almost.Algebra.toAlmostCompInvertIso`.

## Main results

* `TauCeti.Almost.BasicSetup.IsAlmostZero.subsingleton_of_isLocalizedModule` and
  `TauCeti.Almost.BasicSetup.IsAlmostIso.bijective_isLocalizedModule_map`: localizing at a
  submonoid meeting `m` kills almost zero modules and turns almost isomorphisms into bijections.
* `TauCeti.Almost.invertMonoidal` and `TauCeti.Almost.invertBraided`: `invert S hϖ` is braided
  strong monoidal.
* `TauCeti.Almost.not_faithful_invert_of_not_isAlmostZero_quotient`: `invert S hϖ` is not faithful
  whenever `V ⧸ (ϖ)` is not almost zero (in particular for valuation setups at any `ϖ ∈ m`).
* `TauCeti.Almost.exactAt_localizedModuleFunctor_of_isAlmostZero_homology` and
  `TauCeti.Almost.exactAt_extendScalars_away_of_isAlmostZero_homology`: complexes with almost zero
  homology become exact after inverting `ϖ ∈ m`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2 and §5.2,
  proof of Corollary 5.2.15.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Exercise 4.1.9.
* P. Scholze, J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Lecture 8, proof of
  Proposition 8.2.8.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

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

noncomputable instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Localization.Lifting (Module.toAlmost S) S.almostZero.isoModSerre
      (ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))) (invert S hϖ) :=
  ⟨toAlmostCompInvertExtendScalarsIso S hϖ⟩

instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) : PreservesFiniteLimits (invert S hϖ) := by
  dsimp only [invert]
  infer_instance

instance {ϖ : V} (hϖ : ϖ ∈ S.ideal) : PreservesFiniteColimits (invert S hϖ) := by
  dsimp only [invert]
  infer_instance

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

/-! ### Degenerate cases, basic computations, and non-faithfulness -/

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

noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra V ((invert S ϖ).obj A) :=
  inferInstanceAs
    (_root_.Algebra V
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra ((Algebra.elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (_root_.Algebra ((Algebra.elements S).obj A)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V ((Algebra.elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (IsScalarTower V ((Algebra.elements S).obj A)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V (Localization.Away ϖ) ((invert S ϖ).obj A) :=
  inferInstanceAs
    (IsScalarTower V (Localization.Away ϖ)
      ((CommAlgCat.localizationFunctor (Submonoid.powers ϖ)).obj ((Algebra.elements S).obj A)))

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

end Algebra

/-! ### Complexes with almost zero homology become exact after inverting `ϖ` -/

section Complexes

private theorem mapHomologicalComplex_obj_exactAt_iff {C D ι : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).ExactAt i ↔ ((K.sc i).map F).Exact :=
  Iff.rfl

variable {V : Type u} [CommRing V] (S : BasicSetup V)

namespace Module

/-- A short complex of `V`-modules becomes exact in `Almost.Module S` if and only if its homology is
almost zero. -/
@[simp]
theorem exact_map_toAlmost_iff (C : ShortComplex (ModuleCat.{u} V)) :
    (C.map (toAlmost S)).Exact ↔ S.IsAlmostZero C.homology := by
  rw [ShortComplex.exact_iff_isZero_homology,
    (C.mapHomologyIso (toAlmost S)).isZero_iff, isZero_toAlmost_obj_iff]

/-- A homological complex `K` of `V`-modules becomes exact at `i` in `Almost.Module S` if and only
if `K.homology i` is almost zero. -/
@[simp]
theorem exactAt_mapHomologicalComplex_toAlmost_iff {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} V) c) (i : ι) :
    (((toAlmost S).mapHomologicalComplex c).obj K).ExactAt i ↔
      S.IsAlmostZero (K.homology i) := by
  rw [mapHomologicalComplex_obj_exactAt_iff, exact_map_toAlmost_iff]
  rfl

end Module

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
theorem exactAt_localizedModuleFunctor_of_isAlmostZero_homology {ι : Type*} {c : ComplexShape ι}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c} {i : ι}
    (hK : S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).mapHomologicalComplex c).obj
      K).ExactAt i := by
  rw [mapHomologicalComplex_obj_exactAt_iff]
  exact exact_localizedModuleFunctor_of_isAlmostZero_homology S hϖ hK

/-- A homological complex of `V`-modules whose `i`-th homology is almost zero becomes exact at `i`
after extending scalars to `Localization.Away ϖ` for any `ϖ ∈ m`. -/
theorem exactAt_extendScalars_away_of_isAlmostZero_homology {ι : Type*} {c : ComplexShape ι}
    {ϖ : V} (hϖ : ϖ ∈ S.ideal) {K : HomologicalComplex (ModuleCat.{u} V) c} {i : ι}
    (hK : S.IsAlmostZero (K.homology i)) :
    (((ModuleCat.extendScalars
      (algebraMap V (Localization.Away ϖ))).mapHomologicalComplex c).obj K).ExactAt i := by
  rw [mapHomologicalComplex_obj_exactAt_iff]
  exact exact_extendScalars_away_of_isAlmostZero_homology S hϖ hK

end Complexes

end TauCeti.Almost
