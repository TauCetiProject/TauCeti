/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.GorensteinProjective
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Matrix factorizations from projective resolutions of length one

Let `w` be an element of a commutative ring `S` and put `R = S/(w)`. Eisenbud's construction
turns a projective resolution of length one over `S`

`0 → P --f--> Q --g--> M → 0`

of an `R`-module `M` into a matrix factorization of `w`. Since `w` kills `M`, multiplication by
`w` on `Q` lands in the image of the injective map `f`, so it factors uniquely as `f ∘ d₁`; then
`(P --f--> Q --d₁--> P)` is a matrix factorization of `w`
(`TauCeti.MatrixFactorization.ofInjective`, in
`TauCeti.CommutativeAlgebra.MatrixFactorization.Basic`), and the cokernel of its reduction
modulo `w` is `M` (`TauCeti.MatrixFactorization.quotientCokernelIsoOfExact`).

Conversely, the cokernel of the reduction modulo `w` of any finite-projective matrix factorization
`X` is the quotient of the odd component `X₁` by the image of `d₀`
(`TauCeti.MatrixFactorization.exact_d₀_quotientCokernelπ`, in
`TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.BaseChange`), and `d₀` is injective
when `w` is a non-zero-divisor. So for a non-zero-divisor `w`, the `R`-modules arising as such
cokernels are exactly those with a resolution of length one by finitely generated projective
`S`-modules (`TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff`). Among the
`R`-modules finitely presented over `S`, these are exactly those of projective dimension at most
one over `S`
(`TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE`);
over a Noetherian ring `S`, this covers every finitely generated `R`-module. In particular every
such module is Gorenstein-projective over `R`
(`TauCeti.MatrixFactorization.isGorensteinProjective_of_exact`).

No regularity hypothesis is used. When `S` has finite global dimension, every
Gorenstein-projective `R`-module is a high syzygy and hence has projective dimension at most one
over `S`; that step, which gives essential surjectivity of the cokernel functor onto the stable
category of Gorenstein-projective `R`-modules, is not made here.

## Main definitions

* `TauCeti.MatrixFactorization.quotientCokernelIsoOfExact`: the cokernel of the reduction of the
  matrix factorization of a resolution `0 → P → Q → M → 0` is `M`.

## Main results

* `TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff`: for a non-zero-divisor `w`, an
  `S/(w)`-module is the cokernel of the reduction of a matrix factorization exactly when it has a
  resolution of length one by finitely generated projective `S`-modules.
* `TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel_essImage_iff`: the same
  description of the essential image of the cokernel functor to Gorenstein-projective modules.
* `TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE`: an
  `S/(w)`-module finitely presented over `S` is such a cokernel exactly when its projective
  dimension over `S` is at most one; over a Noetherian ring this applies to every finitely
  generated `S/(w)`-module
  (`exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing`).
* `TauCeti.MatrixFactorization.isGorensteinProjective_of_exact` and
  `TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE`: such modules
  are Gorenstein-projective over `S/(w)`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5: the matrix factorization
  attached to an `S`-free resolution of length one of a module over `S/(w)`.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {S : Type u} [CommRing S] {w : S}

/-! ### The cokernel of a resolution of length one -/

section Resolution

variable {P Q : FGModuleCat.{u} S} {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
  {f : P ⟶ Q} {g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M}
  [Module.Projective S P] [Module.Projective S Q]

/-- The map from the cokernel of the reduction of `ofInjective f` to `M` induced by `g`: the
adjoint `S/(w) ⊗ Q → M` of `g` kills the reduction of `f`. -/
private def quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))))).obj ⟶ M :=
  (isColimitCokernelπ _).desc (CokernelCofork.ofπ
    (((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
      _ _).symm g) (by
      have hfg₀ : f.hom ≫ g = 0 := by
        ext y
        exact hfg.apply_apply_eq_zero y
      -- The adjunction is natural, so the adjoint of `g` kills the scalar extension of `f`.
      have h : (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map f.hom ≫
          ((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
            _ _).symm g = 0 := by
        rw [← Adjunction.homEquiv_naturality_left_symm, hfg₀, Equiv.symm_apply_eq,
          Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
      -- The reduction of `ofInjective f` has even differential the scalar extension of its
      -- even differential, which is `f` by `ofInjective_obj_d₀`.
      rw [baseChangeFunctor_obj_d₀, FGModuleCat.forget₂_map]
      exact h))

private theorem cokernelπ_quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w)))) ≫
        quotientCokernelDesc hf hfg =
      ((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
        _ _).symm g :=
  Cofork.IsColimit.π_desc (isColimitCokernelπ _)

/-- Composed with `y ↦ [1 ⊗ y]`, the map induced by `g` is `g`. -/
private theorem quotientCokernelπ_comp_quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    quotientCokernelπ
        (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))) ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map
        (quotientCokernelDesc hf hfg) = g := by
  -- The class of `y` is the image of `1 ⊗ y`, on which the adjoint of `g` takes the value `g y`.
  ext y
  refine (congrArg (quotientCokernelDesc hf hfg).hom (quotientCokernelπ_apply _ y)).trans ?_
  refine (ConcreteCategory.congr_hom (cokernelπ_quotientCokernelDesc hf hfg) _).trans ?_
  refine (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (M := Q.obj) _ y).symm.trans ?_
  rw [Equiv.apply_symm_apply]
  -- `ConcreteCategory.hom` on `ModuleCat` is `ModuleCat.Hom.hom` by definition of the instance.
  rfl

/-- **The cokernel of Eisenbud's matrix factorization.** If `0 → P --f--> Q --g--> M → 0` is a
resolution of an `S/(w)`-module `M` by finitely generated projective `S`-modules, then the
cokernel of the reduction modulo `w` of the matrix factorization `ofInjective f` is `M`. The
isomorphism sends the class of `1 ⊗ y` to `g y`. -/
def quotientCokernelIsoOfExact (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) (hg : Function.Surjective g) :
    (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))))).obj ≅ M :=
  have h := quotientCokernelπ_comp_quotientCokernelDesc hf hfg
  (LinearEquiv.ofBijective (quotientCokernelDesc hf hfg).hom
    ⟨fun a b hab ↦ by
      -- Both classes lift to `Q`, where `g` identifies them modulo the image of `f`.
      obtain ⟨a, rfl⟩ := quotientCokernelπ_surjective (ofInjective f hf _) a
      obtain ⟨b, rfl⟩ := quotientCokernelπ_surjective (ofInjective f hf _) b
      have hab' : g.hom a = g.hom b :=
        (ConcreteCategory.congr_hom h a).symm.trans (hab.trans (ConcreteCategory.congr_hom h b))
      have hπ : quotientCokernelπ (ofInjective f hf _) (a - b) = 0 :=
        (exact_d₀_quotientCokernelπ _ _).2
          ((hfg _).1 ((map_sub g.hom a b).trans (sub_eq_zero.2 hab')))
      rw [map_sub, sub_eq_zero] at hπ
      exact hπ,
    fun m ↦ by
      obtain ⟨y, rfl⟩ := hg m
      exact ⟨_, ConcreteCategory.congr_hom h y⟩⟩).toModuleIso

/-- The isomorphism `quotientCokernelIsoOfExact` sends the class of `1 ⊗ y` to `g y`. -/
theorem quotientCokernelIsoOfExact_hom_quotientCokernelπ (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) (hg : Function.Surjective g) (y : Q) :
    (quotientCokernelIsoOfExact hf hfg hg).hom.hom
      (quotientCokernelπ
        (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))) y) = g y :=
  ConcreteCategory.congr_hom (quotientCokernelπ_comp_quotientCokernelDesc hf hfg) y

/-- **Eisenbud's modules are Gorenstein-projective.** For a non-zero-divisor `w`, an
`S/(w)`-module with a resolution `0 → P → Q → M → 0` of length one by finitely generated
projective `S`-modules is Gorenstein-projective over `S/(w)`. -/
theorem isGorensteinProjective_of_exact (hw : w ∈ nonZeroDivisors S)
    (hf : Function.Injective f.hom.hom) (hfg : Function.Exact f.hom.hom g.hom)
    (hg : Function.Surjective g) : IsGorensteinProjective (S ⧸ Ideal.span {w}) M :=
  (IsGorensteinProjective _).prop_of_iso (quotientCokernelIsoOfExact hf hfg hg)
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw _)

end Resolution

/-! ### Cokernels of reductions are the modules with resolutions of length one -/

/-- **Cokernels of matrix factorizations.** For a non-zero-divisor `w`, an `S/(w)`-module `M` is
isomorphic to the cokernel of the reduction modulo `w` of a finite-projective matrix factorization
of `w` exactly when it has a resolution `0 → P → Q → M → 0` of length one by finitely generated
projective `S`-modules. -/
theorem exists_quotientCokernel_iso_iff (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      ∃ (P Q : FGModuleCat.{u} S), Module.Projective S P ∧ Module.Projective S Q ∧
        ∃ (f : P ⟶ Q)
          (g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M),
          Function.Injective f.hom.hom ∧ Function.Exact f.hom.hom g.hom ∧
            Function.Surjective g := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    let e' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).mapIso e
    refine ⟨X.obj.X₀, X.obj.X₁, inferInstance, inferInstance, X.obj.d₀,
      quotientCokernelπ X ≫ e'.hom, d₀_injective hw X, ?_, ?_⟩
    · exact (exact_d₀_quotientCokernelπ X).comp_injective _
        ((ConcreteCategory.bijective_of_isIso e'.hom).1) (by simp)
    · exact (ConcreteCategory.bijective_of_isIso e'.hom).2.comp
        (quotientCokernelπ_surjective X)
  · rintro ⟨P, Q, _, _, f, g, hf, hfg, hg⟩
    exact ⟨_, ⟨quotientCokernelIsoOfExact hf hfg hg⟩⟩

/-- **The essential image of the Gorenstein-projective cokernel functor.** For a non-zero-divisor
`w`, a Gorenstein-projective `S/(w)`-module is isomorphic to the cokernel of the reduction of a
finite-projective matrix factorization exactly when it has a resolution of length one by finitely
generated projective `S`-modules. -/
theorem quotientGorensteinProjectiveCokernel_essImage_iff (hw : w ∈ nonZeroDivisors S)
    (M : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (quotientGorensteinProjectiveCokernel hw).essImage M ↔
      ∃ (P Q : FGModuleCat.{u} S), Module.Projective S P ∧ Module.Projective S Q ∧
        ∃ (f : P ⟶ Q)
          (g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj),
          Function.Injective f.hom.hom ∧ Function.Exact f.hom.hom g.hom ∧
            Function.Surjective g := by
  rw [← exists_quotientCokernel_iso_iff hw]
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨eqToIso (quotientGorensteinProjectiveCokernel_obj_obj hw X).symm ≪≫
      (IsGorensteinProjective _).ι.mapIso e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨ObjectProperty.isoMk _
      (eqToIso (quotientGorensteinProjectiveCokernel_obj_obj hw X) ≪≫ e)⟩⟩

/-- **Cokernels of matrix factorizations by projective dimension.** For a non-zero-divisor `w`,
an `S/(w)`-module that is finitely presented over `S` is isomorphic to the cokernel of the
reduction modulo `w` of a finite-projective matrix factorization of `w` exactly when its
projective dimension over `S` is at most one. -/
theorem exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.FinitePresentation S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M)] :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  rw [exists_quotientCokernel_iso_iff hw]
  constructor
  · rintro ⟨P, Q, _, _, f, g, hf, hfg, hg⟩
    -- The resolution is a short exact sequence with projective first and second terms.
    have hS : (ShortComplex.mk f.hom g (by ext y; exact hfg.apply_apply_eq_zero y)).ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    have : Projective P.obj := (IsProjective.iff_projective P).1 ‹_›
    have : Projective Q.obj := (IsProjective.iff_projective Q).1 ‹_›
    exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  · intro hM
    let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
    -- Present `M` over `S` by a finite free module; the kernel is finitely generated because
    -- `M` is finitely presented, and projective because `M` has projective dimension at most one.
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' S M'
    have : Module.Finite S (LinearMap.ker π) :=
      Module.Finite.iff_fg.2 (Module.FinitePresentation.fg_ker π hπ)
    have hK : Module.Projective S (LinearMap.ker π) := by
      rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact (π.hasProjectiveDimensionLE_succ_iff_ker hπ 0).1 hM
    refine ⟨FGModuleCat.of S (LinearMap.ker π), FGModuleCat.of S (Fin n → S), hK,
      inferInstanceAs (Module.Projective S (Fin n → S)),
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker π).subtype),
      ModuleCat.ofHom (Y := M') π,
      Subtype.val_injective, LinearMap.exact_subtype_ker_map π, hπ⟩

/-- **Cokernels of matrix factorizations over a Noetherian ring.** For a non-zero-divisor `w` of a
Noetherian ring `S`, a finitely generated `S/(w)`-module is isomorphic to the cokernel of the
reduction modulo `w` of a finite-projective matrix factorization of `w` exactly when its
projective dimension over `S` is at most one. -/
theorem exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing
    [IsNoetherianRing S] (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 :=
  have : Module.Finite S ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :=
    ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
  have := Module.finitePresentation_of_finite S
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M)
  exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE hw M

/-- For a non-zero-divisor `w`, an `S/(w)`-module that is finitely presented over `S` and has
projective dimension at most one over `S` is Gorenstein-projective over `S/(w)`. -/
theorem isGorensteinProjective_of_hasProjectiveDimensionLE (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.FinitePresentation S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M)]
    (hM : HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) M := by
  obtain ⟨X, ⟨e⟩⟩ := (exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE hw M).2 hM
  exact (IsGorensteinProjective _).prop_of_iso e
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)

end TauCeti.MatrixFactorization
