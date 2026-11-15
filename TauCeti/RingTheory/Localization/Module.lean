/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localized linear maps

Facts about the localization `LocalizedModule.map S f : Mₛ → Nₛ` of a linear map at a
submonoid `S`:

* `LocalizedModule.map_comp`: localization is functorial, `(g ∘ f)ₛ = gₛ ∘ fₛ`.
* `LocalizedModule.bijective_map_lsmul`: multiplication by an element of `S` becomes bijective
  after localizing at `S`.
* `LocalizedModule.bijective_map_single`: the inclusion of a factor of a finite product becomes
  bijective after localizing at `S` if every other factor vanishes there.
* `LocalizedModule.equivLocalization`: the localization of `R` itself as a module is
  `Localization S`, sending `mk r s` to `Localization.mk r s`.
* `LinearMap.exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id`: if `M` is finitely
  presented and `N` is finitely generated, a left inverse of the localization `iₛ` of
  `i : N → M` descends to a map `φ : M → N` with `φ ∘ i` multiplication by some element of `S`.
* `LinearMap.surjective_localizedModuleMap_map_baseChange`,
  `LinearMap.surjective_localizedModuleMap_powers_baseChange`: surjectivity of a localized linear
  map passes to its scalar extension along any algebra map.
* `Module.FinitePresentation.exists_bijective_map_of_isLocalizedModule`: if `M` is finitely
  presented, an isomorphism between localizations of `M` and `N` at `S` gives a map `M → N` whose
  localization at `S` is bijective.
* `LocalizedModule.bijective_map_dual_eval_iff`: if `M` and its dual are finitely presented, the
  map `M → M**` becomes bijective after localizing at `S` exactly when the localization `Mₛ` is
  reflexive over `Rₛ`. Taking duals commutes with localization for finitely presented modules,
  so `(M**)ₛ` is the double dual of `Mₛ` over `Rₛ`.

We also record that localization commutes with dividing by an element:

* `TauCeti.localizedQuotSMulTopEquiv`: localizing `M ⧸ a M` gives `M_S ⧸ a M_S`.
-/

public section

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N P : Type*} [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Localization of a composite is the composite of the localizations. -/
@[simp]
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map S (g ∘ₗ f) = map S g ∘ₗ map S f := by
  ext x
  induction x using induction_on with
  | h m s => simp

variable {S} (M) in
/-- Multiplication by an element of `S` becomes bijective after localizing at `S`. -/
theorem bijective_map_lsmul {s : R} (hs : s ∈ S) :
    Function.Bijective (map S (LinearMap.lsmul R M s)) := by
  convert (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (mkLinearMap S M) ⟨s, hs⟩)
    using 1
  ext x
  induction x using induction_on with
  | h m t => simp [smul'_mk]

variable {S} in
/-- Localizing the inclusion `E i → ∏ⱼ E j` of a factor of a finite product gives a bijection when
every other factor vanishes after localizing at `S`. -/
theorem bijective_map_single {ι : Type*} [Finite ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] (i : ι)
    (h : ∀ j ≠ i, Subsingleton (LocalizedModule S (E j))) :
    Function.Bijective (map S (LinearMap.single R E i)) := by
  have := Fintype.ofFinite ι
  refine ⟨map_injective S _ (Pi.single_injective i), fun y ↦ ?_⟩
  induction y using induction_on with
  | h x s =>
    -- Some `u ∈ S` kills every coordinate of `x` other than the `i`-th.
    have hc (j : ι) : ∃ c : S, j ≠ i → c • x j = 0 := by
      by_cases hj : j = i
      · exact ⟨1, fun h ↦ (h hj).elim⟩
      · have := h j hj
        obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S (mkLinearMap S (E j))).mp
          (Subsingleton.elim _ 0)
        exact ⟨c, fun _ ↦ hc⟩
    choose c hc using hc
    have hux : (∏ j, c j) • x = Pi.single i ((∏ j, c j) • x i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
          mul_smul, hc j hj, smul_zero]
    refine ⟨mk ((∏ j, c j) • x i) ((∏ j, c j) * s), ?_⟩
    rw [map_mk, LinearMap.coe_single, ← hux, mk_cancel_common_left]

/-- The localization of `R` at `S`, as an `R`-module, is the ring `Localization S`, linearly over
`Localization S`. -/
noncomputable def equivLocalization : LocalizedModule S R ≃ₗ[Localization S] Localization S :=
  (IsLocalizedModule.iso S (Algebra.linearMap R (Localization S))).extendScalarsOfIsLocalization
    S _

/-- `equivLocalization` sends the fraction `r / s` to the same fraction in `Localization S`. -/
@[simp]
theorem equivLocalization_mk (r : R) (s : S) :
    equivLocalization S (mk r s) = Localization.mk r s := by
  rw [equivLocalization, LinearEquiv.extendScalarsOfIsLocalization_apply,
    IsLocalizedModule.iso_apply_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff,
    Algebra.linearMap_apply, Localization.mk_eq_mk', IsLocalization.smul_mk',
    IsLocalization.mk'_mul_cancel_left]

/-- The inverse of `equivLocalization` sends the fraction `r / s` to the same fraction in
`LocalizedModule S R`. -/
@[simp]
theorem equivLocalization_symm_mk (r : R) (s : S) :
    (equivLocalization S).symm (Localization.mk r s) = mk r s :=
  (equivLocalization S).symm_apply_eq.mpr (equivLocalization_mk S r s).symm

end LocalizedModule

namespace LinearMap

open LocalizedModule

variable {R : Type*} [CommRing R] {S : Submonoid R} {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Let `M` be finitely presented and `N` finitely generated. If the localization of
`i : N →ₗ[R] M` at `S` has a left inverse, then some `φ : M →ₗ[R] N` is a left inverse of `i` up
to multiplication by an element of `S`. -/
theorem exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id
    [Module.FinitePresentation R M] [Module.Finite R N]
    (i : N →ₗ[R] M) {ρ : LocalizedModule S M →ₗ[Localization S] LocalizedModule S N}
    (hρ : ρ ∘ₗ LocalizedModule.map S i = LinearMap.id) :
    ∃ s ∈ S, ∃ φ : M →ₗ[R] N, φ ∘ₗ i = LinearMap.lsmul R N s := by
  -- Lift `ρ` to `φ : M → N` with denominator `s`; then `φ ∘ i` and `s` agree after localizing,
  -- hence after multiplication by some `u ∈ S`.
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (mkLinearMap S N) (ρ.restrictScalars R ∘ₗ mkLinearMap S M)
  have key : mkLinearMap S N ∘ₗ (φ ∘ₗ i) = mkLinearMap S N ∘ₗ LinearMap.lsmul R N s := by
    ext n
    have h₁ := congr($hφ (i n))
    have h₂ := congr($hρ (LocalizedModule.mk n 1))
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, mkLinearMap_apply,
      LinearMap.smul_apply, map_mk, LinearMap.id_apply] at h₁ h₂
    simp [h₁, h₂, Submonoid.smul_def, smul'_mk]
  obtain ⟨u, hu⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
    (mkLinearMap S N) _ _ key
  refine ⟨u * s, mul_mem u.2 s.2, (u : R) • φ, ?_⟩
  ext n
  simpa [Submonoid.smul_def, mul_smul] using congr($hu n)

open TensorProduct in
/-- If the localization of `f : M →ₗ[R] N` at `S` is surjective, then the localization of its base
change `f.baseChange A` at the image of `S` in `A` is surjective. -/
theorem surjective_localizedModuleMap_map_baseChange {A : Type*} [CommRing A] [Algebra R A]
    (f : M →ₗ[R] N) (hf : Function.Surjective (LocalizedModule.map S f)) :
    Function.Surjective (LocalizedModule.map (S.map (algebraMap R A)) (f.baseChange A)) := by
  let S' : Submonoid A := S.map (algebraMap R A)
  let locAM := LocalizedModule.mkLinearMap S' (A ⊗[R] M)
  let locAN := LocalizedModule.mkLinearMap S' (A ⊗[R] N)
  let F := LocalizedModule.map S' (f.baseChange A)
  have hpure (a : A) (x : N) : locAN (a ⊗ₜ[R] x) ∈ LinearMap.range F := by
    obtain ⟨z, hz⟩ := hf (LocalizedModule.mk x 1)
    induction z using LocalizedModule.induction_on with
    | h m t =>
      simp only [LocalizedModule.map_mk] at hz
      have hclear : LocalizedModule.mkLinearMap S N (f m) =
          LocalizedModule.mkLinearMap S N ((t : R) • x) := by
        have := congrArg (fun u ↦ t • u) hz
        rwa [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_cancel',
          IsLocalizedModule.mk_eq_mk', Submonoid.smul_def, ← IsLocalizedModule.mk_eq_mk',
          LocalizedModule.smul'_mk, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_one] at this
      obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_iff_exists S (LocalizedModule.mkLinearMap S N)).mp
        hclear
      let c : S' := ⟨algebraMap R A ((u * t : S) : R), ⟨u * t, (u * t).2, rfl⟩⟩
      refine ⟨LocalizedModule.mk (a ⊗ₜ[R] ((u : R) • m)) c, ?_⟩
      apply IsLocalizedModule.smul_injective locAN c
      dsimp only [F, locAN]
      rw [LocalizedModule.map_mk, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_cancel',
        Submonoid.smul_def, ← LinearMap.map_smul, LinearMap.baseChange_tmul, f.map_smul,
        ← Submonoid.smul_def, hu]
      congr 1
      dsimp only [c]
      rw [Submonoid.coe_mul, algebraMap_smul, ← TensorProduct.tmul_smul, Submonoid.smul_def,
        mul_smul]
  have hy_mem (y : A ⊗[R] N) : locAN y ∈ LinearMap.range F := by
    induction y using TensorProduct.inductionOn with
    | tmul a x => exact hpure a x
    | add u v hu hv =>
      rw [map_add]
      exact Submodule.add_mem _ hu hv
  intro w
  induction w using LocalizedModule.induction_on with
  | h y c =>
    obtain ⟨z, hz⟩ := hy_mem y
    induction z using LocalizedModule.induction_on with
    | h t b =>
      refine ⟨LocalizedModule.mk t (b * c), ?_⟩
      apply IsLocalizedModule.smul_injective locAN (b * c)
      have hbz : (b : A) • LocalizedModule.mk t b = locAM t := by
        rw [← Submonoid.smul_def, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_cancel']
      have hcy : c • LocalizedModule.mk y c = locAN y := by
        rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_cancel']
      have h1 : (b * c) • F (LocalizedModule.mk t (b * c)) = F (locAM t) := by
        dsimp only [F]
        rw [LocalizedModule.map_mk, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_cancel']
        exact (LocalizedModule.map_mk S' (f.baseChange A) t 1).symm
      have h2 : (b * c) • LocalizedModule.mk y c = F (locAM t) := by
        rw [mul_smul, hcy, ← hz, Submonoid.smul_def]
        exact ((F.restrictScalars A).map_smul (b : A) (LocalizedModule.mk t b)).symm.trans
          (congrArg F hbz)
      exact h1.trans h2.symm

open TensorProduct in
/-- If `LocalizedModule.map (.powers r) f` is surjective, then the localization of `f.baseChange A`
at `algebraMap R A r` is surjective. -/
theorem surjective_localizedModuleMap_powers_baseChange {A : Type*} [CommRing A] [Algebra R A]
    (f : M →ₗ[R] N) (r : R) (hf : Function.Surjective (LocalizedModule.map (.powers r) f)) :
    Function.Surjective (LocalizedModule.map (.powers (algebraMap R A r)) (f.baseChange A)) := by
  rw [← Submonoid.map_powers]
  exact surjective_localizedModuleMap_map_baseChange f hf

end LinearMap

namespace Module.FinitePresentation

variable {R : Type*} [CommRing R] (S : Submonoid R) {M N M' N' : Type*} [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N']
  [Module R N'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- Let `M` be finitely presented. An isomorphism `l : M' ≃ N'` between localizations of `M` and
`N` at `S` comes, up to multiplication by an element of `S`, from a linear map `h : M → N`; in
particular the localization of `h` is bijective. This is the first step of the proof of Mathlib's
`Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule`. -/
theorem exists_bijective_map_of_isLocalizedModule [FinitePresentation R M] (l : M' ≃ₗ[R] N') :
    ∃ h : M →ₗ[R] N, Function.Bijective (IsLocalizedModule.map S f g h) := by
  obtain ⟨h, s, hh⟩ := exists_lift_of_isLocalizedModule S g (l.toLinearMap ∘ₗ f)
  refine ⟨h, ?_⟩
  have : IsLocalizedModule.map S f g h = (s • LinearMap.id) ∘ₗ l.toLinearMap := by
    refine IsLocalizedModule.ext S f (IsLocalizedModule.map_units g) (LinearMap.ext fun x ↦ ?_)
    simpa using congr($hh x)
  rw [this]
  exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).comp l.bijective

end Module.FinitePresentation

namespace LocalizedModule

open Module

variable {R : Type*} [CommRing R] (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']

/-- Let `f : M → M'` be a localization of `M` at `S`, over the localization `Rₛ` of `R`. If `M`
and its dual are finitely presented, the canonical map `M → M**` becomes bijective after
localizing at `S` exactly when `M'` is reflexive over `Rₛ`. -/
theorem bijective_map_dual_eval_iff (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [FinitePresentation R M] [FinitePresentation R (Dual R M)] :
    Function.Bijective (map S (Dual.eval R M)) ↔ Function.Bijective (Dual.eval Rₛ M') := by
  -- Localizing the dual and the double dual: `D` and `E` are localizations at `S`, because
  -- `M` and `M*` are finitely presented.
  let g := Algebra.linearMap R Rₛ
  let D : Dual R M →ₗ[R] Dual Rₛ M' := IsLocalizedModule.mapExtendScalars S f g Rₛ
  let E : Dual R (Dual R M) →ₗ[R] Dual Rₛ (Dual Rₛ M') :=
    IsLocalizedModule.mapExtendScalars S D g Rₛ
  -- Under these identifications, the localization of `M → M**` is `M' → M'**`.
  have key : IsLocalizedModule.map S f E (Dual.eval R M) =
      (Dual.eval Rₛ M').restrictScalars R := by
    refine IsLocalizedModule.linearMap_ext S f E ?_
    rw [IsLocalizedModule.map_comp]
    ext m : 1
    refine LinearMap.restrictScalars_injective R (IsLocalizedModule.linearMap_ext S D g ?_)
    ext φ
    simp [E, D, g]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective f E, key,
    LinearMap.coe_restrictScalars]

end LocalizedModule

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

variable (M) in
/-- Localization commutes with dividing a module by an element: for `a : R` and a submonoid `S`,
the localization of `M ⧸ a M` at `S` is `M_S ⧸ a M_S`, linearly over `R_S`. -/
noncomputable def localizedQuotSMulTopEquiv (a : R) (S : Submonoid R) :
    LocalizedModule S (QuotSMulTop a M) ≃ₗ[Localization S]
      QuotSMulTop (algebraMap R (Localization S) a) (LocalizedModule S M) :=
  (localizedQuotientEquiv _ _).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.localized, ← Submodule.ideal_span_singleton_smul,
      Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
      Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul])

/-- `TauCeti.localizedQuotSMulTopEquiv` sends `(m mod a M) / s` to `(m / s) mod a M_S`. -/
@[simp]
theorem localizedQuotSMulTopEquiv_mk (a : R) (S : Submonoid R) (m : M) (s : S) :
    localizedQuotSMulTopEquiv M a S (LocalizedModule.mk (Submodule.Quotient.mk m) s) =
      Submodule.Quotient.mk (LocalizedModule.mk m s) := by
  have h1 : localizedQuotSMulTopEquiv M a S
      (LocalizedModule.mkLinearMap S (QuotSMulTop a M) (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := by
    rw [localizedQuotSMulTopEquiv, LinearEquiv.trans_apply]
    -- `localizedQuotientEquiv` is `IsLocalizedModule.linearEquiv` with scalars restricted.
    exact (congrArg _ (IsLocalizedModule.linearEquiv_symm_apply S
      (Submodule.toLocalizedQuotient S _) (LocalizedModule.mkLinearMap S _)
      (Submodule.Quotient.mk m))).trans (Submodule.quotEquivOfEq_mk _ _ _ _)
  -- Divide by `s` using `Localization S`-linearity.
  have hs {N : Type v} [AddCommGroup N] [Module R N] (x : N) :
      LocalizedModule.mk x s = Localization.mk (1 : R) s • LocalizedModule.mk x 1 := by
    rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
  rw [hs, map_smul, ← LocalizedModule.mkLinearMap_apply, h1, LocalizedModule.mkLinearMap_apply,
    ← Submodule.Quotient.mk_smul, hs]

end TauCeti
