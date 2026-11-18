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
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localized linear maps

Facts about the localization `LocalizedModule.map S f : Mₛ → Nₛ` of a linear map at a
submonoid `S`:

* `LocalizedModule.map_comp`: localization is functorial, `(g ∘ f)ₛ = gₛ ∘ fₛ`.
* `LocalizedModule.surjective_map_of_exact_of_subsingleton`,
  `LocalizedModule.bijective_map_of_exact_of_subsingleton`: in an exact sequence `M → N → P` with
  `P_S` a subsingleton, `M_S → N_S` is surjective (and bijective when `M → N` is injective).
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

/-- In an exact sequence `M → N → P`, if `P_S` is a subsingleton, then `M_S → N_S` is
surjective. -/
theorem surjective_map_of_exact_of_subsingleton {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hex : Function.Exact f g) [Subsingleton (LocalizedModule S P)] :
    Function.Surjective (map S f) :=
  (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    (mkLinearMap S M) (mkLinearMap S N)).mp
    fun y ↦ (LocalizedModule.map_exact S f g hex y).mp (Subsingleton.elim _ 0)

/-- In an exact sequence `0 → M → N → P`, if `f : M → N` is injective and `P_S` is a
subsingleton, then `M_S → N_S` is bijective. -/
theorem bijective_map_of_exact_of_subsingleton {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : Function.Injective f) (hex : Function.Exact f g)
    [Subsingleton (LocalizedModule S P)] :
    Function.Bijective (map S f) :=
  ⟨map_injective S f hf, surjective_map_of_exact_of_subsingleton S hex⟩

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

section

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

end

section Semiring

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M N : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {A : Type*} [CommSemiring A] [Algebra R A]

open TensorProduct in
/-- If the localization of `f : M →ₗ[R] N` at `S` is surjective, then the localization of its base
change `f.baseChange A` at the image of `S` in `A` is surjective. -/
theorem surjective_localizedModuleMap_map_baseChange (f : M →ₗ[R] N)
    (hf : Function.Surjective (LocalizedModule.map S f)) :
    Function.Surjective (LocalizedModule.map (S.map (algebraMap R A)) (f.baseChange A)) := by
  let lM : A ⊗[R] M →ₗ[R] LocalizedModule S M ⊗[R] A :=
    TensorProduct.AlgebraTensorModule.rTensor R A (mkLinearMap S M) ∘ₗ
      (TensorProduct.comm R A M).toLinearMap
  let lN : A ⊗[R] N →ₗ[R] LocalizedModule S N ⊗[R] A :=
    TensorProduct.AlgebraTensorModule.rTensor R A (mkLinearMap S N) ∘ₗ
      (TensorProduct.comm R A N).toLinearMap
  have hl : IsLocalizedModule.map S lM lN ((f.baseChange A).restrictScalars R) =
      ((LocalizedModule.map S f).restrictScalars R).rTensor A := by
    apply IsLocalizedModule.linearMap_ext S lM lN
    rw [IsLocalizedModule.map_comp]
    ext a m
    simp [lM, lN]
  have hsurj_R :
      Function.Surjective (LocalizedModule.map S ((f.baseChange A).restrictScalars R)) :=
    (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective lM lN).mp
      (hl ▸ LinearMap.rTensor_surjective A (hf : Function.Surjective (LocalizedModule.map S f)))
  -- `Algebra.algebraMapSubmonoid A S` is `S.map (algebraMap R A)` by definition.
  let S' : Submonoid A := Algebra.algebraMapSubmonoid A S
  let m' : A ⊗[R] M →ₗ[R] LocalizedModule S' (A ⊗[R] M) :=
    (mkLinearMap S' (A ⊗[R] M)).restrictScalars R
  let n' : A ⊗[R] N →ₗ[R] LocalizedModule S' (A ⊗[R] N) :=
    (mkLinearMap S' (A ⊗[R] N)).restrictScalars R
  have : IsLocalizedModule S m' := IsLocalizedModule.restrictScalars S _
  have : IsLocalizedModule S n' := IsLocalizedModule.restrictScalars S _
  have hm : IsLocalizedModule.map S m' n' ((f.baseChange A).restrictScalars R) =
      (LocalizedModule.map S' (f.baseChange A)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S m' n'
    refine LinearMap.ext fun x ↦ ?_
    exact (IsLocalizedModule.map_apply S m' n' _ x).trans
      (LocalizedModule.map_mk S' (f.baseChange A) x 1).symm
  have hsurj_S' :=
    (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective m' n').mpr hsurj_R
  rwa [hm] at hsurj_S'

open TensorProduct in
/-- If `LocalizedModule.map (.powers r) f` is surjective, then the localization of `f.baseChange A`
at `algebraMap R A r` is surjective. -/
theorem surjective_localizedModuleMap_powers_baseChange (f : M →ₗ[R] N) (r : R)
    (hf : Function.Surjective (LocalizedModule.map (.powers r) f)) :
    Function.Surjective (LocalizedModule.map (.powers (algebraMap R A r)) (f.baseChange A)) := by
  rw [← Submonoid.map_powers]
  exact surjective_localizedModuleMap_map_baseChange f hf

end Semiring

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
