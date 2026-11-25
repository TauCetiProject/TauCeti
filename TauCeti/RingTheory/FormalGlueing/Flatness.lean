/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
import TauCeti.Algebra.Module.LocalizedModule.BaseChange
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# Flatness and projectivity on the pieces of formal glueing

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, where `I` has a finite
generating set `G`. A module is flat if and only if its scalar extensions to `S` and to every
`R[1/g]`, for `g ∈ G`, are flat. A finitely generated module is projective if and only if these
scalar extensions are projective. No Noetherian hypothesis is needed.

Together with the detection of finite generation and finite presentation in
`TauCeti.RingTheory.FormalGlueing.Finiteness`, these are the property clauses of formal glueing
of modules: a module glued from pieces that are finite, finitely presented, flat, or finite
projective has the same property over `R`. The projectivity clause is stated for finitely
generated modules; there, projective is the same as flat and finitely presented
(`Module.Flat.projective_of_finitePresentation`), so it follows from the other clauses.

Flatness is tested on ideals (`Module.Flat.iff_lTensor_injective'`): for an ideal `J` of `R`, an
element of the kernel of `M ⊗[R] J → M ⊗[R] R` becomes zero in `M' ⊗[R] J` along any map from
`M` to a flat module `M'`. Taking for `M'` the base change `S ⊗[R] M` and the localizations
`M[1/g]`, which are flat over `R` because `S` and `R[1/g]` are, the element vanishes on every
formal-glueing piece, so it is zero (`TauCeti.eq_zero_of_one_tmul_eq_zero_of_localized`).

`IsBaseChange.flat_of_formalGlueing` and `IsBaseChange.projective_of_formalGlueing` (together with
their `LocalizedModule` variants) package these criteria for an abstract base-change map
`φ : E →ₗ[R] N` and principal-localization equivalences to `M`, in the form produced by
`IsBaseChange.exists_formalGlueing_module`.

## References

* The Stacks Project, Proposition 15.91.16 (05ER), formal glueing of modules.
* The Stacks Project, Remark 15.91.20 (05EU), preservation of flatness and finite projectivity
  in formal glueing.
-/

public section

open TensorProduct Function

namespace TauCeti

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] {G : Finset R}

/-- Flatness is detected on the formal-glueing pieces. The tensor products with
`Localization.Away g` are the principal localizations of the module. -/
theorem flat_iff_baseChange_and_localized
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Flat R M ↔ Module.Flat S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.Flat (Localization.Away g) (Localization.Away g ⊗[R] M) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  have : Module.Flat R (S ⊗[R] M) := .trans R S _
  refine Module.Flat.iff_lTensor_injective'.mpr fun J ↦
    (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  -- On each piece, `x` is sent along a map `ψ` from `M` to a flat module `M'`; its image in
  -- `M' ⊗[R] J` vanishes, since `M' ⊗[R] J → M' ⊗[R] R` is injective and `ψ` commutes with the
  -- inclusion of `J`.
  refine eq_zero_of_one_tmul_eq_zero_of_localized hG x ?_ fun g hg ↦ ?_
  · have h : (TensorProduct.assoc R S M J).toLinearMap ∘ₗ (TensorProduct.mk R S M 1).rTensor J =
        TensorProduct.mk R S (M ⊗[R] J) 1 := by
      ext m j
      simp
    have h0 : (TensorProduct.mk R S M 1).rTensor J x = 0 :=
      Module.Flat.rTensor_apply_eq_zero_of_lTensor_apply_eq_zero _ J.injective_subtype hx
    simpa [h0] using (LinearMap.congr_fun h x).symm
  · have := hloc g hg
    have : Module.Flat R (Localization.Away g ⊗[R] M) := .trans R (Localization.Away g) _
    have : Module.Flat R (LocalizedModule (.powers g) M) := .of_linearEquiv
      ((LocalizedModule.equivTensorProduct (.powers g) M).restrictScalars R)
    have h0 : (LocalizedModule.mkLinearMap (.powers g) M).rTensor J x = 0 :=
      Module.Flat.rTensor_apply_eq_zero_of_lTensor_apply_eq_zero _ J.injective_subtype hx
    -- Localizing `M ⊗[R] J` at `g` is localizing the factor `M`.
    have : IsLocalizedModule (.powers g)
        ((LocalizedModule.mkLinearMap (.powers g) M).rTensor J) :=
      IsLocalizedModule.rTensor (A := R) (.powers g) (LocalizedModule.mkLinearMap (.powers g) M)
    exact (IsLocalizedModule.eq_zero_iff (.powers g) _).mpr
      ((IsLocalizedModule.eq_zero_iff (.powers g) _).mp h0)

/-- Projectivity of a finitely generated module is detected on the formal-glueing pieces. The
tensor products with `Localization.Away g` are the principal localizations of the module. -/
theorem projective_iff_baseChange_and_localized [Module.Finite R M]
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Projective R M ↔ Module.Projective S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.Projective (Localization.Away g) (Localization.Away g ⊗[R] M) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  have : Module.FinitePresentation R M := (finitePresentation_iff_baseChange_and_localized hG).mpr
    ⟨Module.finitePresentation_of_projective _ _, fun g hg ↦ by
      have := hloc g hg
      exact Module.finitePresentation_of_projective _ _⟩
  have : Module.Flat R M := (flat_iff_baseChange_and_localized hG).mpr
    ⟨inferInstance, fun g hg ↦ by
      have := hloc g hg
      infer_instance⟩
  exact Module.Flat.projective_of_finitePresentation

end TauCeti

namespace IsBaseChange

variable {R S E M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Any module `E` glued from a flat `S`-module `N` and a locally flat `R`-module `M` across `G`
via `Localization.Away r ⊗[R] _` equivalences is flat over `R`. -/
@[stacks 05EU "flatness of a glued module"]
theorem flat_of_formalGlueing
    {φ : E →ₗ[R] N} (hφ : IsBaseChange S φ) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (e_loc : ∀ r ∈ G, Localization.Away r ⊗[R] E ≃ₗ[Localization.Away r]
      Localization.Away r ⊗[R] M)
    [Module.Flat S N]
    (hM : ∀ r ∈ G, Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] M)) :
    Module.Flat R E :=
  (TauCeti.flat_iff_baseChange_and_localized hG).mpr
    ⟨.of_linearEquiv hφ.equiv, fun r hr ↦ by
      have := hM r hr
      exact .of_linearEquiv (e_loc r hr)⟩

/-- Any module `E` glued from a finite projective `S`-module `N` and a locally finite projective
`R`-module `M` across `G` via `Localization.Away r ⊗[R] _` equivalences is projective over `R`; it
is finitely generated by `IsBaseChange.finite_of_formalGlueing`. -/
@[stacks 05EU "finite projectivity of a glued module"]
theorem projective_of_formalGlueing
    {φ : E →ₗ[R] N} (hφ : IsBaseChange S φ) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (e_loc : ∀ r ∈ G, Localization.Away r ⊗[R] E ≃ₗ[Localization.Away r]
      Localization.Away r ⊗[R] M)
    [Module.Finite S N] [Module.Projective S N]
    (hMf : ∀ r ∈ G, Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] M))
    (hMp : ∀ r ∈ G, Module.Projective (Localization.Away r) (Localization.Away r ⊗[R] M)) :
    Module.Projective R E :=
  have := hφ.finite_of_formalGlueing G hG e_loc hMf
  (TauCeti.projective_iff_baseChange_and_localized hG).mpr
    ⟨.of_equiv hφ.equiv.symm, fun r hr ↦ by
      have := hMp r hr
      exact .of_equiv (e_loc r hr).symm⟩

/-- Any module `E` glued from a flat `S`-module `N` and a locally flat `R`-module `M` across `G`
via `LocalizedModule (.powers r) _` equivalences is flat over `R`. -/
@[stacks 05EU "flatness of a glued module"]
theorem flat_of_formalGlueing_localizedModule
    {φ : E →ₗ[R] N} (hφ : IsBaseChange S φ) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (e_loc : ∀ r ∈ G, LocalizedModule (.powers r) E ≃ₗ[Localization.Away r]
      LocalizedModule (.powers r) M)
    [Module.Flat S N]
    (hM : ∀ r ∈ G, Module.Flat (Localization.Away r) (LocalizedModule (.powers r) M)) :
    Module.Flat R E :=
  hφ.flat_of_formalGlueing G hG
    (fun r hr ↦ LocalizedModule.tensorProductEquivOfEquiv (e_loc r hr))
    (fun r hr ↦ by
      have := hM r hr
      exact .of_linearEquiv (LocalizedModule.equivTensorProduct (.powers r) M).symm)

/-- Any module `E` glued from a finite projective `S`-module `N` and a locally finite projective
`R`-module `M` across `G` via `LocalizedModule (.powers r) _` equivalences is projective over `R`;
it is finitely generated by `IsBaseChange.finite_of_formalGlueing_localizedModule`. -/
@[stacks 05EU "finite projectivity of a glued module"]
theorem projective_of_formalGlueing_localizedModule
    {φ : E →ₗ[R] N} (hφ : IsBaseChange S φ) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (e_loc : ∀ r ∈ G, LocalizedModule (.powers r) E ≃ₗ[Localization.Away r]
      LocalizedModule (.powers r) M)
    [Module.Finite S N] [Module.Projective S N]
    (hMf : ∀ r ∈ G, Module.Finite (Localization.Away r) (LocalizedModule (.powers r) M))
    (hMp : ∀ r ∈ G, Module.Projective (Localization.Away r) (LocalizedModule (.powers r) M)) :
    Module.Projective R E :=
  hφ.projective_of_formalGlueing G hG
    (fun r hr ↦ LocalizedModule.tensorProductEquivOfEquiv (e_loc r hr))
    (fun r hr ↦ by
      have := hMf r hr
      exact Module.Finite.equiv (LocalizedModule.equivTensorProduct (.powers r) M))
    (fun r hr ↦ by
      have := hMp r hr
      exact .of_equiv (LocalizedModule.equivTensorProduct (.powers r) M))

end IsBaseChange
