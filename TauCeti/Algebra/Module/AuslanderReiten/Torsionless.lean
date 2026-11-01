/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import TauCeti.LinearAlgebra.Dual.Opposite

/-!
# Torsionless and reflexive modules through a projective presentation

Let `A` be a ring and `M` a left `A`-module with a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely
generated projective modules. The evaluation `M ⟶ M**` into the opposite double dual
(`TauCeti.opDualEval`) is compared with extension problems for right `A`-linear functionals, using
that finitely generated projective modules are reflexive (`TauCeti.opDualEvalEquiv`).

* Evaluation is surjective if and only if every functional on `M*` extends along the dual
  `M* ⟶ P₀*` of the augmentation.
* Evaluation is injective, that is, `M` is torsionless, if and only if every functional on the
  image `K` of the dual `P₀* ⟶ P₁*` of the presenting map extends along `K ⟶ P₁*`.

These are the obstruction groups of the Auslander–Bridger exact sequence
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`, where `Tr M = coker(P₀* ⟶ P₁*)` is the
transpose (`TauCeti.AuslanderReitenTranspose`). The short exact sequences of right modules
`0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` and `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` have projective middle terms, so the second
extension problem is `Ext¹(Tr M, A) = 0` and the first is `Ext¹(K, A) = 0`, that is,
`Ext²(Tr M, A) = 0`. Hence `M` is torsionless exactly when `Ext¹(Tr M, A) = 0`, and reflexive
exactly when moreover `Ext²(Tr M, A) = 0`.

## Main results

* `TauCeti.opDualEval_surjective_iff_exists_comp_lcomp_eq`: surjectivity of evaluation as an
  extension property along `M* ⟶ P₀*`.
* `TauCeti.opDualEval_injective_iff_exists_comp_subtype_eq`: injectivity of evaluation as an
  extension property along `K ⟶ P₁*`.
* `TauCeti.opDualEval_injective_iff_ext_one_eq_zero`: `M` is torsionless if and only if
  `Ext¹(Tr M, A) = 0`.
* `TauCeti.opDualEval_surjective_iff_ext_two_eq_zero`: evaluation is surjective if and only if
  `Ext²(Tr M, A) = 0`.
* `TauCeti.opDualEval_bijective_iff_ext_eq_zero`: `M` is reflexive if and only if
  `Ext¹(Tr M, A) = 0` and `Ext²(Tr M, A) = 0`.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969),
  Proposition 2.6.
-/

public section

namespace TauCeti

section Linear

variable {A : Type*} [Ring A] {P₀ P₁ M : Type*} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup M] [Module A M]
  [Module.Finite A P₀] [Module.Projective A P₀]

/-- **Surjectivity of evaluation**: for a surjection `π : P₀ ⟶ M` from a finitely generated
projective module, evaluation `M ⟶ M**` is surjective if and only if every functional on `M*`
extends along the dual `π* : M* ⟶ P₀*`. -/
theorem opDualEval_surjective_iff_exists_comp_lcomp_eq {π : P₀ →ₗ[A] M}
    (hπ : Function.Surjective π) :
    Function.Surjective (opDualEval A M) ↔
      ∀ g : Module.Dual A M →ₗ[Aᵐᵒᵖ] A, ∃ h : Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A,
        h ∘ₗ π.lcomp Aᵐᵒᵖ A = g := by
  refine ⟨fun hev g ↦ ?_, fun hext g ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := hev g
    obtain ⟨x, rfl⟩ := hπ m
    exact ⟨opDualEval A P₀ x, LinearMap.ext fun φ ↦ by
      simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, opDualEval_apply]⟩
  · obtain ⟨h, rfl⟩ := hext g
    refine ⟨π ((opDualEvalEquiv A P₀).symm h), LinearMap.ext fun φ ↦ ?_⟩
    rw [opDualEval_apply, LinearMap.comp_apply, ← apply_opDualEvalEquiv_symm A P₀ h,
      LinearMap.lcomp_apply]

variable [Module.Finite A P₁] [Module.Projective A P₁] {p : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}

omit [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁] [Module.Projective A P₁] in
/-- A functional on `P₀` vanishing on the image of `p` factors through the cokernel `π`. -/
private lemma exists_comp_eq_of_comp_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) (ψ : Module.Dual A P₀) (hψ : ψ ∘ₗ p = 0) :
    ∃ φ : Module.Dual A M, φ ∘ₗ π = ψ := by
  refine ⟨(LinearMap.range p).liftQ ψ (by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hψ, LinearMap.zero_apply]) ∘ₗ
      (hexact.linearEquivOfSurjective hπ).symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  simp

/-- **Injectivity of evaluation**: for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely generated
projective modules, evaluation `M ⟶ M**` is injective, that is, `M` is torsionless, if and only if
every functional on the image `K` of the dual `p* : P₀* ⟶ P₁*` extends to `P₁*`. -/
theorem opDualEval_injective_iff_exists_comp_subtype_eq (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Injective (opDualEval A M) ↔
      ∀ g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A, ∃ h : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] A,
        h ∘ₗ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype = g := by
  refine ⟨fun hev g ↦ ?_, fun hext ↦ ?_⟩
  · -- `g` precomposed with `P₀* ⟶ K` is evaluation at some `x : P₀`, and `π x` evaluates to zero.
    obtain ⟨x, hx⟩ : ∃ x : P₀, ∀ ψ : Module.Dual A P₀, ψ x = g ⟨ψ ∘ₗ p, ψ, rfl⟩ :=
      ⟨(opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict),
        fun ψ ↦ apply_opDualEvalEquiv_symm A P₀ _ ψ⟩
    have h0 : π x = 0 := hev (LinearMap.ext fun φ ↦ by
      rw [opDualEval_apply, map_zero, LinearMap.zero_apply, ← LinearMap.comp_apply φ π, hx]
      convert g.map_zero
      ext y
      simp [hexact.apply_apply_eq_zero])
    obtain ⟨y, hy⟩ := (hexact x).1 h0
    refine ⟨opDualEval A P₁ y, LinearMap.ext fun ⟨k, ψ, hk⟩ ↦ ?_⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, opDualEval_apply]
    have := hx ψ
    simp only [← hk, LinearMap.lcomp_apply] at this ⊢
    rw [hy, this]
    rfl
  · -- An element `π x` evaluating to zero gives a functional `ψ ∘ p ↦ ψ x` on `K`.
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨x, rfl⟩ := hπ m
    have hker : LinearMap.ker (p.lcomp Aᵐᵒᵖ A) ≤ LinearMap.ker (opDualEval A P₀ x) := by
      intro ψ hψ
      obtain ⟨φ, rfl⟩ := exists_comp_eq_of_comp_eq_zero hexact hπ ψ hψ
      have := LinearMap.congr_fun hm φ
      rw [opDualEval_apply, LinearMap.zero_apply] at this
      rw [LinearMap.mem_ker, opDualEval_apply, LinearMap.comp_apply, this]
    obtain ⟨h, hh⟩ := hext ((LinearMap.ker (p.lcomp Aᵐᵒᵖ A)).liftQ _ hker ∘ₗ
      (p.lcomp Aᵐᵒᵖ A).quotKerEquivRange.symm.toLinearMap)
    let y := (opDualEvalEquiv A P₁).symm h
    have hy : x = p y := (opDualEval_bijective A P₀).1 (LinearMap.ext fun ψ ↦ by
      have := LinearMap.congr_fun hh ⟨(p.lcomp Aᵐᵒᵖ A) ψ, LinearMap.mem_range_self _ ψ⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
        Submodule.liftQ_apply,
        opDualEval_apply] at this
      rw [opDualEval_apply, opDualEval_apply, ← LinearMap.comp_apply ψ p,
        ← LinearMap.lcomp_apply' (S := Aᵐᵒᵖ) (N := A), apply_opDualEvalEquiv_symm, this])
    rw [hy, hexact.apply_apply_eq_zero]

end Linear

section Ext

open CategoryTheory CategoryTheory.Abelian

universe w u

variable {A : Type u} [Ring A] {P₀ P₁ M : Type u} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup M] [Module A M]
  {p : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}

variable (p) in
/-- The short exact sequence `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` of right modules, where `K` is the image of
the dual `p* : P₀* ⟶ P₁*`. -/
private noncomputable abbrev transposeShortComplex : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
  ShortComplex.mk (X₁ := ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)))
    (X₂ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A P₁))
    (X₃ := ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p))
    (ModuleCat.ofHom (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype)
    (ModuleCat.ofHom (AuslanderReitenTranspose.mk p))
    (ModuleCat.hom_ext (LinearMap.ext fun ⟨_, hx⟩ ↦
      (AuslanderReitenTranspose.mk_eq_zero_iff p _).2 hx))

private lemma transposeShortComplex_shortExact : (transposeShortComplex p).ShortExact := by
  refine .mk' (ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ ?_) ?_ ?_
  · simp
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact AuslanderReitenTranspose.mk_surjective p

variable (p π) in
/-- The short exact sequence `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` of right modules dual to a presentation. -/
private noncomputable abbrev dualShortComplex (h : π ∘ₗ p = 0) :
    ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
  ShortComplex.mk (X₁ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A M))
    (X₂ := ModuleCat.of Aᵐᵒᵖ (Module.Dual A P₀))
    (X₃ := ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)))
    (ModuleCat.ofHom (π.lcomp Aᵐᵒᵖ A))
    (ModuleCat.ofHom (p.lcomp Aᵐᵒᵖ A).rangeRestrict)
    (ModuleCat.hom_ext (LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.ext fun x ↦ by
      simp [← LinearMap.comp_apply π p, h])))

private lemma dualShortComplex_shortExact (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    (dualShortComplex p π hexact.linearMap_comp_eq_zero).ShortExact := by
  refine .mk' (ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ ?_) ?_ ?_
  · ext ψ
    simp only [ModuleCat.hom_ofHom, LinearMap.mem_range, LinearMap.mem_ker]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨φ, rfl⟩
      exact Subtype.ext (LinearMap.ext fun x ↦ by
        simp [← LinearMap.comp_apply π p, hexact.linearMap_comp_eq_zero])
    · obtain ⟨φ, rfl⟩ := exists_comp_eq_of_comp_eq_zero hexact hπ ψ (by
        simpa [LinearMap.lcomp_apply'] using congrArg Subtype.val h)
      exact ⟨φ, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro φ φ' h
    ext m
    obtain ⟨x, rfl⟩ := hπ m
    exact LinearMap.congr_fun h x
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.surjective_rangeRestrict _

variable [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁]
  [Module.Projective A P₁] [HasExt.{w} (ModuleCat.{u} Aᵐᵒᵖ)]

/-- **Torsionless modules** (Auslander–Bridger): for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely
generated projective modules, evaluation `M ⟶ M**` is injective if and only if
`Ext¹(Tr M, A) = 0`, where `Tr M` is the transpose of the presentation. -/
theorem opDualEval_injective_iff_ext_one_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Injective (opDualEval A M) ↔
      ∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1,
        e = 0 := by
  refine (opDualEval_injective_iff_exists_comp_subtype_eq hexact hπ).trans
    (Iff.trans ?_ (transposeShortComplex_shortExact (p := p)).forall_ext_one_eq_zero_iff.symm)
  refine ⟨fun h ψ ↦ ?_, fun h g ↦ ?_⟩
  · obtain ⟨g, hg⟩ := h ψ.hom
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  · obtain ⟨g', hg'⟩ := h (ModuleCat.ofHom g)
    exact ⟨g'.hom, congrArg ModuleCat.Hom.hom hg'⟩

/-- **Surjectivity of evaluation** (Auslander–Bridger): for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by
finitely generated projective modules, evaluation `M ⟶ M**` is surjective if and only if
`Ext²(Tr M, A) = 0`. -/
theorem opDualEval_surjective_iff_ext_two_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Surjective (opDualEval A M) ↔
      ∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2,
        e = 0 := by
  refine (opDualEval_surjective_iff_exists_comp_lcomp_eq hπ).trans (Iff.trans ?_
    ((transposeShortComplex_shortExact (p := p)).forall_ext_add_two_eq_zero_iff 0).symm)
  refine Iff.trans ?_ (dualShortComplex_shortExact hexact hπ).forall_ext_one_eq_zero_iff.symm
  refine ⟨fun h ψ ↦ ?_, fun h g ↦ ?_⟩
  · obtain ⟨g, hg⟩ := h ψ.hom
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  · obtain ⟨g', hg'⟩ := h (ModuleCat.ofHom g)
    exact ⟨g'.hom, congrArg ModuleCat.Hom.hom hg'⟩

/-- **Reflexive modules** (Auslander–Bridger): for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely
generated projective modules, evaluation `M ⟶ M**` is bijective if and only if
`Ext¹(Tr M, A) = 0` and `Ext²(Tr M, A) = 0`. -/
theorem opDualEval_bijective_iff_ext_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Bijective (opDualEval A M) ↔
      (∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1,
        e = 0) ∧
      ∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2,
        e = 0 := by
  rw [Function.Bijective, opDualEval_injective_iff_ext_one_eq_zero hexact hπ,
    opDualEval_surjective_iff_ext_two_eq_zero hexact hπ]

end Ext

end TauCeti
