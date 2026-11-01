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
# The Auslander–Bridger sequence

Let `A` be a ring and `M` a left `A`-module with a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely
generated projective modules. Write `M* = Hom_A(M, A)` for the dual right module, `M**` for the
opposite double dual and `Tr M = coker(P₀* ⟶ P₁*)` for the transpose of the presentation
(`TauCeti.AuslanderReitenTranspose`). This file constructs the **Auslander–Bridger sequence**

`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`,

whose middle map is evaluation (`TauCeti.opDualEval`), with `Ext` computed among right modules
(`ModuleCat Aᵐᵒᵖ`). Mathlib's `Ext` groups are abelian groups, so the outer maps are additive maps;
the left `A`-module structure of `Ext^i(Tr M, A)`, coming from the left action of `A` on itself, is
not used here.

Let `K` be the image of `P₀* ⟶ P₁*`, so that `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` and
`0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` are short exact with projective middle terms. Every class in
`Ext¹(Tr M, A)` is the connecting image of a functional `g : K ⟶ A`, and the first map sends it
to the image in `M` of the element of `P₀ ≅ P₀**` representing `ψ ↦ g (ψ ∘ p)`. The last map is the
composite of the two connecting maps `Hom(M*, A) ⟶ Ext¹(K, A) ⟶ Ext²(Tr M, A)`. Exactness reduces
to the reflexivity of finitely generated projective modules (`TauCeti.opDualEvalEquiv`).

As consequences, `M` is torsionless (evaluation is injective) exactly when `Ext¹(Tr M, A) = 0`,
evaluation is surjective exactly when `Ext²(Tr M, A) = 0`, and `M` is reflexive exactly when both
vanish.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.extOneToModule`: the map `Ext¹(Tr M, A) ⟶ M`.
* `TauCeti.AuslanderReitenTranspose.doubleDualToExtTwo`: the map `M** ⟶ Ext²(Tr M, A)`.

## Main results

* `TauCeti.AuslanderReitenTranspose.injective_extOneToModule`,
  `TauCeti.AuslanderReitenTranspose.exact_extOneToModule_opDualEval`,
  `TauCeti.AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo` and
  `TauCeti.AuslanderReitenTranspose.surjective_doubleDualToExtTwo`: exactness of the
  Auslander–Bridger sequence.
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
  {p : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}

/-- A functional on `P₀` vanishing on the image of `p` factors through the cokernel `π`. -/
private lemma exists_comp_eq_of_comp_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) (ψ : Module.Dual A P₀) (hψ : ψ ∘ₗ p = 0) :
    ∃ φ : Module.Dual A M, φ ∘ₗ π = ψ := by
  refine ⟨(LinearMap.range p).liftQ ψ (by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hψ, LinearMap.zero_apply]) ∘ₗ
      (hexact.linearEquivOfSurjective hπ).symm.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  simp

variable [Module.Finite A P₀] [Module.Projective A P₀]

variable (p π) in
/-- The additive map `Hom(K, A) ⟶ M`, where `K` is the image of the dual `p* : P₀* ⟶ P₁*`, sending
`g` to the image in `M` of the element of `P₀ ≅ P₀**` representing `ψ ↦ g (ψ ∘ p)`. -/
private noncomputable def rangeDualToModule :
    (LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) →+ M where
  toFun g := π ((opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict))
  map_zero' := by simp
  map_add' g g' := by simp [LinearMap.add_comp]

/-- The element of `P₀` underlying `rangeDualToModule` evaluates as `ψ ↦ g (ψ ∘ p)`. -/
private lemma apply_opDualEvalEquiv_symm_comp_rangeRestrict
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) (ψ : Module.Dual A P₀) :
    ψ ((opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict)) =
      g ⟨(p.lcomp Aᵐᵒᵖ A) ψ, LinearMap.mem_range_self _ ψ⟩ :=
  apply_opDualEvalEquiv_symm A P₀ _ ψ

variable [Module.Finite A P₁] [Module.Projective A P₁]

/-- `rangeDualToModule` kills exactly the functionals on `K` that extend to `P₁*`. -/
private lemma rangeDualToModule_eq_zero_iff (hexact : Function.Exact p π)
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    rangeDualToModule p π g = 0 ↔
      ∃ h : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] A, h ∘ₗ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype = g := by
  set x := (opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict) with hxdef
  have hx (ψ : Module.Dual A P₀) : ψ x = g ⟨(p.lcomp Aᵐᵒᵖ A) ψ, LinearMap.mem_range_self _ ψ⟩ :=
    apply_opDualEvalEquiv_symm_comp_rangeRestrict g ψ
  change π x = 0 ↔ _
  refine ⟨fun h0 ↦ ?_, fun ⟨h, hh⟩ ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (hexact x).1 h0
    refine ⟨opDualEval A P₁ y, LinearMap.ext fun ⟨k, ψ, hk⟩ ↦ ?_⟩
    subst hk
    rw [LinearMap.comp_apply, Submodule.subtype_apply, opDualEval_apply, LinearMap.lcomp_apply, hy,
      hx]
  · have hy : x = p ((opDualEvalEquiv A P₁).symm h) :=
      (opDualEval_bijective A P₀).1 (LinearMap.ext fun ψ ↦ by
        rw [opDualEval_apply, opDualEval_apply, hx, ← hh, LinearMap.comp_apply,
          Submodule.subtype_apply, ← apply_opDualEvalEquiv_symm A P₁ h, LinearMap.lcomp_apply])
    rw [hy, hexact.apply_apply_eq_zero]

omit [Module.Finite A P₁] [Module.Projective A P₁] in
/-- The image of `rangeDualToModule` is the kernel of evaluation `M ⟶ M**`. -/
private lemma opDualEval_eq_zero_iff (hexact : Function.Exact p π) (hπ : Function.Surjective π)
    (m : M) : opDualEval A M m = 0 ↔ ∃ g, rangeDualToModule p π g = m := by
  refine ⟨fun hm ↦ ?_, ?_⟩
  · -- The functional `ψ ∘ p ↦ ψ x` on `K` is well defined when `π x` evaluates to zero.
    obtain ⟨x, rfl⟩ := hπ m
    have hker : LinearMap.ker (p.lcomp Aᵐᵒᵖ A) ≤ LinearMap.ker (opDualEval A P₀ x) := by
      intro ψ hψ
      obtain ⟨φ, rfl⟩ := exists_comp_eq_of_comp_eq_zero hexact hπ ψ hψ
      have := LinearMap.congr_fun hm φ
      rw [opDualEval_apply, LinearMap.zero_apply] at this
      rw [LinearMap.mem_ker, opDualEval_apply, LinearMap.comp_apply, this]
    let g := (LinearMap.ker (p.lcomp Aᵐᵒᵖ A)).liftQ _ hker ∘ₗ
      (p.lcomp Aᵐᵒᵖ A).quotKerEquivRange.symm.toLinearMap
    refine ⟨g, congrArg π ((opDualEval_bijective A P₀).1 (LinearMap.ext fun ψ ↦ ?_))⟩
    rw [opDualEval_apply, opDualEval_apply, apply_opDualEvalEquiv_symm_comp_rangeRestrict]
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
      opDualEval_apply]
  · rintro ⟨g, rfl⟩
    refine LinearMap.ext fun φ ↦ ?_
    rw [opDualEval_apply, LinearMap.zero_apply]
    change φ (π ((opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict))) = 0
    rw [← LinearMap.comp_apply φ π, apply_opDualEvalEquiv_symm_comp_rangeRestrict]
    convert g.map_zero
    ext y
    simp [hexact.apply_apply_eq_zero]

omit [Module.Finite A P₁] [Module.Projective A P₁] in
/-- A functional on `M*` extends along `π* : M* ⟶ P₀*` exactly when it is an evaluation. -/
private lemma exists_comp_lcomp_eq_iff (hπ : Function.Surjective π)
    (g : Module.Dual A M →ₗ[Aᵐᵒᵖ] A) :
    (∃ h : Module.Dual A P₀ →ₗ[Aᵐᵒᵖ] A, h ∘ₗ π.lcomp Aᵐᵒᵖ A = g) ↔
      ∃ m, opDualEval A M m = g := by
  refine ⟨fun ⟨h, hh⟩ ↦ ⟨π ((opDualEvalEquiv A P₀).symm h), ?_⟩, fun ⟨m, hm⟩ ↦ ?_⟩
  · refine hh ▸ LinearMap.ext fun φ ↦ ?_
    rw [opDualEval_apply, LinearMap.comp_apply, ← apply_opDualEvalEquiv_symm A P₀ h,
      LinearMap.lcomp_apply]
  · obtain ⟨x, rfl⟩ := hπ m
    exact ⟨opDualEval A P₀ x, hm ▸ LinearMap.ext fun φ ↦ by
      simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, opDualEval_apply]⟩

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

variable (p) in
/-- The connecting map `Hom(K, A) ⟶ Ext¹(Tr M, A)` of `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`. -/
private noncomputable def transposeConnecting :
    (LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) →+
      Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1 where
  toFun g := (transposeShortComplex_shortExact (p := p)).extClass.comp
    (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1)
  map_zero' := by simp [Ext.mk₀_zero]
  map_add' g g' := by simp [ModuleCat.ofHom_add, Ext.mk₀_add, Ext.comp_add]

omit [Module.Finite A P₀] [Module.Projective A P₀] in
variable (p) in
private lemma transposeConnecting_surjective :
    Function.Surjective (transposeConnecting.{w} p) := fun e ↦ by
  obtain ⟨g, rfl⟩ := (transposeShortComplex_shortExact (p := p)).exists_extClass_comp_mk₀_eq e
  exact ⟨g.hom, rfl⟩

omit [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁]
  [Module.Projective A P₁] in
private lemma transposeConnecting_eq_zero_iff
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    transposeConnecting.{w} p g = 0 ↔
      ∃ h : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] A, h ∘ₗ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype = g := by
  refine ((transposeShortComplex_shortExact (p := p)).extClass_comp_mk₀_eq_zero_iff _).trans
    ⟨fun ⟨h, hh⟩ ↦ ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩,
      fun ⟨h, hh⟩ ↦ ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩⟩

variable (p π) in
/-- The first map `Ext¹(Tr M, A) ⟶ M` of the **Auslander–Bridger sequence**
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`. A class `extClass ∘ g`, with
`g : K ⟶ A` defined on the image `K` of `p* : P₀* ⟶ P₁*`, goes to the image in `M` of the element
of `P₀ ≅ P₀**` representing `ψ ↦ g (ψ ∘ p)`. -/
noncomputable def AuslanderReitenTranspose.extOneToModule (hexact : Function.Exact p π) :
    Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1 →+ M :=
  (QuotientAddGroup.lift (transposeConnecting.{w} p).ker (rangeDualToModule p π) fun g hg ↦
    (rangeDualToModule_eq_zero_iff hexact g).2 ((transposeConnecting_eq_zero_iff g).1 hg)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (transposeConnecting_surjective p)).symm.toAddMonoidHom

private lemma extOneToModule_transposeConnecting (hexact : Function.Exact p π)
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    AuslanderReitenTranspose.extOneToModule p π hexact (transposeConnecting.{w} p g) =
      rangeDualToModule p π g := by
  simp only [AuslanderReitenTranspose.extOneToModule, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [show (QuotientAddGroup.quotientKerEquivOfSurjective _ (transposeConnecting_surjective p)).symm
    (transposeConnecting.{w} p g) = (g : _ ⧸ (transposeConnecting.{w} p).ker) from
    AddEquiv.symm_apply_eq _ |>.2 rfl]
  rfl

/-- The first map of the Auslander–Bridger sequence is injective. -/
theorem AuslanderReitenTranspose.injective_extOneToModule (hexact : Function.Exact p π) :
    Function.Injective (extOneToModule.{w} p π hexact) := by
  refine (injective_iff_map_eq_zero _).2 fun e he ↦ ?_
  obtain ⟨g, rfl⟩ := transposeConnecting_surjective.{w} p e
  rw [extOneToModule_transposeConnecting, rangeDualToModule_eq_zero_iff hexact] at he
  exact (transposeConnecting_eq_zero_iff g).2 he

/-- **Exactness of the Auslander–Bridger sequence at `M`**: the kernel of evaluation `M ⟶ M**` is
the image of `Ext¹(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_extOneToModule_opDualEval (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Exact (extOneToModule.{w} p π hexact) (opDualEval A M) := fun m ↦ by
  rw [opDualEval_eq_zero_iff hexact hπ]
  refine ⟨fun ⟨g, hg⟩ ↦
    ⟨transposeConnecting.{w} p g, by rw [extOneToModule_transposeConnecting, hg]⟩,
    fun ⟨e, he⟩ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := transposeConnecting_surjective.{w} p e
  exact ⟨g, by rw [← he, extOneToModule_transposeConnecting]⟩

variable (p π) in
/-- The last map `M** ⟶ Ext²(Tr M, A)` of the **Auslander–Bridger sequence**
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`: the composite of the connecting maps of
`0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`. -/
noncomputable def AuslanderReitenTranspose.doubleDualToExtTwo (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    (Module.Dual A M →ₗ[Aᵐᵒᵖ] A) →+
      Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2 where
  toFun g := (transposeShortComplex_shortExact (p := p)).extClass.comp
    ((dualShortComplex_shortExact hexact hπ).extClass.comp (Ext.mk₀ (ModuleCat.ofHom g))
      (add_zero 1)) rfl
  map_zero' := by simp [Ext.mk₀_zero]
  map_add' g g' := by simp [ModuleCat.ofHom_add, Ext.mk₀_add, Ext.comp_add]

/-- The last map of the Auslander–Bridger sequence is surjective. -/
theorem AuslanderReitenTranspose.surjective_doubleDualToExtTwo (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Surjective (doubleDualToExtTwo.{w} p π hexact hπ) := fun e ↦ by
  obtain ⟨x, rfl⟩ := ((transposeShortComplex_shortExact (p := p)).bijective_precomp_extClass
    (Y := ModuleCat.of Aᵐᵒᵖ A) 0).2 e
  obtain ⟨g, rfl⟩ := (dualShortComplex_shortExact hexact hπ).exists_extClass_comp_mk₀_eq x
  exact ⟨g.hom, rfl⟩

/-- **Exactness of the Auslander–Bridger sequence at `M**`**: the image of evaluation `M ⟶ M**` is
the kernel of the map to `Ext²(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo
    (hexact : Function.Exact p π) (hπ : Function.Surjective π) :
    Function.Exact (opDualEval A M) (doubleDualToExtTwo.{w} p π hexact hπ) := fun g ↦ by
  rw [Set.mem_range, ← exists_comp_lcomp_eq_iff hπ]
  have hinj := ((transposeShortComplex_shortExact (p := p)).bijective_precomp_extClass
    (Y := ModuleCat.of Aᵐᵒᵖ A) 0).1
  refine (hinj.eq_iff' (map_zero _)).trans
    (((dualShortComplex_shortExact hexact hπ).extClass_comp_mk₀_eq_zero_iff _).trans
      ⟨fun ⟨h, hh⟩ ↦ ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩,
        fun ⟨h, hh⟩ ↦ ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩⟩)

/-- **Torsionless modules** (Auslander–Bridger): for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely
generated projective modules, evaluation `M ⟶ M**` is injective if and only if
`Ext¹(Tr M, A) = 0`, where `Tr M` is the transpose of the presentation. -/
theorem opDualEval_injective_iff_ext_one_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Injective (opDualEval A M) ↔
      ∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1,
        e = 0 := by
  have hα := AuslanderReitenTranspose.injective_extOneToModule.{w} hexact
  have hex := AuslanderReitenTranspose.exact_extOneToModule_opDualEval.{w} hexact hπ
  refine ⟨fun hev e ↦ hα ?_, fun h ↦ (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_⟩
  · rw [map_zero]
    exact hev ((hex _).2 ⟨e, rfl⟩ |>.trans (map_zero _).symm)
  · obtain ⟨e, rfl⟩ := (hex m).1 hm
    rw [h e, map_zero]

/-- **Surjectivity of evaluation** (Auslander–Bridger): for a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by
finitely generated projective modules, evaluation `M ⟶ M**` is surjective if and only if
`Ext²(Tr M, A) = 0`. -/
theorem opDualEval_surjective_iff_ext_two_eq_zero (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Surjective (opDualEval A M) ↔
      ∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2,
        e = 0 := by
  have hβ := AuslanderReitenTranspose.surjective_doubleDualToExtTwo.{w} hexact hπ
  have hex := AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo.{w} hexact hπ
  refine ⟨fun hev e ↦ ?_, fun h g ↦ (hex g).1 (h _)⟩
  obtain ⟨g, rfl⟩ := hβ e
  obtain ⟨m, rfl⟩ := hev g
  exact (hex _).2 ⟨m, rfl⟩

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
