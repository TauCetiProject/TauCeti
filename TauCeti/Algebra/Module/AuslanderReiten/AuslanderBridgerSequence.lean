/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Ext.Presentation
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
  have hker : LinearMap.ker π ≤ LinearMap.ker ψ := by
    rw [hexact.linearMap_ker_eq]
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun hψ y
  exact ⟨π.liftOfSurjective hπ ⟨ψ, hker⟩,
    LinearMap.ext fun x ↦ (LinearMap.comp_apply _ _ _).trans
      (LinearMap.equivOfSurjective_apply hπ hker)⟩

variable [Module.Finite A P₀] [Module.Projective A P₀]

variable (p π) in
/-- The additive map `Hom(K, A) ⟶ M`, where `K` is the image of the dual `p* : P₀* ⟶ P₁*`, sending
`g` to the image in `M` of the element of `P₀ ≅ P₀**` representing `ψ ↦ g (ψ ∘ p)`. -/
private noncomputable def rangeDualToModule :
    (LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) →+ M where
  toFun g := π ((opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict))
  map_zero' := by simp
  map_add' g g' := by simp [LinearMap.add_comp]

variable [Module.Finite A P₁] [Module.Projective A P₁]

/-- `rangeDualToModule` kills exactly the functionals on `K` that extend to `P₁*`. -/
private lemma rangeDualToModule_eq_zero_iff (hexact : Function.Exact p π)
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    rangeDualToModule p π g = 0 ↔
      ∃ h : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] A, h ∘ₗ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype = g := by
  set x := (opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict) with hxdef
  change π x = 0 ↔ _
  refine ⟨fun h0 ↦ ?_, fun ⟨h, hh⟩ ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (hexact x).1 h0
    refine ⟨opDualEval A P₁ y, LinearMap.ext fun ⟨k, ψ, hk⟩ ↦ ?_⟩
    subst hk
    rw [LinearMap.comp_apply, Submodule.subtype_apply, opDualEval_apply, LinearMap.lcomp_apply, hy,
      hxdef, apply_opDualEvalEquiv_symm]
    rfl
  · have hy : x = p ((opDualEvalEquiv A P₁).symm h) :=
      (opDualEval_bijective A P₀).1 (LinearMap.ext fun ψ ↦ by
        rw [opDualEval_apply, opDualEval_apply, hxdef, apply_opDualEvalEquiv_symm, ← hh,
          LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          ← apply_opDualEvalEquiv_symm A P₁ h]
        rfl)
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
    rw [opDualEval_apply, opDualEval_apply, apply_opDualEvalEquiv_symm, LinearMap.comp_apply,
      show (p.lcomp Aᵐᵒᵖ A).rangeRestrict ψ =
        ⟨(p.lcomp Aᵐᵒᵖ A) ψ, LinearMap.mem_range_self _ ψ⟩ from rfl]
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
      opDualEval_apply]
  · rintro ⟨g, rfl⟩
    refine LinearMap.ext fun φ ↦ ?_
    rw [opDualEval_apply, LinearMap.zero_apply]
    change φ (π ((opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict))) = 0
    rw [← LinearMap.comp_apply φ π, apply_opDualEvalEquiv_symm, LinearMap.comp_apply]
    convert g.map_zero
    ext y
    simp [hexact.apply_apply_eq_zero]

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

-- `homBoundary ℤ` uses the `ℤ`-module structure of `Ext` coming from `Linear ℤ`, which is not
-- definitionally the default `AddCommGroup.toIntModule`; prefer it in this section.
attribute [local instance high] CategoryTheory.Abelian.Ext.instModule

variable (p π) in
/-- The first map `Ext¹(Tr M, A) ⟶ M` of the **Auslander–Bridger sequence**
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`. A class in `Ext¹(Tr M, A)` is represented,
through `TauCeti.homCokernelEquivExt`, by a functional `g : K ⟶ A` on the image `K` of
`p* : P₀* ⟶ P₁*`, and goes to the image in `M` of the element of `P₀ ≅ P₀**` representing
`ψ ↦ g (ψ ∘ p)`. -/
noncomputable def AuslanderReitenTranspose.extOneToModule (hexact : Function.Exact p π) :
    Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 1 →+ M :=
  ((Submodule.liftQ _ (AddMonoidHom.mk'
      (fun g : ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)) ⟶ ModuleCat.of Aᵐᵒᵖ A ↦
        rangeDualToModule p π g.hom) fun g g' ↦ by
        rw [ModuleCat.hom_add, map_add]).toIntLinearMap
    (by
      rintro _ ⟨h, rfl⟩
      exact (rangeDualToModule_eq_zero_iff hexact _).2 ⟨h.hom, rfl⟩)) ∘ₗ
    (homCokernelEquivExt ℤ (transposeShortComplex_shortExact (p := p))
      (ModuleCat.of Aᵐᵒᵖ A)).symm.toLinearMap).toAddMonoidHom

/-- The first map of the Auslander–Bridger sequence on the connecting image of a functional. -/
private lemma extOneToModule_homBoundary (hexact : Function.Exact p π)
    (g : ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)) ⟶ ModuleCat.of Aᵐᵒᵖ A) :
    AuslanderReitenTranspose.extOneToModule.{w} p π hexact
        (homBoundary ℤ (transposeShortComplex_shortExact (p := p)) _ g) =
      rangeDualToModule p π g.hom := by
  rw [homBoundary_apply]
  simp only [AuslanderReitenTranspose.extOneToModule, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [homCokernelEquivExt_symm_comp_mk₀]
  rfl

/-- The first map of the Auslander–Bridger sequence is injective. -/
theorem AuslanderReitenTranspose.injective_extOneToModule (hexact : Function.Exact p π) :
    Function.Injective (extOneToModule.{w} p π hexact) := by
  refine (injective_iff_map_eq_zero _).2 fun e he ↦ ?_
  obtain ⟨g, rfl⟩ := homBoundary_surjective ℤ (transposeShortComplex_shortExact (p := p)) _ e
  rw [extOneToModule_homBoundary, rangeDualToModule_eq_zero_iff hexact] at he
  obtain ⟨h, hh⟩ := he
  rw [← LinearMap.mem_ker, ker_homBoundary]
  exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

/-- **Exactness of the Auslander–Bridger sequence at `M`**: the kernel of evaluation `M ⟶ M**` is
the image of `Ext¹(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_extOneToModule_opDualEval (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Exact (extOneToModule.{w} p π hexact) (opDualEval A M) := fun m ↦ by
  rw [opDualEval_eq_zero_iff hexact hπ]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨homBoundary ℤ (transposeShortComplex_shortExact (p := p)) _
    (ModuleCat.ofHom g), by rw [extOneToModule_homBoundary, ← hg]; rfl⟩, fun ⟨e, he⟩ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := homBoundary_surjective ℤ (transposeShortComplex_shortExact (p := p)) _ e
  exact ⟨g.hom, by rw [← he, extOneToModule_homBoundary]⟩

variable (p π) in
/-- The last map `M** ⟶ Ext²(Tr M, A)` of the **Auslander–Bridger sequence**
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`: the composite of the connecting maps of
`0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`. -/
noncomputable def AuslanderReitenTranspose.doubleDualToExtTwo (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    (Module.Dual A M →ₗ[Aᵐᵒᵖ] A) →+
      Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2 :=
  ((Ext.precomp (transposeShortComplex_shortExact (p := p)).extClass (ModuleCat.of Aᵐᵒᵖ A)
    (show 1 + (0 + 1) = 0 + 2 by lia)).comp
    (homBoundary ℤ (dualShortComplex_shortExact hexact hπ)
      (ModuleCat.of Aᵐᵒᵖ A)).toAddMonoidHom).comp
    (AddMonoidHom.mk' (fun g ↦ (ModuleCat.ofHom g : ModuleCat.of Aᵐᵒᵖ (Module.Dual A M) ⟶
      ModuleCat.of Aᵐᵒᵖ A)) fun _ _ ↦ rfl)

omit [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁] [Module.Projective A P₁] in
/-- The last map of the Auslander–Bridger sequence is the composite of the two connecting maps. -/
private lemma doubleDualToExtTwo_apply (hexact : Function.Exact p π) (hπ : Function.Surjective π)
    (g : Module.Dual A M →ₗ[Aᵐᵒᵖ] A) :
    AuslanderReitenTranspose.doubleDualToExtTwo.{w} p π hexact hπ g =
      Ext.precomp (transposeShortComplex_shortExact (p := p)).extClass (ModuleCat.of Aᵐᵒᵖ A)
        (show 1 + (0 + 1) = 0 + 2 by lia)
        (homBoundary ℤ (dualShortComplex_shortExact hexact hπ) _ (ModuleCat.ofHom g)) :=
  rfl

/-- The last map of the Auslander–Bridger sequence is surjective. -/
theorem AuslanderReitenTranspose.surjective_doubleDualToExtTwo (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Surjective (doubleDualToExtTwo.{w} p π hexact hπ) := fun e ↦ by
  obtain ⟨x, rfl⟩ :=
    (bijective_precomp_extClass (transposeShortComplex_shortExact (p := p)) _ 0).2 e
  obtain ⟨g, rfl⟩ := homBoundary_surjective ℤ (dualShortComplex_shortExact hexact hπ) _ x
  exact ⟨g.hom, doubleDualToExtTwo_apply hexact hπ _⟩

/-- **Exactness of the Auslander–Bridger sequence at `M**`**: the image of evaluation `M ⟶ M**` is
the kernel of the map to `Ext²(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo
    (hexact : Function.Exact p π) (hπ : Function.Surjective π) :
    Function.Exact (opDualEval A M) (doubleDualToExtTwo.{w} p π hexact hπ) := fun g ↦ by
  -- The image of evaluation is the image of `(π*)* : P₀** ⟶ M**`.
  have hrange := map_range_opDualEval A π
  rw [LinearMap.range_eq_top.2 hπ, Submodule.map_top] at hrange
  rw [show g ∈ Set.range (opDualEval A M) ↔ g ∈ LinearMap.range (opDualEval A M) from Iff.rfl,
    hrange, doubleDualToExtTwo_apply, ((bijective_precomp_extClass
      (transposeShortComplex_shortExact (p := p)) _ 0).1.eq_iff' (map_zero _)),
    ← LinearMap.mem_ker, ker_homBoundary]
  exact ⟨fun ⟨h, hh⟩ ↦ ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩,
    fun ⟨h, hh⟩ ↦ ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩⟩

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
