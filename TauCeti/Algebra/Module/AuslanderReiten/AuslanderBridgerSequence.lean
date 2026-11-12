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
public import TauCeti.LinearAlgebra.Exact

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
* `TauCeti.AuslanderReitenTranspose.shortComplex` and
  `TauCeti.AuslanderReitenTranspose.dualShortComplex`: the short exact sequences
  `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` and `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0`.

## Main results

* `TauCeti.AuslanderReitenTranspose.extOneToModule_homBoundary` and
  `TauCeti.AuslanderReitenTranspose.doubleDualToExtTwo_apply`: formulas for the two outer maps.
* `TauCeti.AuslanderReitenTranspose.extOneToModule_injective`,
  `TauCeti.AuslanderReitenTranspose.exact_extOneToModule_opDualEval`,
  `TauCeti.AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo` and
  `TauCeti.AuslanderReitenTranspose.doubleDualToExtTwo_surjective`: exactness of the
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

variable [Module.Finite A P₀] [Module.Projective A P₀]

omit [Module.Finite A P₀] [Module.Projective A P₀] in
/-- The image of a functional under `p* : P₀* ⟶ P₁*`, viewed in the image `K` of `p*`. -/
private lemma coe_rangeRestrict_lcomp (ψ : Module.Dual A P₀) :
    ((p.lcomp Aᵐᵒᵖ A).rangeRestrict ψ : Module.Dual A P₁) = ψ ∘ₗ p := by
  rw [← Submodule.subtype_apply, ← LinearMap.comp_apply, LinearMap.subtype_comp_rangeRestrict,
    LinearMap.lcomp_apply']

variable (p) in
/-- The element of `P₀ ≅ P₀**` representing the functional `ψ ↦ g (ψ ∘ p)` on `P₀*`, for a
functional `g` on the image `K` of `p* : P₀* ⟶ P₁*`. -/
private noncomputable def rangeDualPreimage (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    P₀ :=
  (opDualEvalEquiv A P₀).symm (g ∘ₗ (p.lcomp Aᵐᵒᵖ A).rangeRestrict)

/-- Evaluating a functional at `rangeDualPreimage p g` computes `g (ψ ∘ p)`. -/
private lemma apply_rangeDualPreimage (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A)
    (ψ : Module.Dual A P₀) :
    ψ (rangeDualPreimage p g) = g ((p.lcomp Aᵐᵒᵖ A).rangeRestrict ψ) := by
  rw [rangeDualPreimage, apply_opDualEvalEquiv_symm, LinearMap.comp_apply]

/-- `rangeDualPreimage p g` is the only element on which every `ψ` evaluates to `g (ψ ∘ p)`. -/
private lemma eq_rangeDualPreimage {g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A} {x : P₀}
    (hx : ∀ ψ : Module.Dual A P₀, ψ x = g ((p.lcomp Aᵐᵒᵖ A).rangeRestrict ψ)) :
    x = rangeDualPreimage p g :=
  (opDualEval_bijective A P₀).1 (LinearMap.ext fun ψ ↦ by
    simp [hx, apply_rangeDualPreimage])

variable (p π) in
/-- The additive map `Hom(K, A) ⟶ M`, where `K` is the image of the dual `p* : P₀* ⟶ P₁*`, sending
`g` to the image in `M` of the element of `P₀ ≅ P₀**` representing `ψ ↦ g (ψ ∘ p)`. -/
private noncomputable def rangeDualToModule :
    (LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) →+ M where
  toFun g := π (rangeDualPreimage p g)
  map_zero' := by simp [rangeDualPreimage]
  map_add' g g' := by simp [rangeDualPreimage, LinearMap.add_comp]

/-- The defining formula of `rangeDualToModule`, as an equation for rewriting. -/
private lemma rangeDualToModule_apply (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    rangeDualToModule p π g = π (rangeDualPreimage p g) :=
  rfl

variable [Module.Finite A P₁] [Module.Projective A P₁]

/-- `rangeDualToModule` kills exactly the functionals on `K` that extend to `P₁*`. -/
private lemma rangeDualToModule_eq_zero_iff (hexact : Function.Exact p π)
    (g : LinearMap.range (p.lcomp Aᵐᵒᵖ A) →ₗ[Aᵐᵒᵖ] A) :
    rangeDualToModule p π g = 0 ↔
      ∃ h : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] A, h ∘ₗ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype = g := by
  rw [rangeDualToModule_apply]
  refine ⟨fun h0 ↦ ?_, fun ⟨h, hh⟩ ↦ ?_⟩
  · -- `rangeDualPreimage p g = p y`, and `g` extends to the evaluation at `y`.
    obtain ⟨y, hy⟩ := (hexact _).1 h0
    refine ⟨opDualEval A P₁ y, LinearMap.ext fun k ↦ ?_⟩
    obtain ⟨ψ, rfl⟩ := (p.lcomp Aᵐᵒᵖ A).surjective_rangeRestrict k
    simp [hy, apply_rangeDualPreimage]
  · -- An extension `h` of `g` is the evaluation at some `y : P₁`, so that `rangeDualPreimage p g`
    -- is `p y`, which `π` kills.
    rw [← eq_rangeDualPreimage (x := p ((opDualEvalEquiv A P₁).symm h)) fun ψ ↦ ?_,
      hexact.apply_apply_eq_zero]
    rw [← hh, LinearMap.comp_apply, Submodule.subtype_apply, coe_rangeRestrict_lcomp,
      ← LinearMap.comp_apply ψ p, apply_opDualEvalEquiv_symm]

omit [Module.Finite A P₁] [Module.Projective A P₁] in
/-- The image of `rangeDualToModule` is the kernel of evaluation `M ⟶ M**`. -/
private lemma opDualEval_eq_zero_iff (hexact : Function.Exact p π) (hπ : Function.Surjective π)
    (m : M) : opDualEval A M m = 0 ↔ ∃ g, rangeDualToModule p π g = m := by
  refine ⟨fun hm ↦ ?_, ?_⟩
  · -- The functional `ψ ∘ p ↦ ψ x` on `K` is well defined when `π x` evaluates to zero.
    obtain ⟨x, rfl⟩ := hπ m
    have hker : LinearMap.ker (p.lcomp Aᵐᵒᵖ A) ≤ LinearMap.ker (opDualEval A P₀ x) := by
      intro ψ hψ
      obtain ⟨φ, rfl⟩ := ((hexact.lcomp_of_surjective (T := Aᵐᵒᵖ) A hπ) ψ).1 hψ
      simpa [LinearMap.lcomp_apply'] using LinearMap.congr_fun hm φ
    rw [← LinearMap.ker_rangeRestrict] at hker
    -- The implicit arguments are given to avoid a slow unification between the two semiring
    -- structures on `Aᵐᵒᵖ`.
    let g := LinearMap.liftOfSurjective (R := Aᵐᵒᵖ) (M := Module.Dual A P₀)
      (M₂ := LinearMap.range (p.lcomp Aᵐᵒᵖ A)) (M₃ := A)
      (LinearMap.surjective_rangeRestrict (p.lcomp Aᵐᵒᵖ A)) ⟨opDualEval A P₀ x, hker⟩
    refine ⟨g, ?_⟩
    rw [rangeDualToModule_apply, ← eq_rangeDualPreimage (g := g) (x := x) fun ψ ↦ ?_]
    rw [LinearMap.equivOfSurjective_apply, opDualEval_apply]
  · rintro ⟨g, rfl⟩
    refine LinearMap.ext fun φ ↦ ?_
    -- `φ ∘ π` vanishes on the image of `p`, so its image in `K` is zero.
    have hφ : (p.lcomp Aᵐᵒᵖ A).rangeRestrict (φ ∘ₗ π) = 0 := by
      rw [← LinearMap.mem_ker, LinearMap.ker_rangeRestrict, LinearMap.mem_ker,
        LinearMap.lcomp_apply', LinearMap.comp_assoc, hexact.linearMap_comp_eq_zero,
        LinearMap.comp_zero]
    simpa [rangeDualToModule_apply, hφ] using apply_rangeDualPreimage g (φ ∘ₗ π)

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
noncomputable abbrev AuslanderReitenTranspose.shortComplex : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
  ModuleCat.shortComplexOfCompEqZero (R := Aᵐᵒᵖ) (M := LinearMap.range (p.lcomp Aᵐᵒᵖ A))
    (N := Module.Dual A P₁) (L := AuslanderReitenTranspose p)
    (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype (AuslanderReitenTranspose.mk p)
    (LinearMap.ext fun ⟨_, hx⟩ ↦ (AuslanderReitenTranspose.mk_eq_zero_iff p _).2 hx)

variable (p) in
/-- The sequence `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` is short exact. -/
theorem AuslanderReitenTranspose.shortComplex_shortExact : (shortComplex p).ShortExact :=
  ModuleCat.shortComplex_shortExact (shortComplex p)
    ((LinearMap.exact_iff (f := (LinearMap.range (p.lcomp Aᵐᵒᵖ A)).subtype) (g := mk p)).2
      (by rw [ker_mk, Submodule.range_subtype])) Subtype.val_injective
    (mk_surjective p)

variable (p π) in
/-- The short exact sequence `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` of right modules dual to a presentation,
where `K` is the image of the dual `p* : P₀* ⟶ P₁*`. -/
noncomputable abbrev AuslanderReitenTranspose.dualShortComplex (h : π ∘ₗ p = 0) :
    ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
  ModuleCat.shortComplexOfCompEqZero (R := Aᵐᵒᵖ) (M := Module.Dual A M) (N := Module.Dual A P₀)
    (L := LinearMap.range (p.lcomp Aᵐᵒᵖ A)) (π.lcomp Aᵐᵒᵖ A) (p.lcomp Aᵐᵒᵖ A).rangeRestrict
    (LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.ext fun x ↦ by
      simp [← LinearMap.comp_apply π p, h]))

/-- The sequence `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` is short exact. -/
theorem AuslanderReitenTranspose.dualShortComplex_shortExact (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    (dualShortComplex p π hexact.linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact (dualShortComplex p π hexact.linearMap_comp_eq_zero)
    ((LinearMap.exact_iff (f := π.lcomp Aᵐᵒᵖ A) (g := (p.lcomp Aᵐᵒᵖ A).rangeRestrict)).2 (by
      rw [LinearMap.ker_rangeRestrict]
      exact (hexact.lcomp_of_surjective (T := Aᵐᵒᵖ) A hπ).linearMap_ker_eq))
    (LinearMap.lcomp_injective_of_surjective π hπ) (LinearMap.surjective_rangeRestrict _)

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
  ((Submodule.liftQ _ ((rangeDualToModule p π).comp (ModuleCat.homAddEquiv
      (M := ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)))
      (N := ModuleCat.of Aᵐᵒᵖ A)).toAddMonoidHom).toIntLinearMap
    (by
      rintro _ ⟨h, rfl⟩
      exact (rangeDualToModule_eq_zero_iff hexact _).2 ⟨h.hom, rfl⟩)) ∘ₗ
    (homCokernelEquivExt ℤ (AuslanderReitenTranspose.shortComplex_shortExact p)
      (ModuleCat.of Aᵐᵒᵖ A)).symm.toLinearMap).toAddMonoidHom

/-- The first map of the Auslander–Bridger sequence on the connecting image of a functional. -/
private lemma extOneToModule_homBoundary' (hexact : Function.Exact p π)
    (g : ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)) ⟶ ModuleCat.of Aᵐᵒᵖ A) :
    AuslanderReitenTranspose.extOneToModule.{w} p π hexact
        (homBoundary ℤ (AuslanderReitenTranspose.shortComplex_shortExact p) _ g) =
      rangeDualToModule p π g.hom := by
  rw [homBoundary_apply]
  simp only [AuslanderReitenTranspose.extOneToModule, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [homCokernelEquivExt_symm_comp_mk₀, Submodule.liftQ_apply, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, ModuleCat.homAddEquiv_apply]

/-- **Computing the first map of the Auslander–Bridger sequence**: the connecting image in
`Ext¹(Tr M, A)` of a functional `g : K ⟶ A` goes to `π x`, for the element `x : P₀` with
`ψ x = g (ψ ∘ p)` for every `ψ : P₀*`. Every class in `Ext¹(Tr M, A)` is such a connecting image
(`TauCeti.homBoundary_surjective`). -/
theorem AuslanderReitenTranspose.extOneToModule_homBoundary (hexact : Function.Exact p π)
    (g : ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)) ⟶ ModuleCat.of Aᵐᵒᵖ A) (x : P₀)
    (hx : ∀ ψ : Module.Dual A P₀, ψ x = g.hom ((p.lcomp Aᵐᵒᵖ A).rangeRestrict ψ)) :
    extOneToModule.{w} p π hexact (homBoundary ℤ (shortComplex_shortExact p) _ g) = π x := by
  rw [extOneToModule_homBoundary', rangeDualToModule_apply, ← eq_rangeDualPreimage hx]

/-- The first map of the Auslander–Bridger sequence is injective. -/
theorem AuslanderReitenTranspose.extOneToModule_injective (hexact : Function.Exact p π) :
    Function.Injective (extOneToModule.{w} p π hexact) := by
  refine (injective_iff_map_eq_zero _).2 fun e he ↦ ?_
  obtain ⟨g, rfl⟩ :=
    homBoundary_surjective ℤ (AuslanderReitenTranspose.shortComplex_shortExact p) _ e
  rw [extOneToModule_homBoundary', rangeDualToModule_eq_zero_iff hexact] at he
  obtain ⟨h, hh⟩ := he
  rw [← LinearMap.mem_ker, ker_homBoundary]
  exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

/-- **Exactness of the Auslander–Bridger sequence at `M`**: the kernel of evaluation `M ⟶ M**` is
the image of `Ext¹(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_extOneToModule_opDualEval (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Exact (extOneToModule.{w} p π hexact) (opDualEval A M) := fun m ↦ by
  rw [opDualEval_eq_zero_iff hexact hπ]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨homBoundary ℤ (shortComplex_shortExact p) _ (ModuleCat.ofHom g),
    by rw [extOneToModule_homBoundary', ModuleCat.hom_ofHom, hg]⟩, fun ⟨e, he⟩ ↦ ?_⟩
  obtain ⟨g, rfl⟩ :=
    homBoundary_surjective ℤ (AuslanderReitenTranspose.shortComplex_shortExact p) _ e
  exact ⟨g.hom, by rw [← he, extOneToModule_homBoundary']⟩

variable (p π) in
/-- The last map `M** ⟶ Ext²(Tr M, A)` of the **Auslander–Bridger sequence**
`0 ⟶ Ext¹(Tr M, A) ⟶ M ⟶ M** ⟶ Ext²(Tr M, A) ⟶ 0`: the composite of the connecting maps of
`0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0` and `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0`. -/
noncomputable def AuslanderReitenTranspose.doubleDualToExtTwo (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    (Module.Dual A M →ₗ[Aᵐᵒᵖ] A) →+
      Ext.{w} (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) 2 :=
  ((Ext.precomp (AuslanderReitenTranspose.shortComplex_shortExact p).extClass (ModuleCat.of Aᵐᵒᵖ A)
    (by norm_num : 1 + 1 = 2)).comp
    (homBoundary ℤ (AuslanderReitenTranspose.dualShortComplex_shortExact hexact hπ)
      (ModuleCat.of Aᵐᵒᵖ A)).toAddMonoidHom).comp
    (ModuleCat.homAddEquiv (M := ModuleCat.of Aᵐᵒᵖ (Module.Dual A M))
      (N := ModuleCat.of Aᵐᵒᵖ A)).symm.toAddMonoidHom

omit [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁] [Module.Projective A P₁] in
/-- **Computing the last map of the Auslander–Bridger sequence**: it sends `g : M**` to the
composite of the extension class of `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` with the connecting image of `g`
for `0 ⟶ M* ⟶ P₀* ⟶ K ⟶ 0`. -/
theorem AuslanderReitenTranspose.doubleDualToExtTwo_apply (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) (g : Module.Dual A M →ₗ[Aᵐᵒᵖ] A) :
    doubleDualToExtTwo.{w} p π hexact hπ g =
      Ext.precomp (shortComplex_shortExact p).extClass (ModuleCat.of Aᵐᵒᵖ A)
        (by norm_num : 1 + 1 = 2)
        (homBoundary ℤ (dualShortComplex_shortExact hexact hπ) _ (ModuleCat.ofHom g)) :=
  (rfl)

/-- The last map of the Auslander–Bridger sequence is surjective. -/
theorem AuslanderReitenTranspose.doubleDualToExtTwo_surjective (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) :
    Function.Surjective (doubleDualToExtTwo.{w} p π hexact hπ) := fun e ↦ by
  obtain ⟨x, rfl⟩ :=
    (precomp_extClass_bijective (AuslanderReitenTranspose.shortComplex_shortExact p) _ 0).2 e
  obtain ⟨g, rfl⟩ :=
    homBoundary_surjective ℤ (AuslanderReitenTranspose.dualShortComplex_shortExact hexact hπ) _ x
  exact ⟨g.hom, AuslanderReitenTranspose.doubleDualToExtTwo_apply hexact hπ _⟩

/-- **Exactness of the Auslander–Bridger sequence at `M**`**: the image of evaluation `M ⟶ M**` is
the kernel of the map to `Ext²(Tr M, A)`. -/
theorem AuslanderReitenTranspose.exact_opDualEval_doubleDualToExtTwo
    (hexact : Function.Exact p π) (hπ : Function.Surjective π) :
    Function.Exact (opDualEval A M) (doubleDualToExtTwo.{w} p π hexact hπ) := fun g ↦ by
  -- The image of evaluation is the image of `(π*)* : P₀** ⟶ M**`.
  have hrange := map_range_opDualEval A π
  rw [LinearMap.range_eq_top.2 hπ, Submodule.map_top] at hrange
  rw [Set.mem_range, ← LinearMap.mem_range, hrange, doubleDualToExtTwo_apply]
  rw [(precomp_extClass_bijective (shortComplex_shortExact p) _ 0).1.eq_iff' (map_zero _),
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
  have hα := AuslanderReitenTranspose.extOneToModule_injective.{w} hexact
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
  have hβ := AuslanderReitenTranspose.doubleDualToExtTwo_surjective.{w} hexact hπ
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
