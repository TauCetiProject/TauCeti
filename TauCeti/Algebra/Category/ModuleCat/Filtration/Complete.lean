/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.Algebra.Category.ModuleCat.Filtration

/-!
# Complete filtrations of modules by submodules

A filtration `ofSubmodules F hF` of a module `M` by submodules is complete when `M` is the limit
of its quotients `M / F i` (`CategoryTheory.FilteredObject.IsComplete`). This file gives an
element-wise criterion: `M` is complete when only `0` lies in every `F i` and every compatible
family of representatives `y i ∈ M` (with `y i - y j ∈ F j` along each morphism `i ⟶ j`) has a
limit `x`, with `x - y i ∈ F i` for every `i`. For an ideal `J` and a `J`-adically complete
module `M` (Mathlib's `IsAdicComplete`), the decreasing filtration `F^p = J^p • M` (with
`F^p = M` for `p ≤ 0`) satisfies it.

## Main results

* `CategoryTheory.FilteredObject.isComplete_ofSubmodules`: the element-wise criterion.
* `CategoryTheory.FilteredObject.step_adicFiltration`,
  `CategoryTheory.FilteredObject.subobjectModule_step_adicFiltration`: the step `F^p` of the
  `J`-adic filtration is `J ^ p • M`.
* `CategoryTheory.FilteredObject.isExhaustive_adicFiltration`,
  `CategoryTheory.FilteredObject.isSeparated_adicFiltration`: the `J`-adic filtration is
  exhaustive, and separated when `M` is `J`-adically Hausdorff.
* `CategoryTheory.FilteredObject.isComplete_adicFiltration`: the `J`-adic filtration of a
  `J`-adically complete module is complete.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Type*} [Category* I] {F : I → Submodule R M} {hF : ∀ ⦃i j⦄, (i ⟶ j) → F i ≤ F j}

/-- **Element-wise criterion for completeness.** The filtration `ofSubmodules F hF` is complete
when only `0` lies in every `F i`, and every family `y : I → M` that is compatible, with
`y i - y j ∈ F j` for every morphism `i ⟶ j`, has a limit `x`, with `x - y i ∈ F i` for every
`i`. -/
theorem isComplete_ofSubmodules (hsep : ∀ x, (∀ i, x ∈ F i) → x = 0)
    (hex : ∀ y : I → M, (∀ ⦃i j⦄, (i ⟶ j) → y i - y j ∈ F j) → ∃ x, ∀ i, x - y i ∈ F i) :
    (ofSubmodules F hF).IsComplete := by
  have hπ (i : I) (x y : M) := cokernel_π_stepι_ofSubmodules_apply_eq_iff F hF i x y
  have hsurj (i : I) : Function.Surjective (cokernel.π ((ofSubmodules F hF).stepι i)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  -- An element of `M` is determined by its images in all the quotients `M / F_i`.
  have huniq {x x' : M} (h : ∀ i, (cokernel.π ((ofSubmodules F hF).stepι i)).hom x =
      (cokernel.π ((ofSubmodules F hF).stepι i)).hom x') : x = x' :=
    sub_eq_zero.1 (hsep _ fun i ↦ (hπ i x x').1 (h i))
  -- A cone over the quotients sends each element to the image of a unique element of `M`.
  have hlim (s : Cone (ofSubmodules F hF).quotientDiagram) (a : s.pt) :
      ∃ x : M, ∀ i, (cokernel.π ((ofSubmodules F hF).stepι i)).hom x = (s.π.app i).hom a := by
    choose y hy using fun i ↦ hsurj i ((s.π.app i).hom a)
    obtain ⟨x, hx⟩ := hex y fun i j f ↦ by
      have h₁ := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (cokernel_π_quotientDiagram_map (ofSubmodules F hF) f)) (y i)
      have h₂ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (s.w f)) a
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
      exact (hπ j _ _).1 <| h₁.symm.trans <| (congrArg _ (hy i)).trans <| h₂.trans (hy j).symm
    exact ⟨x, fun i ↦ (hπ i x (y i)).2 (hx i) |>.trans (hy i)⟩
  choose g hg using hlim
  -- In `map_add'` and `map_smul'`, the final `rfl` identifies the operations on
  -- `quotientDiagram.obj i` with those on `cokernel (stepι i)`, its definition.
  refine IsComplete.mk
    { lift s := ModuleCat.ofHom
        { toFun := g s
          map_add' a b := huniq fun i ↦ by
            rw [map_add, hg, hg, hg, map_add]
            rfl
          map_smul' r a := huniq fun i ↦ by
            rw [map_smul, hg, hg, map_smul, RingHom.id_apply]
            rfl }
      fac s i := by ext a; exact hg s a i
      uniq s m hm := by
        ext a
        exact huniq fun i ↦ (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hm i)) a).trans
          (hg s a i).symm }

end CategoryTheory.FilteredObject

namespace CategoryTheory.FilteredObject

variable {R : Type u} [CommRing R] (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The `J`-adic decreasing filtration `F^p = J^p • M` of a module `M`, with `F^p = M` for
`p ≤ 0`. -/
noncomputable abbrev adicFiltration : FilteredObject (ModuleCat.{v} R) ℤᵒᵖ :=
  ofSubmodules (fun p : ℤᵒᵖ ↦ J ^ p.unop.toNat • (⊤ : Submodule R M)) fun _ _ f ↦
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Int.toNat_le_toNat (leOfHom f.unop)))

/-- The step `F^p` of the `J`-adic filtration is the subobject of `J ^ p • M` (of `M` for
`p ≤ 0`). -/
theorem step_adicFiltration (p : ℤᵒᵖ) :
    (adicFiltration J M).step p =
      (ModuleCat.subobjectModule (ModuleCat.of R M)).symm (J ^ p.unop.toNat • ⊤) :=
  step_ofSubmodules _ _ p

/-- `ModuleCat.subobjectModule` sends the step `F^p` of the `J`-adic filtration to `J ^ p • M`
(to `M` for `p ≤ 0`). -/
@[simp]
theorem subobjectModule_step_adicFiltration (p : ℤᵒᵖ) :
    ModuleCat.subobjectModule (ModuleCat.of R M) ((adicFiltration J M).step p) =
      J ^ p.unop.toNat • ⊤ :=
  subobjectModule_step_ofSubmodules _ _ p

/-- The steps `F^p` of the `J`-adic filtration with `p ≤ 0` are the whole module. -/
theorem step_adicFiltration_of_nonpos {p : ℤ} (hp : p ≤ 0) :
    (adicFiltration J M).step (op p) = ⊤ := by
  rw [step_adicFiltration, unop_op, Int.toNat_eq_zero.2 hp, pow_zero, Ideal.one_eq_top,
    Submodule.top_smul, map_top]

/-- The `J`-adic filtration is exhaustive: its step `F^0` is the whole module. -/
theorem isExhaustive_adicFiltration : (adicFiltration J M).IsExhaustive :=
  isExhaustive_of_step_eq_top _ (step_adicFiltration_of_nonpos J M le_rfl)

/-- The `J`-adic filtration of a `J`-adically Hausdorff module is separated. -/
theorem isSeparated_adicFiltration [IsHausdorff J M] : (adicFiltration J M).IsSeparated :=
  (isSeparated_ofSubmodules_iff_forall_mem _ _).2 fun x hx ↦
    IsHausdorff.haus (inferInstance : IsHausdorff J M) x fun n ↦ by
      simpa [SModEq.sub_mem] using hx (op (n : ℤ))

/-- **The `J`-adic filtration of a `J`-adically complete module is complete.** -/
theorem isComplete_adicFiltration [IsAdicComplete J M] : (adicFiltration J M).IsComplete := by
  refine isComplete_ofSubmodules
    ((isSeparated_ofSubmodules_iff_forall_mem _ _).1 (isSeparated_adicFiltration J M))
    fun y hy ↦ ?_
  -- The representatives at the natural indices form a Cauchy sequence.
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J M)
    (f := fun n : ℕ ↦ y (op (n : ℤ))) fun {m n} hmn ↦ by
      rw [SModEq.sub_mem, ← neg_mem_iff, neg_sub]
      simpa using hy (homOfLE (Int.ofNat_le.2 hmn)).op
  refine ⟨L, fun p ↦ ?_⟩
  -- Compare `y p` with the representative at the natural index `p.unop.toNat ≥ p.unop`.
  have h₁ := hy (homOfLE (Int.self_le_toNat p.unop)).op
  have h₂ := (SModEq.sub_mem.1 (hL p.unop.toNat))
  simp only [op_unop] at h₁ h₂
  convert Submodule.sub_mem _ h₁ h₂ using 1
  abel

end CategoryTheory.FilteredObject
