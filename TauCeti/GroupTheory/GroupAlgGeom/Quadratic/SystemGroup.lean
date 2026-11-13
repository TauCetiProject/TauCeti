/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.CoefficientFree
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.SurfaceGroup.LowGenus
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import TauCeti.Logic.Equiv.Set

/-!
# The groups of the standard quadratic equations without coefficients

For a system `S` of equations over a group `G`, [IFT] writes `G_S = G[X] ⧸ ncl(S)` for the group
of the system. The standard quadratic equations of types (1) and (3),

`[x₁, y₁] ⋯ [xₙ, yₙ] = 1` and `x₁² ⋯ xₙ² = 1`,

have no coefficients, and their left sides are the defining relators of the closed orientable and
non-orientable surface groups `S⁺(n, 0)` and `S⁻(n, 0)` in the variables. Hence the group of such
an equation is the free product of `G` with the surface group, and with the free group on the
variables of `X` that do not occur in the equation:

`G_S ≃* G ∗ (S^±(n, 0) ∗ F(X ∖ {variables of S}))`.

When every variable of `X` occurs in the equation, this is `G_S ≃* G ∗ S^±(n, 0)`.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableSystemGroupEquiv`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.nonorientableSystemGroupEquiv`: the isomorphisms
  `G_S ≃* G ∗ (S^±(n, 0) ∗ F(X ∖ {variables of S}))` for the equations of types (1) and (3).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableSystemGroupEquivOfSurjective`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.nonorientableSystemGroupEquivOfSurjective`: the
  isomorphisms `G_S ≃* G ∗ S^±(n, 0)` when every variable occurs in the equation.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.orderOf_mk_inr_of_nonorientable_one`: in the group of
  the equation `x² = 1`, the variable `x` has order `2`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.4 (the group `G_S` of a system) and §2.7 (standard quadratic equations).
-/

public section

open Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

open SurfaceGroup

variable {G X : Type*} [Group G] {n : ℕ}

/-! ### Type (1): products of commutators -/

section Orientable

variable {x y : Fin n → X}

/-- The variables of `X` are the generators of the closed orientable surface group, sent to the
variables of the equation, together with the variables that do not occur in the equation. -/
private noncomputable def orientableVarEquiv (inj : (Sum.elim x y).Injective) :
    OrientableGenerator n 0 ⊕ ↥(Set.range (Sum.elim x y))ᶜ ≃ X :=
  (((OrientableGenerator.equivSum n 0).trans (Equiv.sumEmpty _ _)).sumCongr (.refl _)).trans
    (Equiv.ofInjectiveSumCompl _ inj)

private theorem orientableVarEquiv_a (inj : (Sum.elim x y).Injective) (i : Fin n) :
    orientableVarEquiv inj (.inl (.a i)) = x i := by
  simp [orientableVarEquiv]

private theorem orientableVarEquiv_b (inj : (Sum.elim x y).Injective) (i : Fin n) :
    orientableVarEquiv inj (.inl (.b i)) = y i := by
  simp [orientableVarEquiv]

private theorem orientableVarEquiv_inr (inj : (Sum.elim x y).Injective)
    (v : ↥(Set.range (Sum.elim x y))ᶜ) : orientableVarEquiv inj (.inr v) = v := by
  simp [orientableVarEquiv]

private theorem normalClosure_toWord_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    normalClosure {(orientable (G := G) n hn x y inj).toWord} =
      normalClosure ((inr : FreeGroup X →* GX G X) ''
        (FreeGroup.map (orientableVarEquiv inj ∘ Sum.inl) '' {orientableRelator n 0})) := by
  rw [Set.image_singleton, Set.image_singleton, toWord_orientable, orientableRelator_def,
    map_orientableWord (FreeGroup.map _), map_orientableWord (inr : FreeGroup X →* GX G X)]
  simp [orientableWord_def, orientableVarEquiv_a, orientableVarEquiv_b]

variable (G) in
/-- The group of the standard quadratic equation `[x₁, y₁] ⋯ [xₙ, yₙ] = 1` over `G` is the free
product of `G`, the closed orientable surface group `S⁺(n, 0)` and the free group on the variables
that do not occur in the equation. -/
noncomputable def orientableSystemGroupEquiv (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    SystemGroup G {(orientable (G := G) n hn x y inj).toWord} ≃*
      Monoid.Coprod G (Monoid.Coprod (Orientable n 0) (FreeGroup ↥(Set.range (Sum.elim x y))ᶜ)) :=
  (QuotientGroup.quotientMulEquivOfEq (normalClosure_toWord_orientable hn inj)).trans
    (SystemGroup.coprodPresentedGroupFreeGroupEquiv G {orientableRelator n 0}
      (orientableVarEquiv inj))

variable (hn : 0 < n) (inj : (Sum.elim x y).Injective)

@[simp]
theorem orientableSystemGroupEquiv_mk_inl (g : G) :
    orientableSystemGroupEquiv G hn inj ((inl g : GX G X) : SystemGroup G _) = inl g := by
  simp [orientableSystemGroupEquiv]

@[simp]
theorem orientableSystemGroupEquiv_mk_inr_of_x (i : Fin n) :
    orientableSystemGroupEquiv G hn inj ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      inr (inl (Orientable.a n 0 i)) := by
  simp [orientableSystemGroupEquiv, ← orientableVarEquiv_a inj, Orientable.a_def]

@[simp]
theorem orientableSystemGroupEquiv_mk_inr_of_y (i : Fin n) :
    orientableSystemGroupEquiv G hn inj ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) =
      inr (inl (Orientable.b n 0 i)) := by
  simp [orientableSystemGroupEquiv, ← orientableVarEquiv_b inj, Orientable.b_def]

@[simp]
theorem orientableSystemGroupEquiv_mk_inr_of_val (v : ↥(Set.range (Sum.elim x y))ᶜ) :
    orientableSystemGroupEquiv G hn inj ((inr (FreeGroup.of (v : X)) : GX G X) : SystemGroup G _) =
      inr (inr (FreeGroup.of v)) := by
  simp [orientableSystemGroupEquiv, ← orientableVarEquiv_inr inj]

@[simp]
theorem orientableSystemGroupEquiv_symm_inl (g : G) :
    (orientableSystemGroupEquiv G hn inj).symm (inl g) = ((inl g : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem orientableSystemGroupEquiv_symm_inr_inl_a (i : Fin n) :
    (orientableSystemGroupEquiv G hn inj).symm (inr (inl (Orientable.a n 0 i))) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem orientableSystemGroupEquiv_symm_inr_inl_b (i : Fin n) :
    (orientableSystemGroupEquiv G hn inj).symm (inr (inl (Orientable.b n 0 i))) =
      ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem orientableSystemGroupEquiv_symm_inr_inr_of (v : ↥(Set.range (Sum.elim x y))ᶜ) :
    (orientableSystemGroupEquiv G hn inj).symm (inr (inr (FreeGroup.of v))) =
      ((inr (FreeGroup.of (v : X)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

variable (G) in
/-- When every variable occurs in the standard quadratic equation `[x₁, y₁] ⋯ [xₙ, yₙ] = 1`, its
group over `G` is the free product of `G` and the closed orientable surface group `S⁺(n, 0)`. -/
noncomputable def orientableSystemGroupEquivOfSurjective
    (surj : (Sum.elim x y).Surjective) :
    SystemGroup G {(orientable (G := G) n hn x y inj).toWord} ≃*
      Monoid.Coprod G (Orientable n 0) :=
  have : IsEmpty ↥(Set.range (Sum.elim x y))ᶜ := by simp [surj.range_eq]
  (orientableSystemGroupEquiv G hn inj).trans
    (MulEquiv.coprodCongr (.refl G) GX.equivOfIsEmpty)

variable (surj : (Sum.elim x y).Surjective)

@[simp]
theorem orientableSystemGroupEquivOfSurjective_mk_inl (g : G) :
    orientableSystemGroupEquivOfSurjective G hn inj surj ((inl g : GX G X) : SystemGroup G _) =
      inl g := by
  simp [orientableSystemGroupEquivOfSurjective]

@[simp]
theorem orientableSystemGroupEquivOfSurjective_mk_inr_of_x (i : Fin n) :
    orientableSystemGroupEquivOfSurjective G hn inj surj
        ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      inr (Orientable.a n 0 i) := by
  simp [orientableSystemGroupEquivOfSurjective]

@[simp]
theorem orientableSystemGroupEquivOfSurjective_mk_inr_of_y (i : Fin n) :
    orientableSystemGroupEquivOfSurjective G hn inj surj
        ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) =
      inr (Orientable.b n 0 i) := by
  simp [orientableSystemGroupEquivOfSurjective]

@[simp]
theorem orientableSystemGroupEquivOfSurjective_symm_inl (g : G) :
    (orientableSystemGroupEquivOfSurjective G hn inj surj).symm (inl g) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem orientableSystemGroupEquivOfSurjective_symm_inr_a (i : Fin n) :
    (orientableSystemGroupEquivOfSurjective G hn inj surj).symm (inr (Orientable.a n 0 i)) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem orientableSystemGroupEquivOfSurjective_symm_inr_b (i : Fin n) :
    (orientableSystemGroupEquivOfSurjective G hn inj surj).symm (inr (Orientable.b n 0 i)) =
      ((inr (FreeGroup.of (y i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

end Orientable

/-! ### Type (3): products of squares -/

section Nonorientable

variable {x : Fin n → X}

/-- The variables of `X` are the generators of the closed non-orientable surface group, sent to
the variables of the equation, together with the variables that do not occur in the equation. -/
private noncomputable def nonorientableVarEquiv (inj : x.Injective) :
    NonorientableGenerator n 0 ⊕ ↥(Set.range x)ᶜ ≃ X :=
  (((NonorientableGenerator.equivSum n 0).trans (Equiv.sumEmpty _ _)).sumCongr (.refl _)).trans
    (Equiv.ofInjectiveSumCompl _ inj)

private theorem nonorientableVarEquiv_c (inj : x.Injective) (i : Fin n) :
    nonorientableVarEquiv inj (.inl (.c i)) = x i := by
  simp [nonorientableVarEquiv]

private theorem nonorientableVarEquiv_inr (inj : x.Injective) (v : ↥(Set.range x)ᶜ) :
    nonorientableVarEquiv inj (.inr v) = v := by
  simp [nonorientableVarEquiv]

private theorem normalClosure_toWord_nonorientable (hn : 0 < n) (inj : x.Injective) :
    normalClosure {(nonorientable (G := G) n hn x inj).toWord} =
      normalClosure ((inr : FreeGroup X →* GX G X) ''
        (FreeGroup.map (nonorientableVarEquiv inj ∘ Sum.inl) '' {nonorientableRelator n 0})) := by
  rw [Set.image_singleton, Set.image_singleton, toWord_nonorientable, nonorientableRelator_def,
    map_nonorientableWord (FreeGroup.map _), map_nonorientableWord (inr : FreeGroup X →* GX G X)]
  simp [nonorientableWord_def, nonorientableVarEquiv_c]

variable (G) in
/-- The group of the standard quadratic equation `x₁² ⋯ xₙ² = 1` over `G` is the free product of
`G`, the closed non-orientable surface group `S⁻(n, 0)` and the free group on the variables that
do not occur in the equation. -/
noncomputable def nonorientableSystemGroupEquiv (hn : 0 < n) (inj : x.Injective) :
    SystemGroup G {(nonorientable (G := G) n hn x inj).toWord} ≃*
      Monoid.Coprod G (Monoid.Coprod (Nonorientable n 0) (FreeGroup ↥(Set.range x)ᶜ)) :=
  (QuotientGroup.quotientMulEquivOfEq (normalClosure_toWord_nonorientable hn inj)).trans
    (SystemGroup.coprodPresentedGroupFreeGroupEquiv G {nonorientableRelator n 0}
      (nonorientableVarEquiv inj))

variable (hn : 0 < n) (inj : x.Injective)

@[simp]
theorem nonorientableSystemGroupEquiv_mk_inl (g : G) :
    nonorientableSystemGroupEquiv G hn inj ((inl g : GX G X) : SystemGroup G _) = inl g := by
  simp [nonorientableSystemGroupEquiv]

@[simp]
theorem nonorientableSystemGroupEquiv_mk_inr_of_x (i : Fin n) :
    nonorientableSystemGroupEquiv G hn inj
        ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      inr (inl (Nonorientable.c n 0 i)) := by
  simp [nonorientableSystemGroupEquiv, ← nonorientableVarEquiv_c inj, Nonorientable.c_def]

@[simp]
theorem nonorientableSystemGroupEquiv_mk_inr_of_val (v : ↥(Set.range x)ᶜ) :
    nonorientableSystemGroupEquiv G hn inj
        ((inr (FreeGroup.of (v : X)) : GX G X) : SystemGroup G _) =
      inr (inr (FreeGroup.of v)) := by
  simp [nonorientableSystemGroupEquiv, ← nonorientableVarEquiv_inr inj]

@[simp]
theorem nonorientableSystemGroupEquiv_symm_inl (g : G) :
    (nonorientableSystemGroupEquiv G hn inj).symm (inl g) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem nonorientableSystemGroupEquiv_symm_inr_inl_c (i : Fin n) :
    (nonorientableSystemGroupEquiv G hn inj).symm (inr (inl (Nonorientable.c n 0 i))) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem nonorientableSystemGroupEquiv_symm_inr_inr_of (v : ↥(Set.range x)ᶜ) :
    (nonorientableSystemGroupEquiv G hn inj).symm (inr (inr (FreeGroup.of v))) =
      ((inr (FreeGroup.of (v : X)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

variable (G) in
/-- When every variable occurs in the standard quadratic equation `x₁² ⋯ xₙ² = 1`, its group over
`G` is the free product of `G` and the closed non-orientable surface group `S⁻(n, 0)`. -/
noncomputable def nonorientableSystemGroupEquivOfSurjective (surj : x.Surjective) :
    SystemGroup G {(nonorientable (G := G) n hn x inj).toWord} ≃*
      Monoid.Coprod G (Nonorientable n 0) :=
  have : IsEmpty ↥(Set.range x)ᶜ := by simp [surj.range_eq]
  (nonorientableSystemGroupEquiv G hn inj).trans
    (MulEquiv.coprodCongr (.refl G) GX.equivOfIsEmpty)

variable (surj : x.Surjective)

@[simp]
theorem nonorientableSystemGroupEquivOfSurjective_mk_inl (g : G) :
    nonorientableSystemGroupEquivOfSurjective G hn inj surj
        ((inl g : GX G X) : SystemGroup G _) = inl g := by
  simp [nonorientableSystemGroupEquivOfSurjective]

@[simp]
theorem nonorientableSystemGroupEquivOfSurjective_mk_inr_of_x (i : Fin n) :
    nonorientableSystemGroupEquivOfSurjective G hn inj surj
        ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) =
      inr (Nonorientable.c n 0 i) := by
  simp [nonorientableSystemGroupEquivOfSurjective]

@[simp]
theorem nonorientableSystemGroupEquivOfSurjective_symm_inl (g : G) :
    (nonorientableSystemGroupEquivOfSurjective G hn inj surj).symm (inl g) =
      ((inl g : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

@[simp]
theorem nonorientableSystemGroupEquivOfSurjective_symm_inr_c (i : Fin n) :
    (nonorientableSystemGroupEquivOfSurjective G hn inj surj).symm
        (inr (Nonorientable.c n 0 i)) =
      ((inr (FreeGroup.of (x i)) : GX G X) : SystemGroup G _) := by
  simp [MulEquiv.symm_apply_eq]

end Nonorientable

/-! ### Examples -/

section Examples

/-- In the group of the equation `x² = 1` over any group `G`, in any set of variables, the
variable `x` has order `2`: it is the generator of the free factor `S⁻(1, 0) ≃* ℤ/2`. -/
theorem orderOf_mk_inr_of_nonorientable_one {x : Fin 1 → X} (inj : x.Injective) :
    orderOf ((inr (FreeGroup.of (x 0)) : GX G X) :
      SystemGroup G {(nonorientable (G := G) 1 one_pos x inj).toWord}) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact subset_normalClosure (by simp [toWord_def])
  · have h' := congrArg (fun w => Nonorientable.projectivePlaneEquiv (fst (snd w)))
      (congrArg (nonorientableSystemGroupEquiv G one_pos inj) h)
    simp at h'

/-- The group of the torus equation `[x, y] = 1` over `G`, in the variables `x` and `y`, is
`G ∗ ℤ²`. -/
theorem nonempty_systemGroup_torus_mulEquiv :
    Nonempty (SystemGroup G
        {(orientable (G := G) (X := Fin 1 ⊕ Fin 1) 1 one_pos Sum.inl Sum.inr
          (by simp [Function.injective_id])).toWord} ≃*
      Monoid.Coprod G (Multiplicative (Fin 2 → ℤ))) :=
  ⟨(orientableSystemGroupEquivOfSurjective G one_pos _ (by simp [Function.surjective_id])).trans
    (MulEquiv.coprodCongr (.refl G) Orientable.torusEquiv)⟩

end Examples

end TauCeti.GroupAlgGeom.Quadratic.Standard
