/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Basic
public import TauCeti.CategoryTheory.CStar.Basic

/-!
# Hilbert C*-module structures, Cauchy–Schwarz, and polarization on Hom spaces

In a C\*-category `C`, each Hom space `X ⟶ Y` carries two compatible Hilbert C\*-module structures
whose module norms both coincide with the categorical Hom norm:

* **Right Hilbert `End X`-module** (`CStarModule (End X)ᵐᵒᵖ (X ⟶ Y)`): the right action of
  `a : End X` is precomposition `MulOpposite.op a • f = a.asHom ≫ f`, and the `End X`-valued inner
  product is `MulOpposite.unop (inner (End X)ᵐᵒᵖ f g) = End.of (g ≫ dagger f)`.
* **Left Hilbert `End Y`-module** (`CStarModule (End Y) (X ⟶ Y)`): the left action of `b : End Y`
  is postcomposition `b • f = f ≫ b.asHom`, and the `End Y`-valued inner product is
  `inner (End Y) f g = End.of (dagger f ≫ g)`.

Specializing `TauCeti.Analysis.CStarAlgebra.Module.Basic` to these two instances yields the
endomorphism-valued Cauchy–Schwarz inequalities in `End X` and `End Y`, polarization identities for
`g ≫ dagger f` and `dagger f ≫ g`, separation of parallel morphisms by inner-product pairings, and
recovery of `‖f‖` from pairings against the closed unit ball of `X ⟶ Y`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. **120** (1985), §1.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) **84** (2002), §2.
-/

public section

noncomputable section

open CategoryTheory MulOpposite Complex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]
variable [CStarCategory C] {X Y : C}

/-- Each Hom space `X ⟶ Y` is a right Hilbert `End X`-module under precomposition
`MulOpposite.op a • f = a.asHom ≫ f`, with `End X`-valued inner product `End.of (g ≫ dagger f)`. -/
instance instHomRightCStarModule (X Y : C) : CStarModule (End X)ᵐᵒᵖ (X ⟶ Y) where
  inner f g := op (End.of (g ≫ dagger f))
  inner_add_right := by simp [Preadditive.add_comp]
  inner_self_nonneg := op_nonneg.mpr (End.of_comp_dagger_self_nonneg _)
  inner_self := by simp [End.ext_iff]
  inner_op_smul_right {a f g} := by
    apply unop_injective
    ext
    simp [End.smul_left, Category.assoc]
  inner_smul_right_complex := by simp
  star_inner f g := by
    apply unop_injective
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [MulOpposite.norm_op, End.norm_of, norm_comp_dagger_self, sq,
      Real.sqrt_mul_self (norm_nonneg f)]

/-- Each Hom space `X ⟶ Y` is a left Hilbert `End Y`-module under postcomposition
`b • f = f ≫ b.asHom`, with `End Y`-valued inner product `End.of (dagger f ≫ g)`. -/
instance instHomLeftCStarModule (X Y : C) : CStarModule (End Y) (X ⟶ Y) where
  inner f g := End.of (dagger f ≫ g)
  inner_add_right := by simp [Preadditive.comp_add]
  inner_self_nonneg := End.of_dagger_comp_self_nonneg _
  inner_self := by simp [End.ext_iff]
  inner_op_smul_right {b f g} := by
    ext
    simp [End.smul_right, Category.assoc]
  inner_smul_right_complex := by simp
  star_inner f g := by
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [End.norm_of, norm_dagger_comp_self, sq, Real.sqrt_mul_self (norm_nonneg f)]

/-- Evaluation of the `(End X)ᵐᵒᵖ`-valued inner product on `X ⟶ Y`. -/
theorem hom_inner_opEnd (f g : X ⟶ Y) :
    inner (End X)ᵐᵒᵖ f g = op (End.of (g ≫ dagger f)) := (rfl)

/-- Unwrapping `MulOpposite.unop` from the right Hilbert `End X`-module inner product gives
`End.of (g ≫ dagger f)`. -/
@[simp] theorem hom_unop_inner_opEnd (f g : X ⟶ Y) :
    unop (inner (End X)ᵐᵒᵖ f g) = End.of (g ≫ dagger f) := (rfl)

/-- Evaluation of the `End Y`-valued inner product on `X ⟶ Y`. -/
@[simp] theorem hom_inner_end (f g : X ⟶ Y) :
    inner (End Y) f g = End.of (dagger f ≫ g) := (rfl)

/-! ### Cauchy–Schwarz inequalities on Hom spaces -/

/-- **Cauchy–Schwarz inequality in `End X`:** for parallel arrows `f g : X ⟶ Y`,
`End.of (g ≫ dagger f ≫ f ≫ dagger g) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g)`. -/
theorem end_of_comp_dagger_comp_le (f g : X ⟶ Y) :
    End.of (g ≫ dagger f ≫ f ≫ dagger g) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  have h := CStarModule.star_unop_inner_mul_unop_inner_le (A := End X) f g
  simpa only [hom_unop_inner_opEnd, ← End.of_dagger, dagger_comp, dagger_dagger,
    ← End.of_comp, Category.assoc] using h

/-- **Cauchy–Schwarz inequality in `End Y`:** for parallel arrows `f g : X ⟶ Y`,
`End.of (dagger g ≫ f ≫ dagger f ≫ g) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g)`. -/
theorem end_of_dagger_comp_comp_le (f g : X ⟶ Y) :
    End.of (dagger g ≫ f ≫ dagger f ≫ g) ≤ ‖f‖ ^ 2 • End.of (dagger g ≫ g) := by
  have h := CStarModule.inner_mul_inner_swap_le (A := End Y) (x := f) (y := g)
  simpa only [hom_inner_end, ← End.of_comp, Category.assoc] using h

/-- Norm Cauchy–Schwarz bound for `g ≫ dagger f`. -/
theorem norm_comp_dagger_le (f g : X ⟶ Y) : ‖g ≫ dagger f‖ ≤ ‖f‖ * ‖g‖ := by
  simpa only [hom_unop_inner_opEnd, End.norm_of] using
    CStarModule.norm_unop_inner_le (A := End X) f g

/-- Norm Cauchy–Schwarz bound for `dagger f ≫ g`. -/
theorem norm_dagger_comp_le (f g : X ⟶ Y) : ‖dagger f ≫ g‖ ≤ ‖f‖ * ‖g‖ := by
  simpa only [hom_inner_end, End.norm_of] using
    CStarModule.norm_inner_le (A := End Y) (E := X ⟶ Y) (x := f) (y := g)

/-! ### Polarization, separation, and norm recovery -/

/-- **Polarization identity in `X ⟶ X`:** `g ≫ dagger f` is a linear combination of the four
diagonal terms `(f ± g) ≫ dagger (f ± g)` and `(f ± I • g) ≫ dagger (f ± I • g)`. -/
theorem comp_dagger_polarization (f g : X ⟶ Y) :
    g ≫ dagger f =
      (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) -
        I • ((f + I • g) ≫ dagger (f + I • g)) +
        I • ((f - I • g) ≫ dagger (f - I • g))) := by
  have h := congrArg (End.asHom ∘ unop) (CStarModule.inner_polarization (A := (End X)ᵐᵒᵖ) f g)
  simpa only [Function.comp_apply, MulOpposite.unop_smul, MulOpposite.unop_add,
    MulOpposite.unop_sub, hom_unop_inner_opEnd, End.smul_asHom, End.add_asHom,
    End.sub_asHom] using h

/-- **Polarization identity in `Y ⟶ Y`:** `dagger f ≫ g` is a linear combination of the four
diagonal terms `dagger (f ± g) ≫ (f ± g)` and `dagger (f ± I • g) ≫ (f ± I • g)`. -/
theorem dagger_comp_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ • (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        I • (dagger (f + I • g) ≫ (f + I • g)) +
        I • (dagger (f - I • g) ≫ (f - I • g))) := by
  have h := congrArg End.asHom (CStarModule.inner_polarization (A := End Y) f g)
  simpa only [hom_inner_end, End.smul_asHom, End.add_asHom, End.sub_asHom] using h

/-- Parallel morphisms `f g : X ⟶ Y` are equal when `f ≫ dagger h = g ≫ dagger h` for all
`h : X ⟶ Y`. -/
theorem ext_comp_dagger_right {f g : X ⟶ Y} (h : ∀ k : X ⟶ Y, f ≫ dagger k = g ≫ dagger k) :
    f = g :=
  CStarModule.ext_inner_left (A := (End X)ᵐᵒᵖ) fun k => by simp [hom_inner_opEnd, h k]

/-- Parallel morphisms `f g : X ⟶ Y` are equal when `dagger k ≫ f = dagger k ≫ g` for all
`k : X ⟶ Y`. -/
theorem ext_dagger_comp_left {f g : X ⟶ Y} (h : ∀ k : X ⟶ Y, dagger k ≫ f = dagger k ≫ g) :
    f = g :=
  CStarModule.ext_inner_left (A := End Y) fun k => by simp [h k]

/-- Norm recovery from `X ⟶ X`-pairings: `‖f‖` is the greatest value of `‖f ≫ dagger g‖` over
`g : X ⟶ Y` in the closed unit ball. -/
theorem isGreatest_norm_comp_dagger (f : X ⟶ Y) :
    IsGreatest { ‖f ≫ dagger g‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1) } ‖f‖ := by
  simpa only [hom_unop_inner_opEnd, End.norm_of] using
    CStarModule.isGreatest_norm_unop_inner (A := End X) f

/-- Norm recovery from `Y ⟶ Y`-pairings: `‖f‖` is the greatest value of `‖dagger g ≫ f‖` over
`g : X ⟶ Y` in the closed unit ball. -/
theorem isGreatest_norm_dagger_comp (f : X ⟶ Y) :
    IsGreatest { ‖dagger g ≫ f‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1) } ‖f‖ := by
  simpa only [hom_inner_end, End.norm_of] using
    CStarModule.isGreatest_norm_inner (A := End Y) f

end TauCeti
