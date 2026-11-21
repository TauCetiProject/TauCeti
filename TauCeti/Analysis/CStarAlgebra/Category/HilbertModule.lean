/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Basic

/-!
# Hom spaces of a C*-category as Hilbert C*-modules

In a C*-category, the Hom space `X ⟶ Y` is a right Hilbert module over the C*-algebra `End X`:
the right action of `a : End X` is precomposition, `f a = a ≫ f` in categorical notation, and
the `End X`-valued inner product is `⟨f, g⟩ = f†g`, that is `g ≫ dagger f`. The module norm is
the given Hom norm, by the C*-identity `‖f‖² = ‖f†f‖`. Following Tau Ceti's convention for right
Hilbert modules, this is the instance `CStarModule (End X)ᵐᵒᵖ (X ⟶ Y)`, built on Mathlib's
action `SMul (End X)ᵐᵒᵖ (X ⟶ Y)`. It makes the Hilbert-module theory, such as Cauchy–Schwarz,
norm recovery and Paschke's inequality, available on Hom spaces.

Conjugation `a ↦ g†ag` by an arrow `g : X ⟶ Y` maps `End Y` to `End X`; it is monotone, and
`g†ag ≤ ‖a‖ g†g` for self-adjoint `a`. With `a = ff†` this is the Cauchy–Schwarz inequality
`(f†g)†(f†g) ≤ ‖f‖² g†g` for parallel arrows `f g : X ⟶ Y`. Arrows out of `X` with
`f†f ≤ g†g` in `End X` satisfy `‖f‖ ≤ ‖g‖`.

The polarization identity for `f†g` holds in any complex linear dagger category
(`TauCeti.comp_dagger_polarization`).

## Main declarations

* `TauCeti.CStarCategory.instCStarModule`: `X ⟶ Y` is a right Hilbert `End X`-module.
* `CategoryTheory.End.comp_comp_dagger_mono`: conjugation by an arrow is monotone.
* `CategoryTheory.End.comp_comp_dagger_le_norm_smul`: `g†ag ≤ ‖a‖ g†g` for self-adjoint `a`.
* `CategoryTheory.End.comp_dagger_comp_comp_dagger_le`: the Cauchy–Schwarz inequality
  `(f†g)†(f†g) ≤ ‖f‖² g†g`.
* `TauCeti.CStarCategory.norm_le_norm_of_self_comp_dagger_le`: `f†f ≤ g†g` implies
  `‖f‖ ≤ ‖g‖`.
* `TauCeti.CStarCategory.isGreatest_norm_comp_dagger`: `‖f‖` is the largest value of `‖g†f‖`
  over arrows `g` of norm at most one.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X Y : C}

/-- An arrow `f` with `f†f = 0`, that is `f ≫ dagger f = 0`, is zero. -/
@[simp] theorem self_comp_dagger_eq_zero {f : X ⟶ Y} : f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, pow_eq_zero_iff two_ne_zero, norm_eq_zero]

/-- The Hom space `X ⟶ Y` of a C*-category is a right Hilbert module over the C*-algebra
`End X`, with right action by precomposition and inner product `⟨f, g⟩ = f†g`, that is
`g ≫ dagger f`. -/
instance instCStarModule (X Y : C) : CStarModule (End X)ᵐᵒᵖ (X ⟶ Y) where
  inner f g := MulOpposite.op (.of (g ≫ dagger f))
  inner_add_right := by
    intro f g h
    rw [← MulOpposite.op_add]
    congr 1
    ext
    simp
  inner_self_nonneg := MulOpposite.op_nonneg.2 (End.self_comp_dagger_nonneg _)
  inner_self {f} := by
    rw [MulOpposite.op_eq_zero_iff, End.ext_iff, End.zero_asHom]
    exact self_comp_dagger_eq_zero
  inner_op_smul_right {a f g} := by
    rw [← MulOpposite.op_unop a, ← MulOpposite.op_mul]
    congr 1
    ext
    simp [End.smul_left]
  inner_smul_right_complex := by
    intro z f g
    rw [← MulOpposite.op_smul]
    congr 1
    ext
    simp
  star_inner f g := by
    rw [← MulOpposite.op_star]
    congr 1
    ext
    simp
  norm_eq_sqrt_norm_inner_self f := by
    rw [MulOpposite.norm_op, End.norm_of, norm_self_comp_dagger, Real.sqrt_sq (norm_nonneg f)]

/-- The `(End X)ᵐᵒᵖ`-valued inner product of the Hilbert module `X ⟶ Y`. -/
theorem inner_def (f g : X ⟶ Y) :
    inner (End X)ᵐᵒᵖ f g = MulOpposite.op (.of (g ≫ dagger f)) := (rfl)

/-- The `End X`-valued inner product of the Hilbert module `X ⟶ Y` is `⟨f, g⟩ = f†g`, that is
`g ≫ dagger f`. -/
@[simp] theorem unop_inner (f g : X ⟶ Y) :
    MulOpposite.unop (inner (End X)ᵐᵒᵖ f g) = .of (g ≫ dagger f) := (rfl)

end TauCeti.CStarCategory

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X Y : C}

/-- Conjugation by an arrow `g : X ⟶ Y` is monotone from `End Y` to `End X`: `a ≤ b` implies
`g†ag ≤ g†bg`, that is `g ≫ a ≫ dagger g ≤ g ≫ b ≫ dagger g`. -/
theorem comp_comp_dagger_mono (g : X ⟶ Y) {a b : End Y} (hab : a ≤ b) :
    End.of (g ≫ a.asHom ≫ dagger g) ≤ End.of (g ≫ b.asHom ≫ dagger g) := by
  obtain ⟨h, hh⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (sub_nonneg.2 hab)
  have key : End.of (g ≫ b.asHom ≫ dagger g) - End.of (g ≫ a.asHom ≫ dagger g) =
      End.of ((g ≫ h.asHom) ≫ dagger (g ≫ h.asHom)) := by
    have := congrArg End.asHom hh
    simp only [End.sub_asHom, End.mul_asHom, star_asHom] at this
    ext
    simp [← Preadditive.comp_sub, ← Preadditive.sub_comp, this]
  rw [← sub_nonneg, key]
  exact self_comp_dagger_nonneg _

/-- For a self-adjoint `a : End Y` and an arrow `g : X ⟶ Y`, the conjugate `g†ag`, that is
`g ≫ a ≫ dagger g`, is at most `‖a‖ g†g` in `End X`. -/
theorem comp_comp_dagger_le_norm_smul (g : X ⟶ Y) (a : End Y)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    End.of (g ≫ a.asHom ≫ dagger g) ≤ ‖a‖ • End.of (g ≫ dagger g) := by
  refine (comp_comp_dagger_mono g ha.le_algebraMap_norm_self).trans_eq ?_
  ext
  simp [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]

/-- The Cauchy–Schwarz inequality for parallel arrows `f g : X ⟶ Y` of a C*-category:
`(f†g)†(f†g) ≤ ‖f‖² g†g` in `End X`, that is
`g ≫ dagger f ≫ f ≫ dagger g ≤ ‖f‖ ^ 2 • (g ≫ dagger g)`. -/
theorem comp_dagger_comp_comp_dagger_le (f g : X ⟶ Y) :
    End.of (g ≫ dagger f ≫ f ≫ dagger g) ≤ ‖f‖ ^ 2 • End.of (g ≫ dagger g) := by
  have ha : IsSelfAdjoint (End.of (dagger f ≫ f)) := by
    rw [IsSelfAdjoint, End.ext_iff]
    simp
  simpa [End.norm_of, CStarCategory.norm_dagger_comp_self] using
    comp_comp_dagger_le_norm_smul g (End.of (dagger f ≫ f)) ha

end CategoryTheory.End

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X Y Z : C}

/-- Norms are monotone in `f†f`: for arrows `f : X ⟶ Y` and `g : X ⟶ Z` with `f†f ≤ g†g` in
`End X`, that is `f ≫ dagger f ≤ g ≫ dagger g`, we have `‖f‖ ≤ ‖g‖`. -/
theorem norm_le_norm_of_self_comp_dagger_le {f : X ⟶ Y} {g : X ⟶ Z}
    (h : End.of (f ≫ dagger f) ≤ End.of (g ≫ dagger g)) : ‖f‖ ≤ ‖g‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg f) (norm_nonneg g) two_ne_zero).1 ?_
  rw [← norm_self_comp_dagger, ← norm_self_comp_dagger, ← End.norm_of, ← End.norm_of]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg h (End.self_comp_dagger_nonneg f)

/-- Norm recovery: `‖f‖` is the largest value of `‖g†f‖`, that is `‖f ≫ dagger g‖`, over arrows
`g : X ⟶ Y` of norm at most one. -/
theorem isGreatest_norm_comp_dagger (f : X ⟶ Y) :
    IsGreatest {‖f ≫ dagger g‖ | (g : X ⟶ Y) (_ : ‖g‖ ≤ 1)} ‖f‖ := by
  simpa only [unop_inner, End.norm_of] using
    CStarModule.isGreatest_norm_unop_inner (A := End X) f

end TauCeti.CStarCategory
