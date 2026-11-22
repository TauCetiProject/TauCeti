/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# C*-categories

A C*-category is a complex linear dagger category whose Hom spaces are Banach spaces, with
contractive composition, the C*-identity `‖f†f‖ = ‖f‖²`, and `f†f` positive in `End X` for
every arrow `f` out of `X`. Here `f†f` denotes the operator-order composite, which is
`f ≫ dagger f` in categorical notation.

`TauCeti.CStarCategory` adds this analytic structure to Mathlib's native `Preadditive` and
`Linear ℂ` carriers and to a conjugate-linear `TauCeti.DaggerCategory`. Positivity of `f†f`
is stated as `f ≫ dagger f = g ≫ dagger g` for an endomorphism `g` of `X`; in the C*-algebra
`End X` this is equivalent to `0 ≤ f†f` (`CategoryTheory.End.nonneg_iff`).

## Main declarations

* `TauCeti.CStarCategory`: the C*-category axioms on given Hom norms.
* `TauCeti.CStarCategory.norm_dagger` and `TauCeti.CStarCategory.norm_self_comp_dagger`: the
  dagger is isometric and the C*-identity holds with equality.
* `TauCeti.CStarCategory.norm_comp_dagger_sq_le` and `TauCeti.CStarCategory.norm_dagger_comp_sq_le`:
  norm Cauchy–Schwarz inequalities.
* `TauCeti.CStarCategory.norm_comp_dagger_le_polarization`: polarization norm bound.
* `TauCeti.CStarCategory.norm_id`, `TauCeti.CStarCategory.isZero_iff_norm_id_eq_zero`, and
  `TauCeti.CStarCategory.not_isZero_iff_norm_id_eq_one`: zero-object vs nonzero identity norms,
  together with norm formulas for self-adjoint idempotents and unitary arrows.
* `CategoryTheory.End.instCStarAlgebra`: each endomorphism algebra `End X` is a unital
  C*-algebra, with Mathlib's operator-order multiplication and the dagger as star.
* `CategoryTheory.End.nonneg_iff`: the positive elements of `End X` are exactly the composites
  `f ≫ dagger f` for arrows `f` out of `X`.

## Implementation notes

As for Mathlib's `CStarModule`, the class takes the Hom norms as `Norm` parameters and asks for
a `NormedSpace.Core`, rather than registering `NormedAddCommGroup` instances on Hom types: a
concrete category such as Hilbert spaces already carries normed structures on its Hom types,
whose uniformities need not be definitionally those induced by the norm. The abbreviations
`TauCeti.CStarCategory.normedAddCommGroup` and `TauCeti.CStarCategory.normedSpace` provide
these structures when no others are present. The type `End X` has no prior norm, so its
normed and C*-algebra structures are global instances.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti

/-- A *C*-category* structure on given norms of the Hom spaces of a complex linear dagger
category: the Hom spaces are complex Banach spaces, composition is contractive, the
C*-inequality `‖f‖² ≤ ‖f†f‖` holds, and `f†f` has the form `g†g` for an endomorphism `g`
of the source of `f`. Here `f†f` is the operator-order composite `f ≫ dagger f`. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    [∀ X Y : C, Norm (X ⟶ Y)] : Prop where
  /-- Each Hom space is a complex normed space for the given norm. -/
  normedSpaceCore (X Y : C) : NormedSpace.Core ℂ (X ⟶ Y)
  /-- Each Hom space is complete for the metric of its norm. -/
  completeSpace (X Y : C) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore X Y)
    CompleteSpace (X ⟶ Y)
  /-- Composition is contractive. -/
  norm_comp_le {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖
  /-- The C*-inequality; equality follows (`TauCeti.CStarCategory.norm_self_comp_dagger`). -/
  norm_mul_self_le {X Y : C} (f : X ⟶ Y) : ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖
  /-- Positivity of `f†f` in `End X`: it is `g†g` for some endomorphism `g` of `X`. -/
  exists_self_comp_dagger_eq {X Y : C} (f : X ⟶ Y) :
    ∃ g : X ⟶ X, f ≫ dagger f = g ≫ dagger g

namespace CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed group structure of a Hom space of a C*-category. This is not an instance:
a Hom type may already carry a normed structure with a better uniformity. -/
abbrev normedAddCommGroup (X Y : C) : NormedAddCommGroup (X ⟶ Y) :=
  .ofCore (normedSpaceCore X Y)

/-- The complex normed space structure of a Hom space of a C*-category. This is not an
instance, for the same reason as `TauCeti.CStarCategory.normedAddCommGroup`. -/
abbrev normedSpace (X Y : C) :
    letI := normedAddCommGroup X Y
    NormedSpace ℂ (X ⟶ Y) :=
  letI := normedAddCommGroup X Y
  .ofCore (normedSpaceCore X Y)

variable {W X Y Z : C}

/-- Hom norms are nonnegative. -/
theorem norm_nonneg (f : X ⟶ Y) : 0 ≤ ‖f‖ :=
  (normedSpaceCore X Y).norm_nonneg f

/-- An arrow has norm zero exactly when it is zero. -/
@[simp] theorem norm_eq_zero {f : X ⟶ Y} : ‖f‖ = 0 ↔ f = 0 :=
  (normedSpaceCore X Y).norm_eq_zero_iff f

/-- The zero arrow has norm zero. -/
@[simp] theorem norm_zero : ‖(0 : X ⟶ Y)‖ = 0 :=
  norm_eq_zero.2 rfl

/-- Hom norms are absolutely homogeneous for complex scalars. -/
theorem norm_smul (c : ℂ) (f : X ⟶ Y) : ‖c • f‖ = ‖c‖ * ‖f‖ :=
  (normedSpaceCore X Y).norm_smul c f

/-- Hom norms satisfy the triangle inequality. -/
theorem norm_add_le (f g : X ⟶ Y) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (normedSpaceCore X Y).norm_triangle f g

/-- Negating an arrow preserves its norm. -/
@[simp] theorem norm_neg (f : X ⟶ Y) : ‖-f‖ = ‖f‖ := by
  simpa using norm_smul (-1 : ℂ) f

/-- Hom norms satisfy the triangle inequality for subtraction. -/
theorem norm_sub_le (f g : X ⟶ Y) : ‖f - g‖ ≤ ‖f‖ + ‖g‖ := by
  simpa [sub_eq_add_neg, norm_neg] using norm_add_le f (-g)

/-- The dagger of a C*-category is isometric. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ := by
  -- `‖f‖² ≤ ‖f ≫ dagger f‖ ≤ ‖f‖ ‖dagger f‖` gives `‖f‖ ≤ ‖dagger f‖`, for `f` and `dagger f`.
  have key : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ ≤ ‖dagger f‖ := by
    intro X Y f
    have h := (norm_mul_self_le f).trans (norm_comp_le f (dagger f))
    rcases (norm_nonneg f).eq_or_lt with hf | hf
    · rw [← hf]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_left h hf
  exact le_antisymm (by simpa using key (dagger f)) (key f)

/-- The C*-identity: `‖f†f‖ = ‖f‖²`, where `f†f` is `f ≫ dagger f`. -/
theorem norm_self_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [pow_two]
  refine le_antisymm ?_ (norm_mul_self_le f)
  simpa using norm_comp_le f (dagger f)

/-- The C*-identity for `f f†`, where `f f†` is `dagger f ≫ f`. -/
theorem norm_dagger_comp_self (f : X ⟶ Y) : ‖dagger f ≫ f‖ = ‖f‖ ^ 2 := by
  simpa using norm_self_comp_dagger (dagger f)

/-- `f ≫ dagger f` vanishes precisely when `f` vanishes. -/
@[simp] theorem self_comp_dagger_eq_zero_iff (f : X ⟶ Y) :
    f ≫ dagger f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_self_comp_dagger, sq_eq_zero_iff, norm_eq_zero]

/-- `dagger f ≫ f` vanishes precisely when `f` vanishes. -/
@[simp] theorem dagger_comp_self_eq_zero_iff (f : X ⟶ Y) :
    dagger f ≫ f = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_dagger_comp_self, sq_eq_zero_iff, norm_eq_zero]

/-- Norm Cauchy–Schwarz inequality for `f ≫ dagger g`:
`‖f ≫ dagger g‖ ^ 2 ≤ ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖`. -/
theorem norm_comp_dagger_sq_le (f : X ⟶ Y) (g : Z ⟶ Y) :
    ‖f ≫ dagger g‖ ^ 2 ≤ ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖ := by
  calc
    ‖f ≫ dagger g‖ ^ 2 ≤ (‖f‖ * ‖dagger g‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_comp_le f (dagger g)) 2
    _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by rw [norm_dagger, mul_pow]
    _ = ‖f ≫ dagger f‖ * ‖g ≫ dagger g‖ := by
      rw [norm_self_comp_dagger, norm_self_comp_dagger]

/-- Norm Cauchy–Schwarz inequality for `dagger f ≫ g`:
`‖dagger f ≫ g‖ ^ 2 ≤ ‖dagger f ≫ f‖ * ‖dagger g ≫ g‖`. -/
theorem norm_dagger_comp_sq_le (f : Y ⟶ X) (g : Y ⟶ Z) :
    ‖dagger f ≫ g‖ ^ 2 ≤ ‖dagger f ≫ f‖ * ‖dagger g ≫ g‖ := by
  simpa only [dagger_dagger] using norm_comp_dagger_sq_le (dagger f) (dagger g)

/-- Polarization norm bound on `f ≫ dagger g` in terms of the four polarized combinations. -/
theorem norm_comp_dagger_le_polarization (f g : X ⟶ Y) :
    ‖f ≫ dagger g‖ ≤
      (4 : ℝ)⁻¹ * (‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 +
        ‖f + Complex.I • g‖ ^ 2 + ‖f - Complex.I • g‖ ^ 2) := by
  rw [comp_dagger_eq_polarization f g, norm_smul]
  have h4 : ‖(4 : ℂ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
  rw [h4]
  gcongr
  calc
    ‖(f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g))‖
      ≤ ‖(f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g)‖ +
          ‖Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
            (f - Complex.I • g) ≫ dagger (f - Complex.I • g))‖ := norm_add_le _ _
    _ ≤ (‖(f + g) ≫ dagger (f + g)‖ + ‖(f - g) ≫ dagger (f - g)‖) +
          (‖(f + Complex.I • g) ≫ dagger (f + Complex.I • g)‖ +
            ‖(f - Complex.I • g) ≫ dagger (f - Complex.I • g)‖) := by
        rw [norm_smul, Complex.norm_I, one_mul]
        exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 +
          ‖f + Complex.I • g‖ ^ 2 + ‖f - Complex.I • g‖ ^ 2 := by
        simp only [norm_self_comp_dagger, add_assoc]

/-! ### Identity, unitary, projection, and zero-object norm formulas -/

/-- Every self-adjoint idempotent `p : X ⟶ X` in a C*-category has norm `0` or `1`. -/
theorem norm_eq_zero_or_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) : ‖p‖ = 0 ∨ ‖p‖ = 1 := by
  have hsq : ‖p‖ ^ 2 = ‖p‖ := by
    calc
      ‖p‖ ^ 2 = ‖p ≫ dagger p‖ := (norm_self_comp_dagger p).symm
      _ = ‖p‖ := by rw [hsa, hp]
  by_cases h0 : ‖p‖ = 0
  · exact Or.inl h0
  · exact Or.inr (mul_left_cancel₀ h0 (by simpa [sq] using hsq))

/-- A nonzero self-adjoint idempotent has norm `1`. -/
theorem norm_eq_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) (hp0 : p ≠ 0) : ‖p‖ = 1 :=
  (norm_eq_zero_or_one_of_idempotent_of_dagger hp hsa).resolve_left (mt norm_eq_zero.mp hp0)

/-- Every self-adjoint idempotent is a contraction (`‖p‖ ≤ 1`). -/
theorem norm_le_one_of_idempotent_of_dagger {p : X ⟶ X}
    (hp : p ≫ p = p) (hsa : dagger p = p) : ‖p‖ ≤ 1 := by
  rcases norm_eq_zero_or_one_of_idempotent_of_dagger hp hsa with h | h <;> linarith

/-- The norm of an identity arrow is idempotent under squaring. -/
private theorem sq_norm_id (X : C) : ‖𝟙 X‖ ^ 2 = ‖𝟙 X‖ := by
  simpa using (norm_self_comp_dagger (𝟙 X)).symm

/-- The identity arrow of any object in a C*-category has norm `0` or `1`. -/
theorem norm_id_eq_zero_or_one (X : C) : ‖(𝟙 X : X ⟶ X)‖ = 0 ∨ ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  norm_eq_zero_or_one_of_idempotent_of_dagger (Category.id_comp (𝟙 X)) (dagger_id X)

/-- The identity of an object has norm at most one. -/
theorem norm_id_le_one (X : C) : ‖𝟙 X‖ ≤ 1 :=
  norm_le_one_of_idempotent_of_dagger (Category.id_comp (𝟙 X)) (dagger_id X)

/-- The identity of an object that is not a zero object has norm one. -/
theorem norm_id {X : C} (hX : ¬ Limits.IsZero X) : ‖𝟙 X‖ = 1 :=
  norm_eq_one_of_idempotent_of_dagger (Category.id_comp (𝟙 X)) (dagger_id X)
    (mt (Limits.IsZero.iff_id_eq_zero X).mpr hX)

/-- Every arrow out of a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_hom_left (hX : Limits.IsZero X) (f : X ⟶ Y) :
    ‖f‖ = 0 := by
  rw [hX.eq_of_src f 0, norm_zero]

/-- Every arrow into a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_hom_right (hY : Limits.IsZero Y) (f : X ⟶ Y) :
    ‖f‖ = 0 := by
  rw [hY.eq_of_tgt f 0, norm_zero]

/-- The identity arrow of a zero object has norm `0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_id (hX : Limits.IsZero X) :
    ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  hX.norm_hom_left (𝟙 X)

/-- An object in a C*-category is a zero object precisely when its identity arrow has norm `0`. -/
theorem isZero_iff_norm_id_eq_zero (X : C) : Limits.IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 0 := by
  rw [Limits.IsZero.iff_id_eq_zero, norm_eq_zero]

/-- An object in a C*-category is nonzero precisely when its identity arrow has norm `1`. -/
theorem not_isZero_iff_norm_id_eq_one (X : C) : ¬ Limits.IsZero X ↔ ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  rw [isZero_iff_norm_id_eq_zero]
  rcases norm_id_eq_zero_or_one X with h | h <;> simp [h]

/-- If `X ⟶ X` is nontrivial, the identity arrow `𝟙 X` has norm `1`. -/
@[simp] theorem norm_id_of_nontrivial (X : C) [Nontrivial (X ⟶ X)] :
    ‖(𝟙 X : X ⟶ X)‖ = 1 := by
  refine (not_isZero_iff_norm_id_eq_one X).mp fun hX => ?_
  obtain ⟨f, g, hfg⟩ := exists_pair_ne (X ⟶ X)
  exact hfg (hX.eq_of_src f g)

/-- In a C*-category with a chosen zero object `0`, `‖𝟙 (0 : C)‖ = 0`. -/
theorem norm_id_zero_object [Limits.HasZeroObject C] :
    open scoped ZeroObject in
    ‖(𝟙 (0 : C) : (0 : C) ⟶ 0)‖ = 0 :=
  (Limits.isZero_zero C).norm_id

/-- Pre-composing with an arrow satisfying `dagger u ≫ u = 𝟙 Y` preserves norms. -/
theorem norm_comp_of_dagger_comp_id {u : X ⟶ Y} (hu : dagger u ≫ u = 𝟙 Y) (g : Y ⟶ Z) :
    ‖u ≫ g‖ = ‖g‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_dagger_comp_self,
    ← norm_dagger_comp_self g, dagger_comp, Category.assoc, ← Category.assoc (dagger u) u g,
    hu, Category.id_comp]

/-- Post-composing with an arrow satisfying `u ≫ dagger u = 𝟙 X` preserves norms. -/
theorem norm_comp_of_comp_dagger_id {u : X ⟶ Y} (hu : u ≫ dagger u = 𝟙 X) (f : W ⟶ X) :
    ‖f ≫ u‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_self_comp_dagger,
    ← norm_self_comp_dagger f, dagger_comp, Category.assoc, ← Category.assoc u (dagger u),
    hu, Category.id_comp]

/-- Pre-composing with a unitary arrow preserves norms. -/
@[simp] theorem _root_.TauCeti.IsUnitary.norm_comp_left {u : X ⟶ Y} (hu : IsUnitary u)
    (g : Y ⟶ Z) : ‖u ≫ g‖ = ‖g‖ :=
  norm_comp_of_dagger_comp_id hu.dagger_hom_id g

/-- Post-composing with a unitary arrow preserves norms. -/
@[simp] theorem _root_.TauCeti.IsUnitary.norm_comp_right {u : X ⟶ Y} (hu : IsUnitary u)
    (f : W ⟶ X) : ‖f ≫ u‖ = ‖f‖ :=
  norm_comp_of_comp_dagger_id hu.hom_dagger_id f

/-- The norm of a unitary arrow `u : X ⟶ Y` equals `‖𝟙 X‖` (`1` when `X` is nonzero, `0` when `X`
is a zero object). -/
theorem _root_.TauCeti.IsUnitary.norm_eq_norm_id {u : X ⟶ Y} (hu : IsUnitary u) :
    ‖u‖ = ‖(𝟙 X : X ⟶ X)‖ := by
  have hsq : ‖u‖ ^ 2 = ‖(𝟙 X : X ⟶ X)‖ ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖u ≫ dagger u‖ := (norm_self_comp_dagger u).symm
      _ = ‖(𝟙 X : X ⟶ X)‖ := by rw [hu.hom_dagger_id]
      _ = ‖(𝟙 X : X ⟶ X)‖ ^ 2 := (sq_norm_id X).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Every unitary arrow is a contraction (`‖u‖ ≤ 1`). -/
theorem _root_.TauCeti.IsUnitary.norm_le_one {u : X ⟶ Y} (hu : IsUnitary u) : ‖u‖ ≤ 1 :=
  hu.norm_eq_norm_id.trans_le (norm_id_le_one X)

/-- A unitary arrow out of an object with nontrivial endomorphisms has norm `1`. -/
theorem _root_.TauCeti.IsUnitary.norm_eq_one {u : X ⟶ Y} (hu : IsUnitary u)
    [Nontrivial (X ⟶ X)] : ‖u‖ = 1 := by
  rw [hu.norm_eq_norm_id, norm_id_of_nontrivial]

end CStarCategory

end TauCeti

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C]

section Norm

variable [∀ X Y : C, Norm (X ⟶ Y)] {X : C}

/-- An endomorphism has the norm of its underlying arrow. -/
instance instNorm : Norm (End X) where
  norm a := ‖a.asHom‖

/-- The norm of an endomorphism is the norm of its underlying arrow. -/
theorem norm_def (a : End X) : ‖a‖ = ‖a.asHom‖ := (rfl)

/-- Regarding an arrow as an endomorphism preserves its norm. -/
@[simp] theorem norm_of (f : X ⟶ X) : ‖End.of f‖ = ‖f‖ := (rfl)

end Norm

section Transport

variable [Preadditive C] [∀ X Y : C, Norm (X ⟶ Y)] {X : C}

/-- Transport `NormedSpace.Core` from `X ⟶ X` to `End X` along `End.asHom`. -/
theorem normedSpaceCoreOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X)) : NormedSpace.Core 𝕜 (End X) where
  norm_nonneg a := hcore.norm_nonneg a.asHom
  norm_smul c a := by
    simpa only [norm_def, smul_asHom] using hcore.norm_smul c a.asHom
  norm_triangle a b := by
    simpa only [norm_def, add_asHom] using hcore.norm_triangle a.asHom b.asHom
  norm_eq_zero_iff a := by
    rw [norm_def, hcore.norm_eq_zero_iff, End.ext_iff, zero_asHom]

/-- Transport `NormedRing` on `End X` from a `NormedSpace.Core` on `X ⟶ X` and submultiplicative
composition. -/
@[expose, instance_reducible]
def normedRingOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X))
    (hcomp : ∀ f g : X ⟶ X, ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖) : NormedRing (End X) where
  __ := NormedAddCommGroup.ofCore (normedSpaceCoreOf hcore)
  __ := (inferInstance : Ring (End X))
  norm_mul_le a b := by
    simpa only [norm_def, mul_asHom, mul_comm ‖a.asHom‖] using hcomp b.asHom a.asHom

/-- Transport `NormedAlgebra` on `End X` from a `NormedSpace.Core` on `X ⟶ X` and
submultiplicative composition. -/
@[expose, instance_reducible]
def normedAlgebraOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X))
    (hcomp : ∀ f g : X ⟶ X, ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖) :
    letI := normedRingOf hcore hcomp
    NormedAlgebra 𝕜 (End X) :=
  letI := normedRingOf hcore hcomp
  ⟨fun c a => ((normedSpaceCoreOf hcore).norm_smul c a).le⟩

/-- Transport `End X ≃ₗᵢ[𝕜] (X ⟶ X)` from a `NormedSpace.Core` on `X ⟶ X`. -/
@[expose]
def linearIsometryEquivOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X)) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCoreOf hcore)
    letI := NormedAddCommGroup.ofCore hcore
    End X ≃ₗᵢ[𝕜] (X ⟶ X) :=
  letI := NormedAddCommGroup.ofCore (normedSpaceCoreOf hcore)
  letI := NormedAddCommGroup.ofCore hcore
  { toLinearEquiv := End.linearEquiv
    norm_map' _ := rfl }

/-- Transport completeness from `X ⟶ X` to `End X` along `End.linearIsometryEquivOf`. -/
theorem completeSpaceOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X))
    (hcomplete : letI := NormedAddCommGroup.ofCore hcore; CompleteSpace (X ⟶ X)) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCoreOf hcore)
    CompleteSpace (End X) :=
  letI := NormedAddCommGroup.ofCore hcore
  haveI := hcomplete
  letI := NormedAddCommGroup.ofCore (normedSpaceCoreOf hcore)
  (linearIsometryEquivOf hcore).toIsometryEquiv.completeSpace

/-- Transport `CStarRing` on `End X` from a `NormedSpace.Core` on `X ⟶ X`, submultiplicative
composition, and the C*-inequality on `X ⟶ X`. -/
theorem cstarRingOf {𝕜 : Type*} [NormedField 𝕜] [Linear 𝕜 C]
    [DaggerCategory C] [DaggerPreadditive C]
    (hcore : NormedSpace.Core 𝕜 (X ⟶ X))
    (hcomp : ∀ f g : X ⟶ X, ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖)
    (hmul_self : ∀ f : X ⟶ X, ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖) :
    letI := normedRingOf hcore hcomp
    CStarRing (End X) :=
  letI := normedRingOf hcore hcomp
  ⟨fun a => by simpa only [norm_def, mul_asHom, star_asHom] using hmul_self a.asHom⟩

/-- Transport `CStarAlgebra` on `End X` from a complex `NormedSpace.Core`, completeness,
submultiplicative composition, and the C*-inequality on `X ⟶ X`. -/
@[expose, instance_reducible]
def cstarAlgebraOf [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    (hcore : NormedSpace.Core ℂ (X ⟶ X))
    (hcomplete : letI := NormedAddCommGroup.ofCore hcore; CompleteSpace (X ⟶ X))
    (hcomp : ∀ f g : X ⟶ X, ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖)
    (hmul_self : ∀ f : X ⟶ X, ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖) :
    CStarAlgebra (End X) :=
  letI := normedRingOf hcore hcomp
  letI := normedAlgebraOf hcore hcomp
  haveI := completeSpaceOf hcore hcomplete
  haveI := cstarRingOf hcore hcomp hmul_self
  {}

end Transport

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] {X : C}

/-- The normed space axioms for `End X`, transported from the Hom space of `X`. -/
theorem normedSpaceCore (X : C) : NormedSpace.Core ℂ (End X) :=
  normedSpaceCoreOf (CStarCategory.normedSpaceCore X X)

/-- `End X` is a normed group for the norm of its underlying arrows. -/
instance instNormedAddCommGroup : NormedAddCommGroup (End X) :=
  .ofCore (normedSpaceCore X)

/-- `End X` is a normed ring: its operator-order multiplication is submultiplicative. -/
instance instNormedRing : NormedRing (End X) :=
  normedRingOf (CStarCategory.normedSpaceCore X X) (fun f g => CStarCategory.norm_comp_le f g)

/-- `End X` is a normed complex algebra. -/
instance instNormedAlgebra : NormedAlgebra ℂ (End X) :=
  normedAlgebraOf (CStarCategory.normedSpaceCore X X) (fun f g => CStarCategory.norm_comp_le f g)

/-- `End X` is complete, since the Hom space of `X` is. -/
instance instCompleteSpace : CompleteSpace (End X) :=
  completeSpaceOf (CStarCategory.normedSpaceCore X X) (CStarCategory.completeSpace X X)

/-- The C*-identity in `End X`, from the C*-inequality of the category. -/
instance instCStarRing : CStarRing (End X) :=
  cstarRingOf (CStarCategory.normedSpaceCore X X) (fun f g => CStarCategory.norm_comp_le f g)
    (fun f => CStarCategory.norm_mul_self_le f)

/-- Each endomorphism algebra of a C*-category is a unital C*-algebra, with the dagger as
star and Mathlib's operator-order multiplication. -/
instance instCStarAlgebra : CStarAlgebra (End X) :=
  cstarAlgebraOf (CStarCategory.normedSpaceCore X X) (CStarCategory.completeSpace X X)
    (fun f g => CStarCategory.norm_comp_le f g) (fun f => CStarCategory.norm_mul_self_le f)

/-- The positive cone of the C*-algebra `End X`: self-adjoint elements with nonnegative
spectrum. -/
instance instPartialOrder : PartialOrder (End X) := CStarAlgebra.spectralOrder (End X)

/-- The order of `End X` is the C*-algebra order. -/
instance instStarOrderedRing : StarOrderedRing (End X) :=
  CStarAlgebra.spectralOrderedRing (End X)

/-- In the endomorphism C*-algebra of a zero object, `‖(1 : End X)‖ = 0`. -/
theorem _root_.CategoryTheory.Limits.IsZero.norm_one_end (hX : Limits.IsZero X) :
    ‖(1 : End X)‖ = 0 :=
  hX.norm_id

/-- The unit of `End X` has norm `0` precisely when `X` is a zero object. -/
theorem norm_one_eq_zero_iff_isZero (X : C) :
    ‖(1 : End X)‖ = 0 ↔ Limits.IsZero X :=
  (CStarCategory.isZero_iff_norm_id_eq_zero X).symm

/-- An object is nonzero precisely when the unit of `End X` has norm `1`. -/
theorem norm_one_eq_one_iff_not_isZero (X : C) :
    ‖(1 : End X)‖ = 1 ↔ ¬ Limits.IsZero X :=
  (CStarCategory.not_isZero_iff_norm_id_eq_one X).symm

/-- For an arrow `f` out of `X`, the endomorphism `f†f`, that is `f ≫ dagger f`, is
positive in the C*-algebra `End X`. -/
theorem self_comp_dagger_nonneg {Y : C} (f : X ⟶ Y) : 0 ≤ End.of (f ≫ dagger f) := by
  obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger_eq f
  rw [hg]
  exact star_mul_self_nonneg (End.of g)

/-- For an arrow `f : X ⟶ Y`, the endomorphism `dagger f ≫ f` is positive in `End Y`. -/
theorem dagger_comp_self_nonneg {Y : C} (f : X ⟶ Y) : 0 ≤ End.of (dagger f ≫ f) := by
  simpa only [dagger_dagger] using self_comp_dagger_nonneg (dagger f)

/-- The positive elements of `End X` are exactly the endomorphisms `f ≫ dagger f`, for arrows
`f` out of `X`. -/
theorem nonneg_iff {a : End X} : 0 ≤ a ↔ ∃ (Y : C) (f : X ⟶ Y), a = End.of (f ≫ dagger f) := by
  refine ⟨fun ha => ?_, ?_⟩
  · obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 ha
    exact ⟨X, b.asHom, End.ext (by simp)⟩
  · rintro ⟨Y, f, rfl⟩
    exact self_comp_dagger_nonneg f

end CategoryTheory.End
