/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Order, spectral positivity, congruence, and operator-order Cauchy–Schwarz

In a C*-category `C`, each endomorphism algebra `CategoryTheory.End X` carries the spectral
partial order `CStarAlgebra.spectralOrder (End X)`. This file proves:

* spectral nonnegativity of `End.of (f ≫ dagger f)` over `ℝ` and `ℂ`;
* congruence positivity and monotonicity across arbitrary objects
  `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` and `a ↦ End.of (dagger g ≫ a.asHom ≫ g)`;
* operator-order bounds and Cauchy–Schwarz inequalities in `End X`;
* `TauCeti.CStarCategory.ofSpectrumNonneg`: constructing a `TauCeti.CStarCategory` instance from
  spectral nonnegativity of `End.of (f ≫ dagger f)` over `ℂ` instead of explicit square-root
  witnesses `exists_self_comp_dagger_eq`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v u

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- Real scalar multiplication on `End X` acts on underlying arrows via coercion to `ℂ`. -/
@[simp] theorem real_smul_asHom {X : C} (r : ℝ) (a : End X) :
    (r • a).asHom = (r : ℂ) • a.asHom := by
  rw [← Complex.coe_smul, smul_asHom]

section Order

variable [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y Z : C}

/-- Every real spectral value of `End.of (f ≫ dagger f)` is nonnegative. -/
theorem spectrum_self_comp_dagger_nonneg (f : X ⟶ Y) ⦃x : ℝ⦄
    (hx : x ∈ spectrum ℝ (End.of (f ≫ dagger f))) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg (self_comp_dagger_nonneg f) hx

/-- Every complex spectral value of `End.of (f ≫ dagger f)` has nonnegative real part and zero
imaginary part. -/
theorem complexSpectrum_self_comp_dagger_nonneg (f : X ⟶ Y) ⦃z : ℂ⦄
    (hz : z ∈ spectrum ℂ (End.of (f ≫ dagger f))) : 0 ≤ z.re ∧ z.im = 0 := by
  open ComplexOrder in
  obtain ⟨hre, him⟩ :=
    Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg (self_comp_dagger_nonneg f) hz)
  exact ⟨hre, him.symm⟩

/-- Congruence `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` sends positive elements of `End Y` to
positive elements of `End X` for any `f : X ⟶ Y`. -/
theorem comp_asHom_comp_dagger_nonneg (f : X ⟶ Y) {a : End Y} (ha : 0 ≤ a) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  have hfg : f ≫ a.asHom ≫ dagger f = (f ≫ b.asHom) ≫ dagger (f ≫ b.asHom) := by
    rw [hb, mul_asHom, star_asHom, dagger_comp, Category.assoc, Category.assoc]
  rw [hfg]
  exact self_comp_dagger_nonneg (f ≫ b.asHom)

/-- Congruence `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` is monotone from `End Y` to `End X`. -/
theorem comp_asHom_comp_dagger_mono (f : X ⟶ Y) {a b : End Y} (hab : a ≤ b) :
    End.of (f ≫ a.asHom ≫ dagger f) ≤ End.of (f ≫ b.asHom ≫ dagger f) := by
  rw [← sub_nonneg] at hab ⊢
  have hsub : End.of (f ≫ b.asHom ≫ dagger f) - End.of (f ≫ a.asHom ≫ dagger f) =
      End.of (f ≫ (b - a).asHom ≫ dagger f) := by
    ext
    simp [Preadditive.comp_sub, Preadditive.sub_comp]
  rw [hsub]
  exact comp_asHom_comp_dagger_nonneg f hab

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` sends positive elements of `End X` to
positive elements of `End Y` for any `g : X ⟶ Y`. -/
theorem dagger_comp_asHom_comp_nonneg (g : X ⟶ Y) {a : End X} (ha : 0 ≤ a) :
    0 ≤ End.of (dagger g ≫ a.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_asHom_comp_dagger_nonneg (dagger g) ha

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` is monotone from `End X` to `End Y`. -/
theorem dagger_comp_asHom_comp_mono (g : X ⟶ Y) {a b : End X} (hab : a ≤ b) :
    End.of (dagger g ≫ a.asHom ≫ g) ≤ End.of (dagger g ≫ b.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_asHom_comp_dagger_mono (dagger g) hab

/-- Categorical operator-order bound: `End.of ((f ≫ g) ≫ dagger (f ≫ g))` is bounded in `End X` by
`(‖g‖ ^ 2) • End.of (f ≫ dagger f)`. -/
theorem comp_dagger_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of ((f ≫ g) ≫ dagger (f ≫ g)) ≤ (‖g‖ ^ 2) • End.of (f ≫ dagger f) := by
  have hle : End.of (g ≫ dagger g) ≤ algebraMap ℝ (End Y) (‖g‖ ^ 2) := by
    simpa only [End.norm_of, CStarCategory.norm_self_comp_dagger] using
      (self_comp_dagger_nonneg g).isSelfAdjoint.le_algebraMap_norm_self
  have hcong := comp_asHom_comp_dagger_mono f hle
  have hlhs : End.of (f ≫ (End.of (g ≫ dagger g)).asHom ≫ dagger f) =
      End.of ((f ≫ g) ≫ dagger (f ≫ g)) := by
    ext
    simp [Category.assoc]
  have hrhs : End.of (f ≫ (algebraMap ℝ (End Y) (‖g‖ ^ 2)).asHom ≫ dagger f) =
      (‖g‖ ^ 2) • End.of (f ≫ dagger f) := by
    ext
    simp [Algebra.algebraMap_eq_smul_one]
  rwa [hlhs, hrhs] at hcong

/-- Dual operator-order bound: `End.of (dagger (f ≫ g) ≫ (f ≫ g))` is bounded in `End Z` by
`(‖f‖ ^ 2) • End.of (dagger g ≫ g)`. -/
theorem dagger_comp_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of (dagger (f ≫ g) ≫ (f ≫ g)) ≤ (‖f‖ ^ 2) • End.of (dagger g ≫ g) := by
  simpa only [dagger_comp, dagger_dagger, CStarCategory.norm_dagger] using
    comp_dagger_self_comp_le (dagger g) (dagger f)

/-- Categorical Cauchy–Schwarz inequality in `End X` for two co-targeted morphisms `f : X ⟶ Y` and
`g : Z ⟶ Y`: `<f, g> <f, g>† ≤ ‖<g, g>‖ • <f, f>` where `<f, g> = f ≫ dagger g`. -/
theorem comp_dagger_comp_dagger_le_norm_smul (f : X ⟶ Y) (g : Z ⟶ Y) :
    End.of ((f ≫ dagger g) ≫ dagger (f ≫ dagger g)) ≤
      ‖g ≫ dagger g‖ • End.of (f ≫ dagger f) := by
  simpa only [CStarCategory.norm_dagger, CStarCategory.norm_self_comp_dagger] using
    comp_dagger_self_comp_le f (dagger g)

/-- Dual categorical Cauchy–Schwarz inequality in `End Z` for two co-sourced morphisms `f : Y ⟶ X`
and `g : Y ⟶ Z`. -/
theorem dagger_comp_dagger_comp_le_norm_smul (f : Y ⟶ X) (g : Y ⟶ Z) :
    End.of (dagger (dagger f ≫ g) ≫ (dagger f ≫ g)) ≤
      ‖dagger f ≫ f‖ • End.of (dagger g ≫ g) := by
  simpa only [CStarCategory.norm_dagger, CStarCategory.norm_dagger_comp_self] using
    dagger_comp_self_comp_le (dagger f) g

end Order

end CategoryTheory.End

namespace TauCeti.CStarCategory

/-- Construct a `CStarCategory` from spectral nonnegativity of `End.of (f ≫ dagger f)` over `ℂ`
instead of providing explicit square-root witnesses `exists_self_comp_dagger_eq`. -/
theorem ofSpectrumNonneg {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
    [∀ X Y : C, Norm (X ⟶ Y)]
    (normedSpaceCore : ∀ X Y : C, NormedSpace.Core ℂ (X ⟶ Y))
    (completeSpace : ∀ X Y : C,
      letI := NormedAddCommGroup.ofCore (normedSpaceCore X Y)
      CompleteSpace (X ⟶ Y))
    (norm_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ‖f ≫ g‖ ≤ ‖f‖ * ‖g‖)
    (norm_mul_self_le : ∀ {X Y : C} (f : X ⟶ Y), ‖f‖ * ‖f‖ ≤ ‖f ≫ dagger f‖)
    (spectrum_nonneg : ∀ {X Y : C} (f : X ⟶ Y) ⦃z : ℂ⦄,
      z ∈ spectrum ℂ (End.of (f ≫ dagger f)) → 0 ≤ z.re) :
    CStarCategory C where
  normedSpaceCore := normedSpaceCore
  completeSpace := completeSpace
  norm_comp_le := norm_comp_le
  norm_mul_self_le := norm_mul_self_le
  exists_self_comp_dagger_eq {X Y} f := by
    let _ : CStarAlgebra (End X) :=
      End.cstarAlgebraOf (normedSpaceCore X X) (completeSpace X X)
        (fun g h => norm_comp_le g h) (fun g => norm_mul_self_le g)
    let _ : PartialOrder (End X) := CStarAlgebra.spectralOrder (End X)
    have _ : StarOrderedRing (End X) := CStarAlgebra.spectralOrderedRing (End X)
    have hsa : IsSelfAdjoint (End.of (f ≫ dagger f)) := by
      rw [isSelfAdjoint_iff]
      ext
      simp
    have hpos : 0 ≤ End.of (f ≫ dagger f) := by
      rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa]
      intro x hx
      simpa using spectrum_nonneg f (spectrum.algebraMap_mem ℂ hx)
    obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
    have hmem := congrArg End.asHom hb
    simp only [End.mul_asHom, End.star_asHom] at hmem
    exact ⟨b.asHom, hmem⟩

end TauCeti.CStarCategory
