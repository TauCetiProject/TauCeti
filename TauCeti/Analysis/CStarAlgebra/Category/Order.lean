/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Order, congruence, and operator-order bounds

In a C*-category `C`, each endomorphism algebra `CategoryTheory.End X` carries the spectral
partial order `CStarAlgebra.spectralOrder (End X)`. This file proves:

* congruence positivity and monotonicity across arbitrary objects
  `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` and `a ↦ End.of (dagger g ≫ a.asHom ≫ g)`;
* operator-order composition bounds `CategoryTheory.End.comp_dagger_self_comp_le` and
  `CategoryTheory.End.dagger_comp_self_comp_le` in `End X` (whose specializations
  `comp_dagger_self_comp_le f (dagger g)` and `dagger_comp_self_comp_le (dagger f) g` give the
  categorical Cauchy–Schwarz inequalities);
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
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {X Y Z : C}

/-- Congruence `a ↦ End.of (f ≫ a.asHom ≫ dagger f)` sends positive elements of `End Y` to
positive elements of `End X` for any `f : X ⟶ Y`. -/
theorem comp_comp_dagger_nonneg (f : X ⟶ Y) {a : End Y} (ha : 0 ≤ a) :
    0 ≤ End.of (f ≫ a.asHom ≫ dagger f) := by
  simpa using comp_comp_dagger_mono f ha

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` sends positive elements of `End X` to
positive elements of `End Y` for any `g : X ⟶ Y`. -/
theorem dagger_comp_comp_nonneg (g : X ⟶ Y) {a : End X} (ha : 0 ≤ a) :
    0 ≤ End.of (dagger g ≫ a.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_comp_dagger_nonneg (dagger g) ha

/-- Dual congruence `a ↦ End.of (dagger g ≫ a.asHom ≫ g)` is monotone from `End X` to `End Y`. -/
theorem dagger_comp_comp_mono (g : X ⟶ Y) {a b : End X} (hab : a ≤ b) :
    End.of (dagger g ≫ a.asHom ≫ g) ≤ End.of (dagger g ≫ b.asHom ≫ g) := by
  simpa only [dagger_dagger] using comp_comp_dagger_mono (dagger g) hab

/-- Categorical operator-order bound: `End.of ((f ≫ g) ≫ dagger (f ≫ g))` is bounded in `End X` by
`(‖g‖ ^ 2) • End.of (f ≫ dagger f)`. Specializing `g` to `dagger h` gives the operator-order
Cauchy–Schwarz inequality for `f ≫ dagger h`. -/
theorem comp_dagger_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of ((f ≫ g) ≫ dagger (f ≫ g)) ≤ (‖g‖ ^ 2) • End.of (f ≫ dagger f) := by
  simpa only [Category.assoc, dagger_comp, End.norm_of,
    CStarCategory.norm_self_comp_dagger] using
    End.comp_comp_dagger_le_norm_smul f (End.of (g ≫ dagger g))
      (End.self_comp_dagger_nonneg g).isSelfAdjoint

/-- Dual operator-order bound: `End.of (dagger (f ≫ g) ≫ (f ≫ g))` is bounded in `End Z` by
`(‖f‖ ^ 2) • End.of (dagger g ≫ g)`. Specializing `f` to `dagger h` gives the operator-order
Cauchy–Schwarz inequality for `dagger h ≫ g`. -/
theorem dagger_comp_self_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) :
    End.of (dagger (f ≫ g) ≫ (f ≫ g)) ≤ (‖f‖ ^ 2) • End.of (dagger g ≫ g) := by
  simpa only [dagger_comp, dagger_dagger, CStarCategory.norm_dagger] using
    comp_dagger_self_comp_le (dagger g) (dagger f)

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
