/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.CategoryTheory.Exact.Resolution.OfChainComplex

/-!
# Finite graded projective resolutions as exact-category resolutions

Given a concrete `TauCeti.GradedProjectiveResolution` whose terms `r.X n` are finitely generated
`A`-modules, this bridge file packages each term in the finite graded projective subcategory
(`TauCeti.GradedProjectiveResolution.finiteProjectiveTerm`) and converts a concrete resolution whose
`(n + 1)`-st term vanishes into an `ExactStructure.FiniteResolution` for the canonical graded
exact structure (`TauCeti.GradedProjectiveResolution.toFiniteResolution`).

Neither `DirectSum.Decomposition`, basis theory, nor the Laurent resolution theorem is needed here;
alternating-sum Cartan class formulas live in
`TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution`.

## Main definitions

* `TauCeti.GradedProjectiveResolution.finiteProjectiveTerm`: the `n`-th finitely generated term
  of a `GradedProjectiveResolution` in the finite graded projective subcategory.
* `TauCeti.GradedProjectiveResolution.toFiniteResolution`: a `GradedProjectiveResolution` with
  finitely generated terms and vanishing `(n + 1)`-st term packaged as an
  `ExactStructure.FiniteResolution`.

## Main results

* `TauCeti.GradedProjectiveResolution.foldAlternating_toFiniteResolution`: computes
  `foldAlternating` along `toFiniteResolution` as a finite alternating sum.
* `TauCeti.GradedProjectiveResolution.gradedFiniteModules_of_finiteResolution`: any graded module
  admitting a finite `gradedFiniteProjectiveModules`-resolution is a finite graded module.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

namespace GradedProjectiveResolution

section Terms

variable {M : GradedModuleCat.{uA} 𝒜}

/-- A finitely generated term of a concrete graded projective resolution, as an object of the
finite graded projective category. -/
def finiteProjectiveTerm
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨r.termObj n, gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective n⟩⟩

/-- The underlying graded object of the finite projective term is the original resolution term. -/
@[simp]
theorem finiteProjectiveTerm_obj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (r.finiteProjectiveTerm n).obj = r.termObj n := (rfl)

/-- The `n`-th finite projective term of a shifted resolution is the `d`-shift of the original
finite projective term. -/
@[simp]
theorem finiteProjectiveTerm_shiftObj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (d : ℤ) (n : ℕ)
    [Module.Finite A (r.X n)] :
    (r.shiftObj d).finiteProjectiveTerm n =
      ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
        gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩ :=
  ObjectProperty.FullSubcategory.ext (by simp)

/-- The `n`-th finite projective term of the tail resolution is the `(n + 1)`-st finite projective
term of `r`. -/
@[simp]
theorem finiteProjectiveTerm_tail
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X (n + 1))] :
    r.tail.finiteProjectiveTerm n = r.finiteProjectiveTerm (n + 1) :=
  ObjectProperty.FullSubcategory.ext (by simp [finiteProjectiveTerm_obj])

end Terms

/-! ### Conversion to finite exact resolutions -/

section FiniteResolution

/-- A concrete graded projective resolution whose terms are finitely generated and whose
`(n + 1)`-st term vanishes, packaged as a finite `gradedFiniteProjectiveModules`-resolution of `M`
for the canonical graded exact structure. -/
noncomputable def toFiniteResolution {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] {n : ℕ} (h : Subsingleton (r.X (n + 1))) :
    (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M := by
  have hK : ∀ i < n, (ShortComplex.mk (r.complex.d (i + 2) (i + 1)) (r.complex.d (i + 1) i)
      (r.complex.d_comp_d _ _ _)).Exact := fun i _ =>
    (HomologicalComplex.exactAt_iff' r.complex (i + 2) (i + 1) i (by simp) (by simp)).mp
      (r.complex_exactAt_succ i)
  have hn : IsZero (r.complex.X (n + 1)) :=
    haveI : Subsingleton (r.complex.X (n + 1)) := h
    GradedModuleCat.isZero_of_subsingleton _
  have : Epi (X := r.complex.X 0) r.augmentation :=
    (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π
  have : (gradedFiniteProjectiveModules 𝒜).IsClosedUnderIsomorphisms :=
    ObjectProperty.isClosedUnderIsomorphisms_of_containsZero _
  have hP : ∀ i ≤ n, gradedFiniteProjectiveModules 𝒜 (r.complex.X i) := fun i _ =>
    gradedFiniteProjectiveModules_iff.mpr
      ⟨inferInstanceAs (Module.Finite A (r.X i)), r.projective i⟩
  exact (GradedExactStructure.abelian_toExactStructure
    (GradedModuleCat.shift (𝒜 := 𝒜))).symm ▸
    ExactStructure.FiniteResolution.ofChainComplex
      r.complex_exact_d_one_zero hK hn hP

/-- Alternating sums along `r.toFiniteResolution h` are alternating sums over the terms
`r.termObj i` for `i : Fin (n + 1)`. -/
theorem foldAlternating_toFiniteResolution {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] {n : ℕ} (h : Subsingleton (r.X (n + 1)))
    {B : Type*} [AddCommGroup B]
    (f : ∀ Z : GradedModuleCat.{uA} 𝒜, gradedFiniteProjectiveModules 𝒜 Z → B)
    (hf : ∀ {Y Z : GradedModuleCat.{uA} 𝒜} (_ : Y ≅ Z)
      (hY : gradedFiniteProjectiveModules 𝒜 Y) (hZ : gradedFiniteProjectiveModules 𝒜 Z),
      f Y hY = f Z hZ) :
    (r.toFiniteResolution h).foldAlternating f =
      ∑ i : Fin (n + 1),
        (-1 : ℤ) ^ (i : ℕ) •
          f (r.termObj i)
            (gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective i⟩) := by
  have : Epi (X := r.complex.X 0) r.augmentation :=
    (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π
  have : (gradedFiniteProjectiveModules 𝒜).IsClosedUnderIsomorphisms :=
    ObjectProperty.isClosedUnderIsomorphisms_of_containsZero _
  have hcast : ∀ {E₁ E₂ : ExactStructure (GradedModuleCat.{uA} 𝒜)} (heq : E₁ = E₂)
      (rf : E₁.FiniteResolution (gradedFiniteProjectiveModules 𝒜) M),
      (heq ▸ rf).foldAlternating f = rf.foldAlternating f := by
    rintro _ _ rfl _
    rfl
  rw [toFiniteResolution, hcast]
  exact ExactStructure.FiniteResolution.foldAlternating_ofChainComplex
    r.complex_exact_d_one_zero _ _ _ f hf

/-- Any graded module admitting a finite resolution by finite graded projectives is a finite
graded module. -/
theorem gradedFiniteModules_of_finiteResolution {M : GradedModuleCat.{uA} 𝒜}
    (rf : (gradedModuleCanonicalExactStructure 𝒜).toExactStructure.FiniteResolution
      (gradedFiniteProjectiveModules 𝒜) M) :
    gradedFiniteModules 𝒜 M := by
  induction rf with
  | base hX => exact gradedFiniteProjectiveModules_le_finiteModules _ hX
  | @step K Q X hQ i p zero hp _ _ =>
    rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure,
      ExactStructure.abelian_conflation] at hp
    have : Module.Finite A Q :=
      gradedFiniteModules_iff.1 (gradedFiniteProjectiveModules_le_finiteModules _ hQ)
    exact gradedFiniteModules_iff.2 <|
      Module.Finite.of_surjective p.hom ((GradedModuleCat.epi_iff_surjective p).1 hp.epi_g)

end FiniteResolution

end GradedProjectiveResolution

end TauCeti
