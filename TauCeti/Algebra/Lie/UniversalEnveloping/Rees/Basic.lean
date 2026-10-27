/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra

/-!
# The PBW Rees algebra

The PBW Rees algebra consists of polynomials in a central parameter whose coefficient of
parameter degree `n` lies in PBW filtration degree at most `n`. It retains the filtration
inside the polynomial ring over the possibly noncommutative enveloping algebra.

We use `TauCeti.coeffSubalgebra`, so its grading, homogeneous components, and the linear
equivalence between its degree `n` piece and the `n`-th filtration step are available directly
from `TauCeti.coeffSubalgebra.grade`, `coe_decompose_apply`, and `gradeEquiv`. The
coefficientwise membership test is `TauCeti.mem_coeffSubalgebra_iff`. The shared parameter
API is `TauCeti.coeffSubalgebra.commute_X`, `X_mul_injective`, and `coe_algebraMap`;
scalar evaluation is `TauCeti.coeffSubalgebra.eval`.

The parameter is central and multiplication by it is injective. The linear generators
`j(x) = ι(x)t` satisfy `j(x)j(y) - j(y)j(x) = t j([x,y])`. Evaluation at parameter one
surjects onto the enveloping algebra. These constructions require neither a basis nor
characteristic zero.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17, for the
  PBW filtration and the defining enveloping-algebra relation.
* J. Dixmier, *Enveloping Algebras*, for the Rees construction of a filtered enveloping algebra.
-/

public section

open Polynomial

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The PBW Rees algebra: the coefficient of `tⁿ` belongs to PBW filtration degree `n`. -/
abbrev reesAlgebra : Subalgebra R U[X] :=
  coeffSubalgebra (pbwFiltration R L)

/-- The central deformation parameter of the PBW Rees algebra. -/
noncomputable abbrev reesParameter : reesAlgebra R L :=
  coeffSubalgebra.X (pbwFiltration R L) (one_mem_pbwFiltration R L 1)

/-- The PBW Rees algebra is an algebra over the polynomial parameter ring. -/
noncomputable instance : Algebra R[X] (reesAlgebra R L) :=
  coeffSubalgebra.algebra (pbwFiltration R L) (one_mem_pbwFiltration R L 1)

/-- The parameter-ring algebra structure extends the original coefficient-ring structure. -/
noncomputable instance : IsScalarTower R R[X] (reesAlgebra R L) :=
  coeffSubalgebra.isScalarTower (pbwFiltration R L) (one_mem_pbwFiltration R L 1)

/-- The linear Rees generator `j(x) = ι(x)t`. -/
noncomputable def reesGenerator : L →ₗ[R] reesAlgebra R L :=
  LinearMap.codRestrict (reesAlgebra R L).toSubmodule
    (((Polynomial.monomial 1).restrictScalars R).comp
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap) fun x ↦
      monomial_mem_coeffSubalgebra_iff.mpr (ι_mem_pbwFiltration_one R L x)

@[simp]
theorem coe_reesGenerator (x : L) :
    (reesGenerator R L x : U[X]) = monomial 1 (_root_.UniversalEnvelopingAlgebra.ι R x) :=
  (rfl)

/-- The commutator of Rees generators has one factor of the deformation parameter. -/
theorem reesGenerator_mul_sub_mul (x y : L) :
    reesGenerator R L x * reesGenerator R L y -
        reesGenerator R L y * reesGenerator R L x =
      reesParameter R L * reesGenerator R L ⁅x, y⁆ := by
  apply Subtype.ext
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_reesGenerator, coeffSubalgebra.coe_X,
    ← monomial_one_one_eq_X, monomial_mul_monomial, ← map_sub, one_mul]
  congr 1
  exact mul_sub_mul_eq_map_ι_lie (AlgHom.id R U) x y

@[simp]
theorem eval_reesGenerator (r : R) (x : L) :
    coeffSubalgebra.eval (pbwFiltration R L) r (reesGenerator R L x) =
      r • _root_.UniversalEnvelopingAlgebra.ι R x := by
  simp [coeffSubalgebra.eval_apply, Algebra.smul_def, Algebra.commutes]

/-- Every enveloping-algebra element is the value at parameter one of a Rees polynomial. -/
theorem evalOne_surjective :
    Function.Surjective (coeffSubalgebra.evalOne (pbwFiltration R L)) :=
  coeffSubalgebra.evalOne_surjective _ (iSup_pbwFiltration_eq_top R L)

/-- The degree-one piece is spanned by the parameter and the linear Rees generators. -/
theorem grade_one_le_span_reesParameter_reesGenerator :
    coeffSubalgebra.grade (pbwFiltration R L) 1 ≤
      Submodule.span R ({reesParameter R L} ∪ Set.range (reesGenerator R L)) := by
  intro p hp
  obtain ⟨a, ha, heq⟩ := coeffSubalgebra.mem_grade_iff.mp hp
  obtain rfl : p = coeffSubalgebra.monomial (pbwFiltration R L) 1 a ha :=
    Subtype.ext (by simpa using heq.symm)
  rw [pbwFiltration_one] at ha
  obtain ⟨b, hb, c, hc, heq⟩ := Submodule.mem_sup.mp ha
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hb
  obtain ⟨x, rfl⟩ := hc
  have hdecomp : coeffSubalgebra.monomial (pbwFiltration R L) 1 a
      (by rwa [pbwFiltration_one]) = r • reesParameter R L + reesGenerator R L x := by
    apply Subtype.ext
    simp [← heq, Algebra.smul_def, C_mul_X_eq_monomial]
  rw [hdecomp]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ r (Submodule.subset_span (Or.inl rfl)))
    (Submodule.subset_span (Or.inr ⟨x, rfl⟩))

/-- The parameter and the linear Rees generators generate the PBW Rees algebra over `R`. -/
theorem adjoin_reesParameter_reesGenerator :
    Algebra.adjoin R ({reesParameter R L} ∪ Set.range (reesGenerator R L)) = ⊤ := by
  have hgen : Algebra.adjoin R (coeffSubalgebra.grade (pbwFiltration R L) 1 :
      Set (reesAlgebra R L)) = ⊤ := by
    apply coeffSubalgebra.adjoin_grade_one_eq_top_iff.mpr
    intro n
    simp only [pbwFiltration_eq_pow, pow_one, le_refl]
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  have hspan : Submodule.span R ({reesParameter R L} ∪ Set.range (reesGenerator R L)) ≤
      (Algebra.adjoin R ({reesParameter R L} ∪ Set.range (reesGenerator R L))).toSubmodule :=
    Submodule.span_le.mpr Algebra.subset_adjoin
  exact fun _ hp ↦ hspan (grade_one_le_span_reesParameter_reesGenerator R L hp)

/-- Over the parameter ring, the linear Rees generators alone generate the Rees algebra. -/
theorem adjoin_reesGenerator :
    Algebra.adjoin R[X] (Set.range (reesGenerator R L)) = ⊤ := by
  have hle : Algebra.adjoin R ({reesParameter R L} ∪ Set.range (reesGenerator R L)) ≤
      (Algebra.adjoin R[X] (Set.range (reesGenerator R L))).restrictScalars R := by
    apply Algebra.adjoin_le
    rintro a (ha | ha)
    · obtain rfl := Set.mem_singleton_iff.mp ha
      simpa using (Algebra.adjoin R[X] (Set.range (reesGenerator R L))).algebraMap_mem X
    · exact Algebra.subset_adjoin ha
  rw [adjoin_reesParameter_reesGenerator] at hle
  exact top_unique hle

end TauCeti.UniversalEnvelopingAlgebra
