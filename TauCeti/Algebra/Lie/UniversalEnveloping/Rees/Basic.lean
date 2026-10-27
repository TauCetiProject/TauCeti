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
coefficientwise membership test is `TauCeti.mem_coeffSubalgebra_iff`.

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
noncomputable def reesParameter : reesAlgebra R L :=
  coeffSubalgebra.monomial (pbwFiltration R L) 1 1 (one_mem_pbwFiltration R L 1)

@[simp]
theorem coe_reesParameter : (reesParameter R L : U[X]) = X := by
  simp [reesParameter, X]

/-- The deformation parameter commutes with every element of the Rees algebra. -/
theorem reesParameter_commute (a : reesAlgebra R L) : Commute (reesParameter R L) a := by
  apply Subtype.ext
  simpa using (Polynomial.X_mul (p := (a : U[X])))

/-- Multiplication by the deformation parameter is injective, even over rings with torsion. -/
theorem reesParameter_mul_injective :
    Function.Injective (fun a : reesAlgebra R L ↦ reesParameter R L * a) := by
  intro a b h
  apply Subtype.ext
  ext n
  have hc := congrArg (fun p : reesAlgebra R L ↦ (p : U[X]).coeff (n + 1)) h
  simpa using hc

/-- The polynomial parameter map sends `X` to the central Rees parameter. -/
noncomputable def reesParameterHom : R[X] →ₐ[R] reesAlgebra R L :=
  Polynomial.aeval (reesParameter R L)

@[simp]
theorem reesParameterHom_X : reesParameterHom R L X = reesParameter R L :=
  Polynomial.aeval_X _

/-- Every scalar polynomial in the deformation parameter is central. -/
theorem reesParameterHom_commute (p : R[X]) (a : reesAlgebra R L) :
    Commute (reesParameterHom R L p) a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_left hq
  | monomial n r =>
    simpa [reesParameterHom, aeval_def] using
      Commute.mul_left (Algebra.commutes r a) ((reesParameter_commute R L a).pow_left n)

/-- The PBW Rees algebra is an algebra over the polynomial parameter ring. -/
noncomputable instance : Algebra R[X] (reesAlgebra R L) :=
  (reesParameterHom R L).toRingHom.toAlgebra' fun p a ↦
    (reesParameterHom_commute R L p a).eq

@[simp]
theorem algebraMap_reesAlgebra (p : R[X]) :
    algebraMap R[X] (reesAlgebra R L) p = reesParameterHom R L p :=
  (rfl)

/-- The parameter-ring algebra structure extends the original coefficient-ring structure. -/
noncomputable instance : IsScalarTower R R[X] (reesAlgebra R L) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ (reesParameterHom R L).commutes r |>.symm

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
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_reesGenerator, coe_reesParameter,
    X, monomial_mul_monomial, ← map_sub, one_mul]
  congr 1
  exact mul_sub_mul_eq_map_ι_lie (AlgHom.id R U) x y

/-- Evaluation of a Rees polynomial at a scalar parameter, as an algebra homomorphism. -/
noncomputable def reesEval (r : R) : reesAlgebra R L →ₐ[R] U :=
  (Polynomial.eval₂AlgHom (AlgHom.id R U) (algebraMap R U r)
    (fun a ↦ (Algebra.commutes r a).symm)).comp (reesAlgebra R L).val

/-- Evaluation at a scalar parameter agrees with ambient polynomial evaluation. -/
theorem reesEval_apply (r : R) (a : reesAlgebra R L) :
    reesEval R L r a = (a : U[X]).eval (algebraMap R U r) :=
  (rfl)

@[simp]
theorem reesEval_monomial (r : R) (n : ℕ) (a : U) (ha : a ∈ pbwFiltration R L n) :
    reesEval R L r (coeffSubalgebra.monomial (pbwFiltration R L) n a ha) =
      a * algebraMap R U r ^ n := by
  simp [reesEval_apply]

@[simp]
theorem reesEval_reesParameter (r : R) :
    reesEval R L r (reesParameter R L) = algebraMap R U r := by
  simp [reesEval_apply]

@[simp]
theorem reesEval_reesGenerator (r : R) (x : L) :
    reesEval R L r (reesGenerator R L x) = r • _root_.UniversalEnvelopingAlgebra.ι R x := by
  simp [reesEval_apply, Algebra.smul_def, Algebra.commutes]

/-- Every enveloping-algebra element is the value at parameter one of a Rees polynomial. -/
theorem reesEval_one_surjective : Function.Surjective (reesEval R L 1) := by
  intro a
  obtain ⟨n, hn⟩ := exists_mem_pbwFiltration R L a
  exact ⟨coeffSubalgebra.monomial (pbwFiltration R L) n a hn, by simp⟩

/-- The parameter and the linear Rees generators generate the PBW Rees algebra over `R`. -/
theorem adjoin_reesParameter_reesGenerator :
    Algebra.adjoin R ({reesParameter R L} ∪ Set.range (reesGenerator R L)) = ⊤ := by
  let S := Algebra.adjoin R ({reesParameter R L} ∪ Set.range (reesGenerator R L))
  have hlinear : ∀ (a : U) (ha : a ∈ pbwFiltration R L 1),
      coeffSubalgebra.monomial (pbwFiltration R L) 1 a ha ∈ S := by
    intro a ha
    have ha' := ha
    rw [pbwFiltration_one] at ha'
    have hmap : ∀ a ∈ (1 : Submodule R U) ⊔
        LinearMap.range (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap,
        monomial 1 a ∈ S.map (reesAlgebra R L).val := by
      intro a ha
      obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
      rw [map_add]
      apply add_mem
      · obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hb
        have ht : reesParameter R L ∈ S := Algebra.subset_adjoin (Or.inl rfl)
        exact ⟨r • reesParameter R L, S.smul_mem ht r, by
          simp [Algebra.smul_def, C_mul_X_eq_monomial]⟩
      · obtain ⟨x, rfl⟩ := hc
        exact ⟨reesGenerator R L x, Algebra.subset_adjoin (Or.inr ⟨x, rfl⟩), by simp⟩
    obtain ⟨p, hp, heq⟩ := hmap a ha'
    have heq' : p = coeffSubalgebra.monomial (pbwFiltration R L) 1 a ha := by
      apply Subtype.ext
      simpa using heq
    exact heq' ▸ hp
  have hgen : Algebra.adjoin R (coeffSubalgebra.grade (pbwFiltration R L) 1 :
      Set (reesAlgebra R L)) = ⊤ := by
    apply coeffSubalgebra.adjoin_grade_one_eq_top_iff.mpr
    intro n
    simp only [pbwFiltration_eq_pow, pow_one, le_refl]
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  intro p hp
  obtain ⟨a, ha, heq⟩ := coeffSubalgebra.mem_grade_iff.mp hp
  have heq' : coeffSubalgebra.monomial (pbwFiltration R L) 1 a ha = p := by
    apply Subtype.ext
    simpa using heq
  exact heq' ▸ hlinear a ha

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
