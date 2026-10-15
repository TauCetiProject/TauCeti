/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The graded subalgebra of `B[X]` cut out by a graded family of coefficients

Let `B` be an `R`-algebra and let `M : ℕ → Submodule R B` be a graded family of submodules:
`1 ∈ M 0` and `M m * M n ⊆ M (m + n)` (`SetLike.GradedMonoid M`). The polynomials `∑ bₙ Xⁿ` with
`bₙ ∈ M n` for every `n` form an `R`-subalgebra `TauCeti.coeffSubalgebra M` of `B[X]`: it is the
direct sum `⨁ₙ Mₙ Xⁿ`, realized inside `B[X]` so that elements of different degrees that are equal
in `B` stay apart. This file grades it by the power of `X`: the degree `n` piece consists of the
monomials `b Xⁿ` with `b ∈ M n`, and the homogeneous components of a polynomial are its monomials.

Two instances motivate the construction. For an ideal `I` of a commutative ring `R` and
`M n = Iⁿ` it is Mathlib's Rees algebra `reesAlgebra I`, whose grading in
`TauCeti.RingTheory.ReesAlgebra.Grading` is the one constructed here. For a divisor `D` of an
algebraic function field and `M n = L(nD)` it is the section ring `⨁ₙ L(nD)` of `D`
(`TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing`), the graded ring from which
projective models of a curve are built as `Proj`.

## Main definitions

* `TauCeti.coeffSubalgebra M`: the polynomials whose `n`-th coefficient lies in `M n`.
* `TauCeti.coeffSubalgebra.monomial M n b hb`: the monomial `b Xⁿ`, for `b ∈ M n`.
* `TauCeti.coeffSubalgebra.grade M n`: the degree `n` piece, the monomials `b Xⁿ` with `b ∈ M n`.
* `TauCeti.coeffSubalgebra.gradedAlgebra`: the `GradedAlgebra` instance.

## Main results

* `TauCeti.coeffSubalgebra.mem_grade_iff_monomial_coeff`: an element has degree `n` exactly when
  it is the monomial of degree `n` formed by its `n`-th coefficient.
* `TauCeti.coeffSubalgebra.coeff_eq_zero_iff_of_mem_grade`: an element of degree `n` vanishes
  exactly when its `n`-th coefficient does.
* `TauCeti.coeffSubalgebra.isInternal_grade`: the subalgebra is the internal direct sum of its
  graded pieces.
* `TauCeti.coeffSubalgebra.coe_decompose_apply`: the degree `n` component of `f` is the monomial
  `f.coeff n • Xⁿ`.
-/

public section

open Polynomial DirectSum

namespace TauCeti

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  (M : ℕ → Submodule R B) [SetLike.GradedMonoid M]

/-- The `R`-subalgebra of `B[X]` of polynomials whose `n`-th coefficient lies in `M n`, for a
graded family `M` of submodules of `B`: the direct sum `⨁ₙ Mₙ Xⁿ` realized inside `B[X]`. -/
def coeffSubalgebra : Subalgebra R B[X] where
  carrier := {f | ∀ n, f.coeff n ∈ M n}
  mul_mem' {f g} hf hg n := by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun x hx ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hx]
    exact SetLike.mul_mem_graded (hf x.1) (hg x.2)
  add_mem' {f g} hf hg n := by
    rw [coeff_add]
    exact add_mem (hf n) (hg n)
  algebraMap_mem' r n := by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r SetLike.GradedOne.one_mem
    · exact zero_mem _

variable {M}

@[simp]
theorem mem_coeffSubalgebra_iff {f : B[X]} : f ∈ coeffSubalgebra M ↔ ∀ n, f.coeff n ∈ M n :=
  Iff.rfl

/-- A monomial `b Xⁿ` lies in `coeffSubalgebra M` exactly when `b ∈ M n`. -/
theorem monomial_mem_coeffSubalgebra_iff {n : ℕ} {b : B} :
    Polynomial.monomial n b ∈ coeffSubalgebra M ↔ b ∈ M n := by
  refine ⟨fun h ↦ by simpa using h n, fun hb m ↦ ?_⟩
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ hb
  · exact zero_mem _

namespace coeffSubalgebra

variable (M) in
/-- The monomial `b Xⁿ` of `coeffSubalgebra M`, for `b ∈ M n`. -/
noncomputable def monomial (n : ℕ) (b : B) (hb : b ∈ M n) : coeffSubalgebra M :=
  ⟨Polynomial.monomial n b, monomial_mem_coeffSubalgebra_iff.mpr hb⟩

@[simp]
theorem coe_monomial (n : ℕ) (b : B) (hb : b ∈ M n) :
    (monomial M n b hb : B[X]) = Polynomial.monomial n b :=
  (rfl)

/-- The monomial formed by any single coefficient of an element of `coeffSubalgebra M` lies in
`coeffSubalgebra M`. -/
theorem monomial_coeff_mem (f : coeffSubalgebra M) (n : ℕ) :
    Polynomial.monomial n ((f : B[X]).coeff n) ∈ coeffSubalgebra M :=
  monomial_mem_coeffSubalgebra_iff.mpr (f.2 n)

variable (M) in
/-- The degree `n` piece of `coeffSubalgebra M`: the monomials `b Xⁿ` with `b ∈ M n`. -/
noncomputable def grade (n : ℕ) : Submodule R (coeffSubalgebra M) :=
  Submodule.comap (coeffSubalgebra M).val.toLinearMap
    (Submodule.map ((Polynomial.monomial n).restrictScalars R) (M n))

/-- The elements of degree `n` of `coeffSubalgebra M` are the monomials `b Xⁿ` with `b ∈ M n`. -/
theorem mem_grade_iff {n : ℕ} {f : coeffSubalgebra M} :
    f ∈ grade M n ↔ ∃ b ∈ M n, Polynomial.monomial n b = (f : B[X]) :=
  Iff.rfl

/-- An element of `coeffSubalgebra M` has degree `n` exactly when it is the monomial of degree `n`
formed by its `n`-th coefficient. -/
theorem mem_grade_iff_monomial_coeff {n : ℕ} {f : coeffSubalgebra M} :
    f ∈ grade M n ↔ Polynomial.monomial n ((f : B[X]).coeff n) = f := by
  refine ⟨fun hf ↦ ?_, fun h ↦ mem_grade_iff.mpr ⟨_, f.2 n, h⟩⟩
  obtain ⟨b, -, hb⟩ := mem_grade_iff.mp hf
  rw [← hb, coeff_monomial_same]

/-- The monomial `b Xⁿ` with `b ∈ M n` has degree `n`. -/
theorem monomial_mem_grade (n : ℕ) (b : B) (hb : b ∈ M n) : monomial M n b hb ∈ grade M n :=
  mem_grade_iff.mpr ⟨b, hb, rfl⟩

/-- The coefficients of an element of degree `n` vanish away from `n`. -/
theorem coeff_eq_zero_of_mem_grade {m n : ℕ} {f : coeffSubalgebra M} (hf : f ∈ grade M n)
    (hmn : m ≠ n) : (f : B[X]).coeff m = 0 := by
  rw [← mem_grade_iff_monomial_coeff.mp hf, coeff_monomial_of_ne _ hmn]

/-- An element of degree `n` vanishes exactly when its `n`-th coefficient does. -/
theorem coeff_eq_zero_iff_of_mem_grade {n : ℕ} {f : coeffSubalgebra M} (hf : f ∈ grade M n) :
    (f : B[X]).coeff n = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, ZeroMemClass.coe_zero, coeff_zero]⟩
  ext1
  rw [← mem_grade_iff_monomial_coeff.mp hf, h, map_zero, ZeroMemClass.coe_zero]

/-- Evaluating an element of degree `n` at `X = 1` gives its `n`-th coefficient. -/
theorem eval_one_of_mem_grade {n : ℕ} {f : coeffSubalgebra M} (hf : f ∈ grade M n) :
    (f : B[X]).eval 1 = (f : B[X]).coeff n := by
  rw [← mem_grade_iff_monomial_coeff.mp hf, eval_monomial, one_pow, mul_one, coeff_monomial_same]

instance gradedMonoid : SetLike.GradedMonoid (grade M) where
  one_mem := mem_grade_iff.mpr ⟨1, SetLike.GradedOne.one_mem, by simp [monomial_zero_left]⟩
  mul_mem m n f g hf hg := by
    obtain ⟨b, hb, hf⟩ := mem_grade_iff.mp hf
    obtain ⟨c, hc, hg⟩ := mem_grade_iff.mp hg
    exact mem_grade_iff.mpr ⟨b * c, SetLike.mul_mem_graded hb hc, by
      rw [Subalgebra.coe_mul, ← hf, ← hg, monomial_mul_monomial]⟩

/-- The degree `n` component of an element of `coeffSubalgebra M`: the monomial of degree `n`
formed by its `n`-th coefficient. -/
private noncomputable def component (n : ℕ) (f : coeffSubalgebra M) : grade M n :=
  ⟨⟨Polynomial.monomial n ((f : B[X]).coeff n), monomial_coeff_mem f n⟩,
    monomial_mem_grade n _ (f.2 n)⟩

private theorem component_add (n : ℕ) (f g : coeffSubalgebra M) :
    component n (f + g) = component n f + component n g := by
  ext1; ext1
  simp [component]

private theorem component_of_mem {m n : ℕ} {f : coeffSubalgebra M} (hf : f ∈ grade M m) :
    component n f = if h : m = n then h ▸ ⟨f, hf⟩ else 0 := by
  split_ifs with h
  · subst h
    exact Subtype.ext (Subtype.ext (mem_grade_iff_monomial_coeff.mp hf))
  · ext1; ext1
    simp [component, coeff_eq_zero_of_mem_grade hf (Ne.symm h)]

/-- The decomposition of an element of `coeffSubalgebra M` into its homogeneous components. -/
private noncomputable def decomposeAux (f : coeffSubalgebra M) : ⨁ n, grade M n :=
  ∑ n ∈ (f : B[X]).support, of (fun n ↦ grade M n) n (component n f)

private theorem decomposeAux_apply (f : coeffSubalgebra M) (n : ℕ) :
    decomposeAux f n = component n f := by
  classical
  rw [decomposeAux, DFinsupp.finsetSum_apply]
  simp_rw [of_apply]
  rw [Finset.sum_dite_eq']
  split_ifs with h
  · rfl
  · ext1; ext1
    simp [component, notMem_support_iff.mp h]

private theorem coe_decomposeAux (f : coeffSubalgebra M) :
    DirectSum.coeAddMonoidHom (fun n ↦ grade M n) (decomposeAux f) = f := by
  rw [decomposeAux, map_sum]
  simp_rw [coeAddMonoidHom_of]
  ext1
  rw [AddSubmonoidClass.coe_finsetSum]
  exact ((f : B[X]).as_sum_support).symm

private theorem decomposeAux_coe (x : ⨁ n, grade M n) :
    decomposeAux (DirectSum.coeAddMonoidHom (fun n ↦ grade M n) x) = x := by
  ext n : 1
  rw [decomposeAux_apply]
  induction x using DirectSum.induction_on with
  | zero => ext1; ext1; simp [component]
  | of m y =>
    rw [coeAddMonoidHom_of, component_of_mem y.2, of_apply]
  | add x y hx hy => rw [map_add, component_add, hx, hy, add_apply]

variable (M) in
/-- `coeffSubalgebra M` is the internal direct sum of its graded pieces. -/
theorem isInternal_grade : IsInternal (grade M) :=
  Function.bijective_iff_has_inverse.mpr ⟨decomposeAux, decomposeAux_coe, coe_decomposeAux⟩

/-- The grading of `coeffSubalgebra M` by the power of `X`. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grade M) :=
  (isInternal_grade M).gradedAlgebra

/-- The degree `n` component of an element `f` of `coeffSubalgebra M` is the monomial
`f.coeff n • Xⁿ`. -/
@[simp]
theorem coe_decompose_apply (f : coeffSubalgebra M) (n : ℕ) :
    ((decompose (grade M) f n : coeffSubalgebra M) : B[X]) =
      Polynomial.monomial n ((f : B[X]).coeff n) := by
  have : decompose (grade M) f = decomposeAux f :=
    (isInternal_grade M).1 <| by
      rw [coe_decomposeAux]
      exact (decompose (grade M)).symm_apply_apply f
  rw [this, decomposeAux_apply]
  rfl

end coeffSubalgebra

end TauCeti
