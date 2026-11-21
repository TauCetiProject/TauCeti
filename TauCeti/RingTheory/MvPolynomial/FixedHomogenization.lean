/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Fixed-degree homogenization

Polynomials of total degree at most `d` are linearly equivalent to homogeneous forms of degree
`d` after adjoining one variable. The new variable is indexed by `none`, and the original
variables by `some`. The inverse sets the new variable to one. This identifies affine
coefficient spaces with homogeneous forms without changing the native polynomial carriers.

The construction specializes `MvPolynomial.blockHomogenize` to one block and renames its
variables. It works over commutative semirings, including the zero semiring, and with arbitrary
variable types. The degree is fixed in advance, not taken to be the degree of the input;
thus the construction is linear. Multiplication adds the prescribed degrees.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), §3, pp. 491–493.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Fixed-degree homogenization, discarding monomials above degree `d`. The variable `none`
has the slack exponent and `some j` retains the exponent of `j`. -/
noncomputable def fixedHomogenize (d : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial (Option σ) R where
  toFun f := rename (Sum.elim (fun _ : Unit ↦ none) some)
    (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f)
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The one-block supplier formula for fixed-degree homogenization. -/
theorem fixedHomogenize_apply (d : ℕ) (f : MvPolynomial σ R) :
    fixedHomogenize d f = rename (Sum.elim (fun _ : Unit ↦ none) some)
      (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f) := (rfl)

/-- Fixed-degree homogenization always produces a homogeneous form of the prescribed degree. -/
theorem isHomogeneous_fixedHomogenize (d : ℕ) (f : MvPolynomial σ R) :
    (fixedHomogenize d f).IsHomogeneous d := by
  have h := isWeightedHomogeneous_blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f ()
  have h' : (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f).IsHomogeneous d := by
    simpa [IsHomogeneous, ← Pi.one_def] using h
  exact h'.rename_isHomogeneous

/-- Setting the homogenizing variable to one recovers every bounded input. -/
@[simp]
theorem aeval_fixedHomogenize (d : ℕ) (f : restrictTotalDegree σ R d) :
    aeval (Option.elim' 1 X) (fixedHomogenize d (f : MvPolynomial σ R)) =
      (f : MvPolynomial σ R) := by
  have hchart : (Option.elim' (1 : MvPolynomial σ R) X) ∘
      Sum.elim (fun _ : Unit ↦ none) some = Sum.elim (fun _ ↦ 1) X := by
    funext i
    cases i <;> rfl
  rw [fixedHomogenize_apply, aeval_rename, hchart]
  apply aeval_blockHomogenize_one_X
  intro a ha ⟨⟩
  have hdeg := Finsupp.degree_mapDomain (fun _ : σ ↦ ()) a
  simp only [Finsupp.degree_eq_sum, Finset.univ_unique, Finset.sum_singleton] at hdeg
  exact hdeg.trans_le ((le_totalDegree ha).trans ((mem_restrictTotalDegree σ d _).mp f.2))

/-- Every homogeneous form is the fixed-degree homogenization of its affine chart equation. -/
@[simp]
theorem fixedHomogenize_aeval (d : ℕ) (F : homogeneousSubmodule (Option σ) R d) :
    fixedHomogenize d (aeval (Option.elim' 1 X) (F : MvPolynomial (Option σ) R)) =
      (F : MvPolynomial (Option σ) R) := by
  let g : Unit ⊕ σ → Option σ := Sum.elim (fun _ ↦ none) some
  let h : Option σ → Unit ⊕ σ := Option.elim' (.inl ()) Sum.inr
  have hrename : rename g (rename h (F : MvPolynomial (Option σ) R)) =
      (F : MvPolynomial (Option σ) R) := by
    rw [rename_rename]
    convert rename_id_apply (F : MvPolynomial (Option σ) R) using 1
    congr 2
    funext i
    cases i <;> rfl
  have hF : (rename h (F : MvPolynomial (Option σ) R)).IsHomogeneous d :=
    F.2.rename_isHomogeneous
  have hblock : blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d)
      (aeval (Sum.elim (fun _ : Unit ↦ 1) X) (rename h (F : MvPolynomial (Option σ) R))) =
        rename h (F : MvPolynomial (Option σ) R) := by
    apply blockHomogenize_aeval_one_X
    intro ⟨⟩
    simpa [IsHomogeneous, ← Pi.one_def] using hF
  have hchart : (Sum.elim (fun _ : Unit ↦ (1 : MvPolynomial σ R)) X) ∘ h =
      Option.elim' 1 X := by
    funext i
    cases i <;> rfl
  rw [aeval_rename, hchart] at hblock
  rw [fixedHomogenize_apply, hblock]
  exact hrename

/-- Fixed-degree homogenization identifies the native bounded polynomial submodule with the
native homogeneous submodule. Its inverse substitutes one for the variable `none`. -/
noncomputable def fixedHomogenization (d : ℕ) :
    restrictTotalDegree σ R d ≃ₗ[R] homogeneousSubmodule (Option σ) R d where
  toFun f := ⟨fixedHomogenize d (f : MvPolynomial σ R), isHomogeneous_fixedHomogenize d _⟩
  invFun F := ⟨aeval (Option.elim' 1 X) (F : MvPolynomial (Option σ) R), by
    apply aeval_mem_restrictTotalDegree
      (fun i ↦ by
        cases i with
        | none => simp
        | some j => exact (isHomogeneous_X R j).totalDegree_le)
      (homogeneousSubmodule_le_restrictTotalDegree (Option σ) R le_rfl F.2)⟩
  left_inv f := Subtype.ext (aeval_fixedHomogenize d f)
  right_inv F := Subtype.ext (fixedHomogenize_aeval d F)
  map_add' f g := Subtype.ext (map_add (fixedHomogenize d) _ _)
  map_smul' c f := Subtype.ext (map_smul (fixedHomogenize d) _ _)

/-- The underlying polynomial of the fixed-degree equivalence is fixed homogenization. -/
@[simp]
theorem coe_fixedHomogenization (d : ℕ) (f : restrictTotalDegree σ R d) :
    (fixedHomogenization d f : MvPolynomial (Option σ) R) =
      fixedHomogenize d (f : MvPolynomial σ R) := (rfl)

/-- The inverse equivalence sets the homogenizing coordinate to one. -/
@[simp]
theorem coe_fixedHomogenization_symm (d : ℕ) (F : homogeneousSubmodule (Option σ) R d) :
    ((fixedHomogenization d).symm F : MvPolynomial σ R) =
      aeval (Option.elim' 1 X) (F : MvPolynomial (Option σ) R) := (rfl)

/-- Homogenizing an admissible monomial inserts exactly its slack exponent at `none`. -/
@[simp]
theorem fixedHomogenize_monomial (d : ℕ) (a : σ →₀ ℕ) (c : R) (ha : a.degree ≤ d) :
    fixedHomogenize d (monomial a c) = monomial (a.optionElim (d - a.degree)) c := by
  have hm : (monomial (a.optionElim (d - a.degree)) c).IsHomogeneous d :=
    isHomogeneous_monomial c (by simp [Nat.sub_add_cancel ha])
  have h := fixedHomogenize_aeval d ⟨_, hm⟩
  simp only [aeval_monomial, Finsupp.prod_pow_optionElim, Option.elim'_none,
    Option.elim'_some, one_pow, one_mul, algebraMap_eq] at h
  simpa only [← monomial_eq] using h

/-- The coefficient of a homogeneous exponent is the original affine coefficient exactly
when the exponent has the prescribed degree, and is zero otherwise. -/
@[simp]
theorem coeff_fixedHomogenize (d : ℕ) (f : MvPolynomial σ R) (a : σ →₀ ℕ) (m : ℕ) :
    (fixedHomogenize d f).coeff (a.optionElim m) =
      if m + a.degree = d then f.coeff a else 0 := by
  let g : Unit ⊕ σ → Option σ := Sum.elim (fun _ ↦ none) some
  have hg : Function.Injective g := by
    rintro (⟨⟩ | i) (⟨⟩ | j) h <;> simp_all [g]
  have hexp : a.optionElim m = ((Finsupp.single () m).sumElim a).mapDomain g := by
    ext i
    cases i with
    | none =>
      simpa [g] using (Finsupp.mapDomain_apply_of_injective hg
        ((Finsupp.single () m).sumElim a) (.inl ())).symm
    | some j =>
      simpa [g] using (Finsupp.mapDomain_apply_of_injective hg
        ((Finsupp.single () m).sumElim a) (.inr j)).symm
  have hdeg := Finsupp.degree_mapDomain (fun _ : σ ↦ ()) a
  simp only [Finsupp.degree_eq_sum, Finset.univ_unique, Finset.sum_singleton] at hdeg
  rw [fixedHomogenize_apply, hexp, coeff_rename_mapDomain _ hg,
    coeff_sumElim_blockHomogenize]
  simp [hdeg]

/-- Multiplication adds the prescribed homogenizing degrees on bounded inputs. -/
theorem fixedHomogenize_mul (d e : ℕ) (f : restrictTotalDegree σ R d)
    (g : restrictTotalDegree σ R e) :
    fixedHomogenize (d + e) ((f : MvPolynomial σ R) * (g : MvPolynomial σ R)) =
      fixedHomogenize d (f : MvPolynomial σ R) * fixedHomogenize e (g : MvPolynomial σ R) := by
  have h := fixedHomogenize_aeval (d + e)
    ⟨_, (isHomogeneous_fixedHomogenize d (f : MvPolynomial σ R)).mul
      (isHomogeneous_fixedHomogenize e (g : MvPolynomial σ R))⟩
  simpa only [map_mul, aeval_fixedHomogenize] using h

/-- Constants homogenize to a scalar multiple of the prescribed power of `X none`. -/
@[simp]
theorem fixedHomogenize_C (d : ℕ) (c : R) :
    fixedHomogenize d (C c : MvPolynomial σ R) = C c * X none ^ d := by
  simp [fixedHomogenize_apply]

/-- In degree zero, homogenization keeps exactly the constant coefficient. -/
@[simp]
theorem fixedHomogenize_degree_zero (f : MvPolynomial σ R) :
    fixedHomogenize 0 f = C (f.coeff 0) := by
  simp [fixedHomogenize_apply, ← Pi.zero_def]

/-- Evaluating a homogenized bounded polynomial on the chart `X none = 1` gives its original
value, also at points over a coefficient algebra. -/
theorem aeval_fixedHomogenize_chart {S : Type*} [CommSemiring S] [Algebra R S]
    (d : ℕ) (f : restrictTotalDegree σ R d) (x : σ → S) :
    aeval (Option.elim' 1 x) (fixedHomogenize d (f : MvPolynomial σ R)) =
      aeval x (f : MvPolynomial σ R) := by
  have h := congrArg (aeval x) (aeval_fixedHomogenize d f)
  rw [comp_aeval_apply] at h
  convert h using 2
  congr 1
  funext i
  cases i <;> simp

/-! The fixed degree, rather than the degree of the input, controls the power of `X none`. -/

example : fixedHomogenize 2 (1 + X () : MvPolynomial Unit ℤ) =
    X none ^ 2 + X none * X (some ()) := by
  have hmono := fixedHomogenize_monomial 2 (Finsupp.single () 1) (1 : ℤ) (by simp)
  have hexp : (Finsupp.single () 1).optionElim (2 - (Finsupp.single () 1).degree) =
      Finsupp.single none 1 + Finsupp.single (some ()) 1 := by
    ext i
    cases i <;> simp
  rw [hexp, monomial_add_single] at hmono
  rw [← X, ← X, pow_one] at hmono
  have hone : fixedHomogenize 2 (1 : MvPolynomial Unit ℤ) = X none ^ 2 := by
    simpa using fixedHomogenize_C (σ := Unit) 2 (1 : ℤ)
  rw [map_add, hone, hmono]

example (c : R) : fixedHomogenize 0 (C c : MvPolynomial σ R) = C c := by simp

example (d : ℕ) : fixedHomogenize d (1 : MvPolynomial (Fin 0) R) = X none ^ d := by
  simpa using fixedHomogenize_C (σ := Fin 0) d (1 : R)

end TauCeti
