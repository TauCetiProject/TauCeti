/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Homogenize
import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Fixed-degree homogenization

`TauCeti.fixedHomogenization` identifies `MvPolynomial.restrictTotalDegree σ R d` with
`MvPolynomial.homogeneousSubmodule (Option σ) R d`. The new variable is indexed by `none`, and the
original variables by `some`. The inverse sets the new variable to one, recovering the affine
polynomial on the chart `X none = 1`.

The construction specializes `MvPolynomial.blockHomogenize` to one block and renames its
variables. The degree `d` is fixed in advance: the linear map `TauCeti.fixedHomogenize d` discards
monomials above degree `d` and raises the remaining ones to degree `d` using the new variable.
Multiplication adds the prescribed degrees when each input satisfies its respective degree bound.
The construction works over any commutative semiring and for arbitrary variable types.

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

/-- Fixed-degree homogenization is one-block `MvPolynomial.blockHomogenize` followed by renaming
from `Unit ⊕ σ` to `Option σ`. -/
theorem fixedHomogenize_apply (d : ℕ) (f : MvPolynomial σ R) :
    fixedHomogenize d f = rename (Sum.elim (fun _ : Unit ↦ none) some)
      (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f) := (rfl)

/-- Fixed-degree homogenization always produces a homogeneous form of the prescribed degree. -/
theorem isHomogeneous_fixedHomogenize (d : ℕ) (f : MvPolynomial σ R) :
    (fixedHomogenize d f).IsHomogeneous d := by
  have h := isWeightedHomogeneous_blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f ()
  have h' : (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f).IsHomogeneous d := by
    simpa [IsHomogeneous, ← Pi.one_def] using h
  rw [fixedHomogenize_apply]
  exact h'.rename_isHomogeneous

private theorem mapDomain_unit_apply (a : σ →₀ ℕ) (i : Unit) :
    a.mapDomain (fun _ ↦ ()) i = a.degree := by
  rw [← Finsupp.degree_mapDomain (fun _ : σ ↦ ()) a, Finsupp.degree_eq_sum]
  cases i
  simp

/-- On a bounded input, evaluation after homogenization agrees with evaluation at the original
coordinates if the new coordinate is one. -/
theorem eval₂_fixedHomogenize_of_eq_one {S : Type*} [CommSemiring S] (φ : R →+* S)
    (x : Option σ → S) (hx : x none = 1) {d : ℕ} {f : MvPolynomial σ R}
    (hf : f.totalDegree ≤ d) :
    eval₂ φ x (fixedHomogenize d f) = eval₂ φ (x ∘ some) f := by
  rw [fixedHomogenize_apply, eval₂_rename]
  apply eval₂_blockHomogenize_of_eq_one
  · exact fun _ ↦ hx
  · intro a ha i
    rw [mapDomain_unit_apply, Finsupp.degree_apply]
    exact (le_totalDegree ha).trans hf

/-- Evaluating a homogenized bounded polynomial at a point with new coordinate one recovers its
value on the original coordinates. -/
theorem aeval_fixedHomogenize_of_eq_one {S : Type*} [CommSemiring S] [Algebra R S]
    (x : Option σ → S) (hx : x none = 1) {d : ℕ} {f : MvPolynomial σ R}
    (hf : f.totalDegree ≤ d) :
    aeval x (fixedHomogenize d f) = aeval (x ∘ some) f := by
  simpa only [aeval_def] using eval₂_fixedHomogenize_of_eq_one (algebraMap R S) x hx hf

/-- Setting the homogenizing variable to one recovers every bounded input. -/
@[simp]
theorem aeval_fixedHomogenize_one_X {d : ℕ} {f : MvPolynomial σ R} (hf : f.totalDegree ≤ d) :
    aeval (Option.elim' 1 X) (fixedHomogenize d f) = f :=
  (aeval_fixedHomogenize_of_eq_one (Option.elim' 1 X) rfl hf).trans (aeval_X_left_apply f)

private def unitSumEquivOption (σ : Type*) : Unit ⊕ σ ≃ Option σ :=
  (Equiv.sumComm Unit σ).trans (Equiv.optionEquivSumPUnit.{0, _} σ).symm

private theorem coe_unitSumEquivOption :
    (unitSumEquivOption σ : Unit ⊕ σ → Option σ) = Sum.elim (fun _ ↦ none) some := by
  funext i
  cases i <;> rfl

private theorem mapDomain_unitSumEquivOption_sumElim (b : Unit →₀ ℕ) (a : σ →₀ ℕ) :
    (b.sumElim a).mapDomain (unitSumEquivOption σ) = a.optionElim (b ()) := by
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  cases i <;> simp [unitSumEquivOption]

/-- Every homogeneous form is the fixed-degree homogenization of its affine chart equation. -/
@[simp]
theorem fixedHomogenize_aeval_one_X {d : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous d) : fixedHomogenize d (aeval (Option.elim' 1 X) F) = F := by
  let e := unitSumEquivOption σ
  have hhom : (rename e.symm F).IsHomogeneous d := hF.rename_isHomogeneous
  have hblock : blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d)
      (aeval (Sum.elim (fun _ : Unit ↦ 1) X) (rename e.symm F)) = rename e.symm F := by
    apply blockHomogenize_aeval_one_X
    intro ⟨⟩
    simpa [IsHomogeneous, ← Pi.one_def] using hhom
  have hchart : (Sum.elim (fun _ : Unit ↦ (1 : MvPolynomial σ R)) X) ∘ e.symm =
      Option.elim' 1 X := by
    funext i
    cases i <;> rfl
  rw [aeval_rename, hchart] at hblock
  rw [fixedHomogenize_apply, ← coe_unitSumEquivOption, hblock]
  exact rename_leftInverse e.right_inv F

/-- Fixed-degree homogenization identifies the native bounded polynomial submodule with the
native homogeneous submodule. Its inverse substitutes one for the variable `none`. -/
noncomputable def fixedHomogenization (d : ℕ) :
    restrictTotalDegree σ R d ≃ₗ[R] homogeneousSubmodule (Option σ) R d where
  toFun f := ⟨fixedHomogenize d (f : MvPolynomial σ R),
    (mem_homogeneousSubmodule d _).mpr (isHomogeneous_fixedHomogenize d _)⟩
  invFun F := ⟨aeval (Option.elim' 1 X) (F : MvPolynomial (Option σ) R), by
    apply aeval_mem_restrictTotalDegree
      (fun i ↦ by
        cases i with
        | none => simp
        | some j => exact (isHomogeneous_X R j).totalDegree_le)
      (homogeneousSubmodule_le_restrictTotalDegree (Option σ) R le_rfl F.property)⟩
  left_inv f := Subtype.ext
    (aeval_fixedHomogenize_one_X ((mem_restrictTotalDegree σ d _).mp f.property))
  right_inv F := Subtype.ext
    (fixedHomogenize_aeval_one_X ((mem_homogeneousSubmodule d _).mp F.property))
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

/-- Homogenizing a monomial inserts its slack exponent at `none`, or gives zero if it exceeds
the prescribed degree. -/
theorem fixedHomogenize_monomial (d : ℕ) (a : σ →₀ ℕ) (c : R) :
    fixedHomogenize d (monomial a c) =
      if a.degree ≤ d then monomial (a.optionElim (d - a.degree)) c else 0 := by
  have hexp : (blockHomogenizeExponent (fun _ : σ ↦ ()) (fun _ ↦ d) a).mapDomain
      (unitSumEquivOption σ) = a.optionElim (d - a.degree) := by
    ext i
    rw [Finsupp.mapDomain_equiv_apply]
    cases i <;> simp [unitSumEquivOption, mapDomain_unit_apply]
  rw [fixedHomogenize_apply, ← coe_unitSumEquivOption, blockHomogenize_monomial,
    apply_ite (rename (unitSumEquivOption σ)), rename_monomial, hexp, map_zero]
  simp only [mapDomain_unit_apply, forall_const]

/-- A monomial within the degree bound acquires its slack exponent at `none`. -/
@[simp]
theorem fixedHomogenize_monomial_of_le {d : ℕ} {a : σ →₀ ℕ} (c : R) (ha : a.degree ≤ d) :
    fixedHomogenize d (monomial a c) = monomial (a.optionElim (d - a.degree)) c := by
  rw [fixedHomogenize_monomial, ite_eq_left ha]

/-- A monomial above the degree bound is discarded. -/
@[simp]
theorem fixedHomogenize_monomial_of_lt {d : ℕ} {a : σ →₀ ℕ} (c : R) (ha : d < a.degree) :
    fixedHomogenize d (monomial a c) = 0 := by
  rw [fixedHomogenize_monomial, ite_eq_right ha.not_ge]

/-- At an exponent of degree `d`, the coefficient is the original coefficient after dropping
the exponent at `none`. At any other degree the coefficient is zero. -/
@[simp]
theorem coeff_fixedHomogenize (d : ℕ) (f : MvPolynomial σ R) (u : Option σ →₀ ℕ) :
    (fixedHomogenize d f).coeff u = if u.degree = d then f.coeff u.some else 0 := by
  obtain ⟨a, m, rfl⟩ : ∃ (a : σ →₀ ℕ) (m : ℕ), u = a.optionElim m :=
    ⟨u.some, u none, (Finsupp.optionElim_some u).symm⟩
  have hexp : ((Finsupp.single () m).sumElim a).mapDomain (unitSumEquivOption σ) =
      a.optionElim m := by
    rw [mapDomain_unitSumEquivOption_sumElim, Finsupp.single_eq_same]
  rw [fixedHomogenize_apply, ← coe_unitSumEquivOption, ← hexp,
    coeff_rename_mapDomain _ (unitSumEquivOption σ).injective, coeff_sumElim_blockHomogenize, hexp]
  simp [mapDomain_unit_apply]

/-- Multiplication adds the prescribed homogenizing degrees on bounded inputs. -/
theorem fixedHomogenize_mul {d e : ℕ} {f g : MvPolynomial σ R}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ e) :
    fixedHomogenize (d + e) (f * g) = fixedHomogenize d f * fixedHomogenize e g := by
  have h := fixedHomogenize_aeval_one_X
    ((isHomogeneous_fixedHomogenize d f).mul (isHomogeneous_fixedHomogenize e g))
  rwa [map_mul, aeval_fixedHomogenize_one_X hf, aeval_fixedHomogenize_one_X hg] at h

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

/-- The constant one homogenizes to the prescribed power of `X none`. -/
@[simp]
theorem fixedHomogenize_one (d : ℕ) :
    fixedHomogenize d (1 : MvPolynomial σ R) = X none ^ d := by
  simpa using fixedHomogenize_C (σ := σ) d (1 : R)

/-- In positive degree the homogenization of `X j` is `X (some j)` times the slack power. -/
@[simp]
theorem fixedHomogenize_X {d : ℕ} (hd : d ≠ 0) (j : σ) :
    fixedHomogenize d (X j : MvPolynomial σ R) = X none ^ (d - 1) * X (some j) := by
  rw [X, fixedHomogenize_monomial_of_le _ (by simpa using Nat.one_le_iff_ne_zero.mpr hd)]
  simp only [Finsupp.degree_single, monomial_eq, Finsupp.prod_pow_optionElim,
    Finsupp.prod_single_index, pow_zero, pow_one, map_one, one_mul]

/-- Fixed-degree homogenization commutes with changing coefficients. -/
theorem fixedHomogenize_map {S : Type*} [CommSemiring S] (φ : R →+* S) (d : ℕ)
    (f : MvPolynomial σ R) : fixedHomogenize d (map φ f) = map φ (fixedHomogenize d f) := by
  rw [fixedHomogenize_apply, fixedHomogenize_apply, blockHomogenize_map, map_rename]

/-- Evaluation over the coefficient semiring recovers the original value on the chart
`X none = 1`. -/
@[simp]
theorem eval_fixedHomogenize_optionElim'_one {d : ℕ} {f : MvPolynomial σ R}
    (hf : f.totalDegree ≤ d) (x : σ → R) :
    eval (Option.elim' 1 x) (fixedHomogenize d f) = eval x f := by
  rw [← eval₂_id, eval₂_fixedHomogenize_of_eq_one _ _ rfl hf, eval₂_id]
  rfl

/-! The fixed degree, rather than the degree of the input, controls the power of `X none`. -/

example : fixedHomogenize 2 (1 + X () : MvPolynomial Unit ℤ) =
    X none ^ 2 + X none * X (some ()) := by
  simp

example (c : R) : fixedHomogenize 0 (C c : MvPolynomial σ R) = C c := by simp

example (d : ℕ) : fixedHomogenize d (1 : MvPolynomial (Fin 0) R) = X none ^ d := by
  simp

end TauCeti
