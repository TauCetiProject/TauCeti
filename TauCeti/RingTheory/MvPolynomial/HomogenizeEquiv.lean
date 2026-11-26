/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Homogenize
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Fixed-degree homogenization of bounded-degree polynomials

Adjoin one homogenizing variable `X₀`, the variable `none`, to the affine variables `Xⱼ`, the
variables `some j`. Homogenization in degree `d` sends a polynomial `f` of total degree at most
`d` to the form `X₀ᵈ f(X / X₀)` of degree `d`: the monomial `c Xᵅ` with `|α| ≤ d` becomes
`c X₀^(d - |α|) Xᵅ`. It is the one-block case of `MvPolynomial.blockHomogenize`, with the block
variable renamed to `none` and the affine variables to `some`.

Homogenization in degree `d` is a linear equivalence `MvPolynomial.homogenizeEquiv σ R d` from the
polynomials of total degree at most `d` onto the homogeneous polynomials of degree `d`, whose
inverse sets `X₀ = 1`. It identifies the coefficient space of bounded affine polynomials with the
space of forms of degree `d` in one more variable, and it turns products of bounded polynomials
into products of forms, `H_{d+e}(f g) = H_d(f) H_e(g)`.

## Main definitions

* `MvPolynomial.homogenizeEquiv σ R d`: homogenization in degree `d`, as a linear equivalence
  between `restrictTotalDegree σ R d` and `homogeneousSubmodule (Option σ) R d`.

## Main results

* `MvPolynomial.homogenizeEquiv_monomial`: `c Xᵅ` maps to `c X₀^(d - |α|) Xᵅ`.
* `MvPolynomial.coeff_homogenizeEquiv`: the coefficients of a homogenization are those of the
  original polynomial, at the exponents of degree `d`.
* `MvPolynomial.coe_homogenizeEquiv_symm_apply`: the inverse sets `X₀ = 1`.
* `MvPolynomial.homogenizeEquiv_mul`: homogenization is multiplicative, adding the degrees.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), §3.
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ R : Type*} [CommSemiring R]

/-- The variables `Option σ` as the one-block variables `Unit ⊕ σ`: `none` is the homogenizing
variable and `some j` is the affine variable `j`. -/
private def homogenizeVarEquiv : Option σ ≃ Unit ⊕ σ :=
  (Equiv.optionEquivSumPUnit σ).trans (Equiv.sumComm _ _)

private theorem coe_homogenizeVarEquiv_symm :
    ⇑(homogenizeVarEquiv (σ := σ)).symm = Sum.elim (fun _ ↦ none) some := by
  funext v
  rcases v with ⟨⟩ | j <;> rfl

private theorem sumElim_none_some_injective :
    Function.Injective (Sum.elim (fun _ : Unit ↦ (none : Option σ)) some) := by
  rw [← coe_homogenizeVarEquiv_symm]
  exact Equiv.injective _

private theorem option_elim_comp_sumElim {S : Type*} [One S] (x : σ → S) :
    Option.elim' 1 x ∘ Sum.elim (fun _ : Unit ↦ none) some = Sum.elim (fun _ : Unit ↦ 1) x := by
  funext v
  rcases v with ⟨⟩ | j <;> rfl

/-- With a single block, block homogeneity is ordinary homogeneity. -/
private theorem isWeightedHomogeneous_unit_iff {F : MvPolynomial (Unit ⊕ σ) R} {d : ℕ} :
    F.IsWeightedHomogeneous
        (fun v ↦ if Sum.elim id (fun _ : σ ↦ ()) v = () then 1 else 0) d ↔
      F.IsHomogeneous d := by
  -- Every variable lies in the single block, so the block weight is the constant weight `1`.
  have hw : (fun v : Unit ⊕ σ ↦ if Sum.elim id (fun _ : σ ↦ ()) v = () then 1 else 0) =
      (1 : Unit ⊕ σ → ℕ) :=
    _root_.funext fun _ ↦ by simp
  rw [hw]
  rfl

/-- Renamed to `Option σ`, the exponent of the one-block homogenization of `Xᵅ` in degree `d` is
`α` with `d - |α|` at `none`. -/
private theorem mapDomain_blockHomogenizeExponent_unit (d : ℕ) (s : σ →₀ ℕ) :
    (blockHomogenizeExponent (fun _ : σ ↦ ()) (fun _ ↦ d) s).mapDomain
        (Sum.elim (fun _ ↦ none) some) = single none (d - s.degree) + s.mapDomain some := by
  ext v
  rcases v with _ | j
  · refine (mapDomain_apply_of_injective sumElim_none_some_injective _ (Sum.inl ())).trans ?_
    simp [mapDomain_apply_eq_degree, mapDomain_of_notMem_range]
  · refine (mapDomain_apply_of_injective sumElim_none_some_injective _ (Sum.inr j)).trans ?_
    simp [mapDomain_apply_of_injective (Option.some_injective σ)]

/-- The underlying polynomial map of homogenization in degree `d`. -/
private noncomputable def homogenizeFun (d : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  rename (Sum.elim (fun _ ↦ none) some) (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f)

private theorem isHomogeneous_homogenizeFun (d : ℕ) (f : MvPolynomial σ R) :
    (homogenizeFun d f).IsHomogeneous d := by
  classical
  exact (isWeightedHomogeneous_unit_iff.1
    (isWeightedHomogeneous_blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f ())).rename_isHomogeneous

private theorem aeval_homogenizeFun_one_X {d : ℕ} {f : MvPolynomial σ R}
    (hf : f ∈ restrictTotalDegree σ R d) :
    aeval (R := R) (Option.elim' 1 X) (homogenizeFun d f) = f := by
  rw [homogenizeFun, aeval_rename, option_elim_comp_sumElim]
  refine aeval_blockHomogenize_one_X _ _ fun e he _ ↦ ?_
  rw [mapDomain_apply_eq_degree]
  exact (le_totalDegree he).trans ((mem_restrictTotalDegree σ d f).1 hf)

private theorem homogenizeFun_aeval_one_X {d : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous d) :
    homogenizeFun d (aeval (R := R) (Option.elim' 1 X) F) = F := by
  classical
  have hG : rename (Sum.elim (fun _ ↦ none) some) (rename homogenizeVarEquiv F) = F := by
    rw [rename_rename, ← coe_homogenizeVarEquiv_symm, Equiv.symm_comp_self, rename_id_apply]
  conv_lhs => rw [← hG, aeval_rename, option_elim_comp_sumElim]
  rw [homogenizeFun, blockHomogenize_aeval_one_X _ _ fun _ ↦
    isWeightedHomogeneous_unit_iff.2 hF.rename_isHomogeneous, hG]

variable (σ R) in
/-- Homogenization in degree `d`: the linear equivalence from the polynomials of total degree at
most `d` in the variables `σ` to the homogeneous polynomials of degree `d` in the variables
`Option σ`, sending `c Xᵅ` to `c X₀^(d - |α|) Xᵅ`, where `X₀ = X none` and `Xⱼ = X (some j)`.
Its inverse sets `X₀ = 1`. -/
noncomputable def homogenizeEquiv (d : ℕ) :
    restrictTotalDegree σ R d ≃ₗ[R] homogeneousSubmodule (Option σ) R d where
  toFun f := ⟨homogenizeFun d f.val, isHomogeneous_homogenizeFun d f.val⟩
  invFun F := ⟨aeval (R := R) (Option.elim' 1 X) F.val,
    aeval_option_elim_one_X_mem_restrictTotalDegree
      (homogeneousSubmodule_le_restrictTotalDegree _ _ le_rfl F.property)⟩
  map_add' f g := Subtype.ext <| by
    simp only [Submodule.coe_add, homogenizeFun, blockHomogenize_add, map_add]
  map_smul' c f := Subtype.ext <| by
    simp only [SetLike.val_smul, homogenizeFun, blockHomogenize_smul, map_smul, RingHom.id_apply]
  left_inv f := Subtype.ext (aeval_homogenizeFun_one_X (d := d) (f := f.val) f.property)
  right_inv F := Subtype.ext (homogenizeFun_aeval_one_X (d := d) (F := F.val) F.property)

/-- Homogenization in degree `d` is the one-block block homogenization with block degree `d`,
with the homogenizing variable renamed to `none` and the affine variable `j` to `some j`. -/
theorem coe_homogenizeEquiv_apply {d : ℕ} (f : restrictTotalDegree σ R d) :
    (homogenizeEquiv σ R d f : MvPolynomial (Option σ) R) =
      rename (Sum.elim (fun _ ↦ none) some)
        (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) (f : MvPolynomial σ R)) :=
  (rfl)

/-- The inverse of homogenization sets the homogenizing variable `X₀ = X none` to `1`. -/
@[simp]
theorem coe_homogenizeEquiv_symm_apply {d : ℕ} (F : homogeneousSubmodule (Option σ) R d) :
    ((homogenizeEquiv σ R d).symm F : MvPolynomial σ R) =
      aeval (Option.elim' 1 X) (F : MvPolynomial (Option σ) R) :=
  (rfl)

/-- Setting `X₀ = 1` in the homogenization of `f` recovers `f`. -/
@[simp]
theorem aeval_homogenizeEquiv_one_X {d : ℕ} (f : restrictTotalDegree σ R d) :
    aeval (Option.elim' 1 X) (homogenizeEquiv σ R d f : MvPolynomial (Option σ) R) =
      (f : MvPolynomial σ R) := by
  rw [← coe_homogenizeEquiv_symm_apply, LinearEquiv.symm_apply_apply]

/-- A homogeneous polynomial of degree `d` is the homogenization of the polynomial obtained by
setting `X₀ = 1`. -/
theorem homogenizeEquiv_aeval_one_X {d : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous d) :
    (homogenizeEquiv σ R d ⟨aeval (Option.elim' 1 X) F,
        aeval_option_elim_one_X_mem_restrictTotalDegree
          (homogeneousSubmodule_le_restrictTotalDegree _ _ le_rfl hF)⟩ :
        MvPolynomial (Option σ) R) = F :=
  congrArg Subtype.val ((homogenizeEquiv σ R d).apply_symm_apply ⟨F, hF⟩)

/-- The coefficient of the homogenization of `f` in degree `d` at an exponent `n` of degree `d` is
the coefficient of `f` at the restriction `n.some` of `n` to the affine variables. At exponents
of any other degree it is zero. -/
theorem coeff_homogenizeEquiv {d : ℕ} (f : restrictTotalDegree σ R d) (n : Option σ →₀ ℕ) :
    (homogenizeEquiv σ R d f : MvPolynomial (Option σ) R).coeff n =
      if n.degree = d then (f : MvPolynomial σ R).coeff n.some else 0 := by
  split_ifs with hn
  · have hdeg : n.degree = n none + n.some.degree := by
      simpa using degree_optionElim n.some (n none)
    have hn' : n = (blockHomogenizeExponent (fun _ : σ ↦ ()) (fun _ ↦ d) n.some).mapDomain
        (Sum.elim (fun _ ↦ none) some) := by
      rw [mapDomain_blockHomogenizeExponent_unit]
      ext v
      rcases v with _ | j
      · simp [mapDomain_of_notMem_range]
        omega
      · simp [mapDomain_apply_of_injective (Option.some_injective σ)]
    conv_lhs => rw [hn']
    rw [coe_homogenizeEquiv_apply, coeff_rename_mapDomain _ sumElim_none_some_injective,
      coeff_blockHomogenizeExponent_blockHomogenize _ _ _ fun _ ↦ by
        rw [mapDomain_apply_eq_degree]
        omega]
  · exact (homogenizeEquiv σ R d f).property.coeff_eq_zero hn

/-- Homogenization in degree `d` sends the monomial `c Xᵅ`, `|α| ≤ d`, to
`c X₀^(d - |α|) Xᵅ`. -/
theorem homogenizeEquiv_monomial {d : ℕ} {s : σ →₀ ℕ} (hs : s.degree ≤ d) (c : R) :
    (homogenizeEquiv σ R d ⟨monomial s c, monomial_mem_restrictTotalDegree hs c⟩ :
        MvPolynomial (Option σ) R) =
      X none ^ (d - s.degree) * monomial (s.mapDomain Option.some) c := by
  rw [coe_homogenizeEquiv_apply, blockHomogenize_monomial, ite_eq_left fun _ ↦ by
    rw [mapDomain_apply_eq_degree]; exact hs, rename_monomial, X_pow_eq_monomial,
    monomial_mul_monomial, one_mul, mapDomain_blockHomogenizeExponent_unit]

/-- Homogenization in degree `d` sends the constant `c` to `c X₀ᵈ`. -/
@[simp]
theorem homogenizeEquiv_C {d : ℕ} (c : R) :
    (homogenizeEquiv σ R d ⟨C c, monomial_mem_restrictTotalDegree (by simp) c⟩ :
        MvPolynomial (Option σ) R) = C c * X none ^ d := by
  simpa [mul_comm] using homogenizeEquiv_monomial (σ := σ) (d := d) (s := 0) (by simp) c

/-- Homogenization is multiplicative: for `f` of total degree at most `d` and `g` of total degree
at most `e`, the homogenization of `f g` in degree `d + e` is the product of the homogenizations
of `f` in degree `d` and of `g` in degree `e`. -/
theorem homogenizeEquiv_mul {d e : ℕ} (f : restrictTotalDegree σ R d)
    (g : restrictTotalDegree σ R e) :
    (homogenizeEquiv σ R (d + e) ⟨f * g, mul_mem_restrictTotalDegree f.property g.property⟩ :
        MvPolynomial (Option σ) R) =
      homogenizeEquiv σ R d f * homogenizeEquiv σ R e g := by
  have hFG : ((homogenizeEquiv σ R d f : MvPolynomial (Option σ) R) *
      homogenizeEquiv σ R e g).IsHomogeneous (d + e) :=
    (homogenizeEquiv σ R d f).property.mul (homogenizeEquiv σ R e g).property
  rw [← homogenizeEquiv_aeval_one_X hFG]
  congr 2
  simp

end MvPolynomial
