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
space of forms of degree `d` in one more variable, that is, with the sections of `O(d)` on
projective space, and it turns products of bounded polynomials into products of forms,
`H_{d+e}(f g) = H_d(f) H_e(g)`.

## Main definitions

* `MvPolynomial.homogenizeEquiv σ R d`: homogenization in degree `d`, as a linear equivalence
  between `restrictTotalDegree σ R d` and `homogeneousSubmodule (Option σ) R d`.

## Main results

* `MvPolynomial.homogenizeEquiv_monomial`: `c Xᵅ` maps to `c X₀^(d - |α|) Xᵅ`.
* `MvPolynomial.coe_homogenizeEquiv_symm_apply`: the inverse sets `X₀ = 1`.
* `MvPolynomial.homogenizeEquiv_mul`: homogenization is multiplicative, adding the degrees.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), §3.
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ R : Type*} [CommSemiring R]

/-- The renaming of the one-block variables `Unit ⊕ σ` to `Option σ`: the homogenizing variable
becomes `none` and the affine variable `j` becomes `some j`. -/
private def homogenizeVar : Unit ⊕ σ → Option σ := Sum.elim (fun _ ↦ none) some

/-- The inverse renaming of `homogenizeVar`. -/
private def homogenizeVarInv : Option σ → Unit ⊕ σ := Option.elim' (.inl ()) .inr

private theorem homogenizeVar_comp_inv : homogenizeVar ∘ homogenizeVarInv (σ := σ) = id := by
  funext v
  cases v <;> rfl

private theorem homogenizeVar_injective : Function.Injective (homogenizeVar (σ := σ)) :=
  Function.LeftInverse.injective (g := homogenizeVarInv) fun v ↦ by rcases v with ⟨⟩ | j <;> rfl

private theorem option_elim_comp_homogenizeVar {S : Type*} [One S] (x : σ → S) :
    Option.elim' 1 x ∘ homogenizeVar = Sum.elim (fun _ : Unit ↦ 1) x := by
  funext v
  rcases v with ⟨⟩ | j <;> rfl

/-- With a single block, the degree of an exponent in that block is its total degree. -/
private theorem mapDomain_unit_apply (e : σ →₀ ℕ) :
    e.mapDomain (fun _ ↦ ()) () = e.degree := by
  rw [← degree_mapDomain (fun _ : σ ↦ ()) e, degree_eq_sum, Fintype.sum_unique]

/-- With a single block, block homogeneity is ordinary homogeneity. -/
private theorem isWeightedHomogeneous_unit_iff {F : MvPolynomial (Unit ⊕ σ) R} {d : ℕ} :
    F.IsWeightedHomogeneous
        (fun v ↦ if Sum.elim id (fun _ : σ ↦ ()) v = () then 1 else 0) d ↔
      F.IsHomogeneous d := by
  -- Every variable lies in the single block, so the block weight is the constant weight `1`.
  simp only [IsHomogeneous, ite_true]
  rfl

/-- The underlying polynomial map of homogenization in degree `d`. -/
private noncomputable def homogenizeFun (d : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  rename homogenizeVar (blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f)

private theorem isHomogeneous_homogenizeFun (d : ℕ) (f : MvPolynomial σ R) :
    (homogenizeFun d f).IsHomogeneous d := by
  classical
  exact (isWeightedHomogeneous_unit_iff.1
    (isWeightedHomogeneous_blockHomogenize (fun _ : σ ↦ ()) (fun _ ↦ d) f ())).rename_isHomogeneous

private theorem aeval_homogenizeFun {d : ℕ} {f : MvPolynomial σ R}
    (hf : f ∈ restrictTotalDegree σ R d) :
    aeval (R := R) (Option.elim' 1 X) (homogenizeFun d f) = f := by
  rw [homogenizeFun, aeval_rename, option_elim_comp_homogenizeVar]
  refine aeval_blockHomogenize_one_X _ _ fun e he _ ↦ ?_
  rw [mapDomain_unit_apply]
  exact (le_totalDegree he).trans ((mem_restrictTotalDegree σ d f).1 hf)

private theorem homogenizeFun_aeval {d : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous d) :
    homogenizeFun d (aeval (R := R) (Option.elim' 1 X) F) = F := by
  classical
  have hG : rename homogenizeVar (rename homogenizeVarInv F) = F := by
    rw [rename_rename, homogenizeVar_comp_inv, rename_id_apply]
  conv_lhs => rw [← hG, aeval_rename, option_elim_comp_homogenizeVar]
  rw [homogenizeFun, blockHomogenize_aeval_one_X _ _ fun _ ↦
    isWeightedHomogeneous_unit_iff.2 hF.rename_isHomogeneous, hG]

/-- Setting the variable `none` to `1` and keeping the variables `some j` does not raise the total
degree. -/
theorem aeval_option_elim_one_X_mem_restrictTotalDegree {d : ℕ}
    {F : MvPolynomial (Option σ) R} (hF : F ∈ restrictTotalDegree (Option σ) R d) :
    aeval (Option.elim' 1 X) F ∈ restrictTotalDegree σ R d := by
  refine aeval_mem_restrictTotalDegree (fun v ↦ ?_) hF
  cases v
  · simp
  · simpa [← X_pow_eq_monomial] using totalDegree_monomial_le (Finsupp.single _ 1) (1 : R)

variable (σ R) in
/-- Homogenization in degree `d`: the linear equivalence from the polynomials of total degree at
most `d` in the variables `σ` to the homogeneous polynomials of degree `d` in the variables
`Option σ`, sending `c Xᵅ` to `c X₀^(d - |α|) Xᵅ`, where `X₀ = X none` and `Xⱼ = X (some j)`.
Its inverse sets `X₀ = 1`. -/
noncomputable def homogenizeEquiv (d : ℕ) :
    restrictTotalDegree σ R d ≃ₗ[R] homogeneousSubmodule (Option σ) R d where
  toFun f := ⟨homogenizeFun d f.1, isHomogeneous_homogenizeFun d f.1⟩
  invFun F := ⟨aeval (R := R) (Option.elim' 1 X) F.1,
    aeval_option_elim_one_X_mem_restrictTotalDegree
      (homogeneousSubmodule_le_restrictTotalDegree _ _ le_rfl F.2)⟩
  map_add' f g := Subtype.ext <| by
    simp only [Submodule.coe_add, homogenizeFun, blockHomogenize_add, map_add]
  map_smul' c f := Subtype.ext <| by
    simp only [SetLike.val_smul, homogenizeFun, blockHomogenize_smul, map_smul, RingHom.id_apply]
  left_inv f := Subtype.ext (aeval_homogenizeFun (d := d) (f := f.1) f.2)
  right_inv F := Subtype.ext (homogenizeFun_aeval (d := d) (F := F.1) F.2)

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
theorem aeval_homogenizeEquiv {d : ℕ} (f : restrictTotalDegree σ R d) :
    aeval (Option.elim' 1 X) (homogenizeEquiv σ R d f : MvPolynomial (Option σ) R) =
      (f : MvPolynomial σ R) := by
  rw [← coe_homogenizeEquiv_symm_apply, LinearEquiv.symm_apply_apply]

/-- A homogeneous polynomial of degree `d` is the homogenization of the polynomial obtained by
setting `X₀ = 1`. -/
theorem homogenizeEquiv_aeval {d : ℕ} {F : MvPolynomial (Option σ) R} (hF : F.IsHomogeneous d) :
    (homogenizeEquiv σ R d ⟨aeval (Option.elim' 1 X) F,
        aeval_option_elim_one_X_mem_restrictTotalDegree
          (homogeneousSubmodule_le_restrictTotalDegree _ _ le_rfl hF)⟩ :
        MvPolynomial (Option σ) R) = F :=
  congrArg Subtype.val ((homogenizeEquiv σ R d).apply_symm_apply ⟨F, hF⟩)

/-- Homogenization in degree `d` sends the monomial `c Xᵅ`, `|α| ≤ d`, to
`c X₀^(d - |α|) Xᵅ`. -/
theorem homogenizeEquiv_monomial {d : ℕ} {s : σ →₀ ℕ} (hs : s.degree ≤ d) (c : R) :
    (homogenizeEquiv σ R d ⟨monomial s c, monomial_mem_restrictTotalDegree hs c⟩ :
        MvPolynomial (Option σ) R) =
      X none ^ (d - s.degree) * monomial (s.mapDomain Option.some) c := by
  rw [coe_homogenizeEquiv_apply, blockHomogenize_monomial, ite_eq_left fun _ ↦ by
    rw [mapDomain_unit_apply]; exact hs, rename_monomial, X_pow_eq_monomial,
    monomial_mul_monomial, one_mul]
  congr 2
  ext v
  rcases v with _ | j
  · have := Finsupp.mapDomain_apply_of_injective homogenizeVar_injective
      (blockHomogenizeExponent (fun _ : σ ↦ ()) (fun _ ↦ d) s) (Sum.inl ())
    simp_all [homogenizeVar, mapDomain_unit_apply,
      Finsupp.mapDomain_of_notMem_range (f := Option.some) s (none : Option σ) (by simp)]
  · have := Finsupp.mapDomain_apply_of_injective homogenizeVar_injective
      (blockHomogenizeExponent (fun _ : σ ↦ ()) (fun _ ↦ d) s) (Sum.inr j)
    simp_all [homogenizeVar, Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]

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
    (homogenizeEquiv σ R (d + e) ⟨f * g, mul_mem_restrictTotalDegree f.2 g.2⟩ :
        MvPolynomial (Option σ) R) =
      homogenizeEquiv σ R d f * homogenizeEquiv σ R e g := by
  have hFG : ((homogenizeEquiv σ R d f : MvPolynomial (Option σ) R) *
      homogenizeEquiv σ R e g).IsHomogeneous (d + e) :=
    (homogenizeEquiv σ R d f).2.mul (homogenizeEquiv σ R e g).2
  rw [← homogenizeEquiv_aeval hFG]
  congr 2
  simp

end MvPolynomial
