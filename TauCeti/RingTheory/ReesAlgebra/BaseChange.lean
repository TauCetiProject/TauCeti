/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
public import TauCeti.RingTheory.ReesAlgebra.Grading
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Base change of the Rees algebra

Let `I` be an ideal of a commutative ring `R` and let `S` be an `R`-algebra, with extended ideal
`IS = I.map (algebraMap R S)`. Extending scalars from `R` to `S` compares the two Rees algebras:

`S ⊗[R] R[It] ⟶ S[(IS)t]`, `s ⊗ f ↦ s · f`,

where the coefficients of `f ∈ R[It] ⊆ R[X]` are mapped to `S`. This comparison is a surjective
homomorphism of graded `S`-algebras, for the grading `n ↦ (R[It]ₙ).baseChange S` of the source.
In degree `n` it is the multiplication map `S ⊗[R] Iⁿ ⟶ (IS)ⁿ`; when `S` is flat over `R` the
latter is injective, and the comparison is an isomorphism of graded algebras.

Geometrically, `Proj` of the Rees algebra is the blowup of `Spec R` along `V(I)`, so the
surjectivity makes the blowup of `Spec S` along `V(IS)` a closed subscheme of the base change of
the blowup of `Spec R`, and the flat case identifies the two. The comparison is the composite of
`S ⊗[R] R[It] ⟶ S ⊗[R] R[X]` with Mathlib's `polyEquivTensor'`.

## Main definitions

* `reesAlgebra.baseChangeHom I S`: the comparison `S ⊗[R] R[It] →ₐ[S] S[(IS)t]`.
* `reesAlgebra.baseChangeGradedAlgHom I S`: the same comparison as a graded algebra homomorphism.
* `reesAlgebra.baseChangeEquiv I S`: for flat `S`, the comparison as an algebra isomorphism.
* `reesAlgebra.baseChangeGradedAlgHomSymm I S`: for flat `S`, its inverse as a graded algebra
  homomorphism.

## Main results

* `reesAlgebra.coe_baseChangeHom_tmul`: the comparison sends `s ⊗ f` to `s · f`.
* `reesAlgebra.baseChangeHom_surjective`: the comparison is surjective.
* `reesAlgebra.baseChangeHom_injective`: for flat `S`, the comparison is injective.
* `reesAlgebra.baseChangeHom_mem_grade_iff`: for flat `S`, the comparison preserves and reflects
  degrees.
* `reesAlgebra.baseChangeHom_baseChangeEquiv_symm_apply`,
  `reesAlgebra.baseChangeEquiv_symm_baseChangeHom_apply`: for flat `S`, the comparison and the
  inverse of `reesAlgebra.baseChangeEquiv` cancel.

## References

* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF), where
  blowing up is shown to commute with flat base change.
-/

public section

open Polynomial
open scoped TensorProduct

namespace reesAlgebra

variable {R : Type*} [CommRing R] (I : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

/-- The composite `S ⊗[R] R[It] ⟶ S ⊗[R] R[X] ≃ S[X]`, before restricting its codomain. -/
private noncomputable def toPolynomial : S ⊗[R] reesAlgebra I →ₐ[S] S[X] :=
  (polyEquivTensor' R S).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id S S) (reesAlgebra I).val)

private theorem toPolynomial_tmul (s : S) (f : reesAlgebra I) :
    toPolynomial I S (s ⊗ₜ f) = s • (f : R[X]).map (algebraMap R S) := by
  simp [toPolynomial]

/-- Extension of scalars of a polynomial in the Rees algebra lands in the Rees algebra of the
extended ideal. -/
private theorem toPolynomial_mem (x : S ⊗[R] reesAlgebra I) :
    toPolynomial I S x ∈ reesAlgebra (I.map (algebraMap R S)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using add_mem hx hy
  | tmul s f =>
    rw [toPolynomial_tmul, mem_reesAlgebra_iff]
    intro n
    rw [coeff_smul, coeff_map, smul_eq_mul, ← Ideal.map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).mp f.2 n))

/-- The comparison `S ⊗[R] R[It] →ₐ[S] S[(IS)t]` between the base change of the Rees algebra of
`I` and the Rees algebra of the extended ideal `IS`: it sends `s ⊗ f` to `s · f`, with the
coefficients of `f` mapped to `S` (`reesAlgebra.coe_baseChangeHom_tmul`). -/
noncomputable def baseChangeHom :
    S ⊗[R] reesAlgebra I →ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  (toPolynomial I S).codRestrict _ (toPolynomial_mem I S)

private theorem coe_baseChangeHom (x : S ⊗[R] reesAlgebra I) :
    (baseChangeHom I S x : S[X]) = toPolynomial I S x :=
  (rfl)

/-- The comparison sends `s ⊗ f` to `s · f`, with the coefficients of `f` mapped to `S`. -/
@[simp]
theorem coe_baseChangeHom_tmul (s : S) (f : reesAlgebra I) :
    (baseChangeHom I S (s ⊗ₜ f) : S[X]) = s • (f : R[X]).map (algebraMap R S) := by
  rw [coe_baseChangeHom, toPolynomial_tmul]

/-- **The comparison of Rees algebras is surjective**: the Rees algebra of `IS` is generated over
`S` by the monomials `a t` with `a ∈ I`. -/
theorem baseChangeHom_surjective : Function.Surjective (baseChangeHom I S) := by
  let φ : S ⊗[R] reesAlgebra I →ₐ[S] S[X] := (reesAlgebra _).val.comp (baseChangeHom I S)
  -- the monomials `c t` with `c ∈ IS` lie in the range, as `IS` is spanned by the image of `I`
  have hmon {c : S} (hc : c ∈ I.map (algebraMap R S)) : monomial 1 c ∈ φ.range := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ha, rfl⟩ := hc
      exact ⟨1 ⊗ₜ monomialDegreeOne ha, by simp [φ]⟩
    | zero => simp
    | add c d _ _ hc hd => simpa only [map_add] using φ.range.add_mem hc hd
    | smul s c _ hc =>
      have := φ.range.smul_mem hc s
      rwa [smul_monomial] at this
  have hle : reesAlgebra (I.map (algebraMap R S)) ≤ φ.range := by
    rw [← adjoin_monomial_eq_reesAlgebra, Algebra.adjoin_le_iff]
    rintro - ⟨c, hc, rfl⟩
    exact hmon hc
  intro f
  obtain ⟨x, hx⟩ := hle f.2
  exact ⟨x, Subtype.ext hx⟩

/-- **The comparison of Rees algebras is injective after flat base change**: for flat `S`, the
inclusion `R[It] ⊆ R[X]` stays injective after tensoring with `S`. -/
theorem baseChangeHom_injective [Module.Flat R S] : Function.Injective (baseChangeHom I S) := by
  have hmap : ⇑(Algebra.TensorProduct.map (AlgHom.id S S) (reesAlgebra I).val) =
      ⇑((reesAlgebra I).val.toLinearMap.lTensor S) :=
    funext fun x ↦ (AlgHom.lTensor_toLinearMap_apply S (reesAlgebra I).val x).symm
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id S S) (reesAlgebra I).val) := by
    rw [hmap]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y hxy
  refine hinj ((polyEquivTensor' R S).symm.injective ?_)
  simpa only [coe_baseChangeHom, toPolynomial, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using
    congr_arg Subtype.val hxy

/-- The comparison sends the base change of the degree `n` piece of `R[It]` into the degree `n`
piece of `S[(IS)t]`. -/
theorem baseChangeHom_mem_grade {n : ℕ} {x : S ⊗[R] reesAlgebra I}
    (hx : x ∈ (grade I n).baseChange S) :
    baseChangeHom I S x ∈ grade (I.map (algebraMap R S)) n := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨r, hr, hrf⟩ := mem_grade_iff.mp hf
    refine mem_grade_iff.mpr ⟨algebraMap R S r, ?_, ?_⟩
    · rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    · simp [← hrf]
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul s x _ hx => simpa only [map_smul] using Submodule.smul_mem _ s hx

/-- The comparison `S ⊗[R] R[It] ⟶ S[(IS)t]` as a homomorphism of graded `S`-algebras, for the
grading `n ↦ (R[It]ₙ).baseChange S` of the source. -/
noncomputable def baseChangeGradedAlgHom :
    (fun n ↦ (grade I n).baseChange S) →ₐᵍ[S] grade (I.map (algebraMap R S)) where
  __ := baseChangeHom I S
  map_mem := baseChangeHom_mem_grade I S

/-- The graded comparison has the comparison `reesAlgebra.baseChangeHom` as underlying map. -/
@[simp]
theorem baseChangeGradedAlgHom_apply (x : S ⊗[R] reesAlgebra I) :
    baseChangeGradedAlgHom I S x = baseChangeHom I S x :=
  (rfl)

/-- The graded comparison of Rees algebras is surjective. -/
theorem baseChangeGradedAlgHom_surjective : Function.Surjective (baseChangeGradedAlgHom I S) :=
  baseChangeHom_surjective I S

variable {I S} in
/-- For flat `S`, the comparison of Rees algebras preserves and reflects degrees. -/
@[simp]
theorem baseChangeHom_mem_grade_iff [Module.Flat R S] {n : ℕ} {x : S ⊗[R] reesAlgebra I} :
    baseChangeHom I S x ∈ grade (I.map (algebraMap R S)) n ↔ x ∈ (grade I n).baseChange S :=
  Graded.map_mem_iff_of_injective (baseChangeGradedAlgHom I S) (baseChangeHom_injective I S)

/-- **Rees algebras commute with flat base change**: for flat `S`, the comparison
`S ⊗[R] R[It] ≃ₐ[S] S[(IS)t]` is an isomorphism. -/
noncomputable def baseChangeEquiv [Module.Flat R S] :
    S ⊗[R] reesAlgebra I ≃ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  AlgEquiv.ofBijective (baseChangeHom I S)
    ⟨baseChangeHom_injective I S, baseChangeHom_surjective I S⟩

/-- The isomorphism `reesAlgebra.baseChangeEquiv` is the comparison `reesAlgebra.baseChangeHom`. -/
@[simp]
theorem baseChangeEquiv_apply [Module.Flat R S] (x : S ⊗[R] reesAlgebra I) :
    baseChangeEquiv I S x = baseChangeHom I S x :=
  (rfl)

/-- For flat `S`, the inverse of the comparison `S ⊗[R] R[It] ≃ₐ[S] S[(IS)t]` as a homomorphism of
graded `S`-algebras. -/
noncomputable def baseChangeGradedAlgHomSymm [Module.Flat R S] :
    grade (I.map (algebraMap R S)) →ₐᵍ[S] (fun n ↦ (grade I n).baseChange S) where
  __ := (baseChangeEquiv I S).symm.toAlgHom
  map_mem {_ x} hx := by
    rw [← baseChangeHom_mem_grade_iff]
    simpa [← baseChangeEquiv_apply] using hx

/-- The inverse graded comparison is the inverse of `reesAlgebra.baseChangeEquiv`. -/
@[simp]
theorem baseChangeGradedAlgHomSymm_apply [Module.Flat R S]
    (x : reesAlgebra (I.map (algebraMap R S))) :
    baseChangeGradedAlgHomSymm I S x = (baseChangeEquiv I S).symm x :=
  (rfl)

/-- For flat `S`, the comparison undoes the inverse of `reesAlgebra.baseChangeEquiv`. -/
@[simp]
theorem baseChangeHom_baseChangeEquiv_symm_apply [Module.Flat R S]
    (x : reesAlgebra (I.map (algebraMap R S))) :
    baseChangeHom I S ((baseChangeEquiv I S).symm x) = x :=
  (baseChangeEquiv I S).apply_symm_apply x

/-- For flat `S`, the inverse of `reesAlgebra.baseChangeEquiv` undoes the comparison. -/
@[simp]
theorem baseChangeEquiv_symm_baseChangeHom_apply [Module.Flat R S] (x : S ⊗[R] reesAlgebra I) :
    (baseChangeEquiv I S).symm (baseChangeHom I S x) = x :=
  (baseChangeEquiv I S).symm_apply_apply x

/-- For flat `S`, the inverse graded comparison is a right inverse of the graded comparison. -/
theorem baseChangeGradedAlgHom_rightInverse [Module.Flat R S] :
    Function.RightInverse (baseChangeGradedAlgHomSymm I S) (baseChangeGradedAlgHom I S) :=
  (baseChangeEquiv I S).apply_symm_apply

/-- For flat `S`, the inverse graded comparison is a left inverse of the graded comparison. -/
theorem baseChangeGradedAlgHom_leftInverse [Module.Flat R S] :
    Function.LeftInverse (baseChangeGradedAlgHomSymm I S) (baseChangeGradedAlgHom I S) :=
  (baseChangeEquiv I S).symm_apply_apply

end reesAlgebra
