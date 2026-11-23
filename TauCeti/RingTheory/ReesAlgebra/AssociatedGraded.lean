/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.Ideal.AssociatedGraded
public import TauCeti.RingTheory.ReesAlgebra.Grading

/-!
# The associated graded ring as a quotient of the Rees algebra

Let `I` be an ideal of a commutative ring `R`, with Rees algebra `R[It] = ⨁ₙ Iⁿ tⁿ`, realized by
Mathlib as the subalgebra `reesAlgebra I` of `R[X]`. The extended ideal `I R[It]` consists of the
Rees polynomials whose coefficient in degree `n` lies in `Iⁿ⁺¹`
(`mem_map_algebraMap_reesAlgebra_iff`). The *Rees quotient*

`R[It] ⧸ I R[It] = ⨁ₙ Iⁿ tⁿ ⧸ Iⁿ⁺¹ tⁿ`

is therefore the associated graded ring `gr_I R = ⨁ₙ Iⁿ ⧸ Iⁿ⁺¹` of `I`, constructed directly on its
direct-sum carrier in `TauCeti.RingTheory.Ideal.AssociatedGraded`. This file proves this
identification. The symbol map `R[It] → gr_I R` sends `∑ aₙ tⁿ` to the family of classes
`[aₙ] ∈ Iⁿ ⧸ Iⁿ⁺¹`; it is a surjective `R`-algebra map with kernel `I R[It]`, and so induces an
isomorphism of `R ⧸ I`-algebras from the Rees quotient to `gr_I R`. Under this isomorphism the
class of the monomial `x tⁿ`, for `x ∈ Iⁿ`, corresponds to the class of `x` in degree `n`.

This presents `gr_I R` as a quotient of the Rees algebra, which is a finitely generated
`R`-algebra when `I` is finitely generated. The equivalence transports the
direct-sum coordinates to the Rees quotient: the degree-`n` coefficient of the class of a Rees
polynomial `f` is the class of the `n`-th coefficient of `f`, and the image of the degree-`n`
inclusion is the degree-`n` piece of the grading that `I R[It]`, a homogeneous ideal, induces on
the quotient.

## Main definitions

* `reesAlgebra.toAssociatedGraded I`: the symbol map `R[It] →ₐ[R] gr_I R`.
* `Ideal.ReesQuotient I`: the Rees quotient `R[It] ⧸ I R[It]`, an `R ⧸ I`-algebra.
* `Ideal.ReesQuotient.mk I n`: the class `x ↦ [x tⁿ]` of an element of `Iⁿ` in degree `n`.
* `Ideal.ReesQuotient.equivAssociatedGraded I`: the `R ⧸ I`-algebra isomorphism
  `R[It] ⧸ I R[It] ≃ gr_I R`.
* `Ideal.ReesQuotient.coeff I n` and `Ideal.ReesQuotient.of I n`: the degree-`n` coefficient map
  to `Iⁿ ⧸ Iⁿ⁺¹` and the degree-`n` inclusion from it.

## Main results

* `reesAlgebra.toAssociatedGraded_apply`: the degree-`n` component of the symbol of `f` is the
  class of the `n`-th coefficient of `f`.
* `reesAlgebra.ker_toAssociatedGraded` and `reesAlgebra.toAssociatedGraded_surjective`: the symbol
  map is onto, with kernel `I R[It]`.
* `Ideal.ReesQuotient.mk_eq_zero_iff`: the class of `x ∈ Iⁿ` in degree `n` vanishes exactly when
  `x ∈ Iⁿ⁺¹`; `Ideal.ReesQuotient.mk_mul_mk`: classes multiply with degrees adding.
* `Ideal.ReesQuotient.coeff_of_self`, `Ideal.ReesQuotient.coeff_of_of_ne`,
  `Ideal.ReesQuotient.ext_coeff` and `Ideal.ReesQuotient.sum_of_coeff`: the coefficient maps
  retract the inclusions, kill the other degrees, detect equality and reconstruct every element.
* `Ideal.ReesQuotient.sum_of_coeff_quotientMk`: reconstruction over the support of a polynomial
  representative, without deciding which quotient coefficients vanish.
* `Ideal.ReesQuotient.range_of`: the image of the degree-`n` inclusion is the degree-`n` piece of
  the quotient grading.

## Implementation notes

The symbol map is assembled from its homogeneous components with `DirectSum.toAlgebra`, following
`TauCeti.Algebra.wordFiltration.reesSymbol`. The `R ⧸ I`-algebra structure on the Rees quotient is
Mathlib's `Ideal.Quotient.algebraQuotientMapQuotient`.

## References

* The Stacks Project, Chapter 10 (Commutative Algebra), section *Associated graded ring*.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

public section

open Polynomial DirectSum

universe u

variable {R : Type u} [CommRing R]

namespace reesAlgebra

variable (I : Ideal R)

/-- The monomial `x tⁿ` of the Rees algebra, as a linear function of `x ∈ Iⁿ`. -/
private noncomputable def monomialLinear (n : ℕ) : ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun x := ⟨monomial n (x : R), monomial_mem.mpr x.property⟩
  map_add' x y := by ext1; simp
  map_smul' r x := by ext1; simp [smul_monomial]

/-- The coefficient of a Rees polynomial of degree `n`, as an element of `Iⁿ`. -/
private noncomputable def gradeCoeff (n : ℕ) : grade I n →ₗ[R] ↥(I ^ n) where
  toFun f :=
    ⟨((f : reesAlgebra I) : R[X]).coeff n, (mem_reesAlgebra_iff I _).mp
        (f : reesAlgebra I).property n⟩
  map_add' f g := by ext1; simp
  map_smul' r f := by ext1; simp

private theorem coe_gradeCoeff (n : ℕ) (f : grade I n) :
    (gradeCoeff I n f : R) = ((f : reesAlgebra I) : R[X]).coeff n :=
  rfl

/-- A Rees polynomial of degree `n` is the monomial of its `n`-th coefficient. -/
private theorem coe_eq_monomial_gradeCoeff {n : ℕ} (f : grade I n) :
    ((f : reesAlgebra I) : R[X]) = monomial n (gradeCoeff I n f : R) :=
  (mem_grade_iff_monomial_coeff.mp f.property).symm

/-- The degree-`n` component of the symbol map: `x tⁿ ↦ [x] ∈ Iⁿ ⧸ Iⁿ⁺¹`. -/
private noncomputable def symbolComponent (n : ℕ) : grade I n →ₗ[R] I.AssociatedGraded :=
  Ideal.AssociatedGraded.mk I n ∘ₗ gradeCoeff I n

private theorem symbolComponent_one :
    symbolComponent I 0 (GradedMonoid.GOne.one (A := fun n ↦ grade I n)) = 1 := by
  rw [← Ideal.AssociatedGraded.mk_zero_one, symbolComponent, LinearMap.comp_apply]
  congr 1
  ext1
  simp [coe_gradeCoeff]

private theorem symbolComponent_mul {i j : ℕ} (f : grade I i) (g : grade I j) :
    symbolComponent I (i + j) (GradedMonoid.GMul.mul (A := fun n ↦ grade I n) f g) =
      symbolComponent I i f * symbolComponent I j g := by
  simp only [symbolComponent, LinearMap.comp_apply, Ideal.AssociatedGraded.mk_mul_mk]
  congr 1
  ext1
  rw [coe_gradeCoeff, SetLike.coe_gMul, Subalgebra.coe_mul, coe_eq_monomial_gradeCoeff I f,
    coe_eq_monomial_gradeCoeff I g, monomial_mul_monomial, coeff_monomial_same]

/-- **The symbol map** `R[It] → gr_I R`. It sends a Rees polynomial `∑ aₙ tⁿ`, with `aₙ ∈ Iⁿ`, to
the family of classes `[aₙ] ∈ Iⁿ ⧸ Iⁿ⁺¹` (`reesAlgebra.toAssociatedGraded_apply`). -/
noncomputable def toAssociatedGraded : reesAlgebra I →ₐ[R] I.AssociatedGraded :=
  (DirectSum.toAlgebra R (fun n ↦ grade I n) (symbolComponent I) (symbolComponent_one I)
    (symbolComponent_mul I)).comp (decomposeAlgEquiv (grade I)).toAlgHom

variable {I}

/-- The symbol of the monomial `x tⁿ`, for `x ∈ Iⁿ`, is the class of `x` in degree `n`. -/
@[simp]
theorem toAssociatedGraded_monomial {n : ℕ} {x : R} (hx : x ∈ I ^ n) :
    toAssociatedGraded I ⟨monomial n x, monomial_mem.mpr hx⟩ =
      Ideal.AssociatedGraded.mk I n ⟨x, hx⟩ := by
  rw [toAssociatedGraded, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, decomposeAlgEquiv_apply,
    decompose_of_mem (grade I) (monomial_mem_grade hx)]
  simp only [DirectSum.toAlgebra_apply, DirectSum.toSemiring_of, LinearMap.toAddMonoidHom_coe,
    symbolComponent, LinearMap.comp_apply]
  congr 1
  ext1
  simp [coe_gradeCoeff]

/-- The degree-`n` component of the symbol of `f` is the class of the `n`-th coefficient of `f`. -/
@[simp]
theorem toAssociatedGraded_apply (f : reesAlgebra I) (n : ℕ) :
    toAssociatedGraded I f n =
      Submodule.Quotient.mk ⟨(f : R[X]).coeff n, (mem_reesAlgebra_iff I _).mp f.property n⟩ := by
  induction f using DirectSum.Decomposition.inductionOn (grade I) with
  | zero =>
    rw [map_zero, DirectSum.zero_apply]
    exact (Submodule.Quotient.mk_zero _).symm
  | add f g hf hg =>
    rw [map_add, DirectSum.add_apply, hf, hg, ← Submodule.Quotient.mk_add]
    congr 1
  | @homogeneous m f =>
    obtain ⟨f, hf⟩ := f
    obtain ⟨x, hx, hxf⟩ := mem_grade_iff.mp hf
    obtain rfl : f = ⟨monomial m x, monomial_mem.mpr hx⟩ := Subtype.ext hxf.symm
    rw [toAssociatedGraded_monomial hx, Ideal.AssociatedGraded.mk_apply]
    by_cases hmn : n = m
    · subst hmn
      rw [DirectSum.of_eq_same]
      congr 1
      ext1
      simp
    · rw [DirectSum.of_eq_of_ne _ _ _ hmn, eq_comm, Submodule.Quotient.mk_eq_zero]
      simp [Ne.symm hmn]

/-- The symbol of `f` vanishes exactly when every coefficient of `f` lies one power deeper. -/
theorem toAssociatedGraded_eq_zero_iff (f : reesAlgebra I) :
    toAssociatedGraded I f = 0 ↔ ∀ n, (f : R[X]).coeff n ∈ I ^ (n + 1) := by
  simp only [DirectSum.ext_iff, toAssociatedGraded_apply, DirectSum.zero_apply,
    Ideal.gradedPiece_mk_eq_zero_iff]

variable (I)

/-- The kernel of the symbol map `R[It] → gr_I R` is the extended ideal `I R[It]`. -/
theorem ker_toAssociatedGraded :
    RingHom.ker (toAssociatedGraded I) = I.map (algebraMap R (reesAlgebra I)) := by
  ext f
  rw [RingHom.mem_ker, toAssociatedGraded_eq_zero_iff, mem_map_algebraMap_reesAlgebra_iff]

/-- Every element of `gr_I R` is the symbol of a Rees polynomial. -/
theorem toAssociatedGraded_surjective : Function.Surjective (toAssociatedGraded I) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n y =>
    induction y using Submodule.Quotient.induction_on with
    | _ x => exact ⟨⟨monomial n (x : R), monomial_mem.mpr x.property⟩,
        (toAssociatedGraded_monomial x.property).trans (Ideal.AssociatedGraded.mk_apply n x)⟩
  | add y z hy hz =>
    obtain ⟨f, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := hz
    exact ⟨f + g, map_add _ f g⟩

end reesAlgebra

namespace Ideal

variable (I : Ideal R)

/-- The **Rees quotient** `R[It] ⧸ I R[It]` of an ideal `I`, the quotient of the Rees algebra by
the extended ideal `I R[It]`, whose elements are the Rees polynomials with `n`-th coefficient in
`Iⁿ⁺¹`. It is an `R ⧸ I`-algebra (`Ideal.Quotient.algebraQuotientMapQuotient`), isomorphic to
the associated graded ring `gr_I R` (`Ideal.ReesQuotient.equivAssociatedGraded`). -/
abbrev ReesQuotient : Type u :=
  reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))

namespace ReesQuotient

/-- The ordinary Rees quotient is graded by the images of the homogeneous Rees components. -/
noncomputable instance instGradedAlgebra :
    GradedAlgebra (TauCeti.GradedAlgebra.quotientPiece (reesAlgebra.grade I)
      (I.map (algebraMap R (reesAlgebra I)))) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece _ _ (reesAlgebra.isHomogeneous_map_algebraMap I)

/-- The class `[x tⁿ]` in the Rees quotient of an element `x ∈ Iⁿ`, placed in degree `n`. -/
noncomputable def mk (n : ℕ) : ↥(I ^ n) →ₗ[R] I.ReesQuotient :=
  (Ideal.Quotient.mkₐ R _).toLinearMap ∘ₗ reesAlgebra.monomialLinear I n

variable {I}

/-- The class of `x ∈ Iⁿ` in degree `n` is the class of the Rees monomial `x tⁿ`. -/
theorem mk_apply (n : ℕ) (x : ↥(I ^ n)) :
    mk I n x = Ideal.Quotient.mk _ ⟨monomial n (x : R), reesAlgebra.monomial_mem.mpr x.property⟩ :=
  (rfl)

variable (I) in
/-- **The Rees quotient is the associated graded ring.** The symbol map induces an isomorphism of
`R ⧸ I`-algebras `R[It] ⧸ I R[It] ≃ gr_I R`, sending the class of a Rees polynomial `∑ aₙ tⁿ` to
the family of classes `[aₙ] ∈ Iⁿ ⧸ Iⁿ⁺¹`. -/
noncomputable def equivAssociatedGraded : I.ReesQuotient ≃ₐ[R ⧸ I] I.AssociatedGraded :=
  AlgEquiv.ofRingEquiv
    (f := ((Ideal.quotientEquivAlgOfEq R (reesAlgebra.ker_toAssociatedGraded I).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (reesAlgebra.toAssociatedGraded_surjective I))
      ).toRingEquiv) fun r ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [Quotient.algebraMap_quotient_map_quotient, AssociatedGraded.algebraMap_quotient_mk]
    exact (reesAlgebra.toAssociatedGraded I).commutes r

/-- The isomorphism sends the class of a Rees polynomial to its symbol. -/
@[simp]
theorem equivAssociatedGraded_quotientMk (f : reesAlgebra I) :
    equivAssociatedGraded I (Ideal.Quotient.mk _ f) = reesAlgebra.toAssociatedGraded I f :=
  (congrArg (Ideal.quotientKerAlgEquivOfSurjective (reesAlgebra.toAssociatedGraded_surjective I))
    (Ideal.quotientEquivAlgOfEq_mk R (reesAlgebra.ker_toAssociatedGraded I).symm f)).trans
      (Ideal.quotientKerAlgEquivOfSurjective_mk (reesAlgebra.toAssociatedGraded_surjective I) f)

/-- The isomorphism sends the class of `x ∈ Iⁿ` in degree `n` of the Rees quotient to its class
in degree `n` of the associated graded ring. -/
@[simp]
theorem equivAssociatedGraded_mk (n : ℕ) (x : ↥(I ^ n)) :
    equivAssociatedGraded I (mk I n x) = AssociatedGraded.mk I n x := by
  rw [mk_apply, equivAssociatedGraded_quotientMk, reesAlgebra.toAssociatedGraded_monomial]

/-- The inverse isomorphism sends the class of `x ∈ Iⁿ` in degree `n` of the associated graded
ring to the class of the Rees monomial `x tⁿ`. -/
@[simp]
theorem equivAssociatedGraded_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    (equivAssociatedGraded I).symm (AssociatedGraded.mk I n x) = mk I n x := by
  rw [AlgEquiv.symm_apply_eq, equivAssociatedGraded_mk]

/-- The class of `x ∈ Iⁿ` in degree `n` of the Rees quotient vanishes exactly when
`x ∈ Iⁿ⁺¹`. -/
-- Not `@[simp]`: the `simpNF` linter times out synthesizing `Nontrivial I.ReesQuotient` on the
-- left-hand side.
theorem mk_eq_zero_iff {n : ℕ} (x : ↥(I ^ n)) : mk I n x = 0 ↔ (x : R) ∈ I ^ (n + 1) := by
  rw [← AssociatedGraded.mk_eq_zero_iff, ← equivAssociatedGraded_mk,
    map_eq_zero_iff _ (equivAssociatedGraded I).injective]

/-- The kernel of the degree-`n` class map is `Iⁿ⁺¹`; in degree one it is `I²` inside `I`. -/
theorem ker_mk (n : ℕ) :
    LinearMap.ker (mk I n) = Submodule.comap (I ^ n).subtype (I ^ (n + 1)) := by
  ext x
  rw [LinearMap.mem_ker, mk_eq_zero_iff, Submodule.mem_comap, Submodule.subtype_apply]

/-- **Product rule.** The product of the classes of `x ∈ Iᵐ` and `y ∈ Iⁿ` is the class of `x * y`
in degree `m + n`. -/
@[simp]
theorem mk_mul_mk {m n : ℕ} (x : ↥(I ^ m)) (y : ↥(I ^ n)) :
    mk I m x * mk I n y = mk I (m + n) ⟨(x : R) * y, Ideal.mul_mem_pow_add x.property y.property⟩
        := by
  apply (equivAssociatedGraded I).injective
  rw [map_mul, equivAssociatedGraded_mk, equivAssociatedGraded_mk, equivAssociatedGraded_mk,
    AssociatedGraded.mk_mul_mk]

/-- The class of `r ∈ I⁰ = R` in degree zero is the image of `r` under the algebra map. -/
@[simp]
theorem mk_zero (r : ↥(I ^ 0)) : mk I 0 r = algebraMap R I.ReesQuotient r := by
  apply (equivAssociatedGraded I).injective
  rw [equivAssociatedGraded_mk, AssociatedGraded.mk_zero,
    IsScalarTower.algebraMap_apply R (R ⧸ I) I.ReesQuotient, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

variable (I) in
/-- The algebra map `R ⧸ I → R[It] ⧸ I R[It]` is injective. -/
theorem algebraMap_quotient_injective :
    Function.Injective (algebraMap (R ⧸ I) I.ReesQuotient) := by
  have h : ⇑(algebraMap (R ⧸ I) I.ReesQuotient) =
      (equivAssociatedGraded I).symm ∘ algebraMap (R ⧸ I) I.AssociatedGraded := by
    ext q
    rw [Function.comp_apply, AlgEquiv.commutes]
  rw [h]
  exact (equivAssociatedGraded I).symm.injective.comp AssociatedGraded.algebraMap_quotient_injective

variable (I) in
/-- The degree-`n` coefficient `R[It] ⧸ I R[It] → Iⁿ ⧸ Iⁿ⁺¹`, sending the class of a Rees
polynomial to the class of its `n`-th coefficient (`Ideal.ReesQuotient.coeff_quotientMk`). -/
noncomputable def coeff (n : ℕ) : I.ReesQuotient →ₗ[R] I.GradedPiece n :=
  DirectSum.component R ℕ I.GradedPiece n ∘ₗ
    ((equivAssociatedGraded I).toLinearMap.restrictScalars R)

/-- The degree-`n` coefficient is the degree-`n` component under the isomorphism with `gr_I R`. -/
theorem coeff_apply (n : ℕ) (q : I.ReesQuotient) :
    coeff I n q = equivAssociatedGraded I q n :=
  (rfl)

/-- The degree-`n` coefficient of the class of a Rees polynomial `f` is the class of the `n`-th
coefficient of `f`. -/
@[simp]
theorem coeff_quotientMk (n : ℕ) (f : reesAlgebra I) :
    coeff I n (Ideal.Quotient.mk _ f) =
      Submodule.Quotient.mk ⟨(f : R[X]).coeff n, (mem_reesAlgebra_iff I _).mp f.property n⟩ := by
  rw [coeff_apply, equivAssociatedGraded_quotientMk, reesAlgebra.toAssociatedGraded_apply]

/-- Two elements of the Rees quotient with the same coefficients in every degree are equal. -/
theorem ext_coeff {p q : I.ReesQuotient} (h : ∀ n, coeff I n p = coeff I n q) : p = q :=
  (equivAssociatedGraded I).injective (DirectSum.ext h)

/-- Elements of the Rees quotient are equal exactly when all their coefficients agree. -/
theorem ext_coeff_iff {p q : I.ReesQuotient} : p = q ↔ ∀ n, coeff I n p = coeff I n q :=
  ⟨fun h _ ↦ h ▸ rfl, ext_coeff⟩

variable (I) in
/-- The inclusion `Iⁿ ⧸ Iⁿ⁺¹ → R[It] ⧸ I R[It]` of the degree-`n` piece, sending the class of
`x ∈ Iⁿ` to the class of the Rees monomial `x tⁿ` (`Ideal.ReesQuotient.of_mk`). -/
noncomputable def of (n : ℕ) : I.GradedPiece n →ₗ[R] I.ReesQuotient :=
  ((equivAssociatedGraded I).symm.toLinearMap.restrictScalars R) ∘ₗ
    DirectSum.lof R ℕ I.GradedPiece n

/-- The degree-`n` inclusion corresponds to the summand inclusion of `gr_I R`. -/
@[simp]
theorem equivAssociatedGraded_of (n : ℕ) (x : I.GradedPiece n) :
    equivAssociatedGraded I (of I n x) = DirectSum.of I.GradedPiece n x := by
  rw [of, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, DirectSum.lof_eq_of]

/-- The degree-`n` inclusion sends the class of `x ∈ Iⁿ` to the class of `x tⁿ`. -/
@[simp]
theorem of_mk (n : ℕ) (x : ↥(I ^ n)) : of I n (Submodule.Quotient.mk x) = mk I n x := by
  apply (equivAssociatedGraded I).injective
  rw [equivAssociatedGraded_of, equivAssociatedGraded_mk, AssociatedGraded.mk_apply]

/-- The degree-`n` coefficient retracts the degree-`n` inclusion. -/
@[simp]
theorem coeff_of_self (n : ℕ) (x : I.GradedPiece n) : coeff I n (of I n x) = x := by
  rw [coeff_apply, equivAssociatedGraded_of, DirectSum.of_eq_same]

/-- The degree-`n` coefficient kills the pieces of every other degree. -/
theorem coeff_of_of_ne {m n : ℕ} (h : m ≠ n) (x : I.GradedPiece m) : coeff I n (of I m x) = 0 := by
  rw [coeff_apply, equivAssociatedGraded_of, DirectSum.of_eq_of_ne _ _ _ h.symm]

/-- The degree-`n` coefficient of the class of `x ∈ Iⁿ` in degree `n` is the class of `x`. -/
@[simp]
theorem coeff_mk_self (n : ℕ) (x : ↥(I ^ n)) : coeff I n (mk I n x) = Submodule.Quotient.mk x := by
  rw [← of_mk, coeff_of_self]

/-- The degree-`n` coefficient of a class placed in another degree vanishes. -/
theorem coeff_mk_of_ne {m n : ℕ} (h : m ≠ n) (x : ↥(I ^ m)) : coeff I n (mk I m x) = 0 := by
  rw [← of_mk, coeff_of_of_ne h]

/-- Every element of the Rees quotient is the finite sum of the inclusions of its coefficients,
over the degrees in which its image in `gr_I R` is nonzero. -/
theorem sum_of_coeff [∀ n (x : I.GradedPiece n), Decidable (x ≠ 0)] (q : I.ReesQuotient) :
    ∑ n ∈ (equivAssociatedGraded I q).support, of I n (coeff I n q) = q := by
  apply (equivAssociatedGraded I).injective
  simp_rw [map_sum, equivAssociatedGraded_of, coeff_apply]
  exact DirectSum.sum_support_of _

/-- The class of a Rees polynomial can be reconstructed from its quotient coefficients by summing
over the support of the polynomial itself. -/
theorem sum_of_coeff_quotientMk (f : reesAlgebra I) :
    ∑ n ∈ (f : R[X]).support, of I n (coeff I n (Ideal.Quotient.mk _ f)) =
      Ideal.Quotient.mk _ f := by
  simp only [coeff_quotientMk, of_mk, mk_apply]
  simpa only [map_sum] using congrArg (Ideal.Quotient.mk
    (I.map (algebraMap R (reesAlgebra I)))) (reesAlgebra.as_sum_support f).symm

variable (I) in
/-- The image of the class map in degree `n` is the degree-`n` piece of the grading that the
homogeneous ideal `I R[It]` induces on the Rees quotient. -/
theorem range_mk (n : ℕ) :
    LinearMap.range (mk I n) = TauCeti.GradedAlgebra.quotientPiece (reesAlgebra.grade I)
      (I.map (algebraMap R (reesAlgebra I))) n := by
  ext q
  rw [LinearMap.mem_range, TauCeti.GradedAlgebra.mem_quotientPiece_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, reesAlgebra.monomial_mem_grade x.property, (mk_apply n x).symm⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨x, hx, hxf⟩ := reesAlgebra.mem_grade_iff.mp hf
    exact ⟨⟨x, hx⟩, (mk_apply n ⟨x, hx⟩).trans (congrArg (Ideal.Quotient.mk _) (Subtype.ext hxf))⟩

variable (I) in
/-- The image of the degree-`n` inclusion is the degree-`n` piece of the grading that the
homogeneous ideal `I R[It]` induces on the Rees quotient. -/
theorem range_of (n : ℕ) :
    LinearMap.range (of I n) = TauCeti.GradedAlgebra.quotientPiece (reesAlgebra.grade I)
      (I.map (algebraMap R (reesAlgebra I))) n := by
  have h : of I n ∘ₗ Submodule.mkQ _ = mk I n := LinearMap.ext (of_mk n)
  rw [← range_mk, ← h, LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ _)]

end ReesQuotient

end Ideal
