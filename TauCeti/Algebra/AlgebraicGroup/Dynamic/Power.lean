/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability

/-!
# Dynamic subgroups of a power of a cocharacter

For a cocharacter `λ : 𝔾ₘ → G` and an integer `n`, the power `λⁿ : t ↦ λ(tⁿ)` is again a
cocharacter. On coordinates it is `λ` followed by the substitution `T ↦ Tⁿ` of the Laurent
variable, so conjugation by the generic point of `λⁿ` is conjugation by the generic point of `λ`
followed by that substitution. For `n > 0` the substitution matches the negative coefficients
of the two conjugation families and preserves the constant coefficient. Hence

* `P(λⁿ) = P(λ)` and `U(λⁿ) = U(λ)` for `n > 0`, and the two limit homomorphisms agree;
* `Z(λⁿ) = Z(λ)` for `n ≠ 0`, because the substitution is injective.

These hold on points over every commutative value semiring, and for the defining Hopf ideals
over a commutative ring, with no field, smoothness or finite-type hypothesis.

## Main declarations

* `BialgHom.powCocharacter`: the power `λⁿ` of a cocharacter, with
  `BialgHom.powCocharacter_one`, `BialgHom.powCocharacter_powCocharacter` and
  `BialgHom.powCocharacter_neg_one` relating it to `λ`, `λ^{mn}` and the opposite cocharacter.
* `BialgHom.conjugate_powCocharacter`: generic conjugation by `λⁿ` is generic conjugation by
  `λ` followed by `T ↦ Tⁿ`; `BialgHom.coeff_conjugate_powCocharacter` is its coefficientwise
  form.
* `BialgHom.parabolic_powCocharacter`, `BialgHom.levi_powCocharacter`,
  `BialgHom.unipotent_powCocharacter` and `BialgHom.limit_powCocharacter`: the dynamic subgroups
  and the limit homomorphism of `λⁿ`.
* `BialgHom.parabolicDefiningHopfIdeal_powCocharacter`,
  `BialgHom.leviDefiningHopfIdeal_powCocharacter` and
  `BialgHom.unipotentDefiningHopfIdeal_powCocharacter`: the same closed subgroup schemes.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

section Bialgebra

variable {R H A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [CommSemiring A] [Algebra R A]

/-- The `n`-th power `t ↦ λ(tⁿ)` of a cocharacter `λ`: its composite with the `n`-th power
map of the multiplicative group. -/
noncomputable def powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) :
    H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulRight n)).comp l

/-- On coordinates the `n`-th power of a cocharacter substitutes `Tⁿ` for the Laurent
variable. -/
@[simp]
theorem powCocharacter_apply (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) (h : H) :
    l.powCocharacter n h = AddMonoidAlgebra.mapDomain (· * n) (l h) := (rfl)

/-- The first power of a cocharacter is the cocharacter itself. -/
@[simp]
theorem powCocharacter_one (l : H →ₐc[R] LaurentPolynomial R) : l.powCocharacter 1 = l := by
  ext h k : 2
  simp

/-- Powers of a cocharacter compose by multiplying the exponents: `(λᵐ)ⁿ = λ^{mn}`. -/
@[simp]
theorem powCocharacter_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (m n : ℤ) :
    (l.powCocharacter m).powCocharacter n = l.powCocharacter (m * n) := by
  ext h k : 2
  simp only [powCocharacter_apply, AddMonoidAlgebra.coeff_mapDomain, ← Finsupp.mapDomain_comp,
    Function.comp_def, mul_assoc]

/-- The power `λ⁻¹` of a cocharacter is its opposite cocharacter. -/
theorem powCocharacter_neg_one (l : H →ₐc[R] LaurentPolynomial R) :
    l.powCocharacter (-1) = l.oppositeCocharacter := by
  ext h k : 2
  simpa using Finsupp.mapDomain_apply_of_injective neg_injective (l h).coeff (-k)

/-- The `n`-th power of a cocharacter evaluates at the `n`-th power of a unit. -/
@[simp]
theorem pointsHom_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) (u : Aˣ) :
    pointsHom A (l.powCocharacter n) u = pointsHom A l (u ^ n) := by
  ext h
  rw [pointsHom_apply, pointsHom_apply, ← laurentEval_comp_mapDomainAlgHom_mulRight]
  simp [BialgHom.mapDomain_apply]

end Bialgebra

section HopfAlgebra

variable {R H A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A]

/-- **Generic conjugation by a power of a cocharacter**: conjugation by the generic point of
`λⁿ` is conjugation by the generic point of `λ` followed by the substitution `T ↦ Tⁿ`. -/
theorem conjugate_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ)
    (g : WithConv (H →ₐ[R] A)) :
    conjugate A (l.powCocharacter n) g =
      AlgHom.mapValue (AddMonoidAlgebra.mapDomainAlgHom R A (AddMonoidHom.mulRight n))
        (conjugate A l g) := by
  set ψ : LaurentPolynomial A →ₐ[R] LaurentPolynomial A :=
    AddMonoidAlgebra.mapDomainAlgHom R A (AddMonoidHom.mulRight n)
  have hu : Units.map ψ.toMonoidHom (LaurentPolynomial.genericUnit A) =
      LaurentPolynomial.genericUnit A ^ n := by
    apply Units.ext
    simp only [Units.coe_map, LaurentPolynomial.genericUnit_val,
      LaurentPolynomial.genericUnit_zpow_val, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ψ,
      LaurentPolynomial.mapDomainAlgHom_mulRight_T, one_mul]
  rw [mapValue_conjugate, hu, LaurentPolynomial.mapDomainAlgHom_mulRight_comp_toAlgHom,
    conjugate_apply,
    genericPoint_eq_pointsHom, pointsHom_powCocharacter, constPoint_apply, AlgHom.mapValue_apply]

/-- The Laurent coefficients of generic conjugation by `λⁿ` are those of generic conjugation by
`λ`, moved along the substitution `T ↦ Tⁿ` of exponents. -/
theorem coeff_conjugate_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ)
    (g : WithConv (H →ₐ[R] A)) (h : H) (k : ℤ) :
    ((conjugate A (l.powCocharacter n) g).ofConv h).coeff k =
      Finsupp.mapDomain (· * n) ((conjugate A l g).ofConv h).coeff k := by
  rw [conjugate_powCocharacter]
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidHom.coe_mulRight,
    AddMonoidAlgebra.coeff_mapDomain]

/-- **The dynamic parabolic of a positive power**: `P(λⁿ) = P(λ)` for `n > 0`. -/
theorem parabolic_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ} (hn : 0 < n) :
    parabolic A (l.powCocharacter n) = parabolic A l := by
  have hinj : Function.Injective (· * n) := mul_left_injective₀ hn.ne'
  ext g
  rw [mem_parabolic_iff_forall_coeff_conjugate_eq_zero,
    mem_parabolic_iff_forall_coeff_conjugate_eq_zero]
  refine forall_congr' fun h ↦ ?_
  simp only [coeff_conjugate_powCocharacter]
  constructor
  · intro hc k hk
    rw [← Finsupp.mapDomain_apply_of_injective hinj]
    exact hc (k * n) (mul_neg_of_neg_of_pos hk hn)
  · intro hc k hk
    by_cases hk' : k ∈ Set.range (· * n)
    · obtain ⟨j, rfl⟩ := hk'
      rw [Finsupp.mapDomain_apply_of_injective hinj]
      exact hc j (neg_of_mul_neg_left hk hn.le)
    · exact Finsupp.mapDomain_of_notMem_range _ _ hk'

/-- **The limit homomorphism of a power**: for `n ≠ 0`, a point in the dynamic parabolics of
both `λⁿ` and `λ` has the same limit for both cocharacters. -/
theorem limit_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ} (hn : n ≠ 0)
    {g : WithConv (H →ₐ[R] A)} (hgn : g ∈ parabolic A (l.powCocharacter n))
    (hg : g ∈ parabolic A l) :
    limit A (l.powCocharacter n) ⟨g, hgn⟩ = limit A l ⟨g, hg⟩ := by
  ext h
  rw [limit_apply_eq_coeff_conjugate, limit_apply_eq_coeff_conjugate,
    coeff_conjugate_powCocharacter]
  simpa only [zero_mul] using
    Finsupp.mapDomain_apply_of_injective (mul_left_injective₀ hn) _ (0 : ℤ)

/-- **The dynamic unipotent subgroup of a positive power**: `U(λⁿ) = U(λ)` for `n > 0`. -/
theorem unipotent_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ} (hn : 0 < n) :
    unipotent A (l.powCocharacter n) = unipotent A l := by
  ext g
  simp only [mem_unipotent_iff]
  constructor
  · rintro ⟨hgn, h1⟩
    have hg : g ∈ parabolic A l := by rwa [← parabolic_powCocharacter l hn]
    exact ⟨hg, by rwa [← limit_powCocharacter l hn.ne' hgn hg]⟩
  · rintro ⟨hg, h1⟩
    have hgn : g ∈ parabolic A (l.powCocharacter n) := by rwa [parabolic_powCocharacter l hn]
    exact ⟨hgn, by rwa [limit_powCocharacter l hn.ne' hgn hg]⟩

/-- **The dynamic Levi subgroup of a nonzero power**: `Z(λⁿ) = Z(λ)` for `n ≠ 0`. -/
theorem levi_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ} (hn : n ≠ 0) :
    levi A (l.powCocharacter n) = levi A l := by
  set ψ : LaurentPolynomial A →ₐ[R] LaurentPolynomial A :=
    AddMonoidAlgebra.mapDomainAlgHom R A (AddMonoidHom.mulRight n)
  have hψ : Function.Injective ψ :=
    AddMonoidAlgebra.mapDomain_injective (mul_left_injective₀ hn)
  have hconst (g : WithConv (H →ₐ[R] A)) :
      AlgHom.mapValue ψ (constPoint A g) = constPoint A g := by
    rw [constPoint_apply, AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.comp_assoc,
      LaurentPolynomial.mapDomainAlgHom_mulRight_comp_toAlgHom]
  ext g
  rw [mem_levi_iff, mem_levi_iff, conjugate_powCocharacter]
  refine Iff.trans ?_ (AlgHom.mapValue_injective hψ).eq_iff
  rw [hconst]

end HopfAlgebra

/-! ### The defining Hopf ideals -/

section HopfIdeal

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The defining Hopf ideal of the dynamic parabolic of `λⁿ` is that of `λ`, for `n > 0`. -/
theorem parabolicDefiningHopfIdeal_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ}
    (hn : 0 < n) : parabolicDefiningHopfIdeal (l.powCocharacter n) =
      parabolicDefiningHopfIdeal l := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of R H)
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal, parabolic_powCocharacter l hn]

/-- The defining Hopf ideal of the dynamic Levi of `λⁿ` is that of `λ`, for `n ≠ 0`. -/
theorem leviDefiningHopfIdeal_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ}
    (hn : n ≠ 0) : leviDefiningHopfIdeal (l.powCocharacter n) = leviDefiningHopfIdeal l := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of R H)
  intro A
  rw [quotientPointsSubgroup_leviDefiningHopfIdeal, quotientPointsSubgroup_leviDefiningHopfIdeal,
    levi_powCocharacter l hn]

/-- The defining Hopf ideal of the dynamic unipotent subgroup of `λⁿ` is that of `λ`, for
`n > 0`. -/
theorem unipotentDefiningHopfIdeal_powCocharacter (l : H →ₐc[R] LaurentPolynomial R) {n : ℤ}
    (hn : 0 < n) :
    (l.powCocharacter n).unipotentDefiningHopfIdeal = l.unipotentDefiningHopfIdeal := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := _root_.CommHopfAlgCat.of R H)
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    quotientPointsSubgroup_unipotentDefiningHopfIdeal, unipotent_powCocharacter l hn]

end HopfIdeal

end BialgHom
