/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Smoothness of dynamic parabolic subgroups

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H`, with dynamic parabolic
`P(λ)`, dynamic unipotent subgroup `U(λ)` and dynamic Levi subgroup `Z(λ)`. This file proves that
`P(λ)` is formally smooth whenever `G` is, over an arbitrary commutative base ring. Since `U(λ)`
and `Z(λ)` are retracts of `P(λ)`, all three are smooth when `G` is a smooth affine group of
finite type over a Noetherian ring, for example a field. Smoothness of `P(λ)` is part of what
makes it a parabolic subgroup in the sense of `TauCeti.HopfIdeal.IsParabolic`.

The proof is the infinitesimal lifting criterion. Let `C → C ⧸ J` be a square-zero thickening
and `g₀ ∈ P(λ)(C ⧸ J)`. By definition `T ↦ λ(T) g₀ λ(T)⁻¹` extends to a point `F₀` over
`(C ⧸ J)[X]`, and smoothness of `G` lifts `F₀` to some point `F` over `C[X]`. The lift `F` need
not be equivariant, so `F(1)` need not lie in `P(λ)(C)`. The point `Ψ = λ(T)⁻¹ F λ(T)` over
`C[T;T⁻¹]` reduces to the constant point `g₀` modulo `J`, and the constant coefficient of `Ψ` is
the required lift. It is multiplicative because the nonconstant coefficients of `Ψ` lie in the
square-zero ideal `J`. It lies in `P(λ)(C)` because on a coefficient `x` of weight `n` of
universal conjugation, `Ψ` is `F(x) · T⁻ⁿ`, whose constant coefficient is the `Xⁿ`-coefficient
of `F(x)`. That coefficient vanishes for `n < 0`.

## Main declarations

* `BialgHom.formallySmooth_quotient_parabolicDefiningHopfIdeal`: the dynamic parabolic of a
  formally smooth affine group is formally smooth.
* `BialgHom.smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal`,
  `BialgHom.smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal` and
  `BialgHom.smoothCommHopfAlgProperty_quotient_leviDefiningHopfIdeal`: the dynamic parabolic,
  unipotent and Levi subgroups of a smooth affine group of finite type over a Noetherian ring
  are smooth.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, Proposition 2.1.8(3).
* J. S. Milne, *Algebraic Groups* (2017), Theorem 13.33.
-/

public section

open CategoryTheory WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

section Lift

variable {C : Type*} [CommRing C] [Algebra R C] (l : H →ₐc[R] LaurentPolynomial R)

/-- The point `l(T)⁻¹ · F · l(T)` over `C[T;T⁻¹]` obtained from a point `F` over `C[X]`. -/
private noncomputable def twistedPoint (F : WithConv (H →ₐ[R] Polynomial C)) :
    WithConv (H →ₐ[R] LaurentPolynomial C) :=
  (genericPoint C l)⁻¹ * ofPolyPoint C F * genericPoint C l

/-- On a coefficient of weight `n` of universal conjugation, the twisted point is the value of
`F`, read as a Laurent polynomial, times `T⁻ⁿ`. -/
private theorem twistedPoint_coeff_conjugationAlgHom (F : WithConv (H →ₐ[R] Polynomial C))
    (h : H) (n : ℤ) :
    (twistedPoint l F).ofConv ((conjugationAlgHom l h).coeff n) =
      (F.ofConv ((conjugationAlgHom l h).coeff n)).toLaurent * LaurentPolynomial.T (-n) := by
  -- The twisted point is generic conjugation of `F` followed by the substitution `T' ↦ T⁻¹`.
  let ψ : LaurentPolynomial (LaurentPolynomial C) →ₐ[R] LaurentPolynomial C :=
    (laurentEval (R := LaurentPolynomial C) (LaurentPolynomial.genericUnit C)⁻¹).restrictScalars R
  have hψ : AlgHom.mapValue ψ (conjugate (LaurentPolynomial C) l (ofPolyPoint C F)) =
      twistedPoint l F := by
    have hu : Units.map ψ.toMonoidHom (LaurentPolynomial.genericUnit (LaurentPolynomial C)) =
        (LaurentPolynomial.genericUnit C)⁻¹ :=
      Units.ext (by simp [ψ])
    have hc : ψ.comp (IsScalarTower.toAlgHom R (LaurentPolynomial C)
        (LaurentPolynomial (LaurentPolynomial C))) = AlgHom.id R _ :=
      AlgHom.ext fun p ↦ by simp [ψ]
    rw [mapValue_conjugate, hu, hc, AlgHom.mapValue_id, MonoidHom.id_apply, map_inv, inv_inv,
      ← genericPoint_eq_pointsHom, twistedPoint]
  rw [← hψ, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    conjugate_ofConv_coeff_conjugationAlgHom, map_mul]
  simp only [ψ, ofPolyPoint_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.toLaurentAlg_apply, laurentEval_C, Algebra.algebraMap_self, RingHom.id_apply,
    laurentEval_T, inv_zpow', LaurentPolynomial.genericUnit_zpow_val]

/-- If `F` reduces, along `φ`, to the extension over the affine line of the conjugation family of
`g₀`, then the twisted point reduces to the constant point `g₀`. -/
private theorem mapValue_twistedPoint {D : Type*} [CommRing D] [Algebra R D] (φ : C →ₐ[R] D)
    (F : WithConv (H →ₐ[R] Polynomial C)) (g₀ : WithConv (H →ₐ[R] D))
    (hF : ofPolyPoint D (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) = conjugate D l g₀) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (twistedPoint l F) = constPoint D g₀ := by
  rw [twistedPoint, map_mul, map_mul, map_inv, mapValue_genericPoint, mapValue_ofPolyPoint, hF,
    conjugate_apply]
  group

section ConstCoeff

variable {J : Ideal C} {Ψ : WithConv (H →ₐ[R] LaurentPolynomial C)}
  {g₀ : WithConv (H →ₐ[R] C ⧸ J)}

/-- If `Ψ` reduces modulo `J` to the constant point `g₀`, then its coefficients reduce to those
of `g₀`. -/
private theorem mk_coeff_of_mapValue_eq_constPoint
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) (h : H) (n : ℤ) :
    Ideal.Quotient.mk J ((Ψ.ofConv h).coeff n) = if n = 0 then g₀.ofConv h else 0 := by
  have := congrArg (fun x : WithConv (H →ₐ[R] LaurentPolynomial (C ⧸ J)) ↦
    (x.ofConv h).coeff n) hΨ
  simpa [constPoint_apply, LaurentPolynomial.C_apply] using this

/-- The constant coefficient of a point `Ψ` over `C[T;T⁻¹]` that reduces, modulo a square-zero
ideal `J`, to a constant point. It is an algebra map because the nonconstant coefficients of `Ψ`
lie in `J`. -/
private noncomputable def constCoeffAlgHom (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) : H →ₐ[R] C where
  toFun h := (Ψ.ofConv h).coeff 0
  map_one' := by simp
  map_mul' a b := by
    have hmem (h : H) (n : ℤ) (hn : n ≠ 0) : (Ψ.ofConv h).coeff n ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_coeff_of_mapValue_eq_constPoint hΨ]
      simp [hn]
    rw [map_mul]
    exact AddMonoidAlgebra.coeff_zero_mul_of_coeff_mem hJ (hmem a) (hmem b)
  map_zero' := by simp
  map_add' a b := by simp
  commutes' r := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R C (LaurentPolynomial C),
      ← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.C_apply]
    simp

private theorem constCoeffAlgHom_apply (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) (h : H) :
    constCoeffAlgHom hJ hΨ h = (Ψ.ofConv h).coeff 0 :=
  rfl

/-- The constant coefficient of `Ψ` lifts `g₀`. -/
private theorem mkₐ_comp_constCoeffAlgHom (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) :
    (Ideal.Quotient.mkₐ R J).comp (constCoeffAlgHom hJ hΨ) = g₀.ofConv := by
  refine AlgHom.ext fun h ↦ ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, constCoeffAlgHom_apply,
    mk_coeff_of_mapValue_eq_constPoint hΨ]
  simp

end ConstCoeff

end Lift

/-- **The dynamic parabolic of a formally smooth affine group is formally smooth.** No
finite-type, field or reductivity hypothesis is needed. -/
instance formallySmooth_quotient_parabolicDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    [Algebra.FormallySmooth R H] :
    Algebra.FormallySmooth R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) := by
  refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun C _ _ J hJ f ↦ ?_
  -- The point `g₀` of `P(l)(C ⧸ J)` given by `f`, and its extension `F₀` over the affine line.
  let g₀ : WithConv (H →ₐ[R] C ⧸ J) := toConv (f.comp (Ideal.Quotient.mkₐ R _))
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : H →ₐ[R] Polynomial (C ⧸ J),
      (Polynomial.toLaurentAlg.restrictScalars R).comp F₀ = (conjugate (C ⧸ J) l g₀).ofConv := by
    refine exists_algHom_toLaurent_comp_eq_iff.mpr fun h n hn ↦ ?_
    have hI : (conjugationAlgHom l h).coeff n ∈ (parabolicDefiningHopfIdeal l).toIdeal :=
      HopfIdeal.mem_toIdeal.mpr (coeff_conjugationAlgHom_mem_parabolicDefiningHopfIdeal l h hn)
    rw [coeff_conjugate]
    simp [g₀, Ideal.Quotient.eq_zero_iff_mem.mpr hI]
  -- Lift `F₀` along the square-zero thickening `C[X] → (C ⧸ J)[X]`.
  let π := Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)
  have hπ : Function.Surjective π := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (π : Polynomial C →+* Polynomial (C ⧸ J))) := by
    refine ⟨2, ?_⟩
    simp only [π, Polynomial.toRingHom_mapAlgHom]
    rw [Polynomial.ker_mapRingHom, Ideal.Quotient.mkₐ_ker, ← Ideal.map_pow, hJ, Ideal.map_bot,
      Ideal.zero_eq_bot]
  let F := Algebra.FormallySmooth.liftOfSurjective F₀ π hπ hker
  have hF : π.comp F = F₀ := Algebra.FormallySmooth.comp_liftOfSurjective F₀ π hπ hker
  -- The twisted point `Ψ = l(T)⁻¹ · F · l(T)` reduces modulo `J` to the constant point `g₀`.
  let Ψ := twistedPoint l (toConv F)
  have hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀ := by
    refine mapValue_twistedPoint l _ _ g₀ ?_
    rw [AlgHom.mapValue_apply, ofConv_toConv, hF, ofPolyPoint_apply, ofConv_toConv, hF₀,
      toConv_ofConv]
  -- Its constant coefficient is an algebra map lifting `g₀`.
  let g := constCoeffAlgHom hJ hΨ
  -- It vanishes on the negative coefficients of universal conjugation, which generate the
  -- defining ideal of the dynamic parabolic.
  have hgI : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker g := by
    rw [parabolicDefiningHopfIdeal_toIdeal, Ideal.span_le]
    rintro _ ⟨h, n, hn, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, constCoeffAlgHom_apply,
      twistedPoint_coeff_conjugationAlgHom, ← LaurentPolynomial.T_mul,
      LaurentPolynomial.coeff_T_mul, zero_sub, neg_neg]
    exact exists_toLaurent_eq_iff.mp ⟨_, rfl⟩ n hn
  refine ⟨Ideal.Quotient.liftₐ _ g fun x hx ↦ RingHom.mem_ker.mp (hgI hx),
    Ideal.Quotient.algHom_ext R ?_⟩
  rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, mkₐ_comp_constCoeffAlgHom]

section FiniteType

variable [IsNoetherianRing R] {H : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- **The dynamic parabolic of a smooth affine group of finite type over a Noetherian ring is
smooth.** -/
theorem smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal
    [Algebra.Smooth R H] (l : H →ₐc[R] LaurentPolynomial R) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient H (parabolicDefiningHopfIdeal l)).obj := by
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- **The dynamic unipotent subgroup of a smooth affine group of finite type over a Noetherian ring
is smooth.** -/
theorem smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
    [Algebra.Smooth R H] (l : H →ₐc[R] LaurentPolynomial R) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient H l.unipotentDefiningHopfIdeal).obj := by
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- **The dynamic Levi subgroup of a smooth affine group of finite type over a Noetherian ring
is smooth.** -/
theorem smoothCommHopfAlgProperty_quotient_leviDefiningHopfIdeal
    [Algebra.Smooth R H] (l : H →ₐc[R] LaurentPolynomial R) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient H (leviDefiningHopfIdeal l)).obj := by
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end FiniteType

end BialgHom
