/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Localization of the nodal equation at the closed point

For a local ring `R` and `π` in its maximal ideal, the image of `(𝔪_R, x, y)` in
`NodeAlgebra R (π ^ n)` is prime exactly when `n ≠ 0`. Its localization is the quotient
of the ambient polynomial local ring by `xy - πⁿ`. This comparison needs no regularity
hypothesis on the base ring and transfers local invariants of the hypersurface to the node
algebra. Simp lemmas describe the comparison and its inverse on polynomial representatives.
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

variable {R : Type*} [CommRing R] [IsLocalRing R] {π : R}

/-- For `n ≠ 0`, the node equation `xy - πⁿ` lies in `𝔪 = (𝔪_R, x, y)`. -/
theorem X_mul_X_sub_C_pow_mem_comap_maximalIdeal (hπ : π ∈ maximalIdeal R) {n : ℕ}
    (hn : n ≠ 0) :
    X 0 * X 1 - C (π ^ n) ∈
      (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R) := by
  simpa [hn] using hπ

/-- For `n ≠ 0`, the node equation lies in the maximal ideal of the ambient polynomial
local ring `R[x, y]_𝔪`. -/
theorem algebraMap_X_mul_X_sub_C_pow_mem_maximalIdeal (hπ : π ∈ maximalIdeal R) {n : ℕ}
    (hn : n ≠ 0) :
    algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap
          (constantCoeff : MvPolynomial (Fin 2) R →+* R))) (X 0 * X 1 - C (π ^ n)) ∈
      maximalIdeal (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R))) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ ((maximalIdeal R).comap constantCoeff) _).mpr
    (X_mul_X_sub_C_pow_mem_comap_maximalIdeal hπ hn)

/-- For `2 ≤ n`, the node equation lies in the square of the maximal ideal of the ambient
polynomial local ring `R[x, y]_𝔪`, since it has no linear term. -/
theorem algebraMap_X_mul_X_sub_C_pow_mem_maximalIdeal_sq (hπ : π ∈ maximalIdeal R) {n : ℕ}
    (hn : 2 ≤ n) :
    algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap
          (constantCoeff : MvPolynomial (Fin 2) R →+* R))) (X 0 * X 1 - C (π ^ n)) ∈
      maximalIdeal (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R))) ^ 2 := by
  have hmem (p : MvPolynomial (Fin 2) R) (hp : constantCoeff p ∈ maximalIdeal R) :
      algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R))) p ∈ maximalIdeal _ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ ((maximalIdeal R).comap constantCoeff) p).mpr
      hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [map_sub, map_mul, C_pow, map_pow, pow_add, pow_two, pow_two]
  exact sub_mem (mul_mem_mul (hmem _ (by simp)) (hmem _ (by simp)))
    (mul_mem_right _ _ (mul_mem_mul (hmem _ (by simpa using hπ)) (hmem _ (by simpa using hπ))))

/-- If the image of `𝔪 = (𝔪_R, x, y)` in `R[x, y] ⧸ (xy - a)` is a prime ideal, then `a` lies
in `𝔪_R`: otherwise `xy = a` is a unit, so the image of `x` is a unit in that ideal. -/
theorem mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C {a : R}
    [h : (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk a)).IsPrime] :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hX0 : X (0 : Fin 2) ∈
      (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R) := by simp
  have hu := (notMem_maximalIdeal.mp ha).map (algebraMap R (NodeAlgebra R a))
  rw [← NodeAlgebra.coord_zero_mul_coord_one] at hu
  refine h.ne_top (eq_top_of_isUnit_mem _ (mem_map_of_mem _ hX0) ?_)
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, NodeAlgebra.mk_X] using
    isUnit_of_mul_isUnit_left hu

/-- If the image of `𝔪 = (𝔪_R, x, y)` in `R[x, y] ⧸ (xy - πⁿ)` is a prime ideal, then `π` lies
in `𝔪_R`. -/
theorem mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C_pow (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    π ∈ maximalIdeal R :=
  (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem n
    mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C

/-- The image of `𝔪 = (𝔪_R, x, y)` in `R[x, y] ⧸ (xy - πⁿ)` is a prime ideal exactly when
`n ≠ 0`, that is, exactly when the origin of the special fibre lies on the model. -/
theorem isPrime_map_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R) (n : ℕ) :
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime ↔ n ≠ 0 := by
  refine ⟨?_, fun hn ↦ map_isPrime_of_surjective
    (f := NodeAlgebra.mk (π ^ n)) (NodeAlgebra.mk_surjective _) ?_⟩
  · -- for `n = 0` the constant `πⁿ = 1` is a unit, so it does not lie in `𝔪_R`
    rintro h rfl
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp
      (mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C (a := π ^ 0))) (by simp)
  · rw [AlgHom.ker_coe, NodeAlgebra.ker_mk, span_le, Set.singleton_subset_iff,
      SetLike.mem_coe]
    exact X_mul_X_sub_C_pow_mem_comap_maximalIdeal hπ hn

private noncomputable def nodeToLocalQuotient (n : ℕ) :
    NodeAlgebra R (π ^ n) →ₐ[R]
      (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
          span {(algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime ((maximalIdeal R).comap
              (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
            (X 0 * X 1 - C (π ^ n)))}) := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let J := span {algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))}
  let φ : MvPolynomial (Fin 2) R →ₐ[R] B ⧸ J :=
    (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) B)
  have hφ : φ (X 0) * φ (X 1) = algebraMap R (B ⧸ J) (π ^ n) := by
    have h : φ (X 0 * X 1 - C (π ^ n)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_span_singleton_self _)
    simpa only [map_sub, map_mul, ← algebraMap_eq, AlgHom.commutes, sub_eq_zero] using h
  exact NodeAlgebra.lift (π ^ n) (φ (X 0)) (φ (X 1)) hφ

private theorem nodeToLocalQuotient_comp_mk (n : ℕ) :
    (nodeToLocalQuotient (π := π) n).comp (NodeAlgebra.mk (π ^ n)) =
      (Ideal.Quotient.mkₐ R _).comp
        (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R)
          (Localization.AtPrime ((maximalIdeal R).comap constantCoeff))) := by
  ext i
  fin_cases i <;> simp [nodeToLocalQuotient]

private theorem nodeToLocalQuotient_mk (n : ℕ) (p : MvPolynomial (Fin 2) R) :
    nodeToLocalQuotient (π := π) n (NodeAlgebra.mk (π ^ n) p) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap constantCoeff)) p) := by
  simpa using AlgHom.congr_fun (nodeToLocalQuotient_comp_mk (π := π) n) p

/-- The node algebra acts on the quotient of the ambient polynomial local ring through
`nodeToLocalQuotient`. -/
private noncomputable abbrev nodeToLocalQuotientAlgebra (n : ℕ) :
    Algebra (NodeAlgebra R (π ^ n))
      (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
          span {(algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime ((maximalIdeal R).comap
              (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
            (X 0 * X 1 - C (π ^ n)))}) :=
  RingHom.toAlgebra (S := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
      span {(algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap
          (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
        (X 0 * X 1 - C (π ^ n)))}) (nodeToLocalQuotient (π := π) n).toRingHom

/-- The quotient of the ambient polynomial local ring by the node equation is a localization
of the node algebra at the image of `𝔪`, the node algebra acting through
`nodeToLocalQuotient`. -/
private theorem isLocalization_nodeToLocalQuotient (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    letI := nodeToLocalQuotientAlgebra (π := π) n
    IsLocalization
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n))).primeCompl
      (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
          span {(algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime ((maximalIdeal R).comap
              (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
            (X 0 * X 1 - C (π ^ n)))}) := by
  let := nodeToLocalQuotientAlgebra (π := π) n
  let 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)
  let q : MvPolynomial (Fin 2) R →+* NodeAlgebra R (π ^ n) := NodeAlgebra.mk (π ^ n)
  let B := Localization.AtPrime 𝔪
  let J := span {algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))}
  have hloc := IsLocalization.of_surjective (S := B) (S' := B ⧸ J) 𝔪.primeCompl q
      (NodeAlgebra.mk_surjective _) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (congrArg AlgHom.toRingHom (nodeToLocalQuotient_comp_mk (π := π) n).symm)
      (by
        simp only [q, mk_ker, NodeAlgebra.ker_mk,
          Ideal.map_span, Set.image_singleton]
        exact le_rfl)
  have hq : 𝔪.map q = 𝔪.map (NodeAlgebra.mk (π ^ n)) := map_coe _ _
  have hcomap : (𝔪.map (NodeAlgebra.mk (π ^ n))).comap q = 𝔪 := by
    rw [← hq, comap_map_of_surjective' q (NodeAlgebra.mk_surjective _)]
    simp only [q, NodeAlgebra.ker_mk]
    rw [sup_eq_left, span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have hπ : π ∈ maximalIdeal R := mem_maximalIdeal_of_isPrime_map_quotient_X_mul_X_sub_C_pow n
    exact X_mul_X_sub_C_pow_mem_comap_maximalIdeal hπ
      ((isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance)
  have hsub := map_primeCompl_comap_of_surjective q (NodeAlgebra.mk_surjective (π ^ n))
    (𝔪.map (NodeAlgebra.mk (π ^ n)))
  simp only [hcomap] at hsub
  rwa [hsub] at hloc

private theorem isUnit_nodeToLocalQuotient (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime]
    (y : (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).primeCompl) :
    IsUnit (nodeToLocalQuotient (π := π) n y) := by
  let := nodeToLocalQuotientAlgebra (π := π) n
  have := isLocalization_nodeToLocalQuotient (π := π) n
  exact ((isLocalization_iff _ _).mp this).1 y

private theorem bijective_lift_nodeToLocalQuotient (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    Function.Bijective (IsLocalization.lift (S := Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)))) (P := (Localization.AtPrime ((maximalIdeal R).comap
            (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
              span {(algebraMap (MvPolynomial (Fin 2) R)
                (Localization.AtPrime ((maximalIdeal R).comap
                  (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
                (X 0 * X 1 - C (π ^ n)))}))
      (g := (nodeToLocalQuotient (π := π) n).toRingHom) (isUnit_nodeToLocalQuotient n)) := by
  let := nodeToLocalQuotientAlgebra (π := π) n
  have := isLocalization_nodeToLocalQuotient (π := π) n
  exact IsLocalization.bijective (((maximalIdeal R).comap constantCoeff).map
    (NodeAlgebra.mk (π ^ n))).primeCompl _ (IsLocalization.lift_comp _)

/-- The local ring of a node at the image of `(𝔪_R, x, y)` is the quotient of the ambient
polynomial local ring by the node equation. -/
noncomputable def localizationQuotientXMulXSubCPowEquiv (π : R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n))) ≃+*
      (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
          span {(algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime ((maximalIdeal R).comap
              (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
            (X 0 * X 1 - C (π ^ n)))}) :=
  RingEquiv.ofBijective _ (bijective_lift_nodeToLocalQuotient (π := π) n)

/-- The localization comparison sends a polynomial representative to its image in the
quotient of the ambient local ring. -/
@[simp]
theorem localizationQuotientXMulXSubCPowEquiv_algebraMap_mk
    (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] (p : MvPolynomial (Fin 2) R) :
    localizationQuotientXMulXSubCPowEquiv π n
        (algebraMap _ _ (NodeAlgebra.mk (π ^ n) p)) =
      algebraMap (MvPolynomial (Fin 2) R) _ p := by
  rw [localizationQuotientXMulXSubCPowEquiv, RingEquiv.ofBijective_apply, IsLocalization.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, nodeToLocalQuotient_mk,
    Ideal.Quotient.mk_algebraMap]

/-- The localization comparison sends a coordinate of the node algebra to the class of the
corresponding polynomial variable. -/
@[simp]
theorem localizationQuotientXMulXSubCPowEquiv_algebraMap_coord
    (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] (i : Fin 2) :
    localizationQuotientXMulXSubCPowEquiv π n
        (algebraMap _ _ (NodeAlgebra.coord (π ^ n) i)) =
      algebraMap (MvPolynomial (Fin 2) R) _ (X i) := by
  rw [← NodeAlgebra.mk_X, localizationQuotientXMulXSubCPowEquiv_algebraMap_mk]

/-- Composed with the localization map and the quotient map from polynomials, the
localization comparison is the quotient map of the ambient local ring. -/
theorem localizationQuotientXMulXSubCPowEquiv_comp_algebraMap_comp_mk
    (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] :
    ((localizationQuotientXMulXSubCPowEquiv π n).toRingHom.comp
        ((algebraMap (NodeAlgebra R (π ^ n)) _).comp (NodeAlgebra.mk (π ^ n)).toRingHom)) =
      algebraMap (MvPolynomial (Fin 2) R) _ :=
  RingHom.ext (localizationQuotientXMulXSubCPowEquiv_algebraMap_mk (π := π) n)

/-- The inverse localization comparison sends the class of a polynomial back to its
localized class in the node algebra. -/
@[simp]
theorem localizationQuotientXMulXSubCPowEquiv_symm_algebraMap
    (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n))).IsPrime] (p : MvPolynomial (Fin 2) R) :
    (localizationQuotientXMulXSubCPowEquiv π n).symm (algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap
          (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
            span {(algebraMap (MvPolynomial (Fin 2) R)
              (Localization.AtPrime ((maximalIdeal R).comap
                (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
              (X 0 * X 1 - C (π ^ n)))}) p) =
      algebraMap _ _ (NodeAlgebra.mk (π ^ n) p) := by
  apply (localizationQuotientXMulXSubCPowEquiv π n).injective
  simp only [RingEquiv.apply_symm_apply, localizationQuotientXMulXSubCPowEquiv_algebraMap_mk]

end TauCeti
