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

/-- The image of `𝔪 = (𝔪_R, x, y)` in `R[x, y] ⧸ (xy - πⁿ)` is a prime ideal exactly when
`n ≠ 0`, that is, exactly when the origin of the special fibre lies on the model. -/
theorem isPrime_map_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R) (n : ℕ) :
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime ↔ n ≠ 0 := by
  refine ⟨?_, fun hn ↦ map_isPrime_of_surjective
    (f := (NodeAlgebra.mk (π ^ n)).toRingHom) (NodeAlgebra.mk_surjective _) ?_⟩
  · -- for `n = 0` the image of `x` is a unit
    rintro h rfl
    rw [pow_zero] at h
    have hX0 : X (0 : Fin 2) ∈
        (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R) := by simp
    refine h.ne_top (eq_top_of_isUnit_mem _ (mem_map_of_mem _ hX0)
      (IsUnit.of_mul_eq_one (NodeAlgebra.coord (1 : R) 1) ?_))
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, NodeAlgebra.mk_X, map_one] using
      NodeAlgebra.coord_zero_mul_coord_one (1 : R)
  · rw [AlgHom.toRingHom_eq_coe, NodeAlgebra.ker_mk, span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_comap]
    simpa [hn] using hπ

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

/-- The local ring of a node at the image of `(𝔪_R, x, y)` is the quotient of the ambient
polynomial local ring by the node equation. -/
noncomputable def localizationQuotientXMulXSubCPowEquiv (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] :
    Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (NodeAlgebra.mk (π ^ n)).toRingHom) ≃+*
      (Localization.AtPrime ((maximalIdeal R).comap
        (constantCoeff : MvPolynomial (Fin 2) R →+* R)) ⧸
          span {(algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime ((maximalIdeal R).comap
              (constantCoeff : MvPolynomial (Fin 2) R →+* R)))
            (X 0 * X 1 - C (π ^ n)))}) := by
  let 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)
  let f : MvPolynomial (Fin 2) R := X 0 * X 1 - C (π ^ n)
  let q := (NodeAlgebra.mk (π ^ n)).toRingHom
  let B := Localization.AtPrime 𝔪
  let J := span {algebraMap (MvPolynomial (Fin 2) R) B f}
  -- `B ⧸ (f)` is the localization of `R[x, y] ⧸ (f)` at the image of `𝔪`
  let φ : MvPolynomial (Fin 2) R →ₐ[R] B ⧸ J :=
    (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) B)
  let ψ := nodeToLocalQuotient (π := π) n
  have hcomp : ψ.comp (NodeAlgebra.mk (π ^ n)) = φ := nodeToLocalQuotient_comp_mk n
  letI := RingHom.toAlgebra (R := NodeAlgebra R (π ^ n)) (S := B ⧸ J) ψ.toRingHom
  have hloc := IsLocalization.of_surjective (S := B) (S' := B ⧸ J) 𝔪.primeCompl q
      (NodeAlgebra.mk_surjective _) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (congrArg AlgHom.toRingHom hcomp.symm)
      (by
        simp only [q, mk_ker, AlgHom.toRingHom_eq_coe, NodeAlgebra.ker_mk,
          Ideal.map_span, Set.image_singleton]
        exact le_rfl)
  have hcomap : (𝔪.map q).comap q = 𝔪 := by
    rw [comap_map_of_surjective' q (NodeAlgebra.mk_surjective _)]
    simp only [q, AlgHom.toRingHom_eq_coe, NodeAlgebra.ker_mk]
    rw [sup_eq_left, span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have hn : n ≠ 0 := (isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance
    simpa [𝔪, f, hn] using hπ
  have hsub : 𝔪.primeCompl.map q = (𝔪.map q).primeCompl := by
    ext a
    refine ⟨?_, fun ha ↦ ?_⟩
    · rintro ⟨p, hp, rfl⟩
      rw [mem_primeCompl_iff, ← mem_comap, hcomap]
      exact hp
    · -- Fix the ring-hom coercion so rewriting uses the same map as `hcomap`.
      obtain ⟨p, rfl⟩ := (show Function.Surjective q from NodeAlgebra.mk_surjective (π ^ n)) a
      rw [mem_primeCompl_iff, ← mem_comap, hcomap] at ha
      exact ⟨p, ha, rfl⟩
  rw [hsub] at hloc
  let e := IsLocalization.algEquiv (𝔪.map q).primeCompl (Localization.AtPrime (𝔪.map q)) (B ⧸ J)
  exact e.toRingEquiv

/-- The localization comparison sends a polynomial representative to its image in the
quotient of the ambient local ring. -/
@[simp]
theorem localizationQuotientXMulXSubCPowEquiv_algebraMap_mk
    (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] (p : MvPolynomial (Fin 2) R) :
    localizationQuotientXMulXSubCPowEquiv hπ n
        (algebraMap _ _ (NodeAlgebra.mk (π ^ n) p)) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime ((maximalIdeal R).comap
          (constantCoeff : MvPolynomial (Fin 2) R →+* R))) p) := by
  simp only [localizationQuotientXMulXSubCPowEquiv, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.commutes]
  exact AlgHom.congr_fun (nodeToLocalQuotient_comp_mk (π := π) n) p

/-- The inverse localization comparison sends the class of a polynomial back to its
localized class in the node algebra. -/
@[simp]
theorem localizationQuotientXMulXSubCPowEquiv_symm_mk_algebraMap
    (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime] (p : MvPolynomial (Fin 2) R) :
    (localizationQuotientXMulXSubCPowEquiv hπ n).symm
        (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 2) R)
          (Localization.AtPrime ((maximalIdeal R).comap
            (constantCoeff : MvPolynomial (Fin 2) R →+* R))) p)) =
      algebraMap _ _ (NodeAlgebra.mk (π ^ n) p) := by
  apply (localizationQuotientXMulXSubCPowEquiv hπ n).injective
  simp only [RingEquiv.apply_symm_apply, localizationQuotientXMulXSubCPowEquiv_algebraMap_mk]

end TauCeti
