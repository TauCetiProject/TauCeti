/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Friendly.Conjugation

/-!
# Friendly places through decomposition groups

Let `K` be a number field with largest totally real or CM subfield `E_K`, and let `L` be a number
field containing `K`, with a prime `Q` of `𝓞 L` above the place `v` of `K`. An automorphism `δ`
of `L` in the decomposition group of `Q` (`δ • Q = Q`) that acts on `E_K` as its complex
conjugation `c` fixes the place `u` of `E_K` below `v`: the place below `δ • Q` is `c • u`. With
`IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_complexConj_smul_eq` this gives the
group-theoretic form of friendliness (Lawrence–Venkatesh, §2.4, Definition 2.7): a place `v`
unramified over `ℚ` is friendly when some element of the decomposition group at `Q` acts on `E_K`
as complex conjugation; in particular when an arithmetic Frobenius at `Q` does. Conversely, for
`L` Galois over `ℚ`, the complex conjugation of `E_K` extends to an automorphism `σ` of `L`, and
when it fixes the place `u`, the primes `σ • Q` and `Q` both lie over `u`, so some
`τ ∈ Gal(L/E_K)` moves `σ • Q` to `Q`, and `τ σ` lies in the decomposition group of `Q`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.complexConj_smul_under_eq_of_smul_eq`: an element of the
  decomposition group at `Q` acting on `E_K` as complex conjugation fixes the place of `E_K`
  below `v`.
* `IsDedekindDomain.HeightOneSpectrum.exists_smul_eq_of_complexConj_smul_under_eq`: conversely,
  for `L` Galois over `ℚ`, if complex conjugation fixes that place, it extends to an element of
  the decomposition group at `Q`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_of_smul_eq`: if, when `E_K` is CM, some element
  of the decomposition group at `Q` acts on `E_K` as complex conjugation, then the place `v` below
  `Q` is friendly when it is unramified over `ℚ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_exists_smul_eq`: for `L` Galois over `ℚ`, `v`
  is friendly if and only if it is unramified over `ℚ` and, when `E_K` is CM, some element of the
  decomposition group at `Q` acts on `E_K` as complex conjugation.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_of_isArithFrobAt`: **the Frobenius criterion**,
  if an arithmetic Frobenius at `Q` acts on `E_K` as complex conjugation, the place `v` below `Q`
  is friendly when it is unramified over `ℚ`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4,
  Definition 2.7.
-/

public section

open NumberField TauCeti.NumberField

open scoped Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- If `δ ∈ Gal(L/ℚ)` acts on `E_K` as its complex conjugation `c`, the prime of `𝓞 E_K` below
`δ • Q` is `c` applied to the prime below `Q`. -/
private theorem under_smul_eq_complexConj_smul [IsCMField (maximalRealOrCMSubfield K)]
    (Q : Ideal (𝓞 L)) (δ : L ≃ₐ[ℚ] L)
    (hδ : ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
      algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x)) :
    (δ • Q).under (𝓞 (maximalRealOrCMSubfield K)) =
      IsCMField.complexConj (maximalRealOrCMSubfield K) •
        Q.under (𝓞 (maximalRealOrCMSubfield K)) := by
  set E := maximalRealOrCMSubfield K
  set c := IsCMField.complexConj E
  -- `δ` intertwines `c` on `𝓞 E` with its own action on `𝓞 L`, through `E ⊆ K ⊆ L`
  have hc (y : 𝓞 E) : algebraMap (𝓞 E) (𝓞 L) (c • y) = δ • algebraMap (𝓞 E) (𝓞 L) y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [algebraMap_smul_eq_apply, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 E) E L, IsScalarTower.algebraMap_apply E K L,
      Subfield.algebraMap_ofSubfield, Subfield.coe_subtype, hδ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.under_def,
    Ideal.mem_comap, Ideal.mem_comap, ← smul_inv_smul c y, hc, inv_smul_smul,
    Ideal.smul_mem_pointwise_smul_iff]

/-- **The decomposition group and complex conjugation.** Let `Q` be a prime of `𝓞 L` above the
place `v` of `K`. If `δ ∈ Gal(L/ℚ)` lies in the decomposition group of `Q` and acts on `E_K` as
its complex conjugation `c`, then `c` fixes the place of `E_K` below `v`. -/
theorem complexConj_smul_under_eq_of_smul_eq [IsCMField (maximalRealOrCMSubfield K)]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.LiesOver v.asIdeal]
    (δ : L ≃ₐ[ℚ] L) (hQ : δ • Q = Q)
    (hδ : ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
      algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x)) :
    IsCMField.complexConj (maximalRealOrCMSubfield K) •
        v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) =
      v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) := by
  rw [Ideal.over_def Q (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))),
    ← under_smul_eq_complexConj_smul Q δ hδ, hQ]

/-- **Complex conjugation extends into the decomposition group.** Let `L` be Galois over `ℚ` and
`Q` a prime of `𝓞 L` above the place `v` of `K`. If the complex conjugation `c` of `E_K` fixes
the place of `E_K` below `v`, then some `δ ∈ Gal(L/ℚ)` in the decomposition group of `Q` acts on
`E_K` as `c`. -/
theorem exists_smul_eq_of_complexConj_smul_under_eq [IsGalois ℚ L]
    [IsCMField (maximalRealOrCMSubfield K)] (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : IsCMField.complexConj (maximalRealOrCMSubfield K) •
        v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) =
      v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))) :
    ∃ δ : L ≃ₐ[ℚ] L, δ • Q = Q ∧ ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
      algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x) := by
  set E := maximalRealOrCMSubfield K
  set c := IsCMField.complexConj E
  have : IsScalarTower ℚ E L := .of_algebraMap_eq fun x ↦ by simp
  have : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  -- extend `c` to an automorphism `σ` of `L`
  set σ : L ≃ₐ[ℚ] L := (c.restrictScalars ℚ).liftNormal L
  have hσ (x : E) : σ (algebraMap K L x) = algebraMap K L (c x) :=
    AlgEquiv.liftNormal_commutes (c.restrictScalars ℚ) L x
  -- `σ • Q` and `Q` lie over the same prime of `𝓞 E`
  have hσQ : (σ • Q).LiesOver (Q.under (𝓞 E)) :=
    ⟨by rw [under_smul_eq_complexConj_smul Q σ hσ, ← Ideal.over_def Q (v.asIdeal.under (𝓞 E)), h]⟩
  obtain ⟨τ, hτ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 E)) (σ • Q) Q (L ≃ₐ[E] L)
  refine ⟨τ.restrictScalars ℚ * σ, ?_, fun x ↦ ?_⟩
  · -- `τ` acts on ideals of `𝓞 L` as its restriction of scalars
    have hτℚ : MulSemiringAction.toRingHom _ (𝓞 L) (τ.restrictScalars ℚ) =
        MulSemiringAction.toRingHom _ (𝓞 L) τ := by
      refine RingHom.ext fun z ↦ ?_
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      simp only [MulSemiringAction.toRingHom_apply, algebraMap_smul_eq_apply,
        AlgEquiv.restrictScalars_apply]
    rw [mul_smul, Ideal.pointwise_smul_def, hτℚ, ← Ideal.pointwise_smul_def, hτ]
  · rw [AlgEquiv.mul_apply, hσ, AlgEquiv.restrictScalars_apply]
    exact τ.commutes (c x)

/-- **Friendly places through the decomposition group.** Let `Q` be a prime of `𝓞 L` above the
place `v` of `K`, with `v` unramified over `ℚ`. If, when `E_K` is CM, some `δ ∈ Gal(L/ℚ)` in the
decomposition group of `Q` acts on `E_K` as its complex conjugation, then `v` is friendly. -/
theorem isFriendly_of_smul_eq (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L))
    [Q.LiesOver v.asIdeal] (he : v.asIdeal.ramificationIdx ℤ = 1)
    (h : ∀ [IsCMField (maximalRealOrCMSubfield K)], ∃ δ : L ≃ₐ[ℚ] L, δ • Q = Q ∧
      ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
        algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x)) :
    IsFriendly v := by
  refine (isFriendly_iff_complexConj_smul_eq v).2 ⟨he, ?_⟩
  intro hCM
  obtain ⟨δ, hQ, hδ⟩ := @h hCM
  exact complexConj_smul_under_eq_of_smul_eq v Q δ hQ hδ

/-- **Friendly places through decomposition groups** (Lawrence–Venkatesh, §2.4, Definition 2.7).
Let `L` be Galois over `ℚ` and `Q` a prime of `𝓞 L` above the place `v` of `K`. Then `v` is
friendly if and only if it is unramified over `ℚ` and, when `E_K` is CM, some `δ ∈ Gal(L/ℚ)` in
the decomposition group of `Q` acts on `E_K` as its complex conjugation. -/
theorem isFriendly_iff_exists_smul_eq [IsGalois ℚ L] (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 ∧
      ∀ [IsCMField (maximalRealOrCMSubfield K)], ∃ δ : L ≃ₐ[ℚ] L, δ • Q = Q ∧
        ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
          algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x) := by
  refine ⟨fun h ↦ ⟨h.ramificationIdx_eq_one, ?_⟩, fun h ↦ isFriendly_of_smul_eq v Q h.1 h.2⟩
  intro hCM
  exact exists_smul_eq_of_complexConj_smul_under_eq v Q
    ((isFriendly_iff_complexConj_smul_eq v).1 h).2

/-- **The Frobenius criterion for friendliness.** Let `Q` be a prime of `𝓞 L` above the place `v`
of `K`, with `v` unramified over `ℚ`. If, when `E_K` is CM, an arithmetic Frobenius `δ` at `Q`
acts on `E_K` as its complex conjugation, then `v` is friendly. -/
theorem isFriendly_of_isArithFrobAt (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] (he : v.asIdeal.ramificationIdx ℤ = 1) (δ : L ≃ₐ[ℚ] L)
    (hF : IsArithFrobAt ℤ δ Q)
    (hδ : ∀ [IsCMField (maximalRealOrCMSubfield K)], ∀ x : maximalRealOrCMSubfield K,
      δ (algebraMap K L x) =
        algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x)) :
    IsFriendly v :=
  isFriendly_of_smul_eq v Q he ⟨δ, hF.mem_stabilizer, hδ⟩

end IsDedekindDomain.HeightOneSpectrum
