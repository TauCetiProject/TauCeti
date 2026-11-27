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
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_of_smul_eq`: such an element makes every place
  `v` unramified over `ℚ` friendly.
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

/-- An automorphism `δ` of `L` acting on `E_K` as its complex conjugation `c` intertwines `c` on
`𝓞 E_K` and `δ` on `𝓞 L`. -/
theorem algebraMap_complexConj_smul_eq_smul [IsCMField (maximalRealOrCMSubfield K)]
    (δ : L ≃ₐ[ℚ] L)
    (hδ : ∀ x : maximalRealOrCMSubfield K, δ (algebraMap K L x) =
      algebraMap K L (IsCMField.complexConj (maximalRealOrCMSubfield K) x))
    (x : 𝓞 (maximalRealOrCMSubfield K)) :
    algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K)
        (IsCMField.complexConj (maximalRealOrCMSubfield K) • x)) =
      δ • algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K) x) := by
  -- route both sides through `E_K ⊆ K ⊆ L`
  have h (y : 𝓞 (maximalRealOrCMSubfield K)) :
      algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K) y)) =
        algebraMap K L (algebraMap _ (maximalRealOrCMSubfield K) y) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L,
      ← IsScalarTower.algebraMap_apply _ (𝓞 K) K,
      IsScalarTower.algebraMap_apply _ (maximalRealOrCMSubfield K) K]
    rfl
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  rw [h, algebraMap_smul_eq_apply, algebraMap_smul_eq_apply, h]
  exact (hδ _).symm

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
  set c := IsCMField.complexConj (maximalRealOrCMSubfield K)
  have hc : c⁻¹ = c :=
    inv_eq_iff_mul_eq_one.2 (AlgEquiv.ext (IsCMField.complexConj_apply_apply _))
  -- membership in the place of `E_K` below `v` is membership of the image in `Q`
  have hmem (y : 𝓞 (maximalRealOrCMSubfield K)) :
      y ∈ v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) ↔
        algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K) y) ∈ Q := by
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.over_def Q v.asIdeal, Ideal.under_def,
      Ideal.mem_comap]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc, hmem, hmem,
    algebraMap_complexConj_smul_eq_smul δ hδ]
  nth_rw 1 [← hQ]
  exact Ideal.smul_mem_pointwise_smul_iff

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
  -- the map `𝓞 E → 𝓞 L` factors through `𝓞 K`
  have hj (y : 𝓞 E) : algebraMap (𝓞 E) (𝓞 L) y = algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 E) E L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L,
      ← IsScalarTower.algebraMap_apply _ (𝓞 K) K, IsScalarTower.algebraMap_apply _ E K]
    rfl
  have hmem (I : Ideal (𝓞 L)) (y : 𝓞 E) :
      y ∈ I.under (𝓞 E) ↔ algebraMap (𝓞 K) (𝓞 L) (algebraMap _ (𝓞 K) y) ∈ I := by
    rw [Ideal.under_def, Ideal.mem_comap, hj]
  -- extend `c` to an automorphism `σ` of `L`
  set σ : L ≃ₐ[ℚ] L := (c.restrictScalars ℚ).liftNormal L
  have hσ (x : E) : σ (algebraMap K L x) = algebraMap K L (c x) :=
    AlgEquiv.liftNormal_commutes (c.restrictScalars ℚ) L x
  have hc : c⁻¹ = c :=
    inv_eq_iff_mul_eq_one.2 (AlgEquiv.ext (IsCMField.complexConj_apply_apply _))
  -- `σ • Q` and `Q` lie over the same prime of `𝓞 E`
  have hQ : Q.under (𝓞 E) = v.asIdeal.under (𝓞 E) := by
    ext y
    rw [hmem, Ideal.under_def, Ideal.mem_comap, Ideal.over_def Q v.asIdeal, Ideal.under_def,
      Ideal.mem_comap]
  have hσQ : (σ • Q).LiesOver (Q.under (𝓞 E)) := by
    refine ⟨Ideal.ext fun y ↦ ?_⟩
    have hy : c • c • y = y := by rw [← mul_smul, inv_eq_iff_mul_eq_one.1 hc, one_smul]
    rw [hQ, ← Ideal.smul_mem_pointwise_smul_iff (a := c), h, ← hQ, hmem, hmem,
      ← Ideal.smul_mem_pointwise_smul_iff (a := σ), ← algebraMap_complexConj_smul_eq_smul σ hσ, hy]
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
