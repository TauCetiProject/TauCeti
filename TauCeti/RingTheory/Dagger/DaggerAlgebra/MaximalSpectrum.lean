/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm
public import TauCeti.RingTheory.Dagger.SupSeminorm

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Maximal spectra and the supremum seminorm of dagger algebras

Let `K` be a complete ultrametric normed field. Because the residue field at every maximal ideal of
a `K`-dagger algebra `B` is finite-dimensional over `K`, any `K`-algebra homomorphism `A →ₐ[K] B`
contracts maximal ideals to maximal ideals, even when `A` is not itself a dagger algebra. This
induces the contravariant map `TauCeti.Dagger.IsDaggerAlgebra.maximalSpectrumComap` on classical
points.

Over a nontrivially normed complete ultrametric field `K`, pulling classical points back along the
completion map `τ : A → Â` is a bijection preserving residue fields and point norms. Consequently
the completion map preserves the supremum seminorm (`TauCeti.Dagger.supSeminorm_toCompletion`), and
all spectral properties of affinoid algebras—the maximum modulus principle, contraction of
`|·|sup` along `K`-algebra homomorphisms, the bound `|a|sup ≤ ‖a‖` by the residue norm, and the
nilradical kernel `{a | |a|sup = 0}`—transfer from `Â` to `A` without assuming reducedness.

## Main definitions

* `TauCeti.Dagger.IsDaggerAlgebra.maximalSpectrumComap`: the contravariant map
  `MaximalSpectrum B → MaximalSpectrum A` induced by `f : A →ₐ[K] B` into a dagger algebra `B`.

## Main results

* `TauCeti.Dagger.IsDaggerAlgebra.comap_isMaximal`: a `K`-algebra map into a dagger algebra
  contracts maximal ideals to maximal ideals.
* `TauCeti.Dagger.supSeminorm_toCompletion`: `|τ a|sup = |a|sup`.
* `TauCeti.Dagger.IsDaggerAlgebra.exists_pointNorm_eq_supSeminorm`: maximum modulus principle for
  nonzero dagger algebras.
* `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_map_le`: `K`-algebra maps between dagger algebras
  (and from dagger algebras to affinoid algebras) contract `|·|sup`.
* `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_le_norm`: `|a|sup ≤ ‖a‖` for the residue norm.
* `TauCeti.Dagger.IsDaggerAlgebra.supSeminorm_eq_zero_iff`: `|a|sup = 0` iff `a` is nilpotent.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2, Theorem 1.7, and §1.9.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.8 and 6.2.1.
-/

public section

namespace TauCeti.Dagger

section MaximalSpectrum

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]
  {B : Type*} [CommRing B] [Algebra K B]

namespace IsDaggerAlgebra

/-- A `K`-algebra homomorphism into a dagger algebra contracts maximal ideals to maximal ideals.
The source algebra need not itself be a dagger algebra. -/
theorem comap_isMaximal [IsDaggerAlgebra K B] (f : A →ₐ[K] B) (m : Ideal B) [m.IsMaximal] :
    (m.comap f).IsMaximal := by
  let q : A ⧸ m.comap f →ₐ[K] B ⧸ m := Ideal.quotientMapₐ m f le_rfl
  have : Module.Finite K (B ⧸ m) := finite_quotient_of_isMaximal K m
  have : Module.Finite K (A ⧸ m.comap f) :=
    Module.Finite.of_injective q.toLinearMap Ideal.quotientMap_injective
  have : IsDomain (A ⧸ m.comap f) :=
    (Ideal.Quotient.isDomain_iff_prime (m.comap f)).mpr inferInstance
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
    (IsField.of_isDomain_of_finite K _)

/-- The contravariant map on maximal spectra induced by a `K`-algebra map into a dagger algebra. -/
def maximalSpectrumComap [IsDaggerAlgebra K B] (f : A →ₐ[K] B) :
    MaximalSpectrum B → MaximalSpectrum A :=
  fun x ↦ ⟨x.asIdeal.comap f, comap_isMaximal f x.asIdeal⟩

@[simp]
theorem maximalSpectrumComap_asIdeal [IsDaggerAlgebra K B] (f : A →ₐ[K] B)
    (x : MaximalSpectrum B) :
    (maximalSpectrumComap f x).asIdeal = x.asIdeal.comap f := (rfl)

@[simp]
theorem maximalSpectrumComap_id [IsDaggerAlgebra K A] :
    maximalSpectrumComap (AlgHom.id K A) = id := by
  funext x
  exact MaximalSpectrum.ext (Ideal.comap_idₐ (R := K) x.asIdeal)

@[simp]
theorem maximalSpectrumComap_comp {C : Type*} [CommRing C] [Algebra K C]
    [IsDaggerAlgebra K B] [IsDaggerAlgebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    maximalSpectrumComap (g.comp f) = maximalSpectrumComap f ∘ maximalSpectrumComap g := by
  funext x
  exact MaximalSpectrum.ext (Ideal.comap_comapₐ f g).symm

/-- A surjective `K`-algebra map into a dagger algebra induces an injective map on maximal
spectra. -/
theorem maximalSpectrumComap_injective [IsDaggerAlgebra K B] (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : Function.Injective (maximalSpectrumComap f) := fun _ _ hxy ↦
  MaximalSpectrum.ext <|
    Ideal.comap_injective_of_surjective f hf (congrArg MaximalSpectrum.asIdeal hxy)

/-- An integral injective `K`-algebra map into a dagger algebra induces a surjective map on
maximal spectra. -/
theorem maximalSpectrumComap_surjective [IsDaggerAlgebra K B] (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) (hfi : Function.Injective f) :
    Function.Surjective (maximalSpectrumComap f) := by
  algebraize [f.toRingHom]
  let _ : Algebra.IsIntegral A B := ⟨hf⟩
  intro x
  obtain ⟨m, hm, hmcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (R := A) (S := B) x.asIdeal (by
      have hinj : Function.Injective (algebraMap A B) := hfi
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le)
  exact ⟨⟨m, hm⟩, MaximalSpectrum.ext hmcomap⟩

/-- If `A` maps integrally and injectively into a dagger algebra, then its residue field at every
maximal ideal is finite over `K`. -/
theorem finite_quotient_of_isIntegral [IsDaggerAlgebra K B] (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) (hfi : Function.Injective f) (m : Ideal A) [m.IsMaximal] :
    Module.Finite K (A ⧸ m) := by
  obtain ⟨y, hy⟩ := maximalSpectrumComap_surjective f hf hfi ⟨m, inferInstance⟩
  obtain rfl : y.asIdeal.comap f = m := congrArg MaximalSpectrum.asIdeal hy
  have := finite_quotient_of_isMaximal K y.asIdeal
  exact Module.Finite.of_injective (Ideal.quotientMapₐ y.asIdeal f le_rfl).toLinearMap
    Ideal.quotientMap_injective

end IsDaggerAlgebra

end MaximalSpectrum

section SupSeminorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]
  {B : Type*} [CommRing B] [Algebra K B]

/-- Pulling a classical point back along a `K`-algebra map into a dagger algebra preserves the
point norm. -/
@[simp]
theorem IsDaggerAlgebra.pointNorm_maximalSpectrumComap [IsDaggerAlgebra K B] (φ : A →ₐ[K] B)
    (x : MaximalSpectrum B) (a : A) :
    pointNorm K (maximalSpectrumComap φ x) a = pointNorm K x (φ a) :=
  pointNorm_comap φ x (comap_isMaximal φ x.asIdeal) a

/-- An integral injective `K`-algebra homomorphism into a dagger algebra preserves the supremum
seminorm; the source algebra need not itself be a dagger algebra. -/
theorem IsDaggerAlgebra.supSeminorm_map_of_isIntegral [IsDaggerAlgebra K B] (φ : A →ₐ[K] B)
    (hφ : φ.toRingHom.IsIntegral) (hφi : Function.Injective φ) (a : A) :
    supSeminorm K (φ a) = supSeminorm K a := by
  rw [supSeminorm_eq_iSup, supSeminorm_eq_iSup,
    ← (maximalSpectrumComap_surjective φ hφ hφi).iSup_comp (pointNorm K · a)]
  exact iSup_congr fun y ↦ (pointNorm_maximalSpectrumComap φ y a).symm

variable [IsDaggerAlgebra K A]

variable (K) in
/-- **Completion preserves the supremum seminorm.** On any `K`-dagger algebra `A`,
`|τ a|sup = |a|sup`. -/
@[simp]
theorem supSeminorm_toCompletion (a : A) :
    supSeminorm K (toCompletion K A a) = supSeminorm K a := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  rw [supSeminorm_eq_iSup, supSeminorm_eq_iSup,
    ← (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective.iSup_comp
      (pointNorm K · a)]
  exact iSup_congr fun y ↦ (hÂ.pointNorm_maximalSpectrumComap (toCompletion K A) y a).symm

namespace IsDaggerAlgebra

/-- On a dagger algebra, `|a(x)| = 0` iff `a` lies in the maximal ideal `x`. -/
theorem pointNorm_eq_zero_iff {x : MaximalSpectrum A} {a : A} :
    pointNorm K x a = 0 ↔ a ∈ x.asIdeal := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  obtain ⟨y, rfl⟩ :=
    (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective x
  rw [hÂ.pointNorm_maximalSpectrumComap, hÂ.pointNorm_eq_zero_iff]
  simp

/-- The absolute value at a classical point of a dagger algebra is multiplicative. -/
theorem pointNorm_mul (x : MaximalSpectrum A) (a b : A) :
    pointNorm K x (a * b) = pointNorm K x a * pointNorm K x b := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  obtain ⟨y, rfl⟩ :=
    (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective x
  rw [hÂ.pointNorm_maximalSpectrumComap, hÂ.pointNorm_maximalSpectrumComap,
    hÂ.pointNorm_maximalSpectrumComap, map_mul, hÂ.pointNorm_mul]

/-- The absolute value at a classical point of a dagger algebra is ultrametric. -/
theorem pointNorm_add_le (x : MaximalSpectrum A) (a b : A) :
    pointNorm K x (a + b) ≤ max (pointNorm K x a) (pointNorm K x b) := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  obtain ⟨y, rfl⟩ :=
    (maximalSpectrumComap_toCompletion_bijective (K := K) (A := A)).surjective x
  rw [hÂ.pointNorm_maximalSpectrumComap, hÂ.pointNorm_maximalSpectrumComap,
    hÂ.pointNorm_maximalSpectrumComap, map_add]
  exact hÂ.pointNorm_add_le y _ _

/-- **Units of a dagger algebra are functions without classical zeros.** -/
theorem isUnit_iff_forall_pointNorm_ne_zero {a : A} :
    IsUnit a ↔ ∀ x : MaximalSpectrum A, pointNorm K x a ≠ 0 := by
  simp_rw [Ne, pointNorm_eq_zero_iff (K := K)]
  refine ⟨fun ha x hx ↦ x.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hx ha), fun h ↦ ?_⟩
  by_contra ha
  obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top ha)
  exact h ⟨M, hM⟩ (haM (Ideal.mem_span_singleton_self a))

/-- The absolute value of the inverse of a unit at a classical point is the inverse absolute
value. -/
theorem pointNorm_inverse (x : MaximalSpectrum A) {u : A} (hu : IsUnit u) :
    pointNorm K x (Ring.inverse u) = (pointNorm K x u)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← pointNorm_mul, Ring.inverse_mul_cancel u hu, pointNorm_one]

/-- **Maximum modulus principle for dagger algebras.** On a nonzero `K`-dagger algebra, every
element attains its supremum seminorm at a classical point. -/
theorem exists_pointNorm_eq_supSeminorm [Nontrivial A] (a : A) :
    ∃ x : MaximalSpectrum A, pointNorm K x a = supSeminorm K a := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  have : Nontrivial (completion K A) := (toCompletion_injective (K := K) (A := A)).nontrivial
  obtain ⟨y, hy⟩ := hÂ.exists_pointNorm_eq_supSeminorm (toCompletion K A a)
  refine ⟨hÂ.maximalSpectrumComap (toCompletion K A) y, ?_⟩
  rw [hÂ.pointNorm_maximalSpectrumComap, hy, supSeminorm_toCompletion]

/-- Characterization of `|a|sup ≤ r` for `0 ≤ r` on a dagger algebra. -/
theorem supSeminorm_le_iff {a : A} {r : ℝ} (hr : 0 ≤ r) :
    supSeminorm K a ≤ r ↔ ∀ x : MaximalSpectrum A, pointNorm K x a ≤ r :=
  ⟨fun h x ↦ (pointNorm_le_supSeminorm x a).trans h, supSeminorm_le hr⟩

/-- Characterization of `|a|sup < r` for `0 < r` on a dagger algebra. -/
theorem supSeminorm_lt_iff {a : A} {r : ℝ} (hr : 0 < r) :
    supSeminorm K a < r ↔ ∀ x : MaximalSpectrum A, pointNorm K x a < r := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have : IsEmpty (MaximalSpectrum A) := ⟨fun x ↦ x.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    simp [supSeminorm_eq_zero_of_subsingleton a, hr]
  · refine ⟨fun h x ↦ (pointNorm_le_supSeminorm x a).trans_lt h, fun h ↦ ?_⟩
    obtain ⟨x, hx⟩ := exists_pointNorm_eq_supSeminorm (K := K) a
    exact hx ▸ h x

/-- Any `K`-algebra map out of a dagger algebra that contracts maximal ideals to maximal ideals
does not increase the supremum seminorm. -/
theorem supSeminorm_map_le_of_forall_isMaximal (φ : A →ₐ[K] B)
    (hφ : ∀ y : MaximalSpectrum B, (y.asIdeal.comap φ).IsMaximal) (a : A) :
    supSeminorm K (φ a) ≤ supSeminorm K a :=
  supSeminorm_le (supSeminorm_nonneg a) fun y ↦ by
    rw [← pointNorm_comap φ y (hφ y)]
    exact pointNorm_le_supSeminorm _ a

/-- **`K`-algebra homomorphisms of dagger algebras contract the supremum seminorm.** -/
theorem supSeminorm_map_le [IsDaggerAlgebra K B] (φ : A →ₐ[K] B) (a : A) :
    supSeminorm K (φ a) ≤ supSeminorm K a :=
  supSeminorm_map_le_of_forall_isMaximal φ (fun y ↦ comap_isMaximal φ y.asIdeal) a

/-- A `K`-algebra homomorphism from a dagger algebra into an affinoid algebra contracts the
supremum seminorm. -/
theorem supSeminorm_map_le_of_isAffinoidAlgebra (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B)
    (a : A) : supSeminorm K (φ a) ≤ supSeminorm K a :=
  supSeminorm_map_le_of_forall_isMaximal φ (fun y ↦ hB.comap_isMaximal φ y.asIdeal) a

/-- **The supremum seminorm is bounded by the residue norm.** -/
theorem supSeminorm_le_norm (a : A) :
    letI := residueNormedCommRing K A
    supSeminorm K a ≤ ‖a‖ :=
  letI := residueNormedCommRing K A
  by
  obtain ⟨f, rfl, hf⟩ := exists_presentation_norm_eq K A a
  exact hf ▸ washnitzerAlgebra.supSeminorm_map_le_norm (presentation_surjective K A) f

/-- **The kernel of the supremum seminorm on a dagger algebra is the nilradical.** -/
theorem supSeminorm_eq_zero_iff {a : A} : supSeminorm K a = 0 ↔ IsNilpotent a := by
  have hÂ : IsAffinoidAlgebra K (completion K A) := isAffinoidAlgebra_completion
  rw [← supSeminorm_toCompletion K, hÂ.supSeminorm_eq_zero_iff]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, toCompletion_injective (K := K) (A := A) (by simpa using hn)⟩,
    fun h ↦ h.map (toCompletion K A)⟩

/-- A dagger algebra is reduced iff the supremum seminorm separates points. -/
theorem isReduced_iff_supSeminorm_eq_zero :
    IsReduced A ↔ ∀ a : A, supSeminorm K a = 0 → a = 0 := by
  simp_rw [supSeminorm_eq_zero_iff (K := K), isReduced_iff]

end IsDaggerAlgebra

end SupSeminorm

end TauCeti.Dagger
