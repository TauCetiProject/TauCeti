/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.LaurentFraction
public import TauCeti.RingTheory.Affinoid.Subdomain.Basic

import TauCeti.RingTheory.Affinoid.QuotientNorm

import TauCeti.RingTheory.Affinoid.Restricted.PointNorm

/-!
# Laurent domains of affinoid algebras

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, and let
`f = (f₁, …, f_r)` and `g = (g₁, …, g_s)` be families in `A`. The Laurent domain

`L(f, g⁻¹) = {x ∈ Sp A : |fᵢ(x)| ≤ 1 and |gⱼ(x)| ≥ 1 for all i, j}`

is a set of classical points, that is, of maximal ideals of `A`. This file proves the universal
property of the Laurent fraction algebra `A⟨f, g⁻¹⟩ = A⟨X, Y⟩ ⧸ (Xᵢ - fᵢ, gⱼ Yⱼ - 1)` in terms of
classical points: for an affinoid algebra `B` with a complete ultrametric algebra norm, a
`K`-algebra map `φ : A → B` factors through `A⟨f, g⁻¹⟩` if and only if the induced map
`Sp B → Sp A` takes values in `L(f, g⁻¹)`, and the factorisation is then unique. In particular
every classical point of `A⟨f, g⁻¹⟩` lies over a point of `L(f, g⁻¹)`. The structure map
represents this set as an affinoid subdomain (`LaurentFraction.isAffinoidSubdomainMap`), with
no norm or topology required on the test algebras in that universal property.

The universal property is the point-free one of `TauCeti.LaurentFraction.existsUnique_algHom`
(each `φ fᵢ` is power-bounded, each `φ gⱼ` is a unit with power-bounded inverse), translated by
the pointwise descriptions of power-bounded elements
(`TauCeti.IsAffinoidAlgebra.isPowerBounded_iff_forall_pointNorm_le_one`) and of units with
power-bounded inverse (`TauCeti.IsAffinoidAlgebra.isUnit_and_isPowerBounded_inverse_iff`) in `B`.

## Main definitions

* `TauCeti.laurentDomain K f g`: the Laurent domain `L(f, g⁻¹) ⊆ Sp A`.

## Main results

* `TauCeti.IsAffinoidAlgebra.range_maximalSpectrumComap_subset_laurentDomain_iff`: `Sp B → Sp A`
  lands in `L(f, g⁻¹)` if and only if every `φ fᵢ` is power-bounded and every `φ gⱼ` is a unit
  with power-bounded inverse.
* `TauCeti.LaurentFraction.existsUnique_algHom_iff_range_subset`: the universal property of
  `A⟨f, g⁻¹⟩` in terms of classical points.
* `TauCeti.LaurentFraction.pointNorm_algebraMap_le_one` and
  `TauCeti.LaurentFraction.one_le_pointNorm_algebraMap`: `|fᵢ| ≤ 1` and `|gⱼ| ≥ 1` at every
  classical point of `A⟨f, g⁻¹⟩`.
* `TauCeti.LaurentFraction.isAffinoidSubdomainMap`: the Laurent fraction algebra represents
  the Laurent domain as an affinoid subdomain, including empty domains and nonreduced algebras.
* `TauCeti.LaurentFraction.maximalSpectrumComap_mem_laurentDomain`: the map
  `Sp A⟨f, g⁻¹⟩ → Sp A` takes values in `L(f, g⁻¹)`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.2.2 and
  7.2.3.
-/

public section

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K]

section LaurentDomain

variable {A : Type*} [CommRing A] [Algebra K A] {r s : ℕ}

variable (K) in
/-- **The Laurent domain** `L(f, g⁻¹) = {x ∈ Sp A : |fᵢ(x)| ≤ 1, |gⱼ(x)| ≥ 1 for all i, j}` of
classical points of `A`, with absolute values computed by `TauCeti.pointNorm`. When `A` is affinoid,
maps factoring through the Laurent fraction algebra `A⟨f, g⁻¹⟩` are exactly those whose classical
points land in it (`TauCeti.LaurentFraction.existsUnique_algHom_iff_range_subset`). -/
def laurentDomain (f : Fin r → A) (g : Fin s → A) : Set (MaximalSpectrum A) :=
  {x | (∀ i, pointNorm K x (f i) ≤ 1) ∧ ∀ j, 1 ≤ pointNorm K x (g j)}

@[simp]
theorem mem_laurentDomain {f : Fin r → A} {g : Fin s → A} {x : MaximalSpectrum A} :
    x ∈ laurentDomain K f g ↔ (∀ i, pointNorm K x (f i) ≤ 1) ∧ ∀ j, 1 ≤ pointNorm K x (g j) :=
  Iff.rfl

end LaurentDomain

variable [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidAlgebra

variable {A : Type*} [CommRing A] [Algebra K A] {r s : ℕ}
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

/-- **Maps landing in a Laurent domain.** For a `K`-algebra map `φ : A → B` into an affinoid
algebra with a complete ultrametric algebra norm, the induced map `Sp B → Sp A` takes values in
the Laurent domain `L(f, g⁻¹)` if and only if every `φ fᵢ` is power-bounded and every `φ gⱼ` is a
unit of `B` with power-bounded inverse. -/
theorem range_maximalSpectrumComap_subset_laurentDomain_iff (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) {f : Fin r → A} {g : Fin s → A} :
    Set.range (hB.maximalSpectrumComap φ) ⊆ laurentDomain K f g ↔
      (∀ i, Huber.IsPowerBounded (φ (f i))) ∧
        ∀ j, IsUnit (φ (g j)) ∧ Huber.IsPowerBounded (Ring.inverse (φ (g j))) := by
  simp_rw [hB.isUnit_and_isPowerBounded_inverse_iff, hB.isPowerBounded_iff_forall_pointNorm_le_one,
    Set.range_subset_iff, mem_laurentDomain, pointNorm_maximalSpectrumComap]
  exact ⟨fun h ↦ ⟨fun i y ↦ (h y).1 i, fun j y ↦ (h y).2 j⟩,
    fun ⟨hf, hg⟩ y ↦ ⟨fun i ↦ hf i y, fun j ↦ hg j y⟩⟩

end IsAffinoidAlgebra

namespace LaurentFraction

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]
  (hA : IsAffinoidAlgebra K A) {r s : ℕ} {f : Fin r → A} {g : Fin s → A}
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  (hB : IsAffinoidAlgebra K B)

include hA hB in
/-- **The universal property of `A⟨f, g⁻¹⟩` in terms of classical points.** Let `A` and `B` be
affinoid algebras with complete ultrametric algebra norms. A `K`-algebra map `φ : A → B` extends to
a `K`-algebra map `A⟨f, g⁻¹⟩ → B` if and only if the induced map `Sp B → Sp A` takes values in the
Laurent domain `L(f, g⁻¹)`, and the extension is then unique. -/
theorem existsUnique_algHom_iff_range_subset (φ : A →ₐ[K] B) :
    (∃! ψ : LaurentFraction f g →ₐ[K] B, ∀ a, ψ (algebraMap A _ a) = φ a) ↔
      Set.range (hB.maximalSpectrumComap φ) ⊆ laurentDomain K f g := by
  rw [existsUnique_algHom hA hB, hB.range_maximalSpectrumComap_subset_laurentDomain_iff]

include hA in
/-- Each `fᵢ` has absolute value at most one at every classical point of `A⟨f, g⁻¹⟩`. -/
theorem pointNorm_algebraMap_le_one (x : MaximalSpectrum (LaurentFraction f g)) (i : Fin r) :
    pointNorm K x (algebraMap A (LaurentFraction f g) (f i)) ≤ 1 :=
  mk_X_castAdd (g := g) i ▸ hA.pointNorm_quotientMk_X_le_one x _

include hA in
/-- Each `gⱼ` has absolute value at least one at every classical point of `A⟨f, g⁻¹⟩`. -/
theorem one_le_pointNorm_algebraMap (x : MaximalSpectrum (LaurentFraction f g)) (j : Fin s) :
    1 ≤ pointNorm K x (algebraMap A (LaurentFraction f g) (g j)) := by
  -- `|gⱼ(x)| · |gⱼ⁻¹(x)| = 1` with `|gⱼ⁻¹(x)| ≤ 1`.
  have h := congrArg (pointNorm K x) (algebraMap_mul_inverse_algebraMap (f := f) (g := g) j)
  rw [(isAffinoidAlgebra hA f g).pointNorm_mul, pointNorm_one] at h
  exact h.ge.trans (mul_le_of_le_one_right (pointNorm_nonneg _)
    (mk_X_natAdd (f := f) j ▸ hA.pointNorm_quotientMk_X_le_one x _))

include hA in
/-- Every classical point of `A⟨f, g⁻¹⟩` lies over a point of the Laurent domain `L(f, g⁻¹)`. -/
theorem maximalSpectrumComap_mem_laurentDomain (x : MaximalSpectrum (LaurentFraction f g)) :
    (isAffinoidAlgebra hA f g).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) x ∈
      laurentDomain K f g := by
  simp only [mem_laurentDomain, IsAffinoidAlgebra.pointNorm_maximalSpectrumComap,
    IsScalarTower.coe_toAlgHom']
  exact ⟨pointNorm_algebraMap_le_one hA x, one_le_pointNorm_algebraMap hA x⟩

include hA in
/-- **Laurent domains are affinoid subdomains.** The structure map
`A → A⟨f, g⁻¹⟩` represents `L(f, g⁻¹)` among all affinoid test algebras, without choosing
norms on those test algebras. No unit-ideal condition on `f` and `g` is required. -/
theorem isAffinoidSubdomainMap :
    IsAffinoidSubdomainMap (IsScalarTower.toAlgHom K A (LaurentFraction f g))
      (laurentDomain K f g) where
  isAffinoidAlgebra := isAffinoidAlgebra hA f g
  range_maximalSpectrumComap_subset :=
    Set.range_subset_iff.mpr (maximalSpectrumComap_mem_laurentDomain hA)
  existsUnique_algHom {C} _ _ hC ψ hψ := by
    -- The predicate is algebraic; equip the test algebra with a residue norm only here.
    let := hC.residueNormedCommRing
    let := hC.residueNormedAlgebra
    have := hC.isUltrametricDist_residueNormedCommRing
    have := hC.completeSpace_residueNormedCommRing
    obtain ⟨χ, hχ, huniq⟩ := (existsUnique_algHom_iff_range_subset hA hC ψ).mpr hψ
    exact ⟨χ, AlgHom.ext hχ, fun θ hθ ↦ huniq θ (AlgHom.congr_fun hθ)⟩

end LaurentFraction

end TauCeti
