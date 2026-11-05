/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.RationalFraction
public import TauCeti.RingTheory.Affinoid.Subdomain.Basic

import TauCeti.RingTheory.Affinoid.Restricted.PointNorm
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal

/-!
# Rational domains of affinoid algebras

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, and let `g, f₁, …, fₘ`
generate the unit ideal of `A`. The rational domain

`R(f/g) = {x ∈ Sp A : |g(x)| ≠ 0, |fᵢ(x)| ≤ |g(x)| for all i}`

is a set of classical points, that is, of maximal ideals of `A`. This file shows that the rational
fraction algebra `A⟨f/g⟩ = A⟨X₁, …, Xₘ⟩ ⧸ (g Xᵢ - fᵢ)` represents `R(f/g)` as an affinoid subdomain
in the sense of [BGR, §7.2.2] (`TauCeti.IsAffinoidSubdomainMap`).

* **Universal property.** For an affinoid algebra `B` with a complete ultrametric algebra norm, a
  `K`-algebra map `φ : A → B` factors through `A⟨f/g⟩` if and only if the induced map
  `Sp B → Sp A` takes values in `R(f/g)`, and the factorisation is then unique.
* **Affinoid subdomain.** The same holds for every affinoid algebra `B`, with no chosen norm, since
  every affinoid algebra is isomorphic to a quotient of a Tate algebra with its residue norm. The
  general theory of affinoid subdomains then shows that `Sp A⟨f/g⟩ → Sp A` is injective with image
  `R(f/g)`.

The universal property is the point-free one of `TauCeti.RationalFraction.existsUnique_algHom`
(`φ g` is a unit and every `φ fᵢ / φ g` is power-bounded), translated by two pointwise criteria on
`B`: an element is a unit exactly when it vanishes at no classical point
(`TauCeti.IsAffinoidAlgebra.isUnit_iff_forall_pointNorm_ne_zero`), and `b / c` is power-bounded
exactly when `|b(y)| ≤ |c(y)|` at every classical point `y`, for a unit `c`
(`TauCeti.IsAffinoidAlgebra.isPowerBounded_mul_inverse_iff`), by the supremum-seminorm description
of power-bounded elements.

## Main definitions

* `TauCeti.rationalDomain K g f`: the rational domain `R(f/g) ⊆ Sp A`.

## Main results

* `TauCeti.IsAffinoidAlgebra.range_maximalSpectrumComap_subset_rationalDomain_iff`: `Sp B → Sp A`
  lands in `R(f/g)` if and only if `φ g` is a unit and every `φ fᵢ · (φ g)⁻¹` is power-bounded.
* `TauCeti.RationalFraction.existsUnique_algHom_iff_range_subset`: the universal property of
  `A⟨f/g⟩` in terms of classical points.
* `TauCeti.RationalFraction.isAffinoidSubdomainMap`: `A → A⟨f/g⟩` represents `R(f/g)` as an
  affinoid subdomain.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§7.2.2 and
  7.2.3.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K]

section RationalDomain

variable {A : Type*} [CommRing A] [Algebra K A] {m : ℕ}

variable (K) in
/-- **The rational domain** `R(f/g) = {x ∈ Sp A : |g(x)| ≠ 0, |fᵢ(x)| ≤ |g(x)| for all i}` of
classical points of `A`, with absolute values computed by `TauCeti.pointNorm`. When `A` is affinoid
and `g, f₁, …, fₘ` generate the unit ideal, it is represented by the rational fraction algebra
`A⟨f/g⟩` (`TauCeti.RationalFraction.isAffinoidSubdomainMap`). -/
def rationalDomain (g : A) (f : Fin m → A) : Set (MaximalSpectrum A) :=
  {x | pointNorm K x g ≠ 0 ∧ ∀ i, pointNorm K x (f i) ≤ pointNorm K x g}

@[simp]
theorem mem_rationalDomain {g : A} {f : Fin m → A} {x : MaximalSpectrum A} :
    x ∈ rationalDomain K g f ↔ pointNorm K x g ≠ 0 ∧ ∀ i, pointNorm K x (f i) ≤ pointNorm K x g :=
  Iff.rfl

end RationalDomain

variable [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidAlgebra

variable {A : Type*} [CommRing A] [Algebra K A] {m : ℕ}
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

/-- **Maps landing in a rational domain.** For a `K`-algebra map `φ : A → B` into an affinoid
algebra with a complete ultrametric algebra norm, the induced map `Sp B → Sp A` takes values in
the rational domain `R(f/g)` if and only if `φ g` is a unit of `B` and every `φ fᵢ · (φ g)⁻¹` is
power-bounded. -/
theorem range_maximalSpectrumComap_subset_rationalDomain_iff (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) {g : A} {f : Fin m → A} :
    Set.range (hB.maximalSpectrumComap φ) ⊆ rationalDomain K g f ↔
      IsUnit (φ g) ∧ ∀ i, Huber.IsPowerBounded (φ (f i) * Ring.inverse (φ g)) := by
  simp only [Set.range_subset_iff, mem_rationalDomain, pointNorm_maximalSpectrumComap]
  refine ⟨fun h ↦ ?_, fun ⟨hg, hf⟩ y ↦ ?_⟩
  · have hg : IsUnit (φ g) := hB.isUnit_iff_forall_pointNorm_ne_zero.mpr fun y ↦ (h y).1
    exact ⟨hg, fun i ↦ (hB.isPowerBounded_mul_inverse_iff hg).mpr fun y ↦ (h y).2 i⟩
  · exact ⟨hB.isUnit_iff_forall_pointNorm_ne_zero.mp hg y,
      fun i ↦ (hB.isPowerBounded_mul_inverse_iff hg).mp (hf i) y⟩

end IsAffinoidAlgebra

namespace RationalFraction

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]
  (hA : IsAffinoidAlgebra K A) {m : ℕ} {g : A} {f : Fin m → A}
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  (hB : IsAffinoidAlgebra K B)

include hA in
/-- The ratio `fᵢ/g` has absolute value at most one at every classical point of `A⟨f/g⟩`. -/
theorem pointNorm_ratio_le_one (x : MaximalSpectrum (RationalFraction g f)) (i : Fin m) :
    pointNorm K x (ratio g f i) ≤ 1 :=
  mk_X (g := g) (f := f) i ▸ hA.pointNorm_quotientMk_X_le_one x i

include hA hB in
/-- **The universal property of `A⟨f/g⟩` in terms of classical points.** Let `A` and `B` be affinoid
algebras with complete ultrametric algebra norms, and let `g, f₁, …, fₘ` generate the unit ideal of
`A`. A `K`-algebra map `φ : A → B` extends to a `K`-algebra map `A⟨f/g⟩ → B` if and only if the
induced map `Sp B → Sp A` takes values in the rational domain `R(f/g)`, and the extension is then
unique. -/
theorem existsUnique_algHom_iff_range_subset (h : Ideal.span (insert g (Set.range f)) = ⊤)
    (φ : A →ₐ[K] B) :
    (∃! ψ : RationalFraction g f →ₐ[K] B, ∀ a, ψ (algebraMap A _ a) = φ a) ↔
      Set.range (hB.maximalSpectrumComap φ) ⊆ rationalDomain K g f := by
  rw [existsUnique_algHom hA hB h, hB.range_maximalSpectrumComap_subset_rationalDomain_iff]

include hA in
/-- Every classical point of `A⟨f/g⟩` lies over a point of the rational domain `R(f/g)`, when
`g, f₁, …, fₘ` generate the unit ideal of `A`. -/
theorem maximalSpectrumComap_mem_rationalDomain (h : Ideal.span (insert g (Set.range f)) = ⊤)
    (x : MaximalSpectrum (RationalFraction g f)) :
    (isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) x ∈
      rationalDomain K g f := by
  have hR := isAffinoidAlgebra hA g f
  simp only [mem_rationalDomain, IsAffinoidAlgebra.pointNorm_maximalSpectrumComap,
    IsScalarTower.coe_toAlgHom', ← algebraMap_mul_ratio (g := g) (f := f), hR.pointNorm_mul]
  exact ⟨hR.isUnit_iff_forall_pointNorm_ne_zero.mp (isUnit_algebraMap h) x, fun i ↦
    mul_le_of_le_one_right (pointNorm_nonneg _) (pointNorm_ratio_le_one hA x i)⟩

include hA in
/-- **Rational domains are affinoid subdomains.** When `g, f₁, …, fₘ` generate the unit ideal of
`A`, the structure map `A → A⟨f/g⟩` represents the rational domain `R(f/g)`. In particular
`Sp A⟨f/g⟩ → Sp A` is injective with image `R(f/g)`
(`TauCeti.IsAffinoidSubdomainMap.maximalSpectrumEquiv`). -/
theorem isAffinoidSubdomainMap (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    IsAffinoidSubdomainMap (IsScalarTower.toAlgHom K A (RationalFraction g f))
      (rationalDomain K g f) where
  isAffinoidAlgebra := isAffinoidAlgebra hA g f
  range_maximalSpectrumComap_subset :=
    Set.range_subset_iff.mpr (maximalSpectrumComap_mem_rationalDomain hA h)
  existsUnique_algHom {C} _ _ hC ψ hψ := by
    -- Transport the problem to `C ≃ Tₙ ⧸ ker π`, which carries the residue Gauss norm.
    obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K C).mp hC
    let e := Ideal.quotientKerAlgEquivOfSurjective hπ
    have hD := isAffinoidAlgebra_tate.quotient (RingHom.ker π)
    have hψ' : Set.range (hD.maximalSpectrumComap (e.symm.toAlgHom.comp ψ)) ⊆
        rationalDomain K g f := by
      rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hC hD, Set.range_comp]
      exact (Set.image_subset_range _ _).trans hψ
    obtain ⟨χ, hχ, huniq⟩ := (existsUnique_algHom_iff_range_subset
      (B := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) ⧸ RingHom.ker π) hA hD h _).mpr hψ'
    refine ⟨e.toAlgHom.comp χ, AlgHom.ext fun a ↦ by simp [hχ], fun θ hθ ↦ ?_⟩
    have : e.symm.toAlgHom.comp θ = χ := huniq _ fun a ↦ by simp [← hθ]
    rw [← this]
    ext
    simp

end RationalFraction

end TauCeti
