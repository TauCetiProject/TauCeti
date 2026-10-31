/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Affinoid.RationalFraction

import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.RingTheory.Huber.ClosedSubmodule

/-!
# Rational domains of affinoid algebras

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, and let `g, f₁, …, fₘ`
generate the unit ideal of `A`. The rational domain

`R(f/g) = {x ∈ Sp A : |g(x)| ≠ 0, |fᵢ(x)| ≤ |g(x)| for all i}`

is a set of classical points, that is, of maximal ideals of `A`. This file shows that the rational
fraction algebra `A⟨f/g⟩ = A⟨X₁, …, Xₘ⟩ ⧸ (g Xᵢ - fᵢ)` represents `R(f/g)`, in two senses.

* **Points.** The map `Sp A⟨f/g⟩ → Sp A` contracting maximal ideals along `A → A⟨f/g⟩` is
  injective, with image `R(f/g)`.
* **Universal property.** For an affinoid algebra `B` with a complete ultrametric algebra norm, a
  `K`-algebra map `φ : A → B` factors through `A⟨f/g⟩` if and only if the induced map
  `Sp B → Sp A` takes values in `R(f/g)`, and the factorisation is then unique.

In the language of [BGR, §7.2.2] this says that `R(f/g)` is an affinoid subdomain of `Sp A`,
represented by `A → A⟨f/g⟩`; the universal property is stated for target algebras carrying a
complete ultrametric algebra norm, which every affinoid algebra admits.

The universal property is the point-free one of `TauCeti.RationalFraction.existsUnique_algHom`
(`φ g` is a unit and every `φ fᵢ / φ g` is power-bounded), translated by two pointwise criteria on
`B`: an element is a unit exactly when it vanishes at no classical point
(`TauCeti.IsAffinoidAlgebra.isUnit_iff_forall_pointNorm_ne_zero`), and `b / c` is power-bounded
exactly when `|b(y)| ≤ |c(y)|` at every classical point `y`, for a unit `c`
(`TauCeti.IsAffinoidAlgebra.isPowerBounded_mul_inverse_iff`), by the supremum-seminorm description
of power-bounded elements.

A point `x ∈ R(f/g)` lifts to `A⟨f/g⟩` by the universal property applied to the residue algebra
`A ⧸ x`. A point of `A⟨f/g⟩` above `x` is then the kernel of this lift: the residue map at that
point and the lift followed by `A ⧸ x → A⟨f/g⟩ ⧸ x'` agree on `A`, hence everywhere.

## Main definitions

* `TauCeti.rationalDomain K g f`: the rational domain `R(f/g) ⊆ Sp A`.
* `TauCeti.RationalFraction.maximalSpectrumEquiv`: the bijection `Sp A⟨f/g⟩ ≃ R(f/g)`.

## Main results

* `TauCeti.IsAffinoidAlgebra.range_maximalSpectrumComap_subset_rationalDomain_iff`: `Sp B → Sp A`
  lands in `R(f/g)` if and only if `φ g` is a unit and every `φ fᵢ · (φ g)⁻¹` is power-bounded.
* `TauCeti.RationalFraction.existsUnique_algHom_iff_range_subset`: the universal property of
  `A⟨f/g⟩` in terms of classical points.
* `TauCeti.RationalFraction.range_maximalSpectrumComap`: the image of `Sp A⟨f/g⟩ → Sp A` is
  `R(f/g)`.
* `TauCeti.RationalFraction.maximalSpectrumComap_injective`: the map `Sp A⟨f/g⟩ → Sp A` is
  injective.

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
`A⟨f/g⟩` (`TauCeti.RationalFraction.range_maximalSpectrumComap`). -/
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
    pointNorm K x (ratio g f i) ≤ 1 := by
  -- The ratio is the image of the power-bounded variable `Xᵢ` of `A⟨X₁, …, Xₘ⟩`.
  have hT := hA.isRestricted_subring (τ := Fin m)
  rw [← mk_X, ← Ideal.Quotient.mkₐ_eq_mk K,
    ← (isAffinoidAlgebra hA g f).pointNorm_maximalSpectrumComap]
  exact (hT.pointNorm_le_supSeminorm _ _).trans
    (hT.isPowerBounded_iff_supSeminorm_le_one.mp (isPowerBounded_X i))

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
/-- A point `x` of the rational domain `R(f/g)` has a `K`-algebra map `A⟨f/g⟩ → A ⧸ x` extending
the residue map, for the residue norm on `A ⧸ x`. -/
private theorem exists_algHom_quotient (h : Ideal.span (insert g (Set.range f)) = ⊤)
    {x : MaximalSpectrum A} [IsClosed (x.asIdeal : Set A)] (hx : x ∈ rationalDomain K g f) :
    ∃ ψ : RationalFraction g f →ₐ[K] A ⧸ x.asIdeal,
      ∀ a, ψ (algebraMap A _ a) = Ideal.Quotient.mk x.asIdeal a := by
  have hQ : IsAffinoidAlgebra K (A ⧸ x.asIdeal) := hA.quotient _
  -- Every classical point of `A ⧸ x` lies over `x`.
  refine ((existsUnique_algHom_iff_range_subset hA hQ h
    (Ideal.Quotient.mkₐ K x.asIdeal)).mpr ?_).exists
  rintro _ ⟨y, rfl⟩
  have hy : hQ.maximalSpectrumComap (Ideal.Quotient.mkₐ K x.asIdeal) y = x := by
    refine MaximalSpectrum.ext <| (hQ.maximalSpectrumComap_asIdeal _ y).trans (x.isMaximal.eq_of_le
      (hQ.comap_isMaximal (Ideal.Quotient.mkₐ K x.asIdeal) y.asIdeal).ne_top fun a ha ↦ ?_).symm
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  rw [hy]
  exact hx

include hA in
/-- A classical point `x'` of `A⟨f/g⟩` is the kernel of every `K`-algebra map `A⟨f/g⟩ → A ⧸ x`
extending the residue map at the point `x` below `x'`. -/
private theorem asIdeal_eq_ker (h : Ideal.span (insert g (Set.range f)) = ⊤)
    (x' : MaximalSpectrum (RationalFraction g f)) {x : MaximalSpectrum A}
    [IsClosed (x.asIdeal : Set A)]
    (hx : (isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) x' = x)
    (ψ : RationalFraction g f →ₐ[K] A ⧸ x.asIdeal)
    (hψ : ∀ a, ψ (algebraMap A _ a) = Ideal.Quotient.mk x.asIdeal a) :
    x'.asIdeal = RingHom.ker ψ := by
  -- Compare `ψ` with the residue map at `x'`, realised on the normed quotient of `A⟨X⟩` by the
  -- preimage `P` of `x'`.
  have hT := hA.isRestricted_subring (τ := Fin m)
  have := hT.isNoetherianRing
  let := Huber.IsTateRing.of_normedAlgebra K (IsRestricted.subring (R := A) fun _ : Fin m ↦ 1)
  let P := x'.asIdeal.comap (Ideal.Quotient.mkₐ K (rationalIdeal g f))
  have : IsClosed (P : Set (IsRestricted.subring (R := A) fun _ : Fin m ↦ 1)) :=
    Huber.isClosed_of_isNoetherian P
  have hP : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : rationalIdeal g f ≤ P := fun r hr ↦ by
    simp [P, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let ρ : RationalFraction g f →ₐ[K] _ ⧸ P := Ideal.Quotient.factorₐ K hle
  have hρ : RingHom.ker ρ = x'.asIdeal := by
    ext z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [ρ, P, Ideal.Quotient.eq_zero_iff_mem]
  have hj (a : A) (ha : a ∈ x.asIdeal) : ρ.comp (IsScalarTower.toAlgHom K A _) a = 0 := by
    subst hx
    rw [IsAffinoidAlgebra.maximalSpectrumComap_asIdeal, Ideal.mem_comap, ← hρ] at ha
    exact ha
  let j : A ⧸ x.asIdeal →ₐ[K] _ ⧸ P := Ideal.Quotient.liftₐ _ _ hj
  have hρj : ρ = j.comp ψ := by
    refine algHom_ext (B := IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) ⧸ P) hA
      (hT.quotient P) h fun a ↦ ?_
    simp only [AlgHom.comp_apply, hψ, j, Ideal.Quotient.liftₐ_apply]
    exact (Ideal.Quotient.lift_mk x.asIdeal _ hj).symm
  let := Ideal.Quotient.field x.asIdeal
  have : Nontrivial (_ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  rw [← hρ, hρj]
  exact RingHom.ker_comp_of_injective (ψ : RationalFraction g f →+* A ⧸ x.asIdeal)
    (j : A ⧸ x.asIdeal →+* _ ⧸ P).injective

include hA in
/-- **The classical points of `A⟨f/g⟩` cover the rational domain.** When `g, f₁, …, fₘ` generate
the unit ideal of `A`, the image of `Sp A⟨f/g⟩ → Sp A` is the rational domain `R(f/g)`. -/
theorem range_maximalSpectrumComap (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    Set.range ((isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _)) =
      rationalDomain K g f := by
  refine subset_antisymm (Set.range_subset_iff.mpr (maximalSpectrumComap_mem_rationalDomain hA h))
    fun x hx ↦ ?_
  -- The kernel of a lift `A⟨f/g⟩ → A ⧸ x` of the residue map is a point over `x`.
  have := hA.isNoetherianRing
  let := Huber.IsTateRing.of_normedAlgebra K A
  have : IsClosed (x.asIdeal : Set A) := Huber.isClosed_of_isNoetherian x.asIdeal
  obtain ⟨ψ, hψ⟩ := exists_algHom_quotient hA h hx
  have hsurj : Function.Surjective ψ := fun z ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨_, hψ a⟩
  let := Ideal.Quotient.field x.asIdeal
  refine ⟨⟨RingHom.ker ψ, RingHom.ker_isMaximal_of_surjective _ hsurj⟩, MaximalSpectrum.ext ?_⟩
  ext a
  simp [hψ, Ideal.Quotient.eq_zero_iff_mem]

include hA in
/-- **Distinct classical points of `A⟨f/g⟩` lie over distinct points of `A`**, when
`g, f₁, …, fₘ` generate the unit ideal of `A`. -/
theorem maximalSpectrumComap_injective (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    Function.Injective
      ((isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _)) := by
  intro x₁ x₂ hx
  have := hA.isNoetherianRing
  let := Huber.IsTateRing.of_normedAlgebra K A
  have : IsClosed
      (((isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) x₁).asIdeal :
        Set A) :=
    Huber.isClosed_of_isNoetherian _
  obtain ⟨ψ, hψ⟩ := exists_algHom_quotient hA h (maximalSpectrumComap_mem_rationalDomain hA h x₁)
  exact MaximalSpectrum.ext ((asIdeal_eq_ker hA h x₁ rfl ψ hψ).trans
    (asIdeal_eq_ker hA h x₂ hx.symm ψ hψ).symm)

include hA in
/-- **The classical points of `A⟨f/g⟩` are the points of the rational domain** `R(f/g)`: the
contraction of maximal ideals along `A → A⟨f/g⟩` is a bijection `Sp A⟨f/g⟩ ≃ R(f/g)` when
`g, f₁, …, fₘ` generate the unit ideal of `A`. -/
noncomputable def maximalSpectrumEquiv (h : Ideal.span (insert g (Set.range f)) = ⊤) :
    MaximalSpectrum (RationalFraction g f) ≃ rationalDomain K g f :=
  (Equiv.ofInjective _ (maximalSpectrumComap_injective hA h)).trans
    (Set.equivOfEq (range_maximalSpectrumComap hA h))

@[simp]
theorem coe_maximalSpectrumEquiv (h : Ideal.span (insert g (Set.range f)) = ⊤)
    (x : MaximalSpectrum (RationalFraction g f)) :
    (maximalSpectrumEquiv hA h x : MaximalSpectrum A) =
      (isAffinoidAlgebra hA g f).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) x :=
  (rfl)

end RationalFraction

end TauCeti
