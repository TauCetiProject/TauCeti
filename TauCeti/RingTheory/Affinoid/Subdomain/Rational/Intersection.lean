/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basis
public import TauCeti.RingTheory.Affinoid.QuotientNorm

import TauCeti.RingTheory.Huber.ClosedSubmodule

/-!
# Iterated rational fractions and intersection coordinates

Restricting a rational domain of `Sp A` to an affinoid subdomain represented by
`φ : A → B` gives the rational fraction with denominator `φ g` and numerators `φ fᵢ`.
Its composite structure map represents the intersection in `Sp A`.

In particular, if `B` represents `R(f/g)`, then
`B⟨φ f'/φ g'⟩` is canonically isomorphic to
`A⟨F/(g g')⟩`, where `F` is the family of all products of entries of `(g,f)`
and `(g',f')`. The comparison is a homeomorphism for the quotient topologies
and preserves restriction from `B`, not just the structure map from `A`.
These compatibilities identify the coordinate rings and restrictions on overlaps
in rational-cover Čech complexes. No assertion that an ordinary algebraic tensor
product is already complete is involved.

The first representing algebra may carry any complete ultrametric algebra norm.
Empty numerator families, empty domains, zero algebras and nilpotents are retained.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§6.1.4, 7.2.2–7.2.3 and 8.2.
-/

public section

namespace TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidSubdomainMap

variable {A B : Type u} [CommRing A] [Algebra K A]
  [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}

/-- A rational fraction over a representing algebra represents the intersection with the
ambient rational domain. Only the second rational presentation needs a unit-ideal hypothesis. -/
theorem rational_comp (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)
    {n : ℕ} {g : A} {f : Fin n → A}
    (hf : Ideal.span (insert g (Set.range f)) = ⊤) :
    IsAffinoidSubdomainMap
      ((IsScalarTower.toAlgHom K B (RationalFraction (φ g) (φ ∘ f))).comp φ)
      (U ∩ rationalDomain K g f) := by
  have hfB : Ideal.span (insert (φ g) (Set.range (φ ∘ f))) = ⊤ := by
    rw [Set.range_comp, ← Set.image_insert_eq, ← Ideal.map_span, hf, Ideal.map_top]
  have hc := h.comp hA (RationalFraction.isAffinoidSubdomainMap h.isAffinoidAlgebra hfB)
  rw [← h.isAffinoidAlgebra.preimage_maximalSpectrumComap_rationalDomain,
    Set.image_preimage_eq_inter_range, h.range_maximalSpectrumComap hA, Set.inter_comm] at hc
  exact hc

end IsAffinoidSubdomainMap

namespace RationalFraction

variable {A : Type u} [NormedCommRing A] [NormedAlgebra K A]
  [IsUltrametricDist A] [CompleteSpace A]
  {m n : ℕ} {g g' : A} {f : Fin m → A} {f' : Fin n → A}

omit [CompleteSpace A] in
/-- The second denominator is a unit in the product-denominator intersection presentation. -/
theorem isUnit_inter_secondDenominator
    (hf : Ideal.span (insert g (Set.range f)) = ⊤)
    (hf' : Ideal.span (insert g' (Set.range f')) = ⊤) :
    IsUnit (algebraMap A (RationalFraction (g * g') (rationalInterNumerator g f g' f')) g') := by
  apply isUnit_of_mul_isUnit_right (x := algebraMap A _ g)
  rw [← map_mul]
  exact isUnit_algebraMap (span_insert_rationalInterNumerator_eq_top hf hf')

section Restriction

variable {B : Type u} [CommRing B] [Algebra K B]
  {φ : A →ₐ[K] B} (hA : IsAffinoidAlgebra K A)
  (hB : IsAffinoidSubdomainMap φ (rationalDomain K g f))
  (hf : Ideal.span (insert g (Set.range f)) = ⊤)
  (hf' : Ideal.span (insert g' (Set.range f')) = ⊤)

/-- Restriction from the first rational domain to the product-denominator presentation
of its intersection with the second rational domain. -/
noncomputable def interRestrict :
    B →ₐ[K] RationalFraction (g * g') (rationalInterNumerator g f g' f') :=
  hB.lift (isAffinoidAlgebra hA _ _) (IsScalarTower.toAlgHom K A _)
    (fun _ hx ↦ ((isAffinoidSubdomainMap_inter hA hf hf').range_maximalSpectrumComap_subset hx).1)

/-- Restriction to the intersection extends the structure map from `A`. -/
@[simp]
theorem interRestrict_apply (a : A) :
    interRestrict hA hB hf hf' (φ a) =
      algebraMap A (RationalFraction (g * g') (rationalInterNumerator g f g' f')) a :=
  hB.lift_apply _ _ _ a

end Restriction

section Iterate

variable {B : Type u} [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]
  {φ : A →ₐ[K] B} (hA : IsAffinoidAlgebra K A)
  (hB : IsAffinoidSubdomainMap φ (rationalDomain K g f))
  (hf : Ideal.span (insert g (Set.range f)) = ⊤)
  (hf' : Ideal.span (insert g' (Set.range f')) = ⊤)

/-- **Intersection coordinates by successive rational localisation.** The rational fraction
of any representing algebra of `R(f/g)` at the images of `g',f'` is the single rational
fraction with product denominator and product numerators. -/
noncomputable def interAlgEquiv :
    RationalFraction (φ g') (φ ∘ f') ≃ₐ[K]
      RationalFraction (g * g') (rationalInterNumerator g f g' f') :=
  (hB.rational_comp hA hf').algEquiv (isAffinoidSubdomainMap_inter hA hf hf')

/-- The intersection comparison preserves the restriction map from the first domain. -/
@[simp]
theorem interAlgEquiv_algebraMap (b : B) :
    interAlgEquiv hA hB hf hf' (algebraMap B _ b) = interRestrict hA hB hf hf' b := by
  have he : (interAlgEquiv hA hB hf hf').toAlgHom.comp
      (IsScalarTower.toAlgHom K B _) = interRestrict hA hB hf hf' := by
    apply hB.algHom_ext (isAffinoidAlgebra hA _ _)
    ext a
    exact ((hB.rational_comp hA hf').algEquiv_apply
      (isAffinoidSubdomainMap_inter hA hf hf') a).trans
        (interRestrict_apply hA hB hf hf' a).symm
  exact AlgHom.congr_fun he b

/-- The inverse comparison also preserves restriction from the first domain. -/
@[simp]
theorem interAlgEquiv_symm_interRestrict (b : B) :
    (interAlgEquiv hA hB hf hf').symm (interRestrict hA hB hf hf' b) =
      algebraMap B _ b := by
  rw [← interAlgEquiv_algebraMap, AlgEquiv.symm_apply_apply]

include hA hB hf hf' in
/-- The product denominator is a unit in the iterated fraction presentation. -/
theorem isUnit_iterated_interDenominator :
    IsUnit (algebraMap B (RationalFraction (φ g') (φ ∘ f')) (φ (g * g'))) := by
  have hu := (isUnit_algebraMap (span_insert_rationalInterNumerator_eq_top hf hf')).map
    (interAlgEquiv hA hB hf hf').symm
  rwa [← interRestrict_apply hA hB hf hf', interAlgEquiv_symm_interRestrict] at hu

/-- On the ratios in the second rational fraction, the comparison is division by the
image of the second denominator in the intersection algebra. The inverse is taken in the
unit group so simplification need not test whether a coefficient map reflects units. -/
@[simp]
theorem interAlgEquiv_ratio (i : Fin n) :
    interAlgEquiv hA hB hf hf' (ratio (φ g') (φ ∘ f') i) =
      algebraMap A _ (f' i) * ↑((isUnit_inter_secondDenominator hf hf').unit⁻¹) := by
  have hfB : Ideal.span (insert (φ g') (Set.range (φ ∘ f'))) = ⊤ := by
    rw [Set.range_comp, ← Set.image_insert_eq, ← Ideal.map_span, hf', Ideal.map_top]
  rw [ratio_eq_algebraMap_mul_inverse hfB, map_mul,
    (isUnit_algebraMap hfB).map_ringInverse]
  simp only [interAlgEquiv_algebraMap, interRestrict_apply, Function.comp_apply]
  have hu : IsUnit (algebraMap A
      (RationalFraction (g * g') (rationalInterNumerator g f g' f')) g') :=
    isUnit_inter_secondDenominator hf hf'
  exact congrArg (algebraMap A _ (f' i) * ·) (Ring.inverse_of_isUnit hu)

/-- The inverse sends each product numerator divided by `g g'` to the same expression
in the iterated fraction algebra. This includes the redundant denominator numerator.
As in the forward formula, use the inverse of the known unit rather than `Ring.inverse`. -/
@[simp]
theorem interAlgEquiv_symm_ratio (i : Fin ((m + 1) * (n + 1))) :
    (interAlgEquiv hA hB hf hf').symm (ratio (g * g') (rationalInterNumerator g f g' f') i) =
      algebraMap B _ (φ (rationalInterNumerator g f g' f' i)) *
        ↑((isUnit_iterated_interDenominator hA hB hf hf').unit⁻¹) := by
  have ha (a : A) : (interAlgEquiv hA hB hf hf').symm (algebraMap A _ a) =
      algebraMap B _ (φ a) := by
    rw [← interRestrict_apply hA hB hf hf', interAlgEquiv_symm_interRestrict]
  rw [ratio_eq_algebraMap_mul_inverse (span_insert_rationalInterNumerator_eq_top hf hf'),
    map_mul, (isUnit_algebraMap (span_insert_rationalInterNumerator_eq_top hf hf')).map_ringInverse,
    ha, ha]
  have hu : IsUnit (algebraMap B (RationalFraction (φ g') (φ ∘ f')) (φ (g * g'))) :=
    isUnit_iterated_interDenominator hA hB hf hf'
  exact congrArg (algebraMap B _ (φ (rationalInterNumerator g f g' f' i)) * ·)
    (Ring.inverse_of_isUnit hu)

/-- The intersection comparison is a topological algebra isomorphism. The quotient norms
are used only to apply automatic continuity; no isometry of presentation norms is claimed. -/
noncomputable def interContinuousAlgEquiv :
    RationalFraction (φ g') (φ ∘ f') ≃A[K]
      RationalFraction (g * g') (rationalInterNumerator g f g' f') := by
  have := (hA.isRestricted_subring (τ := Fin ((m + 1) * (n + 1)))).isNoetherianRing
  have := (hB.isAffinoidAlgebra.isRestricted_subring (τ := Fin n)).isNoetherianRing
  have := Huber.IsTateRing.of_normedAlgebra K
    (_root_.MvPowerSeries.IsRestricted.subring (R := A)
      (fun _ : Fin ((m + 1) * (n + 1)) ↦ 1))
  have := Huber.IsTateRing.of_normedAlgebra K
    (_root_.MvPowerSeries.IsRestricted.subring (R := B) (fun _ : Fin n ↦ 1))
  have : IsClosed (rationalIdeal (g * g') (rationalInterNumerator g f g' f') :
      Set (_root_.MvPowerSeries.IsRestricted.subring
        (R := A) (fun _ : Fin ((m + 1) * (n + 1)) ↦ 1))) :=
    Huber.isClosed_of_isNoetherian _
  have : IsClosed (rationalIdeal (φ g') (φ ∘ f') :
      Set (_root_.MvPowerSeries.IsRestricted.subring (R := B) (fun _ : Fin n ↦ 1))) :=
    Huber.isClosed_of_isNoetherian _
  exact IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := RationalFraction (φ g') (φ ∘ f'))
    (B := RationalFraction (g * g') (rationalInterNumerator g f g' f'))
    (isAffinoidAlgebra hA _ _) (interAlgEquiv hA hB hf hf')

/-- The topological comparison has the specified algebraic comparison as underlying map. -/
@[simp]
theorem interContinuousAlgEquiv_toAlgEquiv :
    (interContinuousAlgEquiv hA hB hf hf').toAlgEquiv = interAlgEquiv hA hB hf hf' := by
  simp only [interContinuousAlgEquiv, IsAffinoidAlgebra.toAlgEquiv_toContinuousAlgEquiv]

/-- On elements, the topological comparison is the algebraic comparison. -/
@[simp]
theorem coe_interContinuousAlgEquiv :
    ⇑(interContinuousAlgEquiv hA hB hf hf') = ⇑(interAlgEquiv hA hB hf hf') := by
  simp only [interContinuousAlgEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv]

end Iterate

end RationalFraction

end TauCeti
