/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Krull dimension of finitely generated algebras over a field

Let `A` be a nontrivial finitely generated algebra over a field `k`. Noether normalization gives an
injective finite map `k[X₁, …, Xₛ] → A`, so `A` has Krull dimension `s`. Extending scalars along
any Noetherian `k`-algebra `K` keeps the map `K[X₁, …, Xₛ] → K ⊗[k] A` injective (every
`k`-module is flat) and finite, so `K ⊗[k] A` has the dimension of `K[X₁, …, Xₛ]`, namely
`dim K + s`. The tensor-product theorem handles the subsingleton case separately.

In particular the Krull dimension of a finitely generated algebra over a field does not change
under extension of the base field. This is the affine form of the invariance of the dimension of
a scheme locally of finite type over a field under field extension, which is what makes
fibrewise dimension bounds on morphisms stable under base change.

For a domain `A`, the same Noether normalization identifies `s` with the transcendence degree of
`A` over `k`: the variables form a transcendence basis because `A` is integral over them. The
transcendence degree only sees the fraction field, so an algebraic extension of finitely generated
domains, such as a localization `A[1/f]` with `f ≠ 0`, does not change the Krull dimension.
Geometrically, a nonempty open part of an irreducible closed subset of `Spec A` has the dimension
of the whole closed subset; this is what makes pure-dimensionality of schemes locally of finite
type over a field a local property.

## Main results

* `TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial`: an injective integral map
  `k[X₁, …, Xₛ] → A` forces `dim A = s`, the number of variables.
* `TauCeti.finiteRingKrullDim_of_finiteType`: a nontrivial finitely generated algebra over a field
  has finite Krull dimension.
* `TauCeti.ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType`:
  `dim (K ⊗[k] A) = dim K + dim A` for a Noetherian `k`-algebra `K`.
* `TauCeti.ringKrullDim_tensorProduct_field_of_finiteType`: `dim (K ⊗[k] A) = dim A` for a field
  extension `K / k`.
* `TauCeti.ringKrullDim_eq_toNat_trdeg`: a finitely generated domain over `k` has Krull dimension
  its transcendence degree over `k`.
* `TauCeti.ringKrullDim_eq_of_isAlgebraic`: an algebraic extension of finitely generated domains
  over `k` preserves the Krull dimension; `TauCeti.ringKrullDim_localization_away` is the case of
  `A[1/f]` with `f ≠ 0`.
* `TauCeti.topologicalKrullDim_inter_eq_of_finiteType`: in `Spec A`, a nonempty open part of an
  irreducible closed subset has the dimension of that subset.

## References

* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW) (Noether normalization)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) (dimension and
  transcendence degree)
-/

public section

namespace TauCeti

open scoped TensorProduct
open Topology PrimeSpectrum

variable {k : Type*} [Field k]

/-- If a `k`-algebra `A` is integral over a polynomial ring `k[Xᵢ | i ∈ ι]` in finitely many
variables embedded in it, then `A` has Krull dimension the number of variables. -/
theorem ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial {ι A : Type*} [Finite ι]
    [CommRing A] [Algebra k A] (g : MvPolynomial ι k →ₐ[k] A) (hinj : Function.Injective g)
    (hint : g.IsIntegral) : ringKrullDim A = Nat.card ι := by
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial ι k) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := MvPolynomial ι k),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

variable (k) in
/-- A nontrivial finitely generated algebra over a field has finite Krull dimension. -/
theorem finiteRingKrullDim_of_finiteType (A : Type*) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [finiteRingKrullDim_iff_ne_bot_and_top,
    ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint]
  exact ⟨WithBot.coe_ne_bot, WithBot.coe_inj.not.2 (ENat.natCast_ne_top _)⟩

/-- The Krull dimension of `K ⊗[k] A`, for a Noetherian `k`-algebra `K` and a finitely generated
`k`-algebra `A`, is the sum of the Krull dimensions of `K` and `A`. -/
@[simp]
theorem ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType (K A : Type*) [CommRing K]
    [IsNoetherianRing K] [Algebra k K] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim K + ringKrullDim A := by
  cases subsingleton_or_nontrivial A with
  | inl hA => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
    -- Noether normalization `k[X₁, …, Xₛ] → A`, base-changed to `K[X₁, …, Xₛ] → K ⊗[k] A`,
    -- stays finite, and stays injective because `K` is flat over the field `k`.
    obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    let φ := Algebra.TensorProduct.map (AlgHom.id k K) g
    have hφinj : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K) g.toLinearMap hinj
    have hφfin : φ.toRingHom.Finite := RingHom.Finite.tensorProductMap (AlgHom.Finite.id k K) hfin
    algebraize [φ.toRingHom]
    have : FaithfulSMul (K ⊗[k] MvPolynomial (Fin s) k) (K ⊗[k] A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
    rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := K ⊗[k] MvPolynomial (Fin s) k),
      ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hfin.to_isIntegral]

/-- The Krull dimension of a finitely generated algebra over a field is unchanged by extending
the base field. -/
theorem ringKrullDim_tensorProduct_field_of_finiteType (K A : Type*) [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim A := by
  rw [ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType, ringKrullDim_eq_zero_of_field,
    zero_add]

variable (k) in
/-- A finitely generated domain over a field `k` has Krull dimension its transcendence degree over
`k`. The transcendence degree is finite by `Algebra.trdeg_lt_aleph0_of_finiteType`. -/
theorem ringKrullDim_eq_toNat_trdeg (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A = (Algebra.trdeg k A).toNat := by
  -- Noether normalization `k[X₁, …, Xₛ] → A` gives `dim A = s`, and the variables form a
  -- transcendence basis of `A` since `A` is integral, hence algebraic, over them.
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint]
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A)] at h
  rw [← Cardinal.toNat_lift, ← h]
  simp

variable (k) in
/-- An algebraic extension `B / A` of finitely generated domains over a field `k` does not change
the Krull dimension: both have the transcendence degree of `B` over `k`. -/
theorem ringKrullDim_eq_of_isAlgebraic (A B : Type*) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    [Algebra.IsAlgebraic A B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    ringKrullDim A = ringKrullDim B := by
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain (algebraMap A B)
  have h := lift_trdeg_add_eq k A B
  rw [trdeg_eq_zero (R := A) (A := B), Cardinal.lift_zero, add_zero] at h
  rw [ringKrullDim_eq_toNat_trdeg k, ringKrullDim_eq_toNat_trdeg k, ← Cardinal.toNat_lift, h,
    Cardinal.toNat_lift]

variable (k) in
/-- Inverting a nonzero element of a finitely generated domain over a field does not change its
Krull dimension. -/
theorem ringKrullDim_localization_away {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim A := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : FaithfulSMul A (Localization.Away f) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have := IsLocalization.isAlgebraic (Localization.Away f) (Submonoid.powers f)
  exact (ringKrullDim_eq_of_isAlgebraic k A _).symm

variable (k) in
/-- In the spectrum of a finitely generated algebra over a field, a nonempty open part `Z ∩ U` of
an irreducible closed subset `Z` has the Krull dimension of `Z`. -/
theorem topologicalKrullDim_inter_eq_of_finiteType {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] {Z U : Set (PrimeSpectrum A)} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) (hU : IsOpen U) (hZU : (Z ∩ U).Nonempty) :
    topologicalKrullDim ↥(Z ∩ U) = topologicalKrullDim Z := by
  refine le_antisymm (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le
    ?_
  -- `Z` is the zero locus of a prime `p`, so it is `Spec (A ⧸ p)`; and `Z ∩ U` contains the basic
  -- open set of some `g ∉ p`, which is `Spec (A ⧸ p)[1/g']` for the image `g'` of `g`.
  set p := vanishingIdeal Z
  have := isIrreducible_iff_vanishingIdeal_isPrime.mp hZ
  have hZp : zeroLocus p = Z := by rw [zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  obtain ⟨x, hxZ, hxU⟩ := hZU
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  set g' := Ideal.Quotient.mk p g
  have hg : g' ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h ↦ hxg ((hZp ▸ hxZ : x ∈ zeroLocus p) h)
  let i := comap (Ideal.Quotient.mk p)
  have hi : IsClosedEmbedding i :=
    isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hrange : Set.range i = Z := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hZp]
  let j := comap (algebraMap (A ⧸ p) (Localization.Away g'))
  have hj : IsOpenEmbedding j := localization_away_isOpenEmbedding _ g'
  have hsub (y : PrimeSpectrum (Localization.Away g')) : i (j y) ∈ Z ∩ U := by
    refine ⟨hrange ▸ ⟨_, rfl⟩, hgU ?_⟩
    have hy : j y ∈ (basicOpen g' : Set (PrimeSpectrum (A ⧸ p))) :=
      localization_away_comap_range (Localization.Away g') g' ▸ ⟨y, rfl⟩
    rw [SetLike.mem_coe, mem_basicOpen] at hy ⊢
    simpa [i, comap_asIdeal] using hy
  calc topologicalKrullDim Z = topologicalKrullDim (PrimeSpectrum (A ⧸ p)) :=
        ((hi.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm.isHomeomorph
          |>.topologicalKrullDim_eq
    _ = topologicalKrullDim (PrimeSpectrum (Localization.Away g')) := by
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_localization_away k hg]
    _ ≤ topologicalKrullDim ↥(Z ∩ U) :=
        ((hi.isEmbedding.comp hj.isEmbedding).isInducing.codRestrict hsub).topologicalKrullDim_le

end TauCeti
