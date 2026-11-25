/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme.Factorial
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Effective Cartier complements of affine open immersions

On a locally Noetherian scheme, the reduced complement of a dense open whose inclusion is
affine is an effective Cartier divisor if the local rings along its complement are factorial.
In particular, this holds for a dense affine open when the scheme has affine diagonal.
The criterion
`Scheme.IdealSheafData.isEffectiveCartier_of_exists_map_germ_eq_span_singleton` turns the
nonzero principal stalk ideals into regular equations on affine neighbourhoods.

These are the Cartier complements used in translated affine covers in projectivity arguments
for algebraic groups.

## References

* The Stacks Project, Tag 0BCW.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

private theorem exists_compl_equation_of_mem (X : Scheme.{u}) {U : X.Opens}
    {x : X} (hxU : x ∈ U) :
    ∃ (V : X.affineOpens) (hxV : x ∈ V.val) (a : X.presheaf.stalk x),
      IsSMulRegular (X.presheaf.stalk x) a ∧
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).ideal V).map
            (X.presheaf.germ V x hxV).hom = Ideal.span {a} := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  refine ⟨⟨V, hV⟩, hxV, 1, IsSMulRegular.one _, ?_⟩
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, Closeds.coe_mk]
  -- Identify the affine-open subtype projections with `V` and `hV` in the chart formula.
  change (PrimeSpectrum.vanishingIdeal (hV.fromSpec ⁻¹' (U : Set X)ᶜ)).map
    (X.presheaf.germ V x hxV).hom = Ideal.span {1}
  have hempty : (fun z : PrimeSpectrum Γ(X, V) ↦ hV.fromSpec z) ⁻¹' (U : Set X)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz (hVU (((Set.ext_iff.mp hV.range_fromSpec) _).mp (Set.mem_range_self z)))
  rw [hempty, PrimeSpectrum.vanishingIdeal_empty, Ideal.map_top, Ideal.span_singleton_one]

private theorem exists_localized_compl_generator_of_dense
    {R : CommRingCat.{u}} (hfin : (minimalPrimes R).Finite)
    {U : (Spec R).Opens} (hU : IsAffineOpen U) (hdense : Dense (U : Set (Spec R)))
    (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
    [Nontrivial S] [UniqueFactorizationMonoid S] :
    ∃ a : S, a ≠ 0 ∧
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ).map
        (algebraMap R S) = Ideal.span {a} := by
  exact hU.exists_ne_zero_map_vanishingIdeal_compl_eq_span_singleton M S
    (PrimeSpectrum.preimage_comap_nonempty_of_isOpen_of_dense
      hfin U.isOpen hdense M S)

private theorem exists_localized_compl_generator
    (X : Scheme.{u}) [IsLocallyNoetherian X] {U V : X.Opens} [IsAffineHom U.ι]
    (hdense : Dense (U : Set X)) (hV : IsAffineOpen V) (x : X) (hxV : x ∈ V)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ a : X.presheaf.stalk x, a ≠ 0 ∧
      (PrimeSpectrum.vanishingIdeal (hV.fromSpec ⁻¹ᵁ U : Set (Spec Γ(X, V)))ᶜ).map
        (X.presheaf.germ V x hxV).hom = Ideal.span {a} := by
  have hpre : IsAffineOpen (hV.fromSpec ⁻¹ᵁ U) :=
    IsAffine.of_isPullback (isPullback_morphismRestrict hV.fromSpec U).flip
  have hd : Dense (hV.fromSpec ⁻¹ᵁ U : Set (Spec Γ(X, V))) :=
    hdense.preimage hV.fromSpec.isOpenEmbedding.isOpenMap
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hgen := exists_localized_compl_generator_of_dense
    (minimalPrimes.finite_of_isNoetherianRing Γ(X, V)) hpre hd
    P.primeCompl (X.presheaf.stalk x)
  rw [X.presheaf.stalk_open_algebraMap (U := V) ⟨x, hxV⟩] at hgen
  exact hgen

private theorem exists_compl_equation_of_factorial_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] {U : X.Opens} [IsAffineHom U.ι]
    (hdense : Dense (U : Set X)) (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ (V : X.affineOpens) (hxV : x ∈ V.val) (a : X.presheaf.stalk x),
      IsSMulRegular (X.presheaf.stalk x) a ∧
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).ideal V).map
            (X.presheaf.germ V x hxV).hom = Ideal.span {a} := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨a, ha, hgen⟩ := exists_localized_compl_generator X hdense hV x hxV
  have : IsDomain (X.presheaf.stalk x) := {}
  refine ⟨⟨V, hV⟩, hxV, a, IsSMulRegular.of_ne_zero ha, ?_⟩
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, Closeds.coe_mk]
  -- Identify the affine-open subtype projections with `V` and `hV` in the chart formula.
  change (PrimeSpectrum.vanishingIdeal (hV.fromSpec ⁻¹' (U : Set X)ᶜ)).map
    (X.presheaf.germ V x hxV).hom = Ideal.span {a}
  have hcompl : (fun z : PrimeSpectrum Γ(X, V) ↦ hV.fromSpec z) ⁻¹' (U : Set X)ᶜ =
      (hV.fromSpec ⁻¹ᵁ U : Set (Spec Γ(X, V)))ᶜ :=
    Set.preimage_compl.trans (congrArg Set.compl hV.fromSpec.coe_preimage.symm)
  exact (congrArg (fun Z : Set (PrimeSpectrum Γ(X, V)) ↦
    (PrimeSpectrum.vanishingIdeal Z).map (X.presheaf.germ V x hxV).hom) hcompl).trans hgen

/-- The reduced complement of a dense open with affine inclusion on a locally Noetherian
scheme is an effective Cartier divisor if the local rings along the complement are factorial. -/
@[stacks 0BCW]
theorem Scheme.isEffectiveCartier_vanishingIdeal_compl_of_isAffineHom
    (X : Scheme.{u}) [IsLocallyNoetherian X] {U : X.Opens} [IsAffineHom U.ι]
    (hdense : Dense (U : Set X))
    (hX : ∀ x ∉ U, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    (IdealSheafData.vanishingIdeal
      ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).IsEffectiveCartier := by
  refine IdealSheafData.isEffectiveCartier_of_exists_map_germ_eq_span_singleton fun x ↦ ?_
  by_cases hxU : x ∈ U
  · exact exists_compl_equation_of_mem X hxU
  · have := hX x hxU
    exact exists_compl_equation_of_factorial_stalk X hdense x

/-- On a locally Noetherian scheme with affine diagonal, the reduced complement of a dense
affine open is an effective Cartier divisor if the local rings along the complement are factorial.
-/
theorem Scheme.isEffectiveCartier_vanishingIdeal_compl_of_isAffineOpen
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {U : X.Opens} (hU : IsAffineOpen U) (hdense : Dense (U : Set X))
    (hX : ∀ x ∉ U, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    (IdealSheafData.vanishingIdeal
      ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).IsEffectiveCartier := by
  have : IsAffineHom U.ι := hU.isAffineHom_ι
  exact X.isEffectiveCartier_vanishingIdeal_compl_of_isAffineHom hdense hX

end AlgebraicGeometry
