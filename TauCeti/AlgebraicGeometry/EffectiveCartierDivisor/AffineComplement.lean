/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme.Factorial
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk

/-!
# Effective Cartier complements of affine open immersions

On an integral locally Noetherian scheme with factorial local rings, the reduced complement
of a nonempty open whose inclusion is affine is an effective Cartier divisor. In particular,
this holds for a nonempty affine open when the scheme has affine diagonal.
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

/-- The reduced complement of a nonempty open with affine inclusion on an integral locally
Noetherian scheme with factorial local rings is an effective Cartier divisor. -/
@[stacks 0BCW]
theorem Scheme.isEffectiveCartier_vanishingIdeal_compl_of_isAffineHom
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsIntegral X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {U : X.Opens} [IsAffineHom U.ι] (hne : (U : Set X).Nonempty) :
    (IdealSheafData.vanishingIdeal
      ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).IsEffectiveCartier := by
  refine IdealSheafData.isEffectiveCartier_of_exists_map_germ_eq_span_singleton fun x ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hUV : IsAffineOpen (U ⊓ V) := by
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] using
      U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr (hV.preimage U.ι)
  have hpre : IsAffineOpen (hV.fromSpec ⁻¹ᵁ U) := by
    rw [← hV.fromSpec.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec, inf_comm]
    exact hUV
  have hWne : (hV.fromSpec ⁻¹ᵁ U : Set (Spec Γ(X, V))).Nonempty := by
    obtain ⟨z, hzU, hzV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hne ⟨x, hxV⟩
    obtain ⟨z', rfl⟩ : z ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hzV
    exact ⟨z', hzU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := hX x
  let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨a, ha, hgen⟩ := hpre.exists_ne_zero_map_vanishingIdeal_compl_eq_span_singleton
    hWne P.primeCompl P.primeCompl_le_nonZeroDivisors (X.presheaf.stalk x)
  refine ⟨⟨V, hV⟩, hxV, a, IsSMulRegular.of_ne_zero ha, ?_⟩
  rw [IdealSheafData.vanishingIdeal_ideal, Closeds.coe_mk]
  have hcompl : (fun z : PrimeSpectrum Γ(X, V) ↦ hV.fromSpec z) ⁻¹' (U : Set X)ᶜ =
      (hV.fromSpec ⁻¹ᵁ U : Set (Spec Γ(X, V)))ᶜ :=
    Set.preimage_compl.trans (congrArg Set.compl hV.fromSpec.coe_preimage.symm)
  change (PrimeSpectrum.vanishingIdeal (hV.fromSpec ⁻¹' (U : Set X)ᶜ)).map
    (X.presheaf.germ V x hxV).hom = Ideal.span {a}
  rw [← X.presheaf.stalk_open_algebraMap (U := V) ⟨x, hxV⟩]
  exact (congrArg (fun Z : Set (PrimeSpectrum Γ(X, V)) ↦
    (PrimeSpectrum.vanishingIdeal Z).map (algebraMap Γ(X, V) (X.presheaf.stalk x)))
      hcompl).trans hgen

/-- On an integral locally Noetherian scheme with affine diagonal and factorial local rings,
the reduced complement of a nonempty affine open is an effective Cartier divisor. -/
theorem Scheme.isEffectiveCartier_vanishingIdeal_compl_of_isAffineOpen
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    (IdealSheafData.vanishingIdeal
      ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).IsEffectiveCartier := by
  have : IsAffineHom U.ι := ⟨fun V hV ↦ by
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact hU.inf hV⟩
  exact X.isEffectiveCartier_vanishingIdeal_compl_of_isAffineHom hX hne

end AlgebraicGeometry
