/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.Tactic.Algebraize

/-!
# The fibre of a finite morphism and maximal ideals of a semilocal ring

Let `g : X ⟶ Y` be a finite morphism of schemes, `U` an affine open of `Y` and `x ∈ U`, with
prime `p` of `Γ(Y, U)`. Localizing the finite `Γ(Y, U)`-algebra `Γ(X, g⁻¹ U)` at the complement of
`p` gives a semilocal ring `Γ(X, g⁻¹ U)_x`, finite over the local ring `𝒪_{Y,x}`. Its maximal
ideals are exactly the points of the fibre of `g` over `x`: the point `y` corresponds to the
extension of its prime ideal in `Γ(X, g⁻¹ U)`
(`AlgebraicGeometry.Scheme.Hom.exists_equiv_maximalSpectrum`). A maximal ideal of a finite
extension lies over the maximal ideal of `𝒪_{Y,x}`, and primes disjoint from the localized
submonoid are recovered from their extensions.

This is how sums over the fibre of a finite morphism, such as the local projection formula, are
computed by commutative algebra over `𝒪_{Y,x}`.
-/

public section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]

/-- The points of the fibre of `g` over `x ∈ U`, for `U` affine, are the maximal ideals of the
semilocal ring `Γ(X, g⁻¹ U)_x`, localized at the complement of the prime of `x`: the point `y`
corresponds to the extension of its prime ideal in `Γ(X, g⁻¹ U)`. -/
theorem exists_equiv_maximalSpectrum {x : Y} {U : Y.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    letI := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    ∃ e : {y : X // g y = x} ≃ MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(X, g ⁻¹ᵁ U) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)),
      ∀ y, (e y).asIdeal = ((hU.preimage g).primeIdealOf
        ⟨y, g.mem_preimage.mpr (y.property.symm ▸ hxU)⟩).asIdeal.map (algebraMap _ _) := by
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  set φ := g.appLE U (g ⁻¹ᵁ U) le_rfl with hφ
  have hfin : φ.hom.Finite := by
    rw [hφ, ← g.app_eq_appLE]
    exact g.finite_app U hU
  algebraize [φ.hom]
  set p := hU.primeIdealOf ⟨x, hxU⟩ with hp
  let := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  set M := p.asIdeal.primeCompl
  set B := Localization (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M)
  let : Algebra (Y.presheaf.stalk x) B := localizationAlgebra M Γ(X, g ⁻¹ᵁ U)
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk x) B := isScalarTower_localizationAlgebra _ _
  have : Module.Finite (Y.presheaf.stalk x) B := by
    have : IsLocalization (M.map (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U))) B :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid _ M) B)
    exact RingHom.finite_algebraMap.mp (RingHom.finite_localizationPreserves
      (algebraMap Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) M (Y.presheaf.stalk x) B hfin)
  have hyV (y : {y : X // g y = x}) : (y : X) ∈ g ⁻¹ᵁ U :=
    g.mem_preimage.mpr (y.property.symm ▸ hxU)
  let q (y : {y : X // g y = x}) := (hV.primeIdealOf ⟨y, hyV y⟩).asIdeal
  -- The prime of a point of the fibre lies over the prime `p` of `x`.
  have hq (y : {y : X // g y = x}) : (q y).LiesOver p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl (hyV y)
    rw [show (⟨g y, hyV y⟩ : U) = ⟨x, hxU⟩ from Subtype.ext y.property] at h
    exact ⟨congrArg PrimeSpectrum.asIdeal h.symm⟩
  -- Its extension to `B` lies over the maximal ideal of `𝒪_{Y,x}`, so is maximal.
  have hmax (y : {y : X // g y = x}) : ((q y).map (algebraMap _ B)).IsMaximal := by
    have := IsLocalization.AtPrime.isPrime_map_of_liesOver _ p.asIdeal B (q y)
    have := IsLocalization.AtPrime.liesOver_map_of_liesOver p.asIdeal (Y.presheaf.stalk x) B (q y)
    exact Ideal.IsMaximal.of_liesOver_isMaximal _ (maximalIdeal (Y.presheaf.stalk x))
  let e : {y : X // g y = x} → MaximalSpectrum B := fun y ↦ ⟨_, hmax y⟩
  refine ⟨.ofBijective e ⟨fun y₁ y₂ h ↦ ?_, fun m ↦ ?_⟩, fun _ ↦ rfl⟩
  · -- Primes disjoint from the localized submonoid are recovered from their extensions.
    have h' := congrArg (fun m : MaximalSpectrum B ↦ m.asIdeal.under Γ(X, g ⁻¹ᵁ U)) h
    simp only [e] at h'
    rw [IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance
        (Ideal.disjoint_primeCompl_of_liesOver _ p.asIdeal),
      IsLocalization.under_map_of_isPrime_disjoint _ B inferInstance
        (Ideal.disjoint_primeCompl_of_liesOver _ p.asIdeal)] at h'
    simpa only [IsAffineOpen.fromSpec_primeIdealOf, Subtype.ext_iff] using
      congrArg hV.fromSpec (PrimeSpectrum.ext h')
  · -- A maximal ideal of `B` lies over the maximal ideal of `𝒪_{Y,x}`, so its contraction to
    -- `Γ(X, g⁻¹ U)` is the prime of a point over `x`.
    have : m.asIdeal.LiesOver (maximalIdeal (Y.presheaf.stalk x)) :=
      ⟨(eq_maximalIdeal (Ideal.IsMaximal.under (Y.presheaf.stalk x) m.asIdeal)).symm⟩
    have := IsLocalization.AtPrime.liesOver_comap_of_liesOver p.asIdeal
      (Y.presheaf.stalk x) (S := Γ(X, g ⁻¹ᵁ U)) m.asIdeal
    let z : g ⁻¹ᵁ U := hV.isoSpec.inv ⟨m.asIdeal.under _, inferInstance⟩
    have hz : hV.primeIdealOf z = ⟨m.asIdeal.under _, inferInstance⟩ :=
      Scheme.inv_hom_apply hV.isoSpec _
    have hzx : g z = x := by
      have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl z.property
      simp only [Subtype.coe_eta] at h
      have h' : hU.primeIdealOf ⟨g z, z.property⟩ = p := by
        rw [← h, hz]
        exact PrimeSpectrum.ext (Ideal.over_def _ p.asIdeal).symm
      simpa only [hp, IsAffineOpen.fromSpec_primeIdealOf] using congrArg hU.fromSpec h'
    refine ⟨⟨z, hzx⟩, MaximalSpectrum.ext ?_⟩
    -- Unfold the local functions `e` and `q`: the ideal underlying `e ⟨z, hzx⟩` is
    -- the extension of the prime of `z`. The subtype reconstructions have the same value
    -- and proof-irrelevant membership witnesses. There is no application lemma for these
    -- local functions; exposing their definitions lets `hz` rewrite the prime ideal.
    change ((hV.primeIdealOf z).asIdeal).map _ = _
    rw [hz]
    exact IsLocalization.map_under (Algebra.algebraMapSubmonoid Γ(X, g ⁻¹ᵁ U) M) B m.asIdeal

end AlgebraicGeometry.Scheme.Hom
