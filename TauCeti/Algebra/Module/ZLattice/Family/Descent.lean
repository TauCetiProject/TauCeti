/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Geometry.Manifold.Quotient.Descent

/-!
# Descent of a family of tori through a free action on the base

Let `P : Y → (Λ →ₗ[ℤ] E)` be a `C^n` family of full period lattices over a manifold `Y`, with
total space `X = (Y × E)/Λ` and projection `p : X → Y` (`TauCeti.torusFamilyProjection`). Let a
group `Γ` act on `Y` freely, properly discontinuously and by `C^n` maps, and act on `X` by a `C^n`
affine cocycle `g • [y, v] = R g y v +ᵥ b g y` (`TauCeti.torusFamilyAffineMulAction`), whose
translation part `b g` is a section of the family itself.

The affine action on `X` is then free and properly discontinuous by `C^n` maps, so both orbit
spaces `X/Γ` and `Y/Γ` are `C^n` manifolds. The projection `p` is equivariant
(`TauCeti.torusFamilyAffineProjectionHom`), so it descends to a map `X/Γ → Y/Γ`, sending the
orbit of `[y, v]` to the orbit of `y`. This file proves that the descended projection is a `C^n`
submersion with complement `E`, like `p` itself
(`TauCeti.isSubmersionOfComplement_torusFamilyAffineProjection_orbitRelQuotientMap`): near each
point of `X/Γ`, it is `p` read through local sections of the two orbit projections. For a complex
manifold `Y`, a complex space `E`, `𝕜 = ℂ` and holomorphic data, `X/Γ → Y/Γ` is a holomorphic
submersion.

Freeness of the action on `Y` is needed for `Y/Γ` to be a manifold. When `Γ` has fixed points on
`Y`, the free locus of the base (`TauCeti.freeLocus`) is open and invariant, but this file does
not restrict the family to it.

## Main results

* `TauCeti.isSubmersionOfComplement_torusFamilyAffineProjection_orbitRelQuotientMap`: the descended
  projection `X/Γ → Y/Γ` is a `C^n` submersion with complement `E`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y]
  [IsCancelSMul Γ Y] [ContMDiffConstSMul I n Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y),
    b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **The descended family of tori is a submersion.** Let `Γ` act on the base `Y` freely, properly
discontinuously and by `C^n` maps, and on the family of tori `X = (Y × E)/Λ` of a `C^n` family of
full lattices by an affine cocycle with `C^n` linear-part evaluations `(y, v) ↦ R g y v` and `C^n`
translation sections `b g`. Then the projection `X → Y` descends to a `C^n` submersion
`X/Γ → Y/Γ` with complement `E`, for the quotient manifold structures. Over `ℂ` with holomorphic
data, it is a holomorphic submersion. -/
theorem isSubmersionOfComplement_torusFamilyAffineProjection_orbitRelQuotientMap
    (hR : ∀ g : Γ,
      ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    haveI := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
    haveI := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
    haveI : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      t2Space_of_properlyDiscontinuousVAdd_of_t2Space
    haveI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    haveI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbone hbmul
    haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
    haveI := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    Manifold.IsSubmersionOfComplement E (I.prod 𝓘(𝕜, E)) I n
      (MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbone hbmul)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    t2Space_of_properlyDiscontinuousVAdd_of_t2Space
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbone hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  have := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul hbone
    hbmul hR hbc
  refine isSubmersionOfComplement_orbitRelQuotientMap ?_
  rw [coe_torusFamilyAffineProjectionHom]
  exact isSubmersionOfComplement_torusFamilyProjection P hinj hP

end Regularity

end TauCeti
