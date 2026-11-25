/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Algebra.Module.ZLattice.Family.DiffeomorphProd
public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.Geometry.Manifold.Quotient.Trivialization
public import TauCeti.Topology.FiberBundle.Trivialization

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

Over `𝕜 = ℝ`, the descended family is moreover smoothly locally trivial with fibre the standard
torus `ℝ^ι/ℤ^ι`, for a `ℤ`-basis of `Λ` indexed by `ι`
(`TauCeti.exists_trivialization_torusFamilyAffineProjection_orbitRelQuotientMap`). Every point of
`Y` has an open neighbourhood `V` on which the orbit projection of `Y` is injective, and over the
image of `V` the smooth global trivialization `[y, v] ↦ (y, [F_y⁻¹ v])` of
`TauCeti.torusFamilyDiffeomorphProd`, restricted to `p⁻¹(V)`, descends to `X/Γ`
(`Bundle.Trivialization.orbitRelQuotient`). Like the global trivialization, these are real `C^n`
trivializations; no holomorphic triviality is claimed.

Freeness of the action on `Y` is needed for `Y/Γ` to be a manifold. When `Γ` has fixed points on
`Y`, the free locus of the base (`TauCeti.freeLocus`) is open and invariant, but this file does
not restrict the family to it.

## Main results

* `TauCeti.isSubmersionOfComplement_torusFamilyAffineProjection_orbitRelQuotientMap`: the descended
  projection `X/Γ → Y/Γ` is a `C^n` submersion with complement `E`.
* `TauCeti.exists_trivialization_torusFamilyAffineProjection_orbitRelQuotientMap`: over the image
  of a neighbourhood of each point of `Y`, the descended projection has a `C^n` trivialization with
  `C^n` inverse and fibre `ℝ^ι/ℤ^ι`, given on representatives by the period coordinates.

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
  {Λ : Type*} [AddCommGroup Λ]
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
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    haveI := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
    haveI := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
    haveI : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      t2Space_of_properlyDiscontinuousVAdd_of_t2Space
    haveI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    haveI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbmul
    haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
    haveI := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    Manifold.IsSubmersionOfComplement E (I.prod 𝓘(𝕜, E)) I n
      (MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbmul)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    t2Space_of_properlyDiscontinuousVAdd_of_t2Space
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  have := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul
    hbmul hR hbc
  refine isSubmersionOfComplement_orbitRelQuotientMap ?_
  rw [coe_torusFamilyAffineProjectionHom]
  exact isSubmersionOfComplement_torusFamilyProjection P hinj hP

end Regularity

section Trivialization

open Bundle Module Set Submodule

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(ℝ, E) n fun y ↦ P y l)
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y]
  [IsCancelSMul Γ Y] [ContMDiffConstSMul I n Γ Y] (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbmul : ∀ (g h : Γ) (y : Y),
    b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  {ι : Type*} [Fintype ι] (bΛ : Basis ι ℤ Λ)

/-- **The descended family of tori is smoothly locally trivial.** Let `Γ` act on the base `Y`
freely, properly discontinuously and by `C^n` maps, and on the family of tori `X = (Y × E)/Λ` of a
`C^n` family of full lattices by an affine cocycle with `C^n` linear-part evaluations and `C^n`
translation sections. Fix a `ℤ`-basis `bΛ` of `Λ`, indexed by `ι`. Then every `y₀ : Y` has an open
neighbourhood `V` over whose image in `Y/Γ` the descended projection `X/Γ → Y/Γ` has a `C^n`
trivialization with fibre the standard torus `ℝ^ι/ℤ^ι`, with `C^n` inverse. On representatives
over `V` it is the smooth global trivialization `TauCeti.torusFamilyDiffeomorphProd` of the family
over `Y`: it sends the orbit of `[y, v]` to the orbit of `y` and the class of the coordinates of `v`
in the period basis at `y`. -/
theorem exists_trivialization_torusFamilyAffineProjection_orbitRelQuotientMap
    (hR : ∀ g : Γ,
      ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) n fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      ∀ g, ContMDiff I (I.prod 𝓘(ℝ, E)) n (b g)) (y₀ : Y) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    haveI := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
    haveI := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
    haveI : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      t2Space_of_properlyDiscontinuousVAdd_of_t2Space
    haveI : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
      AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
    haveI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbmul
    haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
    haveI := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
      ∃ e : Trivialization (AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ))
        (MulActionHom.orbitRelQuotientMap
          (torusFamilyAffineProjectionHom R hone hmul P ρ hequiv b hb hbmul)),
        e.baseSet = Quotient.mk _ '' V ∧
        (∀ y ∈ V, ∀ v : E, e (Quotient.mk _ (Quotient.mk _ (y, v))) =
          (Quotient.mk _ y, Quotient.mk _ ((periodBasis P bΛ hinj y).equivFun v))) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ι → ℝ)) n e e.source ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) (I.prod 𝓘(ℝ, E)) n e.toOpenPartialHomeomorph.symm
          e.target := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  have : T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    t2Space_of_properlyDiscontinuousVAdd_of_t2Space
  have : LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) :=
    AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb
    hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  have := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul
    hbmul hR hbc
  have : Nonempty (AddAction.orbitRel.Quotient Λ (Y × E)) := ⟨Quotient.mk _ (y₀, 0)⟩
  -- A chart of the orbit projection of `Y` at `y₀` gives a neighbourhood on which it is injective.
  obtain ⟨c, hy₀, hc⟩ :=
    (isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := Γ)).isLocalHomeomorph y₀
  let D := torusFamilyDiffeomorphProd P bΛ hinj hP (n := n)
  let e := (D.toHomeomorph.toTrivialization (proj := torusFamilyAffineProjectionHom R hone hmul
    P ρ hequiv b hb hbmul) fun z ↦ by
      simp only [Diffeomorph.coe_toHomeomorph, coe_torusFamilyAffineProjectionHom]
      exact fst_torusFamilyDiffeomorphProd P bΛ hinj hP z).restrOpen
    c.source c.open_source
  have hinjV : InjOn (Quotient.mk (MulAction.orbitRel Γ Y)) e.baseSet :=
    (hc ▸ c.injOn).mono inter_subset_right
  have hfree : ∀ y ∈ e.baseSet, ∀ g : Γ, g • y = y → g = 1 :=
    fun _ _ _ hg ↦ IsCancelSMul.eq_one_of_smul hg
  refine ⟨c.source, c.open_source, hy₀, e.orbitRelQuotient hinjV hfree, by simp [e], ?_,
    e.contMDiffOn_orbitRelQuotient hinjV hfree (by simpa [e] using D.contMDiff.contMDiffOn),
    e.contMDiffOn_orbitRelQuotient_symm hinjV hfree
      (by simpa [e] using D.symm.contMDiff.contMDiffOn)⟩
  intro y hy v
  rw [e.orbitRelQuotient_apply_mk hinjV hfree (e.mem_source.2 (by simpa [e] using hy))]
  simp [e, D]

end Trivialization

end TauCeti
