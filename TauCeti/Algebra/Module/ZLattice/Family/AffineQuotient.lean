/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Algebra.Module.ZLattice.Family.Topology
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Quotients of families of tori by free affine actions

Let `P : Y → (Λ →ₗ[ℤ] E)` be a `C^n` family of full lattices over a manifold `Y`, with total space
`X = (Y × E)/Λ` (`TauCeti.isManifold_torusFamily`), and let a group `Γ` act on `X` by the affine
action `g • [y, v] = R g y v +ᵥ b g y` of a `C^n` cocycle (`TauCeti.torusFamilyAffineMulAction`),
lifting a properly discontinuous action on `Y`. If the action on `X` is free, which can hold over
fixed points of the base (`TauCeti.isCancelSMul_torusFamilyAffineMulAction_iff`), then the
standard orbit space `Q = X/Γ` carries Mathlib's quotient atlas
(`TauCeti.torusFamilyAffineQuotientChartedSpace`), for which it is a `C^n` manifold
(`TauCeti.isManifold_torusFamilyAffineQuotient`) and the orbit map `X → Q` is a `C^n` local
diffeomorphism (`TauCeti.isLocalDiffeomorph_torusFamilyAffineQuotient_mk`). Over `ℂ` with
holomorphic data, `Q` is a complex manifold and the orbit map is a local biholomorphism.

The projection of `X` to `Y` does not in general descend to `Q`, but its composite with a
`Γ`-invariant map `f : Y → Z` does: `TauCeti.torusFamilyAffineQuotientLift` sends the class of
`[y, v]` to `f y`. It is `C^n` when `f` is, and it is a submersion with complement `E` at the class
of every point of `X` whose base point is a point at which `f` is a local diffeomorphism
(`TauCeti.isSubmersionAtOfComplement_torusFamilyAffineQuotientLift`): through the orbit map, a
local diffeomorphism, it is the projection of the family, a submersion with complement `E`,
followed by `f`.

For the cyclic group `C_m` of rotations of a disc `D` and `f(z) = z ^ m`, the map
`p_Q : X / C_m → ℂ` is the projection of a cyclic quotient onto the quotient disc, of radius
`r ^ m` when `D` has radius `r`. It is a holomorphic submersion off its fibre over `0`, which is the
image of the central torus. This is the local construction of multiple fibres in the reference
below; the multiplicity of the central fibre is not computed here.

## Main definitions

* `TauCeti.torusFamilyAffineQuotientChartedSpace`: the quotient atlas on `X/Γ`.
* `TauCeti.torusFamilyAffineQuotientLift`: the map `X/Γ → Z` induced by a `Γ`-invariant map
  `f : Y → Z`.

## Main results

* `TauCeti.isManifold_torusFamilyAffineQuotient`: `X/Γ` is a `C^n` manifold.
* `TauCeti.isLocalDiffeomorph_torusFamilyAffineQuotient_mk`: the orbit map `X → X/Γ` is a `C^n`
  local diffeomorphism.
* `TauCeti.contMDiff_torusFamilyAffineQuotientLift`: the induced map is `C^n` when `f` is.
* `TauCeti.isSubmersionAtOfComplement_torusFamilyAffineQuotientLift`: the induced map is a
  submersion with complement `E` over every point at which `f` is a local diffeomorphism.
* `TauCeti.isSubmersionAtOfComplement_torusFamilyAffineQuotientLift_rootsOfUnityBall`: over the
  rotated disc, the map `X / C_m → ℂ` induced by `z ↦ z ^ m` is a holomorphic submersion off its
  fibre over `0`.
* `TauCeti.range_torusFamilyAffineQuotientLift_rootsOfUnityBall`,
  `TauCeti.preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero`: its image is the disc of
  radius `r ^ m`, and its fibre over `0` is the image of the central torus.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for quotients of
  families of tori by free cyclic actions.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti

section Lift

variable {Y : Type*} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) {Γ : Type*} [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **The map induced by an invariant map of the base.** For a map `f : Y → Z` invariant under
the action of `Γ` on `Y`, the map `X/Γ → Z` sending the class of a point `x` of the family
`X = (Y × E)/Λ` to `f` of its base point. It is well defined because the projection of the family
is equivariant. -/
def torusFamilyAffineQuotientLift {Z : Type*} (f : Y → Z) (hf : ∀ (g : Γ) y, f (g • y) = f y) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)) → Z :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  Quotient.lift (f ∘ torusFamilyProjection P) fun x x' hxx' ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hxx')
    simp [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap, hf]

/-- The induced map sends the class of a point of the family to `f` of its base point. -/
@[simp]
theorem torusFamilyAffineQuotientLift_mk {Z : Type*} (f : Y → Z)
    (hf : ∀ (g : Γ) y, f (g • y) = f y)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf (Quotient.mk _ x) =
      f (torusFamilyProjection P x) :=
  (rfl)

end Lift

section Topology

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Function.Injective (P y))
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

/-- **The atlas of a quotient of a family of tori.** For a continuous family of full lattices and a
free affine action by continuous maps, lifting a properly discontinuous action on the base,
Mathlib's quotient atlas `MulAction.instChartedSpaceQuotient` on the orbit space `X/Γ` of the
family `X = (Y × E)/Λ`: its charts are local sections of the orbit map followed by charts of `X`.
It does not depend on the proofs of its hypotheses. -/
@[instance_reducible]
noncomputable def torusFamilyAffineQuotientChartedSpace
    (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) (hbc : ∀ g, Continuous (b g))
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    ChartedSpace (ModelProd H E)
      (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P hcont hinj
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  haveI := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hRc hbc
  haveI := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  haveI := t2Space_torusFamily P hcont hinj
  haveI := locallyCompactSpace_torusFamily P hcont
  MulAction.instChartedSpaceQuotient

end Topology

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
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun p : Y × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))

/-- **A quotient of a family of tori is a manifold.** For a `C^n` family of full lattices and a free
affine action of a `C^n` cocycle, lifting a properly discontinuous action on the base, the orbit
space `X/Γ` of the family `X = (Y × E)/Λ` is a `C^n` manifold for the quotient atlas. Over `ℂ`
with holomorphic data, it is a complex manifold. -/
theorem isManifold_torusFamilyAffineQuotient :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
      hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsManifold (I.prod 𝓘(𝕜, E)) n
      (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul hbone
    hbmul hR hbc
  have := ContMDiffConstSMul.continuousConstSMul (I := I.prod 𝓘(𝕜, E)) (Γ := Γ)
    (M := AddAction.orbitRel.Quotient Λ (Y × E)) n
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  have := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
  have := locallyCompactSpace_torusFamily P (fun l ↦ (hP l).continuous)
  exact instIsManifoldQuotient

/-- **The orbit map of a quotient of a family of tori is a local diffeomorphism.** Under the
hypotheses of `TauCeti.isManifold_torusFamilyAffineQuotient`, the orbit map `X → X/Γ` is a `C^n`
local diffeomorphism; over `ℂ` with holomorphic data, it is a local biholomorphism. -/
theorem isLocalDiffeomorph_torusFamilyAffineQuotient_mk :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
      hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (Quotient.mk _ : AddAction.orbitRel.Quotient Λ (Y × E) →
        MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := isManifold_torusFamily P hinj hP
  have := contMDiffConstSMul_torusFamilyAffineMulAction P hinj hP R ρ hequiv b hb hone hmul hbone
    hbmul hR hbc
  have := ContMDiffConstSMul.continuousConstSMul (I := I.prod 𝓘(𝕜, E)) (Γ := Γ)
    (M := AddAction.orbitRel.Quotient Λ (Y × E)) n
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  have := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
  have := locallyCompactSpace_torusFamily P (fun l ↦ (hP l).continuous)
  exact isLocalDiffeomorph_quotientMk

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] {HZ : Type*}
  [TopologicalSpace HZ] {J : ModelWithCorners 𝕜 EZ HZ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace HZ Z] (f : Y → Z) (hf : ∀ (g : Γ) y, f (g • y) = f y)

/-- **The induced map of a quotient of a family of tori is `C^n`.** For a `C^n` map `f : Y → Z`
invariant under `Γ`, the map `X/Γ → Z` sending the class of a point to `f` of its base point is
`C^n`; over `ℂ` with holomorphic data and holomorphic `f`, it is holomorphic. -/
theorem contMDiff_torusFamilyAffineQuotientLift (hfn : ContMDiff I J n f) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
      hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    ContMDiff (I.prod 𝓘(𝕜, E)) J n
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
    hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
    (fun g ↦ (hbc g).continuous) hfree
  have := isManifold_torusFamily P hinj hP
  have := isManifold_torusFamilyAffineQuotient P hinj hP R ρ hequiv b hb hone hmul hbone hbmul hR
    hbc hfree
  -- The orbit map is a surjective local diffeomorphism, through which the induced map reads as
  -- `f` composed with the projection of the family.
  refine ((isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul
    hbone hbmul hR hbc hfree).contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 ?_
  exact hfn.comp (contMDiff_torusFamilyProjection P hinj hP)

/-- **The induced map of a quotient of a family of tori is a submersion.** Let `f : Y → Z` be
invariant under `Γ`, with `Z` modelled like `Y`. At the class of a point `x` of the family whose
base point `y` is a point at which `f` is a `C^n` local diffeomorphism, the map `X/Γ → Z` sending
the class of a point to `f` of its base point is a `C^n` submersion with complement `E`. Over `ℂ`
with holomorphic data, it is a holomorphic submersion there. -/
theorem isSubmersionAtOfComplement_torusFamilyAffineQuotientLift
    [ChartedSpace H Z] [IsManifold I n Z] {f : Y → Z} (hf : ∀ (g : Γ) y, f (g • y) = f y)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hfx : IsLocalDiffeomorphAt I I n f (torusFamilyProjection P x)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
      hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsSubmersionAtOfComplement E (I.prod 𝓘(𝕜, E)) I n
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf)
      (Quotient.mk _ x) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj R ρ
    hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
    (fun g ↦ (hbc g).continuous) hfree
  have := isManifold_torusFamily P hinj hP
  have := isManifold_torusFamilyAffineQuotient P hinj hP R ρ hequiv b hb hone hmul hbone hbmul hR
    hbc hfree
  -- Through the orbit map, a local diffeomorphism, the induced map is `f` composed with the
  -- projection of the family, a submersion with complement `E`.
  refine ((isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul
    hbone hbmul hR hbc hfree x).isSubmersionAtOfComplement_comp_iff).1 ?_
  have hcomp : torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf ∘
      Quotient.mk _ = f ∘ torusFamilyProjection P :=
    funext (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbone hbmul f hf)
  rw [hcomp]
  exact hfx.comp_isSubmersionAtOfComplement
    ((isSubmersionOfComplement_torusFamilyProjection P hinj hP).isSubmersionAt x)

end Regularity

section RotatedDiscLift

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))

/-- **The cyclic quotient lies over the quotient disc.** For a family of tori `X → D` over the
disc `D` of radius `r ≥ 0` and an affine action of the `m`-th roots of unity lifting the
rotations, the map `p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` has image the disc of radius
`r ^ m`, the quotient of `D` by the rotations (`TauCeti.rootsOfUnityBallQuotientHomeomorph`). -/
theorem range_torusFamilyAffineQuotientLift_rootsOfUnityBall (hr : 0 ≤ r) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    Set.range (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) =
      Metric.ball 0 (r ^ m) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  rw [← image_pow_ball hr]
  ext t
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Quotient.inductionOn with | h x =>
    induction x using Quotient.inductionOn with | h p =>
    rw [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk]
    exact ⟨p.1, mem_ball_zero_iff.2 (mem_rootsOfUnityBall.1 p.1.2), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Quotient.mk _ (Quotient.mk _
      (⟨u, mem_rootsOfUnityBall.2 (mem_ball_zero_iff.1 hu)⟩, 0)), ?_⟩
    rw [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk]

/-- **The central fibre of the cyclic quotient.** For a family of tori `X → D` over the disc and
an affine action of the `m`-th roots of unity lifting the rotations, the fibre over `0` of the map
`p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` is the image in `X / C_m` of the fibre of `X` over the
centre `u₀` of the disc, the central torus `T₀ = E / LinearMap.range (P u₀)`. -/
theorem preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero {u₀ : rootsOfUnityBall m r}
    (hu₀ : (u₀ : ℂ) = 0) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) ⁻¹'
        {0} = Set.range fun v : E ↦ Quotient.mk _ (Quotient.mk _ (u₀, v)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  ext y
  induction y using Quotient.inductionOn with | h x =>
  induction x using Quotient.inductionOn with | h p =>
  rw [Set.mem_preimage, torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk,
    Set.mem_singleton_iff, pow_eq_zero_iff (NeZero.ne m)]
  constructor
  · intro hp
    exact ⟨p.2, by rw [show u₀ = p.1 from Subtype.ext (hu₀.trans hp.symm)]⟩
  · rintro ⟨v, hv⟩
    -- The map induced by `z ↦ z ^ m` takes the same value on both classes, `0` on the class of
    -- a point over the centre.
    have h := congrArg (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) hv
    simp only [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk, hu₀,
      zero_pow (NeZero.ne m)] at h
    exact (pow_eq_zero_iff (NeZero.ne m)).1 h.symm

end RotatedDiscLift

section RotatedDisc

variable {m : ℕ} [NeZero m] {r : ℝ}
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) [∀ z, DiscreteTopology (LinearMap.range (P z))]
  [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hinj : ∀ z, Function.Injective (P z)) (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) ω fun z ↦ P z l)
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))
  (hR : ∀ g : rootsOfUnity m ℂ,
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) ω fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) ω (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- **The cyclic quotient is a holomorphic submersion off the central fibre.** For a holomorphic
family of tori `X → D` over the disc `D` and a free holomorphic affine action of the `m`-th roots of
unity lifting the rotations, the map `p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` is a holomorphic
submersion, with complement `E`, at every point of `X / C_m` that it does not send to `0`. Freeness
of the action is characterized by
`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`. -/
theorem isSubmersionAtOfComplement_torusFamilyAffineQuotientLift_rootsOfUnityBall
    (y : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
    (hy : torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) y ≠
        0) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj R ρ
      hequiv b hb hone hmul hbone hbmul (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsSubmersionAtOfComplement E (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) ω
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
      y := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  induction y using Quotient.inductionOn with | h x =>
  rw [torusFamilyAffineQuotientLift_mk] at hy
  exact isSubmersionAtOfComplement_torusFamilyAffineQuotientLift P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree _ x
    (isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall le_top fun h ↦ hy (by rw [h, zero_pow
      (NeZero.ne m)]))

end RotatedDisc

end TauCeti
