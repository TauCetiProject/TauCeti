/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Algebra.Module.ZLattice.Family.Topology
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
followed by `f`. Every chart of the quotient atlas reads the induced map through its first
coordinate alone: a chart of `X/Γ` is the inverse of a chart of `X` followed by the orbit map, and
the first coordinate of a chart of `X` is a chart coordinate of `Y`
(`TauCeti.exists_torusFamilyAffineQuotientLift_symm_eq_of_mem_atlas`).

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
* `TauCeti.exists_torusFamilyAffineQuotientLift_symm_eq_of_mem_atlas`: every chart of the
  quotient atlas reads the induced map as `(u, v) ↦ f (c.symm u)` for a chart `c` of `Y`.

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

/-- The affine quotient projection induced by a continuous invariant base map is continuous. -/
theorem continuous_torusFamilyAffineQuotientLift [TopologicalSpace Y] [TopologicalSpace E]
    {Z : Type*} [TopologicalSpace Z] {f : Y → Z}
    {hf : ∀ (g : Γ) y, f (g • y) = f y} (hfc : Continuous f) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    Continuous (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf) := by
  apply isQuotientMap_quot_mk.continuous_iff.2
  convert hfc.comp (continuous_torusFamilyProjection P) using 1
  funext x
  exact torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbone hbmul f hf x

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

/-- **Charts of the quotient read the induced map on the base coordinate.** For a `Γ`-invariant
map `f : Y → Z`, every chart `e` of the quotient atlas of `X/Γ` reads the induced map
`X/Γ → Z` through the first coordinate and the inverse of a chart of `Y`: there is a point `y`
such that the induced map sends `e.symm (u, v)` to `f ((chartAt H y).symm u)` on the target of
`e`. Its value does not depend on the fibre coordinate `v`. -/
theorem exists_torusFamilyAffineQuotientLift_symm_eq_of_mem_atlas {Z : Type*} (f : Y → Z)
    (hf : ∀ (g : Γ) y, f (g • y) = f y) (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    {e : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      OpenPartialHomeomorph (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
        (ModelProd H E)}
    (he : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
        hbone hbmul hcont hRc hbc hfree
      e ∈ atlas (ModelProd H E)
        (MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)))) :
    ∃ y : Y, ∀ w ∈ e.target, w.1 ∈ (chartAt H y).target ∧
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf (e.symm w) =
        f ((chartAt H y).symm w.1) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P hcont hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  -- A chart of `X/Γ` is the inverse of a chart of `X` followed by the orbit map, and a chart of
  -- `X` reads the projection to `Y` through a chart of `Y`.
  obtain ⟨x, hx⟩ := exists_symm_eq_mk_of_mem_atlas_torusFamilyAffineQuotient P hinj R ρ hequiv b
    hb hone hmul hbone hbmul hcont hRc hbc hfree he
  obtain ⟨y, hy⟩ := exists_torusFamilyProjection_symm_eq_of_mem_atlas P hcont hinj
    (chart_mem_atlas (ModelProd H E) x)
  refine ⟨y, fun w hw ↦ ?_⟩
  obtain ⟨hwx, hw⟩ := hx w hw
  obtain ⟨hwy, hwp⟩ := hy w hwx
  rw [hw, torusFamilyAffineQuotientLift_mk, hwp]
  exact ⟨hwy, rfl⟩

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
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    ContMDiff (I.prod 𝓘(𝕜, E)) J n
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
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
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsSubmersionAtOfComplement E (I.prod 𝓘(𝕜, E)) I n
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul f hf)
      (Quotient.mk _ x) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
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

end TauCeti
