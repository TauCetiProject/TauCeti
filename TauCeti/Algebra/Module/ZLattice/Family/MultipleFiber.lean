/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.RotatedDisc
public import TauCeti.Algebra.Module.ZLattice.Family.Stabilizer
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# The multiple fibre of a cyclic quotient of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a family of full lattices with total space `X = (Y × E)/Λ`, and let a
group `Γ` act on `X` by an affine cocycle `g • [y, v] = R g y v +ᵥ b g y`
(`TauCeti.torusFamilyAffineMulAction`) lifting an action on `Y`. If `y` is fixed by every element
of `Γ`, then `Γ` acts on the torus `T_y = E / LinearMap.range (P y)` by affine automorphisms
(`TauCeti.torusFamilyFiberMulAction`), and the inclusion `T_y → X` of the fibre over `y` is
equivariant. It therefore induces a map of orbit spaces

`ι : T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`

(`MulActionHom.orbitRelQuotientMap` applied to `TauCeti.torusFamilyFiberMulActionHom`). This map is
injective (`TauCeti.orbitRelQuotientMap_torusFamilyFiberMulActionHom_injective`), and its image is
the image in `X / Γ` of the fibre of `X` over `y`
(`TauCeti.range_orbitRelQuotientMap_torusFamilyFiberMulActionHom`).

Suppose the data are `C^n`, `Γ` acts properly discontinuously on `Y` and freely on `X`. Then `Γ`
also acts freely, properly discontinuously and by `C^n` maps on `T_y`, so the orbit space
`T_y / Γ` carries Mathlib's quotient atlas (`TauCeti.torusFamilyFiberQuotientChartedSpace`), for
which it is a `C^n` manifold modelled on `E` (`TauCeti.isManifold_torusFamilyFiberQuotient`). Over
`ℝ` or `ℂ`, for a boundaryless finite-dimensional model of `Y` and `n ≥ 1`, the map `ι` is a `C^n`
embedding into the manifold `X / Γ`
(`TauCeti.isSmoothEmbedding_orbitRelQuotientMap_torusFamilyFiberMulActionHom`): an immersion
which is a homeomorphism onto its image, the compact torus quotient `T_y / Γ` being embedded in the
Hausdorff space `X / Γ`. The model of `T_y / Γ` is `E`, while that of `X / Γ` is
the product of the model of `Y` with `E`.

## The central fibre over a rotated disc

Over the disc `D = TauCeti.rootsOfUnityBall m r`, rotated by the group `C_m` of `m`-th roots of
unity, the centre `u₀` is fixed by every rotation. For a free affine action of `C_m` on the family
`X → D` lifting the rotations, the orbit space `Q = X / C_m` is a complex manifold with a
holomorphic map `p_Q : Q → ℂ` induced by `z ↦ z ^ m`
(`TauCeti.torusFamilyAffineQuotientLift`). Its fibre over `0` is the multiple fibre
`F = p_Q⁻¹(0)`, and it is the image of `ι : T₀ / C_m → Q`
(`TauCeti.range_orbitRelQuotientMap_torusFamilyFiberMulActionHom_rootsOfUnityBall`). With the
embedding theorem above, `ι` is a holomorphic embedding of the compact complex manifold `T₀ / C_m`
onto `F`, of complex codimension one.

Near every point of `Q` there are holomorphic coordinates `(u, w)`, valued in `D × E`, in which
`p_Q = u ^ m` (`TauCeti.exists_partialDiffeomorph_torusFamilyAffineQuotientLift_eq_pow`): they are
local inverses of the composite orbit map `D × E → X → Q`, a local biholomorphism along which
`p_Q` is `(z, v) ↦ z ^ m`. Near a point of `F` the coordinate `u` vanishes exactly on `F`, so in
these coordinates `F` is the slice `u = 0` and `p_Q` is the `m`-th power of its defining
coordinate.

## Main results

* `TauCeti.orbitRelQuotientMap_torusFamilyFiberMulActionHom_injective`,
  `TauCeti.range_orbitRelQuotientMap_torusFamilyFiberMulActionHom`: the map `T_y / Γ → X / Γ` is
  injective, with image the image of the fibre over `y`.
* `TauCeti.isManifold_torusFamilyFiberQuotient`,
  `TauCeti.isLocalDiffeomorph_torusFamilyFiberQuotient_mk`: `T_y / Γ` is a `C^n` manifold, and the
  orbit map `T_y → T_y / Γ` is a `C^n` local diffeomorphism.
* `TauCeti.isSmoothEmbedding_orbitRelQuotientMap_torusFamilyFiberMulActionHom`: the map
  `T_y / Γ → X / Γ` is a `C^n` embedding.
* `TauCeti.range_orbitRelQuotientMap_torusFamilyFiberMulActionHom_rootsOfUnityBall`: over the
  rotated disc, its image is the fibre over `0` of the map `X / C_m → ℂ` induced by `z ↦ z ^ m`.
* `TauCeti.exists_partialDiffeomorph_torusFamilyAffineQuotientLift_eq_pow`: in suitable local
  holomorphic coordinates `(u, w)` on `X / C_m`, that map is `u ^ m`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for the multiple
  fibre of the cyclic quotient of a family of tori over a disc and its local equation `t = u ^ m`.
-/

public section

open Function Set MulAction Manifold
open scoped Manifold ContDiff

namespace TauCeti

/-! ### The orbit space of the fibre over a fixed point -/

section Algebra

variable {Y Λ E Γ : Type*} [AddCommGroup Λ] [AddCommGroup E] [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  {y : Y} (hy : ∀ g : Γ, g • y = y)

/-- **The fibre over a fixed point embeds into the quotient.** Two points of the fibre over a
fixed point `y` lying in one orbit of the affine action on the family lie in one orbit of the
action on the fibre, so the map `T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`, is injective. -/
theorem orbitRelQuotientMap_torusFamilyFiberMulActionHom_injective :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    Injective (MulActionHom.orbitRelQuotientMap
      (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  intro q q' h
  induction q using Quotient.inductionOn with | h z =>
  induction q' using Quotient.inductionOn with | h z' =>
  simp only [MulActionHom.orbitRelQuotientMap_mk, coe_torusFamilyFiberMulActionHom,
    Quotient.eq, orbitRel_apply, mem_orbit_iff] at h ⊢
  obtain ⟨g, hg⟩ := h
  rw [← torusFamilyFiberMap_smul R hone hmul P ρ hequiv b hb hbone hbmul hy] at hg
  exact ⟨g, torusFamilyFiberMap_injective P y hg⟩

/-- **The image of the fibre over a fixed point.** The image of the map
`T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`, consists of the orbits of the points of the family lying
over `y`. -/
theorem range_orbitRelQuotientMap_torusFamilyFiberMulActionHom :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    range (MulActionHom.orbitRelQuotientMap
      (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy)) =
      Quotient.mk _ '' {x | torusFamilyProjection P x = y} := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  rw [← Quotient.mk_surjective.range_comp, MulActionHom.orbitRelQuotientMap_comp_mk, range_comp,
    coe_torusFamilyFiberMulActionHom, range_torusFamilyFiberMap]

end Algebra

section Topology

variable {Y Λ E Γ : Type*} [AddCommGroup Λ] [Group Γ] [MulAction Γ Y] [TopologicalSpace Y]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  {y : Y} (hy : ∀ g : Γ, g • y = y) (hcont : ∀ l, Continuous fun y ↦ P y l)

include hcont in
/-- The action on the fibre over a fixed point is by continuous maps when the linear-part
evaluations and the translation sections of the affine action are continuous: the fibre carries
the subspace topology of the family, on which the action is continuous. -/
theorem continuousConstSMul_torusFamilyFiberMulAction
    (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g)) :
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    ContinuousConstSMul Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hRc hbc
  exact (isEmbedding_torusFamilyFiberMap P y hcont).isInducing.continuousConstSMul id
    fun {g z} ↦ torusFamilyFiberMap_smul R hone hmul P ρ hequiv b hb hbone hbmul hy g z

include hcont in
/-- The action on the fibre over a fixed point is properly discontinuous whenever the action on
the base is: the inclusion of the fibre is continuous and equivariant, and the affine action on
the family is properly discontinuous. -/
theorem properlyDiscontinuousSMul_torusFamilyFiberMulAction [ProperlyDiscontinuousSMul Γ Y] :
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    ProperlyDiscontinuousSMul Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  exact (isEmbedding_torusFamilyFiberMap P y hcont).continuous.properlyDiscontinuousSMul
    (torusFamilyFiberMap_smul R hone hmul P ρ hequiv b hb hbone hbmul hy)

end Topology

/-! ### The manifold structure of the orbit space of the fibre -/

section Atlas

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  {y : Y} (hy : ∀ g : Γ, g • y = y)

/-- **The atlas of the orbit space of the fibre over a fixed point.** Let `Γ` act properly
discontinuously on `Y`, fixing `y`, and freely on the family of tori `X = (Y × E)/Λ` of a
continuous family of discrete lattices by an affine cocycle with continuous linear-part
evaluations and translation sections. This is Mathlib's quotient atlas
`MulAction.instChartedSpaceQuotient` on the orbit space `T_y / Γ` of the action on the torus
`T_y = E / LinearMap.range (P y)`: its charts are local sections of the orbit map followed by
charts of `T_y`. It does not depend on the proofs of the hypotheses. -/
@[instance_reducible]
noncomputable def torusFamilyFiberQuotientChartedSpace (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hRc : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    ChartedSpace E
      (orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E)) :=
  letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  haveI := continuousConstSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hy hcont hRc hbc
  haveI := properlyDiscontinuousSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul hy hcont
  haveI := isCancelSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy hfree
  haveI := (AddAction.isOpenQuotientMap_quotientMk (Γ := LinearMap.range (P y))
    (T := E)).locallyCompactSpace
  MulAction.instChartedSpaceQuotient (H := E)

end Atlas

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
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
  {y : Y} (hy : ∀ g : Γ, g • y = y)

omit [T2Space Y] [LocallyCompactSpace Y] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] [IsManifold I n Y] [ProperlyDiscontinuousSMul Γ Y] in
include hR in
/-- The action on the fibre over a fixed point is by `C^n` maps of the torus `T_y` when the
linear-part evaluations of the affine action are `C^n`: on representatives, `g` acts by
`v ↦ R g y v + β` for a representative `β` of its translation part. -/
theorem contMDiffConstSMul_torusFamilyFiberMulAction :
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    ContMDiffConstSMul 𝓘(𝕜, E) n Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) := by
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  refine ⟨fun g ↦ ?_⟩
  obtain ⟨β, hβ⟩ := Quotient.exists_rep (torusFamilyFiberTranslationPart P b hb (hy g))
  refine Submodule.contMDiff_orbitRelQuotient_of_comp_mk (f := fun v ↦ R g y v + β)
    (((hR g).comp (contMDiff_const.prodMk contMDiff_id)).add contMDiff_const) (funext fun v ↦ ?_)
  rw [comp_apply, torusFamilyFiberMulAction_smul, AddEquiv.affineEquiv_apply,
    torusFamilyFiberLinearPart_mk, ← hβ, comp_apply, Submodule.orbitRelQuotient_mk_add]

omit [IsManifold I n Y] in
/-- The orbit map `T_y → T_y / Γ` is a `C^n` local diffeomorphism, and `T_y / Γ` is a `C^n`
manifold. -/
private theorem isLocalDiffeomorph_torusFamilyFiberQuotient_mk_and_isManifold :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Quotient.mk (orbitRel Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E))) ∧
      IsManifold 𝓘(𝕜, E) n
        (orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  have := continuousConstSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  have := (AddAction.isOpenQuotientMap_quotientMk (Γ := LinearMap.range (P y))
    (T := E)).locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul hy fun l ↦ (hP l).continuous
  have := isCancelSMul_torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy hfree
  have := contMDiffConstSMul_torusFamilyFiberMulAction P R ρ hequiv b hb hone hmul hbone hbmul hR hy
  exact ⟨isLocalDiffeomorph_quotientMk, instIsManifoldQuotient⟩

omit [IsManifold I n Y] in
/-- **The orbit space of the fibre over a fixed point is a manifold.** Let `Γ` act properly
discontinuously on `Y`, fixing `y`, and freely on the family of tori `X = (Y × E)/Λ` of a `C^n`
family of full lattices by an affine cocycle with `C^n` linear-part evaluations and translation
sections. Then the orbit space `T_y / Γ` of the torus `T_y = E / LinearMap.range (P y)` is a `C^n`
manifold modelled on `E`. Over `ℂ` with holomorphic data and `n = ω`, it is a complex manifold. -/
theorem isManifold_torusFamilyFiberQuotient :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    IsManifold 𝓘(𝕜, E) n
      (orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E)) :=
  (isLocalDiffeomorph_torusFamilyFiberQuotient_mk_and_isManifold P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree hy).2

omit [IsManifold I n Y] in
/-- **The orbit map of the fibre over a fixed point is a local diffeomorphism.** Under the
hypotheses of `TauCeti.isManifold_torusFamilyFiberQuotient`, the orbit map `T_y → T_y / Γ` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_torusFamilyFiberQuotient_mk :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) n
      (Quotient.mk (orbitRel Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E))) :=
  (isLocalDiffeomorph_torusFamilyFiberQuotient_mk_and_isManifold P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree hy).1

/-- **The fibre over a fixed point maps smoothly to the quotient.** Under the hypotheses of
`TauCeti.isManifold_torusFamilyFiberQuotient`, the map `T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`, is
`C^n`; over `ℂ` with holomorphic data and `n = ω`, it is holomorphic. -/
theorem contMDiff_orbitRelQuotientMap_torusFamilyFiberMulActionHom :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    ContMDiff 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (MulActionHom.orbitRelQuotientMap
      (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  -- Through the orbit map of `T_y`, a surjective local diffeomorphism, the map reads as the
  -- inclusion of the fibre followed by the orbit map of `X`.
  rw [← (isLocalDiffeomorph_torusFamilyFiberQuotient_mk P hinj hP R ρ hequiv b hb hone hmul hbone
      hbmul hR hbc hfree hy).contMDiff_comp_iff Quotient.mk_surjective le_rfl,
    MulActionHom.orbitRelQuotientMap_comp_mk, coe_torusFamilyFiberMulActionHom]
  exact (isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul hbone
    hbmul hR hbc hfree).contMDiff.comp (contMDiff_torusFamilyFiberMap P hinj hP y)

end Regularity

section Embedding

variable {𝕜 : Type*} [RCLike 𝕜] {EY : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [FiniteDimensional 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  [I.Boundaryless] {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y]
  [LocallyCompactSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
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
  {y : Y} (hy : ∀ g : Γ, g • y = y)

/-- **The fibre over a fixed point immerses into the quotient.** Under the hypotheses of
`TauCeti.isManifold_torusFamilyFiberQuotient`, over `ℝ` or `ℂ`, for a boundaryless
finite-dimensional model of `Y` and `n ≥ 1`, the map `T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`, is a
`C^n` immersion. -/
theorem isImmersion_orbitRelQuotientMap_torusFamilyFiberMulActionHom (hn : 1 ≤ n) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    IsImmersion 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (MulActionHom.orbitRelQuotientMap
      (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  have := isManifold_torusFamilyAffineQuotient P hinj hP R ρ hequiv b hb hone hmul hbone hbmul hR
    hbc hfree
  have := isManifold_torusFamilyFiberQuotient P hinj hP R ρ hequiv b hb hone hmul hbone hbmul hR
    hbc hfree hy
  -- Through the orbit map of `T_y`, a local diffeomorphism, the map reads as the inclusion of the
  -- fibre, an immersion, followed by the orbit map of `X`, a local diffeomorphism.
  have himm := isImmersion_isLocalDiffeomorphAt_comp (fun _ ↦
    isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul hbone
      hbmul hR hbc hfree _) (isImmersion_torusFamilyFiberMap P hinj hP hn y)
  rw [← coe_torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy,
    ← MulActionHom.orbitRelQuotientMap_comp_mk] at himm
  refine isImmersion_iff_forall_isImmersionAt.2 fun q ↦ ?_
  induction q using Quotient.inductionOn with | h z =>
  exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff
    (isLocalDiffeomorph_torusFamilyFiberQuotient_mk P hinj hP R ρ hequiv b hb hone hmul hbone hbmul
      hR hbc hfree hy z)).1 (himm.isImmersionAt z)

/-- **The fibre over a fixed point embeds into the quotient.** Under the hypotheses of
`TauCeti.isManifold_torusFamilyFiberQuotient`, over `ℝ` or `ℂ`, for a boundaryless
finite-dimensional model of `Y` and `n ≥ 1`, the map `T_y / Γ → X / Γ`, `[[v]] ↦ [[y, v]]`, is a
`C^n` embedding, with image the orbits of the fibre over `y`
(`TauCeti.range_orbitRelQuotientMap_torusFamilyFiberMulActionHom`). For a complex family with
holomorphic data and `n = ω`, it embeds the compact complex manifold `T_y / Γ` holomorphically into
`X / Γ`. -/
theorem isSmoothEmbedding_orbitRelQuotientMap_torusFamilyFiberMulActionHom (hn : 1 ≤ n) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    IsSmoothEmbedding 𝓘(𝕜, E) (I.prod 𝓘(𝕜, E)) n (MulActionHom.orbitRelQuotientMap
      (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv b hb hbone hbmul hy)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul hy
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbone hbmul hy
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  -- The orbit space of `X` is Hausdorff, and the compact torus quotient `T_y / Γ` maps
  -- continuously and injectively into it.
  have := continuousConstVAdd_periodAddAction P fun l ↦ (hP l).continuous
  have := t2Space_torusFamily P (fun l ↦ (hP l).continuous) hinj
  have := (AddAction.isOpenQuotientMap_quotientMk (Γ := Λ) (T := Y × E)).locallyCompactSpace
  have := properlyDiscontinuousSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone
    hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) fun g ↦ (hbc g).continuous
  refine ⟨isImmersion_orbitRelQuotientMap_torusFamilyFiberMulActionHom P hinj hP R ρ hequiv b hb
    hone hmul hbone hbmul hR hbc hfree hy hn, ?_⟩
  exact ((contMDiff_orbitRelQuotientMap_torusFamilyFiberMulActionHom P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree hy).continuous.isClosedEmbedding
      (orbitRelQuotientMap_torusFamilyFiberMulActionHom_injective R hone hmul P ρ hequiv b hb hbone
        hbmul hy)).isEmbedding

end Embedding

/-! ### The multiple fibre over a rotated disc -/

section RotatedDisc

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

/-- **The multiple fibre is the quotient of the central torus.** For a family of tori `X → D` over
the disc and an affine action of the `m`-th roots of unity lifting the rotations, the fibre over
`0` of the map `p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` is the image of the map
`T₀ / C_m → X / C_m`, `[[v]] ↦ [[u₀, v]]`, from the orbit space of the central torus
`T₀ = E / LinearMap.range (P u₀)` under the action of the rotations, which fix the centre `u₀`. -/
theorem range_orbitRelQuotientMap_torusFamilyFiberMulActionHom_rootsOfUnityBall
    {u₀ : rootsOfUnityBall m r} (hu₀ : (u₀ : ℂ) = 0) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g
    range (MulActionHom.orbitRelQuotientMap (torusFamilyFiberMulActionHom R hone hmul P ρ hequiv
      b hb hbone hbmul fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)) =
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m)
        (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) ⁻¹' {0} := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  rw [preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero P R ρ hequiv b hb hone hmul
      hbone hbmul hu₀, range_orbitRelQuotientMap_torusFamilyFiberMulActionHom,
    ← range_torusFamilyFiberMap, ← range_comp, ← Quotient.mk_surjective.range_comp]
  exact congrArg range (funext fun v ↦ by rw [comp_apply, comp_apply, torusFamilyFiberMap_mk])

end RotatedDisc

section RotatedDiscChart

variable {m : ℕ} [NeZero m] {r : ℝ}
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) [∀ z, DiscreteTopology (LinearMap.range (P z))]
  [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hinj : ∀ z, Injective (P z)) {n : ℕ∞ω} (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun z ↦ P z l)
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
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) n fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- **The local equation `t = u ^ m` of the cyclic quotient.** For a `C^n` family of tori `X → D`
over the disc and a free `C^n` affine action of the `m`-th roots of unity lifting the rotations,
every point of `Q = X / C_m` lies in the source of a `C^n` partial diffeomorphism
`κ : Q → D × E` in which the map `p_Q : Q → ℂ` induced by `z ↦ z ^ m` reads `p_Q = u ^ m`, where
`u` is the first coordinate of `κ`. With holomorphic data and `n = ω`, these are holomorphic
coordinates on the complex manifold `Q`. On the source of `κ`, the coordinate `u` vanishes exactly
on the multiple fibre `p_Q⁻¹(0)`, which is therefore the slice `u = 0`, with defining coordinate
whose `m`-th power is `p_Q`. The coordinates are local inverses of the composite orbit map
`D × E → X → Q`. -/
theorem exists_partialDiffeomorph_torusFamilyAffineQuotientLift_eq_pow
    (q : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    ∃ κ : PartialDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
        (orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
        (rootsOfUnityBall m r × E) n,
      q ∈ κ.source ∧ ∀ x ∈ κ.source,
        torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
          (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m)
          (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) x = ((κ x).1 : ℂ) ^ m := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
  have := isManifold_torusFamily P hinj hP
  -- The composite orbit map `ψ : D × E → Q` is a surjective local diffeomorphism along which `p_Q`
  -- is `(z, v) ↦ z ^ m`; take a local inverse of `ψ` at a preimage of `q`.
  have hψ : IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (Quotient.mk (orbitRel (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) ∘ Quotient.mk _) := fun p ↦
    IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_torusFamily_mk P hinj hP p)
      (hg := isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul
        hbone hbmul hR hbc hfree _)
  have hlift (p : rootsOfUnityBall m r × E) :
      torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
        (Quotient.mk _ (Quotient.mk _ p)) = (p.1 : ℂ) ^ m := by
    rw [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk]
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective.comp Quotient.mk_surjective q
  refine ⟨(hψ p).localInverse, (hψ p).localInverse_mem_source, fun x hx ↦ ?_⟩
  rw [← hlift]
  exact congrArg _ ((hψ p).localInverse_right_inv hx).symm

end RotatedDiscChart

end TauCeti
