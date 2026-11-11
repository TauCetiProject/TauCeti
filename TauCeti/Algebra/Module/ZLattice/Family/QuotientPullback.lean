/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.AffineQuotient
public import TauCeti.Geometry.Manifold.Quotient.Pullback

/-!
# Recovering a torus family through a covering of the base

Let `X = (Y × E)/Λ` be a varying period quotient, with an affine action of `Γ` lifting
an action on `Y`, and let `β : Y → Z` be a quotient covering by `Γ`. The canonical map
`x ↦ (p x, [x])` identifies `X` with the literal pullback of `X/Γ → Z` along `β`.
The inverse takes an orbit representative and translates it to the specified base point.

This is the covering comparison for cyclic quotients over a punctured disc. It allows
nontrivial linear monodromy and does not identify the quotient downstairs with a family
extending across the puncture. The lattice continues to vary with the base point.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*,
  second edition, Chapter V, section on logarithmic transformations.
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti

section Topology

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  (P : Y → Λ →ₗ[ℤ] E) {Γ : Type*} [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : ∀ g, Continuous (b g))
  {Z : Type*} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)

/-- The upstairs torus family is the pullback of its affine quotient through the quotient
covering of the base, via `x ↦ (p x, [x])`. The target has the product subspace topology. -/
noncomputable def torusFamilyAffineQuotientPullbackHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ₜ
      β.Pullback (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        β (fun g _ ↦ hβ.map_smul g)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hR hbc
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientPullbackHomeomorph β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbone hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul hβ.continuous)

/-- The covering comparison preserves the base point and records the affine orbit. -/
@[simp] theorem torusFamilyAffineQuotientPullbackHomeomorph_val
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbone hbmul
      hcont hR hbc β hβ x).1 = (torusFamilyProjection P x, Quotient.mk _ x) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    hcont hR hbc
  simp only [torusFamilyAffineQuotientPullbackHomeomorph,
    MulActionHom.orbitRelQuotientPullbackHomeomorph_apply,
    MulActionHom.orbitRelQuotientPullback_val]
  rfl

/-- The inverse covering comparison sends `(g • y, [[y, v]])` to `g • [y, v]`.
This formula allows arbitrary linear and translation parts of the affine action. -/
@[simp] theorem torusFamilyAffineQuotientPullbackHomeomorph_symm_mk
    (g : Γ) (y : Y) (v : E) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbone hbmul
      hcont hR hbc β hβ).symm
        ⟨(g • y, Quotient.mk _ (Quotient.mk _ (y, v))), by
          simpa only [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk] using
            hβ.map_smul g (e := y)⟩ =
      g • (Quotient.mk _ (y, v) : AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  apply (torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbone hbmul
    hcont hR hbc β hβ).injective
  apply Subtype.ext
  simp only [Homeomorph.apply_symm_apply, torusFamilyAffineQuotientPullbackHomeomorph_val]
  exact Prod.ext (by simp [hb]) MulAction.orbitRel.Quotient.quotient_smul_eq.symm

end Topology

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
  {Γ : Type*} [Group Γ] [MulAction Γ Y] [ProperlyDiscontinuousSMul Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, ContMDiff (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) n fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff I (I.prod 𝓘(𝕜, E)) n (b g))
  {Z : Type*} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)

/-- Recovering a `C^n` varying torus family from its affine quotient through a covering
of the base is a `C^n` diffeomorphism. For holomorphic input it is biholomorphic.
The literal pullback receives its atlas from the installed quotient atlas through the
second projection; no manifold structure on that pullback is assumed. -/
noncomputable def torusFamilyAffineQuotientPullbackDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := hβ.isCancelSMul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous)
      (isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul)
    letI := (hβ.isLocalHomeomorph.pullback_snd
      (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (hf := fun g _ ↦ hβ.map_smul g) hβ.continuous)).chartedSpaceComap (H := ModelProd H E)
    Diffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E))
      (AddAction.orbitRel.Quotient Λ (Y × E))
      (β.Pullback (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        β (fun g _ ↦ hβ.map_smul g))) n := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := hβ.isCancelSMul
  have hfree := isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
    hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
    (fun g ↦ (hbc g).continuous) hfree
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
  let p : AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y :=
    ⟨torusFamilyProjection P, fun g x ↦ by simp⟩
  exact p.orbitRelQuotientPullbackDiffeomorph β _
    (torusFamilyAffineQuotientLift_mk P R ρ hequiv b hb hone hmul hbone hbmul β _)
    (continuous_torusFamilyProjection P) hβ
    (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul hβ.continuous)
    (isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul hbone
      hbmul hR hbc hfree)

/-- The differentiable covering comparison has the canonical homeomorphism as its underlying
map, so its inverse and both projection formulas agree with the topological comparison. -/
@[simp] theorem torusFamilyAffineQuotientPullbackDiffeomorph_toHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := hβ.isCancelSMul
    letI := torusFamilyAffineQuotientChartedSpace (H := H) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous)
      (isCancelSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul)
    letI := (hβ.isLocalHomeomorph.pullback_snd
      (continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (hf := fun g _ ↦ hβ.map_smul g) hβ.continuous)).chartedSpaceComap (H := ModelProd H E)
    (torusFamilyAffineQuotientPullbackDiffeomorph P hinj hP R ρ hequiv b hb hone hmul hbone hbmul
      hR hbc β hβ).toHomeomorph =
      torusFamilyAffineQuotientPullbackHomeomorph P R ρ hequiv b hb hone hmul hbone hbmul
        (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
        β hβ := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  have := continuousConstSMul_torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
  simp only [torusFamilyAffineQuotientPullbackDiffeomorph,
    MulActionHom.orbitRelQuotientPullbackDiffeomorph_toHomeomorph,
    torusFamilyAffineQuotientPullbackHomeomorph]

end Regularity

end TauCeti
