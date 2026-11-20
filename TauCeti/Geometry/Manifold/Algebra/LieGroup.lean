/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph
public import TauCeti.Geometry.Manifold.PullbackGroupoid

import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Lie groups covered by local diffeomorphisms

Let `π : G →* G'` be a surjective group homomorphism out of a `C^n` Lie group `G` which is a `C^n`
local diffeomorphism onto a `C^n` manifold `G'`. Then `G'` is a `C^n` Lie group. Near a pair of
points of `G'`, multiplication is the image under `π` of the product of two local inverses of `π`,
which are `C^n`; inversion on `G'` is the descent of inversion on `G`. This covers quotients of Lie
groups by discrete normal subgroups, such as tori `E ⧸ L` and circles `AddCircle p`. The same holds
when `π` is only a `C^n` submersion and `G` has a boundaryless model: multiplication and inversion
of `G'` then descend along the surjective submersions `π × π` and `π`. This covers quotients of Lie
groups by closed normal subgroups.

The charts of a Lie group can also be pulled back along a locally homeomorphic homomorphism
from a topological group, giving the source a Lie-group structure over the same model, or
transported along a `C^n` diffeomorphism of model spaces via `ChartedSpace.comp` (in particular,
re-modelling any finite-dimensional Lie group over `ℝ` or `ℂ` on `EuclideanSpace 𝕜 (Fin d)`).

This file also proves that the integer power maps of a `C^n` Lie group are `C^n`, and packages
inversion as a `C^n` diffeomorphism.

## Main results

* `IsLocalDiffeomorph.lieGroup`, `IsLocalDiffeomorph.lieAddGroup`: the image of a Lie group under
  a surjective homomorphism which is a local diffeomorphism is a Lie group.
* `Manifold.IsSubmersion.lieGroup`, `Manifold.IsSubmersion.lieAddGroup`: the same for a surjective
  homomorphism which is a submersion, out of a Lie group with boundaryless model.
* `IsLocalHomeomorph.lieGroup_chartedSpaceComap`,
  `IsLocalHomeomorph.lieAddGroup_chartedSpaceComap`: Lie-group structures for pulled-back charts.
* `ContinuousMulEquiv.lieGroup_pullbackChartedSpace` transfers the Lie-group structure
  to the charts pulled back along a continuous group isomorphism.
* `Diffeomorph.lieGroup_chartedSpaceComp`, `Diffeomorph.lieAddGroup_chartedSpaceComp`:
  transporting a Lie-group structure along a `C^n` diffeomorphism of models.
* `TauCeti.exists_chartedSpace_euclideanSpace_lieGroup`,
  `TauCeti.exists_chartedSpace_euclideanSpace_lieAddGroup`: re-modelling a finite-dimensional
  `C^n` Lie group over `ℝ` or `ℂ` on `EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))`.
* `TauCeti.contMDiff_zpow`, `TauCeti.contMDiff_zsmul`: integer powers, and integer multiples, in
  a Lie group are `C^n`.
* `TauCeti.Lie.invDiffeomorph`, `TauCeti.Lie.negDiffeomorph`: inversion, and negation, in a Lie
  group as a `C^n` diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 4.40 and Theorem 7.7.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [IsManifold I' n G'] [Group G']

/-- If a surjective group homomorphism `π : G →* G'` out of a `C^n` Lie group is a `C^n` local
diffeomorphism, then `G'` is a `C^n` Lie group. -/
@[to_additive /-- If a surjective additive group homomorphism `π : G →+ G'` out of a `C^n` additive
Lie group is a `C^n` local diffeomorphism, then `G'` is a `C^n` additive Lie group. -/]
theorem IsLocalDiffeomorph.lieGroup (π : G →* G') (hπ : IsLocalDiffeomorph I I' n π)
    (hsurj : Function.Surjective π) : LieGroup I' n G' where
  contMDiff_mul := by
    -- Near a pair of points, multiplication is the image under `π` of the product of two local
    -- inverses of `π`.
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have ha := hπ a
    have hb := hπ b
    have h₀ : ContMDiffAt (I'.prod I') I n
        (fun z : G' × G' ↦ ha.localInverse z.1 * hb.localInverse z.2) (π a, π b) :=
      (ha.contMDiffAt_localInverse.comp_of_eq contMDiffAt_fst rfl).mul
        (hb.contMDiffAt_localInverse.comp_of_eq contMDiffAt_snd rfl)
    refine (hπ.contMDiff.contMDiffAt.comp _ h₀).congr_of_eventuallyEq ?_
    filter_upwards [ha.localInverse_eventuallyEq_right.prodMk_nhds
      hb.localInverse_eventuallyEq_right] with z hz
    simp only [Function.comp_apply, id, map_mul] at hz ⊢
    rw [hz.1, hz.2]
  contMDiff_inv := by
    -- Inversion is the descent of inversion on `G`.
    have h : (fun x : G' ↦ x⁻¹) ∘ π = π ∘ fun x : G ↦ x⁻¹ := funext fun x ↦ (map_inv π x).symm
    rw [← hπ.contMDiff_comp_iff hsurj le_rfl, h]
    exact hπ.contMDiff.comp (contMDiff_inv I n)

/-- If a surjective group homomorphism `π : G →* G'` out of a `C^n` Lie group with boundaryless
model is a `C^n` submersion, then `G'` is a `C^n` Lie group. Multiplication and inversion of `G'`
descend along the surjective submersions `π × π` and `π`. -/
@[to_additive /-- If a surjective additive group homomorphism `π : G →+ G'` out of a `C^n` additive
Lie group with boundaryless model is a `C^n` submersion, then `G'` is a `C^n` additive Lie
group. -/]
theorem Manifold.IsSubmersion.lieGroup [I.Boundaryless] (π : G →* G')
    (hπ : IsSubmersion I I' n π) (hsurj : Function.Surjective π) : LieGroup I' n G' where
  contMDiff_mul := by
    -- On representatives, multiplication is that of `G`.
    have h : (fun p : G' × G' ↦ p.1 * p.2) ∘ Prod.map π π = π ∘ fun p : G × G ↦ p.1 * p.2 :=
      funext fun p ↦ (map_mul π p.1 p.2).symm
    rw [← (hπ.prodMap hπ).contMDiff_comp_iff (hsurj.prodMap hsurj) le_rfl, h]
    exact hπ.contMDiff.comp (contMDiff_mul I n)
  contMDiff_inv := by
    -- On representatives, inversion is that of `G`.
    have h : (fun x : G' ↦ x⁻¹) ∘ π = π ∘ fun x : G ↦ x⁻¹ := funext fun x ↦ (map_inv π x).symm
    rw [← hπ.contMDiff_comp_iff hsurj le_rfl, h]
    exact hπ.contMDiff.comp (contMDiff_inv I n)

section Comap

variable {A B : Type*} [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
  [TopologicalSpace B] [Group B] [ChartedSpace H B] [LieGroup I n B]
  {p : A → B}

/-- Charts pulled back through a locally homeomorphic homomorphism from a topological group
form a Lie-group structure over the target's model. -/
@[to_additive /-- Charts pulled back through a locally homeomorphic additive homomorphism from a
topological additive group form an additive Lie-group structure over the target's model. -/]
theorem IsLocalHomeomorph.lieGroup_chartedSpaceComap (hp : IsLocalHomeomorph p)
    (hmul : ∀ x y, p (x * y) = p x * p y) :
    let _ : ChartedSpace H A := hp.chartedSpaceComap
    LieGroup I n A := by
  let _ : ChartedSpace H A := hp.chartedSpaceComap
  let _ : IsManifold I n A := hp.isManifold_chartedSpaceComap
  have hinv (x : A) : p x⁻¹ = (p x)⁻¹ := by
    simpa only [MonoidHom.mk'_apply] using map_inv (MonoidHom.mk' p hmul) x
  exact
    { contMDiff_mul := by
        apply hp.contMDiff_chartedSpaceComap_iff.mpr
        refine ⟨continuous_mul, ?_⟩
        simpa only [Function.comp_def, hmul, Pi.mul_def] using
          ((hp.contMDiff_chartedSpaceComap (I := I) (n := n)).comp contMDiff_fst).mul
            ((hp.contMDiff_chartedSpaceComap (I := I) (n := n)).comp contMDiff_snd)
      contMDiff_inv := by
        apply hp.contMDiff_chartedSpaceComap_iff.mpr
        refine ⟨continuous_inv, ?_⟩
        simpa only [Function.comp_def, hinv] using
          (hp.contMDiff_chartedSpaceComap (I := I) (n := n)).inv }

end Comap

section Pullback

variable {A B : Type*} [TopologicalSpace A] [Group A]
  [TopologicalSpace B] [Group B] [cB : ChartedSpace H B] [lieB : LieGroup I n B]

/-- Pulling back the charts of a Lie group along a continuous multiplicative equivalence
makes the source a Lie group over the same model. -/
theorem ContinuousMulEquiv.lieGroup_pullbackChartedSpace (e : A ≃ₜ* B) :
    let _ := e.toHomeomorph.pullbackChartedSpace (H := H)
    LieGroup I n A := by
  let _ := e.toHomeomorph.pullbackChartedSpace (H := H)
  let _ := e.toHomeomorph.pullback_isManifold I n
  let φ := e.toHomeomorph.pullbackDiffeomorph I n
  have hφ : (φ.symm : B → A) = e.symm.toMulEquiv.toMonoidHom := by
    rw [Homeomorph.coe_pullbackDiffeomorph_symm]
    -- Both the homeomorphism and monoid-hom coercions retain the inverse function of `e`.
    rfl
  exact IsLocalDiffeomorph.lieGroup e.symm.toMulEquiv.toMonoidHom
    (hφ ▸ φ.symm.isLocalDiffeomorph) e.symm.surjective

end Pullback

section ModelTransport

/-- Changing the model space of a `C^n` Lie group along a `C^n` diffeomorphism of models
`Φ : H ≃ₘ^n⟮I, I'⟯ H'` makes `G` a `C^n` Lie group over `I'` for the composite charts
`ChartedSpace.comp H' H G`. -/
@[to_additive /-- Changing the model space of a `C^n` additive Lie group along a `C^n`
diffeomorphism of models `Φ : H ≃ₘ^n⟮I, I'⟯ H'` makes `G` a `C^n` additive Lie group over `I'`
for the composite charts `ChartedSpace.comp H' H G`. -/]
theorem Diffeomorph.lieGroup_chartedSpaceComp (Φ : H ≃ₘ^n⟮I, I'⟯ H') (G : Type*)
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] :
    letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H G
    LieGroup I' n G := by
  let _ := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let _ := ChartedSpace.comp H' H G
  let _ : IsManifold I' n G := Φ.isManifold_chartedSpaceComp G
  have hid : ContMDiff I' I n (id : G → G) :=
    (Φ.contMDiff_chartedSpaceComp_iff (I'' := I') (f := (id : G → G))).mp (contMDiff_id (I := I'))
  exact
    { contMDiff_mul :=
        (Φ.contMDiff_chartedSpaceComp_iff (I'' := I'.prod I')
          (f := fun p : G × G ↦ p.1 * p.2)).mpr
          ((hid.comp contMDiff_fst).mul (hid.comp contMDiff_snd))
      contMDiff_inv :=
        (Φ.contMDiff_chartedSpaceComp_iff (I'' := I') (f := fun g : G ↦ g⁻¹)).mpr
          ((contMDiff_inv I n).comp hid) }

/-- Every `C^n` Lie group modelled on a finite-dimensional normed space `E` over `𝕜` (`ℝ` or `ℂ`)
carries a `C^n` Lie-group structure (for the same topology) modelled on
`EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))`. -/
@[to_additive /-- Every `C^n` additive Lie group modelled on a finite-dimensional normed space `E`
over `𝕜` (`ℝ` or `ℂ`) carries a `C^n` additive Lie-group structure (for the same topology)
modelled on `EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))`. -/]
theorem TauCeti.exists_chartedSpace_euclideanSpace_lieGroup
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (G : Type*) [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(𝕜, E) n G] :
    ∃ atlas : ChartedSpace (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) G,
      letI := atlas
      LieGroup 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) n G := by
  let ψLin : E ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)) :=
    (Module.finBasis 𝕜 E).equivFun.trans
      (EuclideanSpace.equiv (Fin (Module.finrank 𝕜 E)) 𝕜).symm.toLinearEquiv
  let Φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) E
      (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) n :=
    { toEquiv := ψLin.toContinuousLinearEquiv.toEquiv
      contMDiff_toFun := ψLin.toContinuousLinearEquiv.contDiff.contMDiff
      contMDiff_invFun := ψLin.toContinuousLinearEquiv.symm.contDiff.contMDiff }
  have hlie := Φ.lieGroup_chartedSpaceComp G
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) E :=
    Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  exact ⟨ChartedSpace.comp (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))) E G, hlie⟩

end ModelTransport

namespace TauCeti

/-- In a `C^n` Lie group, every integer power map is `C^n`. -/
@[to_additive /-- In a `C^n` additive Lie group, multiplication by every integer is `C^n`. -/]
theorem contMDiff_zpow : ∀ k : ℤ, ContMDiff I I n fun a : G ↦ a ^ k
  | (k : ℕ) => by simpa using contMDiff_pow k
  | .negSucc k => by simpa using (contMDiff_pow (k + 1)).inv

end TauCeti

namespace TauCeti.Lie

/-- Inversion in a `C^n` Lie group as a `C^n` diffeomorphism; it is its own inverse. -/
@[to_additive
  /-- Negation in a `C^n` additive Lie group as a `C^n` diffeomorphism; it is its own inverse. -/]
def invDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (G : Type*)
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] : G ≃ₘ^n⟮I, I⟯ G where
  toEquiv := Equiv.inv G
  contMDiff_toFun := contMDiff_inv I n
  contMDiff_invFun := contMDiff_inv I n

@[to_additive (attr := simp)]
theorem invDiffeomorph_apply (g : G) : invDiffeomorph I n G g = g⁻¹ :=
  (rfl)

@[to_additive (attr := simp)]
theorem invDiffeomorph_symm : (invDiffeomorph I n G).symm = invDiffeomorph I n G :=
  (rfl)

end TauCeti.Lie
