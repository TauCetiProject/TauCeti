/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Moment maps of Lie group actions and their equivariance defect

Let a Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G` act smoothly on the left on a
manifold `M` carrying a two-form `σ`, and let `ξ ↦ ξ_M` be the infinitesimal action by fundamental
vector fields (`TauCeti.InfinitesimalAction.fundamental`). A **group-level moment map** is a moment
map `μ : M → 𝔤*` of this infinitesimal action, `d⟨μ, ξ⟩ = ι_{ξ_M} σ`, which is moreover
equivariant for the coadjoint action `Ad*_g ν = ν ∘ Ad_{g⁻¹}`:

`μ (g • x) = Ad*_g (μ x)`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`).

The failure of an arbitrary map `μ : M → 𝔤*` to be equivariant is measured by its **defect**
`θ(g, x) = μ (g • x) - Ad*_g (μ x)` (`TauCeti.momentDefect`). It always satisfies the cocycle
identity

`θ(g h, x) = θ(g, h • x) + Ad*_g θ(h, x)`

(`TauCeti.momentDefect_mul`). When `μ` is a moment map, `g` acts by a symplectomorphism
(`g^* σ = σ`) and `M` is preconnected, `θ(g, x)` does not depend on `x`
(`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq`): the components of `x ↦ μ (g • x)` and of
`x ↦ Ad*_g (μ x)` have the same differentials, because `g` carries `(Ad_{g⁻¹} ξ)_M` to `ξ_M`.
For an action by symplectomorphisms the defect is therefore a map `θ : G → 𝔤*` with
`θ(g h) = θ(g) + Ad*_g θ(h)` (`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_mul_eq`), and `μ`
is equivariant for the affine action `ν ↦ Ad*_g ν + θ(g)`
(`TauCeti.SmoothTwoForm.IsMomentMap.apply_smul_eq_add_momentDefect`).

The derivative of the defect at the identity is the Lie algebra cocycle
`c(ξ, η) = σ(ξ_M, η_M) - μ_{⁅ξ, η⁆}` of `μ` (`TauCeti.SmoothTwoForm.momentCocycle`):
`(dθ_1 η)(ξ) = c(ξ, η)` (`TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_momentDefect_one`). Combined
with the cocycle identity, this shows that for an action by symplectomorphisms of a preconnected
manifold, infinitesimal equivariance (vanishing of `c`) makes the defect constant on each connected
component of `G` (`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq_of_mem_connectedComponent`), so
zero on the identity component. For a preconnected group it therefore implies coadjoint equivariance
(`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`). A
disconnected group needs in addition a component condition: by
`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_momentCocycle_eq_zero_and_apply_smul`
equivariance holds exactly when the cocycle vanishes and the defect vanishes at one element of each
connected component.

The criteria for equivariance do not need `M` to be connected, provided the cocycle vanishes at
every point, although `θ(g, x)` is then only locally constant in `x`. For an element `g` acting by
a symplectomorphism, the defect `θ(g, ·)` always has vanishing differential
(`TauCeti.SmoothTwoForm.IsMomentMap.mfderiv_momentDefect_apply_eq_zero`). Differentiating the
cocycle identity `θ(g k, x) = θ(g, k • x) + Ad*_g θ(k, x)` in `k` at `k = 1` then shows that
`θ(·, x)` is constant on each connected component of `G` as soon as the cocycle vanishes at `x`
(`SmoothTwoForm.IsMomentMap.momentDefect_eq_of_momentCocycle_eq_zero_of_mem_connectedComponent`).
So for a preconnected group acting by symplectomorphisms of any manifold, a moment map is
coadjoint-equivariant exactly when its cocycle vanishes at every point
(`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero`), and
a disconnected group needs in addition equivariance of one element of each connected component
(`IsMomentMap.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero_and_apply_smul`).

Shifting `μ` by a constant `ν ∈ 𝔤*` changes the defect by the coboundary `ν - Ad*_g ν`
(`TauCeti.momentDefect_add_const`). Consequently, on a preconnected manifold the group-level moment
maps of an action are exactly the shifts of any one of them by coadjoint-invariant constants
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add`).

Where the form is nondegenerate, the differential `dμ_x` of a moment map is surjective exactly when
the isotropy algebra `𝔤_x` vanishes
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff`). For the fundamental vector
fields of a group action, `𝔤_x` is the Lie algebra of the stabilizer `G_x`, so `dμ_x` is
surjective exactly when `G_x` is discrete
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff_discreteTopology_stabilizer`). In
particular every point with trivial stabilizer is a regular point of `μ`: for a symplectic form and
a free action, every value of `μ` is a regular value.

For a group-level moment map the differential is itself equivariant,
`dμ_{g • x} ∘ d(g •)_x = Ad*_g ∘ dμ_x`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_smul_mfderiv`), so the regular points
of `μ` form a `G`-invariant set. Hence if `c` is a regular value, `μ` is a submersion at every
point of `μ⁻¹(G · c)`, the preimage of the coadjoint orbit of `c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_of_apply_eq`).

The derivative of an invariant function vanishes on every fundamental vector field, so a moment map
is conserved along the integral curves of a Hamiltonian vector field of an invariant function
(`TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant`), and for a
nondegenerate form every component of the moment map Poisson-commutes with the invariant function
(`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_zero_of_smul_invariant`). This is
**Noether's theorem** for Hamiltonian systems.

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap σ μ`: `μ` is a coadjoint-equivariant moment map
  of the action of `G` on `(M, σ)`.
* `TauCeti.momentDefect μ g x`: the defect `μ (g • x) - Ad*_g (μ x)`.

## Main results

* `TauCeti.momentDefect_mul`: the pointwise cocycle identity of the defect.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq`: for a moment map and an element acting
  symplectically on a preconnected manifold, the defect is independent of the point.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_mul_eq`: for a moment map and `g` acting by a
  symplectomorphism of a preconnected manifold, `θ(g k, x) = θ(g, x) + Ad*_g θ(k, x)`; for an
  action by symplectomorphisms the defect is thus a `1`-cocycle of `G` with values in the
  coadjoint representation.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff`: for an action by
  symplectomorphisms on a preconnected manifold, equivariance can be tested at a single point.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add`:
  uniqueness of group-level moment maps up to coadjoint-invariant constants.
* `TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant`: **Noether's
  theorem**, a moment map is conserved along the integral curves of a Hamiltonian vector field of
  an invariant function.
* `TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_zero_of_smul_invariant`: **Noether's
  theorem**, Poisson form: for a nondegenerate form, every component of a moment map
  Poisson-commutes with an invariant function.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_momentDefect_one`: the derivative of the defect at
  the identity is the moment cocycle.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentCocycle_eq_zero_of_eventually_apply_smul`: a moment map
  that is equivariant under all elements near the identity has vanishing cocycle.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq_of_mem_connectedComponent`,
  `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq_zero_of_mem_connectedComponent_one`: for an
  action by symplectomorphisms of a preconnected manifold, a moment map whose cocycle vanishes at
  one point has defect constant on each connected component of `G`, and zero on the identity
  component.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`: for a
  preconnected group acting by symplectomorphisms of a preconnected manifold, a moment map whose
  cocycle vanishes at one point is coadjoint-equivariant.
* `TauCeti.SmoothTwoForm.IsMomentMap.mfderiv_momentDefect_apply_eq_zero`: for an element acting
  symplectically, the defect of a moment map has vanishing differential in the point.
* `SmoothTwoForm.IsMomentMap.momentDefect_eq_of_momentCocycle_eq_zero_of_mem_connectedComponent`:
  on any manifold, if the cocycle vanishes at `x` then `θ(·, x)` is constant on each connected
  component of `G`.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero`: for
  a preconnected group acting by symplectomorphisms of any manifold, a moment map is
  coadjoint-equivariant exactly when its cocycle vanishes at every point.
* For a possibly disconnected group, equivariance is the vanishing of the cocycle together with
  equivariance at one element of each connected component:
`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_momentCocycle_eq_zero_and_apply_smul`,
  and on any manifold
`SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero_and_apply_smul`.
* `TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff_discreteTopology_stabilizer`: at a
  point where the form is nondegenerate, `dμ_x` is surjective exactly when the stabilizer of `x` is
  discrete; `TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_of_stabilizer_eq_bot` is the
  case of a trivial stabilizer.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`: conversely, the cocycle of
  a group-level moment map vanishes at every point.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_smul_iff`: `dμ_{g • x}` is
  surjective exactly when `dμ_x` is, and
  `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_of_apply_eq`: a group-level
  moment map is a submersion over the coadjoint orbit of a regular value.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §§11.4 and 12.3 (equivariance of momentum maps and the nonequivariance cocycle).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 5.2.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G] {M : Type*} [MulAction G M] {μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)}

/-- The **defect** `θ(g, x) = μ (g • x) - Ad*_g (μ x)` of a map `μ : M → 𝔤*` from equivariance for
the coadjoint action. It vanishes identically exactly when `μ` is coadjoint-equivariant. -/
def momentDefect (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    Module.Dual 𝕜 (GroupLieAlgebra I G) :=
  μ (g • x) - Lie.coadjointRepresentation 𝕜 I G g (μ x)

theorem momentDefect_def (g : G) (x : M) :
    momentDefect μ g x = μ (g • x) - Lie.coadjointRepresentation 𝕜 I G g (μ x) :=
  (rfl)

/-- The defect of the identity element vanishes. -/
@[simp]
theorem momentDefect_one (x : M) : momentDefect μ 1 x = 0 := by
  simp [momentDefect_def]

/-- The defect vanishes at `(g, x)` exactly when `μ (g • x) = Ad*_g (μ x)`. -/
theorem momentDefect_eq_zero_iff {g : G} {x : M} :
    momentDefect μ g x = 0 ↔ μ (g • x) = Lie.coadjointRepresentation 𝕜 I G g (μ x) :=
  sub_eq_zero

/-- **The cocycle identity of the defect**: `θ(g h, x) = θ(g, h • x) + Ad*_g θ(h, x)`. -/
theorem momentDefect_mul (g h : G) (x : M) :
    momentDefect μ (g * h) x =
      momentDefect μ g (h • x) + Lie.coadjointRepresentation 𝕜 I G g (momentDefect μ h x) := by
  simp only [momentDefect_def, map_sub, map_mul, mul_apply_eq_comp, mul_smul]
  abel

/-- Shifting `μ` by a constant `ν ∈ 𝔤*` changes its defect by the coboundary `ν - Ad*_g ν`. -/
theorem momentDefect_add_const (ν : Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    momentDefect (fun y ↦ μ y + ν) g x =
      momentDefect μ g x + (ν - Lie.coadjointRepresentation 𝕜 I G g ν) := by
  simp only [momentDefect_def, map_add]
  abel

/-- Negating `μ` negates its defect. -/
@[simp]
theorem momentDefect_neg (g : G) (x : M) :
    momentDefect (fun y ↦ -μ y) g x = -momentDefect μ g x := by
  simp only [momentDefect_def, map_neg]
  abel

end Defect

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ μ' : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The tangent adjoint maps only need a `C¹` Lie group. -/
local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

section Complete

variable [CompleteSpace E] [CompleteSpace E']

/-- **Noether's theorem for Hamiltonian systems.** Let `μ` be a moment map of the action by
fundamental vector fields and `X` a Hamiltonian vector field of a `G`-invariant function `f`.
Then `μ` is constant along every integral curve of `X` on a preconnected set of times along which
`f` is differentiable. -/
theorem IsMomentMap.apply_eq_of_isMIntegralCurveOn_of_smul_invariant
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {f : M → ℝ}
    (hfG : ∀ (g : G) x, f (g • x) = f x) {X : (x : M) → TangentSpace I' x}
    (hX : σ.IsHamiltonianVectorField f X) {γ : ℝ → M} {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ X s) (hf : ∀ t ∈ s, MDifferentiableAt I' 𝓘(ℝ) f (γ t))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) : μ (γ t) = μ (γ t₀) :=
  h.apply_eq_of_isMIntegralCurveOn hX hs hγ (fun u hu ξ ↦ by
    rw [InfinitesimalAction.fundamental_apply]
    exact mvfderiv_fundamentalVectorField_eq_zero_of_smul_invariant (hf u hu)
      ((ContMDiffSMul.contMDiff_smul_const (n := ∞) (γ u)).mdifferentiableAt (by simp))
      (fun g ↦ hfG g (γ u)) ξ) ht₀ ht

/-- **Noether's theorem for Hamiltonian systems, Poisson form.** For a nondegenerate form on a
finite-dimensional manifold, every component `μ_ξ` of a moment map of the action by fundamental
vector fields Poisson-commutes with a `G`-invariant function `f`: `{μ_ξ, f} = 0`. -/
theorem IsMomentMap.poissonBracket_eq_zero_of_smul_invariant [FiniteDimensional ℝ E']
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    {f : M → ℝ} (hfG : ∀ (g : G) x, f (g • x) = f x) (ξ : GroupLieAlgebra I G) :
    σ.poissonBracket (fun x ↦ μ x ξ) f = 0 := by
  refine (h.poissonBracket_eq_zero_iff hσ f ξ).2 fun x ↦ ?_
  rw [InfinitesimalAction.fundamental_apply]
  by_cases hf : MDifferentiableAt I' 𝓘(ℝ) f x
  · exact mvfderiv_fundamentalVectorField_eq_zero_of_smul_invariant hf
      ((ContMDiffSMul.contMDiff_smul_const (n := ∞) x).mdifferentiableAt (by simp))
      (fun g ↦ hfG g x) ξ
  · -- Where `f` is not differentiable its derivative is zero by convention.
    simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf]

variable (σ) in
/-- `μ : M → 𝔤*` is a **group-level moment map** of the smooth action of `G` on `(M, σ)` when it
is a moment map of the infinitesimal action by fundamental vector fields,
`d⟨μ, ξ⟩ = ι_{ξ_M} σ`, and it is equivariant for the coadjoint action:
`μ (g • x) = Ad*_g (μ x)`. -/
structure IsEquivariantMomentMap (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : Prop
    extends σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ where
  /-- A group-level moment map is coadjoint-equivariant. -/
  apply_smul : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x)

/-- A group-level moment map is a moment map whose defect vanishes identically. -/
theorem isEquivariantMomentMap_iff_momentDefect_eq_zero :
    σ.IsEquivariantMomentMap μ ↔
      σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ ∧
        ∀ (g : G) (x : M), momentDefect μ g x = 0 := by
  simp only [momentDefect_eq_zero_iff]
  exact ⟨fun h ↦ ⟨h.toIsMomentMap, h.apply_smul⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- **Groups with zero Lie algebra.** If the Lie algebra `𝔤` of `G` is zero, as for a discrete
group, then `𝔤* = 0` and every map `μ : M → 𝔤*` is a group-level moment map. -/
theorem isEquivariantMomentMap_of_subsingleton [Subsingleton (GroupLieAlgebra I G)]
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : σ.IsEquivariantMomentMap μ where
  contMDiff ξ := by
    simpa only [Subsingleton.elim ξ 0, map_zero] using contMDiff_const
  isHamiltonianVectorField ξ := by
    simpa only [Subsingleton.elim ξ 0, map_zero] using σ.isHamiltonianVectorField_const 0
  apply_smul _ _ := Subsingleton.elim _ _

namespace IsMomentMap

/-- For a moment map `μ` and an element `g` acting by a symplectomorphism, the map
`x ↦ μ (g • x)` is a moment map of the action `ξ ↦ (Ad_{g⁻¹} ξ)_M`, the restriction of the
fundamental action along `Ad_{g⁻¹}`. -/
private theorem isMomentMap_comp_smul
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ) :
    σ.IsMomentMap ((InfinitesimalAction.fundamental I G I' M).comp
      (Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G))
      (fun x ↦ μ (g • x)) := by
  have hrel : ∀ (ξ : GroupLieAlgebra I G) (x : M),
      mfderiv I' I' (fun y : M ↦ g • y) x
          ((InfinitesimalAction.fundamental I G I' M).comp
            (Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G) ξ x) =
        InfinitesimalAction.fundamental I G I' M ξ (g • x) := fun ξ x ↦ by
    rw [InfinitesimalAction.comp_apply, InfinitesimalAction.fundamental_apply,
      InfinitesimalAction.fundamental_apply, mfderiv_smul_fundamentalVectorField]
    congr 1
    rw [← Lie.tangentAd_apply, LieEquiv.coe_toLieHom, Lie.tangentAd_inv,
      LieEquiv.apply_symm_apply]
  simpa only [hg, Function.comp_def] using
    h.mpullback (ContMDiffSMul.contMDiff_const_smul (I := I) g) hrel

omit [TopologicalSpace M] in
/-- The components of the defect at `g` are `x ↦ μ (g • x) ξ - μ x (Ad_{g⁻¹} ξ)`. -/
private theorem momentDefect_apply_eq_sub (g : G) (ξ : GroupLieAlgebra I G) :
    (fun x ↦ momentDefect μ g x ξ) = fun x ↦ μ (g • x) ξ - (μ x).comp
      ((Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G) :
        GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra I G) ξ := by
  funext x
  rw [momentDefect_def, LinearMap.sub_apply, Lie.coadjointRepresentation_apply,
    LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, Lie.tangentAd_apply]

/-- For a moment map `μ` and an element `g` acting by a symplectomorphism, each component
`x ↦ θ(g, x)(ξ)` of the defect is smooth. -/
private theorem contMDiff_momentDefect_apply_left
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ) (ξ : GroupLieAlgebra I G) :
    ContMDiff I' 𝓘(ℝ) ∞ fun x ↦ momentDefect μ g x ξ := by
  rw [momentDefect_apply_eq_sub]
  exact ((isMomentMap_comp_smul h hg).contMDiff ξ).sub
    ((h.comp (Lie.tangentAd (I := I) g⁻¹ :
      GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G)).contMDiff ξ)

/-- **The defect of a moment map has vanishing differential in the point.** If `μ` is a moment map
of the action by fundamental vector fields and `g` acts by a symplectomorphism, every component
`x ↦ θ(g, x)(ξ)` of the defect has vanishing differential: `x ↦ μ (g • x)` and
`x ↦ Ad*_g (μ x)` are moment maps of the same action `ξ ↦ (Ad_{g⁻¹} ξ)_M`. No connectedness of the
manifold is needed. -/
theorem mfderiv_momentDefect_apply_eq_zero
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ) (ξ : GroupLieAlgebra I G) (x : M) :
    mfderiv I' 𝓘(ℝ) (fun y ↦ momentDefect μ g y ξ) x = 0 := by
  rw [momentDefect_apply_eq_sub]
  exact (h.comp (Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G))
    |>.mfderiv_sub_eq_zero (isMomentMap_comp_smul h hg) ξ x

/-- **The defect of a moment map is independent of the point.** If `μ` is a moment map of the
action by fundamental vector fields and `g` acts by a symplectomorphism of a preconnected manifold,
then `μ (g • x) - Ad*_g (μ x)` does not depend on `x`. -/
theorem momentDefect_eq [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ)
    (x y : M) : momentDefect μ g x = momentDefect μ g y :=
  LinearMap.ext fun ξ ↦ ((contMDiff_momentDefect_apply_left h hg ξ).mdifferentiable (by simp))
    |>.apply_eq_of_mfderiv_eq_zero (h.mfderiv_momentDefect_apply_eq_zero hg ξ) x y

/-- **Equivariance for the affine coadjoint action.** If `g` acts by a symplectomorphism of a
preconnected manifold, a moment map satisfies `μ (g • x) = Ad*_g (μ x) + θ(g)`, where the defect
`θ(g)` may be evaluated at any point `y`. -/
theorem apply_smul_eq_add_momentDefect [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ)
    (x y : M) : μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x) + momentDefect μ g y := by
  rw [← h.momentDefect_eq hg x y, momentDefect_def, add_sub_cancel]

/-- **The defect is a group cocycle.** If `g` acts by a symplectomorphism of a preconnected
manifold, the defect of a moment map satisfies `θ(g h) = θ(g) + Ad*_g θ(h)`, all evaluated at the
same point. -/
theorem momentDefect_mul_eq [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ)
    (k : G) (x : M) :
    momentDefect μ (g * k) x =
      momentDefect μ g x + Lie.coadjointRepresentation ℝ I G g (momentDefect μ k x) := by
  rw [momentDefect_mul, h.momentDefect_eq hg (k • x) x]

/-- **Equivariance can be tested at one point.** For an action by symplectomorphisms of a
preconnected manifold, a moment map is coadjoint-equivariant as soon as
`μ (g • x₀) = Ad*_g (μ x₀)` for every `g` at a single point `x₀`. -/
theorem isEquivariantMomentMap_iff [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x₀ : M) :
    σ.IsEquivariantMomentMap μ ↔
      ∀ g : G, μ (g • x₀) = Lie.coadjointRepresentation ℝ I G g (μ x₀) := by
  simp only [isEquivariantMomentMap_iff_momentDefect_eq_zero, ← momentDefect_eq_zero_iff]
  exact ⟨fun h' g ↦ h'.2 g x₀,
    fun h' ↦ ⟨h, fun g x ↦ (h.momentDefect_eq (hσ g) x x₀).trans (h' g)⟩⟩

end IsMomentMap

namespace IsEquivariantMomentMap

/-- The negative of a group-level moment map for `σ` is a group-level moment map for `-σ`. -/
theorem neg (h : σ.IsEquivariantMomentMap μ) : (-σ).IsEquivariantMomentMap fun x ↦ -μ x where
  toIsMomentMap := h.toIsMomentMap.neg
  apply_smul g x := by rw [h.apply_smul, map_neg]

/-- Shifting a group-level moment map by a coadjoint-invariant constant `ν ∈ 𝔤*` gives a
group-level moment map. -/
theorem add_const (h : σ.IsEquivariantMomentMap μ) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ∀ g : G, Lie.coadjointRepresentation ℝ I G g ν = ν) :
    σ.IsEquivariantMomentMap (fun x ↦ μ x + ν) where
  toIsMomentMap := h.toIsMomentMap.add_const ν
  apply_smul g x := by rw [h.apply_smul, map_add, hν]

/-- **Equivariant shifts.** Shifting a group-level moment map on a nonempty manifold by a constant
`ν ∈ 𝔤*` gives a group-level moment map exactly when `ν` is coadjoint-invariant. -/
theorem add_const_iff [Nonempty M] (h : σ.IsEquivariantMomentMap μ)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    σ.IsEquivariantMomentMap (fun x ↦ μ x + ν) ↔
      ∀ g : G, Lie.coadjointRepresentation ℝ I G g ν = ν := by
  have hμ := (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 h).2
  simp only [isEquivariantMomentMap_iff_momentDefect_eq_zero, momentDefect_add_const, hμ,
    zero_add, sub_eq_zero, eq_comm (a := ν), forall_const,
    and_iff_right (h.toIsMomentMap.add_const ν)]

/-- **Uniqueness of group-level moment maps.** On a preconnected manifold, the group-level moment
maps of an action are exactly the shifts `x ↦ μ x + ν` of any one of them `μ` by
coadjoint-invariant constants `ν ∈ 𝔤*`. -/
theorem isEquivariantMomentMap_iff_exists_eq_add [PreconnectedSpace M]
    (h : σ.IsEquivariantMomentMap μ) :
    σ.IsEquivariantMomentMap μ' ↔ ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G),
      (∀ g : G, Lie.coadjointRepresentation ℝ I G g ν = ν) ∧ μ' = fun x ↦ μ x + ν := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨fun _ ↦ ⟨0, fun g ↦ map_zero _, funext fun x ↦ isEmptyElim x⟩, ?_⟩
    rintro ⟨ν, -, rfl⟩
    exact ⟨h.toIsMomentMap.add_const ν, fun _ x ↦ isEmptyElim x⟩
  constructor
  · intro h'
    obtain ⟨ν, rfl⟩ := (h.toIsMomentMap.isMomentMap_iff_exists_eq_add).1 h'.toIsMomentMap
    exact ⟨ν, (h.add_const_iff ν).1 h', rfl⟩
  · rintro ⟨ν, hν, rfl⟩
    exact (h.add_const_iff ν).2 hν

end IsEquivariantMomentMap

end Complete

/-! ### The infinitesimal defect -/

namespace IsMomentMap

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

section CompleteSpace

variable [CompleteSpace E']

/-- Each component `g ↦ θ(g, x)(ξ)` of the defect of a moment map is smooth. -/
private theorem contMDiff_momentDefect_apply
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (x : M)
    (ξ : GroupLieAlgebra I G) : ContMDiff I 𝓘(ℝ) ∞ fun g : G ↦ momentDefect μ g x ξ := by
  simp only [momentDefect_def, LinearMap.sub_apply]
  exact ((h.contMDiff ξ).comp (ContMDiffSMul.contMDiff_smul_const x)).sub
    (Lie.contMDiff_coadjointRepresentation_apply (μ x) ξ)

/-- **The derivative of the defect is the moment cocycle.** For a moment map `μ` of the action by
fundamental vector fields, the derivative at the identity of `g ↦ θ(g, x)(ξ)` in the direction `η`
is the cocycle `c(ξ, η) = σ(ξ_M x, η_M x) - μ(x)(⁅ξ, η⁆)` of `μ` at `x`. -/
theorem mvfderiv_momentDefect_one (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (x : M) (ξ η : GroupLieAlgebra I G) :
    mvfderiv I (fun g : G ↦ momentDefect μ g x ξ) 1 η =
      TrivialLieModule.equiv ℝ _ ℝ
        (σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x ξ η) := by
  have horbit : MDifferentiableAt I I' (fun g : G ↦ g • x) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (n := 1) x).mdifferentiableAt one_ne_zero
  -- The derivative of `g ↦ μ (g • x) ξ` is `dμ_ξ (η_M x) = σ(ξ_M x, η_M x)`.
  have h₁ : mvfderiv I (fun g : G ↦ μ (g • x) ξ) 1 η =
      SmoothBundleForm.eval₂ σ x (fundamentalVectorField I' ξ x)
        (fundamentalVectorField I' η x) := by
    rw [← InfinitesimalAction.fundamental_apply (I := I) (G := G) (M := M), h.eval₂_apply,
      fundamentalVectorField_apply]
    exact mvfderiv_comp_apply_of_eq (g := fun y : M ↦ μ y ξ) (f := fun g : G ↦ g • x) 1
      (h.mdifferentiableAt ξ x) horbit (one_smul G x) η
  have hd₁ : MDifferentiableAt I 𝓘(ℝ) (fun g : G ↦ μ (g • x) ξ) 1 :=
    (h.mdifferentiableAt ξ x).comp_of_eq (1 : G) horbit (one_smul G x)
  have hd₂ : MDifferentiableAt I 𝓘(ℝ)
      (fun g : G ↦ Lie.coadjointRepresentation ℝ I G g (μ x) ξ) 1 :=
    (Lie.contMDiff_coadjointRepresentation_apply (μ x) ξ).mdifferentiableAt (by simp)
  simp only [momentDefect_def, LinearMap.sub_apply]
  -- The derivative of `g ↦ (Ad*_g (μ x)) ξ` is `μ x ⁅ξ, η⁆`.
  rw [mvfderiv_fun_sub hd₁ hd₂, sub_apply, h₁, Lie.mvfderiv_coadjointRepresentation_apply_one,
    momentCocycle_apply, LinearEquiv.apply_symm_apply, InfinitesimalAction.fundamental_apply,
    InfinitesimalAction.fundamental_apply]

/-- **Equivariance near the identity kills the cocycle.** If a moment map `μ` of the action by
fundamental vector fields satisfies `μ (g • x) = Ad*_g (μ x)` for all `g` in a neighbourhood of the
identity, its cocycle vanishes at `x`: the cocycle is the derivative at the identity of the defect,
which vanishes near the identity. -/
theorem momentCocycle_eq_zero_of_eventually_apply_smul
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {x : M}
    (hx : ∀ᶠ g in nhds (1 : G), μ (g • x) = Lie.coadjointRepresentation ℝ I G g (μ x)) :
    σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0 := by
  refine momentCocycle_eq_zero_iff.2 fun ξ η ↦ ?_
  have hθ : (fun g : G ↦ momentDefect μ g x ξ) =ᶠ[nhds 1] fun _ ↦ 0 :=
    hx.mono fun g hg ↦ by
      dsimp only
      rw [momentDefect_eq_zero_iff.2 hg, LinearMap.zero_apply]
  have hd := h.mvfderiv_momentDefect_one x ξ η
  rw [hθ.mvfderiv_eq, mvfderiv_const, momentCocycle_apply, LinearEquiv.apply_symm_apply] at hd
  exact sub_eq_zero.1 (by simpa using hd.symm)

/-- **The defect at a point is constant on the connected components of the group.** Let `G` act by
symplectomorphisms of a manifold `M`, connected or not, and let `μ` be a moment map of the action
by fundamental vector fields whose cocycle vanishes at `x`. Then
`momentDefect μ k x = momentDefect μ g x` whenever `k` lies in the connected component of `g`. -/
theorem momentDefect_eq_of_momentCocycle_eq_zero_of_mem_connectedComponent
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {x : M}
    (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0) {g k : G}
    (hk : k ∈ connectedComponent g) : momentDefect μ k x = momentDefect μ g x := by
  ext ξ
  -- The component `g ↦ θ(g, x)(ξ)` is smooth with vanishing derivative at every `g`.
  refine (h.contMDiff_momentDefect_apply x ξ).mdifferentiable (by simp)
    |>.isLocallyConstant_of_mfderiv_eq_zero (fun g ↦ ?_)
    |>.apply_eq_of_isPreconnected isPreconnected_connectedComponent hk mem_connectedComponent
  rw [← mvfderiv_eq_zero_iff]
  refine mfderiv_eq_zero_of_mfderiv_mul_left_one_eq_zero ?_
  rw [← mvfderiv_eq_zero_iff]
  /- Near `g`, the defect is `θ(g k, x)(ξ) = θ(g, k • x)(ξ) + θ(k, x)(Ad_{g⁻¹} ξ)`. Its derivative
  in `k` at `1` vanishes: the first term because `θ(g, ·)` has vanishing differential, the second
  because the cocycle at `x` vanishes. -/
  have htrans : (fun k : G ↦ momentDefect μ (g * k) x ξ) = fun k ↦
      momentDefect μ g (k • x) ξ +
        momentDefect μ k x (Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ) := by
    funext k
    rw [momentDefect_mul, LinearMap.add_apply, Lie.coadjointRepresentation_apply]
  have horbit : MDifferentiableAt I I' (fun k : G ↦ k • x) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (n := 1) x).mdifferentiableAt one_ne_zero
  have hθ : MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ momentDefect μ g y ξ) ((1 : G) • x) :=
    (contMDiff_momentDefect_apply_left h (hσ g) ξ).mdifferentiableAt (by simp)
  have h₁ : mfderiv I 𝓘(ℝ) (fun k : G ↦ momentDefect μ g (k • x) ξ) 1 = 0 := by
    rw [← Function.comp_def (fun y ↦ momentDefect μ g y ξ), mfderiv_comp_of_eq hθ horbit rfl,
      h.mfderiv_momentDefect_apply_eq_zero (hσ g), ContinuousLinearMap.zero_comp]
  have hd₁ : MDifferentiableAt I 𝓘(ℝ) (fun k : G ↦ momentDefect μ g (k • x) ξ) 1 :=
    hθ.comp_of_eq (1 : G) horbit rfl
  ext v
  rw [htrans, mvfderiv_fun_add hd₁
      ((h.contMDiff_momentDefect_apply x _).mdifferentiableAt (by simp)),
    mvfderiv_eq_zero_iff.2 h₁, zero_add, h.mvfderiv_momentDefect_one, hc,
    ← LieModule.Cohomology.twoCochain_val_apply]
  -- The zero two-cochain, read as a bilinear map, vanishes.
  simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply, map_zero, zero_apply]

/-- **The defect is constant on the connected components of the group.** Let `G` act by
symplectomorphisms of a preconnected manifold, and let `μ` be a moment map of the action by
fundamental vector fields whose cocycle vanishes at one point. Then
`momentDefect μ k x = momentDefect μ g x` whenever `k` lies in the connected component of `g`. -/
theorem momentDefect_eq_of_mem_connectedComponent [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {x₀ : M}
    (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x₀ = 0) {g k : G}
    (hk : k ∈ connectedComponent g) (x : M) : momentDefect μ k x = momentDefect μ g x := by
  rw [h.momentDefect_eq (hσ k) x x₀, h.momentDefect_eq (hσ g) x x₀]
  exact h.momentDefect_eq_of_momentCocycle_eq_zero_of_mem_connectedComponent hσ hc hk

/-- **The identity component acts equivariantly.** Let `G` act by symplectomorphisms of a
preconnected manifold. If the cocycle of a moment map vanishes at one point, its defect vanishes on
the identity component of `G`. -/
theorem momentDefect_eq_zero_of_mem_connectedComponent_one [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {x₀ : M}
    (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x₀ = 0) {k : G}
    (hk : k ∈ connectedComponent (1 : G)) (x : M) : momentDefect μ k x = 0 := by
  rw [h.momentDefect_eq_of_mem_connectedComponent hσ hc hk, momentDefect_one]

/-- **Infinitesimal equivariance integrates over a connected group.** Let a preconnected Lie group
act by symplectomorphisms of a preconnected manifold. A moment map of the action by fundamental
vector fields whose cocycle vanishes at one point is coadjoint-equivariant. -/
theorem isEquivariantMomentMap_of_momentCocycle_eq_zero [PreconnectedSpace G]
    [PreconnectedSpace M] (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {x₀ : M}
    (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x₀ = 0) :
    σ.IsEquivariantMomentMap μ :=
  (isEquivariantMomentMap_iff_momentDefect_eq_zero.2 ⟨h, fun g ↦
    h.momentDefect_eq_zero_of_mem_connectedComponent_one hσ hc
      (by simp [PreconnectedSpace.connectedComponent_eq_univ])⟩)

end CompleteSpace

/-! ### Locally free points are regular -/

variable [T2Space M] [BoundarylessManifold I' M] [FiniteDimensional ℝ E']

/-- **Locally free points are regular points of a moment map.** At a point where the form is
nondegenerate, the differential `dμ_x` of a moment map of a smooth action is surjective exactly when
the stabilizer `G_x` is discrete, that is, when the action is locally free at `x`. -/
theorem differential_surjective_iff_discreteTopology_stabilizer
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate) :
    Function.Surjective (h.differential x) ↔ DiscreteTopology (MulAction.stabilizer G x) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  rw [h.differential_surjective_iff hσ,
    Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')]

/-- **Freeness implies regularity.** At a point with trivial stabilizer where the form is
nondegenerate, the differential `dμ_x` of a moment map of a smooth action is surjective. So for a
symplectic form and a free action, every value of `μ` is a regular value. -/
theorem differential_surjective_of_stabilizer_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate) (hx : MulAction.stabilizer G x = ⊥) :
    Function.Surjective (h.differential x) := by
  have : Subsingleton (MulAction.stabilizer G x) := by
    rw [hx]
    infer_instance
  exact (h.differential_surjective_iff_discreteTopology_stabilizer hσ).2 inferInstance

end IsMomentMap

namespace IsEquivariantMomentMap

variable [FiniteDimensional ℝ E] [CompleteSpace E'] [LieGroup I ∞ G]

/-- **A group-level moment map is infinitesimally equivariant**: its cocycle vanishes at every
point, `σ(ξ_M, η_M) = μ_{⁅ξ, η⁆}`. The defect of an equivariant moment map vanishes identically,
and the cocycle is its derivative at the identity. -/
theorem momentCocycle_eq_zero (h : σ.IsEquivariantMomentMap μ) (x : M) :
    σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0 :=
  h.toIsMomentMap.momentCocycle_eq_zero_of_eventually_apply_smul
    (Filter.Eventually.of_forall fun g ↦ h.apply_smul g x)

end IsEquivariantMomentMap

/-! ### Regular points along coadjoint orbits -/

namespace IsEquivariantMomentMap

variable [CompleteSpace E] [CompleteSpace E']

/-- **The differential of a group-level moment map is equivariant**:
`dμ_{g • x} (d(g •)_x v) = Ad*_g (dμ_x v)`. -/
theorem differential_smul_mfderiv (h : σ.IsEquivariantMomentMap μ) (g : G) (x : M)
    (v : TangentSpace I' x) :
    h.toIsMomentMap.differential (g • x) (mfderiv I' I' (fun y : M ↦ g • y) x v) =
      Lie.coadjointRepresentation ℝ I G g (h.toIsMomentMap.differential x v) := by
  ext ξ
  rw [IsMomentMap.differential_apply, Lie.coadjointRepresentation_apply,
    IsMomentMap.differential_apply, ← mvfderiv_comp_apply x
      (h.toIsMomentMap.mdifferentiableAt ξ (g • x))
      ((ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt (by simp)) v]
  -- The component `μ_ξ ∘ (g • ·)` is the component `μ_{Ad_{g⁻¹} ξ}`, by equivariance.
  congr 2
  funext y
  rw [Function.comp_apply, h.apply_smul, Lie.coadjointRepresentation_apply]

/-- **Regular points of a group-level moment map form invariant sets**: `dμ_{g • x}` is surjective
exactly when `dμ_x` is. -/
theorem differential_surjective_smul_iff (h : σ.IsEquivariantMomentMap μ) (g : G) (x : M) :
    Function.Surjective (h.toIsMomentMap.differential (g • x)) ↔
      Function.Surjective (h.toIsMomentMap.differential x) := by
  -- If `dμ_x` is surjective, so is `dμ_{g • x}`, since it hits `Ad*_g (dμ_x v)` for every `v`.
  have key : ∀ (g : G) (x : M), Function.Surjective (h.toIsMomentMap.differential x) →
      Function.Surjective (h.toIsMomentMap.differential (g • x)) := fun g x hx ν ↦ by
    obtain ⟨v, hv⟩ := hx (Lie.coadjointRepresentation ℝ I G g⁻¹ ν)
    exact ⟨_, by rw [h.differential_smul_mfderiv, hv, Representation.self_inv_apply]⟩
  refine ⟨fun hx ↦ ?_, key g x⟩
  have hy := key g⁻¹ (g • x) hx
  rwa [inv_smul_smul] at hy

/-- **A group-level moment map is a submersion over the coadjoint orbit of a regular value.** If
`dμ` is surjective at every point of the level `μ⁻¹(c)`, it is surjective at every point `x` with
`μ x = Ad*_g c`, that is, at every point of `μ⁻¹(G · c)`. -/
theorem differential_surjective_of_apply_eq (h : σ.IsEquivariantMomentMap μ)
    {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hreg : ∀ y, μ y = c → Function.Surjective (h.toIsMomentMap.differential y)) {g : G} {x : M}
    (hx : μ x = Lie.coadjointRepresentation ℝ I G g c) :
    Function.Surjective (h.toIsMomentMap.differential x) := by
  have hy : μ (g⁻¹ • x) = c := by
    rw [h.apply_smul, hx, Representation.inv_self_apply]
  have hx' := (h.differential_surjective_smul_iff g (g⁻¹ • x)).2 (hreg _ hy)
  rwa [smul_inv_smul] at hx'

end IsEquivariantMomentMap

/-! ### Disconnected groups -/

namespace IsMomentMap

variable [FiniteDimensional ℝ E] [CompleteSpace E'] [LieGroup I ∞ G]

/-- **Equivariance over a disconnected group.** Let `G` act by symplectomorphisms of a
preconnected manifold, and let `S ⊆ G` meet every connected component of `G`. A moment map of the
action by fundamental vector fields is coadjoint-equivariant exactly when its cocycle vanishes at a
point `x₀` and `μ (s • x₀) = Ad*_s (μ x₀)` for every `s ∈ S`. The vanishing of the cocycle alone
controls the defect only on the identity component of `G`
(`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq_zero_of_mem_connectedComponent_one`); the
condition on `S` handles one element of each other component. For a preconnected group, `S = {1}`
meets every component and the condition on `S` holds trivially. -/
theorem isEquivariantMomentMap_iff_momentCocycle_eq_zero_and_apply_smul [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x₀ : M) {S : Set G}
    (hS : ∀ g : G, ∃ s ∈ S, s ∈ connectedComponent g) :
    σ.IsEquivariantMomentMap μ ↔
      σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x₀ = 0 ∧
        ∀ s ∈ S, μ (s • x₀) = Lie.coadjointRepresentation ℝ I G s (μ x₀) := by
  refine ⟨fun h' ↦ ⟨h'.momentCocycle_eq_zero x₀, fun s _ ↦ h'.apply_smul s x₀⟩,
    fun ⟨hc, hS'⟩ ↦ (h.isEquivariantMomentMap_iff hσ x₀).2 fun g ↦ ?_⟩
  obtain ⟨s, hs, hsg⟩ := hS g
  rw [← momentDefect_eq_zero_iff, ← h.momentDefect_eq_of_mem_connectedComponent hσ hc hsg,
    momentDefect_eq_zero_iff]
  exact hS' s hs

/-- **Equivariance over a disconnected group, on any manifold.** Let `G` act by symplectomorphisms
of a manifold `M`, connected or not, and let `S ⊆ G` meet every connected component of `G`. A
moment map of the action by fundamental vector fields is coadjoint-equivariant exactly when its
cocycle vanishes at every point and `μ (s • x) = Ad*_s (μ x)` for every `s ∈ S` and every `x`.
On a preconnected manifold one point suffices for both conditions
(`SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff_momentCocycle_eq_zero_and_apply_smul`).
-/
theorem isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero_and_apply_smul
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {S : Set G}
    (hS : ∀ g : G, ∃ s ∈ S, s ∈ connectedComponent g) :
    σ.IsEquivariantMomentMap μ ↔
      (∀ x, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0) ∧
        ∀ s ∈ S, ∀ x, μ (s • x) = Lie.coadjointRepresentation ℝ I G s (μ x) := by
  refine ⟨fun h' ↦ ⟨h'.momentCocycle_eq_zero, fun s _ ↦ h'.apply_smul s⟩,
    fun ⟨hc, hS'⟩ ↦ isEquivariantMomentMap_iff_momentDefect_eq_zero.2 ⟨h, fun g x ↦ ?_⟩⟩
  obtain ⟨s, hs, hsg⟩ := hS g
  rw [← h.momentDefect_eq_of_momentCocycle_eq_zero_of_mem_connectedComponent hσ (hc x) hsg,
    momentDefect_eq_zero_iff]
  exact hS' s hs x

/-- **Infinitesimal equivariance integrates over a connected group, on any manifold.** Let a
preconnected Lie group act by symplectomorphisms of a manifold `M`, connected or not. A moment map
of the action by fundamental vector fields is coadjoint-equivariant exactly when its cocycle
vanishes at every point. On a preconnected manifold vanishing at one point suffices
(`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`). -/
theorem isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero [PreconnectedSpace G]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    σ.IsEquivariantMomentMap μ ↔
      ∀ x, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0 := by
  rw [h.isEquivariantMomentMap_iff_forall_momentCocycle_eq_zero_and_apply_smul hσ (S := {1})
    fun g ↦ ⟨1, rfl, by simp [PreconnectedSpace.connectedComponent_eq_univ]⟩]
  simp

end IsMomentMap

end SmoothTwoForm

end TauCeti
