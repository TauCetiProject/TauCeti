/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Coadjoint
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Lie.Adjoint.Smooth
import TauCeti.Geometry.Lie.InvariantVectorField.Basic
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
with the cocycle identity, this shows that for a preconnected group acting by symplectomorphisms of
a preconnected manifold, infinitesimal equivariance (vanishing of `c`) implies coadjoint
equivariance (`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`).

Shifting `μ` by a constant `ν ∈ 𝔤*` changes the defect by the coboundary `ν - Ad*_g ν`
(`TauCeti.momentDefect_add_const`). Consequently, on a preconnected manifold the group-level moment
maps of an action are exactly the shifts of any one of them by coadjoint-invariant constants
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap σ μ`: `μ` is a coadjoint-equivariant moment map
  of the action of `G` on `(M, σ)`.
* `TauCeti.momentDefect μ g x`: the defect `μ (g • x) - Ad*_g (μ x)`.

## Main results

* `TauCeti.momentDefect_mul`: the pointwise cocycle identity of the defect.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq`: for a moment map and an element acting
  symplectically on a preconnected manifold, the defect is independent of the point.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_mul_eq`: the defect is a `1`-cocycle of `G` with
  values in the coadjoint representation.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_iff`: for an action by
  symplectomorphisms on a preconnected manifold, equivariance can be tested at a single point.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add`:
  uniqueness of group-level moment maps up to coadjoint-invariant constants.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_momentDefect_one`: the derivative of the defect at
  the identity is the moment cocycle.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_momentCocycle_eq_zero`: over a
  connected group, infinitesimal equivariance implies coadjoint equivariance.

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
  simp only [momentDefect_def, map_sub, map_mul, Module.End.mul_apply, mul_smul]
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

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ μ' : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The tangent adjoint maps only need a `C¹` Lie group. -/
local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

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

/-- **The defect of a moment map is independent of the point.** If `μ` is a moment map of the
action by fundamental vector fields and `g` acts by a symplectomorphism of a preconnected manifold,
then `μ (g • x) - Ad*_g (μ x)` does not depend on `x`. -/
theorem momentDefect_eq [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
      σ = σ)
    (x y : M) : momentDefect μ g x = momentDefect μ g y := by
  obtain ⟨ν, hν⟩ := ((h.comp (Lie.tangentAd (I := I) g⁻¹ :
    GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G)).isMomentMap_iff_exists_eq_add).1
      (isMomentMap_comp_smul h hg)
  have hdefect (z : M) : momentDefect μ g z = ν := by
    have hz : μ (g • z) = (μ z).comp
        ((Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G) :
          GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra I G) + ν :=
      congrFun hν z
    have hc : (μ z).comp
        ((Lie.tangentAd (I := I) g⁻¹ : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G) :
          GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra I G) =
        Lie.coadjointRepresentation ℝ I G g (μ z) := by
      ext ξ
      rw [Lie.coadjointRepresentation_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
        LieEquiv.coe_toLieHom, Lie.tangentAd_apply]
    rw [momentDefect_def, hz, hc, add_sub_cancel_left]
  rw [hdefect, hdefect]

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

/-! ### The infinitesimal defect -/

namespace IsMomentMap

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

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
  -- The derivative of `g ↦ μ x (Ad_{g⁻¹} ξ)` is `μ x (ad (-η) ξ) = μ x ⁅ξ, η⁆`.
  have hT : MDifferentiableAt I 𝓘(ℝ, E)
      (fun g : G ↦ show E from Lie.tangentAd (I := I) g (ξ : GroupLieAlgebra I G)) 1 :=
    (Lie.contMDiff_tangentAd_apply_const (I := I) (G := G) (show E from ξ)).mdifferentiableAt
      (by simp)
  have hinv : MDifferentiableAt I I (fun g : G ↦ g⁻¹) 1 :=
    (contMDiff_inv I 1).mdifferentiableAt one_ne_zero
  have hAd := Lie.mvfderiv_tangentAd_apply_one (I := I) (G := G) (-η) ξ
  dsimp only at hAd
  have h₂ : mvfderiv I (fun g : G ↦ μ x (Lie.tangentAd (I := I) g⁻¹ ξ)) 1 η = μ x ⁅ξ, η⁆ := by
    let φ := LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from μ x)
    have hcomp := mvfderiv_comp_apply_of_differentiableAt (I := I) (φ := φ)
      (g := (fun g : G ↦ show E from Lie.tangentAd (I := I) g (ξ : GroupLieAlgebra I G)) ∘
        fun g : G ↦ g⁻¹) φ.differentiableAt (hT.comp_of_eq (1 : G) hinv inv_one) η
    rw [φ.fderiv, mvfderiv_comp_apply_of_eq (1 : G) hT hinv inv_one,
      GroupLieAlgebra.mfderiv_inv_one_apply, hAd] at hcomp
    rw [← lie_skew, ← neg_lie]
    exact hcomp
  have hd₁ : MDifferentiableAt I 𝓘(ℝ) (fun g : G ↦ μ (g • x) ξ) 1 :=
    (h.mdifferentiableAt ξ x).comp_of_eq (1 : G) horbit (one_smul G x)
  simp only [momentDefect_def, LinearMap.sub_apply, Lie.coadjointRepresentation_apply,
    ← Lie.tangentAd_apply]
  have hd₂ : MDifferentiableAt I 𝓘(ℝ) (fun g : G ↦ μ x (Lie.tangentAd (I := I) g⁻¹ ξ)) 1 := by
    simpa only [Lie.coadjointRepresentation_apply, ← Lie.tangentAd_apply] using
      (Lie.contMDiff_coadjointRepresentation_apply (μ x) ξ).mdifferentiableAt (by simp)
  rw [mvfderiv_fun_sub hd₁ hd₂,
    sub_apply, h₁, h₂, momentCocycle_apply, LinearEquiv.apply_symm_apply,
    InfinitesimalAction.fundamental_apply, InfinitesimalAction.fundamental_apply]

/-- **Infinitesimal equivariance integrates over a connected group.** Let a preconnected Lie group
act by symplectomorphisms of a preconnected manifold. A moment map of the action by fundamental
vector fields whose cocycle vanishes at one point is coadjoint-equivariant. -/
theorem isEquivariantMomentMap_of_momentCocycle_eq_zero [PreconnectedSpace G]
    [PreconnectedSpace M] (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) {x₀ : M}
    (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x₀ = 0) :
    σ.IsEquivariantMomentMap μ := by
  refine (h.isEquivariantMomentMap_iff hσ x₀).2 fun g₀ ↦ momentDefect_eq_zero_iff.1 ?_
  ext ξ
  have h₁ : momentDefect μ 1 x₀ ξ = 0 := by simp
  rw [LinearMap.zero_apply, ← h₁]
  -- The component `g ↦ θ(g, x₀)(ξ)` is smooth with vanishing derivative at every `g`.
  refine (h.contMDiff_momentDefect_apply x₀ ξ).mdifferentiable (by simp)
    |>.apply_eq_of_mfderiv_eq_zero (fun g ↦ ?_) g₀ 1
  rw [← mvfderiv_eq_zero_iff]
  ext w
  /- Near `g`, the defect is `θ(g k)(ξ) = θ(g)(ξ) + θ(k)(Ad_{g⁻¹} ξ)`, whose derivative in `k`
  at `1` vanishes because the cocycle does. Every tangent vector at `g` is a left translate. -/
  have hL : MDifferentiableAt I I (fun k : G ↦ g * k) 1 :=
    contMDiff_mul_left.mdifferentiableAt one_ne_zero
  have hw : mfderiv I I (fun k : G ↦ g * k) 1 (mfderiv I I (fun k : G ↦ g⁻¹ * k) g w) = w :=
    mulInvariantVectorField_mfderiv_inv_mul (I := I) w
  have htrans : (fun k : G ↦ momentDefect μ (g * k) x₀ ξ) = fun k ↦
      momentDefect μ g x₀ ξ +
        momentDefect μ k x₀ (Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ) := by
    funext k
    rw [h.momentDefect_mul_eq (hσ g), LinearMap.add_apply, Lie.coadjointRepresentation_apply]
  have hθ := h.contMDiff_momentDefect_apply x₀ ξ
  have hcomp := mvfderiv_comp_apply_of_eq (g := fun k : G ↦ momentDefect μ k x₀ ξ)
    (f := fun k : G ↦ g * k) (1 : G) (hθ.mdifferentiableAt (by simp)) hL (mul_one g)
    (mfderiv I I (fun k : G ↦ g⁻¹ * k) g w)
  rw [hw] at hcomp
  have hzero : mvfderiv I (fun k : G ↦
      momentDefect μ k x₀ (Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ)) 1 = 0 := by
    ext v
    rw [h.mvfderiv_momentDefect_one, hc]
    -- Mathlib has no evaluation lemma for the zero `2`-cochain; it evaluates to zero by definition.
    rfl
  rw [zero_apply, ← hcomp, Function.comp_def, htrans,
    mvfderiv_fun_add mdifferentiableAt_const
      ((h.contMDiff_momentDefect_apply x₀ _).mdifferentiableAt (by simp)),
    mvfderiv_const, zero_add, hzero]
  -- The zero linear map on the tangent space at `g` evaluates to zero by definition.
  rfl

end IsMomentMap

end SmoothTwoForm

end TauCeti
