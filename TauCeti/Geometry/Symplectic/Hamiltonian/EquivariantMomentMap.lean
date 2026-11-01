/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Coadjoint
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Equivariant moment maps of Lie group actions and their group defect

Let a Lie group `G`, with tangent Lie algebra `𝔤 = GroupLieAlgebra I G`, act smoothly on the left on
a manifold `M` carrying a two-form `σ`, and let `ξ ↦ ξ_M` be the infinitesimal action by
fundamental vector fields (`TauCeti.InfinitesimalAction.fundamental`). A moment map of this action,
`μ : M → 𝔤*` with `ι_{ξ_M} σ = d⟨μ, ξ⟩` (`TauCeti.SmoothTwoForm.IsMomentMap`), is **equivariant**
when it intertwines the action with the coadjoint representation
(`TauCeti.Lie.coadjointRepresentation`):

`μ(g • x) = Ad*_g (μ x)`, where `(Ad*_g ν)(ξ) = ν(Ad_{g⁻¹} ξ)`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`).

The failure of an arbitrary map `μ : M → 𝔤*` to be equivariant is measured by its **group defect**

`θ(g, x) = μ(g • x) - Ad*_g (μ x)` (`TauCeti.momentDefect`).

It satisfies `θ(gh, x) = θ(g, h • x) + Ad*_g θ(h, x)` for every map `μ`
(`TauCeti.momentDefect_mul`), and shifting `μ` by a constant `ν` adds the coboundary
`ν - Ad*_g ν` (`TauCeti.momentDefect_add_const`). The geometric input is that, when every `g` acts
by a map preserving `σ` and `M` is preconnected, the defect of a moment map does not depend on the
point: `θ(g, x) = θ(g, y)` (`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq`). Indeed both
`x ↦ μ(g • x)` and `x ↦ Ad*_g (μ x)` are moment maps of the action `ξ ↦ (Ad_{g⁻¹} ξ)_M` (the first
because `g` preserves `σ` and carries `(Ad_{g⁻¹} ξ)_M` to `ξ_M`), so they differ by a constant.
Hence `θ(g) = θ(g, x)` is a **group `1`-cocycle** of `G` with values in the coadjoint
representation, `θ(gh) = θ(g) + Ad*_g θ(h)` (`TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_mul`),
and `μ` is equivariant for the affine action `ν ↦ Ad*_g ν + θ(g)` of `G` on `𝔤*`
(`TauCeti.SmoothTwoForm.IsMomentMap.apply_smul_eq`). No connectedness of `G` is assumed, so `θ`
records the behaviour of `μ` on every component of `G`.

A moment map is equivariant exactly when its defect vanishes. Adding a constant `ν` to an
equivariant moment map keeps it equivariant exactly when `ν` is fixed by the coadjoint
representation, and on a preconnected manifold the equivariant moment maps of an action are
exactly the shifts of one of them by coadjoint-invariant constants
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap σ μ`: `μ` is a coadjoint-equivariant moment map of
  the action of `G` on `(M, σ)`.
* `TauCeti.momentDefect μ g x`: the group defect `μ(g • x) - Ad*_g (μ x)`.

## Main results

* `TauCeti.momentDefect_mul`: `θ(gh, x) = θ(g, h • x) + Ad*_g θ(h, x)`.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_eq`: for an action preserving `σ` on a
  preconnected manifold, the defect of a moment map is independent of the point.
* `TauCeti.SmoothTwoForm.IsMomentMap.momentDefect_mul`: the defect is a group `1`-cocycle.
* `TauCeti.SmoothTwoForm.isEquivariantMomentMap_iff_momentDefect_eq_zero`: equivariance is the
  vanishing of the defect.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.add_const_iff`: equivariant shifts are shifts by
  coadjoint-invariant constants.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* J. Marsden and T. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Springer,
  1999, Sections 11.4 and 12.3 (the nonequivariance cocycle `σ(g) = μ(g • x) - Ad*_g μ(x)`).
* J.-M. Souriau, *Structure of Dynamical Systems*, Birkhäuser, 1997, Section 11 (the cocycle of a
  moment map).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]
  {M : Type*} [MulAction G M]

/-- The **group defect** `θ(g, x) = μ(g • x) - Ad*_g (μ x)` of a map `μ : M → 𝔤*` on a space with a
left action of a Lie group `G`, measuring the failure of `μ` to be coadjoint equivariant. -/
def momentDefect (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    Module.Dual 𝕜 (GroupLieAlgebra I G) :=
  μ (g • x) - Lie.coadjointRepresentation I G g (μ x)

theorem momentDefect_apply (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    momentDefect μ g x = μ (g • x) - Lie.coadjointRepresentation I G g (μ x) :=
  (rfl)

/-- A map `μ` is equivariant for the affine action `ν ↦ Ad*_g ν + θ(g, x)` at `x`. -/
theorem apply_smul_eq_add_momentDefect (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G)
    (x : M) : μ (g • x) = Lie.coadjointRepresentation I G g (μ x) + momentDefect μ g x := by
  rw [momentDefect_apply, add_sub_cancel]

/-- The defect vanishes at the identity. -/
@[simp]
theorem momentDefect_one (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (x : M) :
    momentDefect μ 1 x = 0 := by
  simp [momentDefect_apply]

/-- **The cocycle law of the defect**, pointwise: `θ(gh, x) = θ(g, h • x) + Ad*_g θ(h, x)`. -/
theorem momentDefect_mul (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g h : G) (x : M) :
    momentDefect μ (g * h) x =
      momentDefect μ g (h • x) + Lie.coadjointRepresentation I G g (momentDefect μ h x) := by
  simp only [momentDefect_apply, map_sub, mul_smul, map_mul, Module.End.mul_apply]
  abel

/-- Shifting `μ` by a constant `ν` adds the coboundary `ν - Ad*_g ν` to its defect. -/
theorem momentDefect_add_const (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G))
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    momentDefect (fun y ↦ μ y + ν) g x =
      momentDefect μ g x + (ν - Lie.coadjointRepresentation I G g ν) := by
  simp only [momentDefect_apply, map_add]
  abel

/-- The defect of `-μ` is the negative of the defect of `μ`. -/
@[simp]
theorem momentDefect_neg (μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)) (g : G) (x : M) :
    momentDefect (fun y ↦ -μ y) g x = -momentDefect μ g x := by
  simp only [momentDefect_apply, map_neg]
  abel

end Defect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

/-- A Lie group of class `minSmoothness ℝ 3` is in particular a `C¹` Lie group. -/
local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- A smooth action is in particular a `C¹` action. -/
local instance contMDiffSMulOne : ContMDiffSMul I I' 1 G M :=
  ContMDiffSMul.of_le (M := M) (m := ∞) (n := 1) ENat.LEInfty.out

namespace SmoothTwoForm

variable (I G) in
/-- `μ : M → 𝔤*` is a **coadjoint-equivariant moment map** of the smooth action of the Lie group
`G` on `M` for the two-form `σ`: it is a moment map of the infinitesimal action by fundamental
vector fields, `ι_{ξ_M} σ = d⟨μ, ξ⟩`, and `μ(g • x) = Ad*_g (μ x)` for all `g` and `x`. -/
structure IsEquivariantMomentMap (σ : SmoothTwoForm I' M)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : Prop
    extends σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ where
  /-- The moment map intertwines the action with the coadjoint representation. -/
  map_smul : ∀ (g : G) (x : M), μ (g • x) = Lie.coadjointRepresentation I G g (μ x)

variable {σ : SmoothTwoForm I' M} {μ μ' : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- An equivariant moment map is a moment map whose group defect vanishes identically. -/
theorem isEquivariantMomentMap_iff_momentDefect_eq_zero :
    σ.IsEquivariantMomentMap I G μ ↔
      σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ ∧
        ∀ (g : G) (x : M), momentDefect μ g x = 0 := by
  simp only [momentDefect_apply, sub_eq_zero]
  exact ⟨fun h ↦ ⟨h.toIsMomentMap, h.map_smul⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsMomentMap

/-- **Independence of the defect from the point.** If every element of `G` acts by a map preserving
`σ`, the group defect `μ(g • x) - Ad*_g (μ x)` of a moment map `μ` on a preconnected manifold does
not depend on `x`. -/
theorem momentDefect_eq [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (g : G) (x y : M) : momentDefect μ g x = momentDefect μ g y := by
  set a := InfinitesimalAction.fundamental I G I' M
  set f : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G := (Lie.tangentAd (I := I) g⁻¹).toLieHom
    with hf
  -- `x ↦ μ (g • x)` is a moment map of `ξ ↦ (Ad_{g⁻¹} ξ)_M`, since `g` preserves `σ`.
  have h₁ : σ.IsMomentMap (a.comp f) (μ ∘ fun x : M ↦ g • x) := by
    have := h.mpullback (ContMDiffSMul.contMDiff_const_smul (I := I) g) (a' := a.comp f)
      fun ξ x ↦ by
        rw [InfinitesimalAction.comp_apply, InfinitesimalAction.fundamental_apply,
          InfinitesimalAction.fundamental_apply, hf, LieEquiv.coe_toLieHom,
          mfderiv_smul_fundamentalVectorField, Lie.tangentAd_apply,
          ← ContinuousLinearMap.comp_apply, ← Lie.adjointContinuousLinearMap_mul, mul_inv_cancel,
          Lie.adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]
    rwa [hσ g] at this
  -- So is `x ↦ Ad*_g (μ x)`, the restriction of `μ` along `Ad_{g⁻¹}`.
  obtain ⟨ν, hν⟩ := (h.comp f).isMomentMap_iff_exists_eq_add.1 h₁
  have hd (z : M) : momentDefect μ g z = ν := by
    have hz := congrFun hν z
    rw [Function.comp_apply] at hz
    rw [momentDefect_apply, hz, add_sub_right_comm, add_eq_right, sub_eq_zero]
    ext ξ
    rw [LinearMap.comp_apply, hf, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom,
      Lie.tangentAd_apply, Lie.coadjointRepresentation_apply_apply]
  rw [hd, hd]

variable (x₀ : M)

/-- **The defect is a group cocycle.** For an action preserving `σ` on a preconnected manifold, the
defect `θ(g) = θ(g, x)` of a moment map, at any point, satisfies `θ(gh) = θ(g) + Ad*_g θ(h)`. -/
theorem momentDefect_mul [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (g g' : G) :
    momentDefect μ (g * g') x₀ =
      momentDefect μ g x₀ + Lie.coadjointRepresentation I G g (momentDefect μ g' x₀) := by
  rw [TauCeti.momentDefect_mul, h.momentDefect_eq hσ g (g' • x₀) x₀]

/-- **Affine equivariance.** For an action preserving `σ` on a preconnected manifold, a moment map
is equivariant for the affine action `ν ↦ Ad*_g ν + θ(g)` of `G` on `𝔤*`, where `θ(g)` is its
defect at any point `x₀`. -/
theorem apply_smul_eq [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (g : G) (x : M) :
    μ (g • x) = Lie.coadjointRepresentation I G g (μ x) + momentDefect μ g x₀ := by
  rw [← h.momentDefect_eq hσ g x x₀]
  exact apply_smul_eq_add_momentDefect μ g x

/-- For an action preserving `σ` on a preconnected manifold, a moment map is equivariant as soon as
its defect vanishes at a single point. -/
theorem isEquivariantMomentMap_of_momentDefect_eq_zero [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (h₀ : ∀ g : G, momentDefect μ g x₀ = 0) : σ.IsEquivariantMomentMap I G μ :=
  isEquivariantMomentMap_iff_momentDefect_eq_zero.2
    ⟨h, fun g x ↦ (h.momentDefect_eq hσ g x x₀).trans (h₀ g)⟩

end IsMomentMap

namespace IsEquivariantMomentMap

/-- The defect of an equivariant moment map vanishes. -/
theorem momentDefect_eq_zero (h : σ.IsEquivariantMomentMap I G μ) (g : G) (x : M) :
    momentDefect μ g x = 0 :=
  (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 h).2 g x

/-- The negative of an equivariant moment map for `σ` is an equivariant moment map for `-σ`. -/
theorem neg (h : σ.IsEquivariantMomentMap I G μ) :
    (-σ).IsEquivariantMomentMap I G fun x ↦ -μ x where
  toIsMomentMap := h.toIsMomentMap.neg
  map_smul g x := by rw [h.map_smul, map_neg]

/-- Adding a constant `ν` fixed by the coadjoint representation to an equivariant moment map gives
an equivariant moment map. -/
theorem add_const (h : σ.IsEquivariantMomentMap I G μ) {ν : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ∀ g : G, Lie.coadjointRepresentation I G g ν = ν) :
    σ.IsEquivariantMomentMap I G fun x ↦ μ x + ν where
  toIsMomentMap := h.toIsMomentMap.add_const ν
  map_smul g x := by rw [map_add, hν, h.map_smul]

/-- **Equivariant shifts.** Adding a constant `ν` to an equivariant moment map on a nonempty
manifold gives an equivariant moment map exactly when `ν` is fixed by the coadjoint
representation. -/
theorem add_const_iff [Nonempty M] (h : σ.IsEquivariantMomentMap I G μ)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    σ.IsEquivariantMomentMap I G (fun x ↦ μ x + ν) ↔
      ∀ g : G, Lie.coadjointRepresentation I G g ν = ν := by
  refine ⟨fun h' g ↦ ?_, h.add_const⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  have := h'.momentDefect_eq_zero g x
  rwa [momentDefect_add_const, h.momentDefect_eq_zero, zero_add, sub_eq_zero, eq_comm] at this

/-- **Uniqueness of equivariant moment maps.** On a preconnected manifold, the equivariant moment
maps of an action are exactly the shifts `x ↦ μ x + ν` of any one of them by constants `ν` fixed by
the coadjoint representation. -/
theorem isEquivariantMomentMap_iff_exists_eq_add [PreconnectedSpace M]
    (h : σ.IsEquivariantMomentMap I G μ) :
    σ.IsEquivariantMomentMap I G μ' ↔
      ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G),
        (∀ g : G, Lie.coadjointRepresentation I G g ν = ν) ∧ μ' = fun x ↦ μ x + ν := by
  refine ⟨fun h' ↦ ?_, fun ⟨ν, hν, hμ'⟩ ↦ hμ' ▸ h.add_const hν⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun g ↦ map_zero _, funext fun x ↦ isEmptyElim x⟩
  obtain ⟨ν, rfl⟩ := (h.toIsMomentMap.isMomentMap_iff_exists_eq_add).1 h'.toIsMomentMap
  exact ⟨ν, (h.add_const_iff ν).1 h', rfl⟩

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
