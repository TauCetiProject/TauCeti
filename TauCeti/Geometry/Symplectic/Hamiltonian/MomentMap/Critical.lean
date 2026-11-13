/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Critical points of the components of a moment map

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` on a manifold with a
two-form `σ`, so that each component `μ^Z = ⟨μ, Z⟩` satisfies `dμ^Z = ι_{Z_M} σ`. At a point where
`σ` is nondegenerate, `dμ^Z_x = σ(Z_M x, ·)` vanishes exactly when `Z_M x = 0`. So **the critical
set of `μ^Z` is the zero set of `Z_M`** (`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq`),
equivalently the set of points whose isotropy algebra contains `Z`.

For a smooth action of a Lie group `G` on a boundaryless Hausdorff manifold, the zeros of the
fundamental vector field `ξ_M` are the points fixed by every `exp (t ξ)`, and, stabilizers being
closed, the points fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`
(`TauCeti.Lie.closedOneParameterSubgroup`). Hence, for a symplectic action with moment map `μ`,
**the critical set of `μ^ξ` is the fixed-point set `M^{T_ξ}`**
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints`). This holds for every `ξ`,
whether the one-parameter subgroup it generates is closed (a rational direction in a torus) or
not (an irrational direction, where `T_ξ` is a torus of higher dimension).

When `T_ξ = G`, the critical set of `μ^ξ` is the fixed-point set `M^G` of the whole group. For a
torus `G`, Kronecker's theorem makes the generators `ξ` with `T_ξ = G` dense in `𝔤`, so **a
generic component of the moment map has critical set `M^G`**
(`TauCeti.SmoothTwoForm.IsMomentMap.dense_setOf_criticalPoints_eq_fixedPoints`). This is the
starting point of the Morse–Bott theory of moment maps of torus actions: the critical manifolds
of a generic component are the components of the fixed-point set.

Neither closedness of `σ` nor equivariance of `μ` is used, and `M` need not be compact.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_iff`: at a point where `σ` is
  nondegenerate, `x` is a critical point of `μ^Z` exactly when `Z_M x = 0`.
* `TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq`: for a nondegenerate `σ`, the critical set
  of `μ^Z` is the zero set of `Z_M`.
* `TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_iff_closedOneParameterSubgroup_le`: for a
  group action, `x` is a critical point of `μ^ξ` exactly when `T_ξ` fixes `x`.
* `TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints`: the critical set of `μ^ξ` is
  `M^{T_ξ}`.
* `TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints_of_eq_top`: if `T_ξ = G`, the
  critical set of `μ^ξ` is `M^G`.
* `TauCeti.SmoothTwoForm.IsMomentMap.dense_setOf_criticalPoints_eq_fixedPoints`: for a torus, the
  `ξ` whose component `μ^ξ` has critical set `M^G` are dense in the Lie algebra.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the critical set of `μ^ξ` is the fixed-point set of the closure of `exp (ℝ ξ)`).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, § 3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

section Infinitesimal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}

/-- **Critical points of a moment map component.** At a point `x` where `σ` is nondegenerate,
`x` is a critical point of the component `μ^Z = ⟨μ, Z⟩` exactly when `Z_M` vanishes at `x`. -/
theorem mem_criticalPoints_iff (h : σ.IsMomentMap a μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate) (Z : 𝔤) :
    x ∈ criticalPoints I (fun y ↦ μ y Z) ↔ a Z x = 0 := by
  rw [mem_criticalPoints]
  refine ⟨fun hx ↦ hσ.1 _ fun v ↦ ?_, fun hx ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  · rw [SmoothForm.bilinFormAt_apply, h.eval₂_apply, hx, zero_apply]
  · rw [← h.eval₂_apply, ← SmoothForm.bilinFormAt_apply, hx, map_zero, LinearMap.zero_apply,
      zero_apply]

/-- At a point where `σ` is nondegenerate, `x` is a critical point of `μ^Z` exactly when `Z`
lies in the isotropy algebra `𝔤_x`. -/
theorem mem_criticalPoints_iff_mem_isotropy (h : σ.IsMomentMap a μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate) (Z : 𝔤) :
    x ∈ criticalPoints I (fun y ↦ μ y Z) ↔ Z ∈ a.isotropy x := by
  rw [h.mem_criticalPoints_iff hσ, InfinitesimalAction.mem_isotropy_iff]

/-- **The critical set of a moment map component is the zero set of the generated vector
field**: for a nondegenerate `σ`, `Crit(μ^Z) = {x | Z_M x = 0}`. -/
theorem criticalPoints_eq (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (Z : 𝔤) :
    criticalPoints I (fun y ↦ μ y Z) = {x | a Z x = 0} :=
  Set.ext fun _ ↦ h.mem_criticalPoints_iff (hσ.nondegenerate_bilinFormAt _) Z

end Infinitesimal

section Group

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [BoundarylessManifold I' M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **Critical points of a moment map component and closed one-parameter subgroups.** For a
moment map of a smooth group action and a point `x` where `σ` is nondegenerate, `x` is a critical
point of `μ^ξ` exactly when the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` fixes `x`. -/
theorem mem_criticalPoints_iff_closedOneParameterSubgroup_le
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate) (ξ : GroupLieAlgebra I G) :
    x ∈ criticalPoints I' (fun y ↦ μ y ξ) ↔
      Lie.closedOneParameterSubgroup ξ ≤ MulAction.stabilizer G x := by
  rw [h.mem_criticalPoints_iff_mem_isotropy hσ,
    Lie.mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le]

/-- **The critical set of `μ^ξ` is the fixed-point set of `T_ξ`.** For a moment map of a smooth
action of a Lie group `G` on `(M, σ)` with `σ` nondegenerate, the critical set of the component
`μ^ξ` is the set `M^{T_ξ}` of points fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`. -/
theorem criticalPoints_eq_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (ξ : GroupLieAlgebra I G) :
    criticalPoints I' (fun y ↦ μ y ξ) =
      MulAction.fixedPoints (Lie.closedOneParameterSubgroup ξ) M := by
  ext x
  rw [h.mem_criticalPoints_iff_closedOneParameterSubgroup_le (hσ.nondegenerate_bilinFormAt x),
    MulAction.mem_fixedPoints]
  exact ⟨fun hle g ↦ hle g.2, fun hfix g hg ↦ hfix ⟨g, hg⟩⟩

/-- **A component generating a dense one-parameter subgroup has critical set `M^G`.** If the
one-parameter subgroup of `ξ` is dense in `G`, the critical set of `μ^ξ` is the fixed-point set of
the whole group. -/
theorem criticalPoints_eq_fixedPoints_of_eq_top
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    {ξ : GroupLieAlgebra I G} (hξ : Lie.closedOneParameterSubgroup ξ = ⊤) :
    criticalPoints I' (fun y ↦ μ y ξ) = MulAction.fixedPoints G M := by
  ext x
  rw [h.mem_criticalPoints_iff_closedOneParameterSubgroup_le (hσ.nondegenerate_bilinFormAt x), hξ,
    MulAction.mem_fixedPoints]
  exact ⟨fun hle g ↦ hle (Subgroup.mem_top g), fun hfix g _ ↦ hfix g⟩

variable (G) in
/-- **Generic components of a torus moment map have critical set `M^G`.** For a moment map of a
smooth action of a compact connected commutative Lie group `G` on `(M, σ)` with `σ`
nondegenerate, the elements `ξ` of the Lie algebra for which the critical set of `μ^ξ` is the
fixed-point set `M^G` form a dense subset. -/
theorem dense_setOf_criticalPoints_eq_fixedPoints [IsMulCommutative G] [CompactSpace G]
    [PreconnectedSpace G] (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : σ.IsNondegenerate) :
    Dense {ξ : GroupLieAlgebra I G |
      criticalPoints I' (fun y ↦ μ y ξ) = MulAction.fixedPoints G M} :=
  (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).mono fun _ hξ ↦
    h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ

end Group

end TauCeti.SmoothTwoForm.IsMomentMap
