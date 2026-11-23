/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height
public import TauCeti.Geometry.Symplectic.Coadjoint.Height

/-!
# Heights on coadjoint orbits through an invariant form

Let `G` be a real Lie group with Lie algebra `𝔤 = GroupLieAlgebra I G`, let `O = G ⧸ G_ν` be the
coadjoint orbit of `ν ∈ 𝔤*` with orbit map `μ : O → 𝔤*`, and let `f_X = ⟨μ, X⟩` be the height of
`X ∈ 𝔤`. On the orbit manifold, with the intrinsic critical Hessian, the critical points of `f_X`
are the points with `⁅X, μ x⁆ = 0`, and the Morse index at such a point is the negative index of
inertia of `ξ ↦ μ(x)(⁅⁅X, ξ⁆, ξ⁆)` on `𝔤`
(`Module.Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply`). This file reads these
statements through an invariant bilinear form `B` on `𝔤`, as for a compact group with an
`Ad`-invariant inner product.

Write `μ x = B q`; for a separating `B` such a `q ∈ 𝔤` exists and is unique. Then, in the namespace
`Module.Dual`:

* `x` is a critical point of `f_X` exactly when `⁅X, q⁆ = 0`, for a separating `B`
  (`mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero`);
* at a critical point the Morse index of `f_X` is the negative index of the height Hessian
  `h_(q,X)(A, C) = -B(⁅A, q⁆, ⁅C, X⁆)` (`LinearMap.BilinForm.heightHessian`)
  (`manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sigNeg`), and the critical point
  is nondegenerate exactly when the kernel of `h_(q,X)` is the centralizer of `q`
  (`isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff_ker`).

The evaluation of these statements at torus points of a root-plane decomposition is in
`TauCeti.Geometry.Symplectic.Coadjoint.Height.RootPlane`.

## Main results

* `Module.Dual.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero`: the
  critical points of a height through a separating invariant form.
* `Module.Dual.manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sigNeg`: the Morse
  index of a height is the negative index of the height Hessian.
* `Module.Dual.isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff_ker`:
  nondegenerate critical points of a height through a separating invariant form.

## References

* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
-/

public section

noncomputable section

open Module Manifold TauCeti TauCeti.Lie QuadraticMap
open scoped Manifold ContDiff

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {x : G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν}

/-! ### Heights through an invariant form -/

section InvariantForm

variable {X q : GroupLieAlgebra I G}

/-- **The critical points of a height through an invariant form.** If `μ x = B q` for a separating
invariant form `B`, then `x` is a critical point of the height `f_X` exactly when `⁅X, q⁆ = 0`. -/
theorem mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff_lie_eq_zero
    (hB : B.lieInvariant (GroupLieAlgebra I G)) (hsep : B.SeparatingLeft)
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) :
    x ∈ criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) ↔
      ⁅X, q⁆ = 0 := by
  rw [ν.mem_criticalPoints_orbitMap_coadjointRepresentation_apply_iff, hq, hB.lie_apply_eq,
    ← LinearMap.mem_ker, LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep, Submodule.mem_bot]

/-- **The Morse index of a height through an invariant form.** If `μ x = B q` for an invariant
form `B` and `⁅X, q⁆ = 0`, the Morse index of the height `f_X` at `x` is the negative index of
inertia of the height Hessian `h_(q,X)(A, C) = -B(⁅A, q⁆, ⁅C, X⁆)` on `𝔤`. -/
theorem manifoldMorseIndex_orbitMap_coadjointRepresentation_apply_eq_sigNeg
    (hB : B.lieInvariant (GroupLieAlgebra I G))
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) (hXq : ⁅X, q⁆ = 0) :
    manifoldMorseIndex
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x =
      sigNeg (B.heightHessian q X).toQuadraticMap :=
  manifoldMorseIndex_orbitMap_coadjointRepresentation_apply
    (by rw [hq, hB.lie_apply_eq, hXq, map_zero]) _ fun ξ ↦ by
      rw [LinearMap.BilinMap.toQuadraticMap_apply, hq,
        LinearMap.BilinForm.heightHessian_apply_eq_apply_lie_lie hB]

/-- **Nondegenerate critical points of a height through an invariant form.** If `μ x = B q` for a
separating invariant form `B` and `⁅X, q⁆ = 0`, then `x` is a nondegenerate critical point of the
height `f_X` exactly when the kernel of the height Hessian `h_(q,X)` is the centralizer of `q`. -/
theorem isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff_ker
    (hB : B.lieInvariant (GroupLieAlgebra I G)) (hsep : B.SeparatingLeft)
    (hq : (coadjointRepresentation ℝ I G).orbitMap ν x = B q) (hXq : ⁅X, q⁆ = 0) :
    IsManifoldNondegenerateCriticalPoint
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) x ↔
      LinearMap.ker (B.heightHessian q X) = LinearMap.ker (LieAlgebra.ad ℝ _ q) := by
  rw [isManifoldNondegenerateCriticalPoint_orbitMap_coadjointRepresentation_apply_iff
      (by rw [hq, hB.lie_apply_eq, hXq, map_zero]),
    le_antisymm_iff, and_iff_left LinearMap.BilinForm.ker_ad_le_ker_heightHessian]
  -- Both sides say that every `ξ` in the kernel of `h_(q,X)` commutes with `q`.
  refine forall_congr' fun ξ ↦ ?_
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LieAlgebra.ad_apply, ← lie_skew, neg_eq_zero, hq,
    hB.lie_apply_eq, ← LinearMap.mem_ker (f := B), LinearMap.separatingLeft_iff_ker_eq_bot.mp hsep,
    Submodule.mem_bot]
  refine imp_congr ⟨fun h ↦ LinearMap.ext fun η ↦ ?_, fun h η ↦ ?_⟩ Iff.rfl
  · rw [LinearMap.BilinForm.heightHessian_apply_eq_apply_lie_lie hB, h η, LinearMap.zero_apply]
  · rw [← LinearMap.BilinForm.heightHessian_apply_eq_apply_lie_lie hB, h, LinearMap.zero_apply]

end InvariantForm

end Module.Dual
