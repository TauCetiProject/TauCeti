/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Continuous group actions on projective space

A group `G` acting `K`-linearly on `V` acts on the projective space `ℙ K V` by moving lines
(`Projectivization.smul_mk`). When `G` is a topological space acting jointly continuously on `V`,
and scalar multiplication by units of `K` is continuous on `V`, the action on `ℙ K V` is jointly
continuous in the group element and the line. The map
`G × {v : V // v ≠ 0} → G × ℙ K V` is a product of open quotient maps, hence a quotient map, and
the action lifts through it to `(g, v) ↦ [g • v]`.

For matrix groups this gives the jointly continuous actions of `GL(n, K)` and `SL(n, K)` on
`ℙ K (n → K)` over a topological field. The projective special linear group
`PSL(n, K) = SL(n, K) ⧸ Z(SL(n, K))`, with its quotient topology, then acts jointly continuously
as well, because `SL(n, K) → PSL(n, K)` is an open quotient map. Over `ℂ` and `n = 2` these are
the continuous Möbius actions on `ℂℙ¹`, which transport to the Riemann sphere `OnePoint ℂ`
(`OnePoint.instContinuousSMulGL` and `OnePoint.instContinuousSMulPSL`).

When rescaled invertible matrices converge to a possibly singular matrix `B`, their action on
lines converges to the map `[v] ↦ [B v]` (`Projectivization.linearProjection`) away from the
kernel of `B`.

## Main results

* `Projectivization.instContinuousSMul`: a jointly continuous linear action on `V` induces a jointly
  continuous action on `ℙ K V`; for instance by `GL n K` or `SL(n, K)` on `ℙ K (n → K)`.
* `Projectivization.instContinuousSMulPSL`: `PSL(n, K)` acts jointly continuously on
  `ℙ K (n → K)`.
* `Projectivization.tendsto_smul_of_tendsto_smul_coe`: invertible matrices converging projectively
  to a possibly singular matrix `B` act, in the limit, as `[v] ↦ [B v]` away from the kernel of `B`.
-/

public section

open Topology
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Projectivization

section DivisionRing

variable {G K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousConstSMul Kˣ V] [Group G] [DistribMulAction G V] [SMulCommClass G K V]
  [TopologicalSpace G] [ContinuousSMul G V]

/-- A group acting `K`-linearly and jointly continuously on `V` acts jointly continuously on the
projective space `ℙ K V`, provided scalar multiplication by units of `K` is continuous on `V`. -/
instance instContinuousSMul : ContinuousSMul G (ℙ K V) where
  continuous_smul := by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk').isQuotientMap.continuous_iff]
    -- On representatives the action is `(g, v) ↦ [g • v]` (`Projectivization.smul_mk`).
    exact continuous_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
      fun p ↦ (smul_ne_zero_iff_ne p.1).2 p.2.2

end DivisionRing

section Field

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K]

/-- Over a topological field, the projective special linear group `PSL(n, K)`, with the quotient
topology of `SL(n, K) ⧸ Z(SL(n, K))`, acts jointly continuously on `ℙ K (n → K)`. -/
instance instContinuousSMulPSL :
    ContinuousSMul (Matrix.ProjectiveSpecialLinearGroup n K) (ℙ K (n → K)) where
  continuous_smul := by
    rw [(QuotientGroup.isOpenQuotientMap_mk.prodMap
      IsOpenQuotientMap.id).isQuotientMap.continuous_iff]
    -- The class of `g ∈ SL(n, K)` acts as `g` does.
    exact continuous_smul.congr fun p ↦
      (Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk p.1 p.2).symm

open Filter Matrix in
/-- **Limits of projectively convergent matrices.** Let `C a` be invertible matrices which
converge projectively to a possibly singular matrix `B`: for some scalars `c a`, the matrices
`c a • C a` converge to `B`. Then the projective transformations `C a` converge to the map
`[v] ↦ [B v]` (`Projectivization.linearProjection`) away from the kernel of `B`: if lines `x a`
converge to a line `x₀` not killed by `B`, the lines `C a • x a` converge to the line of `B x₀`.
When `B` is invertible this is the continuity of the action; when `B` has rank one the limit map
is constant off the kernel of `B`. -/
theorem tendsto_smul_of_tendsto_smul_coe [T1Space K] [Nonempty n] {α : Type*} {l : Filter α}
    {C : α → GL n K} {c : α → K} {B : Matrix n n K} {x : α → ℙ K (n → K)} {x₀ : ℙ K (n → K)}
    (hC : Tendsto (fun a ↦ c a • (C a : Matrix n n K)) l (𝓝 B)) (hx : Tendsto x l (𝓝 x₀))
    (hx₀ : x₀ ∈ linearProjectionDomain B.mulVecLin) :
    Tendsto (fun a ↦ C a • x a) l (𝓝 (linearProjection B.mulVecLin x₀)) := by
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp [mem_linearProjectionDomain_iff] at hx₀
  refine ((continuousAt_linearProjection (G := fun D : Matrix n n K ↦ D.mulVecLin)
    (continuous_fst.matrix_mulVec continuous_snd) hx₀).tendsto.comp
      (hC.prodMk_nhds hx)).congr' ?_
  -- Eventually `c a ≠ 0`, since the limit `B` is nonzero, and then `[c a • C a (x a)]` is
  -- `C a • x a`.
  filter_upwards [hC.eventually_ne hB0] with a ha
  have hca : c a ≠ 0 := fun h ↦ ha (by simp [h])
  have hCx : (c a • (C a : Matrix n n K)).mulVecLin (x a).rep ≠ 0 := by
    simpa [smul_mulVec, hca, Units.smul_def] using (smul_ne_zero_iff_ne (C a)).2 (x a).rep_ne_zero
  conv_rhs => rw [← mk_rep (x a), smul_mk]
  simp only [Function.comp_apply]
  conv_lhs => rw [← mk_rep (x a)]
  rw [linearProjection_mk _ _ hCx]
  exact (mk_eq_mk_iff' K _ _ _ _).2 ⟨c a, by simp [Units.smul_def]⟩

end Field

end Projectivization
