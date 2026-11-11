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
`c a • C a` converge to `B`. Then the projective transformations `C a` converge to `[v] ↦ [B v]`
away from the kernel of `B`: if lines `x a` converge to a line `x₀` not killed by `B`, the lines
`C a • x a` converge to the line of `B x₀`. When `B` is invertible this is the continuity of the
action; when `B` is singular the limit map is constant along each line of the image of `B`. -/
theorem tendsto_smul_of_tendsto_smul_coe [T1Space K] {α : Type*} {l : Filter α}
    {C : α → GL n K} {c : α → K} {B : Matrix n n K} {x : α → ℙ K (n → K)} {x₀ : ℙ K (n → K)}
    (hC : Tendsto (fun a ↦ c a • (C a : Matrix n n K)) l (𝓝 B)) (hx : Tendsto x l (𝓝 x₀))
    (hB : B *ᵥ x₀.rep ≠ 0) :
    Tendsto (fun a ↦ C a • x a) l (𝓝 (mk K (B *ᵥ x₀.rep) hB)) := by
  classical
  -- The line through a vector, extended by `x₀` at `0`; it is continuous away from `0`.
  set e : (n → K) → ℙ K (n → K) := fun w ↦ if h : w = 0 then x₀ else mk K w h with he
  have he_smul : ∀ (a : K) (w : n → K), a ≠ 0 → e (a • w) = e w := fun a w ha ↦ by
    by_cases hw : w = 0
    · simp [he, hw]
    · simp only [he, smul_eq_zero, ha, hw, or_self, ↓reduceDIte]
      exact (mk_eq_mk_iff' K _ _ _ _).2 ⟨a, rfl⟩
  have he_cont : ∀ w : n → K, w ≠ 0 → ContinuousAt e w := fun w hw ↦ by
    refine (continuousOn_iff_continuous_domRestrict.2 ?_).continuousAt (isOpen_ne.mem_nhds hw)
    convert continuous_mk' (K := K) (V := n → K) using 1
    funext w'
    simp [he, show (w' : n → K) ≠ 0 from w'.2, mk'_eq_mk]
  -- On pairs of a matrix and a line the limit map is `(D, y) ↦ e (D y)`, continuous at `(B, x₀)`
  -- because the quotient map from nonzero vectors to lines is open.
  have key : Tendsto (fun q : Matrix n n K × ℙ K (n → K) ↦ e (q.1 *ᵥ q.2.rep)) (𝓝 (B, x₀))
      (𝓝 (mk K (B *ᵥ x₀.rep) hB)) := by
    let p : Matrix n n K × {v : n → K // v ≠ 0} := (B, ⟨x₀.rep, x₀.rep_ne_zero⟩)
    have hp : Prod.map id (mk' K) p = (B, x₀) := by simp [p, mk'_eq_mk]
    refine Tendsto.mono_left ?_ (hp ▸ (IsOpenMap.id.prodMap isOpenMap_mk').nhds_le p)
    rw [tendsto_map'_iff]
    have hcomp : ((fun q : Matrix n n K × ℙ K (n → K) ↦ e (q.1 *ᵥ q.2.rep)) ∘
        Prod.map id (mk' K)) = fun q ↦ e (q.1 *ᵥ (q.2 : n → K)) := by
      funext q
      obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K q.2.1 q.2.2
      simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, mk'_eq_mk]
      rw [← ha, Units.smul_def, mulVec_smul, he_smul _ _ a.ne_zero]
    have hpB : e (B *ᵥ x₀.rep) = mk K (B *ᵥ x₀.rep) hB := by simp [he, hB]
    rw [hcomp, ← hpB]
    exact (he_cont _ hB).tendsto.comp ((continuous_fst.matrix_mulVec
      (continuous_subtype_val.comp continuous_snd)).tendsto p)
  -- Eventually `c a ≠ 0`, since the limit `B` is nonzero; then `e (c a • C a (x a)) = C a • x a`.
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp at hB
  have hc : ∀ᶠ a in l, c a ≠ 0 := (hC.eventually_ne hB0).mono fun a ha h ↦ by simp [h] at ha
  refine (key.comp (hC.prodMk_nhds hx)).congr' ?_
  filter_upwards [hc] with a ha
  have hCx : (C a : Matrix n n K) *ᵥ (x a).rep ≠ 0 := by
    simpa [Units.smul_def] using (smul_ne_zero_iff_ne (C a)).2 (x a).rep_ne_zero
  dsimp only [Function.comp_apply]
  rw [smul_mulVec, he_smul _ _ ha]
  simp only [he, hCx, ↓reduceDIte]
  conv_rhs => rw [← mk_rep (x a), smul_mk]
  rfl

end Field

end Projectivization
