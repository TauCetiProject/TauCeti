/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
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

A sequence leaving every compact subset of `PSL(n, K)`, over a proper nontrivially normed field,
has lifts to `SL(n, K)` with unbounded norms. Normalized by entries of largest norm, a subsequence
of these lifts converges to a nonzero singular matrix `B`. In general, when rescaled invertible
matrices converge to a possibly singular `B`, their action on lines converges to `[v] ↦ [B v]`
away from the kernel of `B`.

## Main results

* `Projectivization.instContinuousSMul`: a jointly continuous linear action on `V` induces a jointly
  continuous action on `ℙ K V`; for instance by `GL n K` or `SL(n, K)` on `ℙ K (n → K)`.
* `Projectivization.instContinuousSMulPSL`: `PSL(n, K)` acts jointly continuously on
  `ℙ K (n → K)`.
* `Projectivization.tendsto_mk_mulVec_rep`: the line `[D y]` depends continuously on the matrix
  `D` and the line `y` where `D` does not kill `y`.
* `Projectivization.tendsto_smul_of_tendsto_smul_coe`: invertible matrices converging projectively
  to a possibly singular matrix `B` act, in the limit, as `[v] ↦ [B v]` away from the kernel of `B`.
* `Matrix.ProjectiveSpecialLinearGroup.tendsto_norm_of_tendsto_cocompact`: lifts of an escaping
  sequence in `PSL(n, K)` have unbounded norms.
* `Matrix.ProjectiveSpecialLinearGroup.exists_tendsto_inv_smul_of_tendsto_cocompact`: normalized
  lifts of an escaping sequence in `PSL(n, K)` subconverge to a nonzero singular matrix.
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

omit [DecidableEq n] in
open Filter Matrix in
/-- The line `[D y]` depends continuously on a matrix `D` and a line `y` that `D` does not kill:
if `D a → B` and `y a → x₀` with `B x₀ ≠ 0`, then `[D a (y a)] → [B x₀]`. The map from pairs of a
matrix and a nonzero vector to pairs of a matrix and a line is open, and on the former the map is
`(D, w) ↦ [D w]`, continuous where `D w ≠ 0`. -/
theorem tendsto_mk_mulVec_rep [T1Space K] {α : Type*} {l : Filter α} {D : α → Matrix n n K}
    {B : Matrix n n K} {y : α → ℙ K (n → K)} {x₀ : ℙ K (n → K)} (hD : Tendsto D l (𝓝 B))
    (hy : Tendsto y l (𝓝 x₀)) (hDy : ∀ a, D a *ᵥ (y a).rep ≠ 0) (hB : B *ᵥ x₀.rep ≠ 0) :
    Tendsto (fun a ↦ mk K (D a *ᵥ (y a).rep) (hDy a)) l (𝓝 (mk K (B *ᵥ x₀.rep) hB)) := by
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
  -- On pairs of a matrix and a line the map is `(D, y) ↦ e (D y)`, continuous at `(B, x₀)`
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
  exact (key.comp (hD.prodMk_nhds hy)).congr fun a ↦ by simp [he, hDy a]

open Filter Matrix in
/-- **Limits of projectively convergent matrices.** Let `C a` be invertible matrices which
converge projectively to a possibly singular matrix `B`: for some scalars `c a`, the matrices
`c a • C a` converge to `B`. Then the projective transformations `C a` converge to `[v] ↦ [B v]`
away from the kernel of `B`: if lines `x a` converge to a line `x₀` not killed by `B`, the lines
`C a • x a` converge to the line of `B x₀`. When `B` is invertible this is the continuity of the
action; when `B` is singular the limit map `[v] ↦ [B v]` factors through the quotient by the
kernel of `B`, and in particular it is constant when `B` has rank one. -/
theorem tendsto_smul_of_tendsto_smul_coe [T1Space K] {α : Type*} {l : Filter α}
    {C : α → GL n K} {c : α → K} {B : Matrix n n K} {x : α → ℙ K (n → K)} {x₀ : ℙ K (n → K)}
    (hC : Tendsto (fun a ↦ c a • (C a : Matrix n n K)) l (𝓝 B)) (hx : Tendsto x l (𝓝 x₀))
    (hB : B *ᵥ x₀.rep ≠ 0) :
    Tendsto (fun a ↦ C a • x a) l (𝓝 (mk K (B *ᵥ x₀.rep) hB)) := by
  classical
  -- Eventually `c a ≠ 0`, since the limit `B` is nonzero, so `c a` may be replaced by a scalar
  -- `c' a` which never vanishes.
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp at hB
  set c' : α → K := fun a ↦ if c a = 0 then 1 else c a with hc'
  have hc'0 : ∀ a, c' a ≠ 0 := fun a ↦ by by_cases h : c a = 0 <;> simp [hc', h]
  have hC' : Tendsto (fun a ↦ c' a • (C a : Matrix n n K)) l (𝓝 B) := by
    refine hC.congr' ?_
    filter_upwards [hC.eventually_ne hB0] with a ha
    have hca : c a ≠ 0 := fun h ↦ ha (by simp [h])
    simp [hc', hca]
  have hCx : ∀ a, (c' a • (C a : Matrix n n K)) *ᵥ (x a).rep ≠ 0 := fun a ↦ by
    rw [smul_mulVec]
    refine smul_ne_zero (hc'0 a) ?_
    simpa [Units.smul_def] using (smul_ne_zero_iff_ne (C a)).2 (x a).rep_ne_zero
  -- The line of `c' a • C a (x a)` is `C a • x a`.
  refine (tendsto_mk_mulVec_rep hC' hx hCx hB).congr fun a ↦ ?_
  conv_rhs => rw [← mk_rep (x a), smul_mk]
  exact (mk_eq_mk_iff' K _ _ _ _).2 ⟨c' a, by simp [Units.smul_def, smul_mulVec]⟩

end Field

end Projectivization

namespace Matrix.ProjectiveSpecialLinearGroup

/-! ### Escaping sequences of projective transformations -/

open Filter

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- With the entrywise sup norm, the square matrices over a proper field form a proper space. -/
local instance : ProperSpace (Matrix n n 𝕜) := inferInstanceAs (ProperSpace (n → n → 𝕜))

/-- Lifts to `SL(n, 𝕜)` of elements of `PSL(n, 𝕜)` escaping to infinity have unbounded norms. -/
theorem tendsto_norm_of_tendsto_cocompact {α : Type*} {l : Filter α}
    {g : α → ProjectiveSpecialLinearGroup n 𝕜}
    (hg : Tendsto g l (cocompact (ProjectiveSpecialLinearGroup n 𝕜)))
    {A : α → SpecialLinearGroup n 𝕜} (hA : ∀ a, (A a : ProjectiveSpecialLinearGroup n 𝕜) = g a) :
    Tendsto (fun a ↦ ‖(A a : Matrix n n 𝕜)‖) l atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  -- The matrices of determinant one and norm at most `R` form a compact subset of `SL(n, 𝕜)`.
  have hK : IsCompact
      ((QuotientGroup.mk : SpecialLinearGroup n 𝕜 → ProjectiveSpecialLinearGroup n 𝕜) ''
        (((↑) : SpecialLinearGroup n 𝕜 → Matrix n n 𝕜) ⁻¹' Metric.closedBall 0 R)) :=
    (SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (isCompact_closedBall 0 R)).image
      (QuotientGroup.continuous_mk (G := SpecialLinearGroup n 𝕜))
  filter_upwards [hg.eventually hK.compl_mem_cocompact] with a ha
  by_contra! hlt
  exact ha ⟨A a, mem_closedBall_zero_iff.2 hlt.le, hA a⟩

/-- **Escaping sequences converge projectively to singular matrices.** Lifts `A k` to `SL(n, 𝕜)`
of a sequence of elements of `PSL(n, 𝕜)` escaping to infinity, divided by suitable scalars `m k`,
have a subsequence converging to a nonzero singular matrix. The scalar `m k` is an entry of `A k`
of largest norm, so that `(m k)⁻¹ • A k` has norm one and determinant `(m k)⁻ⁿ`, which tends to
zero. Then `Projectivization.tendsto_smul_of_tendsto_smul_coe` describes the limit of the action
on `ℙ 𝕜 (n → 𝕜)`. -/
theorem exists_tendsto_inv_smul_of_tendsto_cocompact [Nonempty n]
    {g : ℕ → ProjectiveSpecialLinearGroup n 𝕜}
    (hg : Tendsto g atTop (cocompact (ProjectiveSpecialLinearGroup n 𝕜)))
    {A : ℕ → SpecialLinearGroup n 𝕜} (hA : ∀ k, (A k : ProjectiveSpecialLinearGroup n 𝕜) = g k) :
    ∃ (m : ℕ → 𝕜) (φ : ℕ → ℕ) (B : Matrix n n 𝕜), StrictMono φ ∧ B ≠ 0 ∧ B.det = 0 ∧
      Tendsto (fun k ↦ (m (φ k))⁻¹ • (A (φ k) : Matrix n n 𝕜)) atTop (𝓝 B) := by
  have hnorm := tendsto_norm_of_tendsto_cocompact hg hA
  choose p hp using fun k ↦ Finite.exists_max fun p : n × n ↦
    ‖(A k : Matrix n n 𝕜) p.1 p.2‖
  set m : ℕ → 𝕜 := fun k ↦ (A k : Matrix n n 𝕜) (p k).1 (p k).2
  have hm_norm : ∀ k, ‖m k‖ = ‖(A k : Matrix n n 𝕜)‖ := fun k ↦
    le_antisymm (norm_apply_le_norm _) <|
      (norm_le_iff (norm_nonneg _)).2 fun i j ↦ hp k (i, j)
  have hm0 : ∀ k, m k ≠ 0 := fun k ↦ by
    rw [← norm_ne_zero_iff, hm_norm, norm_ne_zero_iff]
    exact fun h ↦ by simpa [h] using (A k).2
  set C : ℕ → Matrix n n 𝕜 := fun k ↦ (m k)⁻¹ • (A k : Matrix n n 𝕜) with hC
  have hC_norm : ∀ k, ‖C k‖ = 1 := fun k ↦ by
    rw [hC, norm_smul, norm_inv, hm_norm, inv_mul_cancel₀]
    rw [← hm_norm, norm_ne_zero_iff]
    exact hm0 k
  obtain ⟨B, -, φ, hφ, hCB⟩ :=
    (isCompact_closedBall (0 : Matrix n n 𝕜) 1).tendsto_subseq (x := C)
      fun k ↦ by simp [hC_norm]
  refine ⟨m, φ, B, hφ, ?_, ?_, hCB⟩
  · have hB1 : ‖B‖ = 1 := tendsto_nhds_unique ((continuous_norm.tendsto B).comp hCB)
      (by simp [Function.comp_def, hC_norm])
    rintro rfl
    simp at hB1
  · refine tendsto_nhds_unique ((continuous_id.matrix_det.tendsto B).comp hCB) ?_
    have hdetC : ∀ k, (C k).det = (m k)⁻¹ ^ Fintype.card n := fun k ↦ by
      simp [hC, (A k).2]
    simp only [Function.comp_def, id_eq, hdetC]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [hm_norm, Fintype.card_ne_zero] using ((tendsto_inv_atTop_zero.comp
      (hnorm.comp hφ.tendsto_atTop)).pow (Fintype.card n))

end Matrix.ProjectiveSpecialLinearGroup
