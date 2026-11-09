/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Map
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Module

/-!
# The Maslov index of loops of linear symplectic maps through their graphs

Let `E` be a complex inner product space, with its standard symplectic form `ω(x, y) = Im ⟪x, y⟫`.
A real-linear map `Ψ : E → E` preserving `ω` is a linear symplectic map. Its graph is a Lagrangian
subspace of `(E × E, -ω ⊕ ω)`, which is totally real for the complex structure `(-i) ⊕ i`. To read
it as a maximal totally real subspace of a complex space we use a **conjugation** `K` of `E`, a
real-linear automorphism anticommuting with `i`, such as coordinatewise conjugation on `ℂⁿ`: the
map `(u, w) ↦ (K u, w)` is complex linear from `(E, -i) × (E, i)` to `E × E`, and carries the
graph of `Ψ` to

`conjGraph K Ψ = {(K z, Ψ z) | z ∈ E}` (`TauCeti.conjGraph`).

Write `P = Ψ.complexLinearPart` for the complex-linear part of `Ψ`. The symplectic condition makes
`P` invertible (`ContinuousLinearMap.complexLinearPartEquiv`). The complex-linear automorphism
`(u, w) ↦ (u, Q u + P w)` of `E × E`, with `Q = (Ψ ∘ K⁻¹).complexLinearPart`, carries the
conjugate graph of the identity onto the conjugate graph of `Ψ` (`TauCeti.conjGraph_eq_map`). The
conjugate graph of the identity is maximal totally real, so a continuous loop `Ψ` of linear
symplectic maps gives a loop of maximal totally real subspaces `t ↦ conjGraph K (Ψ t)`
(`TauCeti.symplecticGraphLoop`), with frames given by these automorphisms. Its Maslov index is the
Maslov index of the symplectic loop, normalized as by Robbin and Salamon through the graph.

The main theorem computes it: if `det (P t) = |det (P t)| δ t` for a loop `δ` in the circle, then

`μ(t ↦ conjGraph K (Ψ t)) = 2 deg δ`

(`TauCeti.maslovIndex_symplecticGraphLoop`). The proof deforms the frame
`(u, w) ↦ (u, s Q u + P w)` to `s = 0`, where the loop is the conjugate graph of the identity moved
by the automorphisms `id × P t`. Consequences:

* the index does not depend on the conjugation
  (`TauCeti.maslovIndex_symplecticGraphLoop_congr_conj`);
* composing with a loop `U` of complex-linear maps on either side adds `2 deg (det U)`
  (`TauCeti.maslovIndex_symplecticGraphLoop_comp_left`,
  `TauCeti.maslovIndex_symplecticGraphLoop_comp_right`), which is how the index changes with a
  unitary trivialization;
* the full rotation `t ↦ e^{2πit}` of an `n`-dimensional space has index `2n`
  (`TauCeti.maslovIndex_symplecticGraphLoop_rotation`);
* homotopic loops of linear symplectic maps have the same index
  (`TauCeti.maslovIndex_symplecticGraphLoop_eq_of_homotopy`).

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Maslov index of symplectic paths through their graphs).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Maslov index of loops of symplectic matrices).
-/

public section

noncomputable section

open Module Real
open scoped InnerProductSpace unitInterval

namespace TauCeti

/-! ### The conjugate graph of a real-linear map -/

section Graph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **conjugate graph** `{(K z, Ψ z) | z ∈ E}` of a real-linear operator `Ψ` of a complex
normed space, for a real-linear automorphism `K`. When `K` is a conjugation, this is the graph of
`Ψ` in `(E, -i) × (E, i)`, read in `E × E` through `K` on the first factor. -/
def conjGraph (K : E ≃L[ℝ] E) (Ψ : E →L[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range ((K : E →ₗ[ℝ] E).prod (Ψ : E →ₗ[ℝ] E))

@[simp]
theorem mem_conjGraph {K : E ≃L[ℝ] E} {Ψ : E →L[ℝ] E} {x : E × E} :
    x ∈ conjGraph K Ψ ↔ ∃ z, (K z, Ψ z) = x := by
  simp [conjGraph]

variable {K : E ≃L[ℝ] E}

/-- An automorphism anticommuting with `i` has inverse anticommuting with `i`. -/
private theorem symm_apply_I_smul (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) (z : E) :
    K.symm (Complex.I • K z) = -(Complex.I • z) := by
  rw [K.symm_apply_eq, map_neg, hK, neg_neg]

/-- **The conjugate graph of the identity is maximal totally real.** For an automorphism `K`
anticommuting with `i`, the subspace `{(K z, z)}` of `E × E` is complementary to its image under
multiplication by `i`. -/
theorem isMaximalTotallyReal_conjGraph_id (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E) Complex.I).restrictScalars ℝ)
      (conjGraph K (ContinuousLinearMap.id ℝ E)) := by
  rw [isMaximalTotallyReal_iff]
  constructor
  · -- `(K z, z) = i (K w, w)` forces `K w = -K w`, so `w = 0`.
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨z, rfl⟩ := mem_conjGraph.1 hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    obtain ⟨w, rfl⟩ := mem_conjGraph.1 hy
    simp only [ContinuousLinearMap.coe_id', id_eq, LinearMap.coe_restrictScalars,
      LinearMap.lsmul_apply, Prod.smul_mk, Prod.mk.injEq] at hyx
    obtain ⟨h₁, rfl⟩ := hyx
    rw [hK] at h₁
    have hKw : K w = 0 := by
      have h₂ : (2 : ℂ) • (Complex.I • K w) = 0 := by
        rw [two_smul]
        nth_rw 1 [h₁]
        exact neg_add_cancel _
      simpa using h₂
    have hw0 : w = 0 := K.injective (by simpa using hKw)
    simp [hw0]
  · -- `(u, w)` is `(K a, a) + i (K b, b)` with `a = (w + K⁻¹ u) / 2`, `i b = (w - K⁻¹ u) / 2`.
    rw [codisjoint_iff, eq_top_iff]
    rintro ⟨u, w⟩ -
    have hII (v : E) : Complex.I • Complex.I • v = -v := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    set a : E := (2⁻¹ : ℝ) • (w + K.symm u)
    set b : E := -(Complex.I • ((2⁻¹ : ℝ) • (w - K.symm u)))
    refine Submodule.mem_sup.2 ⟨(K a, a), ⟨a, rfl⟩, Complex.I • (K b, b),
      ⟨(K b, b), ⟨b, rfl⟩, rfl⟩, ?_⟩
    have ha : K a = (2⁻¹ : ℝ) • (K w + u) := by
      simp only [a, map_smul, map_add, K.apply_symm_apply]
    have hb : K b = (2⁻¹ : ℝ) • (Complex.I • (K w - u)) := by
      simp only [b, map_neg, hK, neg_neg, map_smul, map_sub, K.apply_symm_apply]
      rw [smul_comm]
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, ha, hb]
    constructor
    · rw [smul_comm Complex.I (2⁻¹ : ℝ), hII]
      module
    · simp only [a, b, smul_neg, smul_comm Complex.I (2⁻¹ : ℝ), hII]
      module

/-- The conjugate graph of `Ψ` is the conjugate graph of the identity moved by the real-linear map
`(u, w) ↦ (u, Q u + P w)`, where `P` is the complex-linear part of `Ψ` and `Q` that of `Ψ ∘ K⁻¹`. -/
theorem conjGraph_eq_map (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    (Ψ : E →L[ℝ] E) :
    conjGraph K Ψ = (conjGraph K (ContinuousLinearMap.id ℝ E)).map
      ((LinearMap.fst ℝ E E).prod
        (((Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart.restrictScalars ℝ :
            E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E E +
          ((Ψ.complexLinearPart.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.snd ℝ E E)) := by
  -- `Q (K z) + P z = Ψ z`.
  have key (z : E) : (Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart (K z) +
      Ψ.complexLinearPart z = Ψ z := by
    simp only [ContinuousLinearMap.complexLinearPart_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, Function.comp_apply, K.symm_apply_apply]
    rw [symm_apply_I_smul hK, map_neg]
    module
  have hmap (z : E) : ((LinearMap.fst ℝ E E).prod
      (((Ψ.comp (K.symm : E →L[ℝ] E)).complexLinearPart.restrictScalars ℝ :
          E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E E +
        ((Ψ.complexLinearPart.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
          LinearMap.snd ℝ E E)) (K z, z) = (K z, Ψ z) :=
    Prod.ext rfl (key z)
  ext x
  rw [mem_conjGraph, Submodule.mem_map]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(K z, z), mem_conjGraph.2 ⟨z, by simp⟩, hmap z⟩
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_conjGraph.1 hy
    exact ⟨z, by simpa using (hmap z).symm⟩

end Graph

/-! ### Frames of conjugate graphs -/

section Frame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The complex-linear automorphism `(u, w) ↦ (u, Q u + P w)` of `E × E`. -/
private def skewFrame (Q : E →L[ℂ] E) (P : E ≃L[ℂ] E) : (E × E) ≃L[ℂ] (E × E) :=
  (LinearEquiv.skewProd (LinearEquiv.refl ℂ E) P.toLinearEquiv
    (Q : E →ₗ[ℂ] E)).toContinuousLinearEquiv

private theorem skewFrame_apply (Q : E →L[ℂ] E) (P : E ≃L[ℂ] E) (x : E × E) :
    skewFrame Q P x = (x.1, P x.2 + Q x.1) :=
  (rfl)

private theorem coe_skewFrame (Q : E →L[ℂ] E) (P : E ≃L[ℂ] E) :
    (skewFrame Q P : E × E →L[ℂ] E × E) =
      (ContinuousLinearMap.fst ℂ E E).prod
        ((P : E →L[ℂ] E).comp (ContinuousLinearMap.snd ℂ E E) +
          Q.comp (ContinuousLinearMap.fst ℂ E E)) := by
  ext x <;> simp [skewFrame_apply]

/-- The frames `(u, w) ↦ (u, Q u + P w)` depend continuously on `Q` and `P`. -/
private theorem continuous_skewFrame {X : Type*} [TopologicalSpace X] {Q : X → E →L[ℂ] E}
    {P : X → E ≃L[ℂ] E} (hQ : Continuous Q) (hP : Continuous fun x => (P x : E →L[ℂ] E)) :
    Continuous fun x => (skewFrame (Q x) (P x) : E × E →L[ℂ] E × E) := by
  simp_rw [coe_skewFrame]
  exact (ContinuousLinearMap.prodL ℂ).continuous.comp
    (continuous_const.prodMk ((hP.clm_comp continuous_const).add (hQ.clm_comp continuous_const)))

/-- The frame `(u, w) ↦ (u, Q u + P w)` restricts on real scalars to the map of
`TauCeti.conjGraph_eq_map`. -/
private theorem restrictScalars_skewFrame (Q : E →L[ℂ] E) (P : E ≃L[ℂ] E) :
    (((skewFrame Q P).toLinearEquiv : E × E →ₗ[ℂ] E × E).restrictScalars ℝ) =
      (LinearMap.fst ℝ E E).prod
        (((Q.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ LinearMap.fst ℝ E E +
          (((P : E →L[ℂ] E).restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.snd ℝ E E) := by
  ext x <;> simp [skewFrame_apply, add_comm]

end Frame

/-! ### The graph loop of a loop of linear symplectic maps -/

section Loop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {K : E ≃L[ℝ] E}

/-- The frame of the conjugate graph of a parametrized linear symplectic map. -/
private def graphFrame (K : E ≃L[ℝ] E) {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (c : ℂ) (x : X) :
    (E × E) ≃L[ℂ] (E × E) :=
  skewFrame (c • ((Ψ x).comp (K.symm : E →L[ℝ] E)).complexLinearPart)
    ((Ψ x).complexLinearPartEquiv (hsymp x))

private theorem graphFrame_apply {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (c : ℂ) (x : X) (p : E × E) :
    graphFrame K Ψ hsymp c x p =
      (p.1, (Ψ x).complexLinearPart p.2 +
        c • ((Ψ x).comp (K.symm : E →L[ℝ] E)).complexLinearPart p.1) := by
  rw [graphFrame, skewFrame_apply, ContinuousLinearMap.complexLinearPartEquiv_apply,
    smul_apply]

private theorem continuous_graphFrame {X : Type*} [TopologicalSpace X] {Ψ : X → E →L[ℝ] E}
    (hΨ : Continuous Ψ) (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) {c : X → ℂ}
    (hc : Continuous c) :
    Continuous fun x => (graphFrame K Ψ hsymp (c x) x : E × E →L[ℂ] E × E) := by
  refine continuous_skewFrame (hc.smul (ContinuousLinearMap.continuous_complexLinearPart.comp
    (hΨ.clm_comp continuous_const))) ?_
  simp only [ContinuousLinearMap.coe_complexLinearPartEquiv]
  exact ContinuousLinearMap.continuous_complexLinearPart.comp hΨ

/-- The frame with `c = 1` carries the conjugate graph of the identity onto that of `Ψ x`. -/
private theorem map_graphFrame_one (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (x : X) :
    (conjGraph K (ContinuousLinearMap.id ℝ E)).map
        (((graphFrame K Ψ hsymp 1 x).toLinearEquiv : E × E →ₗ[ℂ] E × E).restrictScalars ℝ) =
      conjGraph K (Ψ x) := by
  rw [graphFrame, restrictScalars_skewFrame, conjGraph_eq_map hK (Ψ x), one_smul,
    ContinuousLinearMap.coe_complexLinearPartEquiv]

/-- The frame with `c = 0` is `id × P`, with `P` the complex-linear part. -/
private theorem graphFrame_zero {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (x : X) :
    graphFrame K Ψ hsymp 0 x =
      (ContinuousLinearEquiv.refl ℂ E).prodCongr ((Ψ x).complexLinearPartEquiv (hsymp x)) := by
  ext p <;> simp [graphFrame_apply]

/-- The frames of a closed loop agree at its two ends. -/
private theorem graphFrame_zero_eq_one {Ψ : I → E →L[ℝ] E}
    (hsymp : ∀ t u v, (⟪Ψ t u, Ψ t v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) (c : ℂ) :
    graphFrame K Ψ hsymp c 0 = graphFrame K Ψ hsymp c 1 := by
  ext p <;> simp [graphFrame_apply, hΨ01]

/-- The **graph loop** of a continuous loop `Ψ` of real-linear maps preserving the symplectic form
`Im ⟪·, ·⟫`: the loop `t ↦ conjGraph K (Ψ t) = {(K z, Ψ t z)}` of maximal totally real subspaces of
`E × E`, for a conjugation `K`. Its Maslov index is the Maslov index of the symplectic loop. -/
def symplecticGraphLoop (K : E ≃L[ℝ] E) (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) :
    TotallyRealLoop (E × E) where
  toFun t := conjGraph K (Ψ t)
  exists_frame := ⟨conjGraph K (ContinuousLinearMap.id ℝ E), isMaximalTotallyReal_conjGraph_id hK,
    graphFrame K Ψ hsymp 1, continuous_graphFrame hΨ hsymp continuous_const,
    fun t => (map_graphFrame_one hK Ψ hsymp t).symm⟩
  toFun_zero_eq_toFun_one := by rw [hΨ01]

@[simp]
theorem symplecticGraphLoop_apply (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) (t : I) :
    symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01 t = conjGraph K (Ψ t) :=
  (rfl)

/-- **The Maslov index of a loop of linear symplectic maps.** If the determinants of the
complex-linear parts are `det (P t) = |det (P t)| δ t` for a loop `δ` in the circle, the graph loop
has Maslov index `2 deg δ`. -/
theorem maslovIndex_symplecticGraphLoop (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1)
    {x : Circle} (δ : Path x x)
    (hδ : ∀ t, LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) =
      ‖LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E)‖ * δ t) :
    (symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01).maslovIndex = 2 * Circle.degree δ := by
  have hL₀ := isMaximalTotallyReal_conjGraph_id hK
  -- The loop `t ↦ (id × P t) L₀`, where `L₀` is the conjugate graph of the identity.
  set B : I → (E × E) ≃L[ℂ] (E × E) := graphFrame K Ψ hsymp 0
  have hB : Continuous fun t => (B t : E × E →L[ℂ] E × E) :=
    continuous_graphFrame hΨ hsymp continuous_const
  have hB01 : B 0 = B 1 := graphFrame_zero_eq_one hsymp hΨ01 0
  have hΛ : ((TotallyRealLoop.const hL₀).map B hB hB01).maslovIndex = 2 * Circle.degree δ := by
    rw [TotallyRealLoop.maslovIndex_map _ B hB hB01 δ fun t => ?_,
      TotallyRealLoop.maslovIndex_const, zero_add]
    have hdet : LinearMap.det ((B t).toLinearEquiv : E × E →ₗ[ℂ] E × E) =
        LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) := by
      have : ((B t).toLinearEquiv : E × E →ₗ[ℂ] E × E) =
          LinearMap.prodMap LinearMap.id ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) := by
        ext p <;> simp [B, graphFrame_apply]
      rw [this, LinearMap.det_prodMap, LinearMap.det_id, one_mul]
    rw [hdet]
    exact hδ t
  -- Deform the frame `(u, w) ↦ (u, s Q u + P w)` from `s = 0` to `s = 1`.
  rw [← hΛ]
  refine (TotallyRealLoop.maslovIndex_eq_of_homotopy _ _ hL₀
    (fun p => graphFrame K Ψ hsymp ((p.1 : ℝ) : ℂ) p.2)
    (continuous_graphFrame (hΨ.comp continuous_snd) (fun p => hsymp p.2)
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)))
    (fun t => ?_) (fun t => ?_) (fun s => ?_)).symm
  · simp [B]
  · simpa using (map_graphFrame_one hK Ψ hsymp t).symm
  · rw [graphFrame_zero_eq_one hsymp hΨ01]

/-- The complex-linear parts of a loop of linear symplectic maps have a loop of normalized
determinants. -/
private theorem exists_path_det_complexLinearPart {Ψ : I → E →L[ℝ] E} (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) :
    ∃ (x : Circle) (δ : Path x x), ∀ t,
      LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) =
        ‖LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E)‖ * δ t :=
  exists_path_det_eq_norm_mul (ContinuousLinearMap.continuous_complexLinearPart.comp hΨ)
    (by rw [hΨ01]) fun t => by
      have h := ((Ψ t).complexLinearPartEquiv (hsymp t)).toLinearEquiv.isUnit_det'.ne_zero
      rwa [show (((Ψ t).complexLinearPartEquiv (hsymp t)).toLinearEquiv : E →ₗ[ℂ] E) =
        ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) from LinearMap.ext fun z => by simp] at h

/-- **The Maslov index of the graph loop does not depend on the conjugation.** -/
theorem maslovIndex_symplecticGraphLoop_congr_conj
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) {K' : E ≃L[ℝ] E}
    (hK' : ∀ z, K' (Complex.I • z) = -(Complex.I • K' z)) (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) :
    (symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01).maslovIndex =
      (symplecticGraphLoop K' hK' Ψ hΨ hsymp hΨ01).maslovIndex := by
  obtain ⟨x, δ, hδ⟩ := exists_path_det_complexLinearPart hΨ hsymp hΨ01
  rw [maslovIndex_symplecticGraphLoop hK Ψ hΨ hsymp hΨ01 δ hδ,
    maslovIndex_symplecticGraphLoop hK' Ψ hΨ hsymp hΨ01 δ hδ]

/-- **Composing on the left with a loop of complex-linear maps.** If `U t ∘ Ψ t` is again a loop
of linear symplectic maps and `det (U t) = |det (U t)| δ t`, the Maslov index of the graph loop
increases by `2 deg δ`. -/
theorem maslovIndex_symplecticGraphLoop_comp_left
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1)
    (U : I → E →L[ℂ] E)
    (hUΨ : Continuous fun t => ((U t).restrictScalars ℝ).comp (Ψ t))
    (hsympU : ∀ t x y,
      (⟪((U t).restrictScalars ℝ).comp (Ψ t) x, ((U t).restrictScalars ℝ).comp (Ψ t) y⟫_ℂ).im =
        (⟪x, y⟫_ℂ).im)
    (hUΨ01 : ((U 0).restrictScalars ℝ).comp (Ψ 0) = ((U 1).restrictScalars ℝ).comp (Ψ 1))
    {y : Circle} (δ : Path y y)
    (hδ : ∀ t, LinearMap.det (U t : E →ₗ[ℂ] E) = ‖LinearMap.det (U t : E →ₗ[ℂ] E)‖ * δ t) :
    (symplecticGraphLoop K hK _ hUΨ hsympU hUΨ01).maslovIndex =
      (symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01).maslovIndex + 2 * Circle.degree δ := by
  obtain ⟨x, ε, hε⟩ := exists_path_det_complexLinearPart hΨ hsymp hΨ01
  rw [maslovIndex_symplecticGraphLoop hK Ψ hΨ hsymp hΨ01 ε hε,
    maslovIndex_symplecticGraphLoop hK _ hUΨ hsympU hUΨ01 (δ.mul ε) fun t => ?_,
    Circle.degree_mul]
  · ring
  · rw [ContinuousLinearMap.complexLinearPart_restrictScalars_comp,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, Path.mul_apply, Circle.coe_mul,
      norm_mul, Complex.ofReal_mul]
    nth_rw 1 [hδ t, hε t]
    ring

/-- **Composing on the right with a loop of complex-linear maps.** If `Ψ t ∘ U t` is again a loop
of linear symplectic maps and `det (U t) = |det (U t)| δ t`, the Maslov index of the graph loop
increases by `2 deg δ`. -/
theorem maslovIndex_symplecticGraphLoop_comp_right
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1)
    (U : I → E →L[ℂ] E)
    (hΨU : Continuous fun t => (Ψ t).comp ((U t).restrictScalars ℝ))
    (hsympU : ∀ t x y,
      (⟪(Ψ t).comp ((U t).restrictScalars ℝ) x, (Ψ t).comp ((U t).restrictScalars ℝ) y⟫_ℂ).im =
        (⟪x, y⟫_ℂ).im)
    (hΨU01 : (Ψ 0).comp ((U 0).restrictScalars ℝ) = (Ψ 1).comp ((U 1).restrictScalars ℝ))
    {y : Circle} (δ : Path y y)
    (hδ : ∀ t, LinearMap.det (U t : E →ₗ[ℂ] E) = ‖LinearMap.det (U t : E →ₗ[ℂ] E)‖ * δ t) :
    (symplecticGraphLoop K hK _ hΨU hsympU hΨU01).maslovIndex =
      (symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01).maslovIndex + 2 * Circle.degree δ := by
  obtain ⟨x, ε, hε⟩ := exists_path_det_complexLinearPart hΨ hsymp hΨ01
  rw [maslovIndex_symplecticGraphLoop hK Ψ hΨ hsymp hΨ01 ε hε,
    maslovIndex_symplecticGraphLoop hK _ hΨU hsympU hΨU01 (ε.mul δ) fun t => ?_,
    Circle.degree_mul]
  · ring
  · rw [ContinuousLinearMap.complexLinearPart_comp_restrictScalars,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, Path.mul_apply, Circle.coe_mul,
      norm_mul, Complex.ofReal_mul]
    nth_rw 1 [hε t, hδ t]
    ring

/-- **Normalization.** The full rotation `t ↦ e^{2πit}` of a complex inner product space of
dimension `n` has graph loop of Maslov index `2n`. -/
theorem maslovIndex_symplecticGraphLoop_rotation
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) (Ψ : I → E →L[ℝ] E) (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1)
    (hrot : ∀ t, Ψ t =
      (Complex.exp ((2 * π * t : ℝ) * Complex.I) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) :
    (symplecticGraphLoop K hK Ψ hΨ hsymp hΨ01).maslovIndex = 2 * finrank ℂ E := by
  -- The determinant `e^{2πint}` of the complex-linear part winds `n` times.
  let δ : Path (1 : Circle) 1 :=
    { toFun := fun t => Circle.exp (finrank ℂ E * (2 * π * t))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hδ : Circle.degree δ = finrank ℂ E :=
    Circle.degree_eq_of_sub_eq δ (θ := fun t => finrank ℂ E * (2 * π * t)) (by fun_prop)
      (fun _ => rfl) (by simp)
  rw [maslovIndex_symplecticGraphLoop hK Ψ hΨ hsymp hΨ01 δ fun t => ?_, hδ]
  have hdet : LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) =
      Complex.exp ((finrank ℂ E * (2 * π * t) : ℝ) * Complex.I) := by
    rw [hrot t, ContinuousLinearMap.complexLinearPart_restrictScalars,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id, LinearMap.det_smul,
      LinearMap.det_id, mul_one, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hdet, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul]
  exact (Circle.coe_exp _).symm

/-- **Homotopy invariance.** Homotopic loops of linear symplectic maps, through closed loops of
linear symplectic maps, have graph loops of the same Maslov index. -/
theorem maslovIndex_symplecticGraphLoop_eq_of_homotopy
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) (Ψ : I × I → E →L[ℝ] E)
    (hΨ : Continuous Ψ) (hsymp : ∀ p x y, (⟪Ψ p x, Ψ p y⟫_ℂ).im = (⟪x, y⟫_ℂ).im)
    (hΨ01 : ∀ s, Ψ (s, 0) = Ψ (s, 1)) :
    (symplecticGraphLoop K hK (fun t => Ψ (0, t)) (by fun_prop) (fun t => hsymp (0, t))
        (hΨ01 0)).maslovIndex =
      (symplecticGraphLoop K hK (fun t => Ψ (1, t)) (by fun_prop) (fun t => hsymp (1, t))
        (hΨ01 1)).maslovIndex := by
  refine TotallyRealLoop.maslovIndex_eq_of_homotopy _ _ (isMaximalTotallyReal_conjGraph_id hK)
    (graphFrame K Ψ hsymp 1) (continuous_graphFrame hΨ hsymp continuous_const)
    (fun t => (map_graphFrame_one hK Ψ hsymp (0, t)).symm)
    (fun t => (map_graphFrame_one hK Ψ hsymp (1, t)).symm) fun s => ?_
  rw [map_graphFrame_one hK Ψ hsymp, map_graphFrame_one hK Ψ hsymp, hΨ01]

end Loop

end TauCeti
