/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.DeterminantLoop
public import TauCeti.Analysis.Normed.Operator.RotationLoop
public import TauCeti.LinearAlgebra.TotallyReal.Graph
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Map
import Mathlib.Analysis.Normed.Module.FiniteDimension

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
* the full rotation `t ↦ e^{2πit}` of an `n`-dimensional space (`TauCeti.rotationLoop`) has
  index `2n` (`TauCeti.maslovIndex_symplecticGraphLoop_rotationLoop`);
* homotopic loops of linear symplectic maps have the same index
  (`TauCeti.maslovIndex_symplecticGraphLoop_eq_of_homotopy`).

A loop `δ` as in the main theorem always exists
(`TauCeti.exists_path_det_complexLinearPart`).

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

/-! ### The graph loop of a loop of linear symplectic maps -/

section Loop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {K : E ≃L[ℝ] E}

/-- The frame of the conjugate graph of a parametrized linear symplectic map. -/
private def graphFrame (K : E ≃L[ℝ] E) {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (c : ℂ) (x : X) :
    (E × E) ≃L[ℂ] (E × E) :=
  (ContinuousLinearEquiv.refl ℂ E).skewProd ((Ψ x).complexLinearPartEquiv (hsymp x))
    (c • ((Ψ x).comp (K.symm : E →L[ℝ] E)).complexLinearPart)

private theorem graphFrame_apply {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (c : ℂ) (x : X) (p : E × E) :
    graphFrame K Ψ hsymp c x p =
      (p.1, (Ψ x).complexLinearPart p.2 +
        c • ((Ψ x).comp (K.symm : E →L[ℝ] E)).complexLinearPart p.1) := by
  rw [graphFrame, ContinuousLinearEquiv.skewProd_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearMap.complexLinearPartEquiv_apply, smul_apply]

private theorem continuous_graphFrame {X : Type*} [TopologicalSpace X] {Ψ : X → E →L[ℝ] E}
    (hΨ : Continuous Ψ) (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) {c : X → ℂ}
    (hc : Continuous c) :
    Continuous fun x => (graphFrame K Ψ hsymp (c x) x : E × E →L[ℂ] E × E) := by
  -- The frame is the block operator `(u, w) ↦ (u, P w + c Q u)`.
  have h (x : X) : (graphFrame K Ψ hsymp (c x) x : E × E →L[ℂ] E × E) =
      (ContinuousLinearMap.fst ℂ E E).prod
        ((Ψ x).complexLinearPart.comp (ContinuousLinearMap.snd ℂ E E) +
          (c x • ((Ψ x).comp (K.symm : E →L[ℝ] E)).complexLinearPart).comp
            (ContinuousLinearMap.fst ℂ E E)) := by
    ext p <;> simp [graphFrame_apply]
  simp_rw [h]
  exact (ContinuousLinearMap.prodL ℂ).continuous.comp (continuous_const.prodMk
    (((ContinuousLinearMap.continuous_complexLinearPart.comp hΨ).clm_comp continuous_const).add
      ((hc.smul (ContinuousLinearMap.continuous_complexLinearPart.comp
        (hΨ.clm_comp continuous_const))).clm_comp continuous_const)))

/-- The frame with `c = 1` carries the conjugate graph of the identity onto that of `Ψ x`. -/
private theorem map_graphFrame_one (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z))
    {X : Type*} (Ψ : X → E →L[ℝ] E)
    (hsymp : ∀ x u v, (⟪Ψ x u, Ψ x v⟫_ℂ).im = (⟪u, v⟫_ℂ).im) (x : X) :
    (conjGraph K (ContinuousLinearMap.id ℝ E)).map
        (((graphFrame K Ψ hsymp 1 x).toLinearEquiv : E × E →ₗ[ℂ] E × E).restrictScalars ℝ) =
      conjGraph K (Ψ x) := by
  rw [conjGraph_eq_map hK (Ψ x)]
  congr 1
  ext p <;> simp [graphFrame_apply, add_comm]

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

/-- The complex-linear parts of a loop of linear symplectic maps have a loop `δ` of normalized
determinants, `det (P t) = |det (P t)| δ t`, as asked for by
`TauCeti.maslovIndex_symplecticGraphLoop`. -/
theorem exists_path_det_complexLinearPart {Ψ : I → E →L[ℝ] E} (hΨ : Continuous Ψ)
    (hsymp : ∀ t x y, (⟪Ψ t x, Ψ t y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) (hΨ01 : Ψ 0 = Ψ 1) :
    ∃ (x : Circle) (δ : Path x x), ∀ t,
      LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E) =
        ‖LinearMap.det ((Ψ t).complexLinearPart : E →ₗ[ℂ] E)‖ * δ t :=
  exists_path_det_eq_norm_mul (ContinuousLinearMap.continuous_complexLinearPart.comp hΨ)
    (by rw [hΨ01]) fun t => ContinuousLinearMap.det_complexLinearPart_ne_zero (hsymp t)

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
theorem maslovIndex_symplecticGraphLoop_rotationLoop
    (hK : ∀ z, K (Complex.I • z) = -(Complex.I • K z)) :
    (symplecticGraphLoop K hK (rotationLoop E) (continuous_rotationLoop E)
      (fun t x y => by rw [inner_rotationLoop_apply]) (rotationLoop_zero_eq_one E)).maslovIndex =
      2 * finrank ℂ E := by
  -- The determinant `e^{2πint}` of the complex-linear part winds `n` times.
  let δ : Path (1 : Circle) 1 :=
    { toFun := fun t => Circle.exp (finrank ℂ E * (2 * π * t))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hδ : Circle.degree δ = finrank ℂ E :=
    Circle.degree_eq_of_sub_eq δ (θ := fun t => finrank ℂ E * (2 * π * t)) (by fun_prop)
      (fun _ => rfl) (by simp)
  rw [maslovIndex_symplecticGraphLoop hK _ _ _ _ δ fun t => ?_, hδ]
  have hdet : LinearMap.det ((rotationLoop E t).complexLinearPart : E →ₗ[ℂ] E) =
      Complex.exp ((finrank ℂ E * (2 * π * t) : ℝ) * Complex.I) := by
    have hrot : rotationLoop E t = (Complex.exp ((2 * π * t : ℝ) * Complex.I) •
        ContinuousLinearMap.id ℂ E).restrictScalars ℝ := by
      ext z
      simp
    rw [hrot, ContinuousLinearMap.complexLinearPart_restrictScalars,
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
