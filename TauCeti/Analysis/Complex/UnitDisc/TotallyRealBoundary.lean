/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert
public import TauCeti.LinearAlgebra.TotallyReal.Complex

/-!
# The disc problem with a constant maximal totally real boundary condition

Let `E` be a finite-dimensional complex normed space and `L ⊆ E` a maximal totally real real
subspace, for instance a Lagrangian subspace of `ℂⁿ` for its standard symplectic form. This file
treats the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc for maps `u : ℂ → E` with
the constant boundary condition `u(w) ∈ L` for `‖w‖ = 1`.

This is the linearized problem at a constant holomorphic disc: when `u` is the constant disc at a
point `x` of a totally real submanifold, the linearization of the Cauchy–Riemann section along `u`
is `∂/∂(conj z)` acting on vector fields `ξ : ℂ → E` with `ξ(w)` in the tangent space `L = T_x`
along the boundary. Its kernel, its surjectivity and evaluation at a boundary marked point are
the endpoint computation in the classical argument of Gromov that a compact Lagrangian of `ℂⁿ`
bounds a nonconstant holomorphic disc.

A real basis of `L` is a complex basis of `E` (`TauCeti.IsMaximalTotallyReal.complexBasis`), and
`L` consists of the vectors with real coordinates in it
(`TauCeti.IsMaximalTotallyReal.mem_iff_forall_complexBasis_repr_im_eq_zero`). In these
coordinates the problem splits into `dim_ℂ E` copies of the rank one problem with real boundary
values, the rotating-line problem of `TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary` of
Maslov index `0`. Hence:

* **Kernel.** A map holomorphic on the open disc, continuous on its closure and sending the unit
  circle into `L` is constant on the closed disc (`DiffContOnCl.eqOn_const_of_mapsTo_sphere`). So
  the kernel `TauCeti.unitDiscTotallyRealKernel L` consists of the constants in `L`, and
  evaluation at any point of the closed disc identifies it with `L`
  (`TauCeti.unitDiscTotallyRealKernelEquiv`). Its real dimension is `dim_ℂ E`
  (`TauCeti.finrank_unitDiscTotallyRealKernel`), the Riemann–Roch index `n χ(D) + μ` for rank
  `n = dim_ℂ E`, Euler characteristic `χ(D) = 1` and Maslov index `μ = 0`.
* **Surjectivity.** For compactly supported `C²` data `f : ℂ → E` there is a solution of
  `∂u/∂(conj z) = f` on the open disc, continuous on the closed disc, with boundary values in `L`
  (`TauCeti.exists_conjWirtingerDeriv_eq_and_mapsTo_sphere`). It is unique up to the kernel
  (`TauCeti.domRestrict_sub_mem_unitDiscTotallyRealKernel`).
* **Evaluation at a boundary mark.** The operator together with evaluation at a point `z₀` of the
  unit circle is bijective: for every datum `f` and every `v ∈ L` there is a solution with
  `u z₀ = v` (`TauCeti.exists_conjWirtingerDeriv_eq_and_mapsTo_sphere_and_eq`), and two solutions
  of the same equation that agree at one point of the closed disc agree on the closed disc
  (`TauCeti.eqOn_closedBall_of_conjWirtingerDeriv_eq_of_eq`).

For `E = ℂ` and `L = ℝ` the kernel is the Maslov index zero kernel
`TauCeti.unitDiscCauchyRiemannKernel 0` (`TauCeti.unitDiscTotallyRealKernel_span_one`).

The Sobolev realization of the operator, whose Fredholm theory these classical statements feed,
is not treated here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §2.3 (the disc with boundary on a compact Lagrangian, and the constant discs as the
  starting point of the continuation argument).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the Riemann–Roch theorem, Theorem C.1.10, and
  its proof by splitting a totally real boundary condition into rotating lines).
-/

public section

namespace TauCeti

open Complex Metric Module Set
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Submodule ℝ E}

/-! ### The kernel -/

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc with boundary
values in the real subspace `L`: the restrictions to the closed disc of maps `ℂ → E` holomorphic on
the open disc, continuous on its closure, and sending the unit circle into `L`. When `L` is
maximal totally real it consists of the constants in `L`
(`TauCeti.mem_unitDiscTotallyRealKernel_iff_exists_const`). -/
def unitDiscTotallyRealKernel (L : Submodule ℝ E) : Submodule ℝ (closedBall (0 : ℂ) 1 → E) where
  carrier := {g | ∃ u : ℂ → E, DiffContOnCl ℂ u (ball 0 1) ∧ MapsTo u (sphere 0 1) L ∧
    (closedBall 0 1).domRestrict u = g}
  add_mem' := by
    rintro _ _ ⟨u, hu, hu', rfl⟩ ⟨v, hv, hv', rfl⟩
    exact ⟨u + v, hu.add hv, fun w hw ↦ L.add_mem (hu' hw) (hv' hw), rfl⟩
  zero_mem' := ⟨0, diffContOnCl_const, fun _ _ ↦ L.zero_mem, rfl⟩
  smul_mem' := by
    rintro c _ ⟨u, hu, hu', rfl⟩
    exact ⟨c • u, hu.const_smul c, fun w hw ↦ L.smul_mem c (hu' hw), rfl⟩

/-- Membership in `unitDiscTotallyRealKernel L`, unfolded. -/
@[simp]
theorem mem_unitDiscTotallyRealKernel_iff {g : closedBall (0 : ℂ) 1 → E} :
    g ∈ unitDiscTotallyRealKernel L ↔ ∃ u : ℂ → E, DiffContOnCl ℂ u (ball 0 1) ∧
      MapsTo u (sphere 0 1) L ∧ (closedBall 0 1).domRestrict u = g :=
  Iff.rfl

/-- Elements of `unitDiscTotallyRealKernel L` agreeing at every point of the closed disc are
equal. -/
@[ext]
theorem unitDiscTotallyRealKernel.ext {f g : unitDiscTotallyRealKernel L}
    (h : ∀ z, (f : closedBall (0 : ℂ) 1 → E) z = (g : closedBall (0 : ℂ) 1 → E) z) : f = g :=
  Subtype.ext (_root_.funext h)

variable [FiniteDimensional ℂ E]
  (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- **Holomorphic discs with boundary in a maximal totally real subspace are constant.** A map
holomorphic on the open unit disc and continuous on its closure, sending the unit circle into a
maximal totally real subspace `L`, is constant on the closed disc. -/
theorem _root_.DiffContOnCl.eqOn_const_of_mapsTo_sphere {u : ℂ → E}
    (hu : DiffContOnCl ℂ u (ball 0 1)) (hb : MapsTo u (sphere 0 1) L) {z₀ : ℂ}
    (hz₀ : z₀ ∈ closedBall (0 : ℂ) 1) : EqOn u (fun _ ↦ u z₀) (closedBall 0 1) := by
  let B := hL.complexBasis (Module.finBasis ℝ L)
  intro z hz
  refine B.repr.injective (Finsupp.ext fun i ↦ ?_)
  -- each coordinate has real boundary values, so it is a real constant on the closed disc
  let φ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (B.coord i)
  have hmem : (closedBall 0 1).domRestrict (φ ∘ u) ∈ unitDiscCauchyRiemannKernel 0 := by
    refine mem_unitDiscCauchyRiemannKernel_iff.mpr
      ⟨φ ∘ u, φ.differentiable.comp_diffContOnCl hu, fun w hw ↦ ?_, rfl⟩
    rw [zpow_zero, one_mul, eq_comm, Complex.conj_eq_iff_im]
    simpa [φ] using (hL.mem_iff_forall_complexBasis_repr_im_eq_zero _).mp (hb hw) i
  obtain ⟨r, hr⟩ := mem_unitDiscCauchyRiemannKernel_zero_iff.mp hmem
  have h₁ := congrFun hr ⟨z, hz⟩
  have h₂ := congrFun hr ⟨z₀, hz₀⟩
  simp only [domRestrict_apply, Function.comp_apply] at h₁ h₂
  simpa [φ] using h₁.trans h₂.symm

/-- The kernel of `∂/∂(conj z)` with boundary values in a maximal totally real subspace `L`
consists of the constants in `L`. -/
theorem mem_unitDiscTotallyRealKernel_iff_exists_const {g : closedBall (0 : ℂ) 1 → E} :
    g ∈ unitDiscTotallyRealKernel L ↔ ∃ v ∈ L, g = fun _ ↦ v := by
  refine ⟨fun ⟨u, hu, hb, hg⟩ ↦ ⟨u 1, hb (by simp), ?_⟩, fun ⟨v, hv, hg⟩ ↦
    ⟨fun _ ↦ v, diffContOnCl_const, fun _ _ ↦ hv, hg.symm⟩⟩
  subst hg
  exact _root_.funext fun z ↦ hu.eqOn_const_of_mapsTo_sphere hL hb (by simp) z.2

/-- **The kernel is `L`.** Constant maps identify a maximal totally real subspace `L` with the
kernel of `∂/∂(conj z)` with boundary values in `L`. The inverse is evaluation at any point of the
closed disc (`TauCeti.unitDiscTotallyRealKernelEquiv_symm_apply`), for instance at a marked point
of the boundary. -/
noncomputable def unitDiscTotallyRealKernelEquiv : L ≃ₗ[ℝ] unitDiscTotallyRealKernel L where
  toFun v := ⟨fun _ ↦ v, (mem_unitDiscTotallyRealKernel_iff_exists_const hL).mpr ⟨v, v.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨(g : closedBall (0 : ℂ) 1 → E) ⟨0, by simp⟩, by
    obtain ⟨v, hv, hg⟩ := (mem_unitDiscTotallyRealKernel_iff_exists_const hL).mp g.2
    simpa [hg] using hv⟩
  left_inv _ := rfl
  right_inv g := by
    obtain ⟨v, -, hg⟩ := (mem_unitDiscTotallyRealKernel_iff_exists_const hL).mp g.2
    exact Subtype.ext (by simp [hg])

/-- `TauCeti.unitDiscTotallyRealKernelEquiv` sends `v ∈ L` to the constant map `v`. -/
@[simp]
theorem unitDiscTotallyRealKernelEquiv_apply (v : L) (z : closedBall (0 : ℂ) 1) :
    (unitDiscTotallyRealKernelEquiv hL v : closedBall (0 : ℂ) 1 → E) z = v := by
  simp [unitDiscTotallyRealKernelEquiv]

/-- The inverse of `TauCeti.unitDiscTotallyRealKernelEquiv` is evaluation at any point of the
closed disc. -/
theorem unitDiscTotallyRealKernelEquiv_symm_apply (g : unitDiscTotallyRealKernel L)
    (z : closedBall (0 : ℂ) 1) :
    ((unitDiscTotallyRealKernelEquiv hL).symm g : E) = (g : closedBall (0 : ℂ) 1 → E) z := by
  rw [← unitDiscTotallyRealKernelEquiv_apply hL _ z, LinearEquiv.apply_symm_apply]

/-- The kernel of `∂/∂(conj z)` with boundary values in a maximal totally real subspace of `E` has
real dimension `dim_ℂ E`. -/
theorem finrank_unitDiscTotallyRealKernel :
    finrank ℝ (unitDiscTotallyRealKernel L) = finrank ℂ E :=
  (unitDiscTotallyRealKernelEquiv hL).finrank_eq.symm.trans hL.finrank_eq_finrank_complex

omit hL in
/-- **Check: real boundary values.** For `E = ℂ` and `L = ℝ`, the kernel is the kernel
`TauCeti.unitDiscCauchyRiemannKernel 0` of the rotating-line problem of Maslov index `0`. -/
theorem unitDiscTotallyRealKernel_span_one :
    unitDiscTotallyRealKernel (Submodule.span ℝ {(1 : ℂ)}) = unitDiscCauchyRiemannKernel 0 := by
  ext g
  rw [mem_unitDiscTotallyRealKernel_iff_exists_const isMaximalTotallyReal_span_one,
    mem_unitDiscCauchyRiemannKernel_zero_iff]
  simp [Submodule.mem_span_singleton, eq_comm]

/-! ### Surjectivity and evaluation at a boundary mark -/

/-- **Surjectivity.** For compactly supported `C²` data `f : ℂ → E`, the equation
`∂u/∂(conj z) = f` on the open unit disc has a solution, continuous on the closed disc, with
boundary values in a maximal totally real subspace `L`. -/
theorem exists_conjWirtingerDeriv_eq_and_mapsTo_sphere {f : ℂ → E} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) :
    ∃ u : ℂ → E, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧ MapsTo u (sphere 0 1) L := by
  let B := hL.complexBasis (Module.finBasis ℝ L)
  -- solve the rank one problem with real boundary values in each coordinate
  have hcoord (i) : ∃ v : ℂ → ℂ, ContinuousOn v (closedBall 0 1) ∧
      DifferentiableOn ℝ v (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv v z 1 =
        B.repr (f z) i) ∧ ∀ w ∈ sphere (0 : ℂ) 1, v w = w ^ (0 : ℤ) * conj (v w) := by
    let φ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (B.coord i)
    simpa [φ] using exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj (k := 0) (by norm_num)
      (hc.comp_left (map_zero φ)) ((φ.restrictScalars ℝ).contDiff.comp hf)
  choose v hvc hvd hvf hvb using hcoord
  refine ⟨fun z ↦ ∑ i, v i z • B i, continuousOn_finsetSum _ fun i _ ↦
    (hvc i).smul continuousOn_const, DifferentiableOn.fun_sum fun i _ ↦ (hvd i).smul_const _,
    fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · have hd (i) : DifferentiableAt ℝ (v i) z :=
      (hvd i z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    rw [conjWirtingerDeriv_fun_sum fun i _ ↦ (hd i).smul_const _, sum_apply]
    conv_rhs => rw [← B.sum_repr (f z)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [conjWirtingerDeriv_smul_apply (hd i) (differentiableAt_const _), hvf i z hz]
    simp
  · rw [SetLike.mem_coe, hL.mem_iff_forall_complexBasis_repr_im_eq_zero, B.repr_sum_self]
    intro i
    rw [← Complex.conj_eq_iff_im]
    simpa using (hvb i w hw).symm

omit [FiniteDimensional ℂ E] hL in
/-- **Uniqueness modulo the kernel.** Two maps, continuous on the closed unit disc and real
differentiable on the open disc, with the same `∂/∂(conj z)` on the open disc and boundary values
in `L`, differ on the closed disc by an element of the kernel `TauCeti.unitDiscTotallyRealKernel L`.
-/
theorem domRestrict_sub_mem_unitDiscTotallyRealKernel {u₁ u₂ : ℂ → E}
    (hc₁ : ContinuousOn u₁ (closedBall 0 1)) (hc₂ : ContinuousOn u₂ (closedBall 0 1))
    (hd₁ : DifferentiableOn ℝ u₁ (ball 0 1)) (hd₂ : DifferentiableOn ℝ u₂ (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u₁ z 1 = conjWirtingerDeriv u₂ z 1)
    (hb₁ : MapsTo u₁ (sphere 0 1) L) (hb₂ : MapsTo u₂ (sphere 0 1) L) :
    (closedBall 0 1).domRestrict (u₁ - u₂) ∈ unitDiscTotallyRealKernel L := by
  refine ⟨u₁ - u₂, ⟨fun z hz ↦ ?_, ?_⟩, fun w hw ↦ L.sub_mem (hb₁ hw) (hb₂ hw), rfl⟩
  · have h₁ := (hd₁ z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    have h₂ := (hd₂ z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (h₁.sub h₂)).mpr
      ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub h₁ h₂, sub_apply, heq z hz, sub_self]
  · rw [closure_ball 0 one_ne_zero]
    exact hc₁.sub hc₂

/-- **Injectivity of the operator together with evaluation.** Two maps, continuous on the closed
unit disc and real differentiable on the open disc, with the same `∂/∂(conj z)` on the open disc,
boundary values in a maximal totally real subspace `L`, and the same value at one point `z₀` of the
closed disc, agree on the closed disc. -/
theorem eqOn_closedBall_of_conjWirtingerDeriv_eq_of_eq {u₁ u₂ : ℂ → E}
    (hc₁ : ContinuousOn u₁ (closedBall 0 1)) (hc₂ : ContinuousOn u₂ (closedBall 0 1))
    (hd₁ : DifferentiableOn ℝ u₁ (ball 0 1)) (hd₂ : DifferentiableOn ℝ u₂ (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u₁ z 1 = conjWirtingerDeriv u₂ z 1)
    (hb₁ : MapsTo u₁ (sphere 0 1) L) (hb₂ : MapsTo u₂ (sphere 0 1) L) {z₀ : ℂ}
    (hz₀ : z₀ ∈ closedBall (0 : ℂ) 1) (h : u₁ z₀ = u₂ z₀) : EqOn u₁ u₂ (closedBall 0 1) := by
  obtain ⟨v, -, hv⟩ := (mem_unitDiscTotallyRealKernel_iff_exists_const hL).mp
    (domRestrict_sub_mem_unitDiscTotallyRealKernel hc₁ hc₂ hd₁ hd₂ heq hb₁ hb₂)
  intro z hz
  have hz' := congrFun hv ⟨z, hz⟩
  have hz₀' := congrFun hv ⟨z₀, hz₀⟩
  simp only [domRestrict_apply, Pi.sub_apply, h, sub_self] at hz' hz₀'
  rw [← sub_eq_zero, hz', ← hz₀']

/-- **Surjectivity of the operator together with evaluation at a boundary mark.** For compactly
supported `C²` data `f : ℂ → E`, a point `z₀` of the unit circle and `v ∈ L`, the equation
`∂u/∂(conj z) = f` on the open unit disc has a solution, continuous on the closed disc, with
boundary values in a maximal totally real subspace `L` and `u z₀ = v`. -/
theorem exists_conjWirtingerDeriv_eq_and_mapsTo_sphere_and_eq {f : ℂ → E}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) {z₀ : ℂ} (hz₀ : z₀ ∈ sphere (0 : ℂ) 1)
    {v : E} (hv : v ∈ L) :
    ∃ u : ℂ → E, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧ MapsTo u (sphere 0 1) L ∧
        u z₀ = v := by
  obtain ⟨u, hc, hd, hu, hb⟩ := exists_conjWirtingerDeriv_eq_and_mapsTo_sphere hL hc hf
  -- correct the value at `z₀` by a constant of `L`
  refine ⟨fun z ↦ u z + (v - u z₀), hc.add continuousOn_const, hd.add_const _,
    fun z hz ↦ ?_, fun w hw ↦ L.add_mem (hb hw) (L.sub_mem hv (hb hz₀)), by simp⟩
  simpa [conjWirtingerDeriv_apply] using hu z hz

end TauCeti
