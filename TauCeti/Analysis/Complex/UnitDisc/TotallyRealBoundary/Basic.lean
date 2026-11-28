/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Analysis.Complex.UnitDisc.Cokernel
import TauCeti.Analysis.Complex.UnitDisc.DiagonalBoundary
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# The disc with a constant maximal totally real boundary condition

Let `E` be a finite-dimensional complex normed space and `Λ` a real subspace of `E` which is
maximal totally real, `E = Λ ⊕ i Λ`. This file treats the Cauchy–Riemann operator `∂/∂(conj z)`
on the closed unit disc for maps `u : ℂ → E` with the constant boundary condition
`u(∂D) ⊆ Λ`. This is the linearization of the Cauchy–Riemann section at a constant disc `u ≡ x`
with boundary on a totally real submanifold `L` with `T_x L = Λ`. A Lagrangian subspace of
`ι → ℂ` is such a `Λ`, by `TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_tames`
applied to `TauCeti.stdComplexPiSymplecticForm_tames`.

A real basis of `Λ` is a complex basis of `E` (`TauCeti.IsMaximalTotallyReal.complexBasis`), and
`Λ` consists of the vectors whose coordinates in it are real
(`TauCeti.IsMaximalTotallyReal.mem_iff_forall_conj_complexBasis_repr`). In these coordinates the
problem splits into `n = dim_ℂ E` copies of the scalar problem with real boundary values, the
rotating-line problem of Maslov index `0`. Its solutions are the real constants
(`TauCeti.mem_unitDiscCauchyRiemannKernelPi_zero_iff`) and it has no cokernel
(`TauCeti.unitDiscCauchyRiemannRange_eq_top`). Hence:

* **Kernel.** A map holomorphic on the open disc and continuous on its closure, with boundary
  values in `Λ`, is constant on the closed disc
  (`TauCeti.IsMaximalTotallyReal.eqOn_closedBall_const_of_diffContOnCl`). So the kernel
  `TauCeti.unitDiscTotallyRealKernel Λ` consists of the constant maps with value in `Λ`, and
  evaluation at the boundary point `1` is a real-linear isomorphism from it onto `Λ`
  (`TauCeti.IsMaximalTotallyReal.unitDiscTotallyRealKernelEquiv`). Its dimension is
  `n = n χ(D) + μ` with Maslov index `μ = 0`
  (`TauCeti.IsMaximalTotallyReal.finrank_unitDiscTotallyRealKernel`).
* **Surjectivity.** Every `f`, `C²` at every point of the closed disc, is `∂u/∂(conj z)` on the
  open disc for some `u` continuous on the closed disc with `u(∂D) ⊆ Λ`, and `u 1` can be
  prescribed in `Λ` (`TauCeti.IsMaximalTotallyReal.exists_conjWirtingerDeriv_eq_and_mem`).
* **Uniqueness.** Two such solutions with the same `∂/∂(conj z)` and the same value at `1` agree
  on the closed disc (`TauCeti.IsMaximalTotallyReal.eqOn_closedBall_of_conjWirtingerDeriv_eq`).

Together, the Cauchy–Riemann operator and evaluation at the boundary mark `1` form a bijection from
the solutions, restricted to the closed disc, onto the data and `Λ`
(`TauCeti.IsMaximalTotallyReal.existsUnique_conjWirtingerDeriv_eq_and_mem`).

## Main definitions

* `TauCeti.unitDiscTotallyRealKernel Λ`: the maps on the closed unit disc that are restrictions of
  maps holomorphic on the open disc, continuous on its closure, with boundary values in `Λ`.
* `TauCeti.IsMaximalTotallyReal.unitDiscTotallyRealKernelEquiv`: evaluation at `1`, as a
  real-linear isomorphism from this kernel onto `Λ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.1 (the Riemann–Roch theorem for the disc) and
  Theorem C.4.1 (the rank one problem).
-/

public section

namespace TauCeti

open Complex ComplexConjugate Metric Module Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The kernel -/

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc with the
constant boundary condition `u(∂D) ⊆ Λ`: the maps `g` on the closed unit disc that are
restrictions of maps `u : ℂ → E` holomorphic on the open disc and continuous on its closure, with
`u w ∈ Λ` for `‖w‖ = 1`. For maximal totally real `Λ` it consists of the constant maps with value
in `Λ` (`TauCeti.IsMaximalTotallyReal.mem_unitDiscTotallyRealKernel_iff`). -/
def unitDiscTotallyRealKernel (Λ : Submodule ℝ E) : Submodule ℝ (closedBall (0 : ℂ) 1 → E) where
  carrier := {g | ∃ u : ℂ → E, DiffContOnCl ℂ u (ball 0 1) ∧
    (∀ w ∈ sphere (0 : ℂ) 1, u w ∈ Λ) ∧ (closedBall 0 1).domRestrict u = g}
  add_mem' := by
    rintro _ _ ⟨u, hu, hu', rfl⟩ ⟨v, hv, hv', rfl⟩
    exact ⟨u + v, hu.add hv, fun w hw => Λ.add_mem (hu' w hw) (hv' w hw), rfl⟩
  zero_mem' := ⟨0, diffContOnCl_const, fun _ _ => Λ.zero_mem, rfl⟩
  smul_mem' := by
    rintro c _ ⟨u, hu, hu', rfl⟩
    exact ⟨c • u, hu.const_smul c, fun w hw => Λ.smul_mem c (hu' w hw), rfl⟩

variable {Λ : Submodule ℝ E} {g : closedBall (0 : ℂ) 1 → E}

/-- Membership in `unitDiscTotallyRealKernel Λ`, unfolded. -/
theorem mem_unitDiscTotallyRealKernel_iff_exists :
    g ∈ unitDiscTotallyRealKernel Λ ↔ ∃ u : ℂ → E, DiffContOnCl ℂ u (ball 0 1) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, u w ∈ Λ) ∧ (closedBall 0 1).domRestrict u = g :=
  Iff.rfl

/-- The constant maps with value in `Λ` lie in the kernel. -/
theorem const_mem_unitDiscTotallyRealKernel {v : E} (hv : v ∈ Λ) :
    (fun _ => v : closedBall (0 : ℂ) 1 → E) ∈ unitDiscTotallyRealKernel Λ :=
  ⟨fun _ => v, diffContOnCl_const, fun _ _ => hv, rfl⟩

/-- Elements of `unitDiscTotallyRealKernel Λ` agreeing at every point of the closed disc are
equal. -/
@[ext]
theorem unitDiscTotallyRealKernel.ext {f g : unitDiscTotallyRealKernel Λ}
    (h : ∀ z, (f : closedBall (0 : ℂ) 1 → E) z = (g : closedBall (0 : ℂ) 1 → E) z) : f = g :=
  Subtype.ext (funext h)

namespace IsMaximalTotallyReal

variable [FiniteDimensional ℂ E]
  (hΛ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) Λ)
include hΛ

/-- **The kernel is the constants.** A map holomorphic on the open unit disc and continuous on its
closure, with boundary values in a maximal totally real subspace `Λ`, is constant on the closed
disc. -/
theorem eqOn_closedBall_const_of_diffContOnCl {u : ℂ → E} (hu : DiffContOnCl ℂ u (ball 0 1))
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, u w ∈ Λ) : EqOn u (fun _ => u 1) (closedBall 0 1) := by
  set A := (hΛ.complexBasis (Module.finBasis ℝ Λ)).equivFunL
  have hA : DiffContOnCl ℂ (A ∘ u) (ball 0 1) :=
    A.differentiable.diffContOnCl.comp hu (mapsTo_univ _ _)
  have hk : (closedBall 0 1).domRestrict (A ∘ u) ∈ unitDiscCauchyRiemannKernelPi 0 :=
    mem_unitDiscCauchyRiemannKernelPi_iff_exists.2 ⟨_, hA, fun w hw i => by
      simpa [A] using
        ((hΛ.mem_iff_forall_conj_complexBasis_repr (Module.finBasis ℝ Λ)).1 (hb w hw) i).symm, rfl⟩
  obtain ⟨r, hr⟩ := mem_unitDiscCauchyRiemannKernelPi_zero_iff.1 hk
  intro z hz
  apply A.injective
  have h₁ := congrFun hr ⟨z, hz⟩
  have h₂ := congrFun hr ⟨1, by simp⟩
  simp only [domRestrict_apply, Function.comp_apply] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The kernel of the Cauchy–Riemann operator with boundary values in a maximal totally real
subspace `Λ` consists of the constant maps with value in `Λ`. -/
theorem mem_unitDiscTotallyRealKernel_iff :
    g ∈ unitDiscTotallyRealKernel Λ ↔ ∃ v ∈ Λ, g = fun _ => v := by
  refine ⟨fun ⟨u, hu, hb, hg⟩ => ⟨u 1, hb 1 (by simp), ?_⟩, fun ⟨v, hv, hg⟩ => ?_⟩
  · rw [← hg]
    exact funext fun z => hΛ.eqOn_closedBall_const_of_diffContOnCl hu hb z.property
  · rw [hg]
    exact const_mem_unitDiscTotallyRealKernel hv

/-- **Evaluation at the boundary mark.** For a maximal totally real subspace `Λ`, evaluation at
the boundary point `1` is a real-linear isomorphism from the kernel of the Cauchy–Riemann operator
with boundary values in `Λ` onto `Λ`; its inverse sends `v` to the constant map. -/
noncomputable def unitDiscTotallyRealKernelEquiv : unitDiscTotallyRealKernel Λ ≃ₗ[ℝ] Λ where
  toFun g := ⟨(g : closedBall (0 : ℂ) 1 → E) ⟨1, by simp⟩, by
    obtain ⟨v, hv, hg⟩ := hΛ.mem_unitDiscTotallyRealKernel_iff.1 g.property
    rw [hg]
    exact hv⟩
  invFun v := ⟨fun _ => v, const_mem_unitDiscTotallyRealKernel v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := by
    obtain ⟨v, -, hg⟩ := hΛ.mem_unitDiscTotallyRealKernel_iff.1 g.property
    ext z
    simp [hg]
  right_inv _ := rfl

@[simp]
theorem coe_unitDiscTotallyRealKernelEquiv_apply (g : unitDiscTotallyRealKernel Λ) :
    (hΛ.unitDiscTotallyRealKernelEquiv g : E) = (g : closedBall (0 : ℂ) 1 → E) ⟨1, by simp⟩ := by
  rfl

@[simp]
theorem unitDiscTotallyRealKernelEquiv_symm_apply (v : Λ) (z : closedBall (0 : ℂ) 1) :
    (hΛ.unitDiscTotallyRealKernelEquiv.symm v : closedBall (0 : ℂ) 1 → E) z = v := by
  rfl

/-- The kernel of the Cauchy–Riemann operator with boundary values in a maximal totally real
subspace is finite-dimensional. -/
theorem finiteDimensional_unitDiscTotallyRealKernel :
    FiniteDimensional ℝ (unitDiscTotallyRealKernel Λ) :=
  hΛ.unitDiscTotallyRealKernelEquiv.symm.finiteDimensional

/-- The kernel of the Cauchy–Riemann operator with boundary values in a maximal totally real
subspace has real dimension `n = dim_ℂ E`, the index `n χ(D) + μ` for the Maslov index `μ = 0` of
a constant boundary condition. -/
theorem finrank_unitDiscTotallyRealKernel :
    finrank ℝ (unitDiscTotallyRealKernel Λ) = finrank ℂ E :=
  hΛ.unitDiscTotallyRealKernelEquiv.finrank_eq.trans hΛ.finrank_eq_finrank_complex

/-! ### Surjectivity and uniqueness -/

/-- **Surjectivity.** For a maximal totally real subspace `Λ`, a function `f`, `C²` at every point
of the closed unit disc, and `v ∈ Λ`, there is `u`, continuous on the closed disc and real
differentiable on the open disc, with `∂u/∂(conj z) = f` on the open disc, boundary values in `Λ`
and `u 1 = v`. -/
theorem exists_conjWirtingerDeriv_eq_and_mem {f : ℂ → E}
    (hf : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) {v : E} (hv : v ∈ Λ) :
    ∃ u : ℂ → E, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, u w ∈ Λ) ∧ u 1 = v := by
  set A := (hΛ.complexBasis (Module.finBasis ℝ Λ)).equivFunL
  have hsol : ∀ i, ∃ ui : ℂ → ℂ, ContinuousOn ui (closedBall 0 1) ∧
      DifferentiableOn ℝ ui (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv ui z 1 = A (f z) i) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, conj (ui w) = ui w := by
    intro i
    let π : (Fin (finrank ℝ Λ) → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
    let P : E →L[ℝ] ℂ := (π.comp (A : E →L[ℂ] _)).restrictScalars ℝ
    have hF : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 (fun z => A (f z) i) z :=
      fun z hz => P.contDiff.contDiffAt.comp z (hf z hz)
    have hmem : (⟨(closedBall 0 1).domRestrict fun z => A (f z) i,
        mem_unitDiscCauchyRiemannData_iff.2 ⟨_, hF, rfl⟩⟩ : unitDiscCauchyRiemannData) ∈
        unitDiscCauchyRiemannRange 0 := by
      rw [unitDiscCauchyRiemannRange_eq_top (by norm_num)]
      exact Submodule.mem_top
    obtain ⟨ui, hc, hd, heq, hb⟩ := mem_unitDiscCauchyRiemannRange_iff.1 hmem
    exact ⟨ui, hc, hd, fun z hz => heq z hz, fun w hw => by simpa using (hb w hw).symm⟩
  choose ui hc hd heq hb using hsol
  let U : ℂ → Fin (finrank ℝ Λ) → ℂ := fun z i => ui i z
  have hUc : ContinuousOn U (closedBall 0 1) := continuousOn_pi.2 hc
  have hUd : DifferentiableOn ℝ U (ball 0 1) := differentiableOn_pi.2 hd
  have hmem : ∀ w ∈ sphere (0 : ℂ) 1, A.symm (U w) ∈ Λ := fun w hw =>
    (hΛ.mem_iff_forall_conj_complexBasis_repr (Module.finBasis ℝ Λ)).2 fun i => by
      rw [← Basis.equivFunL_apply, A.apply_symm_apply]
      exact hb i w hw
  refine ⟨fun z => A.symm (U z) + (v - A.symm (U 1)), ?_, ?_, fun z hz => ?_, fun w hw => ?_, ?_⟩
  · exact (A.symm.continuous.comp_continuousOn hUc).add continuousOn_const
  · exact (((A.symm : _ →L[ℂ] E).restrictScalars ℝ).differentiable.comp_differentiableOn
      hUd).add_const _
  · have hUz : DifferentiableAt ℝ U z := hUd.differentiableAt (isOpen_ball.mem_nhds hz)
    have hproj : ∀ i, conjWirtingerDeriv U z 1 i = A (f z) i := fun i => by
      simpa [U, heq i z hz] using
        congr($((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) i).conjWirtingerDeriv_comp_left
          hUz) 1).symm
    simpa [funext hproj] using
      congr($((A.symm : _ →L[ℂ] E).conjWirtingerDeriv_comp_left hUz) 1)
  · exact Λ.add_mem (hmem w hw) (Λ.sub_mem hv (hmem 1 (by simp)))
  · simp

/-- **Uniqueness.** For a maximal totally real subspace `Λ`, two functions continuous on the
closed unit disc and real differentiable on the open disc, with boundary values in `Λ`, the same
`∂/∂(conj z)` on the open disc and the same value at `1`, agree on the closed disc. -/
theorem eqOn_closedBall_of_conjWirtingerDeriv_eq {u₁ u₂ : ℂ → E}
    (hc₁ : ContinuousOn u₁ (closedBall 0 1)) (hc₂ : ContinuousOn u₂ (closedBall 0 1))
    (hd₁ : DifferentiableOn ℝ u₁ (ball 0 1)) (hd₂ : DifferentiableOn ℝ u₂ (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u₁ z 1 = conjWirtingerDeriv u₂ z 1)
    (hb₁ : ∀ w ∈ sphere (0 : ℂ) 1, u₁ w ∈ Λ) (hb₂ : ∀ w ∈ sphere (0 : ℂ) 1, u₂ w ∈ Λ)
    (h₁ : u₁ 1 = u₂ 1) : EqOn u₁ u₂ (closedBall 0 1) := by
  rw [← closure_ball (0 : ℂ) one_ne_zero] at hc₁ hc₂
  have hd := diffContOnCl_sub_of_conjWirtingerDeriv_eq isOpen_ball hc₁ hc₂ hd₁ hd₂ heq
  intro z hz
  have h := hΛ.eqOn_closedBall_const_of_diffContOnCl hd
    (fun w hw => Λ.sub_mem (hb₁ w hw) (hb₂ w hw)) hz
  simpa [h₁, sub_eq_zero] using h

/-- **The Cauchy–Riemann operator and evaluation at the boundary mark form a bijection.** For a
maximal totally real subspace `Λ`, a function `f`, `C²` at every point of the closed unit disc,
and `v ∈ Λ`, there is exactly one map `g` on the closed disc which is the restriction of a
function `u`, continuous on the closed disc and real differentiable on the open disc, with
`∂u/∂(conj z) = f` on the open disc, boundary values in `Λ` and `u 1 = v`. -/
theorem existsUnique_conjWirtingerDeriv_eq_and_mem {f : ℂ → E}
    (hf : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 2 f z) {v : E} (hv : v ∈ Λ) :
    ∃! g : closedBall (0 : ℂ) 1 → E, ∃ u : ℂ → E, ContinuousOn u (closedBall 0 1) ∧
      DifferentiableOn ℝ u (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, u w ∈ Λ) ∧ u 1 = v ∧ (closedBall 0 1).domRestrict u = g := by
  obtain ⟨u, hc, hd, heq, hb, h₁⟩ := hΛ.exists_conjWirtingerDeriv_eq_and_mem hf hv
  refine ⟨_, ⟨u, hc, hd, heq, hb, h₁, rfl⟩, ?_⟩
  rintro _ ⟨u', hc', hd', heq', hb', h₁', rfl⟩
  exact funext fun z => hΛ.eqOn_closedBall_of_conjWirtingerDeriv_eq hc' hc hd' hd
    (fun z hz => (heq' z hz).trans (heq z hz).symm) hb' hb (h₁'.trans h₁.symm) z.property

end IsMaximalTotallyReal

end TauCeti
