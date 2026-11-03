/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Analysis.Holder.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Cauchy heat potential in the order-two parabolic Hölder space

For an initial datum `g ∈ C_b^{2,α}(E)` and a slab `E × [a, b]` with `0 ≤ a < b`, the Cauchy
heat potential `u(t, x) = ∫ K_1(y) g(x - √t • y) dy` (`TauCeti.heatCauchyPotential`) belongs to
the bounded order-two parabolic Hölder space `C_b^{2+α,1+α/2}(E × [a, b])`, and
`g ↦ u` is a bounded linear map `TauCeti.heatCauchyPotentialL` with operator norm at most
`(1 + dim E) (1 + M_α)`, where `M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`. The
bound does not depend on the slab.

Each field of `u` is the Cauchy potential of the corresponding derivative of the datum: the
spatial gradient and Hessian are the Cauchy potentials of `Dg` and `D²g`, and the time derivative
is the Cauchy potential of `Δg`, also at the initial time `t = 0` when `a = 0`. The supremum
bounds then follow from the maximum principle `TauCeti.norm_heatCauchyPotential_le`, and the
parabolic Hölder seminorms of the two top-order fields from the parabolic Hölder estimate
`TauCeti.holderWith_heatCauchyPotential` applied to `D²g` and `Δg`. In particular `u` solves the
heat equation `∂ₜu = Δu` on the closed slab, and when `a = 0` its initial trace is `g`.

This is the initial-data part of the solution operator of the Cauchy problem
`∂ₜu - Δu = f`, `u(·, 0) = g` in parabolic Hölder spaces, whose solution is the sum of the Cauchy
potential of `g` and the Duhamel potential of `f`.

## Main declarations

* `TauCeti.heatCauchyPotentialL`: the Cauchy potential as a continuous linear map
  `C_b^{2,α}(E) → C_b^{2+α,1+α/2}(E × [a, b])`.
* `TauCeti.heatCauchyPotentialL_apply` and its companions: the four fields of the potential.
* `TauCeti.timeDerivL_heatCauchyPotentialL_eq_laplacian`: the heat equation `∂ₜu = Δu`.
* `TauCeti.norm_heatCauchyPotentialL_le`: the operator-norm bound `(1 + dim E) (1 + M_α)`.
* `TauCeti.spatialTrace_heatCauchyPotentialL_left`: the initial trace of the potential is `g`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Set ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {a b : ℝ}

/-! ### The Cauchy potential of a bounded field on a slab -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section SlabPotential

variable {h : E → G} {M : ℝ} {K : ℝ≥0}

/-- The Cauchy potential of a bounded continuous field, restricted to the slab `E × [a, b]`, as a
bounded continuous function. -/
private def slabPotential (h : E → G) (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M) :
    slab (E := E) a b →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p ↦ heatCauchyPotential h (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space)
    ((continuous_heatCauchyPotential hc hM).comp
      ((continuous_time.comp continuous_subtype_val).prodMk
        (continuous_space.comp continuous_subtype_val)))
    M fun _ ↦ norm_heatCauchyPotential_le hM _ _

private theorem slabPotential_apply (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M)
    (p : slab (E := E) a b) :
    slabPotential h hc hM p =
      heatCauchyPotential h (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space :=
  (rfl)

private theorem norm_slabPotential_le (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M) :
    ‖slabPotential (a := a) (b := b) h hc hM‖ ≤ M :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ ((norm_nonneg _).trans (hM 0)) _

private theorem holderWith_slabPotential (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M)
    (hK : HolderWith K α h) :
    HolderWith (K * (1 + heatKernelMoment E α)) α
      (slabPotential (a := a) (b := b) h hc hM : slab (E := E) a b → G) :=
  ((holderWith_heatCauchyPotential hK hc).holderOnWith _).holderWith

/-- The Cauchy potential of a bounded continuous Hölder field, restricted to the slab
`E × [a, b]`, as an element of the bounded Hölder space. -/
private def slabPotentialHolder (h : E → G) (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M)
    (hK : HolderWith K α h) : HolderSpace α (slab (E := E) a b) G :=
  HolderSpace.ofBoundedContinuousFunction (slabPotential h hc hM)
    (holderWith_slabPotential hc hM hK).memHolder

private theorem slabPotentialHolder_apply (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M)
    (hK : HolderWith K α h) (p : slab (E := E) a b) :
    slabPotentialHolder h hc hM hK p =
      heatCauchyPotential h (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [slabPotentialHolder, HolderSpace.ofBoundedContinuousFunction_apply, slabPotential_apply]

private theorem norm_slabPotentialHolder_le (hc : Continuous h) (hM : ∀ y, ‖h y‖ ≤ M)
    (hK : HolderWith K α h) :
    ‖slabPotentialHolder (a := a) (b := b) h hc hM hK‖ ≤
      M + K * (1 + heatKernelMoment E α) := by
  rw [HolderSpace.norm_def, slabPotentialHolder,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  gcongr
  · exact norm_slabPotential_le hc hM
  · exact_mod_cast (holderWith_slabPotential hc hM hK).nnholderNorm_le

end SlabPotential

/-! ### The potential as an order-two parabolic Hölder map -/

variable [CompleteSpace F]

variable (hab : a < b) (ha : 0 ≤ a)

/-- The Cauchy potential of a `C_b^{2,α}` datum, as an element of the order-two parabolic Hölder
space on `E × [a, b]`. -/
private def potential (g : CkHolderSpace 2 α E F) : ParabolicC2HolderSpace α E F hab :=
  ParabolicC2HolderSpace.mk
    (slabPotential g g.contDiff.continuous g.norm_apply_le_iteratedFDeriv_zero)
    (slabPotential (fderiv ℝ g) (g.contDiff.continuous_fderiv two_ne_zero)
      g.norm_fderiv_le_iteratedFDeriv_one)
    (slabPotentialHolder (fderiv ℝ (fderiv ℝ g))
      (g.contDiff_fderiv.continuous_fderiv one_ne_zero)
      g.norm_fderiv_fderiv_le_iteratedFDeriv_two g.holderWith_fderiv_fderiv)
    (slabPotentialHolder (Δ (g : E → F)) g.contDiff.continuous_laplacian
      g.norm_laplacian_le_iteratedFDeriv_two g.holderWith_laplacian)
    (fun t x ↦ by
      simp only [slabPotential_apply, space_slabMk, time_slabMk]
      exact hasFDerivAt_heatCauchyPotential
        (fun y ↦ (g.contDiff.differentiable two_ne_zero y).hasFDerivAt)
        (g.contDiff.continuous_fderiv two_ne_zero) g.norm_fderiv_le_iteratedFDeriv_one t x)
    (fun t x ↦ by
      simp only [slabPotential_apply, slabPotentialHolder_apply, space_slabMk, time_slabMk]
      exact hasFDerivAt_heatCauchyPotential
        (fun y ↦ (g.contDiff_fderiv.differentiable one_ne_zero y).hasFDerivAt)
        (g.contDiff_fderiv.continuous_fderiv one_ne_zero)
        g.norm_fderiv_fderiv_le_iteratedFDeriv_two t x)
    (fun x t ↦ by
      rw [slabPotentialHolder_apply, space_slabMk, time_slabMk]
      refine ((hasDerivWithinAt_heatCauchyPotential g.contDiff
        g.norm_apply_le_iteratedFDeriv_zero g.norm_fderiv_le_iteratedFDeriv_one
        g.norm_fderiv_fderiv_le_iteratedFDeriv_two (ha.trans t.2.1) x).mono
          (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 ha))).congr_of_mem (fun s hs ↦ ?_) t.2
      simp [timeExtension_def, projIcc_of_mem hab.le hs, slabPotential_apply])

private theorem potential_apply (g : CkHolderSpace 2 α E F) (p : slab (E := E) a b) :
    potential hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [potential, ParabolicC2HolderSpace.mk_apply, slabPotential_apply]

private theorem norm_potential_le (g : CkHolderSpace 2 α E F) :
    ‖potential hab ha g‖ ≤
      (1 + Module.finrank ℝ E) * (1 + heatKernelMoment E α) * ‖g‖ := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set m : ℝ := ((heatKernelMoment E α : ℝ≥0) : ℝ)
  set H : ℝ := ((nnHolderNorm α (iteratedFDeriv ℝ 2 g) : ℝ≥0) : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hm : 0 ≤ m := NNReal.coe_nonneg _
  have hH : 0 ≤ H := NNReal.coe_nonneg _
  have h₀ := norm_slabPotential_le (a := a) (b := b) g.contDiff.continuous
    g.norm_apply_le_iteratedFDeriv_zero
  have h₁ := norm_slabPotential_le (a := a) (b := b) (g.contDiff.continuous_fderiv two_ne_zero)
    g.norm_fderiv_le_iteratedFDeriv_one
  have h₂ := norm_slabPotentialHolder_le (a := a) (b := b)
    (g.contDiff_fderiv.continuous_fderiv one_ne_zero)
    g.norm_fderiv_fderiv_le_iteratedFDeriv_two g.holderWith_fderiv_fderiv
  have hΔ := norm_slabPotentialHolder_le (a := a) (b := b) g.contDiff.continuous_laplacian
    g.norm_laplacian_le_iteratedFDeriv_two g.holderWith_laplacian
  push_cast at h₂ hΔ
  have hS₀ := norm_nonneg (g.iteratedFDeriv 0)
  have hS₁ := norm_nonneg (g.iteratedFDeriv 1)
  have hS₂ := norm_nonneg (g.iteratedFDeriv 2)
  rw [ParabolicC2HolderSpace.norm_eq, potential, valueL_mk, spatialFDerivL_mk,
    spatialSecondFDerivL_mk, timeDerivL_mk, CkHolderSpace.norm_eq, Fin.sum_univ_three]
  -- Each of the four fields is bounded by a part of `(1 + d) (1 + m) ‖g‖`.
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hS₀, mul_nonneg hm hS₀,
    mul_nonneg (mul_nonneg hd hm) hS₀, mul_nonneg hd hS₁, mul_nonneg hm hS₁,
    mul_nonneg (mul_nonneg hd hm) hS₁,
    mul_nonneg hm hS₂, mul_nonneg (mul_nonneg hd hm) hS₂, mul_nonneg hd hH]

/-- **The Cauchy heat potential in `C_b^{2+α,1+α/2}`.** For `0 ≤ a < b`, the Cauchy heat potential
`u(t, x) = ∫ K_1(y) g(x - √t • y) dy` of a datum `g ∈ C_b^{2,α}(E)`, restricted to the slab
`E × [a, b]`, as a continuous linear map into the bounded order-two parabolic Hölder space. Its
operator norm is at most `(1 + dim E) (1 + M_α)` (`TauCeti.norm_heatCauchyPotentialL_le`). -/
def heatCauchyPotentialL : CkHolderSpace 2 α E F →L[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearMap.mkContinuous
    { toFun := potential hab ha
      map_add' g₁ g₂ := by
        ext p
        simp only [potential_apply, ParabolicC2HolderSpace.add_apply, CkHolderSpace.coe_add]
        exact heatCauchyPotential_add g₁.contDiff.continuous
          g₁.norm_apply_le_iteratedFDeriv_zero g₂.contDiff.continuous
          g₂.norm_apply_le_iteratedFDeriv_zero _ _
      map_smul' c g := by
        ext p
        simp only [potential_apply, ParabolicC2HolderSpace.smul_apply, CkHolderSpace.coe_smul,
          RingHom.id_apply]
        exact heatCauchyPotential_smul c _ _ _ }
    _ (norm_potential_le hab ha)

private theorem heatCauchyPotentialL_eq_potential (g : CkHolderSpace 2 α E F) :
    heatCauchyPotentialL hab ha g = potential hab ha g :=
  (rfl)

variable {hab ha}

/-- The value of the potential at a point of the slab. -/
@[simp]
theorem heatCauchyPotentialL_apply (g : CkHolderSpace 2 α E F) (p : slab (E := E) a b) :
    heatCauchyPotentialL hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, potential_apply]

/-- The spatial gradient of the potential is the Cauchy potential of `Dg`. -/
@[simp]
theorem spatialFDerivL_heatCauchyPotentialL (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    spatialFDerivL (heatCauchyPotentialL hab ha g) p = heatCauchyPotential (fderiv ℝ g)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, potential, spatialFDerivL_mk, slabPotential_apply]

/-- The spatial Hessian of the potential is the Cauchy potential of `D²g`. -/
@[simp]
theorem spatialSecondFDerivL_heatCauchyPotentialL (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    spatialSecondFDerivL (heatCauchyPotentialL hab ha g) p =
      heatCauchyPotential (fderiv ℝ (fderiv ℝ g))
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, potential, spatialSecondFDerivL_mk,
    slabPotentialHolder_apply]

/-- The time derivative of the potential is the Cauchy potential of `Δg`, also at the endpoints of
the slab. -/
@[simp]
theorem timeDerivL_heatCauchyPotentialL (g : CkHolderSpace 2 α E F) (p : slab (E := E) a b) :
    timeDerivL (heatCauchyPotentialL hab ha g) p = heatCauchyPotential (Δ (g : E → F))
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, potential, timeDerivL_mk, slabPotentialHolder_apply]

/-- **The heat equation.** The time derivative of the Cauchy potential is the spatial Laplacian of
its time slice, at every point of the closed slab. -/
theorem timeDerivL_heatCauchyPotentialL_eq_laplacian (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    timeDerivL (heatCauchyPotentialL hab ha g) p =
      Δ (fun y ↦ heatCauchyPotentialL hab ha g (slabMk y (slabTime p)))
        (p : ParabolicSpaceTime E).space := by
  simp only [timeDerivL_heatCauchyPotentialL, heatCauchyPotentialL_apply, space_slabMk,
    time_slabMk, coe_slabTime]
  rw [laplacian_heatCauchyPotential g.contDiff g.norm_fderiv_le_iteratedFDeriv_one
    g.norm_fderiv_fderiv_le_iteratedFDeriv_two]

variable (hab ha) in
/-- The operator norm of the Cauchy potential is at most `(1 + dim E) (1 + M_α)`, where
`M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`; in particular it is independent of the
slab. -/
theorem norm_heatCauchyPotentialL_le :
    ‖heatCauchyPotentialL (α := α) (E := E) (F := F) hab ha‖ ≤
      (1 + Module.finrank ℝ E) * (1 + heatKernelMoment E α) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g ↦ by
    rw [heatCauchyPotentialL_eq_potential]
    exact norm_potential_le hab ha g

/-- **Attainment of the initial datum.** On the slab `E × [0, b]`, the initial trace of the Cauchy
potential of `g` is `g`. -/
theorem spatialTrace_heatCauchyPotentialL_left (hb : 0 < b) (g : CkHolderSpace 2 α E F) :
    (heatCauchyPotentialL hb le_rfl g).spatialTrace ⟨0, left_mem_Icc.2 hb.le⟩ = g := by
  ext x
  simp

end TauCeti
