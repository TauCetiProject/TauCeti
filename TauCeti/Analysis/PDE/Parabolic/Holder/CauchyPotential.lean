/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Analysis.InnerProductSpace.Laplacian.Holder

/-!
# The Cauchy heat potential in the order-two parabolic Hölder space

Let `0 ≤ a < b` and `0 ≤ α`. For an initial datum `g ∈ C_b^{2,α}(E)` (`CkHolderSpace 2 α E F`),
the Cauchy heat potential `u(t, x) = ∫ K_1(y) g(x - √t • y) dy` (`TauCeti.heatCauchyPotential`)
restricted to the slab `E × [a, b]` lies in the bounded order-two parabolic Hölder space
`C_b^{2+α,1+α/2}(E × [a, b])` (`ParabolicC2HolderSpace`). Its derivative fields are again Cauchy
potentials: those of `Dg` and `D²g` in space, and of `Δg` in time. In particular `u` solves the
heat equation `∂ₜu = Δu` on the closed slab, including the one-sided derivative at `t = a`, and
its trace at time `0` is `g`.

The map `g ↦ u` is a continuous linear operator
`ParabolicC2HolderSpace.heatCauchyPotentialL`, and

`‖u‖ ≤ (n + 1) (1 + M_α) ‖g‖`,

where `n` is the dimension of `E` and `M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`.
The constant depends neither on the slab nor on `F`. The supremum terms of the norm come from the
maximum principle `‖u‖_∞ ≤ ‖g‖_∞` applied to `g`, `Dg`, `D²g` and `Δg`; the parabolic Hölder
seminorms of `D²u` and `∂ₜu` come from the parabolic Hölder estimate of the Cauchy potential
(`TauCeti.holderWith_heatCauchyPotential`) applied to `D²g` and `Δg`, using
`[Δg]_α ≤ n [D²g]_α`.

This operator gives the initial-value part of the solution of the Cauchy problem
`∂ₜu - Δu = f`, `u(·, 0) = g`, in parabolic Hölder spaces.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.heatCauchyPotentialL`: the Cauchy heat potential as a continuous
  linear map `C_b^{2,α}(E) → C_b^{2+α,1+α/2}(E × [a, b])`.
* `TauCeti.ParabolicC2HolderSpace.timeDerivL_heatCauchyPotentialL_eq_laplacian`: the heat
  equation `∂ₜu = Δu` on the closed slab.
* `TauCeti.ParabolicC2HolderSpace.spatialTrace_heatCauchyPotentialL`: the trace at time `0` is the
  initial datum.
* `TauCeti.ParabolicC2HolderSpace.norm_heatCauchyPotentialL_apply_le`: the norm estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (the Cauchy problem for the heat equation in parabolic Hölder spaces).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime InnerProductSpace Laplacian Module
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A local shortcut for the norm on curried Hessians, which otherwise only arises as a nested
instance problem during unification. -/
local instance instNormedAddCommGroupCurriedHessian :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on curried Hessians. -/
local instance instNormedSpaceCurriedHessian : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

section Field

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {M : ℝ}

variable (a b) in
/-- The Cauchy heat potential of a bounded continuous datum on the slab `E × [a, b]`, as a
bounded continuous field. -/
private def potentialField (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) :
    slab (E := E) a b →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => heatCauchyPotential f (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space)
    ((continuous_heatCauchyPotential hfc hM).comp continuous_subtype_val) M
    (fun _ => norm_heatCauchyPotential_le hM _ _)

private theorem potentialField_apply (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M)
    (p : slab (E := E) a b) :
    potentialField a b hfc hM p =
      heatCauchyPotential f (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space :=
  (rfl)

private theorem potentialField_slabMk (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) (x : E)
    (t : Icc a b) : potentialField a b hfc hM (slabMk x t) = heatCauchyPotential f t x := by
  rw [potentialField_apply, space_slabMk, time_slabMk]

private theorem norm_potentialField_le (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) (hM₀ : 0 ≤ M) :
    ‖potentialField a b hfc hM‖ ≤ M :=
  (BoundedContinuousFunction.norm_le hM₀).2 fun _ => norm_heatCauchyPotential_le hM _ _

private theorem holderWith_potentialField (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) {H : ℝ≥0}
    (hH : HolderWith H α f) :
    HolderWith (H * (1 + heatKernelMoment E α)) α (potentialField a b hfc hM) :=
  ((holderWith_heatCauchyPotential hH hfc).holderOnWith (slab a b)).holderWith

variable (a b) in
/-- The Cauchy heat potential of a bounded continuous Hölder datum on the slab `E × [a, b]`, as a
parabolically Hölder field. -/
private def potentialHolder (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) {H : ℝ≥0}
    (hH : HolderWith H α f) : HolderSpace α (slab (E := E) a b) G :=
  HolderSpace.ofBoundedContinuousFunction (potentialField a b hfc hM)
    (holderWith_potentialField hfc hM hH).memHolder

private theorem potentialHolder_slabMk (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) {H : ℝ≥0}
    (hH : HolderWith H α f) (x : E) (t : Icc a b) :
    potentialHolder a b hfc hM hH (slabMk x t) = heatCauchyPotential f t x := by
  rw [potentialHolder, HolderSpace.ofBoundedContinuousFunction_apply, potentialField_slabMk]

private theorem norm_potentialHolder_le (hfc : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) (hM₀ : 0 ≤ M)
    {H : ℝ≥0} (hH : HolderWith H α f) :
    ‖potentialHolder a b hfc hM hH‖ ≤ M + H * (1 + heatKernelMoment E α) := by
  rw [HolderSpace.norm_def, potentialHolder,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  gcongr
  · exact norm_potentialField_le hfc hM hM₀
  · exact_mod_cast (holderWith_potentialField hfc hM hH).nnholderNorm_le

end Field

section Datum

variable (g : CkHolderSpace 2 α E F)

private theorem contDiff_two : ContDiff ℝ 2 g := by
  exact_mod_cast g.contDiff

private theorem norm_iteratedFDeriv_le_iteratedFDeriv (i : Fin 3) (y : E) :
    ‖iteratedFDeriv ℝ i g y‖ ≤ ‖g.iteratedFDeriv i‖ := by
  rw [CkHolderSpace.iteratedFDeriv_eq]
  exact (g.iteratedFDeriv i).norm_coe_le_norm y

private theorem norm_apply_le_iteratedFDeriv_zero (y : E) : ‖g y‖ ≤ ‖g.iteratedFDeriv 0‖ := by
  simpa using norm_iteratedFDeriv_le_iteratedFDeriv g 0 y

private theorem norm_fderiv_le_iteratedFDeriv_one (y : E) :
    ‖fderiv ℝ g y‖ ≤ ‖g.iteratedFDeriv 1‖ := by
  simpa using norm_iteratedFDeriv_le_iteratedFDeriv g 1 y

private theorem norm_iteratedFDeriv_two_le (y : E) :
    ‖iteratedFDeriv ℝ 2 g y‖ ≤ ‖g.iteratedFDeriv 2‖ := by
  simpa using norm_iteratedFDeriv_le_iteratedFDeriv g 2 y

private theorem norm_fderiv_fderiv_le_iteratedFDeriv_two (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ ‖g.iteratedFDeriv 2‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact norm_iteratedFDeriv_two_le g y

/-- The curried Hessian of `g` has the Hölder constant of its second iterated derivative. -/
private theorem holderWith_fderiv_fderiv :
    HolderWith (nnHolderNorm α (iteratedFDeriv ℝ 2 g)) α (fderiv ℝ (fderiv ℝ g)) := by
  have he : (fun y => continuousMultilinearCurryFin2 ℝ E F (iteratedFDeriv ℝ 2 g y)) =
      fderiv ℝ (fderiv ℝ g) := by
    funext y
    ext v w
    rw [continuousMultilinearCurryFin2_apply, _root_.iteratedFDeriv_two_apply]
    simp
  simpa [Function.comp_def, he] using
    (continuousMultilinearCurryFin2 ℝ E F).isometry.lipschitzWith.holderWith.comp
      g.memHolder_iteratedFDeriv.holderWith

private theorem continuous_fderiv_fderiv : Continuous (fderiv ℝ (fderiv ℝ g)) :=
  ((contDiff_two g).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero

variable [FiniteDimensional ℝ E]

private theorem norm_laplacian_le_iteratedFDeriv_two (y : E) :
    ‖Δ (⇑g) y‖ ≤ finrank ℝ E * ‖g.iteratedFDeriv 2‖ :=
  (norm_laplacian_le g y).trans (by gcongr; exact norm_iteratedFDeriv_two_le g y)

private theorem holderWith_laplacian_datum :
    HolderWith (finrank ℝ E * nnHolderNorm α (iteratedFDeriv ℝ 2 g)) α (Δ (⇑g)) :=
  holderWith_laplacian g.memHolder_iteratedFDeriv.holderWith

end Datum

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

variable (hab) in
/-- The Cauchy heat potential of `g ∈ C_b^{2,α}(E)` on the slab `E × [a, b]`, `0 ≤ a`, with its
derivative fields. -/
private def heatCauchyPotentialAux (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F) :
    ParabolicC2HolderSpace α E F hab :=
  mk (potentialField a b (contDiff_two g).continuous (norm_apply_le_iteratedFDeriv_zero g))
    (potentialField a b ((contDiff_two g).continuous_fderiv two_ne_zero)
      (norm_fderiv_le_iteratedFDeriv_one g))
    (potentialHolder a b (continuous_fderiv_fderiv g)
      (norm_fderiv_fderiv_le_iteratedFDeriv_two g) (holderWith_fderiv_fderiv g))
    (potentialHolder a b (contDiff_two g).continuous_laplacian
      (norm_laplacian_le_iteratedFDeriv_two g) (holderWith_laplacian_datum g))
    (fun t x => by
      simpa only [potentialField_slabMk] using hasFDerivAt_heatCauchyPotential
        ((contDiff_two g).differentiable two_ne_zero) ((contDiff_two g).continuous_fderiv
          two_ne_zero) (norm_fderiv_le_iteratedFDeriv_one g) t x)
    (fun t x => by
      simpa only [potentialField_slabMk, potentialHolder_slabMk] using
        hasFDerivAt_heatCauchyPotential (((contDiff_two g).fderiv_right (m := 1)
          (by norm_num)).differentiable one_ne_zero) (continuous_fderiv_fderiv g)
          (norm_fderiv_fderiv_le_iteratedFDeriv_two g) t x)
    (fun x t => by
      rw [potentialHolder_slabMk]
      refine ((hasDerivWithinAt_heatCauchyPotential (contDiff_two g)
        (norm_apply_le_iteratedFDeriv_zero g) (norm_fderiv_le_iteratedFDeriv_one g)
        (norm_fderiv_fderiv_le_iteratedFDeriv_two g) (ha.trans t.2.1) x).mono
          (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 ha))).congr_of_mem (fun s hs => ?_) t.2
      rw [timeExtension_of_mem hab.le _ x ⟨s, hs⟩, potentialField_slabMk])

private theorem heatCauchyPotentialAux_apply (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    heatCauchyPotentialAux hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialAux, mk_apply, potentialField_apply]

/-- The norm estimate behind `heatCauchyPotentialL`. -/
private theorem norm_heatCauchyPotentialAux_le (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F) :
    ‖heatCauchyPotentialAux hab ha g‖ ≤
      (finrank ℝ E + 1) * (1 + heatKernelMoment E α) * ‖g‖ := by
  set n : ℝ := (finrank ℝ E : ℝ)
  set m : ℝ := (heatKernelMoment E α : ℝ)
  set H : ℝ := (nnHolderNorm α (iteratedFDeriv ℝ 2 g) : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hm : 0 ≤ m := NNReal.coe_nonneg _
  have hH : 0 ≤ H := NNReal.coe_nonneg _
  have h0 := norm_nonneg (g.iteratedFDeriv 0)
  have h1 := norm_nonneg (g.iteratedFDeriv 1)
  have h2 := norm_nonneg (g.iteratedFDeriv 2)
  have hu := norm_potentialField_le (a := a) (b := b) (contDiff_two g).continuous
    (norm_apply_le_iteratedFDeriv_zero g) h0
  have hux := norm_potentialField_le (a := a) (b := b)
    ((contDiff_two g).continuous_fderiv two_ne_zero) (norm_fderiv_le_iteratedFDeriv_one g) h1
  have huxx := norm_potentialHolder_le (a := a) (b := b) (continuous_fderiv_fderiv g)
    (norm_fderiv_fderiv_le_iteratedFDeriv_two g) h2 (holderWith_fderiv_fderiv g)
  have hut := norm_potentialHolder_le (a := a) (b := b) (contDiff_two g).continuous_laplacian
    (norm_laplacian_le_iteratedFDeriv_two g) (mul_nonneg hn h2) (holderWith_laplacian_datum g)
  push_cast at huxx hut
  rw [norm_eq, heatCauchyPotentialAux, valueL_mk, spatialFDerivL_mk, spatialSecondFDerivL_mk,
    timeDerivL_mk, CkHolderSpace.norm_eq, Fin.sum_univ_three]
  -- Every term of the norm of `g` is multiplied by at most `(n + 1) (1 + m)`.
  have hK : 1 ≤ (n + 1) * (1 + m) := by nlinarith
  have hK₂ : n + 1 ≤ (n + 1) * (1 + m) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hK h0, mul_le_mul_of_nonneg_right hK h1,
    mul_le_mul_of_nonneg_right hK₂ h2]

variable (hab) in
/-- **The Cauchy heat potential in parabolic Hölder spaces.** For `0 ≤ a < b`, the Cauchy heat
potential `u(t, x) = ∫ K_1(y) g(x - √t • y) dy` of `g ∈ C_b^{2,α}(E)`, restricted to the slab
`E × [a, b]`, as a continuous linear map into `C_b^{2+α,1+α/2}(E × [a, b])`. -/
def heatCauchyPotentialL (ha : 0 ≤ a) :
    CkHolderSpace 2 α E F →L[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearMap.mkContinuous
    { toFun := heatCauchyPotentialAux hab ha
      map_add' := fun f g => ext fun p => by
        rw [add_apply, heatCauchyPotentialAux_apply, heatCauchyPotentialAux_apply,
          heatCauchyPotentialAux_apply, CkHolderSpace.coe_add]
        exact heatCauchyPotential_add (contDiff_two f).continuous (contDiff_two g).continuous
          (norm_apply_le_iteratedFDeriv_zero f) (norm_apply_le_iteratedFDeriv_zero g) _ _
      map_smul' := fun c g => ext fun p => by
        rw [RingHom.id_apply, smul_apply, heatCauchyPotentialAux_apply,
          heatCauchyPotentialAux_apply, CkHolderSpace.coe_smul, heatCauchyPotential_smul] }
    _ (norm_heatCauchyPotentialAux_le ha)

private theorem heatCauchyPotentialL_eq (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F) :
    heatCauchyPotentialL hab ha g = heatCauchyPotentialAux hab ha g := by
  rw [heatCauchyPotentialL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The Cauchy heat potential operator evaluates to the Cauchy heat potential. -/
@[simp]
theorem heatCauchyPotentialL_apply (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    heatCauchyPotentialL hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq, heatCauchyPotentialAux_apply]

/-- The spatial gradient of the Cauchy heat potential of `g` is the Cauchy heat potential of
`Dg`. -/
@[simp]
theorem spatialFDerivL_heatCauchyPotentialL (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    spatialFDerivL (heatCauchyPotentialL hab ha g) p = heatCauchyPotential (fderiv ℝ g)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq, heatCauchyPotentialAux, spatialFDerivL_mk, potentialField_apply]

/-- The spatial Hessian of the Cauchy heat potential of `g` is the Cauchy heat potential of
`D²g`. -/
@[simp]
theorem spatialSecondFDerivL_heatCauchyPotentialL (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    spatialSecondFDerivL (heatCauchyPotentialL hab ha g) p =
      heatCauchyPotential (fderiv ℝ (fderiv ℝ g))
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq, heatCauchyPotentialAux, spatialSecondFDerivL_mk, potentialHolder,
    HolderSpace.ofBoundedContinuousFunction_apply, potentialField_apply]

/-- The time derivative of the Cauchy heat potential of `g` is the Cauchy heat potential of
`Δg`. -/
@[simp]
theorem timeDerivL_heatCauchyPotentialL (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (p : slab (E := E) a b) :
    timeDerivL (heatCauchyPotentialL hab ha g) p =
      heatCauchyPotential (Δ (⇑g)) (p : ParabolicSpaceTime E).time
        (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq, heatCauchyPotentialAux, timeDerivL_mk, potentialHolder,
    HolderSpace.ofBoundedContinuousFunction_apply, potentialField_apply]

/-- **The heat equation.** The Cauchy heat potential `u` of `g ∈ C_b^{2,α}(E)` satisfies
`∂ₜu = Δu` on the closed slab `E × [a, b]`; at `t = a` the time derivative is the one-sided
derivative within `[a, b]`. -/
theorem timeDerivL_heatCauchyPotentialL_eq_laplacian (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    (x : E) (t : Icc a b) :
    timeDerivL (heatCauchyPotentialL hab ha g) (slabMk x t) =
      Δ (fun y => heatCauchyPotentialL hab ha g (slabMk y t)) x := by
  simp only [timeDerivL_heatCauchyPotentialL, heatCauchyPotentialL_apply, space_slabMk,
    time_slabMk]
  exact (laplacian_heatCauchyPotential (contDiff_two g) (norm_fderiv_le_iteratedFDeriv_one g)
    (norm_fderiv_fderiv_le_iteratedFDeriv_two g) t x).symm

/-- **The initial trace.** At time `0` the spatial trace of the Cauchy heat potential of `g` is
`g`. -/
theorem spatialTrace_heatCauchyPotentialL (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F)
    {t : Icc a b} (ht : (t : ℝ) = 0) :
    (heatCauchyPotentialL hab ha g).spatialTrace t = g := by
  ext x
  rw [spatialTrace_apply, heatCauchyPotentialL_apply, space_slabMk, time_slabMk, ht,
    heatCauchyPotential_zero]

/-- **The Schauder estimate of the Cauchy heat potential.** In dimension `n`,
`‖u‖ ≤ (n + 1) (1 + M_α) ‖g‖` for the Cauchy heat potential `u` of `g ∈ C_b^{2,α}(E)` on any
slab `E × [a, b]` with `0 ≤ a`, where `M_α = ∫ ‖y‖^α K_1(y) dy` is `TauCeti.heatKernelMoment`. -/
theorem norm_heatCauchyPotentialL_apply_le (ha : 0 ≤ a) (g : CkHolderSpace 2 α E F) :
    ‖heatCauchyPotentialL hab ha g‖ ≤ (finrank ℝ E + 1) * (1 + heatKernelMoment E α) * ‖g‖ := by
  rw [heatCauchyPotentialL_eq]
  exact norm_heatCauchyPotentialAux_le ha g

end TauCeti.ParabolicC2HolderSpace
