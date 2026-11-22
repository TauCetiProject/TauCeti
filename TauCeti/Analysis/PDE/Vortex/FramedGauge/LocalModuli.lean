/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Analysis.PDE.Vortex.SobolevScale
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.PDE.Vortex.WeakKernel

/-!
# The local moduli of framed plane vortices in the Coulomb slice

Let `k ≥ 2` and let `x` be a continuous framed degree-`m` plane vortex of
`A_m^(k+1) = x_m + H^(k+1)(ℂ; ℝ⁴)` lying in every `A_m^j`, such as the smooth vortices
normalized at their end (`TauCeti.Vortex.exists_contDiff_sobolevVortexDivisor_eq`). In the real
chart of `A_m^(k+1)` (`TauCeti.Vortex.SobolevFieldSpace.realSubRef`), whose coordinates are the
real Hilbert space `(H^(k+1)_ℝ)⁴`, this file shows that near `x` the vortices in the Coulomb slice
through `x` form a real-analytic submanifold of dimension `2m`, tangent to the kernel of the
gauge-fixed operator.

**The gauge-fixed operator.** At real coordinates `u`, the gauge-fixing row `d₀*`
(`TauCeti.Vortex.realSobolevGaugeAdjoint`) and the linearized equation `d₁`
(`TauCeti.Vortex.realSobolevLinearizedEquation`) form the bounded operator

`L = d₀* ⊕ d₁ : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`

(`TauCeti.Vortex.realSobolevGaugeFixedOperator`). At the coordinates of a field `x` it is the
classical gauge-fixed operator `L_x` on the field `continuousRepField v` of continuous
representatives of `v` (`realSobolevGaugeFixedOperator_apply_eq_iff`). At a vortex `x` lying in
every `A_m^j`:

* `L` is onto (`realSobolevGaugeFixedOperator_surjective`), by the weak right inverse of `L_x`,
  which gains one Sobolev derivative (`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_`
  `gaugeFixedAdjoint_eq_and_mem_sobolevFields_add_one`), and the agreement of `C¹` weak and
  classical solutions;
* its kernel is the classical kernel `TauCeti.Vortex.gaugeFixedKernel x` of `L_x`, through
  `v ↦ continuousRepField v` (`kerRealSobolevGaugeFixedOperatorEquiv`), since kernel elements are
  smooth by elliptic regularity; so it has dimension `2m`
  (`finrank_ker_realSobolevGaugeFixedOperator`).

**The slice equation.** The Coulomb slice through `x` is the affine subspace
`d₀*_x (y - x) = 0`. On it the vortex equation is the map

`v ↦ (d₀*_x (v - u_x), equation (x_m + v)) : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`

(`TauCeti.Vortex.realSobolevSliceEquation`), where `u_x` are the real coordinates of `x`. Its zeros
at the coordinates of a field `y` are exactly the vortices in the Coulomb slice through `x`
(`realSobolevSliceEquation_realSubRef_eq_zero_iff`). It is analytic, with derivative `L` at `u_x`
(`hasStrictFDerivAt_realSobolevSliceEquation`). Since `L` is onto with a finite-dimensional, hence
complemented, kernel, the implicit function theorem
(`HasStrictFDerivAt.exists_isSliceChart_preimage_zero`) gives a **slice chart**: a real-analytic
chart of `(H^(k+1)_ℝ)⁴` with real-analytic inverse, defined around `u_x`, which flattens the zeros
of the slice equation onto the `2m`-dimensional space `ker L`
(`exists_isSliceChart_realSobolevSliceEquation`).

That each nearby gauge orbit meets the slice, which would make the vortices in the slice a chart of
the quotient `A_m^(k+1) / G_(k+2)`, is not treated here.

## Main definitions

* `TauCeti.Vortex.realSobolevGaugeFixedOperator`: the gauge-fixed operator on real coordinates.
* `TauCeti.Vortex.kerRealSobolevGaugeFixedOperatorEquiv`: its kernel at a vortex is the classical
  kernel.
* `TauCeti.Vortex.realSobolevSliceEquation`: the vortex equation in the Coulomb slice.

## Main results

* `TauCeti.Vortex.realSobolevGaugeFixedOperator_surjective`: `L` is onto at a vortex.
* `TauCeti.Vortex.finrank_ker_realSobolevGaugeFixedOperator`: its kernel has dimension `2m`.
* `TauCeti.Vortex.realSobolevSliceEquation_realSubRef_eq_zero_iff`: the zeros of the slice
  equation are the vortices in the Coulomb slice.
* `TauCeti.Vortex.exists_isSliceChart_realSobolevSliceEquation`: near a vortex, the vortices in
  its Coulomb slice form a real-analytic submanifold of dimension `2m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace MeasureTheory Module
open scoped BesselPotentialSpace RealInnerProductSpace ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-! ### The gauge-fixed operator on real coordinates -/

variable (f m) in
/-- **The real gauge-fixed vortex operator.** For an integer `k ≥ 2` and real coordinates `u` of a
field `x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` as a bounded real-linear operator
`(H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`: the gauge-fixing row `realSobolevGaugeAdjoint` followed by the
linearized equation `realSobolevLinearizedEquation`. On the coordinates of a field it computes the
classical operator `gaugeFixedOperator x` (`realSobolevGaugeFixedOperator_apply_eq_iff`). -/
def realSobolevGaugeFixedOperator (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) →L[ℝ]
      realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) ×
        (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) :=
  (realSobolevGaugeAdjoint f m hk u).prod (realSobolevLinearizedEquation f m hk u)

@[simp]
theorem realSobolevGaugeFixedOperator_apply (hk : 2 ≤ k)
    (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    realSobolevGaugeFixedOperator f m hk u v =
      (realSobolevGaugeAdjoint f m hk u v, realSobolevLinearizedEquation f m hk u v) :=
  (rfl)

/-- **The real gauge-fixed operator computes `L_x`.** At the real coordinates of a field `x` of
`A_m^(k+1)`, `k ≥ 2`, the real gauge-fixed operator sends `v` to `(g₀, g)` exactly when the
classical operator `L_x` sends the field of real coordinates `v` to the field of real coordinates
`(g₀, g₁, g₂, g₃)` of `H^k_ℝ`. -/
theorem realSobolevGaugeFixedOperator_apply_eq_iff (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le)
    (g : realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) ×
      (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k))) :
    realSobolevGaugeFixedOperator f m hk (x.realSubRef _) v = g ↔
      gaugeFixedOperator x (continuousRepField v) =
        continuousRepField (Fin.cons g.1 g.2 : Fin 4 → realSubmodule ℂ k.cast_nonneg) := by
  have hinj := continuousRep_injective (h := k.cast_nonneg)
    (finrank_real_complex_lt_two_mul ((Nat.one_lt_cast (α := ℝ)).2 hk))
  constructor
  · rintro rfl
    funext z
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp only [gaugeFixedOperator_apply_zero, continuousRepField_apply, Fin.cons_zero,
        realSobolevGaugeFixedOperator_apply, continuousRep_realSobolevGaugeAdjoint]
    · simp only [gaugeFixedOperator_apply_succ, continuousRepField_apply, Fin.cons_succ,
        realSobolevGaugeFixedOperator_apply, continuousRep_realSobolevLinearizedEquation]
  · intro h
    refine Prod.ext (hinj ?_) (funext fun i ↦ hinj ?_)
    · rw [realSobolevGaugeFixedOperator_apply, continuousRep_realSobolevGaugeAdjoint]
      funext z
      simpa only [gaugeFixedOperator_apply_zero, continuousRepField_apply, Fin.cons_zero] using
        congrArg (fun w ↦ w z 0) h
    · rw [realSobolevGaugeFixedOperator_apply, continuousRep_realSobolevLinearizedEquation]
      funext z
      simpa only [gaugeFixedOperator_apply_succ, continuousRepField_apply, Fin.cons_succ] using
        congrArg (fun w ↦ w z i.succ) h

/-- **The real gauge-fixed operator is onto at a vortex.** Let `k ≥ 2` and let `x` be a
continuous plane vortex of `A_m^(k+1)` lying in every `A_m^j`. Then the gauge-fixed operator
`L_x : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` at the real coordinates of `x` is onto. -/
theorem realSobolevGaugeFixedOperator_surjective (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x z = 0) :
    Function.Surjective (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)) := by
  intro g
  have hk₁ := (Nat.one_lt_cast (α := ℝ)).2 hk
  set F := continuousRepField (Fin.cons g.1 g.2 : Fin 4 → realSubmodule ℂ k.cast_nonneg)
  have hFk : F ∈ sobolevFields k := continuousRepField_mem_sobolevFields hk₁ _
  have hFc : Continuous F :=
    (contDiff_continuousRepField (n := 0) (by simpa using hk₁) _).continuous
  have hFL := memLp_of_mem_sobolevFields hFk
  -- The weak right inverse `Q` of `L_x` gains one derivative.
  obtain ⟨Q, hQ⟩ :=
    exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one
      x.continuous hmem hsol
  set q := Q (hFL.toLp F)
  have hq : (q : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields ((k : ℝ) + 1) :=
    (hQ _).2 k (mem_sobolevFields_of_ae_eq hFk hFL.coeFn_toLp.symm)
  -- `x_m + q` has a continuous representative `y` in `A_m^(k+1)`.
  have hmemq : referenceField f m + ⇑q ∈ framedFieldSpace f m ((k : ℝ) + 1) := by
    rwa [mem_framedFieldSpace, add_sub_cancel_left]
  obtain ⟨y, hy⟩ := SobolevFieldSpace.exists_ae_eq (by linarith) hmemq
  refine ⟨y.realSubRef _, ?_⟩
  rw [realSobolevGaugeFixedOperator_apply_eq_iff,
    SobolevFieldSpace.continuousRepField_realSubRef (by linarith)]
  have hy₁ : ContDiff ℝ 1 (⇑y - referenceField f m) :=
    (y.contDiff (n := 1) (by norm_cast; omega)).sub
      ((contDiff_referenceField f m).of_le (by simp))
  -- The `C¹` field `y - x_m` is a weak, hence classical, solution of `L_x (y - x_m) = F`.
  refine funext ((forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) x.continuous hy₁
    hFc).1 fun η hη hηc ↦ ?_)
  calc ∫ z, ⟪(⇑y - referenceField f m) z, gaugeFixedAdjoint x η z⟫
      = ∫ z, ⟪q z, gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hy.mono fun z hz ↦ by
          dsimp only
          rw [Pi.sub_apply, ← hz, Pi.add_apply, add_sub_cancel_left])
    _ = ∫ z, ⟪hFL.toLp F z, η z⟫ :=
        (hQ _).1.isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by norm_cast)) hηc
    _ = ∫ z, ⟪F z, η z⟫ := integral_congr_ae (hFL.coeFn_toLp.mono fun z hz ↦ by
          dsimp only
          rw [hz])

/-! ### The kernel at a vortex -/

/-- The field of real coordinates of an element of the kernel of `L` at a vortex lies in the
classical kernel of `L_x`. -/
private theorem continuousRepField_mem_gaugeFixedKernel (hk : 2 ≤ k)
    {x : SobolevFieldSpace f m ((k : ℝ) + 1)} (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    {v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le}
    (hv : realSobolevGaugeFixedOperator f m hk (x.realSubRef _) v = 0) :
    continuousRepField v ∈ gaugeFixedKernel x := by
  have hy₁ := contDiff_continuousRepField (n := 1) (by norm_cast; omega) v
  have hyL := memLp_of_mem_sobolevFields <| continuousRepField_mem_sobolevFields
    (((Nat.one_lt_cast (α := ℝ)).2 hk).trans (lt_add_one _)) v
  have heq : ∀ z, gaugeFixedOperator x (continuousRepField v) z = 0 := by
    intro z
    rw [(realSobolevGaugeFixedOperator_apply_eq_iff hk x v 0).1 hv]
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp
  -- Classical `L²` solutions of `L_x y = 0` are smooth.
  have hsmooth := contDiff_of_gaugeFixedOperator_eq (f := 0)
    (contDiff_of_forall_mem_framedFieldSpace x.continuous hmem)
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace x.continuous i n
      (hmem (n + 2))) hy₁ hyL (fun _ ↦ zero_mem _) heq
  exact mem_gaugeFixedKernel.2 ⟨hsmooth.of_le (by simp), hyL, heq⟩

/-- Every element of the classical kernel of `L_x` at a vortex is the field of real coordinates
of an element of the kernel of `L`. -/
private theorem exists_continuousRepField_eq (hk : 2 ≤ k)
    {x : SobolevFieldSpace f m ((k : ℝ) + 1)} (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ∃ v, realSobolevGaugeFixedOperator f m hk (x.realSubRef _) v = 0 ∧
      continuousRepField v = y := by
  obtain ⟨hy₂, hyL, heq⟩ := mem_gaugeFixedKernel.1 hy
  have hk₁ := (Nat.one_lt_cast (α := ℝ)).2 hk
  have hxs := contDiff_of_forall_mem_framedFieldSpace x.continuous hmem
  -- `y` is a weak solution of `L_x y = 0`, so it lies in `H^(k+1)`.
  have hyk : y ∈ sobolevFields ((k : ℝ) + 1) := by
    refine mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hxs
      (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace x.continuous i n
        (hmem (n + 2))) hyL (zero_mem _) fun η hη hηc ↦ ?_
    exact (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) x.continuous
      (hy₂.of_le (by norm_num)) continuous_zero).2 heq η hη hηc
  set Y : SobolevFieldSpace f m ((k : ℝ) + 1) :=
    ⟨referenceField f m + y, by rwa [mem_framedFieldSpace, add_sub_cancel_left],
      (contDiff_referenceField f m).continuous.add hy₂.continuous⟩
  have hY : continuousRepField (Y.realSubRef (k.cast_add_one_pos (α := ℝ)).le) = y := by
    rw [SobolevFieldSpace.continuousRepField_realSubRef (by linarith)]
    exact add_sub_cancel_left _ _
  refine ⟨Y.realSubRef _, (realSobolevGaugeFixedOperator_apply_eq_iff hk x _ 0).2 ?_, hY⟩
  rw [hY]
  funext z
  ext j
  rw [heq z]
  refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp

variable (f m) in
/-- **The kernel of `L` at a vortex is the classical kernel.** Let `k ≥ 2` and let `x` be a
continuous plane vortex of `A_m^(k+1)` lying in every `A_m^j`. The field of real coordinates
`v ↦ continuousRepField v` identifies the kernel of the real gauge-fixed operator at the
coordinates of `x` with the kernel `gaugeFixedKernel x` of the classical operator `L_x` on `C²`,
square-integrable fields. -/
def kerRealSobolevGaugeFixedOperatorEquiv (hk : 2 ≤ k) (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j) :
    (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker ≃ₗ[ℝ] gaugeFixedKernel x :=
  LinearEquiv.ofBijective
    ((continuousRepField ∘ₗ
      (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker.subtype).codRestrict _
        fun v ↦ continuousRepField_mem_gaugeFixedKernel hk hmem v.property)
    ⟨fun v w hvw ↦ Subtype.ext <| continuousRepField_injective
      (((Nat.one_lt_cast (α := ℝ)).2 hk).trans (lt_add_one _)) (congrArg Subtype.val hvw),
    fun y ↦ by
      obtain ⟨v, hv, hvy⟩ := exists_continuousRepField_eq hk hmem y.property
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

@[simp]
theorem coe_kerRealSobolevGaugeFixedOperatorEquiv_apply (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    (v : (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker) :
    (kerRealSobolevGaugeFixedOperatorEquiv f m hk x hmem v : ℂ → EuclideanSpace ℝ (Fin 4)) =
      continuousRepField (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :=
  (rfl)

/-- **The kernel of `L` at a vortex is finite dimensional.** -/
theorem finiteDimensional_ker_realSobolevGaugeFixedOperator (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x z = 0) :
    FiniteDimensional ℝ (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace x.continuous hmem
  have := finiteDimensional_gaugeFixedKernel (hxs.of_le (by simp)) (fun w ↦ by simp [hsol w])
    (tendsto_sectionValue_mul_inv_pow (((Nat.one_lt_cast (α := ℝ)).2 hk).trans (lt_add_one _))
      x.mem_framedFieldSpace x.continuous)
  exact (kerRealSobolevGaugeFixedOperatorEquiv f m hk x hmem).symm.finiteDimensional

/-- **The kernel of `L` at a vortex has dimension `2m`** (Taubes), the dimension of the divisor
space `Sym^m ℂ`. -/
theorem finrank_ker_realSobolevGaugeFixedOperator (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x z = 0) :
    finrank ℝ (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker = 2 * m := by
  rw [(kerRealSobolevGaugeFixedOperatorEquiv f m hk x hmem).finrank_eq]
  exact finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace
    (((Nat.one_lt_cast (α := ℝ)).2 hk).trans (lt_add_one _)) x.mem_framedFieldSpace
    (contDiff_of_forall_mem_framedFieldSpace x.continuous hmem) fun w ↦ by simp [hsol w]

/-! ### The vortex equation in the Coulomb slice -/

variable (f m) in
/-- **The vortex equation in the Coulomb slice** through a field `x` of `A_m^(k+1)`, `k ≥ 2`, on
real coordinates `v ∈ (H^(k+1)_ℝ)⁴`: the gauge-fixing row `d₀*_x (v - u_x)`, where `u_x` are the
real coordinates of `x`, together with the vortex equation `realSobolevEquation` at `v`. Its zeros
at the coordinates of a field `y` are the vortices `y` in the Coulomb slice `d₀*_x (y - x) = 0`
(`realSobolevSliceEquation_realSubRef_eq_zero_iff`). -/
def realSobolevSliceEquation (hk : 2 ≤ k) (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) ×
      (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) :=
  (realSobolevGaugeAdjoint f m hk (x.realSubRef _) (v - x.realSubRef _),
    realSobolevEquation f m hk v)

theorem realSobolevSliceEquation_apply (hk : 2 ≤ k) (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    realSobolevSliceEquation f m hk x v =
      (realSobolevGaugeAdjoint f m hk (x.realSubRef _) (v - x.realSubRef _),
        realSobolevEquation f m hk v) :=
  (rfl)

/-- **The zeros of the slice equation are the vortices in the Coulomb slice.** For fields `x` and
`y` of `A_m^(k+1)`, `k ≥ 2`, the slice equation through `x` vanishes at the real coordinates of `y`
exactly when `y` is a vortex with `d₀*_x (y - x) = 0`. -/
theorem realSobolevSliceEquation_realSubRef_eq_zero_iff (hk : 2 ≤ k)
    (x y : SobolevFieldSpace f m ((k : ℝ) + 1)) :
    realSobolevSliceEquation f m hk x (y.realSubRef _) = 0 ↔
      gaugeAdjoint x (⇑y - ⇑x) = 0 ∧ equation y = 0 := by
  have hs := ((Nat.one_lt_cast (α := ℝ)).2 hk).trans (lt_add_one _)
  have hinj := continuousRep_injective (h := k.cast_nonneg)
    (finrank_real_complex_lt_two_mul ((Nat.one_lt_cast (α := ℝ)).2 hk))
  have hfield : continuousRepField (y.realSubRef _ - x.realSubRef _ :
      Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) = ⇑y - ⇑x := by
    rw [map_sub, SobolevFieldSpace.continuousRepField_realSubRef hs,
      SobolevFieldSpace.continuousRepField_realSubRef hs, sub_sub_sub_cancel_right]
  rw [realSobolevSliceEquation_apply, Prod.mk_eq_zero, realSobolevEquation_realSubRef_eq_zero_iff,
    ← hinj.eq_iff, continuousRep_realSobolevGaugeAdjoint, hfield, map_zero]

/-- The slice equation is real-analytic. -/
theorem contDiff_realSobolevSliceEquation (hk : 2 ≤ k) (x : SobolevFieldSpace f m ((k : ℝ) + 1)) :
    ContDiff ℝ ω (realSobolevSliceEquation f m hk x) :=
  (((realSobolevGaugeAdjoint f m hk (x.realSubRef _)).contDiff).comp
    (contDiff_id.sub contDiff_const)).prodMk (contDiff_realSobolevEquation hk)

/-- **The derivative of the slice equation** at real coordinates `v` is the gauge-fixing row at `x`
followed by the linearized equation at `v`. -/
theorem hasFDerivAt_realSobolevSliceEquation (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1))
    (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    HasFDerivAt (realSobolevSliceEquation f m hk x)
      ((realSobolevGaugeAdjoint f m hk (x.realSubRef _)).prod
        (realSobolevLinearizedEquation f m hk v)) v := by
  have h₁ : HasFDerivAt (fun w ↦ realSobolevGaugeAdjoint f m hk (x.realSubRef _)
      (w - x.realSubRef _)) (realSobolevGaugeAdjoint f m hk (x.realSubRef _)) v := by
    simpa only [map_sub] using
      (realSobolevGaugeAdjoint f m hk (x.realSubRef _)).hasFDerivAt.sub_const
        (realSobolevGaugeAdjoint f m hk (x.realSubRef _) (x.realSubRef _))
  exact h₁.prodMk (hasFDerivAt_realSobolevEquation hk v)

/-- **The slice equation is strictly differentiable at `x`** with derivative the gauge-fixed
operator `L` at the real coordinates of `x`. -/
theorem hasStrictFDerivAt_realSobolevSliceEquation (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) :
    HasStrictFDerivAt (realSobolevSliceEquation f m hk x)
      (realSobolevGaugeFixedOperator f m hk (x.realSubRef _)) (x.realSubRef _) := by
  have hL : realSobolevGaugeFixedOperator f m hk (x.realSubRef _) =
      (realSobolevGaugeAdjoint f m hk (x.realSubRef _)).prod
        (realSobolevLinearizedEquation f m hk (x.realSubRef _)) := by
    ext1 v
    rw [realSobolevGaugeFixedOperator_apply, ContinuousLinearMap.prod_apply]
  rw [hL]
  exact (contDiff_realSobolevSliceEquation hk x).contDiffAt.hasStrictFDerivAt
    (hasFDerivAt_realSobolevSliceEquation hk x _) (by simp)

/-! ### The slice chart -/

/-- **Near a vortex, the vortices in its Coulomb slice form a real-analytic submanifold of
dimension `2m`.** Let `k ≥ 2` and let `x` be a continuous plane vortex of `A_m^(k+1)` lying in
every `A_m^j`. There is a real-analytic chart `e` of `(H^(k+1)_ℝ)⁴` with real-analytic inverse,
defined around the real coordinates `u_x` of `x`, which flattens the zeros of the slice equation
through `x`, that is the vortices in the Coulomb slice through `x`
(`realSobolevSliceEquation_realSubRef_eq_zero_iff`), onto the kernel of the gauge-fixed operator
`L` at `u_x`, a space of dimension `2m` (`finrank_ker_realSobolevGaugeFixedOperator`). This is the
implicit function theorem: the slice equation is analytic with derivative `L` at `u_x`, and `L` is
onto (`realSobolevGaugeFixedOperator_surjective`) with a finite-dimensional, hence complemented,
kernel. -/
theorem exists_isSliceChart_realSobolevSliceEquation (hk : 2 ≤ k)
    (x : SobolevFieldSpace f m ((k : ℝ) + 1)) (hmem : ∀ j : ℕ, ⇑x ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x z = 0) :
    ∃ e : OpenPartialHomeomorph (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le)
        (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le),
      x.realSubRef _ ∈ e.source ∧ (∀ v ∈ e.source, ContDiffAt ℝ ω e v) ∧
        (∀ v ∈ e.target, ContDiffAt ℝ ω e.symm v) ∧
        IsSliceChart e ((realSobolevGaugeFixedOperator f m hk (x.realSubRef _)).ker : Set _)
          (realSobolevSliceEquation f m hk x ⁻¹' {0}) := by
  have := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x hmem hsol
  obtain ⟨e, hxe, -, he, hesymm, hslice⟩ :=
    (hasStrictFDerivAt_realSobolevSliceEquation hk x).exists_isSliceChart_preimage_zero
      (LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x hmem hsol))
      (Submodule.ClosedComplemented.of_finiteDimensional _) isOpen_univ (Set.mem_univ _)
      fun v _ ↦ (contDiff_realSobolevSliceEquation hk x).contDiffAt
  exact ⟨e, hxe, he, hesymm, hslice⟩

end TauCeti.Vortex
