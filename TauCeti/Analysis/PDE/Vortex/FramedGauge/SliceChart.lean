/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.PDE.Vortex.SobolevScale
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.PDE.Vortex.WeakKernel

/-!
# The gauge-fixed vortex operator on the Sobolev scale and the Coulomb slice chart

The continuous framed degree-`m` plane vortex fields of `A_m^(k+1) = x_m + H^(k+1)(ℂ; ℝ⁴)` are
identified, through the real coordinates of `x - x_m`, with the real Hilbert space `(H^(k+1)_ℝ)⁴`
(`TauCeti.Vortex.SobolevFieldSpace.realSubRefHomeomorph`), and in these coordinates the vortex
equation is the real-analytic map `TauCeti.Vortex.realSobolevEquation f m hk`. This file builds
the local model of the moduli space of vortices near a vortex `x₀`: the vortices in the Coulomb
slice through `x₀` form, near `x₀`, a space homeomorphic to an open subset of `ℝ^(2m)`.

**The gauge-fixed operator.** For an integer `k ≥ 2` and real coordinates `u` of a field `x`, the
gauge-fixed operator `L_x = d₀* ⊕ d₁` is the bounded real-linear operator

`realSobolevGaugeFixedOperator f m hk u : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`

built from the gauge-fixing row `realSobolevGaugeAdjoint` and the linearized equation
`realSobolevLinearizedEquation`. It is the pointwise operator `gaugeFixedOperator` of the fields
(`realSobolevGaugeFixedOperator_eq_iff`): the continuous representatives of its rows are the rows
of `L_x y`, where `y = continuousRepField v` is the field of the variation `v`. Let `x₀` be a
continuous vortex of `A_m^(k+1)` lying in `A_m^j` for every `j`, for instance any vortex in the
Coulomb slice through such a field (`TauCeti.Vortex.mem_framedFieldSpace_of_equation_eq_zero`).
Then:

* the kernel of `L_{x₀}` is identified with the classical kernel `gaugeFixedKernel x₀` by taking
  fields (`kerRealSobolevGaugeFixedOperatorEquiv`); in particular it has dimension `2m`
  (`finrank_ker_realSobolevGaugeFixedOperator_eq_two_mul`), independently of `k`;
* `L_{x₀}` is onto (`realSobolevGaugeFixedOperator_surjective`): a continuous `f ∈ H^k` is
  `L_{x₀} y` for the continuous representative `y ∈ H^(k+1)` of the image of `f` under the weak
  right inverse of `L_{x₀}`, which gains one derivative by the elliptic bootstrap of
  `TauCeti.Analysis.PDE.Vortex.SobolevScale`, and solves `L_{x₀} y = f` classically;
* hence `L_{x₀}` is Fredholm (`isFredholm_realSobolevGaugeFixedOperator`) of index `2m`
  (`index_realSobolevGaugeFixedOperator_eq_two_mul`). This is Taubes's index theorem on the Sobolev
  scale `H^(k+1) → H^k`, on which the vortex equation is smooth; the corresponding statement for
  `H¹ → L²` is `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`.

**The Coulomb slice chart.** The Coulomb slice map through the real coordinates `u₀` of `x₀`,

`coulombSliceMap f m hk u₀ u = (d₀*_{x₀} (u - u₀), realSobolevEquation f m hk u)`,

vanishes at the coordinates of a field `x` exactly when `x` is a vortex in the Coulomb slice
`d₀*_{x₀} (x - x₀) = 0` (`coulombSliceMap_realSubRef_eq_zero_iff`). It is strictly
differentiable, with derivative `L_{x₀}` at `u₀` (`hasStrictFDerivAt_coulombSliceMap_self`).
Since `L_{x₀}` is onto with a kernel of dimension `2m`, the implicit function theorem, in the form
of `TauCeti.levelSetChartModel`, gives a chart of the level set `{coulombSliceMap u₀ = 0}` at
`u₀` with values in `Fin (2m) → ℝ` (`coulombSliceChart`), sending `u₀` to `0`
(`coulombSliceChart_apply_self`). So a neighbourhood of `x₀` among the vortices in the Coulomb
slice through `x₀` is homeomorphic to an open subset of `ℝ^(2m)`, of the dimension of the divisor
space `Sym^m ℂ`.

The chart describes the Coulomb slice, not yet the quotient by the gauge group `G_(k+2)`: that
the slice meets each nearby gauge orbit exactly once is a separate statement.

## Main definitions

* `TauCeti.Vortex.realSobolevGaugeFixedOperator`: the gauge-fixed operator `L_x` on real
  coordinates, `(H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`.
* `TauCeti.Vortex.kerRealSobolevGaugeFixedOperatorEquiv`: its kernel at a field in every `A_m^j`
  is `gaugeFixedKernel x₀`.
* `TauCeti.Vortex.coulombSliceMap`: the Coulomb slice map through `u₀`.
* `TauCeti.Vortex.coulombSliceChart`: the chart of its zero set at a vortex, modelled on
  `Fin (2m) → ℝ`.

## Main results

* `TauCeti.Vortex.realSobolevGaugeFixedOperator_eq_iff`: the operator computes the pointwise one.
* `TauCeti.Vortex.finrank_ker_realSobolevGaugeFixedOperator_eq_two_mul`,
  `TauCeti.Vortex.realSobolevGaugeFixedOperator_surjective`,
  `TauCeti.Vortex.isFredholm_realSobolevGaugeFixedOperator`,
  `TauCeti.Vortex.index_realSobolevGaugeFixedOperator_eq_two_mul`: at a vortex it is onto and
  Fredholm, with a kernel of dimension `2m` and index `2m`.
* `TauCeti.Vortex.coulombSliceMap_realSubRef_eq_zero_iff`: the zeros of the slice map are the
  vortices in the Coulomb slice.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Appendix A.3 (regular zero sets of Fredholm maps).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace MeasureTheory Module TemperedDistribution
open scoped BesselPotentialSpace ContDiff RealInnerProductSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-! ### The gauge-fixed operator on real coordinates -/

variable (f m) in
/-- **The gauge-fixed vortex operator on the Sobolev scale.** For an integer `k ≥ 2` and real
coordinates `u` of a field `x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` as a bounded
real-linear operator `(H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`: the gauge-fixing row
`realSobolevGaugeAdjoint` followed by the three rows of the linearized equation
`realSobolevLinearizedEquation`. It computes the pointwise operator `gaugeFixedOperator x`
(`realSobolevGaugeFixedOperator_eq_iff`). -/
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

/-! ### The operator computes the pointwise one -/

/-- For `k ≥ 2`, the field of real `H^(k+1)` coordinates is `C¹`. -/
private theorem contDiff_one_continuousRepField (hk : 2 ≤ k)
    (u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    ContDiff ℝ 1 (continuousRepField u) :=
  contDiff_continuousRepField (by norm_cast; omega) u

section Pointwise

variable (hk : 2 ≤ k) (u v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le)

include hk in
/-- The rows of the pointwise gauge-fixed operator at the field with real coordinates `u`,
applied to the field of `v`, are continuous. -/
private theorem continuous_gaugeFixedOperator_continuousRepField_apply (j : Fin 4) :
    Continuous fun z ↦
      gaugeFixedOperator (referenceField f m + continuousRepField u) (continuousRepField v) z
        j :=
  (PiLp.continuous_apply 2 _ j).comp (continuous_gaugeFixedOperator
    ((contDiff_referenceField f m).continuous.add (contDiff_one_continuousRepField hk u).continuous)
    (contDiff_one_continuousRepField hk v))

/-- **The real gauge-fixing row is the pointwise one.** The continuous representative of
`realSobolevGaugeAdjoint f m hk u v` is `d₀* y` at `x`, where `x = x_m + continuousRepField u` is
the field with real coordinates `u` and `y = continuousRepField v` the field of `v`. -/
theorem continuousRep_realSobolevGaugeAdjoint :
    continuousRep (realSobolevGaugeAdjoint f m hk u v) =
      gaugeAdjoint (referenceField f m + continuousRepField u) (continuousRepField v) := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  refine continuousRep_eq_of_ae_eq (finrank_real_complex_lt_two_mul (Nat.one_lt_cast.2 hk)) ?_ ?_
  · exact continuous_gaugeAdjoint ((contDiff_referenceField f m).continuous.add
      (contDiff_one_continuousRepField hk u).continuous) (contDiff_one_continuousRepField hk v)
  · rw [coe_realSobolevGaugeAdjoint_apply]
    exact coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq _
      (coeFn_inclusionLp_ae_eq_continuousRepField hs u)
      (coeFn_inclusionLp_ae_eq_continuousRepField hs v) (contDiff_one_continuousRepField hk v)

/-- **The real linearized equation is the pointwise one.** The continuous representative of the
`i`-th row of `realSobolevLinearizedEquation f m hk u v` is the `i`-th row of `d₁ y` at `x`, where
`x = x_m + continuousRepField u` and `y = continuousRepField v`. -/
theorem continuousRep_realSobolevLinearizedEquation (i : Fin 3) :
    continuousRep (realSobolevLinearizedEquation f m hk u v i) = fun z ↦
      linearizedEquation (referenceField f m + continuousRepField u) (continuousRepField v) z
        i := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  refine continuousRep_eq_of_ae_eq (finrank_real_complex_lt_two_mul (Nat.one_lt_cast.2 hk)) ?_ ?_
  · exact (continuous_gaugeFixedOperator_continuousRepField_apply (f := f) (m := m) hk u v
      i.succ).congr fun z ↦ gaugeFixedOperator_apply_succ _ _ z i
  · rw [coe_realSobolevLinearizedEquation_apply]
    exact coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq _
      (coeFn_inclusionLp_ae_eq_continuousRepField hs u)
      (coeFn_inclusionLp_ae_eq_continuousRepField hs v) (contDiff_one_continuousRepField hk v) i

/-- **The gauge-fixed operator on real coordinates is the pointwise one.** Let
`x = x_m + continuousRepField u` be the field with real coordinates `u` and
`y = continuousRepField v` the field of `v`. Then `L_x v = w` exactly when the rows of the
pointwise operator `L_x y` are the continuous representatives of the components of `w`. -/
theorem realSobolevGaugeFixedOperator_eq_iff
    (w : realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) ×
      (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k))) :
    realSobolevGaugeFixedOperator f m hk u v = w ↔
      gaugeAdjoint (referenceField f m + continuousRepField u) (continuousRepField v) =
          continuousRep w.1 ∧
        ∀ i, (fun z ↦ linearizedEquation (referenceField f m + continuousRepField u)
          (continuousRepField v) z i) = continuousRep (w.2 i) := by
  have hfin := finrank_real_complex_lt_two_mul (Nat.one_lt_cast.2 hk)
  rw [realSobolevGaugeFixedOperator_apply, Prod.ext_iff, funext_iff,
    ← continuousRep_realSobolevGaugeAdjoint hk, (continuousRep_injective hfin).eq_iff]
  simp only [← continuousRep_realSobolevLinearizedEquation hk,
    (continuousRep_injective hfin).eq_iff]

/-- **The kernel of the gauge-fixed operator on real coordinates.** A variation `v` lies in the
kernel of `L_x` exactly when its field `y = continuousRepField v` solves `L_x y = 0` pointwise,
where `x = x_m + continuousRepField u`. -/
theorem mem_ker_realSobolevGaugeFixedOperator_iff :
    v ∈ (realSobolevGaugeFixedOperator f m hk u).ker ↔
      ∀ z, gaugeFixedOperator (referenceField f m + continuousRepField u)
        (continuousRepField v) z = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, realSobolevGaugeFixedOperator_eq_iff hk]
  simp only [gaugeFixedOperator_eq_iff, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero,
    PiLp.zero_apply, funext_iff, forall_and]
  rw [forall_comm]

end Pointwise

/-! ### The kernel at a field lying in every `A_m^j` -/

section Kernel

variable (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
  (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)

include hmem

/-- At `x₀`, a field `y` lies in `gaugeFixedKernel x₀` exactly when it is `C¹`, lies in
`sobolevFields (k + 1)` and solves `L_{x₀} y = 0` pointwise. -/
private theorem mem_gaugeFixedKernel_iff_mem_sobolevFields_add_one
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ gaugeFixedKernel x₀ ↔
      ContDiff ℝ 1 y ∧ y ∈ sobolevFields ((k : ℝ) + 1) ∧ ∀ z, gaugeFixedOperator x₀ y z = 0 :=
  mem_gaugeFixedKernel_iff_mem_sobolevFields (contDiff_of_forall_mem_framedFieldSpace x₀.continuous
    hmem) (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace x₀.continuous i n
      (hmem (n + 2))) _

/-- Taking fields sends the kernel of `L_{x₀}` on real coordinates into `gaugeFixedKernel x₀`. -/
private theorem continuousRepField_mem_gaugeFixedKernel
    {v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le}
    (hv : v ∈ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker) :
    continuousRepField v ∈ gaugeFixedKernel x₀ := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  refine (mem_gaugeFixedKernel_iff_mem_sobolevFields_add_one x₀ hmem).2
    ⟨contDiff_one_continuousRepField hk v, continuousRepField_mem_sobolevFields hs v, ?_⟩
  have hv' := (mem_ker_realSobolevGaugeFixedOperator_iff hk _ v).1 hv
  rwa [SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs] at hv'

/-- Every element of `gaugeFixedKernel x₀` is the field of real coordinates in the kernel of
`L_{x₀}` on real coordinates: the field `x_m + y` of `A_m^(k+1)` has real coordinates whose field
is `y`. -/
private theorem exists_mem_ker_continuousRepField_eq (y : gaugeFixedKernel x₀) :
    ∃ v ∈ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker,
      continuousRepField v = y := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  obtain ⟨hy₁, hyS, hyker⟩ := (mem_gaugeFixedKernel_iff_mem_sobolevFields_add_one x₀ hmem).1
    y.property
  let X : SobolevFieldSpace f m ((k : ℝ) + 1) :=
    ⟨referenceField f m + y, mem_framedFieldSpace.2 (by simpa using hyS),
      (contDiff_referenceField f m).continuous.add hy₁.continuous⟩
  have hXy : continuousRepField (X.realSubRef (by positivity)) = y :=
    add_left_cancel (SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs
      (h := by positivity) X)
  refine ⟨X.realSubRef (by positivity), (mem_ker_realSobolevGaugeFixedOperator_iff hk _ _).2
    fun z ↦ ?_, hXy⟩
  rw [hXy, SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs]
  exact hyker z

/-- **The kernel of `L_{x₀}` on real coordinates is the classical kernel.** At a continuous field
`x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, taking fields
`v ↦ continuousRepField v` is a linear equivalence from the kernel of
`realSobolevGaugeFixedOperator f m hk u₀`, with `u₀` the real coordinates of `x₀`, onto the
`C²` square-integrable solutions of `L_{x₀} y = 0` (`gaugeFixedKernel x₀`). -/
def kerRealSobolevGaugeFixedOperatorEquiv :
    (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker ≃ₗ[ℝ] gaugeFixedKernel x₀ :=
  LinearEquiv.ofBijective
    { toFun := fun v : (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker ↦
        ⟨continuousRepField (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le),
          continuousRepField_mem_gaugeFixedKernel hk x₀ hmem v.property⟩
      map_add' := fun v w ↦ Subtype.ext (by simp [continuousRepField_add])
      map_smul' := fun c v ↦ Subtype.ext (by simp [continuousRepField_smul]) }
    ⟨fun _ _ hvw ↦ Subtype.ext (continuousRepField_injective (by norm_cast; omega)
      (congrArg Subtype.val hvw)),
    fun y ↦
      have ⟨v, hv, hvy⟩ := exists_mem_ker_continuousRepField_eq hk x₀ hmem y
      ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

@[simp]
theorem coe_kerRealSobolevGaugeFixedOperatorEquiv_apply
    (v : (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker) :
    (kerRealSobolevGaugeFixedOperatorEquiv hk x₀ hmem v : ℂ → EuclideanSpace ℝ (Fin 4)) =
      continuousRepField (v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :=
  (rfl)

/-- At a field lying in every `A_m^j` whose section satisfies `∂bar_a α = 0`, the kernel of the
gauge-fixed operator on real coordinates is finite-dimensional. -/
theorem finiteDimensional_ker_realSobolevGaugeFixedOperator
    (hhol : ∀ w, equation x₀ w 1 = 0 ∧ equation x₀ w 2 = 0) :
    FiniteDimensional ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker :=
  have := finiteDimensional_weakGaugeFixedKernel x₀.continuous hmem hhol
  have := (framedGaugeFixedKernelEquivWeak x₀.continuous hmem).symm.finiteDimensional
  (kerRealSobolevGaugeFixedOperatorEquiv hk x₀ hmem).symm.finiteDimensional

/-- **The kernel of `L_{x₀}` on the Sobolev scale has dimension `2m`** (Taubes). At a continuous
field `x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j` and whose section satisfies
`∂bar_a α = 0`, for instance a vortex, the kernel of the gauge-fixed operator
`(H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` has real dimension `2m`, whatever `k`. -/
theorem finrank_ker_realSobolevGaugeFixedOperator_eq_two_mul
    (hhol : ∀ w, equation x₀ w 1 = 0 ∧ equation x₀ w 2 = 0) :
    finrank ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker = 2 * m := by
  rw [(kerRealSobolevGaugeFixedOperatorEquiv hk x₀ hmem).finrank_eq]
  exact finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (s := (2 : ℝ)) one_lt_two
    (by exact_mod_cast hmem 2) (contDiff_of_forall_mem_framedFieldSpace x₀.continuous hmem) hhol

end Kernel

/-! ### Surjectivity and the Fredholm property at a vortex -/

section Vortex

variable (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
  (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : equation x₀ = 0)

include hk hmem hsol in
/-- At a vortex `x₀` lying in every `A_m^j`, every continuous field `G ∈ H^k` is `L_{x₀} y` for
the field `y = continuousRepField v` of some real coordinates `v ∈ (H^(k+1)_ℝ)⁴`: the weak right
inverse of `L_{x₀}` gains one derivative, and the continuous representative of the weak solution
it produces is a classical solution. -/
private theorem exists_forall_gaugeFixedOperator_continuousRepField_eq
    {G : ℂ → EuclideanSpace ℝ (Fin 4)} (hG : G ∈ sobolevFields k) (hGc : Continuous G) :
    ∃ v : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le,
      ∀ z, gaugeFixedOperator x₀ (continuousRepField v) z = G z := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  have hx₀ := x₀.continuous
  have hGL : MemLp G 2 volume := memLp_of_mem_sobolevFields hG
  -- The weak right inverse of `L_{x₀}` sends `G ∈ H^k` to a weak solution in `H^(k+1)`.
  obtain ⟨Q, hQ, -, hQk⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields_add_one
      hx₀ hmem (fun z ↦ congrFun hsol z)
  have hQG : (Q (hGL.toLp G) : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields ((k : ℝ) + 1) := by
    exact_mod_cast hQk k _ (mem_sobolevFields_of_ae_eq hG hGL.coeFn_toLp.symm)
  -- Its continuous representative is the field of real coordinates `v`.
  obtain ⟨X, hX⟩ := SobolevFieldSpace.exists_ae_eq hs (f := f) (m := m)
    (mem_framedFieldSpace.2 (by simpa using hQG) :
      referenceField f m + (Q (hGL.toLp G) : ℂ → EuclideanSpace ℝ (Fin 4)) ∈
        framedFieldSpace f m ((k : ℝ) + 1))
  set v := X.realSubRef (by positivity)
  have hXv := SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs
    (h := by positivity) X
  have hyQ : (Q (hGL.toLp G) : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] continuousRepField v := by
    filter_upwards [hX] with z hz
    rw [← hXv] at hz
    simpa using hz
  -- The weak solution is a classical solution of `L_{x₀} y = G`.
  refine ⟨v, (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx₀
    (contDiff_one_continuousRepField hk v) hGc).1 fun η hη hηc ↦ ?_⟩
  calc ∫ z, ⟪continuousRepField v z, gaugeFixedAdjoint x₀ η z⟫
      = ∫ z, ⟪Q (hGL.toLp G) z, gaugeFixedAdjoint x₀ η z⟫ :=
        integral_congr_ae (hyQ.mono fun z hz ↦ by simp only [hz])
    _ = ∫ z, ⟪hGL.toLp G z, η z⟫ := hQ _ η (hη.of_le (by norm_cast)) hηc
    _ = ∫ z, ⟪G z, η z⟫ := integral_congr_ae (hGL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])

include hmem hsol in
/-- **The gauge-fixed operator on the Sobolev scale is onto at a vortex.** At a continuous vortex
`x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, the gauge-fixed operator
`L_{x₀} : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` is surjective. -/
theorem realSobolevGaugeFixedOperator_surjective :
    Function.Surjective (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)) := by
  intro w
  have hk1 : 1 < (k : ℝ) := by exact_mod_cast (hk : 1 < k)
  -- The target `w`, read as the field of its real coordinates `r`.
  let r : Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) := Fin.cons w.1 w.2
  obtain ⟨v, hLy⟩ := exists_forall_gaugeFixedOperator_continuousRepField_eq hk x₀ hmem hsol
    (continuousRepField_mem_sobolevFields hk1 r)
    (contDiff_continuousRepField (n := 0) (by simpa using hk1) r).continuous
  simp only [gaugeFixedOperator_eq_iff, continuousRepField_apply, r, Fin.cons_zero,
    Fin.cons_succ] at hLy
  refine ⟨v, (realSobolevGaugeFixedOperator_eq_iff hk _ v w).2 ?_⟩
  rw [SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef (by linarith)]
  exact ⟨funext fun z ↦ (hLy z).1, fun i ↦ funext fun z ↦ (hLy z).2 i⟩

include hsol in
/-- At a vortex, the section satisfies the holomorphicity rows `∂bar_a α = 0`. -/
private theorem equation_apply_one_and_apply_two_eq_zero (w : ℂ) :
    equation x₀ w 1 = 0 ∧ equation x₀ w 2 = 0 := by
  simp [hsol]

include hmem hsol in
/-- **The gauge-fixed operator on the Sobolev scale is Fredholm at a vortex.** At a continuous
vortex `x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, the gauge-fixed operator
`L_{x₀} : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` is a Fredholm operator. -/
theorem isFredholm_realSobolevGaugeFixedOperator :
    (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).IsFredholm := by
  have := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x₀ hmem
    (equation_apply_one_and_apply_two_eq_zero x₀ hsol)
  exact .of_surjective (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol)

include hmem hsol in
/-- **Taubes's index theorem on the Sobolev scale.** At a continuous vortex `x₀` of `A_m^(k+1)`,
`k ≥ 2`, lying in `A_m^j` for every `j`, the gauge-fixed operator
`L_{x₀} : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`, which is onto, has real index `2m`, the dimension of
the divisor space `Sym^m ℂ`. -/
theorem index_realSobolevGaugeFixedOperator_eq_two_mul :
    (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).index = 2 * m := by
  exact_mod_cast (ContinuousLinearMap.finrank_ker_eq_iff_index_eq _
    (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol)).1
      (finrank_ker_realSobolevGaugeFixedOperator_eq_two_mul hk x₀ hmem
        (equation_apply_one_and_apply_two_eq_zero x₀ hsol))

end Vortex

/-! ### The Coulomb slice map and its chart -/

variable (f m) in
/-- **The Coulomb slice map** through real coordinates `u₀`. For an integer `k ≥ 2`, the map
`(H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` sending real coordinates `u` to the Coulomb gauge-fixing defect
`d₀*_{x₀} (u - u₀)` at the field `x₀` with coordinates `u₀`, and to the vortex defect
`realSobolevEquation f m hk u`. On the coordinates of a field `x`, it vanishes exactly when `x` is
a vortex in the Coulomb slice `d₀*_{x₀} (x - x₀) = 0` through `x₀`
(`coulombSliceMap_realSubRef_eq_zero_iff`). -/
def coulombSliceMap (hk : 2 ≤ k) (u₀ u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k) ×
      (Fin 3 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) :=
  (realSobolevGaugeAdjoint f m hk u₀ (u - u₀), realSobolevEquation f m hk u)

@[simp]
theorem coulombSliceMap_apply (hk : 2 ≤ k)
    (u₀ u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    coulombSliceMap f m hk u₀ u =
      (realSobolevGaugeAdjoint f m hk u₀ (u - u₀), realSobolevEquation f m hk u) :=
  (rfl)

/-- **The derivative of the Coulomb slice map.** The slice map through `u₀` is strictly
differentiable at every `u`, with derivative `d₀*_{x₀} ⊕ d₁` at `u`, where `d₁` is the
linearized equation at the field with coordinates `u`. -/
theorem hasStrictFDerivAt_coulombSliceMap (hk : 2 ≤ k)
    (u₀ u : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    HasStrictFDerivAt (coulombSliceMap f m hk u₀)
      ((realSobolevGaugeAdjoint f m hk u₀).prod (realSobolevLinearizedEquation f m hk u)) u := by
  have hE : HasStrictFDerivAt (realSobolevEquation f m hk)
      (realSobolevLinearizedEquation f m hk u) u :=
    (contDiff_realSobolevEquation hk).contDiffAt.hasStrictFDerivAt
      (hasFDerivAt_realSobolevEquation hk u) (by simp)
  have hG : HasStrictFDerivAt (fun x ↦ realSobolevGaugeAdjoint f m hk u₀ (x - u₀))
      (realSobolevGaugeAdjoint f m hk u₀) u := by
    simpa using (realSobolevGaugeAdjoint f m hk u₀).hasStrictFDerivAt.comp u
      ((hasStrictFDerivAt_id u).sub_const u₀)
  exact hG.prodMk hE

/-- At its base point the derivative of the Coulomb slice map is the gauge-fixed operator
`L_{x₀} = d₀* ⊕ d₁` at `x₀`. -/
theorem hasStrictFDerivAt_coulombSliceMap_self (hk : 2 ≤ k)
    (u₀ : Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) :
    HasStrictFDerivAt (coulombSliceMap f m hk u₀) (realSobolevGaugeFixedOperator f m hk u₀) u₀ :=
  hasStrictFDerivAt_coulombSliceMap hk u₀ u₀

/-- **The zeros of the Coulomb slice map are the vortices in the Coulomb slice.** For continuous
fields `x₀` and `x` of `A_m^(k+1)`, `k ≥ 2`, the slice map through the real coordinates of `x₀`
vanishes at the real coordinates of `x` exactly when `d₀*_{x₀} (x - x₀) = 0` and `x` is a vortex. -/
theorem coulombSliceMap_realSubRef_eq_zero_iff (hk : 2 ≤ k)
    (x₀ x : SobolevFieldSpace f m ((k : ℝ) + 1)) :
    coulombSliceMap f m hk (x₀.realSubRef _) (x.realSubRef _) = 0 ↔
      gaugeAdjoint x₀ (x - x₀) = 0 ∧ equation x = 0 := by
  have hs : 1 < (k : ℝ) + 1 := by norm_cast; omega
  have hx : continuousRepField (x.realSubRef (by positivity)) -
      continuousRepField (x₀.realSubRef (by positivity)) = ⇑x - ⇑x₀ := by
    rw [← SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs
        (h := by positivity) x,
      ← SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs
        (h := by positivity) x₀]
    abel
  -- The gauge row vanishes exactly when its continuous representative does.
  have hgauge : realSobolevGaugeAdjoint f m hk (x₀.realSubRef _)
      (x.realSubRef _ - x₀.realSubRef _) = 0 ↔ gaugeAdjoint x₀ (x - x₀) = 0 := by
    rw [← (continuousRep_injective (finrank_real_complex_lt_two_mul (Nat.one_lt_cast.2 hk))).eq_iff,
      continuousRep_realSobolevGaugeAdjoint hk]
    simp only [continuousRepField_sub, hx, map_zero,
      SobolevFieldSpace.referenceField_add_continuousRepField_realSubRef hs]
  rw [coulombSliceMap_apply, Prod.mk_eq_zero, hgauge, realSobolevEquation_realSubRef_eq_zero_iff]

/-- At a vortex `x₀` the Coulomb slice map through its real coordinates vanishes at them. -/
theorem coulombSliceMap_self_eq_zero (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
    (hsol : equation x₀ = 0) : coulombSliceMap f m hk (x₀.realSubRef _) (x₀.realSubRef _) = 0 :=
  (coulombSliceMap_realSubRef_eq_zero_iff hk x₀ x₀).2
    ⟨funext fun z ↦ by simp [gaugeAdjoint_def], hsol⟩

section Chart

variable (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
  (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : equation x₀ = 0)

/-- **The Coulomb slice chart at a plane vortex.** Let `x₀` be a continuous vortex of
`A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, with real coordinates `u₀`. The zero set of
the Coulomb slice map through `u₀`, the real coordinates of the vortices in the Coulomb slice
through `x₀` (`coulombSliceMap_realSubRef_eq_zero_iff`), is homeomorphic near `u₀` to an open
subset of `ℝ^(2m)`: this is a chart of it at `u₀` with values in `Fin (2 * m) → ℝ`, sending `u₀`
to `0` (`coulombSliceChart_apply_self`). It reads a zero `u` near `u₀` through the projection of
`u - u₀` onto the kernel of `L_{x₀}`, by the implicit function theorem
(`TauCeti.levelSetChartModel`), which applies because `L_{x₀}` is onto with a kernel of dimension
`2m`. -/
def coulombSliceChart :
    OpenPartialHomeomorph {u | coulombSliceMap f m hk (x₀.realSubRef _) u = 0}
      (Fin (2 * m) → ℝ) :=
  have := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x₀ hmem
    (equation_apply_one_and_apply_two_eq_zero x₀ hsol)
  levelSetChartModel (hasStrictFDerivAt_coulombSliceMap_self hk _)
    (LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol))
    (.of_finiteDimensional _) this
    (finrank_ker_realSobolevGaugeFixedOperator_eq_two_mul hk x₀ hmem
      (equation_apply_one_and_apply_two_eq_zero x₀ hsol))
    (coulombSliceMap_self_eq_zero hk x₀ hsol)

/-- **The Coulomb slice chart is the model chart of the zero set of the slice map** at `u₀`,
`TauCeti.levelSetChartModel`, for any proofs of its hypotheses: the `TauCeti.levelSetChartModel_*`
lemmas give its values, its inverse, its source and its target. -/
theorem coulombSliceChart_eq
    (hker : (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker.ClosedComplemented)
    (hfin : FiniteDimensional ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker)
    (hn : finrank ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker = 2 * m) :
    coulombSliceChart hk x₀ hmem hsol =
      levelSetChartModel (hasStrictFDerivAt_coulombSliceMap_self hk _)
        (LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol))
        hker hfin hn (coulombSliceMap_self_eq_zero hk x₀ hsol) :=
  (rfl)

/-- The base point lies in the source of the Coulomb slice chart. -/
theorem mem_coulombSliceChart_source :
    ⟨x₀.realSubRef _, coulombSliceMap_self_eq_zero hk x₀ hsol⟩ ∈
      (coulombSliceChart hk x₀ hmem hsol).source :=
  mem_levelSetChartModel_source _ _ _ _ _ _

/-- The Coulomb slice chart sends the vortex `x₀` to the origin. -/
@[simp]
theorem coulombSliceChart_apply_self :
    coulombSliceChart hk x₀ hmem hsol ⟨x₀.realSubRef _, coulombSliceMap_self_eq_zero hk x₀ hsol⟩ =
      0 :=
  levelSetChartModel_apply_self _ _ _ _ _ _

/-- The origin, the value of the Coulomb slice chart at the vortex `x₀`, lies in its target. -/
theorem mem_coulombSliceChart_target : 0 ∈ (coulombSliceChart hk x₀ hmem hsol).target :=
  mem_levelSetChartModel_target _ _ _ _ _ _

end Chart

end TauCeti.Vortex
