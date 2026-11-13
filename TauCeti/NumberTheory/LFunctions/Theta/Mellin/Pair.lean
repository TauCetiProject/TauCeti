/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Kernel
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Volume
public import TauCeti.NumberTheory.LSeries.FEPairWithLevel

/-!
# The Mellin pair of the theta kernel of a lattice

Hecke's proof of the functional equation of a partial zeta function applies the Mellin principle
to the kernel `f_D(L, u) = (2^r₂ / w) ∫_D θ_L(x (u / V_L²)^(1/n)) d*x` of a lattice `L` of the
mixed space over a unit fundamental domain `D` (`TauCeti.LFunctions.mellinKernel`). This file
identifies the limit of the kernel at `∞` (Neukirch VII (5.8)) and packages the kernel as a
functional-equation pair.

* `TauCeti.LFunctions.mellinConstant`: the constant term `a₀ = 2^(r-1) R / w` of the kernel over
  a unit fundamental domain, the same for every such domain by the volume computation
  `surfaceHaar_of_isUnitFundamentalDomain` (Neukirch (5.6)).
* `TauCeti.LFunctions.mellinKernelFEPair`: the kernels of `L` over `D` and of the Euclidean dual
  `L^∨` over `D⁻¹` as a `TauCeti.FEPairWithLevel` of level `1`, weight `1/2`, root number `1`
  and both constant terms `a₀`. Every hypothesis of the Mellin principle is discharged from the
  kernel: local integrability from `continuousOn_mellinKernel`, the law from `mellinKernel_inv`
  and the rapid decay from `isBigO_mellinKernel_sub_rpow`. Read backwards it is the pair of
  `L^∨` over `D⁻¹` (`mellinKernelFEPair_symm`).
* The completed function `Λ` of the pair is the Mellin transform of `f_D(L, ·) - a₀` on
  `Re s > 1/2` (`hasMellin_mellinKernel_sub_mellinConstant`), is analytic off `0` and `1/2`
  (`TauCeti.FEPairWithLevel.analyticAt_Λ_iff`, since `a₀ ≠ 0`), where it has simple poles with
  residues `-a₀` and `a₀` (`TauCeti.FEPairWithLevel.meromorphicOrderAt_Λ_zero`,
  `meromorphicOrderAt_Λ_k`, `Λ_residue_zero` and `Λ_residue_k`, simplified by the projection
  lemmas `mellinKernelFEPair_k` and `mellinKernelFEPair_f₀`), and satisfies
  `Λ(D, L, s) = Λ(D⁻¹, L^∨, 1/2 - s)` (`mellinKernelFEPair_Λ_eq`, and as germs at every point
  `mellinKernelFEPair_Λ_eventuallyEq`).

At the lattice `σ(𝔞)` of a fractional ideal, Neukirch's (5.5) reads `Λ` at `s/2` as the completed
partial zeta function of the class of `𝔞⁻¹`; this file does not make that identification.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5)–(5.9).
-/

public section

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units TauCeti.NumberField.mixedEmbedding Set
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The constant term -/

variable (K) in
/-- **The constant term of the Mellin kernel**, Neukirch's `a₀ = 2^(r-1) R / w` of VII (5.8),
with `r` the number of infinite places, `R` the regulator and `w` the number of roots of unity.
It is `(2^r₂ / w) vol(D)` for every unit fundamental domain `D`
(`mellinConstant_eq_mul_surfaceHaar_real`). -/
def mellinConstant : ℝ :=
  2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K

variable (K) in
theorem mellinConstant_def : mellinConstant K =
    2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K / torsionOrder K := (rfl)

variable (K) in
theorem mellinConstant_pos : 0 < mellinConstant K := by
  have := regulator_pos K
  have : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (torsionOrder_pos K)
  rw [mellinConstant_def]
  positivity

variable (K) in
@[simp]
theorem mellinConstant_ne_zero : mellinConstant K ≠ 0 := (mellinConstant_pos K).ne'

/-- Over a unit fundamental domain `D` the constant term `(2^r₂ / w) vol(D)` of the Mellin kernel
is `a₀ = 2^(r-1) R / w`, independently of `D`. -/
theorem mellinConstant_eq_mul_surfaceHaar_real {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    mellinConstant K =
      2 ^ nrComplexPlaces K / torsionOrder K * (surfaceHaar K).real (Subtype.val ⁻¹' D) := by
  have := regulator_pos K
  rw [measureReal_def, surfaceHaar_of_isUnitFundamentalDomain hD,
    ENNReal.toReal_ofReal (by positivity), mellinConstant_def]
  field_simp

open scoped Classical in
/-- Over a unit fundamental domain `D` the kernel of a full lattice minus its constant term `a₀`
decays faster than every power. -/
theorem isBigO_mellinKernel_sub_mellinConstant {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (r : ℝ) :
    (fun u ↦ mellinKernel D L u - mellinConstant K) =O[atTop] (· ^ r) := by
  have h : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  simpa only [h] using isBigO_mellinKernel_sub_rpow hD.measurableSet hD.isBounded L r

/-! ### The functional-equation pair -/

open scoped Classical in
/-- **Hecke's Mellin pair of a lattice**, Neukirch VII (5.8): over a unit fundamental domain `D`,
the kernel `f_D(L, ·)` of a full lattice `L` and the kernel `f_{D⁻¹}(L^∨, ·)` of its Euclidean
dual over the inverse domain, as a functional-equation pair of level `1`, weight `1/2`, root
number `1` and constant terms `a₀ = mellinConstant K`. Both kernels are extended by zero off
`(0, ∞)`, where the pair does not read them. -/
def mellinKernelFEPair {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    FEPairWithLevel ℂ where
  f := (Ioi 0).indicator (mellinKernel D L)
  g := (Ioi 0).indicator (mellinKernel D⁻¹ (mixedDual K L))
  k := 1 / 2
  ε := 1
  f₀ := mellinConstant K
  g₀ := mellinConstant K
  N := 1
  hN := one_pos
  hf_int := ((continuousOn_mellinKernel hD.measurableSet hD.isBounded L).congr
    fun _ ht ↦ indicator_of_mem ht _).locallyIntegrableOn measurableSet_Ioi
  hg_int := ((continuousOn_mellinKernel hD.inv.measurableSet hD.inv.isBounded
    (mixedDual K L)).congr fun _ ht ↦ indicator_of_mem ht _).locallyIntegrableOn measurableSet_Ioi
  hf_nonpos _ ht := indicator_of_notMem (notMem_Ioi.mpr ht) _
  hg_nonpos _ ht := indicator_of_notMem (notMem_Ioi.mpr ht) _
  hk := one_half_pos
  hε := one_ne_zero
  h_feq t ht := by
    rw [one_mul, indicator_of_mem (mem_Ioi.mpr (one_div_pos.mpr ht)), indicator_of_mem ht,
      one_div, mellinKernel_inv D L ht, ← Real.sqrt_eq_rpow, one_mul, smul_eq_mul]
  hf_top r := (isBigO_mellinKernel_sub_mellinConstant hD L r).congr'
    ((eventually_gt_atTop 0).mono fun _ ht ↦ by simp only [indicator_of_mem (mem_Ioi.mpr ht)])
    EventuallyEq.rfl
  hg_top r := (isBigO_mellinKernel_sub_mellinConstant hD.inv (mixedDual K L) r).congr'
    ((eventually_gt_atTop 0).mono fun _ ht ↦ by simp only [indicator_of_mem (mem_Ioi.mpr ht)])
    EventuallyEq.rfl

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_f {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).f = (Ioi 0).indicator (mellinKernel D L) :=
  (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_g {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).g = (Ioi 0).indicator (mellinKernel D⁻¹ (mixedDual K L)) := (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_k {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).k = 1 / 2 := (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_ε {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).ε = 1 := (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_f₀ {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).f₀ = mellinConstant K := (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_g₀ {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).g₀ = mellinConstant K := (rfl)

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_N {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).N = 1 := (rfl)

open scoped Classical in
/-- Read backwards, the pair of `L` over `D` is the pair of the Euclidean dual `L^∨` over `D⁻¹`. -/
theorem mellinKernelFEPair_symm {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).symm = mellinKernelFEPair hD.inv (mixedDual K L) := by
  refine FEPairWithLevel.ext (fun _ _ ↦ by simp) (fun _ _ ↦ ?_) (by simp) (by simp) (by simp)
    (by simp) (by simp)
  simp only [FEPairWithLevel.symm_g, mellinKernelFEPair_f, mellinKernelFEPair_g, inv_inv,
    mixedDual_mixedDual]

open scoped Classical in
/-- On `Re s > 1/2` the completed function of the pair is the Mellin transform of the kernel
minus its constant term, Neukirch VII (5.5). -/
theorem hasMellin_mellinKernel_sub_mellinConstant {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (hs : 1 / 2 < s.re) :
    HasMellin (fun u ↦ mellinKernel D L u - mellinConstant K) s
      ((mellinKernelFEPair hD L).Λ s) := by
  refine (hasMellin_congr fun t ht ↦ ?_).mp ((mellinKernelFEPair hD L).hasMellin hs)
  simp only [mellinKernelFEPair_f, mellinKernelFEPair_f₀, indicator_of_mem ht]

open scoped Classical in
/-- **The functional equation of the pair**, Neukirch VII (5.9) before the dual lattice is
identified: `Λ(D, L, s) = Λ(D⁻¹, L^∨, 1/2 - s)` off the poles `0` and `1/2`. -/
theorem mellinKernelFEPair_Λ_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) :
    (mellinKernelFEPair hD L).Λ s =
      (mellinKernelFEPair hD.inv (mixedDual K L)).Λ (1 / 2 - s) := by
  have hk : s ≠ ((mellinKernelFEPair hD L).k : ℂ) := by simpa using h1
  rw [(mellinKernelFEPair hD L).Λ_eq h0 hk, mellinKernelFEPair_symm]
  simp

open scoped Classical in
/-- The functional equation of the pair as an equality of punctured germs at every point, the
poles included. -/
theorem mellinKernelFEPair_Λ_eventuallyEq {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℂ) :
    (mellinKernelFEPair hD L).Λ =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD.inv (mixedDual K L)).Λ (1 / 2 - z) := by
  filter_upwards [(mellinKernelFEPair hD L).Λ_eventuallyEq s] with z hz
  rw [hz, mellinKernelFEPair_symm]
  simp

end TauCeti.LFunctions
