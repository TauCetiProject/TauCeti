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
import TauCeti.Analysis.MellinTransform.Basic

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

* The pole-cleared entire completion `(mellinKernelFEPair hD L).entireΛ` takes the nonzero
  removable value `a₀ / 2` at both `0` and `1/2`, agrees with `s (s - 1/2) Λ(D, L, s)` off
  `{0, 1/2}`, and satisfies `entireΛ(D, L, s) = entireΛ(D⁻¹, L^∨, 1/2 - s)` on all of `ℂ`
  (`mellinKernelFEPair_entireΛ_eq`).
* For the lattice `σ(I)` of a fractional ideal and its trace dual `J = I^∨`,
  `mellinKernelFEPair_mixedDual_idealLattice` identifies the Euclidean-dual Mellin pair over `D`
  with that of `σ(J)` over the translated unit fundamental domain `(traceShift K * ·) '' D`,
  yielding Neukirch VII (5.9) both off the poles (`mellinKernelFEPair_idealLattice_Λ_eq`) and
  globally for `entireΛ` (`mellinKernelFEPair_idealLattice_entireΛ_eq`).
* `TauCeti.LFunctions.mellinKernelEntireCompletion`: the critical-strip `s / 2`-normalized
  pole-cleared completion `4 * (mellinKernelFEPair hD L).entireΛ (s / 2)`, which agrees with
  `s (s - 1) Λ(D, L, s / 2)` off `{0, 1}`, takes the value `2 a₀` at `0` and `1`, obeys the
  trace-dual ideal-lattice identification `mellinKernelEntireCompletion_mixedDual_idealLattice`,
  and satisfies the global `s ↔ 1 - s` functional equations
  (`mellinKernelEntireCompletion_one_sub`, `mellinKernelEntireCompletion_idealLattice_one_sub`).
* `exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici`: uniform stretched-exponential tail
  bounds around `mellinConstant K` on every ray `[a, ∞)` with `a > 0`.

At the lattice `σ(𝔞)` of a fractional ideal, Neukirch's (5.5) reads `Λ` at `s/2` as the completed
partial zeta function of the class of `𝔞⁻¹`; this file does not make that identification.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5)–(5.9).
-/

public section

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units TauCeti.NumberField.mixedEmbedding Set
open scoped Pointwise Topology nonZeroDivisors

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

variable (K) in
/-- Twice the constant term of the Mellin kernel is `2^(r₁ + r₂) R / w`. -/
theorem two_mul_mellinConstant :
    2 * mellinConstant K =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K / torsionOrder K := by
  rw [mellinConstant_def, ← NumberField.Units.rank_add_one, Nat.add_sub_cancel, pow_succ']
  ring

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

open scoped Classical in
/-- Over a unit fundamental domain `D`, `mellinKernel D L - mellinConstant K` satisfies a
stretched-exponential bound with exponent `[K : ℚ]⁻¹` on every ray `[a, ∞)` with `a > 0`. -/
theorem exists_norm_mellinKernel_sub_mellinConstant_le_on_Ici {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C ≥ 0, ∀ u ∈ Ici a,
      ‖mellinKernel D L u - mellinConstant K‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  have hcst : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  simpa only [hcst] using
    exists_norm_mellinKernel_sub_le_on_Ici hD.measurableSet hD.isBounded L ha

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

open scoped Classical in
theorem mellinKernelFEPair_entireΛ_zero {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).entireΛ 0 = (mellinConstant K : ℂ) / 2 := by
  rw [FEPairWithLevel.entireΛ_zero, mellinKernelFEPair_k, mellinKernelFEPair_f₀, smul_eq_mul]
  push_cast
  ring

open scoped Classical in
@[simp]
theorem mellinKernelFEPair_entireΛ_inv_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    (mellinKernelFEPair hD L).entireΛ 2⁻¹ = (mellinConstant K : ℂ) / 2 := by
  have hk : ((1 / 2 : ℝ) : ℂ) = (2⁻¹ : ℂ) := by norm_num
  rw [← hk, ← mellinKernelFEPair_k hD L, FEPairWithLevel.entireΛ_k, mellinKernelFEPair_k,
    mellinKernelFEPair_ε, mellinKernelFEPair_N, mellinKernelFEPair_g₀]
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, smul_eq_mul]
  push_cast
  ring

open scoped Classical in
/-- Away from `0` and `1/2`, `entireΛ` of the lattice pair is `s * (s - 1/2) * Λ s`. -/
theorem mellinKernelFEPair_entireΛ_eq_mul_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) :
    (mellinKernelFEPair hD L).entireΛ s =
      s * (s - 1 / 2) * (mellinKernelFEPair hD L).Λ s := by
  have hk : s ≠ ((mellinKernelFEPair hD L).k : ℂ) := by simpa using h1
  simpa [smul_eq_mul] using (mellinKernelFEPair hD L).entireΛ_eq_smul_Λ (.inl h0) (.inl hk)

open scoped Classical in
/-- **Global functional equation of the pole-cleared lattice completion**:
`entireΛ(D, L, s) = entireΛ(D⁻¹, L^∨, 1/2 - s)` for every `s : ℂ`, including `0` and `1/2`. -/
theorem mellinKernelFEPair_entireΛ_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ) :
    (mellinKernelFEPair hD L).entireΛ s =
      (mellinKernelFEPair hD.inv (mixedDual K L)).entireΛ (1 / 2 - s) := by
  simpa [mellinKernelFEPair_symm] using (mellinKernelFEPair hD L).entireΛ_eq s

/-! ### Ideal lattices and trace duals -/

open scoped Classical in
/-- For the Euclidean dual of an ideal lattice `σ(I)`, the Mellin pair over `D` coincides with
that of the trace-dual lattice `σ(J)` over the translated domain `(traceShift K * ·) '' D`. -/
theorem mellinKernelFEPair_mixedDual_idealLattice
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) :
    mellinKernelFEPair hD (mixedDual K (idealLattice K I)) =
      mellinKernelFEPair (hD.mul traceShift_mem_normOneSurface) (idealLattice K J) := by
  refine FEPairWithLevel.ext (fun u hu ↦ ?_) (fun u hu ↦ ?_) rfl rfl rfl rfl rfl
  · simp [indicator_of_mem hu, mellinKernel_mixedDual_idealLattice hJ D u]
  · have h1 := (mellinKernelFEPair hD (mixedDual K (idealLattice K I))).h_feq u hu
    have h2 := (mellinKernelFEPair (hD.mul traceShift_mem_normOneSurface)
      (idealLattice K J)).h_feq u hu
    have hf : (mellinKernelFEPair hD (mixedDual K (idealLattice K I))).f (1 / (1 * u)) =
        (mellinKernelFEPair (hD.mul traceShift_mem_normOneSurface)
          (idealLattice K J)).f (1 / (1 * u)) := by
      have hu' : 1 / (1 * u) ∈ Ioi (0 : ℝ) := one_div_pos.mpr (by simpa using hu)
      simp only [mellinKernelFEPair_f, indicator_of_mem hu',
        mellinKernel_mixedDual_idealLattice hJ D]
    simp only [mellinKernelFEPair_N, mellinKernelFEPair_ε, mellinKernelFEPair_k, one_mul,
      smul_eq_mul] at h1 h2 hf
    have hpow : ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne'
    exact mul_left_cancel₀ hpow (h1.symm.trans (hf.trans h2))

open scoped Classical in
/-- **Functional equation for ideal lattices** (Neukirch VII (5.9)): for a fractional ideal `I`
and its trace dual `J = I^∨`, `Λ(D, σ(I), s) = Λ(traceShift · D⁻¹, σ(J), 1/2 - s)` off `0`
and `1/2`. -/
theorem mellinKernelFEPair_idealLattice_Λ_eq
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ s =
      (mellinKernelFEPair (hD.inv.mul traceShift_mem_normOneSurface) (idealLattice K J)).Λ
        (1 / 2 - s) := by
  rw [mellinKernelFEPair_Λ_eq hD (idealLattice K I) h0 h1,
    mellinKernelFEPair_mixedDual_idealLattice hJ hD.inv]

open scoped Classical in
/-- **Global pole-cleared functional equation for ideal lattices**: valid at every `s : ℂ`,
including the cleared poles `0` and `1/2`. -/
theorem mellinKernelFEPair_idealLattice_entireΛ_eq
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) (s : ℂ) :
    (mellinKernelFEPair hD (idealLattice K I)).entireΛ s =
      (mellinKernelFEPair (hD.inv.mul traceShift_mem_normOneSurface) (idealLattice K J)).entireΛ
        (1 / 2 - s) := by
  rw [mellinKernelFEPair_entireΛ_eq hD (idealLattice K I) s,
    mellinKernelFEPair_mixedDual_idealLattice hJ hD.inv]

/-! ### Critical-strip `s / 2` pole-cleared lattice completion -/

open scoped Classical in
/-- **Critical-strip pole-cleared completion** of a lattice Mellin pair:
`4 * (mellinKernelFEPair hD L).entireΛ (s / 2)`. Away from `0` and `1` it equals
`s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2)`, while at `0` and `1` it takes the nonzero
removable value `2 * mellinConstant K`. -/
def mellinKernelEntireCompletion {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℂ) : ℂ :=
  4 * (mellinKernelFEPair hD L).entireΛ (s / 2)

open scoped Classical in
theorem mellinKernelEntireCompletion_def {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ) :
    mellinKernelEntireCompletion hD L s = 4 * (mellinKernelFEPair hD L).entireΛ (s / 2) := (rfl)

open scoped Classical in
/-- `mellinKernelEntireCompletion` is entire on `ℂ`. -/
theorem differentiable_mellinKernelEntireCompletion {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    Differentiable ℂ (mellinKernelEntireCompletion hD L) :=
  ((mellinKernelFEPair hD L).differentiable_entireΛ.comp
    (differentiable_id.div_const 2)).const_mul 4

open scoped Classical in
@[simp]
theorem mellinKernelEntireCompletion_zero {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    mellinKernelEntireCompletion hD L 0 = 2 * (mellinConstant K : ℂ) := by
  rw [mellinKernelEntireCompletion_def, zero_div, mellinKernelFEPair_entireΛ_zero]
  ring

open scoped Classical in
@[simp]
theorem mellinKernelEntireCompletion_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    mellinKernelEntireCompletion hD L 1 = 2 * (mellinConstant K : ℂ) := by
  simp [mellinKernelEntireCompletion_def]
  ring

open scoped Classical in
/-- Away from `0` and `1`, `mellinKernelEntireCompletion` equals
`s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2)`. -/
theorem mellinKernelEntireCompletion_eq_mul_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    mellinKernelEntireCompletion hD L s =
      s * (s - 1) * (mellinKernelFEPair hD L).Λ (s / 2) := by
  have hs0 : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hs1 : s / 2 ≠ 1 / 2 := fun h ↦ h1 ((div_left_inj₀ two_ne_zero).mp h)
  rw [mellinKernelEntireCompletion_def, mellinKernelFEPair_entireΛ_eq_mul_Λ hD L hs0 hs1]
  ring

open scoped Classical in
/-- Global `s ↔ 1 - s` functional equation of `mellinKernelEntireCompletion`. -/
theorem mellinKernelEntireCompletion_one_sub {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ) :
    mellinKernelEntireCompletion hD L (1 - s) =
      mellinKernelEntireCompletion hD.inv (mixedDual K L) s := by
  have harg : (1 - s) / 2 = (1 / 2 : ℂ) - s / 2 := by ring
  rw [mellinKernelEntireCompletion_def, mellinKernelEntireCompletion_def, harg,
    mellinKernelFEPair_entireΛ_eq hD L, sub_sub_cancel]

open scoped Classical in
/-- For the Euclidean dual of an ideal lattice `σ(I)`, the critical-strip completion over `D`
coincides with that of the trace-dual lattice `σ(J)` over the translated domain
`(traceShift K * ·) '' D`. -/
theorem mellinKernelEntireCompletion_mixedDual_idealLattice
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) :
    mellinKernelEntireCompletion hD (mixedDual K (idealLattice K I)) =
      mellinKernelEntireCompletion (hD.mul traceShift_mem_normOneSurface)
        (idealLattice K J) := by
  funext s
  rw [mellinKernelEntireCompletion_def, mellinKernelEntireCompletion_def,
    mellinKernelFEPair_mixedDual_idealLattice hJ hD]

open scoped Classical in
/-- Global `s ↔ 1 - s` functional equation of `mellinKernelEntireCompletion` for an ideal lattice
`σ(I)` and its trace dual `σ(J)`. -/
theorem mellinKernelEntireCompletion_idealLattice_one_sub
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) (s : ℂ) :
    mellinKernelEntireCompletion hD (idealLattice K I) (1 - s) =
      mellinKernelEntireCompletion (hD.inv.mul traceShift_mem_normOneSurface)
        (idealLattice K J) s := by
  rw [mellinKernelEntireCompletion_one_sub,
    mellinKernelEntireCompletion_mixedDual_idealLattice hJ hD.inv]

end TauCeti.LFunctions
