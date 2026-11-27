/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.InnerProductSpace.Variational.FormKernel
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.ConnectedComponents
import TauCeti.Analysis.Sobolev.W1p.InfiniteDimensional
import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# The second Neumann eigenvalue

A real `κ` is a **Neumann eigenvalue** of `-Δ` on an open set `Ω` when some nonzero `u ∈ H¹(Ω)`
satisfies

`∫_Ω ∇u · ∇v = κ ∫_Ω u v` for every `v ∈ H¹(Ω)`,

the weak form of `-Δu = κu` in `Ω` with `∂_ν u = 0` on `∂Ω`: the test space is all of `H¹(Ω)`,
which imposes the natural boundary condition. On a nonempty preconnected `Ω` of finite measure, `0`
is a Neumann eigenvalue with eigenspace the constants, and every other Neumann eigenvalue is
positive.
This file identifies the least positive one, the second eigenvalue `λ₂` when the eigenvalues are
counted with multiplicity, as the minimum of the Rayleigh quotient over the functions of mean zero:

`λ₂ = min {‖∇u‖² / ‖u‖² | u ∈ H¹(Ω), u ≠ 0, ∫_Ω u = 0}`.

The hypothesis is the **Rellich property**, that the value map `H¹(Ω) → L²(Ω)` is compact, as on a
bounded Lipschitz domain. The value map, together with the Dirichlet integral `⟪∇u, ∇v⟫`, is then
a compact form pair (`TauCeti.CompactFormPair`) whose form kernel consists of the functions with
vanishing gradient, which on a preconnected `Ω` are the constants. A function is orthogonal in
`L²(Ω)` to the constants exactly when it has mean zero, and the abstract spectral gap above the
form kernel (`TauCeti.CompactFormPair.isLeast_setOf_formEigenspace_ne_bot_of_isMinOn`) gives the
result: the minimum of the Rayleigh quotient over the mean-zero functions is attained, and it is
the least positive eigenvalue.

* `TauCeti.PDE.exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero`: on a nonempty
  preconnected `Ω` of finite measure with the Rellich property, in a space of positive dimension,
  there is a least positive Neumann eigenvalue, and it is the least Rayleigh quotient of mean zero.
* `TauCeti.PDE.forall_inner_gradient_eq_iff_of_isLeast_neumannEigenvalue_pos`: the
  eigenfunctions of the least positive Neumann eigenvalue `κ` are exactly the functions `u` of mean
  zero with `‖∇u‖² = κ ‖u‖²`, that is, `0` and the minimizers of the Rayleigh quotient of mean
  zero.
* `TauCeti.PDE.exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero_of_isLipschitzDomainWith`:
  the same on a bounded connected Lipschitz domain, where Rellich–Kondrachov
  (`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`) supplies the Rellich property.
* `TauCeti.PDE.exists_isLeast_spectrum_mixedOperator_laplacian_empty_pos_rayleigh_meanZero`: the
  same for the spectrum of the mixed Laplacian `-Δ_∅` (`TauCeti.PDE.mixedOperator` with `Γ = ∅`)
  on `Ω ⊆ ℝⁿ`, when `H¹_∅(Ω) = H¹(Ω)`, so that `-Δ_∅` is the Neumann Laplacian: its least
  positive spectral value exists and is the least Rayleigh quotient of mean zero.

Connectedness cannot be dropped. On an open set of finite measure that is not preconnected, a
function constant on each of two disjoint open pieces can have mean zero and zero gradient, so the
Rayleigh quotient of mean zero has minimum `0`, which is not a positive eigenvalue
(`TauCeti.PDE.isLeast_rayleigh_meanZero_zero_of_not_isPreconnected`). On `(0, 1) ∪ (2, 3)` such a
function is the one equal to `1` on the first interval and `-1` on the second.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1
  (eigenvalues as minima of the Rayleigh quotient under orthogonality constraints to the earlier
  eigenfunctions, with natural boundary conditions when no boundary condition is imposed).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

/-- The compact form pair of the Neumann Laplacian: the value map `H¹(Ω) → L²(Ω)`, compact by
the Rellich property, with the Dirichlet integral `⟪∇u, ∇v⟫` as its form. -/
private noncomputable def neumannPair
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    CompactFormPair ℝ (W1p mu Omega 2) (Lp ℝ 2 (mu.restrict Omega)) where
  inclusion := W1p.valueL
  injective := W1p.valueL_injective
  denseRange := W1p0.denseRange_valueL_two.mono <| by
    rintro _ ⟨w, rfl⟩
    exact ⟨w, by simp⟩
  isCompactOperator := hK
  form := (innerSL ℝ).bilinearComp W1p.gradientL W1p.gradientL
  hermitian u v := by simp [real_inner_comm]
  exists_shifted_coercive := ⟨1, one_pos, 1, fun u ↦ by
    simp only [one_mul, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
      W1p.gradientL_apply, W1p.valueL_apply, RCLike.re_to_real, real_inner_self_eq_norm_sq]
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, add_comm]⟩

variable {hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))}

private theorem neumannPair_inclusion_apply (u : W1p mu Omega 2) :
    (neumannPair hK).inclusion u = W1p.value u :=
  W1p.valueL_apply u

private theorem energy_neumannPair (u : W1p mu Omega 2) :
    (neumannPair hK).energy u = ‖W1p.gradient u‖ ^ 2 := by
  simp [neumannPair, CompactFormPair.energy_def]

private theorem energy_neumannPair_nonneg (u : W1p mu Omega 2) :
    0 ≤ (neumannPair hK).energy u := by
  rw [energy_neumannPair]
  positivity

private theorem mem_formEigenspace_neumannPair {kappa : ℝ} {u : W1p mu Omega 2} :
    u ∈ (neumannPair hK).formEigenspace kappa ↔ ∀ v : W1p mu Omega 2,
      ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  simp [neumannPair]

/-- The positive variational eigenvalues of the Neumann pair are the positive Neumann
eigenvalues. -/
private theorem setOf_formEigenspace_neumannPair_ne_bot :
    {kappa | 0 < kappa ∧ (neumannPair hK).formEigenspace kappa ≠ ⊥} =
      {kappa | 0 < kappa ∧ ∃ u : W1p mu Omega 2, u ≠ 0 ∧ ∀ v : W1p mu Omega 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} := by
  ext kappa
  simp only [Set.mem_ofPred_eq, Submodule.ne_bot_iff, mem_formEigenspace_neumannPair]
  exact and_congr_right fun _ ↦ exists_congr fun _ ↦ and_comm

/-- A least positive Neumann eigenvalue `κ` is the minimum of the energy of the Neumann pair on the
constrained sphere of the mean-zero values: an eigenfunction of `κ` shows that the sphere is
nonempty, so the minimum exists, and it is the least positive eigenvalue. -/
private theorem exists_isMinOn_energy_neumannPair_eq {kappa : ℝ}
    (hkappa : IsLeast {kappa | 0 < kappa ∧ ∃ u : W1p mu Omega 2, u ≠ 0 ∧ ∀ v : W1p mu Omega 2,
      ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} kappa) :
    ∃ u₀ ∈ (neumannPair hK).unitConstraint (neumannPair hK).formKernelImageᗮ,
      IsMinOn (neumannPair hK).energy
        ((neumannPair hK).unitConstraint (neumannPair hK).formKernelImageᗮ) u₀ ∧
        (neumannPair hK).energy u₀ = kappa := by
  rw [← setOf_formEigenspace_neumannPair_ne_bot (hK := hK)] at hkappa
  obtain ⟨u, hu, h1⟩ :=
    CompactFormPair.exists_mem_formEigenspace_norm_inclusion_eq_one hkappa.1.2
  obtain ⟨u₀, hu₀, hmin⟩ := (neumannPair hK).exists_isMinOn_energy_unitConstraint _
    (Submodule.isClosed_orthogonal _) ⟨u, CompactFormPair.mem_unitConstraint.2
      ⟨CompactFormPair.inclusion_mem_orthogonal_of_mem_formEigenspace hkappa.1.1.ne' hu, h1⟩⟩
  exact ⟨u₀, hu₀, hmin,
    (CompactFormPair.isLeast_setOf_formEigenspace_ne_bot_of_isMinOn energy_neumannPair_nonneg hu₀
      hmin).unique hkappa⟩

section FiniteMeasure

variable [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- On a preconnected `Ω`, a value is orthogonal to the values of the form kernel of the Neumann
pair, the constants, exactly when it has mean zero. -/
private theorem value_mem_orthogonal_neumannPair_iff
    (hconn : IsPreconnected (Omega : Set E)) (u : W1p mu Omega 2) :
    W1p.value u ∈ (neumannPair hK).formKernelImageᗮ ↔ ∫ x in Omega, W1p.value u x ∂mu = 0 := by
  have hconst (c : ℝ) : (W1p.const c : W1p mu Omega 2) ∈ (neumannPair hK).formKernel :=
    CompactFormPair.mem_formKernel.2 fun v ↦ by simp [neumannPair]
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have h1 := h _ (CompactFormPair.inclusion_mem_formKernelImage (hconst 1))
    rwa [neumannPair_inclusion_apply, W1p.inner_value_const, one_mul] at h1
  · intro h x hx
    obtain ⟨n, hn, rfl⟩ := CompactFormPair.mem_formKernelImage.1 hx
    have hg : W1p.gradient n = 0 := by
      have h0 := CompactFormPair.energy_eq_zero_of_mem_formKernel hn
      rw [energy_neumannPair, sq_eq_zero_iff, norm_eq_zero] at h0
      exact h0
    obtain ⟨c, rfl⟩ := W1p.exists_eq_const_of_gradient_eq_zero hconn hg
    rw [neumannPair_inclusion_apply, W1p.inner_value_const, h, mul_zero]

/-- The Rayleigh quotients of the Neumann pair over the kernel-orthogonal part are the Rayleigh
quotients of mean zero. -/
private theorem setOf_rayleigh_neumannPair (hconn : IsPreconnected (Omega : Set E)) :
    {r | ∃ u, (neumannPair hK).inclusion u ∈ (neumannPair hK).formKernelImageᗮ ∧
        (neumannPair hK).inclusion u ≠ 0 ∧
        r = (neumannPair hK).energy u / ‖(neumannPair hK).inclusion u‖ ^ 2} =
      {r | ∃ u : W1p mu Omega 2, W1p.value u ≠ 0 ∧ ∫ x in Omega, W1p.value u x ∂mu = 0 ∧
        r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2} := by
  ext r
  simp only [Set.mem_ofPred_eq, neumannPair_inclusion_apply,
    value_mem_orthogonal_neumannPair_iff hconn, energy_neumannPair]
  exact exists_congr fun u ↦ by tauto

/-- **The eigenfunctions of the second Neumann eigenvalue are the Rayleigh minimizers of mean
zero.** Let `Ω` be preconnected and of finite measure, with compact value map `H¹(Ω) → L²(Ω)`, and
let `κ` be the least positive Neumann eigenvalue. Then `u ∈ H¹(Ω)` satisfies
`∫_Ω ∇u · ∇v = κ ∫_Ω u v` for every `v ∈ H¹(Ω)` exactly when `∫_Ω u = 0` and
`‖∇u‖² = κ ‖u‖²`: the nonzero eigenfunctions of `κ` are exactly the functions of mean zero that
attain the least Rayleigh quotient `κ`
(`TauCeti.PDE.exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero`). -/
theorem forall_inner_gradient_eq_iff_of_isLeast_neumannEigenvalue_pos
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set E)) {kappa : ℝ}
    (hkappa : IsLeast {kappa | 0 < kappa ∧ ∃ u : W1p mu Omega 2, u ≠ 0 ∧ ∀ v : W1p mu Omega 2,
      ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} kappa)
    (u : W1p mu Omega 2) :
    (∀ v : W1p mu Omega 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ) ↔
      ∫ x in Omega, W1p.value u x ∂mu = 0 ∧ ‖W1p.gradient u‖ ^ 2 = kappa * ‖W1p.value u‖ ^ 2 := by
  obtain ⟨u₀, hu₀, hmin, hE⟩ := exists_isMinOn_energy_neumannPair_eq (hK := hK) hkappa
  have h := CompactFormPair.mem_formEigenspace_iff_of_isMinOn (u := u) energy_neumannPair_nonneg
    hu₀ hmin
  rwa [hE, mem_formEigenspace_neumannPair, neumannPair_inclusion_apply,
    value_mem_orthogonal_neumannPair_iff hconn, energy_neumannPair] at h

/-- **The second Neumann eigenvalue is the least Rayleigh quotient of mean zero.** Let `Ω` be a
nonempty preconnected open set of finite measure in a space of positive dimension, with compact
value map `H¹(Ω) → L²(Ω)`. Then there is a least positive Neumann eigenvalue `κ`, the least `κ > 0`
for which some nonzero `u ∈ H¹(Ω)` satisfies `∫_Ω ∇u · ∇v = κ ∫_Ω u v` for every `v ∈ H¹(Ω)`, and
`κ` is the minimum of the Rayleigh quotient `‖∇u‖² / ‖u‖²` over the `u ∈ H¹(Ω)` with `u ≠ 0` and
`∫_Ω u = 0`. -/
theorem exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero [Nontrivial E]
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set E)) (hne : (Omega : Set E).Nonempty) :
    ∃ kappa : ℝ,
      IsLeast {kappa | 0 < kappa ∧ ∃ u : W1p mu Omega 2, u ≠ 0 ∧ ∀ v : W1p mu Omega 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} kappa ∧
      IsLeast {r | ∃ u : W1p mu Omega 2, W1p.value u ≠ 0 ∧
        ∫ x in Omega, W1p.value u x ∂mu = 0 ∧ r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2}
        kappa := by
  -- `H¹(Ω)` is infinite dimensional, so the constrained sphere of mean-zero values is nonempty.
  obtain ⟨u₀, hu₀, hmin⟩ := (neumannPair hK).exists_isMinOn_energy_unitConstraint _
    (Submodule.isClosed_orthogonal _)
    (CompactFormPair.unitConstraint_orthogonal_nonempty (W1p.not_finiteDimensional hne))
  refine ⟨(neumannPair hK).energy u₀, ?_, ?_⟩
  · rw [← setOf_formEigenspace_neumannPair_ne_bot (hK := hK)]
    exact CompactFormPair.isLeast_setOf_formEigenspace_ne_bot_of_isMinOn energy_neumannPair_nonneg
      hu₀ hmin
  · rw [← setOf_rayleigh_neumannPair hconn]
    exact CompactFormPair.isLeast_rayleigh_of_isMinOn hu₀ hmin

/-- **On a disconnected domain the least Rayleigh quotient of mean zero is `0`.** If the open set
`Ω` has finite measure and is not preconnected, the minimum of `‖∇u‖² / ‖u‖²` over the nonzero
`u ∈ H¹(Ω)` with `∫_Ω u = 0` is `0`, attained by a function constant on each of two disjoint open
pieces of `Ω`. So it is not a positive Neumann eigenvalue, and the connectedness hypothesis of
`TauCeti.PDE.exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero` cannot be dropped. -/
theorem isLeast_rayleigh_meanZero_zero_of_not_isPreconnected
    (hconn : ¬IsPreconnected (Omega : Set E)) :
    IsLeast {r | ∃ u : W1p mu Omega 2, W1p.value u ≠ 0 ∧
      ∫ x in Omega, W1p.value u x ∂mu = 0 ∧ r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2} 0 := by
  obtain ⟨u, hu, hgrad, hint⟩ :=
    W1p.exists_ne_zero_and_gradient_eq_zero_and_setIntegral_eq_zero (mu := mu) (p := 2) hconn
  refine ⟨⟨u, fun h => hu (W1p.ext_value (h.trans W1p.value_zero.symm)), hint, by simp [hgrad]⟩,
    ?_⟩
  rintro _ ⟨v, -, -, rfl⟩
  positivity

end FiniteMeasure

/-- **The second Neumann eigenvalue of a bounded connected Lipschitz domain** is the least Rayleigh
quotient of mean zero: on a bounded connected Lipschitz domain `Ω ⊆ ℝ × E` there is a least
positive Neumann eigenvalue, and it is the minimum of `‖∇u‖² / ‖u‖²` over the nonzero
`u ∈ H¹(Ω)` with `∫_Ω u = 0`. -/
theorem exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero_of_isLipschitzDomainWith
    {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsConnected (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ kappa : ℝ,
      IsLeast {kappa | 0 < kappa ∧ ∃ u : W1p volume Ω 2, u ≠ 0 ∧ ∀ v : W1p volume Ω 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} kappa ∧
      IsLeast {r | ∃ u : W1p volume Ω 2, W1p.value u ≠ 0 ∧
        ∫ x in Ω, W1p.value u x = 0 ∧ r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2} kappa := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  exact exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb) hconn.isPreconnected
    hconn.nonempty

end PDE

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- When `H¹_∅(Ω) = H¹(Ω)`, the positive part of the spectrum of the mixed Laplacian `-Δ_∅` is
the set of positive Neumann eigenvalues. -/
private theorem spectrum_mixedOperator_laplacian_empty_inter_Ioi
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (htop : w1pVanishingOnSubmodule mu Omega 2 ∅ = ⊤) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) ∅).spectrum ∩ Ioi 0 =
      {kappa | 0 < kappa ∧ ∃ u : W1p mu Omega 2, u ≠ 0 ∧ ∀ v : W1p mu Omega 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ} := by
  have hmem (u : W1p mu Omega 2) : u ∈ w1pVanishingOnSubmodule mu Omega 2 ∅ := by
    rw [htop]
    exact ClosedSubmodule.mem_top
  ext kappa
  rw [Set.mem_inter_iff, mem_spectrum_mixedOperator_laplacian_iff (Set.empty_disjoint _) hK,
    and_comm]
  refine and_congr_right fun _ ↦ ⟨fun ⟨u, hu, h⟩ ↦ ⟨u, fun h0 ↦ hu (Subtype.ext h0),
    fun v ↦ h ⟨v, hmem v⟩⟩, fun ⟨u, hu, h⟩ ↦ ⟨⟨u, hmem u⟩, fun h0 ↦ hu (congrArg Subtype.val h0),
    fun v ↦ h v⟩⟩

/-- **The second eigenvalue of the Neumann Laplacian `-Δ_∅` is the least Rayleigh quotient of
mean zero.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a nonempty preconnected open set of finite measure with
compact value map `H¹(Ω) → L²(Ω)`, on which `H¹_∅(Ω) = H¹(Ω)`, as on a bounded Lipschitz domain
(`TauCeti.w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith`), so that the mixed Laplacian
`-Δ_∅` is the Neumann Laplacian. Then the spectrum of `-Δ_∅` has a least positive element `κ`, and
`κ` is the minimum of the Rayleigh quotient `‖∇u‖² / ‖u‖²` over the `u ∈ H¹(Ω)` with `u ≠ 0` and
`∫_Ω u = 0`. -/
theorem exists_isLeast_spectrum_mixedOperator_laplacian_empty_pos_rayleigh_meanZero
    [Nonempty ι] [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (htop : w1pVanishingOnSubmodule mu Omega 2 ∅ = ⊤)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ kappa : ℝ,
      IsLeast ((mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) ∅).spectrum ∩ Ioi 0) kappa ∧
      IsLeast {r | ∃ u : W1p mu Omega 2, W1p.value u ≠ 0 ∧
        ∫ x in Omega, W1p.value u x ∂mu = 0 ∧ r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2}
        kappa := by
  rw [spectrum_mixedOperator_laplacian_empty_inter_Ioi hK htop]
  exact exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero hK hconn hne

end PDE

end TauCeti
