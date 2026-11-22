/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Degree
public import TauCeti.Algebra.Lie.Current.Vacuum.VectorField

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding

/-!
# The Segal--Sugawara operators and quadratic state on the vacuum module

Let `V = U / I₀` be the vacuum module (`TauCeti.CurrentAlgebra.VacuumModule`) of the residue central
extension of an invariant symmetric bilinear form `Φ` on `L` at central value `a`, with vacuum
vector `|0⟩` (`TauCeti.CurrentAlgebra.vacuum`). Because `V` is smooth for the natural-order left
ideals `I_n` (`TauCeti.CurrentAlgebra.smoothModules_natCast_vacuumModule`), the completed enveloping
algebra `Û = lim_N U / I_N` acts on `V` through `TauCeti.ModuleTower.limSmul`.

When `L` is finite-dimensional over a field `K` with nondegenerate Killing form `κ_L`, this file
studies the action of the Segal--Sugawara modes `Sₙ` and normalised Virasoro modes `Lₙ` on `V`, as
well as the quadratic Segal--Sugawara state `S₋₂ |0⟩` (`TauCeti.CurrentAlgebra.sugawaraVacuum`).

* **Action of regular Virasoro modes and conformal vector fields.** For `n ≥ -1`, all summands of
  `Sₙ` modulo `I₀` vanish, so `Sₙ` and `Lₙ` kill the vacuum `|0⟩`
  (`TauCeti.CurrentAlgebra.limSmul_sugawaraMode_vacuum_eq_zero`). Combining this with the inner
  derivation identity `ad(Sₘ) = (1 - 2 a c) • (-t^{m+1} d/dt)` shows that for `Φ = c • κ_L` and
  `m ≥ -1`, `Sₘ` acts on `V` as `(1 - 2 a c)` times the regular vector field `-t^{m+1} d/dt`
  (`TauCeti.CurrentAlgebra.limSmul_sugawaraMode_eq_smul_vacuumVectorField`). Away from the critical
  level (`1 - 2 a c ≠ 0`), `L₋₁` acts on `V` as the translation operator `T = -d/dt`
  (`TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_neg_one`), `L₀` acts as the conformal-weight
  operator `-t d/dt` (`TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_zero`), and `D_κ = -L₀` acts
  as `t d/dt`.
* **The quadratic Segal--Sugawara vacuum vector and current action.** At `n = -2`, the only
  surviving index modulo `I₀` is `m = -1`, so `S₋₂ |0⟩ = ∑ᵢ (bᵢ)₋₁ (b'ᵢ)₋₁ |0⟩` in every basis `b`
  of `L` and its Killing-dual basis `b'` (`TauCeti.CurrentAlgebra.sugawaraVacuum_eq_sum`), of
  conformal weight `2`
  (`TauCeti.CurrentAlgebra.sugawaraVacuum_mem_eigenspace_vacuumDegreeOperator`).
  Current modes of order `k = 0` or `k ≥ 2` annihilate `S₋₂ |0⟩` at every level, while at `k = 1`
  and `Φ = c • κ_L` one has `z₁ (S₋₂ |0⟩) = (1 - 2 a c) • z₋₁ |0⟩`
  (`TauCeti.CurrentAlgebra.envelopingι_single_one_smul_sugawaraVacuum_of_eq_smul_killingForm`).
  Hence `S₋₂ |0⟩` is killed by all nonnegative currents `L[[t]]` at the critical level `2 a Φ = κ_L`
  (`TauCeti.CurrentAlgebra.envelopingι_smul_sugawaraVacuum_eq_zero`), and is not killed by all of
  `L[[t]]` away from the critical level whenever `L` is nontrivial
  (`TauCeti.CurrentAlgebra.not_forall_envelopingι_smul_sugawaraVacuum_eq_zero`), so
  `S₋₂ ∉ Z(Û)` (`TauCeti.CurrentAlgebra.sugawaraMode_neg_two_notMem_center`).

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraVacuum`: the quadratic Segal--Sugawara vector `S₋₂ |0⟩` in the
  vacuum module.

## Main results

* `TauCeti.CurrentAlgebra.limSmul_sugawaraMode_eq_smul_vacuumVectorField`,
  `TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_eq_vacuumVectorField`,
  `TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_neg_one`,
  `TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_zero`: for `Φ = c • κ_L` and `m ≥ -1`, `Sₘ`
  acts on `V` as `(1 - 2 a c)` times the regular Witt vector field `-t^{m+1} d/dt`, and away from
  the critical level (`1 - 2 a c ≠ 0`), `Lₘ` acts as `-t^{m+1} d/dt`, with `L₋₁ = T` and
  `L₀ = -t d/dt` as special cases.
* `TauCeti.CurrentAlgebra.sugawaraVacuum_eq_sum`: `S₋₂ |0⟩ = ∑ᵢ (bᵢ)₋₁ (b'ᵢ)₋₁ |0⟩`.
* `TauCeti.CurrentAlgebra.envelopingι_smul_sugawaraVacuum_eq_zero`,
  `TauCeti.CurrentAlgebra.not_forall_envelopingι_smul_sugawaraVacuum_eq_zero`,
  `TauCeti.CurrentAlgebra.sugawaraMode_neg_two_notMem_center`: critical vs noncritical
  `L[[t]]`-invariance of `S₋₂ |0⟩` and non-centrality of `S₋₂` away from the critical level.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.2, §3.1, and §3.2.2.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4 and §2.5.10.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.7 and §5.7.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

attribute [local instance 1100] HahnSeries.instAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

/-! ### Action of Segal--Sugawara and Virasoro modes on the vacuum module -/

section SugawaraVacuum

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

local notation "c₀" => twoCocycleOfBilinear K L Φ hΦ hΦs
local notation "UK" => CentralQuotient K (centralElement c₀) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "V" => VacuumModule Φ hΦ hΦs a
local notation "hV" => smoothModules_natCast_vacuumModule Φ hΦ hΦs a
local notation "ι[" x ", " m "]" => envelopingι c₀ a (HahnSeries.single m (1 : K) ⊗ₜ[K] x)

/-- **The quadratic Segal--Sugawara vector** `S₋₂ |0⟩` in the vacuum module `V = U / I₀`, defined at
every level `Φ` and central value `a`. Away from the critical level, rescaling by `(1 - 2 a c)⁻¹`
gives the Virasoro conformal vector `L₋₂ |0⟩`; at the critical level `2 a Φ = κ_L`, it is a
quadratic `L[[t]]`-singular vector in `V`. -/
def sugawaraVacuum : V :=
  ModuleTower.limSmul hV (sugawaraMode Φ hΦ hΦs a (-2)) (vacuum Φ hΦ hΦs a)

variable {Φ hΦ hΦs a}

/-- `sugawaraVacuum` is the action of `S₋₂` on the vacuum vector `|0⟩`. -/
theorem sugawaraVacuum_def :
    sugawaraVacuum Φ hΦ hΦs a =
      ModuleTower.limSmul hV (sugawaraMode Φ hΦ hΦs a (-2)) (vacuum Φ hΦ hΦs a) :=
  (rfl)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem orderLeftIdeal_zero_smul_vacuum :
    ∀ u ∈ orderLeftIdeal Φ hΦ hΦs a (0 : ℕ), u • vacuum Φ hΦ hΦs a = 0 :=
  fun _ hu ↦ smul_vacuum_eq_zero_iff.2 (by simpa using hu)

/-- **Segal--Sugawara modes of index `n ≥ -1` kill the vacuum vector**, at every level and central
value. -/
theorem limSmul_sugawaraMode_vacuum_eq_zero {n : ℤ} (hn : -1 ≤ n) :
    ModuleTower.limSmul hV (sugawaraMode Φ hΦ hΦs a n) (vacuum Φ hΦ hΦs a) = 0 := by
  rw [limSmul_sugawaraMode hV (Module.finBasis K L) n orderLeftIdeal_zero_smul_vacuum]
  have hIco : Finset.Ico (min (n + 1) 0) 0 = ∅ := Finset.Ico_eq_empty (by omega)
  simp [hIco]

/-- **Normalised Segal--Sugawara Virasoro modes of index `n ≥ -1` kill the vacuum vector.** -/
theorem limSmul_sugawaraVirasoro_vacuum_eq_zero (c : K) {n : ℤ} (hn : -1 ≤ n) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c n) (vacuum Φ hΦ hΦs a) = 0 := by
  rw [sugawaraVirasoro_def, ModuleTower.smul_limSmul, limSmul_sugawaraMode_vacuum_eq_zero hn,
    smul_zero]

/-- **The Sugawara degree element `D_κ = -L₀` kills the vacuum vector.** -/
@[simp]
theorem limSmul_sugawaraDegree_vacuum_eq_zero (c : K) :
    ModuleTower.limSmul hV (sugawaraDegree Φ hΦ hΦs a c) (vacuum Φ hΦ hΦs a) = 0 := by
  rw [sugawaraDegree_def, ModuleTower.neg_limSmul,
    limSmul_sugawaraVirasoro_vacuum_eq_zero c (by omega), neg_zero]

/-- **For `Φ = c • κ_L` and `m ≥ -1`, `Sₘ` acts on the vacuum module as `(1 - 2 a c)` times the
regular Witt vector field `-t^{m+1} d/dt`**, at every level including the critical level. -/
theorem limSmul_sugawaraMode_eq_smul_vacuumVectorField {c : K}
    (h : Φ = c • killingForm K L) {m : ℤ} (hm : -1 ≤ m)
    (hh : 0 ≤ (-HahnSeries.single (m + 1) (1 : K)).orderTop) (v : V) :
    ModuleTower.limSmul hV (sugawaraMode Φ hΦ hΦs a m) v =
      (1 - 2 * a * c) •
        vacuumVectorField Φ hΦ hΦs a (-HahnSeries.single (m + 1) (1 : K)) hh v := by
  obtain ⟨u, rfl⟩ := exists_smul_vacuum_eq v
  have hd := congrArg (fun D : derivationLieAlgebra K Û ↦
      (D : Module.End K Û) (toCompletedEnveloping Φ hΦ hΦs a u))
    (innerDerivation_sugawaraMode_of_eq_smul_killingForm (hΦ := hΦ) (hΦs := hΦs) (a := a) h m)
  simp only [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def, SetLike.val_smul,
    LinearMap.smul_apply, coe_toCompletedEnveloping,
    vectorFieldCompletedEnvelopingDerivation_toLimQuotients] at hd
  simp only [← coe_toCompletedEnveloping] at hd
  rw [sub_eq_iff_eq_add] at hd
  have hv := congrArg (fun x ↦ ModuleTower.limSmul hV x (vacuum Φ hΦ hΦs a)) hd
  simpa only [mul_limSmul, limSmul_toCompletedEnveloping, ModuleTower.add_limSmul,
    ModuleTower.smul_limSmul, limSmul_sugawaraMode_vacuum_eq_zero hm, smul_zero, add_zero,
    vacuumVectorField_smul_vacuum] using hv

/-- **Away from the critical level, `Lₘ` (`m ≥ -1`) acts on the vacuum module as the regular Witt
vector field `-t^{m+1} d/dt`.** -/
theorem limSmul_sugawaraVirasoro_eq_vacuumVectorField {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) {m : ℤ} (hm : -1 ≤ m)
    (hh : 0 ≤ (-HahnSeries.single (m + 1) (1 : K)).orderTop) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c m) v =
      vacuumVectorField Φ hΦ hΦs a (-HahnSeries.single (m + 1) (1 : K)) hh v := by
  rw [sugawaraVirasoro_def, ModuleTower.smul_limSmul,
    limSmul_sugawaraMode_eq_smul_vacuumVectorField h hm hh, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Away from the critical level, `L₋₁` acts on the vacuum module as the translation operator
`T = -d/dt`.** -/
theorem limSmul_sugawaraVirasoro_neg_one {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-1)) v =
      vacuumTranslation Φ hΦ hΦs a v := by
  have h1 : (-HahnSeries.single (-1 + 1 : ℤ) (1 : K)) = -1 := by
    rw [neg_add_cancel, HahnSeries.single_zero_one]
  have hh : 0 ≤ (-1 : K⸨X⸩).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact HahnSeries.zero_le_orderTop_one
  rw [limSmul_sugawaraVirasoro_eq_vacuumVectorField h hc le_rfl (h1.symm ▸ hh),
    vacuumVectorField_congr _ hh h1, ← vacuumTranslation_def]

/-- **Away from the critical level, `L₀` acts on the vacuum module as the degree operator
`-t d/dt`.** -/
theorem limSmul_sugawaraVirasoro_zero {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c 0) v =
      vacuumDegreeOperator Φ hΦ hΦs a v := by
  have h1 : (-HahnSeries.single (0 + 1 : ℤ) (1 : K)) = -HahnSeries.single 1 1 := by
    rw [zero_add]
  have hh : 0 ≤ (-HahnSeries.single 1 1 : K⸨X⸩).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact HahnSeries.zero_le_orderTop_single zero_le_one 1
  rw [limSmul_sugawaraVirasoro_eq_vacuumVectorField h hc (by omega) (h1.symm ▸ hh),
    vacuumVectorField_congr _ hh h1, ← vacuumDegreeOperator_def]

/-- **Away from the critical level, `D_κ = -L₀` acts on the vacuum module as `-vacuumDegreeOperator`
(`t d/dt`).** -/
theorem limSmul_sugawaraDegree {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraDegree Φ hΦ hΦs a c) v =
      -vacuumDegreeOperator Φ hΦ hΦs a v := by
  rw [sugawaraDegree_def, ModuleTower.neg_limSmul, limSmul_sugawaraVirasoro_zero h hc]

/-! ### Basis expansion, conformal weight, and current action on `S₋₂ |0⟩` -/

/-- The Virasoro mode `L₋₂` sends `|0⟩` to `(1 - 2 a c)⁻¹ • S₋₂ |0⟩`. -/
@[simp]
theorem limSmul_sugawaraVirasoro_neg_two_vacuum (c : K) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-2)) (vacuum Φ hΦ hΦs a) =
      (1 - 2 * a * c)⁻¹ • sugawaraVacuum Φ hΦ hΦs a := by
  rw [sugawaraVirasoro_def, ModuleTower.smul_limSmul, sugawaraVacuum_def]

/-- **In any basis `b` of `L` with Killing-dual basis `b'`, `S₋₂ |0⟩ = ∑ᵢ (bᵢ)₋₁ (b'ᵢ)₋₁ |0⟩`.** -/
theorem sugawaraVacuum_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) :
    sugawaraVacuum Φ hΦ hΦs a =
      ∑ i, (ι[b i, -1] * ι[killingDualBasis b i, -1]) • vacuum Φ hΦ hΦs a := by
  rw [sugawaraVacuum_def, limSmul_sugawaraMode hV b (-2) orderLeftIdeal_zero_smul_vacuum]
  have hIco : Finset.Ico (min (-2 + 1 - ((0 : ℕ) : ℤ)) 0) ((0 : ℕ) : ℤ) = {-1} := by
    ext m
    simp only [Finset.mem_Ico, Finset.mem_singleton, Nat.cast_zero]
    omega
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hIco, Finset.sum_singleton, normalOrderedSummand_apply, neg_one_lt_zero, ↓reduceIte]
  norm_num

/-- **The quadratic Segal--Sugawara vector `S₋₂ |0⟩` has conformal weight `2`** for
`vacuumDegreeOperator`, at every level and central value. -/
theorem sugawaraVacuum_mem_eigenspace_vacuumDegreeOperator :
    sugawaraVacuum Φ hΦ hΦs a ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace 2 := by
  rw [sugawaraVacuum_eq_sum (Module.finBasis K L)]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h1 := ncoeff_currentField_apply_mem_eigenspace_vacuumDegreeOperator
    (killingDualBasis (Module.finBasis K L) i) (-1)
    (vacuum_mem_eigenspace_vacuumDegreeOperator (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a))
  have h2 := ncoeff_currentField_apply_mem_eigenspace_vacuumDegreeOperator
    (Module.finBasis K L i) (-1) h1
  simp only [ncoeff_currentField, envelopingAction_apply, ← mul_smul, Int.cast_neg,
    Int.cast_one] at h2
  convert h2 using 2
  norm_num

/-- **Action of a nonnegative current mode on `S₋₂ |0⟩`**: if `w` is Killing-dual to `Φ(z, ·)` and
`0 ≤ k`, then `z_k (S₋₂ |0⟩) = k (z - 2 a w)_{k-2} |0⟩`. -/
theorem envelopingι_single_smul_sugawaraVacuum_of_nonneg {z w : L}
    (hw : ∀ y, killingForm K L w y = Φ z y) {k : ℤ} (hk : 0 ≤ k) :
    ι[z, k] • sugawaraVacuum Φ hΦ hΦs a =
      (k : K) • (ι[z - (2 * a) • w, k - 2] • vacuum Φ hΦ hΦs a) := by
  have hcomm := toCompletedEnveloping_mul_sugawaraMode_sub_mul
    (hΦ := hΦ) (hΦs := hΦs) (a := a) hw k (-2)
  rw [sub_eq_iff_eq_add, neg_add_eq_sub] at hcomm
  have hv := congrArg (fun x ↦ ModuleTower.limSmul hV x (vacuum Φ hΦ hΦs a)) hcomm
  have hzk : ι[z, k] • vacuum Φ hΦ hΦs a = 0 :=
    envelopingι_smul_vacuum (single_tmul_mem_orderSubmodule K L hk 1 z)
  simpa only [mul_limSmul, limSmul_toCompletedEnveloping, ← sugawaraVacuum_def,
    ModuleTower.add_limSmul, ModuleTower.smul_limSmul, hzk, ModuleTower.limSmul_zero,
    add_zero] using hv

/-- **Zero-mode currents `z₀` annihilate `S₋₂ |0⟩` (`L`-invariance)**, at every level and central
value. -/
theorem envelopingι_single_zero_smul_sugawaraVacuum (z : L) :
    ι[z, 0] • sugawaraVacuum Φ hΦ hΦs a = 0 := by
  rw [envelopingι_single_smul_sugawaraVacuum_of_nonneg
    (killingForm_killingDuality_symm_apply K L (Φ z)) le_rfl, Int.cast_zero, zero_smul]

/-- **Constant currents `1 ⊗ z` annihilate `S₋₂ |0⟩` (`L`-invariance)**, at every level and central
value. -/
@[simp]
theorem envelopingι_one_tmul_smul_sugawaraVacuum (z : L) :
    envelopingι c₀ a ((1 : K⸨X⸩) ⊗ₜ[K] z) • sugawaraVacuum Φ hΦ hΦs a = 0 := by
  rw [← HahnSeries.single_zero_one, envelopingι_single_zero_smul_sugawaraVacuum]

/-- **Current modes `z_k` of order `k ≥ 2` annihilate `S₋₂ |0⟩`**, at every level and central
value. -/
theorem envelopingι_single_smul_sugawaraVacuum_eq_zero_of_two_le (z : L) {k : ℤ} (hk : 2 ≤ k) :
    ι[z, k] • sugawaraVacuum Φ hΦ hΦs a = 0 := by
  rw [envelopingι_single_smul_sugawaraVacuum_of_nonneg
    (killingForm_killingDuality_symm_apply K L (Φ z)) (by omega),
    envelopingι_smul_vacuum (single_tmul_mem_orderSubmodule K L (by omega) 1 _), smul_zero]

/-- **Action of `z₁` on `S₋₂ |0⟩` for `Φ = c • κ_L`**: `z₁ (S₋₂ |0⟩) = (1 - 2 a c) • z₋₁ |0⟩`. -/
theorem envelopingι_single_one_smul_sugawaraVacuum_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (z : L) :
    ι[z, 1] • sugawaraVacuum Φ hΦ hΦs a = (1 - 2 * a * c) • (ι[z, -1] • vacuum Φ hΦ hΦs a) := by
  have hw (y : L) : killingForm K L (c • z) y = Φ z y := by
    simp [h]
  rw [envelopingι_single_smul_sugawaraVacuum_of_nonneg hw zero_le_one, Int.cast_one, one_smul,
    smul_smul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_sub, map_smul, sub_smul,
    smul_assoc, sub_smul, one_smul]
  norm_num

/-- **At the critical level `2 a Φ = κ_L`, every nonnegative current in `L[[t]]` annihilates
`S₋₂ |0⟩`**, making `S₋₂ |0⟩` a singular vector for `L[[t]]`. -/
theorem envelopingι_smul_sugawaraVacuum_eq_zero (h : (2 * a) • Φ = killingForm K L)
    {u : currentAlgebra K L} (hu : u ∈ orderSubmodule K L 0) :
    envelopingι c₀ a u • sugawaraVacuum Φ hΦ hΦs a = 0 := by
  rw [sugawaraVacuum_def, ← limSmul_smul_of_mem_center hV (sugawaraMode_mem_center h (-2)),
    envelopingι_smul_vacuum hu, ModuleTower.limSmul_zero]

/-- **Away from the critical level, `S₋₂ |0⟩` is not annihilated by `L[[t]]` whenever `L` is
nontrivial**: if `z ≠ 0`, the mode `z₁` sends `S₋₂ |0⟩` to the nonzero vector
`(1 - 2 a c) • z₋₁ |0⟩`. -/
theorem not_forall_envelopingι_smul_sugawaraVacuum_eq_zero [Nontrivial L] {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) :
    ¬ ∀ u ∈ orderSubmodule K L 0, envelopingι c₀ a u • sugawaraVacuum Φ hΦ hΦs a = 0 := by
  intro hall
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  have h1 := hall (HahnSeries.single 1 (1 : K) ⊗ₜ[K] z)
    (single_tmul_mem_orderSubmodule K L zero_le_one 1 z)
  rw [envelopingι_single_one_smul_sugawaraVacuum_of_eq_smul_killingForm h z, smul_eq_zero] at h1
  have hv0 : ι[z, -1] • vacuum Φ hΦ hΦs a = 0 := h1.resolve_left hc
  rw [← negativeEnvelopingHom_ι_negativeSingle neg_one_lt_zero, ← vacuumPBWEquiv_apply,
    EmbeddingLike.map_eq_zero_iff] at hv0
  exact hz ((map_eq_zero_iff _ (negativeSingle_injective neg_one_lt_zero)).1
    ((map_eq_zero_iff _ (TauCeti.UniversalEnvelopingAlgebra.ι_injective K
      (negativeLieSubalgebra Φ hΦ hΦs))).1 hv0))

/-- **Away from the critical level, `S₋₂` does not lie in the completed center `Z(Û)`** when `L`
is nontrivial. -/
theorem sugawaraMode_neg_two_notMem_center [Nontrivial L] {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) :
    sugawaraMode Φ hΦ hΦs a (-2) ∉ Subalgebra.center K Û := by
  intro hz
  refine not_forall_envelopingι_smul_sugawaraVacuum_eq_zero (hΦ := hΦ) (hΦs := hΦs) h hc
    fun u hu ↦ ?_
  rw [sugawaraVacuum_def, ← limSmul_smul_of_mem_center hV hz, envelopingι_smul_vacuum hu,
    ModuleTower.limSmul_zero]

end SugawaraVacuum

end TauCeti.CurrentAlgebra
