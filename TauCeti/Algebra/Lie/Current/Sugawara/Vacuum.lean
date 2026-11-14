/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Degree
public import TauCeti.Algebra.Lie.Current.Vacuum.VectorField
public import TauCeti.Algebra.Lie.Killing.SymmetricAlgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Homogeneous
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective

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
  (`TauCeti.CurrentAlgebra.not_forall_envelopingι_smul_sugawaraVacuum_eq_zero`).
* **PBW symbol and nonscalarity.** Under the PBW isomorphism `U(t⁻¹ L[t⁻¹]) ≃ V`
  (`TauCeti.CurrentAlgebra.vacuumPBWEquiv`), `S₋₂ |0⟩` corresponds to
  `∑ᵢ ι(t⁻¹ ⊗ bᵢ) ι(t⁻¹ ⊗ b'ᵢ)` in PBW filtration degree `2`, whose class in `gr₂ U(t⁻¹ L[t⁻¹])` is
  the image of the quadratic symmetric Casimir `TauCeti.symmetricCasimir K L` along the mode-`(-1)`
  embedding (`TauCeti.CurrentAlgebra.pbwHomogeneousComponentMap_symmetricCasimir_eq`). When `2 ≠ 0`
  in `K` and `L` is nontrivial, injectivity of the PBW map and of `SymmetricAlgebra.map` shows that
  this PBW preimage does not lie in filtration degree `1`
  (`TauCeti.CurrentAlgebra.vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one`). Therefore
  `S₋₂ |0⟩` does not lie in the `K`-span of `|0⟩` at any level, including the critical level and
  `a = 0` (`TauCeti.CurrentAlgebra.sugawaraVacuum_notMem_span_vacuum`). In particular `S₋₂` is never
  a scalar in `Û` (`TauCeti.CurrentAlgebra.sugawaraMode_neg_two_notMem_bot`), so at the critical
  level the completed center `Z(Û)` is strictly larger than the scalars
  (`TauCeti.CurrentAlgebra.center_completedEnveloping_ne_bot`), whereas away from the critical level
  `S₋₂ ∉ Z(Û)` (`TauCeti.CurrentAlgebra.sugawaraMode_neg_two_notMem_center`).

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraVacuum`: the quadratic Segal--Sugawara vector `S₋₂ |0⟩` in the
  vacuum module.

## Main results

* `TauCeti.CurrentAlgebra.smoothModules_natCast_vacuumModule`: the vacuum module is smooth for the
  natural-order left ideals `I_n`.
* `TauCeti.CurrentAlgebra.limSmul_sugawaraMode_eq_smul_vacuumVectorField`,
  `TauCeti.CurrentAlgebra.limSmul_sugawaraVirasoro_eq_vacuumVectorField`: `Sₘ` and `Lₘ` implement
  the regular Witt vector fields `-t^{m+1} d/dt` on `V` for `m ≥ -1` (in particular `L₋₁ = T` and
  `L₀ = -t d/dt`).
* `TauCeti.CurrentAlgebra.sugawaraVacuum_eq_sum`: `S₋₂ |0⟩ = ∑ᵢ (bᵢ)₋₁ (b'ᵢ)₋₁ |0⟩`.
* `TauCeti.CurrentAlgebra.envelopingι_smul_sugawaraVacuum_eq_zero`,
  `TauCeti.CurrentAlgebra.not_forall_envelopingι_smul_sugawaraVacuum_eq_zero`: critical vs
  noncritical `L[[t]]`-invariance of `S₋₂ |0⟩`.
* `TauCeti.CurrentAlgebra.pbwHomogeneousComponentMap_symmetricCasimir_eq`: the degree-two PBW symbol
  of `S₋₂ |0⟩` is the mode-`(-1)` image of `symmetricCasimir K L`.
* `TauCeti.CurrentAlgebra.sugawaraVacuum_notMem_span_vacuum`: `S₋₂ |0⟩` is nonscalar in `V` at
  every level when `2 ≠ 0` and `L` is nontrivial.
* `TauCeti.CurrentAlgebra.center_completedEnveloping_ne_bot`: at the critical level, `Z(Û) ≠ ⊥`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.2, §3.1, and §3.2.2.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4 and §2.5.10.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.7 and §5.7.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open CategoryTheory LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

attribute [local instance 1100] HahnSeries.instAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

/-! ### Smoothness of the vacuum module for the natural-order left ideals -/

section Smooth

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "UK" => CentralQuotient R (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a

/-- **The vacuum module `U / I₀` is smooth** for the natural-order left ideals `I_n`, so the
completed enveloping algebra `Û` acts on it via `TauCeti.ModuleTower.limSmul`. -/
theorem smoothModules_natCast_vacuumModule :
    smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n)
      (ModuleCat.of UK (VacuumModule Φ hΦ hΦs a)) :=
  (smoothModules_orderLeftIdeal_natCast Φ hΦ hΦs a).symm ▸
    smoothModules_quotient_orderLeftIdeal Φ hΦ hΦs a 0

end Smooth

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
private theorem smul_limSmul_vacuumModule (r : K) (x : Û) (v : V) :
    ModuleTower.limSmul hV (r • x) v = r • ModuleTower.limSmul hV x v := by
  rw [Algebra.smul_def, ← (toCompletedEnveloping Φ hΦ hΦs a).commutes, mul_limSmul,
    limSmul_toCompletedEnveloping, algebraMap_smul]

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem neg_limSmul_vacuumModule (x : Û) (v : V) :
    ModuleTower.limSmul hV (-x) v = -ModuleTower.limSmul hV x v :=
  eq_neg_of_add_eq_zero_left (by rw [← ModuleTower.add_limSmul, neg_add_cancel,
    ModuleTower.zero_limSmul])

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
  rw [sugawaraVirasoro_def, smul_limSmul_vacuumModule, limSmul_sugawaraMode_vacuum_eq_zero hn,
    smul_zero]

/-- **The Sugawara degree element `D_κ = -L₀` kills the vacuum vector.** -/
@[simp]
theorem limSmul_sugawaraDegree_vacuum_eq_zero (c : K) :
    ModuleTower.limSmul hV (sugawaraDegree Φ hΦ hΦs a c) (vacuum Φ hΦ hΦs a) = 0 := by
  rw [sugawaraDegree_def, neg_limSmul_vacuumModule,
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
    smul_limSmul_vacuumModule, limSmul_sugawaraMode_vacuum_eq_zero hm, smul_zero, add_zero,
    vacuumVectorField_smul_vacuum] using hv

/-- **Away from the critical level, `Lₘ` (`m ≥ -1`) acts on the vacuum module as the regular Witt
vector field `-t^{m+1} d/dt`.** -/
theorem limSmul_sugawaraVirasoro_eq_vacuumVectorField {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) {m : ℤ} (hm : -1 ≤ m)
    (hh : 0 ≤ (-HahnSeries.single (m + 1) (1 : K)).orderTop) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c m) v =
      vacuumVectorField Φ hΦ hΦs a (-HahnSeries.single (m + 1) (1 : K)) hh v := by
  rw [sugawaraVirasoro_def, smul_limSmul_vacuumModule,
    limSmul_sugawaraMode_eq_smul_vacuumVectorField h hm hh, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Away from the critical level, `L₋₁` acts on the vacuum module as the translation operator
`T = -d/dt`.** -/
theorem limSmul_sugawaraVirasoro_neg_one {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-1)) v =
      vacuumTranslation Φ hΦ hΦs a v := by
  have hh : 0 ≤ (-HahnSeries.single (-1 + 1 : ℤ) (1 : K)).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact HahnSeries.zero_le_orderTop_single (by omega) 1
  have h1 : (-HahnSeries.single (-1 + 1 : ℤ) (1 : K)) = -1 := by
    rw [neg_add_cancel, HahnSeries.single_zero_one]
  have hvec (f g : K⸨X⸩) (hf : 0 ≤ f.orderTop) (hg : 0 ≤ g.orderTop) (hfg : f = g) :
      vacuumVectorField Φ hΦ hΦs a f hf = vacuumVectorField Φ hΦ hΦs a g hg := by
    subst hfg; rfl
  rw [limSmul_sugawaraVirasoro_eq_vacuumVectorField h hc le_rfl hh, hvec _ (-1) hh (h1 ▸ hh) h1,
    ← vacuumTranslation_def]

/-- **Away from the critical level, `L₀` acts on the vacuum module as the degree operator
`-t d/dt`.** -/
theorem limSmul_sugawaraVirasoro_zero {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c 0) v =
      vacuumDegreeOperator Φ hΦ hΦs a v := by
  have hh : 0 ≤ (-HahnSeries.single (0 + 1 : ℤ) (1 : K)).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact HahnSeries.zero_le_orderTop_single (by omega) 1
  have h1 : (-HahnSeries.single (0 + 1 : ℤ) (1 : K)) = -HahnSeries.single 1 1 := by
    rw [zero_add]
  have hvec (f g : K⸨X⸩) (hf : 0 ≤ f.orderTop) (hg : 0 ≤ g.orderTop) (hfg : f = g) :
      vacuumVectorField Φ hΦ hΦs a f hf = vacuumVectorField Φ hΦ hΦs a g hg := by
    subst hfg; rfl
  rw [limSmul_sugawaraVirasoro_eq_vacuumVectorField h hc (by omega) hh,
    hvec _ (-HahnSeries.single 1 1) hh (h1 ▸ hh) h1, ← vacuumDegreeOperator_def]

/-- **Away from the critical level, `D_κ = -L₀` acts on the vacuum module as `-vacuumDegreeOperator`
(`t d/dt`).** -/
theorem limSmul_sugawaraDegree {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (v : V) :
    ModuleTower.limSmul hV (sugawaraDegree Φ hΦ hΦs a c) v =
      -vacuumDegreeOperator Φ hΦ hΦs a v := by
  rw [sugawaraDegree_def, neg_limSmul_vacuumModule, limSmul_sugawaraVirasoro_zero h hc]

/-! ### Basis expansion, conformal weight, and current action on `S₋₂ |0⟩` -/

/-- The Virasoro mode `L₋₂` sends `|0⟩` to `(1 - 2 a c)⁻¹ • S₋₂ |0⟩`. -/
@[simp]
theorem limSmul_sugawaraVirasoro_neg_two_vacuum (c : K) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-2)) (vacuum Φ hΦ hΦs a) =
      (1 - 2 * a * c)⁻¹ • sugawaraVacuum Φ hΦ hΦs a := by
  rw [sugawaraVirasoro_def, smul_limSmul_vacuumModule, sugawaraVacuum_def]

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
  simp only [hIco, Finset.sum_singleton, normalOrderedSummand_apply, show (-1 : ℤ) < 0 by decide,
    ↓reduceIte, show (-2 : ℤ) - -1 = -1 by ring]

/-- **The quadratic Segal--Sugawara vector `S₋₂ |0⟩` has conformal weight `2`** for
`vacuumDegreeOperator`, at every level and central value. -/
theorem sugawaraVacuum_mem_eigenspace_vacuumDegreeOperator :
    sugawaraVacuum Φ hΦ hΦs a ∈ (vacuumDegreeOperator Φ hΦ hΦs a).eigenspace 2 := by
  have hh : 0 ≤ (-HahnSeries.single 1 1 : K⸨X⸩).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact HahnSeries.zero_le_orderTop_single zero_le_one 1
  have hact (x : L) :
      (vectorFieldEnvelopingDerivation Φ hΦ hΦs a (-HahnSeries.single 1 1) : Module.End K UK)
          ι[x, -1] = ι[x, -1] := by
    simp [vectorFieldEnvelopingDerivation_envelopingι, vectorFieldDerivation_neg,
      TensorProduct.neg_tmul]
  rw [sugawaraVacuum_eq_sum (Module.finBasis K L)]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Module.End.mem_eigenspace_iff, vacuumDegreeOperator_def hh, vacuumVectorField_smul_vacuum,
    derivationLieAlgebra.leibniz, hact, hact, ← two_smul K (_ * _), smul_assoc]

/-- **Action of a nonnegative current mode on `S₋₂ |0⟩`**: if `w` is Killing-dual to `Φ(z, ·)` and
`0 ≤ k`, then `z_k (S₋₂ |0⟩) = k (z - 2 a w)_{k-2} |0⟩`. -/
theorem envelopingι_single_smul_sugawaraVacuum_of_nonneg {z w : L}
    (hw : ∀ y, killingForm K L w y = Φ z y) {k : ℤ} (hk : 0 ≤ k) :
    ι[z, k] • sugawaraVacuum Φ hΦ hΦs a =
      (k : K) • (ι[z - (2 * a) • w, k - 2] • vacuum Φ hΦ hΦs a) := by
  have hcomm := toCompletedEnveloping_mul_sugawaraMode_sub_mul
    (hΦ := hΦ) (hΦs := hΦs) (a := a) hw k (-2)
  rw [sub_eq_iff_eq_add, show (-2 : ℤ) + k = k - 2 by ring] at hcomm
  have hv := congrArg (fun x ↦ ModuleTower.limSmul hV x (vacuum Φ hΦ hΦs a)) hcomm
  have hzk : ι[z, k] • vacuum Φ hΦ hΦs a = 0 :=
    envelopingι_smul_vacuum (single_tmul_mem_orderSubmodule K L hk 1 z)
  simpa only [mul_limSmul, limSmul_toCompletedEnveloping, ← sugawaraVacuum_def,
    ModuleTower.add_limSmul, smul_limSmul_vacuumModule, hzk, ModuleTower.limSmul_zero,
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
    show (1 : ℤ) - 2 = -1 by ring, smul_smul,
    show z - (2 * a * c) • z = (1 - 2 * a * c) • z by module,
    TensorProduct.tmul_smul, map_smul, smul_assoc]

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
  have hi := congrArg (negativeEnvelopingHom Φ hΦ hΦs a) hv0
  rw [map_zero, negativeEnvelopingHom_ι_negativeSingle] at hi
  have ht := (map_eq_zero_iff _ (envelopingι_injective Φ hΦ hΦs a)).1 hi
  have hc0 := congrArg (coeff K L (-1)) ht
  rw [map_zero, coeff_tmul, HahnSeries.coeff_single_same, one_smul] at hc0
  exact hz hc0

/-! ### PBW preimage, quadratic Casimir symbol, and nonscalarity -/

local notation "Nneg" => negativeLieSubalgebra Φ hΦ hΦs
local notation "Uneg" => _root_.UniversalEnvelopingAlgebra K Nneg

/-- **The PBW preimage of `S₋₂ |0⟩` in `U(t⁻¹ L[t⁻¹])`** is `∑ᵢ ι(t⁻¹ ⊗ bᵢ) ι(t⁻¹ ⊗ b'ᵢ)` in every
basis `b` of `L` with Killing-dual basis `b'`. -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) =
      ∑ i, _root_.UniversalEnvelopingAlgebra.ι K (negativeSingle Φ hΦ hΦs neg_one_lt_zero (b i)) *
        _root_.UniversalEnvelopingAlgebra.ι K
          (negativeSingle Φ hΦ hΦs neg_one_lt_zero (killingDualBasis b i)) := by
  rw [sugawaraVacuum_eq_sum b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← negativeEnvelopingHom_ι_negativeSingle neg_one_lt_zero,
    ← negativeEnvelopingHom_ι_negativeSingle neg_one_lt_zero, ← map_mul,
    vacuumPBWEquiv_symm_smul_vacuum]

/-- **The PBW preimage of `S₋₂ |0⟩` lies in PBW filtration degree `2`.** -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∈ pbwFiltration K Nneg 2 := by
  rw [vacuumPBWEquiv_symm_sugawaraVacuum (Module.finBasis K L)]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact mul_mem_pbwFiltration K Nneg (ι_mem_pbwFiltration_one K Nneg _)
    (ι_mem_pbwFiltration_one K Nneg _)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem pbwGradedPiece_mk_sum {ι : Type*} (s : Finset ι)
    (q : ι → TauCeti.Algebra.wordFiltration
      (_root_.UniversalEnvelopingAlgebra.ι K : Nneg →ₗ⁅K⁆ Uneg).toLinearMap 2) :
    (Submodule.Quotient.mk (∑ i ∈ s, q i) : PBWGradedPiece K Nneg 2) =
      ∑ i ∈ s, Submodule.Quotient.mk (q i) := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons j s hj ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

/-- **The degree-two PBW graded class of `S₋₂ |0⟩` is the PBW image of the mode-`(-1)` quadratic
symmetric Casimir `SymmetricAlgebra.map K (negativeSingle ...) (symmetricCasimir K L)`.** -/
theorem pbwHomogeneousComponentMap_symmetricCasimir_eq :
    pbwHomogeneousComponentMap K Nneg 2
        ⟨SymmetricAlgebra.map K (negativeSingle Φ hΦ hΦs neg_one_lt_zero) (symmetricCasimir K L),
          TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
            (symmetricCasimir_mem_homogeneousSubmodule K L)⟩ =
      (Submodule.Quotient.mk
        ⟨(vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a), by
          rw [← pbwFiltration_def]
          exact vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two⟩ :
        PBWGradedPiece K Nneg 2) := by
  set b := Module.finBasis K L
  set e := negativeSingle Φ hΦ hΦs (neg_one_lt_zero : (-1 : ℤ) < 0)
  let p (i : Fin (Module.finrank K L)) :
      TauCeti.SymmetricAlgebra.homogeneousSubmodule K Nneg 2 :=
    ⟨([e (b i), e (killingDualBasis b i)].map (SymmetricAlgebra.ι K Nneg)).prod,
      TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule K Nneg
        [e (b i), e (killingDualBasis b i)]⟩
  let q (i : Fin (Module.finrank K L)) :
      TauCeti.Algebra.wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι K : Nneg →ₗ⁅K⁆ Uneg).toLinearMap 2 :=
    ⟨([e (b i), e (killingDualBasis b i)].map (_root_.UniversalEnvelopingAlgebra.ι K)).prod,
      TauCeti.Algebra.prod_map_mem_wordFiltration _ le_rfl⟩
  have hp : (⟨SymmetricAlgebra.map K e (symmetricCasimir K L),
      TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
        (symmetricCasimir_mem_homogeneousSubmodule K L)⟩ :
      TauCeti.SymmetricAlgebra.homogeneousSubmodule K Nneg 2) = ∑ i, p i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, p, symmetricCasimir_eq_sum b, map_sum, map_mul,
      SymmetricAlgebra.map_apply_ι, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
  have hq : (⟨(vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a), by
      rw [← pbwFiltration_def]
      exact vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two⟩ :
      TauCeti.Algebra.wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι K : Nneg →ₗ⁅K⁆ Uneg).toLinearMap 2) = ∑ i, q i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, q, e, vacuumPBWEquiv_symm_sugawaraVacuum b,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  let mk2 : TauCeti.Algebra.wordFiltration
      (_root_.UniversalEnvelopingAlgebra.ι K : Nneg →ₗ⁅K⁆ Uneg).toLinearMap 2 →
      PBWGradedPiece K Nneg 2 := Submodule.Quotient.mk
  have hlhs : pbwHomogeneousComponentMap K Nneg 2
      ⟨SymmetricAlgebra.map K e (symmetricCasimir K L),
        TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _
          (symmetricCasimir_mem_homogeneousSubmodule K L)⟩ = ∑ i, mk2 (q i) := by
    rw [hp, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      pbwHomogeneousComponentMap_prod_map_ι K Nneg [e (b i), e (killingDualBasis b i)]
  exact hlhs.trans ((congrArg mk2 hq).trans (pbwGradedPiece_mk_sum Finset.univ q)).symm

/-- **Away from characteristic two, the PBW preimage of `S₋₂ |0⟩` for a nontrivial Lie algebra does
not lie in PBW filtration degree `1`** (it has exact PBW degree `2`). -/
theorem vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one
    [NeZero (2 : K)] [Nontrivial L] :
    (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∉ pbwFiltration K Nneg 1 := by
  intro hmem
  have hprev : (vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a) ∈
      TauCeti.Algebra.wordFiltrationPrevious
        (_root_.UniversalEnvelopingAlgebra.ι K : Nneg →ₗ⁅K⁆ Uneg).toLinearMap 2 := by
    rwa [← pbwFiltrationPrevious_def, pbwFiltrationPrevious_succ]
  have hmk : (Submodule.Quotient.mk
      ⟨(vacuumPBWEquiv Φ hΦ hΦs a).symm (sugawaraVacuum Φ hΦ hΦs a), by
        rw [← pbwFiltration_def]
        exact vacuumPBWEquiv_symm_sugawaraVacuum_mem_pbwFiltration_two⟩ :
      PBWGradedPiece K Nneg 2) = 0 :=
    (TauCeti.Algebra.wordFiltration.gradedPiece_mk_eq_zero_iff _ _).2 hprev
  rw [← pbwHomogeneousComponentMap_symmetricCasimir_eq] at hmk
  have hsym := pbwHomogeneousComponentMap_injective K Nneg 2
    (hmk.trans (map_zero (pbwHomogeneousComponentMap K Nneg 2)).symm)
  have hmap : SymmetricAlgebra.map K (negativeSingle Φ hΦ hΦs neg_one_lt_zero)
      (symmetricCasimir K L) = 0 := congrArg Subtype.val hsym
  have hcas := SymmetricAlgebra.map_injective (negativeSingle Φ hΦ hΦs neg_one_lt_zero)
    (negativeSingle_injective neg_one_lt_zero) (hmap.trans (map_zero _).symm)
  exact symmetricCasimir_ne_zero K L hcas

/-- **Away from characteristic two, `S₋₂ |0⟩` is not a scalar multiple of the vacuum vector `|0⟩`**
when `L` is nontrivial, at every level `Φ` and central value `a` (including the critical level and
`a = 0`). -/
theorem sugawaraVacuum_notMem_span_vacuum [NeZero (2 : K)] [Nontrivial L] :
    sugawaraVacuum Φ hΦ hΦs a ∉ Submodule.span K {vacuum Φ hΦ hΦs a} := by
  intro hspan
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hspan
  apply vacuumPBWEquiv_symm_sugawaraVacuum_notMem_pbwFiltration_one
    (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  rw [← hr, map_smul, ← vacuumPBWEquiv_one (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a),
    LinearEquiv.symm_apply_apply, Algebra.smul_def, mul_one]
  exact algebraMap_mem_pbwFiltration K Nneg r 1

/-- **Away from characteristic two, `S₋₂ |0⟩ ≠ 0` when `L` is nontrivial**, at every level `Φ` and
central value `a`. -/
theorem sugawaraVacuum_ne_zero [NeZero (2 : K)] [Nontrivial L] :
    sugawaraVacuum Φ hΦ hΦs a ≠ 0 :=
  fun h0 ↦ sugawaraVacuum_notMem_span_vacuum (h0 ▸ Submodule.zero_mem _)

/-- **Away from characteristic two and the critical level, the Virasoro conformal vector
`L₋₂ |0⟩` is not a scalar multiple of `|0⟩`** when `L` is nontrivial. -/
theorem limSmul_sugawaraVirasoro_neg_two_vacuum_notMem_span_vacuum
    [NeZero (2 : K)] [Nontrivial L] {c : K} (hc : 1 - 2 * a * c ≠ 0) :
    ModuleTower.limSmul hV (sugawaraVirasoro Φ hΦ hΦs a c (-2)) (vacuum Φ hΦ hΦs a) ∉
      Submodule.span K {vacuum Φ hΦ hΦs a} := by
  rw [limSmul_sugawaraVirasoro_neg_two_vacuum]
  intro hspan
  apply sugawaraVacuum_notMem_span_vacuum (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  have h2 := Submodule.smul_mem _ (1 - 2 * a * c) hspan
  rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at h2

/-- **Away from characteristic two, `S₋₂` is not a scalar in the completed enveloping algebra `Û`**
when `L` is nontrivial, at every level `Φ` and central value `a`. -/
theorem sugawaraMode_neg_two_notMem_bot [NeZero (2 : K)] [Nontrivial L] :
    sugawaraMode Φ hΦ hΦs a (-2) ∉ (⊥ : Subalgebra K Û) := by
  intro hbot
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 hbot
  apply sugawaraVacuum_notMem_span_vacuum (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
  rw [sugawaraVacuum_def, ← hr, ← (toCompletedEnveloping Φ hΦ hΦs a).commutes,
    limSmul_toCompletedEnveloping, algebraMap_smul]
  exact Submodule.mem_span_singleton.2 ⟨r, rfl⟩

/-- **Away from characteristic two, `S₋₂ ≠ 0` in `Û` when `L` is nontrivial**, at every level `Φ`
and central value `a`. -/
theorem sugawaraMode_neg_two_ne_zero [NeZero (2 : K)] [Nontrivial L] :
    sugawaraMode Φ hΦ hΦs a (-2) ≠ 0 :=
  fun h0 ↦ sugawaraMode_neg_two_notMem_bot (h0 ▸ Subalgebra.zero_mem ⊥)

/-- **At the critical level `2 a Φ = κ_L`, the completed center `Z(Û)` is strictly larger than the
scalars `K`** whenever `2 ≠ 0` in `K` and `L` is nontrivial, witnessed by `S₋₂ ∈ Z(Û) \ K`. -/
theorem center_completedEnveloping_ne_bot [NeZero (2 : K)] [Nontrivial L]
    (h : (2 * a) • Φ = killingForm K L) :
    Subalgebra.center K Û ≠ ⊥ := by
  intro hbot
  exact sugawaraMode_neg_two_notMem_bot (hbot ▸ sugawaraMode_mem_center h (-2))

/-- **Away from characteristic two and the critical level, `S₋₂` does not lie in the completed
center `Z(Û)`** when `L` is nontrivial. -/
theorem sugawaraMode_neg_two_notMem_center [NeZero (2 : K)] [Nontrivial L] {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) :
    sugawaraMode Φ hΦ hΦs a (-2) ∉ Subalgebra.center K Û := by
  intro hz
  have hd := vectorFieldCompletedEnvelopingDerivation_single_one_eq_zero_of_mem_center h hc hz
  rw [vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraMode,
    ← Int.cast_smul_eq_zsmul K, smul_eq_zero] at hd
  have h20 : ((-2 : ℤ) : K) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_ofNat, neg_ne_zero]
    exact NeZero.ne (2 : K)
  exact sugawaraMode_neg_two_ne_zero (hd.resolve_left h20)

end SugawaraVacuum

end TauCeti.CurrentAlgebra
