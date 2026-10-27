/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Count
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Independence
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Normalized
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The weight-two Eisenstein subspace with fixed nebentypus

In weight two the Eisenstein series of an index `(ψ, φ, t)` of
`TauCeti.EisensteinSeries.CharIndex N 2` (primitive characters `ψ` modulo `u` and `φ` modulo
`v` with `ψ(-1) φ(-1) = 1`, and `t u v ∣ N`) is, following Diamond–Shurman §4.6,

* the normalized raised series `E₂^{ψ,φ,t}` (`TauCeti.EisensteinSeries.normalizedCharG2MFRaise`)
  when `(ψ, φ)` is not the trivial pair, and
* the corrected series `E₂(z) - t E₂(t z)` (`TauCeti.EisensteinSeries.correctedE2`) when
  `ψ = φ = 1`, since the trivial pair gives no modular series in weight two.

The second family vanishes exactly at `t = 1`, so the nonzero series are those of the indices
other than `(1, 1, 1)`. These are linearly independent in `M₂(Γ₁(N))` (Diamond–Shurman,
Theorem 4.6.2), and the series of nebentypus `χ` span the Eisenstein subspace of `M₂(N, χ)`
defined here, of dimension the number of such indices.

The proof of independence reads off the positive Fourier coefficients, as in weight `k ≥ 3`. Those
of `E₂^{ψ,φ,t}` form the sequence `n ↦ σ₁^{ψ,φ}(n / t)` on the multiples of `t`, and those of
`E₂(z) - t E₂(t z)` are `-24` times the sequence of `(1, 1, 1)` plus `24 t` times that of
`(1, 1, t)`. The sequences of all indices are linearly independent
(`TauCeti.EisensteinSeries.CharIndex.linearIndependent_twistedDivisorSum`). In a vanishing
combination of the series, the sequence of each index other than `(1, 1, 1)` comes from its own
series alone, with a nonzero factor, so every coefficient of the combination vanishes.

## Main definitions

* `TauCeti.EisensteinSeries.CharIndex.weightTwoForm`: the weight-two Eisenstein series of an
  index.
* `TauCeti.weightTwoEisensteinSubspace`: the span in `M₂(N, χ)` of the series of nebentypus `χ`.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.weightTwoForm_mem_modFormCharSpace`: the series of an index
  lies in the character space of its nebentypus.
* `TauCeti.EisensteinSeries.CharIndex.qExpansion_weightTwoForm_coeff_of_ne_one` and
  `TauCeti.EisensteinSeries.CharIndex.qExpansion_weightTwoForm_coeff_of_eq_one`: its positive
  Fourier coefficients.
* `TauCeti.EisensteinSeries.CharIndex.weightTwoForm_eq_zero_iff` and
  `TauCeti.EisensteinSeries.CharIndex.weightTwoForm_eq_zero_iff_eq_one`: it vanishes exactly at
  the index `(1, 1, 1)` (`TauCeti.EisensteinSeries.CharIndex.one`).
* `TauCeti.EisensteinSeries.CharIndex.linearIndepOn_weightTwoForm`: the nonzero series are
  linearly independent.
* `TauCeti.finrank_weightTwoEisensteinSubspace`: the weight-two Eisenstein subspace of `M₂(N, χ)`
  has dimension the number of indices of nebentypus `χ` other than `(1, 1, 1)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6,
  Theorem 4.6.2.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauCeti.EisensteinSeries.CharIndex

variable {N : ℕ} [NeZero N] (a : CharIndex N 2)

open scoped Classical in
/-- The weight-two Eisenstein series of an index `(ψ, φ, t)` (Diamond–Shurman §4.6): the
normalized raised series `E₂^{ψ,φ,t}` unless `ψ` and `φ` are both trivial, and the corrected
series `E₂(z) - t E₂(t z)`, restricted from `Γ₀(t)` to `Γ₁(N)`, for the trivial pair. -/
def weightTwoForm : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 :=
  haveI : NeZero a.t := NeZero.of_dvd a.t_dvd
  if a.psi = 1 ∧ a.phi = 1 then
    ModularForm.restrict (Gamma1_map_le_Gamma0_map N)
      (ModularForm.restrict (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd a.t_dvd))
        (correctedE2 a.t))
  else normalizedCharG2MFRaise a.psi a.phi a.t a.level_dvd

/-- For the trivial pair, the weight-two series of an index is the corrected series
`E₂(z) - t E₂(t z)`. -/
theorem weightTwoForm_of_eq_one (h : a.psi = 1 ∧ a.phi = 1) :
    haveI : NeZero a.t := NeZero.of_dvd a.t_dvd
    a.weightTwoForm = ModularForm.restrict (Gamma1_map_le_Gamma0_map N)
      (ModularForm.restrict (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd a.t_dvd))
        (correctedE2 a.t)) := by
  rw [weightTwoForm, ite_eq_left h]

/-- Away from the trivial pair, the weight-two series of an index is `E₂^{ψ,φ,t}`. -/
theorem weightTwoForm_of_ne_one (h : a.psi ≠ 1 ∨ a.phi ≠ 1) :
    a.weightTwoForm = normalizedCharG2MFRaise a.psi a.phi a.t a.level_dvd := by
  rw [weightTwoForm, ite_eq_right (not_and_or.mpr h)]

/-- The weight-two series of an index belongs to the character space of its nebentypus. -/
theorem weightTwoForm_mem_modFormCharSpace :
    a.weightTwoForm ∈ modFormCharSpace 2 a.nebentypus := by
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · rw [weightTwoForm_of_eq_one a h, nebentypus_eq_one a h]
    exact restrict_mem_modFormCharSpace_one _
  · rw [weightTwoForm_of_ne_one a (not_and_or.mp h), nebentypus_def]
    exact normalizedCharG2MFRaise_mem_modFormCharSpace a.psi a.phi a.level_dvd

/-- The positive Fourier coefficients of the weight-two series of an index `(ψ, φ, t)` away from
the trivial pair are the twisted divisor sums `σ₁^{ψ,φ}(n / t)` at multiples `n` of `t`, and zero
at the other positive indices. -/
theorem qExpansion_weightTwoForm_coeff_of_ne_one (h : a.psi ≠ 1 ∨ a.phi ≠ 1) {n : ℕ}
    (hn : n ≠ 0) :
    (qExpansion 1 a.weightTwoForm).coeff n =
      if a.t ∣ n then DirichletCharacter.twistedDivisorSum 1 a.psi a.phi (n / a.t) else 0 := by
  rw [weightTwoForm_of_ne_one a h]
  exact qExpansion_normalizedCharG2MFRaise_coeff a.psi a.phi a.level_dvd h
    (by simpa using a.parity) a.phi_primitive hn

/-- The positive Fourier coefficients of the weight-two series of an index `(1, 1, t)` are those
of `E₂(z) - t E₂(t z)`: `-24 (σ₁(n) - t σ₁(n / t))`, the second term present only when `t ∣ n`. -/
theorem qExpansion_weightTwoForm_coeff_of_eq_one (h : a.psi = 1 ∧ a.phi = 1) {n : ℕ}
    (hn : n ≠ 0) :
    (qExpansion 1 a.weightTwoForm).coeff n =
      -24 * ((σ 1 n : ℂ) - if a.t ∣ n then a.t * (σ 1 (n / a.t) : ℂ) else 0) := by
  have : NeZero a.t := NeZero.of_dvd a.t_dvd
  rw [weightTwoForm_of_eq_one a h]
  simpa only [ModularForm.coe_restrict, ite_eq_right hn] using qExpansion_coeff_correctedE2 a.t n

/-- The weight-two series of an index vanishes exactly at the index `(1, 1, 1)`. -/
theorem weightTwoForm_eq_zero_iff :
    a.weightTwoForm = 0 ↔ a.psi = 1 ∧ a.phi = 1 ∧ a.t = 1 := by
  have : NeZero a.t := NeZero.of_dvd a.t_dvd
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · simp only [h, true_and, weightTwoForm_of_eq_one a h, ← correctedE2_eq_zero_iff a.t]
    constructor <;> intro H <;> ext z
    · simpa using DFunLike.congr_fun H z
    · simp [H]
  · rw [weightTwoForm_of_ne_one a (not_and_or.mp h)]
    exact iff_of_false (normalizedCharG2MFRaise_ne_zero a.psi a.phi a.level_dvd
      (not_and_or.mp h) (by simpa using a.parity) a.phi_primitive) fun h' ↦ h ⟨h'.1, h'.2.1⟩

/-- The weight-two series of an index vanishes exactly at the index `(1, 1, 1)`, stated as an
equality of indices. -/
theorem weightTwoForm_eq_zero_iff_eq_one : a.weightTwoForm = 0 ↔ a = one even_two := by
  rw [weightTwoForm_eq_zero_iff, eq_one_iff]

open scoped Classical in
/-- The positive coefficients of the weight-two series of an index, as a combination of the
sequences of `linearIndependent_twistedDivisorSum`: for the trivial pair, `24 t` times the
sequence of the index minus `24` times that of `(1, 1, 1)`. -/
private lemma qExpansion_weightTwoForm_coeff_eq (n : {n : ℕ // n ≠ 0}) :
    (qExpansion 1 a.weightTwoForm).coeff n =
      (if a.psi = 1 ∧ a.phi = 1 then 24 * (a.t : ℂ) else 1) *
          (if a.t ∣ (n : ℕ) then DirichletCharacter.twistedDivisorSum 1 a.psi a.phi (n / a.t)
            else 0) +
        (if a.psi = 1 ∧ a.phi = 1 then -24 else 0) *
          (if (one even_two : CharIndex N 2).t ∣ (n : ℕ) then
            DirichletCharacter.twistedDivisorSum 1 (one even_two : CharIndex N 2).psi
              (one even_two : CharIndex N 2).phi (n / (one even_two : CharIndex N 2).t)
          else 0) := by
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · rw [qExpansion_weightTwoForm_coeff_of_eq_one a h n.2, ite_eq_left h, ite_eq_left h,
      twistedDivisorSum_of_eq_one a h, twistedDivisorSum_of_eq_one (one even_two) ⟨rfl, rfl⟩]
    simp only [one, one_dvd, ite_true, Nat.div_one]
    split_ifs <;> ring
  · rw [qExpansion_weightTwoForm_coeff_of_ne_one a (not_and_or.mp h) n.2, ite_eq_right h,
      ite_eq_right h]
    ring

/-- **Linear independence of the weight-two Eisenstein series** (Diamond–Shurman,
Theorem 4.6.2): the nonzero weight-two series `E₂^{ψ,φ,t}` and `E₂(z) - t E₂(t z)`, those of the
indices other than `(1, 1, 1)`, are linearly independent. -/
theorem linearIndepOn_weightTwoForm :
    LinearIndepOn ℂ weightTwoForm {a : CharIndex N 2 | a.weightTwoForm ≠ 0} := by
  classical
  let _ : Fintype (CharIndex N 2) := Fintype.ofFinite _
  -- The positive Fourier coefficients.
  let L : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 →ₗ[ℂ] {n : ℕ // n ≠ 0} → ℂ :=
    LinearMap.pi fun n ↦ (PowerSeries.coeff (n : ℕ)).comp
      (ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) 2)
  have hv := linearIndependent_twistedDivisorSum (N := N) (k := 2) one_ne_zero
  set v := fun (a : CharIndex N 2) (n : {n : ℕ // n ≠ 0}) ↦
    if a.t ∣ (n : ℕ) then DirichletCharacter.twistedDivisorSum 1 a.psi a.phi (n / a.t) else 0
  set α : CharIndex N 2 → ℂ := fun a ↦ if a.psi = 1 ∧ a.phi = 1 then 24 * (a.t : ℂ) else 1
  set β : CharIndex N 2 → ℂ := fun a ↦ if a.psi = 1 ∧ a.phi = 1 then -24 else 0
  have hL (a : CharIndex N 2) : L a.weightTwoForm = α a • v a + β a • v (one even_two) := by
    funext n
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, ModularForm.qExpansionLinearMap_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact qExpansion_weightTwoForm_coeff_eq a n
  refine linearIndepOn_iff.mpr fun l hl hzero ↦ ?_
  -- Rewrite the relation among the series as one among the sequences `v`.
  have hrel : ∑ a, (l a * α a + if a = one even_two then ∑ b, l b * β b else 0) • v a = 0 := by
    have h := congrArg L hzero
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), map_sum,
      map_zero] at h
    simp only [map_smul, hL, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul] at h
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, mul_smul]
    simpa [mul_smul] using h
  ext a
  by_cases ha : a.weightTwoForm = 0
  · exact Finsupp.notMem_support_iff.mp fun h ↦ hl h ha
  have hne : a ≠ one even_two := fun h ↦ ha <| (weightTwoForm_eq_zero_iff_eq_one _).mpr h
  have h := Fintype.linearIndependent_iff.mp hv _ hrel a
  rw [ite_eq_right hne, add_zero] at h
  have hα : α a ≠ 0 := by
    have : (a.t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.of_dvd a.t_dvd).out
    simp only [α]
    split_ifs <;> simp [this]
  simpa [hα] using h

variable {χ : (ZMod N)ˣ →* ℂˣ}

/-- The weight-two series of an index, as an element of a character space whose character agrees
with the nebentypus of the index. -/
def weightTwoInCharSpace (hχ : a.nebentypus = χ) : modFormCharSpace 2 χ :=
  ⟨a.weightTwoForm, hχ ▸ a.weightTwoForm_mem_modFormCharSpace⟩

/-- Coercing `weightTwoInCharSpace` forgets only the proof of character-space membership. -/
@[simp]
theorem coe_weightTwoInCharSpace (hχ : a.nebentypus = χ) :
    (a.weightTwoInCharSpace hχ : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) = a.weightTwoForm :=
  (rfl)

/-- The nonzero weight-two series of nebentypus `χ` are linearly independent in `M₂(N, χ)`. -/
theorem linearIndependent_weightTwoInCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ fun a : {a : CharIndex N 2 // a.nebentypus = χ ∧ a.weightTwoForm ≠ 0} ↦
      a.1.weightTwoInCharSpace a.2.1 := by
  let f (a : {a : CharIndex N 2 // a.nebentypus = χ ∧ a.weightTwoForm ≠ 0}) :
      {a : CharIndex N 2 | a.weightTwoForm ≠ 0} := ⟨a.1, a.2.2⟩
  have hf : Function.Injective f := fun a b hab ↦
    Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
  refine LinearIndependent.of_comp (modFormCharSpace 2 χ).subtype ?_
  exact (linearIndepOn_weightTwoForm (N := N)).comp f hf

end TauCeti.EisensteinSeries.CharIndex

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)

/-- The **weight-two Eisenstein subspace** of `M₂(N, χ)`: the span of the weight-two Eisenstein
series `E₂^{ψ,φ,t}` and `E₂(z) - t E₂(t z)` of the indices of nebentypus `χ`. -/
def weightTwoEisensteinSubspace : Submodule ℂ (modFormCharSpace 2 χ) :=
  Submodule.span ℂ (Set.range fun a : {a : CharIndex N 2 // a.nebentypus = χ} ↦
    a.1.weightTwoInCharSpace a.2)

/-- The defining span of the weight-two Eisenstein subspace. -/
theorem weightTwoEisensteinSubspace_def :
    weightTwoEisensteinSubspace χ =
      Submodule.span ℂ (Set.range fun a : {a : CharIndex N 2 // a.nebentypus = χ} ↦
        a.1.weightTwoInCharSpace a.2) :=
  (rfl)

/-- The weight-two series of an index of nebentypus `χ` belongs to the weight-two Eisenstein
subspace. -/
theorem mem_weightTwoEisensteinSubspace (a : CharIndex N 2) (hχ : a.nebentypus = χ) :
    a.weightTwoInCharSpace hχ ∈ weightTwoEisensteinSubspace χ :=
  Submodule.subset_span ⟨⟨a, hχ⟩, rfl⟩

/-- A form belongs to the weight-two Eisenstein subspace exactly when it is a finite linear
combination of the weight-two series of the indices of nebentypus `χ`. -/
theorem mem_weightTwoEisensteinSubspace_iff (f : modFormCharSpace 2 χ) :
    f ∈ weightTwoEisensteinSubspace χ ↔
      ∃ c : {a : CharIndex N 2 // a.nebentypus = χ} →₀ ℂ,
        c.sum (fun a z ↦ z • a.1.weightTwoInCharSpace a.2) = f :=
  Finsupp.mem_span_range_iff_exists_finsupp

/-- Elimination rule for the weight-two Eisenstein subspace: a subspace containing the weight-two
series of every index of nebentypus `χ` contains their span. -/
theorem weightTwoEisensteinSubspace_le {V : Submodule ℂ (modFormCharSpace 2 χ)}
    (hV : ∀ (a : CharIndex N 2) (hχ : a.nebentypus = χ), a.weightTwoInCharSpace hχ ∈ V) :
    weightTwoEisensteinSubspace χ ≤ V := by
  rw [weightTwoEisensteinSubspace_def, Submodule.span_le]
  rintro _ ⟨⟨a, hχ⟩, rfl⟩
  exact hV a hχ

/-- The weight-two Eisenstein subspace of `M₂(N, χ)` has dimension the number of indices of
nebentypus `χ` other than `(1, 1, 1)`, that is, with nonzero weight-two series. -/
theorem finrank_weightTwoEisensteinSubspace :
    Module.finrank ℂ (weightTwoEisensteinSubspace χ) =
      Nat.card {a : CharIndex N 2 // a.nebentypus = χ ∧ a.weightTwoForm ≠ 0} := by
  have hli := CharIndex.linearIndependent_weightTwoInCharSpace χ
  have hspan : weightTwoEisensteinSubspace χ = Submodule.span ℂ (Set.range
      fun a : {a : CharIndex N 2 // a.nebentypus = χ ∧ a.weightTwoForm ≠ 0} ↦
        a.1.weightTwoInCharSpace a.2.1) := by
    refine le_antisymm (weightTwoEisensteinSubspace_le χ fun a hχ ↦ ?_)
      (Submodule.span_mono ?_)
    · by_cases ha : a.weightTwoForm = 0
      · rw [show a.weightTwoInCharSpace hχ = 0 from Subtype.ext ha]
        exact zero_mem _
      · exact Submodule.subset_span ⟨⟨a, hχ, ha⟩, rfl⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨a.1, a.2.1⟩, rfl⟩
  rw [hspan, Module.finrank, rank_span hli, Cardinal.mk_range_eq _ hli.injective]
  rfl

end TauCeti
