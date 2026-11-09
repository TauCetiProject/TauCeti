/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Count
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Independence
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The weight-one Eisenstein subspace with fixed nebentypus

In weight one the Eisenstein series of an index `(ψ, φ, t)` of
`TauCeti.EisensteinSeries.CharIndex N 1` (primitive characters `ψ` modulo `u` and `φ` modulo `v`
with `ψ(-1) φ(-1) = -1`, and `t u v ∣ N`) is the normalized raised series `E₁^{ψ,φ,t}`
(`TauCeti.EisensteinSeries.normalizedCharE1MFRaise`), whose positive Fourier coefficients are
`σ₀^{ψ,φ}(n / t)` at the multiples `n` of `t`. Unlike in weight `k ≥ 2`, these series are not
linearly independent: the divisor sums `σ₀^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n / d) φ(d)` are symmetric in
`ψ` and `φ`, so exchanging the two characters (`TauCeti.EisensteinSeries.CharIndex.swap`) gives
the same series (Diamond–Shurman §4.8). This file proves that this is the only linear relation
among them:

* two indices have the same series exactly when they are equal or exchanged
  (`TauCeti.EisensteinSeries.CharIndex.weightOneForm_eq_weightOneForm_iff`), and
* the series of a set of indices containing no index together with its exchange are linearly
  independent (`TauCeti.EisensteinSeries.CharIndex.linearIndepOn_weightOneForm`).

In odd weight no index is its own exchange, since `ψ` and `φ` have opposite parities. Hence the
span `TauCeti.weightOneEisensteinSubspace χ` in `M₁(N, χ)` of the series of nebentypus `χ` has
dimension half the number of indices of nebentypus `χ`, and the span of all the series in
`M₁(Γ₁(N))` has dimension half the number of cusps of `Γ₁(N)` away from the levels `1`, `2` and
`4`. That is the largest dimension a complement of the cusp forms can have
(`TauCeti.ModularForm.two_mul_finrank_le_card_cuspOrbit_of_disjoint`).

The independence reads off the positive Fourier coefficients, as in weight `k ≥ 2`, through the
independence of the sequences `σ₀^{ψ,φ}` over distinct unordered pairs of characters
(`TauCeti.EisensteinSeries.CharIndex.linearIndepOn_twistedDivisorSum_zero`).

## Main definitions

* `TauCeti.EisensteinSeries.CharIndex.weightOneForm`: the weight-one Eisenstein series of an
  index.
* `TauCeti.weightOneEisensteinSubspace`: the span in `M₁(N, χ)` of the series of nebentypus `χ`.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.weightOneForm_mem_modFormCharSpace`: the series of an index
  lies in the character space of its nebentypus.
* `TauCeti.EisensteinSeries.CharIndex.qExpansion_weightOneForm_coeff`: its positive Fourier
  coefficients.
* `TauCeti.EisensteinSeries.CharIndex.weightOneForm_swap`: exchanging the characters does not
  change the series.
* `TauCeti.EisensteinSeries.CharIndex.linearIndepOn_weightOneForm`: the series of a set of indices
  free of exchanged pairs are linearly independent.
* `TauCeti.EisensteinSeries.CharIndex.weightOneForm_eq_weightOneForm_iff`: two indices have the
  same series exactly when they are equal or exchanged.
* `TauCeti.two_mul_finrank_weightOneEisensteinSubspace`: twice the dimension of the weight-one
  Eisenstein subspace of `M₁(N, χ)` is the number of indices of nebentypus `χ`.
* `TauCeti.EisensteinSeries.two_mul_finrank_span_range_weightOneForm_eq_card_cuspOrbit_Gamma1`:
  twice the dimension of the span of all weight-one series is the number of cusps of `Γ₁(N)`, for
  `N ∉ {1, 2, 4}`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries.CharIndex

variable {N : ℕ} [NeZero N] (a : CharIndex N 1)

/-- The weight-one Eisenstein series of an index `(ψ, φ, t)` (Diamond–Shurman §4.8): the
normalized raised series `E₁^{ψ,φ,t}`. -/
def weightOneForm : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 :=
  normalizedCharE1MFRaise a.psi a.phi a.t a.level_dvd

/-- The defining expression for the weight-one series of an index. -/
theorem weightOneForm_def :
    a.weightOneForm = normalizedCharE1MFRaise a.psi a.phi a.t a.level_dvd :=
  (rfl)

omit [NeZero N] in
/-- The characters of an index of weight one have opposite parities. -/
private theorem parity_one : a.psi (-1) * a.phi (-1) = -1 := by
  simpa using a.parity

/-- The weight-one series of an index belongs to the character space of its nebentypus. -/
theorem weightOneForm_mem_modFormCharSpace :
    a.weightOneForm ∈ modFormCharSpace 1 a.nebentypus := by
  rw [weightOneForm_def, nebentypus_def]
  exact normalizedCharE1MFRaise_mem_modFormCharSpace a.psi a.phi a.level_dvd

/-- The positive Fourier coefficients of the weight-one series of an index `(ψ, φ, t)` are the
divisor sums `σ₀^{ψ,φ}(n / t)` at multiples `n` of `t`, and zero at the other positive indices. -/
theorem qExpansion_weightOneForm_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 a.weightOneForm).coeff n =
      if a.t ∣ n then DirichletCharacter.twistedDivisorSum 0 a.psi a.phi (n / a.t) else 0 :=
  qExpansion_normalizedCharE1MFRaise_coeff a.psi a.phi a.level_dvd a.parity_one
    a.phi_primitive hn

/-- The weight-one series of an index is nonzero. -/
theorem weightOneForm_ne_zero : a.weightOneForm ≠ 0 :=
  normalizedCharE1MFRaise_ne_zero a.psi a.phi a.level_dvd a.parity_one a.phi_primitive

/-- **Character exchange in weight one**: exchanging the two characters of an index does not
change its weight-one series, `E₁^{φ,ψ,t} = E₁^{ψ,φ,t}`. -/
@[simp]
theorem weightOneForm_swap : a.swap.weightOneForm = a.weightOneForm := by
  rw [weightOneForm_def, weightOneForm_def]
  exact (normalizedCharE1MFRaise_comm a.psi a.phi a.level_dvd a.parity_one a.psi_primitive
    a.phi_primitive).symm

/-- **Linear independence of the weight-one Eisenstein series**: the series `E₁^{ψ,φ,t}` of a set
of indices containing no index together with its exchange `(φ, ψ, t)` are linearly
independent. -/
theorem linearIndepOn_weightOneForm {S : Set (CharIndex N 1)} (hS : ∀ a ∈ S, a.swap ∉ S) :
    LinearIndepOn ℂ weightOneForm S := by
  refine LinearIndepOn.of_comp (LinearMap.pi fun n : {n : ℕ // n ≠ 0} ↦
    (PowerSeries.coeff (n : ℕ)).comp (ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods_Gamma1_map N) 1)) ?_
  convert linearIndepOn_twistedDivisorSum_zero fun a ha has ↦ (hS a ha has).elim using 1
  ext a n
  simp [qExpansion_weightOneForm_coeff _ n.2]

/-- **The linear relations among the weight-one Eisenstein series**: two indices have the same
weight-one series exactly when they are equal or exchanged. -/
theorem weightOneForm_eq_weightOneForm_iff {a b : CharIndex N 1} :
    a.weightOneForm = b.weightOneForm ↔ b = a ∨ b = a.swap := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra! hb
    have hS : ∀ c ∈ ({a, b} : Set (CharIndex N 1)), c.swap ∉ ({a, b} : Set (CharIndex N 1)) := by
      have ha := a.swap_ne_self odd_one
      have hb' := b.swap_ne_self odd_one
      rintro c (rfl | rfl) (h' | h')
      · exact ha h'
      · exact hb.2 h'.symm
      · exact hb.2 (by rw [← h', swap_swap])
      · exact hb' h'
    exact hb.1 ((linearIndepOn_weightOneForm hS).injOn (by simp) (by simp) h).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (weightOneForm_swap a).symm

/-- The weight-one series of a set of indices closed under exchange span a space of dimension
half the number of indices. -/
private theorem two_mul_finrank_span_image_weightOneForm {T : Set (CharIndex N 1)}
    (hT : ∀ a ∈ T, a.swap ∈ T) :
    2 * Module.finrank ℂ (Submodule.span ℂ (weightOneForm '' T)) = Nat.card T := by
  classical
  -- A set `S` of representatives: the indices listed before their exchange.
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (CharIndex N 1)
  let S : Set (CharIndex N 1) := {a | a ∈ T ∧ e a < e a.swap}
  have hS : ∀ a ∈ S, a.swap ∉ S := fun a ha has ↦
    lt_asymm ha.2 (by simpa using has.2)
  have hrep (a : CharIndex N 1) (ha : a ∈ T) : a ∈ S ∨ a.swap ∈ S := by
    rcases lt_or_gt_of_ne (e.injective.ne (a.swap_ne_self odd_one).symm) with h | h
    · exact .inl ⟨ha, h⟩
    · exact .inr ⟨hT a ha, by simpa using h⟩
  have himage : weightOneForm '' T = weightOneForm '' S := by
    refine le_antisymm (fun f ⟨a, ha, hf⟩ ↦ ?_) (Set.image_mono fun a ha ↦ ha.1)
    rcases hrep a ha with h | h
    · exact ⟨a, h, hf⟩
    · exact ⟨a.swap, h, (weightOneForm_swap a).trans hf⟩
  have hcard : T = S ∪ swap '' S := by
    refine le_antisymm (fun a ha ↦ ?_) (Set.union_subset (fun a ha ↦ ha.1) ?_)
    · rcases hrep a ha with h | h
      · exact .inl h
      · exact .inr ⟨a.swap, h, swap_swap a⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hT a ha.1
  have hdisj : Disjoint S (swap '' S) := by
    refine Set.disjoint_left.mpr fun a ha ⟨b, hb, hba⟩ ↦ hS b hb ?_
    rwa [hba]
  have := Fintype.ofFinite S
  -- The span has dimension `#S`, and `T` has `2 * #S` elements.
  have hdim : Module.finrank ℂ (Submodule.span ℂ (weightOneForm '' T)) = Nat.card S := by
    rw [himage, Set.image_eq_range, finrank_span_eq_card (linearIndepOn_weightOneForm hS),
      Nat.card_eq_fintype_card]
  have hT2 : Nat.card T = 2 * Nat.card S := by
    rw [hcard, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj,
      Set.ncard_image_of_injective _ swap_involutive.injective, ← Nat.card_coe_set_eq, two_mul]
  omega

variable {χ : (ZMod N)ˣ →* ℂˣ}

/-- The weight-one series of an index, as an element of a character space whose character agrees
with the nebentypus of the index. -/
def weightOneInCharSpace (hχ : a.nebentypus = χ) : modFormCharSpace 1 χ :=
  ⟨a.weightOneForm, hχ ▸ a.weightOneForm_mem_modFormCharSpace⟩

/-- Coercing `weightOneInCharSpace` forgets only the proof of character-space membership. -/
@[simp]
theorem coe_weightOneInCharSpace (hχ : a.nebentypus = χ) :
    (a.weightOneInCharSpace hχ : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1) = a.weightOneForm :=
  (rfl)

end CharIndex

/-- **The weight-one Eisenstein series span a space of half the number of indices**: twice the
dimension of the span of all the weight-one series in `M₁(Γ₁(N))` is the number of indices. -/
theorem two_mul_finrank_span_range_weightOneForm {N : ℕ} [NeZero N] :
    2 * Module.finrank ℂ (Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))) =
      Nat.card (CharIndex N 1) := by
  rw [← Set.image_univ, CharIndex.two_mul_finrank_span_image_weightOneForm fun _ _ ↦ trivial,
    Nat.card_univ]

/-- Away from the levels `1`, `2` and `4`, twice the dimension of the span of the weight-one
Eisenstein series in `M₁(Γ₁(N))` is the number of cusps of `Γ₁(N)`, the largest value permitted
for a complement of the cusp forms
(`TauCeti.ModularForm.two_mul_finrank_le_card_cuspOrbit_of_disjoint`). -/
theorem two_mul_finrank_span_range_weightOneForm_eq_card_cuspOrbit_Gamma1 {N : ℕ} [NeZero N]
    (hN : 2 < N) (hN4 : N ≠ 4) :
    2 * Module.finrank ℂ (Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N)))) =
      Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  rw [two_mul_finrank_span_range_weightOneForm, CharIndex.card_eq_card_cuspOrbit_Gamma1 hN hN4]

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)

/-- The **weight-one Eisenstein subspace** of `M₁(N, χ)`: the span of the weight-one Eisenstein
series `E₁^{ψ,φ,t}` of the indices of nebentypus `χ`. -/
def weightOneEisensteinSubspace : Submodule ℂ (modFormCharSpace 1 χ) :=
  Submodule.span ℂ (Set.range fun a : {a : CharIndex N 1 // a.nebentypus = χ} ↦
    a.1.weightOneInCharSpace a.2)

/-- The defining span of the weight-one Eisenstein subspace. -/
theorem weightOneEisensteinSubspace_def :
    weightOneEisensteinSubspace χ =
      Submodule.span ℂ (Set.range fun a : {a : CharIndex N 1 // a.nebentypus = χ} ↦
        a.1.weightOneInCharSpace a.2) :=
  (rfl)

/-- The weight-one series of an index of nebentypus `χ` belongs to the weight-one Eisenstein
subspace. -/
theorem mem_weightOneEisensteinSubspace (a : CharIndex N 1) (hχ : a.nebentypus = χ) :
    a.weightOneInCharSpace hχ ∈ weightOneEisensteinSubspace χ :=
  Submodule.subset_span ⟨⟨a, hχ⟩, rfl⟩

/-- A form belongs to the weight-one Eisenstein subspace exactly when it is a finite linear
combination of the weight-one series of the indices of nebentypus `χ`. -/
theorem mem_weightOneEisensteinSubspace_iff (f : modFormCharSpace 1 χ) :
    f ∈ weightOneEisensteinSubspace χ ↔
      ∃ c : {a : CharIndex N 1 // a.nebentypus = χ} →₀ ℂ,
        c.sum (fun a z ↦ z • a.1.weightOneInCharSpace a.2) = f :=
  Finsupp.mem_span_range_iff_exists_finsupp

/-- Elimination rule for the weight-one Eisenstein subspace: a subspace containing the weight-one
series of every index of nebentypus `χ` contains their span. -/
theorem weightOneEisensteinSubspace_le {V : Submodule ℂ (modFormCharSpace 1 χ)}
    (hV : ∀ (a : CharIndex N 1) (hχ : a.nebentypus = χ), a.weightOneInCharSpace hχ ∈ V) :
    weightOneEisensteinSubspace χ ≤ V := by
  rw [weightOneEisensteinSubspace_def, Submodule.span_le]
  rintro _ ⟨⟨a, hχ⟩, rfl⟩
  exact hV a hχ

/-- **The dimension of the weight-one Eisenstein subspace**: twice the dimension of the weight-one
Eisenstein subspace of `M₁(N, χ)` is the number of indices of nebentypus `χ`, each series being
attached to exactly two indices, `(ψ, φ, t)` and `(φ, ψ, t)`. -/
theorem two_mul_finrank_weightOneEisensteinSubspace :
    2 * Module.finrank ℂ (weightOneEisensteinSubspace χ) =
      Nat.card {a : CharIndex N 1 // a.nebentypus = χ} := by
  have hmap : (weightOneEisensteinSubspace χ).map (modFormCharSpace 1 χ).subtype =
      Submodule.span ℂ (CharIndex.weightOneForm '' {a | a.nebentypus = χ}) := by
    rw [weightOneEisensteinSubspace_def, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext f
    simp [Set.mem_image]
  rw [(Submodule.equivMapOfInjective _ (modFormCharSpace 1 χ).injective_subtype _).finrank_eq,
    hmap, CharIndex.two_mul_finrank_span_image_weightOneForm fun a ha ↦ by
      simpa using ha, Set.coe_ofPred]

end TauCeti
