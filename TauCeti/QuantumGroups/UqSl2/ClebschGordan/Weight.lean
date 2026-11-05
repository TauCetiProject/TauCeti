/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Projection
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Hom

/-!
# Admissible Clebsch–Gordan triples and weight-indexed binary intertwiners

Binary Clebsch–Gordan channels on `L_a^ε ⊗ L_b^δ` are indexed in `ClebschGordan.Basic` and
`ClebschGordan.Projection` by lowering steps `j : Fin (min a b + 1)` with weight `c = a + b - 2j`.
To state recoupling and pentagon identities across iterated tensor products without dependent `Fin`
arithmetic, this file introduces `IsClebschGordanTriple a b c` and packages the normalized
inclusions and projections into weight-indexed `UqSl2 q`-linear maps extended by zero outside
admissible triples.

## Main definitions

* `TauCeti.UqSl2.IsClebschGordanTriple`: admissibility predicate for binary summand weights.
* `TauCeti.UqSl2.clebschGordanTripleEquiv`: equivalence with lowering steps `Fin (min a b + 1)`.
* `TauCeti.UqSl2.clebschGordanWeightInclusion`, `TauCeti.UqSl2.clebschGordanWeightProjection`:
  weight-indexed binary Clebsch–Gordan inclusions and projections, zero outside admissible triples.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter VII.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

/-- A natural number `c` is an admissible Clebsch–Gordan summand highest weight for `L_a^ε ⊗ L_b^δ`
if `a`, `b`, `c` satisfy the triangle inequalities and `a + b - c` is even. -/
def IsClebschGordanTriple (a b c : ℕ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c)

/-- Unfolded characterization of `IsClebschGordanTriple`. -/
theorem isClebschGordanTriple_iff (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c) := Iff.rfl

instance (a b c : ℕ) : Decidable (IsClebschGordanTriple a b c) :=
  inferInstanceAs (Decidable (a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c)))

/-- First triangle inequality `a ≤ b + c` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add_right {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    a ≤ b + c := h.1

/-- Second triangle inequality `b ≤ a + c` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add_left {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    b ≤ a + c := h.2.1

/-- Upper bound `c ≤ a + b` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    c ≤ a + b := h.2.2.1

/-- Parity condition `Even (a + b - c)` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.even_add_sub {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    Even (a + b - c) := h.2.2.2

/-- Filtering `Finset.range (a + b + 1)` by `IsClebschGordanTriple a b u ∧ p u` retains every
natural number satisfying `IsClebschGordanTriple a b u ∧ p u`. -/
theorem mem_filter_range_isClebschGordanTriple_and {a b u : ℕ} {p : ℕ → Prop} [DecidablePred p] :
    u ∈ (Finset.range (a + b + 1)).filter (fun u => IsClebschGordanTriple a b u ∧ p u) ↔
      IsClebschGordanTriple a b u ∧ p u := by
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

/-- Every lowering step `j : Fin (min a b + 1)` yields an admissible weight `a + b - 2 * j`. -/
theorem isClebschGordanTriple_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    IsClebschGordanTriple a b (a + b - 2 * (j : ℕ)) := by
  have := j.isLt; exact ⟨by omega, by omega, by omega, ⟨j, by omega⟩⟩

/-- Equivalence between admissible Clebsch–Gordan summand weights `c` in `L_a^ε ⊗ L_b^δ` and
lowering-step indices `j : Fin (min a b + 1)` via `c = a + b - 2j` and `j = (a + b - c) / 2`. -/
def clebschGordanTripleEquiv (a b : ℕ) :
    { c : ℕ // IsClebschGordanTriple a b c } ≃ Fin (min a b + 1) where
  toFun c := ⟨(a + b - c.1) / 2, by obtain ⟨_, _, _, _, _⟩ := c.2; omega⟩
  invFun j := ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩
  left_inv c := by obtain ⟨_, _, _, _, _⟩ := c.2; ext; dsimp only; omega
  right_inv j := by have := j.isLt; ext; dsimp only; omega

/-- Recovery of `c = a + b - 2 * j` from `j = clebschGordanTripleEquiv a b ⟨c, h⟩`. -/
theorem IsClebschGordanTriple.eq_sub_two_mul_clebschGordanTripleEquiv {a b c : ℕ}
    (h : IsClebschGordanTriple a b c) :
    c = a + b - 2 * (clebschGordanTripleEquiv a b ⟨c, h⟩ : ℕ) :=
  (congrArg Subtype.val ((clebschGordanTripleEquiv a b).symm_apply_apply ⟨c, h⟩)).symm

/-- `clebschGordanTripleEquiv` sends `a + b - 2 * j` back to `j`. -/
@[simp] theorem clebschGordanTripleEquiv_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    clebschGordanTripleEquiv a b ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩ = j :=
  (clebschGordanTripleEquiv a b).apply_symm_apply j

/-- `IsClebschGordanTriple a b c` holds iff `c = a + b - 2 * j` for some `j : Fin (min a b + 1)`. -/
theorem isClebschGordanTriple_iff_exists_fin (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ ∃ j : Fin (min a b + 1), c = a + b - 2 * (j : ℕ) :=
  ⟨fun h => ⟨clebschGordanTripleEquiv a b ⟨c, h⟩, h.eq_sub_two_mul_clebschGordanTripleEquiv⟩,
    fun ⟨j, hj⟩ => hj ▸ isClebschGordanTriple_sub_two_mul j⟩

/-- Summing a function vanishing outside admissible Clebsch–Gordan triples over
`Finset.range (a + b + 1)` reindexes to lowering steps `j : Fin (min a b + 1)`. -/
theorem sum_range_eq_sum_fin_sub_two_mul {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (f : ℕ → M) (hf : ∀ c, ¬ IsClebschGordanTriple a b c → f c = 0) :
    ∑ c ∈ Finset.range (a + b + 1), f c = ∑ j : Fin (min a b + 1), f (a + b - 2 * (j : ℕ)) := by
  rw [← Finset.sum_filter_of_ne (p := IsClebschGordanTriple a b) fun c _ => Not.imp_symm (hf c)]
  refine (Finset.sum_nbij (fun j : Fin (min a b + 1) => a + b - 2 * (j : ℕ))
    (fun j _ => by
      have := j.isLt; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, isClebschGordanTriple_sub_two_mul j⟩)
    (fun j₁ _ j₂ _ h => by have := j₁.isLt; have := j₂.isLt; dsimp only at h; ext; omega)
    (fun c hc => ?_) fun _ _ => rfl).symm
  simp only [Finset.mem_coe, Finset.mem_filter] at hc
  exact ⟨clebschGordanTripleEquiv a b ⟨c, hc.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _),
    hc.2.eq_sub_two_mul_clebschGordanTripleEquiv.symm⟩

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Weight-indexed binary Clebsch–Gordan inclusion `L_c^(εδ) →ₗ[UqSl2 q] L_a^ε ⊗ L_b^δ`, equal to
the normalized inclusion when `IsClebschGordanTriple a b c` and `0` otherwise. -/
def clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c : ℕ) :
    LadderModule q c (ε * δ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) :=
  if h : IsClebschGordanTriple a b c then
    (clebschGordanInclusion hq (clebschGordanTripleEquiv a b ⟨c, h⟩)).comp
      (LadderModule.congr h.eq_sub_two_mul_clebschGordanTripleEquiv rfl).toLinearMap
  else 0

/-- Weight-indexed binary Clebsch–Gordan projection `L_a^ε ⊗ L_b^δ →ₗ[UqSl2 q] L_c^(εδ)`, equal to
the normalized projection when `IsClebschGordanTriple a b c` and `0` otherwise. -/
def clebschGordanWeightProjection (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c : ℕ) :
    Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) →ₗ[UqSl2 q]
      LadderModule q c (ε * δ) :=
  if h : IsClebschGordanTriple a b c then
    (LadderModule.congr h.eq_sub_two_mul_clebschGordanTripleEquiv.symm rfl).toLinearMap.comp
      (clebschGordanProjection hq (clebschGordanTripleEquiv a b ⟨c, h⟩))
  else 0

/-- `clebschGordanWeightInclusion` vanishes outside admissible Clebsch–Gordan triples. -/
theorem clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple
    (hq : IsGenericQuantumParameter q) {a b c : ℕ} (ε δ : ℤˣ) (h : ¬ IsClebschGordanTriple a b c) :
    clebschGordanWeightInclusion hq a ε b δ c = 0 := by simp [clebschGordanWeightInclusion, h]

/-- `clebschGordanWeightProjection` vanishes outside admissible Clebsch–Gordan triples. -/
theorem clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple
    (hq : IsGenericQuantumParameter q) {a b c : ℕ} (ε δ : ℤˣ) (h : ¬ IsClebschGordanTriple a b c) :
    clebschGordanWeightProjection hq a ε b δ c = 0 := by simp [clebschGordanWeightProjection, h]

/-- At `c = a + b - 2 * j`, `clebschGordanWeightInclusion` agrees with `clebschGordanInclusion`. -/
@[simp] theorem clebschGordanWeightInclusion_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightInclusion hq a ε b δ (a + b - 2 * (j : ℕ)) = clebschGordanInclusion hq j :=
  LadderModule.hom_ext hq <| by
    simp [clebschGordanWeightInclusion, isClebschGordanTriple_sub_two_mul j]

/-- `clebschGordanWeightProjection` is a left inverse to `clebschGordanWeightInclusion` on any
admissible triple. -/
theorem clebschGordanWeightProjection_comp_inclusion_self (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : IsClebschGordanTriple a b c) :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [clebschGordanWeightProjection, clebschGordanWeightInclusion, dite_eq_left h,
    LinearMap.comp_apply, LinearEquiv.coe_coe, clebschGordanProjection_inclusion_self,
    LinearMap.id_apply]
  rw [← LinearEquiv.trans_apply, congr_trans, congr_refl, LinearEquiv.refl_apply]

/-- Weight-indexed Clebsch–Gordan inclusions and projections at distinct weights are orthogonal. -/
theorem clebschGordanWeightProjection_comp_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {a b c c' : ℕ} (ε δ : ℤˣ) (hne : c ≠ c') :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c') = 0 :=
  hom_eq_zero_of_weight_ne hq hne.symm _

/-- Combined orthogonality formula for weight-indexed binary Clebsch–Gordan maps. -/
theorem clebschGordanWeightProjection_comp_inclusion (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c c' : ℕ) :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c') =
      if h : c = c' ∧ IsClebschGordanTriple a b c then
        (LadderModule.congr h.1.symm rfl).toLinearMap
      else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hc⟩
    simpa using clebschGordanWeightProjection_comp_inclusion_self hq ε δ hc
  · by_cases hcc : c = c'
    · subst hcc
      simp [clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple hq ε δ
        fun hc => h ⟨rfl, hc⟩]
    · exact clebschGordanWeightProjection_comp_inclusion_of_ne hq ε δ hcc

/-- At `c = a + b - 2 * j`, `clebschGordanWeightProjection` agrees with
`clebschGordanProjection`. -/
@[simp] theorem clebschGordanWeightProjection_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightProjection hq a ε b δ (a + b - 2 * (j : ℕ)) =
      clebschGordanProjection hq j := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← sum_clebschGordanInclusion_projection hq x]
  conv_rhs => rw [← sum_clebschGordanInclusion_projection hq x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · simpa using congrArg (· (clebschGordanProjection hq i x))
      (clebschGordanWeightProjection_comp_inclusion_self hq ε δ
        (isClebschGordanTriple_sub_two_mul i))
  · have hne : a + b - 2 * (j : ℕ) ≠ a + b - 2 * (i : ℕ) := by
      have := i.isLt; have := j.isLt; exact fun h => hij (Fin.ext (by omega))
    simpa [clebschGordanProjection_inclusion_of_ne hq (Ne.symm hij)] using
      congrArg (· (clebschGordanProjection hq i x))
        (clebschGordanWeightProjection_comp_inclusion_of_ne (a := a) (b := b) hq ε δ hne)

/-- Weight-indexed Clebsch–Gordan inclusions and projections resolve the identity on
`L_a^ε ⊗ L_b^δ` over `Finset.range (a + b + 1)`. -/
theorem sum_clebschGordanWeightInclusion_comp_projection (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) :
    ∑ c ∈ Finset.range (a + b + 1),
      (clebschGordanWeightInclusion hq a ε b δ c).comp
        (clebschGordanWeightProjection hq a ε b δ c) = LinearMap.id := by
  rw [sum_range_eq_sum_fin_sub_two_mul a b _ fun c htr => by
    simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ε δ htr]]
  simpa using sum_clebschGordanInclusion_comp_projection (m := a) (n := b) (ε := ε) (δ := δ) hq

/-- Transporting the summand weight of `clebschGordanWeightInclusion` along `c = c'`. -/
theorem clebschGordanWeightInclusion_congr_right (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) {c c' : ℕ} (hc : c = c') :
    clebschGordanWeightInclusion hq a ε b δ c' =
      (clebschGordanWeightInclusion hq a ε b δ c).comp
        (LadderModule.congr hc.symm rfl).toLinearMap := by subst hc; simp

/-- Transporting the summand weight of `clebschGordanWeightProjection` along `c = c'`. -/
theorem clebschGordanWeightProjection_congr_right (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) {c c' : ℕ} (hc : c = c') :
    clebschGordanWeightProjection hq a ε b δ c' =
      (LadderModule.congr hc rfl).toLinearMap.comp
        (clebschGordanWeightProjection hq a ε b δ c) := by subst hc; simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightInclusion`. -/
theorem tensorMap_congr_comp_clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap).comp
      (clebschGordanWeightInclusion hq a ε₁ b δ₁ c) =
    (clebschGordanWeightInclusion hq a' ε₂ b' δ₂ c).comp
      (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap := by
  subst ha hb hε hδ; simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightProjection`. -/
theorem clebschGordanWeightProjection_comp_tensorMap_congr (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (clebschGordanWeightProjection hq a' ε₂ b' δ₂ c).comp
      (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap) =
    (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap.comp
      (clebschGordanWeightProjection hq a ε₁ b δ₁ c) := by
  subst ha hb hε hδ; simp

end TauCeti.UqSl2
