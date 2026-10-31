/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNSmul
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.TwoElementary
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram

/-!
# Even two-elementary lattices

An even nondegenerate integral lattice `L` is *`2`-elementary* when its discriminant group
`A_L = Lᵛ/L` is `(ℤ/2)^a`. Nikulin attaches to it the invariants `(δ; t₊, t₋, a)`, where
`(t₊, t₋)` is the signature and `δ = 0` exactly when the half-norm discriminant form `q_L` takes
values in `½ℤ/ℤ`. His Theorem 3.6.2 says that an even `2`-elementary lattice with invariants
`(δ; t₊, t₋, a)` exists exactly when seven arithmetic conditions hold:

1. `a ≤ t₊ + t₋`;
2. `t₊ + t₋ + a ≡ 0 (mod 2)`;
3. `t₊ − t₋ ≡ 0 (mod 4)` when `δ = 0`;
4. `δ = 0` and `t₊ − t₋ ≡ 0 (mod 8)` when `a = 0`;
5. `t₊ − t₋ ≡ ±1 (mod 8)` when `a = 1`;
6. `δ = 0` when `a = 2` and `t₊ − t₋ ≡ 4 (mod 8)`;
7. `t₊ − t₋ ≡ 0 (mod 8)` when `δ = 0` and `a = t₊ + t₋`.

This file records the conditions as the structure `TwoElementaryAdmissible`, with one field per
clause, and proves that they are necessary. Conditions 2 to 6 follow from Milgram's theorem
`sign q_L ≡ t₊ − t₋ (mod 8)` together with the decomposition of a nondegenerate `2`-elementary
finite quadratic module into the generators `q_θ^{(2)}(2)`, `u^{(2)}(2)` and `v^{(2)}(2)`.
Conditions 1 and 7 come from the lattice: since `2Lᵛ ⊆ L`, the order `2^a` of `A_L` divides the
index `2^{t₊ + t₋}` of `2Lᵛ` in `Lᵛ`, and if they are equal then `L = 2Lᵛ`, so that `Lᵛ` with the
doubled form is an integral unimodular lattice of the same signature, even when `δ = 0`.

The boundary clauses 4 to 7 cannot be dropped: the tuples `(0; 4, 0, 0)`, `(1; 3, 0, 1)`,
`(1; 4, 0, 2)` and `(0; 4, 0, 4)` satisfy every condition before clause 4, 5, 6 and 7
respectively, and `TauCeti.IntegralLattice.not_twoElementaryAdmissible_boundary_witnesses`
records that none of them is admissible.

## Main definitions

* `TauCeti.IntegralLattice.TwoElementaryAdmissible`: Nikulin's seven conditions on
  `(δ; t₊, t₋, a)`.
* `TauCeti.IntegralLattice.TwoElementaryLatticeWithInvariants`: an even `2`-elementary lattice
  with invariants `(δ; t₊, t₋, a)` exists.

## Main results

* `TauCeti.IntegralLattice.natCard_discriminantGroup_dvd_two_pow_finrank` and
  `TauCeti.IntegralLattice.exists_mem_dualCarrier_eq_two_nsmul`: a discriminant group killed by `2`
  has order dividing `2^n`, `n` the rank, and if the order is `2^n` then `L = 2Lᵛ`.
* `TauCeti.IntegralLattice.twoElementaryAdmissible_sigPos_sigNeg`: the invariants of an even
  `2`-elementary lattice satisfy Nikulin's conditions.
* `TauCeti.IntegralLattice.TwoElementaryLatticeWithInvariants.twoElementaryAdmissible`: the
  necessity half of Nikulin's Theorem 3.6.2.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 3.6.2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## Nikulin's conditions -/

/-- **Nikulin's seven conditions** on the invariants `(δ; t₊, t₋, a)` of an even `2`-elementary
lattice. Conditions 4 to 7 are boundary clauses at `a = 0`, `a = 1`, `a = 2` and `a = t₊ + t₋`. -/
structure TwoElementaryAdmissible (δ : ZMod 2) (tp tm a : ℕ) : Prop where
  /-- (1) `a ≤ t₊ + t₋`. -/
  le_rank : a ≤ tp + tm
  /-- (2) `t₊ + t₋ + a ≡ 0 (mod 2)`. -/
  parity : ((tp + tm + a : ℕ) : ZMod 2) = 0
  /-- (3) `t₊ − t₋ ≡ 0 (mod 4)` when `δ = 0`. -/
  four_of_delta_zero : δ = 0 → (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 4) = 0
  /-- (4) `δ = 0` and `t₊ − t₋ ≡ 0 (mod 8)` when `a = 0`. -/
  unimodular_of_a_zero : a = 0 → δ = 0 ∧ (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 8) = 0
  /-- (5) `t₊ − t₋ ≡ ±1 (mod 8)` when `a = 1`. -/
  pm_one_of_a_one : a = 1 →
    (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 8) = 1 ∨ (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 8) = -1
  /-- (6) `δ = 0` when `a = 2` and `t₊ − t₋ ≡ 4 (mod 8)`. -/
  delta_zero_of_a_two : a = 2 → (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 8) = 4 → δ = 0
  /-- (7) `t₊ − t₋ ≡ 0 (mod 8)` when `δ = 0` and `a = t₊ + t₋`. -/
  eight_of_a_eq_rank : δ = 0 → a = tp + tm → (((tp : ℤ) - (tm : ℤ) : ℤ) : ZMod 8) = 0

/-- **The four boundary witnesses are not admissible**: `(0; 4, 0, 0)`, `(1; 3, 0, 1)`,
`(1; 4, 0, 2)` and `(0; 4, 0, 4)` fail conditions 4, 5, 6 and 7 respectively. -/
theorem not_twoElementaryAdmissible_boundary_witnesses :
    ¬ TwoElementaryAdmissible 0 4 0 0 ∧ ¬ TwoElementaryAdmissible 1 3 0 1 ∧
      ¬ TwoElementaryAdmissible 1 4 0 2 ∧ ¬ TwoElementaryAdmissible 0 4 0 4 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact absurd (h.unimodular_of_a_zero rfl).2 (by decide)
  · rcases h.pm_one_of_a_one rfl with h' | h' <;> exact absurd h' (by decide)
  · exact absurd (h.delta_zero_of_a_two rfl (by decide)) (by decide)
  · exact absurd (h.eight_of_a_eq_rank rfl rfl) (by decide)

/-! ## Discriminant groups killed by `2` -/

section TwoTorsion

variable (L : IntegralLattice V) [L.IsNondegenerate]

omit [L.IsNondegenerate] in
/-- A dual vector whose discriminant class is killed by `2` has its double in the lattice. -/
private theorem two_nsmul_mem_carrier (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0)
    (y : L.dualCarrier) : 2 • (y : V) ∈ L.carrier := by
  have h := h2 (L.carrierInDual.mkQ y)
  rwa [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_carrierInDual_iff,
    Submodule.coe_smul_of_tower] at h

omit [L.IsNondegenerate] in
/-- When `2A_L = 0`, the image `2Lᵛ` of doubling lies in `L`, viewed inside `Lᵛ`. -/
private theorem range_nsmul_two_le_carrierInDual (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0) :
    (nsmulAddMonoidHom (α := L.dualCarrier) 2).range ≤ L.carrierInDual.toAddSubgroup := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_toAddSubgroup, mem_carrierInDual_iff, nsmulAddMonoidHom_apply,
    Submodule.coe_smul_of_tower]
  exact L.two_nsmul_mem_carrier h2 y

omit [L.IsNondegenerate] in
/-- The index of `L` in `Lᵛ` is the order of the discriminant group. -/
private theorem index_carrierInDual :
    L.carrierInDual.toAddSubgroup.index = Nat.card L.DiscriminantGroup :=
  AddSubgroup.index_eq_card _

/-- The index of `2Lᵛ` in `Lᵛ` is `2^n`, `n` the rank. -/
private theorem index_range_nsmul_two :
    (nsmulAddMonoidHom (α := L.dualCarrier) 2).range.index = 2 ^ finrank ℚ V := by
  rw [AddSubgroup.index_range_nsmul, finrank_dualCarrier]

/-- **A discriminant group killed by `2` has order dividing `2^n`**, `n` the rank: it is a
quotient of `Lᵛ/2Lᵛ ≅ (ℤ/2)^n`. -/
theorem natCard_discriminantGroup_dvd_two_pow_finrank
    (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0) :
    Nat.card L.DiscriminantGroup ∣ 2 ^ finrank ℚ V := by
  rw [← L.index_carrierInDual, ← L.index_range_nsmul_two]
  exact AddSubgroup.index_dvd_of_le (L.range_nsmul_two_le_carrierInDual h2)

/-- **If the discriminant group is killed by `2` and has order `2^n`, `n` the rank, then
`L = 2Lᵛ`**: every lattice vector is twice a dual vector. -/
theorem exists_mem_dualCarrier_eq_two_nsmul (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0)
    (hcard : Nat.card L.DiscriminantGroup = 2 ^ finrank ℚ V) {x : V} (hx : x ∈ L.carrier) :
    ∃ y ∈ L.dualCarrier, x = 2 • y := by
  have hle := L.range_nsmul_two_le_carrierInDual h2
  have hrel := AddSubgroup.relIndex_mul_index hle
  rw [L.index_carrierInDual, hcard, ← L.index_range_nsmul_two] at hrel
  have hK : L.carrierInDual.toAddSubgroup ≤ (nsmulAddMonoidHom (α := L.dualCarrier) 2).range :=
    AddSubgroup.relIndex_eq_one.mp
      (Nat.eq_of_mul_eq_mul_right (by rw [L.index_range_nsmul_two]; positivity)
        (hrel.trans (one_mul _).symm))
  obtain ⟨y, hy⟩ := hK ((Submodule.mem_toAddSubgroup _).mpr
    ((L.mem_carrierInDual_iff ⟨x, L.le_dualCarrier hx⟩).mpr hx))
  have hy' := congrArg Subtype.val hy
  rw [nsmulAddMonoidHom_apply, Submodule.coe_smul_of_tower] at hy'
  exact ⟨y, y.2, hy'.symm⟩

end TwoTorsion

/-! ## Necessity of Nikulin's conditions -/

section Necessity

variable (L : IntegralLattice V) [L.IsNondegenerate] (hL : L.IsEven)

/-- The rescaled dual `Lᵛ(2)`: the dual carrier with the doubled form, an integral lattice when
`2A_L = 0`. -/
private noncomputable def dualTwo (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0) :
    IntegralLattice V :=
  ofSubmodule L.dualCarrier (((2 : ℤ) : ℚ) • L.form) (L.isSymm.smul _) fun x hx ↦ by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    -- `2B(x, y) = B(y, 2x)` with `y ∈ Lᵛ` and `2x ∈ L`.
    have h := (LinearMap.BilinForm.mem_dualSubmodule _).mp hy _
      (L.two_nsmul_mem_carrier h2 ⟨x, hx⟩)
    rw [map_nsmul, nsmul_eq_mul, L.isSymm.eq] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact_mod_cast h

/-- If `L = 2Lᵛ` and `q_L` takes values in `½ℤ/ℤ`, then `Lᵛ(2)` is an even unimodular lattice with
the signature of `L`, so `t₊ − t₋ ≡ 0 (mod 8)`. -/
private theorem eight_dvd_sigPos_sub_sigNeg_of_carrier_eq_two_nsmul
    (h2 : ∀ x : L.DiscriminantGroup, 2 • x = 0)
    (hS : ∀ x ∈ L.carrier, ∃ y ∈ L.dualCarrier, x = 2 • y)
    (hq : ∀ x : L.DiscriminantGroup,
      L.discriminantQuadraticMap hL x + L.discriminantQuadraticMap hL x = 0) :
    (8 : ℤ) ∣ L.sigPos - L.sigNeg := by
  set T := L.dualTwo h2
  have hT : T.form = ((2 : ℤ) : ℚ) • L.form := ofSubmodule_form ..
  have hcarrier : T.carrier = L.dualCarrier := ofSubmodule_carrier ..
  -- The self-pairing of a dual vector is an integer.
  have hnorm (y : L.dualCarrier) : L.form y y ∈ (1 : Submodule ℤ ℚ) := by
    have h := hq (Submodule.Quotient.mk y)
    rwa [discriminantQuadraticMap_mk, ← AddCircle.coe_add, add_halves,
      AddCircle.coe_eq_zero_iff_mem_one] at h
  have hTe : T.IsEven := by
    rw [isEven_iff_forall_norm]
    intro y
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (hnorm ⟨y, hcarrier ▸ y.2⟩)
    exact ⟨z, by rw [norm_apply, hT, LinearMap.smul_apply, LinearMap.smul_apply, ← hz]; simp⟩
  have hTu : T.IsUnimodular := by
    rw [isUnimodular_iff_dualCarrier_le]
    intro v hv
    rw [LinearMap.BilinForm.mem_dualSubmodule] at hv
    rw [hcarrier, LinearMap.BilinForm.mem_dualSubmodule]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hS x hx
    have h := hv y (hcarrier ▸ hy)
    rw [hT, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [map_nsmul, nsmul_eq_mul]
    exact_mod_cast h
  have hpos : T.sigPos = L.sigPos := by
    rw [← sigPos_smul_of_pos (by norm_num : (0 : ℤ) < 2) L]
    simp only [IntegralLattice.sigPos, hT, smul_form]
  have hneg : T.sigNeg = L.sigNeg := by
    rw [← sigNeg_smul_of_pos (by norm_num : (0 : ℤ) < 2) L]
    simp only [IntegralLattice.sigNeg, hT, smul_form]
  rw [← hpos, ← hneg]
  exact T.eight_dvd_sigPos_sub_sigNeg_of_isUnimodular hTe hTu

/-- **The invariants of an even `2`-elementary lattice satisfy Nikulin's conditions.** If the
discriminant group of an even nondegenerate lattice `L` is `(ℤ/2)^a`, and `δ = 0` exactly when
`q_L` takes values in `½ℤ/ℤ`, then `(δ; t₊, t₋, a)` satisfies `TwoElementaryAdmissible`. -/
theorem twoElementaryAdmissible_sigPos_sigNeg {a : ℕ}
    (e : L.DiscriminantGroup ≃+ (Fin a → ZMod 2)) {δ : ZMod 2}
    (hδ : δ = 0 ↔ ∀ x : L.DiscriminantGroup,
      L.discriminantQuadraticMap hL x + L.discriminantQuadraticMap hL x = 0) :
    TwoElementaryAdmissible δ L.sigPos L.sigNeg a := by
  set A := L.discriminantQuadraticModule hL
  have hA : A.IsNondegenerate := L.isNondegenerate_discriminantQuadraticModule hL
  have h2 (x : L.DiscriminantGroup) : 2 • x = 0 :=
    e.injective (by
      rw [map_nsmul, map_zero]
      funext i
      exact (by decide : ∀ z : ZMod 2, 2 • z = 0) _)
  have hcard : Nat.card L.DiscriminantGroup = 2 ^ a := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hmil := L.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg hL
  have hrank : L.sigPos + L.sigNeg = finrank ℚ V := by
    have hnull : L.sigNull = 0 := Nat.eq_zero_of_not_pos fun h ↦
      L.isDegenerate_iff_not_nondegenerate.mp (L.isDegenerate_iff_sigNull_pos.mpr h)
        L.form_nondegenerate
    have := L.signature_sum_eq_finrank
    omega
  have hle : a ≤ L.sigPos + L.sigNeg := by
    have := L.natCard_discriminantGroup_dvd_two_pow_finrank h2
    rw [hcard, ← hrank] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  refine ⟨hle, ?_, fun hδ0 ↦ ?_, fun ha ↦ ?_, fun ha ↦ ?_, fun ha hs ↦ ?_, fun hδ0 ha ↦ ?_⟩
  · -- (2) `t₊ - t₋ ≡ sign q_L ≡ a (mod 2)`.
    obtain ⟨k, hk⟩ :=
      FiniteQuadraticModule.exists_gaussSign_eq_add_two_mul_of_two_nsmul_eq_zero hA h2 hcard
    rw [hmil] at hk
    have h := congrArg (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) hk
    simp only [map_sub, map_add, map_mul, map_natCast, map_ofNat] at h
    have h2' : (2 : ZMod 2) = 0 := rfl
    push_cast
    linear_combination h + (L.sigNeg + a + ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2) k) * h2'
  · -- (3) If `q_L` takes values in `½ℤ/ℤ`, then `sign q_L ∈ {0, 4}`.
    obtain ⟨k, hk⟩ :=
      FiniteQuadraticModule.exists_gaussSign_eq_four_mul_of_quadratic_add_self_eq_zero hA
        (hδ.mp hδ0)
    rw [hmil] at hk
    have h := congrArg (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)) hk
    simp only [map_sub, map_mul, map_natCast, map_ofNat] at h
    have h4 : (4 : ZMod 4) = 0 := rfl
    push_cast
    linear_combination h + ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) k * h4
  · -- (4) A trivial discriminant group has zero form and zero invariant.
    subst ha
    have : Subsingleton L.DiscriminantGroup :=
      (Nat.card_eq_one_iff_unique.mp (hcard.trans (pow_zero 2))).1
    have hsub : Subsingleton A := this
    refine ⟨hδ.mpr fun x ↦ by rw [Subsingleton.elim x 0, map_zero, add_zero], ?_⟩
    rw [FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton] at hmil
    push_cast
    exact hmil.symm
  · -- (5) A nondegenerate module of order two has invariant `±1`.
    subst ha
    push_cast
    rw [← hmil]
    exact FiniteQuadraticModule.gaussSign_eq_one_or_eq_neg_one_of_natCard_eq_two hA
      (hcard.trans (pow_one 2))
  · -- (6) A module of order four with invariant `4` takes values in `½ℤ/ℤ`.
    subst ha
    push_cast at hs
    exact hδ.mpr (FiniteQuadraticModule.quadratic_add_self_eq_zero_of_gaussSign_eq_four hA h2
      (hcard.trans (by norm_num)) (hmil.trans hs))
  · -- (7) If `#A_L = 2^n`, then `L = 2Lᵛ` and `Lᵛ(2)` is even unimodular.
    have hS := fun x hx ↦ L.exists_mem_dualCarrier_eq_two_nsmul h2
      (hcard.trans (by rw [ha, hrank])) (x := x) hx
    have h8 := L.eight_dvd_sigPos_sub_sigNeg_of_carrier_eq_two_nsmul hL h2 hS (hδ.mp hδ0)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (by exact_mod_cast h8)

end Necessity

/-- **An even `2`-elementary lattice with invariants `(δ; t₊, t₋, a)` exists.** It is a
nondegenerate even lattice in `ℚ^{t₊ + t₋}` of signature `(t₊, 0, t₋)` whose discriminant group is
`(ℤ/2)^a`, and `δ = 0` exactly when its half-norm discriminant form takes values in `½ℤ/ℤ`. -/
def TwoElementaryLatticeWithInvariants (δ : ZMod 2) (tp tm a : ℕ) : Prop :=
  ∃ (L : IntegralLattice (Fin (tp + tm) → ℚ)) (_ : L.IsNondegenerate) (hev : L.IsEven),
    L.signature = (tp, 0, tm) ∧ Nonempty (L.DiscriminantGroup ≃+ (Fin a → ZMod 2)) ∧
      (δ = 0 ↔ ∀ x : L.DiscriminantGroup,
        L.discriminantQuadraticMap hev x + L.discriminantQuadraticMap hev x = 0)

/-- **The necessity half of Nikulin's Theorem 3.6.2**: the invariants of an even `2`-elementary
lattice satisfy his seven conditions. -/
theorem TwoElementaryLatticeWithInvariants.twoElementaryAdmissible {δ : ZMod 2} {tp tm a : ℕ}
    (h : TwoElementaryLatticeWithInvariants δ tp tm a) : TwoElementaryAdmissible δ tp tm a := by
  obtain ⟨L, _, hev, hsig, ⟨e⟩, hδ⟩ := h
  have hadm := L.twoElementaryAdmissible_sigPos_sigNeg hev e hδ
  simp only [signature, Prod.mk.injEq] at hsig
  rwa [hsig.1, hsig.2.2] at hadm

end TauCeti.IntegralLattice
