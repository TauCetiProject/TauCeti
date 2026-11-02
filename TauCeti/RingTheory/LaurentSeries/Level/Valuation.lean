/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Extension
public import TauCeti.RingTheory.LaurentSeries.Level.Basis
public import TauCeti.RingTheory.LaurentSeries.Valuation.Ring
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Valuation, integers and ramification of the ramified Laurent-series levels

Let `L = K⸨u⸩` be the level-`d` Laurent field over `F = K⸨t⸩`, with `t = u ^ d`. This file
equips `L` with its `u`-adic valuation and computes the local invariants of `L / F` directly from
the exponent decomposition `f = ∑ r : Fin d, u ^ r * (contract d f r)(u ^ d)`:

* the valuation of `L` restricts to the `d`-th power of the valuation of `F`, and the level
  parameter `u` has valuation `exp (-1)`, so the valuation of `L` extends that of `F`;
* the integer ring `K⟦u⟧` of `L` is free over the integer ring `K⟦t⟧` of `F`, with basis
  `1, u, ..., u ^ (d - 1)`: an element of `L` is integral exactly when all its congruence
  components are;
* the maximal ideal `(t)` of `K⟦t⟧` generates the `d`-th power of the maximal ideal `(u)` of
  `K⟦u⟧`, so the ramification index of `L / F` is `d`;
* every element of `K⟦u⟧` is congruent modulo `u` to a constant, so both residue fields are `K`,
  the residue of an integer being its constant coefficient, and the inertia degree is `1`.

No hypothesis on `K` is needed: the residue field may be infinite, imperfect, or of any
characteristic. Thus `L / F` is totally ramified, with `e f = d = [L : F]`.

## Main definitions

* `TauCeti.LaurentSeries.Level.valuation`: the `u`-adic valuation of the level, valued in `ℤᵐ⁰`.
* `TauCeti.LaurentSeries.Level.integerBasis`: the basis `1, u, ..., u ^ (d - 1)` of the integers
  of the level over the integers of `K⸨X⸩`.
* `TauCeti.LaurentSeries.Level.residueFieldEquiv`: the residue field of the level is `K`.

## Main results

* `TauCeti.LaurentSeries.Level.valuation_algebraMap`: the valuation of the level restricts to the
  `d`-th power of the valuation of `K⸨X⸩`.
* `TauCeti.LaurentSeries.Level.hasExtension`: the valuation of the level extends that of `K⸨X⸩`.
* `TauCeti.LaurentSeries.Level.mem_valuationSubring_iff`: integrality is detected by the
  congruence components.
* `TauCeti.LaurentSeries.Level.map_maximalIdeal`: the maximal ideal of `K⟦t⟧` generates the
  `d`-th power of the maximal ideal of `K⟦u⟧`.
* `TauCeti.LaurentSeries.Level.ramificationIdx_maximalIdeal`: the ramification index is `d`.
* `TauCeti.LaurentSeries.Level.residueFieldEquiv_residue`: the residue of an integer of the level
  is its constant coefficient.
* `TauCeti.LaurentSeries.Level.inertiaDeg_maximalIdeal`: the inertia degree is `1`.
-/

public section

open IsLocalRing Module
open scoped LaurentSeries WithZero

namespace TauCeti.LaurentSeries.Level

open _root_.LaurentSeries

variable (K : Type*) [Field K] (d : ℕ+)

/-- The valuation of the level `K⸨u⸩`: the `u`-adic valuation of its underlying Laurent series,
normalized by `v u = exp (-1)`. -/
noncomputable def valuation : Valuation (Level K d) ℤᵐ⁰ :=
  (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).comap (ringEquivLaurentSeries K d).toRingHom

variable {K d} in
@[simp]
theorem valuation_apply (x : Level K d) :
    valuation K d x = Valued.v (ringEquivLaurentSeries K d x) := (rfl)

theorem valuation_surjective : Function.Surjective (valuation K d) := fun γ ↦ by
  obtain ⟨f, hf⟩ := _root_.LaurentSeries.valuation_surjective K γ
  exact ⟨(ringEquivLaurentSeries K d).symm f, by simpa using hf⟩

/-- The level parameter `u` is a uniformizer of the level. -/
theorem valuation_parameter : valuation K d (parameter K d) = WithZero.exp (-1) := by
  simpa using valuation_single_zpow (K := K) 1

/-- The valuation of the level restricts to the `d`-th power of the valuation of `K⸨X⸩`: the
base parameter `t = u ^ d` has valuation `exp (-d)`. -/
theorem valuation_algebraMap (f : K⸨X⸩) :
    valuation K d (Algebra.algebraMap K⸨X⸩ (Level K d) f) = Valued.v f ^ (d : ℕ) := by
  simp

/-- The valuation of the level extends the valuation of `K⸨X⸩`, up to the equivalence of
valuations that forgets the normalization. -/
instance hasExtension : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).HasExtension (valuation K d) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro f
    simp [pow_le_one_iff_of_nonneg zero_le d.ne_zero]

/-- The integer ring of the level is a discrete valuation ring. -/
instance : IsDiscreteValuationRing (valuation K d).valuationSubring :=
  Valuation.valuationSubring_isDiscreteValuationRing_of_surjective _ (valuation_surjective K d)

/-! ### The integer ring -/

variable {K d}

/-- The congruence components of an integral element of the level are integral. -/
theorem contract_mem_valuationSubring {x : Level K d} (hx : x ∈ (valuation K d).valuationSubring)
    (r : Fin d) :
    contract d (ringEquivLaurentSeries K d x) r ∈
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, valuation_apply, valuation_le_one_iff] at hx
  rw [Valuation.mem_valuationSubring_iff, valuation_le_one_iff]
  intro n hn
  rw [coeff_contract]
  apply hx
  have := r.isLt
  have := d.pos
  nlinarith

theorem parameter_mem_valuationSubring :
    parameter K d ∈ (valuation K d).valuationSubring := by
  simp [Valuation.mem_valuationSubring_iff, valuation_single_zpow]

/-- A combination `∑ r, a r • u ^ r` with integral coefficients `a r` is integral. -/
theorem sum_smul_parameter_pow_mem_valuationSubring
    (a : Fin d → (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring) :
    ∑ r, (a r : K⸨X⸩) • parameter K d ^ (r : ℕ) ∈ (valuation K d).valuationSubring := by
  refine Subring.sum_mem _ fun r _ ↦ ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (Valuation.HasExtension.algebraMap_mem_valuationSubring _ _ (a r))
    (Subring.pow_mem _ parameter_mem_valuationSubring _)

/-- An element of the level is integral exactly when all its congruence components are
integral: the integers `K⟦u⟧` of the level are `⨁ r, u ^ r K⟦t⟧`. -/
theorem mem_valuationSubring_iff {x : Level K d} :
    x ∈ (valuation K d).valuationSubring ↔
      ∀ r, contract d (ringEquivLaurentSeries K d x) r ∈
        (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring := by
  refine ⟨contract_mem_valuationSubring, fun h ↦ ?_⟩
  rw [← (basis K d).sum_repr x]
  simpa using sum_smul_parameter_pow_mem_valuationSubring fun r ↦ ⟨_, h r⟩

variable (K d)

/-- The integers of the level are the `K⟦t⟧`-span of the basis `1, u, ..., u ^ (d - 1)` of the
level over `K⸨X⸩`. -/
private noncomputable def spanBasisEquiv :
    Submodule.span (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring (Set.range (basis K d)) ≃ₗ[
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring] (valuation K d).valuationSubring :=
  have h (x : Level K d) : x ∈ Submodule.span _ (Set.range (basis K d)) ↔
      x ∈ (valuation K d).valuationSubring := by
    rw [Basis.mem_span_iff_repr_mem, mem_valuationSubring_iff]
    simp [basis_repr_apply]
  { toFun x := ⟨x, (h x).mp x.2⟩
    invFun x := ⟨x, (h x).mpr x.2⟩
    map_add' _ _ := rfl
    map_smul' c x := Subtype.ext (Algebra.smul_def (c : K⸨X⸩) (x : Level K d)) }

/-- The basis `1, u, ..., u ^ (d - 1)` of the integers of the level over the integers of
`K⸨X⸩`. -/
noncomputable def integerBasis :
    Basis (Fin d) (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring
      (valuation K d).valuationSubring :=
  (basis K d).restrictScalars _ |>.map (spanBasisEquiv K d)

variable {K d}

/-- The integral basis vectors are the powers `u ^ r`, `r < d`. -/
@[simp]
theorem coe_integerBasis (r : Fin d) :
    (integerBasis K d r : Level K d) = parameter K d ^ (r : ℕ) := by
  simp [integerBasis, spanBasisEquiv]

/-- The integral coordinates are the congruence components. -/
@[simp]
theorem coe_integerBasis_repr (x : (valuation K d).valuationSubring) (r : Fin d) :
    ((integerBasis K d).repr x r : K⸨X⸩) = contract d (ringEquivLaurentSeries K d x) r := by
  rw [← basis_repr_apply]
  exact (basis K d).restrictScalars_repr_apply _ ((spanBasisEquiv K d).symm x) r

variable (K d)

instance : Module.Free (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring
    (valuation K d).valuationSubring :=
  .of_basis (integerBasis K d)

instance : Module.Finite (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring
    (valuation K d).valuationSubring :=
  .of_basis (integerBasis K d)

/-- The integers of the level have rank `d` over the integers of `K⸨X⸩`. -/
theorem finrank_valuationSubring :
    finrank (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring (valuation K d).valuationSubring =
      d := by
  simp [finrank_eq_card_basis (integerBasis K d)]

/-! ### Ramification and residue degree -/

/-- The maximal ideal `(t)` of `K⟦t⟧` generates the `d`-th power of the maximal ideal `(u)` of
`K⟦u⟧`: the level is totally ramified over `K⸨X⸩` with ramification index `d`. -/
theorem map_maximalIdeal :
    (maximalIdeal (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring).map
        (Algebra.algebraMap (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring
          (valuation K d).valuationSubring) =
      maximalIdeal (valuation K d).valuationSubring ^ (d : ℕ) := by
  let t : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring :=
    ⟨HahnSeries.single 1 1, by
      rw [Valuation.mem_valuationSubring_iff, valuation_single_zpow]
      simp⟩
  let u : (valuation K d).valuationSubring := ⟨parameter K d, parameter_mem_valuationSubring⟩
  have ht : Algebra.algebraMap _ (valuation K d).valuationSubring t = u ^ (d : ℕ) := by
    ext
    simp [u, t, parameter_pow]
  rw [Valuation.maximalIdeal_eq_span_of_map_eq_exp_neg_one _ (π := t) (valuation_single_zpow K 1),
    Valuation.maximalIdeal_eq_span_of_map_eq_exp_neg_one _ (π := u) (valuation_parameter K d),
    Ideal.map_span, Set.image_singleton, ht, Ideal.span_singleton_pow]

/-- The ramification index of the level over `K⸨X⸩` is `d`. -/
theorem ramificationIdx_maximalIdeal :
    (maximalIdeal (valuation K d).valuationSubring).ramificationIdx
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring = d :=
  TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow
    (map_maximalIdeal K d)

variable {K d} in
/-- Every integer of the level is congruent modulo `u` to the image of an integer of `K⸨X⸩`,
namely the constant coefficient. -/
theorem exists_sub_algebraMap_mem_maximalIdeal (x : (valuation K d).valuationSubring) :
    ∃ a : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring,
      x - Algebra.algebraMap _ _ a ∈ maximalIdeal (valuation K d).valuationSubring := by
  have hx := x.2
  rw [Valuation.mem_valuationSubring_iff, valuation_apply, valuation_le_one_iff] at hx
  refine ⟨⟨HahnSeries.C ((ringEquivLaurentSeries K d x).coeff 0), by
    rw [Valuation.mem_valuationSubring_iff, valuation_le_one_iff]
    intro n hn
    simp [hn.ne]⟩, ?_⟩
  rw [Valuation.mem_maximalIdeal_iff]
  refine lt_of_le_of_lt (b := WithZero.exp (-1)) ?_ (by simp)
  rw [AddSubgroupClass.coe_sub, Valuation.HasExtension.coe_algebraMap_valuationSubring_eq,
    valuation_apply, map_sub, algebraMap_apply, valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  -- The valuation bound `exp (-1)` means the difference vanishes below exponent `1`.
  have hn0 : n ≤ 0 := by omega
  rcases lt_or_eq_of_le hn0 with hn | rfl
  · simp [hx n hn, hn.ne]
  · simp

variable {K d} in
/-- The integers of the level are the power series in `u`. -/
theorem ringEquivLaurentSeries_mem_powerSeries_as_subring_iff {x : Level K d} :
    ringEquivLaurentSeries K d x ∈ powerSeries_as_subring K ↔
      x ∈ (valuation K d).valuationSubring := by
  rw [Huber.LaurentSeries.powerSeries_as_subring_eq_integer, Valuation.mem_integer_iff,
    Valuation.mem_valuationSubring_iff, valuation_apply]

/-- The integers of the level, identified with the power series `K⟦u⟧` inside `K⸨u⸩`. -/
private noncomputable def valuationSubringEquiv :
    (valuation K d).valuationSubring ≃+* powerSeries_as_subring K :=
  (ringEquivLaurentSeries K d).restrict _ _ fun _ ↦
    ringEquivLaurentSeries_mem_powerSeries_as_subring_iff.symm

/-- The residue field of the level is canonically the coefficient field `K`. -/
noncomputable def residueFieldEquiv : ResidueField (valuation K d).valuationSubring ≃+* K :=
  (ResidueField.mapEquiv (valuationSubringEquiv K d)).trans
    (TauCeti.LaurentSeries.residueFieldEquiv K)

variable {K d} in
/-- The residue of an integer of the level is its constant coefficient. -/
@[simp]
theorem residueFieldEquiv_residue (x : (valuation K d).valuationSubring) :
    residueFieldEquiv K d (residue _ x) = (ringEquivLaurentSeries K d x).coeff 0 := by
  rw [residueFieldEquiv, RingEquiv.trans_apply, ResidueField.mapEquiv_apply,
    ResidueField.map_residue, TauCeti.LaurentSeries.residueFieldEquiv_residue]
  rfl

/-- The residue field extension of the level over `K⸨X⸩` is trivial: its inertia degree is `1`. -/
theorem inertiaDeg_maximalIdeal :
    (maximalIdeal (valuation K d).valuationSubring).inertiaDeg
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring = 1 := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (maximalIdeal (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring)]
  let := Ideal.Quotient.field (maximalIdeal (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring)
  rw [finrank_eq_one_iff_of_nonzero' 1 one_ne_zero]
  rintro ⟨x⟩
  obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal x
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_mk_of_liesOver]
  exact (Ideal.Quotient.eq.mpr ha).symm

/-- The level is totally ramified: `e f = d = [L : K⸨X⸩]`. -/
theorem ramificationIdx_mul_inertiaDeg :
    (maximalIdeal (valuation K d).valuationSubring).ramificationIdx
        (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring *
      (maximalIdeal (valuation K d).valuationSubring).inertiaDeg
        (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).valuationSubring =
      finrank K⸨X⸩ (Level K d) := by
  rw [ramificationIdx_maximalIdeal, inertiaDeg_maximalIdeal, mul_one,
    finrank_eq_card_basis (basis K d), Fintype.card_fin]

end TauCeti.LaurentSeries.Level
