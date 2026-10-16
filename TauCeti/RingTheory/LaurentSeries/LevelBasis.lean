/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerBasis
public import TauCeti.RingTheory.LaurentSeries.Puiseux

/-!
# Power bases of ramified Laurent-series levels

For a positive integer `d`, every Laurent series has a unique decomposition

`f = ∑ r : Fin d, X ^ r * expand d (contract d f r)`.

Here `contract d f r` retains the coefficients of `f` in the congruence class `r` modulo `d`
and divides their exponents by `d`. This realizes the Laurent-series field in the variable `u`
as a degree-`d` extension of the Laurent-series field in `t = u ^ d`, with power basis
`1, u, ..., u ^ (d - 1)`.

The source and target fields have the same underlying Laurent-series type but different algebra
structures. `LaurentSeries.Level K d` is therefore a wrapped copy of `K⸨X⸩`, with the base-field
map given by `LaurentSeries.expand K d`. It embeds into the Puiseux field as its actual level-`d`
subfield. Transporting the power basis proves that this subfield has degree `d`; since every
Puiseux series lies in some level, the Puiseux field is algebraic over `K⸨X⸩` in every
characteristic.

The contraction and decomposition API follows the design proposed in
[Mathlib PR #42313](https://github.com/leanprover-community/mathlib4/pull/42313).

## Main definitions

* `LaurentSeries.contract`: the exponent-congruence component of a Laurent series.
* `LaurentSeries.Level`: the level-`d` Laurent field with base map `X ↦ X ^ d`.
* `LaurentSeries.Level.powerBasis`: the power basis `1, u, ..., u ^ (d - 1)`.
* `TauCeti.puiseuxField.level`: the actual level-`d` intermediate field in the Puiseux field.
* `TauCeti.puiseuxField.levelPowerBasis`: its transported power basis.

## Main results

* `LaurentSeries.sum_single_mul_expand_contract`: reconstruction from congruence components.
* `LaurentSeries.contract_eq_of_sum_eq`: uniqueness of the congruence components.
* `TauCeti.puiseuxField.level_finrank`: level `d` has degree `d` over `K⸨X⸩`.
* `TauCeti.puiseuxField.isAlgebraic_laurentSeries`: every Puiseux series is algebraic over
  `K⸨X⸩`.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace LaurentSeries

variable {R : Type*}

/-- The `r`-th exponent-congruence component of a Laurent series. Its coefficient at `k` is the
coefficient of the original series at `d * k + r`. -/
noncomputable def contract [Zero R] (d : ℕ+) (f : R⸨X⸩) (r : Fin d) : R⸨X⸩ :=
  ofSuppBddBelow (fun k : ℤ ↦ f.coeff ((d : ℤ) * k + r)) <| by
    refine ⟨min 0 f.order, ?_⟩
    intro k hk
    rw [Function.mem_support] at hk
    by_contra hle
    have hklt : k < min 0 f.order := lt_of_not_ge hle
    have hkneg : k < 0 := hklt.trans_le (min_le_left _ _)
    have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast r.val.zero_le
    have hrlt : (r : ℤ) < d := by exact_mod_cast r.isLt
    have hdpos : (0 : ℤ) < d := by exact_mod_cast d.pos
    have hindex : (d : ℤ) * k + r < f.order := by
      have : (d : ℤ) * k + r ≤ k := by nlinarith
      exact this.trans_lt (hklt.trans_le (min_le_right _ _))
    exact hk (coeff_eq_zero_of_lt_order hindex)

/-- The coefficient formula for an exponent-congruence component. -/
@[simp]
theorem coeff_contract [Zero R] (d : ℕ+) (f : R⸨X⸩) (r : Fin d) (k : ℤ) :
    (contract d f r).coeff k = f.coeff ((d : ℤ) * k + r) := (rfl)

/-- Contraction is additive. -/
@[simp]
theorem contract_add [AddCommMonoid R] (d : ℕ+) (f g : R⸨X⸩) (r : Fin d) :
    contract d (f + g) r = contract d f r + contract d g r := by
  ext k
  simp

/-- Every congruence component of the zero series is zero. -/
@[simp]
theorem contract_zero [Zero R] (d : ℕ+) (r : Fin d) : contract d (0 : R⸨X⸩) r = 0 := by
  ext k
  simp

/-- A wrapped copy of the Laurent-series field at ramified level `d`. Its field structure is the
usual one, while its `K⸨X⸩`-algebra structure sends the base parameter to the `d`-th power of the
level parameter. The wrapper avoids installing two algebra structures on `K⸨X⸩` itself. -/
@[ext]
structure Level (K : Type*) [Field K] (d : ℕ+) where
  ofLaurentSeries ::
  /-- The Laurent series underlying an element of a ramified level. -/
  toLaurentSeries : LaurentSeries K

namespace Level

variable (K : Type*) [Field K] (d : ℕ+)

/-- The underlying Laurent series of a ramified-level element. -/
def equivLaurentSeries : Level K d ≃ K⸨X⸩ where
  toFun := toLaurentSeries
  invFun := ofLaurentSeries
  left_inv _ := rfl
  right_inv _ := rfl

/-- A ramified level has the field structure of its underlying Laurent series. -/
noncomputable instance : Field (Level K d) := (equivLaurentSeries K d).field

/-- The ring equivalence from a ramified level to its underlying Laurent-series field. -/
def ringEquivLaurentSeries : Level K d ≃+* K⸨X⸩ where
  __ := equivLaurentSeries K d
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The base-field map into level `d`, given on underlying Laurent series by expansion
`X ↦ X ^ d`. -/
noncomputable def algebraMap : K⸨X⸩ →+* Level K d :=
  (ringEquivLaurentSeries K d).symm.toRingHom.comp (expand K d).toRingHom

/-- Level `d` is a `K⸨X⸩`-algebra through the expansion `X ↦ X ^ d`. -/
noncomputable instance : Algebra K⸨X⸩ (Level K d) := (algebraMap K d).toAlgebra

/-- The algebra map into a ramified level is expansion on underlying Laurent series. -/
@[simp]
theorem algebraMap_apply (f : K⸨X⸩) :
    ringEquivLaurentSeries K d (Algebra.algebraMap K⸨X⸩ (Level K d) f) =
      expand K d f := (rfl)

/-- Wrapping and then taking the underlying Laurent series is the identity. -/
@[simp]
theorem ringEquivLaurentSeries_ofLaurentSeries (f : K⸨X⸩) :
    ringEquivLaurentSeries K d (.ofLaurentSeries f) = f := (rfl)

end Level

variable {K : Type*} [Field K]

/-- At exponent `d * k + r`, a sum of expanded congruence components recovers coefficient `k`
of component `r`. -/
theorem coeff_sum_single_mul_expand {A : Type*} [CommSemiring A] (d : ℕ+)
    (g : Fin d → A⸨X⸩) (r : Fin d) (k : ℤ) :
    (∑ s : Fin d, single (s : ℤ) 1 * expand A d (g s)).coeff ((d : ℤ) * k + r) =
      (g r).coeff k := by
  simp only [coeff_sum, coeff_single_mul, one_mul]
  rw [Finset.sum_eq_single r]
  · convert coeff_expand_mul d (g r) k using 1
    simp
  · intro s _ hsr
    apply coeff_expand_of_not_dvd
    intro hdiv
    obtain ⟨q, hq⟩ := hdiv
    have hmod : (r : ℤ) - s = (d : ℤ) * (q - k) := by
      linear_combination hq
    have hrlt : (r : ℤ) < d := by exact_mod_cast r.isLt
    have hslt : (s : ℤ) < d := by exact_mod_cast s.isLt
    have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast r.val.zero_le
    have hsnonneg : (0 : ℤ) ≤ s := by exact_mod_cast s.val.zero_le
    have hdpos : (0 : ℤ) < d := by exact_mod_cast d.pos
    have hrslt : (r : ℤ) - s < d := by omega
    have hneg : -(d : ℤ) < (r : ℤ) - s := by omega
    have hqk : q - k = 0 := by nlinarith [hmod]
    have hrs : (r : ℤ) = s := by rw [hqk, mul_zero] at hmod; omega
    exact hsr (Fin.ext (by exact_mod_cast hrs.symm))
  · simp

namespace Level

private noncomputable def combination (d : ℕ+) :
    (Fin d → K⸨X⸩) →ₗ[K⸨X⸩] Level K d where
  toFun g := (ringEquivLaurentSeries K d).symm
    (∑ r : Fin d, single (r : ℤ) 1 * expand K d (g r))
  map_add' g h := by
    apply (ringEquivLaurentSeries K d).injective
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a g := by
    apply (ringEquivLaurentSeries K d).injective
    -- The scalar action on the wrapped target is expansion, while the source uses ordinary
    -- multiplication pointwise.
    change (∑ r : Fin d, single (r : ℤ) 1 * expand K d (a * g r)) =
      expand K d a * ∑ r : Fin d, single (r : ℤ) 1 * expand K d (g r)
    simp only [map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

@[simp]
private theorem ringEquiv_combination (d : ℕ+) (g : Fin d → K⸨X⸩) :
    ringEquivLaurentSeries K d (combination d g) =
      ∑ r : Fin d, single (r : ℤ) 1 * expand K d (g r) := (rfl)

private theorem coeff_combination_mul_add (d : ℕ+) (g : Fin d → K⸨X⸩) (r : Fin d)
    (k : ℤ) :
    (ringEquivLaurentSeries K d (combination d g)).coeff ((d : ℤ) * k + r) =
      (g r).coeff k := by
  rw [ringEquiv_combination]
  exact coeff_sum_single_mul_expand d g r k

end Level

/-- A Laurent series is the sum of its expanded exponent-congruence components. -/
theorem sum_single_mul_expand_contract {A : Type*} [CommSemiring A] (d : ℕ+) (f : A⸨X⸩) :
    ∑ r : Fin d, single (r : ℤ) 1 * expand A d (contract d f r) = f := by
  ext z
  let r : Fin d := ⟨(z % d).toNat, by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast d.ne_zero))]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast d.pos)⟩
  let k := z / (d : ℤ)
  have hr : (r : ℤ) = z % d := by
    simp only [r]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast d.ne_zero))]
  have hz : (d : ℤ) * k + r = z := by
    rw [hr, add_comm, Int.emod_add_mul_ediv]
  rw [← hz, coeff_sum_single_mul_expand, coeff_contract, hz]

/-- The components in an expansion by exponent congruence classes are unique. -/
theorem contract_eq_of_sum_eq {A : Type*} [CommSemiring A] (d : ℕ+) (g : Fin d → A⸨X⸩)
    (f : A⸨X⸩) (h : ∑ r : Fin d, single (r : ℤ) 1 * expand A d (g r) = f) (r : Fin d) :
    contract d f r = g r := by
  ext k
  rw [coeff_contract, ← h, coeff_sum_single_mul_expand]

namespace Level

private theorem combination_injective (d : ℕ+) :
    Function.Injective (combination (K := K) d) := by
  intro g h hgh
  funext r
  ext k
  rw [← coeff_combination_mul_add d g r k, hgh, coeff_combination_mul_add d h r k]

private theorem combination_surjective (d : ℕ+) :
    Function.Surjective (combination (K := K) d) := by
  intro f
  let f' := ringEquivLaurentSeries K d f
  refine ⟨fun r ↦ contract d f' r, ?_⟩
  apply (ringEquivLaurentSeries K d).injective
  rw [ringEquiv_combination, sum_single_mul_expand_contract]

private noncomputable def combinationEquiv (K : Type*) [Field K] (d : ℕ+) :
    (Fin d → K⸨X⸩) ≃ₗ[K⸨X⸩] Level K d :=
  LinearEquiv.ofBijective (combination d) ⟨combination_injective d, combination_surjective d⟩

@[simp]
private theorem combinationEquiv_apply (K : Type*) [Field K] (d : ℕ+)
    (g : Fin d → K⸨X⸩) :
    combinationEquiv K d g = combination d g := (rfl)

/-- The basis of level `d` obtained by splitting exponents modulo `d`. -/
noncomputable def basis (K : Type*) [Field K] (d : ℕ+) :
    Module.Basis (Fin d) K⸨X⸩ (Level K d) :=
  Module.Basis.ofEquivFun (combinationEquiv K d).symm

/-- The level parameter `u`, whose `d`-th power is the base parameter. -/
noncomputable def parameter (K : Type*) [Field K] (d : ℕ+) : Level K d :=
  (ringEquivLaurentSeries K d).symm (single 1 1)

/-- The underlying Laurent series of the level parameter is `X`. -/
@[simp]
theorem ringEquiv_parameter (K : Type*) [Field K] (d : ℕ+) :
    ringEquivLaurentSeries K d (parameter K d) = single 1 1 := by
  simp [parameter]

/-- The level parameter is a `d`-th root of the base parameter. -/
theorem parameter_pow (K : Type*) [Field K] (d : ℕ+) :
    parameter K d ^ (d : ℕ) =
      Algebra.algebraMap K⸨X⸩ (Level K d) (single 1 1) := by
  apply (ringEquivLaurentSeries K d).injective
  simp

private theorem basis_eq_combination_single (K : Type*) [Field K] (d : ℕ+) (r : Fin d) :
    basis K d r = combinationEquiv K d (Pi.single r 1) := by
  simp only [basis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]

/-- The basis vectors of level `d` are `1, u, ..., u ^ (d - 1)`. -/
@[simp]
theorem basis_apply (K : Type*) [Field K] (d : ℕ+) (r : Fin d) :
    basis K d r = parameter K d ^ (r : ℕ) := by
  apply (ringEquivLaurentSeries K d).injective
  rw [map_pow, ringEquiv_parameter]
  rw [basis_eq_combination_single]
  rw [combinationEquiv_apply, ringEquiv_combination]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hsr
    simp [hsr]
  · simp

/-- The coordinates of a level element in the power basis are its exponent-congruence
components. -/
@[simp]
theorem basis_repr_apply (K : Type*) [Field K] (d : ℕ+) (f : Level K d) (r : Fin d) :
    (basis K d).repr f r = contract d (ringEquivLaurentSeries K d f) r := by
  rw [basis, Module.Basis.ofEquivFun_repr_apply]
  symm
  apply contract_eq_of_sum_eq d ((combinationEquiv K d).symm f) _
  rw [← ringEquiv_combination, ← combinationEquiv_apply]
  exact congrArg (ringEquivLaurentSeries K d) ((combinationEquiv K d).apply_symm_apply f)

/-- The power basis `1, u, ..., u ^ (d - 1)` of the ramified Laurent-series level. -/
noncomputable def powerBasis (K : Type*) [Field K] (d : ℕ+) :
    PowerBasis K⸨X⸩ (Level K d) where
  gen := parameter K d
  dim := d
  basis := basis K d
  basis_eq_pow := basis_apply K d

/-- A ramified Laurent-series level is finite-dimensional over the base Laurent field. -/
noncomputable instance moduleFinite (K : Type*) [Field K] (d : ℕ+) :
    Module.Finite K⸨X⸩ (Level K d) :=
  (powerBasis K d).finite

/-- The `K⸨X⸩`-algebra embedding of level `d` into the Puiseux field. -/
noncomputable def toPuiseux (K : Type*) [Field K] (d : ℕ+) :
    Level K d →ₐ[K⸨X⸩] TauCeti.puiseuxField K where
  toFun f := TauCeti.puiseuxField.levelEmbedding K d (ringEquivLaurentSeries K d f)
  map_one' := by simp
  map_mul' f g := by simp
  map_zero' := by simp
  map_add' f g := by simp
  commutes' f := by
    apply Subtype.ext
    rw [TauCeti.puiseuxField.coe_algebraMap_laurentSeries,
      TauCeti.puiseuxField.coe_levelEmbedding, algebraMap_apply]
    simpa only [one_mul] using ramifiedEmbedding_expand (R := K) 1 d f

/-- As a rational-exponent Hahn series, the level embedding is the corresponding ramified
embedding. -/
theorem coe_toPuiseux (K : Type*) [Field K] (d : ℕ+) (f : Level K d) :
    ((toPuiseux K d f : TauCeti.puiseuxField K) : HahnSeries ℚ K) =
      ramifiedEmbedding K d (ringEquivLaurentSeries K d f) := by
  exact TauCeti.puiseuxField.coe_levelEmbedding d (ringEquivLaurentSeries K d f)

/-- The embedding of a ramified Laurent-series level into the Puiseux field is injective. -/
theorem toPuiseux_injective (K : Type*) [Field K] (d : ℕ+) :
    Function.Injective (toPuiseux K d) := by
  intro f g h
  apply (ringEquivLaurentSeries K d).injective
  apply ramifiedEmbedding_injective d
  simpa only [coe_toPuiseux] using congrArg (fun x : TauCeti.puiseuxField K ↦
    (x : HahnSeries ℚ K)) h

/-- The abstract level embedding agrees with `puiseuxField.levelEmbedding` on the underlying
Laurent series. -/
@[simp]
theorem toPuiseux_apply (K : Type*) [Field K] (d : ℕ+) (f : Level K d) :
    toPuiseux K d f =
      TauCeti.puiseuxField.levelEmbedding K d (ringEquivLaurentSeries K d f) := by
  apply Subtype.ext
  rw [coe_toPuiseux, TauCeti.puiseuxField.coe_levelEmbedding]

end Level

end LaurentSeries

namespace TauCeti.puiseuxField

/-- The actual level-`d` intermediate field inside the Puiseux field. -/
noncomputable def level (K : Type*) [Field K] (d : ℕ+) :
    IntermediateField K⸨X⸩ (TauCeti.puiseuxField K) :=
  (LaurentSeries.Level.toPuiseux K d).fieldRange

/-- Membership in the actual level is membership in the range of the corresponding level
embedding. -/
theorem mem_level_iff (K : Type*) [Field K] (d : ℕ+) (x : TauCeti.puiseuxField K) :
    x ∈ level K d ↔ x ∈ (levelEmbedding K d).range := by
  rw [level, AlgHom.mem_fieldRange, AlgHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨LaurentSeries.Level.ringEquivLaurentSeries K d f,
      LaurentSeries.Level.toPuiseux_apply K d f⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(LaurentSeries.Level.ringEquivLaurentSeries K d).symm f, ?_⟩
    simp

/-- The abstract ramified Laurent-series level is equivalent to its image in the Puiseux field. -/
noncomputable def levelEquiv (K : Type*) [Field K] (d : ℕ+) :
    LaurentSeries.Level K d ≃ₐ[K⸨X⸩] level K d :=
  (LaurentSeries.Level.toPuiseux K d).equivFieldRange

/-- The transported power basis of the actual level-`d` subfield of the Puiseux field. -/
noncomputable def levelPowerBasis (K : Type*) [Field K] (d : ℕ+) :
    PowerBasis K⸨X⸩ (level K d) :=
  (LaurentSeries.Level.powerBasis K d).map (levelEquiv K d)

/-- The level-`d` Puiseux subfield has degree `d` over `K⸨X⸩`. -/
theorem level_finrank (K : Type*) [Field K] (d : ℕ+) :
    Module.finrank K⸨X⸩ (level K d) = d := by
  rw [(levelPowerBasis K d).finrank]
  rfl

/-- The Puiseux field is algebraic over the Laurent-series field in every characteristic. -/
theorem isAlgebraic_laurentSeries (K : Type*) [Field K] :
    Algebra.IsAlgebraic K⸨X⸩ (TauCeti.puiseuxField K) := by
  constructor
  intro x
  obtain ⟨d, f, hfx⟩ := exists_mem_range_levelEmbedding x
  let y : LaurentSeries.Level K d :=
    (LaurentSeries.Level.ringEquivLaurentSeries K d).symm f
  have hyalg : IsAlgebraic K⸨X⸩ y :=
    @Algebra.IsAlgebraic.isAlgebraic _ _ _ _ _
      (Algebra.IsAlgebraic.of_finite K⸨X⸩ (LaurentSeries.Level K d)) y
  have hy : IsIntegral K⸨X⸩ y := hyalg.isIntegral
  have hmap := hy.map (LaurentSeries.Level.toPuiseux K d)
  simp only [y, LaurentSeries.Level.toPuiseux_apply, RingEquiv.apply_symm_apply] at hmap
  have hfx' : levelEmbedding K d f = x := hfx
  rw [hfx'] at hmap
  exact hmap.isAlgebraic

end TauCeti.puiseuxField
