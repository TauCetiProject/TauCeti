/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerBasis
public import TauCeti.Algebra.Group.Coprime
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic

/-!
# Power bases of ramified Laurent-series levels

For a positive integer `d`, every Laurent series has a unique decomposition

`f = ∑ r : Fin d, X ^ r * expand d (contract d f r)`.

Here `contract d f r` retains the coefficients of `f` in the congruence class `r` modulo `d`
and sends each exponent `d * k + r` to `k`. This realizes the Laurent-series field in the
variable `u` as a degree-`d` extension of the Laurent-series field in `t = u ^ d`, with power
basis `1, u, ..., u ^ (d - 1)`.

The source and target fields have the same underlying Laurent-series type but different algebra
structures. `TauCeti.LaurentSeries.Level K d` is therefore a wrapped copy of `K⸨X⸩`, with the
base-field map given by `LaurentSeries.expand K d`. It embeds into the Puiseux field as its actual
level-`d` subfield. Transporting the power basis proves that this subfield has degree `d`; since
every Puiseux series lies in some level, the Puiseux field is algebraic over `K⸨X⸩` in every
characteristic.

The actual levels form a lattice of intermediate fields mirroring divisibility: level `n` lies in
level `m` exactly when `n ∣ m`, the intersection of levels `n` and `m` is level `gcd n m`, their
compositum is level `lcm n m`, level one is `K⸨X⸩` and the levels exhaust the Puiseux field. These
formulas reduce questions about finitely many ramified subextensions, such as the smallest level
containing given Puiseux series, to divisibility of the levels.

The contraction and decomposition API follows the design proposed in
[Mathlib PR #42313](https://github.com/leanprover-community/mathlib4/pull/42313).

## Main definitions

* `LaurentSeries.contract`: the exponent-congruence component of a Laurent series.
* `TauCeti.LaurentSeries.Level`: the level-`d` Laurent field with base map `X ↦ X ^ d`.
* `TauCeti.LaurentSeries.Level.powerBasis`: the power basis `1, u, ..., u ^ (d - 1)`.
* `TauCeti.puiseuxField.level`: the actual level-`d` intermediate field in the Puiseux field.
* `TauCeti.puiseuxField.levelPowerBasis`: its transported power basis.

## Main results

* `LaurentSeries.sum_single_mul_expand_contract`: reconstruction from congruence components.
* `LaurentSeries.contract_eq_of_sum_eq`: uniqueness of the congruence components.
* `TauCeti.puiseuxField.level_finrank`: level `d` has degree `d` over `K⸨X⸩`.
* `TauCeti.puiseuxField.isAlgebraic_laurentSeries`: every Puiseux series is algebraic over
  `K⸨X⸩`.
* `TauCeti.puiseuxField.level_le_level_iff`: level `n` lies in level `m` exactly when `n ∣ m`.
* `TauCeti.puiseuxField.level_inf_level`: levels `n` and `m` intersect in level `gcd n m`.
* `TauCeti.puiseuxField.level_sup_level`: levels `n` and `m` generate level `lcm n m`.
* `TauCeti.puiseuxField.iSup_level`: the levels exhaust the Puiseux field.
* `IntermediateField.exists_le_level`: a finite-dimensional intermediate field of the Puiseux
  field lies in a single level.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

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

/-- The generator of the level power basis is the level parameter. -/
@[simp]
theorem powerBasis_gen (K : Type*) [Field K] (d : ℕ+) :
    (powerBasis K d).gen = parameter K d := by
  simp only [powerBasis]

/-- The dimension of the level power basis is `d`. -/
@[simp]
theorem powerBasis_dim (K : Type*) [Field K] (d : ℕ+) :
    (powerBasis K d).dim = d := by
  rw [powerBasis]

/-- The basis underlying the level power basis is the congruence-class basis. -/
@[simp]
theorem powerBasis_basis (K : Type*) [Field K] (d : ℕ+) :
    (powerBasis K d).basis.reindex (finCongr (powerBasis_dim K d)) = basis K d := by
  simp only [powerBasis]
  ext i : 1
  rw [Module.Basis.reindex_apply]
  congr

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

/-- The abstract level embedding agrees with `puiseuxField.levelEmbedding` on the underlying
Laurent series. -/
@[simp]
theorem toPuiseux_apply (K : Type*) [Field K] (d : ℕ+) (f : Level K d) :
    toPuiseux K d f =
      TauCeti.puiseuxField.levelEmbedding K d (ringEquivLaurentSeries K d f) := by
  apply Subtype.ext
  rw [coe_toPuiseux, TauCeti.puiseuxField.coe_levelEmbedding]

end Level

end TauCeti.LaurentSeries

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

/-- The level equivalence is the level embedding after coercion to the Puiseux field. -/
@[simp]
theorem coe_levelEquiv_apply (K : Type*) [Field K] (d : ℕ+)
    (f : LaurentSeries.Level K d) :
    ((levelEquiv K d f : level K d) : TauCeti.puiseuxField K) =
      LaurentSeries.Level.toPuiseux K d f := by
  rw [levelEquiv]
  exact AlgHom.equivFieldRange_apply_coe (LaurentSeries.Level.toPuiseux K d) f

/-- The transported power basis of the actual level-`d` subfield of the Puiseux field. -/
noncomputable def levelPowerBasis (K : Type*) [Field K] (d : ℕ+) :
    PowerBasis K⸨X⸩ (level K d) :=
  (LaurentSeries.Level.powerBasis K d).map (levelEquiv K d)

/-- The generator of the actual level power basis is the image of the level parameter. -/
@[simp]
theorem levelPowerBasis_gen (K : Type*) [Field K] (d : ℕ+) :
    (levelPowerBasis K d).gen =
      levelEquiv K d (LaurentSeries.Level.parameter K d) := by
  rw [levelPowerBasis, PowerBasis.map_gen, LaurentSeries.Level.powerBasis_gen]

/-- The dimension of the actual level power basis is `d`. -/
@[simp]
theorem levelPowerBasis_dim (K : Type*) [Field K] (d : ℕ+) :
    (levelPowerBasis K d).dim = d := by
  rw [levelPowerBasis, PowerBasis.map_dim, LaurentSeries.Level.powerBasis_dim]

/-- The basis of the actual level is the transported congruence-class basis. -/
@[simp]
theorem levelPowerBasis_basis (K : Type*) [Field K] (d : ℕ+) :
    (levelPowerBasis K d).basis.reindex (finCongr (levelPowerBasis_dim K d)) =
      (LaurentSeries.Level.basis K d).map (levelEquiv K d).toLinearEquiv := by
  unfold levelPowerBasis LaurentSeries.Level.powerBasis
  ext i : 1
  rw [Module.Basis.reindex_apply]
  congr

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

/-- The generator of the level-`d` power basis is the monomial `t ^ (1 / d)`. -/
theorem coe_levelPowerBasis_gen (K : Type*) [Field K] (d : ℕ+) :
    (((levelPowerBasis K d).gen : TauCeti.puiseuxField K) : HahnSeries ℚ K) =
      HahnSeries.single (d⁻¹ : ℚ) 1 := by
  simp

/-- The level parameters are compatible: if `L = e * k`, then `(t ^ (1 / L)) ^ k = t ^ (1 / e)`. -/
theorem coe_levelPowerBasis_gen_pow (K : Type*) [Field K] {e L : ℕ+} {k : ℕ}
    (h : (L : ℕ) = e * k) :
    ((levelPowerBasis K L).gen : TauCeti.puiseuxField K) ^ k = (levelPowerBasis K e).gen := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_levelPowerBasis_gen, coe_levelPowerBasis_gen,
    HahnSeries.single_pow, one_pow]
  have hk : (k : ℚ) ≠ 0 := by
    have := L.ne_zero
    rw [h] at this
    exact_mod_cast right_ne_zero_of_mul this
  have hL : (L : ℚ) = e * k := by exact_mod_cast h
  rw [nsmul_eq_mul, hL]
  field_simp

/-- The generator `t ^ (1 / d)` of the level-`d` power basis is nonzero. -/
theorem levelPowerBasis_gen_ne_zero (K : Type*) [Field K] (d : ℕ+) :
    ((levelPowerBasis K d).gen : TauCeti.puiseuxField K) ≠ 0 := fun h ↦
  single_ne_zero (one_ne_zero (α := K)) (a := (d⁻¹ : ℚ)) <| by
    rw [← coe_levelPowerBasis_gen, h, ZeroMemClass.coe_zero]

/-- An intermediate field containing the generator `t ^ (1 / d)` contains level `d`. -/
theorem level_le_of_levelPowerBasis_gen_mem (K : Type*) [Field K] {d : ℕ+}
    {S : IntermediateField K⸨X⸩ (TauCeti.puiseuxField K)}
    (h : ((levelPowerBasis K d).gen : TauCeti.puiseuxField K) ∈ S) : level K d ≤ S := by
  intro x hx
  obtain ⟨f, hf⟩ := (levelPowerBasis K d).exists_eq_aeval' ⟨x, hx⟩
  have hx' : x = Polynomial.aeval ((levelPowerBasis K d).gen : TauCeti.puiseuxField K) f := by
    rw [IntermediateField.aeval_coe, ← hf]
  rw [hx']
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr h)
    (Polynomial.aeval_mem_adjoin_singleton _ _)

/-- For `n ∣ m`, level `n` is contained in level `m`. -/
theorem level_le_level_of_dvd (K : Type*) [Field K] {n m : ℕ+} (h : n ∣ m) :
    level K n ≤ level K m := fun x hx ↦ by
  rw [mem_level_iff] at hx ⊢
  exact range_levelEmbedding_le_of_dvd h hx

/-- Level `n` is contained in level `m` exactly when `n ∣ m`. -/
@[simp]
theorem level_le_level_iff (K : Type*) [Field K] {n m : ℕ+} :
    level K n ≤ level K m ↔ n ∣ m := by
  refine ⟨fun h ↦ ?_, level_le_level_of_dvd K⟩
  rw [← range_ramifiedEmbedding_le_iff (R := K)]
  intro x hx
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hx
  have hf := h ((mem_level_iff K n (levelEmbedding K n f)).mpr ⟨f, rfl⟩)
  rwa [mem_level_iff, mem_range_levelEmbedding_iff, coe_levelEmbedding] at hf

/-- Level one is the base field `K⸨X⸩`. -/
@[simp]
theorem level_one (K : Type*) [Field K] : level K 1 = ⊥ := by
  ext x
  simp only [mem_level_iff, IntermediateField.mem_bot, AlgHom.mem_range, Set.mem_range,
    algebraMap_laurentSeries_apply]

/-- The intersection of levels `n` and `m` is level `gcd n m`. -/
@[simp]
theorem level_inf_level (K : Type*) [Field K] (n m : ℕ+) :
    level K n ⊓ level K m = level K (n.gcd m) := by
  ext x
  rw [IntermediateField.mem_inf]
  simp only [mem_level_iff, mem_range_levelEmbedding_iff]
  rw [← Algebra.mem_inf, range_ramifiedEmbedding_inf]

/-- The compositum of levels `n` and `m` is level `lcm n m`. -/
@[simp]
theorem level_sup_level (K : Type*) [Field K] (n m : ℕ+) :
    level K n ⊔ level K m = level K (n.lcm m) := by
  refine le_antisymm (sup_le (level_le_level_of_dvd K (n.dvd_lcm_left m))
    (level_le_level_of_dvd K (n.dvd_lcm_right m))) (level_le_of_levelPowerBasis_gen_mem K ?_)
  -- Write `n = a * g` and `m = b * g` with `g = gcd n m` and `a`, `b` coprime, so that
  -- `lcm n m = n * b = m * a`. Then `u ^ b` and `u ^ a` are the parameters of levels `n` and `m`
  -- for the parameter `u` of level `lcm n m`, and a Bézout relation recovers `u`.
  obtain ⟨a, b, hab, hn, hm⟩ := Nat.exists_coprime (n : ℕ) m
  have hL : ((n.lcm m : ℕ+) : ℕ) = a * b * Nat.gcd n m := by
    rw [PNat.lcm_coe, ← hab.lcm_eq_mul, ← Nat.lcm_mul_right, ← hn, ← hm]
  have hLn : ((n.lcm m : ℕ+) : ℕ) = n * b := by rw [hL, mul_right_comm, ← hn]
  have hLm : ((n.lcm m : ℕ+) : ℕ) = m * a := by rw [hL, mul_comm a, mul_right_comm, ← hm]
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_eq_of_coprime (G := (TauCeti.puiseuxField K)ˣ) hab
  have hu := congrArg Units.val (hij (.mk0 _ (levelPowerBasis_gen_ne_zero K (n.lcm m))))
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    Units.val_mk0] at hu
  rw [← hu, coe_levelPowerBasis_gen_pow K hLm, coe_levelPowerBasis_gen_pow K hLn]
  exact mul_mem (zpow_mem (le_sup_right (a := level K n) (levelPowerBasis K m).gen.2) _)
    (zpow_mem (le_sup_left (a := level K n) (levelPowerBasis K n).gen.2) _)

/-- The levels exhaust the Puiseux field. -/
@[simp]
theorem iSup_level (K : Type*) [Field K] : ⨆ d : ℕ+, level K d = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨d, hd⟩ := exists_mem_range_levelEmbedding x
  exact le_iSup (level K) d ((mem_level_iff K d x).mpr hd)

end TauCeti.puiseuxField

namespace IntermediateField

open TauCeti.puiseuxField

/-- A finite-dimensional intermediate field of the Puiseux field over `K⸨X⸩` lies in a single
ramified level. -/
theorem exists_le_level {K : Type*} [Field K]
    (E : IntermediateField K⸨X⸩ (TauCeti.puiseuxField K)) [FiniteDimensional K⸨X⸩ E] :
    ∃ n : ℕ+, E ≤ level K n := by
  let b := Module.finBasis K⸨X⸩ E
  obtain ⟨n, hn⟩ := exists_forall_mem_range_levelEmbedding fun i ↦ (b i : TauCeti.puiseuxField K)
  refine ⟨n, fun x hx ↦ ?_⟩
  lift x to E using hx
  rw [← b.sum_repr x, coe_sum]
  exact sum_mem fun i _ ↦ smul_mem _ ((mem_level_iff K n _).mpr (hn i))

end IntermediateField
