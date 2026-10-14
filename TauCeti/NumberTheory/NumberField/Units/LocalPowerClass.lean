/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.Kummer.LocalUnit
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit
import TauCeti.RingTheory.Valuation.UnitGroup

/-!
# Local power classes of S-units

For disjoint sets of finite places `S` and `T`, an `S`-unit determines a unit power class
at each place of `T`. The resulting homomorphism has kernel consisting of the `S`-units
that are powers in all these completions.

If a Galois extension contains the radicals of the `S`-units and the Frobenius elements
at `T` generate the subgroup fixing `L`, this kernel is exactly the `S`-units that are
powers in `L`. This identifies the source quotient in the counting proof of local
power-class surjectivity with the quotient used by Kummer theory.

The local target uses the depth-zero unit filtration, so it retains only unit classes;
the valuation classes of the completion are excluded.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemmas 6.3 and 6.9.
-/

public noncomputable section

open IsDedekindDomain NumberField TauCeti

namespace Set

variable {K : Type*} [Field K] [NumberField K]
  (S T : Set (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)

/-- The product of the local unit `n`-th power-class groups at the places of `T`. -/
abbrev UnitLocalPowerClasses (n : ℕ) :=
  (v : T) → unitFiltration (v.1.adicCompletion K) 0 ⧸
    (powMonoidHom n : unitFiltration (v.1.adicCompletion K) 0 →* _).range

/-- The homomorphism taking an `S`-unit to its unit `n`-th power classes at the places of
`T`. Disjointness ensures that every coordinate is a local unit. -/
def unitLocalPowerClassMap (n : ℕ) :
    -- Use the group projections explicitly so consumers can infer the group structures
    -- when applying `MonoidHom.range` to this dependent-product-valued homomorphism.
    @MonoidHom (S.unit K) (UnitLocalPowerClasses T n)
      (inferInstance : Group (S.unit K)).toMulOne
      (inferInstance : Group (UnitLocalPowerClasses T n)).toMulOne :=
  MonoidHom.pi fun v ↦ (QuotientGroup.mk' _).comp
    (((Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom).comp
      (S.unit K).subtype).codRestrict (unitFiltration (v.1.adicCompletion K) 0)
      fun u ↦ (v.1.unitsMap_algebraMap_mem_unitFiltration_zero_iff u.1).mpr
        (Set.unit_valuation_eq_one S K u fun hv ↦ Set.disjoint_left.mp hST hv v.2))

/-- A coordinate of the local power-class map is the class of the corresponding local unit. -/
@[simp]
theorem unitLocalPowerClassMap_apply (n : ℕ) (u : S.unit K) (v : T) :
    unitLocalPowerClassMap S T hST n u v =
      QuotientGroup.mk (⟨Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u.1,
        (v.1.unitsMap_algebraMap_mem_unitFiltration_zero_iff u.1).mpr
          (Set.unit_valuation_eq_one S K u fun hv ↦ Set.disjoint_left.mp hST hv v.2)⟩ :
        unitFiltration (v.1.adicCompletion K) 0) := (rfl)

/-- An `S`-unit has trivial local power classes exactly when it has an `n`-th root in
every completion indexed by `T`. -/
theorem unitLocalPowerClassMap_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : S.unit K) :
    unitLocalPowerClassMap S T hST n u = 1 ↔
      ∀ v : T, ∃ b : v.1.adicCompletion K,
        b ^ n = algebraMap K (v.1.adicCompletion K) (u : Kˣ) := by
  have : NeZero n := ⟨hn⟩
  rw [funext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [unitLocalPowerClassMap_apply, Pi.one_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.1, congrArg (fun x : unitFiltration (v.1.adicCompletion K) 0 ↦
      ((x : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)) hb⟩
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := ne_zero_of_pow_eq_algebraMap hb
    let b' : (v.1.adicCompletion K)ˣ := Units.mk0 b hb0
    have hpow : b' ^ n = Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u.1 :=
      Units.ext hb
    have hunit : b' ∈ unitFiltration (v.1.adicCompletion K) 0 := by
      rw [unitFiltration_zero]
      apply ((ValuativeRel.valuation (v.1.adicCompletion K)).pow_mem_unitGroup_iff hn).mp
      rw [← unitFiltration_zero, hpow]
      exact (v.1.unitsMap_algebraMap_mem_unitFiltration_zero_iff u.1).mpr
        (Set.unit_valuation_eq_one S K u fun hv ↦ Set.disjoint_left.mp hST hv v.2)
    exact ⟨⟨b', hunit⟩, Subtype.ext hpow⟩

variable {M : Type*} [Field M] [Algebra K M] [IsGalois K M]

open TauCeti.NumberField in
/-- **The kernel of the S-unit local power-class map.** Suppose `M` contains an `n`-th
root of every `S`-unit, and Frobenius elements at the places of `T` generate
`Gal(M/L)`. Then an `S`-unit lies in the kernel precisely when its image in `L` is
an `n`-th power. Neither set of places is required to be finite. -/
theorem ker_unitLocalPowerClassMap {n : ℕ} (hn : n ≠ 0)
    (L : IntermediateField K M) (σ : T → M ≃ₐ[K] M) (Q : T → Ideal (𝓞 M))
    [∀ v, (Q v).IsPrime] [∀ v : T, (Q v).LiesOver v.1.asIdeal]
    (hσ : ∀ v, IsArithFrobAt (𝓞 K) (σ v) (Q v))
    (hL : L.fixingSubgroup = Subgroup.closure (Set.range σ))
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ n) (havoid : ∀ v : T, (n : 𝓞 K) ∉ v.1.asIdeal)
    (hroots : ∀ a ∈ S.unit K, ∃ α : M, α ^ n = algebraMap K M (a : K)) :
    (unitLocalPowerClassMap S T hST n).ker =
      ((powMonoidHom n : Lˣ →* Lˣ).range.comap
        (Units.map (algebraMap K L).toMonoidHom)).subgroupOf (S.unit K) := by
  have : NeZero n := ⟨hn⟩
  ext u
  rw [MonoidHom.mem_ker, unitLocalPowerClassMap_eq_one_iff S T hST hn,
    Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_range]
  obtain ⟨α, hα⟩ := hroots u.1 u.2
  rw [← exists_mem_intermediateField_pow_eq_iff_forall_exists_pow_eq_adicCompletion
    hσ hL hζ havoid
    (fun v ↦ Set.unit_valuation_eq_one S K u fun hv ↦ Set.disjoint_left.mp hST hv v.2) hα]
  constructor
  · rintro ⟨β, hβ, hpow⟩
    have hβ0 : β ≠ 0 := ne_zero_of_pow_eq_algebraMap hpow
    refine ⟨Units.mk0 (⟨β, hβ⟩ : L)
      (fun h ↦ hβ0 (congrArg (fun x : L ↦ (x : M)) h)), ?_⟩
    apply Units.ext
    exact Subtype.ext hpow
  · rintro ⟨β, hβ⟩
    exact ⟨β, (β : L).2, congrArg (fun x : Lˣ ↦ ((x : L) : M)) hβ⟩

end Set
