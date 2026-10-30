/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# The maximal tamely ramified subextension

Let `L` be a finite subextension of the algebraic closure of a nonarchimedean local field `K` with
residue characteristic `p`, and write `e(L/K) = p ^ k e'` with `p ∤ e'`. The maximal tamely
ramified subextension of `L/K` is `Kᵗ ⊓ L`, where `Kᵗ` is the canonical maximal tamely ramified
extension. Its ramification index over `K` is the prime-to-`p` part `e'` of `e(L/K)`, its residue
degree is `f(L/K)`, and so its degree over `K` is `[L : K] / p ^ k`. No Galois or separability
hypothesis on `L/K` is needed.

The lower bound on the ramification index comes from a radical: for every uniformizer `π` of `K`,
some `α ∈ L` satisfies `α ^ e' = ω π` with `ω` a root of unity of order prime to `p`
(`TauCeti.exists_pow_ordCompl_ramificationIndex_eq_mul`), and such an `α` lies in `Kᵗ`.

When `L/K` is Galois, `Kᵗ ⊓ L` is also the fixed field of the first lower ramification group
`G₁(L/K)`. These statements accept any compatible local-field structures on `L` and on `Kᵗ ⊓ L`.

## Main results

* `IntermediateField.ramificationIndex_maximalTameExtension_inf`,
  `IntermediateField.inertiaDegree_maximalTameExtension_inf` and
  `IntermediateField.finrank_maximalTameExtension_inf`: the invariants of `Kᵗ ⊓ L` over `K`.
* `TauCeti.LocalFieldsRamification.finrank_fixedField_lowerRamificationGroup_one` and
  `IntermediateField.lift_fixedField_lowerRamificationGroup_one`: for `L/K` Galois, the fixed
  field of `G₁(L/K)` has degree `[L : K] / p ^ k` and lifts to `Kᵗ ⊓ L`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel TauCeti TauCeti.LocalFieldsRamification

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- The degree over the base of the field fixed by wild inertia is
`[L : K] / p ^ (v_p e(L/K))`. -/
theorem finrank_fixedField_lowerRamificationGroup_one :
    Module.finrank K (IntermediateField.fixedField (lowerRamificationGroup K L 1)) =
      Module.finrank K L /
        ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField, Subgroup.index_eq_card_div]
  rw [IsGalois.card_aut_eq_finrank, natCard_lowerRamificationGroup_one]

end TauCeti.LocalFieldsRamification

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Galois

variable (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- The fixed field of finite wild inertia, lifted to the algebraic closure, is the intersection
of `L` with the maximal tamely ramified extension. -/
@[simp]
theorem lift_fixedField_lowerRamificationGroup_one :
    lift (fixedField (lowerRamificationGroup K L 1)) =
      maximalTameExtension K (AlgebraicClosure K) ⊓ L := by
  rw [← map_wildInertiaSubgroup_restrictNormalHom L, wildInertiaSubgroup_def,
    ← InfiniteGalois.restrict_fixedField]
  -- In equal characteristic the absolute fixed field also contains purely inseparable elements;
  -- intersecting with the separable field `L` removes them.
  conv_lhs => rw [← inf_eq_right.mpr (le_separableClosure K _ L), ← inf_assoc,
    fixedField_fixingSubgroup_inf_separableClosure (le_separableClosure K _ _)]

end Galois

/-! ### Arbitrary finite subextensions -/

/-- An element of `L` with a power, of exponent prime to the residue characteristic, in `Kˣ` lies
in the maximal tamely ramified subextension of `L`. -/
private theorem coe_mem_maximalTameExtension_inf (L : IntermediateField K (AlgebraicClosure K))
    {m : ℕ} (hm : ¬ ringChar 𝓀[K] ∣ m) (a : Kˣ) {x : L} (hx : x ^ m = algebraMap K L a) :
    (x : AlgebraicClosure K) ∈ maximalTameExtension K (AlgebraicClosure K) ⊓ L :=
  ⟨mem_maximalTameExtension_of_pow_eq hm a (by simpa using congrArg Subtype.val hx), x.2⟩

variable (L : IntermediateField K (AlgebraicClosure K))
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

section Core

-- In the next three lemmas the field `T = Kᵗ ⊓ L` is a variable with its defining equation `hT`,
-- rather than a local definition, so that instance search finds its local-field structures.
variable (T : IntermediateField K (AlgebraicClosure K))
  [ValuativeRel T] [TopologicalSpace T] [IsNonarchimedeanLocalField T] [ValuativeExtension K T]

/-- The prime-to-`p` part `e'` of `e(L/K)` divides `e(T/K)` for `T = Kᵗ ⊓ L`. -/
private theorem ordCompl_ramificationIndex_dvd
    (hT : maximalTameExtension K (AlgebraicClosure K) ⊓ L = T) :
    ramificationIndex K L / ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K])
      ∣ ramificationIndex K T := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.prime_ringChar 𝓀[K]
  set e' := ramificationIndex K L / p ^ (ramificationIndex K L).factorization p
  have hq : ¬ p ∣ Nat.card 𝓀[L] - 1 := by
    rw [natCard_residueField K L]
    exact IsLocalRing.isUnit_natCast_iff_not_dvd.1
      (isUnit_natCast_natCard_pow_sub_one K inertiaDegree_pos.ne')
  -- Some `α ∈ L` has `α ^ e' = ω π`, for `π` a uniformizer of `K` and `ω` a root of unity.
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  obtain ⟨α, ω, hω, hα⟩ := exists_pow_ordCompl_ramificationIndex_eq_mul (L := L) hπ
  have hω1 : ω ^ (Nat.card 𝓀[L] - 1) = 1 := (mem_rootsOfUnity _ _).1 hω
  -- Both `ω` and `α` have powers, of exponent prime to `p`, in `Kˣ`, so they lie in `T`.
  have hω' : (ω : L) ^ (Nat.card 𝓀[L] - 1) = algebraMap K L ((1 : Kˣ) : K) := by
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val hω1
  have hα' : (α : L) ^ (e' * (Nat.card 𝓀[L] - 1)) =
      algebraMap K L ((π ^ (Nat.card 𝓀[L] - 1) : Kˣ) : K) := by
    have h := congrArg (fun u : Lˣ ↦ ((u ^ (Nat.card 𝓀[L] - 1) : Lˣ) : L)) hα
    simp only [← pow_mul, mul_pow, hω1, one_mul] at h
    simpa using h
  have hαT := hT ▸ coe_mem_maximalTameExtension_inf L (fun h ↦ ((Nat.Prime.dvd_mul hp).1 h).elim
    (Nat.not_dvd_ordCompl hp ramificationIndex_pos.ne') hq) _ hα'
  have hωT := hT ▸ coe_mem_maximalTameExtension_inf L hq _ hω'
  set a : T := ⟨_, hαT⟩
  set w : T := ⟨_, hωT⟩
  have ha : a ≠ 0 := fun h ↦ α.ne_zero (by simpa [a] using congrArg Subtype.val h)
  have hw : w ≠ 0 := fun h ↦ ω.ne_zero (by simpa [w] using congrArg Subtype.val h)
  have heq : Units.mk0 a ha ^ e' = Units.mk0 w hw * Units.map (algebraMap K T : K →* T) π := by
    refine Units.ext (Subtype.ext ?_)
    simpa [a, w] using congrArg (fun u : Lˣ ↦ ((u : L) : AlgebraicClosure K)) hα
  -- Taking valuations in `T`, the root of unity `ω` contributes nothing, so `e' v_T(α) = e(T/K)`.
  have hwpow : w ^ (Nat.card 𝓀[L] - 1) = 1 := by
    have h : (ω : L) ^ (Nat.card 𝓀[L] - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hω1, Units.val_one]
    exact Subtype.ext (by simpa [w] using congrArg Subtype.val h)
  have hwv : normalizedValuation T (Units.mk0 w hw) = 1 :=
    normalizedValuation_eq_one_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.2
      ⟨Nat.card 𝓀[L] - 1, Nat.sub_pos_of_lt Finite.one_lt_card, Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hwpow, Units.val_one])⟩)
  have h := congrArg (fun u ↦ (normalizedValuation T u).toAdd) heq
  simp only [map_pow, map_mul, hwv, normalizedValuation_algebraMap, (isUniformizer_def π).1 hπ,
    one_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one] at h
  exact Int.natCast_dvd_natCast.1 ⟨_, by rw [← h, mul_comm]⟩

/-- `f(L/K)` divides `f(T/K)` for `T = Kᵗ ⊓ L`. -/
private theorem inertiaDegree_dvd (hT : maximalTameExtension K (AlgebraicClosure K) ⊓ L = T) :
    inertiaDegree K L ∣ inertiaDegree K T := by
  have hTL : T ≤ L := hT ▸ inf_le_right
  -- `T` contains a primitive `(q ^ f(L/K) - 1)`-st root of unity of `L`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  have hζT := hT ▸ coe_mem_maximalTameExtension_inf L
    (IsLocalRing.isUnit_natCast_iff_not_dvd.1
      (isUnit_natCast_natCard_pow_sub_one K inertiaDegree_pos.ne')) 1
    (x := ζ) (by simpa using hζ.pow_eq_one)
  exact dvd_inertiaDegree_of_isPrimitiveRoot inertiaDegree_pos.ne'
    (hζ.of_map_of_injective (f := inclusion hTL) (ζ := ⟨_, hζT⟩) (inclusion_injective hTL))

/-- The ramification index and the residue degree of `T = Kᵗ ⊓ L` over `K` are the prime-to-`p`
part of `e(L/K)` and `f(L/K)`. -/
private theorem ramificationIndex_eq_and_inertiaDegree_eq
    (hT : maximalTameExtension K (AlgebraicClosure K) ⊓ L = T) :
    ramificationIndex K T =
        ramificationIndex K L /
          ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) ∧
      inertiaDegree K T = inertiaDegree K L := by
  have := finite_of_valuativeExtension K T
  have hTL : T ≤ L := hT ▸ inf_le_right
  let _ : Algebra T L := (inclusion hTL).toAlgebra
  have : IsScalarTower K T L := .of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension T L := (inclusion hTL).valuativeExtension
  -- `T` is separable and lies in `Kᵗ`, so it is tamely ramified; hence `e(T/K) ∣ e'`, while
  -- `f(T/K) ∣ f(L/K)` holds for any intermediate field.
  have hTt : T ≤ maximalTameExtension K (AlgebraicClosure K) := hT ▸ inf_le_left
  have : Algebra.IsSeparable K T :=
    (le_separableClosure_iff K _ T).1 (hTt.trans (le_separableClosure K _ _))
  have htame : IsTamelyRamified K T := (le_maximalTameExtension_iff T).1 hTt
  refine ⟨Nat.dvd_antisymm ?_ (ordCompl_ramificationIndex_dvd L T hT),
    Nat.dvd_antisymm ?_ (inertiaDegree_dvd L T hT)⟩
  · exact Nat.dvd_ordCompl_of_dvd_not_dvd
      (Dvd.intro _ (ramificationIndex_tower (K := K) (L := T) L).symm)
      ((isTamelyRamified_iff K T).1 htame)
  · exact Dvd.intro _ (inertiaDegree_tower (K := K) (L := T) L).symm

end Core

section Structure

variable [ValuativeRel ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L)]
  [TopologicalSpace ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L)]
  [IsNonarchimedeanLocalField ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L)]
  [ValuativeExtension K ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L)]

/-- **The ramification index of the maximal tamely ramified subextension.** For a finite
subextension `L` of `K^{alg}/K`, the ramification index of `Kᵗ ⊓ L` over `K` is the prime-to-`p`
part `e(L/K) / p ^ (v_p e(L/K))` of `e(L/K)`, where `p` is the residue characteristic. -/
@[simp]
theorem ramificationIndex_maximalTameExtension_inf :
    ramificationIndex K ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L) =
      ramificationIndex K L /
        ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) :=
  (ramificationIndex_eq_and_inertiaDegree_eq L _ rfl).1

/-- **The residue degree of the maximal tamely ramified subextension.** For a finite subextension
`L` of `K^{alg}/K`, the residue degree of `Kᵗ ⊓ L` over `K` is that of `L`. -/
@[simp]
theorem inertiaDegree_maximalTameExtension_inf :
    inertiaDegree K ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L) = inertiaDegree K L :=
  (ramificationIndex_eq_and_inertiaDegree_eq L _ rfl).2

end Structure

/-- **The degree of the maximal tamely ramified subextension.** For a finite subextension `L` of
`K^{alg}/K`, not necessarily Galois or separable, the degree of `Kᵗ ⊓ L` over `K` is
`[L : K] / p ^ (v_p e(L/K))`, where `p` is the residue characteristic. -/
@[simp]
theorem finrank_maximalTameExtension_inf :
    Module.finrank K ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L) =
      Module.finrank K L /
        ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  obtain ⟨T, hT⟩ : ∃ T, maximalTameExtension K (AlgebraicClosure K) ⊓ L = T := ⟨_, rfl⟩
  rw [hT]
  have := finite_of_valuativeExtension K L
  have hTL : T ≤ L := hT ▸ inf_le_right
  have : Module.Finite K T :=
    .of_injective (inclusion hTL).toLinearMap (inclusion_injective hTL)
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) T
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) T
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) T
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) T
  obtain ⟨he, hf⟩ := ramificationIndex_eq_and_inertiaDegree_eq L T hT
  rw [← ramificationIndex_mul_inertiaDegree K T, ← ramificationIndex_mul_inertiaDegree K L, he, hf,
    Nat.div_mul_right_comm (Nat.ordProj_dvd _ _)]

end IntermediateField
