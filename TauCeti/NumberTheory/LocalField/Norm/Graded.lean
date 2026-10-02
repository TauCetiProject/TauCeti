/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
public import TauCeti.NumberTheory.LocalField.Norm.Herbrand
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Uniformizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.NumberTheory.LocalField.Norm.PrimeDegree
import TauCeti.NumberTheory.LocalField.TamelyRamified
import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# The norm on the graded pieces of the unit filtration

Let `L/K` be a finite Galois extension of nonarchimedean local fields, and let
`ψℕ_{L/K} : ℕ → ℕ` be its integral inverse Herbrand function. The norm carries
`U(L, ψℕ_{L/K}(v))` into `U(K, v)` and `U(L, ψℕ_{L/K}(v) + 1)` into `U(K, v + 1)`, so it induces
a homomorphism of graded pieces

`normGradedMap K L v : U(L, ψℕ_{L/K}(v)) / U(L, ψℕ_{L/K}(v) + 1) →* U(K, v) / U(K, v + 1)`.

For a Galois extension of prime degree these maps compare the unit filtrations of `L` and `K`
step by step, and the orders of their kernels and cokernels are what the conductor and the
Hasse–Arf theorem are computed from. This file computes them away from the break and at a
positive break.

*Depth zero.* For a totally ramified Galois extension of degree `n`, `ψℕ_{L/K}(0) = 0`, both
graded pieces are the multiplicative groups of the residue fields, and these residue fields
coincide. Every element of the Galois group lies in the inertia group, so it acts trivially on the
residue field, and the norm `N(u) = ∏_σ σ(u)` of a unit `u` reduces to `ū ^ n`. Thus
`normGradedMap K L 0` is the `n`-th power map of the cyclic group `𝓀ˣ` of order `q - 1`, and its
kernel and cokernel both have order `gcd(q - 1, n)`. If `L/K` is tamely ramified, then `n`
divides `q - 1`, because the inertia group, of order `n`, embeds into `𝓀ˣ` through the tame
character; so the kernel and the cokernel have order `n`. If instead `G_1 = Gal(L/K)`, then `n`
is a power of the residue characteristic `p`, which is prime to `q - 1`, and the map is bijective.

*Before the break.* Let `L/K` have prime degree and let `v > 0` satisfy `G_{v+1} = Gal(L/K)`.
Then `ψℕ_{L/K}(v) = v`, and Hilbert's formula gives `d(L/K) ≥ (v + 2)([L : K] - 1)`, so the trace
carries `𝓂[L] ^ v` into `𝓂[K] ^ (v + 1)`. In the expansion
`N(1 + z) = 1 + Tr(z) + Tr(y) + N(z)` of `TauCeti.exists_norm_one_add_eq_of_mem_maximalIdeal_pow`
only `N(z)` survives modulo `𝓂[K] ^ (v + 1)`, and the norm preserves valuations in a totally
ramified extension. So `normGradedMap K L v` is injective, and it is bijective because both graded
pieces have `q` elements.

*At the break.* Let `L/K` have prime degree `ℓ`, let `t > 0` satisfy `G_t = Gal(L/K)`, and let
`σ ∉ G_{t+1}`, so that `σ π - π = γ π ^ (t + 1)` for a uniformizer `π` of `L` and an integer `γ`
whose residue `c` is nonzero. Coordinatize `U(L, t) / U(L, t + 1)` by `π` and
`U(K, t) / U(K, t + 1)` by `N(π)`. Here `ψℕ_{L/K}(t) = t`, and the trace carries `𝓂[L] ^ (t + 1)`
into `𝓂[K] ^ (t + 1)`, so the expansion of `N(1 + a π ^ t)` gives the class of
`a ^ ℓ + β a` for a constant `β`, the residue of `Tr(π ^ t) / N(π) ^ t`. The unit `σ π / π` has
coordinate `c` and norm `1`, so `c ^ ℓ + β c = 0`, which forces `β = -c ^ (ℓ - 1)`: the graded norm
is `y ↦ y ^ ℓ - c ^ (ℓ - 1) y`. When `t` is the break of the filtration, the Galois group is
`G_1`, a `p`-group of order `ℓ`, so `ℓ = p`, and the kernel of this map is the line `𝔽_ℓ c`. Hence
the kernel and the cokernel of `normGradedMap K L t` both have order `ℓ`.

## Main definitions

* `TauCeti.normGradedMap`: the homomorphism of graded pieces induced by the norm.

## Main results

* `TauCeti.algebraMap_residue_norm_of_isTotallyRamified`: in a totally ramified Galois extension
  of degree `n`, the norm of an integer `z` reduces to the `n`-th power of the residue of `z`.
* `TauCeti.algebraMap_unitFiltrationGradedZeroEquivResidueFieldUnits_normGradedMap_mk`: the
  depth-zero graded norm is the `n`-th power map on residue units.
* `TauCeti.natCard_ker_normGradedMap_zero` and `TauCeti.index_range_normGradedMap_zero`: its
  kernel and its cokernel have order `gcd(q - 1, n)`; `TauCeti.normGradedMap_zero_bijective_iff`:
  it is bijective exactly when `n` is prime to `q - 1`.
* `TauCeti.normGradedMap_tame_break_zero`: in the tame case both have order `n`.
* `TauCeti.normGradedMap_zero_bijective_of_lowerRamificationGroup_one_eq_top`: if
  `G_1 = Gal(L/K)`, the depth-zero graded norm is bijective.
* `TauCeti.normGradedMap_bijective_of_lowerRamificationGroup_eq_top`: in prime degree, the graded
  norm at depth `v` is bijective whenever `G_{v+1} = Gal(L/K)`.
* `TauCeti.normGradedMap_zero_before_break` and `TauCeti.normGradedMap_positive_before_break`: in
  prime degree with an upper break at a natural number `t`, the graded norm is bijective at every
  depth `v < t`.
* `TauCeti.algebraMap_residue_eq_of_norm_one_add_mul_pow_eq` and
  `TauCeti.algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk`: in
  prime degree, at a positive depth `t` with `G_t = Gal(L/K)` and for `σ ∉ G_{t+1}`, the graded
  norm is `y ↦ y ^ ℓ - c ^ (ℓ - 1) y`, where `c` is the coordinate of `σ π / π`.
* `TauCeti.normGradedMap_at_break`: in prime degree `ℓ` with an upper break at a natural number
  `t > 0`, the kernel and the cokernel of the graded norm at depth `t` both have order `ℓ`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3 (Lemmas 4 and 5, Proposition 5).
-/

public section
noncomputable section

open ValuativeRel IsLocalRing Module TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-! ### The graded norm map -/

variable (K L) in
/-- **The norm on the Herbrand-shifted graded pieces of the unit filtration.** For a finite
Galois extension `L/K` of nonarchimedean local fields, the norm induces a homomorphism
`U(L, ψℕ_{L/K}(v)) / U(L, ψℕ_{L/K}(v) + 1) →* U(K, v) / U(K, v + 1)`, by the Herbrand-shifted
inclusions `TauCeti.map_normUnits_unitFiltration_psiNat_le` and
`TauCeti.map_normUnits_unitFiltration_psiNat_add_one_le`. -/
def normGradedMap (v : ℕ) :
    UnitFiltrationGraded L (psiNat K L v) →* UnitFiltrationGraded K v :=
  QuotientGroup.map _ _
    (((Algebra.normUnits K).comp (unitFiltration L (psiNat K L v)).subtype).codRestrict
      (unitFiltration K v) fun x ↦
        map_normUnits_unitFiltration_psiNat_le K L v (Subgroup.mem_map_of_mem _ x.2))
    fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact map_normUnits_unitFiltration_psiNat_add_one_le K L v (Subgroup.mem_map_of_mem _ hx)

/-- The graded norm map sends the class of `x` to the class of its norm. -/
@[simp]
theorem normGradedMap_mk {v : ℕ} (x : unitFiltration L (psiNat K L v)) :
    normGradedMap K L v (QuotientGroup.mk x) =
      QuotientGroup.mk ⟨Algebra.normUnits K (x : Lˣ),
        map_normUnits_unitFiltration_psiNat_le K L v (Subgroup.mem_map_of_mem _ x.2)⟩ := by
  rw [normGradedMap, QuotientGroup.map_mk, MonoidHom.codRestrict_apply]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]

/-! ### The norm modulo the maximal ideal in a totally ramified extension -/

/-- **The norm modulo the maximal ideal in a totally ramified extension.** If `L/K` is a totally
ramified Galois extension of nonarchimedean local fields, the norm of an integer `z` of `L`
reduces to the `[L : K]`-th power of the residue of `z`: every conjugate of `z` has the residue
of `z`. -/
theorem algebraMap_residue_norm_of_isTotallyRamified (h : IsTotallyRamified K L) (z : 𝒪[L]) :
    algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] (Algebra.norm 𝒪[K] z)) =
      residue 𝒪[L] z ^ finrank K L := by
  have hσ (σ : L ≃ₐ[K] L) : residue 𝒪[L] (σ • z) = residue 𝒪[L] z := by
    have hσ : σ ∈ lowerRamificationGroup K L 0 := by
      rw [(lowerRamificationGroup_zero_eq_top_iff K L).2 h]
      exact Subgroup.mem_top σ
    rw [lowerRamificationGroup_def] at hσ
    exact TauCeti.IsLocalRing.residue_smul_eq_of_mem_ramificationGroup_zero _ _ hσ z
  rw [ResidueField.algebraMap_residue, algebraMap_norm_integerRing_eq_prod_automorphisms]
  simp only [map_prod, hσ, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-! ### The graded norm at depth zero -/

/-- Graded pieces of the unit filtration at equal depths are isomorphic. -/
private def unitFiltrationGradedCongr {i j : ℕ} (h : i = j) :
    UnitFiltrationGraded L i ≃* UnitFiltrationGraded L j := by
  subst h
  exact MulEquiv.refl _

private theorem unitFiltrationGradedCongr_mk {i j : ℕ} (h : i = j) (x : unitFiltration L i) :
    unitFiltrationGradedCongr h (QuotientGroup.mk x) = QuotientGroup.mk ⟨x, h ▸ x.2⟩ := by
  subst h
  rfl

/-- **The graded norm at depth zero is the `[L : K]`-th power map.** For a totally ramified Galois
extension `L/K` of nonarchimedean local fields, read through the identifications of the depth-zero
graded pieces with the residue units, the norm sends the class of a unit `x` of `𝒪[L]` to the
`[L : K]`-th power of its residue. -/
theorem algebraMap_unitFiltrationGradedZeroEquivResidueFieldUnits_normGradedMap_mk
    (h : IsTotallyRamified K L) (x : unitFiltration L (psiNat K L 0)) :
    algebraMap 𝓀[K] 𝓀[L]
        (unitFiltrationGradedZeroEquivResidueFieldUnits (normGradedMap K L 0 (QuotientGroup.mk x)))
      = residue 𝒪[L] (unitFiltrationToIntegerUnits _ x : 𝒪[L]) ^ finrank K L := by
  rw [normGradedMap_mk, coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk,
    ← algebraMap_residue_norm_of_isTotallyRamified h]
  congr 2
  apply Subtype.ext
  rw [coe_norm_integerRing, coe_unitFiltrationToIntegerUnits, coe_unitFiltrationToIntegerUnits,
    Algebra.coe_normUnits]

/-- The residue fields of a totally ramified extension coincide. -/
private def residueFieldUnitsEquiv (h : IsTotallyRamified K L) : 𝓀[K]ˣ ≃* 𝓀[L]ˣ := by
  have hbij : Function.Bijective (algebraMap 𝓀[K] 𝓀[L]) :=
    ⟨(algebraMap 𝓀[K] 𝓀[L]).injective,
      (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 h⟩
  exact Units.mapEquiv (RingEquiv.ofBijective (algebraMap 𝓀[K] 𝓀[L]) hbij).toMulEquiv

omit [Module.Finite K L] [IsGalois K L] in
private theorem coe_residueFieldUnitsEquiv (h : IsTotallyRamified K L) (u : 𝓀[K]ˣ) :
    (residueFieldUnitsEquiv h u : 𝓀[L]) = algebraMap 𝓀[K] 𝓀[L] u := by
  simp only [residueFieldUnitsEquiv, Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe,
    RingEquiv.coe_toMulEquiv]
  exact RingEquiv.ofBijective_apply _ _ _

/-- The depth-zero graded piece of `L` at the Herbrand depth `ψℕ_{L/K}(0) = 0`, as the residue
units of `L`. -/
private def sourceEquiv : UnitFiltrationGraded L (psiNat K L 0) ≃* 𝓀[L]ˣ :=
  (unitFiltrationGradedCongr (psiNat_zero K L)).trans unitFiltrationGradedZeroEquivResidueFieldUnits

/-- The depth-zero graded piece of `K`, as the residue units of `L`. -/
private def targetEquiv (h : IsTotallyRamified K L) : UnitFiltrationGraded K 0 ≃* 𝓀[L]ˣ :=
  unitFiltrationGradedZeroEquivResidueFieldUnits.trans (residueFieldUnitsEquiv h)

/-- Read in the residue units of `L` on both sides, the depth-zero graded norm is the
`[L : K]`-th power map. -/
private theorem targetEquiv_comp_normGradedMap_zero (h : IsTotallyRamified K L) :
    (targetEquiv h : UnitFiltrationGraded K 0 →* 𝓀[L]ˣ).comp (normGradedMap K L 0) =
      (powMonoidHom (finrank K L)).comp (sourceEquiv (K := K) (L := L) : _ →* 𝓀[L]ˣ) := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ Units.ext ?_)
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MonoidHom.coe_ofClass,
    powMonoidHom_apply, Units.val_pow_eq_pow_val]
  simp only [targetEquiv, MulEquiv.trans_apply, coe_residueFieldUnitsEquiv]
  rw [algebraMap_unitFiltrationGradedZeroEquivResidueFieldUnits_normGradedMap_mk h]
  simp only [sourceEquiv, MulEquiv.trans_apply, unitFiltrationGradedCongr_mk,
    coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk]
  refine congrArg (fun z : 𝒪[L] ↦ residue 𝒪[L] z ^ finrank K L) (Subtype.ext ?_)
  simp only [coe_unitFiltrationToIntegerUnits]

/-- Transporting along the residue-unit identifications, the kernel of the depth-zero graded norm
has the order of the kernel of the `[L : K]`-th power map on `𝓀[L]ˣ`. -/
private theorem natCard_ker_normGradedMap_zero_eq (h : IsTotallyRamified K L) :
    Nat.card (normGradedMap K L 0).ker =
      Nat.card (powMonoidHom (finrank K L) : 𝓀[L]ˣ →* 𝓀[L]ˣ).ker := by
  rw [← MonoidHom.ker_mulEquiv_comp _ (targetEquiv h), targetEquiv_comp_normGradedMap_zero h,
    MonoidHom.ker_comp_mulEquiv]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

/-- Transporting along the residue-unit identifications, the image of the depth-zero graded norm
has the index of the image of the `[L : K]`-th power map on `𝓀[L]ˣ`. -/
private theorem index_range_normGradedMap_zero_eq (h : IsTotallyRamified K L) :
    (normGradedMap K L 0).range.index =
      (powMonoidHom (finrank K L) : 𝓀[L]ˣ →* 𝓀[L]ˣ).range.index := by
  have hrange :
      (normGradedMap K L 0).range.map (targetEquiv h : UnitFiltrationGraded K 0 →* 𝓀[L]ˣ) =
      (powMonoidHom (finrank K L) : 𝓀[L]ˣ →* 𝓀[L]ˣ).range := by
    rw [← MonoidHom.range_comp, targetEquiv_comp_normGradedMap_zero h, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulEquiv.surjective _), ← MonoidHom.range_eq_map]
  rw [← hrange, Subgroup.index_map_equiv]

omit [Module.Finite K L] [IsGalois K L] in
/-- The residue units of a totally ramified extension have `q - 1` elements, where `q` is the
cardinality of the residue field of the base. -/
private theorem natCard_residueField_units (h : IsTotallyRamified K L) :
    Nat.card 𝓀[L]ˣ = Nat.card 𝓀[K] - 1 := by
  simp [Nat.card_units, natCard_residueField K L, h.inertiaDegree_eq_one]

/-- **The kernel of the graded norm at depth zero.** For a totally ramified Galois extension `L/K`
of nonarchimedean local fields, with residue field of cardinality `q`, the kernel of
`normGradedMap K L 0` has order `gcd(q - 1, [L : K])`. -/
theorem natCard_ker_normGradedMap_zero (h : IsTotallyRamified K L) :
    Nat.card (normGradedMap K L 0).ker = (Nat.card 𝓀[K] - 1).gcd (finrank K L) := by
  rw [natCard_ker_normGradedMap_zero_eq h, IsCyclic.card_powMonoidHom_ker,
    natCard_residueField_units h]

/-- **The cokernel of the graded norm at depth zero.** For a totally ramified Galois extension
`L/K` of nonarchimedean local fields, with residue field of cardinality `q`, the image of
`normGradedMap K L 0` has index `gcd(q - 1, [L : K])`. -/
theorem index_range_normGradedMap_zero (h : IsTotallyRamified K L) :
    (normGradedMap K L 0).range.index = (Nat.card 𝓀[K] - 1).gcd (finrank K L) := by
  rw [index_range_normGradedMap_zero_eq h, IsCyclic.index_powMonoidHom_range,
    natCard_residueField_units h]

/-- **The graded norm at depth zero is bijective exactly in the coprime case.** For a totally
ramified Galois extension `L/K` of nonarchimedean local fields, with residue field of cardinality
`q`, the map `normGradedMap K L 0` is bijective if and only if `[L : K]` is prime to `q - 1`. -/
theorem normGradedMap_zero_bijective_iff (h : IsTotallyRamified K L) :
    Function.Bijective (normGradedMap K L 0) ↔ (finrank K L).Coprime (Nat.card 𝓀[K] - 1) := by
  have hcop : (finrank K L).Coprime (Nat.card 𝓀[K] - 1) ↔
      (Nat.card 𝓀[K] - 1).gcd (finrank K L) = 1 := by
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
  have hinj : Function.Injective (normGradedMap K L 0) ↔
      Nat.card (normGradedMap K L 0).ker = 1 := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.card_eq_one]
  have hsurj : Function.Surjective (normGradedMap K L 0) ↔
      (normGradedMap K L 0).range.index = 1 := by
    rw [← MonoidHom.range_eq_top, Subgroup.index_eq_one]
  rw [Function.Bijective, hinj, hsurj, natCard_ker_normGradedMap_zero h,
    index_range_normGradedMap_zero h, hcop, and_self]

/-! ### The tame case -/

/-- In a totally and tamely ramified Galois extension the degree divides `q - 1`. -/
private theorem finrank_dvd_card_residueField_sub_one (h : IsTotallyRamified K L)
    (ht : IsTamelyRamified K L) : finrank K L ∣ Nat.card 𝓀[K] - 1 := by
  have hdvd := ht.ramificationIndex_dvd_card_residueField_sub_one
  rwa [(isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 h, natCard_residueField K L,
    h.inertiaDegree_eq_one, pow_one] at hdvd

/-- **The tame break at zero.** For a totally and tamely ramified Galois extension `L/K` of
nonarchimedean local fields, the kernel of the graded norm `normGradedMap K L 0` has order
`[L : K]`, and its image has index `[L : K]`. In prime degree this is the regime `v = t = 0`, the
tame case, in which the unique break `t` of the ramification filtration is `0`. -/
theorem normGradedMap_tame_break_zero (h : IsTotallyRamified K L) (ht : IsTamelyRamified K L) :
    Nat.card (normGradedMap K L 0).ker = finrank K L ∧
      (normGradedMap K L 0).range.index = finrank K L := by
  rw [natCard_ker_normGradedMap_zero h, index_range_normGradedMap_zero h,
    Nat.gcd_eq_right (finrank_dvd_card_residueField_sub_one h ht), and_self]

/-! ### Before the break -/

/-- **Depth zero in a totally wildly ramified extension.** If the first ramification group of a
finite Galois extension `L/K` of nonarchimedean local fields is the whole Galois group,
`G_1 = Gal(L/K)`, then the graded norm `normGradedMap K L 0` is bijective: `L/K` is then totally
ramified of degree a power of the residue characteristic `p`, which is prime to `q - 1`. -/
theorem normGradedMap_zero_bijective_of_lowerRamificationGroup_one_eq_top
    (hG : lowerRamificationGroup K L 1 = ⊤) : Function.Bijective (normGradedMap K L 0) := by
  have h : IsTotallyRamified K L := (lowerRamificationGroup_zero_eq_top_iff K L).1 <|
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L zero_le_one)
  have hqKL : Nat.card 𝓀[K] = Nat.card 𝓀[L] := by
    rw [natCard_residueField K L, h.inertiaDegree_eq_one, pow_one]
  rw [normGradedMap_zero_bijective_iff h, hqKL]
  let _ := Fintype.ofFinite 𝓀[L]
  set p := ringChar 𝓀[L]
  have : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  -- The Galois group is `G_1`, a `p`-group, so `[L : K]` is a power of `p`.
  have hpG := isPGroup_ramificationGroup (L := L) (L ≃ₐ[K] L) p (i := 1) one_pos
  rw [← lowerRamificationGroup_def, hG] at hpG
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpG
  rw [Subgroup.card_top, IsGalois.card_aut_eq_finrank] at hk
  obtain ⟨d, -, hd⟩ := FiniteField.card 𝓀[L] p
  have hq : p ∣ Nat.card 𝓀[L] := by
    rw [Nat.card_eq_fintype_card, hd]
    exact dvd_pow_self p d.ne_zero
  rw [hk]
  have hqpos : 1 ≤ Nat.card 𝓀[L] := Nat.card_pos
  exact Nat.Coprime.pow_left k <| Nat.Coprime.of_dvd_left hq <|
    (Nat.coprime_self_sub_right hqpos).2 (by simp)

/-- **Before the break, the graded norm is bijective.** Let `L/K` be a Galois extension of
nonarchimedean local fields of prime degree, and let `v : ℕ` lie strictly before the break of its
lower ramification filtration, `G_{v+1} = Gal(L/K)`. Then the graded norm `normGradedMap K L v`
is bijective. -/
theorem normGradedMap_bijective_of_lowerRamificationGroup_eq_top
    (hℓ : (finrank K L).Prime) {v : ℕ} (hG : lowerRamificationGroup K L (v + 1) = ⊤) :
    Function.Bijective (normGradedMap K L v) := by
  rcases v with _ | v
  · exact normGradedMap_zero_bijective_of_lowerRamificationGroup_one_eq_top (by simpa using hG)
  have hGi (i : ℕ) (hi : i ≤ v + 2) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by push_cast; omega))
  have h : IsTotallyRamified K L :=
    (lowerRamificationGroup_zero_eq_top_iff K L).1 (by simpa using hGi 0 (by omega))
  have hψ : psiNat K L (v + 1) = v + 1 :=
    (psiNat_eq_self_iff K L).2 (by rw [hGi (v + 1) (by omega), ← Nat.cast_zero, hGi 0 (by omega)])
  -- Injectivity: if `N(1 + z) ≡ 1` modulo `𝓂[K] ^ (v + 2)` for `z ∈ 𝓂[L] ^ (v + 1)`, the
  -- expansion `N(1 + z) = 1 + Tr(z) + Tr(y) + N(z)` gives `N(z) ∈ 𝓂[K] ^ (v + 2)`, and in a totally
  -- ramified extension the norm preserves valuations, so `z ∈ 𝓂[L] ^ (v + 2)`.
  have hinj : Function.Injective (normGradedMap K L (v + 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    induction c using QuotientGroup.induction_on with | H x => ?_
    rw [MonoidHom.mem_ker, normGradedMap_mk, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hc
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hx : (x : Lˣ) ∈ unitFiltration L (v + 1) := (congrArg (unitFiltration L) hψ).le x.2
    obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.1 hx
    obtain ⟨u', hu', hux'⟩ := mem_unitFiltration_iff_exists.1 hc
    obtain ⟨y, hy, hN⟩ := exists_norm_one_add_eq_of_mem_maximalIdeal_pow hℓ hu
    rw [add_sub_cancel] at hN
    have hu'N : (u' : 𝒪[K]) = Algebra.norm 𝒪[K] (u : 𝒪[L]) := by
      apply Subtype.ext
      rw [hux', coe_norm_integerRing, hux, Algebra.coe_normUnits]
    have hz : Algebra.norm 𝒪[K] ((u : 𝒪[L]) - 1) ∈ 𝓂[K] ^ (v + 2) := by
      have hz : Algebra.norm 𝒪[K] ((u : 𝒪[L]) - 1) = (u' : 𝒪[K]) - 1 -
          Algebra.trace 𝒪[K] 𝒪[L] ((u : 𝒪[L]) - 1) - Algebra.trace 𝒪[K] 𝒪[L] y := by
        rw [hu'N, hN]
        ring
      rw [hz]
      exact sub_mem (sub_mem hu' (trace_mem_maximalIdeal_pow_succ hℓ.two_le hG hu))
        (trace_mem_maximalIdeal_pow_succ hℓ.two_le hG (Ideal.pow_le_pow_right (by omega) hy))
    refine (congrArg (fun n ↦ unitFiltration L (n + 1)) hψ).ge
      (mem_unitFiltration_iff_exists.2 ⟨u, ?_, hux⟩)
    rw [IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hz ⊢
    rwa [addVal_norm, h.inertiaDegree_eq_one, one_nsmul] at hz
  -- Both graded pieces have `q` elements.
  refine hinj.bijective_of_nat_card_le ?_
  rw [hψ, natCard_unitFiltrationGraded_succ, natCard_unitFiltrationGraded_succ,
    natCard_residueField K L, h.inertiaDegree_eq_one, pow_one]

/-! ### Before a positive break, in prime degree -/

/-- **Depth zero before a positive break.** Let `L/K` be a Galois extension of nonarchimedean local
fields of prime degree whose upper ramification filtration breaks at a natural number `t > 0`.
Then the graded norm `normGradedMap K L 0` is bijective. This is the regime `v = 0 < t`, in which
`L/K` is totally ramified of degree the residue characteristic `p`. -/
theorem normGradedMap_zero_before_break (hℓ : (finrank K L).Prime) {t : ℕ} (ht0 : 0 < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    Function.Bijective (normGradedMap K L 0) :=
  normGradedMap_zero_bijective_of_lowerRamificationGroup_one_eq_top <| top_le_iff.1 <|
    lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht ▸
      lowerRamificationGroup_antitone K L (by exact_mod_cast ht0)

/-- **Before the break, the graded norm is bijective.** Let `L/K` be a Galois extension of
nonarchimedean local fields of prime degree whose upper ramification filtration breaks at a natural
number `t`. Then the graded norm `normGradedMap K L v` is bijective at every depth `v < t`. The
regime `0 < v < t` is the one this result is named for; the depth `v = 0` is also
`TauCeti.normGradedMap_zero_before_break`. -/
theorem normGradedMap_positive_before_break (hℓ : (finrank K L).Prime) {v t : ℕ} (hvt : v < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    Function.Bijective (normGradedMap K L v) :=
  normGradedMap_bijective_of_lowerRamificationGroup_eq_top hℓ <| top_le_iff.1 <|
    lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht ▸
      lowerRamificationGroup_antitone K L (by exact_mod_cast hvt)

/-! ### At a positive break, in prime degree -/

/-- If `G_t = Gal(L/K)`, the trace carries `𝓂[L] ^ m` into `𝓂[K] ^ m` for every `m ≤ t + 1`:
`ψℕ_{L/K}(n) = n` for `n ≤ t`. -/
private theorem trace_mem_maximalIdeal_pow_of_le {t : ℕ} (hG : lowerRamificationGroup K L t = ⊤)
    {m : ℕ} (hm : m ≤ t + 1) {w : 𝒪[L]} (hw : w ∈ 𝓂[L] ^ m) :
    Algebra.trace 𝒪[K] 𝒪[L] w ∈ 𝓂[K] ^ m := by
  rcases m with _ | n
  · simp
  have hGi (i : ℕ) (hi : i ≤ t) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by exact_mod_cast hi))
  have hψ : psiNat K L n = n := (psiNat_eq_self_iff K L).2 <| by
    rw [hGi n (by omega), ← Nat.cast_zero, hGi 0 (by omega)]
  rw [← Algebra.intTrace_eq_trace]
  exact intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat (by rwa [hψ])

/-- **The norm at a positive depth with `G_t = Gal(L/K)`.** In prime degree `ℓ`, for a uniformizer
`π` of `L`, there is a constant `β` with `N(1 + a π ^ t) ≡ 1 + (a ^ ℓ + β a) N(π) ^ t` modulo
`𝓂[K] ^ (t + 1)`, read on residues. -/
private theorem exists_algebraMap_residue_eq_of_norm_one_add_mul_pow_eq
    (hℓ : (finrank K L).Prime) {t : ℕ} (ht0 : 0 < t) (hG : lowerRamificationGroup K L t = ⊤)
    {π : 𝒪[L]} (hπ : Irreducible π) :
    ∃ β : 𝓀[L], ∀ (a : 𝒪[L]) (b : 𝒪[K]),
      Algebra.norm 𝒪[K] (1 + a * π ^ t) = 1 + b * Algebra.norm 𝒪[K] π ^ t →
      algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] b) =
        residue 𝒪[L] a ^ finrank K L + β * residue 𝒪[L] a := by
  have h : IsTotallyRamified K L := (lowerRamificationGroup_zero_eq_top_iff K L).1 <|
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by omega))
  have hπK : Irreducible (Algebra.norm 𝒪[K] π) :=
    (irreducible_norm_iff_inertiaDegree_eq_one_of_irreducible hπ).2 h.inertiaDegree_eq_one
  have hspan (n : ℕ) : 𝓂[K] ^ n = Ideal.span {Algebra.norm 𝒪[K] π ^ n} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπK, Ideal.span_singleton_pow]
  have hπt : π ^ t ∈ 𝓂[L] ^ t :=
    Ideal.pow_mem_pow ((mem_maximalIdeal π).2 hπ.not_isUnit) t
  -- `Tr(π ^ t) = β₀ N(π) ^ t`; the constant is the residue of `β₀`.
  obtain ⟨β₀, hβ₀⟩ := Ideal.mem_span_singleton'.1 <|
    hspan t ▸ trace_mem_maximalIdeal_pow_of_le hG (by omega) hπt
  refine ⟨algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] β₀), fun a b hab ↦ ?_⟩
  -- The residue fields coincide, so `a ≡ a₀` modulo `𝓂[L]` for some `a₀ ∈ 𝒪[K]`.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝒪[K], algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] a₀) = residue 𝒪[L] a := by
    obtain ⟨y, hy⟩ := (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 h
      (residue 𝒪[L] a)
    obtain ⟨a₀, rfl⟩ := residue_surjective y
    exact ⟨a₀, hy⟩
  obtain ⟨w, hw, hN⟩ :=
    exists_norm_one_add_eq_of_mem_maximalIdeal_pow hℓ (Ideal.mul_mem_left _ a hπt)
  have hd : (a - algebraMap 𝒪[K] 𝒪[L] a₀) * π ^ t ∈ 𝓂[L] ^ (t + 1) := by
    rw [pow_succ']
    refine Ideal.mul_mem_mul ?_ hπt
    rw [← residue_eq_zero_iff, map_sub, ← ResidueField.algebraMap_residue, ha₀, sub_self]
  have hsplit : Algebra.trace 𝒪[K] 𝒪[L] (a * π ^ t) =
      a₀ * β₀ * Algebra.norm 𝒪[K] π ^ t +
        Algebra.trace 𝒪[K] 𝒪[L] ((a - algebraMap 𝒪[K] 𝒪[L] a₀) * π ^ t) := by
    rw [sub_mul, map_sub, ← Algebra.smul_def, map_smul, ← hβ₀, smul_eq_mul]
    ring
  -- In `N(1 + a π ^ t) = 1 + Tr(a π ^ t) + Tr(w) + N(a) N(π) ^ t`, both `Tr(w)` and
  -- `Tr((a - a₀) π ^ t)` lie in `𝓂[K] ^ (t + 1)`.
  have hrem : (b - a₀ * β₀ - Algebra.norm 𝒪[K] a) * Algebra.norm 𝒪[K] π ^ t ∈
      𝓂[K] ^ (t + 1) := by
    have heq : (b - a₀ * β₀ - Algebra.norm 𝒪[K] a) * Algebra.norm 𝒪[K] π ^ t =
        Algebra.trace 𝒪[K] 𝒪[L] ((a - algebraMap 𝒪[K] 𝒪[L] a₀) * π ^ t) +
          Algebra.trace 𝒪[K] 𝒪[L] w := by
      have := hab.symm.trans hN
      rw [hsplit, map_mul (Algebra.norm 𝒪[K]) a, map_pow (Algebra.norm 𝒪[K])] at this
      linear_combination this
    rw [heq]
    exact add_mem (trace_mem_maximalIdeal_pow_of_le hG le_rfl hd)
      (trace_mem_maximalIdeal_pow_of_le hG le_rfl
        (Ideal.pow_le_pow_right (show t + 1 ≤ 2 * t by omega) hw))
  have hmem : b - a₀ * β₀ - Algebra.norm 𝒪[K] a ∈ 𝓂[K] := by
    rw [hspan, Ideal.mem_span_singleton'] at hrem
    obtain ⟨d, hd⟩ := hrem
    have hdiv : b - a₀ * β₀ - Algebra.norm 𝒪[K] a = d * Algebra.norm 𝒪[K] π := by
      apply mul_right_cancel₀ (pow_ne_zero t hπK.ne_zero)
      rw [← hd]
      ring
    rw [hdiv]
    exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hπK.not_isUnit)
  rw [← residue_eq_zero_iff, map_sub, map_sub, sub_sub, sub_eq_zero] at hmem
  rw [hmem, map_add, map_mul, map_mul, ha₀, algebraMap_residue_norm_of_isTotallyRamified h]
  ring

omit [IsGalois K L] in
/-- If `σ ∈ G_0` lies outside `G_{t+1}` and `σ π - π = γ π ^ (t + 1)` for a uniformizer `π`, then
the residue of `γ` is nonzero. -/
private theorem residue_ne_zero_of_smul_sub_eq {t : ℕ} {π : 𝒪[L]} (hπ : Irreducible π)
    {σ : L ≃ₐ[K] L} (hσ0 : σ ∈ lowerRamificationGroup K L 0)
    (hσ : σ ∉ lowerRamificationGroup K L (t + 1)) {γ : 𝒪[L]}
    (hγ : σ • π - π = γ * π ^ (t + 1)) : residue 𝒪[L] γ ≠ 0 := by
  intro h0
  apply hσ
  rw [lowerRamificationGroup_def] at hσ0 ⊢
  have := (mem_ramificationGroup_natCast_iff_smul_sub_mem hπ hσ0 (n := t + 1)).2 <| by
    rw [hγ, pow_succ' _ (t + 1)]
    exact Ideal.mul_mem_mul ((residue_eq_zero_iff γ).1 h0)
      (Ideal.pow_mem_pow ((mem_maximalIdeal π).2 hπ.not_isUnit) _)
  exact_mod_cast this

/-- **The norm at the break.** Let `L/K` be a Galois extension of nonarchimedean local fields of
prime degree `ℓ`, let `t > 0` satisfy `G_t = Gal(L/K)`, and let `σ ∉ G_{t+1}`, so that
`σ π - π = γ π ^ (t + 1)` for a uniformizer `π` of `L`. If `N(1 + a π ^ t) = 1 + b N(π) ^ t`, then
the residue of `b` is `y ^ ℓ - c ^ (ℓ - 1) y`, where `y` and `c` are the residues of `a` and `γ`.
-/
theorem algebraMap_residue_eq_of_norm_one_add_mul_pow_eq (hℓ : (finrank K L).Prime) {t : ℕ}
    (ht0 : 0 < t) (hG : lowerRamificationGroup K L t = ⊤) {π : 𝒪[L]} (hπ : Irreducible π)
    {σ : L ≃ₐ[K] L} (hσ : σ ∉ lowerRamificationGroup K L (t + 1)) {γ : 𝒪[L]}
    (hγ : σ • π - π = γ * π ^ (t + 1)) {a : 𝒪[L]} {b : 𝒪[K]}
    (hab : Algebra.norm 𝒪[K] (1 + a * π ^ t) = 1 + b * Algebra.norm 𝒪[K] π ^ t) :
    algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] b) =
      residue 𝒪[L] a ^ finrank K L - residue 𝒪[L] γ ^ (finrank K L - 1) * residue 𝒪[L] a := by
  obtain ⟨β, hβ⟩ := exists_algebraMap_residue_eq_of_norm_one_add_mul_pow_eq hℓ ht0 hG hπ
  have hπK : Algebra.norm 𝒪[K] π ≠ 0 := by
    intro h0
    have := congrArg (fun x : 𝒪[K] ↦ (x : K)) h0
    simp only [coe_norm_integerRing, ZeroMemClass.coe_zero, Algebra.norm_eq_zero_iff] at this
    exact hπ.ne_zero (Subtype.ext this)
  -- The unit `σ π / π = 1 + γ π ^ t` has norm `1`.
  have hnorm : Algebra.norm 𝒪[K] (1 + γ * π ^ t) = 1 + 0 * Algebra.norm 𝒪[K] π ^ t := by
    rw [zero_mul, add_zero]
    apply mul_left_cancel₀ hπK
    rw [← map_mul, mul_one, show π * (1 + γ * π ^ t) = σ • π by linear_combination -hγ]
    apply Subtype.ext
    rw [coe_norm_integerRing, coe_norm_integerRing, AlgEquiv.coe_smul_integerRing,
      Algebra.norm_eq_of_algEquiv]
  have hc := hβ γ 0 hnorm
  rw [map_zero, map_zero] at hc
  have hG0 : lowerRamificationGroup K L 0 = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (Int.natCast_nonneg t))
  have hγ0 := residue_ne_zero_of_smul_sub_eq hπ (hG0 ▸ Subgroup.mem_top σ) hσ hγ
  -- So `c ^ ℓ + β c = 0` with `c ≠ 0`, that is `β = -c ^ (ℓ - 1)`.
  have hβeq : β = -residue 𝒪[L] γ ^ (finrank K L - 1) := by
    have hpow : residue 𝒪[L] γ ^ finrank K L =
        residue 𝒪[L] γ ^ (finrank K L - 1) * residue 𝒪[L] γ := by
      rw [← pow_succ, Nat.sub_add_cancel hℓ.one_lt.le]
    apply mul_right_cancel₀ hγ0
    linear_combination -hc - hpow
  rw [hβ a b hab, hβeq]
  ring

/-- **The graded norm at the break, in coordinates.** Let `L/K` be a Galois extension of
nonarchimedean local fields of prime degree `ℓ` with `G_{t+1} = Gal(L/K)`, and let
`σ ∉ G_{t+2}`, so that `σ π - π = γ π ^ (t + 2)` for a uniformizer `π` of `L`. Coordinatize
`U(L, t + 1) / U(L, t + 2)` by `π` and `U(K, t + 1) / U(K, t + 2)` by the uniformizer `N(π)` of
`K`. Then `normGradedMap K L (t + 1)` is `y ↦ y ^ ℓ - c ^ (ℓ - 1) y`, where `c` is the residue of
`γ`, the coordinate of `σ π / π`. -/
theorem algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk
    (hℓ : (finrank K L).Prime) {t : ℕ} (hG : lowerRamificationGroup K L (t + 1) = ⊤)
    {π : 𝒪[L]} (hπ : Irreducible π) (hπK : Irreducible (Algebra.norm 𝒪[K] π))
    {σ : L ≃ₐ[K] L} (hσ : σ ∉ lowerRamificationGroup K L (t + 2)) {γ : 𝒪[L]}
    (hγ : σ • π - π = γ * π ^ (t + 2)) (x : unitFiltration L (psiNat K L (t + 1))) {a : 𝒪[L]}
    (hxa : ((x : Lˣ) : L) = 1 + a * π ^ (t + 1)) :
    algebraMap 𝓀[K] 𝓀[L] (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer t
        (Algebra.norm 𝒪[K] π) hπK
        (Additive.ofMul (normGradedMap K L (t + 1) (QuotientGroup.mk x)))) =
      residue 𝒪[L] a ^ finrank K L - residue 𝒪[L] γ ^ (finrank K L - 1) * residue 𝒪[L] a := by
  rw [normGradedMap_mk]
  set y : unitFiltration K (t + 1) := ⟨Algebra.normUnits K (x : Lˣ),
    map_normUnits_unitFiltration_psiNat_le K L (t + 1) (Subgroup.mem_map_of_mem _ x.2)⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝒪[K], b * Algebra.norm 𝒪[K] π ^ (t + 1) =
      (unitFiltrationDifference t y : 𝒪[K]) := by
    have hspan : 𝓂[K] ^ (t + 1) = Ideal.span {Algebra.norm 𝒪[K] π ^ (t + 1)} := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπK, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.1 (hspan ▸ (unitFiltrationDifference t y).2)
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue t _ hπK y b
    hb.symm]
  refine algebraMap_residue_eq_of_norm_one_add_mul_pow_eq hℓ (by omega : 0 < t + 1) hG hπ
    (by exact_mod_cast hσ) hγ ?_
  apply Subtype.ext
  have hb' := congrArg (fun z : 𝒪[K] ↦ (z : K)) hb
  simp only [coe_coe_unitFiltrationDifference, y, Algebra.coe_normUnits] at hb'
  have hx : ((1 + a * π ^ (t + 1) : 𝒪[L]) : L) = ((x : Lˣ) : L) := by
    rw [hxa]
    simp
  push_cast
  rw [coe_norm_integerRing, coe_norm_integerRing, hx]
  push_cast at hb'
  rw [coe_norm_integerRing] at hb'
  linear_combination -hb'

/-- If `G_1 = Gal(L/K)` and `[L : K]` is prime, the residue field of `L` has characteristic
`[L : K]`: the Galois group is then a `p`-group of prime order, for `p` the residue
characteristic. -/
private theorem charP_residueField_of_lowerRamificationGroup_one_eq_top
    (hℓ : (finrank K L).Prime) (hG1 : lowerRamificationGroup K L 1 = ⊤) :
    CharP 𝓀[L] (finrank K L) := by
  let _ := Fintype.ofFinite 𝓀[L]
  set p := ringChar 𝓀[L]
  have : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  have hpG := isPGroup_ramificationGroup (L := L) (L ≃ₐ[K] L) p (i := 1) one_pos
  rw [← lowerRamificationGroup_def, hG1] at hpG
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpG
  rw [Subgroup.card_top, IsGalois.card_aut_eq_finrank] at hk
  rw [← ((Nat.Prime.pow_eq_iff hℓ).1 hk.symm).1]
  infer_instance

/-- Read in the coordinate attached to a uniformizer `π`, the kernel of the graded norm at a depth
`t + 1` with `G_{t+1} = Gal(L/K)` is the set of roots of `y ^ ℓ - c ^ (ℓ - 1) y`, by
`TauCeti.algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk`. -/
private theorem natCard_ker_normGradedMap_succ_eq (hℓ : (finrank K L).Prime) {t : ℕ}
    (hG : lowerRamificationGroup K L (t + 1) = ⊤) (hψ : psiNat K L (t + 1) = t + 1)
    {π : 𝒪[L]} (hπ : Irreducible π) (hπK : Irreducible (Algebra.norm 𝒪[K] π))
    {σ : L ≃ₐ[K] L} (hσ : σ ∉ lowerRamificationGroup K L (t + 2)) {γ : 𝒪[L]}
    (hγ : σ • π - π = γ * π ^ (t + 2)) :
    Nat.card (normGradedMap K L (t + 1)).ker = Nat.card {y : 𝓀[L] //
      y ^ finrank K L - residue 𝒪[L] γ ^ (finrank K L - 1) * y = 0} := by
  let E : UnitFiltrationGraded L (psiNat K L (t + 1)) ≃ 𝓀[L] :=
    (unitFiltrationGradedCongr hψ).toEquiv.trans
      (Additive.ofMul.trans (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer t π hπ).toEquiv)
  refine Nat.card_congr (E.subtypeEquiv fun g ↦ ?_)
  induction g using QuotientGroup.induction_on with | H x => ?_
  -- Write `x = 1 + a π ^ (t + 1)`; its coordinate is the residue of `a`.
  obtain ⟨u, hu, hux⟩ :=
    mem_unitFiltration_iff_exists.1 ((congrArg (unitFiltration L) hψ).le x.2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at hu
  obtain ⟨a, ha⟩ := hu
  have hxa : ((x : Lˣ) : L) = 1 + a * π ^ (t + 1) := by
    rw [← hux, ← sub_add_cancel (u : 𝒪[L]) 1, ← ha]
    push_cast
    ring
  have hE : E (QuotientGroup.mk x) = residue 𝒪[L] a := by
    simp only [E, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      unitFiltrationGradedCongr_mk, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
    refine unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue t π hπ _ a
      (Subtype.ext ?_)
    rw [coe_coe_unitFiltrationDifference, hxa]
    push_cast
    ring
  rw [hE, MonoidHom.mem_ker,
    ← algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk hℓ hG hπ
      hπK hσ hγ x hxa, map_eq_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective,
    EmbeddingLike.map_eq_zero_iff, ofMul_eq_zero]

/-- **The graded norm at a positive break.** Let `L/K` be a Galois extension of nonarchimedean
local fields of prime degree `ℓ` whose upper ramification filtration breaks at a natural number
`t > 0`. Then the kernel of the graded norm `normGradedMap K L t` has order `ℓ`, and its image has
index `ℓ`. This is the regime `v = t > 0`, in which `L/K` is totally ramified and `ℓ` is the
residue characteristic. -/
theorem normGradedMap_at_break (hℓ : (finrank K L).Prime) {t : ℕ} (ht0 : 0 < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    Nat.card (normGradedMap K L t).ker = finrank K L ∧
      (normGradedMap K L t).range.index = finrank K L := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hG : lowerRamificationGroup K L ((s + 1 : ℕ) : ℤ) = ⊤ :=
    lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht
  have hGi (i : ℤ) (hi : i ≤ s + 1) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by push_cast; exact hi))
  have h : IsTotallyRamified K L :=
    (lowerRamificationGroup_zero_eq_top_iff K L).1 (hGi 0 (by omega))
  have hψ : psiNat K L (s + 1) = s + 1 :=
    (psiNat_eq_self_iff K L).2 (by rw [hG, hGi 0 (by omega)])
  have : Fact (finrank K L).Prime := ⟨hℓ⟩
  have := charP_residueField_of_lowerRamificationGroup_one_eq_top hℓ (hGi 1 (by omega))
  -- An element `σ ≠ 1` of the Galois group lies outside `G_{s+2} = 1`; write
  -- `σ π - π = γ π ^ (s + 2)`, so that the residue `c` of `γ` is nonzero.
  have : Nontrivial (L ≃ₐ[K] L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    exact hℓ.one_lt
  obtain ⟨σ, hσ1⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have hσ : σ ∉ lowerRamificationGroup K L (((s + 1 : ℕ) : ℤ) + 1) := by
    rw [lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump K L hℓ ht]
    exact hσ1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝒪[L], σ • π - π = γ * π ^ (s + 2) := by
    have hmem := mem_lowerRamificationGroup_iff.1 (hG ▸ Subgroup.mem_top σ) π
    rw [show ((((s + 1 : ℕ) : ℤ) + 1).toNat) = s + 2 by omega,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨γ, hγ⟩ := hmem
    exact ⟨γ, hγ.symm⟩
  have hπK : Irreducible (Algebra.norm 𝒪[K] π) :=
    (irreducible_norm_iff_inertiaDegree_eq_one_of_irreducible hπ).2 h.inertiaDegree_eq_one
  have hc0 : residue 𝒪[L] γ ≠ 0 :=
    residue_ne_zero_of_smul_sub_eq hπ (hGi 0 (by omega) ▸ Subgroup.mem_top σ) hσ hγ
  -- The kernel is `{y | y ^ ℓ = c ^ (ℓ - 1) y}`; writing `y = c z`, this is the line
  -- `{c z | z ^ ℓ = z} = 𝔽_ℓ c`, of order `ℓ`.
  have hcard_ker : Nat.card (normGradedMap K L (s + 1)).ker = finrank K L := by
    rw [natCard_ker_normGradedMap_succ_eq hℓ (by exact_mod_cast hG) hψ hπ hπK
      (by exact_mod_cast hσ) hγ]
    refine (Nat.card_congr ((Equiv.mulLeft₀ _ hc0).subtypeEquiv fun z ↦ ?_)).symm.trans
      (Subfield.card_bot 𝓀[L] (finrank K L))
    set c := residue 𝒪[L] γ
    have hpow : (c * z) ^ finrank K L - c ^ (finrank K L - 1) * (c * z) =
        c ^ finrank K L * (z ^ finrank K L - z) := by
      rw [mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hℓ.one_lt.le]
      ring
    rw [Subfield.mem_bot_iff_pow_eq_self 𝓀[L] (finrank K L), Equiv.mulLeft₀_apply, hpow,
      mul_eq_zero, sub_eq_zero, or_iff_right (pow_ne_zero _ hc0)]
  refine ⟨hcard_ker, ?_⟩
  -- Both graded pieces have `q` elements, so the cokernel has the order of the kernel.
  have hT : Nat.card (UnitFiltrationGraded K (s + 1)) ≠ 0 := by
    rw [natCard_unitFiltrationGraded_succ]
    exact Nat.card_pos.ne'
  have : Finite (UnitFiltrationGraded K (s + 1)) := Nat.finite_of_card_ne_zero hT
  have hST : Nat.card (UnitFiltrationGraded L (psiNat K L (s + 1))) =
      Nat.card (UnitFiltrationGraded K (s + 1)) := by
    rw [hψ, natCard_unitFiltrationGraded_succ, natCard_unitFiltrationGraded_succ,
      natCard_residueField K L, h.inertiaDegree_eq_one, pow_one]
  have h₁ := Subgroup.card_ker_mul_card_range (normGradedMap K L (s + 1))
  have h₂ := Subgroup.card_mul_index (normGradedMap K L (s + 1)).range
  have hpos : 0 < Nat.card (normGradedMap K L (s + 1)).range := Nat.card_pos
  rw [← hcard_ker]
  nlinarith

end TauCeti
