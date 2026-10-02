/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
public import TauCeti.NumberTheory.LocalField.Norm.Herbrand
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
Hasse–Arf theorem are computed from. This file computes them away from the break.

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
  rw [ResidueField.algebraMap_residue, algebraMap_norm_integerRing_eq_prod_automorphisms,
    map_prod, Finset.prod_congr rfl fun σ _ ↦ hσ σ, Finset.prod_const, Finset.card_univ,
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
private def residueFieldUnitsEquiv (h : IsTotallyRamified K L) : 𝓀[K]ˣ ≃* 𝓀[L]ˣ :=
  Units.mapEquiv (RingEquiv.ofBijective (algebraMap 𝓀[K] 𝓀[L])
    (show Function.Bijective (algebraMap 𝓀[K] 𝓀[L]) from ⟨(algebraMap 𝓀[K] 𝓀[L]).injective,
      (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 h⟩)).toMulEquiv

omit [Module.Finite K L] [IsGalois K L] in
private theorem coe_residueFieldUnitsEquiv (h : IsTotallyRamified K L) (u : 𝓀[K]ˣ) :
    (residueFieldUnitsEquiv h u : 𝓀[L]) = algebraMap 𝓀[K] 𝓀[L] u := by
  rw [residueFieldUnitsEquiv, Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe,
    RingEquiv.coe_toMulEquiv, RingEquiv.ofBijective_apply]

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
  rw [targetEquiv, MulEquiv.trans_apply, coe_residueFieldUnitsEquiv,
    algebraMap_unitFiltrationGradedZeroEquivResidueFieldUnits_normGradedMap_mk h, sourceEquiv,
    MulEquiv.trans_apply, unitFiltrationGradedCongr_mk,
    coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk]
  refine congrArg (fun z : 𝒪[L] ↦ residue 𝒪[L] z ^ finrank K L) (Subtype.ext ?_)
  simp only [coe_unitFiltrationToIntegerUnits]

/-- **The kernel of the graded norm at depth zero.** For a totally ramified Galois extension `L/K`
of nonarchimedean local fields, with residue field of cardinality `q`, the kernel of
`normGradedMap K L 0` has order `gcd(q - 1, [L : K])`. -/
theorem natCard_ker_normGradedMap_zero (h : IsTotallyRamified K L) :
    Nat.card (normGradedMap K L 0).ker = (Nat.card 𝓀[K] - 1).gcd (finrank K L) := by
  rw [← MonoidHom.ker_mulEquiv_comp _ (targetEquiv h), targetEquiv_comp_normGradedMap_zero h,
    MonoidHom.ker_comp_mulEquiv, Subgroup.card_map_of_injective (MulEquiv.injective _),
    IsCyclic.card_powMonoidHom_ker, Nat.card_units, natCard_residueField K L,
    h.inertiaDegree_eq_one, pow_one]

/-- **The cokernel of the graded norm at depth zero.** For a totally ramified Galois extension
`L/K` of nonarchimedean local fields, with residue field of cardinality `q`, the image of
`normGradedMap K L 0` has index `gcd(q - 1, [L : K])`. -/
theorem index_range_normGradedMap_zero (h : IsTotallyRamified K L) :
    (normGradedMap K L 0).range.index = (Nat.card 𝓀[K] - 1).gcd (finrank K L) := by
  rw [← Subgroup.index_map_equiv _ (targetEquiv h), MonoidHom.map_range,
    targetEquiv_comp_normGradedMap_zero h, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (MulEquiv.surjective _), ← MonoidHom.range_eq_map, IsCyclic.index_powMonoidHom_range,
    Nat.card_units, natCard_residueField K L, h.inertiaDegree_eq_one, pow_one]

/-- **The graded norm at depth zero is bijective exactly in the coprime case.** For a totally
ramified Galois extension `L/K` of nonarchimedean local fields, with residue field of cardinality
`q`, the map `normGradedMap K L 0` is bijective if and only if `[L : K]` is prime to `q - 1`. -/
theorem normGradedMap_zero_bijective_iff (h : IsTotallyRamified K L) :
    Function.Bijective (normGradedMap K L 0) ↔ (finrank K L).Coprime (Nat.card 𝓀[K] - 1) := by
  rw [Function.Bijective, ← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one,
    natCard_ker_normGradedMap_zero h, ← MonoidHom.range_eq_top, ← Subgroup.index_eq_one,
    index_range_normGradedMap_zero h, and_self, Nat.gcd_comm]

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
  exact Nat.Coprime.pow_left k <| Nat.Coprime.of_dvd_left hq <|
    (Nat.coprime_self_sub_right (show 1 ≤ Nat.card 𝓀[L] from Nat.card_pos)).2 (by simp)

/-- If `[L : K] ≥ 2` and `G_{v+1} = Gal(L/K)`, the trace carries `𝓂[L] ^ v` into
`𝓂[K] ^ (v + 1)`: Hilbert's formula, truncated at `v + 1`, gives
`d(L/K) ≥ (v + 2) ([L : K] - 1)`. -/
private theorem trace_mem_maximalIdeal_pow_succ (h2 : 2 ≤ finrank K L) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 1) = ⊤) {w : 𝒪[L]} (hw : w ∈ 𝓂[L] ^ v) :
    Algebra.trace 𝒪[K] 𝒪[L] w ∈ 𝓂[K] ^ (v + 1) := by
  have hGi (i : ℕ) (hi : i ≤ v + 1) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by omega))
  have he : ramificationIndex K L = finrank K L :=
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 <|
      (lowerRamificationGroup_zero_eq_top_iff K L).1 (by simpa using hGi 0 (by omega))
  have hd : (v + 2) * (finrank K L - 1) ≤ differentExponent K L := by
    have hsum := sum_range_card_lowerRamificationGroup_sub_one_le_differentExponent K L (v + 2)
    rwa [Finset.sum_congr rfl fun i hi ↦ by
        rw [hGi i (by simp only [Finset.mem_range] at hi; omega), Subgroup.card_top,
          IsGalois.card_aut_eq_finrank],
      Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  rw [← Algebra.intTrace_eq_trace]
  refine intTrace_mem_maximalIdeal_pow_of_mem hw ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
  have hm1 : 2 + m - 1 = m + 1 := by omega
  rw [he, hm]
  rw [hm, hm1] at hd
  nlinarith

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

/-- In prime degree, an upper break at a natural number `t` has `G_t = Gal(L/K)`: the group
`G^t = G_{ψ(t)}` strictly contains every later upper group, so it is nontrivial, hence the whole
Galois group, and `t ≤ ψ(t)`. -/
private theorem lowerRamificationGroup_natCast_eq_top_of_upperJump (hℓ : (finrank K L).Prime)
    {t : ℕ} (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K L t = ⊤ := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime := ⟨IsGalois.card_aut_eq_finrank K L ▸ hℓ⟩
  have hlt := (upperJump_iff K L _).1 ht ⟨(t + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (t + 1)⟩
    (Subtype.mk_lt_mk.2 (by push_cast; linarith))
  have hne := (bot_le.trans_lt hlt).ne'
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast,
    lowerRamificationGroupReal_intCast] at hne
  have hψ : lowerRamificationGroup K L (psiNat K L t) = ⊤ :=
    ((lowerRamificationGroup K L _).eq_bot_or_eq_top_of_prime_card).resolve_left hne
  have htψ : (t : ℤ) ≤ psiNat K L t := by exact_mod_cast self_le_psiNat K L t
  exact top_le_iff.1 <| hψ ▸ lowerRamificationGroup_antitone K L htψ

/-- **Depth zero before a positive break.** Let `L/K` be a Galois extension of nonarchimedean local
fields of prime degree whose upper ramification filtration breaks at a natural number `t > 0`.
Then the graded norm `normGradedMap K L 0` is bijective. This is the regime `v = 0 < t`, in which
`L/K` is totally ramified of degree the residue characteristic `p`. -/
theorem normGradedMap_zero_before_break (hℓ : (finrank K L).Prime) {t : ℕ} (ht0 : 0 < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    Function.Bijective (normGradedMap K L 0) :=
  normGradedMap_zero_bijective_of_lowerRamificationGroup_one_eq_top <| top_le_iff.1 <|
    lowerRamificationGroup_natCast_eq_top_of_upperJump hℓ ht ▸
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
    lowerRamificationGroup_natCast_eq_top_of_upperJump hℓ ht ▸
      lowerRamificationGroup_antitone K L (by exact_mod_cast hvt)

end TauCeti
