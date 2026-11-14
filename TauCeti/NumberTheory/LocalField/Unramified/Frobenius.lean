/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import TauCeti.NumberTheory.LocalField.Unramified.ResidueField
import Mathlib.Data.Nat.Prime.Infinite
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.RingTheory.Algebraic.Basic
import TauCeti.RingTheory.AlgebraicIndependent.Automorphism
import TauCeti.RingTheory.AlgebraicIndependent.TranscendenceBasis
import TauCeti.RingTheory.Valuation.ValuativeRel.Frobenius

/-!
# Frobenius congruence, fixed fields, and transcendence of `Breve E`

Let `E` be a nonarchimedean local field with residue field `𝓀[E]` of cardinality `q`, and let `σ`
(`TauCeti.MaxUnramifiedCompletion.frobenius E`) be the arithmetic Frobenius of the completed maximal
unramified extension `Breve E`.

Every Galois automorphism of `E^{ur}/E` preserves the valuation on `E^{ur}`, so by continuity its
extension to `Breve E` preserves the canonical valuation of `Breve E`. In particular `σ` restricts
to an `𝒪[E]`-algebra automorphism `integerFrobenius E : 𝒪[Breve E] ≃ₐ[𝒪[E]] 𝒪[Breve E]` satisfying
the Frobenius congruence `σ(x) ≡ x^q (mod 𝓂[Breve E])` for every `x ∈ 𝒪[Breve E]`.

Uniformizer-adic approximation
(`ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one`) then shows
that:
* the fixed field of `σ` on `Breve E` is `E`, and its fixed ring on `𝒪[Breve E]` is `𝒪[E]`;
* for every `n ≠ 0`, the fixed field of `σ^n` on `Breve E` is the finite unramified extension
  `E_n` of degree `n`;
* consequently an element of `Breve E` is algebraic over `E` if and only if it belongs to `E^{ur}`.

Diagonalizing the powers of `σ` on `𝒪[Breve E]` produces elements of `Breve E` transcendental over
`E` in every characteristic. When `CharZero E`, following [Chen], Proposition 2.0.3, solving
`σ(y_ℓ) = ℓ^{q-1} y_ℓ` for primes `ℓ` strictly larger than the residue characteristic produces an
infinite algebraically independent family in `Breve E`, proving that `Breve E` has infinite
transcendence degree over both `E` and `E^{ur}`.

## Main definitions

* `TauCeti.MaxUnramifiedCompletion.integerFrobenius E`: the restriction of `σ` to an `𝒪[E]`-algebra
  automorphism of `𝒪[Breve E]`.

## Main results

* `TauCeti.MaxUnramifiedCompletion.frobenius_congr`,
  `TauCeti.MaxUnramifiedCompletion.residue_integerFrobenius`: `σ(x) ≡ x^q (mod 𝓂[Breve E])` for
  `x ∈ 𝒪[Breve E]`.
* `TauCeti.MaxUnramifiedCompletion.fixedPoints_frobenius`,
  `TauCeti.MaxUnramifiedCompletion.fixedPoints_integerFrobenius`,
  `TauCeti.MaxUnramifiedCompletion.fixedPoints_frobenius_pow`: the fixed field of `σ` is `E`, its
  integral fixed ring is `𝒪[E]`, and the fixed field of `σ^n` (`n ≠ 0`) is `E_n`.
* `TauCeti.MaxUnramifiedCompletion.isAlgebraic_iff_mem_range_coe`,
  `TauCeti.MaxUnramifiedCompletion.exists_transcendental`,
  `TauCeti.MaxUnramifiedCompletion.not_isAlgebraic`: the elements of `Breve E` algebraic over `E`
  are precisely `E^{ur}`, and `Breve E` contains transcendental elements over `E` in every
  characteristic.
* `TauCeti.MaxUnramifiedCompletion.transcendenceDegree_infinite`,
  `TauCeti.MaxUnramifiedCompletion.transcendenceDegree_unramified_infinite`: when `CharZero E`,
  `Breve E` has infinite transcendence degree over `E` and over `E^{ur}`.

## References

* M. Chen, *Composantes connexes géométriques d'espaces de modules de groupes `p`-divisibles*,
  Ann. Sci. Éc. Norm. Supér. (4) 47 (2014), 723–764, Proposition 2.0.3.
* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997), §1.1.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
-/

public section
noncomputable section

open ValuativeRel UniformSpace IntermediateField

namespace TauCeti.MaxUnramifiedCompletion

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-! ### Galois invariance of the valuation and Frobenius congruence -/

/-- The continuous action of `Gal(E^{ur}/E)` on `Breve E` preserves the canonical valuation. -/
@[simp]
theorem galAction_valuation_eq (τ : Gal(Unramified E/E)) (x : Breve E) :
    valuation (Breve E) (galAction τ x) = valuation (Breve E) x :=
  Completion.valuation_eq_of_continuous (continuous_galAction τ) (fun _ ↦ map_eq_zero _)
    (galAction_coe τ) (fun r ↦ τ.valuation_eq (K := E) r) x

/-- Frobenius on `Breve E` preserves the canonical valuation. -/
@[simp]
theorem frobenius_valuation_eq (x : Breve E) :
    valuation (Breve E) (frobenius E x) = valuation (Breve E) x := by
  rw [frobenius_eq_galAction, galAction_valuation_eq]

/-- The action of `Gal(E^{ur}/E)` preserves the valuation ring `𝒪[Breve E]`. -/
@[simp]
theorem galAction_mem_integer_iff (τ : Gal(Unramified E/E)) (x : Breve E) :
    galAction τ x ∈ 𝒪[Breve E] ↔ x ∈ 𝒪[Breve E] := by
  simp only [Valuation.mem_integer_iff, galAction_valuation_eq]

/-- Frobenius on `Breve E` preserves the valuation ring `𝒪[Breve E]`. -/
@[simp]
theorem frobenius_mem_integer_iff (x : Breve E) :
    frobenius E x ∈ 𝒪[Breve E] ↔ x ∈ 𝒪[Breve E] := by
  rw [frobenius_eq_galAction, galAction_mem_integer_iff]

variable (E) in
/-- **The arithmetic Frobenius on the ring of integers `𝒪[Breve E]`** as an `𝒪[E]`-algebra
automorphism. -/
def integerFrobenius : 𝒪[Breve E] ≃ₐ[𝒪[E]] 𝒪[Breve E] :=
  (frobenius E).integerAlgEquivOfMemInteger frobenius_mem_integer_iff

/-- `integerFrobenius E` agrees with `frobenius E` upon coercion to `Breve E`. -/
@[simp]
theorem coe_integerFrobenius_apply (x : 𝒪[Breve E]) :
    (integerFrobenius E x : Breve E) = frobenius E (x : Breve E) :=
  (frobenius E).coe_integerAlgEquivOfMemInteger_apply frobenius_mem_integer_iff x

/-- `(integerFrobenius E).symm` agrees with `(frobenius E).symm` upon coercion to `Breve E`. -/
@[simp]
theorem coe_integerFrobenius_symm_apply (x : 𝒪[Breve E]) :
    ((integerFrobenius E).symm x : Breve E) = (frobenius E).symm (x : Breve E) :=
  (frobenius E).coe_integerAlgEquivOfMemInteger_symm_apply frobenius_mem_integer_iff x

/-- Iterates of `integerFrobenius E` agree with iterates of `frobenius E` upon coercion to
`Breve E`. -/
theorem coe_integerFrobenius_pow_apply (n : ℕ) (x : 𝒪[Breve E]) :
    ((integerFrobenius E ^ n) x : Breve E) = (frobenius E ^ n) (x : Breve E) :=
  (frobenius E).coe_integerAlgEquivOfMemInteger_pow_apply frobenius_mem_integer_iff n x

/-- **Congruence of Frobenius on `𝒪[E^{ur}]`.** For every integer `x` of `E^{ur}`,
`σ(x) ≡ x^q` modulo the maximal ideal. -/
theorem unramifiedFrobenius_congr {x : Unramified E} (hx : x ∈ 𝒪[Unramified E]) :
    valuation (Unramified E) (unramifiedFrobenius E x - x ^ Nat.card 𝓀[E]) < 1 := by
  obtain ⟨f, _, hxf⟩ := mem_maximalUnramifiedExtension_iff.1 x.2
  let L := unramifiedExtension E (AlgebraicClosure E) f
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension
  let j : L →ₐ[E] Unramified E :=
    inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) f)
  let := j.toAlgebra
  have := j.valuativeExtension
  let xL : L := ⟨x.1, hxf⟩
  have hxL_eq : algebraMap L (Unramified E) xL = x :=
    Subtype.ext (IntermediateField.coe_inclusion _ _)
  have hxL1 : valuation L xL ≤ 1 :=
    (ValuativeExtension.valuation_algebraMap_le_one_iff xL).1 (by rw [hxL_eq]; exact hx)
  have hsub_eq : unramifiedFrobenius E x - x ^ Nat.card 𝓀[E] =
      algebraMap L (Unramified E)
        (frobeniusAlgEquiv (K := E) (L := L) xL - xL ^ Nat.card 𝓀[E]) := by
    refine Subtype.ext ?_
    have hcoe := coe_maximalUnramifiedFrobenius_apply_of_mem (K := E)
      (Ω := AlgebraicClosure E) (f := f) hxf
    have hx_pair : (⟨x.1, unramifiedExtension_le_maximalUnramifiedExtension E
        (AlgebraicClosure E) f hxf⟩ : Unramified E) = x := Subtype.ext rfl
    rw [hx_pair] at hcoe
    have hmap : ((algebraMap L (Unramified E)
        (frobeniusAlgEquiv (K := E) (L := L) xL - xL ^ Nat.card 𝓀[E]) : Unramified E) :
        AlgebraicClosure E) =
        ((frobeniusAlgEquiv (K := E) (L := L) xL - xL ^ Nat.card 𝓀[E] : L) :
          AlgebraicClosure E) :=
      IntermediateField.coe_inclusion _ _
    rw [hmap]
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hcoe, xL]
  rw [hsub_eq, ValuativeExtension.valuation_algebraMap_lt_one_iff]
  exact valuation_frobeniusAlgEquiv_sub_pow (K := E) (L := L) ⟨xL, hxL1⟩

/-- **Congruence of Frobenius on `𝒪[Breve E]`.** For every integer `x` of `Breve E`,
`σ(x) − x^q` has valuation strictly less than `1`, i.e., lies in `𝓂[Breve E]`. -/
theorem frobenius_congr {x : Breve E} (hx : x ∈ 𝒪[Breve E]) :
    valuation (Breve E) (frobenius E x - x ^ Nat.card 𝓀[E]) < 1 := by
  have hcont : Continuous fun z : 𝒪[Breve E] ↦ frobenius E z.1 - z.1 ^ Nat.card 𝓀[E] :=
    (continuous_frobenius.comp continuous_subtype_val).sub
      (continuous_subtype_val.pow (Nat.card 𝓀[E]))
  refine Completion.valuation_lt_one_of_continuous_integer (K := Unramified E) hcont
    (fun y ↦ ?_) ⟨x, hx⟩
  have hcoe : ((algebraMap 𝒪[Unramified E] 𝒪[Breve E] y : 𝒪[Breve E]) : Breve E) =
      ((y : Unramified E) : Breve E) := by
    rw [Valuation.HasExtension.val_algebraMap, Completion.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [hcoe, frobenius_coe]
  have hcast : ((unramifiedFrobenius E (y : Unramified E) : Unramified E) : Breve E) -
      ((y : Unramified E) : Breve E) ^ Nat.card 𝓀[E] =
      ((unramifiedFrobenius E (y : Unramified E) - (y : Unramified E) ^ Nat.card 𝓀[E] :
        Unramified E) : Breve E) :=
    ((Completion.coe_sub _ _).trans
      (congrArg _ (map_pow Completion.coeRingHom (y : Unramified E) _))).symm
  rw [hcast, ← map_one (valuation (Breve E)), ← (valuation (Breve E)).vlt_iff_lt,
    ← Completion.coe_one, Completion.coe_vlt_coe_iff, (valuation (Unramified E)).vlt_iff_lt,
    map_one]
  exact unramifiedFrobenius_congr y.2

/-- On `𝒪[Breve E]`, `integerFrobenius E x - x ^ q` lies in the maximal ideal `𝓂[Breve E]`. -/
theorem integerFrobenius_sub_pow_mem_maximalIdeal (x : 𝒪[Breve E]) :
    integerFrobenius E x - x ^ Nat.card 𝓀[E] ∈ 𝓂[Breve E] :=
  (frobenius E).integerAlgEquivOfMemInteger_sub_pow_mem_maximalIdeal
    frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) x

/-- Reduction modulo `𝓂[Breve E]` intertwines `integerFrobenius E` with the `q`-th power map on
`𝓀[Breve E]`. -/
@[simp]
theorem residue_integerFrobenius (x : 𝒪[Breve E]) :
    IsLocalRing.residue 𝒪[Breve E] (integerFrobenius E x) =
      IsLocalRing.residue 𝒪[Breve E] x ^ Nat.card 𝓀[E] :=
  (frobenius E).residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one
    frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) x

/-- Reduction modulo `𝓂[Breve E]` intertwines the `n`-th power of `integerFrobenius E` with the
`q^n`-th power map on `𝓀[Breve E]`. -/
theorem residue_integerFrobenius_pow (n : ℕ) (x : 𝒪[Breve E]) :
    IsLocalRing.residue 𝒪[Breve E] ((integerFrobenius E ^ n) x) =
      IsLocalRing.residue 𝒪[Breve E] x ^ Nat.card 𝓀[E] ^ n :=
  (frobenius E).residue_integerAlgEquivOfMemInteger_pow_of_valuation_sub_pow_lt_one
    frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) n x

/-- For every `n : ℕ` and `x ∈ 𝒪[Breve E]`, `(σ ^ n)(x) ≡ x^{q^n} (mod 𝓂[Breve E])`. -/
theorem frobenius_pow_congr (n : ℕ) {x : Breve E} (hx : x ∈ 𝒪[Breve E]) :
    valuation (Breve E) ((frobenius E ^ n) x - x ^ Nat.card 𝓀[E] ^ n) < 1 :=
  (frobenius E).valuation_pow_sub_pow_lt_one_of_valuation_sub_pow_lt_one
    Nat.card_pos.ne' (fun _ hz ↦ frobenius_congr hz) n hx

/-! ### Fixed points of Frobenius -/

/-- An element of `Breve E` is fixed by Frobenius if and only if it belongs to the image of `E`. -/
theorem frobenius_eq_self_iff {x : Breve E} :
    frobenius E x = x ↔ x ∈ Set.range (algebraMap E (Breve E)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one
    mapValueGroupWithZero_breve_surjective (frobenius E) (fun _ hz ↦ frobenius_congr hz) x

variable (E) in
/-- **The fixed field of Frobenius on `Breve E` is the base local field `E`.** -/
theorem fixedPoints_frobenius :
    {x : Breve E | frobenius E x = x} = Set.range (algebraMap E (Breve E)) :=
  Set.ext fun _ ↦ frobenius_eq_self_iff

variable (E) in
/-- **The fixed ring of Frobenius on `𝒪[Breve E]` is `𝒪[E]`.** -/
theorem fixedPoints_integerFrobenius :
    {x : 𝒪[Breve E] | integerFrobenius E x = x} = Set.range (algebraMap 𝒪[E] 𝒪[Breve E]) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact Set.ext fun x ↦
    (frobenius E).integerAlgEquivOfMemInteger_eq_self_iff_mem_range_algebraMap
      frobenius_mem_integer_iff mapValueGroupWithZero_breve_surjective
      (fun _ hz ↦ frobenius_congr hz) x

/-- The `n`-th power of Frobenius on `Breve E` extends the `n`-th power of the arithmetic
Frobenius of `E^{ur}`. -/
@[simp]
theorem frobenius_pow_coe (n : ℕ) (x : Unramified E) :
    (frobenius E ^ n) (x : Breve E) = ((unramifiedFrobenius E ^ n) x : Breve E) := by
  rw [frobenius_eq_galAction, ← map_pow, galAction_coe]

/-- **The fixed field of `σ^n` (`n ≠ 0`) on `Breve E` is the unramified extension `E_n` of degree
`n`.** -/
theorem fixedPoints_frobenius_pow {n : ℕ} (hn : n ≠ 0) :
    {x : Breve E | (frobenius E ^ n) x = x} =
      Set.range ((↑) ∘ IntermediateField.inclusion
        (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n)) := by
  let L := unramifiedExtension E (AlgebraicClosure E) n
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension
  let j : L →ₐ[E] Unramified E :=
    inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n)
  let := j.toAlgebra
  have : IsScalarTower E L (Unramified E) := .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have := j.valuativeExtension
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  have : ContinuousConstSMul L (Unramified E) :=
    IsScalarTower.continuousConstSMul L (Unramified E) (Unramified E)
  have : UniformContinuousConstSMul L (Unramified E) :=
    uniformContinuousConstSMul_of_continuousConstSMul L (Unramified E)
  have : ValuativeExtension L (Breve E) := ValuativeExtension.trans L (Unramified E) (Breve E)
  have hsurjL : Function.Surjective (ValuativeExtension.mapValueGroupWithZero L (Breve E)) := by
    have hcomp : Function.Surjective
        ((ValuativeExtension.mapValueGroupWithZero L (Breve E)).comp
          (ValuativeExtension.mapValueGroupWithZero E L)) := by
      rw [ValuativeExtension.mapValueGroupWithZero_comp E L (Breve E)]
      exact mapValueGroupWithZero_breve_surjective
    rw [MonoidWithZeroHom.coe_comp] at hcomp
    exact hcomp.of_comp
  have hfixL (z : L) :
      (frobenius E ^ n) (algebraMap L (Breve E) z) = algebraMap L (Breve E) z := by
    have hord : orderOf (frobeniusAlgEquiv (K := E) (L := L)) = n := by
      rw [orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank,
        finrank_unramifiedExtension hn]
    have hpowL : (frobeniusAlgEquiv (K := E) (L := L) ^ n) z = z := by
      have h1 := hord ▸ pow_orderOf_eq_one (frobeniusAlgEquiv (K := E) (L := L))
      exact congr($h1 z)
    have hcoe := coe_maximalUnramifiedFrobenius_zpow_apply_of_mem (K := E)
      (Ω := AlgebraicClosure E) (f := n) (n : ℤ) z.2
    rw [zpow_natCast, zpow_natCast, hpowL] at hcoe
    have hU : (unramifiedFrobenius E ^ n) (algebraMap L (Unramified E) z) =
        algebraMap L (Unramified E) z :=
      Subtype.ext (hcoe.trans (IntermediateField.coe_inclusion _ _).symm)
    rw [Completion.algebraMap_def, frobenius_pow_coe, hU]
  let σL : Breve E ≃ₐ[L] Breve E := { (frobenius E ^ n).toRingEquiv with commutes' := hfixL }
  have hcardL : Nat.card 𝓀[L] = Nat.card 𝓀[E] ^ n := by
    rw [natCard_residueField E L, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hn]
  ext x
  exact ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one
    hsurjL σL (fun _ hz ↦ hcardL ▸ frobenius_pow_congr n hz) x

/-! ### Algebraic elements and transcendence of `Breve E` -/

/-- **An element of `Breve E` is algebraic over `E` if and only if it belongs to `E^{ur}`.** -/
theorem isAlgebraic_iff_mem_range_coe {x : Breve E} :
    IsAlgebraic E x ↔ x ∈ Set.range ((↑) : Unramified E → Breve E) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨n, hn, hnx⟩ := hx.exists_pow_apply_eq_self_of_algEquiv (frobenius E)
    have hmem : x ∈ {z : Breve E | (frobenius E ^ n) z = z} := hnx
    rw [fixedPoints_frobenius_pow hn] at hmem
    obtain ⟨z, rfl⟩ := hmem
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp0, hpy⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) y
    have hcoe : (y : Breve E) = IsScalarTower.toAlgHom E (Unramified E) (Breve E) y := by
      rw [IsScalarTower.toAlgHom_apply, Completion.algebraMap_def, Algebra.algebraMap_self,
        RingHom.id_apply]
    refine ⟨p, hp0, ?_⟩
    rw [hcoe, Polynomial.aeval_algHom_apply, hpy, map_zero]

variable (E) in
/-- **`Breve E` contains elements transcendental over `E` in every characteristic.** -/
theorem exists_transcendental : ∃ x : Breve E, Transcendental E x :=
  ValuativeExtension.exists_transcendental_of_valuation_sub_pow_lt_one
    mapValueGroupWithZero_breve_surjective (frobenius E) Finite.one_lt_card
    (fun _ hz ↦ frobenius_congr hz)

variable (E) in
/-- **`Breve E` is not algebraic over `E` in any characteristic.** -/
theorem not_isAlgebraic : ¬ Algebra.IsAlgebraic E (Breve E) := by
  obtain ⟨x, hx⟩ := exists_transcendental E
  exact fun h ↦ hx (h.isAlgebraic x)

/-- For every principal unit `u ≡ 1 (mod 𝓂[E])`, the Frobenius eigenvector equation
`σ(y) = u y` admits a nonzero solution in `Breve E`. -/
theorem exists_frobenius_eq_mul_of_sub_one_mem {u : 𝒪[E]} (hu : u - 1 ∈ 𝓂[E]) :
    ∃ y : Breve E, y ≠ 0 ∧ frobenius E y = algebraMap E (Breve E) (u : E) * y :=
  ValuativeExtension.exists_apply_eq_mul_of_sub_one_mem_maximalIdeal
    mapValueGroupWithZero_breve_surjective (frobenius E) Finite.one_lt_card
    (fun _ hz ↦ frobenius_congr hz) hu

variable (E) in
/-- **In characteristic zero, `Breve E` has infinite transcendence degree over `E`.** Following
[Chen], Proposition 2.0.3, solving `σ(y_ℓ) = ℓ^{q-1} y_ℓ` for primes `ℓ` strictly exceeding the
residue characteristic yields an infinite family of nonzero `σ`-eigenvectors with multiplicatively
independent eigenvalues in `E`. -/
theorem transcendenceDegree_infinite [CharZero E] :
    Cardinal.aleph0 ≤ Algebra.trdeg E (Breve E) := by
  classical
  let p : ℕ := ringChar 𝓀[E]
  let _ : Fintype 𝓀[E] := Fintype.ofFinite 𝓀[E]
  let q : ℕ := Nat.card 𝓀[E]
  have hq_card : q = Fintype.card 𝓀[E] := Nat.card_eq_fintype_card
  have hq_sub : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt Finite.one_lt_card
  let ι := {ℓ : ℕ // Nat.Prime ℓ ∧ p < ℓ}
  have hinf : Infinite ι := by
    have hs : {ℓ : ℕ | Nat.Prime ℓ ∧ p < ℓ}.Infinite := by
      refine (Nat.infinite_setOfPred_prime.sdiff (Set.finite_le_nat p)).mono ?_
      exact fun _ h ↦ ⟨h.1, not_le.1 h.2⟩
    exact hs.to_subtype
  let u₀ : ι → 𝒪[E] := fun ℓ ↦ (ℓ.1 : 𝒪[E]) ^ (q - 1)
  have hu₀_mem (ℓ : ι) : u₀ ℓ - 1 ∈ 𝓂[E] := by
    let ψ := IsLocalRing.residue 𝒪[E]
    refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
    have hℓ_ne : (ℓ.1 : 𝓀[E]) ≠ 0 := fun h0 ↦ by
      rcases (Nat.dvd_prime ℓ.2.1).1 ((CharP.cast_eq_zero_iff 𝓀[E] p ℓ.1).1 h0) with hp1 | hp_eq
      · exact (CharP.char_is_prime 𝓀[E] p).ne_one hp1
      · exact ℓ.2.2.ne hp_eq
    rw [ψ.map_sub, ψ.map_one, ψ.map_pow, map_natCast, sub_eq_zero, hq_card]
    exact FiniteField.pow_card_sub_one_eq_one (ℓ.1 : 𝓀[E]) hℓ_ne
  choose y hy0 hy_frob using fun ℓ : ι ↦ exists_frobenius_eq_mul_of_sub_one_mem (hu₀_mem ℓ)
  let u : ι → E := fun ℓ ↦ ((u₀ ℓ : 𝒪[E]) : E)
  have hu_eq : (fun d : ι →₀ ℕ ↦ d.prod fun ℓ k ↦ u ℓ ^ k) =
      fun d : ι →₀ ℕ ↦ d.prod fun ℓ k ↦ ((ℓ.1 : E) ^ (q - 1)) ^ k := by
    ext d
    exact Finsupp.prod_congr fun ℓ _ ↦ by simp [u, u₀]
  have hu_inj : Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun ℓ k ↦ u ℓ ^ k := by
    rw [hu_eq]
    exact finsuppProd_natCast_prime_pow_injective (fun ℓ ↦ ℓ.2.1) Subtype.val_injective hq_sub
  have hind : AlgebraicIndependent E y :=
    (frobenius E).toAlgHom.algebraicIndependent_of_algHom_eigenvectors hy0 hy_frob hu_inj
  have hle : Cardinal.lift.{_, 0} (Cardinal.mk ι) ≤ Algebra.trdeg E (Breve E) := by
    simpa only [Cardinal.lift_uzero] using hind.lift_cardinalMk_le_trdeg
  exact Cardinal.lift_aleph0.symm.trans_le
    ((Cardinal.lift_le.2 (Cardinal.aleph0_le_mk ι)).trans hle)

variable (E) in
/-- **In characteristic zero, `Breve E` has infinite transcendence degree over `E^{ur}`.** -/
theorem transcendenceDegree_unramified_infinite [CharZero E] :
    Cardinal.aleph0 ≤ Algebra.trdeg (Unramified E) (Breve E) := by
  rw [trdeg_eq_of_isAlgebraic_base (R := E) (S := Unramified E) (A := Breve E)]
  exact transcendenceDegree_infinite E

end TauCeti.MaxUnramifiedCompletion
