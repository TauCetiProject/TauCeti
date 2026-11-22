/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Stabilization
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Singularity.Tate
import TauCeti.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.Exponent

/-!
# Tate's genus-change theorem in positive characteristic

In characteristic `p > 0`, the genus of an algebraic function field `F / k` with exact constant
field `k` can drop under an inseparable algebraic constant field extension `F' = F · k'`, and new
constants `k'' ⊇ k'` may appear in `F'`. Tate proved in 1952 that the genus drop is constrained by
a congruence modulo `p - 1`:

`(p - 1) ∣ 2 (g(F / k) - g(F' / k''))`,

and hence `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')` for every odd prime `p`. In particular, whenever
`2 g(F / k) < p - 1` (or `g(F / k) < (p - 1) / 2` for `p ≠ 2`), the genus is conserved across
every algebraic constant field extension. Both bounds are sharp: for an odd prime `p` and a
transcendental `a`, the hyperelliptic-like curve `y ^ 2 = x ^ p - a` over `𝔽_p(a)` has genus
`(p - 1) / 2` and drops to genus `0` over `𝔽_p(a ^ (1 / p))`, while for `p = 2` the curve
`y ^ 2 = x ^ 3 + a` over `𝔽_2(a)` has genus `1` and drops to genus `0` over `𝔽_2(a ^ (1 / 2))`.

Following Schröer (2009), we prove Tate's theorem without differentials by combining the global
genus-change formula `g(F / k) - 1 = [k'' : k'] (g(F' / k'') - 1) + ∑_P δ_P` from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change` with the local divisibility
`(p - 1) ∣ 2 δ_P` for a purely inseparable constant step of prime degree `p` from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Singularity.Tate`. General algebraic
constant extensions reduce to finite ones by
`TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`, split at the separable closure
of `k`, and induct along prime-degree purely inseparable steps inside the exact constant field
upstairs.

## Main results

* `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn`,
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top`, and
  `TauCeti.sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top`:
  Tate's genus-change divisibility `(p - 1) ∣ 2 (g(F / k) - g(F' / k''))` for arbitrary algebraic
  constant extensions in characteristic `p`, with or without constant growth.
* `TauCeti.sub_one_div_two_dvd_genus_sub_genus_of_constantCompositum_eq_top`: for `p ≠ 2`,
  `(p - 1) / 2 ∣ g(F / k) - g(F' / k'')`.
* `TauCeti.genus_eq_genus_of_two_mul_genus_lt_sub_one`,
  `TauCeti.genus_eq_genus_of_genus_lt_sub_one_div_two`, and
  `TauCeti.isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one`: genus conservation
  and preservation of exact constants when `2 g(F / k) < p - 1`.

## References

* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
-/

public section

open IntermediateField Module

namespace TauCeti

universe u u' v v'

/-! ### Tate's genus-change theorem -/

section Tate

/-- Tate's genus-change divisibility for a single purely inseparable constant step of prime degree
`p`, allowing constant growth into an exact constant field `k''` of `F'`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime {k : Type u}
    {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k k'] (hk' : finrank k k' = p) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' ≤ genus k F ∧ (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos (hk' ▸ hp.pos)
  have hFF' : finrank F F' = p := by
    have hdeg := finrank_constantCompositum_eq_finrank_of_finrank_prime F k' F' hex (hk' ▸ hp)
    rwa [h, IntermediateField.finrank_top', hk'] at hdeg
  have hn : finrank F F' = finrank k k' := hFF'.trans hk'.symm
  have hF' := hF.of_constantCompositum_eq_top h
  have : FiniteDimensional k' k'' := hF'.finiteDimensional_of_isAlgebraic k''
  have : IsPurelyInseparable F F' := isPurelyInseparable_of_constantCompositum_eq_top (k := k) h
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime hp
  have : IsPurelyInseparable k' k'' :=
    isPurelyInseparable_enlargement_of_finrank_eq_prime hp hex hFF' (k'' := k'')
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow k' k'' p
  have hfin := finite_setOf_singularityDegree_ne_zero hF hex h hn
  have heq := genus_sub_one_eq_finrank_mul_genus_sub_one_add_finsum_singularityDegree
    hF hex h hn hex''
  have hsupp : (Function.support fun P : Place k F ↦ (P.singularityDegree k' F' : ℤ)) ⊆
      hfin.toFinset := fun P hP ↦ by simpa [Function.mem_support] using hP
  rw [finsum_eq_sum_of_support_subset _ hsupp] at heq
  have hgle : genus k'' F' ≤ genus k F := by
    have hm1 : (1 : ℤ) ≤ finrank k' k'' := by exact_mod_cast (finrank_pos (R := k') (M := k''))
    have hsum : (0 : ℤ) ≤ ∑ P ∈ hfin.toFinset, (P.singularityDegree k' F' : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    by_cases hg0 : genus k'' F' = 0 <;> [omega; nlinarith]
  have hid : (2 * ((genus k F : ℤ) - genus k'' F') : ℤ) =
      2 * ((finrank k' k'' : ℤ) - 1) * ((genus k'' F' : ℤ) - 1) +
        ∑ P ∈ hfin.toFinset, (2 * (P.singularityDegree k' F' : ℤ)) := by
    rw [← Finset.mul_sum]; linarith
  have hp1 : 1 ≤ p := hp.pos
  have hdvd_z : ((p : ℤ) - 1) ∣ 2 * ((genus k F : ℤ) - genus k'' F') := by
    rw [hid]
    refine dvd_add ?_ (Finset.dvd_sum fun P _ ↦ ?_)
    · rw [hm, Nat.cast_pow]
      exact (dvd_mul_of_dvd_right (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 m) 2).mul_right _
    · have hdvdP := Int.natCast_dvd_natCast.2
        (P.sub_one_dvd_two_mul_singularityDegree_of_finrank_eq_prime hk' hF hex h)
      rwa [Nat.cast_sub hp1, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hdvdP
  refine ⟨hgle, (Int.natCast_dvd_natCast.1 ?_)⟩
  simpa [hp1, hgle] using hdvd_z

/-- Single prime-step decomposition inside a nontrivial finite purely inseparable constant
extension `K → M` with exact constants on both sides: given an intermediate field `L` of degree `p`
over `K`, cutting out `L₁ = (E · L) ∩ M` as an intermediate field over `L` produces a strict
subextension `L₁ → M` with exact constants in `E · L` whose genus drop from `E / K` satisfies
Tate's divisibility. -/
private theorem exists_step_of_finrank_eq_prime {K M : Type u'} {E F' : Type v'} [Field K]
    [Field M] [Field E] [Field F'] [Algebra K M] [Algebra K E] [Algebra K F'] [Algebra M F']
    [Algebra E F'] [IsScalarTower K M F'] [IsScalarTower K E F'] {p : ℕ} [Fact p.Prime] [CharP K p]
    [IsPurelyInseparable K M] [FiniteDimensional K M] (L : IntermediateField K M)
    (hL : finrank K L = p) (hE : IsFunctionField K E) (hexK : IsIntegrallyClosedIn K E)
    (hEM : constantCompositum E M F' = ⊤) (hexM : IsIntegrallyClosedIn M F') :
    ∃ (L₁ : IntermediateField L M) (EL : Type v') (_ : Field EL) (_ : Algebra L₁ EL)
      (_ : Algebra EL F') (_ : IsScalarTower L₁ EL F'),
      finrank L₁ M < finrank K M ∧ IsFunctionField L₁ EL ∧ IsIntegrallyClosedIn L₁ EL ∧
        constantCompositum EL M F' = ⊤ ∧ genus L₁ EL ≤ genus K E ∧
        (p - 1) ∣ 2 * (genus K E - genus L₁ EL) := by
  let EL := constantCompositum E L F'
  let _ := constantCompositumAlgebra E L F'
  have := isScalarTower_constantCompositum E L F'
  have := isScalarTower_base_constantCompositum K E L F'
  have hEL : constantCompositum E L EL = ⊤ := (constantCompositum_eq_top_iff E L F' EL).2 rfl
  let L₀ : IntermediateField K M := (EL.restrictScalars K).comap (IsScalarTower.toAlgHom K M F')
  have hmemL₀ (m : M) : m ∈ L₀ ↔ algebraMap M F' m ∈ EL := Iff.rfl
  have hLL₀ : L ≤ L₀ := fun m hm ↦ (hmemL₀ m).2 <| by
    have hmem := algebraMap_mem_constantCompositum E L F' ⟨m, hm⟩
    rwa [IsScalarTower.algebraMap_apply L M F', IntermediateField.algebraMap_apply] at hmem
  let L₁ : IntermediateField L M := IntermediateField.extendScalars hLL₀
  have hmEL (m : L₁) : algebraMap L₁ F' m ∈ EL := by
    rw [IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
    exact (hmemL₀ (m : M)).1 ((IntermediateField.mem_extendScalars hLL₀).1 m.property)
  let _ : Algebra L₁ EL := ((algebraMap L₁ F').codRestrict EL hmEL).toAlgebra
  have hst : IsScalarTower L₁ EL F' := .of_algebraMap_eq fun m ↦ by
    rw [IntermediateField.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]
  have : IsScalarTower L L₁ EL := .of_algebraMap_eq fun c ↦ (algebraMap EL F').injective <| by
    rw [← IsScalarTower.algebraMap_apply L EL F', ← IsScalarTower.algebraMap_apply L₁ EL F',
      ← IsScalarTower.algebraMap_apply L L₁ F']
  have : FiniteDimensional L M := FiniteDimensional.right K L M
  have : FiniteDimensional L L₁ := FiniteDimensional.left L L₁ M
  have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
  have hexL₁ : IsIntegrallyClosedIn L₁ EL :=
    isIntegrallyClosedIn_iff.2 ⟨(algebraMap L₁ EL).injective, fun {y} hy ↦ by
      have hyM : IsIntegral M (y : F') := (hy.map (IsScalarTower.toAlgHom L₁ EL F')).tower_top
      obtain ⟨m, hm⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hyM
      have hm₀ : m ∈ L₀ := (hmemL₀ m).2 (hm.symm ▸ y.property)
      refine ⟨⟨m, (IntermediateField.mem_extendScalars hLL₀).2 hm₀⟩, Subtype.ext ?_⟩
      rw [RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
        IsScalarTower.algebraMap_apply L₁ M F', IntermediateField.algebraMap_apply]
      exact hm⟩
  obtain ⟨hgle₁, hdvd₁⟩ :=
    sub_one_dvd_two_mul_genus_sub_genus_of_finrank_eq_prime hL hE hexK hEL (k'' := L₁) hexL₁
  have hlt : finrank L₁ M < finrank K M := by
    have h1 := finrank_mul_finrank K L M
    have h2 := finrank_mul_finrank L L₁ M
    have hp : p.Prime := Fact.out
    have := hp.one_lt
    have : 0 < finrank L L₁ := finrank_pos
    have : 0 < finrank L₁ M := finrank_pos
    nlinarith
  exact ⟨L₁, EL, inferInstance, inferInstance, inferInstance, hst, hlt,
    (hE.of_constantCompositum_eq_top hEL).of_isAlgebraic, hexL₁,
    constantCompositum_eq_top_of_eq_top E M F' EL hEM, hgle₁, hdvd₁⟩

/-- Induction over finite purely inseparable constant extensions with exact constants on both
sides, stepping along intermediate fields of prime degree `p`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite (p : ℕ)
    [Fact p.Prime] (n : ℕ) :
    ∀ (K M : Type u') (E F' : Type v') [Field K] [Field M] [Field E] [Field F'] [Algebra K M]
      [Algebra K E] [Algebra K F'] [Algebra M F'] [Algebra E F'] [IsScalarTower K M F']
      [IsScalarTower K E F'] [CharP K p] [IsPurelyInseparable K M] [FiniteDimensional K M],
      finrank K M = n → IsFunctionField K E → IsIntegrallyClosedIn K E →
      constantCompositum E M F' = ⊤ → IsIntegrallyClosedIn M F' →
      (p - 1) ∣ 2 * (genus K E - genus M F') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K M E F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hE hexK hEM hexM
  by_cases hsurj : Function.Surjective (algebraMap K M)
  · have hbij : Function.Bijective (algebraMap K M) := ⟨(algebraMap K M).injective, hsurj⟩
    have : Algebra.IsSeparable K M :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofBijective (Algebra.ofId K M) hbij)
    rw [genus_eq_genus_of_constantCompositum_eq_top hE hexK hEM, Nat.sub_self, mul_zero]
    exact dvd_zero _
  · obtain ⟨L, hL⟩ :=
      TauCeti.IsPurelyInseparable.exists_intermediateField_finrank_eq_expChar p hsurj
    obtain ⟨L₁, EL, _, _, _, _, hlt, hFEL₁, hexL₁, hELM_top, hgle₁, hdvd₁⟩ :=
      exists_step_of_finrank_eq_prime L hL hE hexK hEM hexM
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap L L₁).injective p
    have : IsPurelyInseparable L M := IsPurelyInseparable.tower_top K L M
    have : IsPurelyInseparable L₁ M := IsPurelyInseparable.tower_top L L₁ M
    have : FiniteDimensional L M := FiniteDimensional.right K L M
    have : FiniteDimensional L₁ M := FiniteDimensional.right L L₁ M
    have hdvd₂ := ih _ (hn ▸ hlt) L₁ M EL F' rfl hFEL₁ hexL₁ hELM_top hexM
    have hgle₂ : genus M F' ≤ genus L₁ EL :=
      genus_le_genus_of_constantCompositum_eq_top hFEL₁ hELM_top
    have hsplit : 2 * (genus K E - genus M F') =
        2 * (genus K E - genus L₁ EL) + 2 * (genus L₁ EL - genus M F') := by omega
    rw [hsplit]
    exact dvd_add hdvd₁ hdvd₂

/-- Tate's genus-change divisibility for a finite algebraic constant field extension with exact
constants on both sides, splitting `k → M` at the separable closure of `k` in `M`. -/
private theorem sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn
    {k : Type u} {M : Type u'} {F : Type v} {FM : Type v'} [Field k] [Field M] [Field F]
    [Field FM] [Algebra k M] [Algebra k F] [Algebra k FM] [Algebra M FM] [Algebra F FM]
    [IsScalarTower k M FM] [IsScalarTower k F FM] {p : ℕ} [Fact p.Prime] [CharP k p]
    [FiniteDimensional k M] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hFM : constantCompositum F M FM = ⊤) (hexM : IsIntegrallyClosedIn M FM) :
    (p - 1) ∣ 2 * (genus k F - genus M FM) := by
  let S : IntermediateField k M := separableClosure k M
  let FS := constantCompositum F S FM
  let := constantCompositumAlgebra F S FM
  have := isScalarTower_constantCompositum F S FM
  have := isScalarTower_base_constantCompositum k F S FM
  have hFS : constantCompositum F S FS = ⊤ := (constantCompositum_eq_top_iff F S FM FS).2 rfl
  have hFFS : IsFunctionField S FS := hF.of_constantCompositum_eq_top hFS
  have hexS : IsIntegrallyClosedIn S FS := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hFS
  have hgS : genus S FS = genus k F := genus_eq_genus_of_constantCompositum_eq_top hF hex hFS
  have hFSM : constantCompositum FS M FM = ⊤ := constantCompositum_eq_top_of_eq_top F M FM FS hFM
  have : CharP S p := charP_of_injective_algebraMap (algebraMap k S).injective p
  have : IsPurelyInseparable S M := separableClosure.isPurelyInseparable k M
  rw [← hgS]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isPurelyInseparable_of_finite p (finrank S M)
    S M FS FM rfl hFFS hexS hFSM hexM

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **Tate's genus-change theorem** (exact constants): for any algebraic constant field extension
`F' = F · k'` of a function field `F / k` in prime characteristic `p`, finite or infinite, if `k`
is exact in `F` and `k'` is exact in `F'`, then `p - 1` divides `2 (g(F / k) - g(F' / k'))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hex' : IsIntegrallyClosedIn k' F') :
    (p - 1) ∣ 2 * (genus k F - genus k' F') := by
  obtain ⟨L, _, hexL, hgL⟩ := exists_finiteDimensional_isIntegrallyClosedIn_genus_eq hF h hex'
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  have := isScalarTower_constantCompositum F L F'
  have := isScalarTower_base_constantCompositum k F L F'
  have hFL : constantCompositum F L FL = ⊤ := (constantCompositum_eq_top_iff F L F' FL).2 rfl
  rw [← hgL]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_finite_of_isIntegrallyClosedIn hF hex hFL hexL

/-- **Tate's genus-change theorem** (allowing constant growth): for any algebraic constant field
extension `F' = F · k'` of a function field `F / k` in prime characteristic `p` with `k` exact in
`F`, and any algebraic enlargement `k'' / k'` inside `F'` that is exact in `F'`, `p - 1` divides
`2 (g(F / k) - g(F' / k''))`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    (p - 1) ∣ 2 * (genus k F - genus k'' F') := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  exact sub_one_dvd_two_mul_genus_sub_genus_of_isIntegrallyClosedIn hF hex
    (constantCompositum_eq_top_of_isScalarTower h) hex''

/-- **Tate's genus-change theorem for `algebraicClosure k' F'`**: specialization of
`TauCeti.sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top` to
`k'' = algebraicClosure k' F'` for an algebraic constant field extension `F' = F · k'` of a function
field `F / k` in prime characteristic `p` with `k` exact in `F`, requiring no exactness hypothesis
on `k'` in `F'`. -/
theorem sub_one_dvd_two_mul_genus_sub_genus_algebraicClosure_of_constantCompositum_eq_top {p : ℕ}
    [Fact p.Prime] [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    (p - 1) ∣ 2 * (genus k F - genus (algebraicClosure k' F') F') :=
  sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))

/-- **Odd-characteristic Tate divisibility**: for a function field `F / k` in odd prime
characteristic `p` with `k` exact in `F`, `(p - 1) / 2` divides the genus drop
`g(F / k) - g(F' / k'')` across any algebraic constant field extension `F' = F · k'` and any
algebraic extension `k'' / k'` inside `F'` that is exact in `F'`. -/
theorem sub_one_div_two_dvd_genus_sub_genus_of_constantCompositum_eq_top {p : ℕ} [Fact p.Prime]
    [CharP k p] (hp2 : p ≠ 2) [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    ((p - 1) / 2) ∣ genus k F - genus k'' F' := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  refine (Nat.mul_dvd_mul_iff_left two_pos).1 ?_
  rw [h2]
  exact sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''

/-- **Genus conservation in small genus**: for a function field `F / k` in prime characteristic `p`
with `k` exact in `F`, if `2 g(F / k) < p - 1`, then `g(F' / k'') = g(F / k)` for every algebraic
constant field extension `F' = F · k'` and every algebraic extension `k'' / k'` inside `F'` that is
exact in `F'`. -/
theorem genus_eq_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : 2 * genus k F < p - 1)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  have hgle : genus k'' F' ≤ genus k F :=
    genus_le_genus_of_constantCompositum_eq_top hF (constantCompositum_eq_top_of_isScalarTower h)
  have hdvd := sub_one_dvd_two_mul_genus_sub_genus_of_constantCompositum_eq_top hF hex h hex''
  have hzero : 2 * (genus k F - genus k'' F') = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

/-- **Genus conservation in odd characteristic**: for a function field `F / k` in odd prime
characteristic `p` with `k` exact in `F`, if `g(F / k) < (p - 1) / 2`, then
`g(F' / k'') = g(F / k)` for every algebraic constant field extension `F' = F · k'` and every
algebraic extension `k'' / k'` inside `F'` that is exact in `F'`. -/
theorem genus_eq_genus_of_genus_lt_sub_one_div_two {p : ℕ} [Fact p.Prime] [CharP k p] (hp2 : p ≠ 2)
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (hlt : genus k F < (p - 1) / 2)
    {k'' : Type*} [Field k''] [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k' k''] (hex'' : IsIntegrallyClosedIn k'' F') :
    genus k'' F' = genus k F := by
  have hp : p.Prime := Fact.out
  have h2 : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' ((hp.odd_of_ne_two hp2).tsub_odd odd_one).two_dvd
  exact genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h (by omega) hex''

/-- **Exactness of constants in small positive genus**: for a function field `F / k` in prime
characteristic `p` with exact constant field `k`, if `1 ≤ g(F / k)` and `2 g(F / k) < p - 1`, then
for every algebraic constant field extension `F' = F · k'` (finite or infinite), `k'` remains the
exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_one_le_genus_of_two_mul_genus_lt_sub_one {p : ℕ} [Fact p.Prime]
    [CharP k p] [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (hg1 : 1 ≤ genus k F) (hlt : 2 * genus k F < p - 1) :
    IsIntegrallyClosedIn k' F' :=
  isIntegrallyClosedIn_of_one_le_genus_of_genus_eq hF hex h hg1
    (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F'))
    (genus_eq_genus_of_two_mul_genus_lt_sub_one hF hex h hlt
      (isIntegrallyClosedIn_algebraicClosure (k := k') (F := F')))

end Tate

end TauCeti
