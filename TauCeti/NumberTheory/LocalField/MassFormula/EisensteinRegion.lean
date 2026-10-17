/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import TauCeti.MeasureTheory.Group.Measure
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.Module.Compact

/-!
# The Eisenstein region of coefficient space

Serre's mass formula is proved by integrating over the space of Eisenstein polynomials. A monic
polynomial of degree `n` over a nonarchimedean local field `K` is identified with its coefficient
vector `a : Fin n → K`, through `TauCeti.toPoly a = X ^ n + ∑ i, a i * X ^ i`, and the
*Eisenstein region* `TauCeti.eisensteinSet K n` is the set of coefficient vectors all of whose
entries lie in the open unit ball, the constant term having the largest valuation below `1`, that
of a uniformizer. By `TauCeti.mem_eisensteinSet_iff` these are exactly the coefficient vectors of
the polynomials over `𝒪[K]` that are Eisenstein at `𝓂[K]`.

The coefficient space `ι → K` carries the additive Haar measure normalized so that the integer box
`TauCeti.integerBox K ι = 𝒪[K] ^ ι` has volume `1`. For such a measure, writing `q` for the
cardinality of the residue field, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume
`q ^ (-∑ i, e i)`, since it is a subgroup of index `q ^ (∑ i, e i)` of the integer box. The
Eisenstein region is the difference of two such boxes, so its volume is `q ^ (-n) (1 - q⁻¹)`.

The measure statements assume only left invariance of the measure and the normalization; no
product structure on the measure is used.

## Main definitions

* `TauCeti.toPoly a`: the monic polynomial `X ^ n + ∑ i, a i * X ^ i` of a coefficient vector.
* `TauCeti.eisensteinSet K n`: the Eisenstein region in `Fin n → K`.
* `TauCeti.integerBox K ι`: the integer box `𝒪[K] ^ ι` in `ι → K`.

## Main results

* `TauCeti.mem_eisensteinSet_iff`: a coefficient vector lies in the Eisenstein region exactly when
  it is the coefficient vector of a polynomial over `𝒪[K]` that is Eisenstein at `𝓂[K]`.
* `TauCeti.measure_univ_pi_image_maximalIdeal_pow`: the box with factors `𝓂[K] ^ e i` has volume
  `q ^ (-∑ i, e i)`.
* `TauCeti.measure_eisensteinSet`: the Eisenstein region has volume `q ^ (-n) (1 - q⁻¹)`.

## Implementation notes

`toPoly a` is written as `X ^ n + ∑ i, C (a i) * X ^ i` rather than through Mathlib's
`Polynomial.ofFn`, whose definition requires decidable equality on the coefficient ring.

The volume of a box of ideals is read off `AddSubgroup.relIndex_mul_measure`: the box is an additive
subgroup of the integer box, and its relative index is computed coordinatewise from
`cardQuot_pow_of_prime`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2.
-/

public section
noncomputable section

open Polynomial MeasureTheory ValuativeRel
open scoped ENNReal

namespace TauCeti

section toPoly

variable {R S : Type*} [Semiring R] [Semiring S] {n : ℕ}

/-- The monic polynomial of degree `n` with coefficient vector `a`, that is
`X ^ n + ∑ i, a i * X ^ i`: the entry `a i` is the coefficient of `X ^ i`. -/
def toPoly (a : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)

/-- The defining formula of `toPoly`. -/
theorem toPoly_def (a : Fin n → R) : toPoly a = X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ) := by
  rw [toPoly]

/-- The coefficients of `toPoly a` are `a` below the degree `n` and `1` in degree `n`. -/
private theorem coeff_toPoly (a : Fin n → R) (j : ℕ) :
    (toPoly a).coeff j = (if j = n then 1 else 0) + ∑ i : Fin n, if j = i then a i else 0 := by
  simp only [toPoly, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]

/-- Below the degree, the coefficients of `toPoly a` are the entries of `a`. -/
theorem coeff_toPoly_of_lt (a : Fin n → R) {i : ℕ} (hi : i < n) :
    (toPoly a).coeff i = a ⟨i, hi⟩ := by
  rw [coeff_toPoly, ite_eq_right hi.ne, zero_add, Fintype.sum_eq_single ⟨i, hi⟩ fun j hj ↦
    ite_eq_right fun h ↦ hj (Fin.ext h.symm), ite_eq_left rfl]

/-- The coefficient of `X ^ n` in `toPoly a` is `1`. -/
@[simp]
theorem coeff_toPoly_self (a : Fin n → R) : (toPoly a).coeff n = 1 := by
  rw [coeff_toPoly, ite_eq_left rfl, Finset.sum_eq_zero fun i _ ↦ ite_eq_right i.isLt.ne', add_zero]

/-- Above the degree, the coefficients of `toPoly a` vanish. -/
theorem coeff_toPoly_eq_zero_of_lt (a : Fin n → R) {i : ℕ} (hi : n < i) :
    (toPoly a).coeff i = 0 := by
  rw [coeff_toPoly, ite_eq_right hi.ne', zero_add,
    Finset.sum_eq_zero fun j _ ↦ ite_eq_right (j.isLt.trans hi).ne']

/-- `toPoly a` is monic. -/
theorem monic_toPoly (a : Fin n → R) : (toPoly a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

/-- `toPoly a` has degree `n`. -/
@[simp]
theorem natDegree_toPoly [Nontrivial R] (a : Fin n → R) : (toPoly a).natDegree = n := by
  rw [toPoly, natDegree_add_eq_left_of_degree_lt
    ((degree_sum_fin_lt a).trans_eq (degree_X_pow n).symm), natDegree_X_pow]

/-- Mapping `toPoly a` along a ring homomorphism maps its coefficient vector. -/
theorem map_toPoly (f : R →+* S) (a : Fin n → R) : (toPoly a).map f = toPoly (f ∘ a) := by
  ext i
  rw [coeff_map]
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [coeff_toPoly_of_lt _ hi, coeff_toPoly_of_lt _ hi, Function.comp_apply]
  · rw [coeff_toPoly_self, coeff_toPoly_self, map_one]
  · rw [coeff_toPoly_eq_zero_of_lt _ hi, coeff_toPoly_eq_zero_of_lt _ hi, map_zero]

end toPoly

variable {K : Type*} [Field K] [ValuativeRel K]

section CoefficientSpace

variable (K) in
/-- The Eisenstein region in the space `Fin n → K` of coefficient vectors of monic polynomials of
degree `n`: every coefficient has valuation below `1`, and the constant term has the largest
valuation below `1`, that of a uniformizer. By
`TauCeti.mem_eisensteinSet_iff_exists_isEisensteinAt` these are the coefficient vectors of the
Eisenstein polynomials over `𝒪[K]`. -/
def eisensteinSet (n : ℕ) : Set (Fin n → K) :=
  {a | (∀ i, valuation K (a i) < 1) ∧
    ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((toPoly a).coeff 0)}

/-- Membership in the Eisenstein region, unfolded. -/
theorem mem_eisensteinSet {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔ (∀ i, valuation K (a i) < 1) ∧
      ∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K ((toPoly a).coeff 0) :=
  Iff.rfl

variable (K) in
/-- The integer box `𝒪[K] ^ ι` of the coefficient space `ι → K`, on which the Haar measure of the
coefficient space is normalized. -/
def integerBox (ι : Type*) : Set (ι → K) :=
  Set.univ.pi fun _ ↦ (𝒪[K] : Set K)

/-- Membership in the integer box: every coordinate is integral. -/
@[simp]
theorem mem_integerBox {ι : Type*} {a : ι → K} : a ∈ integerBox K ι ↔ ∀ i, a i ∈ 𝒪[K] := by
  simp [integerBox]

end CoefficientSpace

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Valuation

/-- An integer of `K` lies in the maximal ideal exactly when its valuation is below `1`. -/
private theorem valuation_lt_one_iff_mem_maximalIdeal {x : 𝒪[K]} :
    valuation K x < 1 ↔ x ∈ 𝓂[K] := by
  rw [← Valuation.Integer.not_isUnit_iff_valuation_lt_one, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]

/-- An element of `K` has valuation below `1` exactly when it lies in the maximal ideal of
`𝒪[K]`. -/
private theorem valuation_lt_one_iff_mem_image {x : K} :
    valuation K x < 1 ↔ x ∈ ((↑) : 𝒪[K] → K) '' ↑𝓂[K] := by
  refine ⟨fun hx ↦ ⟨⟨x, (Valuation.mem_integer_iff _ _).2 hx.le⟩,
    valuation_lt_one_iff_mem_maximalIdeal.1 hx, rfl⟩, ?_⟩
  rintro ⟨c, hc, rfl⟩
  exact valuation_lt_one_iff_mem_maximalIdeal.2 hc

/-- An element `c` of the maximal ideal of `𝒪[K]` has the largest valuation below `1`, that of a
uniformizer, exactly when it does not lie in the square of the maximal ideal. -/
private theorem forall_valuation_le_iff_notMem_sq {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    (∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K c) ↔ c ∉ 𝓂[K] ^ 2 := by
  constructor
  · -- If `c = ϖ ^ 2 * d`, then `c` has valuation below that of the uniformizer `ϖ`.
    intro h hc2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc2
    obtain ⟨d, rfl⟩ := hc2
    have hϖ1 : valuation K ϖ < 1 :=
      valuation_lt_one_iff_mem_maximalIdeal.2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    have hϖ0 : 0 < valuation K ϖ := by
      rw [zero_lt_iff, Ne, map_eq_zero, ZeroMemClass.coe_eq_zero]
      exact hϖ.ne_zero
    have hd : valuation K d ≤ 1 := (Valuation.mem_integer_iff _ _).1 d.2
    have hle := h ϖ hϖ1
    rw [MulMemClass.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow] at hle
    exact (hle.trans (mul_le_of_le_one_right' hd)).not_gt (pow_lt_self_of_lt_one₀ hϖ0 hϖ1
      one_lt_two)
  · -- If `y ∈ 𝓂` had larger valuation than `c`, then `c = y * (c / y)` would lie in `𝓂 ^ 2`.
    intro hc2 y hy
    by_contra! hlt
    have hy0 : 0 < valuation K y := zero_le.trans_lt hlt
    have hz : valuation K (c / y) < 1 := by
      rwa [map_div₀, div_lt_one₀ hy0]
    refine hc2 ?_
    have hcy : c = ⟨y, (Valuation.mem_integer_iff _ _).2 hy.le⟩ *
        ⟨c / y, (Valuation.mem_integer_iff _ _).2 hz.le⟩ := by
      ext
      rw [MulMemClass.coe_mul, mul_div_cancel₀ _ ((_root_.map_ne_zero _).1 hy0.ne')]
    rw [hcy, pow_two]
    exact Ideal.mul_mem_mul (valuation_lt_one_iff_mem_maximalIdeal.1 hy)
      (valuation_lt_one_iff_mem_maximalIdeal.1 hz)

end Valuation

section EisensteinPolynomial

/-- **The Eisenstein region is the set of Eisenstein polynomials**: a coefficient vector lies in
`eisensteinSet K n` exactly when it is the coefficient vector of a polynomial over `𝒪[K]` that is
Eisenstein at `𝓂[K]`. -/
theorem mem_eisensteinSet_iff_exists_isEisensteinAt {n : ℕ} {a : Fin n → K} :
    a ∈ eisensteinSet K n ↔
      ∃ f : 𝒪[K][X], f.map (algebraMap 𝒪[K] K) = toPoly a ∧ f.IsEisensteinAt 𝓂[K] := by
  constructor
  · rintro ⟨ha, h0⟩
    let c : Fin n → 𝒪[K] := fun i ↦ ⟨a i, (Valuation.mem_integer_iff _ _).2 (ha i).le⟩
    have hc : ∀ i, c i ∈ 𝓂[K] := fun i ↦ valuation_lt_one_iff_mem_maximalIdeal.1 (ha i)
    refine ⟨toPoly c, by rw [map_toPoly, Algebra.coe_algebraMap_ofSubsemiring]; rfl,
      ⟨?_, fun {i} hi ↦ ?_, ?_⟩⟩
    · rw [(monic_toPoly c).leadingCoeff]
      exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
    · rw [natDegree_toPoly] at hi
      rw [coeff_toPoly_of_lt _ hi]
      exact hc _
    · rcases n.eq_zero_or_pos with rfl | hn
      · rw [coeff_toPoly_self]
        exact fun h ↦ (Ideal.ne_top_iff_one _).1
          (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top (Ideal.pow_le_self two_ne_zero h)
      · rw [coeff_toPoly_of_lt _ hn]
        rw [coeff_toPoly_of_lt _ hn] at h0
        exact (forall_valuation_le_iff_notMem_sq (hc _)).1 h0
  · rintro ⟨f, hf, hE⟩
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
        natDegree_toPoly]
    have hcoeff (i : ℕ) : (toPoly a).coeff i = f.coeff i := by
      rw [← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [← coeff_toPoly_of_lt a i.isLt, hcoeff]
      exact valuation_lt_one_iff_mem_maximalIdeal.2 (hE.mem (hdeg ▸ i.isLt))
    · rcases n.eq_zero_or_pos with rfl | hn
      · intro y hy
        rw [coeff_toPoly_self, map_one]
        exact hy.le
      · rw [hcoeff]
        exact (forall_valuation_le_iff_notMem_sq (hE.mem (hdeg ▸ hn))).2 hE.notMem

end EisensteinPolynomial

section Measure

variable {ι : Type*}

variable (K) in
/-- The box `∏ i, 𝓂[K] ^ e i` of `ι → K`, as an additive subgroup. -/
private def idealBox (e : ι → ℕ) : AddSubgroup (ι → K) :=
  (AddSubgroup.pi Set.univ fun i ↦ (𝓂[K] ^ e i).toAddSubgroup).map
    ((𝒪[K].subtype : 𝒪[K] →+* K).toAddMonoidHom.compLeft ι)

private theorem coe_idealBox (e : ι → ℕ) :
    (idealBox K e : Set (ι → K)) = Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i) := by
  ext a
  simp only [idealBox, AddSubgroup.coe_map, AddSubgroup.coe_pi, Set.mem_image, Set.mem_univ_pi,
    Submodule.coe_toAddSubgroup, SetLike.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl⟩ i
    exact ⟨c i, hc i, rfl⟩
  · intro h
    choose c hc hca using h
    exact ⟨c, hc, _root_.funext hca⟩

/-- The index of `𝓂[K] ^ m` in `𝒪[K]` is `q ^ m`. -/
private theorem index_maximalIdeal_pow (m : ℕ) :
    (𝓂[K] ^ m).toAddSubgroup.index = Nat.card 𝓀[K] ^ m := by
  have h := cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[K]) (i := m)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
  -- The quotient by `(𝓂[K] ^ m).toAddSubgroup` is the quotient ring `𝒪[K] ⧸ 𝓂[K] ^ m`.
  rw [AddSubgroup.index_eq_card]
  refine h.trans (congrArg (· ^ m) (Nat.card_congr ?_))
  exact ((Ideal.quotEquivOfEq (IsLocalRing.ker_residue (R := 𝒪[K])).symm).trans
    (RingHom.quotientKerEquivOfSurjective IsLocalRing.residue_surjective)).toEquiv

private theorem isClosed_univ_pi_image_maximalIdeal_pow (e : ι → ℕ) :
    IsClosed (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) :=
  isClosed_set_pi fun _ _ ↦
    ((IsNoetherianRing.isClosed_ideal _).isCompact.image continuous_subtype_val).isClosed

/-- **The volume of a box of ideals**: for an additive Haar measure on `ι → K` normalized on the
integer box, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume `q ^ (-∑ i, e i)`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_univ_pi_image_maximalIdeal_pow [Fintype ι] [MeasurableSpace (ι → K)]
    [BorelSpace (ι → K)] (μ : Measure (ι → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K ι) = 1) (e : ι → ℕ) :
    μ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ∑ i, e i := by
  have hbox : (idealBox K (0 : ι → ℕ) : Set (ι → K)) = integerBox K ι := by
    simp [coe_idealBox, integerBox]
  have hle : idealBox K e ≤ idealBox K (0 : ι → ℕ) :=
    AddSubgroup.map_mono fun _ _ _ _ ↦ by simp
  have hindex : (idealBox K e).relIndex (idealBox K (0 : ι → ℕ)) = Nat.card 𝓀[K] ^ ∑ i, e i := by
    rw [idealBox, idealBox,
      AddSubgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective.comp_left]
    simp only [Pi.zero_apply, pow_zero, Ideal.one_eq_top, Submodule.top_toAddSubgroup,
      AddSubgroup.pi_top, AddSubgroup.relIndex_top_right, AddSubgroup.index_pi,
      index_maximalIdeal_pow, Finset.prod_pow_eq_pow_sum]
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hmeas (e : ι → ℕ) : MeasurableSet (idealBox K e : Set (ι → K)) := by
    rw [coe_idealBox]
    exact (isClosed_univ_pi_image_maximalIdeal_pow e).measurableSet
  have h := AddSubgroup.relIndex_mul_measure hle (by simp [hindex, Nat.card_pos.ne'])
    (hmeas e) (hmeas 0) μ
  rw [hindex, hbox, hμ, coe_idealBox] at h
  rw [ENNReal.eq_div_iff (pow_ne_zero _ hq) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]
  exact_mod_cast h

/-- **The volume of the Eisenstein region**: for an additive Haar measure on `Fin n → K` normalized
on the integer box, the Eisenstein region has volume `q ^ (-n) (1 - q⁻¹)`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_eisensteinSet {n : ℕ} (hn : 0 < n) [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinSet K n) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e : Fin n → ℕ := Function.update (fun _ ↦ 1) i₀ 2
  have he₀ : e i₀ = 2 := Function.update_self ..
  have he₁ (i : Fin n) (hi : i ≠ i₀) : e i = 1 := Function.update_of_ne hi ..
  -- The Eisenstein region is the box `𝓂[K] ^ n` minus the box with the constant term in `𝓂[K] ^ 2`.
  have hE : eisensteinSet K n = (Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 1)) \
      Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i) := by
    ext a
    simp only [Set.mem_sdiff, Set.mem_univ_pi, pow_one, ← valuation_lt_one_iff_mem_image,
      mem_eisensteinSet, coeff_toPoly_of_lt a hn]
    refine and_congr_right fun ha ↦ ?_
    have hc : (⟨a i₀, (Valuation.mem_integer_iff _ _).2 (ha i₀).le⟩ : 𝒪[K]) ∈ 𝓂[K] :=
      valuation_lt_one_iff_mem_maximalIdeal.1 (ha i₀)
    refine (forall_valuation_le_iff_notMem_sq hc).trans (not_congr ⟨fun h i ↦ ?_, fun h ↦ ?_⟩)
    · rcases eq_or_ne i i₀ with rfl | hi
      · rw [he₀]
        exact ⟨_, h, rfl⟩
      · rw [he₁ i hi, pow_one, ← valuation_lt_one_iff_mem_image]
        exact ha i
    · obtain ⟨c, hc, hca⟩ := h i₀
      rw [he₀] at hc
      rwa [show (⟨a i₀, _⟩ : 𝒪[K]) = c from Subtype.ext hca.symm]
  have hsub : (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) ⊆
      Set.univ.pi fun _ ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 1) :=
    Set.pi_mono fun i _ ↦ Set.image_mono <| Ideal.pow_le_pow_right <| by
      rcases eq_or_ne i i₀ with rfl | hi
      · rw [he₀]
        exact one_le_two
      · rw [he₁ i hi]
  have he : ∑ i, e i = n + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ _)),
      Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
    omega
  have h₁ := measure_univ_pi_image_maximalIdeal_pow μ hμ fun _ ↦ 1
  have h₂ := measure_univ_pi_image_maximalIdeal_pow μ hμ e
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h₁
  rw [he] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [hE, measure_sdiff hsub
    (isClosed_univ_pi_image_maximalIdeal_pow e).measurableSet.nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

end Measure

end TauCeti
