/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.NumberTheory.NumberField.SUnits.Lattice
import TauCeti.Analysis.AbsoluteValue.FiniteOrder
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Exponents in a finitely generated group of S-units are bounded by heights

Let `S` be a finite set of finite places of a number field `K`, and let `γ₁, …, γ_t` be
`S`-units that are multiplicatively independent: `∏ j, γ j ^ z j` is a root of unity only for
`z = 0`. Their images under the `S`-logarithmic embedding `ℓ` are then linearly independent over
`ℝ`, because they span a subgroup of the discrete `S`-unit lattice, where the ranks over `ℤ` and
over `ℝ` agree. So the map `z ↦ ∑ j, z j • ℓ(γ j)` has a continuous left inverse `T`, and since
the supremum norm of `ℓ(x)` is at most the logarithmic height of `x`,

`|z j| ≤ ‖T‖ * logHeight₁ (ζ * ∏ i, γ i ^ z i)`

for every root of unity `ζ`, every `z ∈ ℤ^t` and every `j`. This turns height bounds for the
elements of a finitely generated subgroup of `Kˣ` into bounds for their exponents, which is how
effective results on `S`-unit equations bound the exponents of the solutions.

## Main results

* `TauCeti.NumberField.SUnit.linearIndependent_logEmbedding`: multiplicatively independent
  `S`-units have `ℝ`-linearly independent `S`-logarithmic images.
* `TauCeti.NumberField.SUnit.abs_le_opNorm_mul_logHeight₁`: the exponent bound for a given left
  inverse `T`.
* `TauCeti.NumberField.SUnit.exists_abs_le_mul_logHeight₁`: for multiplicatively independent
  elements `γ j` of `K` which are units outside `S`, some `κ ≥ 0` bounds every exponent `|z j|`
  by `κ * logHeight₁ (ζ * ∏ i, γ i ^ z i)`.

## References

* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, Lemma 1.
* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Lemma 5.9.
-/

public section

open Finset Height IsDedekindDomain Module NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}
  {ι : Type*} [Fintype ι]

/-- **Multiplicatively independent `S`-units have linearly independent logarithms.** If no
product `∏ j, γ j ^ z j` with `z ≠ 0` is torsion, then the `S`-logarithmic images of the `γ j`
are linearly independent over `ℝ`. -/
theorem linearIndependent_logEmbedding {γ : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hγ : ∀ z : ι → ℤ,
      ∏ j, γ j ^ z j ∈ CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) → z = 0) :
    LinearIndependent ℝ fun j ↦ logEmbedding S (Additive.ofMul (γ j)) := by
  classical
  set v := fun j ↦ logEmbedding S (Additive.ofMul (γ j))
  have hℤ : LinearIndependent ℤ v := by
    refine Fintype.linearIndependent_iff.mpr fun z hz ↦ ?_
    have h1 := logEmbedding_mul_prod_zpow (γ := γ) (one_mem _) z
    rw [one_mul] at h1
    have h0 := hγ z ((logEmbedding_eq_zero_iff S).mp (h1.trans hz))
    exact fun i ↦ congrFun h0 i
  -- The `ℤ`-span of the `v j` lies in the discrete `S`-unit lattice, so its `ℝ`-rank is its
  -- `ℤ`-rank.
  have hle : Submodule.span ℤ (Set.range v) ≤ unitLattice S :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦
      logEmbedding_mem_unitLattice S (Additive.ofMul (γ j)))
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) :=
    DiscreteTopology.of_subset (s := (unitLattice S : Set (logSpace S)))
      (inferInstanceAs (DiscreteTopology (unitLattice S))) hle
  have hℤrank : Set.finrank ℤ (Set.range v) = Fintype.card ι :=
    (linearIndependent_iff_card_eq_finrank_span.mp hℤ).symm
  have hℝrank : Set.finrank ℝ (Set.range v) = Set.finrank ℤ (Set.range v) :=
    Real.finrank_eq_int_finrank_of_discrete hdisc
  exact linearIndependent_iff_card_eq_finrank_span.mpr (hℝrank.trans hℤrank).symm

open Classical in
/-- **Exponent bound for `S`-units.** Let `T` be a continuous left inverse of the map
`z ↦ ∑ j, z j • ℓ(γ j)`, where `ℓ` is the `S`-logarithmic embedding. If `ζ` is torsion, then for
every `z ∈ ℤ^ι` and every `j`, `|z j| ≤ ‖T‖ * logHeight₁ (ζ * ∏ i, γ i ^ z i)`. -/
theorem abs_le_opNorm_mul_logHeight₁ {γ : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    {T : logSpace S →L[ℝ] ι → ℝ}
    (hT : ∀ z : ι → ℝ, T (∑ j, z j • logEmbedding S (Additive.ofMul (γ j))) = z)
    {ζ : (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hζ : ζ ∈ CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) (z : ι → ℤ)
    (j : ι) :
    |(z j : ℝ)| ≤ ‖T‖ * logHeight₁ (((ζ * ∏ i, γ i ^ z i : _) : Kˣ) : K) := by
  set x := ζ * ∏ i, γ i ^ z i
  have hTx : T (logEmbedding S (Additive.ofMul x)) = fun i ↦ (z i : ℝ) := by
    rw [logEmbedding_mul_prod_zpow hζ, ← hT fun i ↦ (z i : ℝ)]
    simp only [Int.cast_smul_eq_zsmul]
  calc |(z j : ℝ)| = ‖T (logEmbedding S (Additive.ofMul x)) j‖ := by
        rw [hTx, Real.norm_eq_abs]
    _ ≤ ‖T (logEmbedding S (Additive.ofMul x))‖ := norm_le_pi_norm _ j
    _ ≤ ‖T‖ * ‖logEmbedding S (Additive.ofMul x)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * logHeight₁ ((x : Kˣ) : K) :=
        mul_le_mul_of_nonneg_left (norm_logEmbedding_le_logHeight₁ S x) (norm_nonneg T)

/-- **Exponent–height bound for finitely generated groups.** Let `γ j` be nonzero elements of a
number field `K` with absolute value `1` at every finite place outside a finite set `S`, and
multiplicatively independent: `∏ j, γ j ^ z j` is a root of unity only for `z = 0`. Then there is
`κ ≥ 0` such that `|z j| ≤ κ * logHeight₁ (ζ * ∏ i, γ i ^ z i)` for every root of unity `ζ`,
every `z ∈ ℤ^ι` and every `j`. One may take for `κ` the operator norm of any continuous left
inverse of `z ↦ ∑ j, z j • ℓ(γ j)`, where `ℓ` is the `S`-logarithmic embedding; see
`abs_le_opNorm_mul_logHeight₁`. -/
theorem exists_abs_le_mul_logHeight₁ {γ : ι → K} (hγ0 : ∀ j, γ j ≠ 0)
    (hγS : ∀ j, ∀ v ∉ S, HeightOneSpectrum.adicAbv K v (γ j) = 1)
    (hγ : ∀ z : ι → ℤ, IsOfFinOrder (∏ j, γ j ^ z j) → z = 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ ζ : K, IsOfFinOrder ζ → ∀ (z : ι → ℤ) (j : ι),
      |(z j : ℝ)| ≤ κ * logHeight₁ (ζ * ∏ i, γ i ^ z i) := by
  classical
  choose γ' hγ' using fun j ↦
    exists_sUnit_coe_eq (S := (S : Set (HeightOneSpectrum (𝓞 K)))) (hγ0 j) (hγS j)
  have hcoe (ζ' : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (z : ι → ℤ) :
      (((ζ' * ∏ i, γ' i ^ z i : _) : Kˣ) : K) = ((ζ' : Kˣ) : K) * ∏ i, γ i ^ z i := by
    simp [hγ']
  -- The `S`-logarithmic images of the `γ' j` are linearly independent, so the map
  -- `z ↦ ∑ j, z j • ℓ(γ' j)` has a continuous left inverse `T`.
  have hind : LinearIndependent ℝ fun j ↦ logEmbedding S (Additive.ofMul (γ' j)) := by
    refine linearIndependent_logEmbedding fun z hz ↦ hγ z ?_
    have h := ((Units.coeHom K).comp (Subgroup.subtype _)).isOfFinOrder
      ((CommGroup.mem_torsion _).mp hz)
    simpa [hγ'] using h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Fintype.linearCombination ℝ fun j ↦ logEmbedding S (Additive.ofMul (γ' j)))
    (LinearMap.ker_eq_bot.mpr
      (linearIndependent_iff_injective_fintypeLinearCombination.mp hind))
  have hT (z : ι → ℝ) : LinearMap.toContinuousLinearMap g
      (∑ j, z j • logEmbedding S (Additive.ofMul (γ' j))) = z := by
    have h := LinearMap.congr_fun hg z
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply] at h
  refine ⟨‖LinearMap.toContinuousLinearMap g‖, norm_nonneg _, fun ζ hζ z j ↦ ?_⟩
  obtain ⟨ζ', hζ'⟩ := exists_sUnit_coe_eq (S := (S : Set (HeightOneSpectrum (𝓞 K))))
    hζ.isUnit.ne_zero fun v _ ↦ AbsoluteValue.map_eq_one_of_isOfFinOrder _ hζ
  have hζt : ζ' ∈ CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) := by
    rw [CommGroup.mem_torsion, ← Submonoid.isOfFinOrder_coe, ← Units.isOfFinOrder_val]
    simpa [hζ'] using hζ
  have h := abs_le_opNorm_mul_logHeight₁ hT hζt z j
  rwa [hcoe, hζ'] at h

end TauCeti.NumberField.SUnit
