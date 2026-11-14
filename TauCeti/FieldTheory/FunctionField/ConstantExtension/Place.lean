/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated

/-!
# Places under arbitrary constant field extensions

Let `F / k` be an algebraic function field and let `F' = F · K` be a linearly disjoint extension
of constants, where `K / k` may be transcendental (such as `AlgebraicClosure ℚ ⊂ ℂ`). Because
`F' / F` need not be integral, a place `Q'` of `F' / K` can be trivial on `F` — for instance, a
finite place `t = c` of
`K(t)` at a constant `c ∈ K` transcendental over `k`. Every other place of `F' / K` contracts to
the valuation ring of a unique place `Q` of `F / k` (`Q'.integers.comap (algebraMap F F') =
Q.integers`), and conversely every place `Q` of `F / k` extends to at least one such place of
`F' / K`.

At any rational place `Q` (`Q.degree = 1`) — in particular at every place when `k` is algebraically
closed — expanding elements of `F ⊗[k] K` in a `k`-basis of `K` shows that `Q'` is **unique**,
unramified (`Q'.ramificationIdx F = 1`, so `Q'.ord (algebraMap F F' f) = Q.ord f`), and again
rational (`Q'.degree = 1`). Embedding `F'` into its compositum with an algebraic closure of `K` and
factoring through the algebraic closure of `k` inside it deduces unramifiedness
(`Q'.ramificationIdx F = 1`) for every place over a perfect field `k` with exact constants in `F`.

## Main results

* `TauCeti.Place.isTrivialOn_or_existsUnique_integers_comap_eq`: every place of `F' / K` is either
  trivial on `F` or contracts to the valuation ring of a unique place of `F / k`.
* `TauCeti.Place.exists_integers_comap_eq`: every place of `F / k` extends to a place of a
  linearly disjoint compositum `F' = F · K`.
* `TauCeti.Place.existsUnique_integers_comap_eq_of_degree_eq_one` and
  `TauCeti.Place.degree_eq_one_of_integers_comap_eq`: a rational place extends uniquely across a
  linearly disjoint constant extension, and its extension remains rational and unramified.
* `TauCeti.Place.ramificationIdx_eq_one_of_integers_comap_eq` and
  `TauCeti.Place.ord_algebraMap_eq_of_integers_comap_eq`: over a perfect field `k` exact in `F`,
  every place of `F' = F · K` nontrivial on `F` preserves normalized valuations on `F`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
-/

public section

open scoped TensorProduct IntermediateField WithZero nonZeroDivisors

namespace TauCeti.Place

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F']
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

/-! ### Contraction of valuation rings -/

/-- A place of `F' / K` is trivial on `F` precisely when its valuation ring contains `F`. -/
theorem isTrivialOn_iff_integers_comap_eq_top (Q' : Place K F') :
    Q'.valuation.IsTrivialOn F ↔ Q'.integers.comap (algebraMap F F') = ⊤ := by
  refine ⟨fun h ↦ ValuationSubring.ext _ _ fun f ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩,
    fun h ↦ ⟨fun f hf ↦ ?_⟩⟩
  · rw [ValuationSubring.mem_comap, Q'.mem_integers_iff]
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · exact (h.eq_one f hf).le
  · have h1 : Q'.valuation (algebraMap F F' f) ≤ 1 :=
      Q'.mem_integers_iff.mp <|
        ValuationSubring.mem_comap.mp (h.symm ▸ ValuationSubring.mem_top f)
    have h2 : Q'.valuation (algebraMap F F' f⁻¹) ≤ 1 :=
      Q'.mem_integers_iff.mp <|
        ValuationSubring.mem_comap.mp (h.symm ▸ ValuationSubring.mem_top f⁻¹)
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Q'.valuation.ne_zero_iff).mpr
      ((map_ne_zero (algebraMap F F')).mpr hf)))] at h2
    exact le_antisymm h1 h2

/-- **Dichotomy for places under an arbitrary constant extension**: if `F / k` is a function field,
every place `Q'` of `F' / K` is either trivial on `F` or contracts to the valuation ring of a
unique place `Q` of `F / k`. -/
theorem isTrivialOn_or_existsUnique_integers_comap_eq (hF : IsFunctionField k F)
    (Q' : Place K F') :
    Q'.valuation.IsTrivialOn F ∨
      ∃! Q : Place k F, Q'.integers.comap (algebraMap F F') = Q.integers := by
  by_cases hV : Q'.integers.comap (algebraMap F F') = ⊤
  · exact Or.inl ((isTrivialOn_iff_integers_comap_eq_top Q').mpr hV)
  · refine Or.inr ?_
    have hk : ∀ c : k, algebraMap k F c ∈ Q'.integers.comap (algebraMap F F') := fun c ↦ by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply k F F',
        IsScalarTower.algebraMap_apply k K F']
      exact Q'.algebraMap_mem_integers _
    obtain ⟨Q, hQ, huniq⟩ := existsUnique_integers_eq hF hk hV
    exact ⟨Q, hQ.symm, fun Q₁ hQ₁ ↦ huniq Q₁ hQ₁.symm⟩

omit [Algebra k K] [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- When `Q'` contracts to `Q.integers`, its ramification index over `F` is positive and scales
`Q.ord`. -/
theorem ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq
    {Q : Place k F} {Q' : Place K F'} (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    0 < Q'.ramificationIdx F ∧
      ∀ f : F, Q'.ord (algebraMap F F' f) = Q'.ramificationIdx F * Q.ord f := by
  set w := Q'.valuation.comap (algebraMap F F')
  have hsub : w.valuationSubring = Q.valuation.valuationSubring := by
    ext f
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ← Q'.mem_integers_iff,
      ← ValuationSubring.mem_comap, hQ', Q.mem_integers_iff, Valuation.mem_valuationSubring_iff]
  have hw : w.IsEquiv Q.valuation := (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  obtain ⟨t, ht⟩ := Q.ord_surjective 1
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hwt : w t < 1 := (Valuation.isEquiv_iff_val_lt_one.mp hw).mpr <| by
    rw [Q.valuation_eq_exp_neg_ord ht0, ht]; simp
  have : w.IsNontrivial := ⟨t, w.ne_zero_iff.mpr ht0, hwt.ne⟩
  have hpos : 0 < Valuation.ordIndex w :=
    Nat.pos_of_ne_zero (Valuation.ordIndex_ne_zero_of_isNontrivial w)
  have hkt : w.IsTrivialOn k :=
    ⟨fun c hc ↦ (Valuation.isEquiv_iff_val_eq_one.mp hw).mpr (Q.isTrivialOn.eq_one c hc)⟩
  let Q₀ : Place k F :=
    { valuation := w.normalization
      valuation_surjective := Valuation.normalization_surjective w hpos.ne'
      isTrivialOn := Valuation.IsTrivialOn.normalization w }
  have hQ₀ : w.normalization = Q.valuation :=
    congrArg Place.valuation (eq_of_isEquiv ((Valuation.isEquiv_normalization w).trans hw) : Q₀ = Q)
  refine ⟨by rwa [ramificationIdx_def], fun f ↦ ?_⟩
  have hord := Valuation.ord_normalization_mul_ordIndex w f
  rw [hQ₀, Q.ord_valuation, mul_comm, ← ramificationIdx_def, Valuation.ord_comap,
    Q'.ord_valuation] at hord
  exact hord.symm

/-! ### Existence of place extensions -/

/-- Injectivity of the natural map `𝒪_Q ⊗[k] K → F'` under linear disjointness of `F` and `K`. -/
private theorem productMap_integers_injective
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F) (Q : Place k F) :
    let O : Subalgebra k F :=
      { Q.integers.toSubring with algebraMap_mem' := Q.algebraMap_mem_integers }
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom k F F').comp O.val) (IsScalarTower.toAlgHom k K F')) := by
  intro O
  have hg_eq : Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom k F F').comp O.val)
      (IsScalarTower.toAlgHom k K F') =
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
        (IsScalarTower.toAlgHom k K F')).comp (Algebra.TensorProduct.map O.val (AlgHom.id k K)) :=
    Algebra.TensorProduct.ext (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)
  rw [hg_eq, AlgHom.coe_comp]
  refine (productMap_injective_iff_linearDisjoint.mpr H).comp ?_
  rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq]
  exact Module.Flat.rTensor_preserves_injective_linearMap O.val.toLinearMap Subtype.val_injective

/-- **Existence of place extensions across a linearly disjoint constant extension**: every place `Q`
of a function field `F / k` extends to a place `Q'` of `F' = F · K` contracting to `Q.integers`,
without any algebraicity hypothesis on `K / k`. -/
theorem exists_integers_comap_eq (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) (Q : Place k F) :
    ∃ Q' : Place K F', Q'.integers.comap (algebraMap F F') = Q.integers := by
  let O : Subalgebra k F :=
    { Q.integers.toSubring with algebraMap_mem' := Q.algebraMap_mem_integers }
  let g : O ⊗[k] K →ₐ[k] F' := Algebra.TensorProduct.productMap
    ((IsScalarTower.toAlgHom k F F').comp O.val) (IsScalarTower.toAlgHom k K F')
  have hg_inj : Function.Injective g := productMap_integers_injective H Q
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  have hϖ1 : Q.ord ϖ = 1 := Q.isUniformizer_iff_ord_eq_one.mp hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ1
  have hϖO : ϖ ∈ Q.integers := Q.mem_integers_iff_ord_nonneg.mpr (by omega)
  let resAlg : O →ₐ[k] Q.ResidueField :=
    { IsLocalRing.residue Q.integers with commutes' := fun _ ↦ rfl }
  let q : O ⊗[k] K →ₐ[k] Q.ResidueField ⊗[k] K :=
    Algebra.TensorProduct.map resAlg (AlgHom.id k K)
  have : Nontrivial (Q.ResidueField ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k Q.ResidueField K
      (algebraMap k _).injective (algebraMap k K).injective
  let x₀ : g.range.toSubring := ⟨algebraMap F F' ϖ, ⟨⟨ϖ, hϖO⟩ ⊗ₜ[k] 1, by simp [g]⟩⟩
  have hx₀ : ¬ IsUnit x₀ := fun hu ↦ by
    obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨z, hz⟩ := u.2
    change g z = u.1 at hz
    have hx₀_eq : g (⟨ϖ, hϖO⟩ ⊗ₜ[k] 1) = x₀.1 := by simp [g, x₀]
    have hmul : g ((⟨ϖ, hϖO⟩ ⊗ₜ[k] 1) * z) = g 1 := by
      rw [map_mul, map_one, hx₀_eq, hz]; exact congrArg Subtype.val hu'
    have hq1 := congrArg q (hg_inj hmul)
    have hres0 : resAlg ⟨ϖ, hϖO⟩ = 0 :=
      (Q.residue_eq_zero_iff_ord_pos (f := ⟨ϖ, hϖO⟩) hϖ0).mpr (by simp [hϖ1])
    simp [q, hres0] at hq1
  obtain ⟨V, hRV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span ({x₀} : Set g.range.toSubring)) ((Ideal.span_singleton_eq_top.not).mpr hx₀)
  have hϖ_nonunit : algebraMap F F' ϖ ∈ V.nonunits :=
    hIV ⟨x₀, Ideal.subset_span (Set.mem_singleton x₀), rfl⟩
  have hϖ_inv_notMem : (algebraMap F F' ϖ)⁻¹ ∉ V :=
    (V.mem_nonunits_iff_or.mp hϖ_nonunit).resolve_left ((map_ne_zero _).mpr hϖ0)
  have hV_ne_top : V ≠ ⊤ := fun htop ↦ hϖ_inv_notMem (htop ▸ ValuationSubring.mem_top _)
  have hKV : ∀ c : K, algebraMap K F' c ∈ V := fun c ↦ hRV ⟨1 ⊗ₜ[k] c, by simp [g]⟩
  have hle : Q.integers ≤ V.comap (algebraMap F F') := fun f hf ↦
    hRV ⟨⟨f, hf⟩ ⊗ₜ[k] 1, by simp [g]⟩
  have hcomap_ne : V.comap (algebraMap F F') ≠ ⊤ := fun htop ↦ hϖ_inv_notMem <| by
    have hmem : ϖ⁻¹ ∈ V.comap (algebraMap F F') := by rw [htop]; trivial
    simpa [ValuationSubring.mem_comap] using hmem
  have hF' : IsFunctionField K F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  refine ⟨ofValuationSubring hF' hKV hV_ne_top, ?_⟩
  rw [integers_ofValuationSubring]
  exact (Q.integers.eq_of_le_of_ne_top hle hcomap_ne).symm

/-! ### Rational places -/

/-- Every nonzero element of a linearly disjoint compositum `F' = F · K` is a quotient of images of
nonzero elements of `F ⊗[k] K`. -/
private theorem exists_eq_div_productMap
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {w : F'} (hw0 : w ≠ 0) :
    let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k K F')
    ∃ z₁ z₂ : F ⊗[k] K, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ π z₁ ≠ 0 ∧ π z₂ ≠ 0 ∧ w = π z₁ / π z₂ := by
  intro π
  let _ : Algebra (F ⊗[k] K) F' := π.toRingHom.toAlgebra
  have : IsFractionRing (F ⊗[k] K) F' := isFractionRing_tensorProduct_of_linearDisjoint H hcomp
  obtain ⟨z₁, z₂, hz₂, hw⟩ := IsFractionRing.div_surjective (A := F ⊗[k] K) w
  have hw_div : w = π z₁ / π z₂ := hw.symm
  have hz₂0 : z₂ ≠ 0 := nonZeroDivisors.ne_zero hz₂
  have hπz₂0 : π z₂ ≠ 0 :=
    (map_ne_zero_iff π (productMap_injective_iff_linearDisjoint.mpr H)).mpr hz₂0
  have hz₁0 : z₁ ≠ 0 := fun h ↦ hw0 (by rw [hw_div, h, map_zero, zero_div])
  have hπz₁0 : π z₁ ≠ 0 :=
    (map_ne_zero_iff π (productMap_injective_iff_linearDisjoint.mpr H)).mpr hz₁0
  exact ⟨z₁, z₂, hz₁0, hz₂0, hπz₁0, hπz₂0, hw_div⟩

/-- Coordinate expansion of a nonzero element of `F ⊗[k] K` at a rational place `Q` of `F / k`,
using a uniformizer `ϖ` of `Q` and a `k`-basis `b` of `K`. Neither `m` nor `C` depends on any
place upstairs. -/
private theorem exists_repr_decomposition {Q : Place k F} (hQ : Q.degree = 1) {ϖ : F}
    (hϖ : Q.ord ϖ = 1) {ι : Type*} (b : Module.Basis ι k K) {z : F ⊗[k] K} (hz : z ≠ 0) :
    ∃ (m : ℤ) (C : K) (s : Finset ι) (r : ι → F),
      C ≠ 0 ∧ (∀ i ∈ s, Q.valuation (r i) < 1) ∧
      Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
          (IsScalarTower.toAlgHom k K F') z =
        (algebraMap F F' ϖ) ^ m * (algebraMap K F' C +
          ∑ i ∈ s, algebraMap F F' (r i) * algebraMap K F' (b i)) := by
  classical
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  set g := (b.baseChange F).repr z
  have hg_ne : g.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr ((b.baseChange F).repr.map_ne_zero_iff.mpr hz)
  set m : ℤ := g.support.inf' hg_ne fun i ↦ Q.ord (g i)
  obtain ⟨i₀, hi₀s, hi₀m⟩ := Finset.exists_mem_eq_inf' hg_ne fun i ↦ Q.ord (g i)
  have hgi0 : ∀ i ∈ g.support, g i ≠ 0 := fun i hi ↦ Finsupp.mem_support_iff.mp hi
  let h : ι → F := fun i ↦ g i / ϖ ^ m
  have hh_mem : ∀ i ∈ g.support, h i ∈ Q.integers := fun i hi ↦ by
    rw [Q.mem_integers_iff_ord_nonneg, Q.ord_div (hgi0 i hi) (zpow_ne_zero m hϖ0),
      Q.ord_zpow ϖ m, hϖ, mul_one]
    have := Finset.inf'_le (fun j ↦ Q.ord (g j)) hi
    omega
  have hc_ex : ∀ i, ∃ c : k, i ∈ g.support → Q.valuation (h i - algebraMap k F c) < 1 := fun i ↦
    if hi : i ∈ g.support then
      let ⟨c, hc⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hQ) _ (hh_mem i hi)
      ⟨c, fun _ ↦ hc⟩
    else ⟨0, fun h' ↦ (hi h').elim⟩
  choose c hc using hc_ex
  have hci₀ : c i₀ ≠ 0 := fun hc0 ↦ by
    have hlt := hc i₀ hi₀s
    rw [hc0, map_zero, sub_zero] at hlt
    have hord0 : Q.ord (h i₀) = 0 := by
      rw [Q.ord_div (hgi0 i₀ hi₀s) (zpow_ne_zero m hϖ0), Q.ord_zpow ϖ m, hϖ, mul_one, ← hi₀m,
        sub_self]
    exact hlt.ne <| by
      rw [Q.valuation_eq_exp_neg_ord (div_ne_zero (hgi0 i₀ hi₀s) (zpow_ne_zero m hϖ0)), hord0]; simp
  let C : K := ∑ i ∈ g.support, c i • b i
  have hC0 : C ≠ 0 := fun hC ↦
    hci₀ (linearIndependent_iff'.mp b.linearIndependent g.support c hC i₀ hi₀s)
  refine ⟨m, C, g.support, fun i ↦ h i - algebraMap k F (c i), hC0, hc, ?_⟩
  have hz_sum : ∑ i ∈ g.support, g i ⊗ₜ[k] b i = z := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.smul_tmul', g] using
      (b.baseChange F).linearCombination_repr z
  rw [← hz_sum, map_sum, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hgi : g i = ϖ ^ m * (algebraMap k F (c i) + (h i - algebraMap k F (c i))) := by
    simp [h, mul_div_cancel₀ _ (zpow_ne_zero m hϖ0)]
  have hck : algebraMap F F' (algebraMap k F (c i)) = algebraMap K F' (algebraMap k K (c i)) := by
    rw [← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k K F']
  simp only [Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.coe_toAlgHom',
    Algebra.smul_def, map_mul]
  rw [hgi, map_mul, map_zpow₀, map_add, hck]
  ring

omit [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- Ultrametric evaluation of the coordinate decomposition at an extension `Q'` of `Q`. -/
private theorem valuation_and_ord_of_repr_decomposition {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) {ϖ : F} (hϖ : Q.ord ϖ = 1)
    {ι : Type*} (b : Module.Basis ι k K) {m : ℤ} {C : K} (hC0 : C ≠ 0) {s : Finset ι}
    {r : ι → F} (hr : ∀ i ∈ s, Q.valuation (r i) < 1) :
    let R := ∑ i ∈ s, algebraMap F F' (r i) * algebraMap K F' (b i)
    Q'.valuation R < 1 ∧ Q'.valuation (algebraMap K F' C + R) = 1 ∧
      Q'.ord ((algebraMap F F' ϖ) ^ m * (algebraMap K F' C + R)) = Q'.ramificationIdx F * m := by
  intro R
  obtain ⟨he_pos, hord_scale⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  have hR : Q'.valuation R < 1 := by
    refine (Q'.valuation.map_sum_lt' zero_lt_one) fun i hi ↦ ?_
    rw [map_mul]
    rcases eq_or_ne (r i) 0 with h0 | h0
    · simp [h0]
    · have hord_pos : 0 < Q.ord (r i) := by
        have hv := hr i hi
        rw [Q.valuation_eq_exp_neg_ord h0] at hv
        exact neg_lt_zero.mp (WithZero.exp_lt_one_iff.mp hv)
      have hri_lt : Q'.valuation (algebraMap F F' (r i)) < 1 := by
        rw [Q'.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr h0), WithZero.exp_lt_one_iff,
          neg_lt_zero, hord_scale]
        exact mul_pos (by exact_mod_cast he_pos) hord_pos
      have hbi_le : Q'.valuation (algebraMap K F' (b i)) ≤ 1 :=
        Q'.mem_integers_iff.mp (Q'.algebraMap_mem_integers _)
      calc Q'.valuation (algebraMap F F' (r i)) * Q'.valuation (algebraMap K F' (b i))
        _ ≤ Q'.valuation (algebraMap F F' (r i)) * 1 := by gcongr
        _ < 1 := by simpa using hri_lt
  have hC1 : Q'.valuation (algebraMap K F' C) = 1 := Q'.isTrivialOn.eq_one C hC0
  have hu1 : Q'.valuation (algebraMap K F' C + R) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left Q'.valuation (hR.trans_eq hC1.symm), hC1]
  refine ⟨hR, hu1, ?_⟩
  have hu0 : algebraMap K F' C + R ≠ 0 := fun h ↦ by simp [h] at hu1
  have hu_ord : Q'.ord (algebraMap K F' C + R) = 0 :=
    (Q'.ord_eq_iff_valuation_eq_exp_neg hu0).mpr (by simpa using hu1)
  rw [Q'.ord_mul (zpow_ne_zero m ((map_ne_zero _).mpr hϖ0)) hu0,
    Q'.ord_zpow (algebraMap F F' ϖ) m, hord_scale, hϖ, mul_one, hu_ord, add_zero, mul_comm]

/-- **A rational place is unramified under any linearly disjoint constant extension.** Neither
perfectness of `k` nor exactness of `k` in `F` is required once `Q.degree = 1`. -/
theorem ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1) {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.ramificationIdx F = 1 := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k K F')
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  let b := Module.Basis.ofVectorSpace k K
  have hdvd : ∀ z : F ⊗[k] K, z ≠ 0 → (Q'.ramificationIdx F : ℤ) ∣ Q'.ord (π z) := fun z hz ↦ by
    obtain ⟨m, C, s, r, hC0, hr, hz_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz
    obtain ⟨-, -, hord⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b hC0 hr
    exact ⟨m, hz_eq.symm ▸ hord⟩
  obtain ⟨w, hw1⟩ := Q'.ord_surjective 1
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  obtain ⟨z₁, z₂, hz₁0, hz₂0, hπz₁0, hπz₂0, hw_div⟩ := exists_eq_div_productMap H hcomp hw0
  have hdvd1 : (Q'.ramificationIdx F : ℤ) ∣ 1 := by
    rw [← hw1, hw_div, Q'.ord_div hπz₁0 hπz₂0]
    exact dvd_sub (hdvd z₁ hz₁0) (hdvd z₂ hz₂0)
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd1

/-- **A rational place has at most one extension across a linearly disjoint constant extension.** -/
theorem eq_of_degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1)
    {Q₁' Q₂' : Place K F'} (h₁ : Q₁'.integers.comap (algebraMap F F') = Q.integers)
    (h₂ : Q₂'.integers.comap (algebraMap F F') = Q.integers) : Q₁' = Q₂' := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k K F')
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  let b := Module.Basis.ofVectorSpace k K
  have he₁ := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₁
  have he₂ := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₂
  have hπ_ord : ∀ z : F ⊗[k] K, Q₁'.ord (π z) = Q₂'.ord (π z) := fun z ↦ by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    obtain ⟨m, C, s, r, hC0, hr, hz_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz
    obtain ⟨-, -, hord₁⟩ := valuation_and_ord_of_repr_decomposition h₁ hϖ b hC0 hr
    obtain ⟨-, -, hord₂⟩ := valuation_and_ord_of_repr_decomposition h₂ hϖ b hC0 hr
    rw [hz_eq, hord₁, hord₂, he₁, he₂]
  refine Place.ext <| Valuation.ext fun w ↦ ?_
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  obtain ⟨z₁, z₂, -, -, hπz₁0, hπz₂0, hw_div⟩ := exists_eq_div_productMap H hcomp hw0
  rw [Q₁'.valuation_eq_exp_neg_ord hw0, Q₂'.valuation_eq_exp_neg_ord hw0, hw_div,
    Q₁'.ord_div hπz₁0 hπz₂0, Q₂'.ord_div hπz₁0 hπz₂0, hπ_ord, hπ_ord]

/-- **Unique extension of rational places across a linearly disjoint constant extension.** -/
theorem existsUnique_integers_comap_eq_of_degree_eq_one (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1) :
    ∃! Q' : Place K F', Q'.integers.comap (algebraMap F F') = Q.integers := by
  obtain ⟨Q', hQ'⟩ := exists_integers_comap_eq hF H hcomp Q
  exact ⟨Q', hQ', fun Q₁' h₁ ↦ eq_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₁ hQ'⟩

/-- **A place extending a rational place across a linearly disjoint constant extension remains
rational.** -/
theorem degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1)
    {Q' : Place K F'} (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.degree = 1 := by
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  let b := Module.Basis.ofVectorSpace k K
  have he := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ hQ'
  rw [degree_eq_one_iff_forall_exists_valuation_sub_lt_one]
  intro w hw
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨0, by simp⟩
  obtain ⟨z₁, z₂, hz₁0, hz₂0, hπz₁0, hπz₂0, hw_div⟩ := exists_eq_div_productMap H hcomp hw0
  obtain ⟨m₁, C₁, s₁, r₁, hC₁, hr₁, hz₁_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz₁0
  obtain ⟨m₂, C₂, s₂, r₂, hC₂, hr₂, hz₂_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz₂0
  obtain ⟨hR₁, hu₁, hord₁⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b hC₁ hr₁
  obtain ⟨hR₂, hu₂, hord₂⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b hC₂ hr₂
  have hw_ord : 0 ≤ m₁ - m₂ := by
    have h := Q'.mem_integers_iff_ord_nonneg.mp hw
    rwa [hw_div, Q'.ord_div hπz₁0 hπz₂0, hz₁_eq, hz₂_eq, hord₁, hord₂, he, Nat.cast_one,
      one_mul, one_mul] at h
  rcases lt_or_eq_of_le (sub_nonneg.mp hw_ord) with hlt | heq
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, Q'.valuation_eq_exp_neg_ord hw0, WithZero.exp_lt_one_iff, neg_lt_zero,
      hw_div, Q'.ord_div hπz₁0 hπz₂0, hz₁_eq, hz₂_eq, hord₁, hord₂, he]
    omega
  · refine ⟨C₁ / C₂, ?_⟩
    set R₁ := ∑ i ∈ s₁, algebraMap F F' (r₁ i) * algebraMap K F' (b i)
    set R₂ := ∑ i ∈ s₂, algebraMap F F' (r₂ i) * algebraMap K F' (b i)
    have hp0 : (algebraMap F F' ϖ) ^ m₂ ≠ 0 := zpow_ne_zero m₂ ((map_ne_zero _).mpr hϖ0)
    have hw_simp : w = (algebraMap K F' C₁ + R₁) / (algebraMap K F' C₂ + R₂) := by
      rw [hw_div, hz₁_eq, hz₂_eq, ← heq, mul_div_mul_left _ _ hp0]
    have hd0 : algebraMap K F' C₂ + R₂ ≠ 0 := fun h ↦ by simp [h] at hu₂
    have hdiff : w - algebraMap K F' (C₁ / C₂) =
        (R₁ - algebraMap K F' (C₁ / C₂) * R₂) / (algebraMap K F' C₂ + R₂) := by
      rw [hw_simp, map_div₀]
      field_simp [hd0, (map_ne_zero (algebraMap K F')).mpr hC₂]
      ring
    rw [hdiff, map_div₀, hu₂, div_one]
    refine Valuation.map_sub_lt Q'.valuation hR₁ ?_
    rw [map_mul]
    have hle : Q'.valuation (algebraMap K F' (C₁ / C₂)) ≤ 1 :=
      Q'.mem_integers_iff.mp (Q'.algebraMap_mem_integers _)
    calc Q'.valuation (algebraMap K F' (C₁ / C₂)) * Q'.valuation R₂
      _ ≤ 1 * Q'.valuation R₂ := by gcongr
      _ < 1 := by simpa using hR₂

/-! ### Unramifiedness over perfect base fields -/

omit [Field k] [Algebra k K] [Algebra k F] [Algebra k F'] [IsScalarTower k K F']
  [IsScalarTower k F F'] in
/-- Transitivity of `constantCompositum = ⊤` across a tower `F → F' → F''` with constants
`K → Ω`. -/
private theorem constantCompositum_tower_eq_top {Ω F'' : Type*} [Field Ω] [Field F'']
    [Algebra K Ω] [Algebra Ω F''] [Algebra F F''] [Algebra F' F''] [Algebra K F'']
    [IsScalarTower F F' F''] [IsScalarTower K F' F''] [IsScalarTower K Ω F'']
    (hcomp₁ : constantCompositum F K F' = ⊤) (hcomp₂ : constantCompositum F' Ω F'' = ⊤) :
    constantCompositum F Ω F'' = ⊤ := by
  let M := constantCompositum F Ω F''
  have hL : constantCompositum F K F' ≤ M.comap (IsScalarTower.toAlgHom F F' F'') :=
    (constantCompositum_le_iff F K F').mpr fun c ↦ by
      change algebraMap F' F'' (algebraMap K F' c) ∈ M
      rw [← IsScalarTower.algebraMap_apply K F' F'', IsScalarTower.algebraMap_apply K Ω F'']
      exact algebraMap_mem_constantCompositum F Ω F'' (algebraMap K Ω c)
  have hF'M : ∀ y : F', algebraMap F' F'' y ∈ M := fun y ↦
    hL (hcomp₁ ▸ IntermediateField.mem_top : y ∈ constantCompositum F K F')
  let M' : IntermediateField F' F'' :=
    { M.toSubfield with algebraMap_mem' := hF'M }
  have hM' : constantCompositum F' Ω F'' ≤ M' :=
    (constantCompositum_le_iff F' Ω F'').mpr fun ω ↦ algebraMap_mem_constantCompositum F Ω F'' ω
  exact top_le_iff.mp fun z _ ↦ hM' (hcomp₂ ▸ IntermediateField.mem_top)

/-- Linear disjointness of the top step `F₁ → F'` when `F → F'` is linearly disjoint from `K`
over `k`, `F₁ = F · L` for an algebraic intermediate extension `L / k`, and `F' = F₁ · K`. -/
private theorem linearDisjoint_constantCompositum_top [PerfectField k]
    {L F₁ : Type*} [Field L] [Field F₁] [Algebra k L] [Algebra L K] [Algebra L F']
    [Algebra k F₁] [Algebra F F₁] [Algebra L F₁] [Algebra F₁ F']
    [IsScalarTower L K F'] [IsScalarTower k F F₁]
    [IsScalarTower k L F₁] [IsScalarTower F F₁ F'] [IsScalarTower L F₁ F']
    [Algebra.IsAlgebraic k L] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) (hcomp₁ : constantCompositum F L F₁ = ⊤)
    (hcomp₂ : constantCompositum F₁ K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    (IsScalarTower.toAlgHom L K F').fieldRange.LinearDisjoint F₁ := by
  obtain ⟨he', hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  have hxF : Transcendental k ϖ := Valuation.transcendental_of_ne_one k ϖ hϖ0 <| by
    rw [Q.valuation_eq_exp_neg_ord hϖ0, hϖ]; simp
  have : FiniteDimensional k⟮ϖ⟯ F := hF.finiteDimensional_adjoin hxF
  have hxK : Transcendental K (algebraMap F F' ϖ) :=
    Valuation.transcendental_of_ne_one K _ ((map_ne_zero _).mpr hϖ0) <| by
      rw [Q'.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr hϖ0), hord', hϖ]
      exact (WithZero.exp_eq_one.not).mpr (by omega)
  have H₁ : (IsScalarTower.toAlgHom k L F₁).fieldRange.LinearDisjoint F :=
    linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex
  have h1 := finrank_over_adjoin_simple_eq_of_linearDisjoint H₁ hcomp₁ ϖ
  have : FiniteDimensional L⟮algebraMap F F₁ ϖ⟯ F₁ :=
    Module.finite_of_finrank_pos (h1 ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq hcomp₂ (x := algebraMap F F₁ ϖ)
    (by simpa [← IsScalarTower.algebraMap_apply F F₁ F'] using hxK) ?_
  have h2 := finrank_over_adjoin_simple_eq_of_linearDisjoint H hcomp ϖ
  exact (congrArg (fun z : F' ↦ Module.finrank K⟮z⟯ F')
    (IsScalarTower.algebraMap_apply F F₁ F' ϖ).symm).trans (h2.trans h1.symm)

/-- When the enlarged constant field `K` is already algebraically closed, factoring through the
algebraic closure of `k` inside `K` reduces unramifiedness to an algebraic separable step followed
by a rational-place step. -/
private theorem ramificationIdx_eq_one_of_isAlgClosed [PerfectField k] [IsAlgClosed K]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.ramificationIdx F = 1 := by
  obtain ⟨_, hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  let kbar := algebraicClosure k K
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let F₁ := constantCompositum F kbar F'
  let _ : Algebra kbar F₁ := constantCompositumAlgebra F kbar F'
  have : IsScalarTower kbar F₁ F' := isScalarTower_constantCompositum F kbar F'
  have : IsScalarTower k kbar F₁ := isScalarTower_base_constantCompositum k F kbar F'
  have hcomp₁ : constantCompositum F kbar F₁ = ⊤ :=
    (constantCompositum_eq_top_iff F kbar F' F₁).2 rfl
  have hF₁ : IsFunctionField kbar F₁ := hF.of_constantCompositum_eq_top hcomp₁
  have hcomp₂ : constantCompositum F₁ K F' = ⊤ :=
    constantCompositum_eq_top_of_eq_top F K F' F₁ hcomp
  have H₂ : (IsScalarTower.toAlgHom kbar K F').fieldRange.LinearDisjoint F₁ :=
    linearDisjoint_constantCompositum_top hF hex H hcomp hcomp₁ hcomp₂ hQ'
  let V₁ := Q'.integers.comap (algebraMap F₁ F')
  have hV₁_ne : V₁ ≠ ⊤ := fun htop ↦ Q.integers_ne_top <| by
    rw [← hQ', eq_top_iff]
    intro f _
    have hmem : algebraMap F F₁ f ∈ V₁ := by rw [htop]; trivial
    simpa [V₁, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply F F₁ F'] using hmem
  have hkbarV₁ : ∀ c : kbar, algebraMap kbar F₁ c ∈ V₁ := fun c ↦ by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply kbar F₁ F',
      IsScalarTower.algebraMap_apply kbar K F']
    exact Q'.algebraMap_mem_integers _
  let Q₁ : Place kbar F₁ := ofValuationSubring hF₁ hkbarV₁ hV₁_ne
  have hQ'Q₁ : Q'.integers.comap (algebraMap F₁ F') = Q₁.integers :=
    (integers_ofValuationSubring hF₁ hkbarV₁ hV₁_ne).symm
  have : FiniteDimensional kbar Q₁.ResidueField := Q₁.finiteDimensional_residueField hF₁
  have he_top := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H₂ hcomp₂
    Q₁.degree_eq_one_of_isAlgClosed_of_isIntegral hQ'Q₁
  obtain ⟨-, hord_top⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'Q₁
  have : Algebra.IsIntegral F F₁ :=
    (isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp₁).isIntegral
  have hQ₁Q : Q₁.restrict k F = Q := (restrict_eq_iff_integers_le k F Q₁ Q).mpr fun f hf ↦ by
    rw [← hQ'Q₁, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply F F₁ F',
      ← ValuationSubring.mem_comap, hQ']
    exact hf
  have he_bot := ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp₁ Q₁
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have h1 : Q'.ord (algebraMap F F' ϖ) = 1 := by
    rw [IsScalarTower.algebraMap_apply F F₁ F', hord_top, he_top, Nat.cast_one, one_mul,
      ord_algebraMap_restrict k F Q₁, hQ₁Q, he_bot, Nat.cast_one, one_mul, hϖ]
  rw [hord', hϖ, mul_one] at h1
  exact_mod_cast h1

omit [Algebra k K] [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- Multiplicativity step deducing `e(Q' ∣ Q) = 1` once `F' / K` is embedded into an integral
constant extension `F'' / Ω` with `Ω` algebraically closed and `F''` linearly disjoint from `F`. -/
private theorem ramificationIdx_eq_one_of_restrict_isAlgClosed [PerfectField k]
    {Ω F'' : Type*} [Field Ω] [Field F''] [IsAlgClosed Ω]
    [Algebra K Ω] [Algebra k Ω] [Algebra Ω F''] [Algebra k F''] [Algebra F F'']
    [Algebra F' F''] [Algebra K F'']
    [IsScalarTower k Ω F''] [IsScalarTower K Ω F''] [IsScalarTower k F F'']
    [IsScalarTower F F' F''] [IsScalarTower K F' F''] [Algebra.IsIntegral F' F'']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (H_all : (IsScalarTower.toAlgHom k Ω F'').fieldRange.LinearDisjoint F)
    (hcomp_all : constantCompositum F Ω F'' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers)
    (Q'' : Place Ω F'') (hQ'' : Q''.restrict K F' = Q') :
    Q'.ramificationIdx F = 1 := by
  have hQ''Q : Q''.integers.comap (algebraMap F F'') = Q.integers := by
    ext f
    rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply F F' F'',
      ← mem_integers_restrict_iff K F' Q'', hQ'', ← ValuationSubring.mem_comap, hQ']
  have he_all := ramificationIdx_eq_one_of_isAlgClosed hF hex H_all hcomp_all hQ''Q
  obtain ⟨-, hord_all⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ''Q
  obtain ⟨-, hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have h1 := hord_all ϖ
  rw [he_all, Nat.cast_one, one_mul, hϖ, IsScalarTower.algebraMap_apply F F' F'',
    ord_algebraMap_restrict K F' Q'', hQ'', hord', hϖ, mul_one] at h1
  have hmul : Q''.ramificationIdx F' * Q'.ramificationIdx F = 1 := by exact_mod_cast h1
  exact Nat.eq_one_of_mul_eq_one_left hmul

/-- Linear disjointness of the composite constant extension `F → F' → F''` (`k → K → Ω`) when a
place `Q''` of `F'' / Ω` restricts to an extension `Q'` of a place `Q` of `F / k`. -/
private theorem linearDisjoint_tower_of_restrict {Ω F'' : Type*} [Field Ω] [Field F'']
    [Algebra K Ω] [Algebra k Ω] [Algebra Ω F''] [Algebra k F''] [Algebra F F'']
    [Algebra F' F''] [Algebra K F'']
    [IsScalarTower k Ω F''] [IsScalarTower K Ω F''] [IsScalarTower k F F'']
    [IsScalarTower F F' F''] [IsScalarTower K F' F''] [Algebra.IsIntegral F' F'']
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤)
    (H' : (IsScalarTower.toAlgHom K Ω F'').fieldRange.LinearDisjoint F')
    (hcomp' : constantCompositum F' Ω F'' = ⊤)
    (hcomp_all : constantCompositum F Ω F'' = ⊤)
    {Q : Place k F} {Q' : Place K F'} (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers)
    (Q'' : Place Ω F'') (hQ'' : Q''.restrict K F' = Q') :
    (IsScalarTower.toAlgHom k Ω F'').fieldRange.LinearDisjoint F := by
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  obtain ⟨_, hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  have : FiniteDimensional k⟮ϖ⟯ F := hF.finiteDimensional_adjoin <|
    Valuation.transcendental_of_ne_one k ϖ hϖ0 (by rw [Q.valuation_eq_exp_neg_ord hϖ0, hϖ]; simp)
  have hpos : 0 < Q''.ord (algebraMap F F'' ϖ) := by
    rw [IsScalarTower.algebraMap_apply F F' F'', ord_algebraMap_restrict K F' Q'', hQ'', hord', hϖ]
    exact mul_pos (by exact_mod_cast ramificationIdx_pos F' Q'') (by positivity)
  have hxΩ : Transcendental Ω (algebraMap F F'' ϖ) :=
    Valuation.transcendental_of_ne_one Ω _ ((map_ne_zero _).mpr hϖ0) <| by
      rw [Q''.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr hϖ0)]
      exact (WithZero.exp_eq_one.not).mpr (by omega)
  refine linearDisjoint_of_transcendental_of_finrank_eq hcomp_all hxΩ ?_
  have h1 := finrank_over_adjoin_simple_eq_of_linearDisjoint H hcomp ϖ
  have : FiniteDimensional K⟮algebraMap F F' ϖ⟯ F' :=
    Module.finite_of_finrank_pos (h1 ▸ Module.finrank_pos)
  have h2 := finrank_over_adjoin_simple_eq_of_linearDisjoint H' hcomp' (algebraMap F F' ϖ)
  exact (congrArg (fun z : F'' ↦ Module.finrank Ω⟮z⟯ F'')
    (IsScalarTower.algebraMap_apply F F' F'' ϖ)).trans (h2.trans h1)

/-- **Places remain unramified across any linearly disjoint constant extension of a function field
over a perfect field with exact constants.** -/
theorem ramificationIdx_eq_one_of_integers_comap_eq [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.ramificationIdx F = 1 := by
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hx₀
  have : Algebra.IsGeometricallyReduced K F' :=
    isGeometricallyReduced_of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  have hex' : IsIntegrallyClosedIn K F' :=
    hex.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  have hF' : IsFunctionField K F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  let Ω := algebraicClosure K (AlgebraicClosure F')
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsDomain (F' ⊗[K] Ω) := isDomain_tensorProduct_of_isGeometricallyReduced hex' Ω
  let F'' := constantCompositum F' Ω (AlgebraicClosure F')
  let _ : Algebra Ω F'' := constantCompositumAlgebra F' Ω (AlgebraicClosure F')
  have : IsScalarTower Ω F'' (AlgebraicClosure F') :=
    isScalarTower_constantCompositum F' Ω (AlgebraicClosure F')
  have : IsScalarTower K Ω F'' :=
    isScalarTower_base_constantCompositum K F' Ω (AlgebraicClosure F')
  have hcomp' : constantCompositum F' Ω F'' = ⊤ :=
    (constantCompositum_eq_top_iff F' Ω (AlgebraicClosure F') F'').2 rfl
  have hF'' : IsFunctionField Ω F'' := hF'.of_constantCompositum_eq_top hcomp'
  have : Algebra.IsIntegral F' F'' :=
    (isAlgebraic_of_constantCompositum_eq_top (k := K) hcomp').isIntegral
  obtain ⟨Q'', hQ''⟩ := restrict_surjective (k := K) (F := F') hF'' Q'
  change Q''.restrict K F' = Q' at hQ''
  let _ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K Ω := .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra F F'' := ((algebraMap F' F'').comp (algebraMap F F')).toAlgebra
  have : IsScalarTower F F' F'' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra k F'' := ((algebraMap F F'').comp (algebraMap k F)).toAlgebra
  have : IsScalarTower k F F'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k Ω F'' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k F F'', IsScalarTower.algebraMap_apply F F' F'',
      ← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k K F',
      ← IsScalarTower.algebraMap_apply K F' F'', IsScalarTower.algebraMap_apply K Ω F'',
      ← IsScalarTower.algebraMap_apply k K Ω]
  have H' : (IsScalarTower.toAlgHom K Ω F'').fieldRange.LinearDisjoint F' :=
    productMap_injective_iff_linearDisjoint.mp
      (productMap_bijective_of_constantCompositum_eq_top (k := K) (F' := F'') hcomp').injective
  have hcomp_all : constantCompositum F Ω F'' = ⊤ := constantCompositum_tower_eq_top hcomp hcomp'
  have H_all := linearDisjoint_tower_of_restrict hF H hcomp H' hcomp' hcomp_all hQ' Q'' hQ''
  exact ramificationIdx_eq_one_of_restrict_isAlgClosed hF hex H_all hcomp_all hQ' Q'' hQ''

/-- **Normalized orders on `F` are preserved by any linearly disjoint constant extension** over a
perfect base field `k` exact in `F`. -/
theorem ord_algebraMap_eq_of_integers_comap_eq [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (f : F) :
    Q'.ord (algebraMap F F' f) = Q.ord f := by
  obtain ⟨-, hord⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  rw [hord, ramificationIdx_eq_one_of_integers_comap_eq hF hex H hcomp hQ', Nat.cast_one, one_mul]

end TauCeti.Place
