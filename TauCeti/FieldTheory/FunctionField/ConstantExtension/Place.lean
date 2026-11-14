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

For an algebraic function field `F / k` and a linearly disjoint constant extension `F' = F · K`,
every place of `F' / K` is trivial on `F` or contracts to a unique place of `F / k`, and every place
of `F / k` extends to `F' / K`. Rational places extend uniquely, stay rational, and are unramified;
base change to an algebraic closure gives unramifiedness over any perfect exact base field `k`
(Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Section III.6).
-/

public section

open scoped TensorProduct IntermediateField WithZero nonZeroDivisors

namespace TauCeti.Place

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F']
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

/-- A place of `F' / K` is trivial on `F` precisely when its valuation ring contains `F`. -/
theorem isTrivialOn_iff_integers_comap_eq_top (Q' : Place K F') :
    Q'.valuation.IsTrivialOn F ↔ Q'.integers.comap (algebraMap F F') = ⊤ := by
  refine ⟨fun h ↦ ValuationSubring.ext _ _ fun f ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩,
    fun h ↦ ⟨fun f hf ↦ ?_⟩⟩
  · rw [ValuationSubring.mem_comap, Q'.mem_integers_iff]
    rcases eq_or_ne f 0 with rfl | hf; · simp
    exact (h.eq_one f hf).le
  · have hmem (x : F) : Q'.valuation (algebraMap F F' x) ≤ 1 :=
      Q'.mem_integers_iff.mp (ValuationSubring.mem_comap.mp (h.symm ▸ ValuationSubring.mem_top x))
    have h2 := hmem f⁻¹
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Q'.valuation.ne_zero_iff).mpr
      ((map_ne_zero (algebraMap F F')).mpr hf)))] at h2
    exact le_antisymm (hmem f) h2

/-- **Dichotomy for places under an arbitrary constant extension.** -/
theorem isTrivialOn_or_existsUnique_integers_comap_eq (hF : IsFunctionField k F) (Q' : Place K F') :
    Q'.valuation.IsTrivialOn F ∨
      ∃! Q : Place k F, Q'.integers.comap (algebraMap F F') = Q.integers := by
  by_cases hV : Q'.integers.comap (algebraMap F F') = ⊤
  · exact Or.inl ((isTrivialOn_iff_integers_comap_eq_top Q').mpr hV)
  · have hk : ∀ c : k, algebraMap k F c ∈ Q'.integers.comap (algebraMap F F') := fun c ↦ by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply k F F',
        IsScalarTower.algebraMap_apply k K F']
      exact Q'.algebraMap_mem_integers _
    obtain ⟨Q, hQ, huniq⟩ := existsUnique_integers_eq hF hk hV
    exact Or.inr ⟨Q, hQ.symm, fun Q₁ hQ₁ ↦ huniq Q₁ hQ₁.symm⟩

omit [Algebra k K] [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- A contracting place has positive ramification index over `F` scaling `Q.ord`. -/
theorem ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq
    {Q : Place k F} {Q' : Place K F'} (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    0 < Q'.ramificationIdx F ∧
      ∀ f : F, Q'.ord (algebraMap F F' f) = Q'.ramificationIdx F * Q.ord f := by
  set w := Q'.valuation.comap (algebraMap F F')
  have hw : w.IsEquiv Q.valuation := (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| by
    ext f; rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ← Q'.mem_integers_iff,
      ← ValuationSubring.mem_comap, hQ', Q.mem_integers_iff, Valuation.mem_valuationSubring_iff]
  obtain ⟨t, ht⟩ := Q.ord_surjective 1
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hwt : w t < 1 := (Valuation.isEquiv_iff_val_lt_one.mp hw).mpr
    (by rw [Q.valuation_eq_exp_neg_ord ht0, ht]; simp)
  have : w.IsNontrivial := ⟨t, w.ne_zero_iff.mpr ht0, hwt.ne⟩
  have hpos : 0 < Valuation.ordIndex w :=
    Nat.pos_of_ne_zero (Valuation.ordIndex_ne_zero_of_isNontrivial w)
  have hkt : w.IsTrivialOn k :=
    ⟨fun c hc ↦ (Valuation.isEquiv_iff_val_eq_one.mp hw).mpr (Q.isTrivialOn.eq_one c hc)⟩
  let Q₀ : Place k F := ⟨w.normalization, Valuation.normalization_surjective w hpos.ne',
    Valuation.IsTrivialOn.normalization w⟩
  have hQ₀ : w.normalization = Q.valuation :=
    congrArg Place.valuation (eq_of_isEquiv ((Valuation.isEquiv_normalization w).trans hw) : Q₀ = Q)
  refine ⟨by rwa [ramificationIdx_def], fun f ↦ ?_⟩
  have hord := Valuation.ord_normalization_mul_ordIndex w f
  rw [hQ₀, Q.ord_valuation, mul_comm, ← ramificationIdx_def, Valuation.ord_comap,
    Q'.ord_valuation] at hord
  exact hord.symm

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

/-- **Existence of place extensions across a linearly disjoint constant extension.** -/
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
  let q : O ⊗[k] K →ₐ[k] Q.ResidueField ⊗[k] K := Algebra.TensorProduct.map resAlg (AlgHom.id k K)
  have : Nontrivial (Q.ResidueField ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k Q.ResidueField K
      (algebraMap k _).injective (algebraMap k K).injective
  let x₀ : g.range.toSubring := ⟨algebraMap F F' ϖ, ⟨⟨ϖ, hϖO⟩ ⊗ₜ[k] 1, by simp [g]⟩⟩
  have hx₀ : ¬ IsUnit x₀ := fun hu ↦ by
    obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨z, hz⟩ := u.2
    change g z = u.1 at hz
    have hmul : g ((⟨ϖ, hϖO⟩ ⊗ₜ[k] 1) * z) = g 1 := by
      rw [map_mul, map_one, show g (⟨ϖ, hϖO⟩ ⊗ₜ[k] 1) = x₀.1 by simp [g, x₀], hz]
      exact congrArg Subtype.val hu'
    have hres0 : resAlg ⟨ϖ, hϖO⟩ = 0 :=
      (Q.residue_eq_zero_iff_ord_pos (f := ⟨ϖ, hϖO⟩) hϖ0).mpr (by simp [hϖ1])
    have hq1 := congrArg q (hg_inj hmul)
    simp [q, hres0] at hq1
  obtain ⟨V, hRV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span ({x₀} : Set g.range.toSubring)) ((Ideal.span_singleton_eq_top.not).mpr hx₀)
  have hx₀_mem : algebraMap F F' ϖ ∈ V.nonunits :=
    hIV ⟨x₀, Ideal.subset_span (Set.mem_singleton x₀), rfl⟩
  have hϖ_inv_notMem : (algebraMap F F' ϖ)⁻¹ ∉ V :=
    (V.mem_nonunits_iff_or.mp hx₀_mem).resolve_left ((map_ne_zero _).mpr hϖ0)
  have hV_ne_top : V ≠ ⊤ := fun htop ↦ hϖ_inv_notMem (htop ▸ ValuationSubring.mem_top _)
  have hKV : ∀ c : K, algebraMap K F' c ∈ V := fun c ↦ hRV ⟨1 ⊗ₜ[k] c, by simp [g]⟩
  have hle : Q.integers ≤ V.comap (algebraMap F F') := fun f hf ↦ hRV ⟨⟨f, hf⟩ ⊗ₜ[k] 1, by simp [g]⟩
  have hcomap_ne : V.comap (algebraMap F F') ≠ ⊤ := fun htop ↦ hϖ_inv_notMem <| by
    rw [← map_inv₀]; exact ValuationSubring.mem_comap.mp (htop.symm ▸ ValuationSubring.mem_top ϖ⁻¹)
  have hF' : IsFunctionField K F' := hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
  refine ⟨ofValuationSubring hF' hKV hV_ne_top, ?_⟩
  rw [integers_ofValuationSubring]; exact (Q.integers.eq_of_le_of_ne_top hle hcomap_ne).symm

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
    have := Finset.inf'_le (fun j ↦ Q.ord (g j)) hi; omega
  have hc_ex (i : ι) : ∃ c : k, i ∈ g.support → Q.valuation (h i - algebraMap k F c) < 1 :=
    if hi : i ∈ g.support then
      let ⟨c, hc⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hQ) _ (hh_mem i hi)
      ⟨c, fun _ ↦ hc⟩
    else ⟨0, fun h' ↦ (hi h').elim⟩
  choose c hc using hc_ex
  have hci₀ : c i₀ ≠ 0 := fun hc0 ↦ by
    have hlt := hc i₀ hi₀s; rw [hc0, map_zero, sub_zero] at hlt
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
  rw [hgi, map_mul, map_zpow₀, map_add, hck]; ring

omit [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
private theorem valuation_and_ord_of_repr_decomposition {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) {ϖ : F} (hϖ : Q.ord ϖ = 1)
    {ι : Type*} (b : Module.Basis ι k K) (m : ℤ) {C : K} (hC0 : C ≠ 0) {s : Finset ι}
    {r : ι → F} (hr : ∀ i ∈ s, Q.valuation (r i) < 1) :
    let R := ∑ i ∈ s, algebraMap F F' (r i) * algebraMap K F' (b i)
    Q'.valuation R < 1 ∧ Q'.valuation (algebraMap K F' C + R) = 1 ∧
      Q'.ord ((algebraMap F F' ϖ) ^ m * (algebraMap K F' C + R)) = Q'.ramificationIdx F * m := by
  intro R
  obtain ⟨he_pos, hord_scale⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  have hR : Q'.valuation R < 1 := (Q'.valuation.map_sum_lt' zero_lt_one) fun i hi ↦ by
    rw [map_mul]
    rcases eq_or_ne (r i) 0 with h0 | h0; · simp [h0]
    have hord_pos : 0 < Q.ord (r i) := by
      have hv := hr i hi; rw [Q.valuation_eq_exp_neg_ord h0] at hv
      exact neg_lt_zero.mp (WithZero.exp_lt_one_iff.mp hv)
    have hri_lt : Q'.valuation (algebraMap F F' (r i)) < 1 := by
      rw [Q'.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr h0), WithZero.exp_lt_one_iff,
        neg_lt_zero, hord_scale]
      exact mul_pos (by exact_mod_cast he_pos) hord_pos
    exact (mul_le_of_le_one_right'
      (Q'.mem_integers_iff.mp (Q'.algebraMap_mem_integers _))).trans_lt hri_lt
  have hC1 : Q'.valuation (algebraMap K F' C) = 1 := Q'.isTrivialOn.eq_one C hC0
  have hu1 : Q'.valuation (algebraMap K F' C + R) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left Q'.valuation (hR.trans_eq hC1.symm), hC1]
  refine ⟨hR, hu1, ?_⟩
  have hu0 : algebraMap K F' C + R ≠ 0 := fun h ↦ by simp [h] at hu1
  have hu_ord : Q'.ord (algebraMap K F' C + R) = 0 :=
    (Q'.ord_eq_iff_valuation_eq_exp_neg hu0).mpr (by simpa using hu1)
  rw [Q'.ord_mul (zpow_ne_zero m ((map_ne_zero _).mpr hϖ0)) hu0,
    Q'.ord_zpow (algebraMap F F' ϖ) m, hord_scale, hϖ, mul_one, hu_ord, add_zero, mul_comm]

private theorem exists_ord_and_const_of_degree_eq_one
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1)
    {w : F'} (hw0 : w ≠ 0) :
    ∃ (n : ℤ) (c : K),
      (∀ {Q' : Place K F'}, Q'.integers.comap (algebraMap F F') = Q.integers →
        Q'.ord w = Q'.ramificationIdx F * n) ∧
      (∀ {Q' : Place K F'}, n = 0 → Q'.integers.comap (algebraMap F F') = Q.integers →
        Q'.valuation (w - algebraMap K F' c) < 1) := by
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k K F')
  let _ : Algebra (F ⊗[k] K) F' := π.toRingHom.toAlgebra
  have : IsFractionRing (F ⊗[k] K) F' := isFractionRing_tensorProduct_of_linearDisjoint H hcomp
  obtain ⟨z₁, z₂, hz₂, hw⟩ := IsFractionRing.div_surjective (A := F ⊗[k] K) w
  have hw_div : w = π z₁ / π z₂ := hw.symm
  have hπ_inj := productMap_injective_iff_linearDisjoint.mpr H
  have hz₂0 : z₂ ≠ 0 := nonZeroDivisors.ne_zero hz₂
  have hz₁0 : z₁ ≠ 0 := fun h ↦ hw0 (by rw [hw_div, h, map_zero, zero_div])
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  let b := Module.Basis.ofVectorSpace k K
  obtain ⟨m₁, C₁, s₁, r₁, hC₁, hr₁, hz₁_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz₁0
  obtain ⟨m₂, C₂, s₂, r₂, hC₂, hr₂, hz₂_eq⟩ := exists_repr_decomposition (F' := F') hQ hϖ b hz₂0
  refine ⟨m₁ - m₂, C₁ / C₂, fun {Q'} hQ' ↦ ?_, fun {Q'} hn hQ' ↦ ?_⟩
  · obtain ⟨-, -, hord₁⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b m₁ hC₁ hr₁
    obtain ⟨-, -, hord₂⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b m₂ hC₂ hr₂
    rw [hw_div, Q'.ord_div ((map_ne_zero_iff π hπ_inj).mpr hz₁0)
      ((map_ne_zero_iff π hπ_inj).mpr hz₂0), hz₁_eq, hz₂_eq, hord₁, hord₂, mul_sub]
  · obtain ⟨hR₁, -, -⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b m₁ hC₁ hr₁
    obtain ⟨hR₂, hu₂, -⟩ := valuation_and_ord_of_repr_decomposition hQ' hϖ b m₂ hC₂ hr₂
    set R₁ := ∑ i ∈ s₁, algebraMap F F' (r₁ i) * algebraMap K F' (b i)
    set R₂ := ∑ i ∈ s₂, algebraMap F F' (r₂ i) * algebraMap K F' (b i)
    have hp0 : (algebraMap F F' ϖ) ^ m₂ ≠ 0 := zpow_ne_zero m₂ ((map_ne_zero _).mpr hϖ0)
    have hw_simp : w = (algebraMap K F' C₁ + R₁) / (algebraMap K F' C₂ + R₂) := by
      rw [hw_div, hz₁_eq, hz₂_eq, sub_eq_zero.mp hn, mul_div_mul_left _ _ hp0]
    have hd0 : algebraMap K F' C₂ + R₂ ≠ 0 := fun h ↦ by simp [h] at hu₂
    have hdiff : w - algebraMap K F' (C₁ / C₂) =
        (R₁ - algebraMap K F' (C₁ / C₂) * R₂) / (algebraMap K F' C₂ + R₂) := by
      rw [hw_simp, map_div₀]; field_simp [hd0, (map_ne_zero (algebraMap K F')).mpr hC₂]; ring
    rw [hdiff, map_div₀, hu₂, div_one]
    refine Valuation.map_sub_lt Q'.valuation hR₁ ?_
    rw [map_mul]
    exact (mul_le_of_le_one_left'
      (Q'.mem_integers_iff.mp (Q'.algebraMap_mem_integers _))).trans_lt hR₂

/-- **A rational place is unramified under any linearly disjoint constant extension.** -/
theorem ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1) {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.ramificationIdx F = 1 := by
  obtain ⟨w, hw1⟩ := Q'.ord_surjective 1
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  obtain ⟨n, -, hord, -⟩ := exists_ord_and_const_of_degree_eq_one H hcomp hQ hw0
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) ⟨n, hw1 ▸ hord hQ'⟩

/-- **A rational place has at most one extension across a linearly disjoint constant extension.** -/
theorem eq_of_degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1)
    {Q₁' Q₂' : Place K F'} (h₁ : Q₁'.integers.comap (algebraMap F F') = Q.integers)
    (h₂ : Q₂'.integers.comap (algebraMap F F') = Q.integers) : Q₁' = Q₂' := by
  have he₁ := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₁
  have he₂ := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₂
  refine Place.ext <| Valuation.ext fun w ↦ ?_
  rcases eq_or_ne w 0 with rfl | hw0; · simp
  obtain ⟨n, -, hord, -⟩ := exists_ord_and_const_of_degree_eq_one H hcomp hQ hw0
  rw [Q₁'.valuation_eq_exp_neg_ord hw0, Q₂'.valuation_eq_exp_neg_ord hw0, hord h₁, hord h₂,
    he₁, he₂]

/-- **Unique extension of rational places across a linearly disjoint constant extension.** -/
theorem existsUnique_integers_comap_eq_of_degree_eq_one (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1) :
    ∃! Q' : Place K F', Q'.integers.comap (algebraMap F F') = Q.integers :=
  let ⟨Q', hQ'⟩ := exists_integers_comap_eq hF H hcomp Q
  ⟨Q', hQ', fun _ h₁ ↦ eq_of_degree_eq_one_of_integers_comap_eq H hcomp hQ h₁ hQ'⟩

/-- A place extending a rational place across a linearly disjoint constant extension is rational. -/
theorem degree_eq_one_of_integers_comap_eq
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} (hQ : Q.degree = 1)
    {Q' : Place K F'} (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.degree = 1 := by
  have he := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H hcomp hQ hQ'
  rw [degree_eq_one_iff_forall_exists_valuation_sub_lt_one]; intro w hw
  rcases eq_or_ne w 0 with rfl | hw0; · exact ⟨0, by simp⟩
  obtain ⟨n, c, hord, hval⟩ := exists_ord_and_const_of_degree_eq_one H hcomp hQ hw0
  have hn : 0 ≤ n := by
    have h := Q'.mem_integers_iff_ord_nonneg.mp hw
    rwa [hord hQ', he, Nat.cast_one, one_mul] at h
  rcases lt_or_eq_of_le hn with hlt | heq
  · exact ⟨0, by rw [map_zero, sub_zero, Q'.valuation_eq_exp_neg_ord hw0,
      WithZero.exp_lt_one_iff, neg_lt_zero, hord hQ', he]; omega⟩
  · exact ⟨c, hval heq.symm hQ'⟩

omit [Field k] [Algebra k K] [Algebra k F] [Algebra k F'] [IsScalarTower k K F']
  [IsScalarTower k F F'] in
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
  let M' : IntermediateField F' F'' :=
    { M.toSubfield with algebraMap_mem' := fun _ ↦ hL (hcomp₁ ▸ IntermediateField.mem_top) }
  have hM' : constantCompositum F' Ω F'' ≤ M' :=
    (constantCompositum_le_iff F' Ω F'').mpr fun ω ↦ algebraMap_mem_constantCompositum F Ω F'' ω
  exact top_le_iff.mp fun z _ ↦ hM' (hcomp₂ ▸ IntermediateField.mem_top)

private theorem linearDisjoint_of_integers_comap_eq [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F := by
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hx₀
  obtain ⟨he', hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
  have : FiniteDimensional k⟮ϖ⟯ F := hF.finiteDimensional_adjoin <|
    Valuation.transcendental_of_ne_one k ϖ hϖ0 (by rw [Q.valuation_eq_exp_neg_ord hϖ0, hϖ]; simp)
  have hxK : Transcendental K (algebraMap F F' ϖ) :=
    Valuation.transcendental_of_ne_one K _ ((map_ne_zero _).mpr hϖ0) <| by
      rw [Q'.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr hϖ0), hord', hϖ]
      exact (WithZero.exp_eq_one.not).mpr (by omega)
  exact linearDisjoint_of_isGeometricallyReduced_of_transcendental hex hxK

private theorem ramificationIdx_eq_one_of_isAlgClosed [PerfectField k] [IsAlgClosed K]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) :
    Q'.ramificationIdx F = 1 := by
  obtain ⟨_, hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  let kbar := algebraicClosure k K; have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let F₁ := constantCompositum F kbar F'
  let _ : Algebra kbar F₁ := constantCompositumAlgebra F kbar F'
  have : IsScalarTower kbar F₁ F' := isScalarTower_constantCompositum F kbar F'
  have : IsScalarTower k kbar F₁ := isScalarTower_base_constantCompositum k F kbar F'
  have hcomp₁ : constantCompositum F kbar F₁ = ⊤ :=
    (constantCompositum_eq_top_iff F kbar F' F₁).2 rfl
  have hF₁ : IsFunctionField kbar F₁ := hF.of_constantCompositum_eq_top hcomp₁
  have hcomp₂ : constantCompositum F₁ K F' = ⊤ :=
    constantCompositum_eq_top_of_eq_top F K F' F₁ hcomp
  let V₁ := Q'.integers.comap (algebraMap F₁ F')
  have hV₁_ne : V₁ ≠ ⊤ := fun htop ↦ Q.integers_ne_top <| eq_top_iff.mpr fun f _ ↦ by
    have h : algebraMap F F₁ f ∈ V₁ := htop ▸ ValuationSubring.mem_top _
    simpa [← hQ', V₁, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply F F₁ F'] using h
  have hkbarV₁ : ∀ c : kbar, algebraMap kbar F₁ c ∈ V₁ := fun c ↦ by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply kbar F₁ F',
      IsScalarTower.algebraMap_apply kbar K F']
    exact Q'.algebraMap_mem_integers _
  let Q₁ : Place kbar F₁ := ofValuationSubring hF₁ hkbarV₁ hV₁_ne
  have hQ'Q₁ : Q'.integers.comap (algebraMap F₁ F') = Q₁.integers :=
    (integers_ofValuationSubring hF₁ hkbarV₁ hV₁_ne).symm
  have H₂ := linearDisjoint_of_integers_comap_eq hF₁ (hex.of_constantCompositum_eq_top hcomp₁) hQ'Q₁
  have : FiniteDimensional kbar Q₁.ResidueField := Q₁.finiteDimensional_residueField hF₁
  have he_top := ramificationIdx_eq_one_of_degree_eq_one_of_integers_comap_eq H₂ hcomp₂
    Q₁.degree_eq_one_of_isAlgClosed_of_isIntegral hQ'Q₁
  obtain ⟨-, hord_top⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'Q₁
  have : Algebra.IsIntegral F F₁ :=
    (isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp₁).isIntegral
  have hQ₁Q : Q₁.restrict k F = Q := (restrict_eq_iff_integers_le k F Q₁ Q).mpr fun f hf ↦ by
    rwa [← hQ'Q₁, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply F F₁ F',
      ← ValuationSubring.mem_comap, hQ']
  have he_bot := ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) hcomp₁ Q₁
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have h1 : Q'.ord (algebraMap F F' ϖ) = 1 := by
    rw [IsScalarTower.algebraMap_apply F F₁ F', hord_top, he_top, Nat.cast_one, one_mul,
      ord_algebraMap_restrict k F Q₁, hQ₁Q, he_bot, Nat.cast_one, one_mul, hϖ]
  rw [hord', hϖ, mul_one] at h1; exact_mod_cast h1

/-- Places are unramified across any linearly disjoint constant extension over perfect exact `k`. -/
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
  have hex' := hex.of_constantCompositum_eq_top_of_linearDisjoint H hcomp
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
  have : Algebra.IsIntegral F' F'' :=
    (isAlgebraic_of_constantCompositum_eq_top (k := K) hcomp').isIntegral
  obtain ⟨Q'', hQ''⟩ := restrict_surjective (k := K) (F := F')
    (hF'.of_constantCompositum_eq_top hcomp') Q'; dsimp only at hQ''
  let _ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K Ω := .of_algebraMap_eq' rfl
  let _ : Algebra F F'' := ((algebraMap F' F'').comp (algebraMap F F')).toAlgebra
  have : IsScalarTower F F' F'' := .of_algebraMap_eq' rfl
  let _ : Algebra k F'' := ((algebraMap F F'').comp (algebraMap k F)).toAlgebra
  have : IsScalarTower k F F'' := .of_algebraMap_eq' rfl
  have : IsScalarTower k Ω F'' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k F F'', IsScalarTower.algebraMap_apply F F' F'',
      ← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k K F',
      ← IsScalarTower.algebraMap_apply K F' F'', IsScalarTower.algebraMap_apply K Ω F'',
      ← IsScalarTower.algebraMap_apply k K Ω]
  have hQ''Q : Q''.integers.comap (algebraMap F F'') = Q.integers := by
    ext f; rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply F F' F'',
      ← mem_integers_restrict_iff K F' Q'', hQ'', ← ValuationSubring.mem_comap, hQ']
  have he_all := ramificationIdx_eq_one_of_isAlgClosed hF hex
    (constantCompositum_tower_eq_top hcomp hcomp') hQ''Q
  obtain ⟨-, hord_all⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ''Q
  obtain ⟨-, hord'⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  obtain ⟨ϖ, hϖ⟩ := Q.exists_isUniformizer
  rw [Q.isUniformizer_iff_ord_eq_one] at hϖ
  have h1 := hord_all ϖ
  rw [he_all, Nat.cast_one, one_mul, hϖ, IsScalarTower.algebraMap_apply F F' F'',
    ord_algebraMap_restrict K F' Q'', hQ'', hord', hϖ, mul_one] at h1
  exact Nat.eq_one_of_mul_eq_one_left (by exact_mod_cast h1)

/-- Normalized orders on `F` are preserved by linearly disjoint constant extensions over `k`. -/
theorem ord_algebraMap_eq_of_integers_comap_eq [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F K F' = ⊤) {Q : Place k F} {Q' : Place K F'}
    (hQ' : Q'.integers.comap (algebraMap F F') = Q.integers) (f : F) :
    Q'.ord (algebraMap F F' f) = Q.ord f := by
  obtain ⟨-, hord⟩ := ramificationIdx_pos_and_ord_algebraMap_eq_of_integers_comap_eq hQ'
  rw [hord, ramificationIdx_eq_one_of_integers_comap_eq hF hex H hcomp hQ', Nat.cast_one, one_mul]

end TauCeti.Place
