/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Operations
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.UnitNorm
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.GaussSum
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
import TauCeti.NumberTheory.ModularForms.JacobiTheta.GaussSum

/-!
# Milgram's theorem

For an even nondegenerate integral lattice `L` with signature `(t₊, t₀, t₋)`, the Gauss-sum
invariant `sign q_L ∈ ℤ/8` of its discriminant quadratic form, defined by
`∑_{a ∈ A_L} e^{2πi q_L(a)} = √#A_L · e^{2πi·sign(q_L)/8}`, is

```text
sign q_L ≡ t₊ - t₋ (mod 8).
```

This is Milgram's theorem (Nikulin, Theorem 1.3.3). In particular an even unimodular lattice,
whose discriminant form is zero, has `8 ∣ t₊ - t₋`.

## The proof

Both sides are additive over orthogonal sums and invariant under isometry, and the left side is
unchanged under passing to a full sublattice
(`TauCeti.IntegralLattice.gaussSign_discriminantQuadraticModule_restrictFull`). A nondegenerate
lattice of positive rank has a vector `x` of nonzero norm `2m`, and the sublattice
`ℤx + (x^⊥ ∩ L)` has finite index in `L` and is isometric to `⟨2m⟩ ⊥ (x^⊥ ∩ L)`. Induction on
the rank therefore reduces the theorem to the rank-one lattices `⟨2m⟩`. For those the Gauss sum
is half of a classical quadratic Gauss sum of modulus `4|m|`,

```text
∑_{k < 2m} e^{2πi k² / (4m)} = (1 + i) √m = √(2m) · e^{2πi/8}     (m > 0),
```

by Gauss's evaluation (`TauCeti.sum_range_two_mul_cexp_two_pi_I_sq_div_four_mul`), and `⟨2m⟩`
for `m < 0` is the negative of `⟨-2m⟩`.

## Main results

* `TauCeti.IntegralLattice.gaussSign_discriminantQuadraticModule_rankOne`: the Gauss-sum invariant
  of `⟨2m⟩` is the sign of `m`.
* `TauCeti.IntegralLattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg`:
  Milgram's theorem.
* `TauCeti.IntegralLattice.eight_dvd_sigPos_sub_sigNeg_of_isUnimodular`: the signature of an
  even unimodular lattice is divisible by `8`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Theorem 1.3.3.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.
-/

public section

open Complex Module
open scoped Pointwise Real TensorProduct

namespace TauCeti.IntegralLattice

/-! ## The rank-one lattices `⟨2m⟩` -/

variable (m : ℤ) [NeZero m]

/-- For `0 < m`, the Gauss sum of the discriminant form of `⟨2m⟩` is `(1 + i) √m`. -/
private theorem gaussSum_rankOne_of_pos (hm : 0 < m) :
    ((rankOne m).discriminantQuadraticModule (isEven_rankOne m)).gaussSum =
      (1 + I) * √(m : ℝ) := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = M := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  have hn : (2 * (M : ℤ)).natAbs = 2 * M := by omega
  -- `k ↦ k • g` enumerates the discriminant group, which is cyclic of order `2M`.
  let φ : Fin (2 * M) → (rankOne (M : ℤ)).DiscriminantGroup :=
    fun k ↦ ((k : ℕ) : ℤ) • rankOneClass (M : ℤ)
  -- The carrier of the exposed `discriminantQuadraticModule` is the discriminant group, so one
  -- `Fintype` instance serves both the Gauss sum and the enumeration `φ`.
  let inst : Fintype (rankOne (M : ℤ)).DiscriminantGroup := Fintype.ofFinite _
  have hφ : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨fun k l hkl ↦ ?_, ?_⟩
    · have h := congrArg (rankOneDiscriminantEquiv (M : ℤ)) hkl
      simp only [φ, rankOneDiscriminantEquiv_zsmul_rankOneClass, Int.cast_natCast] at h
      have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
      rw [hn, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt l.2] at h'
      exact Fin.ext h'
    · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, natCard_rankOne_discriminantGroup, hn]
  rw [@FiniteQuadraticModule.gaussSum_eq_sum _ inst, Int.cast_natCast,
    ← sum_range_two_mul_cexp_two_pi_I_sq_div_four_mul M, ← Fin.sum_univ_eq_sum_range]
  refine (Fintype.sum_bijective φ hφ _ _ fun k ↦ ?_).symm
  rw [discriminantQuadraticModule_quadratic, discriminantQuadraticMap_zsmul_rankOneClass,
    expCircle_coe]
  push_cast
  ring_nf

omit [NeZero m] in
/-- `√2 · e^{2πi/8} = 1 + i`. -/
private theorem sqrt_two_mul_expCircle_toRatAddCircle_eight_one :
    ((√2 : ℝ) : ℂ) * expCircle (ZMod.toRatAddCircle 8 1) = 1 + I := by
  have h8 : ZMod.toRatAddCircle 8 1 = ((1 / 8 : ℚ) : AddCircle (1 : ℚ)) := by
    simpa using ZMod.toRatAddCircle_natCast 8 1
  have hexp : 2 * (π : ℂ) * I * ((1 / 8 : ℚ) : ℂ) = (π / 4 : ℝ) * I := by
    push_cast
    ring
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt zero_le_two, ofReal_ofNat]
  rw [h8, expCircle_coe, hexp, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  linear_combination (1 + I) / 2 * h2

/-- For `0 < m`, the discriminant form of `⟨2m⟩` has Gauss-sum invariant `1`:
`(1 + i) √m = √(2m) · e^{2πi/8}`. -/
private theorem gaussSign_rankOne_of_pos (hm : 0 < m) :
    ((rankOne m).discriminantQuadraticModule (isEven_rankOne m)).gaussSign = 1 := by
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq _ ?_
  have hcard : Nat.card ((rankOne m).discriminantQuadraticModule (isEven_rankOne m)) =
      (2 * m).natAbs :=
    natCard_rankOne_discriminantGroup m
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = M := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  rw [gaussSum_rankOne_of_pos _ hm, hcard, show (2 * (M : ℤ)).natAbs = 2 * M by omega,
    Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two, Int.cast_natCast,
    ← sqrt_two_mul_expCircle_toRatAddCircle_eight_one]
  push_cast
  ring

omit [NeZero m] in
/-- `⟨2m⟩` is the negative of `⟨-2m⟩`. -/
private theorem rankOne_eq_neg_rankOne_neg : rankOne m = -rankOne (-m) := by
  refine IntegralLattice.ext ?_ ?_
  · ext x
    simp [neg_carrier]
  · refine LinearMap.BilinForm.ext fun x y ↦ ?_
    simp only [neg_form, LinearMap.neg_apply, rankOne_form_apply]
    push_cast
    ring

/-- **Milgram's theorem for `⟨2m⟩`**: the discriminant form of the rank-one lattice `⟨2m⟩` has
Gauss-sum invariant the sign of `m`. -/
theorem gaussSign_discriminantQuadraticModule_rankOne :
    ((rankOne m).discriminantQuadraticModule (isEven_rankOne m)).gaussSign = Int.sign m := by
  rcases (NeZero.ne m).lt_or_gt with hm | hm
  · have : NeZero (-m) := ⟨neg_ne_zero.mpr (NeZero.ne m)⟩
    let e := Isometry.ofEq (rankOne_eq_neg_rankOne_neg m)
    rw [(e.discriminantQuadraticIsometry (isEven_rankOne m)).gaussSign_eq,
      ((rankOne (-m)).discriminantQuadraticIsometryNeg (isEven_rankOne (-m))).gaussSign_eq,
      FiniteQuadraticModule.gaussSign_neg, gaussSign_rankOne_of_pos _ (by omega),
      Int.sign_eq_neg_one_of_neg hm]
    simp
  · rw [gaussSign_rankOne_of_pos m hm, Int.sign_eq_one_of_pos hm, Int.cast_one]

omit [NeZero m] in
/-- The signature difference of `⟨2m⟩` is the sign of `m`. -/
private theorem sigPos_sub_sigNeg_rankOne (hm : m ≠ 0) :
    ((rankOne m).sigPos : ZMod 8) - (rankOne m).sigNeg = Int.sign m := by
  rcases hm.lt_or_gt with hm | hm
  · have h := rankOne_signature_of_neg hm
    simp only [signature, Prod.mk.injEq] at h
    rw [h.1, h.2.2, Int.sign_eq_neg_one_of_neg hm]
    simp
  · have h := rankOne_signature_of_pos hm
    simp only [signature, Prod.mk.injEq] at h
    rw [h.1, h.2.2, Int.sign_eq_one_of_pos hm]
    simp

omit [NeZero m] in
/-- The rank-one Gram-matrix lattice with entry `2m` is `⟨2m⟩`. -/
private theorem ofGramMatrix_singleton_eq_rankOne {c : ℤ} (hc : c = 2 * m)
    (h : (Matrix.of fun (_ _ : Fin 1) ↦ c).IsSymm) :
    ofGramMatrix (Basis.singleton (Fin 1) ℚ) (Matrix.of fun _ _ ↦ c) h = rankOne m := by
  subst hc
  refine IntegralLattice.ext ?_ ?_
  · ext q
    simp [Submodule.mem_span_singleton, eq_comm]
  · refine LinearMap.BilinForm.ext fun p q ↦ ?_
    let _ : DecidableEq (Fin 1) := Classical.decEq _
    rw [rankOne_form_apply, ofGramMatrix_form, Matrix.toBilin_apply]
    simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply, Matrix.of_apply,
      eq_intCast]
    push_cast
    ring

/-! ## Splitting off a vector of nonzero norm, up to finite index -/

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) (x : L)

/-- The sublattice `ℤx + (x^⊥ ∩ L)` of `L`, for a lattice vector `x`. -/
private def splitCarrier : Submodule ℤ V :=
  ℤ ∙ (x : V) ⊔ L.carrier ⊓ LinearMap.ker ((L.form x).restrictScalars ℤ)

private theorem splitCarrier_le : splitCarrier L x ≤ L.carrier :=
  sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr x.2) inf_le_left

/-- If `x` has nonzero norm `d`, then `ℤx + (x^⊥ ∩ L)` contains `dL`: every `y ∈ L` satisfies
`d • y = (x, y) • x + (d • y - (x, y) • x)` with the second summand orthogonal to `x`. Hence it
is a full sublattice. -/
private theorem isLattice_splitCarrier (hx : L.integralNorm x ≠ 0) :
    (splitCarrier L x).IsLattice ℚ := by
  have hd : ((L.integralNorm x : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hx
  refine Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ (M := Units.mk0 _ hd • L.carrier) ?_
    (Submodule.FG.of_le Submodule.IsLattice.fg (splitCarrier_le L x))
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  set c : ℤ := L.integralForm x ⟨y, hy⟩
  have hc : L.form x y = c := (L.integralForm_cast x ⟨y, hy⟩).symm
  have hxx : L.form x x = L.integralNorm x := by rw [integralNorm_cast, norm_apply]
  have hsplit : (Units.mk0 _ hd) • y = c • (x : V) + (L.integralNorm x • y - c • (x : V)) := by
    rw [Units.smul_mk0, Int.cast_smul_eq_zsmul]
    abel
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    ⟨L.carrier.sub_mem (L.carrier.smul_mem _ hy) (L.carrier.smul_mem _ x.2), ?_⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.restrictScalars_apply, map_sub,
    map_zsmul, hc, hxx, zsmul_eq_mul]
  ring

/-- The full sublattice `ℤx + (x^⊥ ∩ L)` of `L`, for a vector `x` of nonzero norm. -/
private noncomputable def splitLattice (hx : L.integralNorm x ≠ 0) : IntegralLattice V :=
  haveI := isLattice_splitCarrier L x hx
  L.restrictFull (splitCarrier L x) (splitCarrier_le L x)

variable (hx : L.integralNorm x ≠ 0)

private theorem splitLattice_carrier : (splitLattice L x hx).carrier = splitCarrier L x :=
  haveI := isLattice_splitCarrier L x hx
  restrictFull_carrier ..

private theorem splitLattice_form : (splitLattice L x hx).form = L.form :=
  haveI := isLattice_splitCarrier L x hx
  restrictFull_form ..

private instance [L.IsNondegenerate] : (splitLattice L x hx).IsNondegenerate :=
  ⟨by rw [splitLattice_form]; exact L.form_nondegenerate⟩

/-- The integral form of the sublattice is the form of `L`. -/
private theorem integralForm_splitLattice_cast (a b : splitLattice L x hx) :
    ((splitLattice L x hx).integralForm a b : ℚ) = L.form a b := by
  rw [integralForm_cast, splitLattice_form]

/-- The vector `x`, as an element of the sublattice `ℤx + (x^⊥ ∩ L)`. -/
private def splitVector : splitLattice L x hx :=
  ⟨x, by
    rw [splitLattice_carrier]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)⟩

/-- In `ℤx + (x^⊥ ∩ L)`, the line through `x` and its orthogonal complement are complementary. -/
private theorem isCompl_splitLattice :
    IsCompl (ℤ ∙ splitVector L x hx)
      ((splitLattice L x hx).integralForm.orthogonal (ℤ ∙ splitVector L x hx)) := by
  have hxx : L.form x x = L.integralNorm x := by rw [integralNorm_cast, norm_apply]
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz hzo
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have h := congrArg (Int.cast : ℤ → ℚ)
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp hzo) _
        (Submodule.mem_span_singleton_self (splitVector L x hx)))
    rw [integralForm_splitLattice_cast, Int.cast_zero, Submodule.coe_smul, map_zsmul,
      zsmul_eq_mul] at h
    have hn : L.form x x ≠ 0 := by
      rw [hxx]
      exact_mod_cast hx
    have ha : a = 0 := by
      simpa [splitVector, hn] using h
    rw [ha, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨z, hz⟩ -
    have hz' : z ∈ splitCarrier L x := by rwa [splitLattice_carrier] at hz
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.mp hz'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have htN : t ∈ (splitLattice L x hx).carrier := by
      rw [splitLattice_carrier]
      exact Submodule.mem_sup_right ht
    have hdecomp : (⟨a • (x : V) + t, hz⟩ : splitLattice L x hx) =
        a • splitVector L x hx + ⟨t, htN⟩ :=
      Subtype.ext (by simp [splitVector])
    rw [hdecomp]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hn
    have htx : L.form x t = 0 := ht.2
    apply Int.cast_injective (α := ℚ)
    rw [integralForm_splitLattice_cast, Int.cast_zero,
      Submodule.coe_smul, map_zsmul, LinearMap.smul_apply]
    simp [splitVector, htx]

private theorem isEven_splitLattice (hL : L.IsEven) : (splitLattice L x hx).IsEven :=
  haveI := isLattice_splitCarrier L x hx
  isEven_restrictFull hL _ _

private theorem gaussSign_splitLattice [L.IsNondegenerate] (hL : L.IsEven) :
    ((splitLattice L x hx).discriminantQuadraticModule
      (isEven_splitLattice L x hx hL)).gaussSign = (L.discriminantQuadraticModule hL).gaussSign :=
  haveI := isLattice_splitCarrier L x hx
  gaussSign_discriminantQuadraticModule_restrictFull L hL _ _

/-- The orthogonal complement of `x` in `ℤx + (x^⊥ ∩ L)`, as a lattice in its own rational
span. -/
private noncomputable abbrev splitComplement :=
  ofIntegralForm
    ((splitLattice L x hx).integralForm.restrict
      ((splitLattice L x hx).integralForm.orthogonal (ℤ ∙ splitVector L x hx)))
    ((splitLattice L x hx).isSymm_integralForm.restrict _)

private theorem integralForm_splitVector {m : ℤ} (hm : L.norm x = 2 * m) :
    (splitLattice L x hx).integralForm (splitVector L x hx) (splitVector L x hx) = 2 * m := by
  apply Int.cast_injective (α := ℚ)
  rw [integralForm_splitLattice_cast, ← norm_apply]
  push_cast
  exact hm

/-- For `x` of norm `2m`, the sublattice `ℤx + (x^⊥ ∩ L)` is isometric to `⟨2m⟩ ⊥ (x^⊥ ∩ L)`. -/
private noncomputable def splitIsometry (m : ℤ) [NeZero m] (hm : L.norm x = 2 * m) :
    Isometry ((rankOne m).orthogonalSum (splitComplement L x hx)) (splitLattice L x hx) :=
  (((Isometry.ofEq (ofGramMatrix_singleton_eq_rankOne m (integralForm_splitVector L x hx hm)
      (by ext; rfl))).symm.trans
    ((splitLattice L x hx).spanSingletonIsometry _ fun h ↦ NeZero.ne m <| by
      have hxK := integralForm_splitVector L x hx hm
      simp only [h, map_zero] at hxK
      omega)).orthogonalSum (Isometry.refl _)).trans
    ((splitLattice L x hx).orthogonalSumIsometryOfIsCompl _ _ (isCompl_splitLattice L x hx) le_rfl)

/-! ## Milgram's theorem -/

/-- **Milgram's theorem.** The Gauss-sum invariant of the discriminant form of an even
nondegenerate lattice is its signature `t₊ - t₋` modulo `8`. -/
theorem gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg [L.IsNondegenerate]
    (hL : L.IsEven) :
    (L.discriminantQuadraticModule hL).gaussSign = (L.sigPos : ZMod 8) - L.sigNeg := by
  have := L.finiteDimensional
  induction hn : finrank ℚ V generalizing V with
  | zero =>
    -- In rank zero the discriminant group and the signature both vanish.
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    have : Subsingleton (L.discriminantQuadraticModule hL) :=
      inferInstanceAs (Subsingleton L.DiscriminantGroup)
    have h := L.signature_sum_eq_finrank
    rw [FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton, show L.sigPos = 0 by omega,
      show L.sigNeg = 0 by omega, Nat.cast_zero, sub_zero]
  | succ n ih =>
    -- Split off a vector `x` of norm `2m ≠ 0`, up to finite index.
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ := L.exists_integralNorm_ne_zero
    obtain ⟨m, hm⟩ := hL.exists_norm_eq_two_mul x
    have : NeZero m := ⟨by
      rintro rfl
      rw [← integralNorm_cast, Int.cast_zero, mul_zero] at hm
      exact hx (by exact_mod_cast hm)⟩
    set T := (splitLattice L x hx).integralForm.orthogonal (ℤ ∙ splitVector L x hx)
    set B := splitComplement L x hx
    let e := splitIsometry L x hx m hm
    have hS : ((rankOne m).orthogonalSum B).IsEven :=
      e.isEven_iff.mpr (isEven_splitLattice L x hx hL)
    have hB : B.IsEven := ((isEven_orthogonalSum_iff _ _).mp hS).2
    have : ((rankOne m).orthogonalSum B).IsNondegenerate := e.symm.isNondegenerate
    have : B.IsNondegenerate :=
      ⟨(((rankOne m).nondegenerate_orthogonalSum_iff B).mp (form_nondegenerate _)).2⟩
    -- The complement has rank `n`, so the induction hypothesis applies to it.
    have hfin : finrank ℚ (ℚ ⊗[ℤ] T) = n := by
      have := B.finiteDimensional
      have h := (e : (ℚ × (ℚ ⊗[ℤ] T)) ≃ₗ[ℚ] V).finrank_eq
      rw [finrank_prod, finrank_self, hn, add_comm n] at h
      exact Nat.add_left_cancel h
    -- Both invariants are additive over `⟨2m⟩ ⊥ B`, and neither changes on the sublattice.
    have hpos : L.sigPos = (rankOne m).sigPos + B.sigPos := by
      rw [← sigPos_orthogonalSum, e.sigPos_eq]
      simp only [sigPos, splitLattice_form]
    have hneg : L.sigNeg = (rankOne m).sigNeg + B.sigNeg := by
      rw [← sigNeg_orthogonalSum, e.sigNeg_eq]
      simp only [sigNeg, splitLattice_form]
    rw [← gaussSign_splitLattice L x hx hL, ← (e.discriminantQuadraticIsometry hS).gaussSign_eq,
      ((rankOne m).discriminantQuadraticIsometryOrthogonalSum B (isEven_rankOne m)
        hB).gaussSign_eq,
      FiniteQuadraticModule.gaussSign_prod (isNondegenerate_discriminantQuadraticModule _ _)
        (isNondegenerate_discriminantQuadraticModule _ _),
      gaussSign_discriminantQuadraticModule_rankOne, ih B hB B.finiteDimensional hfin,
      ← sigPos_sub_sigNeg_rankOne m (NeZero.ne m), hpos, hneg]
    push_cast
    ring

/-- **The signature of an even unimodular lattice is divisible by `8`.** Its discriminant form
is zero, so Milgram's theorem gives `t₊ - t₋ ≡ 0 (mod 8)`. -/
theorem eight_dvd_sigPos_sub_sigNeg_of_isUnimodular (hL : L.IsEven) (hU : L.IsUnimodular) :
    (8 : ℤ) ∣ L.sigPos - L.sigNeg := by
  have : L.IsNondegenerate := ⟨hU.nondegenerate⟩
  have : Subsingleton (L.discriminantQuadraticModule hL) :=
    (isUnimodular_iff_subsingleton_discriminantGroup L).mp hU
  have h := gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg L hL
  rw [FiniteQuadraticModule.gaussSign_eq_zero_of_subsingleton] at h
  have h8 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((L.sigPos : ℤ) - L.sigNeg) 8).mp
  push_cast at h8
  exact_mod_cast h8 h.symm

end TauCeti.IntegralLattice
