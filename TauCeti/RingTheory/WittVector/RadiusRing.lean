/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Ultra
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Valuation.ExtendToLocalization
public import TauCeti.RingTheory.WittVector.GaussValuation
public import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# The radius rings `A^r` and their degree

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser, `0 < v(ϖ) < 1`. Inverting the
Teichmüller representative `[ϖ]` in `𝕎 O` adjoins the Teichmüller representatives of all elements
of `K`: the localisation `𝕎 O[1/[ϖ]]` is Kedlaya's ring `A_L = W(𝒪_L)[[x] : x ∈ L]` for
`L = K`. For `0 < ρ < 1` the Gauss valuation `λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ`
(`TauCeti.WittVector.gaussValuation`) does not vanish at `[ϖ]`, so it extends to `𝕎 O[1/[ϖ]]`,
where it is a multiplicative ultrametric norm. The *radius ring* `A^r` is the completion of
`𝕎 O[1/[ϖ]]` for this norm. It is a complete Hausdorff Tate ring with a multiplicative norm,
with pseudouniformiser `[ϖ]`.

Kedlaya writes `λ_r(∑ₙ pⁿ [xₙ]) = maxₙ p^(-n) |xₙ|^r` for `r > 0`. This is `λ_ρ ^ r` for
`ρ = p^(-1/r)`, so both norms define the same completion `A^r`; here the ring is indexed by `ρ`.

The *degree* of a nonzero element of `A^r` extends the degree of a Witt vector for `λ_ρ`
(`TauCeti.WittVector.gaussDegree`), the largest index at which its Teichmüller expansion attains
the Gauss norm. Every nonzero `x ∈ A^r` is approximated by some `[ϖ]^(-k) y` with `y ∈ 𝕎 O` up to
an error smaller than `‖x‖`, and the degree of `x` is the degree of any such `y`. It only depends
on the leading part of `x` (Kedlaya, Remark 2.7) and is additive on products (Kedlaya,
Lemma 2.6). Kedlaya proves that `A^r` admits Euclidean division for this degree
(Proposition 2.9), and deduces from Remark 2.7 and Proposition 2.9 that the rings
`A^r{T₁/ρ₁, …, Tₙ/ρₙ}` of restricted power series are noetherian (Theorem 3.2), the input for the
strong noetherianity of the interval rings `B^I` (`TauCeti.WittVector.IntervalRing`, his
Theorem 4.10). That deduction is
`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`, whose two hypotheses
are Remark 2.7, proved here, and Proposition 2.9.

## Main definitions

* `TauCeti.WittVector.RadiusLocalization` : `𝕎 O[1/[ϖ]]`, normed by the Gauss norm `λ_ρ`.
* `TauCeti.WittVector.radiusNorm` : the extension of `λ_ρ` to `𝕎 O[1/[ϖ]]`, as an absolute
  value.
* `TauCeti.WittVector.RadiusRing` : the radius ring `A^r`, the completion of
  `RadiusLocalization`.
* `TauCeti.WittVector.RadiusRing.degree` : Kedlaya's degree on `A^r`.

## Main results

* `TauCeti.WittVector.isNonarchimedean_radiusNorm` : the Gauss norm on `𝕎 O[1/[ϖ]]` is
  nonarchimedean.
* `TauCeti.WittVector.norm_algebraMap_radiusRing` : on `𝕎 O`, the norm of `A^r` is `λ_ρ`.
* `TauCeti.WittVector.RadiusLocalization.instIsTateRing` : `𝕎 O[1/[ϖ]]` is a Tate ring, with
  pseudouniformiser `[ϖ]`, so its completion `A^r` is a complete Hausdorff Tate ring.
* `TauCeti.WittVector.RadiusRing.exists_norm_teichmuller_pow_mul_sub_lt` : every nonzero
  `x ∈ A^r` has some `y ∈ 𝕎 O` with `‖[ϖ]^k x - y‖ < ‖[ϖ]^k x‖`.
* `TauCeti.WittVector.RadiusRing.degree_eq_gaussDegree` : the degree of `x ∈ A^r` is the degree of
  any `y ∈ 𝕎 O` with `‖[ϖ]^k x - y‖ < ‖[ϖ]^k x‖`.
* `TauCeti.WittVector.RadiusRing.degree_eq_of_norm_sub_lt` : if `‖x - y‖ < ‖x‖`, then `x` and `y`
  have the same degree.
* `TauCeti.WittVector.RadiusRing.degree_mul` : the degree is additive on products.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Definitions 2.2, 2.4 and 2.5, Lemma 2.6, Remark 2.7.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  {v : Valuation K ℝ≥0} {ϖ : O}

local notation "𝕎" => _root_.WittVector p

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ : ℝ≥0}
  (hρ : ρ ∈ Set.Ioo 0 1)

/-- **`𝕎 O[1/[ϖ]]` with the Gauss norm.** This is the localisation of `𝕎 O` away from the
Teichmüller representative `[ϖ]` of a pseudouniformiser `ϖ` (`0 < v(ϖ) < 1`), normed by the
extension of the Gauss valuation `λ_ρ` (`TauCeti.WittVector.radiusNorm`); its completion is the
radius ring `A^r`. -/
-- The body is exposed because the ring structures below are transferred from
-- `Localization.Away` along it.
@[expose]
def RadiusLocalization (_hv : v.Integers O) (_hϖ : ϖ ≠ 0) (_hϖ' : v (algebraMap O K ϖ) < 1)
    (_hρ : ρ ∈ Set.Ioo 0 1) : Type _ :=
  Localization.Away (teichmuller p ϖ)

namespace RadiusLocalization

noncomputable instance : CommRing (RadiusLocalization p hv hϖ hϖ' hρ) :=
  inferInstanceAs (CommRing (Localization.Away _))

noncomputable instance : Algebra (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) :=
  inferInstanceAs (Algebra (𝕎 O) (Localization.Away _))

instance : IsLocalization.Away (teichmuller p ϖ) (RadiusLocalization p hv hϖ hϖ' hρ) :=
  inferInstanceAs (IsLocalization.Away (teichmuller p ϖ) (Localization.Away (teichmuller p ϖ)))

/-- `[ϖ]` is a unit of `𝕎 O[1/[ϖ]]`. -/
theorem isUnit_algebraMap_teichmuller :
    IsUnit (algebraMap (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) (teichmuller p ϖ)) :=
  IsLocalization.Away.algebraMap_isUnit _

end RadiusLocalization

variable [CharP O p] [PerfectRing O p]

include hϖ in
/-- For `ϖ ≠ 0`, the Gauss valuation `λ_ρ` does not vanish at `[ϖ]`. -/
private theorem gaussValuation_teichmuller_ne_zero :
    gaussValuation p hv ρ hρ.2 (teichmuller p ϖ) ≠ 0 := by
  simpa [map_eq_zero_iff _ hv.hom_inj] using hϖ

/-- The extension of the Gauss valuation `λ_ρ` to `𝕎 O[1/[ϖ]]`, which exists because `λ_ρ` does
not vanish at `[ϖ]`. -/
private noncomputable def radiusValuation : Valuation (RadiusLocalization p hv hϖ hϖ' hρ) ℝ≥0 :=
  (gaussValuation p hv ρ hρ.2).extendToLocalization
    (Valuation.powers_le_supp_primeCompl (gaussValuation_teichmuller_ne_zero p hv hϖ hρ))
    (RadiusLocalization p hv hϖ hϖ' hρ)

private theorem radiusValuation_algebraMap (x : 𝕎 O) :
    radiusValuation p hv hϖ hϖ' hρ (algebraMap (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) x) =
      gaussValuation p hv ρ hρ.2 x := by
  rw [radiusValuation]
  exact Valuation.extendToLocalization_apply_map_apply _ _ _ x

private theorem radiusValuation_eq_zero_iff {x : RadiusLocalization p hv hϖ hϖ' hρ} :
    radiusValuation p hv hϖ hϖ' hρ x = 0 ↔ x = 0 := by
  rw [radiusValuation]
  exact Valuation.extendToLocalization_eq_zero_iff _ _ fun _ ↦
    (gaussValuation_eq_zero_iff hv hρ.1 hρ.2).mp

/-- **The Gauss norm on `𝕎 O[1/[ϖ]]`**: the extension of the Gauss valuation `λ_ρ` to the
localisation, an absolute value because `λ_ρ` is a valuation vanishing only at `0`. -/
noncomputable def radiusNorm : AbsoluteValue (RadiusLocalization p hv hϖ hϖ' hρ) ℝ where
  toFun x := radiusValuation p hv hϖ hϖ' hρ x
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by rw [NNReal.coe_eq_zero, radiusValuation_eq_zero_iff]
  add_le' x y := by
    exact_mod_cast (Valuation.map_add _ x y).trans (max_le_add_of_nonneg zero_le zero_le)

private theorem radiusNorm_apply (x : RadiusLocalization p hv hϖ hϖ' hρ) :
    radiusNorm p hv hϖ hϖ' hρ x = radiusValuation p hv hϖ hϖ' hρ x :=
  rfl

/-- The Gauss norm on `𝕎 O[1/[ϖ]]` extends `λ_ρ`. -/
@[simp]
theorem radiusNorm_algebraMap (x : 𝕎 O) :
    radiusNorm p hv hϖ hϖ' hρ (algebraMap (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) x) =
      gaussValuation p hv ρ hρ.2 x := by
  rw [radiusNorm_apply, radiusValuation_algebraMap]

/-- The Gauss norm of a fraction `x / s` in `𝕎 O[1/[ϖ]]` is `λ_ρ(x) / λ_ρ(s)`. -/
@[simp]
theorem radiusNorm_mk' (x : 𝕎 O) (s : Submonoid.powers (teichmuller p ϖ)) :
    radiusNorm p hv hϖ hϖ' hρ (IsLocalization.mk' (RadiusLocalization p hv hϖ hϖ' hρ) x s) =
      gaussValuation p hv ρ hρ.2 x * (gaussValuation p hv ρ hρ.2 s : ℝ)⁻¹ := by
  rw [radiusNorm_apply, radiusValuation, Valuation.extendToLocalization_mk', NNReal.coe_mul,
    NNReal.coe_inv]

/-- The Gauss norm on `𝕎 O[1/[ϖ]]` is nonarchimedean. -/
theorem isNonarchimedean_radiusNorm : IsNonarchimedean (radiusNorm p hv hϖ hϖ' hρ) := fun x y ↦ by
  simp only [radiusNorm_apply, ← NNReal.coe_max, NNReal.coe_le_coe]
  exact Valuation.map_add _ x y

namespace RadiusLocalization

noncomputable instance : NormedCommRing (RadiusLocalization p hv hϖ hϖ' hρ) where
  __ := (radiusNorm p hv hϖ hϖ' hρ).toNormedRing
  mul_comm := mul_comm

/-- The norm of `𝕎 O[1/[ϖ]]` is the extension of the Gauss valuation `λ_ρ`. -/
theorem norm_def (x : RadiusLocalization p hv hϖ hϖ' hρ) : ‖x‖ = radiusNorm p hv hϖ hϖ' hρ x :=
  rfl

/-- On `𝕎 O`, the norm of `𝕎 O[1/[ϖ]]` is the Gauss valuation `λ_ρ`. -/
@[simp]
theorem norm_algebraMap (x : 𝕎 O) :
    ‖algebraMap (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) x‖ = gaussValuation p hv ρ hρ.2 x := by
  rw [norm_def, radiusNorm_algebraMap]

/-- The norm of a fraction `x / s` in `𝕎 O[1/[ϖ]]` is `λ_ρ(x) / λ_ρ(s)`. -/
@[simp]
theorem norm_mk' (x : 𝕎 O) (s : Submonoid.powers (teichmuller p ϖ)) :
    ‖IsLocalization.mk' (RadiusLocalization p hv hϖ hϖ' hρ) x s‖ =
      gaussValuation p hv ρ hρ.2 x * (gaussValuation p hv ρ hρ.2 s : ℝ)⁻¹ := by
  rw [norm_def, radiusNorm_mk']

instance : NormMulClass (RadiusLocalization p hv hϖ hϖ' hρ) :=
  ⟨fun x y ↦ by simp only [norm_def, map_mul]⟩

instance : IsUltrametricDist (RadiusLocalization p hv hϖ hϖ' hρ) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [norm_def] using isNonarchimedean_radiusNorm p hv hϖ hϖ' hρ x y

instance : NormOneClass (RadiusLocalization p hv hϖ hϖ' hρ) :=
  ⟨by rw [← map_one (algebraMap (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ)), norm_algebraMap,
    map_one, NNReal.coe_one]⟩

/-- **`𝕎 O[1/[ϖ]]` with the Gauss norm is a Tate ring**, with pseudouniformiser `[ϖ]`, a unit of
norm `v(ϖ) < 1`. -/
instance instIsTateRing : IsTateRing (RadiusLocalization p hv hϖ hϖ' hρ) :=
  IsTateRing.of_isUnit_norm_lt_one (isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ)
    (by rw [norm_algebraMap, gaussValuation_teichmuller]; exact_mod_cast hϖ')

/-- Scalar multiplication by `𝕎 O` is uniformly continuous, so that the `𝕎 O`-algebra structure
extends to the completion `A^r`. -/
instance : UniformContinuousConstSMul (𝕎 O) (RadiusLocalization p hv hϖ hϖ' hρ) :=
  ⟨fun c ↦ by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _⟩

end RadiusLocalization

/-- **The radius ring `A^r`**: the completion of `𝕎 O[1/[ϖ]]` for the Gauss norm `λ_ρ`, for a
radius `ρ ∈ (0, 1)` and a pseudouniformiser `ϖ` (`0 < v(ϖ) < 1`). It is a complete Hausdorff
normed commutative ring with a multiplicative ultrametric norm, and a Tate ring. -/
abbrev RadiusRing : Type _ :=
  Completion (RadiusLocalization p hv hϖ hϖ' hρ)

/-- On `𝕎 O`, the norm of `A^r` is the Gauss valuation `λ_ρ`. -/
@[simp]
theorem norm_algebraMap_radiusRing (x : 𝕎 O) :
    ‖algebraMap (𝕎 O) (RadiusRing p hv hϖ hϖ' hρ) x‖ = gaussValuation p hv ρ hρ.2 x := by
  rw [Completion.algebraMap_def, Completion.norm_coe, RadiusLocalization.norm_algebraMap]

/-- The norm of `p` in `A^r` is `ρ`. -/
@[simp]
theorem norm_natCast_radiusRing : ‖(p : RadiusRing p hv hϖ hϖ' hρ)‖ = ρ := by
  rw [← map_natCast (algebraMap (𝕎 O) (RadiusRing p hv hϖ hϖ' hρ)), norm_algebraMap_radiusRing,
    gaussValuation_p]

/-! `A^r` is a complete Hausdorff Tate ring with a multiplicative ultrametric norm: completeness
and separatedness hold for every completion, multiplicativity and the ultrametric inequality pass
to the completion by continuity, and the Tate structure of `𝕎 O[1/[ϖ]]` is carried to the
completion by `TauCeti.Huber.IsTateRing.completion` (Wedhorn, Remark 6.8). -/

example : CompleteSpace (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

example : T2Space (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

example : NormMulClass (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

example : IsUltrametricDist (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

example : IsTateRing (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

namespace RadiusRing

/-! ### The degree -/

local notation "ι" => algebraMap (𝕎 O) (RadiusRing p hv hϖ hϖ' hρ)

/-- The powers of `[ϖ]` have positive norm in `A^r`. -/
private theorem norm_teichmuller_pow_pos (k : ℕ) : 0 < ‖ι (teichmuller p ϖ ^ k)‖ := by
  have := hv.isDomain
  rw [norm_algebraMap_radiusRing, NNReal.coe_pos, pos_iff_ne_zero, ← map_pow,
    gaussValuation_teichmuller, map_ne_zero, map_ne_zero_iff _ hv.hom_inj]
  exact pow_ne_zero k hϖ

/-- Multiplying a nonzero element of `A^r` by a power of `[ϖ]` keeps its norm positive. -/
private theorem norm_teichmuller_pow_mul_pos (k : ℕ) {a : RadiusRing p hv hϖ hϖ' hρ}
    (ha : a ≠ 0) : 0 < ‖ι (teichmuller p ϖ ^ k) * a‖ := by
  rw [norm_mul]
  exact mul_pos (norm_teichmuller_pow_pos p hv hϖ hϖ' hρ k) (norm_pos_iff.mpr ha)

/-- Multiplying by a power of `[ϖ]` preserves a strict inequality of norms in `A^r`. -/
private theorem norm_teichmuller_pow_mul_lt (k : ℕ) {a b : RadiusRing p hv hϖ hϖ' hρ}
    (h : ‖a‖ < ‖b‖) : ‖ι (teichmuller p ϖ ^ k) * a‖ < ‖ι (teichmuller p ϖ ^ k) * b‖ := by
  rw [norm_mul, norm_mul]
  exact mul_lt_mul_of_pos_left h (norm_teichmuller_pow_pos p hv hϖ hϖ' hρ k)

/-- Every nonzero `x ∈ A^r` is approximated by some `[ϖ]^(-k) y` with `y ∈ 𝕎 O`, up to an error
smaller than `‖x‖`: elements of `𝕎 O[1/[ϖ]]` are dense in `A^r`. Such an approximation computes
the degree of `x` (`TauCeti.WittVector.RadiusRing.degree_eq_gaussDegree`). -/
theorem exists_norm_teichmuller_pow_mul_sub_lt {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0) :
    ∃ (k : ℕ) (y : 𝕎 O),
      ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖ := by
  obtain ⟨z, hz⟩ := Completion.denseRange_coe.exists_dist_lt x (norm_pos_iff.mpr hx)
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (teichmuller p ϖ)) z
  obtain ⟨k, hk : teichmuller p ϖ ^ k = s⟩ := s.2
  refine ⟨k, y, ?_⟩
  have hy : ι (teichmuller p ϖ ^ k) * (IsLocalization.mk' (RadiusLocalization p hv hϖ hϖ' hρ) y s :
      RadiusRing p hv hϖ hϖ' hρ) = ι y := by
    rw [hk, Completion.algebraMap_def, Completion.algebraMap_def, ← Completion.coe_mul,
      mul_comm (algebraMap _ _ _), IsLocalization.mk'_spec]
  rw [← hy, ← mul_sub]
  exact norm_teichmuller_pow_mul_lt p hv hϖ hϖ' hρ k (by rwa [← dist_eq_norm])

/-- A Witt vector approximating `x ∈ A^r`, as in `exists_norm_teichmuller_pow_mul_sub_lt`, is
nonzero. -/
private theorem ne_zero_of_norm_sub_lt {x : RadiusRing p hv hϖ hϖ' hρ} {k : ℕ} {y : 𝕎 O}
    (h : ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖) : y ≠ 0 := by
  rintro rfl
  simp at h

/-- Two approximations of `x ∈ A^r` by Witt vectors, as in
`exists_norm_teichmuller_pow_mul_sub_lt`, have the same degree. -/
private theorem gaussDegree_eq_of_approx {x : RadiusRing p hv hϖ hϖ' hρ} {k l : ℕ} {y z : 𝕎 O}
    (hy : ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖)
    (hz : ‖ι (teichmuller p ϖ ^ l) * x - ι z‖ < ‖ι (teichmuller p ϖ ^ l) * x‖) :
    gaussDegree p hv ρ hρ.2 y = gaussDegree p hv ρ hρ.2 z := by
  -- Multiply both approximations to the common power `[ϖ] ^ (k + l)`.
  set X := ι (teichmuller p ϖ ^ (k + l)) * x
  have hX (m n : ℕ) (hmn : m + n = k + l) :
      X = ι (teichmuller p ϖ ^ n) * (ι (teichmuller p ϖ ^ m) * x) := by
    simp only [X, ← hmn, pow_add, map_mul]
    ring
  have hy' : ‖X - ι (teichmuller p ϖ ^ l * y)‖ < ‖X‖ := by
    rw [hX k l rfl, map_mul, ← mul_sub]
    exact norm_teichmuller_pow_mul_lt p hv hϖ hϖ' hρ l hy
  have hz' : ‖X - ι (teichmuller p ϖ ^ k * z)‖ < ‖X‖ := by
    rw [hX l k (add_comm l k), map_mul, ← mul_sub]
    exact norm_teichmuller_pow_mul_lt p hv hϖ hϖ' hρ k hz
  -- The two Witt vectors are closer to each other than their common Gauss valuation.
  have hlt : gaussValuation p hv ρ hρ.2 (teichmuller p ϖ ^ l * y - teichmuller p ϖ ^ k * z) <
      gaussValuation p hv ρ hρ.2 (teichmuller p ϖ ^ l * y) := by
    rw [← NNReal.coe_lt_coe, ← norm_algebraMap_radiusRing p hv hϖ hϖ' hρ,
      ← norm_algebraMap_radiusRing p hv hϖ hϖ' hρ,
      ← IsUltrametricDist.norm_eq_of_norm_sub_lt_left hy', map_sub]
    calc ‖ι (teichmuller p ϖ ^ l * y) - ι (teichmuller p ϖ ^ k * z)‖
        = ‖(X - ι (teichmuller p ϖ ^ k * z)) - (X - ι (teichmuller p ϖ ^ l * y))‖ := by
          rw [sub_sub_sub_cancel_left]
      _ ≤ max ‖X - ι (teichmuller p ϖ ^ k * z)‖ ‖X - ι (teichmuller p ϖ ^ l * y)‖ :=
          IsUltrametricDist.norm_sub_le_max _ _
      _ < ‖X‖ := max_lt hz' hy'
  have h := gaussDegree_eq_of_gaussValuation_sub_lt hv hρ.1 hρ.2 hlt
  have := hv.isDomain
  rwa [← map_pow, ← map_pow, gaussDegree_teichmuller_mul hv hρ.1 hρ.2 (pow_ne_zero k hϖ),
    gaussDegree_teichmuller_mul hv hρ.1 hρ.2 (pow_ne_zero l hϖ), eq_comm] at h

open Classical in
/-- **Kedlaya's degree on `A^r`.** For `x ≠ 0` it is the degree
(`TauCeti.WittVector.gaussDegree`) of any `y ∈ 𝕎 O` with `‖[ϖ]^k x - y‖ < ‖[ϖ]^k x‖` for some
`k`, that is, of any approximation `[ϖ]^(-k) y` of `x` with an error smaller than `‖x‖`
(`TauCeti.WittVector.RadiusRing.degree_eq_gaussDegree`). It is `0` for `x = 0`. -/
noncomputable def degree (x : RadiusRing p hv hϖ hϖ' hρ) : ℕ :=
  if h : ∃ (k : ℕ) (y : 𝕎 O),
      ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖
  then gaussDegree p hv ρ hρ.2 h.choose_spec.choose else 0

/-- **The degree of `x ∈ A^r` is the degree of any approximation of `x` by a Witt vector**: if
`‖[ϖ]^k x - y‖ < ‖[ϖ]^k x‖` with `y ∈ 𝕎 O`, then the degree of `x` is the degree of `y` for
`λ_ρ`. -/
theorem degree_eq_gaussDegree {x : RadiusRing p hv hϖ hϖ' hρ} {k : ℕ} {y : 𝕎 O}
    (h : ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖) :
    degree p hv hϖ hϖ' hρ x = gaussDegree p hv ρ hρ.2 y := by
  have hex : ∃ (k : ℕ) (y : 𝕎 O),
      ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖ := ⟨k, y, h⟩
  simp only [degree, hex, ↓reduceDIte]
  exact gaussDegree_eq_of_approx p hv hϖ hϖ' hρ hex.choose_spec.choose_spec h

/-- The degree of `0` is `0`. -/
@[simp]
theorem degree_zero : degree p hv hϖ hϖ' hρ 0 = 0 := by
  simp [degree]

/-- On a Witt vector, the degree of `A^r` is its degree for the Gauss valuation `λ_ρ`. -/
@[simp]
theorem degree_algebraMap (y : 𝕎 O) :
    degree p hv hϖ hϖ' hρ (ι y) = gaussDegree p hv ρ hρ.2 y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero, degree_zero, gaussDegree_zero]
  refine degree_eq_gaussDegree p hv hϖ hϖ' hρ (k := 0) ?_
  rw [pow_zero, map_one, one_mul, sub_self, norm_zero, norm_algebraMap_radiusRing, NNReal.coe_pos,
    pos_iff_ne_zero, ne_eq, gaussValuation_eq_zero_iff hv hρ.1 hρ.2]
  exact hy

/-- The degree of `p` is `1`. -/
@[simp]
theorem degree_natCast : degree p hv hϖ hϖ' hρ (p : RadiusRing p hv hϖ hϖ' hρ) = 1 := by
  have := hv.isDomain
  have h := gaussDegree_teichmuller_mul_pow (p := p) hv hρ.1 hρ.2 one_ne_zero 1
  rw [map_one, one_mul, pow_one] at h
  rw [← map_natCast ι, degree_algebraMap, h]

/-- **The degree only depends on the leading part** (Kedlaya, Remark 2.7): if `‖x - y‖ < ‖x‖`,
then `x` and `y` have the same degree. -/
theorem degree_eq_of_norm_sub_lt {x y : RadiusRing p hv hϖ hϖ' hρ} (h : ‖x - y‖ < ‖x‖) :
    degree p hv hϖ hϖ' hρ y = degree p hv hϖ hϖ' hρ x := by
  have hxy := IsUltrametricDist.norm_eq_of_norm_sub_lt_left h
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨k, z, hz⟩ := exists_norm_teichmuller_pow_mul_sub_lt p hv hϖ hϖ' hρ hy
  -- An approximation of `y` is also one of `x`.
  have hx : ‖ι (teichmuller p ϖ ^ k) * x - ι z‖ < ‖ι (teichmuller p ϖ ^ k) * x‖ := by
    have hnorm : ‖ι (teichmuller p ϖ ^ k) * y‖ = ‖ι (teichmuller p ϖ ^ k) * x‖ := by
      rw [norm_mul, norm_mul, hxy]
    have e : ι (teichmuller p ϖ ^ k) * x - ι z =
        ι (teichmuller p ϖ ^ k) * (x - y) + (ι (teichmuller p ϖ ^ k) * y - ι z) := by
      ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (norm_teichmuller_pow_mul_lt p hv hϖ hϖ' hρ k h) (hnorm ▸ hz))
  rw [degree_eq_gaussDegree p hv hϖ hϖ' hρ hz, degree_eq_gaussDegree p hv hϖ hϖ' hρ hx]

/-- **The degree is additive on products** (Kedlaya, Lemma 2.6). -/
theorem degree_mul {x y : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0) (hy : y ≠ 0) :
    degree p hv hϖ hϖ' hρ (x * y) = degree p hv hϖ hϖ' hρ x + degree p hv hϖ hϖ' hρ y := by
  obtain ⟨k, z, hz⟩ := exists_norm_teichmuller_pow_mul_sub_lt p hv hϖ hϖ' hρ hx
  obtain ⟨l, w, hw⟩ := exists_norm_teichmuller_pow_mul_sub_lt p hv hϖ hϖ' hρ hy
  set X := ι (teichmuller p ϖ ^ k) * x
  set Y := ι (teichmuller p ϖ ^ l) * y
  have hX : 0 < ‖X‖ := norm_teichmuller_pow_mul_pos p hv hϖ hϖ' hρ k hx
  have hY : 0 < ‖Y‖ := norm_teichmuller_pow_mul_pos p hv hϖ hϖ' hρ l hy
  have hw' : ‖ι w‖ = ‖Y‖ := (IsUltrametricDist.norm_eq_of_norm_sub_lt_left hw).symm
  -- The product of the two approximations approximates the product.
  have hXY : ι (teichmuller p ϖ ^ (k + l)) * (x * y) = X * Y := by
    simp only [X, Y, pow_add, map_mul]
    ring
  have hzw : ‖ι (teichmuller p ϖ ^ (k + l)) * (x * y) - ι (z * w)‖ <
      ‖ι (teichmuller p ϖ ^ (k + l)) * (x * y)‖ := by
    have e : X * Y - ι (z * w) = X * (Y - ι w) + (X - ι z) * ι w := by
      rw [map_mul]
      ring
    rw [hXY, e, norm_mul X Y]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_mul_of_pos_left hw hX
    · rw [norm_mul, hw']
      exact mul_lt_mul_of_pos_right hz hY
  rw [degree_eq_gaussDegree p hv hϖ hϖ' hρ hzw, degree_eq_gaussDegree p hv hϖ hϖ' hρ hz,
    degree_eq_gaussDegree p hv hϖ hϖ' hρ hw,
    gaussDegree_mul hv hρ.1 hρ.2 (ne_zero_of_norm_sub_lt p hv hϖ hϖ' hρ hz)
      (ne_zero_of_norm_sub_lt p hv hϖ hϖ' hρ hw)]

end RadiusRing

end TauCeti.WittVector
