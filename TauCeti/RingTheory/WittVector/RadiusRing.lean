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
import TauCeti.Analysis.Normed.Ring.Approximation
import TauCeti.RingTheory.Valuation.Sum

/-!
# The radius rings `A^r`, their degree, and Euclidean division

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
Lemma 2.6).

`A^r` admits Euclidean division for this degree (Kedlaya, Proposition 2.9): for `x ≠ 0`, every
`y` is `z x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or `deg w < deg x`. Consequently the rings
`A^r{T₁/ρ₁, …, Tₙ/ρₙ}` of restricted power series are noetherian (Kedlaya, Theorem 3.2,
`TauCeti.WittVector.RadiusRing.isNoetherianRing_isRestricted_subring` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.RadiusRing`). This is the input for the strong
noetherianity of the interval rings `B^I` (`TauCeti.WittVector.IntervalRing`, Kedlaya's
Theorem 4.10).

## Euclidean division

Let `x ≠ 0` have degree `m`. Up to a power of `[ϖ]`, `x` is close to a Teichmüller sum
`∑_{l ≤ m} [tₗ] pˡ` whose weighted coefficients `v(tₗ) ρˡ` are at most `v(t_m) ρᵐ`, and the
error is bounded by `ε v(t_m) ρᵐ` for some `ε < 1` with `ρ ≤ ε`. Given `y` close to a Teichmüller
sum `∑_{l ≤ n} [aₗ] pˡ` with `n ≥ m`, multiplying by the unit `[t_m]` and
subtracting `[a_n] p^(n - m) x` cancels the term of index `n`. Witt vector addition only carries
into higher indices, and its carries are smaller by the factor `ρ ≤ ε`
(`TauCeti.WittVector.gaussValuation_teichmuller_add_teichmuller_sub_le`), so the result is again
close to a Teichmüller sum, now of length `n`. Descending to length `m` gives Kedlaya's Lemma 2.8:
a remainder of norm at most `‖y‖` that either has degree less than `m` or is smaller than
`ε ‖y‖`. Iterating on the remainders (`TauCeti.subset_idealSpan_of_approx`) gives Proposition 2.9.

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
* `TauCeti.WittVector.RadiusRing.exists_eq_mul_add` : Euclidean division in `A^r`.
* `TauCeti.WittVector.RadiusRing.isUnit_iff_ne_zero_and_degree_eq_zero` : the units of `A^r` are
  its nonzero elements of degree `0`.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Definitions 2.2, 2.4 and 2.5, Lemmas 2.6 and 2.8, Remark 2.7,
  Proposition 2.9 and Theorem 3.2.
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

/-- On `𝕎 O`, the norm of `A^r` is the Gauss valuation `λ_ρ`, as a nonnegative real. -/
@[simp]
theorem nnnorm_algebraMap_radiusRing (x : 𝕎 O) :
    ‖algebraMap (𝕎 O) (RadiusRing p hv hϖ hϖ' hρ) x‖₊ = gaussValuation p hv ρ hρ.2 x :=
  NNReal.eq (norm_algebraMap_radiusRing p hv hϖ hϖ' hρ x)

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

example : NormOneClass (RadiusRing p hv hϖ hϖ' hρ) := inferInstance

/-- `A^r` is nontrivial, as `‖1‖ = 1`. -/
instance : Nontrivial (RadiusRing p hv hϖ hϖ' hρ) := NormOneClass.nontrivial

namespace RadiusRing

/-! ### The degree -/

local notation "ι" => algebraMap (𝕎 O) (RadiusRing p hv hϖ hϖ' hρ)

/-- The Teichmüller representative `[b]` of a nonzero `b ∈ O` is a unit of `A^r`: it divides a
power of `[ϖ]`. -/
theorem isUnit_algebraMap_teichmuller {b : O} (hb : b ≠ 0) : IsUnit (ι (teichmuller p b)) := by
  have hb' : 0 < v (algebraMap O K b) :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr ((map_ne_zero_iff _ hv.hom_inj).mpr hb))
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hb' hϖ'
  obtain ⟨d, hd⟩ := hv.dvd_of_le (x := ϖ ^ N) (y := b) (by rw [map_pow, map_pow]; exact hN.le)
  have hu : IsUnit (ι (teichmuller p ϖ)) := by
    rw [Completion.algebraMap_def]
    exact (RadiusLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ).map
      Completion.coeRingHom
  refine isUnit_of_mul_isUnit_left (y := ι (teichmuller p d)) ?_
  rw [← map_mul, ← map_mul, ← hd, map_pow, map_pow]
  exact hu.pow N

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

/-- Every nonzero `x ∈ A^r` is approximated by some `[ϖ]^(-k) y` with `y ∈ 𝕎 O` up to an
arbitrarily small relative error `ε`: elements of `𝕎 O[1/[ϖ]]` are dense in `A^r`. -/
theorem exists_norm_teichmuller_pow_mul_sub_lt_mul {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (y : 𝕎 O),
      ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ε * ‖ι (teichmuller p ϖ ^ k) * x‖ := by
  obtain ⟨z, hz⟩ := Completion.denseRange_coe.exists_dist_lt x (mul_pos hε (norm_pos_iff.mpr hx))
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (teichmuller p ϖ)) z
  obtain ⟨k, hk : teichmuller p ϖ ^ k = s⟩ := s.2
  refine ⟨k, y, ?_⟩
  have hy : ι (teichmuller p ϖ ^ k) * (IsLocalization.mk' (RadiusLocalization p hv hϖ hϖ' hρ) y s :
      RadiusRing p hv hϖ hϖ' hρ) = ι y := by
    rw [hk, Completion.algebraMap_def, Completion.algebraMap_def, ← Completion.coe_mul,
      mul_comm (algebraMap _ _ _), IsLocalization.mk'_spec]
  rw [← hy, ← mul_sub, norm_mul, norm_mul, mul_left_comm]
  exact mul_lt_mul_of_pos_left (by rwa [← dist_eq_norm])
    (norm_teichmuller_pow_pos p hv hϖ hϖ' hρ k)

/-- Every nonzero `x ∈ A^r` is approximated by some `[ϖ]^(-k) y` with `y ∈ 𝕎 O`, up to an error
smaller than `‖x‖`. Such an approximation computes the degree of `x`
(`TauCeti.WittVector.RadiusRing.degree_eq_gaussDegree`). -/
theorem exists_norm_teichmuller_pow_mul_sub_lt {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0) :
    ∃ (k : ℕ) (y : 𝕎 O),
      ‖ι (teichmuller p ϖ ^ k) * x - ι y‖ < ‖ι (teichmuller p ϖ ^ k) * x‖ := by
  simpa using exists_norm_teichmuller_pow_mul_sub_lt_mul p hv hϖ hϖ' hρ hx one_pos

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

/-- The degree of `1` is `0`. -/
@[simp]
theorem degree_one : degree p hv hϖ hϖ' hρ 1 = 0 := by
  have := hv.isDomain
  have h := gaussDegree_teichmuller_mul_pow (p := p) hv hρ.1 hρ.2 one_ne_zero 0
  rw [map_one, pow_zero, one_mul] at h
  rw [← map_one ι, degree_algebraMap, h]

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

/-- Units of `A^r` have degree `0`. -/
theorem degree_eq_zero_of_isUnit {x : RadiusRing p hv hϖ hϖ' hρ} (hx : IsUnit x) :
    degree p hv hϖ hϖ' hρ x = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h := degree_mul p hv hϖ hϖ' hρ hx.ne_zero (right_ne_zero_of_mul_eq_one hy)
  rw [hy, degree_one] at h
  omega

/-! ### Euclidean division -/

/-- The finite Teichmüller sum `∑_{l < n} [aₗ] pˡ`. -/
private noncomputable def teichSum (a : ℕ → O) (n : ℕ) : 𝕎 O :=
  ∑ l ∈ Finset.range n, teichmuller p (a l) * (p : 𝕎 O) ^ l

variable {p hv} in
/-- A finite Teichmüller sum whose weighted coefficients are at most `B` has Gauss valuation at
most `B`. -/
private theorem gaussValuation_teichSum_le (hρ : ρ < 1) {a : ℕ → O} {n : ℕ} {B : ℝ≥0}
    (h : ∀ l, v (algebraMap O K (a l)) * ρ ^ l ≤ B) :
    gaussValuation p hv ρ hρ (teichSum p a n) ≤ B := by
  rw [teichSum]
  exact Valuation.map_sum_le _ fun l _ ↦
    (gaussValuation_teichmuller_mul_pow hv hρ _ _).trans_le (h l)

variable {p hv} in
/-- **Carries of a difference of Teichmüller sums.** If the weighted coefficients of `a` and `b`
are at most `B`, then `∑_{l < n} ([aₗ] - [bₗ]) pˡ` differs from the Teichmüller sum
`∑_{l < n} [aₗ - bₗ] pˡ` by at most `ρ B`. -/
private theorem gaussValuation_sum_sub_teichSum_le (hρ : ρ < 1) {a b : ℕ → O} {n : ℕ}
    {B : ℝ≥0} (ha : ∀ l, v (algebraMap O K (a l)) * ρ ^ l ≤ B)
    (hb : ∀ l, v (algebraMap O K (b l)) * ρ ^ l ≤ B) :
    gaussValuation p hv ρ hρ (∑ l ∈ Finset.range n,
      (teichmuller p (a l) - teichmuller p (b l)) * (p : 𝕎 O) ^ l -
        teichSum p (fun l ↦ a l - b l) n) ≤ ρ * B := by
  rw [teichSum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_le _ fun l _ ↦ ?_
  -- `[a] - [b] - [a - b] = -([a - b] + [b] - [(a - b) + b])`.
  have h : (teichmuller p (a l) - teichmuller p (b l)) * (p : 𝕎 O) ^ l -
      teichmuller p (a l - b l) * (p : 𝕎 O) ^ l = -((teichmuller p (a l - b l) +
        teichmuller p (b l) - teichmuller p (a l - b l + b l)) * (p : 𝕎 O) ^ l) := by
    rw [sub_add_cancel]
    ring
  rw [h, Valuation.map_neg, map_mul, map_pow, gaussValuation_p]
  calc gaussValuation p hv ρ hρ (teichmuller p (a l - b l) + teichmuller p (b l) -
          teichmuller p (a l - b l + b l)) * ρ ^ l
      ≤ ρ * max (v (algebraMap O K (a l - b l))) (v (algebraMap O K (b l))) * ρ ^ l :=
        mul_le_mul' (gaussValuation_teichmuller_add_teichmuller_sub_le hv hρ _ _) le_rfl
    _ = ρ * max (v (algebraMap O K (a l - b l)) * ρ ^ l) (v (algebraMap O K (b l)) * ρ ^ l) := by
        rw [mul_assoc, max_mul_of_nonneg _ _ zero_le]
    _ ≤ ρ * B := mul_le_mul' le_rfl
        (max_le ((v.comap (algebraMap O K)).map_sub_mul_le (ha l) (hb l)) (hb l))

omit [CharP O p] [PerfectRing O p] in
/-- The Witt vector identity behind a division step: with `c = t m` and `α = a (m + d)`,
`[c] ∑_{l ≤ m + d} [aₗ] pˡ - [α] pᵈ ∑_{l ≤ m} [tₗ] pˡ = ∑_{l < m + d} ([c aₗ] - [gₗ]) pˡ`, where
`[α] pᵈ ∑_{l < m} [tₗ] pˡ = ∑_{l < m + d} [gₗ] pˡ`: the leading terms `[c α] p^(m + d)` cancel. -/
private theorem teichmuller_mul_teichSum_sub (m d : ℕ) (t a g : ℕ → O)
    (hg : ∀ l, g l = if d ≤ l then a (m + d) * t (l - d) else 0) :
    teichmuller p (t m) * teichSum p a (m + d + 1) -
        teichmuller p (a (m + d)) * (p : 𝕎 O) ^ d * teichSum p t (m + 1) =
      ∑ l ∈ Finset.range (m + d), (teichmuller p (t m * a l) - teichmuller p (g l)) *
        (p : 𝕎 O) ^ l := by
  simp only [hg]
  have hgsum : ∑ l ∈ Finset.range (m + d),
      teichmuller p (if d ≤ l then a (m + d) * t (l - d) else 0) * (p : 𝕎 O) ^ l =
        ∑ l ∈ Finset.range m, teichmuller p (a (m + d)) * (p : 𝕎 O) ^ d *
          (teichmuller p (t l) * (p : 𝕎 O) ^ l) := by
    rw [add_comm m d, Finset.sum_range_add, Finset.sum_eq_zero fun l hl ↦ by
      simp [(Finset.mem_range.mp hl).not_ge], zero_add]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left, map_mul, pow_add]
    ring
  simp only [teichSum, Finset.sum_range_succ, sub_mul, Finset.sum_sub_distrib, hgsum, map_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]
  ring

/-- **One step of Kedlaya's division.** Let `X` be within `ε L` of `∑_{l ≤ m} [tₗ] pˡ`, whose
weighted coefficients are at most `L = v(t_m) ρᵐ`, and let `Y` be within `ε M` of
`∑_{l ≤ m + d} [aₗ] pˡ`, whose weighted coefficients are at most `M`. Subtracting
`[a_{m + d}] pᵈ X` from `[t_m] Y` cancels the term of index `m + d`, so that the result is within
`ε v(t_m) M` of a Teichmüller sum of length `m + d`. The carries of Witt vector addition are
absorbed by `ρ ≤ ε`. -/
private theorem exists_division_step {X Y : RadiusRing p hv hϖ hϖ' hρ} {m d : ℕ} {t a : ℕ → O}
    {ε M : ℝ≥0} (hε : ρ ≤ ε) (hε1 : ε ≤ 1)
    (ht : ∀ l, v (algebraMap O K (t l)) * ρ ^ l ≤ v (algebraMap O K (t m)) * ρ ^ m)
    (hX : ‖X - ι (teichSum p t (m + 1))‖₊ ≤ ε * (v (algebraMap O K (t m)) * ρ ^ m))
    (ha : ∀ l, v (algebraMap O K (a l)) * ρ ^ l ≤ M)
    (hY : ‖Y - ι (teichSum p a (m + d + 1))‖₊ ≤ ε * M) :
    ∃ b : ℕ → O, (∀ l, v (algebraMap O K (b l)) * ρ ^ l ≤ v (algebraMap O K (t m)) * M) ∧
      ‖ι (teichmuller p (a (m + d)) * (p : 𝕎 O) ^ d) * X‖₊ ≤ v (algebraMap O K (t m)) * M ∧
      ‖ι (teichmuller p (t m)) * Y - ι (teichmuller p (a (m + d)) * (p : 𝕎 O) ^ d) * X -
        ι (teichSum p b (m + d))‖₊ ≤ ε * (v (algebraMap O K (t m)) * M) := by
  set c := t m
  set α := a (m + d)
  set w : O → ℝ≥0 := fun x ↦ v (algebraMap O K x)
  set g : ℕ → O := fun l ↦ if d ≤ l then α * t (l - d) else 0
  have hid := congrArg ι (teichmuller_mul_teichSum_sub p m d t a g fun _ ↦ rfl)
  set b : ℕ → O := fun l ↦ c * a l - g l
  have hαM : w α * ρ ^ d * (w c * ρ ^ m) = w c * (w α * ρ ^ (m + d)) := by
    rw [pow_add]
    ring
  have hca (l : ℕ) : w (c * a l) * ρ ^ l ≤ w c * M := by
    simp only [w, map_mul, mul_assoc]
    exact mul_le_mul' le_rfl (ha l)
  have hg (l : ℕ) : w (g l) * ρ ^ l ≤ w c * M := by
    by_cases hl : d ≤ l
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
      calc w (g (d + k)) * ρ ^ (d + k) = w α * ρ ^ d * (w (t k) * ρ ^ k) := by
            simp only [g, w, hl, ↓reduceIte, Nat.add_sub_cancel_left, map_mul, pow_add]
            ring
        _ ≤ w α * ρ ^ d * (w c * ρ ^ m) := mul_le_mul' le_rfl (ht k)
        _ ≤ w c * M := hαM ▸ mul_le_mul' le_rfl (ha _)
    · simp [g, w, hl]
  have hb (l : ℕ) : w (b l) * ρ ^ l ≤ w c * M :=
    (v.comap (algebraMap O K)).map_sub_mul_le (hca l) (hg l)
  have hQ : ‖ι (teichmuller p α * (p : 𝕎 O) ^ d)‖₊ = w α * ρ ^ d := by
    rw [nnnorm_algebraMap_radiusRing, gaussValuation_teichmuller_mul_pow]
  have hT : ‖ι (teichSum p t (m + 1))‖₊ ≤ w c * ρ ^ m := by
    rw [nnnorm_algebraMap_radiusRing]
    exact gaussValuation_teichSum_le hρ.2 ht
  have hXL : ‖X‖₊ ≤ w c * ρ ^ m :=
    calc ‖X‖₊ = ‖(X - ι (teichSum p t (m + 1))) + ι (teichSum p t (m + 1))‖₊ := by
          rw [sub_add_cancel]
      _ ≤ _ := IsUltrametricDist.nnnorm_add_le_max _ _
      _ ≤ w c * ρ ^ m := max_le (hX.trans (mul_le_of_le_one_left' hε1)) hT
  refine ⟨b, hb, ?_, ?_⟩
  · calc ‖ι (teichmuller p α * (p : 𝕎 O) ^ d) * X‖₊ = w α * ρ ^ d * ‖X‖₊ := by
          rw [nnnorm_mul, hQ]
      _ ≤ w α * ρ ^ d * (w c * ρ ^ m) := mul_le_mul' le_rfl hXL
      _ ≤ w c * M := hαM ▸ mul_le_mul' le_rfl (ha _)
  -- The carries `E` of `∑ ([c aₗ] - [gₗ]) pˡ - ∑ [c aₗ - gₗ] pˡ` are at most `ρ v(c) M`.
  set E : 𝕎 O := ∑ l ∈ Finset.range (m + d),
    (teichmuller p (c * a l) - teichmuller p (g l)) * (p : 𝕎 O) ^ l - teichSum p b (m + d)
  have hE : ‖ι E‖₊ ≤ ρ * (w c * M) := by
    rw [nnnorm_algebraMap_radiusRing]
    exact gaussValuation_sum_sub_teichSum_le hρ.2 hca hg
  have hdecomp : ι (teichmuller p c) * Y - ι (teichmuller p α * (p : 𝕎 O) ^ d) * X -
      ι (teichSum p b (m + d)) = ι (teichmuller p c) * (Y - ι (teichSum p a (m + d + 1))) -
        ι (teichmuller p α * (p : 𝕎 O) ^ d) * (X - ι (teichSum p t (m + 1))) + ι E := by
    rw [map_sub, map_mul, map_mul] at hid
    rw [map_sub, ← hid]
    ring
  rw [hdecomp]
  refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.nnnorm_sub_le_max _ _).trans
    (max_le ?_ ?_)) (hE.trans (mul_le_mul' hε le_rfl)))
  · rw [nnnorm_mul, nnnorm_algebraMap_radiusRing, gaussValuation_teichmuller, mul_left_comm]
    exact mul_le_mul' le_rfl hY
  · calc ‖ι (teichmuller p α * (p : 𝕎 O) ^ d) * (X - ι (teichSum p t (m + 1)))‖₊
        ≤ w α * ρ ^ d * (ε * (w c * ρ ^ m)) := by
          rw [nnnorm_mul, hQ]
          exact mul_le_mul' le_rfl hX
      _ = ε * (w α * ρ ^ d * (w c * ρ ^ m)) := by ring
      _ ≤ ε * (w c * M) := mul_le_mul' le_rfl (hαM ▸ mul_le_mul' le_rfl (ha _))

/-- **Iterated division steps.** Under the hypotheses on `X` of `exists_division_step`, if `Y` is
within `ε M` of a Teichmüller sum of length `m + d` whose weighted coefficients are at most `M`,
then for some `b ≠ 0` and `Q` with `‖Q X‖ ≤ v(b) M`, `[b] Y - Q X` is within `ε v(b) M` of a
Teichmüller sum of length `m` whose weighted coefficients are at most `v(b) M`. -/
private theorem exists_division {X : RadiusRing p hv hϖ hϖ' hρ} {m : ℕ} {t : ℕ → O}
    {ε : ℝ≥0} (hε : ρ ≤ ε) (hε1 : ε ≤ 1) (hc : t m ≠ 0)
    (ht : ∀ l, v (algebraMap O K (t l)) * ρ ^ l ≤ v (algebraMap O K (t m)) * ρ ^ m)
    (hX : ‖X - ι (teichSum p t (m + 1))‖₊ ≤ ε * (v (algebraMap O K (t m)) * ρ ^ m)) (d : ℕ)
    (Y : RadiusRing p hv hϖ hϖ' hρ) (M : ℝ≥0) (a : ℕ → O)
    (ha : ∀ l, v (algebraMap O K (a l)) * ρ ^ l ≤ M)
    (hY : ‖Y - ι (teichSum p a (m + d))‖₊ ≤ ε * M) :
    ∃ (b : O) (Q : RadiusRing p hv hϖ hϖ' hρ) (a' : ℕ → O), b ≠ 0 ∧
      ‖Q * X‖₊ ≤ v (algebraMap O K b) * M ∧
      (∀ l, v (algebraMap O K (a' l)) * ρ ^ l ≤ v (algebraMap O K b) * M) ∧
      ‖ι (teichmuller p b) * Y - Q * X - ι (teichSum p a' m)‖₊ ≤
        ε * (v (algebraMap O K b) * M) := by
  have := hv.isDomain
  induction d generalizing Y M a with
  | zero => exact ⟨1, 0, a, one_ne_zero, by simp, by simpa using ha, by simpa using hY⟩
  | succ d ih =>
    obtain ⟨b₁, hb₁, hQ₁, hY₁⟩ := exists_division_step p hv hϖ hϖ' hρ hε hε1 ht hX ha hY
    obtain ⟨b, Q, a', hb, hQ, ha', hY'⟩ := ih _ _ b₁ hb₁ hY₁
    set Q₁ := ι (teichmuller p (a (m + d)) * (p : 𝕎 O) ^ d)
    have hbc : v (algebraMap O K (b * t m)) * M =
        v (algebraMap O K b) * (v (algebraMap O K (t m)) * M) := by
      rw [map_mul, map_mul, mul_assoc]
    refine ⟨b * t m, ι (teichmuller p b) * Q₁ + Q, a', mul_ne_zero hb hc, ?_, hbc ▸ ha', ?_⟩
    · rw [hbc, add_mul, mul_assoc]
      refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le ?_ hQ)
      rw [nnnorm_mul, nnnorm_algebraMap_radiusRing, gaussValuation_teichmuller]
      exact mul_le_mul' le_rfl hQ₁
    · have h : ι (teichmuller p (b * t m)) * Y - (ι (teichmuller p b) * Q₁ + Q) * X -
          ι (teichSum p a' m) = ι (teichmuller p b) * (ι (teichmuller p (t m)) * Y - Q₁ * X) -
            Q * X - ι (teichSum p a' m) := by
        rw [map_mul, map_mul]
        ring
      rw [h, hbc]
      exact hY'

/-- A nonzero `x ∈ A^r` of degree `m`, multiplied by a suitable power of `[ϖ]`, is closer to a
Teichmüller sum `∑_{l ≤ m} [tₗ] pˡ` than `v(t_m) ρᵐ`, which bounds all the weighted coefficients
`v(tₗ) ρˡ` of the sum. -/
private theorem exists_teichSum_degree {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0) :
    ∃ (k : ℕ) (t : ℕ → O), t (degree p hv hϖ hϖ' hρ x) ≠ 0 ∧
      (∀ l, v (algebraMap O K (t l)) * ρ ^ l ≤
        v (algebraMap O K (t (degree p hv hϖ hϖ' hρ x))) * ρ ^ degree p hv hϖ hϖ' hρ x) ∧
      ‖ι (teichmuller p ϖ ^ k) * x - ι (teichSum p t (degree p hv hϖ hϖ' hρ x + 1))‖₊ <
        v (algebraMap O K (t (degree p hv hϖ hϖ' hρ x))) * ρ ^ degree p hv hϖ hϖ' hρ x := by
  obtain ⟨k, y, hy⟩ := exists_norm_teichmuller_pow_mul_sub_lt p hv hϖ hϖ' hρ hx
  set m := degree p hv hϖ hϖ' hρ x
  have hm : m = gaussDegree p hv ρ hρ.2 y := degree_eq_gaussDegree p hv hϖ hϖ' hρ hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  set L := v (algebraMap O K (y.teichmullerCoeff m)) * ρ ^ m
  have hL : gaussValuation p hv ρ hρ.2 y = L := by
    rw [gaussValuation_eq_mul_pow_gaussDegree hv hρ.2 y, ← hm]
  have hL0 : 0 < L := hL ▸ gaussValuation_pos hv hρ.1 hρ.2 hy0
  refine ⟨k, y.teichmullerCoeff, fun h ↦ hL0.ne' (by simp [L, h]),
    fun l ↦ (le_gaussValuation hv hρ.2 y l).trans hL.le, ?_⟩
  have h₁ : ‖ι (teichmuller p ϖ ^ k) * x - ι y‖₊ < L := by
    rw [← hL, ← nnnorm_algebraMap_radiusRing p hv hϖ hϖ' hρ, ← NNReal.coe_lt_coe, coe_nnnorm,
      coe_nnnorm, ← IsUltrametricDist.norm_eq_of_norm_sub_lt_left hy]
    exact hy
  -- The Teichmüller expansion of `y` beyond its degree `m` is smaller than `L`.
  have h₂ : gaussValuation p hv ρ hρ.2 (y - teichSum p y.teichmullerCoeff (m + 1)) < L := by
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hL0 hρ.2
    obtain ⟨w, hw⟩ := pow_dvd_sub_sum_teichmullerCoeff y (m + N)
    rw [← Nat.range_succ_eq_Iic] at hw
    have hsplit : y - teichSum p y.teichmullerCoeff (m + 1) = (p : 𝕎 O) ^ (m + N + 1) * w +
        ∑ l ∈ Finset.Ico (m + 1) (m + N + 1), teichmuller p (y.teichmullerCoeff l) *
          (p : 𝕎 O) ^ l := by
      rw [← hw, teichSum, ← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ m + N + 1)]
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (Valuation.map_sum_lt _ hL0.ne' fun l hl ↦ ?_)
    · rw [map_mul, map_pow, gaussValuation_p]
      calc ρ ^ (m + N + 1) * gaussValuation p hv ρ hρ.2 w ≤ ρ ^ N :=
            (mul_le_of_le_one_right' (gaussValuation_le_one hv hρ.2 w)).trans
              (pow_le_pow_of_le_one zero_le hρ.2.le (by omega))
        _ < L := hN
    · rw [gaussValuation_teichmuller_mul_pow, ← hL]
      exact mul_pow_lt_gaussValuation_of_gaussDegree_lt hv hρ.1 hρ.2 hy0
        (hm ▸ (Finset.mem_Ico.mp hl).1)
  calc ‖ι (teichmuller p ϖ ^ k) * x - ι (teichSum p y.teichmullerCoeff (m + 1))‖₊
      = ‖(ι (teichmuller p ϖ ^ k) * x - ι y) +
          ι (y - teichSum p y.teichmullerCoeff (m + 1))‖₊ := by
        rw [map_sub, sub_add_sub_cancel]
    _ ≤ _ := IsUltrametricDist.nnnorm_add_le_max _ _
    _ < L := max_lt h₁ (by rwa [nnnorm_algebraMap_radiusRing])

/-- Every nonzero `y ∈ A^r`, multiplied by a suitable power of `[ϖ]`, is within `ε` times its norm
of a Teichmüller sum of length at least `n` whose weighted coefficients are at most that norm. -/
private theorem exists_teichSum_approx {y : RadiusRing p hv hϖ hϖ' hρ} (hy : y ≠ 0) {ε : ℝ≥0}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    ∃ (j N : ℕ) (a : ℕ → O),
      (∀ l, v (algebraMap O K (a l)) * ρ ^ l ≤ ‖ι (teichmuller p ϖ ^ j) * y‖₊) ∧
      ‖ι (teichmuller p ϖ ^ j) * y - ι (teichSum p a (n + N))‖₊ ≤
        ε * ‖ι (teichmuller p ϖ ^ j) * y‖₊ := by
  -- Approximate `[ϖ]ʲ y` by a Witt vector `y'`, then truncate the Teichmüller expansion of `y'`.
  obtain ⟨j, y', hy'⟩ := exists_norm_teichmuller_pow_mul_sub_lt_mul p hv hϖ hϖ' hρ hy
    (ε := ε) (by exact_mod_cast hε0)
  set M := ‖ι (teichmuller p ϖ ^ j) * y‖₊
  replace hy' : ‖ι (teichmuller p ϖ ^ j) * y - ι y'‖₊ < ε * M := by
    rwa [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  have hM0 : 0 < M := pos_of_mul_pos_right (lt_of_le_of_lt zero_le hy') zero_le
  have hy'M : gaussValuation p hv ρ hρ.2 y' ≤ M := by
    rw [← nnnorm_algebraMap_radiusRing p hv hϖ hϖ' hρ, ← sub_sub_cancel
      (ι (teichmuller p ϖ ^ j) * y) (ι y')]
    exact (IsUltrametricDist.nnnorm_sub_le_max _ _).trans
      (max_le le_rfl (hy'.le.trans (mul_le_of_le_one_left' hε1)))
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one (mul_pos hε0 hM0) hρ.2
  refine ⟨j, N + 1, y'.teichmullerCoeff, fun l ↦ (le_gaussValuation hv hρ.2 y' l).trans hy'M, ?_⟩
  obtain ⟨w, hw⟩ := pow_dvd_sub_sum_teichmullerCoeff y' (n + N)
  rw [← Nat.range_succ_eq_Iic] at hw
  have hw' : ‖ι (y' - teichSum p y'.teichmullerCoeff (n + (N + 1)))‖₊ ≤ ε * M := by
    rw [teichSum, ← add_assoc, hw, nnnorm_algebraMap_radiusRing, map_mul, map_pow,
      gaussValuation_p]
    exact ((mul_le_of_le_one_right' (gaussValuation_le_one hv hρ.2 w)).trans
      (pow_le_pow_of_le_one zero_le hρ.2.le (by omega))).trans hN.le
  rw [← sub_add_sub_cancel _ (ι y'), ← map_sub]
  exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le hy'.le hw')

/-- **Kedlaya, Lemma 2.8.** For `x ≠ 0` there is `ε < 1` such that every `y ∈ A^r` can be
written `y = z x + w` with `‖w‖ ≤ ‖y‖`, where `w` has smaller degree than `x` unless
`‖w‖ ≤ ε ‖y‖`. -/
private theorem exists_lt_one_forall_exists_eq_mul_add {x : RadiusRing p hv hϖ hϖ' hρ}
    (hx : x ≠ 0) : ∃ ε : ℝ≥0, ε < 1 ∧ ∀ y : RadiusRing p hv hϖ hϖ' hρ, ∃ z w, y = z * x + w ∧
      ‖w‖₊ ≤ ‖y‖₊ ∧ (ε * ‖y‖₊ < ‖w‖₊ → degree p hv hϖ hϖ' hρ w < degree p hv hϖ hϖ' hρ x) := by
  obtain ⟨k, t, hc, ht, hX⟩ := exists_teichSum_degree p hv hϖ hϖ' hρ hx
  set m := degree p hv hϖ hϖ' hρ x
  set L := v (algebraMap O K (t m)) * ρ ^ m
  have hL0 : 0 < L := lt_of_le_of_lt zero_le hX
  -- `ε` absorbs both the carries, `ρ`, and the approximation of `[ϖ]ᵏ x` by a Teichmüller sum.
  set ε := max ρ (‖ι (teichmuller p ϖ ^ k) * x - ι (teichSum p t (m + 1))‖₊ / L)
  have hXε : ‖ι (teichmuller p ϖ ^ k) * x - ι (teichSum p t (m + 1))‖₊ ≤ ε * L := by
    rw [← div_le_iff₀ hL0]
    exact le_max_right _ _
  have hε0 : 0 < ε := hρ.1.trans_le (le_max_left _ _)
  have hε1 : ε < 1 := max_lt hρ.2 ((div_lt_one hL0).mpr hX)
  refine ⟨ε, hε1, fun y ↦ ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, 0, by simp, by simp, by simp⟩
  obtain ⟨j, N, a₀, ha₀, hY⟩ := exists_teichSum_approx p hv hϖ hϖ' hρ hy hε0 hε1.le m
  set M := ‖ι (teichmuller p ϖ ^ j) * y‖₊ with hM
  -- Run the division steps down to a Teichmüller sum of length `m`, and divide by the unit
  -- `e = [b] [ϖ]ʲ`.
  obtain ⟨b, Q, a, hb, hQ, ha, hW⟩ := exists_division p hv hϖ hϖ' hρ (le_max_left _ _) hε1.le hc
    ht hXε N _ M a₀ ha₀ hY
  set e := ι (teichmuller p b) * ι (teichmuller p ϖ ^ j) with he_def
  have he : IsUnit e := (isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ hb).mul (by
    rw [map_pow]
    exact (isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ hϖ).pow j)
  obtain ⟨e', he'⟩ := he.exists_left_inv
  set W := ι (teichmuller p b) * (ι (teichmuller p ϖ ^ j) * y) - Q * (ι (teichmuller p ϖ ^ k) * x)
  have hey : ‖e‖₊ * ‖y‖₊ = v (algebraMap O K b) * M := by
    rw [he_def, hM, nnnorm_mul, nnnorm_mul (ι (teichmuller p ϖ ^ j)), nnnorm_algebraMap_radiusRing,
      gaussValuation_teichmuller, mul_assoc]
  have heW : ‖e‖₊ * ‖e' * W‖₊ = ‖W‖₊ := by
    rw [← nnnorm_mul, ← mul_assoc, mul_comm e e', he', one_mul]
  have he0 : 0 < ‖e‖₊ := nnnorm_pos.mpr he.ne_zero
  have hWM : ‖W‖₊ ≤ v (algebraMap O K b) * M := by
    rw [← sub_add_cancel W (ι (teichSum p a m))]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le
      (hW.trans (mul_le_of_le_one_left' hε1.le)) ?_)
    rw [nnnorm_algebraMap_radiusRing]
    exact gaussValuation_teichSum_le hρ.2 ha
  refine ⟨e' * Q * ι (teichmuller p ϖ ^ k), e' * W, by linear_combination (-y) * he', ?_, ?_⟩
  · exact le_of_mul_le_mul_left (heW ▸ hey ▸ hWM) he0
  · intro hlt
    -- `W` is closer to the Teichmüller sum of length `m` than its norm, so has degree below `m`.
    have hWlt : ‖W - ι (teichSum p a m)‖₊ < ‖W‖₊ := by
      refine hW.trans_lt ?_
      rw [← hey, ← heW, mul_left_comm]
      exact mul_lt_mul_of_pos_left hlt he0
    have hH : teichSum p a m ≠ 0 := by
      rintro h
      rw [h, map_zero, sub_zero] at hWlt
      exact lt_irrefl _ hWlt
    have he'W : e' * W ≠ 0 := by
      rintro h
      rw [h, nnnorm_zero] at hlt
      exact not_lt_zero hlt
    rw [degree_mul p hv hϖ hϖ' hρ (left_ne_zero_of_mul he'W) (right_ne_zero_of_mul he'W),
      degree_eq_zero_of_isUnit p hv hϖ hϖ' hρ (IsUnit.of_mul_eq_one e he'), zero_add,
      ← degree_eq_of_norm_sub_lt p hv hϖ hϖ' hρ (by exact_mod_cast hWlt), degree_algebraMap]
    rw [teichSum] at hH ⊢
    exact gaussDegree_sum_range_teichmuller_mul_pow_lt hv hρ.1 hρ.2 hH

/-- **Euclidean division in `A^r`** (Kedlaya, Proposition 2.9). For `x ≠ 0`, every `y ∈ A^r` can be
written `y = z x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or `w` of smaller degree than `x`. -/
theorem exists_eq_mul_add {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0)
    (y : RadiusRing p hv hϖ hϖ' hρ) : ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧
      (w = 0 ∨ degree p hv hϖ hϖ' hρ w < degree p hv hϖ hϖ' hρ x) := by
  obtain ⟨ε, hε1, hdiv⟩ := exists_lt_one_forall_exists_eq_mul_add p hv hϖ hϖ' hρ hx
  -- The elements admitting no such division are approximated by multiples of `x`, with errors
  -- again admitting no such division, so they are multiples of `x`: there are none.
  set S := {y : RadiusRing p hv hϖ hϖ' hρ | ¬∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧
    (w = 0 ∨ degree p hv hϖ hϖ' hρ w < degree p hv hϖ hϖ' hρ x)}
  have hS : S ⊆ (Ideal.span (({x} : Finset (RadiusRing p hv hϖ hϖ' hρ)) :
      Set (RadiusRing p hv hϖ hϖ' hρ)) : Set (RadiusRing p hv hϖ hϖ' hρ)) := by
    refine TauCeti.subset_idealSpan_of_approx ε.2 hε1 fun y hy ↦ ?_
    obtain ⟨z, w, rfl, hw, hdeg⟩ := hdiv y
    have hw' : ‖w‖ ≤ ‖z * x + w‖ := by exact_mod_cast hw
    have hwS : w ∈ S := fun ⟨z', w', h, hw'', hdeg'⟩ ↦
      hy ⟨z + z', w', by rw [h]; ring, hw''.trans hw', hdeg'⟩
    refine ⟨fun _ ↦ z, fun x' hx' ↦ ?_, by simpa using hwS, ?_⟩
    · rw [Finset.mem_singleton.mp hx', ← norm_mul]
      calc ‖z * x‖ = ‖z * x + w - w‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖z * x + w‖ := (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le le_rfl hw')
    · rw [Finset.sum_singleton, add_sub_cancel_left]
      by_contra! h
      exact hwS ⟨0, w, by simp, le_rfl, Or.inr (hdeg (by exact_mod_cast h))⟩
  by_contra hy
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (by simpa using hS hy)
  exact hy ⟨z, 0, by rw [hz, add_zero], by simp, Or.inl rfl⟩

/-- A nonzero element of `A^r` of degree `0` is a unit: dividing `1` by it leaves no remainder. -/
theorem isUnit_of_degree_eq_zero {x : RadiusRing p hv hϖ hϖ' hρ} (hx : x ≠ 0)
    (hdeg : degree p hv hϖ hϖ' hρ x = 0) : IsUnit x := by
  obtain ⟨z, w, h, -, rfl | hw⟩ := exists_eq_mul_add p hv hϖ hϖ' hρ hx 1
  · exact IsUnit.of_mul_eq_one_right z (by rw [h, add_zero])
  · omega

/-- The units of `A^r` are its nonzero elements of degree `0`. -/
@[simp]
theorem isUnit_iff_ne_zero_and_degree_eq_zero {x : RadiusRing p hv hϖ hϖ' hρ} :
    IsUnit x ↔ x ≠ 0 ∧ degree p hv hϖ hϖ' hρ x = 0 :=
  ⟨fun hx ↦ ⟨hx.ne_zero, degree_eq_zero_of_isUnit p hv hϖ hϖ' hρ hx⟩,
    fun ⟨hx, hdeg⟩ ↦ isUnit_of_degree_eq_zero p hv hϖ hϖ' hρ hx hdeg⟩

end RadiusRing

end TauCeti.WittVector
