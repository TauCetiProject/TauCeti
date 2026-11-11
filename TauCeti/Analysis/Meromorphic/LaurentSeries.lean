/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.Analysis.Analytic.TaylorSeries
public import TauCeti.Analysis.Meromorphic.PrincipalPart

/-!
# The Laurent expansion of a meromorphic germ

Let `𝕜` be a nontrivially normed field and `a : 𝕜`. A meromorphic germ `φ` at `a` is represented as
`(z - a)⁻ᴺ h z` with `h` analytic at `a`; its **Laurent expansion**
`TauCeti.meromorphicGerms.laurentSeries φ` is the formal Laurent series `X⁻ᴺ T`, where `T` is the
Taylor series of `h` at `a` (`TauCeti.taylorSeries`). It does not depend on the representation
(`TauCeti.meromorphicGerms.laurentSeries_eq`).

The Laurent expansion is a homomorphism of `𝕜`-algebras from the field of meromorphic germs to the
field `𝕜⸨X⸩` of formal Laurent series, so it is injective: a meromorphic germ is determined by its
Laurent coefficients. Its multiplicativity is the product formula for Laurent coefficients; since
both factors are bounded below, each coefficient of a product is the finite convolution computed
by multiplication in `𝕜⸨X⸩`. The expansion sends the coordinate `z - a` to `X`, so a polynomial in
`(z - a)⁻¹` goes to the same polynomial in `X⁻¹`. Consequently its negative coefficients are the
coefficients of the principal part `TauCeti.meromorphicGerms.principalPart φ`, and its
nonnegative coefficients are the Taylor coefficients of the regular part.

## Main declarations

* `TauCeti.meromorphicGerms.laurentSeries`: the Laurent expansion, as an algebra homomorphism.
* `TauCeti.meromorphicGerms.laurentSeries_eq`: its value through any representation
  `(z - a)⁻ᴺ h z` with `h` analytic at `a`.
* `TauCeti.meromorphicGerms.laurentSeries_injective`: a meromorphic germ is determined by its
  Laurent expansion.
* `TauCeti.meromorphicGerms.laurentSeries_evalInvSub`: the expansion of a polynomial in
  `(z - a)⁻¹`.
* `TauCeti.meromorphicGerms.coeff_laurentSeries_neg`: the negative coefficients are those of the
  principal part.
* `TauCeti.meromorphicGerms.coeff_laurentSeries_natCast`: the nonnegative coefficients are the
  Taylor coefficients of the regular part.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.3.
-/

public noncomputable section

open Filter Function HahnSeries Polynomial Topology

namespace TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-- Every meromorphic germ at `a` is the germ of `(z - a)⁻ᴺ h z` for some `N` and some `h`
analytic at `a`. -/
private theorem exists_eq_inv_pow_mul (φ : meromorphicGerms 𝕜 a) :
    ∃ N : ℕ, ∃ h : 𝕜 → 𝕜, AnalyticAt 𝕜 h a ∧
      (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜) := by
  obtain ⟨f, ⟨N, hN⟩, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  refine ⟨N, _, hN, hφ.symm.trans (Germ.coe_eq.2 ?_)⟩
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
  rw [smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero N (sub_ne_zero.2 hz))]

/-- The Laurent expansion `X⁻ᴺ T` of `(z - a)⁻ᴺ h z` does not depend on the representation. -/
private theorem single_mul_taylorSeries_eq {N M : ℕ} {h k : 𝕜 → 𝕜} (hh : AnalyticAt 𝕜 h a)
    (hk : AnalyticAt 𝕜 k a)
    (hhk : (fun z ↦ ((z - a) ^ N)⁻¹ * h z) =ᶠ[𝓝[≠] a] fun z ↦ ((z - a) ^ M)⁻¹ * k z) :
    single (-(N : ℤ)) (1 : 𝕜) * ofPowerSeries ℤ 𝕜 (taylorSeries h a) =
      single (-(M : ℤ)) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries k a) := by
  set c : 𝕜 → 𝕜 := fun z ↦ z - a
  have hc : AnalyticAt 𝕜 c a := by fun_prop
  -- Clearing denominators, `(z - a) ^ M * h z = (z - a) ^ N * k z` near `a`, also at `a` itself
  -- by continuity.
  have hNM : c ^ M * h =ᶠ[𝓝[≠] a] c ^ N * k := by
    filter_upwards [hhk, self_mem_nhdsWithin] with z hz (hza : z ≠ a)
    have hz' : z - a ≠ 0 := sub_ne_zero.2 hza
    simp only [Pi.mul_apply, Pi.pow_apply, c]
    field_simp at hz ⊢
    linear_combination hz
  have hNM' : c ^ M * h =ᶠ[𝓝 a] c ^ N * k :=
    ((hc.pow M).mul hh).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hc.pow N).mul hk).continuousAt |>.1 hNM
  have hT := congrArg (ofPowerSeries ℤ 𝕜) (taylorSeries_congr hNM')
  rw [taylorSeries_mul (hc.pow M) hh, taylorSeries_mul (hc.pow N) hk, taylorSeries_pow hc,
    taylorSeries_pow hc, taylorSeries_sub_const, map_mul, map_mul, ofPowerSeries_X_pow,
    ofPowerSeries_X_pow] at hT
  calc single (-(N : ℤ)) (1 : 𝕜) * ofPowerSeries ℤ 𝕜 (taylorSeries h a)
      = single (-(N + M : ℤ)) 1 * (single (M : ℤ) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries h a)) := by
        rw [← mul_assoc, single_mul_single, mul_one, neg_add, neg_add_cancel_right]
    _ = single (-(N + M : ℤ)) 1 * (single (N : ℤ) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries k a)) := by
        rw [hT]
    _ = single (-(M : ℤ)) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries k a) := by
        rw [← mul_assoc, single_mul_single, mul_one, neg_add, add_comm (-(N : ℤ)),
          neg_add_cancel_right]

/-- The Laurent expansion of a meromorphic germ, through a chosen representation. -/
private def laurentSeriesFun (φ : meromorphicGerms 𝕜 a) : LaurentSeries 𝕜 :=
  single (-((exists_eq_inv_pow_mul φ).choose : ℤ)) 1 *
    ofPowerSeries ℤ 𝕜 (taylorSeries (exists_eq_inv_pow_mul φ).choose_spec.choose a)

private theorem laurentSeriesFun_eq {φ : meromorphicGerms 𝕜 a} {N : ℕ} {h : 𝕜 → 𝕜}
    (hh : AnalyticAt 𝕜 h a)
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜)) :
    laurentSeriesFun φ = single (-(N : ℤ)) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries h a) := by
  obtain ⟨hh', hφ'⟩ := (exists_eq_inv_pow_mul φ).choose_spec.choose_spec
  exact single_mul_taylorSeries_eq hh' hh (Germ.coe_eq.1 (hφ'.symm.trans hφ))

/-- A representation `(z - a)⁻ᴺ h z` of a meromorphic germ can be raised to the exponent
`N + M`, as `(z - a)⁻⁽ᴺ⁺ᴹ⁾ ((z - a) ^ M h z)`. -/
private theorem coe_eq_inv_pow_add_mul {φ : meromorphicGerms 𝕜 a} {N : ℕ} {h : 𝕜 → 𝕜}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜)) (M : ℕ) :
    (φ : Germ (𝓝[≠] a) 𝕜) =
      (fun z ↦ ((z - a) ^ (N + M))⁻¹ * ((z - a) ^ M * h z) : 𝕜 → 𝕜) := by
  rw [hφ, Germ.coe_eq]
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
  have hz' : z - a ≠ 0 := sub_ne_zero.2 hz
  field_simp
  ring

/-- The product of the germs of `(z - a)⁻ᴺ h z` and `(z - a)⁻ᴹ k z` is the germ of
`(z - a)⁻⁽ᴺ⁺ᴹ⁾ (h z * k z)`. -/
private theorem coe_mul_eq_inv_pow_mul {φ ψ : meromorphicGerms 𝕜 a} {N M : ℕ} {h k : 𝕜 → 𝕜}
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜))
    (hψ : (ψ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ M)⁻¹ * k z : 𝕜 → 𝕜)) :
    ((φ * ψ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (fun z ↦ ((z - a) ^ (N + M))⁻¹ * (h * k) z : 𝕜 → 𝕜) := by
  rw [Subring.coe_mul, hφ, hψ, ← Germ.coe_mul]
  congr 1
  funext z
  simp only [Pi.mul_apply, pow_add, mul_inv]
  ring

/-- The constant germ `c` is the germ of `(z - a)⁻⁰ c`. -/
private theorem coe_algebraMap_eq_inv_pow_mul (c : 𝕜) :
    ((algebraMap 𝕜 (meromorphicGerms 𝕜 a) c : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
      (fun z ↦ ((z - a) ^ 0)⁻¹ * (fun _ ↦ c) z : 𝕜 → 𝕜) := by
  rw [← mk_const, coe_mk]
  simp only [pow_zero, inv_one, one_mul]

private theorem laurentSeriesFun_algebraMap (c : 𝕜) :
    laurentSeriesFun (algebraMap 𝕜 (meromorphicGerms 𝕜 a) c) = HahnSeries.C c := by
  rw [laurentSeriesFun_eq analyticAt_const (coe_algebraMap_eq_inv_pow_mul c), taylorSeries_const,
    ofPowerSeries_C, Nat.cast_zero, neg_zero, single_zero_one, one_mul]

variable (a) in
/-- The **Laurent expansion** of a meromorphic germ at `a`: for a germ represented by
`(z - a)⁻ᴺ h z` with `h` analytic at `a`, it is `X⁻ᴺ` times the Taylor series of `h` at `a`.
It is a homomorphism of `𝕜`-algebras into the formal Laurent series. -/
def laurentSeries : meromorphicGerms 𝕜 a →ₐ[𝕜] LaurentSeries 𝕜 where
  toFun := laurentSeriesFun
  map_one' := by
    rw [← map_one (algebraMap 𝕜 (meromorphicGerms 𝕜 a)), laurentSeriesFun_algebraMap, C_one]
  map_mul' φ ψ := by
    obtain ⟨N, h, hh, hφ⟩ := exists_eq_inv_pow_mul φ
    obtain ⟨M, k, hk, hψ⟩ := exists_eq_inv_pow_mul ψ
    rw [laurentSeriesFun_eq (hh.mul hk) (coe_mul_eq_inv_pow_mul hφ hψ),
      laurentSeriesFun_eq hh hφ, laurentSeriesFun_eq hk hψ, taylorSeries_mul hh hk, map_mul,
      mul_mul_mul_comm, single_mul_single, mul_one, Nat.cast_add, neg_add]
  map_zero' := by
    rw [← map_zero (algebraMap 𝕜 (meromorphicGerms 𝕜 a)), laurentSeriesFun_algebraMap, map_zero]
  map_add' φ ψ := by
    obtain ⟨N, h, hh, hφ⟩ := exists_eq_inv_pow_mul φ
    obtain ⟨M, k, hk, hψ⟩ := exists_eq_inv_pow_mul ψ
    have hc : AnalyticAt 𝕜 (fun z ↦ z - a) a := by fun_prop
    have hφ' := coe_eq_inv_pow_add_mul hφ M
    have hψ' := coe_eq_inv_pow_add_mul hψ N
    rw [add_comm M N] at hψ'
    have hsum : ((φ + ψ : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) =
        (fun z ↦ ((z - a) ^ (N + M))⁻¹ *
          ((fun z ↦ (z - a) ^ M * h z) + fun z ↦ (z - a) ^ N * k z) z : 𝕜 → 𝕜) := by
      rw [AddMemClass.coe_add, hφ', hψ', ← Germ.coe_add]
      congr 1
      funext z
      simp only [Pi.add_apply]
      ring
    rw [laurentSeriesFun_eq ((hc.pow M).mul hh) hφ', laurentSeriesFun_eq ((hc.pow N).mul hk) hψ',
      laurentSeriesFun_eq (((hc.pow M).mul hh).add ((hc.pow N).mul hk)) hsum,
      taylorSeries_add ((hc.pow M).mul hh) ((hc.pow N).mul hk), map_add, mul_add]
  commutes' c := by
    rw [laurentSeriesFun_algebraMap, LaurentSeries.algebraMap_apply]

/-- **The Laurent expansion through a representation.** If `φ` is the germ of `(z - a)⁻ᴺ h z`
with `h` analytic at `a`, then its Laurent expansion is `X⁻ᴺ` times the Taylor series of `h`
at `a`. -/
theorem laurentSeries_eq {φ : meromorphicGerms 𝕜 a} {N : ℕ} {h : 𝕜 → 𝕜}
    (hh : AnalyticAt 𝕜 h a)
    (hφ : (φ : Germ (𝓝[≠] a) 𝕜) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : 𝕜 → 𝕜)) :
    laurentSeries a φ = single (-(N : ℤ)) 1 * ofPowerSeries ℤ 𝕜 (taylorSeries h a) :=
  laurentSeriesFun_eq hh hφ

/-- The Laurent expansion of the germ of a function analytic at `a` is its Taylor series. -/
@[simp]
theorem laurentSeries_mk_of_analyticAt {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f a) :
    laurentSeries a (mk f hf.meromorphicAt) = ofPowerSeries ℤ 𝕜 (taylorSeries f a) := by
  rw [laurentSeries_eq hf (N := 0) (by simp), Nat.cast_zero, neg_zero, single_zero_one, one_mul]

/-- The Laurent expansion of the coordinate `z - a` is the variable `X`. -/
@[simp]
theorem laurentSeries_coordinate : laurentSeries a (coordinate a) = single 1 1 := by
  have hc : coordinate a = mk (fun z ↦ z - a) ((MeromorphicAt.id a).sub (.const a a)) :=
    Subtype.ext (by rw [coe_coordinate, coe_mk])
  rw [hc, laurentSeries_mk_of_analyticAt (by fun_prop), taylorSeries_sub_const,
    ofPowerSeries_X]

/-- **Uniqueness of Laurent expansions.** A meromorphic germ is determined by its Laurent
expansion. -/
theorem laurentSeries_injective : Injective (laurentSeries (𝕜 := 𝕜) a) :=
  (laurentSeries a).toRingHom.injective

/-- The Laurent expansion of the polynomial `P` in `(z - a)⁻¹` is `P` evaluated at `X⁻¹`. -/
theorem laurentSeries_evalInvSub (P : 𝕜[X]) :
    laurentSeries a (evalInvSub a P) = P.eval₂ HahnSeries.C (single (-1) 1) := by
  have hX : evalInvSub a X = (coordinate a)⁻¹ := Subtype.ext <| by
    rw [coe_evalInvSub, coe_inv, coe_coordinate, ← Germ.coe_inv]
    simp only [eval_X, Pi.inv_def]
  have hinv : (single (1 : ℤ) (1 : 𝕜))⁻¹ = single (-1) 1 :=
    inv_eq_of_mul_eq_one_right (by rw [single_mul_single, add_neg_cancel, mul_one, single_zero_one])
  have hC : ∀ c : 𝕜, evalInvSub a (C c) = algebraMap 𝕜 (meromorphicGerms 𝕜 a) c := fun c ↦
    (Subtype.ext (by simp only [coe_evalInvSub, coe_mk, eval_C])).trans (mk_const c)
  refine congrFun (congrArg DFunLike.coe (Polynomial.ringHom_ext
    (f := (laurentSeries a).toRingHom.comp (evalInvSub a))
    (g := eval₂RingHom HahnSeries.C (single (-1) 1)) (fun c ↦ ?_) ?_)) P
  · simp [hC, LaurentSeries.algebraMap_apply]
  · simp [hX, map_inv₀, hinv]

/-- The coefficients of the Laurent expansion of a polynomial `P` in `(z - a)⁻¹`, as a sum over
the coefficients of `P`. -/
private theorem coeff_laurentSeries_evalInvSub_eq_sum (P : 𝕜[X]) (n : ℤ) :
    (laurentSeries a (evalInvSub a P)).coeff n =
      ∑ i ∈ Finset.range (P.natDegree + 1), if n = -(i : ℤ) then P.coeff i else 0 := by
  rw [laurentSeries_evalInvSub, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [single_pow, C_mul_eq_smul, HahnSeries.coeff_smul, coeff_single, one_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero, smul_neg, nsmul_one]

/-- The coefficient of `X ^ (-k)` in the Laurent expansion of a polynomial `P` in `(z - a)⁻¹` is
the coefficient of `X ^ k` in `P`. -/
@[simp]
theorem coeff_laurentSeries_evalInvSub (P : 𝕜[X]) (k : ℕ) :
    (laurentSeries a (evalInvSub a P)).coeff (-(k : ℤ)) = P.coeff k := by
  rw [coeff_laurentSeries_evalInvSub_eq_sum]
  simp only [neg_inj, Nat.cast_inj]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt]
    rw [Finset.mem_range] at hk
    omega

/-- The Laurent expansion of a polynomial in `(z - a)⁻¹` has no positive coefficients. -/
@[simp]
theorem coeff_laurentSeries_evalInvSub_of_pos (P : 𝕜[X]) {n : ℤ} (hn : 0 < n) :
    (laurentSeries a (evalInvSub a P)).coeff n = 0 := by
  rw [coeff_laurentSeries_evalInvSub_eq_sum]
  exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right_iff.2 fun h ↦ by omega

/-- A meromorphic germ is the sum of its principal part and the germ of an analytic function. -/
private theorem laurentSeries_eq_evalInvSub_add {φ : meromorphicGerms 𝕜 a} {g : 𝕜 → 𝕜}
    (hg : AnalyticAt 𝕜 g a)
    (hφg : ((φ - evalInvSub a (principalPart φ) : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g) :
    laurentSeries a φ = laurentSeries a (evalInvSub a (principalPart φ)) +
      ofPowerSeries ℤ 𝕜 (taylorSeries g a) := by
  rw [← laurentSeries_mk_of_analyticAt hg, ← map_add,
    ← sub_eq_iff_eq_add'.1 (Subtype.ext (by rw [hφg, coe_mk]))]

/-- **Negative Laurent coefficients.** For `k ≠ 0`, the coefficient of `X ^ (-k)` in the Laurent
expansion of a meromorphic germ is the coefficient of `X ^ k` in its principal part. -/
@[simp]
theorem coeff_laurentSeries_neg (φ : meromorphicGerms 𝕜 a) {k : ℕ} (hk : k ≠ 0) :
    (laurentSeries a φ).coeff (-(k : ℤ)) = (principalPart φ).coeff k := by
  obtain ⟨g, hg, hφg⟩ := exists_analyticAt_coe_sub_evalInvSub_principalPart φ
  rw [laurentSeries_eq_evalInvSub_add hg hφg, HahnSeries.coeff_add,
    coeff_laurentSeries_evalInvSub, ofPowerSeries_apply, embDomain_of_notMem_range, add_zero]
  rintro ⟨m, hm⟩
  simp only [Nat.castOrderEmbedding_apply] at hm
  omega

/-- **Nonnegative Laurent coefficients.** If `g` is analytic at `a` and represents the regular
part `φ - P((z - a)⁻¹)` of a meromorphic germ `φ` with principal part `P`, then the coefficient of
`X ^ n`, `n ≥ 0`, in the Laurent expansion of `φ` is the `n`-th Taylor coefficient of `g` at
`a`. -/
theorem coeff_laurentSeries_natCast {φ : meromorphicGerms 𝕜 a} {g : 𝕜 → 𝕜}
    (hg : AnalyticAt 𝕜 g a)
    (hφg : ((φ - evalInvSub a (principalPart φ) : meromorphicGerms 𝕜 a) : Germ (𝓝[≠] a) 𝕜) = g)
    (n : ℕ) :
    (laurentSeries a φ).coeff n = PowerSeries.coeff n (taylorSeries g a) := by
  rw [laurentSeries_eq_evalInvSub_add hg hφg, HahnSeries.coeff_add, ofPowerSeries_apply_coeff]
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Nat.cast_zero, ← neg_zero, ← Nat.cast_zero, coeff_laurentSeries_evalInvSub,
      coeff_zero_principalPart, zero_add]
  · rw [coeff_laurentSeries_evalInvSub_of_pos _ (by exact_mod_cast hn), zero_add]

end TauCeti.meromorphicGerms
