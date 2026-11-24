/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Analysis.Contour.MeromorphicLaurent
public import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# Change of variables for residues

If `φ` is analytic at `p` with `φ'(p) ≠ 0` (a local biholomorphism at `p`), then for every `f`
the residue of the pulled-back function `(f ∘ φ) · φ'` at `p` equals the residue of `f` at `φ p`:
`Res_p ((f ∘ φ) · φ') = Res_{φ p} f`. In the language of differentials, the residue of the
meromorphic `1`-form `f(w) dw` at a point does not depend on the holomorphic coordinate `w` used to
compute it, which is what makes the residue of a meromorphic differential on a Riemann surface
well defined.

The proof is algebraic, computing with the Laurent coefficient that defines
`TauCeti.Contour.residue`. Writing `f = h + ∑ₖ aₖ / (w − φ p) ^ (k + 1)` near `φ p` with `h`
analytic, the pull-back splits as `(h ∘ φ) · φ' + ∑ₖ aₖ · φ' / (φ − φ p) ^ (k + 1)`. The first
summand is analytic. The `k = 0` summand is the logarithmic derivative of `φ − φ p`, a function
with a simple zero at `p`, so its residue is `1`. For `k ≥ 1` the summand is the derivative of
`−(φ − φ p) ^ (−k) / k`, and the residue of the derivative of any meromorphic function vanishes.

The same computation applies when `φ` is merely analytic at `p`, with `φ − φ p` vanishing to some
order `m`: the logarithmic derivative of `φ − φ p` then has residue `m`, so
`Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f` for `f` meromorphic at `φ p`. This is the local form of the
statement that pullback along a holomorphic map multiplies residues by the local multiplicity.

## Main results

* `TauCeti.Contour.residue_deriv_eq_zero`: `Res_p g' = 0` for `g` meromorphic at `p`: exact
  differentials have no residue.
* `TauCeti.Contour.residue_deriv_div_sub_pow_of_analyticOrderAt_eq`: if `φ − φ p` vanishes to
  order `m` at `p`, then `Res_p (φ' / (φ − φ p) ^ (k + 1))` is `m` for `k = 0` and `0` otherwise.
* `TauCeti.Contour.residue_deriv_div_sub_pow`: `Res_p (φ' / (φ − φ p) ^ (k + 1))` is `1` for
  `k = 0` and `0` otherwise, the pull-back of `TauCeti.Contour.residue_const_div_sub_pow`.
* `TauCeti.Contour.residue_comp_mul_deriv_eq_analyticOrderNatAt_mul`: the branched
  change-of-variables formula `Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`.
* `TauCeti.Contour.residue_comp_mul_deriv`: the change-of-variables formula
  `Res_p ((f ∘ φ) · φ') = Res_{φ p} f`.
* `TauCeti.Contour.residue_comp_add_const`, `TauCeti.Contour.residue_comp_const_mul`: the
  translation and dilation special cases.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §9, where the residue of a
  meromorphic differential is defined chart by chart and shown to be independent of the chart.
-/

public section

open Filter Topology

namespace TauCeti.Contour

/-- **Exact differentials have no residue.** If `g` is meromorphic at `z₀`, then the residue of its
derivative `g'` at `z₀` vanishes: differentiating the Laurent expansion of `g` produces no
`(z − z₀)⁻¹` term. -/
@[simp]
theorem residue_deriv_eq_zero {g : ℂ → ℂ} {z₀ : ℂ} (hg : MeromorphicAt g z₀) :
    residue (deriv g) z₀ = 0 := by
  obtain ⟨a, h, hh, hgh⟩ := exists_laurent_data_of_meromorphicAt hg
  generalize meromorphicPolarOrderAt g z₀ = N at a hgh
  -- The derivative of the Laurent expansion of `g` is a Laurent expansion with no `k = 0` term.
  have hderiv : ∀ᶠ z in 𝓝[≠] z₀, deriv g z = deriv h z + ∑ k : Fin (N + 1),
      (Fin.cases 0 (fun j : Fin N ↦ -((j.val : ℂ) + 1) * a j) k : ℂ) / (z - z₀) ^ (k.val + 1) := by
    have hev : g =ᶠ[𝓝[≠] z₀] fun z ↦ h z + ∑ k : Fin N, a k / (z - z₀) ^ (k.val + 1) := hgh
    filter_upwards [hev.nhdsNE_deriv, self_mem_nhdsWithin,
      nhdsWithin_le_nhds hh.eventually_analyticAt] with z hz hzne hhz
    have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
    have hmono : ∀ k : Fin N, HasDerivAt (fun w ↦ a k / (w - z₀) ^ (k.val + 1))
        (-((k.val : ℂ) + 1) * a k / (z - z₀) ^ (k.val + 1 + 1)) z := fun k ↦ by
      have := ((((hasDerivAt_id' z).sub_const z₀).fun_pow (k.val + 1)).fun_inv
        (pow_ne_zero _ hsub)).const_mul (a k)
      convert this using 1
      · simp [div_eq_mul_inv]
      · simp only [Nat.add_sub_cancel, mul_one]
        field_simp
        push_cast
        ring
    rw [hz, (hhz.differentiableAt.hasDerivAt.fun_add
      (HasDerivAt.fun_sum fun k _ ↦ hmono k)).deriv, Fin.sum_univ_succ]
    simp
  rw [residue_of_laurent_expansion hh.deriv hderiv]
  simp

/-- **Residue of a pulled-back Laurent monomial along a branched map.** If `φ` is analytic at `p`
and `φ − φ p` vanishes to finite order `m` at `p`, then `φ' / (φ − φ p) ^ (k + 1)`, the pull-back
along `φ` of the form `dw / (w − φ p) ^ (k + 1)`, has residue `m` at `p` for `k = 0` and `0` for
`k ≥ 1`. In the local normal form `φ = φ p + z ^ m` the `k = 0` form is `m · dz / z`. -/
theorem residue_deriv_div_sub_pow_of_analyticOrderAt_eq {φ : ℂ → ℂ} {p : ℂ} {m : ℕ}
    (hφ : AnalyticAt ℂ φ p) (hm : analyticOrderAt (fun z ↦ φ z - φ p) p = m) (k : ℕ) :
    residue (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1)) p = if k = 0 then (m : ℂ) else 0 := by
  have hsub : AnalyticAt ℂ (fun z ↦ φ z - φ p) p := hφ.sub analyticAt_const
  rcases k with _ | k
  · -- `φ' / (φ − φ p)` is the logarithmic derivative of `φ − φ p`, which vanishes to order `m`.
    have hlog : (fun z ↦ deriv φ z / (φ z - φ p) ^ (0 + 1)) = logDeriv (fun z ↦ φ z - φ p) := by
      ext z
      simp [logDeriv_apply]
    have hord : meromorphicOrderAt (fun z ↦ φ z - φ p) p = ((m : ℤ) : WithTop ℤ) := by
      rw [hsub.meromorphicOrderAt_eq, hm]
      simp
    rw [hlog, residue_logDeriv_eq_meromorphicOrderAt hsub.meromorphicAt hord]
    simp
  · -- `φ − φ p` has isolated zeros, and off them `φ' / (φ − φ p) ^ (k + 2)` is the derivative of
    -- `−(k + 1)⁻¹ · ((φ − φ p) ^ (k + 1))⁻¹`.
    have hnc : ¬ EventuallyConst φ (𝓝 p) := by
      rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hm]
      exact ENat.natCast_ne_top m
    have hne : ∀ᶠ z in 𝓝[≠] p, φ z - φ p ≠ 0 :=
      (Tendsto.eventually (hφ.map_nhdsNE hnc) self_mem_nhdsWithin).mono fun _ hz ↦ sub_ne_zero.2 hz
    set G : ℂ → ℂ := fun z ↦ -((k : ℂ) + 1)⁻¹ * ((φ z - φ p) ^ (k + 1))⁻¹
    have hG : MeromorphicAt G p :=
      analyticAt_const.meromorphicAt.mul (hsub.meromorphicAt.pow _).inv
    have heq : (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1 + 1)) =ᶠ[𝓝[≠] p] deriv G := by
      filter_upwards [hne, nhdsWithin_le_nhds hφ.eventually_analyticAt] with z hsub hφz
      rw [(((hφz.differentiableAt.hasDerivAt.sub_const (φ p)).fun_pow (k + 1)).fun_inv
        (pow_ne_zero _ hsub)).const_mul _ |>.deriv]
      simp only [Nat.add_sub_cancel]
      field_simp
      push_cast
      ring
    rw [residue_congr_nhdsNE heq, residue_deriv_eq_zero hG]
    simp

/-- **Residue of a pulled-back Laurent monomial.** If `φ` is analytic at `p` with `φ'(p) ≠ 0`,
then `φ' / (φ − φ p) ^ (k + 1)`, the pull-back along `φ` of the form `dw / (w − φ p) ^ (k + 1)`,
has residue `1` at `p` for `k = 0` and `0` for `k ≥ 1`. For `φ = id` this is
`TauCeti.Contour.residue_const_div_sub_pow` with coefficient `1`. -/
@[simp]
theorem residue_deriv_div_sub_pow {φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hφ' : deriv φ p ≠ 0) (k : ℕ) :
    residue (fun z ↦ deriv φ z / (φ z - φ p) ^ (k + 1)) p = if k = 0 then 1 else 0 := by
  simpa using residue_deriv_div_sub_pow_of_analyticOrderAt_eq hφ (m := 1)
    (by simpa using hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ') k

/-- **Change of variables for residues along a branched map.** If `φ` is analytic at `p` and `f` is
meromorphic at `φ p`, then the residue of `(f ∘ φ) · φ'` at `p` is the residue of `f` at `φ p`
multiplied by the order `m` of vanishing of `φ − φ p` at `p`:
`Res_p ((f ∘ φ) · φ') = m · Res_{φ p} f`.
Near a point where `φ` is not constant, `φ` is an `m`-fold branched cover in the local normal form
`φ p + z ^ m`, and each of the `m` sheets contributes `Res_{φ p} f`. If `φ` is constant near `p`,
then `analyticOrderNatAt` takes the value `0`, and so does the residue, since `φ' = 0` near `p`. -/
theorem residue_comp_mul_deriv_eq_analyticOrderNatAt_mul {f φ : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f (φ p)) (hφ : AnalyticAt ℂ φ p) :
    residue (fun z ↦ f (φ z) * deriv φ z) p =
      analyticOrderNatAt (fun z ↦ φ z - φ p) p * residue f (φ p) := by
  generalize hm' : analyticOrderAt (fun z ↦ φ z - φ p) p = r
  cases r with
  | top =>
    -- `φ` is constant near `p`, so `φ'` and the pulled-back function vanish near `p`.
    have hc : φ =ᶠ[𝓝 p] fun _ ↦ φ p := by
      filter_upwards [analyticOrderAt_eq_top.1 hm'] with z hz
      exact sub_eq_zero.1 hz
    have hzero : (fun z ↦ f (φ z) * deriv φ z) =ᶠ[𝓝[≠] p] fun _ ↦ (0 : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds hc.deriv] with z hz
      simp [hz]
    rw [residue_congr_nhdsNE hzero, residue_eq_zero_of_analyticAt analyticAt_const,
      analyticOrderNatAt, hm']
    simp
  | coe m =>
  have hm : analyticOrderAt (fun z ↦ φ z - φ p) p = m := hm'
  have hmnat : analyticOrderNatAt (fun z ↦ φ z - φ p) p = m := by
    rw [analyticOrderNatAt, hm, ENat.toNat_natCast]
  have hnc : ¬ EventuallyConst φ (𝓝 p) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hm]
    exact ENat.natCast_ne_top m
  have hφt : Tendsto φ (𝓝[≠] p) (𝓝[≠] φ p) := hφ.map_nhdsNE hnc
  obtain ⟨a, h, hh, hfh⟩ := exists_laurent_data_of_meromorphicAt hf
  generalize meromorphicPolarOrderAt f (φ p) = N at a hfh
  have hterm : ∀ k : Fin N,
      MeromorphicAt (fun z ↦ a k * (deriv φ z / (φ z - φ p) ^ (k.val + 1))) p := fun k ↦
    analyticAt_const.meromorphicAt.mul
      (hφ.deriv.meromorphicAt.div ((hφ.sub analyticAt_const).meromorphicAt.pow _))
  have hhφ : AnalyticAt ℂ (fun z ↦ h (φ z) * deriv φ z) p :=
    (hh.comp_of_eq hφ rfl).mul hφ.deriv
  -- Pull the Laurent expansion of `f` at `φ p` back along `φ`.
  have hpull : (fun z ↦ f (φ z) * deriv φ z) =ᶠ[𝓝[≠] p] (fun z ↦ h (φ z) * deriv φ z) +
      ∑ k : Fin N, fun z ↦ a k * (deriv φ z / (φ z - φ p) ^ (k.val + 1)) := by
    filter_upwards [hφt.eventually hfh] with z hz
    simp only [hz, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  -- Rewrite `f` at `φ p` by its Laurent expansion too, so both sides become sums over `k`.
  have hmono : ∀ k : Fin N, MeromorphicAt (fun w ↦ a k / (w - φ p) ^ (k.val + 1)) (φ p) :=
    fun k ↦ by fun_prop
  have hfeq : f =ᶠ[𝓝[≠] φ p] h + ∑ k : Fin N, fun w ↦ a k / (w - φ p) ^ (k.val + 1) := by
    filter_upwards [hfh] with w hw
    simpa [Finset.sum_apply] using hw
  rw [residue_congr_nhdsNE hpull, residue_congr_nhdsNE hfeq]
  simp [residue_add hhφ.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hterm k),
    residue_add hh.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmono k),
    residue_eq_zero_of_analyticAt hhφ, residue_eq_zero_of_analyticAt hh,
    residue_sum _ fun k _ ↦ hterm k, residue_sum _ fun k _ ↦ hmono k, hmnat, Finset.mul_sum,
    residue_const_mul, residue_deriv_div_sub_pow_of_analyticOrderAt_eq hφ hm,
    residue_const_div_sub_pow, mul_comm]

/-- **Change of variables for residues.** If `φ` is analytic at `p` with `φ'(p) ≠ 0`, then for
every `f : ℂ → ℂ` the residue of `(f ∘ φ) · φ'` at `p` is the residue of `f` at `φ p`. Equivalently,
the residue of the meromorphic `1`-form `f(w) dw` is independent of the local coordinate.

No meromorphy hypothesis on `f` is needed: since `φ` is a local biholomorphism, `(f ∘ φ) · φ'` is
meromorphic at `p` exactly when `f` is meromorphic at `φ p`, and otherwise both residues take the
junk value `0`. -/
theorem residue_comp_mul_deriv {f φ : ℂ → ℂ} {p : ℂ} (hφ : AnalyticAt ℂ φ p)
    (hφ' : deriv φ p ≠ 0) :
    residue (fun z ↦ f (φ z) * deriv φ z) p = residue f (φ p) := by
  by_cases hf : MeromorphicAt f (φ p)
  case neg =>
    have hcomp : ¬ MeromorphicAt (fun z ↦ f (φ z) * deriv φ z) p := fun h ↦ by
      refine hf ((meromorphicAt_comp_iff_of_deriv_ne_zero hφ hφ').1 ?_)
      exact (meromorphicAt_mul_iff_of_ne_zero hφ.deriv hφ').mp
        (h.congr (.of_forall fun z ↦ mul_comm (f (φ z)) (deriv φ z)))
    rw [residue_of_not_meromorphicAt hcomp, residue_of_not_meromorphicAt hf]
  rw [residue_comp_mul_deriv_eq_analyticOrderNatAt_mul hf hφ, analyticOrderNatAt,
    hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ']
  simp

/-- **Translation invariance of the residue.** The residue of `z ↦ f (z + c)` at `p` is the residue
of `f` at `p + c`. -/
@[simp]
theorem residue_comp_add_const (f : ℂ → ℂ) (c p : ℂ) :
    residue (fun z ↦ f (z + c)) p = residue f (p + c) := by
  simpa using residue_comp_mul_deriv (f := f) (φ := fun z ↦ z + c) (p := p) (by fun_prop)
    (by simp)

/-- **Scaling of the residue under dilation.** The residue of `z ↦ f (c * z)` at `p` is `c⁻¹` times
the residue of `f` at `c * p`. For `c = 0` both sides vanish: the left side is the residue of a
constant function, and `0⁻¹ = 0`. -/
@[simp]
theorem residue_comp_const_mul (f : ℂ → ℂ) (c p : ℂ) :
    residue (fun z ↦ f (c * z)) p = c⁻¹ * residue f (c * p) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using residue_eq_zero_of_analyticAt (f := fun _ : ℂ ↦ f 0) (z₀ := p) analyticAt_const
  have h : residue (fun z ↦ c * f (c * z)) p = residue f (c * p) := by
    simpa [mul_comm _ c] using residue_comp_mul_deriv (f := f) (φ := fun z ↦ c * z) (p := p)
      (by fun_prop) (by simpa using hc)
  rw [residue_const_mul] at h
  rw [← h, inv_mul_cancel_left₀ hc]

end TauCeti.Contour

end
