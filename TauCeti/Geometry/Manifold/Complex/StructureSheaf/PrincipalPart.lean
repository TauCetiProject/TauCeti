/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.PrincipalPart
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm

/-!
# Principal parts and regular parts of meromorphic germs

Let `a : ℂ`, let `𝒪_a` be the stalk at `a` of the holomorphic structure sheaf of `ℂ` and let
`K_a = meromorphicGerms ℂ a` be its fraction field of punctured meromorphic germs. The regular
germs in `K_a` are the image of `toMeromorphicGerms a : 𝒪_a →+* K_a`.

This file first identifies the regular germs intrinsically, without the value a representative
takes at `a`: a meromorphic germ is regular exactly when it has a limit at `a` along the punctured
neighbourhoods (Riemann's removable singularity theorem), and the value at `a` of a holomorphic
germ is that limit. Thus evaluation `𝒪_a →+* ℂ` is computed on punctured germs.

It then splits `K_a` into regular germs and finite principal parts. Every `φ : K_a` is uniquely
`φ = r + P((z - a)⁻¹)` with `r` regular and `P` a polynomial without constant term. This gives
the additive maps `principalPart a : K_a →+ ℂ[X]` and `regularPart a : K_a →+ 𝒪_a`.
Informally, the coefficient of `X ^ k` in `principalPart a φ` is the coefficient of
`(z - a)⁻ᵏ` in the Laurent expansion of `φ`. Concretely, if `φ` is the germ of
`(z - a)⁻ⁿ h z` for `h` with power series `p` at `a`, then
`principalPart a φ = ∑ j < n, p.coeff j X ^ (n - j)` and `regularPart a φ` is the germ of the
`n`-th iterated divided slope of `h` at `a` (`principalPart_eq_sum_of_hasFPowerSeriesAt`).
Since `principalPart` and `regularPart` are functions of the germ, these do not depend on the
choice of `n`, of `h` or of the neighbourhood.

## Main results

* `TauCeti.holomorphicStructureSheaf.exists_toMeromorphicGerms_eq_iff_exists_tendsto`: a
  meromorphic germ is regular exactly when it has a limit at `a`.
* `TauCeti.holomorphicStructureSheaf.tendsto_eval_of_toMeromorphicGerms_eq`: the value of a
  holomorphic germ at `a` is the limit of its punctured germ.
* `TauCeti.holomorphicStructureSheaf.evalInvSub_mem_range_toMeromorphicGerms_iff`: a nonzero
  principal part is never regular.
* `TauCeti.holomorphicStructureSheaf.existsUnique_principalPart`: the decomposition into a
  principal part and a regular germ exists and is unique.
* `TauCeti.holomorphicStructureSheaf.principalPart`,
  `TauCeti.holomorphicStructureSheaf.regularPart`: the two components, which add up to the germ
  (`toMeromorphicGerms_regularPart_add_evalInvSub_principalPart`).
* `TauCeti.holomorphicStructureSheaf.principalPart_eq_sum_of_hasFPowerSeriesAt`: the principal
  part read off from the Taylor coefficients of `(z - a)ⁿ φ`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 4, §3.1.
-/

public noncomputable section

open Filter Function Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {a : ℂ}

/-! ### Regular germs and their values -/

/-- A meromorphic germ at `a` is the germ of a holomorphic germ exactly when it is the punctured
germ of a function analytic at `a`. -/
theorem mem_range_toMeromorphicGerms_iff {φ : meromorphicGerms ℂ a} :
    φ ∈ (toMeromorphicGerms a).range ↔
      ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ (r : Germ (𝓝[≠] a) ℂ) = φ := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨r, hr, hrs⟩ := exists_toFilterGerm_eq a s
    exact ⟨r, (contMDiffAt_iff_contDiffAt.1 hr.self_of_nhds).analyticAt, by
      rw [coe_toMeromorphicGerms, hrs]⟩
  · rintro ⟨r, hr, hrφ⟩
    obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hr
    exact ⟨s, Subtype.ext (hs.trans hrφ)⟩

/-- **Riemann's removable singularity theorem for germs.** A function meromorphic at `a` has the
punctured germ of a holomorphic germ at `a` exactly when it has a limit at `a` along the punctured
neighbourhoods of `a`. -/
theorem exists_toMeromorphicGerms_eq_iff_exists_tendsto {f : ℂ → ℂ} (hf : MeromorphicAt f a) :
    (∃ s, (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f) ↔
      ∃ c, Tendsto f (𝓝[≠] a) (𝓝 c) := by
  rw [exists_toMeromorphicGerms_eq_iff hf, tendsto_nhds_iff_meromorphicOrderAt_nonneg hf]

/-- The value at `a` of a holomorphic germ is the limit at `a`, along the punctured
neighbourhoods, of any function with the same punctured germ. In particular it is determined by
the punctured germ alone. -/
theorem tendsto_eval_of_toMeromorphicGerms_eq
    {s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a} {f : ℂ → ℂ}
    (h : (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f) :
    Tendsto f (𝓝[≠] a) (𝓝 (eval 𝓘(ℂ) ℂ a s)) := by
  obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq a s
  rw [eval_eq_of_toFilterGerm_eq (hgs _ le_rfl)]
  rw [coe_toMeromorphicGerms, hgs, Germ.coe_eq] at h
  exact (hg.self_of_nhds.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' h

/-! ### Principal parts -/

/-- A finite principal part `P((z - a)⁻¹)`, for a polynomial `P` without constant term, is a
regular meromorphic germ only when `P = 0`. -/
theorem evalInvSub_mem_range_toMeromorphicGerms_iff {P : ℂ[X]} (hP : P.coeff 0 = 0) :
    meromorphicGerms.evalInvSub a P ∈ (toMeromorphicGerms a).range ↔ P = 0 := by
  refine ⟨fun ⟨s, hs⟩ ↦ P.eq_zero_of_tendsto_eval_inv_sub hP
    (tendsto_eval_of_toMeromorphicGerms_eq (s := s) ?_), fun h ↦ h ▸ by simp⟩
  rw [hs, meromorphicGerms.coe_evalInvSub]

/-- **Existence and uniqueness of principal parts.** Every meromorphic germ `φ` at `a` is, for a
unique polynomial `P` without constant term, the sum of the principal part `P((z - a)⁻¹)` and a
regular germ. -/
theorem existsUnique_principalPart (φ : meromorphicGerms ℂ a) :
    ∃! P : ℂ[X], P.coeff 0 = 0 ∧
      φ - meromorphicGerms.evalInvSub a P ∈ (toMeromorphicGerms a).range := by
  obtain ⟨f, hf, hfφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  obtain ⟨P, hP, r, hr, hfr⟩ := hf.exists_eventuallyEq_eval_inv_sub_add
  have hPφ : φ - meromorphicGerms.evalInvSub a P ∈ (toMeromorphicGerms a).range := by
    refine mem_range_toMeromorphicGerms_iff.2 ⟨r, hr, ?_⟩
    rw [AddSubgroupClass.coe_sub, meromorphicGerms.coe_evalInvSub, ← hfφ, ← Germ.coe_sub,
      Germ.coe_eq]
    filter_upwards [hfr] with z hz
    simp [hz]
  refine ⟨P, ⟨hP, hPφ⟩, fun Q ⟨hQ, hQφ⟩ ↦ ?_⟩
  -- The difference of the two principal parts is a regular principal part, hence zero.
  have hmem := Subring.sub_mem _ hQφ hPφ
  rw [sub_sub_sub_cancel_left, ← map_sub] at hmem
  have := (evalInvSub_mem_range_toMeromorphicGerms_iff (by simp [hP, hQ])).1 hmem
  exact (sub_eq_zero.1 this).symm

variable (a) in
/-- The principal part of a meromorphic germ `φ` at `a`: the unique polynomial `P` without constant
term such that `φ - P((z - a)⁻¹)` is regular. -/
def principalPart : meromorphicGerms ℂ a →+ ℂ[X] where
  toFun φ := (existsUnique_principalPart φ).choose
  map_zero' := ((existsUnique_principalPart (0 : meromorphicGerms ℂ a)).choose_spec.2 0
    ⟨coeff_zero 0, by simp⟩).symm
  map_add' φ ψ := ((existsUnique_principalPart (φ + ψ)).choose_spec.2 _
    ⟨by rw [coeff_add, (existsUnique_principalPart φ).choose_spec.1.1,
      (existsUnique_principalPart ψ).choose_spec.1.1, add_zero], by
      rw [map_add, add_sub_add_comm]
      exact Subring.add_mem _ (existsUnique_principalPart φ).choose_spec.1.2
        (existsUnique_principalPart ψ).choose_spec.1.2⟩).symm

/-- The principal part has no constant term. -/
@[simp]
theorem coeff_zero_principalPart (φ : meromorphicGerms ℂ a) : (principalPart a φ).coeff 0 = 0 :=
  (existsUnique_principalPart φ).choose_spec.1.1

/-- Subtracting its principal part from a meromorphic germ leaves a regular germ. -/
theorem sub_evalInvSub_principalPart_mem_range (φ : meromorphicGerms ℂ a) :
    φ - meromorphicGerms.evalInvSub a (principalPart a φ) ∈ (toMeromorphicGerms a).range :=
  (existsUnique_principalPart φ).choose_spec.1.2

/-- The principal part of `φ` is the only polynomial `P` without constant term for which
`φ - P((z - a)⁻¹)` is regular. -/
theorem principalPart_eq_iff {φ : meromorphicGerms ℂ a} {P : ℂ[X]} (hP : P.coeff 0 = 0) :
    principalPart a φ = P ↔
      φ - meromorphicGerms.evalInvSub a P ∈ (toMeromorphicGerms a).range :=
  ⟨fun h ↦ h ▸ sub_evalInvSub_principalPart_mem_range φ, fun h ↦
    ((existsUnique_principalPart φ).choose_spec.2 P ⟨hP, h⟩).symm⟩

/-- A meromorphic germ has zero principal part exactly when it is regular. -/
theorem principalPart_eq_zero_iff {φ : meromorphicGerms ℂ a} :
    principalPart a φ = 0 ↔ φ ∈ (toMeromorphicGerms a).range := by
  rw [principalPart_eq_iff (coeff_zero 0), map_zero, sub_zero]

/-- A regular germ has zero principal part. -/
@[simp]
theorem principalPart_toMeromorphicGerms
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    principalPart a (toMeromorphicGerms a s) = 0 :=
  principalPart_eq_zero_iff.2 ⟨s, rfl⟩

/-- The principal part of `P((z - a)⁻¹)`, for `P` without constant term, is `P`. -/
@[simp]
theorem principalPart_evalInvSub {P : ℂ[X]} (hP : P.coeff 0 = 0) :
    principalPart a (meromorphicGerms.evalInvSub a P) = P :=
  (principalPart_eq_iff hP).2 (by simp)

/-! ### Regular parts -/

variable (a) in
/-- The regular part of a meromorphic germ `φ` at `a`: the holomorphic germ whose punctured germ
is `φ` minus its principal part. -/
def regularPart : meromorphicGerms ℂ a →+ (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a where
  toFun φ := (sub_evalInvSub_principalPart_mem_range φ).choose
  map_zero' := toMeromorphicGerms_injective a <| by
    rw [(sub_evalInvSub_principalPart_mem_range 0).choose_spec, (principalPart a).map_zero,
      (meromorphicGerms.evalInvSub a).map_zero, (toMeromorphicGerms a).map_zero, sub_zero]
  map_add' φ ψ := toMeromorphicGerms_injective a <| by
    rw [(toMeromorphicGerms a).map_add,
      (sub_evalInvSub_principalPart_mem_range (φ + ψ)).choose_spec,
      (sub_evalInvSub_principalPart_mem_range φ).choose_spec,
      (sub_evalInvSub_principalPart_mem_range ψ).choose_spec, (principalPart a).map_add,
      (meromorphicGerms.evalInvSub a).map_add, add_sub_add_comm]

/-- The punctured germ of the regular part of `φ` is `φ` minus its principal part. -/
theorem toMeromorphicGerms_regularPart (φ : meromorphicGerms ℂ a) :
    toMeromorphicGerms a (regularPart a φ) =
      φ - meromorphicGerms.evalInvSub a (principalPart a φ) :=
  (sub_evalInvSub_principalPart_mem_range φ).choose_spec

/-- Every meromorphic germ is the sum of its regular part and its principal part. -/
@[simp]
theorem toMeromorphicGerms_regularPart_add_evalInvSub_principalPart (φ : meromorphicGerms ℂ a) :
    toMeromorphicGerms a (regularPart a φ) + meromorphicGerms.evalInvSub a (principalPart a φ) =
      φ := by
  rw [toMeromorphicGerms_regularPart, sub_add_cancel]

/-- **Uniqueness of the decomposition.** If `φ = s + P((z - a)⁻¹)` with `s` regular and `P`
without constant term, then `s` is the regular part and `P` the principal part of `φ`. -/
theorem regularPart_eq_and_principalPart_eq {φ : meromorphicGerms ℂ a}
    {s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a} {P : ℂ[X]} (hP : P.coeff 0 = 0)
    (h : toMeromorphicGerms a s + meromorphicGerms.evalInvSub a P = φ) :
    regularPart a φ = s ∧ principalPart a φ = P := by
  have hPφ : principalPart a φ = P :=
    (principalPart_eq_iff hP).2 ⟨s, by rw [← h, add_sub_cancel_right]⟩
  refine ⟨toMeromorphicGerms_injective a ?_, hPφ⟩
  rw [toMeromorphicGerms_regularPart, hPφ, ← h, add_sub_cancel_right]

/-- The regular part of a regular germ is the germ itself. -/
@[simp]
theorem regularPart_toMeromorphicGerms (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    regularPart a (toMeromorphicGerms a s) = s :=
  (regularPart_eq_and_principalPart_eq (coeff_zero 0) (by simp)).1

/-- The regular part of a principal part is zero. -/
@[simp]
theorem regularPart_evalInvSub {P : ℂ[X]} (hP : P.coeff 0 = 0) :
    regularPart a (meromorphicGerms.evalInvSub a P) = 0 :=
  (regularPart_eq_and_principalPart_eq hP (by simp)).1

/-! ### Principal parts from Taylor coefficients -/

/-- **Principal parts from Taylor coefficients.** If `φ` is the punctured germ of
`(z - a)⁻ⁿ h z`, where `h` has the power series `p` at `a`, then the principal part of `φ` is
`∑ j < n, p.coeff j X ^ (n - j)`, and its regular part is the germ of the `n`-th iterated divided
slope of `h` at `a`, the function `q` with `h z = ∑ j < n, p.coeff j (z - a) ^ j + (z - a) ^ n q z`.
-/
theorem principalPart_eq_sum_of_hasFPowerSeriesAt {φ : meromorphicGerms ℂ a} {h : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt h p a) {n : ℕ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = (fun z ↦ ((z - a) ^ n)⁻¹ * h z : ℂ → ℂ)) :
    principalPart a φ = ∑ j ∈ Finset.range n, monomial (n - j) (p.coeff j) ∧
      (toMeromorphicGerms a (regularPart a φ) : Germ (𝓝[≠] a) ℂ) = (swap dslope a)^[n] h := by
  obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt
    (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt
  have hdec := regularPart_eq_and_principalPart_eq (φ := φ) (s := s)
      (TauCeti.coeff_zero_sum_range_monomial_sub n p.coeff) <| Subtype.ext <| by
    rw [Subring.coe_add, hs, meromorphicGerms.coe_evalInvSub, ← Germ.coe_add, hφ, Germ.coe_eq]
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Pi.add_apply, hp.inv_pow_mul_eq_eval_inv_sub_add n hz, add_comm]
  exact ⟨hdec.2, by rw [hdec.1, hs]⟩

end TauCeti.holomorphicStructureSheaf
