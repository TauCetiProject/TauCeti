/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Analysis.Meromorphic.PrincipalPart
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ

/-!
# Meromorphic germs form the fraction field of holomorphic germs

Let `a : ℂ` and let `𝒪_a` be the stalk at `a` of the holomorphic structure sheaf of `ℂ`, an
integral domain. Restricting a holomorphic germ to the punctured neighbourhoods of `a` gives a
punctured meromorphic germ, which defines an injective ring homomorphism
`TauCeti.holomorphicStructureSheaf.toMeromorphicGerms a : 𝒪_a →+* meromorphicGerms ℂ a`
(`toMeromorphicGerms_injective`: by continuity a holomorphic germ is determined by its values off
`a`). This file proves:

* `exists_eq_toMeromorphicGerms_div`: every meromorphic germ at `a` is a quotient `h / (z - a) ^ n`
  of a holomorphic germ `h` by a power of the coordinate. Indeed, by Mathlib's definition a
  function `f` is meromorphic at `a` when `(z - a) ^ n • f z` is analytic at `a` for some `n`.
* `isFractionRing_meromorphicGerms`: consequently `meromorphicGerms ℂ a` is a fraction field of
  `𝒪_a`, so it is identified with `FractionRing 𝒪_a` by `IsFractionRing.algEquiv`.
* `exists_toMeromorphicGerms_eq_iff`: a meromorphic germ comes from a holomorphic germ exactly when
  its order at `a` is nonnegative.
* `mem_range_toMeromorphicGerms_iff_exists_tendsto`: equivalently, exactly when it has a limit
  along the punctured neighbourhoods of `a`.
* `evalInvSub_principalPart_add_toMeromorphicGerms_regularPart` and
  `evalInvSub_add_toMeromorphicGerms_eq_iff`: every meromorphic germ `φ` at `a` splits uniquely as
  `φ = P((z - a)⁻¹) + s`, with `P` a polynomial without constant term, its principal part
  `TauCeti.meromorphicGerms.principalPart φ`, and `s` a holomorphic germ, its regular part
  `regularPart a φ`. If `φ` is the germ of `(z - a)⁻ᴺ h z` with `h` analytic at `a`, the regular
  part is the germ of the remainder `(swap dslope a)^[N] h` in Taylor's formula for `h`
  (`coe_toMeromorphicGerms_regularPart`).
* `mem_range_toMeromorphicGerms_iff_principalPart_eq_zero`: a meromorphic germ comes from a
  holomorphic germ exactly when its principal part vanishes.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
-/

public noncomputable section

open Filter Function Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable (a : ℂ)

/-- Restricting a holomorphic germ at `a : ℂ` to the punctured neighbourhoods of `a` gives a
meromorphic germ at `a`. -/
def toMeromorphicGerms :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a →+* meromorphicGerms ℂ a :=
  (toFilterGerm 𝓘(ℂ) ℂ a (𝓝[≠] a) nhdsWithin_le_nhds).codRestrict _ fun s ↦ by
    obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq a s
    rw [hfs, coe_mem_meromorphicGerms]
    exact (contMDiffAt_iff_contDiffAt.1 hf.self_of_nhds).analyticAt.meromorphicAt

@[simp]
theorem coe_toMeromorphicGerms (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) =
      toFilterGerm 𝓘(ℂ) ℂ a (𝓝[≠] a) nhdsWithin_le_nhds s :=
  (rfl)

/-- A holomorphic germ at `a : ℂ` is determined by its values on a punctured neighbourhood. -/
theorem toMeromorphicGerms_injective : Injective (toMeromorphicGerms a) :=
  fun _ _ h ↦ toFilterGerm_nhdsNE_injective a (congrArg Subtype.val h)

variable {a}

/-- A function analytic at `a : ℂ` has a holomorphic germ at `a`, whose punctured germ is that of
the function. -/
theorem exists_toMeromorphicGerms_eq_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ s, (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f :=
  (exists_toFilterGerm_eq_of_eventually_contMDiffAt
    (hf.eventually_analyticAt.mono fun _ hy ↦ hy.contDiffAt.contMDiffAt)).imp fun _ hs ↦ hs _ _

/-- A function meromorphic at `a : ℂ` has the punctured germ of a holomorphic germ at `a`
exactly when its order at `a` is nonnegative. -/
theorem exists_toMeromorphicGerms_eq_iff {f : ℂ → ℂ} (hf : MeromorphicAt f a) :
    (∃ s, (toMeromorphicGerms a s : Germ (𝓝[≠] a) ℂ) = f) ↔ 0 ≤ meromorphicOrderAt f a := by
  rw [hf.meromorphicOrderAt_nonneg_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq a s
    rw [coe_toMeromorphicGerms, hgs, Germ.coe_eq] at hs
    exact ⟨g, (contMDiffAt_iff_contDiffAt.1 hg.self_of_nhds).analyticAt, hs.symm⟩
  · rintro ⟨g, hg, hfg⟩
    obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hg
    exact ⟨s, hs.trans (Germ.coe_eq.2 hfg.symm)⟩

/-- **Regular germs are those with a limit.** A meromorphic germ at `a` comes from a holomorphic
germ exactly when it has a limit along the punctured neighbourhoods of `a`. -/
theorem mem_range_toMeromorphicGerms_iff_exists_tendsto {φ : meromorphicGerms ℂ a} :
    φ ∈ (toMeromorphicGerms a).range ↔ ∃ c, (φ : Germ (𝓝[≠] a) ℂ).Tendsto (𝓝 c) := by
  obtain ⟨f, hf, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  simp_rw [← hφ, Germ.coe_tendsto, tendsto_nhds_iff_meromorphicOrderAt_nonneg hf,
    ← exists_toMeromorphicGerms_eq_iff hf, hφ, RingHom.mem_range, Subtype.ext_iff]

variable (a)

/-- Every meromorphic germ at `a : ℂ` is the quotient of a holomorphic germ by a power of the
coordinate `z - a`. -/
theorem exists_eq_toMeromorphicGerms_div (φ : meromorphicGerms ℂ a) :
    ∃ (h p : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (n : ℕ),
      (toMeromorphicGerms a p : Germ (𝓝[≠] a) ℂ) = (fun z ↦ (z - a) ^ n : ℂ → ℂ) ∧
        φ = toMeromorphicGerms a h / toMeromorphicGerms a p := by
  obtain ⟨f, ⟨n, hn⟩, hφ⟩ := mem_meromorphicGerms_iff.1 φ.2
  obtain ⟨h, hh⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hn
  have hpa : AnalyticAt ℂ (fun z ↦ (z - a) ^ n) a := by fun_prop
  obtain ⟨p, hp⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hpa
  refine ⟨h, p, n, hp, ?_⟩
  have hp0 : toMeromorphicGerms a p ≠ 0 := fun h0 ↦
    (hpa.meromorphicAt.germ_ne_zero_iff.2 <| eventually_mem_nhdsWithin.mono fun z hz ↦
      pow_ne_zero n (sub_ne_zero.2 hz)) (hp.symm.trans (congrArg Subtype.val h0))
  rw [eq_div_iff hp0]
  apply Subtype.ext
  rw [Subring.coe_mul, hp, hh, ← hφ, ← Germ.coe_mul]
  exact Germ.coe_eq.2 (.of_forall fun z ↦ by simp [smul_eq_mul, mul_comm])

/-- Meromorphic germs at `a : ℂ` form an algebra over the holomorphic germs at `a`, through
`toMeromorphicGerms`. -/
instance : Algebra ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) :=
  (toMeromorphicGerms a).toAlgebra

@[simp]
theorem algebraMap_meromorphicGerms :
    algebraMap ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) =
      toMeromorphicGerms a :=
  (rfl)

/-- The field of meromorphic germs at `a : ℂ` is the fraction field of the ring of holomorphic
germs at `a`. -/
instance isFractionRing_meromorphicGerms :
    IsFractionRing ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) (meromorphicGerms ℂ a) :=
  have : FaithfulSMul ((holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a)
      (meromorphicGerms ℂ a) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (toMeromorphicGerms_injective a)
  IsFractionRing.of_field _ _ fun φ ↦
    let ⟨h, p, _, _, hφ⟩ := exists_eq_toMeromorphicGerms_div a φ
    ⟨h, p, hφ⟩

/-! ### The principal part and the regular part -/

open meromorphicGerms in
/-- Subtracting its principal part from a meromorphic germ at `a : ℂ` leaves a holomorphic
germ. -/
private theorem exists_toMeromorphicGerms_eq_sub_evalInvSub_principalPart
    (φ : meromorphicGerms ℂ a) :
    ∃ s, toMeromorphicGerms a s = φ - evalInvSub a (principalPart φ) := by
  obtain ⟨g, hg, hgφ⟩ := exists_analyticAt_coe_sub_evalInvSub_principalPart φ
  obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_eq_of_analyticAt hg
  exact ⟨s, Subtype.ext (hs.trans hgφ.symm)⟩

open meromorphicGerms in
/-- The regular part of a meromorphic germ `φ` at `a : ℂ`: the holomorphic germ which, restricted
to the punctured neighbourhoods of `a`, is `φ - P((z - a)⁻¹)`, where `P` is the principal part of
`φ`. It is additive in `φ`. -/
def regularPart :
    meromorphicGerms ℂ a →+ (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a where
  toFun φ := (exists_toMeromorphicGerms_eq_sub_evalInvSub_principalPart a φ).choose
  map_zero' := toMeromorphicGerms_injective a <| by
    rw [(exists_toMeromorphicGerms_eq_sub_evalInvSub_principalPart a 0).choose_spec, map_zero,
      map_zero, map_zero, sub_zero]
  map_add' φ ψ := toMeromorphicGerms_injective a <| by
    have h := fun φ ↦ (exists_toMeromorphicGerms_eq_sub_evalInvSub_principalPart a φ).choose_spec
    rw [(toMeromorphicGerms a).map_add, h, h, h, map_add, map_add, add_sub_add_comm]

variable {a}

open meromorphicGerms in
/-- The principal part of a holomorphic germ vanishes. -/
@[simp]
theorem principalPart_toMeromorphicGerms
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    principalPart (toMeromorphicGerms a s) = 0 := by
  obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq a s
  exact principalPart_eq_zero_iff.2 ⟨g, (contMDiffAt_iff_contDiffAt.1 hg.self_of_nhds).analyticAt,
    by rw [coe_toMeromorphicGerms, hgs]⟩


open meromorphicGerms in
/-- On the punctured neighbourhoods of `a`, the regular part of `φ` is `φ` minus its principal
part. -/
theorem toMeromorphicGerms_regularPart (φ : meromorphicGerms ℂ a) :
    toMeromorphicGerms a (regularPart a φ) = φ - evalInvSub a (principalPart φ) :=
  (exists_toMeromorphicGerms_eq_sub_evalInvSub_principalPart a φ).choose_spec

open meromorphicGerms in
/-- **Principal part splitting.** A meromorphic germ at `a : ℂ` is the sum of its principal part
`P((z - a)⁻¹)` and its regular part. -/
theorem evalInvSub_principalPart_add_toMeromorphicGerms_regularPart (φ : meromorphicGerms ℂ a) :
    evalInvSub a (principalPart φ) + toMeromorphicGerms a (regularPart a φ) = φ := by
  rw [toMeromorphicGerms_regularPart, add_sub_cancel]

open meromorphicGerms in
/-- **Uniqueness of the principal part splitting.** A meromorphic germ `φ` at `a : ℂ` is
`P((z - a)⁻¹) + s`, with `P` a polynomial without constant term and `s` a holomorphic germ, exactly
when `P` is the principal part and `s` is the regular part of `φ`. -/
theorem evalInvSub_add_toMeromorphicGerms_eq_iff {φ : meromorphicGerms ℂ a} {P : ℂ[X]}
    (hP : P.coeff 0 = 0) {s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a} :
    evalInvSub a P + toMeromorphicGerms a s = φ ↔ principalPart φ = P ∧ regularPart a φ = s := by
  refine ⟨?_, fun ⟨hφP, hφs⟩ ↦ ?_⟩
  · rintro rfl
    have hφP : principalPart (evalInvSub a P + toMeromorphicGerms a s) = P := by
      rw [map_add, principalPart_evalInvSub_of_coeff_zero hP, principalPart_toMeromorphicGerms,
        add_zero]
    refine ⟨hφP, toMeromorphicGerms_injective a ?_⟩
    rw [toMeromorphicGerms_regularPart, hφP, add_sub_cancel_left]
  · rw [← hφP, ← hφs, evalInvSub_principalPart_add_toMeromorphicGerms_regularPart]

/-- The regular part of a holomorphic germ is the germ itself. -/
@[simp]
theorem regularPart_toMeromorphicGerms (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    regularPart a (toMeromorphicGerms a s) = s :=
  ((evalInvSub_add_toMeromorphicGerms_eq_iff (coeff_zero 0)).1 (by rw [map_zero, zero_add])).2

open meromorphicGerms in
/-- A meromorphic germ at `a` comes from a holomorphic germ exactly when its principal part
vanishes. -/
theorem mem_range_toMeromorphicGerms_iff_principalPart_eq_zero {φ : meromorphicGerms ℂ a} :
    φ ∈ (toMeromorphicGerms a).range ↔ principalPart φ = 0 := by
  refine ⟨fun ⟨s, hs⟩ ↦ hs ▸ principalPart_toMeromorphicGerms s, fun h ↦ ⟨regularPart a φ, ?_⟩⟩
  rw [toMeromorphicGerms_regularPart, h, map_zero, sub_zero]

open meromorphicGerms in
/-- On the punctured neighbourhoods of `a`, the regular part of a polynomial in the inverse
coordinate is its constant term. -/
@[simp]
theorem toMeromorphicGerms_regularPart_evalInvSub (P : ℂ[X]) :
    toMeromorphicGerms a (regularPart a (evalInvSub a P)) = evalInvSub a (C (P.coeff 0)) := by
  rw [toMeromorphicGerms_regularPart, principalPart_evalInvSub, map_sub, sub_sub_cancel]

open meromorphicGerms in
/-- A polynomial without constant term in the inverse coordinate has regular part zero. -/
@[simp]
theorem regularPart_evalInvSub {P : ℂ[X]} (hP : P.coeff 0 = 0) :
    regularPart a (evalInvSub a P) = 0 :=
  toMeromorphicGerms_injective a <| by
    rw [toMeromorphicGerms_regularPart_evalInvSub, hP, C_0, map_zero, map_zero]

open meromorphicGerms in
/-- **The regular part through Taylor's formula.** If `φ` is the germ of `(z - a)⁻ᴺ h z` with `h`
analytic at `a`, then the regular part of `φ` is the holomorphic germ of the remainder
`(swap dslope a)^[N] h` in Taylor's formula
`h z = Σ_{j<N} c_j (z - a) ^ j + (z - a) ^ N (swap dslope a)^[N] h z`. -/
theorem coe_toMeromorphicGerms_regularPart {φ : meromorphicGerms ℂ a} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h a) {N : ℕ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : ℂ → ℂ)) :
    (toMeromorphicGerms a (regularPart a φ) : Germ (𝓝[≠] a) ℂ) = (swap dslope a)^[N] h := by
  rw [toMeromorphicGerms_regularPart, coe_sub_evalInvSub_principalPart hh hφ]

end TauCeti.holomorphicStructureSheaf
