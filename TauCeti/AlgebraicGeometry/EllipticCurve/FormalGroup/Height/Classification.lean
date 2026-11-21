/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nilpotent.Lemmas
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Classification of Weierstrass formal group heights at every prime

Let `W` be a Weierstrass curve over a field `K` of characteristic `p`, and let `Ê` be its formal
group law. This file classifies the height of `Ê` for every Weierstrass curve, smooth or singular,
and establishes sharp multiplication-series order bounds over reduced commutative rings:

* In prime characteristic `p`, if `W` is elliptic (`Δ ≠ 0`), then `Ê` has height `1` or `2`: height
  `1` exactly when `W` is ordinary (equivalently, the Hasse invariant `coeff (p - 1) ω` is
  nonzero), and height `2` exactly when `W` is supersingular (equivalently, the Hasse invariant
  vanishes).
* If `W` is nodal (`Δ = 0` and `c₄ ≠ 0`), then `Ê` has height `1` in prime characteristic `p`, and
  its Hasse invariant is nonzero; for any `m ≠ 0`, `[m]_Ê` has order at most `m`.
* If `W` is cuspidal (`Δ = 0` and `c₄ = 0`), then `[m]_Ê = 0` whenever `(m : K) = 0`, and `Ê` has
  height `⊤` whenever `(p : K) = 0`.
* Over any reduced commutative ring `R`, `[m]_Ê` has order at most `m²` whenever `m ≠ 0` and
  `c₄ ≠ 0 ∨ Δ ≠ 0`, and `[m]_Ê = 0` whenever `Δ = 0`, `c₄ = 0`, and `(m : R) = 0`.

In particular, in characteristic `p`, `Ê` has height `1`, `2`, or `⊤`; in prime characteristic `p`,
it has height at most `2` exactly when `W` is smooth or nodal (`c₄ ≠ 0 ∨ Δ ≠ 0`), height `2`
exactly when `W` is smooth with vanishing Hasse invariant (`Δ ≠ 0 ∧ coeff (p - 1) ω = 0`), and
infinite height exactly at a cusp (`Δ = 0 ∧ c₄ = 0`). More generally, for any `p ≠ 0` with
`(p : K) = 0`, `Ê` has height `⊤` iff `Δ = 0 ∧ c₄ = 0`, and for any `p ≠ 0` over any field, any
smooth or nodal curve has finite `p`-height.

This supplies the field-level and reduced-ring input for ring-level height-ideal bounds,
Landweber's `v₂`-unit condition, and the nodal Hasse-invariant unit condition in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Bound`.

## Strategy

For an elliptic curve `W`, the ordinary and supersingular strata are characterized by height `1`
and `2` in `TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular`, via the
inseparable degree of `[p]`; this file adds the Hasse-invariant description of height `2`.

For a singular curve (`Δ = 0`), passing to `AlgebraicClosure K` preserves the formal-group height
and the order of `[m]_Ê`, and supplies a singular point `(x, y)` together with a root `α` of the
tangent quadratic (`WeierstrassCurve.Affine.exists_isSingular_and_tangent_root_of_Δ_eq_zero`). The
change of variables `⟨1, x, α, y⟩` brings the curve to `y² + (a₁ + 2 α) x y = x³`
(`WeierstrassCurve.Affine.variableChange_eq_of_isSingular`), where `(a₁ + 2 α) ^ 4 = c₄`, leaving
the height and multiplication-series order unchanged. By
`WeierstrassCurve.formalGroup_eq_homothety_smul_𝔾ₘ` and `WeierstrassCurve.formalGroup_eq_𝔾ₐ`,
this cubic has multiplicative formal group when `c₄ ≠ 0` and additive formal group when `c₄ = 0`.
Reducing modulo prime ideals extends the order bound and cuspidal vanishing to every reduced
commutative ring.

## Main results

* `WeierstrassCurve.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero`:
  an elliptic curve in prime characteristic `p` has formal group of height `2` exactly when its
  Hasse invariant vanishes.
* `WeierstrassCurve.order_nsmulSeries_formalGroup_le_sq` and
  `WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero`: over any reduced
  commutative ring, `[m]_Ê` has order at most `m²` when `m ≠ 0` and `c₄ ≠ 0 ∨ Δ ≠ 0`, and
  vanishes when `Δ = 0`, `c₄ = 0`, and `(m : R) = 0`.
* `WeierstrassCurve.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero`: for any `p ≠ 0` over
  any field, a smooth or nodal Weierstrass curve has finite formal-group height.
* `WeierstrassCurve.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero`: nodal cubics in prime
  characteristic have height `1` and cuspidal cubics have height `⊤`.
* `WeierstrassCurve.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero` and
  `WeierstrassCurve.coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero`:
  for a singular Weierstrass curve in prime characteristic, height `1`, nonzero Hasse invariant, and
  `c₄ ≠ 0` coincide.
* `WeierstrassCurve.height_formalGroup_eq_two_iff`,
  `WeierstrassCurve.height_formalGroup_eq_top_iff`,
  `WeierstrassCurve.height_formalGroup_le_two_iff`, and
  `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_or_eq_top`: complete trichotomy and
  exact characterizations of each height stratum for arbitrary Weierstrass curves over fields.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.1.
-/

public section

namespace WeierstrassCurve

section Elliptic

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **Height two from the Hasse invariant**: in prime characteristic `p`, an elliptic curve has
formal group of height `2` exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential of
its formal group vanishes. -/
theorem height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.isSupersingular_iff_height_formalGroup_eq_two,
    W.isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero]

end Elliptic

section OrderBounds

/-- Over the algebraic closure, a singular Weierstrass curve (`Δ = 0`) can be transformed by a
change of variables into `y² + a x y = x³` with `a⁴ = c₄`, preserving both the formal-group height
and the order of `[m]_Ê`. -/
private theorem exists_order_nsmulSeries_formalGroup_eq_of_Δ_eq_zero {K : Type*} [Field K]
    (W : WeierstrassCurve K) (hΔ : W.Δ = 0) (m : ℕ) :
    ∃ a : AlgebraicClosure K, a ^ 4 = algebraMap K (AlgebraicClosure K) W.c₄ ∧
      ((formalGroup W).nsmulSeries m).order =
        ((formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K))).nsmulSeries
          m).order := by
  let Ω := AlgebraicClosure K
  let ι : K →+* Ω := algebraMap K Ω
  let W₁ : WeierstrassCurve Ω := W.map ι
  obtain ⟨x, y, α, hxy, hα'⟩ :=
    W₁.toAffine.exists_isSingular_and_tangent_root_of_Δ_eq_zero (by rw [map_Δ, hΔ, map_zero])
  refine ⟨W₁.a₁ + 2 * α, ?_, ?_⟩
  · have hc₄ := Affine.c₄_eq_of_isSingular hxy hα'
    rw [map_c₄] at hc₄
    rw [add_comm, ← hc₄]
  · have hV := Affine.variableChange_eq_of_isSingular hxy hα'
    calc
      ((formalGroup W).nsmulSeries m).order
        = (PowerSeries.map ι ((formalGroup W).nsmulSeries m)).order :=
            (PowerSeries.order_map_of_injective ι.injective _).symm
      _ = ((formalGroup W₁).nsmulSeries m).order := by
            rw [FormalGroup.map_nsmulSeries, ← map_formalGroup]
      _ = ((formalGroup (VariableChange.mk 1 x α y • W₁)).nsmulSeries m).order := by
            rw [← VariableChange.formalCoordinate_smul_formalGroup _ W₁]
            exact ((FormalGroup.smulIso _ _).order_nsmulSeries_eq m).symm
      _ = ((formalGroup (⟨W₁.a₁ + 2 * α, 0, 0, 0, 0⟩ : WeierstrassCurve Ω)).nsmulSeries m).order :=
            by rw [hV]

/-- Over a field, for a nodal Weierstrass curve (`Δ = 0` and `c₄ ≠ 0`) and `m ≠ 0`, the series
`[m]_Ê` has order at most `m`. -/
theorem order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero {K : Type*} [Field K]
    (W : WeierstrassCurve K) {m : ℕ} (hm : m ≠ 0) (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ m := by
  obtain ⟨a, ha, hord⟩ := W.exists_order_nsmulSeries_formalGroup_eq_of_Δ_eq_zero hΔ m
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at ha
    exact hc₄ ((algebraMap K (AlgebraicClosure K)).injective (by simpa using ha.symm))
  have hgm : ((formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K))).nsmulSeries
      m).order = ((FormalGroup.𝔾ₘ : FormalGroup (AlgebraicClosure K)).nsmulSeries m).order := by
    rw [formalGroup_eq_homothety_smul_𝔾ₘ (Units.mk0 a ha0) rfl rfl rfl rfl rfl]
    exact ((FormalGroup.smulIso _
      (FormalGroup.𝔾ₘ : FormalGroup (AlgebraicClosure K))).order_nsmulSeries_eq m).symm
  rw [hord, hgm]
  have hcoeff : PowerSeries.coeff m
      ((FormalGroup.𝔾ₘ : FormalGroup (AlgebraicClosure K)).nsmulSeries m) = 1 := by
    rw [FormalGroup.nsmulSeries_𝔾ₘ, map_sub, add_comm, add_pow]
    simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_one, hm]
  exact PowerSeries.order_le m (by rw [hcoeff]; exact one_ne_zero)

private theorem order_nsmulSeries_formalGroup_le_sq_field {K : Type*} [Field K]
    (W : WeierstrassCurve K) {m : ℕ} (hm : m ≠ 0) (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) := by
  by_cases hΔ : W.Δ = 0
  · exact (W.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero hm hΔ
      (h.resolve_right (not_not.mpr hΔ))).trans
      (by exact_mod_cast Nat.le_self_pow (by decide) m)
  · have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    rw [W.order_nsmulSeries_formalGroup_of_ne_zero hm, Nat.cast_le]
    set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine (mod_cast hm : (m : ℤ) ≠ 0)
    have hmul : φ.separableDegree * φ.inseparableDegree = m ^ 2 := by
      rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
        Int.natAbs_natCast]
    have hsep : 1 ≤ φ.separableDegree := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
      rw [h0, zero_mul] at hmul
      exact pow_ne_zero 2 hm hmul.symm
    calc
      φ.inseparableDegree = 1 * φ.inseparableDegree := (one_mul _).symm
      _ ≤ φ.separableDegree * φ.inseparableDegree := Nat.mul_le_mul_right _ hsep
      _ = m ^ 2 := hmul

private theorem nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero_field {K : Type*}
    [Field K] (W : WeierstrassCurve K) {m : ℕ} (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0)
    (hm : (m : K) = 0) : (formalGroup W).nsmulSeries m = 0 := by
  obtain ⟨a, ha, hord⟩ := W.exists_order_nsmulSeries_formalGroup_eq_of_Δ_eq_zero hΔ m
  have ha0 : a = 0 := by
    rw [hc₄, map_zero] at ha
    exact (pow_eq_zero_iff (by decide)).mp ha
  have hm' : (m : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), hm, map_zero]
  rw [← PowerSeries.order_eq_top, hord,
    formalGroup_eq_𝔾ₐ (W := (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)))
      ha0 rfl rfl rfl rfl,
    FormalGroup.nsmulSeries_𝔾ₐ, ← map_natCast PowerSeries.C, hm', map_zero, zero_mul,
    PowerSeries.order_zero]

/-- **Order bound for `[m]_Ê` over reduced rings**: for any smooth or nodal Weierstrass curve over
a reduced commutative ring (`c₄ ≠ 0 ∨ Δ ≠ 0`) and any `m ≠ 0`, the multiplication-by-`m` series
has order at most `m²`. -/
theorem order_nsmulSeries_formalGroup_le_sq {R : Type*} [CommRing R] [IsReduced R]
    (W : WeierstrassCurve R) {m : ℕ} (hm : m ≠ 0) (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) := by
  have hex : ∃ P : Ideal R, P.IsPrime ∧ (W.c₄ ∉ P ∨ W.Δ ∉ P) := by
    by_contra hall
    push Not at hall
    have hmem (x : R) (hx : ∀ P : Ideal R, P.IsPrime → x ∈ P) : x = 0 := by
      have : x ∈ nilradical R := nilradical_eq_sInf R ▸ Ideal.mem_sInf.mpr fun P hP ↦ hx P hP
      rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact h.elim (fun hc₄ ↦ hc₄ (hmem _ fun P hP ↦ (hall P hP).1))
      (fun hΔ ↦ hΔ (hmem _ fun P hP ↦ (hall P hP).2))
  obtain ⟨P, hP, hPmem⟩ := hex
  let _ : P.IsPrime := hP
  let f : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hf_ne {x : R} (hx : x ∉ P) : f x ≠ 0 := by
    intro h0
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P)) (by simpa [f] using h0)
  have hmap : (W.map f).c₄ ≠ 0 ∨ (W.map f).Δ ≠ 0 :=
    hPmem.imp (fun hc₄ ↦ by rw [map_c₄]; exact hf_ne hc₄) (fun hΔ ↦ by rw [map_Δ]; exact hf_ne hΔ)
  calc
    ((formalGroup W).nsmulSeries m).order
      ≤ (PowerSeries.map f ((formalGroup W).nsmulSeries m)).order := PowerSeries.le_order_map f
    _ = ((formalGroup (W.map f)).nsmulSeries m).order := by
        rw [FormalGroup.map_nsmulSeries, ← map_formalGroup]
    _ ≤ (m ^ 2 : ℕ) := order_nsmulSeries_formalGroup_le_sq_field (W.map f) hm hmap

/-- **Vanishing of `[m]_Ê` at a cusp over reduced rings**: over a reduced commutative ring, if
`Δ = 0`, `c₄ = 0`, and `(m : R) = 0`, then `[m]_Ê = 0`. -/
theorem nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero {R : Type*} [CommRing R]
    [IsReduced R] (W : WeierstrassCurve R) {m : ℕ} (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0)
    (hm : (m : R) = 0) : (formalGroup W).nsmulSeries m = 0 := by
  ext k
  rw [map_zero]
  suffices PowerSeries.coeff k ((formalGroup W).nsmulSeries m) ∈ nilradical R by
    rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro P hP
  let _ : P.IsPrime := hP
  let f : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hz := nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero_field (W.map f)
    (by simp [hΔ]) (by simp [hc₄]) (by rw [← map_natCast f, hm, map_zero])
  have hk : f (PowerSeries.coeff k ((formalGroup W).nsmulSeries m)) = 0 := by
    rw [← FormalGroup.coeff_nsmulSeries_map, ← map_formalGroup, hz, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P)) (by simpa [f] using hk))

end OrderBounds

section Singular

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- Over any field and for any `p ≠ 0`, a smooth or nodal Weierstrass curve (`c₄ ≠ 0 ∨ Δ ≠ 0`) has
finite formal-group height. -/
theorem height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero {p : ℕ} (hp : p ≠ 0)
    (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [ne_eq, FormalGroup.height_eq_top_iff]
  intro h0
  have hord := W.order_nsmulSeries_formalGroup_le_sq hp h
  simp [h0] at hord

/-- **A cuspidal Weierstrass curve has infinite formal-group height** whenever `(p : K) = 0`:
if `Δ = 0`, `c₄ = 0`, and `(p : K) = 0`, then the formal group of `W` has height `⊤`. -/
theorem height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero_of_cast_eq_zero {p : ℕ}
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) (hp : (p : K) = 0) : (formalGroup W).height p = ⊤ :=
  ((formalGroup W).height_eq_top_iff).mpr
    (W.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hp)

/-- Over a field with `p ≠ 0` and `(p : K) = 0`, the formal group of a Weierstrass curve has
infinite height exactly when the curve is cuspidal (`Δ = 0 ∧ c₄ = 0`). -/
theorem height_formalGroup_eq_top_iff_of_cast_eq_zero {p : ℕ} (hp : p ≠ 0) (hpK : (p : K) = 0) :
    (formalGroup W).height p = ⊤ ↔ W.Δ = 0 ∧ W.c₄ = 0 := by
  refine ⟨fun htop ↦ ?_, fun ⟨hΔ, hc₄⟩ ↦
    W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero_of_cast_eq_zero hΔ hc₄ hpK⟩
  by_contra h
  rw [not_and_or, or_comm] at h
  exact W.height_formalGroup_ne_top_of_c₄_ne_zero_or_Δ_ne_zero hp h htop

variable {p : ℕ} [CharP K p]

omit [CharP K p] in
/-- Over the algebraic closure, a singular Weierstrass curve (`Δ = 0`) can be transformed by a
change of variables into `y² + a x y = x³` with `a⁴ = c₄`, preserving the height of its formal
group. -/
private theorem exists_height_formalGroup_eq_of_Δ_eq_zero (hΔ : W.Δ = 0) :
    ∃ a : AlgebraicClosure K, a ^ 4 = algebraMap K (AlgebraicClosure K) W.c₄ ∧
      (formalGroup W).height p =
        (formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K))).height p := by
  let Ω := AlgebraicClosure K
  let ι : K →+* Ω := algebraMap K Ω
  let W₁ : WeierstrassCurve Ω := W.map ι
  obtain ⟨x, y, α, hxy, hα'⟩ :=
    W₁.toAffine.exists_isSingular_and_tangent_root_of_Δ_eq_zero (by rw [map_Δ, hΔ, map_zero])
  refine ⟨W₁.a₁ + 2 * α, ?_, ?_⟩
  · have hc₄ := Affine.c₄_eq_of_isSingular hxy hα'
    rw [map_c₄] at hc₄
    rw [add_comm, ← hc₄]
  · have hV := Affine.variableChange_eq_of_isSingular hxy hα'
    calc
      (formalGroup W).height p = ((formalGroup W).map ι).height p :=
        ((formalGroup W).height_map ι p).symm
      _ = (formalGroup W₁).height p := by rw [map_formalGroup]
      _ = (formalGroup (VariableChange.mk 1 x α y • W₁)).height p :=
        (VariableChange.height_formalGroup_variableChange _ W₁ p).symm
      _ = (formalGroup (⟨W₁.a₁ + 2 * α, 0, 0, 0, 0⟩ : WeierstrassCurve Ω)).height p := by
        rw [hV]

/-- **A nodal Weierstrass curve has formal-group height `1`.** Over a field of prime characteristic
`p`, if `Δ = 0` and `c₄ ≠ 0`, then the formal group of `W` has height `1`. -/
theorem height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero [Fact p.Prime] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ ≠ 0) : (formalGroup W).height p = 1 := by
  obtain ⟨a, ha, hht⟩ := W.exists_height_formalGroup_eq_of_Δ_eq_zero hΔ
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at ha
    exact hc₄ ((map_eq_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mp ha.symm)
  rw [hht]
  exact height_formalGroup_eq_one (W := (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve (AlgebraicClosure K)))
    ha0 rfl rfl rfl rfl

/-- **A cuspidal Weierstrass curve has infinite formal-group height.** Over a field of
characteristic `p`, if `Δ = 0` and `c₄ = 0`, then the formal group of `W` has height `⊤`. -/
theorem height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    (formalGroup W).height p = ⊤ :=
  W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero_of_cast_eq_zero hΔ hc₄
    (CharP.cast_eq_zero K p)

/-- Over a field of prime characteristic `p`, a singular Weierstrass curve (`Δ = 0`) has
formal-group height `1` exactly when `c₄ ≠ 0` (i.e., when the singularity is a node rather than a
cusp). -/
theorem height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero [Fact p.Prime] (hΔ : W.Δ = 0) :
    (formalGroup W).height p = 1 ↔ W.c₄ ≠ 0 := by
  refine ⟨fun h hc₄ ↦ ?_, W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ⟩
  rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄] at h
  exact ENat.top_ne_one h

/-- Over a field of prime characteristic `p`, the Hasse invariant of a singular Weierstrass curve
(`Δ = 0`) is nonzero exactly when `c₄ ≠ 0`. -/
theorem coeff_invariantDifferential_formalGroup_ne_zero_iff_c₄_ne_zero_of_Δ_eq_zero [Fact p.Prime]
    (hΔ : W.Δ = 0) :
    PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 ↔ W.c₄ ≠ 0 := by
  rw [← W.height_formalGroup_eq_one_iff, W.height_formalGroup_eq_one_iff_c₄_ne_zero_of_Δ_eq_zero hΔ]

/-- **Smooth or nodal Weierstrass curves have formal-group height `1` or `2`.** Over a field of
prime characteristic `p`, whenever `c₄ ≠ 0 ∨ Δ ≠ 0`, the formal group of `W` has height `1` or `2`.
-/
theorem height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero [Fact p.Prime]
    (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases hΔ : W.Δ = 0
  · exact Or.inl (W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ
      (h.resolve_right (not_not.mpr hΔ)))
  · have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact W.height_formalGroup_eq_one_or_eq_two

omit [CharP K p] in
/-- **Trichotomy of formal-group heights for Weierstrass curves.** Over a field of characteristic
`p`, the formal group of any Weierstrass curve has height `1`, `2`, or `⊤`. -/
theorem height_formalGroup_eq_one_or_eq_two_or_eq_top [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ∨ (formalGroup W).height p = ⊤ := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    by_cases h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0
    · rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · push Not at h
      exact Or.inr (Or.inr (W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero h.2 h.1))
  · exact Or.inr (Or.inr (((formalGroup W).height_eq_top_iff).mpr (by simp)))

/-- **Characterization of formal-group height `2`.** Over a field of prime characteristic `p`,
a Weierstrass curve has formal group of height `2` exactly when it is elliptic (`Δ ≠ 0`) and its
Hasse invariant vanishes. -/
theorem height_formalGroup_eq_two_iff [Fact p.Prime] :
    (formalGroup W).height p = 2 ↔
      W.Δ ≠ 0 ∧ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  constructor
  · intro h
    have hΔ : W.Δ ≠ 0 := by
      intro hΔ0
      by_cases hc₄ : W.c₄ = 0
      · rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔ0 hc₄] at h
        exact ENat.natCast_ne_top 2 h.symm
      · rw [W.height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔ0 hc₄] at h
        exact absurd h (by decide)
    have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact ⟨hΔ,
      W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mp h⟩
  · rintro ⟨hΔ, hH⟩
    have : W.IsElliptic := W.isElliptic_iff.mpr (isUnit_iff_ne_zero.mpr hΔ)
    exact W.height_formalGroup_eq_two_iff_coeff_invariantDifferential_formalGroup_eq_zero.mpr hH

/-- **Characterization of infinite formal-group height.** Over a field of prime characteristic `p`,
a Weierstrass curve has formal group of height `⊤` exactly when it is cuspidal (`Δ = 0 ∧ c₄ = 0`).
-/
theorem height_formalGroup_eq_top_iff [hp : Fact p.Prime] :
    (formalGroup W).height p = ⊤ ↔ W.Δ = 0 ∧ W.c₄ = 0 :=
  W.height_formalGroup_eq_top_iff_of_cast_eq_zero hp.out.ne_zero (CharP.cast_eq_zero K p)

/-- **Characterization of formal-group height at most `2`.** Over a field of prime characteristic
`p`, a Weierstrass curve has formal group of height at most `2` exactly when it is smooth or nodal
(`c₄ ≠ 0 ∨ Δ ≠ 0`). -/
theorem height_formalGroup_le_two_iff [Fact p.Prime] :
    (formalGroup W).height p ≤ 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rw [W.height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hne.2 hne.1] at h
    exact absurd h (by decide)
  · intro h
    rcases W.height_formalGroup_eq_one_or_eq_two_of_c₄_ne_zero_or_Δ_ne_zero h with h | h
    · rw [h]; decide
    · exact h.le

end Singular

end WeierstrassCurve
