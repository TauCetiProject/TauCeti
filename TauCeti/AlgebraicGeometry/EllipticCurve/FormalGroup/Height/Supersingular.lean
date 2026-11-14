/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Hom
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.ComputeDegree
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# The formal-group height of elliptic and singular Weierstrass curves

Let `W` be an elliptic curve over a field `K` and `Ê` its formal group law. For a nonzero integer
`n`, the formal power series of the multiplication-by-`n` isogeny `[n] : W → W` is the
`n`-multiplication series `[n]_Ê` (`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`), and the
order of vanishing of an isogeny's formal series is its inseparable degree
(`TauCeti.Isogeny.order_formalSeries`). Hence the order of `[n]_Ê` equals the inseparable degree of
`[n]` (`WeierstrassCurve.order_zsmulSeries_formalGroup`). Over any nontrivial commutative ring,
reducing modulo a maximal ideal shows that `[n]_Ê ≠ 0` for `n ≠ 0`
(`WeierstrassCurve.zsmulSeries_formalGroup_ne_zero`,
`WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`).

Specializing to a prime `p` in characteristic `p`: `[p]` has degree `p²`, and its separable degree
is `p` when `W` is ordinary and `1` when `W` is supersingular
(`WeierstrassCurve.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq`,
`WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one`). Therefore
`[p]_Ê` has order `p` when `W` is ordinary and `p²` when `W` is supersingular: an elliptic curve in
characteristic `p` has formal-group height `1` precisely when it is ordinary, and height `2`
precisely when it is supersingular (`WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`,
`WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`). In particular, every elliptic
curve in characteristic `p` has formal-group height `1` or `2`.

On singular Weierstrass curves (`Δ = 0`), passing to `AlgebraicClosure K` and moving the unique
singular point to the origin brings the equation to `y² + a₁ x y = x³` with `a₁⁴ = c₄`, without
changing `c₄` or the height of `Ê`. By `WeierstrassCurve.height_formalGroup_eq_one` and
`WeierstrassCurve.height_formalGroup_eq_top`, a nodal curve (`Δ = 0`, `c₄ ≠ 0`) has height `1` and
a cuspidal curve (`Δ = 0`, `c₄ = 0`) has height `⊤`. Together with the elliptic case this gives the
complete height classification for arbitrary Weierstrass equations in characteristic `p`: `Ê` has
height `⊤` if and only if `c₄ = 0` and `Δ = 0`, and height `1` or `2` otherwise.

## Main results

* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: over a field, the order of `[n]_Ê` on an
  elliptic curve is the inseparable degree of `[n]`.
* `WeierstrassCurve.zsmulSeries_formalGroup_ne_zero` and
  `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`: over a nontrivial commutative ring, `[n]_Ê`
  is nonzero for `n ≠ 0` on an elliptic curve.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: in prime characteristic `p`, an
  elliptic curve is ordinary if and only if its formal group has height `1`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: in characteristic `p`, an
  elliptic curve is supersingular if and only if its formal group has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: in prime characteristic `p`, the formal group of an
  elliptic curve has height `1` or `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_of_c₄_ne_zero` and
  `WeierstrassCurve.height_formalGroup_eq_top_of_c₄_eq_zero`: nodal curves (`Δ = 0`, `c₄ ≠ 0`) have
  formal-group height `1`, and cuspidal curves (`Δ = 0`, `c₄ = 0`) have height `⊤`.
* `WeierstrassCurve.height_formalGroup_eq_top_iff`,
  `WeierstrassCurve.height_formalGroup_le_two_iff`, and
  `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two_iff`: for any Weierstrass curve in prime
  characteristic `p`, the height is `⊤` on the cuspidal locus `c₄ = Δ = 0` and `1` or `2` on its
  complement.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7 and V.3.1.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire Bourbaki
  1005 (2009), §3.
-/

public section

namespace WeierstrassCurve

section Order

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê` is the inseparable degree of `[n]`.** For an elliptic curve `W` over a
field and `n : ℤ` nonzero, the power-series order of `[n]_Ê` equals the inseparable degree of the
multiplication-by-`n` isogeny. -/
theorem order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero W hn,
    TauCeti.Isogeny.order_formalSeries]

/-- **The order of `[n]_Ê` (`n : ℕ`) is the inseparable degree of `[n]`.** -/
theorem order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
        (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← FormalGroup.zsmulSeries_natCast,
    W.order_zsmulSeries_formalGroup (Nat.cast_ne_zero.mpr hn)]

end Order

section Nonzero

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **On an elliptic curve over a nontrivial ring, `[n]_Ê ≠ 0` for every nonzero `n : ℤ`.** -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let _ := Ideal.Quotient.field 𝔪
  let π := Ideal.Quotient.mk 𝔪
  have : (W.map π).IsElliptic := ⟨W.isUnit_Δ.map π⟩
  intro h0
  have hord := (W.map π).order_zsmulSeries_formalGroup hn
  rw [map_formalGroup, ← FormalGroup.map_zsmulSeries, h0, map_zero, PowerSeries.order_zero]
    at hord
  exact ENat.top_ne_natCast _ hord

/-- **On an elliptic curve over a nontrivial ring, `[n]_Ê ≠ 0` for every nonzero `n : ℕ`.** -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← FormalGroup.zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

end Nonzero

section EllipticHeight

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {p : ℕ}

/-- **Ordinarity is formal-group height one.** Over a field of prime characteristic `p`, an elliptic
curve is ordinary if and only if its formal group has height `1` (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one [hp : Fact p.Prime] [CharP K p] :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hp0
  have hmul : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out, ← Nat.cast_one,
    FormalGroup.height_eq_natCast_iff, pow_one, W.order_nsmulSeries_formalGroup hp.out.ne_zero,
    Nat.cast_inj (R := ℕ∞)]
  change φ.separableDegree = p ↔ φ.inseparableDegree = p
  constructor <;> intro h
  · rw [h] at hmul
    exact Nat.mul_left_cancel hp.out.pos hmul
  · rw [h] at hmul
    exact Nat.mul_right_cancel hp.out.pos hmul

/-- **Supersingularity is formal-group height two.** Over a field of characteristic `p`, an elliptic
curve is supersingular at `p` if and only if its formal group has height `2` (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two [CharP K p] :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hp0
    have hmul : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
      rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
        Int.natAbs_natCast]
    rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p,
      ← Nat.cast_ofNat (n := 2), FormalGroup.height_eq_natCast_iff,
      W.order_nsmulSeries_formalGroup hp.ne_zero, Nat.cast_inj (R := ℕ∞)]
    change φ.separableDegree = 1 ↔ φ.inseparableDegree = p ^ 2
    constructor <;> intro h
    · rwa [h, one_mul] at hmul
    · rw [h] at hmul
      exact Nat.mul_right_cancel (pow_pos hp.pos 2) (hmul.trans (one_mul _).symm)
  · -- For `p = 0`, `height 0 = ⊤ ≠ 2` and `W(AlgebraicClosure K)` contains a nonzero point.
    classical
    have htop : (formalGroup W).height 0 = ⊤ := (formalGroup W).height_eq_top_iff.mpr (by simp)
    refine iff_of_false (fun hss ↦ ?_) (by rw [htop]; exact ENat.top_ne_natCast 2)
    let L := AlgebraicClosure K
    have hdeg : (Polynomial.X ^ 2 + Polynomial.C (algebraMap K L W.a₃) * Polynomial.X -
        Polynomial.C (algebraMap K L W.a₆) : Polynomial L).degree = 2 := by compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; decide)
    have heq : (W.baseChange L).toAffine.Equation 0 y := by
      rw [Affine.equation_iff]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hy
      simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
      linear_combination hy
    have hns : (W.baseChange L).toAffine.Nonsingular 0 y := Affine.equation_iff_nonsingular.mp heq
    exact Affine.Point.some_ne_zero hns (isSupersingular_iff_forall.mp hss _ (zero_nsmul _))

/-- **An elliptic curve in prime characteristic `p` has formal-group height `1` or `2`.** -/
theorem height_formalGroup_eq_one_or_eq_two [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp h)
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp (not_isOrdinary.mp h))

/-- **An elliptic curve in prime characteristic `p` has formal-group height at most `2`.** -/
theorem height_formalGroup_le_two [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> rw [h]; decide

end EllipticHeight

section SingularHeight

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {p : ℕ}

/-- Over `AlgebraicClosure K`, a singular Weierstrass model (`Δ = 0`) can be transformed by
admissible changes of variables into `y² + a₁ x y = x³` with `a₁⁴ = c₄` without altering the
formal-group height. -/
private theorem exists_height_formalGroup_eq_of_Δ_eq_zero (hΔ : W.Δ = 0) :
    ∃ V : WeierstrassCurve (AlgebraicClosure K),
      V.a₂ = 0 ∧ V.a₃ = 0 ∧ V.a₄ = 0 ∧ V.a₆ = 0 ∧
      V.a₁ ^ 4 = algebraMap K (AlgebraicClosure K) W.c₄ ∧
      (formalGroup W).height p = (formalGroup V).height p := by
  let L := AlgebraicClosure K
  let ι := algebraMap K L
  have hΔL : (W.map ι).toAffine.Δ = 0 := by simp [hΔ]
  obtain ⟨x, y, hsing⟩ := Affine.exists_isSingular_of_Δ_eq_zero (W.map ι).toAffine hΔL
  set V₁ := VariableChange.mk 1 x 0 y • W.map ι
  obtain ⟨h₆, h₄, h₃⟩ := (Affine.isSingular_zero V₁.toAffine).mp
    ((Affine.isSingular_iff_variableChange _ x y).mp hsing)
  have hQdeg : (Polynomial.X ^ 2 + Polynomial.C V₁.a₁ * Polynomial.X -
      Polynomial.C V₁.a₂ : Polynomial L).degree = 2 := by compute_degree!
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root _ (by rw [hQdeg]; decide)
  have hs0 : s ^ 2 + V₁.a₁ * s - V₁.a₂ = 0 := by simpa [Polynomial.IsRoot] using hs
  set V₂ := VariableChange.mk 1 0 s 0 • V₁
  have hv₂ : V₂.a₂ = 0 := by
    rw [variableChange_a₂]
    simp only [Units.val_one, inv_one, one_pow, one_mul, mul_zero, add_zero]
    linear_combination -hs0
  have hv₃ : V₂.a₃ = 0 := by simp [V₂, variableChange_a₃, h₃]
  have hv₄ : V₂.a₄ = 0 := by simp [V₂, variableChange_a₄, h₃, h₄]
  have hv₆ : V₂.a₆ = 0 := by simp [V₂, variableChange_a₆, h₃, h₄, h₆]
  have hc₄ : V₂.a₁ ^ 4 = ι W.c₄ := by
    have hV₂c₄ : V₂.c₄ = ι W.c₄ := by simp [V₂, V₁, variableChange_c₄]
    rw [← hV₂c₄]
    simp only [c₄, b₂, b₄, hv₂, hv₃, hv₄]
    ring
  refine ⟨V₂, hv₂, hv₃, hv₄, hv₆, hc₄, ?_⟩
  rw [VariableChange.height_formalGroup_variableChange,
    VariableChange.height_formalGroup_variableChange, map_formalGroup, FormalGroup.height_map]

/-- **A nodal Weierstrass curve (`Δ = 0`, `c₄ ≠ 0`) in prime characteristic `p` has formal-group
height `1`.** -/
theorem height_formalGroup_eq_one_of_c₄_ne_zero [Fact p.Prime] [CharP K p] (hΔ : W.Δ = 0)
    (hc₄ : W.c₄ ≠ 0) : (formalGroup W).height p = 1 := by
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨V, hv₂, hv₃, hv₄, hv₆, hVc₄, hht⟩ :=
    W.exists_height_formalGroup_eq_of_Δ_eq_zero (p := p) hΔ
  have ha₁ : V.a₁ ≠ 0 := fun h0 ↦ hc₄ <|
    (map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).mp
      (by rw [← hVc₄, h0, zero_pow (by decide)])
  rw [hht, height_formalGroup_eq_one ha₁ hv₂ hv₃ hv₄ hv₆]

/-- **A cuspidal Weierstrass curve (`Δ = 0`, `c₄ = 0`) in characteristic `p` has formal-group height
`⊤`.** -/
theorem height_formalGroup_eq_top_of_c₄_eq_zero [CharP K p] (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    (formalGroup W).height p = ⊤ := by
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨V, hv₂, hv₃, hv₄, hv₆, hVc₄, hht⟩ :=
    W.exists_height_formalGroup_eq_of_Δ_eq_zero (p := p) hΔ
  have ha₁ : V.a₁ = 0 := (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp (by rw [hVc₄, hc₄, map_zero])
  rw [hht, height_formalGroup_eq_top ha₁ hv₂ hv₃ hv₄ hv₆]

/-- **Height `⊤` characterizes the cuspidal locus.** Over a field of prime characteristic `p`, the
formal group of a Weierstrass curve `W` has height `⊤` if and only if `W.c₄ = 0` and `W.Δ = 0`. -/
theorem height_formalGroup_eq_top_iff [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = ⊤ ↔ W.c₄ = 0 ∧ W.Δ = 0 := by
  refine ⟨fun htop ↦ ?_, fun ⟨hc₄, hΔ⟩ ↦ W.height_formalGroup_eq_top_of_c₄_eq_zero hΔ hc₄⟩
  have hΔ : W.Δ = 0 := by
    by_contra hΔ
    have : W.IsElliptic := ⟨IsUnit.mk0 _ hΔ⟩
    have hle := W.height_formalGroup_le_two (p := p)
    rw [htop] at hle
    exact absurd hle (by decide)
  refine ⟨?_, hΔ⟩
  by_contra hc₄
  have h1 := W.height_formalGroup_eq_one_of_c₄_ne_zero (p := p) hΔ hc₄
  rw [htop] at h1
  exact ENat.top_ne_one h1

/-- **Height at most `2` characterizes smooth-or-nodal Weierstrass curves.** Over a field of prime
characteristic `p`, `(formalGroup W).height p ≤ 2` holds if and only if `W.c₄ ≠ 0` or `W.Δ ≠ 0`. -/
theorem height_formalGroup_le_two_iff [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p ≤ 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  rw [← not_and_or, ← W.height_formalGroup_eq_top_iff (p := p)]
  refine ⟨fun hle htop ↦ ?_, fun hne ↦ ?_⟩
  · rw [htop] at hle
    exact absurd hle (by decide)
  · by_cases hΔ : W.Δ = 0
    · have hc₄ : W.c₄ ≠ 0 := fun hc₄ ↦ hne (W.height_formalGroup_eq_top_of_c₄_eq_zero hΔ hc₄)
      rw [W.height_formalGroup_eq_one_of_c₄_ne_zero hΔ hc₄]
      decide
    · have : W.IsElliptic := ⟨IsUnit.mk0 _ hΔ⟩
      exact W.height_formalGroup_le_two

/-- **Height `1` or `2` characterizes smooth-or-nodal Weierstrass curves.** Over a field of prime
characteristic `p`, `(formalGroup W).height p` is `1` or `2` if and only if `W.c₄ ≠ 0` or
`W.Δ ≠ 0`. -/
theorem height_formalGroup_eq_one_or_eq_two_iff [Fact p.Prime] [CharP K p] :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 ↔ W.c₄ ≠ 0 ∨ W.Δ ≠ 0 := by
  refine ⟨fun h ↦ W.height_formalGroup_le_two_iff.mp ?_, fun h ↦ ?_⟩
  · rcases h with h | h <;> rw [h]; decide
  · by_cases hΔ : W.Δ = 0
    · exact Or.inl (W.height_formalGroup_eq_one_of_c₄_ne_zero hΔ (h.resolve_right (not_not.mpr hΔ)))
    · have : W.IsElliptic := ⟨IsUnit.mk0 _ hΔ⟩
      exact W.height_formalGroup_eq_one_or_eq_two

end SingularHeight

end WeierstrassCurve
