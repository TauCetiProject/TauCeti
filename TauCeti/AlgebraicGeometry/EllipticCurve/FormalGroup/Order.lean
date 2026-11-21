/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.RingTheory.FormalGroup.ZSMul
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nilpotent.Lemmas
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Orders of multiplication series on Weierstrass formal groups

Let `W` be a Weierstrass curve over a commutative ring `R`, with formal group law
`Ê = formalGroup W` and multiplication-by-`n` series `[n]_Ê`. This file determines the order of
vanishing of `[n]_Ê` for elliptic curves and establishes sharp order bounds and cuspidal vanishing
for general Weierstrass curves:

* For an elliptic curve `W` over a field `K` and `n ≠ 0`, identifying the formal power series of
  the multiplication-by-`n` isogeny `[n]` with `[n]_Ê`
  (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`) and its order of vanishing with the inseparable
  degree (`TauCeti.Isogeny.order_formalSeries`) gives `ord [n]_Ê = deg_i [n]`
  (`WeierstrassCurve.order_zsmulSeries_formalGroup_of_ne_zero`,
  `WeierstrassCurve.order_nsmulSeries_formalGroup_of_ne_zero`). Reducing modulo a maximal ideal
  shows `[n]_Ê ≠ 0` over any nontrivial commutative ring
  (`WeierstrassCurve.zsmulSeries_formalGroup_ne_zero`,
  `WeierstrassCurve.nsmulSeries_formalGroup_ne_zero`).
* For a nodal Weierstrass curve over a field (`Δ = 0` and `c₄ ≠ 0`) and `m ≠ 0`, `[m]_Ê` has order
  at most `m` (`WeierstrassCurve.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero`).
* Over an arbitrary commutative ring `R`, whenever `¬ IsNilpotent W.c₄ ∨ ¬ IsNilpotent W.Δ` (so at
  least one residue-field fiber is smooth or nodal) and `m ≠ 0`, `[m]_Ê` has order at most `m²`
  (`WeierstrassCurve.order_nsmulSeries_formalGroup_le_sq_of_not_isNilpotent`), and in particular
  over any reduced commutative ring whenever `W.c₄ ≠ 0 ∨ W.Δ ≠ 0`
  (`WeierstrassCurve.order_nsmulSeries_formalGroup_le_sq`).
* Over a reduced commutative ring `R`, if `Δ = 0`, `c₄ = 0`, and `(m : R) = 0`, then `[m]_Ê = 0`
  (`WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.4 and IV.7.
-/

public section

open TauCeti.Isogeny

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê` (`n : ℤ`, `n ≠ 0`) is the inseparable degree of `[n]`.** -/
theorem order_zsmulSeries_formalGroup_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← (formalSeries_mulByIntIsogeny W _ :
      (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = _), order_formalSeries]

/-- **The order of `[n]_Ê` (`n : ℕ`, `n ≠ 0`) is the inseparable degree of `[n]`.** -/
theorem order_nsmulSeries_formalGroup_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero_natCast W hn, order_formalSeries]

private theorem zsmulSeries_formalGroup_ne_zero_of_field {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [← (formalSeries_mulByIntIsogeny W _ :
      (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = _)]
  exact (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries_ne_zero

end Field

section NontrivialRing

variable {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **For `n ≠ 0` (`n : ℤ`), multiplication by `n` on the formal group of an elliptic curve over a
nontrivial commutative ring is nonzero.** -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set π := Ideal.Quotient.mk 𝔪
  intro h0
  apply zsmulSeries_formalGroup_ne_zero_of_field (W.map π) hn
  rw [map_formalGroup, ← FormalGroup.map_zsmulSeries, h0, map_zero]

/-- **For `n ≠ 0` (`n : ℕ`), multiplication by `n` on the formal group of an elliptic curve over a
nontrivial commutative ring is nonzero.** -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← FormalGroup.zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (mod_cast hn)

end NontrivialRing

section OrderBounds

/-- Over the algebraic closure, a singular Weierstrass curve (`Δ = 0`) can be transformed by a
change of variables into `y² + a x y = x³` with `a⁴ = c₄`, preserving the order of `[m]_Ê`. -/
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
    calc
      φ.inseparableDegree = 1 * φ.inseparableDegree := (one_mul _).symm
      _ ≤ φ.separableDegree * φ.inseparableDegree :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt φ.separableDegree_pos)
      _ = m ^ 2 := by
        rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
          Int.natAbs_natCast]

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

private theorem ker_algebraMap_comp_mk {R : Type*} [CommRing R] (P : Ideal R) :
    RingHom.ker ((algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))),
    Ideal.mk_ker]

/-- **Order bound for `[m]_Ê` under non-nilpotency**: over any commutative ring `R`, if
`¬ IsNilpotent W.c₄ ∨ ¬ IsNilpotent W.Δ` (so at least one residue-field fiber is smooth or nodal)
and `m ≠ 0`, then the multiplication-by-`m` series has order at most `m²`. -/
theorem order_nsmulSeries_formalGroup_le_sq_of_not_isNilpotent {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {m : ℕ} (hm : m ≠ 0) (h : ¬ IsNilpotent W.c₄ ∨ ¬ IsNilpotent W.Δ) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) := by
  have hex : ∃ P : Ideal R, P.IsPrime ∧ (W.c₄ ∉ P ∨ W.Δ ∉ P) := by
    by_contra hall
    push Not at hall
    have hnil (x : R) (hx : ∀ P : Ideal R, P.IsPrime → x ∈ P) : IsNilpotent x := by
      rw [← mem_nilradical, nilradical_eq_sInf]
      exact Ideal.mem_sInf.mpr fun P hP ↦ hx P hP
    exact h.elim (fun hc₄ ↦ hc₄ (hnil _ fun P hP ↦ (hall P hP).1))
      (fun hΔ ↦ hΔ (hnil _ fun P hP ↦ (hall P hP).2))
  obtain ⟨P, hP, hPmem⟩ := hex
  let _ : P.IsPrime := hP
  let f : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hf_ne {x : R} (hx : x ∉ P) : f x ≠ 0 := by
    rwa [ne_eq, ← RingHom.mem_ker, ker_algebraMap_comp_mk P]
  have hmap : (W.map f).c₄ ≠ 0 ∨ (W.map f).Δ ≠ 0 :=
    hPmem.imp (fun hc₄ ↦ by rw [map_c₄]; exact hf_ne hc₄) (fun hΔ ↦ by rw [map_Δ]; exact hf_ne hΔ)
  calc
    ((formalGroup W).nsmulSeries m).order
      ≤ (PowerSeries.map f ((formalGroup W).nsmulSeries m)).order := PowerSeries.le_order_map f
    _ = ((formalGroup (W.map f)).nsmulSeries m).order := by
        rw [FormalGroup.map_nsmulSeries, ← map_formalGroup]
    _ ≤ (m ^ 2 : ℕ) := order_nsmulSeries_formalGroup_le_sq_field (W.map f) hm hmap

/-- **Order bound for `[m]_Ê` over reduced rings**: over a reduced commutative ring, whenever
`c₄ ≠ 0 ∨ Δ ≠ 0` (so at least one residue-field fiber is smooth or nodal) and `m ≠ 0`, the
multiplication-by-`m` series has order at most `m²`. -/
theorem order_nsmulSeries_formalGroup_le_sq {R : Type*} [CommRing R] [IsReduced R]
    (W : WeierstrassCurve R) {m : ℕ} (hm : m ≠ 0) (h : W.c₄ ≠ 0 ∨ W.Δ ≠ 0) :
    ((formalGroup W).nsmulSeries m).order ≤ (m ^ 2 : ℕ) :=
  W.order_nsmulSeries_formalGroup_le_sq_of_not_isNilpotent hm
    (h.imp (fun hc₄ ↦ by simpa) (fun hΔ ↦ by simpa))

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
  exact ker_algebraMap_comp_mk P ▸ RingHom.mem_ker.mpr hk

end OrderBounds

end WeierstrassCurve

end
