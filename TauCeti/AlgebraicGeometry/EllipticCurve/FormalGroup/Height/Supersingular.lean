/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree

/-!
# Formal-group height and supersingularity of elliptic curves at every prime

Let `W` be an elliptic curve over a field `K`, with formal group law `Ê = formalGroup W`.
Identifying the formal power series of the multiplication-by-`n` isogeny `[n]` with `(formalGroup
W).zsmulSeries n` (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`) and reading its order of
vanishing off the inseparable degree of `[n]` (`TauCeti.Isogeny.order_formalSeries`) gives
`ord [n]_Ê = deg_i [n]` for every `n ≠ 0`. In particular `[n]_Ê ≠ 0`.

When `K` has prime characteristic `p`, multiplication by `p` has total degree `p²` and factors as
`[p] = V ∘ F` with `F` purely inseparable of degree `p` and `V` of prime degree `p`. Comparing
`deg_s [p] * deg_i [p] = p²` with the Verschiebung criteria of
`TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular` yields the
complete formal-group height stratification at every prime `p` (including `p = 2` and `p = 3`,
Silverman V.3.1):

* `W` is ordinary at `p` if and only if `Ê` has height `1`, equivalently if and only if the
  coefficient of `T ^ (p - 1)` in the invariant differential of `Ê` is nonzero;
* `W` is supersingular at `p` if and only if `Ê` has height `2`, equivalently if and only if its
  height exceeds `1`, equivalently if and only if the coefficient of `T ^ (p - 1)` in the invariant
  differential vanishes;
* the formal group of an elliptic curve in characteristic `p` always has height `1` or `2`
  (never `⊤` and never `≥ 3`).

Because every isogeny `φ : W₁ → W₂` induces a nonzero formal-group homomorphism
`φ.formalGroupHom : FormalGroupHom (formalGroup W₁) (formalGroup W₂)`, formal-group height — and
hence ordinarity and supersingularity — are invariant under arbitrary isogenies.

Finally, for an elliptic curve `W` over an arbitrary commutative ring `R` and any prime `p`,
reducing modulo maximal ideals shows that the Landweber height ideals `I_n(Ê)` equal the unit ideal
for all `n ≥ 3` (`WeierstrassCurve.heightIdeal_formalGroup_eq_top`), and consequently the
coefficient `v₂` of `X ^ (p ^ 2)` in `[p]_Ê` is a unit in `R ⧸ I₂(Ê)`
(`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_two`). Thus the sequence `(p, v₁, v₂)`
truncates at height two over any elliptic curve over any base ring.

## Main results

* `TauCeti.Isogeny.order_nsmulSeries_formalGroup_eq`,
  `TauCeti.Isogeny.order_zsmulSeries_formalGroup_eq`, and `TauCeti.Isogeny.height_formalGroup_eq`:
  isogenous elliptic curves have multiplication series of equal order and equal formal-group height.
* `WeierstrassCurve.order_zsmulSeries_formalGroup_of_ne_zero` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup_of_ne_zero`: for `n ≠ 0`, the order of `[n]_Ê` is
  the inseparable degree of `[n]`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one` and
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: an elliptic curve in prime
  characteristic `p` is ordinary iff `height p Ê = 1` and supersingular iff `height p Ê = 2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve in prime
  characteristic `p` has height `1` or `2`.
* `TauCeti.Isogeny.isSupersingular_iff` and `TauCeti.Isogeny.isOrdinary_iff`: supersingularity and
  ordinarity are invariant under arbitrary isogenies.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_two`: over any commutative ring `R`,
  `I_n(formalGroup W) = ⊤` for all `n ≥ 3`, and `v₂` becomes a unit modulo `I₂(formalGroup W)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7 and V.3.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §12.4.
-/

public section

open TauCeti.Isogeny

/-! ### Order of `[n]_Ê` and formal-group height of elliptic curves over fields -/

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê` (`n : ℤ`, `n ≠ 0`) is the inseparable degree of `[n]`.** -/
theorem order_zsmulSeries_formalGroup_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn, order_formalSeries]

/-- **The order of `[n]_Ê` (`n : ℕ`, `n ≠ 0`) is the inseparable degree of `[n]`.** -/
theorem order_nsmulSeries_formalGroup_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero_natCast W hn, order_formalSeries]

/-- **For `n ≠ 0` (`n : ℤ`), multiplication by `n` on the formal group of an elliptic curve over a
field is nonzero.** -/
theorem zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn]
  exact (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries_ne_zero

/-- **For `n ≠ 0` (`n : ℕ`), multiplication by `n` on the formal group of an elliptic curve over a
field is nonzero.** -/
theorem nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero_natCast W hn]
  exact (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).formalSeries_ne_zero

/-- **For `p ≠ 0`, the formal group of an elliptic curve over a field has finite `p`-height.** -/
theorem height_formalGroup_ne_top {p : ℕ} (hp : p ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [Ne, FormalGroup.height_eq_top_iff]
  exact W.nsmulSeries_formalGroup_ne_zero hp

section CharP

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- **An elliptic curve in prime characteristic `p` is ordinary if and only if its formal group has
height `1`** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  set φ := mulByIntIsogenyOfNeZero W.toAffine (n := p) (mod_cast hp.out.ne_zero)
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out,
    ← Nat.cast_one, FormalGroup.height_eq_natCast_iff, pow_one,
    W.order_nsmulSeries_formalGroup_of_ne_zero hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  have hp0 : p ≠ 0 := hp.out.ne_zero
  constructor <;> intro h
  · rw [h, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) hdeg
  · rw [h, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp0) hdeg

/-- **An elliptic curve in prime characteristic `p` is supersingular if and only if its formal group
has height `2`** (Silverman V.3.1). -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have : ExpChar K p := .prime hp.out
  set φ := mulByIntIsogenyOfNeZero W.toAffine (n := p) (mod_cast hp.out.ne_zero)
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  have h2 : (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) := rfl
  rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p, h2,
    FormalGroup.height_eq_natCast_iff, W.order_nsmulSeries_formalGroup_of_ne_zero hp.out.ne_zero,
    Nat.cast_inj (R := ℕ∞)]
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  constructor <;> intro h
  · rwa [h, one_mul] at hdeg
  · rw [h] at hdeg
    exact (Nat.mul_eq_right hp2.ne').mp hdeg

/-- **The formal group of an elliptic curve in prime characteristic `p` has height `1` or `2`.** -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsSupersingular p
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (W.not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve in prime characteristic `p` has height at most `2`.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h
  · rw [h]
    exact one_le_two
  · rw [h]

/-- **An elliptic curve in prime characteristic `p` is supersingular if and only if its formal group
has height strictly greater than `1`.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **An elliptic curve in prime characteristic `p` is ordinary if and only if the coefficient of
`T ^ (p - 1)` in the invariant differential of its formal group is nonzero** (Hasse invariant
criterion, Silverman V.4.1). -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [isOrdinary_iff_height_formalGroup_eq_one, height_formalGroup_eq_one_iff]

/-- **An elliptic curve in prime characteristic `p` is supersingular if and only if the coefficient
of `T ^ (p - 1)` in the invariant differential of its formal group vanishes.** -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

end CharP

end Field

end WeierstrassCurve

/-! ### Invariance under arbitrary isogenies -/

namespace TauCeti.Isogeny

open WeierstrassCurve

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- **Isogenous elliptic curves have `[n]_Ê` series of equal order** (`n : ℕ`). -/
theorem order_nsmulSeries_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (n : ℕ) :
    ((formalGroup W₁).nsmulSeries n).order = ((formalGroup W₂).nsmulSeries n).order := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.formalGroupHom.order_nsmulSeries_eq (by simp [φ.formalSeries_ne_zero]) n

/-- **Isogenous elliptic curves have `[n]_Ê` series of equal order** (`n : ℤ`). -/
theorem order_zsmulSeries_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (n : ℤ) :
    ((formalGroup W₁).zsmulSeries n).order = ((formalGroup W₂).zsmulSeries n).order := by
  have : W₁.IsElliptic := φ.isElliptic
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp [φ.order_nsmulSeries_formalGroup_eq k]
  · have hinv (W : WeierstrassCurve K) : ((formalGroup W).addInvX).order = 1 := by
      rw [← Nat.cast_one, PowerSeries.order_eq_nat]
      refine ⟨by simp, fun i hi ↦ ?_⟩
      rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (formalGroup W).constantCoeff_addInvX
    rw [FormalGroup.zsmulSeries_neg, FormalGroup.zsmulSeries_neg, FormalGroup.zsmulSeries_natCast,
      FormalGroup.zsmulSeries_natCast,
      PowerSeries.order_subst ((formalGroup W₁).constantCoeff_nsmulSeries k),
      PowerSeries.order_subst ((formalGroup W₂).constantCoeff_nsmulSeries k),
      hinv W₁, hinv W₂, mul_one, mul_one]
    exact φ.order_nsmulSeries_formalGroup_eq k

/-- **Isogenous elliptic curves have the same formal-group height.** -/
theorem height_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (formalGroup W₁).height p = (formalGroup W₂).height p := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.formalGroupHom.height_eq (by simp [φ.formalSeries_ne_zero]) p

/-- **Supersingularity is invariant under arbitrary isogenies** in exponential characteristic `p`.
-/
theorem isSupersingular_iff (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) [ExpChar K p] :
    W₁.IsSupersingular p ↔ W₂.IsSupersingular p := by
  -- In characteristic zero (`p = 1`) both curves have trivial `1`-torsion; in prime characteristic
  -- `p` the criterion `isSupersingular_iff_height_formalGroup_eq_two` reduces to
  -- `height_formalGroup_eq`.
  have : W₁.IsElliptic := φ.isElliptic
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · simp [WeierstrassCurve.isSupersingular_iff_forall, one_nsmul]
  · have : Fact p.Prime := ⟨hp⟩
    rw [W₁.isSupersingular_iff_height_formalGroup_eq_two,
      W₂.isSupersingular_iff_height_formalGroup_eq_two, φ.height_formalGroup_eq p]

/-- **Ordinarity is invariant under arbitrary isogenies** in exponential characteristic `p`. -/
theorem isOrdinary_iff (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) [ExpChar K p] :
    W₁.IsOrdinary p ↔ W₂.IsOrdinary p := by
  rw [← W₁.not_isSupersingular, ← W₂.not_isSupersingular, φ.isSupersingular_iff p]

end TauCeti.Isogeny

/-! ### Truncation of Landweber height ideals over arbitrary commutative rings -/

namespace WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **Over any commutative ring `R`, the Landweber height ideals `I_n(formalGroup W)` at a prime
`p` equal the unit ideal for all `n ≥ 3`.** -/
theorem heightIdeal_formalGroup_eq_top {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  -- If `I_n(Ê) ≤ 𝔪` for a maximal ideal `𝔪`, then `R ⧸ 𝔪` has characteristic `p` (since
  -- `p ∈ I₁(Ê) ≤ I_n(Ê) ≤ 𝔪`) and `formalGroup (W.map π)` has height `≥ n ≥ 3`, contradicting
  -- `height_formalGroup_le_two`.
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set π := Ideal.Quotient.mk 𝔪
  have hp_mem : (p : R) ∈ 𝔪 := by
    have h1 : (p : R) ∈ (formalGroup W).heightIdeal p 1 := by
      rw [(formalGroup W).heightIdeal_one hp]
      exact Ideal.mem_span_singleton_self _
    exact hle ((formalGroup W).heightIdeal_mono (by omega : 1 ≤ n) h1)
  have hp0 : ((p : ℕ) : R ⧸ 𝔪) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]
    exact hp_mem
  have hchar : ringChar (R ⧸ 𝔪) = p := by
    have hdvd : ringChar (R ⧸ 𝔪) ∣ p := (ringChar.spec (R ⧸ 𝔪) p).mp hp0
    refine (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h1 ↦ ?_
    have : ((1 : ℕ) : R ⧸ 𝔪) = 0 := (ringChar.spec (R ⧸ 𝔪) 1).mpr (h1 ▸ dvd_rfl)
    simp at this
  have : CharP (R ⧸ 𝔪) p := hchar ▸ ringChar.charP (R ⧸ 𝔪)
  have : Fact p.Prime := ⟨hp⟩
  -- In `R ⧸ 𝔪`, the image of `I_n(formalGroup W)` is both `⊥` (since `I_n ≤ 𝔪`) and `⊤`
  -- (since `height p (formalGroup (W.map π)) ≤ 2 < n`).
  have hbot : ((formalGroup W).heightIdeal p n).map π = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hle
  have htop : ((formalGroup W).heightIdeal p n).map π = ⊤ := by
    rw [FormalGroup.map_heightIdeal, ← map_formalGroup,
      FormalGroup.heightIdeal_eq_top_iff_height_lt]
    exact (W.map π).height_formalGroup_le_two.trans_lt
      (by exact_mod_cast (by omega : 2 < n))
  exact bot_ne_top (hbot.symm.trans htop)

/-- **The height-two coefficient `v₂ = [X ^ (p ^ 2)] [p]_Ê` is a unit modulo `I₂(formalGroup W)`**
for every elliptic curve `W` over every commutative ring `R` and every prime `p`. That is, on the
closed subscheme `Spec (R ⧸ I₂(Ê))` where `p` and `v₁` vanish, `v₂` is invertible. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_two {p : ℕ} (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  set I₂ := (formalGroup W).heightIdeal p 2
  set v₂ := PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p)
  have htop : I₂ ⊔ Ideal.span {v₂} = ⊤ := by
    rw [← (formalGroup W).heightIdeal_succ hp 2]
    exact W.heightIdeal_formalGroup_eq_top hp le_rfl
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
  obtain ⟨i, hi, j, hj, hij⟩ := htop
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  refine .of_mul_eq_one (Ideal.Quotient.mk I₂ a) ?_
  have hq := congrArg (Ideal.Quotient.mk I₂) hij
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_add, map_mul, mul_comm, map_one] at hq
  exact hq

end Ring

end WeierstrassCurve

end
