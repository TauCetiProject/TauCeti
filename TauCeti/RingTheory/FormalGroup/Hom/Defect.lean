/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.FormalGroup.Obstruction
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Homomorphisms of formal group laws modulo a degree

Let `F` and `G` be formal group laws over a commutative ring `R`. The homomorphism defect
`Φ(X, Y) = g(F(X, Y)) - G(g(X), g(Y))` (`FormalGroup.homDefect`) of a power series `g` with zero
constant term vanishes exactly when `g` is a homomorphism from `F` to `G`. When `Φ` has order at
least `n`, the series `g` is a homomorphism up to terms of degree `n`. This file builds such
approximate homomorphisms degree by degree, following Lazard's proof that formal group laws over
a separably closed field are classified by their height.

Suppose that `F` and `G` are commutative and that `Φ` vanishes below degree `n ≥ 2`. Then the
degree-`n` part of `Φ` is `r C_n` for the Lazard cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`
(`FormalGroup.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle`).

* If `d_n` is a unit in `R`, replacing `g` by `g - r d_n⁻¹ Xⁿ` makes the defect vanish below
  degree `n + 1` (`FormalGroup.exists_succ_le_order_homDefect_sub_smul_X_pow`). This applies to
  every `n` that is not a power of `p` when `p = 0` in `R`.
* If `p` is a prime with `p = 0` in `R` and `n = pᵏ` with `k ≥ 1`, the coefficient `r` is the
  coefficient of `Xⁿ` in `[p]_G(g(X)) - g([p]_F(X))`
  (`FormalGroup.homogeneousComponent_homDefect_eq_smul_lazardCocycle`).
  For `g = X + ⋯`, if `[p]_F` and `[p]_G` have order at least `n` and the same coefficient of `Xⁿ`,
  then `r = 0` (`FormalGroup.succ_le_order_homDefect_of_coeff_nsmulSeries_eq`).

Starting from `g = X`, these two steps reach every degree up to `pʰ` when the `p`-series of `F`
and `G` have order at least `pʰ` and the same coefficient of `X^(pʰ)`: then some `g = X + ⋯` is a
homomorphism from `F` to `G` up to terms of degree greater than `pʰ`
(`FormalGroup.exists_le_order_homDefect_of_coeff_nsmulSeries_eq`). Over a field of
characteristic `p` this applies to two formal group laws of height `h` whose `p`-series have the
same leading coefficient. In the degrees `pᵏ` with `k > h` the obstruction no longer vanishes
automatically; over a separably closed field it is removed by solving an Artin–Schreier type
equation. Those degrees are not treated in this file.

## Main results

* `FormalGroup.le_order_homDefect_sub_smul_X_pow`,
  `FormalGroup.homogeneousComponent_homDefect_sub_smul_X_pow`: subtracting `c Xⁿ` from `g`
  subtracts `c ((X + Y)ⁿ - Xⁿ - Yⁿ)` from the degree-`n` part of the defect.
* `FormalGroup.exists_succ_le_order_homDefect_sub_smul_X_pow`: in a degree `n` with `d_n` a unit,
  the defect can be removed by subtracting a multiple of `Xⁿ`.
* `FormalGroup.succ_le_order_homDefect_of_coeff_nsmulSeries_eq`: in a degree `pᵏ` where both
  `p`-series have order at least `pᵏ` and the same coefficient of `X^(pᵏ)`, the defect of
  `g = X + ⋯` vanishes automatically.
* `FormalGroup.exists_le_order_homDefect_of_coeff_nsmulSeries_eq`: commutative formal group laws
  whose `p`-series have order at least `pʰ` and the same coefficient of `X^(pʰ)` are strictly
  isomorphic up to degree `pʰ`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74 (1968).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.2.
-/

public section

namespace FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R]

section Leading

variable {F G : FormalGroup R}

/-- Subtracting `c Xⁿ` from `g` keeps the homomorphism defect zero below degree `n` if it was, and
subtracts `c ((X + Y)ⁿ - Xⁿ - Yⁿ)` from its degree-`n` part. -/
private theorem homDefect_sub_smul_X_pow {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (c : R) :
    ((n : ℕ∞) ≤ (homDefect F G g).order →
      (n : ℕ∞) ≤ (homDefect F G (g - c • PowerSeries.X ^ n)).order) ∧
      homogeneousComponent n (homDefect F G (g - c • PowerSeries.X ^ n)) =
        homogeneousComponent n (homDefect F G g) -
          ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
            MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hQc : homogeneousComponent n (F.homDefect 𝔾ₐ (c • PowerSeries.X ^ n)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
    simpa using F.homogeneousComponent_homDefect_add_sub (G := 𝔾ₐ)
      (f := 0) (by simp) hn₀ c
  set e : PowerSeries R := c • PowerSeries.X ^ n
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have he₀ : PowerSeries.constantCoeff e = 0 := by simp [e, hn₀]
  have hQe := F.homDefect_𝔾ₐ (f := e)
  have hen : (n : ℕ∞) ≤ e.order :=
    PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [e, PowerSeries.coeff_X_pow, hi.ne]
  have hsub (i : Fin 2) : constantCoeff (PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) g) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) g hg
  have hsube (x : MvPowerSeries (Fin 2) R) (hx : constantCoeff x = 0) :
      (n : ℕ∞) ≤ (PowerSeries.subst x e).order :=
    hen.trans (PowerSeries.le_order_subst_left hx)
  set g₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) g
  set g₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) g
  set e₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) e
  set e₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) e
  -- subtracting `e₀` and `e₁` from the arguments of `G` subtracts them from `G(g₀, g₁)`
  have h₀ := G.le_order_subst_add_left_sub (x := g₀) (y := g₁ - e₁) (e := -e₀) (hsub 0)
    (by rw [map_sub, hsub 1, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) e he₀,
      sub_zero]) hn₀ (by rw [order_neg]; exact hsube _ (constantCoeff_X 0))
  have h₁ := G.le_order_subst_add_right_sub (x := g₀) (y := g₁) (e := -e₁) (hsub 0) (hsub 1) hn₀
    (by rw [order_neg]; exact hsube _ (constantCoeff_X 1))
  rw [← sub_eq_add_neg] at h₀ h₁
  -- the remaining change is the additivity defect of `e` along `F`
  have hQ := F.le_order_homDefect_𝔾ₐ hen
  have heq : homDefect F G (g - e) = homDefect F G g - F.homDefect 𝔾ₐ e -
      (G.toPowerSeries.subst ![g₀ - e₀, g₁ - e₁] - G.toPowerSeries.subst ![g₀, g₁ - e₁] - -e₀) -
      (G.toPowerSeries.subst ![g₀, g₁ - e₁] - G.toPowerSeries.subst ![g₀, g₁] - -e₁) := by
    rw [hQe, homDefect_eq_sub_subst_pair F G (g - e), homDefect_eq_sub_subst_pair F G g,
      PowerSeries.subst_sub hF, PowerSeries.subst_sub (hX 0), PowerSeries.subst_sub (hX 1)]
    ring
  have hlt (f : MvPowerSeries (Fin 2) R) (hf : ((n + 1 : ℕ) : ℕ∞) ≤ f.order) :
      (n : ℕ∞) ≤ f.order :=
    (Nat.cast_le.mpr (Nat.le_succ n)).trans hf
  have hzero (f : MvPowerSeries (Fin 2) R) (hf : ((n + 1 : ℕ) : ℕ∞) ≤ f.order) :
      homogeneousComponent n f = 0 :=
    homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr (Nat.lt_succ_self n)).trans_le hf)
  rw [heq]
  refine ⟨fun hn ↦ le_order_sub (le_order_sub (le_order_sub hn hQ) (hlt _ h₀)) (hlt _ h₁), ?_⟩
  rw [map_sub, map_sub, map_sub, hzero _ h₀, hzero _ h₁, hQc, sub_zero, sub_zero]

/-- If the homomorphism defect of `g` vanishes below degree `n ≠ 0`, so does that of `g - c Xⁿ`. -/
theorem le_order_homDefect_sub_smul_X_pow {n : ℕ} (hn₀ : n ≠ 0) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) (c : R) :
    (n : ℕ∞) ≤ (homDefect F G (g - c • PowerSeries.X ^ n)).order :=
  (homDefect_sub_smul_X_pow hn₀ hg c).1 hn

/-- **Correcting the leading defect.** For `n ≠ 0`, subtracting `c Xⁿ` from `g` subtracts
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)` from the degree-`n` part of the homomorphism defect. -/
theorem homogeneousComponent_homDefect_sub_smul_X_pow {n : ℕ} (hn₀ : n ≠ 0)
    {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0) (c : R) :
    homogeneousComponent n (homDefect F G (g - c • PowerSeries.X ^ n)) =
      homogeneousComponent n (homDefect F G g) -
        ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
          MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) :=
  (homDefect_sub_smul_X_pow hn₀ hg c).2

end Leading

section Step

variable {F G : FormalGroup R} [F.IsComm] [G.IsComm]

/-- **Correcting the defect in degrees with invertible `d_n`.** Let `F` and `G` be commutative and
let the homomorphism defect of `g` vanish below degree `n ≥ 2`. If `d_n = TauCeti.lazardGcd n` is a
unit in `R`, for instance if `n` is not a power of a prime `p` with `p = 0` in `R`, then for some
`c` the defect of `g - c Xⁿ` vanishes below degree `n + 1`. -/
theorem exists_succ_le_order_homDefect_sub_smul_X_pow {n : ℕ} (hn₂ : 2 ≤ n)
    (hd : IsUnit (TauCeti.lazardGcd n : R)) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (homDefect F G g).order) :
    ∃ c : R, ((n + 1 : ℕ) : ℕ∞) ≤ (homDefect F G (g - c • PowerSeries.X ^ n)).order := by
  obtain ⟨r, hr⟩ := exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle hg (by omega) hn
  -- `r C_n = (r d_n⁻¹) ((X + Y)ⁿ - Xⁿ - Yⁿ)`
  have hc : r • TauCeti.lazardCocycle n R =
      (r * ↑hd.unit⁻¹) • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R) := by
    rw [← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega), ← Nat.cast_smul_eq_nsmul R,
      smul_smul, mul_assoc, hd.val_inv_mul, mul_one]
  refine ⟨_, succ_le_order_of_homogeneousComponent_eq_zero
    (le_order_homDefect_sub_smul_X_pow (by omega) hg hn (r * ↑hd.unit⁻¹)) ?_⟩
  rw [homogeneousComponent_homDefect_sub_smul_X_pow (by omega) hg, hr, hc, sub_self]

/-- **No defect in degree `pᵏ` when the `p`-series agree.** Let `F` and `G` be commutative and let
the homomorphism defect of `g = X + ⋯` vanish below degree `n = pᵏ`, `k ≥ 1`. If the `p`-series of
`F` and `G` both have order at least `n` and the same coefficient of `Xⁿ`, the defect of `g`
vanishes below degree `n + 1`. -/
theorem succ_le_order_homDefect_of_coeff_nsmulSeries_eq {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ≠ 0) {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hg₁ : PowerSeries.coeff 1 g = 1) (hn : ((p ^ k : ℕ) : ℕ∞) ≤ (homDefect F G g).order)
    (hF : ((p ^ k : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ k : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ k) (G.nsmulSeries p)) :
    ((p ^ k + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g).order := by
  have hn₀ : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have hn₂ : 2 ≤ p ^ k := Nat.one_lt_pow hk hp.one_lt
  -- `p` is the linear coefficient of `[p]_F`, which vanishes
  have hpR : (p : R) = 0 :=
    F.natCast_eq_zero_of_two_le_order_nsmulSeries ((Nat.cast_le.mpr hn₂).trans hF)
  -- since `g = X + ⋯`, the coefficients of `X^(pᵏ)` in `[p]_G(g(X))` and `g([p]_F(X))` are those
  -- of `[p]_G` and `[p]_F`
  have hG' := congrArg (MvPowerSeries.coeff (Finsupp.single () (p ^ k)))
    (PowerSeries.homogeneousComponent_subst_left_eq_C_mul_X_pow hG hg hg₁)
  have hF' := congrArg (MvPowerSeries.coeff (Finsupp.single () (p ^ k)))
    (PowerSeries.homogeneousComponent_subst_right_eq_C_mul_X_pow hn₀ hF hg hg₁)
  simp only [coeff_homogeneousComponent, Finsupp.degree_single, ↓reduceIte, coeff_C_mul,
    coeff_X_pow, mul_one, Algebra.algebraMap_self, RingHom.id_apply] at hG' hF'
  rw [← PowerSeries.coeff_def Finsupp.single_eq_same] at hG' hF'
  refine succ_le_order_of_homogeneousComponent_eq_zero hn ?_
  rw [homogeneousComponent_homDefect_eq_smul_lazardCocycle hg hp hpR hk hn, map_sub, hG', hF',
    hFG, sub_self, zero_smul, MvPolynomial.coe_zero]

/-- The inductive step: a normalised `g` whose homomorphism defect vanishes below a degree
`2 ≤ n ≤ pʰ` can be modified in degree `n` so that its defect vanishes below degree `n + 1`. -/
private theorem exists_succ_le_order_homDefect {p : ℕ} (hp : p.Prime) {h : ℕ}
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ h : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ h) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ h) (G.nsmulSeries p))
    {n : ℕ} (hn₂ : 2 ≤ n) (hnh : n ≤ p ^ h) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hg₁ : PowerSeries.coeff 1 g = 1)
    (hn : n ≤ (homDefect F G g).order) :
    ∃ g' : PowerSeries R, PowerSeries.constantCoeff g' = 0 ∧ PowerSeries.coeff 1 g' = 1 ∧
      ((n + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g').order := by
  by_cases hpow : ∃ k, n = p ^ k
  · -- in degree `pᵏ` the defect vanishes, as both coefficients of `X^(pᵏ)` vanish below the height
    obtain ⟨k, rfl⟩ := hpow
    have hk₀ : k ≠ 0 := by
      rintro rfl
      simp at hn₂
    have hkh : k ≤ h := (Nat.pow_le_pow_iff_right hp.one_lt).mp hnh
    have hle (f : PowerSeries R) (hf : ((p ^ h : ℕ) : ℕ∞) ≤ f.order) :
        ((p ^ k : ℕ) : ℕ∞) ≤ f.order :=
      (Nat.cast_le.mpr hnh).trans hf
    have hcoeff : PowerSeries.coeff (p ^ k) (F.nsmulSeries p) =
        PowerSeries.coeff (p ^ k) (G.nsmulSeries p) := by
      rcases hkh.lt_or_eq with hlt | rfl
      · have hlt' : ((p ^ k : ℕ) : ℕ∞) < ((p ^ h : ℕ) : ℕ∞) :=
          Nat.cast_lt.mpr (Nat.pow_lt_pow_right hp.one_lt hlt)
        rw [PowerSeries.coeff_of_lt_order _ (hlt'.trans_le hF),
          PowerSeries.coeff_of_lt_order _ (hlt'.trans_le hG)]
      · exact hFG
    exact ⟨g, hg, hg₁, succ_le_order_homDefect_of_coeff_nsmulSeries_eq hp hk₀ hg hg₁ hn
      (hle _ hF) (hle _ hG) hcoeff⟩
  · -- otherwise `d_n` is prime to `p`, and `p = 0` in `R`, so `d_n` is a unit
    have hpR : (p : R) = 0 :=
      F.natCast_eq_zero_of_two_le_order_nsmulSeries ((Nat.cast_le.mpr (hn₂.trans hnh)).trans hF)
    obtain ⟨c, hc⟩ := exists_succ_le_order_homDefect_sub_smul_X_pow hn₂
      (TauCeti.isUnit_lazardGcd hp hpR (by omega) hpow) hg hn
    exact ⟨g - c • PowerSeries.X ^ n, by simp [hg, show n ≠ 0 by omega],
      by simp [hg₁, PowerSeries.coeff_X_pow, show 1 ≠ n by omega], hc⟩

/-- **Formal group laws with matching `p`-series agree up to degree `pʰ`.** Let `p` be a prime and
let `F` and `G` be commutative formal group laws over a commutative ring `R` whose `p`-series both
have order at least `pʰ` and the same coefficient of `X^(pʰ)`. Then some power series
`g = X + ⋯` is a homomorphism from `F` to `G` up to terms of degree greater than `pʰ`:
`g(F(X, Y)) - G(g(X), g(Y))` has order at least `pʰ + 1`.

Over a field of characteristic `p`, this applies to two formal group laws of height `h` whose
`p`-series have the same leading coefficient. -/
theorem exists_le_order_homDefect_of_coeff_nsmulSeries_eq {p : ℕ} (hp : p.Prime) {h : ℕ}
    (hF : ((p ^ h : ℕ) : ℕ∞) ≤ (F.nsmulSeries p).order)
    (hG : ((p ^ h : ℕ) : ℕ∞) ≤ (G.nsmulSeries p).order)
    (hFG : PowerSeries.coeff (p ^ h) (F.nsmulSeries p) =
      PowerSeries.coeff (p ^ h) (G.nsmulSeries p)) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      ((p ^ h + 1 : ℕ) : ℕ∞) ≤ (homDefect F G g).order := by
  have hph : 1 ≤ p ^ h := Nat.one_le_pow _ _ hp.pos
  -- by induction on `m`, the defect can be made to vanish below each degree `m + 2 ≤ pʰ + 1`
  suffices key : ∀ m, m + 1 ≤ p ^ h → ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧
      PowerSeries.coeff 1 g = 1 ∧ ((m + 2 : ℕ) : ℕ∞) ≤ (homDefect F G g).order by
    obtain ⟨g, hg⟩ := key (p ^ h - 1) (by omega)
    exact ⟨g, by rwa [show p ^ h - 1 + 2 = p ^ h + 1 by omega] at hg⟩
  intro m
  induction m with
  | zero =>
    -- the defect of `X` is `F(X, Y) - G(X, Y)`
    refine fun _ ↦ ⟨PowerSeries.X, PowerSeries.constantCoeff_X, PowerSeries.coeff_one_X, ?_⟩
    rw [homDefect_X, ← sub_sub_sub_cancel_right _ _ (X 0 + X 1)]
    exact le_order_sub (two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y)
      (two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y)
  | succ m ih =>
    intro hm
    obtain ⟨g, hg, hg₁, hgo⟩ := ih (by omega)
    exact exists_succ_le_order_homDefect hp hF hG hFG (by omega) (by omega) hg hg₁ hgo

end Step

end FormalGroup
