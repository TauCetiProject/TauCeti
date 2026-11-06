/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.RingTheory.FormalGroup.Frobenius.Factorization
public import TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight
import TauCeti.RingTheory.FormalGroup.Obstruction
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Classification of formal group laws by height

Let `K` be a separably closed field of characteristic `p`. Lazard's theorem: two commutative
formal group laws `F` and `G` over `K` are isomorphic exactly when they have the same height
(`FormalGroup.height_eq_height_iff_nonempty_formalGroupIso`). Isomorphic laws have the same height
by `TauCeti.FormalGroupIso.height_eq`, and in height `⊤` both are isomorphic to the additive law by
`FormalGroup.height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ`. This file treats finite height `h`,
writing `q = p ^ h`.

An isomorphism `f : F → G` is built degree by degree. Suppose the homomorphism defect
`Φ(X, Y) = f(F(X, Y)) - G(f(X), f(Y))` (`FormalGroup.homDefect`) vanishes below degree `n ≥ 2`.
Its degree-`n` part is `r C_n` for the Lazard cocycle `C_n`
(`FormalGroup.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle`), and replacing `f` by
`f + c Xⁿ` adds `c ((X + Y)ⁿ - Xⁿ - Yⁿ) = c d_n C_n` to it.

* If `n` is not a power of `p`, then `d_n` is a unit in `K` and a unique `c` cancels the defect.
* If `n = pᵏ`, then `d_n = p = 0` and adding `c Xⁿ` does not change the degree-`n` defect. Instead
  `r` is forced: `-r` is the coefficient of `Xⁿ` in `f([p]_F(X)) - [p]_G(f(X))`
  (`FormalGroup.homogeneousComponent_homDefect_eq_smul_lazardCocycle`). This series vanishes
  below degree `q`, and its coefficient of `X^(m q)` only involves the coefficients of `f` up to
  degree `m`. Since `[p]_G(X) = ψ(X^q)` for an isomorphism `ψ` (`FormalGroup.heightFrobeniusIso`),
  that coefficient changes by `c uᵐ - v c^q` when `f` is replaced by `f + c Xᵐ`, where `u`, `v` are
  the coefficients of `X^q` in `[p]_F`, `[p]_G`. So the free coefficient of `f` in degree `m = pʲ`
  can be chosen, as a root of a separable polynomial `-v x^q + uᵐ x + a`, to make the coefficient
  of `X^(m q)` vanish, and then `r = 0` in degree `pʲ q`. This is where separable closedness is
  used; the linear coefficient of `f` is a nonzero root of `x^(q - 1) = u / v`.

The defect is then zero in the limit, and `f` is an isomorphism since its linear coefficient is
nonzero. The case `G = 𝔾ₐ`, `[p]_F = 0` of the same obstruction argument constructs the normalised
logarithm in `TauCeti.RingTheory.FormalGroup.Logarithm.InfiniteHeight`.

## Main results

* `FormalGroup.height_eq_height_iff_nonempty_formalGroupIso`: over a separably closed field of
  characteristic `p`, commutative formal group laws are isomorphic exactly when their heights
  agree.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Chapter III, §2.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Theorem A2.2.11.
-/

public section

open MvPowerSeries

namespace FormalGroup

section Field

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] {F G : FormalGroup K}
  [F.IsComm] [G.IsComm] {h : ℕ}

/-- The failure `f([p]_F(X)) - [p]_G(f(X))` of `f` to commute with multiplication by `p`. -/
private noncomputable def pSeriesError (F G : FormalGroup K) (p : ℕ) (f : PowerSeries K) :
    PowerSeries K :=
  PowerSeries.subst (F.nsmulSeries p) f - PowerSeries.subst f (G.nsmulSeries p)

omit hp [CharP K p] [F.IsComm] [G.IsComm] in
/-- The `p`-series failure of zero vanishes. -/
private theorem pSeriesError_zero : pSeriesError F G p 0 = 0 := by
  rw [pSeriesError, PowerSeries.subst_zero, PowerSeries.subst_zero_of_constantCoeff_zero
    (G.constantCoeff_nsmulSeries p), sub_zero]

omit [CharP K p] [F.IsComm] [G.IsComm] in
/-- A series with zero constant coefficient has zero constant coefficient after raising to the
power `p ^ h`. -/
private theorem constantCoeff_pow_eq_zero (x : PowerSeries K)
    (hx : PowerSeries.constantCoeff x = 0) :
    constantCoeff (x ^ p ^ h : MvPowerSeries Unit K) = 0 := by
  rw [map_pow, ← PowerSeries.constantCoeff_eq, hx, zero_pow (pow_ne_zero h hp.out.ne_zero)]

omit [G.IsComm] in
/-- A formal group law of finite height `h` over a field of characteristic `p` has `h ≠ 0`. -/
private theorem ne_zero_of_height_eq (hF : F.height p = h) : h ≠ 0 := by
  have := F.one_le_height (p := p)
  rw [hF] at this
  exact_mod_cast (Nat.one_le_iff_ne_zero.mp (by exact_mod_cast this))

omit [G.IsComm] in
/-- The coefficient of `X ^ (p ^ h)` in `[p]_F` is nonzero when `F` has height `h`. -/
private theorem coeff_nsmulSeries_ne_zero (hF : F.height p = h) :
    PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ≠ 0 := by
  have := (F.heightFrobeniusIso hF).isUnit_coeff_one
  rwa [coeff_heightFrobeniusIso, mul_one, isUnit_iff_ne_zero] at this

omit [G.IsComm] in
/-- Composing `c Xᴹ` with `[p]_F` gives a series whose coefficient of `X ^ (M p ^ h)` is `c uᴹ`,
where `u` is the coefficient of `X ^ (p ^ h)` in `[p]_F`. -/
private theorem coeff_subst_nsmulSeries_smul_X_pow (hF : F.height p = h) (M : ℕ) (c : K) :
    PowerSeries.coeff (M * p ^ h) (PowerSeries.subst (F.nsmulSeries p)
      (c • PowerSeries.X ^ M : PowerSeries K)) =
        c * PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ M := by
  have hFp' := PowerSeries.HasSubst.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries p)
  have hdvd : PowerSeries.X ^ p ^ h ∣ F.nsmulSeries p :=
    PowerSeries.X_pow_dvd_iff.mpr fun m hm ↦ PowerSeries.coeff_of_lt_order m
      (by rw [F.height_eq_natCast_iff.mp hF]; exact_mod_cast hm)
  obtain ⟨w, hw⟩ := hdvd
  rw [PowerSeries.subst_smul hFp', PowerSeries.subst_pow hFp', PowerSeries.subst_X hFp', hw,
    mul_pow, ← pow_mul, PowerSeries.coeff_smul, mul_comm (p ^ h) M]
  simp [PowerSeries.coeff_X_pow_mul']

/-- The coefficients of `f([p]_F(X)) - [p]_G(f(X))` in degrees below `(M + 1) p ^ h` only depend
on the coefficients of `f` in degrees at most `M`. -/
private theorem le_order_pSeriesError_sub (hF : F.height p = h) (hG : G.height p = h)
    {f g : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) {M : ℕ} (hfg : (M : ℕ∞) ≤ (f - g).order) :
    ((M * p ^ h : ℕ) : ℕ∞) ≤ (pSeriesError F G p f - pSeriesError F G p g).order := by
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set ψ := (G.heightFrobeniusIso hG).toHom.toPowerSeries
  have hψ : constantCoeff (ψ : MvPowerSeries Unit K) = 0 :=
    (G.heightFrobeniusIso hG).toHom.zero_constantCoeff
  have hq₀ := constantCoeff_pow_eq_zero (K := K) (p := p) (h := h)
  -- `f(X) - g(X)` composed with `[p]_F`, of order `p ^ h`
  have h₁ : ((M * p ^ h : ℕ) : ℕ∞) ≤
      MvPowerSeries.order (PowerSeries.subst (F.nsmulSeries p) (f - g)) := by
    rw [← PowerSeries.order_eq_order, PowerSeries.order_subst (F.constantCoeff_nsmulSeries p),
      F.height_eq_natCast_iff.mp hF, mul_comm M]
    push_cast
    gcongr
  -- `ψ(f ^ (p ^ h)) - ψ(g ^ (p ^ h))`, where `f ^ (p ^ h) - g ^ (p ^ h) = (f - g) ^ (p ^ h)`
  have h₂ : ((M * p ^ h : ℕ) : ℕ∞) ≤ MvPowerSeries.order
      (PowerSeries.subst (f ^ p ^ h) ψ - PowerSeries.subst (g ^ p ^ h) ψ) := by
    have hpow : ((M * p ^ h : ℕ) : ℕ∞) ≤
        MvPowerSeries.order ((f ^ p ^ h - g ^ p ^ h : PowerSeries K)) := by
      rw [← sub_pow_char_pow, ← PowerSeries.order_eq_order]
      refine (PowerSeries.le_order_pow _ _).trans' ?_
      rw [nsmul_eq_mul, mul_comm M]
      push_cast
      gcongr
    simpa [PowerSeries.subst_def] using MvPowerSeries.le_order_subst_sub_subst (H := ψ) (k := 1)
      (one_le_order_iff_constCoeff_eq_zero.mpr hψ)
      (a := fun _ ↦ (f ^ p ^ h : PowerSeries K)) (b := fun _ ↦ (g ^ p ^ h : PowerSeries K))
      (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ f hf)
      (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ g hg) (fun _ ↦ hq₀ f hf) (fun _ ↦ hq₀ g hg)
      fun _ ↦ hpow
  have hsplit : pSeriesError F G p f - pSeriesError F G p g =
      PowerSeries.subst (F.nsmulSeries p) (f - g) -
        (PowerSeries.subst (f ^ p ^ h) ψ - PowerSeries.subst (g ^ p ^ h) ψ) := by
    rw [pSeriesError, pSeriesError, G.subst_nsmulSeries_eq_subst_pow_heightFrobeniusIso hG hf,
      G.subst_nsmulSeries_eq_subst_pow_heightFrobeniusIso hG hg,
      PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero'
        (F.constantCoeff_nsmulSeries p))]
    ring
  rw [hsplit, PowerSeries.order_eq_order]
  exact le_order_sub h₁ h₂

/-- **The `p`-series failure under a perturbation in degree `M`.** Replacing `f` by `f + c Xᴹ`
changes the coefficient of `X^(M p ^ h)` in `f([p]_F(X)) - [p]_G(f(X))` by `c uᴹ - v c^(p ^ h)`,
where `u` and `v` are the coefficients of `X^(p ^ h)` in `[p]_F` and `[p]_G`. -/
private theorem coeff_pSeriesError_add (hF : F.height p = h) (hG : G.height p = h)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {M : ℕ} (hM : M ≠ 0) (c : K) :
    PowerSeries.coeff (M * p ^ h) (pSeriesError F G p (f + c • PowerSeries.X ^ M)) =
      PowerSeries.coeff (M * p ^ h) (pSeriesError F G p f) +
        c * PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ M -
          PowerSeries.coeff (p ^ h) (G.nsmulSeries p) * c ^ p ^ h := by
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set q := p ^ h
  set ψ := (G.heightFrobeniusIso hG).toHom.toPowerSeries
  have hψ : constantCoeff (ψ : MvPowerSeries Unit K) = 0 :=
    (G.heightFrobeniusIso hG).toHom.zero_constantCoeff
  have hq₀ := constantCoeff_pow_eq_zero (K := K) (p := p) (h := h)
  have hcX : PowerSeries.constantCoeff (c • PowerSeries.X ^ M : PowerSeries K) = 0 := by
    simp [hM]
  have hfc : PowerSeries.constantCoeff (f + c • PowerSeries.X ^ M) = 0 := by
    rw [map_add, hf, hcX, _root_.add_zero]
  have hFp := F.constantCoeff_nsmulSeries p
  have hFp' := PowerSeries.HasSubst.of_constantCoeff_zero' hFp
  -- the perturbation composed with `[p]_F`: `c [p]_F ^ M`, whose coefficient is `c uᴹ`
  have hF₁ := coeff_subst_nsmulSeries_smul_X_pow hF M c
  -- `ψ((f + c Xᴹ) ^ q) - ψ(f ^ q) = ψ(f ^ q + c ^ q X^(M q)) - ψ(f ^ q)`, of coefficient `v c ^ q`
  have hdiff : (f + c • PowerSeries.X ^ M) ^ q - f ^ q =
      (c ^ q • PowerSeries.X ^ (M * q) : PowerSeries K) := by
    rw [add_pow_char_pow, smul_pow, ← pow_mul, add_sub_cancel_left]
  have hord : ((M * q : ℕ) : ℕ∞) ≤ MvPowerSeries.order
      ((f + c • PowerSeries.X ^ M) ^ q - f ^ q : PowerSeries K) := by
    rw [hdiff, ← PowerSeries.order_eq_order]
    exact PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
  have hG₁ := MvPowerSeries.coeff_subst_sub_subst_of_degree_le ψ
    (a := fun _ ↦ ((f + c • PowerSeries.X ^ M) ^ q : PowerSeries K))
    (b := fun _ ↦ (f ^ q : PowerSeries K))
    (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ _ hfc)
    (hasSubst_of_constantCoeff_zero fun _ ↦ hq₀ f hf) (fun _ ↦ hq₀ _ hfc) (fun _ ↦ hq₀ f hf)
    (fun _ ↦ hord) (e := Finsupp.single () (M * q)) (by simp)
  have hG₁' : PowerSeries.coeff (M * q) (PowerSeries.subst ((f + c • PowerSeries.X ^ M) ^ q) ψ -
      PowerSeries.subst (f ^ q) ψ) = PowerSeries.coeff 1 ψ * c ^ q := by
    rw [PowerSeries.coeff_def (by simp : Finsupp.single () (M * q) () = M * q),
      PowerSeries.subst_def, PowerSeries.subst_def, hG₁, Fintype.sum_unique, hdiff,
      ← PowerSeries.coeff_def (by simp : Finsupp.single () (M * q) () = M * q),
      ← PowerSeries.coeff_def (by simp : Finsupp.single (default : Unit) 1 () = 1)]
    simp
  have hv : PowerSeries.coeff 1 ψ = PowerSeries.coeff q (G.nsmulSeries p) := by
    rw [coeff_heightFrobeniusIso, mul_one]
  have hsplit : pSeriesError F G p (f + c • PowerSeries.X ^ M) - pSeriesError F G p f =
      PowerSeries.subst (F.nsmulSeries p) (c • PowerSeries.X ^ M : PowerSeries K) -
        (PowerSeries.subst ((f + c • PowerSeries.X ^ M) ^ q) ψ - PowerSeries.subst (f ^ q) ψ) := by
    rw [pSeriesError, pSeriesError, G.subst_nsmulSeries_eq_subst_pow_heightFrobeniusIso hG hf,
      G.subst_nsmulSeries_eq_subst_pow_heightFrobeniusIso hG hfc, PowerSeries.subst_add hFp']
    ring
  have h := congrArg (PowerSeries.coeff (M * q)) hsplit
  rw [map_sub, map_sub, hF₁, hG₁', hv] at h
  linear_combination h

/-- Below degree `p ^ h`, the `p`-series failure vanishes. -/
private theorem coeff_pSeriesError_of_lt (hF : F.height p = h) (hG : G.height p = h)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {n : ℕ} (hn : n < p ^ h) :
    PowerSeries.coeff n (pSeriesError F G p f) = 0 := by
  have hf₁ : (1 : ℕ∞) ≤ f.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf
  rw [pSeriesError, map_sub, PowerSeries.coeff_of_lt_order, PowerSeries.coeff_of_lt_order,
    sub_zero]
  · rw [PowerSeries.order_subst hf, G.height_eq_natCast_iff.mp hG]
    calc (n : ℕ∞) < (p ^ h : ℕ) := by exact_mod_cast hn
      _ = 1 * (p ^ h : ℕ) := (one_mul _).symm
      _ ≤ f.order * (p ^ h : ℕ) := by gcongr
  · rw [PowerSeries.order_subst (F.constantCoeff_nsmulSeries p), F.height_eq_natCast_iff.mp hF]
    calc (n : ℕ∞) < (p ^ h : ℕ) := by exact_mod_cast hn
      _ = (p ^ h : ℕ) * 1 := (mul_one _).symm
      _ ≤ (p ^ h : ℕ) * f.order := by gcongr

/-- If `N + 1 = pᵏ` with `k ≠ 0`, the `p`-series failure vanishing in degrees `pʲ p ^ h` with
`pʲ ≤ N` forces the degree-`N + 1` part of the homomorphism defect to vanish. -/
private theorem homogeneousComponent_homDefect_eq_zero_of_pow (hF : F.height p = h)
    (hG : G.height p = h) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {N k : ℕ}
    (hN : N ≠ 0) (hk : N + 1 = p ^ k) (hΦ : ((N + 1 : ℕ) : ℕ∞) ≤ (F.homDefect G f).order)
    (hP : ∀ j, p ^ j ≤ N → PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p f) = 0) :
    homogeneousComponent (N + 1) (F.homDefect G f) = 0 := by
  have hp' := hp.out
  have hh := ne_zero_of_height_eq hF
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hk₀ : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk
    omega
  have hP₀ : PowerSeries.coeff (N + 1) (pSeriesError F G p f) = 0 := by
    rcases lt_or_ge k h with hkh | hkh
    · exact coeff_pSeriesError_of_lt hF hG hf (hk ▸ Nat.pow_lt_pow_right hp'.one_lt hkh)
    · rw [hk, ← Nat.pow_sub_mul_pow p hkh]
      refine hP (k - h) ?_
      have := Nat.pow_lt_pow_right hp'.one_lt (show k - h < k by omega)
      omega
  rw [hk, homogeneousComponent_homDefect_eq_smul_lazardCocycle hf hp' hpK hk₀ (hk ▸ hΦ),
    ← neg_sub, map_neg, ← pSeriesError, ← hk, hP₀, neg_zero, zero_smul, MvPolynomial.coe_zero]

/-- If `N + 1` is not a power of `p`, some multiple of `(X + Y)ᴹ - Xᴹ - Yᴹ` cancels the
degree-`M = N + 1` part of the homomorphism defect: it is `r C_M` with `d_M` prime to `p`. -/
private theorem exists_smul_add_homogeneousComponent_homDefect_eq_zero
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {N : ℕ}
    (hpow : ¬∃ k, N + 1 = p ^ k) (hΦ : ((N + 1 : ℕ) : ℕ∞) ≤ (F.homDefect G f).order) :
    ∃ c : K, ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (N + 1) -
      MvPolynomial.X 0 ^ (N + 1) - MvPolynomial.X 1 ^ (N + 1)) : MvPolynomial (Fin 2) K) :
        MvPowerSeries (Fin 2) K) + homogeneousComponent (N + 1) (F.homDefect G f) = 0 := by
  have hp' := hp.out
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  obtain ⟨r, hr⟩ := exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle hf
    (by omega : N + 1 ≠ 0) hΦ
  have hd : IsUnit ((TauCeti.lazardGcd (N + 1) : ℕ) : K) := by
    have hcop : (TauCeti.lazardGcd (N + 1)).Coprime p := Nat.Coprime.symm <|
      (Nat.Prime.coprime_iff_not_dvd hp').mpr fun h ↦
        hpow ((TauCeti.prime_dvd_lazardGcd_iff hp' (by omega)).mp h)
    have : IsCoprime ((TauCeti.lazardGcd (N + 1) : ℕ) : K) (p : K) := by
      simpa using (Nat.isCoprime_iff_coprime.mpr hcop).intCast (R := K)
    rwa [hpK, isCoprime_zero_right] at this
  refine ⟨-r * ↑hd.unit⁻¹, ?_⟩
  rw [hr, ← MvPolynomial.coe_add, ← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega),
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_assoc, hd.val_inv_mul, mul_one, ← add_smul,
    neg_add_cancel, zero_smul, MvPolynomial.coe_zero]

/-- **The inductive step.** Let `F` and `G` have the same finite height `h` over a separably
closed field, and let `f` be a homomorphism from `F` to `G` up to degree `N ≥ 1`, whose `p`-series
failure vanishes in the degrees `pʲ p ^ h` with `pʲ ≤ N`. Then for a suitable `c`, `f + c X^(N + 1)`
has the same properties with `N + 1` in place of `N`.

In degree `M = N + 1` the defect is `r C_M`. If `M` is not a power of `p`, then `C_M` is a unit
multiple of `(X + Y)ᴹ - Xᴹ - Yᴹ` and `c` is chosen to cancel it. If `M = pᵏ`, then `r = 0`, since
`-r` is the coefficient of `Xᴹ` in the `p`-series failure, which vanishes below degree `p ^ h` and
by assumption at `M = p^(k - h) p ^ h` otherwise; now `c` is a root of the separable polynomial
`-v x^(p ^ h) + uᴹ x + a` that makes the `p`-series failure vanish in degree `M p ^ h`. -/
private theorem exists_le_order_homDefect_add [IsSepClosed K] (hF : F.height p = h)
    (hG : G.height p = h) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) {N : ℕ}
    (hN : N ≠ 0) (hΦ : ((N + 1 : ℕ) : ℕ∞) ≤ (F.homDefect G f).order)
    (hP : ∀ j, p ^ j ≤ N → PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p f) = 0) :
    ∃ c : K, ((N + 2 : ℕ) : ℕ∞) ≤ (F.homDefect G (f + c • PowerSeries.X ^ (N + 1))).order ∧
      ∀ j, p ^ j ≤ N + 1 → PowerSeries.coeff (p ^ j * p ^ h)
        (pSeriesError F G p (f + c • PowerSeries.X ^ (N + 1))) = 0 := by
  have hp' := hp.out
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hh := ne_zero_of_height_eq hF
  set M := N + 1 with hM
  have hXM (c : K) : (M : ℕ∞) ≤ (f + c • PowerSeries.X ^ M - f).order := by
    rw [add_sub_cancel_left]
    exact PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
  have hfc (c : K) : PowerSeries.constantCoeff (f + c • PowerSeries.X ^ M) = 0 := by
    simp [hf, M]
  -- after adding `c Xᴹ`, the defect in degree `M` changes by `c ((X + Y)ᴹ - Xᴹ - Yᴹ)`
  have hord (c : K) (hc : ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ M -
      MvPolynomial.X 0 ^ M - MvPolynomial.X 1 ^ M) : MvPolynomial (Fin 2) K) :
        MvPowerSeries (Fin 2) K) + homogeneousComponent M (F.homDefect G f) = 0) :
      ((N + 2 : ℕ) : ℕ∞) ≤ (F.homDefect G (f + c • PowerSeries.X ^ M)).order := by
    have hM' : (M : ℕ∞) ≤ (F.homDefect G (f + c • PowerSeries.X ^ M)).order := by
      rw [← sub_add_cancel (F.homDefect G (f + c • PowerSeries.X ^ M)) (F.homDefect G f)]
      exact le_order_add (le_order_homDefect_sub (hfc c) hf (hXM c))
        (hΦ.trans' (by exact_mod_cast le_rfl))
    refine succ_le_order_of_homogeneousComponent_eq_zero hM' ?_
    rw [← sub_add_cancel (F.homDefect G (f + c • PowerSeries.X ^ M)) (F.homDefect G f), map_add,
      homogeneousComponent_homDefect_add_sub hf (by omega), hc]
  -- the `p`-series failure is unchanged in degrees `pʲ p ^ h` with `pʲ < M`
  have hlow (c : K) {j : ℕ} (hj : p ^ j < M) : PowerSeries.coeff (p ^ j * p ^ h)
      (pSeriesError F G p (f + c • PowerSeries.X ^ M)) = 0 := by
    rw [← sub_add_cancel (pSeriesError F G p (f + c • PowerSeries.X ^ M)) (pSeriesError F G p f),
      map_add, hP j (by omega), _root_.add_zero, PowerSeries.coeff_of_lt_order]
    exact (le_order_pSeriesError_sub hF hG (hfc c) hf (hXM c)).trans_lt' (by
      exact_mod_cast Nat.mul_lt_mul_of_pos_right hj (pow_pos hp'.pos h))
  by_cases hpow : ∃ k, M = p ^ k
  · obtain ⟨k, hk⟩ := hpow
    -- the defect in degree `M = pᵏ` is read off the `p`-series failure, which vanishes there
    have hΦ₀ := homogeneousComponent_homDefect_eq_zero_of_pow hF hG hf hN hk hΦ hP
    -- choose `c` to make the `p`-series failure vanish in degree `M p ^ h`
    obtain ⟨c, hc⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
      (-PowerSeries.coeff (p ^ h) (G.nsmulSeries p))
      (PowerSeries.coeff (p ^ h) (F.nsmulSeries p) ^ M)
      (PowerSeries.coeff (M * p ^ h) (pSeriesError F G p f))
      (by rw [Nat.cast_pow, hpK, zero_pow hh])
      (by have := Nat.one_lt_pow hh hp'.one_lt; omega)
      (pow_ne_zero _ (coeff_nsmulSeries_ne_zero hF))
    refine ⟨c, hord c ?_, fun j hj ↦ ?_⟩
    · -- `(X + Y) ^ pᵏ = X ^ pᵏ + Y ^ pᵏ` in characteristic `p`
      rw [hΦ₀, _root_.add_zero, hk, add_pow_char_pow]
      simp
    · rcases hj.lt_or_eq with hj | hj
      · exact hlow c hj
      · rw [hj, coeff_pSeriesError_add hF hG hf (by omega)]
        linear_combination hc
  · -- the defect in degree `M` is `r C_M`, where `d_M` is prime to `p`, hence a unit, and
    -- `r C_M = (r d_M⁻¹) ((X + Y)ᴹ - Xᴹ - Yᴹ)`
    obtain ⟨c, hc⟩ :=
      exists_smul_add_homogeneousComponent_homDefect_eq_zero (F := F) (G := G) hf hpow hΦ
    exact ⟨c, hord c hc, fun j hj ↦ hlow _ (hj.lt_of_ne fun h ↦ hpow ⟨j, h.symm⟩)⟩

section Construction

/-- The approximations to an isomorphism: starting from `c₁ X`, step `n` adds the multiple
`c n g • X ^ (n + 2)` of the current approximation `g`. -/
private noncomputable def approx (c₁ : K) (c : ℕ → PowerSeries K → K) : ℕ → PowerSeries K
  | 0 => c₁ • PowerSeries.X ^ 1
  | n + 1 => approx c₁ c n + c n (approx c₁ c n) • PowerSeries.X ^ (n + 2)

/-- A nonzero root of `x ^ (p ^ h - 1) = u / v`, where `u` and `v` are the coefficients of
`X ^ (p ^ h)` in `[p]_F` and `[p]_G`; it is the linear coefficient of the isomorphism. -/
private theorem exists_pow_sub_one_eq_div [IsSepClosed K] (hF : F.height p = h)
    (hG : G.height p = h) : ∃ c₁ : K, c₁ ≠ 0 ∧ c₁ ^ (p ^ h - 1) =
      PowerSeries.coeff (p ^ h) (F.nsmulSeries p) /
        PowerSeries.coeff (p ^ h) (G.nsmulSeries p) := by
  have hh := ne_zero_of_height_eq hF
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have : NeZero ((p ^ h - 1 : ℕ) : K) := ⟨by
    rw [Nat.cast_sub (by have := Nat.one_lt_pow hh hp.out.one_lt; omega), Nat.cast_pow, hpK,
      zero_pow hh, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero⟩
  obtain ⟨c₁, hc₁⟩ := IsSepClosed.exists_pow_nat_eq
    (PowerSeries.coeff (p ^ h) (F.nsmulSeries p) / PowerSeries.coeff (p ^ h) (G.nsmulSeries p))
    (p ^ h - 1)
  refine ⟨c₁, ?_, hc₁⟩
  rintro rfl
  have h1 := Nat.one_lt_pow hh hp.out.one_lt
  rw [zero_pow (by omega)] at hc₁
  exact div_ne_zero (coeff_nsmulSeries_ne_zero hF) (coeff_nsmulSeries_ne_zero hG) hc₁.symm

/-- The first approximation `c₁ X`, where `c₁ ^ (p ^ h - 1) = u / v`, is a homomorphism up to
degree `2` and satisfies the `p`-series condition in degree `p ^ h`. -/
private theorem approx_zero_spec (hF : F.height p = h) (hG : G.height p = h) {c₁ : K}
    (hc₁ : c₁ ^ (p ^ h - 1) = PowerSeries.coeff (p ^ h) (F.nsmulSeries p) /
      PowerSeries.coeff (p ^ h) (G.nsmulSeries p)) :
    PowerSeries.constantCoeff (c₁ • PowerSeries.X ^ 1 : PowerSeries K) = 0 ∧
      PowerSeries.coeff 1 (c₁ • PowerSeries.X ^ 1 : PowerSeries K) = c₁ ∧
      ((0 + 2 : ℕ) : ℕ∞) ≤ (F.homDefect G (c₁ • PowerSeries.X ^ 1 : PowerSeries K)).order ∧
      ∀ j, p ^ j ≤ 0 + 1 → PowerSeries.coeff (p ^ j * p ^ h)
        (pSeriesError F G p (c₁ • PowerSeries.X ^ 1 : PowerSeries K)) = 0 := by
  have hp' := hp.out
  have hu := coeff_nsmulSeries_ne_zero hF
  have hv := coeff_nsmulSeries_ne_zero hG
  have h₀ : (c₁ • PowerSeries.X ^ 1 : PowerSeries K) = 0 + c₁ • PowerSeries.X ^ 1 := by
    rw [_root_.zero_add]
  refine ⟨by simp, by simp, ?_, fun j hj ↦ ?_⟩
  · have h₁ : ((1 : ℕ) : ℕ∞) ≤ (F.homDefect G (c₁ • PowerSeries.X ^ 1 : PowerSeries K)).order := by
      rw [← sub_zero (F.homDefect G _), ← homDefect_zero (F := F) (G := G)]
      refine le_order_homDefect_sub (by simp) (map_zero _) ?_
      rw [sub_zero, Nat.cast_one]
      exact PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    refine succ_le_order_of_homogeneousComponent_eq_zero h₁ ?_
    have := homogeneousComponent_homDefect_add_sub (F := F) (G := G) (map_zero _)
      one_ne_zero c₁
    rw [← h₀, homDefect_zero, sub_zero] at this
    rw [this]
    simp
  · obtain rfl : j = 0 := by
      by_contra hj₀
      have := Nat.one_lt_pow hj₀ hp'.one_lt
      omega
    have hc₁q : c₁ ^ p ^ h = c₁ * (PowerSeries.coeff (p ^ h) (F.nsmulSeries p) /
        PowerSeries.coeff (p ^ h) (G.nsmulSeries p)) := by
      rw [← hc₁, ← pow_succ']
      congr 1
      have := Nat.one_lt_pow (ne_zero_of_height_eq hF) hp'.one_lt
      omega
    rw [h₀, pow_zero, one_mul, ← one_mul (p ^ h),
      coeff_pSeriesError_add hF hG (map_zero _) one_ne_zero, pSeriesError_zero, map_zero,
      _root_.zero_add, pow_one, hc₁q]
    field_simp
    ring

/-- **Existence of an isomorphism.** Two commutative formal group laws of the same finite height
over a separably closed field of characteristic `p` are related by a homomorphism with nonzero
linear coefficient. It is the limit of the approximations built by
`exists_le_order_homDefect_add`, starting from `c₁ X` with `c₁ ^ (p ^ h - 1) = u / v`, where `u` and
`v` are the coefficients of `X^(p ^ h)` in `[p]_F` and `[p]_G`. -/
private theorem exists_formalGroupHom_coeff_one_ne_zero [IsSepClosed K] (hF : F.height p = h)
    (hG : G.height p = h) :
    ∃ f : TauCeti.FormalGroupHom F G, PowerSeries.coeff 1 f.toPowerSeries ≠ 0 := by
  obtain ⟨c₁, hc₁₀, hc₁⟩ := exists_pow_sub_one_eq_div hF hG
  choose! c hc using fun (n : ℕ) (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = 0)
    (hΦ : ((n + 2 : ℕ) : ℕ∞) ≤ (F.homDefect G g).order)
    (hP : ∀ j, p ^ j ≤ n + 1 → PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p g) = 0) ↦
    exists_le_order_homDefect_add hF hG hg (N := n + 1) (by omega) hΦ hP
  -- `approx c₁ c n` is a homomorphism up to degree `n + 2` with the required `p`-series property
  have key (n : ℕ) : PowerSeries.constantCoeff (approx c₁ c n) = 0 ∧
      PowerSeries.coeff 1 (approx c₁ c n) = c₁ ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ (F.homDefect G (approx c₁ c n)).order ∧
      ∀ j, p ^ j ≤ n + 1 →
        PowerSeries.coeff (p ^ j * p ^ h) (pSeriesError F G p (approx c₁ c n)) = 0 := by
    induction n with
    | zero => exact approx_zero_spec hF hG hc₁
    | succ n ih =>
      obtain ⟨h₀, h₁, hord, hP⟩ := ih
      obtain ⟨hord', hP'⟩ := hc n (approx c₁ c n) h₀ hord hP
      refine ⟨by simp [approx, h₀], ?_, hord', hP'⟩
      rw [approx, map_add, h₁, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
      simp
  -- the limit of the approximations is a homomorphism
  obtain ⟨f, hlim⟩ := PowerSeries.exists_forall_le_order_sub (f := approx c₁ c) fun n ↦ by
    rw [approx, add_sub_cancel_left]
    refine PowerSeries.nat_le_order _ _ fun i hi ↦ ?_
    simp [PowerSeries.coeff_X_pow, show i ≠ n + 2 by omega]
  have hcoeff {m n : ℕ} (hm : m < n) :
      PowerSeries.coeff m f = PowerSeries.coeff m (approx c₁ c n) := by
    rw [← sub_eq_zero, ← map_sub]
    exact PowerSeries.coeff_of_lt_order m ((hlim n).trans_lt' (by exact_mod_cast hm))
  have hf₀ : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff (n := 1) one_pos,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (key 1).1]
  have hΦ : F.homDefect G f = 0 := by
    refine order_eq_top_iff.mp (top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun m _ ↦ ?_))
    have h := le_order_add ((key m).2.2.1.trans' (by exact_mod_cast (by omega : m ≤ m + 2)))
      (le_order_homDefect_sub (F := F) (G := G) hf₀ (key m).1 (hlim m))
    rwa [add_sub_cancel] at h
  refine ⟨TauCeti.FormalGroupHom.ofHomDefectEqZero hf₀ hΦ, ?_⟩
  rw [TauCeti.FormalGroupHom.ofHomDefectEqZero_toPowerSeries, hcoeff (n := 2) one_lt_two,
    (key 2).2.1]
  exact hc₁₀

end Construction

end Field

/-- **Lazard's classification of formal group laws by height.** Over a separably closed field `K`
of characteristic `p`, two commutative formal group laws are isomorphic exactly when they have the
same height. In height `⊤` both are isomorphic to the additive formal group law. -/
theorem height_eq_height_iff_nonempty_formalGroupIso {K : Type*} [Field K] [IsSepClosed K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (F G : FormalGroup K) [F.IsComm] [G.IsComm] :
    F.height p = G.height p ↔ Nonempty (TauCeti.FormalGroupIso F G) := by
  refine ⟨fun hFG ↦ ?_, fun ⟨e⟩ ↦ e.height_eq p⟩
  cases hG : G.height p with
  | top =>
    obtain ⟨e⟩ := (height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ F).mp (hFG.trans hG)
    obtain ⟨e'⟩ := (height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ G).mp hG
    exact ⟨e.trans e'.symm⟩
  | coe h =>
    obtain ⟨f, hf⟩ := exists_formalGroupHom_coeff_one_ne_zero (hFG.trans hG) hG
    exact ⟨f.toIso (isUnit_iff_ne_zero.mpr hf)⟩

end FormalGroup
