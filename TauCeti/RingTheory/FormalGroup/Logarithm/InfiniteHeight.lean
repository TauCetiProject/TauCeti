/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Height
import TauCeti.RingTheory.FormalGroup.AddInv
import TauCeti.RingTheory.FormalGroup.Obstruction
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Formal group laws of infinite height are additive

Let `p` be a prime and let `F` be a commutative formal group law over a commutative ring `R` with
`[p]_F = 0`. Then `p = 0` in `R`, since `p` is the linear coefficient of `[p]_F`, so no logarithm in
the sense of `FormalGroup.log` is available. Nevertheless `F` is strictly isomorphic to the
additive formal group law, along a coordinate that is unique once normalised: there is a unique
power series

  `g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{pᵏ} = 0` for every `k ≥ 1`

such that `g(F(X, Y)) = g(X) + g(Y)`. Over a field of characteristic `p`, the condition
`[p]_F = 0` says that `F` has height `⊤`, so the formal group laws of infinite height are exactly
those isomorphic to the additive one. For `p = 2` this is Quillen's normalised logarithm of a
formal group law of exponent two, `FormalGroup.exponentTwoLog`. No coefficient field and no further
hypothesis on `R` is used: it may have nilpotents or be the zero ring.

The power series `g` is constructed degree by degree. If `g` is additive along `F` up to degree
`n`, the error `Φ(X, Y) = g(F(X, Y)) - g(X) - g(Y)` is the homomorphism defect of `g` from `F` to
the additive formal group law, so its degree-`n` part is `r C_n` for the Lazard cocycle
`C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / d_n`
(`FormalGroup.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle`).

* If `n` is not a power of `p`, then `d_n` is prime to `p`, hence a unit in `R`, and replacing `g`
  by `g - r d_n⁻¹ Xⁿ` makes `g` additive up to degree `n + 1`.
* If `n = pᵏ` with `k ≥ 1`, then `d_n = p` and `r = 0`, since `r` is the coefficient of `Xⁿ` in
  `[p]_{𝔾ₐ}(g(X)) - g([p]_F(X)) = p g(X) - g(0) = 0`
  (`FormalGroup.homogeneousComponent_homDefect_eq_smul_lazardCocycle`).

Each step leaves the coefficients in lower degrees, and those in degrees `pᵏ`, unchanged, and `g`
is the limit of these approximations. Uniqueness is the fact that a nonzero homomorphism to
the additive formal group law has order a power of `p`
(`FormalGroup.exists_order_eq_pow_of_natCast_eq_zero`).

## Main results

* `FormalGroup.existsUnique_logarithm_of_nsmulSeries_eq_zero`: for commutative `F` with
  `[p]_F = 0`, there is a unique power series `g = X + ⋯` without terms of degree `pᵏ`, `k ≥ 1`,
  such that `g(F(X, Y)) = g(X) + g(Y)`.
* `FormalGroup.logarithm_unique_of_natCast_eq_zero`: if `p = 0` in `R`, two such power series
  agree, for any formal group law `F`.
* `FormalGroup.exists_isStrict_formalGroupIso_𝔾ₐ`: a commutative formal group law with
  `[p]_F = 0` is strictly isomorphic to the additive formal group law.
* `FormalGroup.height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ`: over a field of characteristic `p`,
  a commutative formal group law has height `⊤` exactly when it is isomorphic to the additive one.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

section HomDefect

private theorem homDefect_𝔾ₐ_sub {g h : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0) :
    F.homDefect 𝔾ₐ (g - h) = F.homDefect 𝔾ₐ g - F.homDefect 𝔾ₐ h := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  rw [F.homDefect_𝔾ₐ (by rw [map_sub, hg, hh, sub_zero]), F.homDefect_𝔾ₐ hg, F.homDefect_𝔾ₐ hh]
  simp only [PowerSeries.subst_sub hF, PowerSeries.subst_sub (PowerSeries.HasSubst.X _)]
  ring

/-- The additivity defect of `g` vanishes to the order of `g`. -/
private theorem le_order_homDefect_𝔾ₐ {g : PowerSeries R} (hg₀ : PowerSeries.constantCoeff g = 0)
    {n : ℕ} (hg : n ≤ g.order) : (n : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order := by
  have h {x : MvPowerSeries (Fin 2) R} (hx : constantCoeff x = 0) :
      (n : ℕ∞) ≤ (PowerSeries.subst x g).order :=
    hg.trans (PowerSeries.le_order_subst_left hx)
  rw [F.homDefect_𝔾ₐ hg₀]
  exact le_order_sub (le_order_sub (h F.zero_constantCoeff) (h (constantCoeff_X 0)))
    (h (constantCoeff_X 1))

/-- The lowest-degree part of the additivity defect of `c Xⁿ`, `n ≠ 0`, is
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
private theorem homogeneousComponent_homDefect_𝔾ₐ_smul_X_pow (c : R) {n : ℕ} (hn : n ≠ 0) :
    homogeneousComponent n (F.homDefect 𝔾ₐ (c • PowerSeries.X ^ n)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  rw [F.homDefect_𝔾ₐ (by simp [hn])]
  simp only [PowerSeries.subst_smul hF, PowerSeries.subst_smul (hX _),
    PowerSeries.subst_pow hF, PowerSeries.subst_pow (hX _), PowerSeries.subst_X hF,
    PowerSeries.subst_X (hX _), map_sub, _root_.map_smul,
    homogeneousComponent_pow_of_constantCoeff_eq_zero F.zero_constantCoeff,
    homogeneousComponent_pow_of_constantCoeff_eq_zero (constantCoeff_X _),
    homogeneousComponent_one_X,
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y]
  rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_mul, map_sub, map_pow, map_add, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, MvPolynomial.coe_C, MvPowerSeries.smul_eq_C_mul, mul_sub]

end HomDefect

section PSeries

variable {F}

/-- **The inductive step.** If `[p]_F = 0` and the additivity defect of `g` vanishes below degree
`n ≥ 2`, subtracting a suitable multiple `c Xⁿ` makes it vanish below degree `n + 1`, and `c = 0`
when `n` is a power of `p`. -/
private theorem exists_le_order_homDefect_𝔾ₐ_sub_smul_X_pow [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hF : F.nsmulSeries p = 0) {n : ℕ} (hn₂ : 2 ≤ n) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hn : n ≤ (F.homDefect 𝔾ₐ g).order) :
    ∃ c : R, ((n + 1 : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ (g - c • PowerSeries.X ^ n)).order ∧
      ∀ k, n = p ^ k → c = 0 := by
  have hpR : (p : R) = 0 := F.natCast_eq_zero_of_nsmulSeries_eq_zero hF
  obtain ⟨r, hr⟩ := F.exists_homogeneousComponent_homDefect_eq_smul_lazardCocycle hg (by omega) hn
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk : k ≠ 0 := by
      rintro rfl
      simp at hn₂
    -- the obstruction is the coefficient of `Xⁿ` in `[p]_{𝔾ₐ}(g(X)) - g([p]_F(X)) = 0`
    have h0 := F.homogeneousComponent_homDefect_eq_smul_lazardCocycle hg hp hpR hk hn
    have hp0 : (p : PowerSeries R) = 0 := by rw [← map_natCast PowerSeries.C, hpR, map_zero]
    simp only [nsmulSeries_𝔾ₐ, hF, hp0, zero_mul, PowerSeries.subst_zero,
      PowerSeries.subst_zero_of_constantCoeff_zero hg, sub_zero, map_zero, zero_smul,
      MvPolynomial.coe_zero] at h0
    refine ⟨0, ?_, fun _ _ ↦ rfl⟩
    rw [zero_smul, sub_zero]
    exact succ_le_order_of_homogeneousComponent_eq_zero hn h0
  · -- `d_n` is prime to `p`, hence a unit in `R`, and `r C_n = (r d_n⁻¹) ((X + Y)ⁿ - Xⁿ - Yⁿ)`
    have hd : IsUnit ((TauCeti.lazardGcd n : ℕ) : R) := by
      have hcop : (TauCeti.lazardGcd n).Coprime p := Nat.Coprime.symm <|
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h ↦
          hpow ((TauCeti.prime_dvd_lazardGcd_iff hp (by omega)).mp h)
      have : IsCoprime ((TauCeti.lazardGcd n : ℕ) : R) (p : R) := by
        simpa using (Nat.isCoprime_iff_coprime.mpr hcop).intCast (R := R)
      rwa [hpR, isCoprime_zero_right] at this
    have hc : homogeneousComponent n (F.homDefect 𝔾ₐ g) = ↑((r * ↑hd.unit⁻¹) •
        ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
          MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) R)) := by
      rw [hr, ← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega), ← Nat.cast_smul_eq_nsmul R,
        smul_smul, mul_assoc, hd.val_inv_mul, mul_one]
    set c := r * ↑hd.unit⁻¹
    refine ⟨c, ?_, fun k hk ↦ (hpow ⟨k, hk⟩).elim⟩
    have hXn : (n : ℕ∞) ≤ (c • PowerSeries.X ^ n : PowerSeries R).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
    have hXn₀ : PowerSeries.constantCoeff (c • PowerSeries.X ^ n : PowerSeries R) = 0 := by
      simp [show n ≠ 0 by omega]
    have hn' : (n : ℕ∞) ≤ (F.homDefect 𝔾ₐ (g - c • PowerSeries.X ^ n)).order := by
      rw [homDefect_𝔾ₐ_sub F hg hXn₀]
      exact le_order_sub hn (le_order_homDefect_𝔾ₐ F hXn₀ hXn)
    refine succ_le_order_of_homogeneousComponent_eq_zero hn' ?_
    rw [homDefect_𝔾ₐ_sub F hg hXn₀, map_sub,
      homogeneousComponent_homDefect_𝔾ₐ_smul_X_pow F c (by omega), hc, sub_self]

end PSeries

section Construction

/-- The approximations to the logarithm: starting from `X`, step `n` subtracts the multiple
`c (n + 2) g • X ^ (n + 2)` of the current approximation `g`. -/
private noncomputable def approx (c : ℕ → PowerSeries R → R) : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | n + 1 => approx c n - c (n + 2) (approx c n) • PowerSeries.X ^ (n + 2)

/-- The approximations stabilise: `approx c n` and `approx c n'` agree below degree
`min n n' + 2`. -/
private theorem coeff_approx_eq_coeff_approx (c : ℕ → PowerSeries R → R) {m n n' : ℕ}
    (hm : m < n + 2) (hm' : m < n' + 2) :
    PowerSeries.coeff m (approx c n) = PowerSeries.coeff m (approx c n') := by
  wlog h : n ≤ n' generalizing n n'
  · exact (this hm' hm (by omega)).symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ih (by omega) (by omega), ← add_assoc, approx, map_sub, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow]
    simp [show m ≠ n + j + 2 by omega]

/-- The limit of the approximations. -/
private noncomputable def approxLimit (c : ℕ → PowerSeries R → R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m (approx c m)

/-- The limit agrees with `approx c n` below degree `n + 2`. -/
private theorem coeff_approxLimit (c : ℕ → PowerSeries R → R) {m n : ℕ} (hm : m < n + 2) :
    PowerSeries.coeff m (approxLimit c) = PowerSeries.coeff m (approx c n) := by
  rw [approxLimit, PowerSeries.coeff_mk]
  exact coeff_approx_eq_coeff_approx c (by omega) hm

/-- **Existence of the normalised logarithm**, by passing to the limit of the approximations. -/
private theorem exists_logarithm [F.IsComm] {p : ℕ} (hp : p.Prime) (hF : F.nsmulSeries p = 0) :
    ∃ g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (p ^ k) g = 0) ∧ F.homDefect 𝔾ₐ g = 0 := by
  choose! c hc using fun (n : ℕ) (g : PowerSeries R) (hn₂ : 2 ≤ n)
    (hg : PowerSeries.constantCoeff g = 0) (hn : (n : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order) ↦
    exists_le_order_homDefect_𝔾ₐ_sub_smul_X_pow hp hF hn₂ hg hn
  -- `approx c n` is normalised and additive along `F` below degree `n + 2`
  have key (n : ℕ) : PowerSeries.constantCoeff (approx c n) = 0 ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ (F.homDefect 𝔾ₐ (approx c n)).order ∧
      ∀ k, 0 < k → PowerSeries.coeff (p ^ k) (approx c n) = 0 := by
    induction n with
    | zero =>
      have hF' := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
      refine ⟨PowerSeries.constantCoeff_X, ?_, fun k hk ↦ ?_⟩
      · rw [approx, F.homDefect_𝔾ₐ PowerSeries.constantCoeff_X, PowerSeries.subst_X hF',
          PowerSeries.subst_X (PowerSeries.HasSubst.X _),
          PowerSeries.subst_X (PowerSeries.HasSubst.X _), sub_sub]
        exact two_le_order_sub_X_add_X F.zero_constantCoeff F.lin_coeff_X F.lin_coeff_Y
      · simp [approx, PowerSeries.coeff_X, hp.ne_one, hk.ne']
    | succ n ih =>
      obtain ⟨h₀, hord, hpow⟩ := ih
      obtain ⟨hord', hc₀⟩ := hc (n + 2) (approx c n) (by omega) h₀ hord
      refine ⟨by simp [approx, h₀], hord', fun k hk ↦ ?_⟩
      rw [approx, map_sub, hpow k hk, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
      split_ifs with h
      · simp [hc₀ k h.symm]
      · simp
  have h₀ : PowerSeries.constantCoeff (approxLimit c) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_approxLimit c (n := 0) (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (key 0).1]
  refine ⟨approxLimit c, h₀, ?_, fun k hk ↦ ?_, ?_⟩
  · rw [coeff_approxLimit c (n := 0) (by omega)]
    simp [approx]
  · rw [coeff_approxLimit c (n := p ^ k) (by omega), (key _).2.2 k hk]
  · -- the additivity defect of the limit vanishes below every degree
    refine order_eq_top_iff.mp (top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun m _ ↦ ?_))
    have hlim : ((m + 2 : ℕ) : ℕ∞) ≤ (approxLimit c - approx c m).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ by rw [map_sub, coeff_approxLimit c hi, sub_self]
    have hdiff := le_order_homDefect_𝔾ₐ F (by rw [map_sub, h₀, (key m).1, sub_zero]) hlim
    rw [homDefect_𝔾ₐ_sub F h₀ (key m).1] at hdiff
    have h := le_order_add (key m).2.1 hdiff
    rw [add_sub_cancel] at h
    exact (Nat.cast_le.mpr (by omega : m ≤ m + 2)).trans h

end Construction

/-- **Uniqueness of the normalised logarithm** in characteristic `p`. Let `p` be a prime with
`p = 0` in `R`, and let `F` be a formal group law over `R`, not necessarily commutative. Two power
series `g, g' = X + ⋯` without terms of degree `pᵏ`, `k ≥ 1`, that are additive along `F` agree.

Indeed `g - g'` is a homomorphism from `F` to the additive formal group law, and a nonzero such
homomorphism has order a power of `p`. -/
theorem logarithm_unique_of_natCast_eq_zero {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    {g g' : PowerSeries R} (h₀ : PowerSeries.constantCoeff g = 0) (h₁ : PowerSeries.coeff 1 g = 1)
    (hpow : ∀ k, 0 < k → PowerSeries.coeff (p ^ k) g = 0)
    (hg : PowerSeries.subst F.toPowerSeries g =
      PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g)
    (h₀' : PowerSeries.constantCoeff g' = 0) (h₁' : PowerSeries.coeff 1 g' = 1)
    (hpow' : ∀ k, 0 < k → PowerSeries.coeff (p ^ k) g' = 0)
    (hg' : PowerSeries.subst F.toPowerSeries g' =
      PowerSeries.subst (X 0) g' + PowerSeries.subst (X 1) g') :
    g = g' := by
  by_contra hne
  have hne' : g - g' ≠ 0 := sub_ne_zero.mpr hne
  have hf₀ : PowerSeries.constantCoeff (g - g') = 0 := by rw [map_sub, h₀, h₀', sub_zero]
  have hf := (TauCeti.FormalGroupHom.hom_additive_iff (F := F) hf₀).mpr <| by
    rw [PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      PowerSeries.subst_sub (PowerSeries.HasSubst.X _),
      PowerSeries.subst_sub (PowerSeries.HasSubst.X _), hg, hg']
    ring
  obtain ⟨h, hh⟩ := F.exists_order_eq_pow_of_natCast_eq_zero 𝔾ₐ hp hpR hf₀ hf hne'
  have hc := PowerSeries.coeff_order hne'
  rw [hh, ENat.toNat_natCast, map_sub] at hc
  rcases Nat.eq_zero_or_pos h with rfl | hh₀
  · rw [pow_zero, h₁, h₁', sub_self] at hc
    exact hc rfl
  · rw [hpow h hh₀, hpow' h hh₀, sub_self] at hc
    exact hc rfl

/-- **The normalised logarithm of a formal group law of infinite height.** Let `p` be a prime and
let `F` be a commutative formal group law over a commutative ring `R` with `[p]_F = 0`. There is a
unique power series `g(X) = X + ∑_{i ≥ 2} aᵢ Xⁱ` with `a_{pᵏ} = 0` for every `k ≥ 1` such that
`g(F(X, Y)) = g(X) + g(Y)`. -/
theorem existsUnique_logarithm_of_nsmulSeries_eq_zero [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hF : F.nsmulSeries p = 0) :
    ∃! g : PowerSeries R, PowerSeries.constantCoeff g = 0 ∧ PowerSeries.coeff 1 g = 1 ∧
      (∀ k, 0 < k → PowerSeries.coeff (p ^ k) g = 0) ∧
      PowerSeries.subst F.toPowerSeries g =
        PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g := by
  obtain ⟨g, h₀, h₁, hpow, hg⟩ := F.exists_logarithm hp hF
  rw [F.homDefect_𝔾ₐ h₀, sub_sub, sub_eq_zero] at hg
  refine ⟨g, ⟨h₀, h₁, hpow, hg⟩, fun g' ⟨h₀', h₁', hpow', hg'⟩ ↦ ?_⟩
  exact F.logarithm_unique_of_natCast_eq_zero hp (F.natCast_eq_zero_of_nsmulSeries_eq_zero hF)
    h₀' h₁' hpow' hg' h₀ h₁ hpow hg

/-- **A formal group law of infinite height is additive.** If `p` is a prime and `F` is a
commutative formal group law with `[p]_F = 0`, then `F` is strictly isomorphic to the additive
formal group law. -/
theorem exists_isStrict_formalGroupIso_𝔾ₐ [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hF : F.nsmulSeries p = 0) : ∃ f : TauCeti.FormalGroupIso F 𝔾ₐ, f.IsStrict := by
  obtain ⟨g, ⟨h₀, h₁, -, hg⟩, -⟩ := F.existsUnique_logarithm_of_nsmulSeries_eq_zero hp hF
  -- `g` is a strict coordinate transporting `F` to the additive formal group law
  let φ : TauCeti.FormalCoordinate R := ⟨g, h₀, h₁ ▸ isUnit_one⟩
  let f : TauCeti.FormalGroupHom F 𝔾ₐ :=
    ⟨g, h₀, (TauCeti.FormalGroupHom.hom_additive_iff h₀).mpr hg⟩
  have hφ : φ • F = 𝔾ₐ := by
    have hX (i : Fin 2) := φ⁻¹.hasSubst_subst (PowerSeries.HasSubst.X (S := R) i)
    refine FormalGroup.ext ?_
    rw [smul_toPowerSeries]
    refine (f.hom_subst (hasSubst_finTwo (hX 0) (hX 1))).trans ?_
    have h (i : Fin 2) : PowerSeries.subst
        (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries,
          PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries] i)
        f.toPowerSeries = X i := by
      fin_cases i <;> exact φ.subst_subst_inv (PowerSeries.HasSubst.X _)
    simp only [h, subst_self, id]
  rw [← hφ]
  exact ⟨smulIso φ F, (isStrict_smulIso_iff φ F).mpr
    (Units.ext (by rw [TauCeti.FormalCoordinate.val_linearCoeff]; exact h₁))⟩

/-- **Formal group laws of infinite height are the additive ones.** Over a field `K` of
characteristic `p`, a commutative formal group law has height `⊤` exactly when it is isomorphic
to the additive formal group law. -/
theorem height_eq_top_iff_nonempty_formalGroupIso_𝔾ₐ {K : Type*} [Field K] {p : ℕ}
    [hp : Fact p.Prime] [CharP K p] (F : FormalGroup K) [F.IsComm] :
    F.height p = ⊤ ↔ Nonempty (TauCeti.FormalGroupIso F 𝔾ₐ) := by
  refine ⟨fun h ↦ ?_, fun ⟨f⟩ ↦ (f.height_eq p).trans height_𝔾ₐ⟩
  obtain ⟨f, -⟩ := F.exists_isStrict_formalGroupIso_𝔾ₐ hp.out (F.height_eq_top_iff.mp h)
  exact ⟨f⟩

end FormalGroup
