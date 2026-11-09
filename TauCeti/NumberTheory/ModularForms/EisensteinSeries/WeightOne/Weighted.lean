/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ModularForms.QExpansion
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Analysis.SpecialFunctions.Exp.Summable
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent
import TauCeti.Basic.Complex.Basic
import TauCeti.Data.Nat.Cast.Order.Field
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Weight-one Eisenstein series weighted by a function of residues

In weight one the residue-class series `G₁^{a}(z) = ∑_{x ≡ a mod N} (x₀ z + x₁)⁻¹` do not
converge absolutely. Their role is played by the values of the Weierstrass `ζ` function at the
`N`-division points of `ℤ z + ℤ`: writing `x = ã - N y`, the term `(x₀ z + x₁)⁻¹` is `N⁻¹` times
the term `(u - (y₀ z + y₁))⁻¹` of the lattice series of `ζ(u; ℤ z + ℤ)` at
`u = (ã₀ z + ã₁) / N`, which that series makes convergent by adding `l⁻¹ + u l⁻²`. Unlike `℘`, the
function `ζ` is only quasi-periodic, `ζ(u + l) = ζ(u) + η(l)`, so its division values must be
corrected by the quasi-periods `η₁ = η(z)` and `η₂ = η(1)` to depend only on the residue `a`:

`F_a(z) = ζ((ã₀ z + ã₁) / N; ℤ z + ℤ) - (ã₀ η₁ + ã₁ η₂) / N`.

Replacing `ã` by `ã + N y` changes both terms by `y₀ η₁ + y₁ η₂`. This includes the zero residue,
whose division points are the lattice points, the poles of `ζ`: there `ζ` takes the junk value
`ζ(l) = η(l)` (`PeriodPair.weierstrassZeta_coe`), so `F_0 = 0`. For a weight
`W : (Fin 2 → ZMod N) → ℂ` we define

`E₁^W(z) = N⁻¹ ∑_a W(a) F_a(z)`

(`TauCeti.EisensteinSeries.weightedE1`), with `ã₀, ã₁` the least nonnegative representatives
of `a`.

Under `γ ∈ SL(2, ℤ)` the lattice of `γ z` is `(c z + d)⁻¹` times that of `z`, and both `ζ` and
its quasi-periods scale by `c z + d`. Hence slashing `E₁^W` by `γ` in weight one replaces the
weight `W` by `a ↦ W (a γ⁻¹)` (`TauCeti.EisensteinSeries.weightedE1_slash_apply`), exactly as for
the absolutely convergent series of weight `k ≥ 3`. In particular `E₁^W` is invariant under
`Γ(N)` (`TauCeti.EisensteinSeries.weightedE1SIF`); no Legendre relation is needed for this. It is
holomorphic on `ℍ` (`TauCeti.EisensteinSeries.weightedE1_mdifferentiable`), as the lattice series
of `ζ` converges locally uniformly in `z` and the quasi-periods are the division values
`η₁ = 2 ζ(z / 2)`, `η₂ = 2 ζ(1 / 2)`.

Since `ζ` is odd, so is `a ↦ F_a`, and `E₁^W` changes sign when `W` is replaced by `a ↦ W (-a)`
(`TauCeti.EisensteinSeries.weightedE1_comp_neg`). This is the parity constraint of weight one:
`E₁^W = 0` for every even weight `W` (`TauCeti.EisensteinSeries.weightedE1_eq_zero_of_even`), so
for the weights `W(a) = ψ(a₀) conj(φ(a₁))` attached to a pair of Dirichlet characters only the pairs
with `ψ(-1) φ(-1) = -1` contribute.

For the behaviour at `i∞` the quasi-periods are the division values `η₁ = 2 ζ(z / 2)` and
`η₂ = 2 ζ(1 / 2)`, so that for `a ≠ 0`

`F_a = ζ(x) - 2 (a₀ / N) ζ(z / 2) - 2 (a₁ / N) ζ(1 / 2)`, `x = (a₀ z + a₁) / N`.

Summing the lattice series of `ζ` along its rows turns the row `m` at `u` into
`π cot (π (u - m z)) + π cot (π m z) + u ∑_n (m z + n)⁻²`
(`UpperHalfPlane.hasSum_weierstrassZeta_periodPair_rows`); in the combination above the last parts
cancel, as `x - 2 (a₀ / N) (z / 2) - 2 (a₁ / N) (1 / 2) = 0`. What remains are cotangents at
division points `u = (b₀ z + b₁) / M` with `b₀ < M`. For `m ≠ 0` the imaginary parts of `u - m z`
and `m z` have opposite signs and absolute values at least `max (1 / M) (|m| - 1)` times `Im z`,
so the two cotangents approach `π i` and `-π i`. On `1 ≤ Im z` their sum is at most a constant
times `e^(-2π (|m| - 1))`, a summable majorant. Hence
`E₁^W` is bounded at `i∞` (`TauCeti.EisensteinSeries.isBoundedAtImInfty_weightedE1`), and with the
slash action at every cusp: `E₁^W` is a modular form of weight one and level `Γ(N)`
(`TauCeti.EisensteinSeries.weightedE1MF`). By dominated convergence along the rows, only the row
`m = 0` survives at `i∞`, contributing `π cot (π x)`. This tends to `-π i` if `a₀ ≠ 0` and is the
constant `π cot (π a₁ / N)` if `a₀ = 0`. So `E₁^W` tends to `N⁻¹ ∑_a W(a) c_a` with
`c_a = π i (2 a₀ / N - 1)` for `a₀ ≠ 0` and `c_a = π cot (π a₁ / N)` for `a₀ = 0`
(`TauCeti.EisensteinSeries.tendsto_weightedE1_atImInfty`). With the slash action this gives the
value at `i∞` of every `SL(2, ℤ)`-translate, that is, the constant terms of `E₁^W` at all cusps.

For the `q`-expansion each cotangent at a point `w` of the upper half-plane is expanded as
`π cot (π w) = -π i - 2π i ∑_{k ≥ 1} e(k w)`, with `e(w) = e^(2π i w)`
(`TauCeti.hasSum_pi_mul_cot_pi_mul_add_pi_mul_I`). In the row `m` at `x = (a₀ z + a₁) / N`, write
`x - m z = (n z + a₁) / N` with `n = a₀ - m N`: as `m` runs over `ℤ`, `n` runs over the residue
class of `a₀`, the classes `n = c ≥ 1` and `n = -c ≤ -1` expand in powers of `e(z / N)`, and the
cotangents `π cot (π m z)` cancel in pairs
(`TauCeti.hasSum_pi_mul_cot_pi_mul_intCast_mul_add_sign`,
`TauCeti.hasSum_pi_mul_cot_pi_mul_div_sub_intCast_mul_add_pi_mul_cot`). Hence `F_a` minus its
constant term `c_a` is
`-2π i ∑_{c, k ≥ 1} D_a(c, k) e(z / N)^(c k)`, where `D_a(c, k)` is `e(k a₁ / N)` if `c ≡ a₀`
minus `e(-k a₁ / N)` if `c ≡ -a₀`; the rows at the division points `z / 2` and `1 / 2` of the
quasi-periods have no nonconstant terms. Summing over `a`, `E₁^W` minus its value at `i∞` is
`-2π i / N ∑_{c, k ≥ 1} (∑_j (W(c, j) - W(-c, -j)) e(k j / N)) e(z / N)^(c k)`
(`TauCeti.EisensteinSeries.hasSum_weightedE1_sub_valueAtInfty`); only the odd part of `W` enters.

## Main definitions

* `TauCeti.EisensteinSeries.weightedE1`: the weight-one series weighted by `W`.
* `TauCeti.EisensteinSeries.weightedE1SIF`: it is a slash invariant form of weight one and level
  `Γ(N)`.
* `TauCeti.EisensteinSeries.weightedE1MF`: it is a modular form of weight one and level `Γ(N)`.
* `TauCeti.EisensteinSeries.weightedE1MFₗ`: the same, as a linear map in the weight.

## Main results

* `TauCeti.EisensteinSeries.weightedE1_slash_apply`: the slash action of `SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.weightedE1_mdifferentiable`: holomorphy on `ℍ`.
* `TauCeti.EisensteinSeries.weightedE1_comp_neg`,
  `TauCeti.EisensteinSeries.weightedE1_eq_zero_of_even`: the parity constraint.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_weightedE1_slash`: every `SL(2, ℤ)`-translate is
  bounded at `i∞`.
* `TauCeti.EisensteinSeries.tendsto_weightedE1_atImInfty`,
  `TauCeti.EisensteinSeries.valueAtInfty_weightedE1`: the limit at `i∞`.
* `TauCeti.EisensteinSeries.valueAtInfty_weightedE1_slash`: the value at `i∞` of every
  `SL(2, ℤ)`-translate.
* `TauCeti.EisensteinSeries.hasSum_weightedE1_sub_valueAtInfty`: the `q`-expansion in
  `e(z / N)`, as an absolutely convergent double series.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8, where
  the weight-one Eisenstein series of level `N` are constructed by Hecke's trick instead.
* M. Abramowitz and I. A. Stegun, *Handbook of mathematical functions*, Chapter 18, for `ζ` and
  its quasi-periods.
* The locally uniform convergence, and the bounds and limits at `i∞` by summing along rows,
  follow the weight-two argument of
  `TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted`, whose locally uniform
  convergence is modelled on Mathlib's `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly`
  (Chris Birkbeck and David Loeffler).
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Complex Filter Set PeriodPair
open EisensteinSeries
open TauCeti.UpperHalfPlane (tendsto_pi_mul_cot_pi_mul_add_pi_mul_I_atImInfty
  tendsto_pi_mul_cot_pi_mul_sub_pi_mul_I_atImInfty)

open scoped MatrixGroups Topology Manifold Real

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The weight-one Eisenstein series weighted by `W : (Fin 2 → ZMod N) → ℂ`:
`N⁻¹ ∑_a W(a) (ζ((a₀ z + a₁) / N) - (a₀ η₁ + a₁ η₂) / N)`, where `ζ` is the Weierstrass `ζ`
function of `ℤ z + ℤ`, `η₁ = η(z)` and `η₂ = η(1)` are its quasi-periods, and `a₀, a₁` are the
least nonnegative representatives of the residues. -/
def weightedE1 (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ a, W a * (z.periodPair.weierstrassZeta (((a 0).val * (z : ℂ) + (a 1).val) / N) -
    ((a 0).val * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ +
      (a 1).val * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩) / N)

lemma weightedE1_def (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) :
    weightedE1 W z =
      (N : ℂ)⁻¹ * ∑ a, W a *
        (z.periodPair.weierstrassZeta (((a 0).val * (z : ℂ) + (a 1).val) / N) -
          ((a 0).val * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ +
            (a 1).val * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩) / N) :=
  (rfl)

/-- The series is linear in the weight: the zero weight. -/
@[simp]
lemma weightedE1_zero : weightedE1 (0 : (Fin 2 → ZMod N) → ℂ) = 0 := by
  ext z
  simp [weightedE1]

/-- The series is linear in the weight: sums. -/
lemma weightedE1_add (W W' : (Fin 2 → ZMod N) → ℂ) :
    weightedE1 (W + W') = weightedE1 W + weightedE1 W' := by
  ext z
  simp [weightedE1, add_mul, Finset.sum_add_distrib, mul_add]

/-- The series is linear in the weight: scalar multiples. -/
lemma weightedE1_smul (c : ℂ) (W : (Fin 2 → ZMod N) → ℂ) :
    weightedE1 (c • W) = c • weightedE1 W := by
  ext z
  simp [weightedE1, Finset.mul_sum, mul_assoc, mul_left_comm]

/-! ### The corrected division values of `ζ` -/

/-- The least nonnegative representatives of a residue pair. -/
private def lift (a : Fin 2 → ZMod N) : Fin 2 → ℤ := fun i ↦ ((a i).val : ℤ)

private lemma intCast_comp_lift (a : Fin 2 → ZMod N) : ((↑) : ℤ → ZMod N) ∘ lift a = a := by
  ext i
  simp [lift]

omit [NeZero N] in
private lemma lift_zero : lift (0 : Fin 2 → ZMod N) = 0 := by
  ext i
  simp [lift]

/-- The corrected division value `ζ((b₀ z + b₁) / N) - (b₀ η₁ + b₁ η₂) / N` of an integer
pair `b`. -/
private def zetaValue (N : ℕ) (b : Fin 2 → ℤ) (z : ℍ) : ℂ :=
  z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / N) -
    ((b 0 : ℂ) * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ +
      b 1 * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩) / N

private lemma weightedE1_eq_sum_zetaValue (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) :
    weightedE1 W z = (N : ℂ)⁻¹ * ∑ a, W a * zetaValue N (lift a) z := by
  simp [weightedE1, zetaValue, lift]

omit [NeZero N] in
private lemma zetaValue_zero (z : ℍ) : zetaValue N 0 z = 0 := by
  simp [zetaValue]

omit [NeZero N] in
/-- The corrected division values are odd in the integer pair, as `ζ` is odd. -/
private lemma zetaValue_neg (b : Fin 2 → ℤ) (z : ℍ) : zetaValue N (-b) z = -zetaValue N b z := by
  simp only [zetaValue, Pi.neg_apply, Int.cast_neg, neg_mul, ← neg_add, neg_div]
  rw [weierstrassZeta_neg]
  ring

/-- **The corrected division values depend only on the residue**: the value of `b` is that of
the least nonnegative representatives of `b mod N`. Replacing `b` by `b + N y` moves the division
point by the lattice vector `y₀ z + y₁`, which changes `ζ` by its quasi-period `y₀ η₁ + y₁ η₂`,
and the correction by the same amount. -/
private lemma zetaValue_eq_lift (b : Fin 2 → ℤ) (z : ℍ) :
    zetaValue N b z = zetaValue N (lift (((↑) : ℤ → ZMod N) ∘ b)) z := by
  set c := lift (((↑) : ℤ → ZMod N) ∘ b)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdvd (i : Fin 2) : (N : ℤ) ∣ b i - c i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [c, lift]
  obtain ⟨m, hm⟩ := hdvd 0
  obtain ⟨n, hn⟩ := hdvd 1
  have hm' : (b 0 : ℂ) = c 0 + N * m := by
    rw [← sub_eq_iff_eq_add']
    exact_mod_cast hm
  have hn' : (b 1 : ℂ) = c 1 + N * n := by
    rw [← sub_eq_iff_eq_add']
    exact_mod_cast hn
  set l : z.periodPair.lattice := ⟨_, intCast_mul_add_intCast_mem_lattice_periodPair z m n⟩
  have hx : ((b 0 : ℂ) * z + b 1) / N = ((c 0 : ℂ) * z + c 1) / N + l := by
    simp only [l, hm', hn']
    field_simp
    ring
  have hl := z.periodPair.quasiPeriod_eq_intCast_mul_add l (m := m) (n := n) (by simp [l])
  simp only [zetaValue]
  rw [hx, weierstrassZeta_add_coe, hl, hm', hn']
  field_simp
  ring

omit [NeZero N] in
/-- **The slash action on one corrected division value**: the lattice of `γ z` is `(c z + d)⁻¹`
times that of `z`, and both `ζ` and its quasi-periods scale by `c z + d`. -/
private lemma zetaValue_smul (γ : SL(2, ℤ)) (b : Fin 2 → ℤ) (z : ℍ) :
    zetaValue N b (γ • z) = denom γ z * zetaValue N (b ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) z := by
  set b' := b ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  set l : z.periodPair.lattice :=
    ⟨_, intCast_mul_add_intCast_mem_lattice_periodPair z (b' 0) (b' 1)⟩
  have hb := intCast_mul_smul_add_intCast γ z b
  -- the quasi-periods of `γ z` at `b₀ γz + b₁`, which is `l / (c z + d)`
  have hη := (γ • z).periodPair.quasiPeriod_eq_intCast_mul_add
    ⟨_, (div_denom_mem_lattice_periodPair_smul_iff γ z l).mpr l.2⟩ (m := b 0) (n := b 1)
    (by simpa [l] using hb)
  rw [quasiPeriod_periodPair_smul,
    z.periodPair.quasiPeriod_eq_intCast_mul_add l (m := b' 0) (n := b' 1) (by simp [l])] at hη
  simp only [zetaValue]
  rw [← hη, hb, div_right_comm, weierstrassZeta_periodPair_smul]
  ring

/-- The slash action on the corrected division value of a residue pair. -/
private lemma zetaValue_lift_smul (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) (z : ℍ) :
    zetaValue N (lift a) (γ • z) = denom γ z *
      zetaValue N (lift (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) z := by
  rw [zetaValue_smul, zetaValue_eq_lift (lift a ᵥ* _), intCast_comp_vecMul, intCast_comp_lift]

/-- The corrected division value of `-a` is minus that of `a`. -/
private lemma zetaValue_lift_neg (a : Fin 2 → ZMod N) (z : ℍ) :
    zetaValue N (lift (-a)) z = -zetaValue N (lift a) z := by
  have hcast : ((↑) : ℤ → ZMod N) ∘ (-lift a) = -a := by
    rw [← intCast_comp_lift (-a), intCast_comp_lift]
    ext i
    simp [lift]
  rw [← zetaValue_neg, zetaValue_eq_lift (-lift a), hcast]

/-! ### The slash action -/

/-- **The slash action on a weighted weight-one series.** Slashing by `γ ∈ SL(2, ℤ)` replaces the
weight `W` by `a ↦ W (a γ⁻¹)`. -/
theorem weightedE1_slash_apply (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    weightedE1 W ∣[(1 : ℤ)] γ = weightedE1 (fun a ↦
      W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) := by
  ext z
  have hD := denom_ne_zero γ z
  simp_rw [SL_slash_apply, weightedE1_eq_sum_zetaValue, zetaValue_lift_smul]
  have hsum : ∑ a, W a * (denom γ z * zetaValue N
        (lift (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) z) =
      denom γ z * ∑ a, W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N))) * zetaValue N (lift a) z := by
    rw [Finset.mul_sum]
    -- reindex the residues by `a ↦ a γ`
    have h₂ : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
      (Matrix.SpecialLinearGroup.sum_comp_vecMul _ (γ : SL(2, ZMod N)))
    simp only [Matrix.vecMul_vecMul, h₂, Matrix.vecMul_one]
    ring
  rw [hsum, _root_.zpow_neg, zpow_one]
  field_simp

/-- The weighted weight-one series as a slash invariant form of level `Γ(N)`: an element of
`Γ(N)` reduces to the identity modulo `N`, so it does not change the weight. -/
def weightedE1SIF (W : (Fin 2 → ZMod N) → ℂ) : SlashInvariantForm Γ(N) 1 where
  toFun := weightedE1 W
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, weightedE1_slash_apply,
      Gamma_mem'.mp (inv_mem hA)]

@[simp]
lemma coe_weightedE1SIF (W : (Fin 2 → ZMod N) → ℂ) : ⇑(weightedE1SIF W) = weightedE1 W := (rfl)

/-! ### Parity -/

/-- **Replacing the weight by `a ↦ W (-a)` changes the sign of the series**, as `ζ` is odd. -/
theorem weightedE1_comp_neg (W : (Fin 2 → ZMod N) → ℂ) :
    weightedE1 (fun a ↦ W (-a)) = -weightedE1 W := by
  ext z
  simp only [weightedE1_eq_sum_zetaValue, Pi.neg_apply]
  rw [← Equiv.sum_comp (Equiv.neg (Fin 2 → ZMod N))]
  simp [zetaValue_lift_neg, Finset.sum_neg_distrib]

/-- **The parity constraint of weight one**: the series of an even weight vanishes. -/
theorem weightedE1_eq_zero_of_even {W : (Fin 2 → ZMod N) → ℂ} (hW : W.Even) :
    weightedE1 W = 0 := by
  have h := weightedE1_comp_neg W
  have hW' : (fun a ↦ W (-a)) = W := funext hW
  rw [hW'] at h
  ext z
  exact CharZero.eq_neg_self_iff.mp (congrFun h z)

/-! ### Holomorphy -/

/-- The corrected division values are holomorphic on `ℍ`: the quasi-periods are the division
values `η₁ = 2 ζ(z / 2)` and `η₂ = 2 ζ(1 / 2)`. -/
private lemma mdifferentiable_zetaValue (b : Fin 2 → ℤ) : MDiff (zetaValue N b) := by
  have h₁ : MDiff fun z : ℍ ↦ z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ := by
    convert (mdifferentiable_const (c := (2 : ℂ))).mul
      (TauCeti.UpperHalfPlane.mdifferentiable_weierstrassZeta_periodPair_div 2 ![1, 0]) using 1
    ext z
    rw [quasiPeriod_eq_two_mul_weierstrassZeta]
    simp
  have h₂ : MDiff fun z : ℍ ↦ z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩ := by
    convert (mdifferentiable_const (c := (2 : ℂ))).mul
      (TauCeti.UpperHalfPlane.mdifferentiable_weierstrassZeta_periodPair_div 2 ![0, 1]) using 1
    ext z
    rw [quasiPeriod_eq_two_mul_weierstrassZeta]
    simp
  exact (TauCeti.UpperHalfPlane.mdifferentiable_weierstrassZeta_periodPair_div N b).sub
    (((mdifferentiable_const.mul h₁).add (mdifferentiable_const.mul h₂)).mul mdifferentiable_const)

/-- **The weighted weight-one series is holomorphic on `ℍ`.** -/
theorem weightedE1_mdifferentiable (W : (Fin 2 → ZMod N) → ℂ) : MDiff (weightedE1 W) := by
  have h : weightedE1 W = fun z ↦ (N : ℂ)⁻¹ * ∑ a, W a * zetaValue N (lift a) z :=
    funext (weightedE1_eq_sum_zetaValue W)
  rw [h]
  refine mdifferentiable_const.mul ?_
  convert MDifferentiable.sum (t := Finset.univ)
    (f := fun a (z : ℍ) ↦ W a * zetaValue N (lift a) z)
    fun a _ ↦ mdifferentiable_const.mul (mdifferentiable_zetaValue (lift a)) using 1
  ext z
  simp [Finset.sum_apply]

/-! ### Summing along rows -/

/-- The cotangent part `π cot (π (x - m z)) + π cot (π m z)` of the row `m` of the lattice series
of `ζ` at `x`; the full row also contains `x ∑_n (m z + n)⁻²`. -/
private def cotRow (x : ℂ) (m : ℤ) (z : ℍ) : ℂ :=
  π * cot (π * (x - m * z)) + π * cot (π * (m * z))

/-- The row `m` of the corrected division value of `a`, in cotangents. -/
private def zetaRow (a : Fin 2 → ZMod N) (m : ℤ) (z : ℍ) : ℂ :=
  cotRow (((a 0).val * (z : ℂ) + (a 1).val) / N) m z -
    2 * (a 0).val / N * cotRow (z / 2) m z - 2 * (a 1).val / N * cotRow (1 / 2) m z

/-- **The corrected division values as series of cotangent rows.** With `η₁ = 2 ζ(z / 2)` and
`η₂ = 2 ζ(1 / 2)`, the value at a nonzero residue `a` is
`ζ(x) - 2 (a₀ / N) ζ(z / 2) - 2 (a₁ / N) ζ(1 / 2)` with `x = (a₀ z + a₁) / N`. Summing the three
lattice series along rows, the parts `x ∑_n (m z + n)⁻²` of the rows cancel, leaving cotangents. -/
private lemma hasSum_zetaValue_lift {a : Fin 2 → ZMod N} (ha : a ≠ 0) (z : ℍ) :
    HasSum (fun m ↦ zetaRow a m z) (zetaValue N (lift a) z) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx : ((a 0).val * (z : ℂ) + (a 1).val) / N ∉ z.periodPair.lattice := fun h ↦ ha <| by
    rw [← intCast_comp_lift a]
    exact intCast_comp_eq_zero_of_div_mem_lattice_periodPair (by simpa [lift] using h)
  have h₁ := hasSum_weierstrassZeta_periodPair_rows z hx
  have h₂ := hasSum_weierstrassZeta_periodPair_rows z z.periodPair.ω₁_div_two_notMem_lattice
  have h₃ := hasSum_weierstrassZeta_periodPair_rows z z.periodPair.ω₂_div_two_notMem_lattice
  have hη₁ := z.periodPair.quasiPeriod_eq_two_mul_weierstrassZeta
    ⟨_, z.periodPair.ω₁_mem_lattice⟩
  have hη₂ := z.periodPair.quasiPeriod_eq_two_mul_weierstrassZeta
    ⟨_, z.periodPair.ω₂_mem_lattice⟩
  simp only [periodPair_ω₁, periodPair_ω₂] at h₂ h₃ hη₁ hη₂
  convert (h₁.sub (h₂.mul_left (2 * (a 0).val / N : ℂ))).sub
    (h₃.mul_left (2 * (a 1).val / N : ℂ)) using 1
  · ext m
    simp only [zetaRow, cotRow]
    field_simp
    ring
  · simp only [zetaValue, lift, Int.cast_natCast, periodPair_ω₁, periodPair_ω₂] at hη₁ hη₂ ⊢
    rw [hη₁, hη₂]
    field_simp
    ring

/-! ### Boundedness at infinity -/

/-- The decay constant of the cotangents at points with `|Im| ≥ 1 / M`. -/
private def cotConst (M : ℕ) : ℝ := 2 * π / (1 - Real.exp (-2 * π * (1 / M)))

private lemma cotConst_nonneg (M : ℕ) : 0 ≤ cotConst M := by
  refine div_nonneg (by positivity) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr ?_))
  have : 0 ≤ π * (1 / (M : ℝ)) := by positivity
  linarith

/-- The bounds for the cotangent rows at `(b₀ z + b₁) / M`: a summable majorant independent of
`z` on `1 ≤ Im z`. -/
private def rowBound (M b₁ : ℕ) (m : ℤ) : ℝ :=
  2 * cotConst M * Real.exp (-2 * π * (|(m : ℝ)| - 1)) +
    if m = 0 then cotConst M + π + ‖π * cot (π * (b₁ / M))‖ else 0

private lemma rowBound_nonneg (M b₁ : ℕ) (m : ℤ) : 0 ≤ rowBound M b₁ m := by
  have := cotConst_nonneg M
  unfold rowBound
  split_ifs <;> positivity

private lemma summable_rowBound (M b₁ : ℕ) : Summable (rowBound M b₁) :=
  (summable_exp_neg_two_pi_mul_abs_sub_one.mul_left _).add
    (summable_of_ne_finset_zero (s := {0}) fun m hm ↦ by simp_all)

/-- The cotangent row `m = 0` at a division point is bounded: it is `π cot (π x)`, which is
bounded by `cotConst M + π` if `b₀ ≠ 0` and is the constant `π cot (π b₁ / M)` if `b₀ = 0`. -/
private lemma norm_cotRow_zero_le {M b₀ b₁ : ℕ} (hM : 0 < M) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖cotRow ((b₀ * (z : ℂ) + b₁) / M) 0 z‖ ≤ rowBound M b₁ 0 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  simp only [cotRow, Int.cast_zero, zero_mul, sub_zero, mul_zero, cot_zero, add_zero, rowBound,
    ↓reduceIte]
  refine le_add_of_nonneg_of_le (by positivity [cotConst_nonneg M]) ?_
  rcases Nat.eq_zero_or_pos b₀ with hb₀ | hb₀
  · simp only [hb₀, CharP.cast_eq_zero, zero_mul, zero_add]
    exact le_add_of_nonneg_left (by positivity [cotConst_nonneg M])
  have hx : 1 / (M : ℝ) ≤ ((b₀ * (z : ℂ) + b₁) / M).im := by
    have h : ((b₀ * (z : ℂ) + b₁) / M - ((0 : ℤ) : ℂ) * z).im =
        ((b₀ : ℝ) / M - ((0 : ℤ) : ℝ)) * z.im := by
      exact_mod_cast im_ofReal_mul_add_ofReal_div_sub_ofReal_mul b₀ b₁ M 0 z
    simp only [Int.cast_zero, zero_mul, sub_zero] at h
    rw [h]
    have : 1 / (M : ℝ) ≤ b₀ / M := by
      gcongr
      exact_mod_cast hb₀
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ b₀ / M) (sub_nonneg.2 hz)]
  exact (norm_pi_mul_cot_pi_mul_le (div_pos one_pos hM') hx).trans
    (le_add_of_nonneg_right (norm_nonneg _))

/-- **The cotangent rows `m ≠ 0` at a division point are bounded** on `1 ≤ Im z`: for
`x = (b₀ z + b₁) / M` with `b₀ < M`, the imaginary parts of `x - m z` and of `m z` have opposite
signs and absolute values at least `max (1 / M) (|m| - 1)`, so the two cotangents approach
`± π i` with opposite signs. -/
private lemma norm_cotRow_le_of_ne_zero {M b₀ b₁ : ℕ} (hb : b₀ < M) {m : ℤ} (hm : m ≠ 0)
    {z : ℍ} (hz : 1 ≤ z.im) :
    ‖cotRow ((b₀ * (z : ℂ) + b₁) / M) m z‖ ≤ rowBound M b₁ m := by
  have hM : 0 < M := by omega
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  -- the imaginary part of `x - m z` is `(b₀ / M - m) Im z`, with `b₀ / M ≤ 1 - 1 / M`
  have hc1 := Nat.cast_div_le_one_sub_inv (α := ℝ) hb
  have him : ((b₀ * (z : ℂ) + b₁) / M - m * z).im = ((b₀ : ℝ) / M - m) * (z : ℂ).im := by
    exact_mod_cast im_ofReal_mul_add_ofReal_div_sub_ofReal_mul b₀ b₁ M m z
  set c : ℝ := b₀ / M
  have hc0 : 0 ≤ c := by positivity
  have him' : ((m : ℂ) * z).im = m * z.im := by simp
  have hM1 : 1 / (M : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hM) hM'.le
  have hrow : cotRow ((b₀ * (z : ℂ) + b₁) / M) m z =
      π * cot (π * ((b₀ * (z : ℂ) + b₁) / M - m * z)) + π * cot (π * (m * z)) := by
    simp only [cotRow]
  simp only [rowBound, hm, ↓reduceIte, add_zero]
  rcases hm.lt_or_gt with hm | hm
  · -- `m < 0`: `x - m z` lies in the upper and `m z` in the lower half-plane
    have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm
    have habs : |(m : ℝ)| = -m := abs_of_neg (by exact_mod_cast hm)
    have h₁ : -(m : ℝ) ≤ ((b₀ * (z : ℂ) + b₁) / M - m * z).im := by
      rw [him, UpperHalfPlane.coe_im]
      nlinarith
    have h₂ : -(m : ℝ) ≤ -((m : ℂ) * z).im := by
      rw [him']
      nlinarith
    rw [hrow, habs]
    exact norm_pi_mul_cot_pi_mul_add_pi_mul_cot_pi_mul_le (div_pos one_pos hM')
      (hM1.trans (by linarith)) (by linarith) (hM1.trans (by linarith)) (by linarith)
  · -- `m > 0`: `x - m z` lies in the lower and `m z` in the upper half-plane
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have habs : |(m : ℝ)| = m := abs_of_pos (by exact_mod_cast hm)
    have hmc : 1 / (M : ℝ) ≤ m - c := by linarith
    have hmc' : (m : ℝ) - c ≤ (m - c) * z.im :=
      le_mul_of_one_le_right ((div_pos one_pos hM').le.trans hmc) hz
    have h₁ : 1 / (M : ℝ) ≤ -((b₀ * (z : ℂ) + b₁) / M - m * z).im := by
      rw [him, UpperHalfPlane.coe_im]
      linarith
    have h₁' : (m : ℝ) - 1 ≤ -((b₀ * (z : ℂ) + b₁) / M - m * z).im := by
      rw [him, UpperHalfPlane.coe_im]
      linarith [div_pos one_pos hM']
    have h₂ : (m : ℝ) ≤ ((m : ℂ) * z).im := by
      rw [him']
      nlinarith
    rw [hrow, add_comm, habs]
    exact norm_pi_mul_cot_pi_mul_add_pi_mul_cot_pi_mul_le (div_pos one_pos hM')
      (hM1.trans (by linarith)) (by linarith) h₁ h₁'

/-- **The cotangent rows at a division point are bounded** on `1 ≤ Im z`. -/
private lemma norm_cotRow_le {M b₀ b₁ : ℕ} (hb : b₀ < M) (m : ℤ) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖cotRow ((b₀ * (z : ℂ) + b₁) / M) m z‖ ≤ rowBound M b₁ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact norm_cotRow_zero_le (by omega) hz
  · exact norm_cotRow_le_of_ne_zero hb hm hz

/-- The summable majorant of the rows of the corrected division values on `1 ≤ Im z`. -/
private def zetaBound (N b₁ : ℕ) (m : ℤ) : ℝ :=
  rowBound N b₁ m + 2 * rowBound 2 0 m + 2 * rowBound 2 1 m

omit [NeZero N] in
private lemma summable_zetaBound (b₁ : ℕ) : Summable (zetaBound N b₁) :=
  ((summable_rowBound _ _).add ((summable_rowBound 2 0).mul_left 2)).add
    ((summable_rowBound 2 1).mul_left 2)

/-- The `z / 2` and `1 / 2` of `η₁ = 2 ζ(z / 2)` and `η₂ = 2 ζ(1 / 2)` as division points. -/
private lemma div_two_eq (z : ℍ) :
    (z : ℂ) / 2 = (((1 : ℕ) : ℂ) * z + ((0 : ℕ) : ℂ)) / ((2 : ℕ) : ℂ) ∧
      (1 : ℂ) / 2 = (((0 : ℕ) : ℂ) * z + ((1 : ℕ) : ℂ)) / ((2 : ℕ) : ℂ) := by
  simp

/-- Each row of a corrected division value is bounded by `zetaBound` on `1 ≤ Im z`. -/
private lemma norm_zetaRow_le (a : Fin 2 → ZMod N) (m : ℤ) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖zetaRow a m z‖ ≤ zetaBound N (a 1).val m := by
  -- the coefficients `2 r / N` of the rows at `z / 2` and `1 / 2` are at most `2`
  have hcoeff (r : ZMod N) : ‖(2 * r.val / N : ℂ)‖ ≤ 2 := by
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    rw [show (2 * r.val / N : ℂ) = ((2 * r.val / N : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hN]
    have : (r.val : ℝ) ≤ N := by exact_mod_cast (ZMod.val_lt r).le
    nlinarith
  have r₁ := norm_cotRow_le (b₁ := (a 1).val) (ZMod.val_lt (a 0)) m hz
  have r₂ := norm_cotRow_le (M := 2) (b₀ := 1) (b₁ := 0) (by norm_num) m hz
  have r₃ := norm_cotRow_le (M := 2) (b₀ := 0) (b₁ := 1) (by norm_num) m hz
  rw [← (div_two_eq z).1] at r₂
  rw [← (div_two_eq z).2] at r₃
  calc _ ≤ ‖cotRow (((a 0).val * (z : ℂ) + (a 1).val) / N) m z‖ +
        ‖(2 * (a 0).val / N : ℂ)‖ * ‖cotRow (z / 2) m z‖ +
          ‖(2 * (a 1).val / N : ℂ)‖ * ‖cotRow (1 / 2) m z‖ := by
        rw [← norm_mul, ← norm_mul]
        exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ rowBound N (a 1).val m + 2 * rowBound 2 0 m + 2 * rowBound 2 1 m := by
        gcongr
        all_goals exact hcoeff _

/-- Each corrected division value is bounded on `1 ≤ Im z`, by summing along rows. -/
private lemma norm_zetaValue_lift_le (a : Fin 2 → ZMod N) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖zetaValue N (lift a) z‖ ≤ ∑' m, zetaBound N (a 1).val m := by
  by_cases ha : a = 0
  · rw [ha, lift_zero, zetaValue_zero, norm_zero]
    exact tsum_nonneg fun m ↦ by
      have := rowBound_nonneg N 0 m
      have := rowBound_nonneg 2 0 m
      have := rowBound_nonneg 2 1 m
      simp only [zetaBound, ZMod.val_zero, Pi.zero_apply]
      positivity
  exact (hasSum_zetaValue_lift ha z).norm_le_of_bounded (summable_zetaBound _).hasSum
    fun m ↦ norm_zetaRow_le a m hz

/-- **The weighted weight-one series is bounded at `i∞`.** -/
theorem isBoundedAtImInfty_weightedE1 (W : (Fin 2 → ZMod N) → ℂ) :
    IsBoundedAtImInfty (weightedE1 W) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨‖(N : ℂ)⁻¹‖ * ∑ a, ‖W a‖ * ∑' m, zetaBound N (a 1).val m, 1, fun z hz ↦ ?_⟩
  rw [weightedE1_eq_sum_zetaValue, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [norm_mul]
  gcongr
  exact norm_zetaValue_lift_le a hz

/-- Every `SL(2, ℤ)`-translate of the weighted weight-one series is bounded at `i∞`. -/
theorem isBoundedAtImInfty_weightedE1_slash (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (weightedE1 W ∣[(1 : ℤ)] γ) := by
  rw [weightedE1_slash_apply]
  exact isBoundedAtImInfty_weightedE1 _

/-! ### The value at infinity -/

omit [NeZero N] in
/-- **The limit at `i∞` of a cotangent row** at `x = (b₀ z + b₁) / M` with `b₀ < M`: the rows
`m ≠ 0` vanish, and the row `m = 0` is `π cot (π x)`, which tends to `-π i` if `b₀ ≠ 0` and is
the constant `π cot (π b₁ / M)` if `b₀ = 0`. -/
private lemma tendsto_cotRow_atImInfty {M b₀ b₁ : ℕ} (hb : b₀ < M) (m : ℤ) :
    Tendsto (fun z : ℍ ↦ cotRow ((b₀ * (z : ℂ) + b₁) / M) m z) atImInfty
      (𝓝 (if m = 0 then (if b₀ = 0 then π * cot (π * (b₁ / M)) else -(π * Complex.I))
        else 0)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_le _).trans_lt hb
  have hc1 := Nat.cast_div_le_one_sub_inv (α := ℝ) hb
  have him (m : ℤ) (z : ℍ) :
      ((b₀ * (z : ℂ) + b₁) / M - m * z).im = ((b₀ : ℝ) / M - m) * (z : ℂ).im := by
    exact_mod_cast im_ofReal_mul_add_ofReal_div_sub_ofReal_mul b₀ b₁ M m z
  have hc0 : (0 : ℝ) ≤ b₀ / M := by positivity
  have hM1 : 0 < 1 / (M : ℝ) := div_pos one_pos hM'
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · -- `m < 0`
    have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm
    have h₁ := tendsto_pi_mul_cot_pi_mul_add_pi_mul_I_atImInfty
      (w := fun z : ℍ ↦ (b₀ * (z : ℂ) + b₁) / M - m * z) one_pos fun z ↦ by
        rw [him, UpperHalfPlane.coe_im]
        nlinarith [z.im_pos]
    have h₂ := tendsto_pi_mul_cot_pi_mul_sub_pi_mul_I_atImInfty (w := fun z : ℍ ↦ (m : ℂ) * z)
      one_pos fun z ↦ by
      simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, zero_mul, add_zero]
      nlinarith [z.im_pos]
    simp only [hm.ne, ↓reduceIte]
    simpa [cotRow, add_add_sub_cancel] using h₁.add h₂
  · -- `m = 0`
    simp only [cotRow, ↓reduceIte, Int.cast_zero, zero_mul, sub_zero, mul_zero, cot_zero,
      add_zero]
    split_ifs with hb₀
    · refine tendsto_const_nhds.congr fun z ↦ ?_
      simp [hb₀]
    have h := tendsto_pi_mul_cot_pi_mul_add_pi_mul_I_atImInfty
      (w := fun z : ℍ ↦ (b₀ * (z : ℂ) + b₁) / M) (c := 1 / M) hM1 fun z ↦ by
        have h := him 0 z
        simp only [Int.cast_zero, zero_mul, sub_zero] at h
        rw [h, UpperHalfPlane.coe_im]
        have : 1 / (M : ℝ) ≤ b₀ / M := by
          gcongr
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb₀
        nlinarith [z.im_pos]
    simpa using h.sub_const (π * Complex.I)
  · -- `m > 0`
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h₁ := tendsto_pi_mul_cot_pi_mul_sub_pi_mul_I_atImInfty
      (w := fun z : ℍ ↦ (b₀ * (z : ℂ) + b₁) / M - m * z) hM1 fun z ↦ by
        rw [him, UpperHalfPlane.coe_im]
        nlinarith [z.im_pos]
    have h₂ := tendsto_pi_mul_cot_pi_mul_add_pi_mul_I_atImInfty (w := fun z : ℍ ↦ (m : ℂ) * z)
      one_pos fun z ↦ by
      simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, zero_mul, add_zero]
      nlinarith [z.im_pos]
    simp only [hm.ne', ↓reduceIte]
    simpa [cotRow, sub_add_add_cancel] using h₁.add h₂

/-- The constant term of the corrected division value of `a`: `π cot (π a₁ / N)` if `a₀ = 0`, and
`π i (2 a₀ / N - 1)` otherwise, `a₀, a₁` being the least nonnegative representatives. -/
private def zetaValueLimit (a : Fin 2 → ZMod N) : ℂ :=
  if (a 0).val = 0 then π * cot (π * ((a 1).val / N)) else π * Complex.I * (2 * (a 0).val / N - 1)

/-- The limit at `i∞` of a corrected division value, by dominated convergence along the rows. -/
private lemma tendsto_zetaValue_lift_atImInfty (a : Fin 2 → ZMod N) :
    Tendsto (zetaValue N (lift a)) atImInfty (𝓝 (zetaValueLimit a)) := by
  by_cases ha : a = 0
  · subst ha
    have h0 : zetaValue N (lift (0 : Fin 2 → ZMod N)) = fun _ ↦ 0 :=
      funext fun z ↦ by rw [lift_zero, zetaValue_zero]
    rw [h0]
    simp [zetaValueLimit]
  have hfun : zetaValue N (lift a) = fun z ↦ ∑' m, zetaRow a m z :=
    funext fun z ↦ (hasSum_zetaValue_lift ha z).tsum_eq.symm
  have hrow (m : ℤ) : Tendsto (fun z ↦ zetaRow a m z) atImInfty
      (𝓝 (if m = 0 then zetaValueLimit a else 0)) := by
    have t₁ := tendsto_cotRow_atImInfty (b₁ := (a 1).val) (ZMod.val_lt (a 0)) m
    have t₂ := tendsto_cotRow_atImInfty (M := 2) (b₀ := 1) (b₁ := 0) (by norm_num) m
    have t₃ := tendsto_cotRow_atImInfty (M := 2) (b₀ := 0) (b₁ := 1) (by norm_num) m
    simp only [← (div_two_eq _).1, ← (div_two_eq _).2] at t₂ t₃
    unfold zetaRow
    convert (t₁.sub (t₂.const_mul (2 * (a 0).val / N : ℂ))).sub
      (t₃.const_mul (2 * (a 1).val / N : ℂ)) using 2
    -- `cot (π / 2) = 0`, in the two forms produced by `simp`
    have hcot : cot (π * (1 / 2)) = 0 := by
      rw [Complex.cot_eq_cos_div_sin, ← div_eq_mul_one_div, Complex.cos_pi_div_two, zero_div]
    have hcot' : cot (π * 2⁻¹) = 0 := by
      rw [← one_div, hcot]
    rcases eq_or_ne m 0 with rfl | hm
    · by_cases hb₀ : (a 0).val = 0
      · simp [zetaValueLimit, hb₀, hcot']
      · simp only [zetaValueLimit, hb₀]
        simp only [Nat.cast_one, Nat.cast_ofNat, hcot, ↓reduceIte, one_ne_zero, mul_zero]
        ring
    · simp [hm]
  rw [hfun]
  convert tendsto_tsum_of_dominated_convergence (summable_zetaBound (N := N) (a 1).val) hrow ?_
    using 2
  · rw [tsum_ite_eq]
  filter_upwards [(tendsto_comap : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop).eventually_ge_atTop
    1] with z hz m
  exact norm_zetaRow_le a m hz

/-- **The limit at `i∞` of the weighted weight-one series**: `E₁^W` tends to
`N⁻¹ ∑_a W(a) c_a`, where `c_a = π cot (π a₁ / N)` if `a₀ = 0` and `c_a = π i (2 a₀ / N - 1)`
otherwise, `a₀, a₁` being the least nonnegative representatives. -/
theorem tendsto_weightedE1_atImInfty (W : (Fin 2 → ZMod N) → ℂ) :
    Tendsto (weightedE1 W) atImInfty
      (𝓝 ((N : ℂ)⁻¹ * ∑ a, W a * if (a 0).val = 0 then π * cot (π * ((a 1).val / N))
        else π * Complex.I * (2 * (a 0).val / N - 1))) := by
  have h := (tendsto_finsetSum Finset.univ fun a _ ↦
    (tendsto_zetaValue_lift_atImInfty (N := N) a).const_mul (W a)).const_mul (N : ℂ)⁻¹
  unfold zetaValueLimit at h
  convert h using 2 with z
  exact weightedE1_eq_sum_zetaValue W z

/-- The value at `i∞` of the weighted weight-one series: `N⁻¹ ∑_a W(a) c_a`, where
`c_a = π cot (π a₁ / N)` if `a₀ = 0` and `c_a = π i (2 a₀ / N - 1)` otherwise. -/
theorem valueAtInfty_weightedE1 (W : (Fin 2 → ZMod N) → ℂ) :
    valueAtInfty (weightedE1 W) = (N : ℂ)⁻¹ * ∑ a, W a *
      if (a 0).val = 0 then π * cot (π * ((a 1).val / N))
      else π * Complex.I * (2 * (a 0).val / N - 1) :=
  (tendsto_weightedE1_atImInfty W).limUnder_eq

/-- **The value at `i∞` of a translated weighted weight-one series**: slashing by `γ` replaces the
weight `W` by `a ↦ W (a γ⁻¹)`, so the constant term at the cusp `γ ∞` is
`N⁻¹ ∑_a W(a γ⁻¹) c_a`. -/
theorem valueAtInfty_weightedE1_slash (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    valueAtInfty (weightedE1 W ∣[(1 : ℤ)] γ) = (N : ℂ)⁻¹ * ∑ a,
      W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) *
        if (a 0).val = 0 then π * cot (π * ((a 1).val / N))
        else π * Complex.I * (2 * (a 0).val / N - 1) := by
  rw [weightedE1_slash_apply, valueAtInfty_weightedE1]

/-! ### The `q`-expansion -/

/-- The coefficient of `e^(2π i c k z / M)` in the cotangent rows at the division point
`(b₀ z + b₁) / M`: `e(k b₁ / M)` if `c ≡ b₀` minus `e(-k b₁ / M)` if `c ≡ -b₀` modulo `M`. -/
private def divCoeff (M b₀ b₁ c k : ℕ) [NeZero M] : ℂ :=
  (if (c : ZMod M) = b₀ then ZMod.stdAddChar ((k : ZMod M) * (b₁ : ZMod M)) else 0) -
    if (c : ZMod M) = -(b₀ : ZMod M) then ZMod.stdAddChar (-((k : ZMod M) * (b₁ : ZMod M))) else 0

private lemma norm_divCoeff_le (M b₀ b₁ c k : ℕ) [NeZero M] : ‖divCoeff M b₀ b₁ c k‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  have h₁ : ‖(if (c : ZMod M) = b₀ then ZMod.stdAddChar ((k : ZMod M) * (b₁ : ZMod M))
      else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> simp
  have h₂ : ‖(if (c : ZMod M) = -(b₀ : ZMod M) then
      ZMod.stdAddChar (-((k : ZMod M) * (b₁ : ZMod M))) else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> simp
  linarith

omit [NeZero N] in
/-- The rows at the division points `z / 2` and `1 / 2` of the quasi-periods have no
nonconstant terms, as `1 ≡ -1` modulo `2`. -/
private lemma divCoeff_two_one_zero (c k : ℕ) : divCoeff 2 1 0 c k = 0 := by
  simp [divCoeff, ZMod.neg_eq_self_mod_two]

omit [NeZero N] in
private lemma divCoeff_two_zero_one (c k : ℕ) : divCoeff 2 0 1 c k = 0 := by
  simp [divCoeff, ZMod.neg_eq_self_mod_two]

/-- **The `q`-expansion of a corrected division value**: `F_a - c_a` is
`-2π i ∑_{c, k ≥ 1} D_a(c, k) e(z / N)^(c k)`, where `c_a` is the constant term
`zetaValueLimit a`. The rows at `z / 2` and `1 / 2` of the quasi-periods contribute only their
constants `-π i` and `0`. -/
private lemma hasSum_zetaValue_lift_sub (a : Fin 2 → ZMod N) (z : ℍ) :
    HasSum (fun p : ℕ+ × ℕ+ ↦ -2 * π * Complex.I * divCoeff N (a 0).val (a 1).val p.1 p.2 *
        cexp (2 * π * Complex.I * z / N) ^ ((p.1 : ℕ) * p.2))
      (zetaValue N (lift a) z - zetaValueLimit a) := by
  have hs : Summable fun p : ℕ+ × ℕ+ ↦ -2 * π * Complex.I *
      divCoeff N (a 0).val (a 1).val p.1 p.2 *
        cexp (2 * π * Complex.I * z / N) ^ ((p.1 : ℕ) * p.2) :=
    summable_mul_pow_mul (by simpa [Function.Periodic.qParam] using
      UpperHalfPlane.norm_qParam_lt_one N z) (C := ‖-2 * π * Complex.I‖ * 2) fun p ↦ by
      rw [norm_mul]
      gcongr
      exact norm_divCoeff_le ..
  convert hs.hasSum using 1
  by_cases ha : a = 0
  · subst ha
    simp [lift_zero, zetaValue_zero, zetaValueLimit, divCoeff]
  have hcot : cot (π * (1 / 2)) = 0 := by
    rw [Complex.cot_eq_cos_div_sin, ← div_eq_mul_one_div, Complex.cos_pi_div_two, zero_div]
  have hcot' : cot (π * 2⁻¹) = 0 := by
    rw [← one_div, hcot]
  -- the cotangent rows at the division point `(b₀ z + b₁) / M`
  have hdiv {M b₀ : ℕ} [NeZero M] (hb : b₀ < M) (b₁ : ℕ) :
      HasSum (fun m ↦ cotRow ((b₀ * (z : ℂ) + b₁) / M) m z)
        ((if b₀ = 0 then π * cot (π * (b₁ / M)) else -(π * Complex.I)) +
          ∑' p : ℕ+ × ℕ+, -2 * π * Complex.I * divCoeff M b₀ b₁ p.1 p.2 *
            cexp (2 * π * Complex.I * z / M) ^ ((p.1 : ℕ) * p.2)) := by
    simpa [cotRow, divCoeff] using
      hasSum_pi_mul_cot_pi_mul_div_sub_intCast_mul_add_pi_mul_cot hb (b₁ : ℤ) z.im_pos
  have h₁ := hdiv (ZMod.val_lt (a 0)) (a 1).val
  have h₂ := hdiv (M := 2) (b₀ := 1) (by norm_num) 0
  have h₃ := hdiv (M := 2) (b₀ := 0) (by norm_num) 1
  rw [← (div_two_eq z).1] at h₂
  rw [← (div_two_eq z).2] at h₃
  have h₂' : HasSum (fun m ↦ cotRow (z / 2) m z) (-(π * Complex.I)) := by
    simpa [divCoeff_two_one_zero] using h₂
  have h₃' : HasSum (fun m ↦ cotRow (1 / 2) m z) 0 := by
    simpa [divCoeff_two_zero_one, hcot'] using h₃
  have hrow : HasSum (fun m ↦ zetaRow a m z) _ :=
    (h₁.sub (h₂'.mul_left (2 * (a 0).val / N : ℂ))).sub (h₃'.mul_left (2 * (a 1).val / N : ℂ))
  rw [(hasSum_zetaValue_lift ha z).unique hrow, zetaValueLimit]
  split_ifs with h0
  · simp only [h0, Nat.cast_zero]
    ring
  · ring

/-- The weighted sum of the coefficients `D_a(c, k)` of the corrected division values. -/
private lemma sum_mul_divCoeff (W : (Fin 2 → ZMod N) → ℂ) (c k : ℕ) :
    ∑ a, W a * divCoeff N (a 0).val (a 1).val c k =
      ∑ j, (W ![(c : ZMod N), j] - W ![-(c : ZMod N), -j]) *
        ZMod.stdAddChar ((k : ZMod N) * j) := by
  -- a sum over residue pairs whose summand vanishes off the first coordinate `d`
  have hpair (d : ZMod N) (g : ZMod N → ℂ) :
      ∑ a, W a * (if d = a 0 then g (a 1) else 0) = ∑ j, W ![d, j] * g j := by
    rw [← (finTwoArrowEquiv (ZMod N)).symm.sum_comp, Fintype.sum_prod_type]
    simp [mul_ite, Finset.sum_ite_irrel]
  have hneg (x : ZMod N) : ((c : ZMod N) = -x) ↔ (-(c : ZMod N) = x) :=
    neg_eq_iff_eq_neg.symm
  calc ∑ a, W a * divCoeff N (a 0).val (a 1).val c k
      = ∑ a, W a * (if (c : ZMod N) = a 0 then ZMod.stdAddChar ((k : ZMod N) * a 1) else 0) -
          ∑ a, W a * (if -(c : ZMod N) = a 0 then
            ZMod.stdAddChar (-((k : ZMod N) * a 1)) else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp only [divCoeff, ZMod.natCast_zmod_val, hneg]
        ring
    _ = ∑ j, W ![(c : ZMod N), j] * ZMod.stdAddChar ((k : ZMod N) * j) -
          ∑ j, W ![-(c : ZMod N), -j] * ZMod.stdAddChar ((k : ZMod N) * j) := by
        rw [hpair _ fun j ↦ ZMod.stdAddChar ((k : ZMod N) * j),
          hpair _ fun j ↦ ZMod.stdAddChar (-((k : ZMod N) * j)),
          ← Equiv.sum_comp (Equiv.neg (ZMod N))
          (fun j ↦ W ![-(c : ZMod N), j] * ZMod.stdAddChar (-((k : ZMod N) * j)))]
        simp
    _ = _ := by
        rw [← Finset.sum_sub_distrib]
        simp only [sub_mul]

/-- **The `q`-expansion of the weighted weight-one series at level `Γ(N)`.** With
`e(z / N) = e^(2π i z / N)`, the series minus its value at `i∞` is the double series
`-2π i / N ∑_{c, k ≥ 1} (∑_j (W(c, j) - W(-c, -j)) e(k j / N)) e(z / N)^(c k)`, which converges
absolutely; grouping by `n = c k` gives the `q`-expansion in `e(z / N)`. -/
theorem hasSum_weightedE1_sub_valueAtInfty (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) :
    HasSum (fun p : ℕ+ × ℕ+ ↦ -2 * π * Complex.I / N *
        (∑ j, (W ![((p.1 : ℕ) : ZMod N), j] - W ![-((p.1 : ℕ) : ZMod N), -j]) *
          ZMod.stdAddChar (((p.2 : ℕ) : ZMod N) * j)) *
        cexp (2 * π * Complex.I * z / N) ^ ((p.1 : ℕ) * p.2))
      (weightedE1 W z - valueAtInfty (weightedE1 W)) := by
  have h := (hasSum_sum (s := Finset.univ) fun a _ ↦
    (hasSum_zetaValue_lift_sub a z).mul_left (W a)).mul_left (N : ℂ)⁻¹
  convert h using 1
  · ext p
    rw [← sum_mul_divCoeff, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  · rw [valueAtInfty_weightedE1, weightedE1_eq_sum_zetaValue, ← mul_sub,
      ← Finset.sum_sub_distrib]
    simp [zetaValueLimit, mul_sub]

/-! ### The modular form -/

/-- **The weighted weight-one series is a modular form** of weight one and level `Γ(N)`. -/
def weightedE1MF (W : (Fin 2 → ZMod N) → ℂ) : ModularForm Γ(N) 1 where
  toSlashInvariantForm := weightedE1SIF W
  holo' := weightedE1_mdifferentiable W
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ ↦ isBoundedAtImInfty_weightedE1_slash W γ

@[simp]
lemma coe_weightedE1MF (W : (Fin 2 → ZMod N) → ℂ) : ⇑(weightedE1MF W) = weightedE1 W := (rfl)

@[simp]
lemma weightedE1MF_zero : weightedE1MF (0 : (Fin 2 → ZMod N) → ℂ) = 0 := by
  ext z
  exact congrFun weightedE1_zero z

@[simp]
lemma weightedE1MF_add (W W' : (Fin 2 → ZMod N) → ℂ) :
    weightedE1MF (W + W') = weightedE1MF W + weightedE1MF W' := by
  ext z
  exact congrFun (weightedE1_add W W') z

@[simp]
lemma weightedE1MF_smul (c : ℂ) (W : (Fin 2 → ZMod N) → ℂ) :
    weightedE1MF (c • W) = c • weightedE1MF W := by
  ext z
  exact congrFun (weightedE1_smul c W) z

/-- The weighted weight-one series as a linear map from weights to `M₁(Γ(N))`. -/
def weightedE1MFₗ : ((Fin 2 → ZMod N) → ℂ) →ₗ[ℂ] ModularForm Γ(N) 1 where
  toFun := weightedE1MF
  map_add' := weightedE1MF_add
  map_smul' := weightedE1MF_smul

@[simp]
lemma weightedE1MFₗ_apply (W : (Fin 2 → ZMod N) → ℂ) : weightedE1MFₗ W = weightedE1MF W := (rfl)

end TauCeti.EisensteinSeries
