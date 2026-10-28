/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
public import Mathlib.Algebra.Group.EvenFunction
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

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

## Main definitions

* `TauCeti.EisensteinSeries.weightedE1`: the weight-one series weighted by `W`.
* `TauCeti.EisensteinSeries.weightedE1SIF`: it is a slash invariant form of weight one and level
  `Γ(N)`.

## Main results

* `TauCeti.EisensteinSeries.weightedE1_slash_apply`: the slash action of `SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.weightedE1_mdifferentiable`: holomorphy on `ℍ`.
* `TauCeti.EisensteinSeries.weightedE1_comp_neg`,
  `TauCeti.EisensteinSeries.weightedE1_eq_zero_of_even`: the parity constraint.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8, where
  the weight-one Eisenstein series of level `N` are constructed by Hecke's trick instead.
* M. Abramowitz and I. A. Stegun, *Handbook of mathematical functions*, Chapter 18, for `ζ` and
  its quasi-periods.
* The locally uniform convergence follows the weight-two argument of
  `TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted`, itself modelled on
  Mathlib's `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly` (Chris Birkbeck and David
  Loeffler).
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Complex Filter Set PeriodPair
open EisensteinSeries

open scoped MatrixGroups Topology Manifold

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

end TauCeti.EisensteinSeries
