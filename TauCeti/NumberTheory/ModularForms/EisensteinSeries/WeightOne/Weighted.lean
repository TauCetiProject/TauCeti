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

Replacing `ã` by `ã + N y` changes both terms by `y₀ η₁ + y₁ η₂`. For a weight
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

/-- A division point `(b₀ z + b₁) / N` lies in the lattice `ℤ z + ℤ` only if `b ≡ 0 mod N`. -/
private lemma intCast_comp_eq_zero_of_mem_lattice {b : Fin 2 → ℤ} {z : ℍ}
    (h : ((b 0 : ℂ) * z + b 1) / N ∈ z.periodPair.lattice) :
    ((↑) : ℤ → ZMod N) ∘ b = 0 := by
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have h' : (((b 0 / (N : ℤ) : ℚ) : ℂ) * z.periodPair.ω₁ +
      ((b 1 / (N : ℤ) : ℚ) : ℂ) * z.periodPair.ω₂) ∈ z.periodPair.lattice := by
    convert h using 1
    push_cast
    simp only [periodPair_ω₁, periodPair_ω₂]
    ring
  obtain ⟨h0, h1⟩ := mul_ω₁_add_mul_ω₂_mem_lattice.mp h'
  rw [Rat.den_div_intCast_eq_one_iff _ _ hN] at h0 h1
  ext i
  fin_cases i <;> simpa [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The corrected division values depend only on the residue**: for `b ≢ 0 mod N`, the value
of `b` is that of the least nonnegative representatives of `b mod N`. Replacing `b` by `b + N y`
moves the division point by the lattice vector `y₀ z + y₁`, which changes `ζ` by its
quasi-period `y₀ η₁ + y₁ η₂`, and the correction by the same amount. -/
private lemma zetaValue_eq_lift {b : Fin 2 → ℤ} (hb : ((↑) : ℤ → ZMod N) ∘ b ≠ 0) (z : ℍ) :
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
  have hc : ((c 0 : ℂ) * z + c 1) / N ∉ z.periodPair.lattice := fun h ↦ by
    have h0 := intCast_comp_eq_zero_of_mem_lattice h
    rw [intCast_comp_lift] at h0
    exact hb h0
  set l : z.periodPair.lattice := ⟨_, intCast_mul_add_intCast_mem_lattice_periodPair z m n⟩
  have hx : ((b 0 : ℂ) * z + b 1) / N = ((c 0 : ℂ) * z + c 1) / N + l := by
    simp only [l, hm', hn']
    field_simp
    ring
  have hl := z.periodPair.quasiPeriod_eq_intCast_mul_add l (m := m) (n := n) (by simp [l])
  simp only [zetaValue]
  rw [hx, z.periodPair.weierstrassZeta_add_coe hc, hl, hm', hn']
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
  rw [zetaValue_smul]
  by_cases ha : a = 0
  · simp [ha, lift_zero]
  have hcast : ((↑) : ℤ → ZMod N) ∘ (lift a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
      a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    rw [intCast_comp_vecMul, intCast_comp_lift]
  have hne : a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) ≠ 0 := fun h ↦ ha <| by
    rw [Matrix.SpecialLinearGroup.vecMul_eq_iff_eq_vecMul_inv] at h
    rw [h, Matrix.zero_vecMul]
  rw [zetaValue_eq_lift (hcast ▸ hne), hcast]

/-- The corrected division value of `-a` is minus that of `a`. -/
private lemma zetaValue_lift_neg (a : Fin 2 → ZMod N) (z : ℍ) :
    zetaValue N (lift (-a)) z = -zetaValue N (lift a) z := by
  by_cases ha : a = 0
  · simp [ha, lift_zero, zetaValue_zero]
  have hcast : ((↑) : ℤ → ZMod N) ∘ (-lift a) = -a := by
    rw [← intCast_comp_lift (-a), intCast_comp_lift]
    ext i
    simp [lift]
  rw [← zetaValue_neg, zetaValue_eq_lift (b := -lift a) (by rwa [hcast, neg_ne_zero]), hcast]

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
  rw [show (fun a ↦ W (-a)) = W from funext hW] at h
  ext z
  exact CharZero.eq_neg_self_iff.mp (congrFun h z)

/-! ### Holomorphy -/

/-- The lattice series of `ζ` at the division point `(b₀ z + b₁) / M` converges locally uniformly
in `z`. -/
private lemma tendstoLocallyUniformly_weierstrassZeta_div (M : ℕ) [NeZero M] (b : Fin 2 → ℤ) :
    TendstoLocallyUniformly
      (fun (s : Finset (Fin 2 → ℤ)) (z : ℍ) ↦ ∑ y ∈ s,
        (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) + 1 / ((y 0 : ℂ) * z + y 1) +
          ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2))
      (fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ ↦ (z : ℂ))
    continuous_coe.continuousOn
  set r₀ := r ⟨⟨A, B⟩, hB⟩
  have hr₀ : 0 < r₀ := r_pos _
  set R : ℝ := |(b 0 : ℝ)| * |C| + |(b 1 : ℝ)| + 1
  have hR : 0 < R := by positivity
  have hlim : (fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M)) =
      fun z : ℍ ↦ ∑' y : Fin 2 → ℤ, (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
        1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2) :=
    funext fun z ↦ (hasSum_weierstrassZeta_periodPair z _).tsum_eq.symm
  rw [hlim]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually
    (u := fun y ↦ 2 * R ^ 2 * r₀ ^ (-3 : ℝ) * ‖y‖ ^ (-3 : ℝ))
    ((summable_one_div_norm_rpow (by norm_num)).mul_left _) ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, 2 * R / r₀ ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  filter_upwards [hev] with y hy z hz
  have hy' : 2 * R ≤ r₀ * ‖y‖ := by
    rwa [div_le_iff₀' hr₀] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [norm_zero, mul_zero] at hy'
    linarith
  have hl : r₀ * ‖y‖ ≤ ‖(y 0 : ℂ) * z + y 1‖ :=
    (mul_le_mul_of_nonneg_right (r_lower_bound_on_verticalStrip z hB (HABK hz))
      (norm_nonneg _)).trans (r_mul_max_le z hy0)
  have hx : ‖((b 0 : ℂ) * z + b 1) / M‖ < R := by
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
    have hz' : ‖(z : ℂ)‖ ≤ |C| := (hC z hz).trans (le_abs_self C)
    rw [norm_div, Complex.norm_natCast]
    refine (div_le_self (norm_nonneg _) hM).trans_lt ?_
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    have := mul_le_mul_of_nonneg_left hz' (abs_nonneg (b 0 : ℝ))
    linarith
  refine (weierstrassZeta_bound hR hx (hy'.trans hl)).trans ?_
  rw [mul_assoc (2 * R ^ 2), ← Real.mul_rpow hr₀.le (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)) (by positivity)

/-- The partial sums of the lattice series of `ζ` at a division point are holomorphic: in
Eisenstein summands, the terms are `M (b - M y)⁻¹ + y⁻¹ + x y⁻²` with `x = (b₀ z + b₁) / M`. -/
private lemma mdifferentiable_weierstrassZeta_div_term (M : ℕ) [NeZero M] (b y : Fin 2 → ℤ) :
    MDiff fun z : ℍ ↦ (1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
      1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2 : ℂ) := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hS (k : ℤ) (v : Fin 2 → ℤ) : MDiff (eisSummand k v) :=
    UpperHalfPlane.mdifferentiable_iff.mpr (eisSummand_extension_differentiableOn k v)
  have hx : MDiff fun z : ℍ ↦ ((b 0 : ℂ) * z + b 1) / M :=
    ((mdifferentiable_const.mul mdifferentiable_coe).add mdifferentiable_const).mul
      mdifferentiable_const
  have h : (fun z : ℍ ↦ 1 / (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) +
      1 / ((y 0 : ℂ) * z + y 1) + ((b 0 : ℂ) * z + b 1) / M / ((y 0 : ℂ) * z + y 1) ^ 2) =
      fun z ↦ M * eisSummand 1 (b - M • y) z + eisSummand 1 y z +
        ((b 0 : ℂ) * z + b 1) / M * eisSummand 2 y z := by
    ext z
    have he : ((b - M • y) 0 : ℂ) * z + (b - M • y) 1 =
        M * (((b 0 : ℂ) * z + b 1) / M - (y 0 * z + y 1)) := by
      simp only [Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Int.cast_sub,
        Int.cast_mul, Int.cast_natCast]
      field_simp
      ring
    rw [eisSummand, eisSummand, eisSummand, he, _root_.zpow_neg_one, _root_.zpow_neg_one,
      _root_.zpow_neg, zpow_ofNat, mul_inv, mul_inv_cancel_left₀ hM]
    simp only [div_eq_mul_inv, one_mul]
  rw [h]
  exact ((mdifferentiable_const.mul (hS 1 _)).add (hS 1 y)).add (hx.mul (hS 2 y))

/-- Each division value of `ζ` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_weierstrassZeta_div (M : ℕ) [NeZero M] (b : Fin 2 → ℤ) :
    MDiff fun z : ℍ ↦ z.periodPair.weierstrassZeta (((b 0 : ℂ) * z + b 1) / M) :=
  TauCeti.UpperHalfPlane.mdifferentiable_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_weierstrassZeta_div M b) (Eventually.of_forall fun s ↦ by
      convert MDifferentiable.sum (t := s)
        fun y _ ↦ mdifferentiable_weierstrassZeta_div_term M b y using 1
      ext z
      simp [Finset.sum_apply])

/-- The corrected division values are holomorphic on `ℍ`: the quasi-periods are the division
values `η₁ = 2 ζ(z / 2)` and `η₂ = 2 ζ(1 / 2)`. -/
private lemma mdifferentiable_zetaValue (b : Fin 2 → ℤ) : MDiff (zetaValue N b) := by
  have h₁ : MDiff fun z : ℍ ↦ z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ := by
    convert (mdifferentiable_const (c := (2 : ℂ))).mul
      (mdifferentiable_weierstrassZeta_div 2 ![1, 0]) using 1
    ext z
    rw [quasiPeriod_eq_two_mul_weierstrassZeta _ _ z.periodPair.ω₁_div_two_notMem_lattice]
    simp
  have h₂ : MDiff fun z : ℍ ↦ z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩ := by
    convert (mdifferentiable_const (c := (2 : ℂ))).mul
      (mdifferentiable_weierstrassZeta_div 2 ![0, 1]) using 1
    ext z
    rw [quasiPeriod_eq_two_mul_weierstrassZeta _ _ z.periodPair.ω₂_div_two_notMem_lattice]
    simp
  exact (mdifferentiable_weierstrassZeta_div N b).sub
    (((mdifferentiable_const.mul h₁).add (mdifferentiable_const.mul h₂)).mul mdifferentiable_const)

/-- **The weighted weight-one series is holomorphic on `ℍ`.** -/
theorem weightedE1_mdifferentiable (W : (Fin 2 → ZMod N) → ℂ) : MDiff (weightedE1 W) := by
  rw [show weightedE1 W = _ from funext (weightedE1_eq_sum_zetaValue W)]
  refine mdifferentiable_const.mul ?_
  convert MDifferentiable.sum (t := Finset.univ)
    (f := fun a (z : ℍ) ↦ W a * zetaValue N (lift a) z)
    fun a _ ↦ mdifferentiable_const.mul (mdifferentiable_zetaValue (lift a)) using 1
  ext z
  simp [Finset.sum_apply]

end TauCeti.EisensteinSeries
