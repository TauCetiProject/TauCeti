/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Smul
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Dyadic local densities in rank one and for the hyperbolic plane

The bilinear congruence count gives density `4` for both the rank-one unit form and the
hyperbolic plane over `ℤ_[2]`. Rescaling the rank-one unit form by a nonzero `a` gives density
`4 * 2 ^ a.valuation`, in particular density `8` for `⟨2⟩`.

These values distinguish the bilinear congruence count from the count for the half-norm
quadratic form: for the hyperbolic plane the latter has density `1`, not `4`.
The calculations use exact counts modulo `8` followed by stabilization, without an integral
orthogonal group scheme or a smoothness assumption.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), 793–827, Lemma 5.1 and Theorem 5.2, for the dyadic normalization.
-/

public section

open Filter Topology

namespace Matrix

private theorem natCard_isometryMatrices_one_zmod_eight :
    Nat.card (isometryMatrices (1 : Matrix (Fin 1) (Fin 1) (ZMod (2 ^ 3)))) = 4 := by
  let e := (uniqueEquiv : Matrix (Fin 1) (Fin 1) (ZMod (2 ^ 3)) ≃ ZMod (2 ^ 3)).subtypeEquiv
    (p := fun X => X ∈ isometryMatrices (1 : Matrix (Fin 1) (Fin 1) (ZMod (2 ^ 3))))
    (q := fun x => x * x = 1) fun X => by
      simp [mem_isometryMatrices, ← Matrix.ext_iff, Fin.forall_fin_one, mul_apply]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

private theorem localDensityCount_one_fin_one_two_eq_density {r : ℕ} (hr : 3 ≤ r) :
    ((1 : Matrix (Fin 1) (Fin 1) ℤ_[2]).localDensityCount r : ℚ) =
      (1 : Matrix (Fin 1) (Fin 1) ℤ_[2]).localDensity := by
  simpa using localDensityCount_div_pow_of_dvd
    (A := (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])) (by simp) (e := 1) (by simp) (r := r)
    (by omega)

/-- **The dyadic rank-one unit form has bilinear local density `4`.** -/
@[simp] theorem localDensity_one_fin_one_two :
    (1 : Matrix (Fin 1) (Fin 1) ℤ_[2]).localDensity = 4 := by
  have h := localDensityCount_one_fin_one_two_eq_density (r := 3) (by omega)
  have hc : (1 : Matrix (Fin 1) (Fin 1) ℤ_[2]).localDensityCount 3 = 4 := by
    rw [localDensityCount_def, Matrix.map_one _ (map_zero _) (map_one _)]
    exact natCard_isometryMatrices_one_zmod_eight
  norm_num [hc] at h
  exact h.symm

private theorem natCard_isometryMatrices_hyperbolic_zmod_eight :
    Nat.card (isometryMatrices
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 3)))) = 32 := by
  let e : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 3)) ≃
      (ZMod (2 ^ 3) × ZMod (2 ^ 3)) × (ZMod (2 ^ 3) × ZMod (2 ^ 3)) :=
    (Equiv.arrowCongr (Equiv.refl _) (finTwoArrowEquiv _)).trans (finTwoArrowEquiv _)
  let e' := e.subtypeEquiv
    (p := fun X => X ∈ isometryMatrices
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 3))))
    (q := fun x => (x.2.1 * x.1.1 + x.1.1 * x.2.1 = 0 ∧
      x.2.1 * x.1.2 + x.1.1 * x.2.2 = 1) ∧
      x.2.2 * x.1.1 + x.1.2 * x.2.1 = 1 ∧
      x.2.2 * x.1.2 + x.1.2 * x.2.2 = 0) fun X => by
      simp only [mem_isometryMatrices, ← Matrix.ext_iff, Fin.forall_fin_two,
        mul_apply, Fin.sum_univ_two, transpose_apply]
      -- Read the row-wise function equivalence in matrix coordinates.
      have he : e X = ((X 0 0, X 0 1), (X 1 0, X 1 1)) := rfl
      rw [he]
      norm_num
  -- Sum the counts for the second row over the first row, keeping the finite computation small.
  rw [Nat.card_congr e', Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun (x y : ZMod (2 ^ 3) × ZMod (2 ^ 3)) =>
        (y.1 * x.1 + x.1 * y.1 = 0 ∧ y.1 * x.2 + x.1 * y.2 = 1) ∧
        y.2 * x.1 + x.2 * y.1 = 1 ∧ y.2 * x.2 + x.2 * y.2 = 0),
    Fintype.card_sigma]
  decide

private theorem localDensityCount_hyperbolicPlane_two_div_eq_density {r : ℕ} (hr : 3 ≤ r) :
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).localDensityCount r : ℚ) / 2 ^ r =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).localDensity := by
  have hs : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2])ᵀ = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  simpa using localDensityCount_div_pow_of_dvd hs (e := 1)
    (by simp [det_fin_two]) (r := r) (by omega)

/-- **The dyadic hyperbolic plane has bilinear local density `4`.** In particular it does not
have the density `1` of the congruence count for its half-norm quadratic form. -/
@[simp] theorem localDensity_hyperbolicPlane_two :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).localDensity = 4 := by
  have h := localDensityCount_hyperbolicPlane_two_div_eq_density (r := 3) (by omega)
  have hm : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).map
      (PadicInt.toZModPow 3) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 3))) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hc : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).localDensityCount 3 = 32 := by
    rw [localDensityCount_def, hm]
    exact natCard_isometryMatrices_hyperbolic_zmod_eight
  norm_num [hc] at h
  exact h.symm

/-- **Every nonzero dyadic rank-one form has density `4 · 2^k`**, where `k` is the valuation
of its coefficient. The unit part of that coefficient does not affect the count. -/
theorem localDensity_smul_one_fin_one_two {a : ℤ_[2]} (ha : a ≠ 0) :
    (a • (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])).localDensity = (2 : ℚ) ^ a.valuation * 4 := by
  simpa [localDensity_one_fin_one_two] using
    localDensity_smul ha (A := (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])) (by simp) (by simp)

/-- **The rank-one dyadic congruence count stabilizes to `4 · 2^k`.** For a coefficient of
valuation `k`, the formula holds at every level `r + k` with `r ≥ 3`. -/
theorem localDensityCount_smul_one_fin_one_two {a : ℤ_[2]} (ha : a ≠ 0) {r : ℕ}
    (hr : 3 ≤ r) :
    (a • (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])).localDensityCount (r + a.valuation) =
      2 ^ a.valuation * 4 := by
  have h := localDensityCount_one_fin_one_two_eq_density hr
  rw [localDensity_one_fin_one_two] at h
  have hc : (1 : Matrix (Fin 1) (Fin 1) ℤ_[2]).localDensityCount r = 4 := by
    exact_mod_cast h
  simpa [hc] using localDensityCount_smul ha (1 : Matrix (Fin 1) (Fin 1) ℤ_[2]) r

/-- **The scale-two rank-one form has bilinear local density `8`.** -/
@[simp] theorem localDensity_two_smul_one_fin_one :
    ((2 : ℤ_[2]) • (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])).localDensity = 8 := by
  have hv : (2 : ℤ_[2]).valuation = 1 := PadicInt.valuation_p
  rw [localDensity_smul_one_fin_one_two (by norm_num), hv]
  norm_num

/-- **The stabilized dyadic hyperbolic count is `2^(r+2)`.** This counts bilinear
isometries modulo `2^r`, including all lifts that need not preserve the half-norm modulo `2^r`. -/
theorem localDensityCount_hyperbolicPlane_two {r : ℕ} (hr : 3 ≤ r) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).localDensityCount r = 2 ^ (r + 2) := by
  have h := localDensityCount_hyperbolicPlane_two_div_eq_density hr
  rw [localDensity_hyperbolicPlane_two] at h
  have h' := (div_eq_iff (by positivity : (2 : ℚ) ^ r ≠ 0)).mp h
  exact_mod_cast h'.trans (by ring : (4 : ℚ) * 2 ^ r = 2 ^ (r + 2))

end Matrix
