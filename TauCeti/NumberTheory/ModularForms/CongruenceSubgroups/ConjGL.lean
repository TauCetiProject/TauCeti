/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel
public import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.Cusps.LevelRaise
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Conjugates of subgroups of `SL(2, ℤ)` by rational matrices, and the level after scaling

For `Γ ≤ SL(2, ℤ)` and `g ∈ GL(2, ℝ)`, Mathlib's `CongruenceSubgroup.conjGL Γ g` is the subgroup
`g⁻¹ Γ g ∩ SL(2, ℤ)` of the `x ∈ SL(2, ℤ)` with `g x g⁻¹ ∈ Γ`. This file records how it interacts
with `-I` and with adjoining `±I`, that it has finite index whenever `Γ` does and `g` is rational,
and then studies the case `g = A = diag(d, 1)` (`TauCeti.scaleGL d`), the *scaling* of `Γ`:
`Γ_A = A⁻¹ Γ A ∩ SL(2, ℤ)`. If a weight-zero function `f` on `ℍ` is invariant under `Γ`, then
`τ ↦ f (d τ) = f (A τ)` is invariant under `Γ_A`, so the scaling of subgroups accompanies the
scaling `f ↦ f (d ·)` of functions.

The main result bounds the level of `Γ_A`: if every `SL(2, ℤ)`-conjugate of `T ^ N` lies in `Γ`,
then every conjugate of `T ^ (d N)` lies in `Γ_A`, so the strict level of `Γ_A` divides `d` times
that of `Γ` (`Subgroup.strictLevel_conjGL_scaleGL_dvd`), and the same holds for the signed
(geometric) level, the strict level of `Γ·{±I}`
(`Subgroup.strictLevel_withCenter_conjGL_scaleGL_dvd`). Neither `d` prime nor `Γ` of finite index
is needed.

## Main results

* `CongruenceSubgroup.neg_one_mem_conjGL_iff`: `-I ∈ conjGL Γ g ↔ -I ∈ Γ`.
* `CongruenceSubgroup.conjGL_withCenter`: `conjGL` commutes with adjoining `±I`.
* `CongruenceSubgroup.finiteIndex_conjGL_of_finiteIndex`: for `g` rational, `conjGL Γ g` has
  finite index when `Γ` does; in particular `Γ_A` has finite index.
* `CongruenceSubgroup.mem_conjGL_scaleGL_iff`, `CongruenceSubgroup.conjGL_scaleGL_le_Gamma0`:
  the elements of `Γ_A` are the `(a, b; d c, e)` with `(a, d b; c, e) ∈ Γ`; hence `Γ_A ≤ Γ₀(d)`.
* `Subgroup.strictLevel_conjGL_scaleGL_dvd`,
  `Subgroup.strictLevel_withCenter_conjGL_scaleGL_dvd`: the strict and signed levels of `Γ_A`
  divide `d` times those of `Γ`.

## Implementation notes

The level bound writes `A σ = δ β` with `δ ∈ SL(2, ℤ)` and `β` upper triangular with diagonal
`(e, d / e)`, `e = gcd(c, d)` for `c` the lower-left entry of `σ`
(`Matrix.SpecialLinearGroup.exists_scaled_cusp_reduction`), so that
`A (σ T^(d N) σ⁻¹) A⁻¹ = δ T^(N e²) δ⁻¹`. This replaces the case distinction of Calegari, Dimitrov
and Tang according to whether `d` divides the upper-left entry of `σ`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), 627–702, Notation 4.1.5 and Lemma 4.1.7.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti
open scoped MatrixGroups

namespace CongruenceSubgroup

variable {Γ : Subgroup SL(2, ℤ)}

/-- Conjugation fixes the central element `-I`, so it lies in `g⁻¹ Γ g ∩ SL(2, ℤ)` exactly when it
lies in `Γ`. -/
theorem neg_one_mem_conjGL_iff {g : GL (Fin 2) ℝ} : -1 ∈ conjGL Γ g ↔ -1 ∈ Γ := by
  have h : mapGL ℝ (-1 : SL(2, ℤ)) = -1 := by ext i j; simp
  have hg : g * mapGL ℝ (-1 : SL(2, ℤ)) * g⁻¹ = mapGL ℝ (-1 : SL(2, ℤ)) := by
    rw [h, mul_neg, mul_one, neg_mul, mul_inv_cancel]
  simp only [mem_conjGL, coe_GL_eq_mapGL, hg, mapGL_injective.eq_iff, exists_eq_right]

/-- Adjoining `±I` commutes with conjugation: `g⁻¹ (±Γ) g ∩ SL(2, ℤ) = ±(g⁻¹ Γ g ∩ SL(2, ℤ))`. -/
theorem conjGL_withCenter (Γ : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) :
    conjGL Γ.withCenter g = (conjGL Γ g).withCenter := by
  have hneg (x : SL(2, ℤ)) : mapGL ℝ (-x) = -mapGL ℝ x := by ext i j; simp
  ext x
  simp only [mem_conjGL, Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg, coe_GL_eq_mapGL]
  constructor
  · rintro ⟨y, ⟨y', hy', rfl | rfl⟩, hx⟩
    · exact ⟨x, ⟨_, hy', hx⟩, Or.inl rfl⟩
    · refine ⟨-x, ⟨y', hy', ?_⟩, Or.inr (neg_neg x).symm⟩
      rw [hneg, mul_neg, neg_mul, ← hx, hneg, neg_neg]
  · rintro ⟨x', ⟨y, hy, hx'⟩, rfl | rfl⟩
    · exact ⟨y, ⟨y, hy, Or.inl rfl⟩, hx'⟩
    · exact ⟨-y, ⟨y, hy, Or.inr rfl⟩, by rw [hneg, hneg, hx', mul_neg, neg_mul]⟩

/-- If `Γ` has finite index in `SL(2, ℤ)`, then so does `g⁻¹ Γ g ∩ SL(2, ℤ)` for every rational
`g`. This extends Mathlib's `CongruenceSubgroup.finiteIndex_conjGL`, the case `Γ = ⊤`. -/
theorem finiteIndex_conjGL_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (g : GL (Fin 2) ℚ) : (conjGL Γ (g.map (Rat.castHom ℝ))).FiniteIndex := by
  have := Subgroup.IsArithmetic.conj (Γ.map (mapGL ℝ)) g⁻¹
  rw [map_inv] at this
  exact Subgroup.IsArithmetic.finiteIndex_comap _

/-- The scaling `diag(d, 1)⁻¹ Γ diag(d, 1) ∩ SL(2, ℤ)` of a finite-index subgroup has finite
index. -/
instance finiteIndex_conjGL_scaleGL (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (d : ℕ) [NeZero d] :
    (conjGL Γ (scaleGL d)).FiniteIndex := by
  rw [← map_natDiagGL_d_one_eq_scaleGL,
    show algebraMap ℚ ℝ = Rat.castHom ℝ from Subsingleton.elim _ _]
  exact finiteIndex_conjGL_of_finiteIndex Γ _

/-- The elements of the scaling `diag(d, 1)⁻¹ Γ diag(d, 1) ∩ SL(2, ℤ)` are the matrices
`(a, b; d c, e)` whose `diag(d, 1)`-conjugate `(a, d b; c, e)` lies in `Γ`. -/
theorem mem_conjGL_scaleGL_iff {d : ℕ} [NeZero d] {γ : SL(2, ℤ)} :
    γ ∈ conjGL Γ (scaleGL d) ↔ ∃ (c : ℤ) (hc : γ 1 0 = d * c), conjScale d γ c hc ∈ Γ := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, h⟩ ↦ mem_conjGL.mpr ⟨_, h, (mapGL_conjScale γ c hc).symm⟩⟩
  obtain ⟨y, hy, h⟩ := mem_conjGL.mp h
  rw [coe_GL_eq_mapGL, coe_GL_eq_mapGL] at h
  -- the lower-left entry of `y * diag(d, 1) = diag(d, 1) * γ` reads `d * y 1 0 = γ 1 0`
  have hc : γ 1 0 = d * y 1 0 := by
    have := congrArg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
      (eq_mul_inv_iff_mul_eq.mp h)
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    exact_mod_cast this.symm.trans (mul_comm _ _)
  refine ⟨y 1 0, hc, ?_⟩
  rwa [mapGL_injective (R := ℤ) (S := ℝ) ((mapGL_conjScale γ _ hc).symm.trans h.symm)]

/-- The scaling `diag(d, 1)⁻¹ Γ diag(d, 1) ∩ SL(2, ℤ)` lies in `Γ₀(d)`. -/
theorem conjGL_scaleGL_le_Gamma0 (Γ : Subgroup SL(2, ℤ)) (d : ℕ) [NeZero d] :
    conjGL Γ (scaleGL d) ≤ Gamma0 d := fun γ hγ ↦ by
  obtain ⟨c, hc, -⟩ := mem_conjGL_scaleGL_iff.mp hγ
  simp [Gamma0_mem, hc]

/-- At `d = 2`, the scaling of `Γ(2)` contains `T`, whose conjugate `diag(2, 1) T diag(2, 1)⁻¹` is
`T ^ 2`. -/
example : ModularGroup.T ∈ conjGL (Gamma 2) (scaleGL 2) :=
  mem_conjGL_scaleGL_iff.mpr ⟨0, by simp [ModularGroup.T], by
    simpa [Gamma_mem, ModularGroup.T] using ZMod.natCast_self 2⟩

end CongruenceSubgroup

namespace Subgroup

open CongruenceSubgroup

/-- **The strict level after scaling.** If every `SL(2, ℤ)`-conjugate of `T ^ N` lies in `Γ`,
then every conjugate of `T ^ (d N)` lies in the scaling `diag(d, 1)⁻¹ Γ diag(d, 1) ∩ SL(2, ℤ)`:
the strict level of the scaling divides `d` times the strict level of `Γ`. -/
theorem strictLevel_conjGL_scaleGL_dvd (Γ : Subgroup SL(2, ℤ)) (d : ℕ) [NeZero d] :
    (conjGL Γ (scaleGL d)).strictLevel ∣ d * Γ.strictLevel := by
  refine strictLevel_dvd_iff.mpr fun σ ↦ mem_conjGL.mpr ?_
  -- write `diag(d, 1) σ = δ β` with `β` upper triangular with diagonal `(e, d / e)`
  obtain ⟨δ, ha, hc⟩ := σ.exists_scaled_cusp_reduction (t := d)
  obtain ⟨h10, h11⟩ := σ.scaled_cusp_upperTriangular δ ha hc
  set e := Int.gcd (σ 1 0) d
  set β := (mapGL ℝ δ)⁻¹ * (scaleGL d * mapGL ℝ σ) with hβ
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he : (e : ℝ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (σ 1 0)
      (Nat.cast_ne_zero.mpr (NeZero.ne d))).ne'
  have h00 : β 0 0 = e := by
    have hdet : (β.det : ℝ) = d := by simp [β]
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11, mul_zero, sub_zero]
      at hdet
    calc β 0 0 = β 0 0 * (d / e) * (e / d) := by field_simp
      _ = e := by rw [hdet]; field_simp
  -- then `diag(d, 1) σ T^(d N) σ⁻¹ diag(d, 1)⁻¹ = δ T^(N e²) δ⁻¹`, and `N ∣ N e²`
  refine ⟨δ * ModularGroup.T ^ (Γ.strictLevel * e ^ 2) * δ⁻¹,
    strictLevel_dvd_iff.mp (dvd_mul_right _ _) δ, ?_⟩
  have hσ : scaleGL d * mapGL ℝ σ = mapGL ℝ δ * β := by rw [hβ, mul_inv_cancel_left]
  simp only [coe_GL_eq_mapGL, map_mul, map_inv, ModularGroup.mapGL_T_pow_eq_upperRightHom]
  calc mapGL ℝ δ * GeneralLinearGroup.upperRightHom ((Γ.strictLevel * e ^ 2 : ℕ) : ℝ) *
        (mapGL ℝ δ)⁻¹
      = mapGL ℝ δ * (β * GeneralLinearGroup.upperRightHom ((d * Γ.strictLevel : ℕ) : ℝ) * β⁻¹) *
        (mapGL ℝ δ)⁻¹ := by
        rw [GeneralLinearGroup.upperRightHom_conj_of_upperTriangular h10, h00, h11]
        congr 3
        push_cast
        field_simp
    _ = (scaleGL d * mapGL ℝ σ) * GeneralLinearGroup.upperRightHom ((d * Γ.strictLevel : ℕ) : ℝ) *
        (scaleGL d * mapGL ℝ σ)⁻¹ := by rw [hσ]; group
    _ = _ := by group

/-- **The signed level after scaling** (Calegari–Dimitrov–Tang, Lemma 4.1.7). If every
`SL(2, ℤ)`-conjugate of `T ^ N` lies in `±Γ`, then every conjugate of `T ^ (d N)` lies in `±Γ_A`
for the scaling `Γ_A = diag(d, 1)⁻¹ Γ diag(d, 1) ∩ SL(2, ℤ)`: the strict level of `Γ_A·{±I}`
divides `d` times that of `Γ·{±I}`. -/
theorem strictLevel_withCenter_conjGL_scaleGL_dvd (Γ : Subgroup SL(2, ℤ)) (d : ℕ) [NeZero d] :
    (conjGL Γ (scaleGL d)).withCenter.strictLevel ∣ d * Γ.withCenter.strictLevel := by
  rw [← conjGL_withCenter]
  exact strictLevel_conjGL_scaleGL_dvd _ d

end Subgroup
