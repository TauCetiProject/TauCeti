/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
public import TauCeti.NumberTheory.ModularForms.Parity

/-!
# Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` and a weight `k ≥ 3`, the Eisenstein
series of Diamond–Shurman §4.5,
`G_k^{ψ,φ}(z) = ∑_{c mod u} ∑_{d mod v} ∑_{e mod u} ψ(c) φ̄(d) G_k^{(cv, d + ev)}(z)`,
where `G_k^{a}` sums `(m z + n)^(-k)` over all `(m, n) ≡ a mod uv`. Collecting the terms, it is
the series over all integer pairs `x`
`∑_x w(x) (x₀ z + x₁)^(-k)`, `w(x) = ψ(x₀ / v) φ⁻¹(x₁)` if `v ∣ x₀` and `0` otherwise,
that is, `∑_{(c, d)} ψ(c) φ⁻¹(d) (c v z + d)^(-k)`.

We realize it as the residue-weighted Eisenstein series of
`TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted`, at any level `N` with `u v ∣ N`,
and prove its transformation law (Diamond–Shurman §4.5): for `γ ∈ Γ₀(N)` with
lower-right entry `d`, slashing by `γ` multiplies the series by `ψ(d) φ(d)`. Hence the series is a
modular form for `Γ₁(N)` lying in the nebentypus space `M_k(N, ψφ)`.

No primitivity is assumed: the transformation law only uses that `ψ` and `φ` are characters.
Primitivity matters for the `q`-expansion and the normalization of `G_k^{ψ,φ}` to `E_k^{ψ,φ}`,
which are not treated in this file.

## Main definitions

* `TauCeti.EisensteinSeries.charWeight`: the weight `w` as a function of residues modulo `N`.
* `TauCeti.EisensteinSeries.charEisensteinSeriesMF`: `G_k^{ψ,φ}` as a modular form of weight
  `k` for `Γ₁(N)`.

## Main results

* `TauCeti.EisensteinSeries.charWeight_intCast`: the weight evaluated at an integer pair.
* `TauCeti.EisensteinSeries.charWeight_vecMul_inv`: the transformation of the weight under
  `Γ₀(N)`.
* `TauCeti.EisensteinSeries.charEisensteinSeriesMF_apply`: the series formula.
* `TauCeti.EisensteinSeries.charEisensteinSeriesMF_mem_modFormCharSpace`: `G_k^{ψ,φ}` lies in
  `M_k(N, ψφ)`.
* `TauCeti.EisensteinSeries.charEisensteinSeriesMF_eq_zero`: it vanishes unless
  `ψ(-1) φ(-1) = (-1)^k`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.5.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open EisensteinSeries

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v : ℕ} (N : ℕ) (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The weight defining the Eisenstein series with characters `ψ` modulo `u` and `φ` modulo `v`,
as a function of a residue pair modulo `N`: for the least nonnegative representatives
`(m, n)`, it is `ψ(m / v) φ⁻¹(n)` when `v ∣ m`, and `0` otherwise. For `u v ∣ N` this does not
depend on the choice of representatives (`charWeight_intCast`). -/
def charWeight (a : Fin 2 → ZMod N) : ℂ :=
  if v ∣ (a 0).val then ψ (((a 0).val / v : ℕ) : ZMod u) * φ⁻¹ ((a 1).val : ZMod v) else 0

variable {N}

/-- The weight at the reduction of an integer pair `x`: `ψ(x₀ / v) φ⁻¹(x₁)` if `v ∣ x₀`,
and `0` otherwise. -/
theorem charWeight_intCast [NeZero N] (huv : u * v ∣ N) (x : Fin 2 → ℤ) :
    charWeight N ψ φ ((↑) ∘ x) =
      if (v : ℤ) ∣ x 0 then ψ ((x 0 / v : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0 := by
  have hv : v ∣ N := dvd_of_mul_left_dvd huv
  simp only [charWeight, Function.comp_apply]
  -- the second entry: reduction modulo `v` factors through reduction modulo `N`
  have h1 : (((x 1 : ZMod N).val : ℕ) : ZMod v) = (x 1 : ZMod v) := by
    rw [ZMod.natCast_val, ZMod.cast_intCast hv]
  -- the first entry: the representative differs from `x 0` by a multiple of `N`
  obtain ⟨s, hs⟩ : (N : ℤ) ∣ ((x 0 : ZMod N).val : ℤ) - x 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simp)
  obtain ⟨t, rfl⟩ := huv
  have hdvd : v ∣ (x 0 : ZMod (u * v * t)).val ↔ (v : ℤ) ∣ x 0 := by
    rw [← Int.natCast_dvd_natCast, eq_add_of_sub_eq hs]
    push_cast
    exact dvd_add_right ⟨u * t * s, by ring⟩
  rw [h1]
  split_ifs with h h' h''
  · obtain ⟨c, hc⟩ := h'
    have hv0 : (v : ℤ) ≠ 0 := by
      rintro hv0
      exact NeZero.ne (u * v * t) (by simp [show v = 0 by exact_mod_cast hv0])
    have hval : ((((x 0 : ZMod (u * v * t)).val / v : ℕ) : ℤ)) = c + u * t * s := by
      rw [Int.natCast_div, eq_add_of_sub_eq hs, hc, show (↑(u * v * t) : ℤ) * s + v * c =
        v * (c + u * t * s) by push_cast; ring, Int.mul_ediv_cancel_left _ hv0]
    rw [← Int.cast_natCast, hval, hc, Int.mul_ediv_cancel_left _ hv0]
    simp
  · exact absurd (hdvd.mp h) h'
  · exact absurd (hdvd.mpr h'') h
  · rfl

variable {k : ℤ}

/-- **The transformation of the weight under `Γ₀(N)`.** For `γ ∈ Γ₀(N)` with lower-right entry
`d`, right multiplication by `γ⁻¹` multiplies the weight by `ψ(d) φ(d)`. -/
theorem charWeight_vecMul_inv [NeZero N] (huv : u * v ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (x : Fin 2 → ℤ) :
    charWeight N ψ φ ((↑) ∘ (x ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) =
      ψ (γ 1 1 : ZMod u) * φ (γ 1 1 : ZMod v) * charWeight N ψ φ ((↑) ∘ x) := by
  rw [charWeight_intCast ψ φ huv, charWeight_intCast ψ φ huv]
  obtain ⟨t, ht⟩ : (N : ℤ) ∣ γ 1 0 := by
    simpa [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] using hγ
  obtain ⟨n, rfl⟩ := huv
  have hv0 : (v : ℤ) ≠ 0 := by
    rintro hv0
    exact NeZero.ne (u * v * n) (by simp [show v = 0 by exact_mod_cast hv0])
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  have hx0 : (x ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 = x 0 * d - x 1 * c := by
    simp [vecMul, dotProduct, Matrix.adjugate_fin_two, c, d]
    ring
  have hx1 : (x ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 = -(x 0 * b) + x 1 * a := by
    simp [vecMul, dotProduct, Matrix.adjugate_fin_two, a, b]
  rw [hx0, hx1]
  -- `d` is a unit modulo `v`, so divisibility of the first entry does not change
  have hcop : IsCoprime (v : ℤ) d :=
    ⟨-(u * n * t) * b, a, by rw [← hdet, ht]; push_cast; ring⟩
  have hiff : (v : ℤ) ∣ x 0 * d - x 1 * c ↔ (v : ℤ) ∣ x 0 := by
    rw [ht, show x 0 * d - x 1 * (↑(u * v * n) * t) = x 0 * d + v * (-(x 1 * u * n * t)) by
      push_cast; ring, dvd_add_left (dvd_mul_right _ _)]
    exact ⟨fun h ↦ hcop.dvd_of_dvd_mul_right h, fun h ↦ h.mul_right _⟩
  split_ifs with h h' h''
  · obtain ⟨e, he⟩ := h'
    have hq : (x 0 * d - x 1 * c) / v = e * d - x 1 * (u * n * t) := by
      rw [ht, he, show (v : ℤ) * e * d - x 1 * (↑(u * v * n) * t) =
        v * (e * d - x 1 * (u * n * t)) by push_cast; ring, Int.mul_ediv_cancel_left _ hv0]
    have hr : ((-(x 0 * b) + x 1 * a : ℤ) : ZMod v) = (x 1 : ZMod v) * (a : ZMod v) := by
      rw [he]
      push_cast
      simp
    -- `a` and `d` are inverse modulo `v`
    have had : (a : ZMod v) * (d : ZMod v) = 1 := by
      have := congrArg (fun m : ℤ ↦ (m : ZMod v)) hdet
      simp only [ht] at this
      push_cast at this
      simpa using this
    have hinv : φ⁻¹ (a : ZMod v) = φ (d : ZMod v) := by
      rw [MulChar.inv_apply_eq_inv', inv_eq_of_mul_eq_one_right (by rw [← map_mul, had, map_one])]
    rw [hq, hr, he, Int.mul_ediv_cancel_left _ hv0, map_mul, hinv]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, mul_zero, sub_zero, map_mul]
    ring
  · exact absurd (hiff.mp h) h'
  · exact absurd (hiff.mpr h'') h
  · simp

/-! ### The Eisenstein series with character -/

/-- **The transformation law** (Diamond–Shurman, §4.5): for `γ ∈ Γ₀(N)` with lower-right
entry `d`, the series weighted by `charWeight N ψ φ` satisfies `G ∣[k] γ = ψ(d) φ(d) • G`. -/
theorem weightedEisensteinSeries_charWeight_slash [NeZero N] (huv : u * v ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] γ =
      (ψ (γ 1 1 : ZMod u) * φ (γ 1 1 : ZMod v)) •
        weightedEisensteinSeries (charWeight N ψ φ) k := by
  rw [weightedEisensteinSeries_slash_apply, ← weightedEisensteinSeries_smul]
  congr 1
  ext a
  obtain ⟨x, rfl⟩ : ∃ x : Fin 2 → ℤ, (↑) ∘ x = a := ⟨fun i ↦ ((a i).val : ℤ), by ext i; simp⟩
  rw [← intCast_comp_vecMul, charWeight_vecMul_inv ψ φ huv hγ, Pi.smul_apply, smul_eq_mul]

variable [NeZero N]

/-- The Eisenstein series `G_k^{ψ,φ}` with characters `ψ` modulo `u` and `φ` modulo `v`, as a
modular form of weight `k ≥ 3` for `Γ₁(N)`, where `u v ∣ N`: the series
`∑_{x ∈ ℤ², v ∣ x₀} ψ(x₀ / v) φ⁻¹(x₁) (x₀ z + x₁)^(-k)` (`charEisensteinSeriesMF_apply`), whose
underlying function does not depend on `N`. -/
def charEisensteinSeriesMF (hk : 3 ≤ k) (huv : u * v ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (weightedEisensteinSeriesMF (charWeight N ψ φ) hk) fun γ hγ ↦ by
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
      obtain ⟨hg0, hg1⟩ := mem_Gamma1_iff.mp hg
      have h1 {m : ℕ} (hm : m ∣ N) : ((g 1 1 : ℤ) : ZMod m) = 1 := by
        rw [← map_intCast (ZMod.castHom hm (ZMod m)), hg1, map_one]
      -- `SL_slash`: slashing by `g` is slashing by its image `mapGL ℝ g`
      have hslash : weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] mapGL ℝ g = _ :=
        (SL_slash _ g).symm.trans (weightedEisensteinSeries_charWeight_slash ψ φ huv hg0)
      rw [coe_weightedEisensteinSeriesMF, hslash, h1 (dvd_of_mul_right_dvd huv),
        h1 (dvd_of_mul_left_dvd huv), map_one, map_one, one_mul, one_smul]

/-- The Eisenstein series with character is the series weighted by `charWeight N ψ φ`. -/
lemma coe_charEisensteinSeriesMF (hk : 3 ≤ k) (huv : u * v ∣ N) :
    ⇑(charEisensteinSeriesMF ψ φ hk huv) = weightedEisensteinSeries (charWeight N ψ φ) k := by
  rw [charEisensteinSeriesMF, ModularForm.coe_ofSlashInvariant, coe_weightedEisensteinSeriesMF]

/-- The Eisenstein series with character, as a series over all integer pairs. -/
theorem charEisensteinSeriesMF_apply (hk : 3 ≤ k) (huv : u * v ∣ N) (z : ℍ) :
    charEisensteinSeriesMF ψ φ hk huv z = ∑' x : Fin 2 → ℤ,
      (if (v : ℤ) ∣ x 0 then ψ ((x 0 / v : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0) *
        eisSummand k x z := by
  simp only [coe_charEisensteinSeriesMF, weightedEisensteinSeries_def, charWeight_intCast ψ φ huv]

/-- **The nebentypus of the Eisenstein series with character**: `G_k^{ψ,φ} ∈ M_k(N, ψφ)`, the
characters being raised to level `N`. -/
theorem charEisensteinSeriesMF_mem_modFormCharSpace (hk : 3 ≤ k) (huv : u * v ∣ N) :
    charEisensteinSeriesMF ψ φ hk huv ∈ modFormCharSpace k
      (ψ.changeLevel (dvd_of_mul_right_dvd huv) *
        φ.changeLevel (dvd_of_mul_left_dvd huv)).toUnitHom := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  intro g
  -- `SL_slash`: slashing by `g` is slashing by its image `mapGL ℝ g`
  have hslash : weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] mapGL ℝ (g : SL(2, ℤ)) = _ :=
    (SL_slash _ _).symm.trans (weightedEisensteinSeries_charWeight_slash ψ φ huv g.2)
  rw [coe_charEisensteinSeriesMF, hslash, MulChar.coe_toUnitHom, MulChar.coeToFun_mul,
    Pi.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]
  simp [Gamma0Map, ZMod.cast_intCast (dvd_of_mul_right_dvd huv),
    ZMod.cast_intCast (dvd_of_mul_left_dvd huv)]

/-- **Parity**: the Eisenstein series with character vanishes unless `ψ(-1) φ(-1) = (-1)^k`. -/
theorem charEisensteinSeriesMF_eq_zero (hk : 3 ≤ k) (huv : u * v ∣ N)
    (h : ψ (-1) * φ (-1) ≠ (-1) ^ k) : charEisensteinSeriesMF ψ φ hk huv = 0 := by
  have hmem := charEisensteinSeriesMF_mem_modFormCharSpace ψ φ hk huv
  rwa [modFormCharSpace_eq_bot_of_char_neg_one_ne, Submodule.mem_bot] at hmem
  have hneg {m : ℕ} (hm : m ∣ N) (χ : DirichletCharacter ℂ m) :
      χ.changeLevel hm (-1) = χ (-1) := by
    simpa using
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm (a := -1) isCoprime_one_left.neg_left
  simpa [MulChar.coe_toUnitHom, hneg] using h

end TauCeti.EisensteinSeries
