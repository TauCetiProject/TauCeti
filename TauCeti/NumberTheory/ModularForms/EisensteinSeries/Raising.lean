/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Raising Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v`, the Eisenstein series with raising
parameter `t` is

```text
G_k^{ψ,φ,t}(z) = G_k^{ψ,φ}(t z) = V_t G_k^{ψ,φ}(z).
```

If `tuv ∣ N`, this is a modular form of level `Γ₁(N)` and nebentypus obtained by raising the
product character `ψφ` to level `N`. The parameter `t` changes the `q`-expansion by the
substitution `q ↦ q^t`; in particular, its coefficients are supported on multiples of `t`.
These are the raised series used to span the Eisenstein part of a character space.

The construction is stated for arbitrary characters in weight at least three. Primitivity is
not needed for modularity or level raising; it enters later when the Fourier expansion is
normalized and the spanning family is indexed without repetitions.

## Main definitions

* `TauCeti.EisensteinSeries.charEisensteinSeriesMFRaise`: the raised character Eisenstein
  series `V_t G_k^{ψ,φ}` at any level divisible by `tuv`.

## Main results

* `TauCeti.EisensteinSeries.charEisensteinSeriesMFRaise_mem_modFormCharSpace`: membership in the
  target-level character space.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMFRaise`: level raising substitutes
  `q ↦ q^t`.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMFRaise_coeff`: the resulting
  coefficient formula.
* `TauCeti.EisensteinSeries.isSupportedOnDvd_qExpansion_charEisensteinSeriesMFRaise`: the
  `q`-expansion is supported on multiples of `t`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.5.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup EisensteinSeries

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v N t : ℕ} {k : ℤ} [NeZero N]
  (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The character Eisenstein series with raising parameter `t`:
`G_k^{ψ,φ,t} = V_t G_k^{ψ,φ}`, viewed at any level `N` divisible by `tuv`.

The underlying series is formed first at its natural level `uv` and then raised directly to
level `N`. The divisibility hypothesis implies that both `t` and `uv` are nonzero. -/
def charEisensteinSeriesMFRaise (t : ℕ) (hk : 3 ≤ k) (htuv : t * (u * v) ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  exact ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (charEisensteinSeriesMF ψ φ hk dvd_rfl)

/-- The raised character Eisenstein series is the base series evaluated at `t z`. -/
@[simp]
theorem charEisensteinSeriesMFRaise_apply (hk : 3 ≤ k) (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    charEisensteinSeriesMFRaise ψ φ t hk htuv z =
      charEisensteinSeriesMF ψ φ hk dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charEisensteinSeriesMFRaise, ModularForm.levelRaise_apply]

/-- The raised character Eisenstein series as a sum over integer pairs. -/
theorem charEisensteinSeriesMFRaise_apply_eq_tsum (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    charEisensteinSeriesMFRaise ψ φ t hk htuv z = ∑' x : Fin 2 → ℤ,
      (if (v : ℤ) ∣ x 0 then ψ ((x 0 / v : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0) *
        eisSummand k x (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charEisensteinSeriesMFRaise_apply ψ φ hk htuv,
    charEisensteinSeriesMF_apply ψ φ hk dvd_rfl]

/-- At `t = 1`, the raised series is the base series restricted from level `uv` to level `N`. -/
@[simp]
theorem charEisensteinSeriesMFRaise_one (hk : 3 ≤ k) (huv : u * v ∣ N) :
    haveI : NeZero (u * v) := NeZero.of_dvd huv
    charEisensteinSeriesMFRaise ψ φ 1 hk (by simpa using huv) =
      ModularForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd huv)
        (charEisensteinSeriesMF ψ φ hk dvd_rfl) := by
  rw [charEisensteinSeriesMFRaise, ModularForm.levelRaise_one]

/-- The `q`-expansion of `G_k^{ψ,φ,t}` is obtained from that of `G_k^{ψ,φ}` by substituting
`q ↦ q^t`. -/
@[simp]
theorem qExpansion_charEisensteinSeriesMFRaise (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (charEisensteinSeriesMFRaise ψ φ t hk htuv) =
      (qExpansion 1 (charEisensteinSeriesMF ψ φ hk dvd_rfl)).expand t
        (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charEisensteinSeriesMFRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The coefficient formula for a raised character Eisenstein series:
`a_n(G_k^{ψ,φ,t}) = a_{n/t}(G_k^{ψ,φ})` when `t ∣ n`, and is zero otherwise. -/
theorem qExpansion_charEisensteinSeriesMFRaise_coeff (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) (n : ℕ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    (qExpansion 1 (charEisensteinSeriesMFRaise ψ φ t hk htuv)).coeff n =
      if t ∣ n then
        (qExpansion 1 (charEisensteinSeriesMF ψ φ hk dvd_rfl)).coeff (n / t)
      else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charEisensteinSeriesMFRaise]
  exact ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _ n

/-- The `q`-expansion of `G_k^{ψ,φ,t}` is supported on the multiples of `t`. -/
theorem isSupportedOnDvd_qExpansion_charEisensteinSeriesMFRaise (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    PowerSeries.IsSupportedOnDvd t
      (qExpansion 1 (charEisensteinSeriesMFRaise ψ φ t hk htuv)) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charEisensteinSeriesMFRaise]
  exact ModularForm.isSupportedOnDvd_qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- **Character-space membership after raising.** At every target level `N` divisible by `tuv`,
`G_k^{ψ,φ,t}` lies in `M_k(N, ψφ)`, with both characters raised directly to level `N`. -/
theorem charEisensteinSeriesMFRaise_mem_modFormCharSpace (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) :
    charEisensteinSeriesMFRaise ψ φ t hk htuv ∈ modFormCharSpace k
      (ψ.changeLevel ((dvd_mul_right u v).trans
          ((dvd_mul_left (u * v) t).trans htuv)) *
        φ.changeLevel ((dvd_mul_left v u).trans
          ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  have hbase := charEisensteinSeriesMF_mem_modFormCharSpace
    (N := u * v) ψ φ hk dvd_rfl
  have hraise := ModularForm.levelRaise_mem_modFormCharSpace_of_dvd htuv _ hbase
  rw [charEisensteinSeriesMFRaise]
  have hψ := DirichletCharacter.changeLevel_trans ψ (dvd_mul_right u v)
    ((dvd_mul_left (u * v) t).trans htuv)
  have hφ := DirichletCharacter.changeLevel_trans φ (dvd_mul_left v u)
    ((dvd_mul_left (u * v) t).trans htuv)
  have hchar :
      (ψ.changeLevel ((dvd_mul_right u v).trans
            ((dvd_mul_left (u * v) t).trans htuv)) *
          φ.changeLevel ((dvd_mul_left v u).trans
            ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom =
        ((ψ.changeLevel (dvd_mul_right u v) *
          φ.changeLevel (dvd_mul_left v u)).toUnitHom).comp
            (ZMod.unitsMap ((dvd_mul_left (u * v) t).trans htuv)) := by
    rw [hψ, hφ, ← map_mul, DirichletCharacter.changeLevel_toUnitHom]
  rw [hchar]
  exact hraise

/-- The parity obstruction survives level raising: if
`ψ(-1) φ(-1) ≠ (-1)^k`, then every raised series is zero. -/
theorem charEisensteinSeriesMFRaise_eq_zero (hk : 3 ≤ k) (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) ≠ (-1) ^ k) :
    charEisensteinSeriesMFRaise ψ φ t hk htuv = 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  apply ModularForm.ext
  intro z
  rw [charEisensteinSeriesMFRaise_apply ψ φ hk htuv,
    charEisensteinSeriesMF_eq_zero ψ φ hk dvd_rfl hpar]
  rfl

end TauCeti.EisensteinSeries
