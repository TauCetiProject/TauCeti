/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalized
public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# The Atkin–Lehner operators on level-raises

Let `Q ∥ N` be an exact divisor and `W_Q` an Atkin–Lehner matrix of level `N` for `Q`. Writing
`N = Q * R` with `Q` and `R` coprime, a level-raise `V_d` from a divisor level `M` splits into its
`Q`-part and its `R`-part, and so does `M`. Concretely, suppose

```text
Q = d₁ * e₁ * Q₁,    R = d₂ * e₂ * M',    M = Q₁ * M',    d = d₁ * d₂,
```

and put `e = e₁ * d₂`. Then `W_Q` moves past `diag(d, 1)` at the cost of exchanging the `Q`-part
`d₁` of `d` for the complementary factor `e₁`, while the `R`-part `d₂` passes through unchanged:

```text
diag(d, 1) · W_Q = d₁ · (W_{Q₁} · diag(e, 1)),
```

where `W_{Q₁}` is an Atkin–Lehner matrix of the *lower* level `M` for the exact divisor
`Q₁ ∥ M`. Since the scalar matrix `d₁ · I` slashes as multiplication by `d₁ ^ (k - 2)`, on a
form `f` on `Γ₀(M)` this reads

```text
W_Q (V_d f) = d₁⁻¹ · e₁ ^ (k - 1) · V_e (W_{Q₁} f).
```

At `Q = N` this is the Fricke identity of
`TauCeti/NumberTheory/ModularForms/Fricke/OldSpace.lean`, and at `Q = 1` it is the statement
that `V_d` commutes with the identity.

## Main results

* `TauCeti.IsAtkinLehnerMatrix.exists_scaleGL_mul_atkinLehnerGL`: the matrix identity
  `diag(d, 1) · W_Q = d₁ · (W_{Q₁} · diag(e, 1))`.
* `TauCeti.Nat.IsExactDivisor.atkinLehnerOperator_levelRaise`,
  `TauCeti.Nat.IsExactDivisor.atkinLehnerOperatorCusp_levelRaise`,
  `TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperator_levelRaise`,
  `TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp_levelRaise`: the Atkin–Lehner
  operator, raw and normalized, on modular and on cusp forms, intertwines `V_d` at level `N`
  with `V_e` at level `M`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* Miyake, *Modular forms*, Section 4.6.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise TauCeti.ExactDivisor

namespace TauCeti

variable {N Q Q₁ M' d₁ e₁ d₂ e₂ : ℕ} {W : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

/-! ### Moving an Atkin–Lehner matrix past a level-raise -/

/-- **An Atkin–Lehner matrix moves past `diag(d, 1)`.** Let `Q = d₁ * e₁ * Q₁` be a divisor of
`N = Q * (d₂ * e₂ * M')`. For an Atkin–Lehner matrix `W` of level `N` for `Q` there is an
Atkin–Lehner matrix `W'` of level `Q₁ * M'` for `Q₁` with
`diag(d₁ * d₂, 1) · W = d₁ · (W' · diag(e₁ * d₂, 1))`. -/
theorem IsAtkinLehnerMatrix.exists_scaleGL_mul_atkinLehnerGL [NeZero d₁] [NeZero d₂]
    [NeZero e₁] (hQ : 0 < Q) (hQ₁ : 0 < Q₁) (h : IsAtkinLehnerMatrix N Q W)
    (hQd : Q = d₁ * e₁ * Q₁) (hN : N = Q * (d₂ * e₂ * M')) :
    ∃ (W' : Matrix (Fin 2) (Fin 2) ℤ) (hW' : IsAtkinLehnerMatrix (Q₁ * M') Q₁ W'),
      scaleGL (d₁ * d₂) * atkinLehnerGL hQ h =
        Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.mk0 (d₁ : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne d₁))) *
          (atkinLehnerGL hQ₁ hW' * scaleGL (e₁ * d₂)) := by
  obtain ⟨a, b, c, d, rfl, hdet⟩ := h.exists_entries hQ.ne' hN
  have hW' : IsAtkinLehnerMatrix (Q₁ * M') Q₁
      !![(Q₁ : ℤ) * (d₁ * a), d₂ * b; (Q₁ : ℤ) * M' * (e₂ * c), (Q₁ : ℤ) * (e₁ * d)] :=
    isAtkinLehnerMatrix_of_entries rfl _ _ _ _ <| by
      subst hQd
      push_cast at hdet
      linear_combination hdet
  refine ⟨_, hW', Units.ext ?_⟩
  subst hQd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.natCast_apply] <;> ring

/-! ### The Atkin–Lehner operator on a level-raise -/

namespace Nat.IsExactDivisor

variable {M d e : ℕ}

/-- **The Atkin–Lehner operator intertwines the level-raises on modular forms.** Let
`Q = d₁ * e₁ * Q₁` be an exact divisor of `N = Q * (d₂ * e₂ * M')`, and `Q₁` an exact divisor of
`M = Q₁ * M'`. For a modular form `f` on `Γ₀(M)` and `d = d₁ * d₂`, `e = e₁ * d₂`,
`W_Q (V_d f) = d₁⁻¹ · e₁ ^ (k - 1) · V_e (W_{Q₁} f)`, where `W_Q` and `W_{Q₁}` are the Atkin–Lehner
operators of levels `N` and `M`. (The exactness `h₁` of `Q₁` follows from the other hypotheses;
it is taken as an argument because it names the operator `W_{Q₁}`.) -/
theorem atkinLehnerOperator_levelRaise [NeZero d] [NeZero e] (h : Q ∥ N) (h₁ : Q₁ ∥ M)
    (hQ : Q = d₁ * e₁ * Q₁) (hN : N = Q * (d₂ * e₂ * M')) (hM : M = Q₁ * M')
    (hd : d = d₁ * d₂) (he : e = e₁ * d₂)
    (hdΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (heΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma0 M).map (mapGL ℝ)) k) :
    h.atkinLehnerOperator k (ModularForm.levelRaise d hdΓ f) =
      ((d₁ : ℂ)⁻¹ * (e₁ : ℂ) ^ (k - 1)) •
        ModularForm.levelRaise e heΓ (h₁.atkinLehnerOperator k f) := by
  subst hd he hM
  have : NeZero d₁ := ⟨fun h0 ↦ h.ne_zero (by rw [hQ, h0]; ring)⟩
  have : NeZero e₁ := ⟨fun h0 ↦ h.ne_zero (by rw [hQ, h0]; ring)⟩
  have : NeZero d₂ := ⟨fun h0 ↦ NeZero.ne (e₁ * d₂) (by rw [h0, mul_zero])⟩
  obtain ⟨W', hW', hmul⟩ :=
    (isAtkinLehnerMatrix_atkinLehnerMatrix h).exists_scaleGL_mul_atkinLehnerGL h.pos h₁.pos hQ hN
  have hd₁ : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₁)
  have he₁ : (e₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e₁)
  have hd₂ : (d₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d₂)
  refine DFunLike.coe_injective ?_
  rw [h₁.atkinLehnerOperator_eq hW', coe_atkinLehnerOperator, ModularForm.coe_levelRaise,
    FunLike.coe_smul, ModularForm.coe_levelRaise, _root_.TauCeti.coe_atkinLehnerOperator,
    ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos _ _), ← SlashAction.slash_mul,
    hmul, SlashAction.slash_mul, ModularForm.slash_scalar, SlashAction.slash_mul,
    ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos _ _),
    ModularForm.smul_slash_of_det_pos k val_det_scaleGL_pos, smul_smul, smul_smul]
  congr 1
  simp only [Units.val_mk0, Complex.ofReal_natCast]
  push_cast
  rw [mul_zpow, mul_zpow, show k - 2 = -(1 - k) + -1 by ring, zpow_add₀ hd₁,
    show k - 1 = -(1 - k) by ring]
  simp only [zpow_neg, zpow_one]
  field_simp

/-- **The Atkin–Lehner operator intertwines the level-raises on cusp forms**: under the
factorizations of `atkinLehnerOperator_levelRaise`,
`W_Q (V_d f) = d₁⁻¹ · e₁ ^ (k - 1) · V_e (W_{Q₁} f)` for a cusp form `f` on `Γ₀(M)`. -/
theorem atkinLehnerOperatorCusp_levelRaise [NeZero d] [NeZero e] (h : Q ∥ N) (h₁ : Q₁ ∥ M)
    (hQ : Q = d₁ * e₁ * Q₁) (hN : N = Q * (d₂ * e₂ * M')) (hM : M = Q₁ * M')
    (hd : d = d₁ * d₂) (he : e = e₁ * d₂)
    (hdΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (heΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    h.atkinLehnerOperatorCusp k (CuspForm.levelRaise d hdΓ f) =
      ((d₁ : ℂ)⁻¹ * (e₁ : ℂ) ^ (k - 1)) •
        CuspForm.levelRaise e heΓ (h₁.atkinLehnerOperatorCusp k f) := by
  refine DFunLike.coe_injective ?_
  have := congrArg DFunLike.coe (atkinLehnerOperator_levelRaise h h₁ hQ hN hM hd he hdΓ heΓ
    (f : ModularForm ((Gamma0 M).map (mapGL ℝ)) k))
  rw [coe_atkinLehnerOperator, ModularForm.coe_levelRaise, FunLike.coe_smul,
    ModularForm.coe_levelRaise, coe_atkinLehnerOperator, ModularFormClass.coe_modularForm] at this
  rwa [coe_atkinLehnerOperatorCusp, CuspForm.coe_levelRaise, FunLike.coe_smul,
    CuspForm.coe_levelRaise, coe_atkinLehnerOperatorCusp]

/-- **The normalized Atkin–Lehner operator intertwines the level-raises on modular forms**:
under the factorizations of `atkinLehnerOperator_levelRaise`,
`𝒲_Q (V_d f) = (√(d₁ e₁)) ^ (2 - k) · d₁⁻¹ · e₁ ^ (k - 1) · V_e (𝒲_{Q₁} f)`. -/
theorem normalizedAtkinLehnerOperator_levelRaise [NeZero d] [NeZero e] (h : Q ∥ N)
    (h₁ : Q₁ ∥ M) (hQ : Q = d₁ * e₁ * Q₁) (hN : N = Q * (d₂ * e₂ * M')) (hM : M = Q₁ * M')
    (hd : d = d₁ * d₂) (he : e = e₁ * d₂)
    (hdΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (heΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma0 M).map (mapGL ℝ)) k) :
    h.normalizedAtkinLehnerOperator k (ModularForm.levelRaise d hdΓ f) =
      (atkinLehnerNormalizer (d₁ * e₁) k * (d₁ : ℂ)⁻¹ * (e₁ : ℂ) ^ (k - 1)) •
        ModularForm.levelRaise e heΓ (h₁.normalizedAtkinLehnerOperator k f) := by
  have hα : atkinLehnerNormalizer Q k =
      atkinLehnerNormalizer (d₁ * e₁) k * atkinLehnerNormalizer Q₁ k := by
    rw [hQ, atkinLehnerNormalizer_mul]
  rw [normalizedAtkinLehnerOperator_def, LinearMap.smul_apply,
    atkinLehnerOperator_levelRaise h h₁ hQ hN hM hd he hdΓ heΓ, normalizedAtkinLehnerOperator_def,
    LinearMap.smul_apply, hα]
  ext τ
  simp only [FunLike.coe_smul, Pi.smul_apply, ModularForm.levelRaise_apply, smul_eq_mul]
  ring

/-- **The normalized Atkin–Lehner operator intertwines the level-raises on cusp forms**:
under the factorizations of `atkinLehnerOperator_levelRaise`,
`𝒲_Q (V_d f) = (√(d₁ e₁)) ^ (2 - k) · d₁⁻¹ · e₁ ^ (k - 1) · V_e (𝒲_{Q₁} f)`. -/
theorem normalizedAtkinLehnerOperatorCusp_levelRaise [NeZero d] [NeZero e] (h : Q ∥ N)
    (h₁ : Q₁ ∥ M) (hQ : Q = d₁ * e₁ * Q₁) (hN : N = Q * (d₂ * e₂ * M')) (hM : M = Q₁ * M')
    (hd : d = d₁ * d₂) (he : e = e₁ * d₂)
    (hdΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (heΓ : (Gamma0 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma0 M).map (mapGL ℝ))
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) :
    h.normalizedAtkinLehnerOperatorCusp k (CuspForm.levelRaise d hdΓ f) =
      (atkinLehnerNormalizer (d₁ * e₁) k * (d₁ : ℂ)⁻¹ * (e₁ : ℂ) ^ (k - 1)) •
        CuspForm.levelRaise e heΓ (h₁.normalizedAtkinLehnerOperatorCusp k f) := by
  have hα : atkinLehnerNormalizer Q k =
      atkinLehnerNormalizer (d₁ * e₁) k * atkinLehnerNormalizer Q₁ k := by
    rw [hQ, atkinLehnerNormalizer_mul]
  rw [normalizedAtkinLehnerOperatorCusp_def, LinearMap.smul_apply,
    atkinLehnerOperatorCusp_levelRaise h h₁ hQ hN hM hd he hdΓ heΓ,
    normalizedAtkinLehnerOperatorCusp_def, LinearMap.smul_apply, hα]
  ext τ
  simp only [FunLike.coe_smul, Pi.smul_apply, CuspForm.levelRaise_apply, smul_eq_mul]
  ring

end Nat.IsExactDivisor

end TauCeti
