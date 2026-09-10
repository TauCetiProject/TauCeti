/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix
public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The Atkin–Lehner slash operator

An Atkin–Lehner matrix `W` for a divisor `Q` of `N` normalizes `Γ₀(N)`
(`TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_comm`), so the weight-`k` slash by `W` sends
a modular form for `Γ₀(N)` to another one. That is the operator built here, on `M_k(Γ₀(N))` and
on `S_k(Γ₀(N))`.

The operator carries **no** normalizing scalar, so it is not an involution: `W ^ 2` is `Q` times
an element of `Γ₀(N)`, and a scalar matrix slashes by a power of its scalar, so the operator
squares to `Q ^ (k - 2)` (`atkinLehnerOperator_atkinLehnerOperator`). Dividing that away is what
the normalized `𝒲_Q = (√Q) ^ (2 - k) • (· ∣[k] W)` of the roadmap's Layer 6 does; the Fricke
member `Q = N` of the family is already normalized separately in
`TauCeti/NumberTheory/ModularForms/Fricke/`.

The operator does not depend on which Atkin–Lehner matrix for `Q` is used: two of them differ by
an element of `Γ₀(N)`, which a form for `Γ₀(N)` absorbs (`atkinLehnerOperator_congr`). So the
arbitrary Bézout choice in `TauCeti.atkinLehnerMatrix` is invisible downstream, and there is no
need for a canonical representative.

## Main definitions

* `TauCeti.atkinLehnerGL`: an Atkin–Lehner matrix as an element of `GL (Fin 2) ℝ`.
* `TauCeti.atkinLehnerOperator`, `TauCeti.atkinLehnerOperatorCusp`: the slash operator on
  `M_k(Γ₀(N))` and on `S_k(Γ₀(N))`.

## Main results

* `TauCeti.Gamma0_map_inv_conjAct_atkinLehnerGL_eq`: `W` normalizes the image of `Γ₀(N)` in
  `GL (Fin 2) ℝ`. This is what makes the operator well defined.
* `TauCeti.atkinLehnerOperator_congr`, `TauCeti.atkinLehnerOperatorCusp_congr`: independence of
  the chosen Atkin–Lehner matrix.
* `TauCeti.atkinLehnerOperator_atkinLehnerOperator`,
  `TauCeti.atkinLehnerOperatorCusp_atkinLehnerOperatorCusp`: the square is `Q ^ (k - 2)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {N Q : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

/-- An Atkin–Lehner matrix, read in `GL (Fin 2) ℝ`. Its determinant is `Q`, nonzero by the
positivity hypothesis, so the integral matrix really is invertible over `ℝ`. -/
noncomputable def atkinLehnerGL (hQ : 0 < Q) (h : IsAtkinLehnerMatrix N Q M) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map ((↑) : ℤ → ℝ)) <| by
    rw [← Int.cast_det, h.det_eq]
    exact_mod_cast hQ.ne'

/-- The underlying matrix of `atkinLehnerGL` is the entrywise real cast. -/
@[simp]
theorem coe_atkinLehnerGL (hQ : 0 < Q) (h : IsAtkinLehnerMatrix N Q M) :
    (↑(atkinLehnerGL hQ h) : Matrix (Fin 2) (Fin 2) ℝ) = M.map ((↑) : ℤ → ℝ) := by
  simp [atkinLehnerGL]

/-- The determinant of `atkinLehnerGL` is `Q`. -/
theorem val_det_atkinLehnerGL (hQ : 0 < Q) (h : IsAtkinLehnerMatrix N Q M) :
    ((atkinLehnerGL hQ h).det : ℝ) = Q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_atkinLehnerGL, ← Int.cast_det, h.det_eq]
  norm_cast

/-- The determinant of `atkinLehnerGL` is positive, so it slashes by the `det > 0` formula. -/
theorem val_det_atkinLehnerGL_pos (hQ : 0 < Q) (h : IsAtkinLehnerMatrix N Q M) :
    0 < ((atkinLehnerGL hQ h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, val_det_atkinLehnerGL hQ h]
  exact_mod_cast hQ

/-- Casting a matrix product to `ℝ` entrywise is a product; the ring-hom shape
`Matrix.map_mul` needs, spelled for the plain integer cast used throughout this file. -/
private theorem map_intCast_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map ((↑) : ℤ → ℝ) = A.map ((↑) : ℤ → ℝ) * B.map ((↑) : ℤ → ℝ) :=
  Matrix.map_mul (f := (Int.castRingHom ℝ))

/-- The real matrix underlying `mapGL ℝ γ` is the entrywise cast of the integral one. -/
private theorem coe_mapGL_intCast (γ : SL(2, ℤ)) :
    ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ℝ) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- **Moving `W` past `Γ₀(N)`**, the `GL (Fin 2) ℝ` reading of
`IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_comm`. -/
theorem exists_mem_Gamma0_atkinLehnerGL_mul_mapGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      atkinLehnerGL hQ h * mapGL ℝ γ = mapGL ℝ δ * atkinLehnerGL hQ h := by
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_comm hQ.ne' hQN hγ
  refine ⟨δ, hδ, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL,
    coe_mapGL_intCast, coe_mapGL_intCast, ← map_intCast_mul, ← map_intCast_mul, hmul]

/-- **Moving `Γ₀(N)` past `W`**, the mirror of
`exists_mem_Gamma0_atkinLehnerGL_mul_mapGL`. -/
theorem exists_mem_Gamma0_mapGL_mul_atkinLehnerGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      mapGL ℝ γ * atkinLehnerGL hQ h = atkinLehnerGL hQ h * mapGL ℝ δ := by
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_comm' hQ.ne' hQN hγ
  refine ⟨δ, hδ, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL,
    coe_mapGL_intCast, coe_mapGL_intCast, ← map_intCast_mul, ← map_intCast_mul, hmul]

/-- **`W` normalizes `Γ₀(N)` in `GL (Fin 2) ℝ`.** Conjugating the image of `Γ₀(N)` by an
Atkin–Lehner matrix returns that same subgroup, which is what makes the slash by `W` an operator
on modular forms of level `Γ₀(N)`. -/
theorem Gamma0_map_inv_conjAct_atkinLehnerGL_eq (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) :
    ConjAct.toConjAct (atkinLehnerGL hQ h)⁻¹ • (Gamma0 N).map (mapGL ℝ) =
      (Gamma0 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτy⟩
    obtain ⟨δ, hδ, hmul⟩ := exists_mem_Gamma0_mapGL_mul_atkinLehnerGL hQ hQN h hτ
    refine ⟨δ, hδ, ?_⟩
    rw [hτy] at hmul
    refine (mul_left_cancel (a := atkinLehnerGL hQ h) ?_).symm
    rw [← hmul]
    group
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨δ, hδ, hmul⟩ := exists_mem_Gamma0_atkinLehnerGL_mul_mapGL hQ hQN h hσ
    exact ⟨δ, hδ, by rw [hmul]; group⟩

/-- **The Atkin–Lehner slash operator** on `M_k(Γ₀(N))`: `f ↦ f ∣[k] W`, as a `ℂ`-linear
endomorphism. It carries no normalizing scalar; see the module docstring. -/
noncomputable def atkinLehnerOperator (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f :=
    ModularForm.mcast rfl (ModularForm.translate f (atkinLehnerGL hQ h))
      (Gamma0_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h).symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (atkinLehnerGL hQ h) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun
      (ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos hQ h) ⇑f c) z

/-- On underlying functions the Atkin–Lehner operator is `⇑f ∣[k] W`. -/
@[simp]
theorem coe_atkinLehnerOperator (hQ : 0 < Q) (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(atkinLehnerOperator hQ hQN h k f) : ℍ → ℂ) = ⇑f ∣[k] atkinLehnerGL hQ h := (rfl)

/-- **The Atkin–Lehner slash operator on cusp forms** `S_k(Γ₀(N))`. -/
noncomputable def atkinLehnerOperatorCusp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f :=
    CuspForm.mcast rfl (CuspForm.translate f (atkinLehnerGL hQ h))
      (Gamma0_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h).symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (atkinLehnerGL hQ h) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun
      (ModularForm.smul_slash_of_det_pos k (val_det_atkinLehnerGL_pos hQ h) ⇑f c) z

/-- On underlying functions the cusp-form Atkin–Lehner operator is `⇑f ∣[k] W`. -/
@[simp]
theorem coe_atkinLehnerOperatorCusp (hQ : 0 < Q) (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(atkinLehnerOperatorCusp hQ hQN h k f) : ℍ → ℂ) = ⇑f ∣[k] atkinLehnerGL hQ h := (rfl)

/-- **The operator does not depend on the chosen Atkin–Lehner matrix.** Two of them differ by an
element of `Γ₀(N)` on the left, which a form of level `Γ₀(N)` absorbs. -/
theorem atkinLehnerOperator_congr (hQ : 0 < Q) (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M)
    (h' : IsAtkinLehnerMatrix N Q M') (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    atkinLehnerOperator hQ hQN h k f = atkinLehnerOperator hQ hQN h' k f := by
  obtain ⟨γ, hγ, hM⟩ := h'.exists_mem_Gamma0_mul_eq hQ.ne' hQN h
  have hGL : atkinLehnerGL hQ h = mapGL ℝ γ * atkinLehnerGL hQ h' := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, coe_atkinLehnerGL,
      coe_mapGL_intCast, ← map_intCast_mul, hM]
  refine DFunLike.coe_injective ?_
  rw [coe_atkinLehnerOperator, coe_atkinLehnerOperator, hGL, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hγ)]

/-- **The cusp-form operator does not depend on the chosen Atkin–Lehner matrix.** -/
theorem atkinLehnerOperatorCusp_congr (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (h' : IsAtkinLehnerMatrix N Q M')
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorCusp hQ hQN h k f = atkinLehnerOperatorCusp hQ hQN h' k f := by
  obtain ⟨γ, hγ, hM⟩ := h'.exists_mem_Gamma0_mul_eq hQ.ne' hQN h
  have hGL : atkinLehnerGL hQ h = mapGL ℝ γ * atkinLehnerGL hQ h' := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, coe_atkinLehnerGL,
      coe_mapGL_intCast, ← map_intCast_mul, hM]
  refine DFunLike.coe_injective ?_
  rw [coe_atkinLehnerOperatorCusp, coe_atkinLehnerOperatorCusp, hGL, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hγ)]

/-- **Slashing twice by `W` multiplies by `Q ^ (k - 2)`.** The square `W ^ 2` is `Q` times an
element of `Γ₀(N)`; the scalar matrix contributes `Q ^ (k - 2)` and the `Γ₀(N)` factor is
absorbed. This is the identity the normalization `(√Q) ^ (2 - k)` of Layer 6 is designed to turn
into an involution in even weight. -/
theorem slash_atkinLehnerGL_slash_atkinLehnerGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f) :
    (f ∣[k] atkinLehnerGL hQ h) ∣[k] atkinLehnerGL hQ h = (Q : ℂ) ^ (k - 2) • f := by
  obtain ⟨γ, hγ, hsq⟩ := h.exists_mem_Gamma0_mul_self hQ.ne' hQN
  have hQR : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hGL : atkinLehnerGL hQ h * atkinLehnerGL hQ h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Q : ℝ) hQR) * mapGL ℝ γ := by
    have hscal : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Q : ℝ) hQR) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Q : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Units.val_mk0]
      split_ifs <;> simp
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL,
      coe_mapGL_intCast, ← map_intCast_mul, hsq, hscal, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hdet : (0 : ℝ) < ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [coe_mapGL_intCast, ← Int.cast_det, γ.property]
    norm_num
  rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul, ModularForm.slash_scalar,
    ModularForm.smul_slash_of_det_pos k hdet, hf _ (Subgroup.mem_map_of_mem _ hγ)]
  simp

/-- **The Atkin–Lehner operator squares to `Q ^ (k - 2)`** on `M_k(Γ₀(N))`. -/
theorem atkinLehnerOperator_atkinLehnerOperator (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    atkinLehnerOperator hQ hQN h k (atkinLehnerOperator hQ hQN h k f) = (Q : ℂ) ^ (k - 2) • f :=
  DFunLike.coe_injective <| by
    rw [coe_atkinLehnerOperator, coe_atkinLehnerOperator,
      slash_atkinLehnerGL_slash_atkinLehnerGL hQ hQN h ⇑f fun γ hγ ↦
        SlashInvariantForm.slash_action_eqn f γ hγ]
    rfl

/-- **The cusp-form Atkin–Lehner operator squares to `Q ^ (k - 2)`.** -/
theorem atkinLehnerOperatorCusp_atkinLehnerOperatorCusp (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorCusp hQ hQN h k (atkinLehnerOperatorCusp hQ hQN h k f) =
      (Q : ℂ) ^ (k - 2) • f :=
  DFunLike.coe_injective <| by
    rw [coe_atkinLehnerOperatorCusp, coe_atkinLehnerOperatorCusp,
      slash_atkinLehnerGL_slash_atkinLehnerGL hQ hQN h ⇑f fun γ hγ ↦
        SlashInvariantForm.slash_action_eqn f γ hγ]
    rfl

end TauCeti
