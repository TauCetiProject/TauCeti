/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.Fricke.Matrix

/-!
# The Atkin–Lehner slash operator

An Atkin–Lehner matrix `W` for a divisor `Q` of `N` normalizes `Γ₀(N)`
(`TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul`), so the weight-`k` slash by `W` sends
a modular form for `Γ₀(N)` to another one. That is the operator built here, on `M_k(Γ₀(N))` and
on `S_k(Γ₀(N))`.

The operator carries **no** normalizing scalar, so it is not an involution: `W ^ 2` is `Q` times
an element of `Γ₀(N)`, and a scalar matrix slashes by a power of its scalar, so the operator
squares to `Q ^ (k - 2)` (`atkinLehnerOperator_atkinLehnerOperator`). Dividing that away is the
job of the normalized operator `𝒲_Q = (√Q) ^ (2 - k) • (· ∣[k] W)`; the Fricke member `Q = N` of
the family is already normalized separately in
`TauCeti/NumberTheory/ModularForms/Fricke/`.

The operator does not depend on which Atkin–Lehner matrix for `Q` is used: two of them differ by
an element of `Γ₀(N)`, which a form for `Γ₀(N)` absorbs (`atkinLehnerOperator_congr`). The
arbitrary Bézout choice in `TauCeti.atkinLehnerMatrix` is therefore invisible, and
`TauCeti.Nat.IsExactDivisor.atkinLehnerOperator` — the operator `W_Q` indexed by the exact divisor
alone, with no matrix to supply — is the interface to use.

## Main definitions

* `TauCeti.atkinLehnerGL`: an Atkin–Lehner matrix as an element of `GL (Fin 2) ℝ`.
* `TauCeti.atkinLehnerOperator`, `TauCeti.atkinLehnerOperatorCusp`: the slash operator by a
  given Atkin–Lehner matrix, on `M_k(Γ₀(N))` and on `S_k(Γ₀(N))`.
* `TauCeti.Nat.IsExactDivisor.atkinLehnerOperator`,
  `TauCeti.Nat.IsExactDivisor.atkinLehnerOperatorCusp`: the operator `W_Q` of an exact divisor `Q`,
  with the matrix taken to be `TauCeti.atkinLehnerMatrix N Q`.

## Main results

* `TauCeti.Gamma0_map_inv_conjAct_atkinLehnerGL_eq`: `W` normalizes the image of `Γ₀(N)` in
  `GL (Fin 2) ℝ`. This is what makes the operator well defined.
* `TauCeti.atkinLehnerOperator_congr`, `TauCeti.atkinLehnerOperatorCusp_congr`: independence of
  the chosen Atkin–Lehner matrix.
* `TauCeti.atkinLehnerOperator_atkinLehnerOperator`,
  `TauCeti.atkinLehnerOperatorCusp_atkinLehnerOperatorCusp` and their
  `TauCeti.Nat.IsExactDivisor` counterparts: the square is `Q ^ (k - 2)`.
* `TauCeti.Nat.IsExactDivisor.atkinLehnerOperator_eq`,
  `TauCeti.Nat.IsExactDivisor.atkinLehnerOperatorCusp_eq`: `W_Q` is the slash by *any* Atkin–Lehner
  matrix for `Q`.
* `TauCeti.Nat.IsExactDivisor.atkinLehnerOperator_one`,
  `TauCeti.Nat.IsExactDivisor.atkinLehnerOperatorCusp_one`: `W_1` is the identity.
* `TauCeti.Nat.IsExactDivisor.coe_atkinLehnerOperator_self`,
  `TauCeti.Nat.IsExactDivisor.coe_atkinLehnerOperatorCusp_self`: `W_N` is the slash by the Fricke
  matrix `TauCeti.frickeGL ℝ N`, the slash that `TauCeti.frickeOperator` performs at level
  `Γ₁(N)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise TauCeti.ExactDivisor

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

/-- **Moving `W` past `Γ₀(N)`**, the `GL (Fin 2) ℝ` reading of
`IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul`. -/
theorem exists_mem_Gamma0_atkinLehnerGL_mul_mapGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      atkinLehnerGL hQ h * mapGL ℝ γ = mapGL ℝ δ * atkinLehnerGL hQ h := by
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul hQ.ne' hQN hγ
  refine ⟨δ, hδ, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    Int.coe_castRingHom, ← Matrix.map_mul_intCast, hmul]

/-- **Moving `Γ₀(N)` past `W`**, the mirror of
`exists_mem_Gamma0_atkinLehnerGL_mul_mapGL`. -/
theorem exists_mem_Gamma0_mapGL_mul_atkinLehnerGL (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      mapGL ℝ γ * atkinLehnerGL hQ h = atkinLehnerGL hQ h * mapGL ℝ δ := by
  obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul' hQ.ne' hQN hγ
  refine ⟨δ, hδ, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
    Int.coe_castRingHom, ← Matrix.map_mul_intCast, hmul]

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
  obtain ⟨γ, hγ, hM⟩ := h'.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN h
  have hGL : atkinLehnerGL hQ h = mapGL ℝ γ * atkinLehnerGL hQ h' := by
    refine Units.ext ?_
    simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
      Int.coe_castRingHom, ← Matrix.map_mul_intCast, hM]
  refine DFunLike.coe_injective ?_
  rw [coe_atkinLehnerOperator, coe_atkinLehnerOperator, hGL, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hγ)]

/-- **The cusp-form operator does not depend on the chosen Atkin–Lehner matrix.** -/
theorem atkinLehnerOperatorCusp_congr (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (h' : IsAtkinLehnerMatrix N Q M')
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorCusp hQ hQN h k f = atkinLehnerOperatorCusp hQ hQN h' k f := by
  obtain ⟨γ, hγ, hM⟩ := h'.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN h
  have hGL : atkinLehnerGL hQ h = mapGL ℝ γ * atkinLehnerGL hQ h' := by
    refine Units.ext ?_
    simp only [Matrix.GeneralLinearGroup.coe_mul, coe_atkinLehnerGL, mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, algebraMap_int_eq,
      Int.coe_castRingHom, ← Matrix.map_mul_intCast, hM]
  refine DFunLike.coe_injective ?_
  rw [coe_atkinLehnerOperatorCusp, coe_atkinLehnerOperatorCusp, hGL, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hγ)]

/-- **Slashing twice by `W` multiplies by `Q ^ (k - 2)`.** The square `W ^ 2` is `Q` times an
element of `Γ₀(N)`; the scalar matrix contributes `Q ^ (k - 2)` and the `Γ₀(N)` factor is
absorbed. This is the identity the normalization `(√Q) ^ (2 - k)` turns into an involution in
even weight. -/
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
      mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      algebraMap_int_eq, Int.coe_castRingHom, ← Matrix.map_mul_intCast, hsq, hscal,
      Matrix.smul_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hdet : (0 : ℝ) < ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det :=
    det_pos_of_mem_slGL ⟨γ, rfl⟩
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

/-!
## The operator of an exact divisor

Taking the Bézout witness `atkinLehnerMatrix N Q` as the representative leaves one operator `W_Q`
per exact divisor `Q` of `N`, with no matrix for the user to supply. By
`atkinLehnerOperator_congr` it is the slash by any Atkin–Lehner matrix for `Q` whatsoever.
-/

/-- **The Atkin–Lehner operator `W_Q`** on `M_k(Γ₀(N))`, for an exact divisor `Q` of `N`: the
slash by `atkinLehnerMatrix N Q`. Any other Atkin–Lehner matrix for `Q` gives the same operator
(`Nat.IsExactDivisor.atkinLehnerOperator_eq`). -/
noncomputable def Nat.IsExactDivisor.atkinLehnerOperator (h : Q ∥ N) (k : ℤ) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k :=
  _root_.TauCeti.atkinLehnerOperator h.pos h.dvd (isAtkinLehnerMatrix_atkinLehnerMatrix h) k

/-- **The Atkin–Lehner operator `W_Q` on cusp forms** `S_k(Γ₀(N))`. -/
noncomputable def Nat.IsExactDivisor.atkinLehnerOperatorCusp (h : Q ∥ N) (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  _root_.TauCeti.atkinLehnerOperatorCusp h.pos h.dvd (isAtkinLehnerMatrix_atkinLehnerMatrix h) k

/-- On underlying functions `W_Q` is the slash by `atkinLehnerMatrix N Q`, read in
`GL (Fin 2) ℝ`. -/
@[simp]
theorem Nat.IsExactDivisor.coe_atkinLehnerOperator (h : Q ∥ N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(h.atkinLehnerOperator k f) : ℍ → ℂ) =
      ⇑f ∣[k] atkinLehnerGL h.pos (isAtkinLehnerMatrix_atkinLehnerMatrix h) := (rfl)

/-- On underlying functions the cusp-form `W_Q` is the slash by `atkinLehnerMatrix N Q`, read in
`GL (Fin 2) ℝ`. -/
@[simp]
theorem Nat.IsExactDivisor.coe_atkinLehnerOperatorCusp (h : Q ∥ N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(h.atkinLehnerOperatorCusp k f) : ℍ → ℂ) =
      ⇑f ∣[k] atkinLehnerGL h.pos (isAtkinLehnerMatrix_atkinLehnerMatrix h) := (rfl)

/-- **`W_Q` is the slash by any Atkin–Lehner matrix for `Q`.** -/
theorem Nat.IsExactDivisor.atkinLehnerOperator_eq (h : Q ∥ N) (h' : IsAtkinLehnerMatrix N Q M)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    h.atkinLehnerOperator k f = _root_.TauCeti.atkinLehnerOperator h.pos h.dvd h' k f :=
  atkinLehnerOperator_congr h.pos h.dvd _ h' f

/-- **The cusp-form `W_Q` is the slash by any Atkin–Lehner matrix for `Q`.** -/
theorem Nat.IsExactDivisor.atkinLehnerOperatorCusp_eq (h : Q ∥ N) (h' : IsAtkinLehnerMatrix N Q M)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    h.atkinLehnerOperatorCusp k f = _root_.TauCeti.atkinLehnerOperatorCusp h.pos h.dvd h' k f :=
  atkinLehnerOperatorCusp_congr h.pos h.dvd _ h' f

/-- **`W_Q` squares to `Q ^ (k - 2)`** on `M_k(Γ₀(N))`. -/
theorem Nat.IsExactDivisor.atkinLehnerOperator_atkinLehnerOperator (h : Q ∥ N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    h.atkinLehnerOperator k (h.atkinLehnerOperator k f) = (Q : ℂ) ^ (k - 2) • f :=
  _root_.TauCeti.atkinLehnerOperator_atkinLehnerOperator h.pos h.dvd _ f

/-- **The cusp-form `W_Q` squares to `Q ^ (k - 2)`.** -/
theorem Nat.IsExactDivisor.atkinLehnerOperatorCusp_atkinLehnerOperatorCusp (h : Q ∥ N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    h.atkinLehnerOperatorCusp k (h.atkinLehnerOperatorCusp k f) = (Q : ℂ) ^ (k - 2) • f :=
  _root_.TauCeti.atkinLehnerOperatorCusp_atkinLehnerOperatorCusp h.pos h.dvd _ f

/-!
## The endpoints `Q = 1` and `Q = N`
-/

/-- At `Q = 1` the matrix `atkinLehnerMatrix N 1` has determinant `1`, so it is an element of
`Γ₀(N)` (`isAtkinLehnerMatrix_one_iff_mem_Gamma0`), and a function invariant under `Γ₀(N)` is
unchanged by the slash. -/
theorem Nat.IsExactDivisor.slash_atkinLehnerGL_one (h : 1 ∥ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] atkinLehnerGL h.pos (isAtkinLehnerMatrix_atkinLehnerMatrix h) = f := by
  have hM := isAtkinLehnerMatrix_atkinLehnerMatrix h
  obtain ⟨γ, hγM⟩ : ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) = atkinLehnerMatrix N 1 :=
    ⟨⟨atkinLehnerMatrix N 1, by rw [hM.det_eq, Nat.cast_one]⟩, rfl⟩
  have hγ : γ ∈ Gamma0 N := (isAtkinLehnerMatrix_one_iff_mem_Gamma0 γ).mp (hγM ▸ hM)
  have hGL : atkinLehnerGL h.pos hM = mapGL ℝ γ := by
    refine Units.ext ?_
    simp only [coe_atkinLehnerGL, mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hγM]
  rw [hGL]
  exact hf _ (Subgroup.mem_map_of_mem _ hγ)

/-- **`W_1` is the identity** on `M_k(Γ₀(N))`. -/
@[simp]
theorem Nat.IsExactDivisor.atkinLehnerOperator_one (h : 1 ∥ N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) : h.atkinLehnerOperator k f = f :=
  DFunLike.coe_injective <| h.slash_atkinLehnerGL_one ⇑f fun γ hγ ↦
    SlashInvariantForm.slash_action_eqn f γ hγ

/-- **The cusp-form `W_1` is the identity** on `S_k(Γ₀(N))`. -/
@[simp]
theorem Nat.IsExactDivisor.atkinLehnerOperatorCusp_one (h : 1 ∥ N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : h.atkinLehnerOperatorCusp k f = f :=
  DFunLike.coe_injective <| h.slash_atkinLehnerGL_one ⇑f fun γ hγ ↦
    SlashInvariantForm.slash_action_eqn f γ hγ

/-- The Fricke matrix read as an Atkin–Lehner matrix for `Q = N` is `frickeGL ℝ N`. -/
theorem atkinLehnerGL_fricke [NeZero N] (hN : 0 < N) :
    atkinLehnerGL hN (isAtkinLehnerMatrix_fricke (N := N)) = frickeGL ℝ N := by
  refine Units.ext ?_
  rw [coe_atkinLehnerGL, coe_frickeGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **`W_N` is the Fricke slash** on `M_k(Γ₀(N))`: on underlying functions it is
`⇑f ∣[k] frickeGL ℝ N`, the slash that `frickeOperator` performs at level `Γ₁(N)`
(`coe_frickeOperator`). -/
theorem Nat.IsExactDivisor.coe_atkinLehnerOperator_self [NeZero N] (h : N ∥ N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(h.atkinLehnerOperator k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := by
  rw [h.atkinLehnerOperator_eq isAtkinLehnerMatrix_fricke,
    _root_.TauCeti.coe_atkinLehnerOperator, atkinLehnerGL_fricke]

/-- **The cusp-form `W_N` is the Fricke slash** on `S_k(Γ₀(N))`, the slash that
`frickeOperatorCusp` performs at level `Γ₁(N)` (`coe_frickeOperatorCusp`). -/
theorem Nat.IsExactDivisor.coe_atkinLehnerOperatorCusp_self [NeZero N] (h : N ∥ N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(h.atkinLehnerOperatorCusp k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := by
  rw [h.atkinLehnerOperatorCusp_eq isAtkinLehnerMatrix_fricke,
    _root_.TauCeti.coe_atkinLehnerOperatorCusp, atkinLehnerGL_fricke]

end TauCeti
