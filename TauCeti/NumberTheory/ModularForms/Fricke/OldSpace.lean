/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic

/-!
# The Fricke operator preserves the old subspace

Let `N = d * e * M`. The Fricke matrix `W_N = !![0, -1; N, 0]` moves past the level-raising
matrix `diag(d, 1)` at the cost of exchanging `d` for the complementary factor `e`:

```text
diag(d, 1) · W_N = d · (W_M · diag(e, 1)),
```

both sides being `!![0, -d; N, 0]`. Since the scalar matrix `d · I` slashes as multiplication
by `d ^ (k - 2)`, the Fricke operator carries a level-raise `V_d f` of a form `f` of level `M`
to a multiple of the level-raise `V_e (W_M f)`, where `W_M` is the Fricke operator of the
*lower* level:

```text
W_N (V_d f) = d⁻¹ · e ^ (k - 1) · V_e (W_M f).
```

As `e * M` divides `N` and `M` is still a proper divisor of `N`, the right-hand side is again
old. So `W_N` maps the old subspace `S_k(Γ₁(N))ᵒˡᵈ` into itself, and, being invertible, onto
itself; the same holds for the normalized operator `𝒲_N`, a nonzero multiple of `W_N`. This is
the Fricke transport of the degeneracy maps and of the old subspace (Diamond–Shurman §5.6,
Miyake §4.6): combined with the Petersson unitarity of `𝒲_N`, it makes the new subspace, the
Petersson complement of the old one, stable under `𝒲_N`.

## Main results

* `TauCeti.scaleGL_mul_frickeGL`: the matrix identity `diag(d, 1) · W_N = d · W_M · diag(e, 1)`.
* `TauCeti.slash_scaleGL_slash_frickeGL`: its slash form, for an arbitrary function.
* `TauCeti.frickeOperator_levelRaise`, `TauCeti.frickeOperatorCusp_levelRaise`,
  `TauCeti.normalizedFrickeOperator_levelRaise`, `TauCeti.normalizedFrickeOperatorCusp_levelRaise`:
  the Fricke operator, raw and normalized, on modular and on cusp forms, intertwines `V_d` at
  level `N` with `V_e` at level `M`.
* `TauCeti.frickeOperatorCusp_mem_cuspFormsOld`,
  `TauCeti.normalizedFrickeOperatorCusp_mem_cuspFormsOld`: the old subspace is stable.
* `TauCeti.cuspFormsOld_map_frickeOperatorCusp`,
  `TauCeti.cuspFormsOld_map_normalizedFrickeOperatorCusp`: the old subspace is carried *onto*
  itself.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.6 and
  §5.10.
* Miyake, *Modular forms*, Section 4.6.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {M d e N : ℕ} {k : ℤ}

/-! ### Moving the Fricke matrix past a level-raise -/

/-- **The Fricke matrix moves past `diag(d, 1)`**: for `N = d * e * M`,
`diag(d, 1) · W_N = d · (W_M · diag(e, 1))`, both sides being `!![0, -d; N, 0]`. -/
theorem scaleGL_mul_frickeGL [NeZero M] [NeZero d] [NeZero e] [NeZero N] (h : d * e * M = N) :
    scaleGL d * frickeGL ℝ N =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.mk0 (d : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne d))) *
        (frickeGL ℝ M * scaleGL e) := by
  have hN : (N : ℝ) = d * (e * M) := by rw [← h]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar, hN,
      Matrix.natCast_apply, mul_comm]

/-- **Slashing by `diag(d, 1)` and then by `W_N`** is `d ^ (k - 2)` times slashing by `W_M` and
then by `diag(e, 1)`, whenever `N = d * e * M`. This is `scaleGL_mul_frickeGL` read through the
weight-`k` slash action, for a function not assumed to be a form. -/
theorem slash_scaleGL_slash_frickeGL [NeZero M] [NeZero d] [NeZero e] [NeZero N]
    (h : d * e * M = N) (k : ℤ) (f : ℍ → ℂ) :
    (f ∣[k] scaleGL d) ∣[k] frickeGL ℝ N =
      (d : ℂ) ^ (k - 2) • ((f ∣[k] frickeGL ℝ M) ∣[k] scaleGL e) := by
  rw [← SlashAction.slash_mul, scaleGL_mul_frickeGL h, SlashAction.slash_mul,
    ModularForm.slash_scalar, SlashAction.slash_mul,
    ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos,
    ModularForm.smul_slash_of_det_pos k val_det_scaleGL_pos]
  simp

/-! ### The Fricke operator on a level-raise -/

/-- **The Fricke operator intertwines the level-raises on modular forms**: for `N = d * e * M`
and a modular form `f` of level `M`, `W_N (V_d f) = d⁻¹ · e ^ (k - 1) · V_e (W_M f)`, where `W_N`
and `W_M` are the Fricke operators of levels `N` and `M`. -/
theorem frickeOperator_levelRaise [NeZero M] [NeZero d] [NeZero e] [NeZero N]
    (h : d * e * M = N)
    (hd : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (he : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    frickeOperator k (ModularForm.levelRaise d hd f) =
      ((d : ℂ)⁻¹ * (e : ℂ) ^ (k - 1)) • ModularForm.levelRaise e he (frickeOperator k f) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e)
  refine DFunLike.coe_injective ?_
  rw [coe_frickeOperator, ModularForm.coe_levelRaise, FunLike.coe_smul,
    ModularForm.coe_levelRaise, coe_frickeOperator,
    ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos, slash_scaleGL_slash_frickeGL h,
    smul_smul, smul_smul]
  congr 1
  rw [← zpow_add₀ hd0, mul_assoc, ← zpow_add₀ he0]
  simp

/-- **The Fricke operator intertwines the level-raises**: for `N = d * e * M` and a cusp form
`f` of level `M`, `W_N (V_d f) = d⁻¹ · e ^ (k - 1) · V_e (W_M f)`, where `W_N` and `W_M` are the
Fricke operators of levels `N` and `M`. -/
theorem frickeOperatorCusp_levelRaise [NeZero M] [NeZero d] [NeZero e] [NeZero N]
    (h : d * e * M = N)
    (hd : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (he : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    frickeOperatorCusp k (CuspForm.levelRaise d hd f) =
      ((d : ℂ)⁻¹ * (e : ℂ) ^ (k - 1)) • CuspForm.levelRaise e he (frickeOperatorCusp k f) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e)
  refine DFunLike.coe_injective ?_
  rw [coe_frickeOperatorCusp, CuspForm.coe_levelRaise, FunLike.coe_smul, CuspForm.coe_levelRaise,
    coe_frickeOperatorCusp, ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos,
    slash_scaleGL_slash_frickeGL h, smul_smul, smul_smul]
  congr 1
  rw [← zpow_add₀ hd0, mul_assoc, ← zpow_add₀ he0]
  simp

/-- **The normalized Fricke operator intertwines the level-raises**: for `N = d * e * M`,
`𝒲_N (V_d f) = (√(d e)) ^ (2 - k) · d⁻¹ · e ^ (k - 1) · V_e (𝒲_M f)`. The scalar is
`(e / d) ^ (k / 2)`; it is written through `atkinLehnerNormalizer (d * e) k`, the ratio of the
normalizers of `𝒲_N` and `𝒲_M`. -/
theorem normalizedFrickeOperatorCusp_levelRaise [NeZero M] [NeZero d] [NeZero e] [NeZero N]
    (h : d * e * M = N)
    (hd : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (he : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    normalizedFrickeOperatorCusp k (CuspForm.levelRaise d hd f) =
      (atkinLehnerNormalizer (d * e) k * (d : ℂ)⁻¹ * (e : ℂ) ^ (k - 1)) •
        CuspForm.levelRaise e he (normalizedFrickeOperatorCusp k f) := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply, frickeOperatorCusp_levelRaise h hd he,
    normalizedFrickeOperatorCusp_def, LinearMap.smul_apply]
  have hα : atkinLehnerNormalizer N k =
      atkinLehnerNormalizer (d * e) k * atkinLehnerNormalizer M k := by
    rw [← h, atkinLehnerNormalizer_mul]
  rw [hα]
  ext τ
  simp only [FunLike.coe_smul, Pi.smul_apply, CuspForm.levelRaise_apply, smul_eq_mul]
  ring

/-- **The normalized Fricke operator intertwines the level-raises on modular forms**: for
`N = d * e * M`, `𝒲_N (V_d f) = (√(d e)) ^ (2 - k) · d⁻¹ · e ^ (k - 1) · V_e (𝒲_M f)`. -/
theorem normalizedFrickeOperator_levelRaise [NeZero M] [NeZero d] [NeZero e] [NeZero N]
    (h : d * e * M = N)
    (hd : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (he : (Gamma1 N).map (mapGL ℝ) ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • (Gamma1 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    normalizedFrickeOperator k (ModularForm.levelRaise d hd f) =
      (atkinLehnerNormalizer (d * e) k * (d : ℂ)⁻¹ * (e : ℂ) ^ (k - 1)) •
        ModularForm.levelRaise e he (normalizedFrickeOperator k f) := by
  rw [normalizedFrickeOperator_def, LinearMap.smul_apply, frickeOperator_levelRaise h hd he,
    normalizedFrickeOperator_def, LinearMap.smul_apply]
  have hα : atkinLehnerNormalizer N k =
      atkinLehnerNormalizer (d * e) k * atkinLehnerNormalizer M k := by
    rw [← h, atkinLehnerNormalizer_mul]
  rw [hα]
  ext τ
  simp only [FunLike.coe_smul, Pi.smul_apply, ModularForm.levelRaise_apply, smul_eq_mul]
  ring

/-! ### Stability of the old subspace -/

/-- **The Fricke operator preserves the old subspace**: `W_N` maps `S_k(Γ₁(N))ᵒˡᵈ` into itself.
A level-raise `V_d f` from a proper divisor level `M`, with `d * M ∣ N`, goes to a multiple of
`V_e (W_M f)` for the complementary `e = N / (d * M)` (`frickeOperatorCusp_levelRaise`), which is
again old. -/
theorem frickeOperatorCusp_mem_cuspFormsOld [NeZero N]
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    frickeOperatorCusp k f ∈ cuspFormsOld N k := by
  refine (cuspFormsOld_le (V := (cuspFormsOld N k).comap (frickeOperatorCusp k))
    fun M d hdM hM g ↦ ?_) hf
  obtain ⟨e, he⟩ := hdM
  have hN : d * e * M = N := by rw [he]; ring
  have heM : e * M ∣ N := ⟨d, by rw [← hN]; ring⟩
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd ⟨e, he⟩)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd ⟨e, he⟩)
  have : NeZero e := NeZero.of_dvd (dvd_of_mul_right_dvd heM)
  rw [Submodule.mem_comap, frickeOperatorCusp_levelRaise hN _
    (Gamma1_map_le_conjAct_scaleGL_of_dvd heM)]
  exact Submodule.smul_mem _ _ (levelRaise_mem_cuspFormsOld heM hM k _)

/-- **The normalized Fricke operator preserves the old subspace**: `𝒲_N` maps
`S_k(Γ₁(N))ᵒˡᵈ` into itself, being a scalar multiple of `W_N`. -/
theorem normalizedFrickeOperatorCusp_mem_cuspFormsOld [NeZero N]
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    normalizedFrickeOperatorCusp k f ∈ cuspFormsOld N k := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (frickeOperatorCusp_mem_cuspFormsOld hf)

/-- **The Fricke operator carries the old subspace onto itself.** It maps the old subspace into
itself (`frickeOperatorCusp_mem_cuspFormsOld`), and every old form is `(frickeScalar N k)⁻¹`
times the image of the old form `W_N f`, since `W_N ∘ W_N = frickeScalar N k • id`. -/
theorem cuspFormsOld_map_frickeOperatorCusp (N : ℕ) [NeZero N] (k : ℤ) :
    (cuspFormsOld N k).map (frickeOperatorCusp k) = cuspFormsOld N k := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun f hf ↦
    frickeOperatorCusp_mem_cuspFormsOld hf) fun f hf ↦ ?_
  refine ⟨(frickeScalar N k)⁻¹ • frickeOperatorCusp k f,
    Submodule.smul_mem _ _ (frickeOperatorCusp_mem_cuspFormsOld hf), ?_⟩
  rw [map_smul, frickeOperatorCusp_frickeOperatorCusp_apply, smul_smul,
    inv_mul_cancel₀ (frickeScalar_ne_zero k), one_smul]

/-- **The normalized Fricke operator carries the old subspace onto itself**: `𝒲_N` maps it into
itself (`normalizedFrickeOperatorCusp_mem_cuspFormsOld`), and squares to the unit `(-1) ^ k`. -/
theorem cuspFormsOld_map_normalizedFrickeOperatorCusp (N : ℕ) [NeZero N] (k : ℤ) :
    (cuspFormsOld N k).map (normalizedFrickeOperatorCusp k) = cuspFormsOld N k := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun f hf ↦
    normalizedFrickeOperatorCusp_mem_cuspFormsOld hf) fun f hf ↦ ?_
  refine ⟨(-1 : ℂ) ^ k • normalizedFrickeOperatorCusp k f,
    Submodule.smul_mem _ _ (normalizedFrickeOperatorCusp_mem_cuspFormsOld hf), ?_⟩
  rw [map_smul, normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply, smul_smul,
    ← mul_zpow, neg_one_mul, neg_neg, one_zpow, one_smul]

end TauCeti
