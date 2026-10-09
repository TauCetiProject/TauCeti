/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Conjugate
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.Petersson.Conjugate
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne

/-!
# The conjugate of a newform

The conjugate form `f_ρ(τ) = conj (f (-conj τ))` has the complex-conjugate `q`-expansion
coefficients, and carries `S_k(N, χ)` to `S_k(N, χ⁻¹)` intertwining the Hecke operators
(`TauCeti/NumberTheory/ModularForms/Conjugate.lean`). This file shows that it also preserves the
old and the new subspaces of `S_k(Γ₁(N))`: it commutes with the level-raising operators that span
the old subspace, and it conjugates the Petersson product, so it preserves the orthogonal
complement. Consequently the conjugate of a newform `f` of nebentypus `χ` is again a newform,
of nebentypus `χ⁻¹`, with the conjugate eigenvalues: the **conjugate newform** `f_ρ` of
Miyake, §4.6. It is the form to which the Fricke involution sends `f`, up to a scalar.

For trivial nebentypus the good Hecke eigenvalues of a newform are real, so by strong
multiplicity one the conjugate newform is the newform itself.

## Main definitions

* `HeckeRing.GL2.Newform.conj`: the conjugate newform `f_ρ`.

## Main results

* `TauCeti.conj_mem_cuspFormsOld`, `TauCeti.conj_mem_cuspFormsNew`: `f ↦ f_ρ` preserves the
  old and the new subspaces.
* `HeckeRing.GL2.Newform.qExpansion_conj`: the coefficients of `f_ρ` are the conjugates of those
  of `f`.
* `HeckeRing.GL2.Newform.conj_conj`: `f ↦ f_ρ` is an involution on newforms.
* `HeckeRing.GL2.Newform.conj_eq_self_of_χ_eq_one`: a newform of trivial nebentypus is its own
  conjugate.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6, where the conjugate form is written `f_ρ`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Conjugation preserves the old subspace**: the conjugate of a level-raise `V_d g` from a
proper divisor level is the level-raise `V_d (g_ρ)`. -/
theorem conj_mem_cuspFormsOld {f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsOld N k) :
    CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f ∈ cuspFormsOld N k := by
  have key : cuspFormsOld N k ≤ (cuspFormsOld N k).comap
      (CuspForm.conjₗ (k := k) (Gamma1_map_le_conjAct_inv_J N)) :=
    cuspFormsOld_le fun M d h hM g ↦ by
      have := NeZero.of_dvd (dvd_of_mul_right_dvd h)
      rw [Submodule.mem_comap, CuspForm.conjₗ_apply, CuspForm.conj_levelRaise _ _
        (Gamma1_map_le_conjAct_inv_J M) (Gamma1_map_le_conjAct_scaleGL_of_dvd h)]
      exact levelRaise_mem_cuspFormsOld h hM k _
  simpa only [Submodule.mem_comap, CuspForm.conjₗ_apply] using key hf

/-- **Conjugation preserves the new subspace**: if `f` is a new cusp form of level `N`, so is
its conjugate `f_ρ`. -/
theorem conj_mem_cuspFormsNew {f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsNew N k) :
    CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f ∈ cuspFormsNew N k := by
  -- `f ↦ f_ρ` preserves the old subspace and conjugates the Petersson product, so it preserves
  -- the orthogonal complement of the old subspace.
  rw [cuspFormsNew_def, CuspForm.mem_peterssonOrthogonal_iff] at hf ⊢
  intro g hg
  have hJ := Gamma1_map_le_conjAct_inv_J N
  rw [← CuspForm.conj_conj hJ g, _root_.CuspForm.peterssonInnerCosets_conj_conj,
    hf _ (conj_mem_cuspFormsOld hg), map_zero]

end TauCeti

namespace HeckeRing.GL2.Newform

open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The conjugate newform** `f_ρ(τ) = conj (f (-conj τ))` of a newform `f` of nebentypus `χ`:
a newform of nebentypus `χ⁻¹` whose eigenvalues and `q`-expansion coefficients are the complex
conjugates of those of `f`. -/
noncomputable def conj (f : Newform N k) : Newform N k where
  toCuspForm := CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f.toCuspForm
  χ := f.χ⁻¹
  mem_charSpace := CuspForm.conj_mem_cuspFormCharSpace f.mem_charSpace
  eigenvalue n hn := starRingEnd ℂ (f.eigenvalue n hn)
  isEigen n hn := by
    have h := CuspForm.heckeRingHomCuspCharSpace_conjCharSpace_eq_smul n.ne_zero (f.isEigen n hn)
    have he : CuspForm.conjCharSpace k f.χ ⟨f.toCuspForm, f.mem_charSpace⟩ =
        ⟨_, CuspForm.conj_mem_cuspFormCharSpace f.mem_charSpace⟩ :=
      Subtype.ext (CuspForm.coe_conjCharSpace_apply _)
    rwa [he] at h
  ne_zero := by
    rw [← CuspForm.conj_zero (Gamma1_map_le_conjAct_inv_J N)]
    exact (CuspForm.conj_injective _).ne f.ne_zero
  isNew := conj_mem_cuspFormsNew f.isNew
  isNorm := by
    rw [CuspForm.qExpansion_conj one_pos (one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_map, f.isNorm, map_one]

/-- The underlying cusp form of the conjugate newform is the conjugate form. -/
@[simp]
theorem toCuspForm_conj (f : Newform N k) :
    f.conj.toCuspForm = CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f.toCuspForm :=
  (rfl)

/-- The nebentypus of the conjugate newform is the inverse, that is the complex conjugate, of the
nebentypus. -/
@[simp]
theorem χ_conj (f : Newform N k) : f.conj.χ = f.χ⁻¹ :=
  (rfl)

/-- The eigenvalues of the conjugate newform are the complex conjugates of the eigenvalues. -/
@[simp]
theorem eigenvalue_conj (f : Newform N k) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    f.conj.eigenvalue n hn = starRingEnd ℂ (f.eigenvalue n hn) :=
  (rfl)

/-- The `q`-expansion coefficients of the conjugate newform are the complex conjugates of those of
the newform. -/
theorem qExpansion_conj (f : Newform N k) :
    qExpansion 1 f.conj.toCuspForm = PowerSeries.map (starRingEnd ℂ) (qExpansion 1 f.toCuspForm) :=
  CuspForm.qExpansion_conj one_pos (one_mem_strictPeriods_Gamma1_map N) _ _

/-- Conjugating a newform twice gives it back. -/
@[simp]
theorem conj_conj (f : Newform N k) : f.conj.conj = f :=
  Newform.ext (CuspForm.conj_conj _ _)

/-- **A newform of trivial nebentypus is its own conjugate.** -/
theorem conj_eq_self_of_χ_eq_one (f : Newform N k) (hχ : f.χ = 1) : f.conj = f := by
  -- The good eigenvalues of `f` are real, so `f` and `f_ρ` have the same nebentypus and the same
  -- good eigenvalues, hence are equal by strong multiplicity one.
  refine Newform.eq_of_forall_prime_eigenvalue_eq (by rw [χ_conj, hχ]; ext; simp) fun p hp hpN ↦
    (eigenvalue_conj f ⟨p, hp.pos⟩ hpN).trans ?_
  conv_rhs => rw [f.toEigenformAwayFromLevel.eigenvalue_eq_mul_conj hp hpN]
  simp [hχ]

end HeckeRing.GL2.Newform
