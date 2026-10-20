/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Killing.InvariantForm

/-!
# Two-cocycles on loop algebras vanishing on constant loops

Let `L` be a Lie algebra over a characteristic-zero domain `K` and write `x_m = t^m ⊗ x` for the
modes of the polynomial loop algebra `loopAlgebra K ℤ L = K[t, t⁻¹] ⊗ L`. Mathlib attaches to an
invariant symmetric form `Ψ` on `L` the residue 2-cocycle
`LieAlgebra.LoopAlgebra.twoCocycleOfBilinear`, whose value on modes is
`(x_m, y_n) ↦ n Ψ(x, y) δ_{m + n, 0}`, the residue of `x_m d y_n` paired by `Ψ`.

This file proves the mode-recurrence step of the classification of central extensions of loop
algebras: if every invariant bilinear form on `L` is a multiple of `Ψ` and `Ψ ⁅x, y⁆ z ≠ 0` for
some `x, y, z`, then a 2-cocycle with trivial coefficients is a scalar multiple of the residue
cocycle of `Ψ` exactly when it vanishes whenever its first argument is a constant loop
`x_0 = 1 ⊗ x`.

The argument runs as follows. For a 2-cocycle `c` vanishing on constant loops, the cocycle
identity with a constant first argument says that each mode block `(x, y) ↦ c(x_m, y_n)` is an
invariant form on `L`, hence equal to `λ(m, n) Ψ`. The cocycle identity on three modes, together
with invariance of `Ψ`, then gives the recurrence `λ(k + m, n) = λ(k, m + n) + λ(m, k + n)`. Along
each line `m + n = s` this makes `a ↦ λ(a, s - a)` additive, hence linear in `a`; since it vanishes
at `a = s`, it vanishes identically unless `s = 0`, and on the line `s = 0` it is `a λ(1, -1)`.

A finite-dimensional Lie algebra over an algebraically closed field of characteristic zero with
irreducible adjoint module and nondegenerate Killing form, such as a simple Lie algebra, satisfies
these hypotheses with `Ψ` its Killing form. The vanishing on constant loops is the normalisation
that the Whitehead lemmas provide for an arbitrary 2-cocycle, after which this file identifies the
cocycle with a multiple of the residue cocycle.

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul`: the residue pairing on modes.
* `TauCeti.LieAlgebra.LoopAlgebra.residuePairing_one_tmul`: the residue pairing vanishes when its
  first argument is a constant loop.
* `TauCeti.LieAlgebra.LoopAlgebra.exists_eq_smul_twoCocycleOfBilinear_iff`: **a 2-cocycle is a
  multiple of the residue cocycle if and only if it vanishes on constant loops**, for a form `Ψ`
  spanning the invariant forms and nonzero on some bracket.
* `TauCeti.LieAlgebra.LoopAlgebra.exists_eq_smul_twoCocycleOfBilinear_killingForm_iff`: the case
  of the Killing form of a simple Lie algebra.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for loop algebras and
  their central extensions by the residue cocycle.
* C. Kassel, *Kähler differentials and coverings of complex simple Lie algebras extended over a
  commutative algebra*, J. Pure Appl. Algebra 34 (1984), for the universal central extension of
  current algebras.
-/

public section

open scoped TensorProduct

namespace TauCeti.LieAlgebra.LoopAlgebra

open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra _root_.LieModule.Cohomology

section ResiduePairing

variable {R A L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup A] [DecidableEq A] [DistribSMul A R] [SMulCommClass A R R]

/-- The residue pairing on modes: `Res(x_m d y_n)` paired by `Φ` is `n Φ(x, y)` when
`m + n = 0`, and zero otherwise. -/
theorem residuePairing_single_tmul (Φ : LinearMap.BilinForm R L) (m n : A) (x y : L) :
    residuePairing R A L Φ (AddMonoidAlgebra.single m 1 ⊗ₜ x)
        (AddMonoidAlgebra.single n 1 ⊗ₜ y) =
      if m + n = 0 then n • Φ x y else 0 := by
  rw [residuePairing_apply_apply, toFinsupp_single_tmul, toFinsupp_single_tmul,
    Finsupp.sum_single_index (by simp)]
  split_ifs with h
  · rw [eq_neg_of_add_eq_zero_left h, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (fun h' => h (by rw [← h', neg_add_cancel])), map_zero,
      LinearMap.zero_apply, smul_zero]

end ResiduePairing

section ResiduePairingConstant

variable {R A L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [Ring A] [Module A R] [SMulCommClass A R R]

/-- The residue pairing vanishes when its first argument is a constant loop `1 ⊗ x`. -/
theorem residuePairing_one_tmul (Φ : LinearMap.BilinForm R L) (x : L) (a : loopAlgebra R A L) :
    residuePairing R A L Φ (1 ⊗ₜ x) a = 0 := by
  rw [AddMonoidAlgebra.one_def, residuePairing_apply_apply, toFinsupp_single_tmul, Finsupp.sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases h : n = 0
  · rw [h, zero_smul]
  · rw [Finsupp.single_eq_of_ne (neg_ne_zero.mpr h), map_zero, LinearMap.zero_apply, smul_zero]

end ResiduePairingConstant

section Classification

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The mode block `(x, y) ↦ c(x_m, y_n)` of a 2-cochain on the loop algebra, as a bilinear form
on `L`. -/
private noncomputable def modeForm
    (c : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) (m n : ℤ) :
    LinearMap.BilinForm K L :=
  (c.val.compl₁₂ (TensorProduct.mk K _ L (AddMonoidAlgebra.single m 1))
    (TensorProduct.mk K _ L (AddMonoidAlgebra.single n 1))).compr₂
    (TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).toLinearMap

private theorem modeForm_apply
    (c : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) (m n : ℤ)
    (x y : L) :
    modeForm c m n x y = TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
      (c (AddMonoidAlgebra.single m 1 ⊗ₜ x) (AddMonoidAlgebra.single n 1 ⊗ₜ y)) :=
  (rfl)

/-- The cocycle identity for trivial coefficients, evaluated on three modes. -/
private theorem cocycle_single_tmul
    (c : twoCocycle K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K))
    (k m n : ℤ) (x y z : L) :
    modeForm c.1 k (m + n) x ⁅y, z⁆ =
      modeForm c.1 (k + m) n ⁅x, y⁆ z + modeForm c.1 m (k + n) y ⁅x, z⁆ := by
  have h := (mem_twoCocycle_iff_of_trivial _ _ _ c.1).mp c.2 (AddMonoidAlgebra.single k 1 ⊗ₜ x)
    (AddMonoidAlgebra.single m 1 ⊗ₜ y) (AddMonoidAlgebra.single n 1 ⊗ₜ z)
  simp only [ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one] at h
  simp only [modeForm_apply, h, map_add]

/-- **The 2-cocycles on a loop algebra vanishing on constant loops are the multiples of the
residue cocycle.** Let `Ψ` be an invariant symmetric form on `L` such that every invariant
bilinear form on `L` is a multiple of `Ψ` and `Ψ` does not vanish on all brackets. A 2-cocycle with
trivial coefficients on the polynomial loop algebra `loopAlgebra K ℤ L` is a scalar multiple of
the residue cocycle of `Ψ` if and only if it vanishes whenever its first argument is a constant
loop `1 ⊗ x`. -/
theorem exists_eq_smul_twoCocycleOfBilinear_iff [IsDomain K] [CharZero K]
    {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0)
    (c : twoCocycle K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) :
    (∃ t : K, c = t • twoCocycleOfBilinear K ℤ L Ψ hΨ hΨs) ↔
      ∀ (x : L) (a : loopAlgebra K ℤ L), c.1 (1 ⊗ₜ x) a = 0 := by
  refine ⟨?_, fun hc => ?_⟩
  · rintro ⟨t, rfl⟩ x a
    rw [Submodule.coe_smul, smul_apply_apply, twoCocycleOfBilinear_coe,
      twoCochainOfBilinear_apply_apply, residuePairing_one_tmul, map_zero, smul_zero]
  replace hc (x : L) (a : loopAlgebra K ℤ L) : c.1 (AddMonoidAlgebra.single 0 1 ⊗ₜ x) a = 0 := by
    rw [← AddMonoidAlgebra.one_def, hc]
  set e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  obtain ⟨x₀, y₀, z₀, h₀⟩ := hne
  -- Each mode block of `c` is an invariant form, hence a multiple `λ m n` of `Ψ`.
  have hinv (m n : ℤ) : (modeForm c.1 m n).lieInvariant L := by
    intro w x y
    have h := cocycle_single_tmul c 0 m n w x y
    rw [modeForm_apply, hc, map_zero, zero_add, zero_add] at h
    rw [← sub_eq_zero, sub_neg_eq_add, ← h]
  choose lam hlam using fun m n => hspan _ (hinv m n)
  have hlam_apply (m n : ℤ) (x y : L) : modeForm c.1 m n x y = lam m n * Ψ x y := by
    rw [hlam m n, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  -- The coefficients are cancelled against the nonzero value `Ψ ⁅x₀, y₀⁆ z₀`.
  have hcancel {a b : K} (h : a * Ψ ⁅x₀, y₀⁆ z₀ = b * Ψ ⁅x₀, y₀⁆ z₀) : a = b :=
    mul_right_cancel₀ h₀ h
  have hzero_left (n : ℤ) : lam 0 n = 0 := hcancel <| by
    rw [← hlam_apply, modeForm_apply, hc, map_zero, zero_mul]
  have hzero_right (m : ℤ) : lam m 0 = 0 := hcancel <| by
    rw [← hlam_apply, modeForm_apply, ← twoCochain_skew, hc, neg_zero, map_zero, zero_mul]
  -- The cocycle identity on three modes is a recurrence for `λ`.
  have hrec (k m n : ℤ) : lam (k + m) n = lam k (m + n) + lam m (k + n) := by
    have h := cocycle_single_tmul c k m n x₀ y₀ z₀
    have h₁ : Ψ x₀ ⁅y₀, z₀⁆ = Ψ ⁅x₀, y₀⁆ z₀ := by
      rw [← neg_neg (Ψ x₀ _), ← hΨ y₀ x₀ z₀, ← lie_skew, LinearMap.map_neg₂, neg_neg]
    have h₂ : Ψ y₀ ⁅x₀, z₀⁆ = -Ψ ⁅x₀, y₀⁆ z₀ := by rw [hΨ x₀ y₀ z₀, neg_neg]
    rw [hlam_apply, hlam_apply, hlam_apply, h₁, h₂] at h
    exact hcancel (by linear_combination (-1 : K) * h)
  -- Along each line `m + n = s`, the coefficient `a ↦ λ(a, s - a)` is additive, hence linear.
  have hline (s a : ℤ) : lam a (s - a) = a • lam 1 (s - 1) := by
    let f : ℤ →+ K :=
      AddMonoidHom.mk' (fun a => lam a (s - a)) fun k m => by
        simpa only [show m + (s - (k + m)) = s - k by ring, show k + (s - (k + m)) = s - m by ring]
          using hrec k m (s - (k + m))
    simpa [f] using map_zsmul f a 1
  have hlam_eq (m n : ℤ) : lam m n = if m + n = 0 then m * lam 1 (-1) else 0 := by
    have hm := hline (m + n) m
    rw [add_sub_cancel_left] at hm
    split_ifs with h
    · rw [hm, h, zsmul_eq_mul, zero_sub]
    · have hs := hline (m + n) (m + n)
      rw [sub_self, hzero_right, zsmul_eq_mul, eq_comm, mul_eq_zero, Int.cast_eq_zero] at hs
      rw [hm, hs.resolve_left h, smul_zero]
  refine ⟨-lam 1 (-1), Subtype.ext <| Subtype.ext ?_⟩
  ext m x n y
  apply e.injective
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.comp_apply,
    AddMonoidAlgebra.lsingle_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars]
  rw [twoCochain_val_apply, twoCochain_val_apply, ← modeForm_apply, hlam_apply, hlam_eq,
    Submodule.coe_smul, smul_apply_apply, map_smul, twoCocycleOfBilinear_coe,
    twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply, residuePairing_single_tmul]
  split_ifs with h
  · rw [eq_neg_of_add_eq_zero_right h, zsmul_eq_mul, smul_eq_mul, Int.cast_neg]
    ring
  · rw [zero_mul, smul_zero]

/-- **The 2-cocycles on the loop algebra of a simple Lie algebra vanishing on constant loops are
the multiples of the residue cocycle of the Killing form.** Here `L` is a finite-dimensional Lie
algebra over an algebraically closed field of characteristic zero whose adjoint module is
irreducible and whose Killing form is nondegenerate, for instance a simple Lie algebra. -/
theorem exists_eq_smul_twoCocycleOfBilinear_killingForm_iff {K L : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [_root_.LieModule.IsIrreducible K L L] [IsKilling K L]
    (c : twoCocycle K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) :
    (∃ t : K, c = t • twoCocycleOfBilinear K ℤ L (killingForm K L)
      (_root_.LieModule.traceForm_lieInvariant K L L)
      (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))) ↔
      ∀ (x : L) (a : loopAlgebra K ℤ L), c.1 (1 ⊗ₜ x) a = 0 := by
  refine exists_eq_smul_twoCocycleOfBilinear_iff _ _
    (fun _ hΦ => TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ) ?_ c
  have := _root_.LieModule.nontrivial_of_isIrreducible K L L
  -- A nontrivial Killing Lie algebra is not abelian, so some bracket is nonzero, and the
  -- nondegenerate Killing form detects it.
  have hab : ¬ IsLieAbelian L := by
    rw [IsKilling.isLieAbelian_iff_subsingleton K L, not_subsingleton_iff_nontrivial]
    infer_instance
  obtain ⟨x, y, hxy⟩ : ∃ x y : L, ⁅x, y⁆ ≠ 0 := by
    by_contra! h
    exact hab ⟨h⟩
  by_contra! h
  exact hxy ((IsKilling.killingForm_nondegenerate K L).1 _ (h x y))

end Classification

end TauCeti.LieAlgebra.LoopAlgebra
