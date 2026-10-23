/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Killing.InvariantForm
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.Cochain
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Whitehead

/-!
# Two-cocycles on loop algebras and their cohomology classes

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
these hypotheses with `Ψ` its Killing form.

The vanishing on constant loops is a normalisation that every 2-cocycle admits up to a coboundary
when `L` is finite-dimensional with nondegenerate Killing form over a field of characteristic zero.
For each mode `n`, the cocycle identity says that `x ↦ (y ↦ c(x_0, y_n))` is a 1-cocycle of `L`
with values in the coadjoint module `Module.Dual K L`. This module is finite-dimensional, so
Whitehead's first lemma writes the block as `c(x_0, y_n) = -φ_n ⁅x, y⁆`, and subtracting the
coboundary of the 1-cochain `y_n ↦ φ_n y` removes all values on constant loops. Working one mode
at a time avoids any Whitehead lemma for the infinite-dimensional dual of the loop algebra.

Combining the two steps, the 2-cocycles on `loopAlgebra K ℤ L` are the sums of a multiple of the
residue cocycle and a coboundary. Conversely a nonzero multiple of the residue 2-cochain of a
nonzero symmetric form is never a coboundary: on `(x_1, y_{-1})` and `(x_{-1}, y_1)` it takes
opposite values `∓Ψ(x, y)`, while a coboundary takes the same value `-f(⁅x, y⁆_0)` on both.
Thus for a simple Lie algebra over an algebraically closed field of characteristic zero the second
cohomology of its loop algebra with trivial coefficients is one-dimensional, spanned by the residue
class of the Killing form.

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul`: the residue pairing on modes.
* `TauCeti.LieAlgebra.LoopAlgebra.residuePairing_one_tmul`: the residue pairing vanishes when its
  first argument is a constant loop.
* `TauCeti.LieAlgebra.LoopAlgebra.single_add_tmul_mem_span_lie`: for a perfect Lie algebra, every
  mode `x_{a + b}` is a linear combination of brackets `⁅y_a, z_b⁆`.
* `TauCeti.LieAlgebra.LoopAlgebra.exists_eq_smul_twoCocycleOfBilinear_iff`: **a 2-cocycle is a
  multiple of the residue cocycle if and only if it vanishes on constant loops**, for a form `Ψ`
  spanning the invariant forms and nonzero on some bracket.
* `TauCeti.LieAlgebra.LoopAlgebra.exists_eq_smul_twoCocycleOfBilinear_killingForm_iff`: the case
  of the Killing form of a simple Lie algebra.
* `TauCeti.LieAlgebra.LoopAlgebra.exists_apply_one_tmul_eq_d₁₂_apply`: **every 2-cocycle agrees
  with a coboundary on constant loops**, for any exponent monoid.
* `TauCeti.LieAlgebra.LoopAlgebra.smul_twoCochainOfBilinear_mem_range_d₁₂_iff`: a multiple of the
  residue 2-cochain of a nonzero symmetric form is a coboundary only when the multiple is zero.
* `TauCeti.LieAlgebra.LoopAlgebra.twoCocycle_eq_span_sup_range_d₁₂`: **the 2-cocycles are the
  multiples of the residue cocycle plus coboundaries**.
* `TauCeti.LieAlgebra.LoopAlgebra.twoCocycle_eq_span_killingForm_sup_range_d₁₂`: the case of the
  Killing form of a simple Lie algebra.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for loop algebras and
  their central extensions by the residue cocycle.
* N. Jacobson, *Lie Algebras*, Chapter III, for Whitehead's first lemma.
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

section Perfect

variable {R A L : Type*} [CommRing R] [AddCommMonoid A] [LieRing L] [LieAlgebra R L]

/-- **Modes of a perfect Lie algebra are sums of brackets of modes.** If `L` is perfect, then for
all exponents `a` and `b` every mode `x_{a + b}` is a linear combination of brackets
`⁅y_a, z_b⁆` of modes `y_a = t^a ⊗ y` and `z_b = t^b ⊗ z`. -/
theorem single_add_tmul_mem_span_lie (hL : derivedSeries R L 1 = ⊤) (a b : A) (x : L) :
    (AddMonoidAlgebra.single (a + b) 1 ⊗ₜ x : loopAlgebra R A L) ∈ Submodule.span R
      {u | ∃ y z : L, ⁅(AddMonoidAlgebra.single a 1 ⊗ₜ y : loopAlgebra R A L),
        AddMonoidAlgebra.single b 1 ⊗ₜ z⁆ = u} := by
  have hx : x ∈ Submodule.span R {u | ∃ y z : L, ⁅y, z⁆ = u} := by
    rw [← coe_derivedSeries_one_eq, LieIdeal.toLieSubalgebra_toSubmodule, hL]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, z, rfl⟩ := hu
    refine Submodule.subset_span ⟨y, z, ?_⟩
    rw [ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one]
  | zero => simp
  | add u v _ _ hu hv => simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hu hv
  | smul r u _ hu => simpa only [TensorProduct.tmul_smul] using Submodule.smul_mem _ r hu

end Perfect

section ModeBlocks

variable {K A L : Type*} [CommRing K] [AddCommMonoid A] [LieRing L] [LieAlgebra K L]

/-- The mode block `(x, y) ↦ c(x_m, y_n)` of a 2-cochain on the loop algebra, as a bilinear form
on `L`. -/
private noncomputable def modeForm
    (c : twoCochain K (loopAlgebra K A L) (TrivialLieModule K (loopAlgebra K A L) K)) (m n : A) :
    LinearMap.BilinForm K L :=
  (c.val.compl₁₂ (TensorProduct.mk K _ L (AddMonoidAlgebra.single m 1))
    (TensorProduct.mk K _ L (AddMonoidAlgebra.single n 1))).compr₂
    (TrivialLieModule.equiv K (loopAlgebra K A L) K).toLinearMap

private theorem modeForm_apply
    (c : twoCochain K (loopAlgebra K A L) (TrivialLieModule K (loopAlgebra K A L) K)) (m n : A)
    (x y : L) :
    modeForm c m n x y = TrivialLieModule.equiv K (loopAlgebra K A L) K
      (c (AddMonoidAlgebra.single m 1 ⊗ₜ x) (AddMonoidAlgebra.single n 1 ⊗ₜ y)) :=
  (rfl)

/-- The cocycle identity for trivial coefficients, evaluated on three modes. -/
private theorem cocycle_single_tmul
    (c : twoCocycle K (loopAlgebra K A L) (TrivialLieModule K (loopAlgebra K A L) K))
    (k m n : A) (x y z : L) :
    modeForm c.1 k (m + n) x ⁅y, z⁆ =
      modeForm c.1 (k + m) n ⁅x, y⁆ z + modeForm c.1 m (k + n) y ⁅x, z⁆ := by
  have h := (mem_twoCocycle_iff_of_trivial _ _ _ c.1).mp c.2 (AddMonoidAlgebra.single k 1 ⊗ₜ x)
    (AddMonoidAlgebra.single m 1 ⊗ₜ y) (AddMonoidAlgebra.single n 1 ⊗ₜ z)
  simp only [ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one] at h
  simp only [modeForm_apply, h, map_add]

end ModeBlocks

section Classification

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

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
      ∀ (x : L) (a : loopAlgebra K ℤ L), c.1 (1 ⊗ₜ x) a = 0 :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  exists_eq_smul_twoCocycleOfBilinear_iff _ _
    (fun _ hΦ => TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ) exists_killingForm_lie_ne_zero c

end Classification

section Normalization

variable {K A L : Type*} [Field K] [CharZero K] [AddCommMonoid A] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]

/-- **Every 2-cocycle on a loop algebra agrees with a coboundary on constant loops.** Let `L` be a
finite-dimensional Lie algebra with nondegenerate Killing form over a field of characteristic
zero. For every 2-cocycle `c` with trivial coefficients on `loopAlgebra K A L` there is a 1-cochain
`f` with `c(1 ⊗ x, a) = d₁₂ f (1 ⊗ x, a)` for all `x` and `a`, so that `c - d₁₂ f` vanishes
whenever its first argument is a constant loop. -/
theorem exists_apply_one_tmul_eq_d₁₂_apply
    (c : twoCocycle K (loopAlgebra K A L) (TrivialLieModule K (loopAlgebra K A L) K)) :
    ∃ f : oneCochain K (loopAlgebra K A L) (TrivialLieModule K (loopAlgebra K A L) K),
      ∀ (x : L) (a : loopAlgebra K A L), c.1 (1 ⊗ₜ x) a = d₁₂ K _ _ f (1 ⊗ₜ x) a := by
  set e := TrivialLieModule.equiv K (loopAlgebra K A L) K
  -- Each mode block `x ↦ (y ↦ c(x_0, y_n))` is a 1-cocycle in the finite-dimensional coadjoint
  -- module, hence inner by Whitehead's first lemma, applied one mode at a time.
  have hblock (n : A) : ∃ φ : Module.Dual K L, ∀ x y : L, modeForm c.1 0 n x y = -φ ⁅x, y⁆ := by
    have hD : d₁₂ K L (Module.Dual K L) (modeForm c.1 0 n) = 0 := by
      ext x y z
      have h := cocycle_single_tmul c 0 0 n x y z
      rw [zero_add, add_zero] at h
      simp only [d₁₂_apply_coe_apply_apply, Submodule.coe_zero, LinearMap.zero_apply,
        LinearMap.sub_apply, Module.Dual.lie_apply]
      linear_combination h
    obtain ⟨φ, hφ⟩ := exists_eq_lie_of_d₁₂_eq_zero hD
    exact ⟨φ, fun x y ↦ by rw [hφ x, Module.Dual.lie_apply]⟩
  choose φ hφ using hblock
  -- The 1-cochain `y_n ↦ φ n y` has the same values as `c` on constant loops.
  refine ⟨e.symm.toLinearMap ∘ₗ Finsupp.lsum K φ ∘ₗ (toFinsupp K A L).toLinearMap,
    fun x a ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (toFinsupp K A L).symm.surjective a
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n y =>
    apply e.injective
    rw [toFinsupp_symm_single, d₁₂_apply_apply_ofTrivial, AddMonoidAlgebra.one_def,
      ← modeForm_apply, hφ]
    simp [ExtendScalars.bracket_tmul, e]

end Normalization

section ResidueClass

variable {K L : Type*} [CommRing K] [IsDomain K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- **The residue 2-cochain of a nonzero symmetric form is not a coboundary.** Over a
characteristic-zero domain, a multiple `t • c_Ψ` of the residue 2-cochain of a nonzero symmetric
form `Ψ` on `L` is a coboundary on the loop algebra `loopAlgebra K ℤ L` only for `t = 0`. -/
theorem smul_twoCochainOfBilinear_mem_range_d₁₂_iff {Ψ : LinearMap.BilinForm K L}
    (hΨs : Ψ.IsSymm) (hΨ : Ψ ≠ 0) (t : K) :
    t • twoCochainOfBilinear K ℤ L Ψ hΨs ∈
        LinearMap.range (d₁₂ K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) ↔
      t = 0 := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ht ↦ by simp [ht]⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y : L, Ψ x y ≠ 0 := by
    by_contra! h
    exact hΨ (LinearMap.ext₂ h)
  -- On `(x_m, y_{-m})` the residue 2-cochain is `-m Ψ(x, y)`, while every coboundary takes the
  -- value `-f([x, y]_0)`, independent of `m`.
  have hval (m : ℤ) : t * (-m * Ψ x y) = -TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
      (f (AddMonoidAlgebra.single 0 1 ⊗ₜ ⁅x, y⁆)) := by
    have h := congrArg (fun c ↦ TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
      (c (AddMonoidAlgebra.single m 1 ⊗ₜ x) (AddMonoidAlgebra.single (-m) 1 ⊗ₜ y))) hf
    simp only [d₁₂_apply_apply_ofTrivial, ExtendScalars.bracket_tmul,
      AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one, smul_apply_apply, map_neg,
      map_smul, twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply,
      residuePairing_single_tmul, ite_true, smul_eq_mul, zsmul_eq_mul, Int.cast_neg] at h
    linear_combination -h
  have h2 : (2 : K) * t * Ψ x y = 0 := by
    linear_combination (hval (-1)) - (hval 1)
  simpa [hxy] using h2

end ResidueClass

section SecondCohomology

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L]

/-- **The second cohomology of a loop algebra is spanned by the residue class.** Let `L` be a
finite-dimensional Lie algebra with nondegenerate Killing form over a field of characteristic
zero, and `Ψ` an invariant symmetric form on `L` spanning the invariant forms and nonzero on some
bracket. Then the 2-cocycles with trivial coefficients on `loopAlgebra K ℤ L` are exactly the sums
of a multiple of the residue cocycle of `Ψ` and a coboundary. -/
theorem twoCocycle_eq_span_sup_range_d₁₂ {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) :
    twoCocycle K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) =
      (K ∙ twoCochainOfBilinear K ℤ L Ψ hΨs) ⊔ LinearMap.range (d₁₂ K _ _) := by
  refine le_antisymm (fun c hc ↦ ?_) (sup_le ?_ range_d₁₂_le_twoCocycle)
  · -- Normalize `c` on constant loops, then identify the result with a residue multiple.
    obtain ⟨f, hf⟩ := exists_apply_one_tmul_eq_d₁₂_apply ⟨c, hc⟩
    obtain ⟨t, ht⟩ := (exists_eq_smul_twoCocycleOfBilinear_iff hΨ hΨs hspan hne
      ⟨c + d₁₂ K _ _ (-f), add_mem hc (range_d₁₂_le_twoCocycle ⟨-f, rfl⟩)⟩).mpr
      fun x a ↦ by simp [hf, -map_neg]
    have hc' : c = t • twoCochainOfBilinear K ℤ L Ψ hΨs + d₁₂ K _ _ f := by
      have h : c + d₁₂ K _ _ (-f) = _ := congrArg Subtype.val ht
      rw [Submodule.coe_smul, twoCocycleOfBilinear_coe, map_neg] at h
      exact eq_add_of_add_neg_eq h
    rw [hc']
    exact Submodule.add_mem_sup (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _))
      ⟨f, rfl⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (twoCocycleOfBilinear K ℤ L Ψ hΨ hΨs).2

/-- **The second cohomology of the loop algebra of a simple Lie algebra is spanned by the residue
class of the Killing form.** Here `L` is a finite-dimensional Lie algebra over an algebraically
closed field of characteristic zero whose adjoint module is irreducible and whose Killing form is
nondegenerate, for instance a simple Lie algebra. Together with
`smul_twoCochainOfBilinear_mem_range_d₁₂_iff`, this says that the second cohomology of
`loopAlgebra K ℤ L` with trivial coefficients is one-dimensional. -/
theorem twoCocycle_eq_span_killingForm_sup_range_d₁₂ [IsAlgClosed K]
    [_root_.LieModule.IsIrreducible K L L] :
    twoCocycle K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) =
      (K ∙ twoCochainOfBilinear K ℤ L (killingForm K L)
        (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))) ⊔
        LinearMap.range (d₁₂ K _ _) :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  twoCocycle_eq_span_sup_range_d₁₂ (_root_.LieModule.traceForm_lieInvariant K L L) _
    (fun _ hΦ => TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ) exists_killingForm_lie_ne_zero

end SecondCohomology

end TauCeti.LieAlgebra.LoopAlgebra
