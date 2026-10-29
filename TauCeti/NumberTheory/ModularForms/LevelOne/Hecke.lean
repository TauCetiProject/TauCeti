/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule

/-!
# The Hecke operators `Tₙ` at level one

For a positive integer `n`, the classical Hecke operator `Tₙ` on modular forms of weight `k` on
`SL(2, ℤ)` sums the slashes of `f` over a set of representatives of `SL(2, ℤ) \ ℳₙ`, where `ℳₙ`
is the set of integral matrices of determinant `n`. With the upper-triangular representatives
`(a b; 0 d)`, `ad = n`, `0 < a`, `0 ≤ b < d`, of `FixedDetMatrices.reps n`, this is

`Tₙ f = ∑_{(a b; 0 d)} f ∣[k] (a b; 0 d)`,

which, with Mathlib's normalization of the slash action, is
`(Tₙ f)(τ) = n^(k-1) ∑_{ad = n} ∑_{0 ≤ b < d} d^(-k) f((aτ + b)/d)`.

Unlike the operator `HeckeRing.GL2.heckeTNat` of the single double coset
`SL(2, ℤ) diag(1, n) SL(2, ℤ)`, the sum runs over all of `ℳₙ`, that is over every double coset
`SL(2, ℤ) diag(a, d) SL(2, ℤ)` with `a ∣ d` and `ad = n`; so it is the classical `Tₙ` at every
`n`, not only at squarefree ones. The representatives are those through which Popa and Zagier
compute the Hecke action on period polynomials. Its comparison with the level-one action of the
Hecke-ring element `HeckeRing.GL2.heckeTCompositeGamma0 1 n`, for instance through the coefficient
formula `aₘ(Tₙ f) = ∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)`, is not proved here.

The sum is independent of the representatives in the sense that matters here: right
multiplication by `γ ∈ SL(2, ℤ)` permutes the cosets `SL(2, ℤ) A`, so `Tₙ f` is invariant under
`SL(2, ℤ)` when `f` is (`TauCeti.ModularForm.heckeSlashLevelOne_slash_eq`). Holomorphy and the
behaviour at the cusps pass through finite sums of rational slashes, so `Tₙ` preserves modular and
cusp forms.

## Main definitions

* `TauCeti.ModularForm.heckeSlashLevelOne k n f`: the slash sum `∑ f ∣[k] (a b; 0 d)` over the
  representatives `FixedDetMatrices.reps n`, for a function `f : ℍ → ℂ`.
* `TauCeti.ModularForm.heckeTLevelOne k n`: `Tₙ` on `M_k(SL(2, ℤ))`.
* `TauCeti.ModularForm.heckeTCuspLevelOne k n`: `Tₙ` on `S_k(SL(2, ℤ))`.

## Main results

* `TauCeti.ModularForm.heckeSlashLevelOne_slash_eq`: the slash sum of an `SL(2, ℤ)`-invariant
  function is `SL(2, ℤ)`-invariant.
* `TauCeti.ModularForm.mdifferentiable_heckeSlashLevelOne`: the slash sum of a holomorphic
  function is holomorphic.
* `TauCeti.ModularForm.coe_heckeTLevelOne`, `TauCeti.ModularForm.coe_heckeTCuspLevelOne`: both
  operators are the slash sum on underlying functions, and
  `TauCeti.ModularForm.heckeTLevelOne_coe_cuspForm`: they agree on cusp forms.

## References

* [J.-P. Serre, *A course in arithmetic*][serre1973], Chapter VII, §5.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
-/

public section

open Matrix UpperHalfPlane FixedDetMatrices
open Matrix.SpecialLinearGroup (mapGL)

open scoped MatrixGroups ModularForm Manifold

namespace TauCeti.ModularForm

variable (k : ℤ) (n : ℕ) [NeZero n]

/-- The determinant `n` of a Hecke operator `Tₙ`, as a nonzero integer. -/
private theorem natCast_ne_zero : (n : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.2 (NeZero.ne n)

/-- **The level-one Hecke slash sum** `∑ f ∣[k] (a b; 0 d)`, over the upper-triangular
representatives `(a b; 0 d)` of `SL(2, ℤ) \ ℳₙ` in `FixedDetMatrices.reps n`. On a level-one
modular form this is the classical Hecke operator `Tₙ`
(`TauCeti.ModularForm.heckeTLevelOne`). -/
noncomputable def heckeSlashLevelOne (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ A : reps (n : ℤ), f ∣[k] toGL (natCast_ne_zero n) A.1

/-- The defining equation of `heckeSlashLevelOne`. -/
theorem heckeSlashLevelOne_def (f : ℍ → ℂ) :
    heckeSlashLevelOne k n f =
      ∑ A : reps (n : ℤ), f ∣[k] toGL (Int.natCast_ne_zero.2 (NeZero.ne n)) A.1 := (rfl)

/-- The slash sum is additive in `f`. -/
@[simp]
theorem heckeSlashLevelOne_add (f g : ℍ → ℂ) :
    heckeSlashLevelOne k n (f + g) = heckeSlashLevelOne k n f + heckeSlashLevelOne k n g := by
  simp [heckeSlashLevelOne_def, Finset.sum_add_distrib]

/-- The slash sum is homogeneous in `f`: every representative has positive determinant `n`, so
scalars pass through the slashes. -/
@[simp]
theorem heckeSlashLevelOne_smul (c : ℂ) (f : ℍ → ℂ) :
    heckeSlashLevelOne k n (c • f) = c • heckeSlashLevelOne k n f := by
  rw [heckeSlashLevelOne_def, heckeSlashLevelOne_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ ↦ ModularForm.rat_smul_slash_of_det_pos k ?_ f c
  rw [det_toGL]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-! ### Invariance under `SL(2, ℤ)` -/

/-- A matrix of `SL(2, ℤ)` moving the right translate `A γ⁻¹` back into `reps n`. -/
private noncomputable def repsRightMulFactor (γ : SL(2, ℤ)) (A : reps (n : ℤ)) : SL(2, ℤ) :=
  (exists_smul_mem_reps (natCast_ne_zero n) (traceFormulaMatrixRight γ A.1)).choose

/-- **Right multiplication by `γ⁻¹` on `SL(2, ℤ) \ ℳₙ`**, read on the representatives `reps n`:
the representative of the coset `SL(2, ℤ) A γ⁻¹`. -/
private noncomputable def repsRightMul (γ : SL(2, ℤ)) (A : reps (n : ℤ)) : reps (n : ℤ) :=
  ⟨repsRightMulFactor n γ A • traceFormulaMatrixRight γ A.1,
    (exists_smul_mem_reps (natCast_ne_zero n) (traceFormulaMatrixRight γ A.1)).choose_spec⟩

private theorem coe_repsRightMul (γ : SL(2, ℤ)) (A : reps (n : ℤ)) :
    (repsRightMul n γ A).1 = repsRightMulFactor n γ A • traceFormulaMatrixRight γ A.1 := (rfl)

private theorem toGL_repsRightMul (hn : (n : ℤ) ≠ 0) (γ : SL(2, ℤ)) (A : reps (n : ℤ)) :
    toGL hn (repsRightMul n γ A).1 =
      mapGL ℚ (repsRightMulFactor n γ A) * (toGL hn A.1 * mapGL ℚ γ⁻¹) := by
  rw [coe_repsRightMul, toGL_smul, toGL_traceFormulaMatrixRight]

/-- Right multiplication by `γ⁻¹` permutes `SL(2, ℤ) \ ℳₙ`: distinct cosets have distinct right
translates. -/
private theorem repsRightMul_injective (γ : SL(2, ℤ)) :
    Function.Injective (repsRightMul n γ) := by
  intro A B h
  have hn := natCast_ne_zero n
  have hGL := congrArg (fun C : reps (n : ℤ) ↦ toGL hn C.1) h
  simp only [toGL_repsRightMul] at hGL
  -- cancel `γ` on the right and move the left factors across: `A = g • B` for some `g`
  have hAB : toGL hn A.1 =
      toGL hn (((repsRightMulFactor n γ A)⁻¹ * repsRightMulFactor n γ B) • B.1) := by
    rw [toGL_smul, map_mul, map_inv]
    simpa [mul_assoc] using
      congrArg (fun x ↦ (mapGL ℚ (repsRightMulFactor n γ A))⁻¹ * x * (mapGL ℚ γ⁻¹)⁻¹) hGL
  exact (Subtype.ext (eq_of_smul_eq_of_mem_reps B.2 A.2 (toGL_injective hn hAB).symm)).symm

/-- **The slash sum of an `SL(2, ℤ)`-invariant function is `SL(2, ℤ)`-invariant.** Right
multiplication by `γ ∈ SL(2, ℤ)` permutes the cosets `SL(2, ℤ) A`, `A ∈ ℳₙ`, and the slash of an
invariant function by `A` depends only on the coset of `A`. -/
theorem heckeSlashLevelOne_slash_eq {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ 𝒮ℒ) : heckeSlashLevelOne k n f ∣[k] γ = heckeSlashLevelOne k n f := by
  obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hγ
  have hn := natCast_ne_zero n
  have hfσ (g : SL(2, ℤ)) : f ∣[k] (mapGL ℚ g : GL (Fin 2) ℚ) = f := by
    rw [ModularForm.rat_slash_mapGL]
    exact hf _ ⟨g, rfl⟩
  -- slashing the summand of `A` by `σ` gives the summand of the representative of `A σ`, which
  -- is `repsRightMul n σ⁻¹ A`
  have hperm (A : reps (n : ℤ)) :
      (f ∣[k] toGL hn A.1) ∣[k] (mapGL ℚ σ : GL (Fin 2) ℚ) =
        f ∣[k] toGL hn (repsRightMul n σ⁻¹ A).1 := by
    rw [toGL_repsRightMul, inv_inv, SlashAction.slash_mul, SlashAction.slash_mul, hfσ,
      ← SlashAction.slash_mul]
  let e := Equiv.ofBijective _ (repsRightMul_injective n σ⁻¹).bijective_of_finite
  rw [← ModularForm.rat_slash_mapGL, heckeSlashLevelOne_def, SlashAction.sum_slash]
  exact Fintype.sum_equiv e _ _ hperm

/-! ### The operators on modular forms and cusp forms -/

/-- The slash sum of a holomorphic function is holomorphic. -/
theorem mdifferentiable_heckeSlashLevelOne {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (heckeSlashLevelOne k n f) := by
  rw [heckeSlashLevelOne_def]
  refine MDifferentiable.sum fun A _ ↦ ?_
  rw [ModularForm.rat_slash]
  exact hf.slash k _

/-- `Tₙ` as a map of modular forms. -/
private noncomputable def heckeTLevelOneAux (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toFun := heckeSlashLevelOne k n f
  slash_action_eq' _ hγ := heckeSlashLevelOne_slash_eq k n
    (fun γ hγ ↦ SlashInvariantFormClass.slash_action_eq f γ hγ) hγ
  holo' := mdifferentiable_heckeSlashLevelOne k n (ModularFormClass.holo f)
  bdd_at_cusps' hc := OnePoint.isBoundedAt_sum_rat_slash k _ _
    (fun _ hc ↦ ModularFormClass.bdd_at_cusps f hc) hc

private theorem coe_heckeTLevelOneAux (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeTLevelOneAux k n f) = heckeSlashLevelOne k n f := (rfl)

/-- `Tₙ` as a map of cusp forms. -/
private noncomputable def heckeTCuspLevelOneAux (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k :=
  { heckeTLevelOneAux k n (f : ModularForm 𝒮ℒ k) with
    zero_at_cusps' := fun hc ↦ OnePoint.isZeroAt_sum_rat_slash k _ _
      (fun _ hc ↦ CuspFormClass.zero_at_cusps f hc) hc }

private theorem coe_heckeTCuspLevelOneAux (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeTCuspLevelOneAux k n f) = heckeSlashLevelOne k n f := (rfl)

/-- **The Hecke operator `Tₙ` on `M_k(SL(2, ℤ))`**, `f ↦ ∑ f ∣[k] (a b; 0 d)`, the sum over the
upper-triangular representatives of `SL(2, ℤ) \ ℳₙ`. It runs over all of `ℳₙ`, so it is the
classical `Tₙ` at every `n ≥ 1`. -/
noncomputable def heckeTLevelOne : Module.End ℂ (ModularForm 𝒮ℒ k) where
  toFun := heckeTLevelOneAux k n
  map_add' f g := by ext τ; simp [coe_heckeTLevelOneAux]
  map_smul' c f := by ext τ; simp [coe_heckeTLevelOneAux]

/-- **The Hecke operator `Tₙ` on `S_k(SL(2, ℤ))`**: the operator `heckeTLevelOne` restricted to
cusp forms, which it preserves. -/
noncomputable def heckeTCuspLevelOne : Module.End ℂ (CuspForm 𝒮ℒ k) where
  toFun := heckeTCuspLevelOneAux k n
  map_add' f g := by ext τ; simp [coe_heckeTCuspLevelOneAux]
  map_smul' c f := by ext τ; simp [coe_heckeTCuspLevelOneAux]

/-- On underlying functions, `Tₙ` is the slash sum over the representatives of
`SL(2, ℤ) \ ℳₙ`. -/
@[simp]
theorem coe_heckeTLevelOne (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeTLevelOne k n f) = heckeSlashLevelOne k n f := (rfl)

/-- On underlying functions, the cusp-form `Tₙ` is the slash sum over the representatives of
`SL(2, ℤ) \ ℳₙ`. -/
@[simp]
theorem coe_heckeTCuspLevelOne (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeTCuspLevelOne k n f) = heckeSlashLevelOne k n f := (rfl)

/-- `Tₙ` commutes with the inclusion of cusp forms into modular forms. -/
theorem heckeTLevelOne_coe_cuspForm (f : CuspForm 𝒮ℒ k) :
    heckeTLevelOne k n (f : ModularForm 𝒮ℒ k) = (heckeTCuspLevelOne k n f : ModularForm 𝒮ℒ k) :=
  ModularForm.ext fun _ ↦ rfl

end TauCeti.ModularForm
