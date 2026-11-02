/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.NumberTheory.Divisors
public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
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
compute the Hecke action on period polynomials.

On `q`-expansions, `Tₙ` has the classical divisor-sum formula

`aₘ(Tₙ f) = ∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)`,

for every `m ≥ 0`, which is the arithmetic normalization of the Hecke operators fixed by
Diamond–Shurman. It is computed from the factorization `(a b; 0 d) = (1 b; 0 d) · diag(a, 1)`
of the representatives. The `d` representatives with the same diagonal `(a, d)` sum to
`(U_d f) ∣[k] diag(a, 1)`, where `U_d f = ∑_{b < d} f ∣[k] (1 b; 0 d)` has coefficients
`aₘ(U_d f) = a_{dm}(f)`, and slashing by `diag(a, 1)` spreads an expansion along `a ℕ` and
multiplies it by `a^(k-1)`. Summing over the factor pairs `ad = n` gives the formula. In
particular `a₁(Tₙ f) = aₙ(f)` and `a₀(Tₙ f) = (∑_{d ∣ n} d^(k-1)) a₀(f)`. The formula has the
shape of the level-`N` formula
`HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero` for the
Hecke-ring element `HeckeRing.GL2.heckeTCompositeGamma0 N n`, with trivial character; no
comparison of the two operators is made here.

The sum is independent of the representatives in the sense that matters here: right
multiplication by `γ ∈ SL(2, ℤ)` permutes the cosets `SL(2, ℤ) A`, so `Tₙ f` is invariant under
`SL(2, ℤ)` when `f` is (`TauCeti.heckeSlashLevelOne_slash_eq`). Holomorphy and the
behaviour at the cusps pass through finite sums of rational slashes, so `Tₙ` preserves modular and
cusp forms.

## Main definitions

* `TauCeti.heckeSlashLevelOne k n f`: the slash sum `∑ f ∣[k] (a b; 0 d)` over the
  representatives `FixedDetMatrices.reps n`, for a function `f : ℍ → ℂ`.
* `TauCeti.heckeTLevelOne k n`: `Tₙ` on `M_k(SL(2, ℤ))`.
* `TauCeti.heckeTCuspLevelOne k n`: `Tₙ` on `S_k(SL(2, ℤ))`.

## Main results

* `TauCeti.heckeSlashLevelOne_slash_eq`: the slash sum of an `SL(2, ℤ)`-invariant
  function is `SL(2, ℤ)`-invariant.
* `TauCeti.mdifferentiable_heckeSlashLevelOne`: the slash sum of a holomorphic
  function is holomorphic.
* `TauCeti.coe_heckeTLevelOne`, `TauCeti.coe_heckeTCuspLevelOne`: both
  operators are the slash sum on underlying functions, and
  `TauCeti.heckeTLevelOne_coe_cuspForm`: they agree on cusp forms.
* `TauCeti.heckeSlashLevelOne_eq_sum_heckeSlashUpperTri_slash`: the slash sum is
  `∑_{ad = n} (U_d f) ∣[k] diag(a, 1)`.
* `TauCeti.hasSum_qExpansion_heckeSlashLevelOne`: the `q`-expansion of the slash sum of a
  `1`-periodic holomorphic function bounded at `i∞`.
* `TauCeti.qExpansion_coeff_heckeTLevelOne`, `TauCeti.qExpansion_coeff_heckeTCuspLevelOne`: the
  coefficient formula `aₘ(Tₙ f) = ∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)`.
* `TauCeti.qExpansion_coeff_one_heckeTLevelOne`, `TauCeti.qExpansion_coeff_one_heckeTCuspLevelOne`:
  `a₁(Tₙ f) = aₙ(f)`; `TauCeti.qExpansion_coeff_zero_heckeTLevelOne`:
  `a₀(Tₙ f) = (∑_{d ∣ n} d^(k-1)) a₀(f)`.

## References

* [J.-P. Serre, *A course in arithmetic*][serre1973], Chapter VII, §5.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.3.1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
-/

public section

open Matrix UpperHalfPlane FixedDetMatrices HeckeRing.GL2 HeckeRing.GLn Function
open Matrix.SpecialLinearGroup (mapGL)

open scoped MatrixGroups ModularForm Manifold

namespace TauCeti

variable (k : ℤ) (n : ℕ) [NeZero n]

/-- The determinant `n` of a Hecke operator `Tₙ`, as a nonzero integer. -/
private theorem natCast_ne_zero : (n : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.2 (NeZero.ne n)

/-- **The level-one Hecke slash sum** `∑ f ∣[k] (a b; 0 d)`, over the upper-triangular
representatives `(a b; 0 d)` of `SL(2, ℤ) \ ℳₙ` in `FixedDetMatrices.reps n`. On a level-one
modular form this is the classical Hecke operator `Tₙ`
(`TauCeti.heckeTLevelOne`). -/
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

/-! ### Fourier coefficients -/

/-- The representative `(a b; 0 d)` of the factor pair `(a, d)` and the residue `b` is
`(1 b; 0 d) · diag(a, 1)`. -/
private theorem toGL_repsEquiv_symm
    (x : Σ p : ↥(n : ℤ).natAbs.divisorsAntidiagonal, Fin p.1.2) :
    toGL (natCast_ne_zero n) ((repsEquiv (natCast_ne_zero n)).symm x).1 =
      upperTriRep x.1.1.2 x.2 * natDiagGL 2 ![x.1.1.1, 1] := by
  have ha : 0 < x.1.1.1 :=
    Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.1.2)
  apply Units.ext
  rw [Units.val_mul, coe_toGL, coe_repsEquiv_symm_apply, coe_upperTriRep,
    natDiagGL_coe 2 _ fun i ↦ by fin_cases i <;> simp [ha]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Int.sign_natCast_of_ne_zero (NeZero.ne n)]

/-- **The slash sum by diagonal type**: `∑ f ∣[k] (a b; 0 d) = ∑_{ad = n} (U_d f) ∣[k] diag(a, 1)`,
where `U_d f = ∑_{b < d} f ∣[k] (1 b; 0 d)` is `HeckeRing.GL2.heckeSlashUpperTri k d f`. -/
theorem heckeSlashLevelOne_eq_sum_heckeSlashUpperTri_slash (f : ℍ → ℂ) :
    heckeSlashLevelOne k n f =
      ∑ p ∈ n.divisorsAntidiagonal,
        heckeSlashUpperTri k p.2 f ∣[k] (natDiagGL 2 ![p.1, 1] : GL (Fin 2) ℚ) := by
  rw [heckeSlashLevelOne_def, ← (repsEquiv (natCast_ne_zero n)).symm.sum_comp,
    Fintype.sum_sigma]
  have h (i : ↥(n : ℤ).natAbs.divisorsAntidiagonal) :
      ∑ b : Fin i.1.2, f ∣[k] toGL (natCast_ne_zero n)
          ((repsEquiv (natCast_ne_zero n)).symm ⟨i, b⟩).1 =
        heckeSlashUpperTri k i.1.2 f ∣[k] (natDiagGL 2 ![i.1.1, 1] : GL (Fin 2) ℚ) := by
    simp only [toGL_repsEquiv_symm, SlashAction.slash_mul, heckeSlashUpperTri_def,
      SlashAction.sum_slash]
  rw [Fintype.sum_congr _ _ h, Finset.sum_coe_sort (n : ℤ).natAbs.divisorsAntidiagonal
    fun p ↦ heckeSlashUpperTri k p.2 f ∣[k] (natDiagGL 2 ![p.1, 1] : GL (Fin 2) ℚ),
    Int.natAbs_natCast]

local notation "𝕢" => Function.Periodic.qParam

/-- **The `q`-expansion of the level-one Hecke slash sum.** For a `1`-periodic holomorphic `f`
bounded at `i∞`, the slash sum `∑ f ∣[k] (a b; 0 d)` has the expansion
`∑ₘ (∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)) qᵐ` at every point. -/
theorem hasSum_qExpansion_heckeSlashLevelOne {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (∑ d ∈ (m.gcd n).divisors,
        (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2)) • 𝕢 1 (τ : ℂ) ^ m)
      (heckeSlashLevelOne k n f τ) := by
  have hfper' : ∀ x : ℂ, f (ofComplex (x + 1)) = f (ofComplex x) := by
    simpa only [Periodic, Function.comp_apply] using hfper
  -- the expansion of the summand of each factor pair `(a, d)`
  have h : ∀ p ∈ n.divisorsAntidiagonal, HasSum (fun j : ℕ ↦ (if p.1 ∣ j then
      (p.1 : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (p.2 * (j / p.1)) else 0) • 𝕢 1 (τ : ℂ) ^ j)
      ((heckeSlashUpperTri k p.2 f ∣[k] (natDiagGL 2 ![p.1, 1] : GL (Fin 2) ℚ)) τ) := by
    intro p hp
    have : NeZero p.1 := ⟨Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp⟩
    have hd : 0 < p.2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
    have h := hasSum_slash_natDiagGL_d_one (d := p.1) k (N := 1) one_pos
      (by simpa using periodic_heckeSlashUpperTri k p.2 hfper)
      (mdifferentiable_heckeSlashUpperTri k p.2 hfhol)
      (isBoundedAtImInfty_heckeSlashUpperTri k p.2 hfbdd) τ
    simpa only [Nat.cast_one, qExpansion_coeff_heckeSlashUpperTri k p.2 hd hfper' hfhol hfbdd]
      using h
  rw [heckeSlashLevelOne_eq_sum_heckeSlashUpperTri_slash, Finset.sum_apply]
  refine (hasSum_sum h).congr_fun fun m ↦ ?_
  rw [← Finset.sum_smul, Nat.sum_divisorsAntidiagonal_ite_dvd (NeZero.ne n) m
    fun a j ↦ (a : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff j]

/-- **The coefficient formula for `Tₙ` on `M_k(SL(2, ℤ))`**:
`aₘ(Tₙ f) = ∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)` for every `m`. -/
theorem qExpansion_coeff_heckeTLevelOne (f : ModularForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeTLevelOne k n f)).coeff m =
      ∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2) := by
  have h τ := hasSum_qExpansion_heckeSlashLevelOne k n
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  simp only [← coe_heckeTLevelOne] at h
  exact (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL h m).symm

/-- **The coefficient formula for `Tₙ` on `S_k(SL(2, ℤ))`**:
`aₘ(Tₙ f) = ∑_{d ∣ (m, n)} d^(k-1) a_{mn/d²}(f)` for every `m`. -/
theorem qExpansion_coeff_heckeTCuspLevelOne (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeTCuspLevelOne k n f)).coeff m =
      ∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2) := by
  have h τ := hasSum_qExpansion_heckeSlashLevelOne k n
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  simp only [← coe_heckeTCuspLevelOne] at h
  exact (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL h m).symm

/-- The first coefficient of `Tₙ f` is the `n`-th coefficient of `f`: `a₁(Tₙ f) = aₙ(f)`. -/
theorem qExpansion_coeff_one_heckeTLevelOne (f : ModularForm 𝒮ℒ k) :
    (qExpansion 1 (heckeTLevelOne k n f)).coeff 1 = (qExpansion 1 f).coeff n := by
  rw [qExpansion_coeff_heckeTLevelOne]
  simp

/-- The first coefficient of `Tₙ f` is the `n`-th coefficient of `f`: `a₁(Tₙ f) = aₙ(f)`. -/
theorem qExpansion_coeff_one_heckeTCuspLevelOne (f : CuspForm 𝒮ℒ k) :
    (qExpansion 1 (heckeTCuspLevelOne k n f)).coeff 1 = (qExpansion 1 f).coeff n := by
  rw [qExpansion_coeff_heckeTCuspLevelOne]
  simp

/-- The constant coefficient of `Tₙ f` is `a₀(Tₙ f) = (∑_{d ∣ n} d^(k-1)) a₀(f)`. -/
theorem qExpansion_coeff_zero_heckeTLevelOne (f : ModularForm 𝒮ℒ k) :
    (qExpansion 1 (heckeTLevelOne k n f)).coeff 0 =
      (∑ d ∈ n.divisors, (d : ℂ) ^ (k - 1)) * (qExpansion 1 f).coeff 0 := by
  rw [qExpansion_coeff_heckeTLevelOne]
  simp [Finset.sum_mul]

end TauCeti
