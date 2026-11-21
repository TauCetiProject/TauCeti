/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
import TauCeti.Analysis.InnerProductSpace.FanDominance

/-!
# Row and column Schatten norms of finite families of operators

Let `a = (aₖ)` be a finite family of linear maps `E →ₗ[𝕜] F` between finite-dimensional inner
product spaces. Its *column* and *row* Schatten `p`-norms are

`C_p(a) = ‖(∑ₖ aₖ† aₖ)^(1/2)‖_p` and `R_p(a) = ‖(∑ₖ aₖ aₖ†)^(1/2)‖_p`,

the Schatten norms of the column and row square functions of `a`. These are the norms of the
noncommutative sequence spaces `L_p(ℓ²_C)` and `L_p(ℓ²_R)` that appear in the noncommutative
Khintchine inequalities of Lust-Piquard and Pisier, in their finite-dimensional form.

Both are realized as Schatten norms of a single operator. The block column
`blockColumn a : E →ₗ[𝕜] PiLp 2 (fun _ ↦ F)`, `x ↦ (aₖ x)ₖ`, is the column matrix with blocks
`aₖ`, and its Gram operator is `∑ₖ aₖ† aₖ`. The block row `blockRow a : PiLp 2 (fun _ ↦ E) →ₗ[𝕜] F`,
`y ↦ ∑ₖ aₖ yₖ`, is the row matrix with blocks `aₖ`, and `blockRow a ∘ (blockRow a)† = ∑ₖ aₖ aₖ†`.
Defining `C_p` and `R_p` through these operators makes them seminorms in `a`; the triangle
inequality for the square functions, which is not apparent from the formulas above, comes from that
of the Schatten norm.

For `1 ≤ p < 2` the Khintchine inequalities use the sum norm `inf_{a = b + c} (C_p(b) + R_p(c))`,
which is `(columnSchatten p ⊓ rowSchatten p) a` (`Seminorm.inf_apply`), and for `2 ≤ p` the
intersection norm `max (C_p(a)) (R_p(a))`, which is `(columnSchatten p ⊔ rowSchatten p) a`
(`Seminorm.sup_apply`).

## Main declarations

* `TauCeti.blockColumn`, `TauCeti.blockRow`: the block column and block row of a family, linear
  in the family; `TauCeti.adjoint_blockRow` identifies the adjoint of the block row of `a` with the
  block column of `(aₖ†)ₖ`.
* `TauCeti.columnSchatten`, `TauCeti.rowSchatten`: the column and row Schatten `p`-norms
  `C_p` and `R_p`, as seminorms on families.
* `TauCeti.columnSchatten_apply_eq_schatten_sqrt`, `TauCeti.rowSchatten_apply_eq_schatten_sqrt`:
  the square function formulas `C_p(a) = ‖(∑ₖ aₖ† aₖ)^(1/2)‖_p` and
  `R_p(a) = ‖(∑ₖ aₖ aₖ†)^(1/2)‖_p`.
* `TauCeti.rowSchatten_apply_eq_columnSchatten_apply_adjoint`: `R_p(a) = C_p((aₖ†)ₖ)`.
* `TauCeti.columnSchatten_apply_eq_zero_iff`, `TauCeti.rowSchatten_apply_eq_zero_iff`,
  `TauCeti.columnSchatten_inf_rowSchatten_apply_eq_zero_iff`: the column, row and sum norms are
  norms.
* `TauCeti.schatten_apply_le_columnSchatten`, `TauCeti.schatten_apply_le_rowSchatten`,
  `TauCeti.schatten_apply_le_columnSchatten_inf_rowSchatten`: every entry is bounded in `S_p` by
  `C_p(a)`, by `R_p(a)` and by the sum norm.
* `TauCeti.columnSchatten_smul_le`, `TauCeti.rowSchatten_smul_le`: multiplying the entries by
  scalars of modulus at most `c` multiplies both norms by at most `c`.
* `TauCeti.columnSchatten_two_apply`, `TauCeti.rowSchatten_two_apply`, `TauCeti.rowSchatten_two`:
  at `p = 2` both norms are `(∑ₖ ‖aₖ‖₂²)^(1/2)`, so they coincide.
* `TauCeti.columnSchatten_top_apply`, `TauCeti.rowSchatten_top_apply`: at `p = ∞` they are
  `‖∑ₖ aₖ† aₖ‖^(1/2)` and `‖∑ₖ aₖ aₖ†‖^(1/2)`.

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260, §I.
* G. Pisier and Q. Xu, *Non-commutative martingale inequalities*, Comm. Math. Phys. 189 (1997),
  667–698, §1.
-/

public section

open Module LinearMap TauCeti.UnitarilyInvariantSeminorm
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {𝕜 ι E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### The block column and row operators -/

/-- The **block column** of a finite family `a = (aₖ)` of maps `E →ₗ[𝕜] F`: the map
`x ↦ (aₖ x)ₖ` into the Euclidean product of copies of `F`, that is, the block column matrix with
entries `aₖ`. It is linear in the family. -/
noncomputable def blockColumn : (ι → E →ₗ[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] PiLp 2 (fun _ : ι ↦ F) where
  toFun a := (WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ LinearMap.pi a
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

@[simp]
theorem blockColumn_apply (a : ι → E →ₗ[𝕜] F) (x : E) :
    blockColumn a x = WithLp.toLp 2 fun k ↦ a k x :=
  (rfl)

/-- The `k`-th coordinate of the block column of `a` is `aₖ`. -/
@[simp]
theorem projₗ_comp_blockColumn (a : ι → E →ₗ[𝕜] F) (k : ι) :
    PiLp.projₗ 2 (fun _ : ι ↦ F) k ∘ₗ blockColumn a = a k := by
  ext; simp

variable [Fintype ι]

/-- The **block row** of a finite family `a = (aₖ)` of maps `E →ₗ[𝕜] F`: the map
`y ↦ ∑ₖ aₖ yₖ` from the Euclidean product of copies of `E`, that is, the block row matrix with
entries `aₖ`. It is linear in the family. -/
noncomputable def blockRow : (ι → E →ₗ[𝕜] F) →ₗ[𝕜] PiLp 2 (fun _ : ι ↦ E) →ₗ[𝕜] F where
  toFun a := ∑ k, a k ∘ₗ PiLp.projₗ 2 (fun _ : ι ↦ E) k
  map_add' a b := by simp [Finset.sum_add_distrib, add_comp]
  map_smul' c a := by simp [Finset.smul_sum, smul_comp]

@[simp]
theorem blockRow_apply (a : ι → E →ₗ[𝕜] F) (y : PiLp 2 fun _ : ι ↦ E) :
    blockRow a y = ∑ k, a k (y k) := by
  simp [blockRow]

/-- The squared norm of the block column at `x` is `∑ₖ ‖aₖ x‖²`. -/
theorem norm_blockColumn_apply_sq (a : ι → E →ₗ[𝕜] F) (x : E) :
    ‖blockColumn a x‖ ^ 2 = ∑ k, ‖a k x‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The adjoint of the block row of `(aₖ)` is the block column of `(aₖ†)`. -/
theorem adjoint_blockRow (a : ι → E →ₗ[𝕜] F) :
    (blockRow a).adjoint = blockColumn fun k ↦ (a k).adjoint := by
  refine ((eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp [PiLp.inner_apply, inner_sum, adjoint_inner_left]

/-- The adjoint of the block column of `(aₖ)` is the block row of `(aₖ†)`. -/
theorem adjoint_blockColumn (a : ι → E →ₗ[𝕜] F) :
    (blockColumn a).adjoint = blockRow fun k ↦ (a k).adjoint := by
  simpa using (congrArg LinearMap.adjoint (adjoint_blockRow fun k ↦ (a k).adjoint)).symm

/-- The Gram operator of the block column is the column square `∑ₖ aₖ† aₖ`. -/
theorem adjoint_blockColumn_comp_blockColumn (a : ι → E →ₗ[𝕜] F) :
    (blockColumn a).adjoint ∘ₗ blockColumn a = ∑ k, (a k).adjoint ∘ₗ a k := by
  ext x
  simp [adjoint_blockColumn]

/-- The target Gram operator of the block row is the row square `∑ₖ aₖ aₖ†`. -/
theorem blockRow_comp_adjoint_blockRow (a : ι → E →ₗ[𝕜] F) :
    blockRow a ∘ₗ (blockRow a).adjoint = ∑ k, a k ∘ₗ (a k).adjoint := by
  ext x
  simp [adjoint_blockRow]

/-! ### The column and row Schatten norms -/

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **column Schatten `p`-norm** `C_p(a) = ‖(∑ₖ aₖ† aₖ)^(1/2)‖_p` of a finite family of maps
(`TauCeti.columnSchatten_apply_eq_schatten_sqrt`), defined as the Schatten `p`-norm of the block
column `x ↦ (aₖ x)ₖ`. -/
noncomputable def columnSchatten : Seminorm 𝕜 (ι → E →ₗ[𝕜] F) :=
  (schatten 𝕜 E (PiLp 2 fun _ : ι ↦ F) p).toSeminorm.comp blockColumn

/-- The **row Schatten `p`-norm** `R_p(a) = ‖(∑ₖ aₖ aₖ†)^(1/2)‖_p` of a finite family of maps
(`TauCeti.rowSchatten_apply_eq_schatten_sqrt`), defined as the Schatten `p`-norm of the block row
`y ↦ ∑ₖ aₖ yₖ`. -/
noncomputable def rowSchatten : Seminorm 𝕜 (ι → E →ₗ[𝕜] F) :=
  (schatten 𝕜 (PiLp 2 fun _ : ι ↦ E) F p).toSeminorm.comp blockRow

/-- The column norm is the Schatten norm of the block column. -/
theorem columnSchatten_apply (a : ι → E →ₗ[𝕜] F) :
    columnSchatten p a = schatten 𝕜 E (PiLp 2 fun _ : ι ↦ F) p (blockColumn a) :=
  (rfl)

/-- The row norm is the Schatten norm of the block row. -/
theorem rowSchatten_apply (a : ι → E →ₗ[𝕜] F) :
    rowSchatten p a = schatten 𝕜 (PiLp 2 fun _ : ι ↦ E) F p (blockRow a) :=
  (rfl)

/-- The row norm of `(aₖ)` is the column norm of `(aₖ†)`: `R_p(a) = C_p((aₖ†)ₖ)`. -/
theorem rowSchatten_apply_eq_columnSchatten_apply_adjoint (a : ι → E →ₗ[𝕜] F) :
    rowSchatten p a = columnSchatten p fun k ↦ (a k).adjoint := by
  rw [rowSchatten_apply, columnSchatten_apply, ← adjoint_blockRow, schatten_apply_adjoint]

/-- **The column square function formula.** For the positive square root `(∑ₖ aₖ† aₖ)^(1/2)`,
`C_p(a) = ‖(∑ₖ aₖ† aₖ)^(1/2)‖_p`. -/
theorem columnSchatten_apply_eq_schatten_sqrt (a : ι → E →ₗ[𝕜] F)
    (hT : (∑ k, (a k).adjoint ∘ₗ a k).IsPositive) :
    columnSchatten p a = schatten 𝕜 E E p hT.sqrt := by
  rw [hT.sqrt_isPositive.eq_operatorAbs (A := blockColumn a)
      (by rw [hT.sqrt_sq, adjoint_blockColumn_comp_blockColumn]),
    schatten_apply_operatorAbs, columnSchatten_apply p a]

/-- **The row square function formula.** For the positive square root `(∑ₖ aₖ aₖ†)^(1/2)`,
`R_p(a) = ‖(∑ₖ aₖ aₖ†)^(1/2)‖_p`. -/
theorem rowSchatten_apply_eq_schatten_sqrt (a : ι → E →ₗ[𝕜] F)
    (hT : (∑ k, a k ∘ₗ (a k).adjoint).IsPositive) :
    rowSchatten p a = schatten 𝕜 F F p hT.sqrt := by
  rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint,
    columnSchatten_apply_eq_schatten_sqrt p _ (by simpa using hT)]
  simp

/-- The column Schatten norm is a norm: `C_p(a) = 0` only for `a = 0`. -/
@[simp]
theorem columnSchatten_apply_eq_zero_iff {a : ι → E →ₗ[𝕜] F} : columnSchatten p a = 0 ↔ a = 0 := by
  rw [columnSchatten_apply, schatten_apply_eq_zero_iff]
  refine ⟨fun h ↦ funext fun k ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  rw [← projₗ_comp_blockColumn a k, h, comp_zero, Pi.zero_apply]

/-- The row Schatten norm is a norm: `R_p(a) = 0` only for `a = 0`. -/
@[simp]
theorem rowSchatten_apply_eq_zero_iff {a : ι → E →ₗ[𝕜] F} : rowSchatten p a = 0 ↔ a = 0 := by
  rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint, columnSchatten_apply_eq_zero_iff]
  simp [funext_iff]

/-! ### Entries, scalar multipliers and the sum norm -/

/-- Each entry is bounded by the column norm: `‖aₖ‖_p ≤ C_p(a)`. -/
theorem schatten_apply_le_columnSchatten (a : ι → E →ₗ[𝕜] F) (k : ι) :
    schatten 𝕜 E F p (a k) ≤ columnSchatten p a := by
  simpa [columnSchatten_apply] using schatten_comp_le_left p (PiLp.projₗ 2 (fun _ : ι ↦ F) k)
    (blockColumn a) (c := 1) fun y ↦ by simpa using PiLp.norm_apply_le y k

/-- Each entry is bounded by the row norm: `‖aₖ‖_p ≤ R_p(a)`. -/
theorem schatten_apply_le_rowSchatten (a : ι → E →ₗ[𝕜] F) (k : ι) :
    schatten 𝕜 E F p (a k) ≤ rowSchatten p a := by
  rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint p a, ← schatten_apply_adjoint p (a k)]
  exact schatten_apply_le_columnSchatten p (fun k ↦ (a k).adjoint) k

/-- Each entry is bounded by the **sum norm** `inf_{a = b + c} (C_p(b) + R_p(c))`, the norm
`(columnSchatten p ⊓ rowSchatten p) a` of the sum of the column and row spaces
(`Seminorm.inf_apply`). -/
theorem schatten_apply_le_columnSchatten_inf_rowSchatten (a : ι → E →ₗ[𝕜] F) (k : ι) :
    schatten 𝕜 E F p (a k) ≤
      (columnSchatten p ⊓ rowSchatten p : Seminorm 𝕜 (ι → E →ₗ[𝕜] F)) a := by
  have hle : (schatten 𝕜 E F p).toSeminorm.comp
      (LinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ E →ₗ[𝕜] F) k) ≤
      columnSchatten p ⊓ rowSchatten p :=
    le_inf (fun b ↦ schatten_apply_le_columnSchatten p b k)
      fun b ↦ schatten_apply_le_rowSchatten p b k
  exact hle a

/-- The sum norm `inf_{a = b + c} (C_p(b) + R_p(c))` is a norm: it vanishes only at `a = 0`. -/
theorem columnSchatten_inf_rowSchatten_apply_eq_zero_iff {a : ι → E →ₗ[𝕜] F} :
    (columnSchatten p ⊓ rowSchatten p : Seminorm 𝕜 (ι → E →ₗ[𝕜] F)) a = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ funext fun k ↦ (schatten_apply_eq_zero_iff p).1 <| le_antisymm ?_
    (apply_nonneg _ _), fun h ↦ h ▸ map_zero _⟩
  exact h ▸ schatten_apply_le_columnSchatten_inf_rowSchatten p a k

/-- **Contraction principle for the column norm.** If `‖αₖ‖ ≤ c` for every `k`, then
`C_p((αₖ aₖ)ₖ) ≤ c C_p(a)`. With `αₖ ∈ {0, 1}` this says that truncating a family does not
increase its column norm. -/
theorem columnSchatten_smul_le (a : ι → E →ₗ[𝕜] F) {α : ι → 𝕜} {c : ℝ}
    (hα : ∀ k, ‖α k‖ ≤ c) : columnSchatten p (fun k ↦ α k • a k) ≤ c * columnSchatten p a := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · rw [Subsingleton.elim (fun k ↦ α k • a k) 0, Subsingleton.elim a 0]
    simp
  have hc : 0 ≤ c := (norm_nonneg _).trans (hα k₀)
  refine (schatten 𝕜 E _ p).map_le_mul_of_norm_apply_le fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_blockColumn_apply_sq,
    norm_blockColumn_apply_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [LinearMap.smul_apply, norm_smul, mul_pow]
  gcongr
  exact hα k

/-- **Contraction principle for the row norm.** If `‖αₖ‖ ≤ c` for every `k`, then
`R_p((αₖ aₖ)ₖ) ≤ c R_p(a)`. With `αₖ ∈ {0, 1}` this says that truncating a family does not
increase its row norm. -/
theorem rowSchatten_smul_le (a : ι → E →ₗ[𝕜] F) {α : ι → 𝕜} {c : ℝ}
    (hα : ∀ k, ‖α k‖ ≤ c) : rowSchatten p (fun k ↦ α k • a k) ≤ c * rowSchatten p a := by
  simp_rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint, map_smulₛₗ]
  exact columnSchatten_smul_le p _ fun k ↦ by simpa using hα k

/-! ### The endpoints `p = 2` and `p = ∞` -/

/-- At `p = 2` the column norm is `C₂(a) = (∑ₖ ‖aₖ‖₂²)^(1/2)`, with `‖·‖₂` the Frobenius norm. -/
theorem columnSchatten_two_apply (a : ι → E →ₗ[𝕜] F) :
    columnSchatten 2 a = √(∑ k, frobenius 𝕜 E F (a k) ^ 2) := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [columnSchatten_apply, schatten_two, frobenius_apply b]
  simp_rw [norm_blockColumn_apply_sq, sq_frobenius_apply b]
  rw [Finset.sum_comm]

/-- At `p = 2` the row norm is `R₂(a) = (∑ₖ ‖aₖ‖₂²)^(1/2)`, with `‖·‖₂` the Frobenius norm. -/
theorem rowSchatten_two_apply (a : ι → E →ₗ[𝕜] F) :
    rowSchatten 2 a = √(∑ k, frobenius 𝕜 E F (a k) ^ 2) := by
  rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint, columnSchatten_two_apply]
  simp_rw [← schatten_two, schatten_apply_adjoint]

/-- At `p = 2` the row and column norms coincide: `R₂ = C₂`. -/
theorem rowSchatten_two : (rowSchatten 2 : Seminorm 𝕜 (ι → E →ₗ[𝕜] F)) = columnSchatten 2 := by
  ext a
  rw [rowSchatten_two_apply, columnSchatten_two_apply]

/-- At `p = ∞` the column norm is `C_∞(a) = ‖∑ₖ aₖ† aₖ‖^(1/2)`, with `‖·‖` the operator norm. -/
theorem columnSchatten_top_apply (a : ι → E →ₗ[𝕜] F) :
    columnSchatten ∞ a = √(opNorm 𝕜 E E (∑ k, (a k).adjoint ∘ₗ a k)) := by
  rw [← adjoint_blockColumn_comp_blockColumn, opNorm_apply_adjoint_comp_self,
    Real.sqrt_sq (apply_nonneg _ _), columnSchatten_apply, schatten_top]

/-- At `p = ∞` the row norm is `R_∞(a) = ‖∑ₖ aₖ aₖ†‖^(1/2)`, with `‖·‖` the operator norm. -/
theorem rowSchatten_top_apply (a : ι → E →ₗ[𝕜] F) :
    rowSchatten ∞ a = √(opNorm 𝕜 F F (∑ k, a k ∘ₗ (a k).adjoint)) := by
  rw [rowSchatten_apply_eq_columnSchatten_apply_adjoint, columnSchatten_top_apply]
  simp

end TauCeti
