/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.InnerProductSpace.Positive.Definite

/-!
# The operator norm of the Lie bracket

Let `L` be a real Lie algebra with a bilinear form `B`, which for the applications is an inner
product `⟨X, Y⟩ = B X Y`, so `|X| = √(B X X)`. The **operator norm of the bracket**

`γ₀(L, B) = sup { |⁅X, Y⁆| : |X| ≤ 1, |Y| ≤ 1 }`

is the best constant in `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`. In gauge theory, with `L` the Lie algebra of a
compact structure group and `B` an `Ad`-invariant inner product, it is the structure constant `γ₀`
that controls the quadratic and cubic curvature terms: it enters the cubic bound on self-dual
two-forms in the Weitzenböck formula, and through it the energy gap `16π²/γ₀²` for nontrivial
Yang–Mills connections on `ℝ⁴`.

The supremum runs over the closed unit balls, so it is `0` for the zero Lie algebra and for every
abelian one. For a positive-definite form on a finite-dimensional Lie algebra the unit balls are
compact and the supremum is a maximum (`LinearMap.BilinForm.exists_lieBracketOpNorm_eq`);
`γ₀` is then the least nonnegative constant with `|⁅X, Y⁆| ≤ γ₀ |X| |Y|` for all `X`, `Y`
(`LinearMap.BilinForm.isLeast_lieBracketOpNorm`), and it vanishes exactly when the bracket does
(`LinearMap.BilinForm.lieBracketOpNorm_eq_zero_iff`). Scaling the form by `c > 0` scales it by
`c^{-1/2}` (`LinearMap.BilinForm.lieBracketOpNorm_smul`). Only the values `B X X` enter, so the
form need not be symmetric.

The form is a parameter rather than an inner product space instance on `L`, since the same Lie
algebra is considered with several forms (rescaled ones, or restrictions to ideals) and the Lie
algebras in question, such as Lie subalgebras of matrices, already carry their own topology.

## Main definitions

* `LinearMap.BilinForm.lieBracketOpNorm`: the operator norm `γ₀` of the bracket for the norm
  `√(B X X)`.

## Main results

* `LinearMap.BilinForm.exists_lieBracketOpNorm_eq`: the supremum over the unit balls is attained.
* `LinearMap.BilinForm.sqrt_apply_self_lie_le`: `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`.
* `LinearMap.BilinForm.isLeast_lieBracketOpNorm`: `γ₀` is the least such nonnegative constant.
* `LinearMap.BilinForm.lieBracketOpNorm_smul`: `γ₀(L, c B) = (√c)⁻¹ γ₀(L, B)` for `c ≥ 0`.
* `LinearMap.BilinForm.lieBracketOpNorm_eq_zero_iff`: `γ₀ = 0` exactly when `L` is abelian.

## References

* K. Gursky, C. L. Kelleher and J. Streets, *A conformally invariant gap theorem in Yang–Mills
  theory*, Comm. Math. Phys. 361 (2018), arXiv:1708.01157, Definition 2.3.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 6.
-/

public section

noncomputable section

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L)

/-- The **operator norm of the Lie bracket** `γ₀(L, B)` for the norm `|X| = √(B X X)`: the
supremum of `|⁅X, Y⁆|` over `|X| ≤ 1` and `|Y| ≤ 1`. For a positive-definite form on a
finite-dimensional Lie algebra it is attained (`LinearMap.BilinForm.exists_lieBracketOpNorm_eq`)
and is the best constant in `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`
(`LinearMap.BilinForm.isLeast_lieBracketOpNorm`). -/
def lieBracketOpNorm : ℝ :=
  sSup ((fun p : L × L ↦ √(B ⁅p.1, p.2⁆ ⁅p.1, p.2⁆)) '' {p | B p.1 p.1 ≤ 1 ∧ B p.2 p.2 ≤ 1})

/-- `γ₀` is the supremum of `√(B ⁅X, Y⁆ ⁅X, Y⁆)` over `B X X ≤ 1` and `B Y Y ≤ 1`. -/
theorem lieBracketOpNorm_def :
    B.lieBracketOpNorm =
      sSup ((fun p : L × L ↦ √(B ⁅p.1, p.2⁆ ⁅p.1, p.2⁆)) '' {p | B p.1 p.1 ≤ 1 ∧ B p.2 p.2 ≤ 1}) :=
  (rfl)

/-- `γ₀` is nonnegative, whatever the form. -/
theorem lieBracketOpNorm_nonneg : 0 ≤ B.lieBracketOpNorm :=
  Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact Real.sqrt_nonneg _)

/-- An upper bound for `|⁅X, Y⁆|` on the unit balls bounds `γ₀`. -/
theorem lieBracketOpNorm_le {C : ℝ}
    (h : ∀ X Y, B X X ≤ 1 → B Y Y ≤ 1 → √(B ⁅X, Y⁆ ⁅X, Y⁆) ≤ C) : B.lieBracketOpNorm ≤ C :=
  csSup_le ⟨_, (0, 0), by simp, rfl⟩ (by rintro _ ⟨p, hp, rfl⟩; exact h p.1 p.2 hp.1 hp.2)

/-- The operator norm of the bracket of an abelian Lie algebra vanishes. -/
@[simp]
theorem lieBracketOpNorm_of_isLieAbelian [IsLieAbelian L] : B.lieBracketOpNorm = 0 :=
  le_antisymm (B.lieBracketOpNorm_le fun _ _ _ _ ↦ by rw [trivial_lie_zero]; simp)
    B.lieBracketOpNorm_nonneg

/-- The norm `√(B X X)` is absolutely homogeneous. -/
private theorem sqrt_apply_smul_smul (c : ℝ) (X : L) : √(B (c • X) (c • X)) = |c| * √(B X X) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- **Scaling the form**: for `c ≥ 0`, `γ₀(L, c B) = (√c)⁻¹ γ₀(L, B)`. For `c = 0` both sides
vanish. -/
theorem lieBracketOpNorm_smul {c : ℝ} (hc : 0 ≤ c) :
    (c • B).lieBracketOpNorm = (√c)⁻¹ * B.lieBracketOpNorm := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [Real.sqrt_zero, inv_zero, zero_mul]
    exact le_antisymm ((0 • B).lieBracketOpNorm_le fun _ _ _ _ ↦ by simp)
      (0 • B).lieBracketOpNorm_nonneg
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  have hss : √c * √c = c := Real.mul_self_sqrt hc.le
  -- `X ↦ √c • X` maps the unit ball of `c B` onto that of `B`, and multiplies `|⁅X, Y⁆|` by `√c`
  -- for `c B` and by `c` for `B`.
  have hball (X : L) : (c • B) X X ≤ 1 ↔ B (√c • X) (√c • X) ≤ 1 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, hss]
  have hval (X Y : L) :
      √((c • B) ⁅X, Y⁆ ⁅X, Y⁆) = (√c)⁻¹ * √(B ⁅√c • X, √c • Y⁆ ⁅√c • X, √c • Y⁆) := by
    rw [smul_lie, lie_smul, smul_smul, sqrt_apply_smul_smul, abs_of_pos (mul_pos hs hs),
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, Real.sqrt_mul hc.le]
  rw [lieBracketOpNorm_def, lieBracketOpNorm_def, ← smul_eq_mul,
    ← Real.sSup_smul_of_nonneg (inv_nonneg.2 hs.le)]
  congr 1
  ext t
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_smul_set, Prod.exists, smul_eq_mul]
  constructor
  · rintro ⟨X, Y, ⟨hX, hY⟩, rfl⟩
    exact ⟨_, ⟨√c • X, √c • Y, ⟨(hball X).1 hX, (hball Y).1 hY⟩, rfl⟩, (hval X Y).symm⟩
  · rintro ⟨_, ⟨X, Y, ⟨hX, hY⟩, rfl⟩, rfl⟩
    refine ⟨(√c)⁻¹ • X, (√c)⁻¹ • Y, ⟨?_, ?_⟩, ?_⟩
    · rwa [hball, smul_inv_smul₀ hs.ne']
    · rwa [hball, smul_inv_smul₀ hs.ne']
    · rw [hval, smul_inv_smul₀ hs.ne', smul_inv_smul₀ hs.ne']

section FiniteDimensional

variable [FiniteDimensional ℝ L] {B} (hpos : B.toQuadraticMap.PosDef)
include hpos

/-- On a finite-dimensional Lie algebra with a positive-definite form, `|⁅X, Y⁆|` attains its
supremum over the unit balls. -/
private theorem exists_isGreatest :
    ∃ X Y, B X X ≤ 1 ∧ B Y Y ≤ 1 ∧
      IsGreatest ((fun p : L × L ↦ √(B ⁅p.1, p.2⁆ ⁅p.1, p.2⁆)) ''
        {p | B p.1 p.1 ≤ 1 ∧ B p.2 p.2 ≤ 1}) (√(B ⁅X, Y⁆ ⁅X, Y⁆)) := by
  -- Only the diagonal of `B` enters, so `B` may be replaced by its symmetric part `S`. Identify
  -- `S` with the inner product of a Euclidean space, whose unit ball is compact, and maximise the
  -- norm of the transported bracket over the product of two unit balls.
  let S : LinearMap.BilinForm ℝ L := (2⁻¹ : ℝ) • (B + B.flip)
  have hS (Z : L) : S Z Z = B Z Z := by
    simp only [S, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.BilinForm.flip_apply,
      smul_eq_mul]
    ring
  obtain ⟨φ, hφ⟩ := TauCeti.exists_linearEquiv_inner_eq_of_posDef
    (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ L))) (B := S) (by simp)
    (fun Z hZ ↦ by rw [LinearMap.BilinMap.toQuadraticMap_apply, hS]; exact hpos Z hZ)
    ⟨fun X Y ↦ by simp only [S, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.BilinForm.flip_apply, add_comm]⟩
  have hsq (X : L) : B X X = ‖φ X‖ ^ 2 := by rw [← hS, ← hφ, real_inner_self_eq_norm_sq]
  have hball (X : L) : B X X ≤ 1 ↔ ‖φ X‖ ≤ 1 := by rw [hsq, sq_le_one_iff₀ (norm_nonneg _)]
  let M : EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u v ↦ φ ⁅φ.symm u, φ.symm v⁆) (by simp [add_lie]) (by simp [smul_lie])
        (by simp [lie_add]) (by simp [lie_smul])
  have hM (X Y : L) : √(B ⁅X, Y⁆ ⁅X, Y⁆) = ‖M (φ X) (φ Y)‖ := by
    simp [M, hsq]
  have hcont : Continuous fun q : _ × _ ↦ ‖M q.1 q.2‖ :=
    (((LinearMap.continuous_of_finiteDimensional M).comp continuous_fst).clm_apply
      continuous_snd).norm
  obtain ⟨q, hq, hmax⟩ := ((isCompact_closedBall 0 1).prod
    (isCompact_closedBall 0 1)).exists_isMaxOn ⟨(0, 0), by simp⟩ hcont.continuousOn
  simp only [Set.mem_prod, mem_closedBall_zero_iff] at hq
  refine ⟨φ.symm q.1, φ.symm q.2, by simpa [hball] using hq.1, by simpa [hball] using hq.2,
    ⟨(φ.symm q.1, φ.symm q.2), ⟨by simpa [hball] using hq.1, by simpa [hball] using hq.2⟩, rfl⟩,
    ?_⟩
  rintro _ ⟨p, ⟨hp₁, hp₂⟩, rfl⟩
  have h := isMaxOn_iff.1 hmax (φ p.1, φ p.2)
    ⟨by simpa [hball] using hp₁, by simpa [hball] using hp₂⟩
  simpa only [hM, LinearEquiv.apply_symm_apply] using h

/-- **The supremum defining `γ₀` is a maximum**: some `X`, `Y` in the unit balls have
`|⁅X, Y⁆| = γ₀`. -/
theorem exists_lieBracketOpNorm_eq :
    ∃ X Y, B X X ≤ 1 ∧ B Y Y ≤ 1 ∧ √(B ⁅X, Y⁆ ⁅X, Y⁆) = B.lieBracketOpNorm := by
  obtain ⟨X, Y, hX, hY, h⟩ := exists_isGreatest hpos
  exact ⟨X, Y, hX, hY, h.csSup_eq.symm⟩

/-- On the unit balls, `|⁅X, Y⁆| ≤ γ₀`. -/
theorem sqrt_apply_self_lie_le_of_le_one {X Y : L} (hX : B X X ≤ 1) (hY : B Y Y ≤ 1) :
    √(B ⁅X, Y⁆ ⁅X, Y⁆) ≤ B.lieBracketOpNorm := by
  obtain ⟨_, _, _, _, h⟩ := exists_isGreatest hpos
  exact le_csSup h.bddAbove ⟨(X, Y), ⟨hX, hY⟩, rfl⟩

/-- **The bracket bound** `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`. -/
theorem sqrt_apply_self_lie_le (X Y : L) :
    √(B ⁅X, Y⁆ ⁅X, Y⁆) ≤ B.lieBracketOpNorm * √(B X X) * √(B Y Y) := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  rcases eq_or_ne Y 0 with rfl | hY
  · simp
  -- Rescale `X` and `Y` to unit length.
  have hpos' {Z : L} (hZ : Z ≠ 0) : 0 < √(B Z Z) := Real.sqrt_pos.2 (hpos Z hZ)
  have hunit {Z : L} (hZ : Z ≠ 0) : B ((√(B Z Z))⁻¹ • Z) ((√(B Z Z))⁻¹ • Z) ≤ 1 := by
    rw [← Real.sqrt_le_one, sqrt_apply_smul_smul, abs_inv, abs_of_pos (hpos' hZ),
      inv_mul_cancel₀ (hpos' hZ).ne']
  have h := sqrt_apply_self_lie_le_of_le_one hpos (hunit hX) (hunit hY)
  rw [smul_lie, lie_smul, smul_smul, sqrt_apply_smul_smul, abs_of_pos
    (mul_pos (inv_pos.2 (hpos' hX)) (inv_pos.2 (hpos' hY)))] at h
  rwa [mul_assoc, ← div_le_iff₀ (mul_pos (hpos' hX) (hpos' hY)), div_eq_inv_mul, mul_inv]

/-- The squared bracket bound `|⁅X, Y⁆|² ≤ γ₀² |X|² |Y|²`. -/
theorem apply_self_lie_le (X Y : L) :
    B ⁅X, Y⁆ ⁅X, Y⁆ ≤ B.lieBracketOpNorm ^ 2 * B X X * B Y Y := by
  have hnonneg (Z : L) : 0 ≤ B Z Z := hpos.nonneg Z
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_apply_self_lie_le hpos X Y) 2
  rwa [mul_pow, mul_pow, Real.sq_sqrt (hnonneg _), Real.sq_sqrt (hnonneg _),
    Real.sq_sqrt (hnonneg _)] at h

/-- **`γ₀` is the best constant**: the least `C ≥ 0` with `|⁅X, Y⁆| ≤ C |X| |Y|` for all `X` and
`Y`. -/
theorem isLeast_lieBracketOpNorm :
    IsLeast {C | 0 ≤ C ∧ ∀ X Y, √(B ⁅X, Y⁆ ⁅X, Y⁆) ≤ C * √(B X X) * √(B Y Y)}
      B.lieBracketOpNorm := by
  refine ⟨⟨B.lieBracketOpNorm_nonneg, sqrt_apply_self_lie_le hpos⟩, fun C ⟨hC, h⟩ ↦
    B.lieBracketOpNorm_le fun X Y hX hY ↦ (h X Y).trans ?_⟩
  have hX' := Real.sqrt_le_one.2 hX
  have hY' := Real.sqrt_le_one.2 hY
  calc C * √(B X X) * √(B Y Y) ≤ C * 1 * 1 := by gcongr
    _ = C := by ring

/-- **`γ₀` vanishes exactly when the bracket does.** -/
theorem lieBracketOpNorm_eq_zero_iff : B.lieBracketOpNorm = 0 ↔ IsLieAbelian L := by
  refine ⟨fun h ↦ ⟨fun X Y ↦ hpos.anisotropic _ (le_antisymm ?_ (hpos.nonneg _))⟩,
    fun _ ↦ B.lieBracketOpNorm_of_isLieAbelian⟩
  simpa [h] using apply_self_lie_le hpos X Y

/-- `γ₀` is positive exactly when the bracket is nonzero. -/
theorem lieBracketOpNorm_pos_iff : 0 < B.lieBracketOpNorm ↔ ¬IsLieAbelian L := by
  rw [B.lieBracketOpNorm_nonneg.lt_iff_ne', ne_eq, lieBracketOpNorm_eq_zero_iff hpos]

end FiniteDimensional

end LinearMap.BilinForm
