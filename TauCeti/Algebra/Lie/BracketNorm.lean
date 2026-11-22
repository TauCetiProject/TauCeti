/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# The norm of the Lie bracket

Let `L` be a finite-dimensional real Lie algebra with a positive definite quadratic form `Q`, the
squared norm `|X|² = Q X` of an inner product on `L`. The bracket is a bilinear map `L × L → L`,
and its norm

`γ₀(L, Q) = max {|⁅X, Y⁆| : |X| ≤ 1, |Y| ≤ 1}`

(`QuadraticMap.lieBracketNorm`) is the best constant in `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`. For the Lie
algebra `𝔤` of a compact structure group with an `Ad`-invariant inner product it is the
structure constant of Yang–Mills theory: it governs the cubic curvature terms of the
Weitzenböck formulas, and the energy gap and ground state energy of harmonic Yang–Mills
connections on `ℝ⁴` are stated in terms of it.

The maximum is attained, and `γ₀` is the least `C ≥ 0` with `|⁅X, Y⁆| ≤ C |X| |Y|`; for
`L ≠ 0` it is the supremum of `|⁅X, Y⁆| / (|X| |Y|)` over nonzero `X`, `Y`. It scales as
`γ₀(L, c Q) = c^{-1/2} γ₀(L, Q)` for `c > 0`, vanishes exactly when `L` is abelian, is invariant
under Lie algebra isomorphisms, does not increase along Lie algebra homomorphisms into `L`, and
for the orthogonal sum `Q₁ ⊕ Q₂` on a product `L₁ × L₂` it is the larger of the two constants.

## Main definitions

* `QuadraticMap.lieBracketNorm`: the norm `γ₀(L, Q)` of the Lie bracket.

## Main results

* `QuadraticMap.exists_sqrt_apply_lie_eq_lieBracketNorm`: the maximum is attained.
* `QuadraticMap.sqrt_apply_lie_le`: `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`, and
  `QuadraticMap.isLeast_lieBracketNorm`: `γ₀` is the least such constant.
* `QuadraticMap.lieBracketNorm_eq_sSup_div`: `γ₀` is the supremum of the ratios
  `|⁅X, Y⁆| / (|X| |Y|)` over nonzero pairs.
* `QuadraticMap.lieBracketNorm_smul`: `γ₀(L, c Q) = c^{-1/2} γ₀(L, Q)`.
* `QuadraticMap.lieBracketNorm_eq_zero_iff`: `γ₀ = 0` exactly when `L` is abelian.
* `QuadraticMap.lieBracketNorm_comp_lieEquiv` and `QuadraticMap.lieBracketNorm_comp_le`:
  invariance under Lie algebra isomorphisms and monotonicity along Lie algebra homomorphisms.
* `QuadraticMap.lieBracketNorm_prod`: `γ₀(L₁ × L₂, Q₁ ⊕ Q₂) = max (γ₀(L₁, Q₁)) (γ₀(L₂, Q₂))`.

## References

* S. Gursky, C. Kelleher and J. Streets, *A conformally invariant gap theorem in Yang–Mills
  theory*, Comm. Math. Phys. 361 (2018), arXiv:1708.01157, Definition 2.3.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 6.
-/

public section

noncomputable section

open Module Metric Set

namespace QuadraticMap

variable {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']
  (Q : QuadraticForm ℝ L)

/-- The **norm of the Lie bracket** `γ₀(L, Q)` for a quadratic form `Q` on a real Lie algebra
`L`, read as the squared norm `|X|² = Q X`: the supremum of `|⁅X, Y⁆|` over `|X| ≤ 1` and
`|Y| ≤ 1`. For `Q` positive definite and `L` finite-dimensional this supremum is attained
(`QuadraticMap.exists_sqrt_apply_lie_eq_lieBracketNorm`), and it is the least constant in
`|⁅X, Y⁆| ≤ γ₀ |X| |Y|` (`QuadraticMap.isLeast_lieBracketNorm`). -/
def lieBracketNorm : ℝ :=
  sSup ((fun p : L × L ↦ √(Q ⁅p.1, p.2⁆)) '' {p | Q p.1 ≤ 1 ∧ Q p.2 ≤ 1})

/-- The norm of the Lie bracket is the supremum of `|⁅X, Y⁆|` over `|X| ≤ 1` and `|Y| ≤ 1`. -/
theorem lieBracketNorm_def :
    Q.lieBracketNorm = sSup ((fun p : L × L ↦ √(Q ⁅p.1, p.2⁆)) '' {p | Q p.1 ≤ 1 ∧ Q p.2 ≤ 1}) :=
  (rfl)

variable {Q}

/-- The norm of the Lie bracket is nonnegative. -/
theorem lieBracketNorm_nonneg (Q : QuadraticForm ℝ L) : 0 ≤ Q.lieBracketNorm :=
  Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact Real.sqrt_nonneg _)

/-- Any `C ≥ 0` with `|⁅X, Y⁆| ≤ C |X| |Y|` for all `X`, `Y` bounds the norm of the Lie
bracket. -/
theorem lieBracketNorm_le_of_forall_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X Y, √(Q ⁅X, Y⁆) ≤ C * √(Q X) * √(Q Y)) : Q.lieBracketNorm ≤ C := by
  refine csSup_le ⟨_, (0, 0), by simp, rfl⟩ ?_
  rintro _ ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
  calc √(Q ⁅X, Y⁆) ≤ C * √(Q X) * √(Q Y) := h X Y
    _ ≤ C * 1 * 1 := by gcongr <;> exact Real.sqrt_le_one.mpr ‹_›
    _ = C := by ring

/-- The squared form of `QuadraticMap.lieBracketNorm_le_of_forall_le`: for `Q` nonnegative, any
`C ≥ 0` with `Q ⁅X, Y⁆ ≤ C² Q X Q Y` for all `X`, `Y` bounds the norm of the Lie bracket. -/
theorem lieBracketNorm_le_of_forall_apply_le (hQ : ∀ X, 0 ≤ Q X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X Y, Q ⁅X, Y⁆ ≤ C ^ 2 * Q X * Q Y) : Q.lieBracketNorm ≤ C := by
  refine lieBracketNorm_le_of_forall_le hC fun X Y ↦ ?_
  calc √(Q ⁅X, Y⁆) ≤ √(C ^ 2 * Q X * Q Y) := Real.sqrt_le_sqrt (h X Y)
    _ = C * √(Q X) * √(Q Y) := by
      rw [Real.sqrt_mul (by have := hQ X; positivity), Real.sqrt_mul (sq_nonneg C),
        Real.sqrt_sq hC]

/-- On an abelian Lie algebra the norm of the Lie bracket vanishes. -/
@[simp]
theorem lieBracketNorm_of_isLieAbelian [IsLieAbelian L] (Q : QuadraticForm ℝ L) :
    Q.lieBracketNorm = 0 :=
  le_antisymm (lieBracketNorm_le_of_forall_le le_rfl fun X Y ↦ by simp [trivial_lie_zero])
    (lieBracketNorm_nonneg Q)

/-- The norm of the Lie bracket is invariant under Lie algebra isomorphisms. -/
@[simp]
theorem lieBracketNorm_comp_lieEquiv (e : L' ≃ₗ⁅ℝ⁆ L) :
    (Q.comp (e : L' →ₗ[ℝ] L)).lieBracketNorm = Q.lieBracketNorm := by
  rw [lieBracketNorm_def, lieBracketNorm_def]
  congr 1
  ext r
  constructor
  · rintro ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
    exact ⟨(e X, e Y), ⟨hX, hY⟩, by simp [LieEquiv.map_lie]⟩
  · rintro ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
    exact ⟨(e.symm X, e.symm Y), ⟨by simpa using hX, by simpa using hY⟩,
      by simp [LieEquiv.map_lie]⟩

variable [FiniteDimensional ℝ L]

/-- On a finite-dimensional real Lie algebra with a positive definite quadratic form, the set of
values `|⁅X, Y⁆|` over `|X| ≤ 1`, `|Y| ≤ 1` has a greatest element. -/
private theorem exists_isGreatest (hQ : Q.PosDef) :
    ∃ X Y, Q X ≤ 1 ∧ Q Y ≤ 1 ∧
      IsGreatest ((fun p : L × L ↦ √(Q ⁅p.1, p.2⁆)) '' {p | Q p.1 ≤ 1 ∧ Q p.2 ≤ 1})
        √(Q ⁅X, Y⁆) := by
  -- Transport the problem to Euclidean space, where the closed unit ball is compact.
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply
    (g := associated (R := ℝ) Q) ⟨associated_isSymm ℝ Q⟩ fun v hv ↦ by
      simpa [associated_eq_self_apply] using hQ v hv
  have hQe (x) : Q (e x) = ‖x‖ ^ 2 := by
    rw [← associated_eq_self_apply ℝ Q, he, real_inner_self_eq_norm_sq]
  -- The bracket transported to Euclidean space, a continuous bilinear map.
  let β : EuclideanSpace ℝ (Fin (finrank ℝ L)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ L)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ L)) :=
    LinearMap.mk₂ ℝ (fun x y ↦ e.symm ⁅e x, e y⁆) (by simp [add_lie]) (by simp [smul_lie])
      (by simp [lie_add]) (by simp [lie_smul])
  let M := (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ β).toContinuousLinearMap
  have hM : Continuous fun p : EuclideanSpace ℝ (Fin (finrank ℝ L)) ×
      EuclideanSpace ℝ (Fin (finrank ℝ L)) ↦ M p.1 p.2 :=
    (M.continuous.comp continuous_fst).clm_apply continuous_snd
  have hf (x y) : √(Q ⁅e x, e y⁆) = ‖M x y‖ := by
    rw [show ⁅e x, e y⁆ = e (M x y) by simp [M, β], hQe, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ _) 1).prod
    (isCompact_closedBall 0 1) |>.exists_isMaxOn ⟨(0, 0), by simp⟩
    (continuous_norm.comp hM).continuousOn
  simp only [mem_prod, mem_closedBall_zero_iff] at hxy
  have hx : Q (e x) ≤ 1 := by rw [hQe]; exact pow_le_one₀ (norm_nonneg _) hxy.1
  have hy : Q (e y) ≤ 1 := by rw [hQe]; exact pow_le_one₀ (norm_nonneg _) hxy.2
  refine ⟨e x, e y, hx, hy, ⟨⟨(e x, e y), ⟨hx, hy⟩, rfl⟩, ?_⟩⟩
  rintro _ ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
  obtain ⟨x', rfl⟩ := e.surjective X
  obtain ⟨y', rfl⟩ := e.surjective Y
  rw [hQe] at hX hY
  have hmem : (x', y') ∈ closedBall (0 : EuclideanSpace ℝ _) 1 ×ˢ closedBall 0 1 :=
    ⟨mem_closedBall_zero_iff.mpr ((sq_le_one_iff₀ (norm_nonneg _)).mp hX),
      mem_closedBall_zero_iff.mpr ((sq_le_one_iff₀ (norm_nonneg _)).mp hY)⟩
  have h := isMaxOn_iff.mp hmax _ hmem
  simp only [Function.comp_apply] at h
  dsimp only
  rw [hf, hf]
  exact h

/-- **The norm of the Lie bracket is attained**: for `Q` positive definite on a
finite-dimensional real Lie algebra there are `X`, `Y` with `|X| ≤ 1`, `|Y| ≤ 1` and
`|⁅X, Y⁆| = γ₀`. -/
theorem exists_sqrt_apply_lie_eq_lieBracketNorm (hQ : Q.PosDef) :
    ∃ X Y, Q X ≤ 1 ∧ Q Y ≤ 1 ∧ √(Q ⁅X, Y⁆) = Q.lieBracketNorm := by
  obtain ⟨X, Y, hX, hY, h⟩ := exists_isGreatest hQ
  exact ⟨X, Y, hX, hY, h.csSup_eq.symm⟩

/-- For `|X| ≤ 1` and `|Y| ≤ 1`, `|⁅X, Y⁆| ≤ γ₀`. -/
theorem sqrt_apply_lie_le_lieBracketNorm (hQ : Q.PosDef) {X Y : L} (hX : Q X ≤ 1)
    (hY : Q Y ≤ 1) : √(Q ⁅X, Y⁆) ≤ Q.lieBracketNorm := by
  obtain ⟨_, _, _, _, h⟩ := exists_isGreatest hQ
  exact (h.2 ⟨(X, Y), ⟨hX, hY⟩, rfl⟩).trans_eq h.csSup_eq.symm

/-- **The bracket bound** `|⁅X, Y⁆| ≤ γ₀ |X| |Y|`. -/
theorem sqrt_apply_lie_le (hQ : Q.PosDef) (X Y : L) :
    √(Q ⁅X, Y⁆) ≤ Q.lieBracketNorm * √(Q X) * √(Q Y) := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  rcases eq_or_ne Y 0 with rfl | hY
  · simp
  have ha : 0 < √(Q X) := Real.sqrt_pos.mpr (hQ X hX)
  have hb : 0 < √(Q Y) := Real.sqrt_pos.mpr (hQ Y hY)
  -- Normalize `X` and `Y` to unit length.
  have hunit {Z : L} (hZ : Z ≠ 0) : Q ((√(Q Z))⁻¹ • Z) = 1 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, ← mul_inv, Real.mul_self_sqrt (hQ.nonneg Z),
      inv_mul_cancel₀ (hQ Z hZ).ne']
  have h := sqrt_apply_lie_le_lieBracketNorm hQ (hunit hX).le (hunit hY).le
  rw [smul_lie, lie_smul, smul_smul, QuadraticMap.map_smul, smul_eq_mul,
    Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (by positivity), ← mul_inv,
    inv_mul_le_iff₀ (by positivity)] at h
  linarith

/-- The squared form of the bracket bound, `|⁅X, Y⁆|² ≤ γ₀² |X|² |Y|²`. -/
theorem apply_lie_le (hQ : Q.PosDef) (X Y : L) :
    Q ⁅X, Y⁆ ≤ Q.lieBracketNorm ^ 2 * Q X * Q Y := by
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_apply_lie_le hQ X Y) 2
  rwa [mul_pow, mul_pow, Real.sq_sqrt (hQ.nonneg _), Real.sq_sqrt (hQ.nonneg _),
    Real.sq_sqrt (hQ.nonneg _)] at h

/-- **The norm of the Lie bracket is the best constant**: it is the least `C ≥ 0` with
`|⁅X, Y⁆| ≤ C |X| |Y|` for all `X`, `Y`. -/
theorem isLeast_lieBracketNorm (hQ : Q.PosDef) :
    IsLeast {C | 0 ≤ C ∧ ∀ X Y, √(Q ⁅X, Y⁆) ≤ C * √(Q X) * √(Q Y)} Q.lieBracketNorm :=
  ⟨⟨lieBracketNorm_nonneg Q, sqrt_apply_lie_le hQ⟩,
    fun _ hC ↦ lieBracketNorm_le_of_forall_le hC.1 hC.2⟩

/-- On a nonzero Lie algebra the norm of the Lie bracket is the supremum of the ratios
`|⁅X, Y⁆| / (|X| |Y|)` over nonzero `X` and `Y`. -/
theorem lieBracketNorm_eq_sSup_div [Nontrivial L] (hQ : Q.PosDef) :
    Q.lieBracketNorm = sSup ((fun p : L × L ↦ √(Q ⁅p.1, p.2⁆) / (√(Q p.1) * √(Q p.2))) ''
      {p | p.1 ≠ 0 ∧ p.2 ≠ 0}) := by
  set S := (fun p : L × L ↦ √(Q ⁅p.1, p.2⁆) / (√(Q p.1) * √(Q p.2))) ''
    {p | p.1 ≠ 0 ∧ p.2 ≠ 0}
  have hpos {Z : L} (hZ : Z ≠ 0) : 0 < √(Q Z) := Real.sqrt_pos.mpr (hQ Z hZ)
  obtain ⟨Z, hZ⟩ := exists_ne (0 : L)
  have hne : S.Nonempty := ⟨_, (Z, Z), ⟨hZ, hZ⟩, rfl⟩
  have hle : ∀ r ∈ S, r ≤ Q.lieBracketNorm := by
    rintro _ ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
    rw [div_le_iff₀ (mul_pos (hpos hX) (hpos hY)), ← mul_assoc]
    exact sqrt_apply_lie_le hQ X Y
  refine le_antisymm ?_ (csSup_le hne hle)
  obtain ⟨X, Y, hX, hY, h⟩ := exists_sqrt_apply_lie_eq_lieBracketNorm hQ
  rcases eq_or_ne ⁅X, Y⁆ 0 with h0 | h0
  · rw [← h, h0, map_zero, Real.sqrt_zero]
    obtain ⟨r, hr⟩ := hne
    refine le_csSup_of_le ⟨_, hle⟩ hr ?_
    obtain ⟨p, -, rfl⟩ := hr
    positivity
  · have hX0 : X ≠ 0 := by rintro rfl; simp at h0
    have hY0 : Y ≠ 0 := by rintro rfl; simp at h0
    refine le_csSup_of_le ⟨_, hle⟩ ⟨(X, Y), ⟨hX0, hY0⟩, rfl⟩ ?_
    rw [← h]
    refine le_div_self (Real.sqrt_nonneg _) (mul_pos (hpos hX0) (hpos hY0)) ?_
    exact (mul_le_mul (Real.sqrt_le_one.mpr hX) (Real.sqrt_le_one.mpr hY) (Real.sqrt_nonneg _)
      zero_le_one).trans_eq (one_mul 1)

/-- **The norm of the Lie bracket vanishes exactly on abelian Lie algebras.** -/
theorem lieBracketNorm_eq_zero_iff (hQ : Q.PosDef) : Q.lieBracketNorm = 0 ↔ IsLieAbelian L := by
  refine ⟨fun h ↦ ⟨fun X Y ↦ hQ.anisotropic _ ?_⟩, fun _ ↦ lieBracketNorm_of_isLieAbelian Q⟩
  have := apply_lie_le hQ X Y
  rw [h] at this
  exact le_antisymm (by simpa using this) (hQ.nonneg _)

/-- The norm of the Lie bracket is positive exactly on non-abelian Lie algebras. -/
theorem lieBracketNorm_pos_iff (hQ : Q.PosDef) : 0 < Q.lieBracketNorm ↔ ¬IsLieAbelian L := by
  rw [← lieBracketNorm_eq_zero_iff hQ, (lieBracketNorm_nonneg Q).lt_iff_ne', ne_eq]

private theorem lieBracketNorm_smul_le (hQ : Q.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • Q).lieBracketNorm ≤ (√c)⁻¹ * Q.lieBracketNorm := by
  have : 0 < √c := Real.sqrt_pos.mpr hc
  refine lieBracketNorm_le_of_forall_le (by have := lieBracketNorm_nonneg Q; positivity)
    fun X Y ↦ ?_
  simp only [smul_apply, smul_eq_mul, Real.sqrt_mul hc.le]
  have := sqrt_apply_lie_le hQ X Y
  calc √c * √(Q ⁅X, Y⁆) ≤ √c * (Q.lieBracketNorm * √(Q X) * √(Q Y)) := by gcongr
    _ = (√c)⁻¹ * Q.lieBracketNorm * (√c * √(Q X)) * (√c * √(Q Y)) := by
      field_simp

/-- **Scaling of the norm of the Lie bracket**: `γ₀(L, c Q) = c^{-1/2} γ₀(L, Q)` for `c > 0`. -/
theorem lieBracketNorm_smul (hQ : Q.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • Q).lieBracketNorm = (√c)⁻¹ * Q.lieBracketNorm := by
  refine le_antisymm (lieBracketNorm_smul_le hQ hc) ?_
  have h := lieBracketNorm_smul_le (hQ.smul hc) (inv_pos.mpr hc)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, Real.sqrt_inv, inv_inv] at h
  rw [inv_mul_le_iff₀ (Real.sqrt_pos.mpr hc)]
  exact h

/-- The norm of the Lie bracket does not increase under pullback along a Lie algebra
homomorphism: `γ₀(L', Q ∘ f) ≤ γ₀(L, Q)`. -/
theorem lieBracketNorm_comp_le (hQ : Q.PosDef) (f : L' →ₗ⁅ℝ⁆ L) :
    (Q.comp (f : L' →ₗ[ℝ] L)).lieBracketNorm ≤ Q.lieBracketNorm :=
  lieBracketNorm_le_of_forall_le (lieBracketNorm_nonneg Q) fun X Y ↦ by
    simpa using sqrt_apply_lie_le hQ (f X) (f Y)

variable {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℝ L₁] [LieRing L₂] [LieAlgebra ℝ L₂]
  [FiniteDimensional ℝ L₁] [FiniteDimensional ℝ L₂]

/-- **The norm of the Lie bracket of a product** with the orthogonal sum `Q₁ ⊕ Q₂` of positive
definite quadratic forms is the larger of the two norms. -/
theorem lieBracketNorm_prod {Q₁ : QuadraticForm ℝ L₁} {Q₂ : QuadraticForm ℝ L₂} (hQ₁ : Q₁.PosDef)
    (hQ₂ : Q₂.PosDef) :
    (Q₁.prod Q₂).lieBracketNorm = max Q₁.lieBracketNorm Q₂.lieBracketNorm := by
  have hQ := hQ₁.prod hQ₂
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine lieBracketNorm_le_of_forall_apply_le hQ.nonneg
      ((lieBracketNorm_nonneg _).trans (le_max_left _ _)) fun X Y ↦ ?_
    simp only [prod_apply, LieAlgebra.Prod.bracket_apply]
    have h₁ := apply_lie_le hQ₁ X.1 Y.1
    have h₂ := apply_lie_le hQ₂ X.2 Y.2
    have hm₁ : Q₁.lieBracketNorm ^ 2 ≤ max Q₁.lieBracketNorm Q₂.lieBracketNorm ^ 2 :=
      pow_le_pow_left₀ (lieBracketNorm_nonneg _) (le_max_left _ _) 2
    have hm₂ : Q₂.lieBracketNorm ^ 2 ≤ max Q₁.lieBracketNorm Q₂.lieBracketNorm ^ 2 :=
      pow_le_pow_left₀ (lieBracketNorm_nonneg _) (le_max_right _ _) 2
    have := hQ₁.nonneg X.1
    have := hQ₁.nonneg Y.1
    have := hQ₂.nonneg X.2
    have := hQ₂.nonneg Y.2
    calc Q₁ ⁅X.1, Y.1⁆ + Q₂ ⁅X.2, Y.2⁆
        ≤ Q₁.lieBracketNorm ^ 2 * Q₁ X.1 * Q₁ Y.1 + Q₂.lieBracketNorm ^ 2 * Q₂ X.2 * Q₂ Y.2 :=
          add_le_add h₁ h₂
      _ ≤ max Q₁.lieBracketNorm Q₂.lieBracketNorm ^ 2 * Q₁ X.1 * Q₁ Y.1 +
          max Q₁.lieBracketNorm Q₂.lieBracketNorm ^ 2 * Q₂ X.2 * Q₂ Y.2 := by gcongr
      _ ≤ max Q₁.lieBracketNorm Q₂.lieBracketNorm ^ 2 * (Q₁ X.1 + Q₂ X.2) *
          (Q₁ Y.1 + Q₂ Y.2) := by
        have := sq_nonneg (max Q₁.lieBracketNorm Q₂.lieBracketNorm)
        nlinarith [mul_nonneg (mul_nonneg this (hQ₁.nonneg X.1)) (hQ₂.nonneg Y.2),
          mul_nonneg (mul_nonneg this (hQ₂.nonneg X.2)) (hQ₁.nonneg Y.1)]
  · calc Q₁.lieBracketNorm
        = ((Q₁.prod Q₂).comp (LieHom.inl ℝ L₁ L₂ : L₁ →ₗ[ℝ] L₁ × L₂)).lieBracketNorm := by
          congr 1; ext X; simp
      _ ≤ (Q₁.prod Q₂).lieBracketNorm := lieBracketNorm_comp_le hQ _
  · calc Q₂.lieBracketNorm
        = ((Q₁.prod Q₂).comp (LieHom.inr ℝ L₁ L₂ : L₂ →ₗ[ℝ] L₁ × L₂)).lieBracketNorm := by
          congr 1; ext X; simp
      _ ≤ (Q₁.prod Q₂).lieBracketNorm := lieBracketNorm_comp_le hQ _

end QuadraticMap
