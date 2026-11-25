/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup

/-!
# The action of `U(1, n)` on the unit ball

Let `𝕜` be `ℝ` or `ℂ`. A matrix `g = [[a, bᵀ], [c, D]]` on `𝕜^(Fin 1 ⊕ q)`, with blocks of sizes
`1` and `q`, acts on `EuclideanSpace 𝕜 q` by the fractional linear map
`ballMap g w = (c + D w) / (a + bᵀ w)`: the line spanned by `g (1, w)`, read in the affine chart
`z₀ ≠ 0`. The denominator `a + bᵀ w` is `ballMapDenom g w`; where it vanishes Lean's division
gives the value `0`.

For `g` in the indefinite unitary group `U(1, q)`, the group of matrices preserving the form
`⟨z, z⟩ = ‖z₀‖² - Σ ‖zᵢ‖²`, the vector `(1, w)` has `⟨(1, w), (1, w)⟩ = 1 - ‖w‖²`, and the identity
`‖a + bᵀ w‖² - ‖c + D w‖² = 1 - ‖w‖²` gives the transformation rule
`1 - ‖g · w‖² = (1 - ‖w‖²) / ‖a + bᵀ w‖²`. Hence the denominator does not vanish on the closed unit
ball, and `g` maps the open ball, the closed ball and the unit sphere into themselves. Over `ℂ`
this is the action of `U(1, n)` on the bounded model of complex hyperbolic `n`-space; over `ℝ` it
is the action of `O(1, n)` on the Klein model of real hyperbolic `n`-space.

The main results:

* `Matrix.GeneralLinearGroup.ballMap_mul`: `ballMap (g * h) = ballMap g ∘ ballMap h` wherever the
  denominator of `h` does not vanish, for arbitrary invertible `g` and `h`; scalar matrices act
  trivially (`Matrix.GeneralLinearGroup.ballMap_scalar`).
* `Matrix.GeneralLinearGroup.ballMapDenom_ne_zero` and
  `Matrix.GeneralLinearGroup.one_sub_norm_ballMap_sq`: for `g ∈ U(1, q)`, the denominator does
  not vanish on the closed ball, and the transformation rule above.
* `Matrix.GeneralLinearGroup.mapsTo_ballMap_ball`, `mapsTo_ballMap_closedBall`,
  `mapsTo_ballMap_sphere`, `continuousOn_ballMap_closedBall`: `U(1, q)` acts on the closed ball by
  continuous maps preserving the open ball and the sphere.
* `Matrix.GeneralLinearGroup.exists_val_eq_scalar_of_forall_ballMap_eq_self`: an invertible
  matrix whose map is the identity on the open ball is scalar.
* `TauCeti.Matrix.indefiniteUnitaryGroup.ballHomeomorph`: the action of `U(1, q)` on the open
  ball, as a homomorphism to its group of homeomorphisms (likewise `closedBallHomeomorph` and
  `sphereHomeomorph` on the closed ball and on the boundary sphere), and
  `TauCeti.Matrix.indefiniteUnitaryGroup.ker_ballHomeomorph`: its kernel is the centre of
  `U(1, q)`, the unit scalars, so the action of `PU(1, q)` is faithful.
* `TauCeti.Matrix.indefiniteUnitaryGroup.ballMap_zero_eq_zero_iff`: the stabilizer of the origin
  is the block-diagonal subgroup `U(1) × U(q)`, which acts by the unitary linear maps
  `w ↦ a⁻¹ D w` (`TauCeti.Matrix.indefiniteUnitaryGroup.ballMap_fromBlocksHom`).
* `TauCeti.Matrix.indefiniteUnitaryGroup.exists_ballMap_zero_eq`: `U(1, q)` acts transitively on
  the open ball.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford Mathematical Monographs, Oxford University
  Press (1999), Chapter 3.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2.
-/

public section

open LieAlgebra.Orthogonal Matrix

namespace Matrix.GeneralLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜] {q : Type*} [Fintype q] [DecidableEq q]

/-- The denominator `a + bᵀ w` of the fractional linear map of `g = [[a, bᵀ], [c, D]]` at `w`: the
coordinate `z₀` of `z = g (1, w)`. -/
noncomputable def ballMapDenom (g : GL (Fin 1 ⊕ q) 𝕜) (w : EuclideanSpace 𝕜 q) : 𝕜 :=
  ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) (Sum.inl 0)

/-- The **fractional linear map** `w ↦ (c + D w) / (a + bᵀ w)` of a matrix `g = [[a, bᵀ], [c, D]]`
with blocks of sizes `1` and `q`: the line spanned by `g (1, w)`, read in the affine chart
`z₀ ≠ 0`. Where the denominator `ballMapDenom g w` vanishes its value is `0`. For `g` in `U(1, q)`
the denominator does not vanish on the closed unit ball (`ballMapDenom_ne_zero`), and `ballMap g`
is the action of `g` on the unit ball and on its boundary sphere. -/
noncomputable def ballMap (g : GL (Fin 1 ⊕ q) 𝕜) (w : EuclideanSpace 𝕜 q) :
    EuclideanSpace 𝕜 q :=
  WithLp.toLp 2 fun i =>
    ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) (Sum.inr i) / ballMapDenom g w

variable {g h : GL (Fin 1 ⊕ q) 𝕜} {w : EuclideanSpace 𝕜 q}

/-- The denominator is the coordinate `z₀` of `z = g (1, w)`. -/
theorem ballMapDenom_def (g : GL (Fin 1 ⊕ q) 𝕜) (w : EuclideanSpace 𝕜 q) :
    ballMapDenom g w = ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) (Sum.inl 0) :=
  (rfl)

/-- The coordinates of `ballMap g w` are the ratios `zᵢ / z₀` of the coordinates of
`z = g (1, w)`. -/
@[simp]
theorem ballMap_apply (g : GL (Fin 1 ⊕ q) 𝕜) (w : EuclideanSpace 𝕜 q) (i : q) :
    ballMap g w i =
      ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) (Sum.inr i) /
        ballMapDenom g w :=
  (rfl)

/-- Where the denominator does not vanish, `(1, ballMap g w)` is the multiple
`(ballMapDenom g w)⁻¹ • g (1, w)` of `g (1, w)`. -/
theorem sumElim_one_ballMap (hw : ballMapDenom g w ≠ 0) :
    (Sum.elim 1 (ballMap g w).ofLp : Fin 1 ⊕ q → 𝕜) =
      (ballMapDenom g w)⁻¹ • ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) := by
  funext i
  rcases i with i | i
  · rw [Fin.fin_one_eq_zero i]
    simp [← ballMapDenom_def, inv_mul_cancel₀ hw]
  · simp [div_eq_inv_mul]

/-- Where the denominator of `h` does not vanish, `g (1, ballMap h w)` is the multiple
`(ballMapDenom h w)⁻¹ • (g * h) (1, w)` of `(g * h) (1, w)`. -/
theorem mulVec_sumElim_one_ballMap (hw : ballMapDenom h w ≠ 0) :
    (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 (ballMap h w).ofLp =
      (ballMapDenom h w)⁻¹ •
        (((g * h : GL (Fin 1 ⊕ q) 𝕜) : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ
          Sum.elim 1 w.ofLp) := by
  rw [sumElim_one_ballMap hw, mulVec_smul, mulVec_mulVec, Units.val_mul]

/-- The denominators of fractional linear maps form a cocycle. -/
theorem ballMapDenom_mul (hw : ballMapDenom h w ≠ 0) :
    ballMapDenom (g * h) w = ballMapDenom g (ballMap h w) * ballMapDenom h w := by
  rw [ballMapDenom_def g, mulVec_sumElim_one_ballMap hw, Pi.smul_apply, smul_eq_mul,
    ← ballMapDenom_def]
  field_simp

/-- **The fractional linear maps compose**: `ballMap (g * h) w = ballMap g (ballMap h w)` wherever
the denominator of `h` at `w` does not vanish. -/
theorem ballMap_mul (hw : ballMapDenom h w ≠ 0) :
    ballMap (g * h) w = ballMap g (ballMap h w) := by
  ext i
  rw [ballMap_apply, ballMap_apply, ballMapDenom_mul hw, mulVec_sumElim_one_ballMap hw,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The identity matrix has denominator `1`. -/
@[simp]
theorem ballMapDenom_one (w : EuclideanSpace 𝕜 q) : ballMapDenom 1 w = 1 := by
  simp [ballMapDenom_def]

/-- The identity matrix acts as the identity. -/
@[simp]
theorem ballMap_one (w : EuclideanSpace 𝕜 q) : ballMap 1 w = w := by
  ext i
  simp

/-- `ballMap g⁻¹` is a left inverse of `ballMap g` wherever the denominator of `g` does not
vanish. -/
theorem ballMap_inv_ballMap (hw : ballMapDenom g w ≠ 0) : ballMap g⁻¹ (ballMap g w) = w := by
  rw [← ballMap_mul hw, inv_mul_cancel, ballMap_one]

/-- `ballMap g⁻¹` is a right inverse of `ballMap g` wherever the denominator of `g⁻¹` does not
vanish. -/
theorem ballMap_ballMap_inv (hw : ballMapDenom g⁻¹ w ≠ 0) : ballMap g (ballMap g⁻¹ w) = w := by
  rw [← ballMap_mul hw, mul_inv_cancel, ballMap_one]

/-- The scalar matrix `c • 1` has constant denominator `c`. -/
@[simp]
theorem ballMapDenom_scalar (c : 𝕜ˣ) (w : EuclideanSpace 𝕜 q) :
    ballMapDenom (scalar (Fin 1 ⊕ q) c) w = c := by
  simp [ballMapDenom_def]

/-- Scalar matrices act trivially. -/
@[simp]
theorem ballMap_scalar (c : 𝕜ˣ) (w : EuclideanSpace 𝕜 q) :
    ballMap (scalar (Fin 1 ⊕ q) c) w = w := by
  ext i
  simp

/-- The denominator at the origin is the corner entry `a` of `g = [[a, bᵀ], [c, D]]`. -/
@[simp]
theorem ballMapDenom_zero (g : GL (Fin 1 ⊕ q) 𝕜) :
    ballMapDenom g 0 = (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inl 0) (Sum.inl 0) := by
  simp [ballMapDenom_def, mulVec, dotProduct, Fintype.sum_sum_type]

/-- The image of the origin under `ballMap g` is the column `c / a` of `g = [[a, bᵀ], [c, D]]`. -/
theorem ballMap_zero_apply (g : GL (Fin 1 ⊕ q) 𝕜) (i : q) :
    ballMap g 0 i = (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inr i) (Sum.inl 0) /
      (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inl 0) (Sum.inl 0) := by
  rw [ballMap_apply, ballMapDenom_zero]
  simp [mulVec, dotProduct, Fintype.sum_sum_type]

omit [Fintype q] [DecidableEq q] in
/-- The homogeneous lift `w ↦ (1, w)` is continuous. -/
private theorem continuous_sumElim_one_ofLp :
    Continuous fun w : EuclideanSpace 𝕜 q => (Sum.elim 1 w.ofLp : Fin 1 ⊕ q → 𝕜) :=
  continuous_pi fun j => by
    rcases j with j | j
    exacts [continuous_const, PiLp.continuous_apply 2 _ j]

/-- The lifted map `w ↦ g (1, w)` is continuous. -/
private theorem continuous_mulVec_sumElim_one (g : GL (Fin 1 ⊕ q) 𝕜) :
    Continuous fun w : EuclideanSpace 𝕜 q =>
      (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp :=
  continuous_const.matrix_mulVec continuous_sumElim_one_ofLp

/-- The denominator `w ↦ a + bᵀ w` is continuous. -/
theorem continuous_ballMapDenom (g : GL (Fin 1 ⊕ q) 𝕜) : Continuous (ballMapDenom g) :=
  (continuous_apply _).comp (continuous_mulVec_sumElim_one g)

/-- The fractional linear map is continuous where its denominator does not vanish. -/
theorem continuousAt_ballMap (hw : ballMapDenom g w ≠ 0) : ContinuousAt (ballMap g) w := by
  refine (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.2 fun i => ?_)
  exact ((continuous_apply _).comp (continuous_mulVec_sumElim_one g)).continuousAt.div
    (continuous_ballMapDenom g).continuousAt hw

section indefiniteUnitaryGroup

open Metric TauCeti.Matrix

/-- For `g ∈ U(1, q)`, the coordinates of `z = g (1, w)` satisfy
`‖z₀‖² - Σ ‖zᵢ‖² = ⟨z, z⟩ = ⟨(1, w), (1, w)⟩ = 1 - ‖w‖²`. -/
theorem norm_ballMapDenom_sq_sub_sum (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : EuclideanSpace 𝕜 q) :
    ‖ballMapDenom g w‖ ^ 2 -
        ∑ i, ‖((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp) (Sum.inr i)‖ ^ 2 =
      1 - ‖w‖ ^ 2 := by
  have h := mem_unitaryGroupOf_iff_forall_dotProduct.mp hg (Sum.elim 1 w.ofLp)
    (Sum.elim 1 w.ofLp)
  rw [star_dotProduct_indefiniteDiagonal_mulVec_self,
    star_dotProduct_indefiniteDiagonal_mulVec_self, RCLike.ofReal_inj] at h
  simpa [EuclideanSpace.norm_sq_eq, ← ballMapDenom_def] using h

/-- **The denominator does not vanish on the closed ball**: for `g ∈ U(1, q)` and `‖w‖ ≤ 1`,
`a + bᵀ w ≠ 0`. -/
theorem ballMapDenom_ne_zero (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) (hw : ‖w‖ ≤ 1) :
    ballMapDenom g w ≠ 0 := by
  intro h0
  set z := (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 w.ofLp with hz
  have h := norm_ballMapDenom_sq_sub_sum hg w
  rw [h0, norm_zero, ← hz] at h
  have hsum : ∑ i, ‖z (Sum.inr i)‖ ^ 2 = 0 := by
    have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖z (Sum.inr i)‖
    nlinarith [norm_nonneg w]
  have hz0 : z = 0 := by
    funext i
    rcases i with i | i
    · rw [Fin.fin_one_eq_zero i]
      exact h0
    · simpa using (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp hsum i
        (Finset.mem_univ i)
  have h1 := mulVec_injective_of_isUnit g.isUnit (hz0.trans (mulVec_zero _).symm)
  simpa using congrFun h1 (Sum.inl 0)

/-- **The transformation rule of `1 - ‖w‖²`**: for `g ∈ U(1, q)`,
`1 - ‖ballMap g w‖² = (1 - ‖w‖²) / ‖ballMapDenom g w‖²` wherever the denominator does not
vanish. -/
theorem one_sub_norm_ballMap_sq (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (hw : ballMapDenom g w ≠ 0) :
    1 - ‖ballMap g w‖ ^ 2 = (1 - ‖w‖ ^ 2) / ‖ballMapDenom g w‖ ^ 2 := by
  have hd : ‖ballMapDenom g w‖ ^ 2 ≠ 0 := by positivity
  rw [← norm_ballMapDenom_sq_sub_sum hg w, EuclideanSpace.norm_sq_eq, eq_div_iff hd, sub_mul,
    Finset.sum_mul]
  simp [div_pow, div_mul_cancel₀ _ hd]

/-- `g ∈ U(1, q)` maps points of the open ball, and only those, into the open ball. -/
theorem norm_ballMap_lt_one_iff (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (hw : ballMapDenom g w ≠ 0) : ‖ballMap g w‖ < 1 ↔ ‖w‖ < 1 := by
  have hd : 0 < ‖ballMapDenom g w‖ ^ 2 := by positivity
  have key : 0 < 1 - ‖ballMap g w‖ ^ 2 ↔ 0 < 1 - ‖w‖ ^ 2 := by
    rw [one_sub_norm_ballMap_sq hg hw, div_pos_iff_of_pos_right hd]
  simpa only [sub_pos, sq_lt_one_iff₀ (norm_nonneg _)] using key

/-- `g ∈ U(1, q)` maps points of the unit sphere, and only those, onto the unit sphere. -/
theorem norm_ballMap_eq_one_iff (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (hw : ballMapDenom g w ≠ 0) : ‖ballMap g w‖ = 1 ↔ ‖w‖ = 1 := by
  have hd : ‖ballMapDenom g w‖ ^ 2 ≠ 0 := by positivity
  have key : 1 - ‖ballMap g w‖ ^ 2 = 0 ↔ 1 - ‖w‖ ^ 2 = 0 := by
    rw [one_sub_norm_ballMap_sq hg hw, div_eq_zero_iff, or_iff_left hd]
  simpa only [sub_eq_zero, eq_comm (a := (1 : ℝ)),
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] using key

/-- `g ∈ U(1, q)` maps points of the closed ball, and only those, into the closed ball. -/
theorem norm_ballMap_le_one_iff (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (hw : ballMapDenom g w ≠ 0) : ‖ballMap g w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := by
  simp only [le_iff_lt_or_eq, norm_ballMap_lt_one_iff hg hw, norm_ballMap_eq_one_iff hg hw]

/-- An element of `U(1, q)` maps the open unit ball into itself. -/
theorem mapsTo_ballMap_ball (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) :
    Set.MapsTo (ballMap g) (ball 0 1) (ball 0 1) := fun w hw => by
  rw [mem_ball_zero_iff] at hw ⊢
  exact (norm_ballMap_lt_one_iff hg (ballMapDenom_ne_zero hg hw.le)).mpr hw

/-- An element of `U(1, q)` maps the unit sphere into itself. -/
theorem mapsTo_ballMap_sphere (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) :
    Set.MapsTo (ballMap g) (sphere 0 1) (sphere 0 1) := fun w hw => by
  rw [mem_sphere_zero_iff_norm] at hw ⊢
  exact (norm_ballMap_eq_one_iff hg (ballMapDenom_ne_zero hg hw.le)).mpr hw

/-- An element of `U(1, q)` maps the closed unit ball into itself. -/
theorem mapsTo_ballMap_closedBall (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) :
    Set.MapsTo (ballMap g) (closedBall 0 1) (closedBall 0 1) := fun w hw => by
  rw [mem_closedBall_zero_iff] at hw ⊢
  exact (norm_ballMap_le_one_iff hg (ballMapDenom_ne_zero hg hw)).mpr hw

/-- On the closed ball, the maps of elements of `U(1, q)` compose. -/
theorem ballMap_mul_of_mem (hh : h ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) (hw : ‖w‖ ≤ 1) :
    ballMap (g * h) w = ballMap g (ballMap h w) :=
  ballMap_mul (ballMapDenom_ne_zero hh hw)

/-- On the closed ball, `ballMap g⁻¹` is a left inverse of `ballMap g` for `g ∈ U(1, q)`. -/
theorem ballMap_inv_ballMap_of_mem (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) (hw : ‖w‖ ≤ 1) :
    ballMap g⁻¹ (ballMap g w) = w :=
  ballMap_inv_ballMap (ballMapDenom_ne_zero hg hw)

/-- On the closed ball, `ballMap g⁻¹` is a right inverse of `ballMap g` for `g ∈ U(1, q)`. -/
theorem ballMap_ballMap_inv_of_mem (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) (hw : ‖w‖ ≤ 1) :
    ballMap g (ballMap g⁻¹ w) = w :=
  ballMap_ballMap_inv (ballMapDenom_ne_zero (inv_mem hg) hw)

/-- An element of `U(1, q)` acts continuously on the closed unit ball. -/
theorem continuousOn_ballMap_closedBall (hg : g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜) :
    ContinuousOn (ballMap g) (closedBall 0 1) := fun _ hw =>
  (continuousAt_ballMap
    (ballMapDenom_ne_zero hg (mem_closedBall_zero_iff.mp hw))).continuousWithinAt

end indefiniteUnitaryGroup

/-- The coordinates of `g *ᵥ (1, w)` at `w = t eₖ`. -/
private theorem mulVec_sumElim_one_single (g : GL (Fin 1 ⊕ q) 𝕜) (k : q) (t : 𝕜)
    (r : Fin 1 ⊕ q) :
    ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ
        Sum.elim 1 (EuclideanSpace.single k t : EuclideanSpace 𝕜 q).ofLp) r =
      (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) r (Sum.inl 0) +
        t * (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) r (Sum.inr k) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply, mul_comm]

/-- If `g` fixes the point `t eₖ ≠ 0`, then `g *ᵥ (1, t eₖ)` is a multiple of `(1, t eₖ)`. -/
private theorem apply_inl_add_mul_eq_of_ballMap_single_eq {k : q} {t : 𝕜} (ht : t ≠ 0)
    (h : ballMap g (EuclideanSpace.single k t) = EuclideanSpace.single k t) (i : q) :
    (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inr i) (Sum.inl 0) +
        t * (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inr i) (Sum.inr k) =
      (Pi.single k t : q → 𝕜) i * ((g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inl 0) (Sum.inl 0) +
        t * (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) (Sum.inl 0) (Sum.inr k)) := by
  have hd : ballMapDenom g (EuclideanSpace.single k t) ≠ 0 := by
    intro hd
    have := congrArg (fun v : EuclideanSpace 𝕜 q => v k) h
    simp [hd, ht.symm] at this
  have := congrArg (fun v : EuclideanSpace 𝕜 q => v i) h
  simp only [ballMap_apply, mulVec_sumElim_one_single] at this
  rw [ballMapDenom_def, mulVec_sumElim_one_single] at this hd
  rw [div_eq_iff hd] at this
  simpa [Pi.single_apply] using this

/-- **Only scalar matrices fix the ball pointwise.** If the fractional linear map of `g` is the
identity on the open unit ball, then `g` is a scalar matrix. -/
theorem exists_val_eq_scalar_of_forall_ballMap_eq_self
    (h : ∀ w ∈ Metric.ball (0 : EuclideanSpace 𝕜 q) 1, ballMap g w = w) :
    ∃ c : 𝕜, (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) = Matrix.scalar (Fin 1 ⊕ q) c := by
  set M : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜 := (g : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜)
  have hfix (k : q) (t : 𝕜) (ht : t ≠ 0) (ht1 : ‖t‖ < 1) :=
    apply_inl_add_mul_eq_of_ballMap_single_eq ht
      (h _ (by simpa [mem_ball_zero_iff] using ht1)) (k := k)
  have h₁ (k : q) := hfix k (1 / 2) (by norm_num) (by simp; norm_num)
  have h₂ (k : q) := hfix k (-1 / 2) (by norm_num) (by simp; norm_num)
  have h₃ (k : q) := hfix k (1 / 3) (by norm_num) (by simp; norm_num)
  -- Writing `g = [[a, bᵀ], [c, D]]`, the fixed point `t eₖ` gives `cᵢ + t Dᵢₖ = t δᵢₖ (a + t bₖ)`.
  -- For `i ≠ k` the values `t = ±1/2` give `cᵢ = Dᵢₖ = 0`.
  have hoff {i k : q} (hik : i ≠ k) :
      M (Sum.inr i) (Sum.inl 0) = 0 ∧ M (Sum.inr i) (Sum.inr k) = 0 := by
    have e₁ := h₁ k i
    have e₂ := h₂ k i
    simp only [Pi.single_apply, hik, ite_false, zero_mul] at e₁ e₂
    exact ⟨by linear_combination (e₁ + e₂) / 2, by linear_combination e₁ - e₂⟩
  have hdiag (k : q) : M (Sum.inr k) (Sum.inl 0) = 0 ∧ M (Sum.inl 0) (Sum.inr k) = 0 ∧
      M (Sum.inr k) (Sum.inr k) = M (Sum.inl 0) (Sum.inl 0) := by
    have e₁ := h₁ k k
    have e₂ := h₂ k k
    -- For `i = k` the three values of `t` give `cₖ = bₖ = 0` and `Dₖₖ = a`.
    have e₃ := h₃ k k
    simp only [Pi.single_eq_same] at e₁ e₂ e₃
    refine ⟨?_, ?_, by linear_combination e₁ - e₂⟩
    · linear_combination -e₁ + (1 / 5) * e₂ + (9 / 5) * e₃
    · linear_combination -6 * e₁ - (6 / 5) * e₂ + (36 / 5) * e₃
  refine ⟨M (Sum.inl 0) (Sum.inl 0), ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [Fin.fin_one_eq_zero r, Fin.fin_one_eq_zero s]
  · simp [Fin.fin_one_eq_zero r, (hdiag s).2.1]
  · simp [Fin.fin_one_eq_zero s, (hdiag r).1]
  · rcases eq_or_ne r s with rfl | hrs
    · simp [(hdiag r).2.2]
    · simp [(hoff hrs).2, hrs]

end Matrix.GeneralLinearGroup

namespace TauCeti.Matrix.indefiniteUnitaryGroup

open Metric Matrix.GeneralLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜] {q : Type*} [Fintype q] [DecidableEq q]

/-- The action of `U(1, q)` on a subset `S` of the closed unit ball that every element of
`U(1, q)` maps into itself, as a homomorphism to the group of homeomorphisms of `S`. -/
private noncomputable def homeomorphOfMapsTo (S : Set (EuclideanSpace 𝕜 q))
    (hS : S ⊆ closedBall 0 1)
    (hmaps : ∀ g ∈ indefiniteUnitaryGroup (Fin 1) q 𝕜, Set.MapsTo (ballMap g) S S) :
    indefiniteUnitaryGroup (Fin 1) q 𝕜 →* (S ≃ₜ S) where
  toFun g :=
    { toFun w := ⟨ballMap g w, hmaps g g.property w.property⟩
      invFun w := ⟨ballMap (g : GL (Fin 1 ⊕ q) 𝕜)⁻¹ w, hmaps _ (inv_mem g.property) w.property⟩
      left_inv w := Subtype.ext <|
        ballMap_inv_ballMap_of_mem g.property (mem_closedBall_zero_iff.mp (hS w.property))
      right_inv w := Subtype.ext <|
        ballMap_ballMap_inv_of_mem g.property (mem_closedBall_zero_iff.mp (hS w.property))
      continuous_toFun := ((continuousOn_ballMap_closedBall g.property).mono hS
        |>.mapsToRestrict (hmaps g g.property))
      continuous_invFun := ((continuousOn_ballMap_closedBall (inv_mem g.property)).mono hS
        |>.mapsToRestrict (hmaps _ (inv_mem g.property))) }
  map_one' := Homeomorph.ext fun _ => Subtype.ext <| ballMap_one _
  map_mul' _ h := Homeomorph.ext fun w => Subtype.ext <|
    ballMap_mul_of_mem h.property (mem_closedBall_zero_iff.mp (hS w.property))

variable (𝕜 q) in
/-- **The action of `U(1, q)` on the unit ball**: the homomorphism sending `g` to the
homeomorphism `w ↦ ballMap g w` of the open unit ball of `EuclideanSpace 𝕜 q`. Its kernel is the
centre (`ker_ballHomeomorph`), so it descends to a faithful action of `PU(1, q)`. -/
noncomputable def ballHomeomorph :
    indefiniteUnitaryGroup (Fin 1) q 𝕜 →*
      (ball (0 : EuclideanSpace 𝕜 q) 1 ≃ₜ ball (0 : EuclideanSpace 𝕜 q) 1) :=
  homeomorphOfMapsTo _ ball_subset_closedBall fun _ => mapsTo_ballMap_ball

variable (𝕜 q) in
/-- The action of `U(1, q)` on the closed unit ball: the homomorphism sending `g` to the
homeomorphism `w ↦ ballMap g w` of the closed unit ball of `EuclideanSpace 𝕜 q`. -/
noncomputable def closedBallHomeomorph :
    indefiniteUnitaryGroup (Fin 1) q 𝕜 →*
      (closedBall (0 : EuclideanSpace 𝕜 q) 1 ≃ₜ closedBall (0 : EuclideanSpace 𝕜 q) 1) :=
  homeomorphOfMapsTo _ subset_rfl fun _ => mapsTo_ballMap_closedBall

variable (𝕜 q) in
/-- The action of `U(1, q)` on the boundary of the unit ball: the homomorphism sending `g` to the
homeomorphism `w ↦ ballMap g w` of the unit sphere of `EuclideanSpace 𝕜 q`. -/
noncomputable def sphereHomeomorph :
    indefiniteUnitaryGroup (Fin 1) q 𝕜 →*
      (sphere (0 : EuclideanSpace 𝕜 q) 1 ≃ₜ sphere (0 : EuclideanSpace 𝕜 q) 1) :=
  homeomorphOfMapsTo _ sphere_subset_closedBall fun _ => mapsTo_ballMap_sphere

/-- The homeomorphism `ballHomeomorph 𝕜 q g` of the ball is `ballMap g`. -/
@[simp]
theorem coe_ballHomeomorph_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : ball (0 : EuclideanSpace 𝕜 q) 1) :
    (ballHomeomorph 𝕜 q g w : EuclideanSpace 𝕜 q) = ballMap g w :=
  (rfl)

/-- The inverse of the homeomorphism `ballHomeomorph 𝕜 q g` of the ball is `ballMap g⁻¹`. -/
@[simp]
theorem coe_ballHomeomorph_symm_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : ball (0 : EuclideanSpace 𝕜 q) 1) :
    ((ballHomeomorph 𝕜 q g).symm w : EuclideanSpace 𝕜 q) = ballMap (g : GL (Fin 1 ⊕ q) 𝕜)⁻¹ w :=
  (rfl)

/-- The homeomorphism `closedBallHomeomorph 𝕜 q g` of the closed ball is `ballMap g`. -/
@[simp]
theorem coe_closedBallHomeomorph_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : closedBall (0 : EuclideanSpace 𝕜 q) 1) :
    (closedBallHomeomorph 𝕜 q g w : EuclideanSpace 𝕜 q) = ballMap g w :=
  (rfl)

/-- The inverse of the homeomorphism `closedBallHomeomorph 𝕜 q g` of the closed ball is
`ballMap g⁻¹`. -/
@[simp]
theorem coe_closedBallHomeomorph_symm_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : closedBall (0 : EuclideanSpace 𝕜 q) 1) :
    ((closedBallHomeomorph 𝕜 q g).symm w : EuclideanSpace 𝕜 q) =
      ballMap (g : GL (Fin 1 ⊕ q) 𝕜)⁻¹ w :=
  (rfl)

/-- The homeomorphism `sphereHomeomorph 𝕜 q g` of the unit sphere is `ballMap g`. -/
@[simp]
theorem coe_sphereHomeomorph_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : sphere (0 : EuclideanSpace 𝕜 q) 1) :
    (sphereHomeomorph 𝕜 q g w : EuclideanSpace 𝕜 q) = ballMap g w :=
  (rfl)

/-- The inverse of the homeomorphism `sphereHomeomorph 𝕜 q g` of the unit sphere is
`ballMap g⁻¹`. -/
@[simp]
theorem coe_sphereHomeomorph_symm_apply (g : indefiniteUnitaryGroup (Fin 1) q 𝕜)
    (w : sphere (0 : EuclideanSpace 𝕜 q) 1) :
    ((sphereHomeomorph 𝕜 q g).symm w : EuclideanSpace 𝕜 q) =
      ballMap (g : GL (Fin 1 ⊕ q) 𝕜)⁻¹ w :=
  (rfl)

/-- **The kernel of the action on the ball is the centre**: an element of `U(1, q)` acts
trivially on the open unit ball exactly when it is a unit scalar. -/
theorem ker_ballHomeomorph :
    (ballHomeomorph 𝕜 q).ker = Subgroup.center (indefiniteUnitaryGroup (Fin 1) q 𝕜) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := exists_val_eq_scalar_of_forall_ballMap_eq_self fun w hw => by
      simpa using congrArg Subtype.val (DFunLike.congr_fun hg ⟨w, hw⟩)
    refine Subgroup.mem_center_iff.mpr fun h => unitaryGroupOf.ext ?_
    simp only [Subgroup.coe_mul, Units.val_mul, hc]
    exact (scalar_commute c (fun _ => Commute.all _ _) _).eq.symm
  · intro hg
    rw [center_eq_range_scalarHom] at hg
    obtain ⟨u, rfl⟩ := hg
    refine Homeomorph.ext fun w => Subtype.ext ?_
    have hu : ((unitaryGroupOf.scalarHom (indefiniteDiagonal (Fin 1) q 𝕜) u :
        indefiniteUnitaryGroup (Fin 1) q 𝕜) : GL (Fin 1 ⊕ q) 𝕜) =
        GeneralLinearGroup.scalar (Fin 1 ⊕ q) (Unitary.toUnits u) := Units.ext (by simp)
    rw [coe_ballHomeomorph_apply, hu, ballMap_scalar]
    exact congrArg Subtype.val (Homeomorph.one_apply w).symm

/-- **Two elements of `U(1, q)` act in the same way on the ball exactly when they differ by a unit
scalar.** -/
theorem ballHomeomorph_eq_ballHomeomorph_iff {g h : indefiniteUnitaryGroup (Fin 1) q 𝕜} :
    ballHomeomorph 𝕜 q g = ballHomeomorph 𝕜 q h ↔
      ∃ u : unitary 𝕜, h = g * unitaryGroupOf.scalarHom (indefiniteDiagonal (Fin 1) q 𝕜) u := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, ker_ballHomeomorph,
    center_eq_range_scalarHom, MonoidHom.mem_range]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, by rw [hu, mul_inv_cancel_left]⟩,
    fun ⟨u, hu⟩ => ⟨u, by rw [hu, inv_mul_cancel_left]⟩⟩

/-- **The stabilizer of the origin.** An element of `U(1, q)` fixes the centre `0` of the ball
exactly when it is block diagonal, that is lies in the image `U(1) × U(q)` of `fromBlocksHom`. -/
theorem ballMap_zero_eq_zero_iff {g : indefiniteUnitaryGroup (Fin 1) q 𝕜} :
    ballMap (g : GL (Fin 1 ⊕ q) 𝕜) 0 = 0 ↔ g ∈ (fromBlocksHom (Fin 1) q 𝕜).range := by
  have hd := ballMapDenom_ne_zero g.property (w := 0) (by simp)
  rw [ballMapDenom_zero] at hd
  rw [mem_range_fromBlocksHom_iff]
  constructor
  · intro h
    ext i j
    rw [Fin.fin_one_eq_zero j]
    have h' := congrArg (fun v : EuclideanSpace 𝕜 q => v i) h
    dsimp only at h'
    rw [ballMap_zero_apply, PiLp.zero_apply, div_eq_zero_iff, or_iff_left hd] at h'
    simpa [toBlocks₂₁] using h'
  · intro h
    ext i
    rw [ballMap_zero_apply, PiLp.zero_apply, div_eq_zero_iff]
    exact Or.inl (by simpa [toBlocks₂₁] using congrFun (congrFun h i) 0)

/-- The block-diagonal element `diag(a, D)` of `U(1, q)` acts on the ball by the unitary linear
map `w ↦ a⁻¹ D w`. -/
theorem ballMap_fromBlocksHom (x : unitaryGroup (Fin 1) 𝕜 × unitaryGroup q 𝕜)
    (w : EuclideanSpace 𝕜 q) :
    ballMap (fromBlocksHom (Fin 1) q 𝕜 x : GL (Fin 1 ⊕ q) 𝕜) w =
      WithLp.toLp 2 (((x.1 : Matrix (Fin 1) (Fin 1) 𝕜) 0 0)⁻¹ •
        ((x.2 : Matrix q q 𝕜) *ᵥ w.ofLp)) := by
  ext i
  simp [ballMapDenom_def, mulVec, dotProduct, Fintype.sum_sum_type, div_eq_inv_mul]

/-- For `w ≠ 0` in the open ball, the reflection in `s e₀ - (1, w)`, where `s = √(1 - ‖w‖²)`, is
an element of `U(1, q)` sending `e₀ = (1, 0)` to a nonzero multiple of `(1, w)`. -/
private theorem exists_mulVec_sumElim_one_zero_eq_smul {w : EuclideanSpace 𝕜 q} (hw : ‖w‖ < 1)
    (hw0 : w ≠ 0) :
    ∃ (g : indefiniteUnitaryGroup (Fin 1) q 𝕜) (c : 𝕜), c ≠ 0 ∧
      ((g : GL (Fin 1 ⊕ q) 𝕜) : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ Sum.elim 1 0 =
        c • (Sum.elim 1 w.ofLp : Fin 1 ⊕ q → 𝕜) := by
  set s : ℝ := √(1 - ‖w‖ ^ 2)
  have hw2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  have hs2 : s ^ 2 = 1 - ‖w‖ ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : ‖w‖ ^ 2 = 0 := by rw [h1] at hs2; linarith
    exact hw0 (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))
  set e : Fin 1 ⊕ q → 𝕜 := Sum.elim 1 0
  set v : Fin 1 ⊕ q → 𝕜 := (s : 𝕜) • e - (Sum.elim 1 w.ofLp : Fin 1 ⊕ q → 𝕜)
  have hvv : star v ⬝ᵥ indefiniteDiagonal (Fin 1) q 𝕜 *ᵥ v = ((2 * s * (s - 1) : ℝ) : 𝕜) := by
    rw [star_dotProduct_indefiniteDiagonal_mulVec_self, RCLike.ofReal_inj]
    have h0 : ‖v (Sum.inl 0)‖ ^ 2 = (s - 1) ^ 2 := by
      have : v (Sum.inl 0) = ((s - 1 : ℝ) : 𝕜) := by simp [v, e, Algebra.smul_def]
      rw [this, RCLike.norm_ofReal, sq_abs]
    have h1 : ∑ j, ‖v (Sum.inr j)‖ ^ 2 = ‖w‖ ^ 2 := by
      simp [v, e, EuclideanSpace.norm_sq_eq]
    rw [Fintype.sum_unique, Fin.default_eq_zero, h0, h1]
    linear_combination -hs2
  have hve : star v ⬝ᵥ indefiniteDiagonal (Fin 1) q 𝕜 *ᵥ e = ((s - 1 : ℝ) : 𝕜) := by
    simp [v, e, dotProduct, Fintype.sum_sum_type, indefiniteDiagonal, mulVec_diagonal,
      Algebra.smul_def]
  have hv0 : star v ⬝ᵥ indefiniteDiagonal (Fin 1) q 𝕜 *ᵥ v ≠ 0 := by
    rw [hvv, RCLike.ofReal_ne_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs0.ne') (sub_ne_zero.mpr hs1)
  set R := unitaryGroupOf.reflection isHermitian_indefiniteDiagonal isUnit_indefiniteDiagonal v hv0
  -- The reflection sends `e₀` to `s⁻¹ (1, w)`.
  have hR : ((R : GL (Fin 1 ⊕ q) 𝕜) : Matrix (Fin 1 ⊕ q) (Fin 1 ⊕ q) 𝕜) *ᵥ e =
      (s : 𝕜)⁻¹ • (Sum.elim 1 w.ofLp : Fin 1 ⊕ q → 𝕜) := by
    have hs' : (s : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hs0.ne'
    have hs1' : (s : 𝕜) - 1 ≠ 0 := by
      rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.ofReal_ne_zero]
      exact sub_ne_zero.mpr hs1
    rw [unitaryGroupOf.reflection_mulVec, hvv, hve]
    funext r
    rcases r with r | r
    · rw [Fin.fin_one_eq_zero r]
      simp only [v, e, Pi.sub_apply, Pi.smul_apply, Sum.elim_inl, Pi.one_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    · simp only [v, e, Pi.sub_apply, Pi.smul_apply, Sum.elim_inr, Pi.zero_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
  exact ⟨R, (s : 𝕜)⁻¹, inv_ne_zero (RCLike.ofReal_ne_zero.mpr hs0.ne'), hR⟩

/-- **`U(1, q)` acts transitively on the ball**: every point `w` of the open unit ball is the
image of the origin under an element of `U(1, q)`. -/
theorem exists_ballMap_zero_eq {w : EuclideanSpace 𝕜 q} (hw : ‖w‖ < 1) :
    ∃ g : indefiniteUnitaryGroup (Fin 1) q 𝕜, ballMap (g : GL (Fin 1 ⊕ q) 𝕜) 0 = w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨1, by simp⟩
  obtain ⟨g, c, hc, hg⟩ := exists_mulVec_sumElim_one_zero_eq_smul hw hw0
  refine ⟨g, ?_⟩
  ext i
  rw [ballMap_apply, ballMapDenom_def, WithLp.ofLp_zero, hg]
  simp only [Pi.smul_apply, Sum.elim_inr, Sum.elim_inl, Pi.one_apply, smul_eq_mul, mul_one]
  field_simp

end TauCeti.Matrix.indefiniteUnitaryGroup
