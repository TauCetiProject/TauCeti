/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinear
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Sharp triple transitivity of Möbius transformations

The Möbius transformations of the projective line `OnePoint K` over a field `K` act sharply
triply transitively: for any three pairwise distinct points `x`, `y`, `z` there is exactly one
element of `PGL(2, K)` carrying `0`, `1`, `∞` to `x`, `y`, `z`. Existence follows from the
2-transitivity of `GL(2, K)` (`OnePoint.instIsMultiplyPretransitiveGL`) followed by a dilation,
and uniqueness from the fact that a matrix fixing `0`, `1` and `∞` is scalar
(`TauCeti.mem_center_of_smul_zero_one_infty_eq_self`).

The same holds for `PSL(2, K)` when every unit of `K` is a square, in particular over an
algebraically closed field such as `ℂ`: there the inclusion `PSL(2, K) → PGL(2, K)` is bijective
and compatible with the actions (`Matrix.ProjectiveSpecialLinearGroup.toPGL_smul`). Without
square roots this fails: over `ℝ`, `PSL(2, ℝ)` preserves the cyclic order of the real projective
line.

For the Riemann sphere `OnePoint ℂ`, this identifies `PSL(2, ℂ)` with the ordered triples of
distinct points, which is how the automorphisms of a genus-zero domain are normalized by fixing
`(0, 1, ∞)`.

## Main results

* `OnePoint.exists_smul_zero_one_infty_eq`: some element of `GL(2, K)` carries `0`, `1`, `∞` to
  any three pairwise distinct points.
* `OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`: exactly one element of `PGL(2, K)` does.
* `OnePoint.instIsMultiplyPretransitivePGL`: `PGL(2, K)` acts 3-transitively on `OnePoint K`.
* `Matrix.ProjectiveSpecialLinearGroup.toPGL_smul`: the inclusion `PSL(2, K) → PGL(2, K)` is
  compatible with the actions.
* `OnePoint.existsUnique_psl_smul_zero_one_infty_eq_of_roots` and
  `OnePoint.existsUnique_psl_smul_zero_one_infty_eq`: exactly one element of `PSL(2, K)` carries
  `0`, `1`, `∞` to three pairwise distinct points, when every unit of `K` is a square and when `K`
  is algebraically closed.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Theorem 3.2.2.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §2.
-/

public section

open scoped MatrixGroups

namespace OnePoint

open Matrix

variable {K : Type*} [Field K] [DecidableEq K]

/-- **`GL(2, K)` carries `0`, `1`, `∞` to any three pairwise distinct points** of the projective
line. -/
theorem exists_smul_zero_one_infty_eq {x y z : OnePoint K} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    ∃ g : GL (Fin 2) K, g • ((0 : K) : OnePoint K) = x ∧ g • ((1 : K) : OnePoint K) = y ∧
      g • (∞ : OnePoint K) = z := by
  -- Move `0` and `∞` to `x` and `z` by 2-transitivity; the preimage of `y` is then a nonzero
  -- affine point `c`, and the dilation `w ↦ c * w`, which fixes `0` and `∞`, moves `1` to it.
  obtain ⟨g, hg0, hginf⟩ := MulAction.is_two_pretransitive_iff.mp instIsMultiplyPretransitiveGL
    (coe_ne_infty (0 : K)) hxz
  -- The preimage `g⁻¹ • y` of `y` is neither `0` nor `∞`.
  obtain ⟨c, hc⟩ : ∃ c : K, ((c : K) : OnePoint K) = g⁻¹ • y := by
    induction h : g⁻¹ • y using OnePoint.rec with
    | infty => exact absurd (by rw [← hginf, ← h, smul_inv_smul]) hyz
    | coe c => exact ⟨c, rfl⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hxy (by rw [← hg0, hc, smul_inv_smul])
  refine ⟨g * GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1] (by simpa using hc0), ?_, ?_, ?_⟩
  · rw [mul_smul, smul_some_eq_ite]
    simpa [GeneralLinearGroup.mkOfDetNeZero] using hg0
  · rw [mul_smul, smul_some_eq_ite]
    simp [GeneralLinearGroup.mkOfDetNeZero, hc]
  · rw [mul_smul, smul_infty_eq_self_iff.mpr (by simp [GeneralLinearGroup.mkOfDetNeZero]), hginf]

/-- **Sharp triple transitivity of `PGL(2, K)`.** Exactly one Möbius transformation carries `0`,
`1`, `∞` to three given pairwise distinct points of the projective line. -/
theorem existsUnique_pgl_smul_zero_one_infty_eq {x y z : OnePoint K} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃! g : PGL(2, K), g • ((0 : K) : OnePoint K) = x ∧ g • ((1 : K) : OnePoint K) = y ∧
      g • (∞ : OnePoint K) = z := by
  obtain ⟨g, hg⟩ := exists_smul_zero_one_infty_eq hxy hxz hyz
  refine ⟨ProjGenLinGroup.mk g, by simpa using hg, ?_⟩
  rintro g' ⟨h0, h1, hinf⟩
  obtain ⟨g', rfl⟩ := ProjGenLinGroup.mk_surjective g'
  simp only [pglMk_smul] at h0 h1 hinf
  -- `g⁻¹ * g'` fixes `0`, `1` and `∞`, so it is central.
  have hfix (w : OnePoint K) (hw : g' • w = g • w) : (g⁻¹ * g') • w = w := by
    rw [mul_smul, hw, inv_smul_smul]
  have hcentre := TauCeti.mem_center_of_smul_zero_one_infty_eq_self (hfix _ (h0.trans hg.1.symm))
    (hfix _ (h1.trans hg.2.1.symm)) (hfix _ (hinf.trans hg.2.2.symm))
  rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_inv, inv_mul_eq_one] at hcentre
  exact hcentre.symm

/-- **`PGL(2, K)` acts 3-transitively on the projective line**: any ordered triple of distinct
points is carried to any other by some Möbius transformation. -/
instance instIsMultiplyPretransitivePGL :
    MulAction.IsMultiplyPretransitive PGL(2, K) (OnePoint K) 3 where
  exists_smul_eq a b := by
    -- Both triples are images of `(0, 1, ∞)`.
    have key (e : Fin 3 ↪ OnePoint K) : ∃ g : PGL(2, K), g • ((0 : K) : OnePoint K) = e 0 ∧
        g • ((1 : K) : OnePoint K) = e 1 ∧ g • (∞ : OnePoint K) = e 2 :=
      (existsUnique_pgl_smul_zero_one_infty_eq (e.injective.ne (by decide))
        (e.injective.ne (by decide)) (e.injective.ne (by decide))).exists
    obtain ⟨g, ha⟩ := key a
    obtain ⟨h, hb⟩ := key b
    refine ⟨h * g⁻¹, Function.Embedding.ext fun i ↦ ?_⟩
    rw [Function.Embedding.smul_apply, mul_smul]
    fin_cases i
    · simp [← ha.1, hb.1]
    · simp [← ha.2.1, hb.2.1]
    · simp [← ha.2.2, hb.2.2]

end OnePoint

namespace Matrix.ProjectiveSpecialLinearGroup

variable {K : Type*} [Field K] [DecidableEq K]

/-- The inclusion `PSL(2, K) → PGL(2, K)` is compatible with the actions on the projective line:
both act through the underlying matrix. -/
@[simp]
theorem toPGL_smul (g : PSL(2, K)) (c : OnePoint K) : toPGL g • c = g • c := by
  induction g using QuotientGroup.induction_on with
  | H g => simp

end Matrix.ProjectiveSpecialLinearGroup

namespace OnePoint

open Matrix

variable {K : Type*} [Field K] [DecidableEq K]

/-- If every invertible matrix is a determinant-one matrix times a scalar matrix, `PSL(2, K)`
acts sharply triply transitively on the projective line. -/
private theorem existsUnique_psl_smul_zero_one_infty_eq_of_factor
    (hK : ∀ g : GL (Fin 2) K, ∃ (s : SL(2, K)) (u : Kˣ),
      SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar (Fin 2) u = g)
    {x y z : OnePoint K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃! g : PSL(2, K), g • ((0 : K) : OnePoint K) = x ∧ g • ((1 : K) : OnePoint K) = y ∧
      g • (∞ : OnePoint K) = z := by
  obtain ⟨g, hg⟩ := exists_smul_zero_one_infty_eq hxy hxz hyz
  obtain ⟨s, u, rfl⟩ := hK g
  refine ⟨s, by simpa [mul_smul] using hg, fun g' hg' ↦ ?_⟩
  refine ProjectiveSpecialLinearGroup.toPGL_injective
    ((existsUnique_pgl_smul_zero_one_infty_eq hxy hxz hyz).unique ?_ ?_)
  · simpa only [ProjectiveSpecialLinearGroup.toPGL_smul] using hg'
  · simpa [mul_smul] using hg

/-- **Sharp triple transitivity of `PSL(2, K)` when units are squares.** If every unit of `K` is
a square, exactly one element of `PSL(2, K)` carries `0`, `1`, `∞` to three given pairwise
distinct points of the projective line. -/
theorem existsUnique_psl_smul_zero_one_infty_eq_of_roots
    (hK : ∀ r : Kˣ, ∃ k : Kˣ, k ^ 2 = r) {x y z : OnePoint K} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    ∃! g : PSL(2, K), g • ((0 : K) : OnePoint K) = x ∧ g • ((1 : K) : OnePoint K) = y ∧
      g • (∞ : OnePoint K) = z :=
  existsUnique_psl_smul_zero_one_infty_eq_of_factor
    (fun g ↦ GeneralLinearGroup.exists_toGL_mul_scalar_eq_of_roots g (by simpa using hK))
    hxy hxz hyz

/-- **Sharp triple transitivity of `PSL(2, K)` over an algebraically closed field.** Exactly one
element of `PSL(2, K)` carries `0`, `1`, `∞` to three given pairwise distinct points of the
projective line. For `K = ℂ` these are the automorphisms of the Riemann sphere normalized at
`(0, 1, ∞)`. -/
theorem existsUnique_psl_smul_zero_one_infty_eq [IsAlgClosed K] {x y z : OnePoint K}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃! g : PSL(2, K), g • ((0 : K) : OnePoint K) = x ∧ g • ((1 : K) : OnePoint K) = y ∧
      g • (∞ : OnePoint K) = z :=
  existsUnique_psl_smul_zero_one_infty_eq_of_factor
    GeneralLinearGroup.exists_toGL_mul_scalar_eq hxy hxz hyz

end OnePoint
