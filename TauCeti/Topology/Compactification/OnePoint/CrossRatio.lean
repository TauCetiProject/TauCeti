/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Compactification.OnePoint.MultipleTransitivity

/-!
# The cross ratio of four points of the projective line

Let `K` be a field. Möbius transformations act sharply triply transitively on the projective line
`OnePoint K` (`OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`), so for three pairwise distinct
points `a`, `b`, `c` there is exactly one element of `PGL(2, K)` carrying them to `0`, `1`, `∞`.
The *cross ratio* `OnePoint.crossRatio a b c d` is the image of a fourth point `d` under this
transformation. This pins the normalization `crossRatio 0 1 ∞ z = z`
(`OnePoint.crossRatio_zero_one_infty`). When `a`, `b`, `c` are not pairwise distinct the cross
ratio is defined to be `∞`.

For finite points the cross ratio is `(d - a) (b - c) / ((d - c) (b - a))`
(`OnePoint.crossRatio_coe`), and `(d - a) / (b - a)` when `c = ∞`
(`OnePoint.crossRatio_coe_coe_infty_coe`). It is invariant under Möbius transformations, and the
six transpositions of the four points act on it through the anharmonic group:
`t ↦ 1 - t`, `t ↦ t / (t - 1)` and `t ↦ t⁻¹`. For instance `crossRatio 1 0 ∞ z = 1 - z`.

Restricted to ordered quadruples of pairwise distinct points, `Fin 4 ↪ OnePoint K`, the cross
ratio is a complete invariant of the action of `PGL(2, K)`: two quadruples have the same cross
ratio exactly when a Möbius transformation carries one to the other
(`OnePoint.crossRatio_eq_crossRatio_iff`). It takes every value except `0`, `1` and `∞`, so it
identifies the orbit space with the thrice-punctured projective line
(`OnePoint.crossRatioEquiv`). For the Riemann sphere `OnePoint ℂ` this is the identification of
the moduli space `M(0, 4)` of four ordered distinct points on the sphere with
`OnePoint ℂ ∖ {0, 1, ∞}`; there `PSL(2, ℂ)` has the same orbits as `PGL(2, ℂ)`
(`OnePoint.crossRatio_eq_crossRatio_iff_psl`, and more generally whenever every unit of `K` is a
square).

## Main definitions

* `OnePoint.crossRatio a b c d`: the image of `d` under the Möbius transformation carrying `a`,
  `b`, `c` to `0`, `1`, `∞`.
* `OnePoint.crossRatioEquiv`: the orbits of `PGL(2, K)` on ordered quadruples of pairwise distinct
  points are in bijection with `OnePoint K ∖ {0, 1, ∞}`; its inverse sends `z` to the orbit of
  `OnePoint.zeroOneInftyEmbedding z`, the quadruple `(0, 1, ∞, z)`.

## Main results

* `OnePoint.crossRatio_eq_smul`: the defining property of the cross ratio.
* `OnePoint.crossRatio_smul`, `OnePoint.crossRatio_gl_smul`, `OnePoint.crossRatio_psl_smul`:
  invariance under Möbius transformations.
* `OnePoint.crossRatio_bijective`: for pairwise distinct `a`, `b`, `c`, the map
  `d ↦ crossRatio a b c d` is a bijection of the projective line.
* `OnePoint.crossRatio_eq_zero_iff`, `OnePoint.crossRatio_eq_one_iff`,
  `OnePoint.crossRatio_eq_infty_iff`: where the cross ratio takes the values `0`, `1`, `∞`, and
  `OnePoint.crossRatio_fourth_eq_first` and its two companions: its values at `a`, `b`, `c`.
* `OnePoint.crossRatio_coe`, `OnePoint.crossRatio_coe_coe_coe_infty`,
  `OnePoint.crossRatio_coe_coe_infty_coe`: formulas in affine coordinates.
* `OnePoint.crossRatio_swap_first_second` and its five companions: the action of the
  transpositions of the four points.
* `OnePoint.crossRatio_mem_compl`: the cross ratio of four distinct points is not `0`, `1`, `∞`.
* `OnePoint.crossRatio_eq_crossRatio_iff`: the cross ratio classifies ordered quadruples of
  distinct points up to Möbius transformations, and `OnePoint.crossRatio_eq_crossRatio_iff_psl`
  and `OnePoint.crossRatio_eq_crossRatio_iff_psl_of_roots` do the same for `PSL(2, K)` when every
  unit of `K` is a square.

## References

* Lars Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Chapter 3, §3.2 (the cross
  ratio). Ahlfors normalizes the second, third and fourth points to `1`, `0`, `∞` and evaluates at
  the first, so his `(z₁, z₂, z₃, z₄)` is `crossRatio z₃ z₂ z₄ z₁` here.
-/

public section

open scoped MatrixGroups

namespace OnePoint

open Matrix

variable {K : Type*} [Field K] [DecidableEq K]

/-- The **cross ratio** of four points of the projective line `OnePoint K`: the image of `d` under
the unique Möbius transformation carrying `a`, `b`, `c` to `0`, `1`, `∞`
(`OnePoint.crossRatio_eq_smul`), so that `crossRatio 0 1 ∞ z = z`. For finite points it is
`(d - a) (b - c) / ((d - c) (b - a))` (`OnePoint.crossRatio_coe`). If `a`, `b`, `c` are not
pairwise distinct, it is `∞` by convention. -/
noncomputable def crossRatio (a b c d : OnePoint K) : OnePoint K :=
  open scoped Classical in
  if h : a ≠ b ∧ a ≠ c ∧ b ≠ c then (exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2).choose • d
  else ∞

/-- **The defining property of the cross ratio.** If a Möbius transformation `g` carries `a`, `b`,
`c` to `0`, `1`, `∞`, then the cross ratio `crossRatio a b c d` is `g • d`. -/
theorem crossRatio_eq_smul {a b c : OnePoint K} (d : OnePoint K) {g : PGL(2, K)}
    (ha : g • a = (0 : K)) (hb : g • b = (1 : K)) (hc : g • c = ∞) :
    crossRatio a b c d = g • d := by
  have h := pairwise_ne_of_smul_eq_zero_one_infty ha hb hc
  rw [crossRatio, dite_eq_left h]
  obtain ⟨ha', hb', hc'⟩ := (exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2).choose_spec
  generalize (exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2).choose = k at ha' hb' hc' ⊢
  -- Both inverses carry `0`, `1`, `∞` to `a`, `b`, `c`, so they agree by sharp transitivity.
  have key := (existsUnique_pgl_smul_zero_one_infty_eq h.1 h.2.1 h.2.2).unique
    (y₁ := k⁻¹) (y₂ := g⁻¹)
    ⟨inv_smul_eq_iff.mpr ha'.symm, inv_smul_eq_iff.mpr hb'.symm, inv_smul_eq_iff.mpr hc'.symm⟩
    ⟨inv_smul_eq_iff.mpr ha.symm, inv_smul_eq_iff.mpr hb.symm, inv_smul_eq_iff.mpr hc.symm⟩
  rw [inv_inj.mp key]

/-- The defining property of the cross ratio, for a Möbius transformation given by an invertible
matrix. -/
theorem crossRatio_eq_gl_smul {a b c : OnePoint K} (d : OnePoint K) {g : GL (Fin 2) K}
    (ha : g • a = (0 : K)) (hb : g • b = (1 : K)) (hc : g • c = ∞) :
    crossRatio a b c d = g • d := by
  simpa using crossRatio_eq_smul d (g := ProjGenLinGroup.mk g) (by simpa using ha)
    (by simpa using hb) (by simpa using hc)

/-- If `a`, `b`, `c` are not pairwise distinct, the cross ratio is `∞` by convention. -/
theorem crossRatio_of_not_pairwise_ne {a b c : OnePoint K} (d : OnePoint K)
    (h : ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c)) : crossRatio a b c d = ∞ := by
  rw [crossRatio, dite_eq_right h]

/-- **Normalization of the cross ratio**: `crossRatio 0 1 ∞ z = z`. -/
@[simp]
theorem crossRatio_zero_one_infty (d : OnePoint K) :
    crossRatio ((0 : K) : OnePoint K) ((1 : K) : OnePoint K) ∞ d = d := by
  simpa using crossRatio_eq_smul d (g := 1) (by simp) (by simp) (by simp)

/-- **Möbius invariance of the cross ratio.** -/
@[simp]
theorem crossRatio_smul (g : PGL(2, K)) (a b c d : OnePoint K) :
    crossRatio (g • a) (g • b) (g • c) (g • d) = crossRatio a b c d := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨k, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2
    rw [crossRatio_eq_smul d ha hb hc, crossRatio_eq_smul (g := k * g⁻¹) (g • d)
      (by rwa [mul_smul, inv_smul_smul]) (by rwa [mul_smul, inv_smul_smul])
      (by rwa [mul_smul, inv_smul_smul]), mul_smul, inv_smul_smul]
  · rw [crossRatio_of_not_pairwise_ne d h, crossRatio_of_not_pairwise_ne]
    simpa using h

/-- Möbius invariance of the cross ratio, for a transformation given by an invertible matrix. -/
@[simp]
theorem crossRatio_gl_smul (g : GL (Fin 2) K) (a b c d : OnePoint K) :
    crossRatio (g • a) (g • b) (g • c) (g • d) = crossRatio a b c d := by
  simpa using crossRatio_smul (ProjGenLinGroup.mk g) a b c d

/-- Möbius invariance of the cross ratio, for a transformation in `PSL(2, K)`. -/
@[simp]
theorem crossRatio_psl_smul (g : PSL(2, K)) (a b c d : OnePoint K) :
    crossRatio (g • a) (g • b) (g • c) (g • d) = crossRatio a b c d := by
  simpa [ProjectiveSpecialLinearGroup.toPGL_smul] using
    crossRatio_smul (ProjectiveSpecialLinearGroup.toPGL g) a b c d

/-- For pairwise distinct `a`, `b`, `c`, the cross ratio `d ↦ crossRatio a b c d` is a bijection
of the projective line: it is a Möbius transformation. -/
theorem crossRatio_bijective {a b c : OnePoint K} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    Function.Bijective (crossRatio a b c) := by
  obtain ⟨g, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2
  have heq : crossRatio a b c = (g • ·) := funext fun d ↦ crossRatio_eq_smul d ha hb hc
  rw [heq]
  exact MulAction.bijective g

/-- The cross ratio `crossRatio a b c d` is `0` exactly when `a`, `b`, `c` are pairwise distinct
and `d = a`. -/
@[simp]
theorem crossRatio_eq_zero_iff {a b c d : OnePoint K} :
    crossRatio a b c d = (0 : K) ↔ (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧ d = a := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨g, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2
    rw [crossRatio_eq_smul d ha hb hc, ← ha, smul_left_cancel_iff]
    exact ⟨fun hd ↦ ⟨h, hd⟩, And.right⟩
  · simp [crossRatio_of_not_pairwise_ne d h, h]

/-- The cross ratio `crossRatio a b c d` is `1` exactly when `a`, `b`, `c` are pairwise distinct
and `d = b`. -/
@[simp]
theorem crossRatio_eq_one_iff {a b c d : OnePoint K} :
    crossRatio a b c d = (1 : K) ↔ (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧ d = b := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨g, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2
    rw [crossRatio_eq_smul d ha hb hc, ← hb, smul_left_cancel_iff]
    exact ⟨fun hd ↦ ⟨h, hd⟩, And.right⟩
  · simp [crossRatio_of_not_pairwise_ne d h, h]

/-- The cross ratio `crossRatio a b c d` is `∞` exactly when `a`, `b`, `c` are not pairwise
distinct or `d = c`. -/
@[simp]
theorem crossRatio_eq_infty_iff {a b c d : OnePoint K} :
    crossRatio a b c d = ∞ ↔ ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨ d = c := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨g, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty h.1 h.2.1 h.2.2
    rw [crossRatio_eq_smul d ha hb hc, ← hc, smul_left_cancel_iff]
    simp [h]
  · simp [crossRatio_of_not_pairwise_ne d h, h]

/-- The cross ratio at the first point is `0`. -/
@[simp]
theorem crossRatio_fourth_eq_first {a b c : OnePoint K} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : crossRatio a b c a = (0 : K) :=
  crossRatio_eq_zero_iff.mpr ⟨⟨hab, hac, hbc⟩, rfl⟩

/-- The cross ratio at the second point is `1`. -/
@[simp]
theorem crossRatio_fourth_eq_second {a b c : OnePoint K} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : crossRatio a b c b = (1 : K) :=
  crossRatio_eq_one_iff.mpr ⟨⟨hab, hac, hbc⟩, rfl⟩

/-- The cross ratio at the third point is `∞`. -/
@[simp]
theorem crossRatio_fourth_eq_third (a b c : OnePoint K) : crossRatio a b c c = ∞ :=
  crossRatio_eq_infty_iff.mpr (.inr rfl)

/-! ### Formulas in affine coordinates -/

/-- The Möbius transformation `z ↦ (b - c) (z - a) / ((b - a) (z - c))`, which carries `a`, `b`,
`c` to `0`, `1`, `∞`. -/
private def normalizingGL {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![b - c, -(a * (b - c)); b - a, -(c * (b - a))] <| by
    rw [det_fin_two_of]
    have : (b - c) * (b - a) * (a - c) ≠ 0 := by
      simp [sub_ne_zero, hab.symm, hac, hbc]
    convert this using 1
    ring

private theorem normalizingGL_smul_coe {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {z : K} (hz : z ≠ c) :
    normalizingGL hab hac hbc • (z : OnePoint K) =
      ((b - c) * (z - a) / ((b - a) * (z - c)) : K) := by
  have hden : (b - a) * z + -(c * (b - a)) ≠ 0 := by
    rw [show (b - a) * z + -(c * (b - a)) = (b - a) * (z - c) by ring]
    simp [sub_ne_zero, hab.symm, hz]
  rw [smul_some_eq_ite, ite_eq_right (by simpa [normalizingGL] using hden)]
  congr 1
  simp only [normalizingGL, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_fin_one, empty_val']
  ring

private theorem normalizingGL_smul_coe_self {a b c : K} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : normalizingGL hab hac hbc • (c : OnePoint K) = ∞ := by
  rw [smul_some_eq_infty_iff]
  simp only [normalizingGL, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_fin_one, empty_val']
  ring

private theorem normalizingGL_smul_infty {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    normalizingGL hab hac hbc • (∞ : OnePoint K) = ((b - c) / (b - a) : K) := by
  rw [smul_infty_eq_ite, ite_eq_right (by simpa [normalizingGL, sub_eq_zero] using hab.symm)]
  simp [normalizingGL]

/-- **The cross ratio of four finite points**: `(d - a) (b - c) / ((d - c) (b - a))`. -/
theorem crossRatio_coe {a b c d : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c) :
    crossRatio (a : OnePoint K) b c d = ((d - a) * (b - c) / ((d - c) * (b - a)) : K) := by
  rw [crossRatio_eq_gl_smul (g := normalizingGL hab hac hbc) _ ?_ ?_
    (normalizingGL_smul_coe_self hab hac hbc), normalizingGL_smul_coe hab hac hbc hdc]
  · congr 1
    ring
  · rw [normalizingGL_smul_coe hab hac hbc hac]
    simp
  · rw [normalizingGL_smul_coe hab hac hbc hbc]
    congr 1
    field_simp [sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hbc]

/-- The cross ratio of three finite points and `∞`: `(b - c) / (b - a)`. -/
theorem crossRatio_coe_coe_coe_infty {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    crossRatio (a : OnePoint K) b c ∞ = ((b - c) / (b - a) : K) := by
  rw [crossRatio_eq_gl_smul (g := normalizingGL hab hac hbc) _ ?_ ?_
    (normalizingGL_smul_coe_self hab hac hbc), normalizingGL_smul_infty hab hac hbc]
  · rw [normalizingGL_smul_coe hab hac hbc hac]
    simp
  · rw [normalizingGL_smul_coe hab hac hbc hbc]
    congr 1
    field_simp [sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hbc]

/-- The cross ratio of two finite points, `∞` and a finite point: `(d - a) / (b - a)`. -/
theorem crossRatio_coe_coe_infty_coe {a b : K} (hab : a ≠ b) (d : K) :
    crossRatio (a : OnePoint K) b ∞ d = ((d - a) / (b - a) : K) := by
  have hdet : det !![1, -a; 0, b - a] ≠ 0 := by
    simp [det_fin_two_of, sub_eq_zero, hab.symm]
  have hsmul (z : K) : GeneralLinearGroup.mkOfDetNeZero _ hdet • (z : OnePoint K) =
      ((z - a) / (b - a) : K) := by
    rw [smul_some_eq_ite, ite_eq_right (by simpa [sub_eq_zero] using hab.symm)]
    simp [sub_eq_add_neg]
  rw [crossRatio_eq_gl_smul (g := GeneralLinearGroup.mkOfDetNeZero _ hdet) _ (by simp [hsmul])
    (by simp [hsmul, sub_ne_zero.mpr hab.symm]) (smul_infty_eq_self_iff.mpr (by simp)), hsmul]

/-! ### The anharmonic group

The six transpositions of the four points `a`, `b`, `c`, `d` act on a finite cross ratio `t` by
`t ↦ 1 - t` (exchanging `a, b` or `c, d`), `t ↦ t / (t - 1)` (exchanging `b, c` or `a, d`) and
`t ↦ t⁻¹` (exchanging `a, c` or `b, d`). Since the transpositions generate the symmetric group,
these laws determine the cross ratio of every reordering. Each law follows by moving `a`, `b`, `c`,
`d` to `0`, `1`, `∞`, `t` and evaluating there. -/

/-- If the cross ratio is the finite point `t`, a Möbius transformation carries the four points to
`0`, `1`, `∞`, `t`. -/
private theorem exists_smul_eq_of_crossRatio_eq_coe {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) :
    ∃ g : PGL(2, K), g • a = (0 : K) ∧ g • b = (1 : K) ∧ g • c = ∞ ∧ g • d = t := by
  have hne : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    by_contra hn
    rw [crossRatio_of_not_pairwise_ne d hn] at h
    exact infty_ne_coe t h
  obtain ⟨g, ha, hb, hc⟩ := exists_pgl_smul_eq_zero_one_infty hne.1 hne.2.1 hne.2.2
  exact ⟨g, ha, hb, hc, (crossRatio_eq_smul d ha hb hc).symm.trans h⟩

/-- Exchanging the first two points replaces the cross ratio `t` by `1 - t`. -/
theorem crossRatio_swap_first_second {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) : crossRatio b a c d = ((1 - t : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd, crossRatio_coe_coe_infty_coe one_ne_zero]
  congr 1
  ring

/-- Exchanging the last two points replaces the cross ratio `t` by `1 - t`. -/
theorem crossRatio_swap_third_fourth {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    crossRatio a b d c = ((1 - t : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd,
    crossRatio_coe_coe_coe_infty zero_ne_one (Ne.symm h0) (Ne.symm h1)]
  simp

/-- Exchanging the middle two points replaces the cross ratio `t` by `t / (t - 1)`. -/
theorem crossRatio_swap_second_third {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) (h1 : t ≠ 1) :
    crossRatio a c b d = ((t / (t - 1) : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd]
  -- The transformation `z ↦ z / (z - 1)` carries `0`, `∞`, `1` to `0`, `1`, `∞`.
  have hdet : det !![(1 : K), 0; 1, -1] ≠ 0 := by simp [det_fin_two_of]
  rw [crossRatio_eq_gl_smul (g := GeneralLinearGroup.mkOfDetNeZero _ hdet) _
    (by simp [smul_some_eq_ite]) (by simp [smul_infty_eq_ite]) (by simp),
    smul_some_eq_ite, ite_eq_right (by simpa [← sub_eq_add_neg, sub_eq_zero] using h1)]
  simp [sub_eq_add_neg]

/-- Exchanging the first and last points replaces the cross ratio `t` by `t / (t - 1)`. -/
theorem crossRatio_swap_first_fourth {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) (h1 : t ≠ 1) :
    crossRatio d b c a = ((t / (t - 1) : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd, crossRatio_coe_coe_infty_coe h1]
  congr 1
  rw [← neg_div_neg_eq]
  ring

/-- Exchanging the first and third points replaces the cross ratio `t` by `t⁻¹`. -/
theorem crossRatio_swap_first_third {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) (h0 : t ≠ 0) :
    crossRatio c b a d = ((t⁻¹ : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd]
  -- The transformation `z ↦ z⁻¹` carries `∞`, `1`, `0` to `0`, `1`, `∞`.
  have hdet : det !![(0 : K), 1; 1, 0] ≠ 0 := by simp [det_fin_two_of]
  rw [crossRatio_eq_gl_smul (g := GeneralLinearGroup.mkOfDetNeZero _ hdet) _
    (by simp [smul_infty_eq_ite]) (by simp [smul_some_eq_ite]) (by simp),
    smul_some_eq_ite, ite_eq_right (by simpa using h0)]
  simp

/-- Exchanging the second and fourth points replaces the cross ratio `t` by `t⁻¹`. -/
theorem crossRatio_swap_second_fourth {a b c d : OnePoint K} {t : K}
    (h : crossRatio a b c d = t) (h0 : t ≠ 0) :
    crossRatio a d c b = ((t⁻¹ : K) : OnePoint K) := by
  obtain ⟨g, ha, hb, hc, hd⟩ := exists_smul_eq_of_crossRatio_eq_coe h
  rw [← crossRatio_smul g, ha, hb, hc, hd, crossRatio_coe_coe_infty_coe (Ne.symm h0)]
  simp

/-! ### Ordered quadruples of distinct points -/

/-- The cross ratio of four pairwise distinct points is neither `0`, `1` nor `∞`. -/
theorem crossRatio_mem_compl (x : Fin 4 ↪ OnePoint K) :
    crossRatio (x 0) (x 1) (x 2) (x 3) ∈
      ({((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞}ᶜ : Set (OnePoint K)) := by
  simp

/-- **The cross ratio classifies ordered quadruples of distinct points up to Möbius
transformations**: two quadruples have the same cross ratio exactly when an element of
`PGL(2, K)` carries one to the other. -/
theorem crossRatio_eq_crossRatio_iff (x y : Fin 4 ↪ OnePoint K) :
    crossRatio (x 0) (x 1) (x 2) (x 3) = crossRatio (y 0) (y 1) (y 2) (y 3) ↔
      ∃ g : PGL(2, K), g • x = y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ by simp [← hg, Function.Embedding.smul_apply]⟩
  obtain ⟨g, hx0, hx1, hx2⟩ :=
    exists_pgl_smul_eq_zero_one_infty (x := x 0) (y := x 1) (z := x 2) (by simp) (by simp) (by simp)
  obtain ⟨k, hy0, hy1, hy2⟩ :=
    exists_pgl_smul_eq_zero_one_infty (x := y 0) (y := y 1) (z := y 2) (by simp) (by simp) (by simp)
  rw [crossRatio_eq_smul _ hx0 hx1 hx2, crossRatio_eq_smul _ hy0 hy1 hy2] at h
  -- Both quadruples are carried to `0`, `1`, `∞` and their common cross ratio.
  refine ⟨k⁻¹ * g, Function.Embedding.ext fun i ↦ ?_⟩
  rw [Function.Embedding.smul_apply, mul_smul, inv_smul_eq_iff]
  fin_cases i
  · exact hx0.trans hy0.symm
  · exact hx1.trans hy1.symm
  · exact hx2.trans hy2.symm
  · exact h

/-- If every invertible matrix is a determinant-one matrix times a scalar matrix, the cross ratio
classifies ordered quadruples of distinct points up to the action of `PSL(2, K)`. -/
private theorem crossRatio_eq_crossRatio_iff_psl_of_factor
    (hK : ∀ g : GL (Fin 2) K, ∃ (s : SL(2, K)) (u : Kˣ),
      SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar (Fin 2) u = g)
    (x y : Fin 4 ↪ OnePoint K) :
    crossRatio (x 0) (x 1) (x 2) (x 3) = crossRatio (y 0) (y 1) (y 2) (y 3) ↔
      ∃ g : PSL(2, K), g • x = y := by
  rw [crossRatio_eq_crossRatio_iff]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ⟨ProjectiveSpecialLinearGroup.toPGL g, ?_⟩⟩
  · obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective g
    obtain ⟨s, z, rfl⟩ := hK h
    refine ⟨s, Function.Embedding.ext fun i ↦ ?_⟩
    simpa [Function.Embedding.smul_apply, mul_smul] using congr($hg i)
  · ext i
    simpa [Function.Embedding.smul_apply, ProjectiveSpecialLinearGroup.toPGL_smul] using
      congr($hg i)

/-- If every unit of `K` is a square, the cross ratio classifies ordered quadruples of distinct
points up to the action of `PSL(2, K)`. -/
theorem crossRatio_eq_crossRatio_iff_psl_of_roots (hK : ∀ r : Kˣ, ∃ k : Kˣ, k ^ 2 = r)
    (x y : Fin 4 ↪ OnePoint K) :
    crossRatio (x 0) (x 1) (x 2) (x 3) = crossRatio (y 0) (y 1) (y 2) (y 3) ↔
      ∃ g : PSL(2, K), g • x = y :=
  crossRatio_eq_crossRatio_iff_psl_of_factor
    (fun g ↦ GeneralLinearGroup.exists_toGL_mul_scalar_eq_of_roots g (by simpa using hK)) x y

/-- Over an algebraically closed field, such as `ℂ`, the cross ratio classifies ordered quadruples
of distinct points up to the action of `PSL(2, K)`. -/
theorem crossRatio_eq_crossRatio_iff_psl [IsAlgClosed K] (x y : Fin 4 ↪ OnePoint K) :
    crossRatio (x 0) (x 1) (x 2) (x 3) = crossRatio (y 0) (y 1) (y 2) (y 3) ↔
      ∃ g : PSL(2, K), g • x = y :=
  crossRatio_eq_crossRatio_iff_psl_of_factor GeneralLinearGroup.exists_toGL_mul_scalar_eq x y

/-- The ordered quadruple `0`, `1`, `∞`, `z` for a point `z` other than `0`, `1`, `∞`. -/
def zeroOneInftyEmbedding
    (z : ({((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞}ᶜ : Set (OnePoint K))) :
    Fin 4 ↪ OnePoint K :=
  ⟨![((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞, z], by
    obtain ⟨z, hz⟩ := z
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

omit [DecidableEq K] in
/-- The entries of the quadruple `(0, 1, ∞, z)`. -/
@[simp]
theorem zeroOneInftyEmbedding_apply
    (z : ({((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞}ᶜ : Set (OnePoint K))) (i : Fin 4) :
    zeroOneInftyEmbedding z i = ![((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞, z] i :=
  (rfl)

/-- **The moduli space of four ordered distinct points on the projective line.** The cross ratio
identifies the orbits of `PGL(2, K)` on ordered quadruples of pairwise distinct points of
`OnePoint K` with the points other than `0`, `1`, `∞`; the inverse sends `z` to the orbit of
`(0, 1, ∞, z)`. For `K = ℂ` this is `M(0, 4) = OnePoint ℂ ∖ {0, 1, ∞}`. -/
noncomputable def crossRatioEquiv :
    MulAction.orbitRel.Quotient PGL(2, K) (Fin 4 ↪ OnePoint K) ≃
      ({((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞}ᶜ : Set (OnePoint K)) where
  toFun := Quotient.lift (fun x ↦ ⟨crossRatio (x 0) (x 1) (x 2) (x 3), crossRatio_mem_compl x⟩)
    fun x y hxy ↦ Subtype.ext ((crossRatio_eq_crossRatio_iff y x).mpr
      (MulAction.mem_orbit_iff.mp hxy)).symm
  invFun z := Quotient.mk'' (zeroOneInftyEmbedding z)
  left_inv q := by
    induction q using Quotient.inductionOn' with | h x =>
    refine Quotient.sound' (MulAction.mem_orbit_iff.mpr ((crossRatio_eq_crossRatio_iff x _).mp ?_))
    simp [zeroOneInftyEmbedding]
  right_inv z := Subtype.ext (by simp [zeroOneInftyEmbedding])

/-- The orbit of an ordered quadruple of distinct points corresponds to its cross ratio. -/
@[simp]
theorem coe_crossRatioEquiv_mk (x : Fin 4 ↪ OnePoint K) :
    (crossRatioEquiv (Quotient.mk'' x : MulAction.orbitRel.Quotient PGL(2, K) _) : OnePoint K) =
      crossRatio (x 0) (x 1) (x 2) (x 3) :=
  (rfl)

/-- A point other than `0`, `1`, `∞` corresponds to the orbit of the quadruple `(0, 1, ∞, z)`. -/
@[simp]
theorem crossRatioEquiv_symm_apply
    (z : ({((0 : K) : OnePoint K), ((1 : K) : OnePoint K), ∞}ᶜ : Set (OnePoint K))) :
    (crossRatioEquiv (K := K)).symm z = Quotient.mk'' (zeroOneInftyEmbedding z) :=
  (rfl)

end OnePoint
