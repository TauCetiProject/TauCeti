/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# The Wirtinger inequality for a compatible triple

Let `ω` be a symplectic form compatible with an almost complex structure `J`, and let
`g(v, w) = ω(v, J w)` be the associated metric. The `g`-area of the parallelogram spanned by two
vectors is the norm of their wedge product,
`|v ∧ w|_g = √(g(v, v) g(w, w) - g(v, w)²)`.

The degree-two **Wirtinger inequality** says that `ω` calibrates `g`:
`ω(v, w) ≤ |v ∧ w|_g`, with equality for linearly independent `v` and `w` exactly when
`w = a v + b J v` with `b > 0`, that is, when the oriented plane `(v, w)` is a `J`-complex line
carrying its complex orientation. The proof is a Cauchy--Schwarz argument: `ω(v, w) = g(J v, w)`,
the vector `J v` is `g`-orthogonal to `v` and has the same length, and the component `w⊥` of `w`
orthogonal to the plane spanned by `v` and `J v` contributes nothing to `ω(v, w)` but increases
`|v ∧ w|_g²` by `g(v, v) g(w⊥, w⊥)`. In fact `g(v, w)² + ω(v, w)² ≤ g(v, v) g(w, w)`.

The arithmetic-geometric mean inequality gives the second link of the chain
`ω(v, w) ≤ |v ∧ w|_g ≤ (g(v, v) + g(w, w)) / 2`; the second inequality is an equality exactly
when the pair `(v, w)` is conformal (`g(v, v) = g(w, w)` and `g(v, w) = 0`), and the two together
are equalities exactly when `w = J v`. Applied to the partial derivatives of a map from a surface,
this is the pointwise chain `energy density ≥ area density ≥ symplectic area density` of
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Area`, where the equality case of the whole
chain is `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm_iff`.

Everything is pointwise linear algebra: no integrability of `J` or closedness of `ω` is involved.

## Main declarations

* `TauCeti.SymplecticForm.wedgeNorm`: the `g`-norm `|v ∧ w|_g` of a wedge of two vectors.
* `TauCeti.SymplecticForm.Compatible.sq_associatedBilinForm_add_sq_le`:
  `g(v, w)² + ω(v, w)² ≤ g(v, v) g(w, w)`.
* `TauCeti.SymplecticForm.Compatible.apply_le_wedgeNorm`: the Wirtinger inequality
  `ω(v, w) ≤ |v ∧ w|_g`.
* `TauCeti.SymplecticForm.Compatible.apply_eq_wedgeNorm_iff_of_linearIndependent`: its equality
  case `w = a v + b J v` with `b > 0`.
* `TauCeti.SymplecticForm.Compatible.two_mul_wedgeNorm_le`:
  `2 |v ∧ w|_g ≤ g(v, v) + g(w, w)`, with equality case
  `TauCeti.SymplecticForm.Compatible.two_mul_wedgeNorm_eq_iff` for conformal pairs.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Lemma 2.2.1.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The norm `|v ∧ w|_g` of the wedge of two vectors for the associated metric
`g = ω(·, J ·)`: the square root of the Gram determinant `g(v, v) g(w, w) - g(v, w)²`. For a
compatible pair this is the `g`-area of the parallelogram spanned by `v` and `w`. -/
noncomputable def wedgeNorm (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) : ℝ :=
  √(ω.associatedBilinForm J v v * ω.associatedBilinForm J w w -
    ω.associatedBilinForm J v w ^ 2)

/-- The wedge norm is the square root of the Gram determinant of the associated metric. -/
lemma wedgeNorm_def (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    ω.wedgeNorm J v w =
      √(ω.associatedBilinForm J v v * ω.associatedBilinForm J w w -
        ω.associatedBilinForm J v w ^ 2) :=
  (rfl)

/-- The wedge norm is nonnegative. -/
lemma wedgeNorm_nonneg (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    0 ≤ ω.wedgeNorm J v w :=
  Real.sqrt_nonneg _

/-- The wedge of a vector with itself has norm zero. -/
@[simp]
lemma wedgeNorm_self (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v : V) :
    ω.wedgeNorm J v v = 0 := by
  simp [wedgeNorm_def, sq]

/-- The wedge of the zero vector with any vector has norm zero. -/
@[simp]
lemma wedgeNorm_zero_left (ω : SymplecticForm V) (J : AlmostComplexStructure V) (w : V) :
    ω.wedgeNorm J 0 w = 0 := by
  simp [wedgeNorm_def]

/-- The wedge of any vector with the zero vector has norm zero. -/
@[simp]
lemma wedgeNorm_zero_right (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v : V) :
    ω.wedgeNorm J v 0 = 0 := by
  simp [wedgeNorm_def]

/-- The wedge norm is symmetric for a `J`-invariant form, whose associated metric is
symmetric. -/
lemma Invariant.wedgeNorm_comm (hinv : ω.Invariant J) (v w : V) :
    ω.wedgeNorm J v w = ω.wedgeNorm J w v := by
  rw [wedgeNorm_def, wedgeNorm_def, mul_comm, hinv.associatedBilinForm_isSymm.eq v w]

/-- The key identity behind the Wirtinger inequality: with `c = g(v, v)`, the vector
`r = c w - g(v, w) v - ω(v, w) J v` is `w` with its component along the plane spanned by `v` and
`J v` removed (and rescaled by `c`), and `g(r, r) = c (c g(w, w) - g(v, w)² - ω(v, w)²)`. -/
private lemma Invariant.associatedBilinForm_remainder (hinv : ω.Invariant J) (v w : V) :
    ω.associatedBilinForm J
        (ω.associatedBilinForm J v v • w - ω.associatedBilinForm J v w • v - ω v w • J v)
        (ω.associatedBilinForm J v v • w - ω.associatedBilinForm J v w • v - ω v w • J v) =
      ω.associatedBilinForm J v v *
        (ω.associatedBilinForm J v v * ω.associatedBilinForm J w w -
          ω.associatedBilinForm J v w ^ 2 - ω v w ^ 2) := by
  set g := ω.associatedBilinForm J
  have hwv : g w v = g v w := hinv.associatedBilinForm_apply_swap w v
  have hJvw : g (J v) w = ω v w := hinv.associatedBilinForm_apply_left_apply v w
  have hwJv : g w (J v) = ω v w := by
    rw [← hJvw]; exact hinv.associatedBilinForm_apply_swap w (J v)
  have hvJv : g v (J v) = 0 := by simp [g]
  have hJvv : g (J v) v = 0 := by
    rw [← hvJv]; exact hinv.associatedBilinForm_apply_swap (J v) v
  have hJvJv : g (J v) (J v) = g v v := ω.associatedBilinForm_apply_apply_self_eq J v
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hwv, hJvw, hwJv, hvJv, hJvv, hJvJv]
  ring

/-- **Cauchy--Schwarz along a complex line.** For a compatible pair, the squares of the
components `g(v, w)` and `ω(v, w) = g(J v, w)` of `w` along the orthogonal pair `v`, `J v` add up
to at most `g(v, v) g(w, w)`. -/
theorem Compatible.sq_associatedBilinForm_add_sq_le (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J v w ^ 2 + ω v w ^ 2 ≤
      ω.associatedBilinForm J v v * ω.associatedBilinForm J w w := by
  have hid := h.invariant.associatedBilinForm_remainder v w
  rcases (h.associatedBilinForm_self_nonneg v).eq_or_lt with hv | hv
  · have hv0 : v = 0 := h.associatedBilinForm_self_eq_zero.mp hv.symm
    simp [hv0]
  · have hr := h.associatedBilinForm_self_nonneg
      (ω.associatedBilinForm J v v • w - ω.associatedBilinForm J v w • v - ω v w • J v)
    rw [hid] at hr
    nlinarith [(mul_nonneg_iff_of_pos_left hv).mp hr]

/-- For a compatible pair, the square of the wedge norm is the Gram determinant
`g(v, v) g(w, w) - g(v, w)²`. -/
lemma Compatible.sq_wedgeNorm (h : ω.Compatible J) (v w : V) :
    ω.wedgeNorm J v w ^ 2 =
      ω.associatedBilinForm J v v * ω.associatedBilinForm J w w -
        ω.associatedBilinForm J v w ^ 2 := by
  rw [wedgeNorm_def, Real.sq_sqrt (sub_nonneg.mpr <| (ω.associatedBilinForm J).apply_sq_le_of_symm
    h.associatedBilinForm_self_nonneg
    (LinearMap.BilinForm.isSymm_iff.mp h.associatedBilinForm_isSymm) v w)]

/-- For a compatible pair, the wedge norm is positive exactly for linearly independent pairs. -/
theorem Compatible.wedgeNorm_pos_iff (h : ω.Compatible J) (v w : V) :
    0 < ω.wedgeNorm J v w ↔ LinearIndependent ℝ ![v, w] := by
  rw [wedgeNorm_def, Real.sqrt_pos, sub_pos]
  exact (ω.associatedBilinForm J).apply_sq_lt_iff_linearIndependent_of_symm
    (fun _ hx => h.associated_pos hx)
    (LinearMap.BilinForm.isSymm_iff.mp h.associatedBilinForm_isSymm) v w

/-- The wedge of `v` with `J v` has norm `g(v, v)`: the pair `(v, J v)` is `g`-orthogonal and its
two vectors have the same length. -/
lemma Tames.wedgeNorm_apply_self (h : ω.Tames J) (v : V) :
    ω.wedgeNorm J v (J v) = ω.associatedBilinForm J v v := by
  have hvJv : ω.associatedBilinForm J v (J v) = 0 := by simp
  rw [wedgeNorm_def, associatedBilinForm_apply_apply_self_eq, hvJv, ← sq, zero_pow two_ne_zero,
    sub_zero,
    Real.sqrt_sq (associatedBilinForm_self_nonneg ((ω.tames_iff_associated_pos J).mp h) v)]

/-- For a compatible pair, `|ω(v, w)|` is at most the wedge norm `|v ∧ w|_g`. -/
theorem Compatible.abs_apply_le_wedgeNorm (h : ω.Compatible J) (v w : V) :
    |ω v w| ≤ ω.wedgeNorm J v w := by
  rw [wedgeNorm_def, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  linarith [h.sq_associatedBilinForm_add_sq_le v w]

/-- **The Wirtinger inequality.** A symplectic form compatible with `J` calibrates the associated
metric: `ω(v, w) ≤ |v ∧ w|_g`. -/
theorem Compatible.apply_le_wedgeNorm (h : ω.Compatible J) (v w : V) :
    ω v w ≤ ω.wedgeNorm J v w :=
  (le_abs_self _).trans (h.abs_apply_le_wedgeNorm v w)

/-- The equality case of the Wirtinger inequality for a nonzero first vector: `ω(v, w)` equals
`|v ∧ w|_g` exactly when `w` lies in the closed half of the complex line through `v` on the side
of `J v`, that is, `w = a v + b J v` with `b ≥ 0`. -/
theorem Compatible.apply_eq_wedgeNorm_iff (h : ω.Compatible J) {v : V} (hv : v ≠ 0) (w : V) :
    ω v w = ω.wedgeNorm J v w ↔ ∃ a b : ℝ, 0 ≤ b ∧ w = a • v + b • J v := by
  have hc : 0 < ω.associatedBilinForm J v v := h.associated_pos hv
  constructor
  · intro heq
    -- Equality forces the remainder `r = c w - g(v, w) v - ω(v, w) J v` to vanish.
    have hsq : ω v w ^ 2 = ω.associatedBilinForm J v v * ω.associatedBilinForm J w w -
        ω.associatedBilinForm J v w ^ 2 := by
      rw [heq, h.sq_wedgeNorm]
    have hr0 := h.associatedBilinForm_self_eq_zero.mp <| by
      rw [h.invariant.associatedBilinForm_remainder, hsq, sub_self, mul_zero]
    rw [sub_sub, sub_eq_zero] at hr0
    refine ⟨ω.associatedBilinForm J v w / ω.associatedBilinForm J v v,
      ω v w / ω.associatedBilinForm J v v, div_nonneg (heq ▸ ω.wedgeNorm_nonneg J v w) hc.le, ?_⟩
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← hr0, smul_smul,
      inv_mul_cancel₀ hc.ne', one_smul]
  · rintro ⟨a, b, hb, rfl⟩
    have hvJv : ω.associatedBilinForm J v (J v) = 0 := by simp
    have hJvv : ω.associatedBilinForm J (J v) v = 0 :=
      (h.associatedBilinForm_isSymm.eq (J v) v).trans hvJv
    have hJvJv := ω.associatedBilinForm_apply_apply_self_eq J v
    have hω : ω v (a • v + b • J v) = b * ω.associatedBilinForm J v v := by
      simp only [map_add, map_smul, smul_eq_mul,
        ω.self_eq_zero, associatedBilinForm_apply]
      ring
    rw [hω, ← sq_eq_sq₀ (mul_nonneg hb hc.le) (ω.wedgeNorm_nonneg J _ _), h.sq_wedgeNorm]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hvJv, hJvv, hJvJv]
    ring

/-- **The equality case of the Wirtinger inequality.** For linearly independent `v` and `w`,
`ω(v, w) = |v ∧ w|_g` exactly when `w = a v + b J v` with `b > 0`: the oriented plane `(v, w)` is a
`J`-complex line with its complex orientation. -/
theorem Compatible.apply_eq_wedgeNorm_iff_of_linearIndependent (h : ω.Compatible J) {v w : V}
    (hvw : LinearIndependent ℝ ![v, w]) :
    ω v w = ω.wedgeNorm J v w ↔ ∃ a b : ℝ, 0 < b ∧ w = a • v + b • J v := by
  have hv : v ≠ 0 := by simpa using hvw.ne_zero 0
  rw [h.apply_eq_wedgeNorm_iff hv]
  refine ⟨fun ⟨a, b, hb, hw⟩ => ⟨a, b, hb.lt_of_ne ?_, hw⟩,
    fun ⟨a, b, hb, hw⟩ => ⟨a, b, hb.le, hw⟩⟩
  rintro rfl
  rw [LinearIndependent.pair_iff] at hvw
  have := hvw a (-1) (by simp [hw])
  norm_num at this

/-- The arithmetic-geometric mean identity behind `2 |v ∧ w|_g ≤ g(v, v) + g(w, w)`. -/
private lemma Compatible.sq_add_sub_four_mul_sq_wedgeNorm (h : ω.Compatible J) (v w : V) :
    (ω.associatedBilinForm J v v + ω.associatedBilinForm J w w) ^ 2 - 4 * ω.wedgeNorm J v w ^ 2 =
      (ω.associatedBilinForm J v v - ω.associatedBilinForm J w w) ^ 2 +
        4 * ω.associatedBilinForm J v w ^ 2 := by
  rw [h.sq_wedgeNorm]
  ring

/-- **Area is at most energy.** For a compatible pair,
`2 |v ∧ w|_g ≤ g(v, v) + g(w, w)`. -/
theorem Compatible.two_mul_wedgeNorm_le (h : ω.Compatible J) (v w : V) :
    2 * ω.wedgeNorm J v w ≤ ω.associatedBilinForm J v v + ω.associatedBilinForm J w w := by
  have hid := h.sq_add_sub_four_mul_sq_wedgeNorm v w
  have hsum := add_nonneg (h.associatedBilinForm_self_nonneg v)
    (h.associatedBilinForm_self_nonneg w)
  have hx := ω.wedgeNorm_nonneg J v w
  nlinarith [hx, sq_nonneg (ω.associatedBilinForm J v v - ω.associatedBilinForm J w w),
    sq_nonneg (ω.associatedBilinForm J v w)]

/-- The equality case of `2 |v ∧ w|_g ≤ g(v, v) + g(w, w)`: it holds exactly for conformal pairs,
those with `g(v, v) = g(w, w)` and `g(v, w) = 0`. -/
theorem Compatible.two_mul_wedgeNorm_eq_iff (h : ω.Compatible J) (v w : V) :
    2 * ω.wedgeNorm J v w = ω.associatedBilinForm J v v + ω.associatedBilinForm J w w ↔
      ω.associatedBilinForm J v v = ω.associatedBilinForm J w w ∧
        ω.associatedBilinForm J v w = 0 := by
  have hid := h.sq_add_sub_four_mul_sq_wedgeNorm v w
  constructor
  · intro heq
    have hzero : (ω.associatedBilinForm J v v - ω.associatedBilinForm J w w) ^ 2 +
        4 * ω.associatedBilinForm J v w ^ 2 = 0 := by
      rw [← hid, ← heq]
      ring
    have h1 := sq_nonneg (ω.associatedBilinForm J v v - ω.associatedBilinForm J w w)
    have h2 := sq_nonneg (ω.associatedBilinForm J v w)
    exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by linarith)),
      pow_eq_zero_iff two_ne_zero |>.mp (by linarith)⟩
  · rintro ⟨hvw, h0⟩
    rw [wedgeNorm_def, ← hvw, h0, ← sq, zero_pow two_ne_zero, sub_zero,
      Real.sqrt_sq (h.associatedBilinForm_self_nonneg v)]
    ring

end SymplecticForm

end TauCeti
