/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre

/-!
# Piecewise-affine interpolation of lattice functions and the concavity criterion

A function `f : Hive.Vertex n → ℝ` on the triangular lattice `Δₙ` extends to the closed real
triangle `realTriangle n = {x ∈ ℝ³ | 0 ≤ xᵢ, x₀ + x₁ + x₂ = n}` by the interpolation
`interpolate f x = ∑ p, f p * p.hat x`, where the hat function `p.hat x = max 0 (1 - ‖x - p‖)` uses
the sup norm on `ℝ³`. On each unit triangle of `Δₙ` the hat functions of the three vertices are
the barycentric weights and all other hat functions vanish, so `interpolate f` is the continuous
function that agrees with `f` on `Δₙ` and is affine on every unit triangle.

The main theorem is the **concavity criterion** `concaveOn_interpolate_iff`: the interpolation is
concave on the real triangle exactly when `f` satisfies every unit-rhombus inequality
(`IsRhombusConcave f`), so that the interpolation of a real hive is concave
(`concaveOn_interpolate`). This is the dictionary between hives and concave piecewise-affine
functions on the triangle.

The forward direction evaluates concavity at the common midpoint of the two diagonals of a unit
rhombus. The converse rests on a discrete supporting-plane statement: a rhombus-concave function
lies below the barycentric-affine extension of its values on any unit triangle. Subtracting that
extension leaves a rhombus-concave function vanishing on the triangle; it is nonpositive on the
three lattice lines through the edges by discrete concavity along lines
(`IsRhombusConcave.ofYZ_add_ofYZ_le`), and then on each `60°` sector bounded by two of these lines
by the parallelogram inequality `IsRhombusConcave.parallelogram_le`. Since interpolation is
monotone and reproduces affine functions (`interpolate_comp_realCoord`), the affine extension of
the triangle containing a point supports `interpolate f` there.

## Main definitions

* `TauCeti.Hive.Vertex.realCoord`, `TauCeti.Hive.realTriangle`: real coordinates of vertices and
  the closed real triangle.
* `TauCeti.Hive.Vertex.hat`: the hat function of a vertex.
* `TauCeti.Hive.interpolate`: the linear interpolation map from lattice functions to functions on
  `ℝ³`.

## Main results

* `TauCeti.Hive.interpolate_realCoord`, `TauCeti.Hive.interpolate_comp_realCoord`,
  `TauCeti.Hive.continuous_interpolate`, `TauCeti.Hive.monotone_interpolate`.
* `TauCeti.Hive.IsRhombusConcave.ofYZ_add_ofYZ_le`: discrete concavity along lattice lines.
* `TauCeti.Hive.concaveOn_interpolate_iff`, `TauCeti.Hive.concaveOn_interpolate`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) **46**
  (2000), 43–60.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

section Discrete

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- Along each line of constant `z`, a rhombus-concave function is discretely concave:
`f(y, z) + f(y + 2, z) ≤ 2 f(y + 1, z)` whenever the three points lie in `Δₙ`. -/
theorem IsRhombusConcave.ofYZ_add_ofYZ_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    {y z : ℕ} (h : y + 2 + z ≤ n) :
    f (Vertex.ofYZ n y z (by omega)) + f (Vertex.ofYZ n (y + 2) z h) ≤
      f (Vertex.ofYZ n (y + 1) z (by omega)) + f (Vertex.ofYZ n (y + 1) z (by omega)) := by
  have h₁ := (isRhombusConcave_def f).mp hf
    (isRhombus_ofYZ_step (n := n) (y := y) (z := z) (by omega))
  have h₂ := (isRhombusConcave_def f).mp hf (isRhombus_ofYZ_step' h)
  refine le_of_add_le_add_right (a := f (Vertex.ofYZ n y (z + 1) (by omega)) +
    f (Vertex.ofYZ n (y + 1) (z + 1) (by omega))) ?_
  calc _ = (f (Vertex.ofYZ n y z (by omega)) + f (Vertex.ofYZ n (y + 1) (z + 1) (by omega))) +
        (f (Vertex.ofYZ n (y + 2) z h) + f (Vertex.ofYZ n y (z + 1) (by omega))) := by abel
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by abel

/-- A rhombus-concave function vanishing at two adjacent points `(a, z)`, `(a + 1, z)` of a line of
constant `z` is nonpositive on that whole line. -/
private theorem le_zero_of_ofYZ_line {g : Vertex n → R} (hg : IsRhombusConcave g) {a z : ℕ}
    (ha : a + 1 + z ≤ n) (h₀ : g (Vertex.ofYZ n a z (by omega)) = 0)
    (h₁ : g (Vertex.ofYZ n (a + 1) z ha) = 0) (y : ℕ) (hy : y + z ≤ n) :
    g (Vertex.ofYZ n y z hy) ≤ 0 := by
  -- Work with the sequence `s y = g(y, z)`, extended by `0` beyond the triangle.
  let s : ℕ → R := fun y => if hy : y + z ≤ n then g (Vertex.ofYZ n y z hy) else 0
  have hs : ∀ y (hy : y + z ≤ n), s y = g (Vertex.ofYZ n y z hy) := fun y hy => by simp [s, hy]
  have hc : ∀ i, i + 2 + z ≤ n → s i + s (i + 2) ≤ s (i + 1) + s (i + 1) := fun i hi => by
    rw [hs i (by omega), hs (i + 2) hi, hs (i + 1) (by omega)]
    exact hg.ofYZ_add_ofYZ_le hi
  have hs₀ : s a = 0 := (hs a (by omega)).trans h₀
  have hs₁ : s (a + 1) = 0 := (hs (a + 1) ha).trans h₁
  rw [← hs y hy]
  -- Beyond `a + 1` the sequence decreases, and before `a` it increases.
  have hup : ∀ j, a + 1 + j + z ≤ n → s (a + 1 + j) ≤ 0 ∧ s (a + 1 + j) ≤ s (a + j) := by
    intro j
    induction j with
    | zero => intro _; simp [hs₀, hs₁]
    | succ j ih =>
      intro hj
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      have := hc (a + j) (by omega)
      rw [show a + j + 2 = a + 1 + (j + 1) by omega, show a + j + 1 = a + 1 + j by omega] at this
      have h' : s (a + 1 + (j + 1)) ≤ s (a + 1 + j) := by
        refine le_of_add_le_add_left (a := s (a + j)) ?_
        calc s (a + j) + s (a + 1 + (j + 1)) ≤ s (a + 1 + j) + s (a + 1 + j) := this
          _ ≤ s (a + j) + s (a + 1 + j) := add_le_add ih₂ le_rfl
      exact ⟨h'.trans ih₁, by rwa [show a + (j + 1) = a + 1 + j by omega]⟩
  have hdown : ∀ j, j ≤ a → s (a - j) ≤ 0 ∧ s (a - j) ≤ s (a - j + 1) := by
    intro j
    induction j with
    | zero => intro _; simp [hs₀, hs₁]
    | succ j ih =>
      intro hj
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      have := hc (a - (j + 1)) (by omega)
      rw [show a - (j + 1) + 2 = a - j + 1 by omega, show a - (j + 1) + 1 = a - j by omega] at this
      have h' : s (a - (j + 1)) ≤ s (a - j) := by
        refine le_of_add_le_add_right (a := s (a - j + 1)) ?_
        calc s (a - (j + 1)) + s (a - j + 1) ≤ s (a - j) + s (a - j) := this
          _ ≤ s (a - j) + s (a - j + 1) := add_le_add le_rfl ih₂
      exact ⟨h'.trans ih₁, by rwa [show a - (j + 1) + 1 = a - j by omega]⟩
  rcases le_or_gt y a with hya | hya
  · simpa [show a - (a - y) = y by omega] using (hdown (a - y) (by omega)).1
  · simpa [show a + 1 + (y - (a + 1)) = y by omega] using (hup (y - (a + 1)) (by omega)).1

/-- `le_zero_of_ofYZ_line` for two adjacent points `a, b` on a line of constant `z`. -/
private theorem le_zero_of_line_z {g : Vertex n → R} (hg : IsRhombusConcave g) {a b : Vertex n}
    (hz : b.z = a.z) (hy : b.y = a.y + 1) (ha : g a = 0) (hb : g b = 0) {p : Vertex n}
    (hp : p.z = a.z) : g p ≤ 0 := by
  have hb' := b.sum_eq
  have hp' := p.sum_eq
  have key := le_zero_of_ofYZ_line hg (a := a.y) (z := a.z) (by omega)
    (by rwa [Vertex.ofYZ_y_z]) (by convert hb using 2; ext <;> simp <;> omega) p.y (by omega)
  convert key using 2
  ext <;> simp <;> omega

/-- `le_zero_of_line_z` rotated to a line of constant `x`. -/
private theorem le_zero_of_line_x {g : Vertex n → R} (hg : IsRhombusConcave g) {a b : Vertex n}
    (hx : b.x = a.x) (hz : b.z = a.z + 1) (ha : g a = 0) (hb : g b = 0) {p : Vertex n}
    (hp : p.x = a.x) : g p ≤ 0 := by
  simpa using le_zero_of_line_z hg.comp_rotate (a := a.rotate.rotate)
    (b := b.rotate.rotate) (p := p.rotate.rotate) (by simpa using hx) (by simpa using hz)
    (by simpa using ha) (by simpa using hb) (by simpa using hp)

/-- `le_zero_of_line_z` rotated to a line of constant `y`. -/
private theorem le_zero_of_line_y {g : Vertex n → R} (hg : IsRhombusConcave g) {a b : Vertex n}
    (hy : b.y = a.y) (hx : b.x = a.x + 1) (ha : g a = 0) (hb : g b = 0) {p : Vertex n}
    (hp : p.y = a.y) : g p ≤ 0 := by
  simpa using le_zero_of_line_z hg.comp_rotate.comp_rotate
    (a := a.rotate) (b := b.rotate) (p := p.rotate) (by simpa using hy) (by simpa using hx)
    (by simpa using ha) (by simpa using hb) (by simpa using hp)

/-- A rhombus-concave function that is nonnegative at `v` and nonpositive on the lines of constant
`y` and constant `z` through `v` is nonpositive on the two `60°` sectors at `v` bounded by these
lines: sum the rhombus inequalities over the lattice parallelogram spanned by `v` and `p`. -/
private theorem le_zero_of_quadrant_yz {g : Vertex n → R} (hg : IsRhombusConcave g)
    {v : Vertex n} (hv : 0 ≤ g v) (hy : ∀ p : Vertex n, p.y = v.y → g p ≤ 0)
    (hz : ∀ p : Vertex n, p.z = v.z → g p ≤ 0) {p : Vertex n}
    (hp : (v.y ≤ p.y ∧ v.z ≤ p.z) ∨ (p.y ≤ v.y ∧ p.z ≤ v.z)) : g p ≤ 0 := by
  have hv' := v.sum_eq
  have hp' := p.sum_eq
  rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have key := hg.parallelogram_le h₁ h₂ (by omega : p.y + p.z ≤ n)
    rw [Vertex.ofYZ_y_z, Vertex.ofYZ_y_z] at key
    calc g p ≤ g v + g p := le_add_of_nonneg_left hv
      _ ≤ _ := key
      _ ≤ 0 := add_nonpos (hz _ (by simp)) (hy _ (by simp))
  · have key := hg.parallelogram_le h₁ h₂ (by omega : v.y + v.z ≤ n)
    rw [Vertex.ofYZ_y_z, Vertex.ofYZ_y_z] at key
    calc g p ≤ g p + g v := le_add_of_nonneg_right hv
      _ ≤ _ := key
      _ ≤ 0 := add_nonpos (hy _ (by simp)) (hz _ (by simp))

/-- `le_zero_of_quadrant_yz` rotated to the sectors bounded by lines of constant `z` and `x`. -/
private theorem le_zero_of_quadrant_zx {g : Vertex n → R} (hg : IsRhombusConcave g)
    {v : Vertex n} (hv : 0 ≤ g v) (hz : ∀ p : Vertex n, p.z = v.z → g p ≤ 0)
    (hx : ∀ p : Vertex n, p.x = v.x → g p ≤ 0) {p : Vertex n}
    (hp : (v.z ≤ p.z ∧ v.x ≤ p.x) ∨ (p.z ≤ v.z ∧ p.x ≤ v.x)) : g p ≤ 0 := by
  simpa using le_zero_of_quadrant_yz hg.comp_rotate (v := v.rotate.rotate)
    (p := p.rotate.rotate) (by simpa using hv) (fun q hq => hz _ (by simpa using hq))
    (fun q hq => hx _ (by simpa using hq)) (by simpa using hp)

/-- `le_zero_of_quadrant_yz` rotated to the sectors bounded by lines of constant `x` and `y`. -/
private theorem le_zero_of_quadrant_xy {g : Vertex n → R} (hg : IsRhombusConcave g)
    {v : Vertex n} (hv : 0 ≤ g v) (hx : ∀ p : Vertex n, p.x = v.x → g p ≤ 0)
    (hy : ∀ p : Vertex n, p.y = v.y → g p ≤ 0) {p : Vertex n}
    (hp : (v.x ≤ p.x ∧ v.y ≤ p.y) ∨ (p.x ≤ v.x ∧ p.y ≤ v.y)) : g p ≤ 0 := by
  simpa using le_zero_of_quadrant_yz hg.comp_rotate.comp_rotate (v := v.rotate)
    (p := p.rotate) (by simpa using hv) (fun q hq => hx _ (by simpa using hq))
    (fun q hq => hy _ (by simpa using hq)) (by simpa using hp)

end Discrete

/-! ### Unit triangles -/

/-- A unit triangle of `Δₙ`: its vertices are `base + sign • eₖ` for the three standard basis
vectors `eₖ`, with `sign = 1` for an upward and `sign = -1` for a downward triangle. -/
private structure Cell (n : ℕ) where
  sign : ℤ
  sign_eq : sign = 1 ∨ sign = -1
  base : Fin 3 → ℤ
  vertex : Fin 3 → Vertex n
  coord_vertex : ∀ k i, ((vertex k).coord i : ℤ) = base i + if i = k then sign else 0

namespace Cell

variable {n : ℕ}

/-- A rhombus-concave function vanishing at the three vertices of a unit triangle is nonpositive
everywhere. It is nonpositive on the three lattice lines through the edges of the triangle by
discrete concavity along each line, and every vertex of `Δₙ` lies in one of the six `60°` sectors
bounded by two of these lines at a vertex of the triangle. -/
private theorem le_zero {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    {g : Vertex n → R} (hg : IsRhombusConcave g) (T : Cell n) (h₀ : ∀ k, g (T.vertex k) = 0)
    (p : Vertex n) : g p ≤ 0 := by
  obtain ⟨ε, hε, q, t, ht⟩ := T
  have ha : g (t 0) = 0 := h₀ 0
  have hb : g (t 1) = 0 := h₀ 1
  have hc : g (t 2) = 0 := h₀ 2
  have h00 := ht 0 0; have h01 := ht 0 1; have h02 := ht 0 2
  have h10 := ht 1 0; have h11 := ht 1 1; have h12 := ht 1 2
  have h20 := ht 2 0; have h21 := ht 2 1; have h22 := ht 2 2
  simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two, Fin.isValue, ↓reduceIte,
    Fin.reduceEq, add_zero] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  -- The three lines through the edges of the triangle.
  have hz : ∀ p : Vertex n, (p.z : ℤ) = q 2 → g p ≤ 0 := by
    rcases hε with rfl | rfl
    · exact fun p hp => le_zero_of_line_z hg (by omega) (by omega) ha hb (by omega)
    · exact fun p hp => le_zero_of_line_z hg (a := t 1) (by omega) (by omega) hb ha (by omega)
  have hy : ∀ p : Vertex n, (p.y : ℤ) = q 1 → g p ≤ 0 := by
    rcases hε with rfl | rfl
    · exact fun p hp => le_zero_of_line_y hg (a := t 2) (by omega) (by omega) hc ha (by omega)
    · exact fun p hp => le_zero_of_line_y hg (a := t 0) (by omega) (by omega) ha hc (by omega)
  have hx : ∀ p : Vertex n, (p.x : ℤ) = q 0 → g p ≤ 0 := by
    rcases hε with rfl | rfl
    · exact fun p hp => le_zero_of_line_x hg (a := t 1) (by omega) (by omega) hb hc (by omega)
    · exact fun p hp => le_zero_of_line_x hg (a := t 2) (by omega) (by omega) hc hb (by omega)
  -- Two of the three coordinate displacements from `q` have the same sign.
  rcases le_total (p.x : ℤ) (q 0) with h₁ | h₁ <;> rcases le_total (p.y : ℤ) (q 1) with h₂ | h₂ <;>
    rcases le_total (p.z : ℤ) (q 2) with h₃ | h₃
  all_goals first
    | exact le_zero_of_quadrant_yz hg ha.ge (fun p hp => hy p (by omega))
        (fun p hp => hz p (by omega)) (by omega)
    | exact le_zero_of_quadrant_zx hg hb.ge (fun p hp => hz p (by omega))
        (fun p hp => hx p (by omega)) (by omega)
    | exact le_zero_of_quadrant_xy hg hc.ge (fun p hp => hx p (by omega))
        (fun p hp => hy p (by omega)) (by omega)

/-- **Discrete supporting planes.** A rhombus-concave function lies below every
barycentric-affine function that agrees with it at the three vertices of a unit triangle. -/
private theorem le_barycentricLinear {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R]
    {f : Vertex n → R} (hf : IsRhombusConcave f) (T : Cell n) {c₀ α β γ : R}
    (h : ∀ k, f (T.vertex k) = barycentricLinear c₀ α β γ (T.vertex k)) (p : Vertex n) :
    f p ≤ barycentricLinear c₀ α β γ p := by
  have hg : IsRhombusConcave (f + barycentricLinear (-c₀) (-α) (-β) (-γ)) :=
    (isRhombusConcave_add_barycentricLinear_iff f _ _ _ _).2 hf
  have heq : ∀ p, (f + barycentricLinear (-c₀) (-α) (-β) (-γ) : Vertex n → R) p =
      f p - barycentricLinear c₀ α β γ p := fun p => by
    simp only [Pi.add_apply, barycentricLinear_apply, smul_neg]; abel
  have := T.le_zero hg (fun k => by rw [heq, h, sub_self]) p
  rwa [heq, sub_nonpos] at this

end Cell

/-! ### The real triangle and hat functions -/

section Real

variable {n : ℕ}

/-- The real barycentric coordinates `(x, y, z)` of a lattice vertex. -/
def Vertex.realCoord (p : Vertex n) : Fin 3 → ℝ := fun i => (p.coord i : ℝ)

@[simp] theorem Vertex.realCoord_apply (p : Vertex n) (i : Fin 3) :
    p.realCoord i = p.coord i := (rfl)

/-- The closed real triangle `{x ∈ ℝ³ | 0 ≤ xᵢ, x₀ + x₁ + x₂ = n}` spanned by `Δₙ`. -/
def realTriangle (n : ℕ) : Set (Fin 3 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n}

theorem mem_realTriangle_iff {x : Fin 3 → ℝ} :
    x ∈ realTriangle n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n := Iff.rfl

theorem convex_realTriangle (n : ℕ) : Convex ℝ (realTriangle n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2, hy.2]
    rw [← add_mul, hab, one_mul]

theorem Vertex.realCoord_mem_realTriangle (p : Vertex n) : p.realCoord ∈ realTriangle n :=
  ⟨fun _ => Nat.cast_nonneg _, by
    simp only [Vertex.realCoord_apply, Fin.sum_univ_three, Vertex.coord_zero, Vertex.coord_one,
      Vertex.coord_two]
    exact_mod_cast p.sum_eq⟩

/-- The **hat function** of a lattice vertex `p`, `x ↦ max 0 (1 - ‖x - p‖)` for the sup norm on
`ℝ³`. It equals `1` at `p` and `0` at every other vertex of `Δₙ`, and on the plane
`x₀ + x₁ + x₂ = n` it is supported on the hexagon of unit triangles around `p`. -/
def Vertex.hat (p : Vertex n) (x : Fin 3 → ℝ) : ℝ := max 0 (1 - ‖x - p.realCoord‖)

theorem Vertex.hat_def (p : Vertex n) (x : Fin 3 → ℝ) :
    p.hat x = max 0 (1 - ‖x - p.realCoord‖) := (rfl)

theorem Vertex.hat_nonneg (p : Vertex n) (x : Fin 3 → ℝ) : 0 ≤ p.hat x := le_max_left _ _

theorem Vertex.continuous_hat (p : Vertex n) : Continuous p.hat :=
  continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).norm))

/-- A coordinate of `x - p` of absolute value at least `1` puts `x` outside the support of the hat
function of `p`. -/
private theorem Vertex.hat_eq_zero_of_le_abs (p : Vertex n) {x : Fin 3 → ℝ} (i : Fin 3)
    (h : 1 ≤ |x i - p.realCoord i|) : p.hat x = 0 := by
  have : 1 ≤ ‖x - p.realCoord‖ :=
    h.trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (x - p.realCoord) i)
  exact max_eq_left (by linarith)

private theorem Vertex.hat_eq_zero_of_two_le (p : Vertex n) {x : Fin 3 → ℝ} (i : Fin 3) (N : ℤ)
    (hN : 2 * (x i - p.realCoord i) = N) (h : 2 ≤ N ∨ N ≤ -2) : p.hat x = 0 := by
  refine p.hat_eq_zero_of_le_abs i (le_abs.2 ?_)
  rcases h with h | h
  · exact Or.inl (by have : (2 : ℝ) ≤ N := by exact_mod_cast h
                     linarith)
  · exact Or.inr (by have : (N : ℝ) ≤ -2 := by exact_mod_cast h
                     linarith)

/-- The hat function of `p` takes the value `1` at `p` and `0` at every other vertex. -/
@[simp] theorem Vertex.hat_realCoord (p q : Vertex n) :
    p.hat q.realCoord = if q = p then 1 else 0 := by
  split_ifs with h
  · subst h; simp [Vertex.hat_def]
  · have hne : q.x ≠ p.x ∨ q.y ≠ p.y ∨ q.z ≠ p.z := by
      by_contra H; push Not at H; exact h (Vertex.ext H.1 H.2.1 H.2.2)
    have : (2 ≤ 2 * ((q.x : ℤ) - p.x) ∨ 2 * ((q.x : ℤ) - p.x) ≤ -2) ∨
        (2 ≤ 2 * ((q.y : ℤ) - p.y) ∨ 2 * ((q.y : ℤ) - p.y) ≤ -2) ∨
        (2 ≤ 2 * ((q.z : ℤ) - p.z) ∨ 2 * ((q.z : ℤ) - p.z) ≤ -2) := by omega
    rcases this with h' | h' | h'
    · exact p.hat_eq_zero_of_two_le 0 _ (by simp) h'
    · exact p.hat_eq_zero_of_two_le 1 _ (by simp) h'
    · exact p.hat_eq_zero_of_two_le 2 _ (by simp) h'

/-! ### The interpolation map -/

/-- The **interpolation** of a lattice function, `x ↦ ∑ p, f p * p.hat x`. On `realTriangle n` it
agrees with `f` at the vertices (`interpolate_realCoord`), is affine on each unit triangle, and
reproduces affine functions (`interpolate_comp_realCoord`). -/
def interpolate : (Vertex n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) → ℝ where
  toFun f x := ∑ p, f p * p.hat x
  map_add' f g := by funext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by funext x; simp [Finset.mul_sum, mul_assoc]

theorem interpolate_apply (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate f x = ∑ p, f p * p.hat x := (rfl)

/-- The interpolation of `f` agrees with `f` at every vertex. -/
@[simp] theorem interpolate_realCoord (f : Vertex n → ℝ) (p : Vertex n) :
    interpolate f p.realCoord = f p := by
  simp [interpolate_apply]

theorem monotone_interpolate : Monotone (interpolate (n := n)) := fun _ _ h x => by
  simp only [interpolate_apply]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (h p) (p.hat_nonneg x)

theorem continuous_interpolate (f : Vertex n → ℝ) : Continuous (interpolate f) := by
  rw [show interpolate f = fun x => ∑ p, f p * p.hat x from funext (interpolate_apply f)]
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (Vertex.continuous_hat p)

/-! ### Interpolation on a unit triangle -/

/-- The unit triangle with vertices `q + ε eₖ`, given that these lie in `Δₙ`. -/
private def Cell.ofBase (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (q : Fin 3 → ℤ) (hq : ∀ i, 0 ≤ q i)
    (hqε : ∀ i, 0 ≤ q i + ε) (hs : q 0 + q 1 + q 2 + ε = n) : Cell n where
  sign := ε
  sign_eq := hε
  base := q
  vertex k := ⟨(q 0 + if 0 = k then ε else 0).toNat, (q 1 + if 1 = k then ε else 0).toNat,
    (q 2 + if 2 = k then ε else 0).toNat, by
      have := hq 0; have := hq 1; have := hq 2; have := hqε 0; have := hqε 1; have := hqε 2
      fin_cases k <;> simp <;> omega⟩
  coord_vertex k i := by
    have := hq 0; have := hq 1; have := hq 2; have := hqε 0; have := hqε 1; have := hqε 2
    fin_cases k <;> fin_cases i <;> simp <;> omega

private theorem Cell.realCoord_vertex (T : Cell n) (k i : Fin 3) :
    (T.vertex k).realCoord i = T.base i + if i = k then (T.sign : ℝ) else 0 := by
  have h := T.coord_vertex k i
  rw [Vertex.realCoord_apply]
  split_ifs at h ⊢ <;> exact_mod_cast h

private theorem Cell.vertex_injective (T : Cell n) : Function.Injective T.vertex := by
  intro k k' h
  by_contra hne
  have h₁ := T.coord_vertex k k
  have h₂ := T.coord_vertex k' k
  rw [h, h₂] at h₁
  simp [hne] at h₁
  rcases T.sign_eq with h | h <;> omega

/-- On a unit triangle, the hat function of a vertex is its barycentric weight. -/
private theorem Cell.hat_vertex (T : Cell n) {x l : Fin 3 → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hsum : ∑ i, l i = 1) (hx : ∀ i, x i = T.base i + T.sign * l i) (k : Fin 3) :
    (T.vertex k).hat x = l k := by
  have hε : |(T.sign : ℝ)| = 1 := by rcases T.sign_eq with h | h <;> simp [h]
  have hsum3 : l 0 + l 1 + l 2 = 1 := by simpa [Fin.sum_univ_three] using hsum
  have hcomp : ∀ i, |(x - (T.vertex k).realCoord) i| = |l i - if i = k then 1 else 0| := by
    intro i
    have : (x - (T.vertex k).realCoord) i = T.sign * (l i - if i = k then 1 else 0) := by
      rw [Pi.sub_apply, hx, T.realCoord_vertex]; split_ifs <;> ring
    rw [this, abs_mul, hε, one_mul]
  have hlk : l k ≤ 1 := by fin_cases k <;> simp <;> linarith [hl 0, hl 1, hl 2]
  have hnorm : ‖x - (T.vertex k).realCoord‖ = 1 - l k := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_) ?_
    · rw [Real.norm_eq_abs, hcomp]
      by_cases hik : i = k
      · subst hik; rw [ite_eq_left rfl, abs_of_nonpos (by linarith)]; linarith
      · rw [ite_eq_right hik, sub_zero, abs_of_nonneg (hl i)]
        fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> linarith [hl 0, hl 1, hl 2]
    · have hk : |(x - (T.vertex k).realCoord) k| = 1 - l k := by
        rw [hcomp, ite_eq_left rfl, abs_of_nonpos (by linarith)]; ring
      rw [← hk, ← Real.norm_eq_abs]; exact norm_le_pi_norm _ k
  rw [Vertex.hat_def, hnorm, sub_sub_cancel, max_eq_right (hl k)]

/-- On a unit triangle, the hat function of every other vertex vanishes. -/
private theorem Cell.hat_eq_zero (T : Cell n) {x l : Fin 3 → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hx : ∀ i, x i = T.base i + T.sign * l i) {p : Vertex n} (hp : ∀ k, p ≠ T.vertex k) :
    p.hat x = 0 := by
  obtain ⟨ε, hε, q, t, ht⟩ := T
  simp only at hx hp
  have hne : ∀ k, p.x ≠ (t k).x ∨ p.y ≠ (t k).y ∨ p.z ≠ (t k).z := fun k => by
    by_contra H; push Not at H; exact hp k (Vertex.ext H.1 H.2.1 H.2.2)
  have hp0 := hne 0; have hp1 := hne 1; have hp2 := hne 2
  have h00 := ht 0 0; have h01 := ht 0 1; have h02 := ht 0 2
  have h10 := ht 1 0; have h11 := ht 1 1; have h12 := ht 1 2
  have h20 := ht 2 0; have h21 := ht 2 1; have h22 := ht 2 2
  simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two, Fin.isValue, ↓reduceIte,
    Fin.reduceEq, add_zero] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hpn := p.sum_eq
  have htn := (t 0).sum_eq
  rcases hε with rfl | rfl
  · -- Upward triangle: some coordinate of `p` lies strictly below `q`.
    obtain ⟨i, hi⟩ : ∃ i, (p.coord i : ℤ) + 1 ≤ q i := by
      have : (p.x : ℤ) + 1 ≤ q 0 ∨ (p.y : ℤ) + 1 ≤ q 1 ∨ (p.z : ℤ) + 1 ≤ q 2 := by omega
      rcases this with h | h | h
      exacts [⟨0, by simpa using h⟩, ⟨1, by simpa using h⟩, ⟨2, by simpa using h⟩]
    have hi' : (p.coord i : ℝ) + 1 ≤ q i := by exact_mod_cast hi
    refine p.hat_eq_zero_of_le_abs i (le_abs.2 (Or.inl ?_))
    rw [hx i, Vertex.realCoord_apply]; push_cast
    linarith [hl i]
  · -- Downward triangle: some coordinate of `p` lies strictly above `q`.
    obtain ⟨i, hi⟩ : ∃ i, q i + 1 ≤ (p.coord i : ℤ) := by
      have : q 0 + 1 ≤ (p.x : ℤ) ∨ q 1 + 1 ≤ (p.y : ℤ) ∨ q 2 + 1 ≤ (p.z : ℤ) := by omega
      rcases this with h | h | h
      exacts [⟨0, by simpa using h⟩, ⟨1, by simpa using h⟩, ⟨2, by simpa using h⟩]
    have hi' : (q i : ℝ) + 1 ≤ p.coord i := by exact_mod_cast hi
    refine p.hat_eq_zero_of_le_abs i (le_abs.2 (Or.inr ?_))
    rw [hx i, Vertex.realCoord_apply]; push_cast
    linarith [hl i]

/-- On a unit triangle, the interpolation is the affine interpolation of the three vertex
values. -/
private theorem Cell.interpolate_eq (T : Cell n) {x l : Fin 3 → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hsum : ∑ i, l i = 1) (hx : ∀ i, x i = T.base i + T.sign * l i) (f : Vertex n → ℝ) :
    interpolate f x = ∑ k, l k * f (T.vertex k) := by
  have hhat : ∀ p : Vertex n, p.hat x = ∑ k, if p = T.vertex k then l k else 0 := by
    intro p
    by_cases hp : ∃ k, p = T.vertex k
    · obtain ⟨k, rfl⟩ := hp
      rw [Finset.sum_eq_single k
        (fun k' _ hk' => ite_eq_right fun h => hk' (T.vertex_injective h).symm) (by simp),
        ite_eq_left rfl, T.hat_vertex hl hsum hx]
    · push Not at hp
      simp [hp, T.hat_eq_zero hl hx hp]
  simp only [interpolate_apply, hhat, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- Every point of the real triangle lies in a unit triangle with vertices in `Δₙ`. -/
private theorem exists_cell {x : Fin 3 → ℝ} (hx : x ∈ realTriangle n) (hn : 0 < n) :
    ∃ (T : Cell n) (l : Fin 3 → ℝ), (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧
      ∀ i, x i = T.base i + T.sign * l i := by
  obtain ⟨hx0, hxs⟩ := hx
  set q : Fin 3 → ℤ := fun i => ⌊x i⌋
  have hq0 : ∀ i, 0 ≤ q i := fun i => Int.floor_nonneg.2 (hx0 i)
  have hql : ∀ i, (q i : ℝ) ≤ x i := fun i => Int.floor_le _
  have hqu : ∀ i, x i < q i + 1 := fun i => Int.lt_floor_add_one _
  simp only [Fin.sum_univ_three] at hxs
  have hlo : (0 : ℤ) ≤ n - (q 0 + q 1 + q 2) := by
    have : ((q 0 + q 1 + q 2 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by
      push_cast; linarith [hql 0, hql 1, hql 2]
    have := Int.cast_le.1 this; omega
  have hhi : (n : ℤ) - (q 0 + q 1 + q 2) < 3 := by
    have : ((n : ℤ) : ℝ) < ((q 0 + q 1 + q 2 + 3 : ℤ) : ℝ) := by
      push_cast; linarith [hqu 0, hqu 1, hqu 2]
    have := Int.cast_lt.1 this; omega
  obtain h | h | h : (n : ℤ) - (q 0 + q 1 + q 2) = 0 ∨ (n : ℤ) - (q 0 + q 1 + q 2) = 1 ∨
      (n : ℤ) - (q 0 + q 1 + q 2) = 2 := by omega
  · -- A lattice point: it is a vertex of an upward triangle based at `q - eⱼ` with `qⱼ ≥ 1`.
    have h' : (n : ℤ) = q 0 + q 1 + q 2 := by omega
    have hR : (n : ℝ) = q 0 + q 1 + q 2 := by exact_mod_cast h'
    have hr : ∀ i, x i = q i := fun i => by
      fin_cases i <;> simp <;> linarith [hql 0, hql 1, hql 2]
    obtain ⟨j, hj⟩ : ∃ j, 1 ≤ q j := by
      by_contra H; push Not at H; have := H 0; have := H 1; have := H 2; omega
    refine ⟨Cell.ofBase 1 (Or.inl rfl) (fun i => q i - if i = j then 1 else 0)
      (fun i => by
        have := hq0 i
        split_ifs with hij
        · subst hij; omega
        · omega)
      (fun i => by have := hq0 i; split_ifs <;> omega)
      (by fin_cases j <;> simp <;> omega),
      fun i => if i = j then 1 else 0, fun i => by beta_reduce; split_ifs <;> norm_num,
      by fin_cases j <;> simp, fun i => ?_⟩
    simp only [Cell.ofBase, hr i]
    split_ifs <;> push_cast <;> ring
  · -- An upward triangle based at `q`.
    have hR : (n : ℝ) - (q 0 + q 1 + q 2) = 1 := by exact_mod_cast h
    refine ⟨Cell.ofBase 1 (Or.inl rfl) q hq0 (fun i => by linarith [hq0 i]) (by omega),
      fun i => x i - q i, fun i => sub_nonneg.2 (hql i), ?_, fun i => by simp [Cell.ofBase]⟩
    simp only [Fin.sum_univ_three]; linarith
  · -- A downward triangle based at `q + (1, 1, 1)`.
    have hR : (n : ℝ) - (q 0 + q 1 + q 2) = 2 := by exact_mod_cast h
    refine ⟨Cell.ofBase (-1) (Or.inr rfl) (fun i => q i + 1) (fun i => by linarith [hq0 i])
      (fun i => by linarith [hq0 i]) (by omega), fun i => q i + 1 - x i,
      fun i => by linarith [hqu i], ?_, fun i => by simp [Cell.ofBase]⟩
    simp only [Fin.sum_univ_three]; linarith

private theorem eq_realCoord_cornerA_of_mem_realTriangle_zero {x : Fin 3 → ℝ}
    (hx : x ∈ realTriangle 0) : x = (Vertex.cornerA 0).realCoord := by
  obtain ⟨h0, hs⟩ := hx
  simp only [Fin.sum_univ_three, Nat.cast_zero] at hs
  funext i
  fin_cases i <;> simp <;> linarith [h0 0, h0 1, h0 2]

private theorem Vertex.eq_cornerA_zero (p : Vertex 0) : p = Vertex.cornerA 0 := by
  have := p.sum_eq
  ext <;> simp <;> omega

/-- Interpolation reproduces affine functions, in coordinates. -/
private theorem interpolate_affine (c : ℝ) (a : Fin 3 → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ realTriangle n) :
    interpolate (fun p : Vertex n => c + ∑ i, a i * p.realCoord i) x = c + ∑ i, a i * x i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [eq_realCoord_cornerA_of_mem_realTriangle_zero hx, interpolate_realCoord]
  · obtain ⟨T, l, hl, hsum, hxl⟩ := exists_cell hx hn
    rw [T.interpolate_eq hl hsum hxl]
    simp only [Fin.sum_univ_three] at hsum
    simp only [T.realCoord_vertex, hxl, Fin.sum_univ_three, Fin.isValue, ↓reduceIte,
      Fin.reduceEq, add_zero]
    linear_combination (c + a 0 * T.base 0 + a 1 * T.base 1 + a 2 * T.base 2) * hsum

/-- **Interpolation reproduces affine functions**: on the real triangle, the interpolation of the
restriction of an affine function `L` to the vertices is `L` itself. -/
theorem interpolate_comp_realCoord (L : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ realTriangle n) : interpolate (fun p : Vertex n => L p.realCoord) x = L x := by
  have hL : ∀ y, L y = L 0 + ∑ i, L.linear (fun j => if i = j then 1 else 0) * y i := by
    intro y
    have := L.map_vadd 0 y
    rw [vadd_eq_add, add_zero, vadd_eq_add] at this
    rw [this, add_comm, LinearMap.pi_apply_eq_sum_univ L.linear y]
    simp [mul_comm]
  have hf : (fun p : Vertex n => L p.realCoord) =
      fun p => L 0 + ∑ i, L.linear (fun j => if i = j then 1 else 0) * p.realCoord i :=
    funext fun p => hL _
  rw [hf, hL x]
  exact interpolate_affine _ _ hx

private theorem barycentricLinear_eq_real (c : ℝ) (a : Fin 3 → ℝ) (p : Vertex n) :
    barycentricLinear c (a 0) (a 1) (a 2) p = c + ∑ i, a i * p.realCoord i := by
  simp [barycentricLinear_apply, Fin.sum_univ_three, nsmul_eq_mul, mul_comm, add_assoc]

/-- At every point of the real triangle, the interpolation of a rhombus-concave function has an
affine supporting function lying above the function at every vertex: the affine extension of its
values on a unit triangle containing the point. -/
private theorem exists_support {f : Vertex n → ℝ} (hf : IsRhombusConcave f) {x : Fin 3 → ℝ}
    (hx : x ∈ realTriangle n) : ∃ (c : ℝ) (a : Fin 3 → ℝ),
      interpolate f x = c + ∑ i, a i * x i ∧
        ∀ p : Vertex n, f p ≤ c + ∑ i, a i * p.realCoord i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨f (Vertex.cornerA 0), 0, ?_, fun p => ?_⟩
    · rw [eq_realCoord_cornerA_of_mem_realTriangle_zero hx, interpolate_realCoord]; simp
    · rw [Vertex.eq_cornerA_zero p]; simp
  · obtain ⟨T, l, hl, hsum, hxl⟩ := exists_cell hx hn
    have hε : (T.sign : ℝ) * T.sign = 1 := by rcases T.sign_eq with h | h <;> simp [h]
    have hvert : ∀ k, f (T.vertex k) = -∑ i, (T.sign : ℝ) * T.base i * f (T.vertex i) +
        ∑ i, (T.sign * f (T.vertex i)) * (T.vertex k).realCoord i := by
      intro k
      simp only [T.realCoord_vertex, Fin.sum_univ_three]
      fin_cases k <;> simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, add_zero, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk] <;>
        linear_combination (-f (T.vertex _)) * hε
    refine ⟨-∑ i, (T.sign : ℝ) * T.base i * f (T.vertex i), fun i => T.sign * f (T.vertex i), ?_,
      fun p => ?_⟩
    · rw [T.interpolate_eq hl hsum hxl]
      simp only [hxl, Fin.sum_univ_three]
      linear_combination (-(l 0 * f (T.vertex 0) + l 1 * f (T.vertex 1) +
        l 2 * f (T.vertex 2))) * hε
    · rw [← barycentricLinear_eq_real]
      exact T.le_barycentricLinear hf (fun k => (hvert k).trans
        (barycentricLinear_eq_real _ (fun i => (T.sign : ℝ) * f (T.vertex i)) _).symm) p

/-! ### The concavity criterion -/

private theorem abs_sub_le_one_of_sqDist {a c : Vertex n} (h : a.sqDist c = 2) (i : Fin 3) :
    -1 ≤ (c.coord i : ℤ) - a.coord i ∧ (c.coord i : ℤ) - a.coord i ≤ 1 := by
  rw [Vertex.sqDist_def] at h
  fin_cases i <;> simp <;> constructor <;>
    nlinarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y),
      sq_nonneg ((a.z : ℤ) - c.z)]

private theorem coord_ne_of_sqDist {a c : Vertex n} (h : a.sqDist c = 2) :
    a.x ≠ c.x ∨ a.y ≠ c.y ∨ a.z ≠ c.z := by
  by_contra H; push Not at H
  rw [Vertex.ext H.1 H.2.1 H.2.2, Vertex.sqDist_self] at h
  exact absurd h (by norm_num)

/-- At the midpoint of a unit edge `ac`, the hat function of `a` takes the value `1 / 2`. -/
private theorem hat_midpoint_left {a c : Vertex n} (h : a.sqDist c = 2) :
    a.hat ((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord) = 1 / 2 := by
  have hb := abs_sub_le_one_of_sqDist h
  have hcomp : ∀ i, ((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord - a.realCoord) i =
      (((c.coord i : ℤ) - a.coord i : ℤ) : ℝ) / 2 := fun i => by simp; ring
  have hle : ∀ i, |((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord - a.realCoord) i| ≤
      1 / 2 := by
    intro i
    rw [hcomp, abs_div, abs_two, div_le_div_iff_of_pos_right two_pos, abs_le]
    exact ⟨by exact_mod_cast (hb i).1, by exact_mod_cast (hb i).2⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      (c.coord k : ℤ) - a.coord k = 1 ∨ (c.coord k : ℤ) - a.coord k = -1 := by
    have hne := coord_ne_of_sqDist h
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
    simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two] at h0 h1 h2
    rcases hne with hne | hne | hne
    · exact ⟨0, by simp; omega⟩
    · exact ⟨1, by simp; omega⟩
    · exact ⟨2, by simp; omega⟩
  have hnorm : ‖(1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord - a.realCoord‖ = 1 / 2 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hle i
    · have hk' : |((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord - a.realCoord) k| =
          1 / 2 := by
        rw [hcomp]; rcases hk with hk | hk <;> rw [hk] <;> norm_num
      calc (1 / 2 : ℝ)
          = ‖((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord - a.realCoord) k‖ := by
            rw [Real.norm_eq_abs, hk']
        _ ≤ _ := norm_le_pi_norm _ k
  rw [Vertex.hat_def, hnorm]; norm_num

/-- At the midpoint of a unit edge `ac`, the hat function of every other vertex vanishes. -/
private theorem hat_midpoint_eq_zero {a c p : Vertex n} (h : a.sqDist c = 2) (ha : p ≠ a)
    (hc : p ≠ c) : p.hat ((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord) = 0 := by
  have hb := abs_sub_le_one_of_sqDist h
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two] at h0 h1 h2
  have ha' : p.x ≠ a.x ∨ p.y ≠ a.y ∨ p.z ≠ a.z := by
    by_contra H; push Not at H; exact ha (Vertex.ext H.1 H.2.1 H.2.2)
  have hc' : p.x ≠ c.x ∨ p.y ≠ c.y ∨ p.z ≠ c.z := by
    by_contra H; push Not at H; exact hc (Vertex.ext H.1 H.2.1 H.2.2)
  have := p.sum_eq; have := a.sum_eq; have := c.sum_eq
  -- Some coordinate of `a + c - 2p` has absolute value at least `2`.
  have key : (2 ≤ (a.x : ℤ) + c.x - 2 * p.x ∨ (a.x : ℤ) + c.x - 2 * p.x ≤ -2) ∨
      (2 ≤ (a.y : ℤ) + c.y - 2 * p.y ∨ (a.y : ℤ) + c.y - 2 * p.y ≤ -2) ∨
      (2 ≤ (a.z : ℤ) + c.z - 2 * p.z ∨ (a.z : ℤ) + c.z - 2 * p.z ≤ -2) := by omega
  rcases key with key | key | key
  · exact p.hat_eq_zero_of_two_le 0 _ (by simp; ring) key
  · exact p.hat_eq_zero_of_two_le 1 _ (by simp; ring) key
  · exact p.hat_eq_zero_of_two_le 2 _ (by simp; ring) key

/-- The interpolation takes the average of the endpoint values at the midpoint of a unit edge. -/
private theorem interpolate_midpoint (f : Vertex n → ℝ) {a c : Vertex n} (h : a.sqDist c = 2) :
    interpolate f ((1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord) = (f a + f c) / 2 := by
  have hac : a ≠ c := by rintro rfl; simp at h
  have h' : c.sqDist a = 2 := by rwa [Vertex.sqDist_comm]
  rw [interpolate_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac
    (fun p _ hp => by rw [hat_midpoint_eq_zero h hp.1 hp.2, mul_zero]), hat_midpoint_left h,
    add_comm ((1 / 2 : ℝ) • a.realCoord), hat_midpoint_left h']
  ring

/-- **Concavity criterion.** The interpolation of a lattice function is concave on the real
triangle if and only if the function satisfies every unit-rhombus inequality. -/
theorem concaveOn_interpolate_iff {f : Vertex n → ℝ} :
    ConcaveOn ℝ (realTriangle n) (interpolate f) ↔ IsRhombusConcave f := by
  refine ⟨fun hc => (isRhombusConcave_def f).mpr fun a b c d hr => ?_,
    fun hf => ⟨convex_realTriangle n, fun x hx y hy s t hs ht hst => ?_⟩⟩
  · -- The long diagonal `bd` and the short diagonal `ac` share their midpoint.
    have hx : (b.x : ℝ) + d.x = a.x + c.x := by exact_mod_cast hr.midpoint_x.symm
    have hy : (b.y : ℝ) + d.y = a.y + c.y := by exact_mod_cast hr.midpoint_y.symm
    have hz : (b.z : ℝ) + d.z = a.z + c.z := by exact_mod_cast hr.midpoint_z.symm
    have hm : (1 / 2 : ℝ) • b.realCoord + (1 / 2 : ℝ) • d.realCoord =
        (1 / 2 : ℝ) • a.realCoord + (1 / 2 : ℝ) • c.realCoord := by
      funext i; fin_cases i <;> simp <;> linarith
    have key := hc.2 b.realCoord_mem_realTriangle d.realCoord_mem_realTriangle
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [hm, interpolate_midpoint f hr.short, interpolate_realCoord, interpolate_realCoord,
      smul_eq_mul, smul_eq_mul] at key
    linarith
  · -- Compare both endpoints with a supporting affine function at the convex combination.
    obtain ⟨c, a, hzF, hle⟩ := exists_support hf (convex_realTriangle n hx hy hs ht hst)
    have hbound : ∀ w ∈ realTriangle n, interpolate f w ≤ c + ∑ i, a i * w i := fun w hw =>
      (monotone_interpolate (fun p => hle p) w).trans_eq (interpolate_affine c a hw)
    have h₁ := mul_le_mul_of_nonneg_left (hbound x hx) hs
    have h₂ := mul_le_mul_of_nonneg_left (hbound y hy) ht
    have hc := congrArg (c * ·) hst
    rw [hzF]
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Fin.sum_univ_three] at h₁ h₂ hc ⊢
    linarith

/-- The interpolation of a real hive is concave on the real triangle. -/
theorem concaveOn_interpolate (h : RealHive n) :
    ConcaveOn ℝ (realTriangle n) (interpolate (h : Vertex n → ℝ)) :=
  concaveOn_interpolate_iff.2 h.isRhombusConcave

end Real

end TauCeti.Hive
