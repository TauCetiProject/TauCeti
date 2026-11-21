/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Function
public import TauCeti.Combinatorics.Hive.Concave
-- Reuse the private extension by zero and discrete supporting planes of the chart.
import all TauCeti.Combinatorics.Hive.Concave
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Piecewise-linear interpolation of lattice functions and the concavity criterion

The lines `y = const`, `z = const` and `y + z = const` through the integer points of the `(y, z)`
chart cut the triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` into the unit triangles of `Δₙ`.
`Hive.interpolation f` is the function on that triangle which agrees with `f : Vertex n → 𝕜` at
the lattice points and is affine on every closed unit triangle (`Hive.interpolation_vertex`,
`Hive.interpolation_up`, `Hive.interpolation_down`). The chart differs from the equilateral
embedding `Hive.Vertex.plane` by an affine change of coordinates, so concavity does not depend on
which of the two is used.

The main result is the concavity criterion `Hive.concaveOn_interpolation_iff`: the interpolation
is concave on the triangle exactly when `f` satisfies all unit-rhombus inequalities. In particular
the interpolation of every hive is concave (`Hive.concaveOn_interpolation`), which is how hives
are compared with real geometry (honeycombs, Hermitian spectra).

## Main definitions

* `TauCeti.Hive.interpolation f`: the interpolation of `f : Vertex n → 𝕜` that is affine on unit
  triangles.

## Main results

* `TauCeti.Hive.concaveOn_interpolation_iff`: the interpolation is concave iff `f` is
  rhombus-concave; `TauCeti.Hive.concaveOn_interpolation` for hives.

## Implementation notes

The forward direction of the criterion evaluates concavity at the common midpoint of the two
diagonals of a rhombus. The converse rests on the discrete supporting planes of
`TauCeti.Combinatorics.Hive.Concave` (`Hive.IsRhombusConcave.le_barycentricLinear`): an affine
function agreeing with a rhombus-concave function on one unit triangle majorizes it at every
lattice point. The interpolation is then, at every point, the value of an affine function that
majorizes it everywhere on the triangle, hence concave.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-! ### The piecewise-linear interpolation -/

section Triangle

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]

theorem convex_yzTriangle [IsOrderedRing 𝕜] : Convex 𝕜 (yzTriangle 𝕜 n) := by
  convert ((convex_halfSpace_ge (LinearMap.fst 𝕜 𝕜 𝕜).isLinear 0).inter
    (convex_halfSpace_ge (LinearMap.snd 𝕜 𝕜 𝕜).isLinear 0)).inter
    (convex_halfSpace_le (LinearMap.fst 𝕜 𝕜 𝕜 + LinearMap.snd 𝕜 𝕜 𝕜).isLinear (n : 𝕜)) using 1
  ext q
  simp [and_assoc]

end Triangle

section Interpolation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `YZConcave.le_affine` for field-valued functions, with the affine function in coordinates. -/
private theorem YZConcave.le_affine_of_corner {g : ℤ × ℤ → 𝕜} (hg : YZConcave n g)
    {k : Fin 6} {p : ℤ × ℤ} (hp : p ∈ yzTriangle ℤ n) (hk : p + yzStep k ∈ yzTriangle ℤ n)
    (hk₁ : p + yzStep (k + 1) ∈ yzTriangle ℤ n) {α β : 𝕜}
    (h₁ : ((yzStep k).1 : 𝕜) * α + ((yzStep k).2 : 𝕜) * β = g (p + yzStep k) - g p)
    (h₂ : ((yzStep (k + 1)).1 : 𝕜) * α + ((yzStep (k + 1)).2 : 𝕜) * β =
      g (p + yzStep (k + 1)) - g p) :
    ∀ v ∈ yzTriangle ℤ n, g v ≤ (g p - p.1 * α - p.2 * β) + α * v.1 + β * v.2 := by
  intro v hv
  have h := hg.le_affine hp hk hk₁ (α := α) (β := β) (by simpa [yzLinear_apply] using h₁)
    (by simpa [yzLinear_apply] using h₂) hv
  simp only [yzLinear_apply, Prod.fst_sub, Prod.snd_sub, zsmul_eq_mul, Int.cast_sub] at h
  linarith

/-- At a lattice point on the side `y + z = n`, a rhombus-concave function agrees with an affine
function that majorizes it at all lattice points of `Δₙ`. -/
private theorem YZConcave.exists_affine_of_add_eq {g : ℤ × ℤ → 𝕜} (hg : YZConcave n g)
    {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) (hij : i + j = n) :
    ∃ c₀ c₁ c₂ : 𝕜, g (i, j) = c₀ + c₁ * i + c₂ * j ∧
      ∀ v ∈ yzTriangle ℤ n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2 := by
  by_cases hj₁ : 1 ≤ j
  · -- the upward triangle below `(i, j)`
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 4) (p := (i, j))
      (α := g (i + 1, j - 1) - g (i, j - 1)) (β := g (i, j) - g (i, j - 1)) ⟨hi, hj, by omega⟩
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, sub_eq_add_neg]) (by simp [yzStep_def, sub_eq_add_neg])⟩
    ring
  by_cases hi₁ : 1 ≤ i
  · -- the upward triangle to the left of `(i, j)`
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 2) (p := (i, j))
      (α := g (i, j) - g (i - 1, j)) (β := g (i - 1, j + 1) - g (i - 1, j)) ⟨hi, hj, by omega⟩
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, sub_eq_add_neg]; ring) (by simp [yzStep_def, sub_eq_add_neg])⟩
    ring
  -- `n = 0`, and `Δₙ` is a single point
  refine ⟨g (i, j), 0, 0, by ring, fun v hv => ?_⟩
  obtain ⟨hv₁, hv₂, hv₃⟩ := hv
  obtain rfl : v = (i, j) := Prod.ext (by omega) (by omega)
  simp

variable [FloorRing 𝕜]

/-- The interpolation of `g : ℤ × ℤ → 𝕜` that is affine on the unit triangles cut out by the
lines `y = const`, `z = const` and `y + z = const`. -/
private def yzInterp (g : ℤ × ℤ → 𝕜) (q : 𝕜 × 𝕜) : 𝕜 :=
  if Int.fract q.1 + Int.fract q.2 ≤ 1 then
    (1 - Int.fract q.1 - Int.fract q.2) * g (⌊q.1⌋, ⌊q.2⌋) +
      Int.fract q.1 * g (⌊q.1⌋ + 1, ⌊q.2⌋) + Int.fract q.2 * g (⌊q.1⌋, ⌊q.2⌋ + 1)
  else
    (Int.fract q.1 + Int.fract q.2 - 1) * g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) +
      (1 - Int.fract q.2) * g (⌊q.1⌋ + 1, ⌊q.2⌋) + (1 - Int.fract q.1) * g (⌊q.1⌋, ⌊q.2⌋ + 1)

private theorem yzInterp_of_lt_one (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : 0 ≤ a)
    (ha₁ : a < 1) (hb : 0 ≤ b) (hb₁ : b < 1) :
    yzInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      if a + b ≤ 1 then (1 - a - b) * g (i, j) + a * g (i + 1, j) + b * g (i, j + 1)
      else (a + b - 1) * g (i + 1, j + 1) + (1 - b) * g (i + 1, j) + (1 - a) * g (i, j + 1) := by
  have hfa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha, ha₁⟩
  have hfb : Int.fract b = b := Int.fract_eq_self.mpr ⟨hb, hb₁⟩
  have hla : ⌊a⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ha, ha₁⟩
  have hlb : ⌊b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hb, hb₁⟩
  simp only [yzInterp, Int.fract_intCast_add, Int.floor_intCast_add, hfa, hfb, hla, hlb,
    add_zero]

private theorem yzInterp_intCast (g : ℤ × ℤ → 𝕜) (i j : ℤ) :
    yzInterp g ((i : 𝕜), (j : 𝕜)) = g (i, j) := by
  simpa using yzInterp_of_lt_one g i j (a := (0 : 𝕜)) (b := 0) le_rfl one_pos le_rfl one_pos

/-- On a closed upward unit triangle the interpolation is the barycentric combination of the
three corner values. -/
private theorem yzInterp_up (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    yzInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      (1 - a - b) * g (i, j) + a * g (i + 1, j) + b * g (i, j + 1) := by
  rcases (show a ≤ 1 by linarith).lt_or_eq with ha₁ | rfl
  · rcases (show b ≤ 1 by linarith).lt_or_eq with hb₁ | rfl
    · rw [yzInterp_of_lt_one g i j ha ha₁ hb hb₁, ite_eq_left hab]
    · obtain rfl : a = 0 := by linarith
      have := yzInterp_intCast g i (j + 1)
      push_cast at this
      rw [add_zero, this]
      ring
  · obtain rfl : b = 0 := by linarith
    have := yzInterp_intCast g (i + 1) j
    push_cast at this
    rw [add_zero, this]
    ring

/-- On a closed downward unit triangle the interpolation is the barycentric combination of the
three corner values. -/
private theorem yzInterp_down (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : 1 ≤ a + b) :
    yzInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      (a + b - 1) * g (i + 1, j + 1) + (1 - b) * g (i + 1, j) + (1 - a) * g (i, j + 1) := by
  rcases ha.lt_or_eq with ha₁ | rfl
  · rcases hb.lt_or_eq with hb₁ | rfl
    · rw [yzInterp_of_lt_one g i j (by linarith) ha₁ (by linarith) hb₁]
      split_ifs with h
      · obtain rfl : b = 1 - a := by linarith
        ring
      · rfl
    · have := yzInterp_up g i (j + 1) (a := a) (b := 0) (by linarith) le_rfl (by linarith)
      push_cast at this
      rw [add_zero] at this
      rw [this]
      ring
  · have := yzInterp_up g (i + 1) j (a := 0) (b := b) le_rfl (by linarith) (by linarith)
    push_cast at this
    rw [add_zero] at this
    rw [this]
    ring

/-- The interpolation of `f : Vertex n → 𝕜` over the triangle `yzTriangle 𝕜 n` of the `(y, z)`
chart: on each closed unit triangle it is the affine function through the values of `f` at the
three corners (`interpolation_vertex`, `interpolation_up`, `interpolation_down`). -/
def interpolation (f : Vertex n → 𝕜) : 𝕜 × 𝕜 → 𝕜 := yzInterp (yzExtend f)

/-- The interpolation of `f` agrees with `f` at every lattice point. -/
@[simp] theorem interpolation_vertex (f : Vertex n → 𝕜) (p : Vertex n) :
    interpolation f ((p.y : 𝕜), (p.z : 𝕜)) = f p := by
  have := yzInterp_intCast (yzExtend f) (p.y : ℤ) (p.z : ℤ)
  push_cast at this
  rw [interpolation, this, yzExtend_of_yz_eq f (p := p) (Prod.ext (by simp) (by simp))]

/-- On the upward unit triangle with corners `p`, `p + (1, 0)` and `p + (0, 1)` in the `(y, z)`
chart, the interpolation is the barycentric combination of the corner values. -/
theorem interpolation_up (f : Vertex n → 𝕜) {p q r : Vertex n} (hq : q.yz = p.yz + (1, 0))
    (hr : r.yz = p.yz + (0, 1)) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    interpolation f ((p.y : 𝕜) + a, (p.z : 𝕜) + b) = (1 - a - b) * f p + a * f q + b * f r := by
  have := yzInterp_up (yzExtend f) (p.y : ℤ) (p.z : ℤ) ha hb hab
  push_cast at this
  have e₀ : yzExtend f ((p.y : ℤ), (p.z : ℤ)) = f p :=
    yzExtend_of_yz_eq f (Prod.ext (by simp) (by simp))
  have e₁ : yzExtend f ((p.y : ℤ) + 1, (p.z : ℤ)) = f q :=
    yzExtend_of_yz_eq f (Prod.ext (by simp [hq]) (by simp [hq]))
  have e₂ : yzExtend f ((p.y : ℤ), (p.z : ℤ) + 1) = f r :=
    yzExtend_of_yz_eq f (Prod.ext (by simp [hr]) (by simp [hr]))
  rw [interpolation, this, e₀, e₁, e₂]

/-- On the downward unit triangle with corners `p`, `p - (1, 0)` and `p - (0, 1)` in the
`(y, z)` chart, the interpolation is the barycentric combination of the corner values. -/
theorem interpolation_down (f : Vertex n → 𝕜) {p q r : Vertex n} (hq : q.yz = p.yz + (-1, 0))
    (hr : r.yz = p.yz + (0, -1)) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    interpolation f ((p.y : 𝕜) - a, (p.z : 𝕜) - b) = (1 - a - b) * f p + a * f q + b * f r := by
  have := yzInterp_down (yzExtend f) ((p.y : ℤ) - 1) ((p.z : ℤ) - 1) (a := 1 - a)
    (b := 1 - b) (by linarith) (by linarith) (by linarith)
  push_cast at this
  simp only [sub_add_cancel] at this
  have e₀ : yzExtend f ((p.y : ℤ), (p.z : ℤ)) = f p :=
    yzExtend_of_yz_eq f (Prod.ext (by simp) (by simp))
  have e₁ : yzExtend f ((p.y : ℤ) - 1, (p.z : ℤ)) = f q :=
    yzExtend_of_yz_eq f (Prod.ext (by simp [hq]; ring) (by simp [hq]))
  have e₂ : yzExtend f ((p.y : ℤ), (p.z : ℤ) - 1) = f r :=
    yzExtend_of_yz_eq f (Prod.ext (by simp [hr]) (by simp [hr]; ring))
  rw [show ((p.y : 𝕜) - a, (p.z : 𝕜) - b) = ((p.y : 𝕜) - 1 + (1 - a), (p.z : 𝕜) - 1 + (1 - b)) by
    ext <;> ring, interpolation, this, e₀, e₁, e₂]
  ring

/-! ### The concavity criterion -/

/-- The unit cell of a point `q` of the triangle: its corner `(⌊q.1⌋, ⌊q.2⌋)` has nonnegative
coordinates, and moving it `k` steps along `y + z` stays in `Δₙ` whenever `k` is less than
`fract q.1 + fract q.2 + 1`. -/
private theorem floor_cell {q : 𝕜 × 𝕜} (hq : q ∈ yzTriangle 𝕜 n) :
    0 ≤ ⌊q.1⌋ ∧ 0 ≤ ⌊q.2⌋ ∧
      ∀ k : ℤ, (k : 𝕜) < Int.fract q.1 + Int.fract q.2 + 1 → ⌊q.1⌋ + ⌊q.2⌋ + k ≤ n := by
  obtain ⟨hq₁, hq₂, hq₃⟩ := hq
  refine ⟨Int.floor_nonneg.mpr hq₁, Int.floor_nonneg.mpr hq₂, fun k hk => ?_⟩
  have e₁ := Int.floor_add_fract q.1
  have e₂ := Int.floor_add_fract q.2
  have : ((⌊q.1⌋ + ⌊q.2⌋ + k - 1 : ℤ) : 𝕜) < n := by push_cast; linarith
  have : ⌊q.1⌋ + ⌊q.2⌋ + k - 1 < (n : ℤ) := by exact_mod_cast this
  omega

/-- An affine function majorizing `g` at the lattice points of `Δₙ` majorizes its interpolation on
the triangle. -/
private theorem yzInterp_le_of_forall_le {g : ℤ × ℤ → 𝕜} {c₀ c₁ c₂ : 𝕜}
    (hmaj : ∀ v ∈ yzTriangle ℤ n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2) {x : 𝕜 × 𝕜}
    (hx : x ∈ yzTriangle 𝕜 n) : yzInterp g x ≤ c₀ + c₁ * x.1 + c₂ * x.2 := by
  obtain ⟨hi, hj, hcell⟩ := floor_cell hx
  have ha := Int.fract_nonneg x.1
  have hb := Int.fract_nonneg x.2
  have ha₁ := Int.fract_lt_one x.1
  have hb₁ := Int.fract_lt_one x.2
  have e₁ := Int.floor_add_fract x.1
  have e₂ := Int.floor_add_fract x.2
  have term : ∀ (c : 𝕜) (v : ℤ × ℤ), 0 ≤ c → (0 < c → v ∈ yzTriangle ℤ n) →
      c * g v ≤ c * (c₀ + c₁ * v.1 + c₂ * v.2) := by
    intro c v hc hv
    rcases hc.lt_or_eq with hc | rfl
    · exact mul_le_mul_of_nonneg_left (hmaj v (hv hc)) hc.le
    · simp
  have h₀ : (⌊x.1⌋, ⌊x.2⌋) ∈ yzTriangle ℤ n :=
    ⟨hi, hj, by simpa using hcell 0 (by push_cast; linarith)⟩
  unfold yzInterp
  split_ifs with hab
  · have hlt (h : 0 < Int.fract x.1 + Int.fract x.2) : ⌊x.1⌋ + ⌊x.2⌋ + 1 ≤ n :=
      hcell 1 (by push_cast; linarith)
    calc _ ≤ (1 - Int.fract x.1 - Int.fract x.2) * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ⌊x.2⌋) +
          Int.fract x.1 * (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ⌊x.2⌋) +
          Int.fract x.2 * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) := by
          gcongr ?_ + ?_ + ?_
          · exact term _ _ (by linarith) fun _ => h₀
          · exact term _ _ ha fun h => ⟨by omega, hj, by have := hlt (by linarith); omega⟩
          · exact term _ _ hb fun h => ⟨hi, by omega, by have := hlt (by linarith); omega⟩
      _ = c₀ + c₁ * x.1 + c₂ * x.2 := by
          push_cast
          linear_combination c₁ * e₁ + c₂ * e₂
  · have hlt : ⌊x.1⌋ + ⌊x.2⌋ + 2 ≤ n := hcell 2 (by push_cast; linarith)
    calc _ ≤ (Int.fract x.1 + Int.fract x.2 - 1) *
          (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) +
          (1 - Int.fract x.2) * (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ⌊x.2⌋) +
          (1 - Int.fract x.1) * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) := by
          gcongr ?_ + ?_ + ?_
          · exact term _ _ (by linarith) fun _ => ⟨by omega, by omega, by omega⟩
          · exact term _ _ (by linarith) fun _ => ⟨by omega, hj, by omega⟩
          · exact term _ _ (by linarith) fun _ => ⟨hi, by omega, by omega⟩
      _ = c₀ + c₁ * x.1 + c₂ * x.2 := by
          push_cast
          linear_combination c₁ * e₁ + c₂ * e₂

/-- At every point of the triangle, the interpolation of a rhombus-concave function agrees with an
affine function that majorizes the function at all lattice points of `Δₙ`. -/
private theorem YZConcave.exists_affine {g : ℤ × ℤ → 𝕜} (hg : YZConcave n g) {q : 𝕜 × 𝕜}
    (hq : q ∈ yzTriangle 𝕜 n) :
    ∃ c₀ c₁ c₂ : 𝕜, yzInterp g q = c₀ + c₁ * q.1 + c₂ * q.2 ∧
      ∀ v ∈ yzTriangle ℤ n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2 := by
  obtain ⟨hi, hj, hcell⟩ := floor_cell hq
  have ha := Int.fract_nonneg q.1
  have hb := Int.fract_nonneg q.2
  have e₁ := Int.floor_add_fract q.1
  have e₂ := Int.floor_add_fract q.2
  have hle : ⌊q.1⌋ + ⌊q.2⌋ ≤ n := by simpa using hcell 0 (by push_cast; linarith)
  unfold yzInterp
  split_ifs with hab
  · by_cases hn : ⌊q.1⌋ + ⌊q.2⌋ + 1 ≤ n
    · -- the upward triangle at `(⌊y⌋, ⌊z⌋)`
      refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 0) (p := (⌊q.1⌋, ⌊q.2⌋))
        (α := g (⌊q.1⌋ + 1, ⌊q.2⌋) - g (⌊q.1⌋, ⌊q.2⌋))
        (β := g (⌊q.1⌋, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋)) ⟨hi, hj, by omega⟩
        (by simp [yzStep_def, mem_yzTriangle]; omega)
        (by simp [yzStep_def, mem_yzTriangle]; omega) (by simp [yzStep_def])
        (by simp [yzStep_def])⟩
      linear_combination (g (⌊q.1⌋ + 1, ⌊q.2⌋) - g (⌊q.1⌋, ⌊q.2⌋)) * e₁ +
        (g (⌊q.1⌋, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋)) * e₂
    · -- `q` is a lattice point on the side `y + z = n`
      have hs : ¬0 < Int.fract q.1 + Int.fract q.2 := fun h =>
        hn (hcell 1 (by push_cast; linarith))
      have hfa : Int.fract q.1 = 0 := by linarith
      have hfb : Int.fract q.2 = 0 := by linarith
      obtain ⟨c₀, c₁, c₂, hc, hmaj⟩ := hg.exists_affine_of_add_eq hi hj (by omega)
      refine ⟨c₀, c₁, c₂, ?_, hmaj⟩
      rw [hfa] at e₁
      rw [hfb] at e₂
      simp only [hfa, hfb, sub_zero, one_mul, zero_mul, add_zero, hc]
      linear_combination c₁ * e₁ + c₂ * e₂
  · -- the downward triangle with top corner `(⌊y⌋ + 1, ⌊z⌋ + 1)`
    have hlt : ⌊q.1⌋ + ⌊q.2⌋ + 2 ≤ n := hcell 2 (by push_cast; linarith)
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 3) (p := (⌊q.1⌋ + 1, ⌊q.2⌋ + 1))
      (α := g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋ + 1))
      (β := g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋ + 1, ⌊q.2⌋)) ⟨by omega, by omega, by omega⟩
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, mem_yzTriangle]; omega)
      (by simp [yzStep_def, sub_eq_add_neg]) (by simp [yzStep_def, sub_eq_add_neg])⟩
    push_cast
    linear_combination (g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋ + 1)) * e₁ +
      (g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋ + 1, ⌊q.2⌋)) * e₂

/-- `yzInterp_up` with the point (componentwise) and the value in any equal form. -/
private theorem yzInterp_eq_of_up (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) {q : 𝕜 × 𝕜} (hq₁ : q.1 = i + a) (hq₂ : q.2 = j + b) {c : 𝕜}
    (hc : (1 - a - b) * g (i, j) + a * g (i + 1, j) + b * g (i, j + 1) = c) :
    yzInterp g q = c := by
  rw [show q = ((i : 𝕜) + a, (j : 𝕜) + b) from Prod.ext hq₁ hq₂, yzInterp_up g i j ha hb hab, hc]

/-- The interpolation at the midpoint of a unit lattice edge is the average of the two ends. -/
private theorem yzInterp_midpoint (g : ℤ × ℤ → 𝕜) {x x' : ℤ × ℤ}
    (h : ∃ m, x' = x + yzStep m) :
    yzInterp g (((x.1 : 𝕜) + x'.1) / 2, ((x.2 : 𝕜) + x'.2) / 2) = (g x + g x') / 2 := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨i, j⟩ := x
  -- the edge is a side of the upward unit triangle at the componentwise minimum of its ends
  fin_cases m <;> [
    refine yzInterp_eq_of_up g i j (a := 1 / 2) (b := 0) (by norm_num) le_rfl (by norm_num)
      ?_ ?_ ?_;
    refine yzInterp_eq_of_up g i j (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
      ?_ ?_ ?_;
    refine yzInterp_eq_of_up g (i - 1) j (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) ?_ ?_ ?_;
    refine yzInterp_eq_of_up g (i - 1) j (a := 1 / 2) (b := 0) (by norm_num) le_rfl (by norm_num)
      ?_ ?_ ?_;
    refine yzInterp_eq_of_up g i (j - 1) (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
      ?_ ?_ ?_;
    refine yzInterp_eq_of_up g i (j - 1) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) ?_ ?_ ?_] <;>
    simp [yzStep_def, ← sub_eq_add_neg] <;> ring

/-- **The concavity criterion.** The interpolation of `f : Vertex n → 𝕜` is concave on the
triangle exactly when `f` satisfies every unit-rhombus inequality. -/
theorem concaveOn_interpolation_iff (f : Vertex n → 𝕜) :
    ConcaveOn 𝕜 (yzTriangle 𝕜 n) (interpolation f) ↔ IsRhombusConcave f := by
  constructor
  · intro hF
    rw [isRhombusConcave_def]
    intro a b c d h
    -- the common midpoint of the two diagonals lies on the unit edge from `a` to `c`
    have hmid := hF.2 (natCast_mem_yzTriangle b) (natCast_mem_yzTriangle d)
      (by norm_num : (0 : 𝕜) ≤ 1 / 2) (by norm_num : (0 : 𝕜) ≤ 1 / 2)
      (by norm_num : (1 / 2 : 𝕜) + 1 / 2 = 1)
    rw [interpolation_vertex, interpolation_vertex] at hmid
    have hpt : (1 / 2 : 𝕜) • ((b.y : 𝕜), (b.z : 𝕜)) + (1 / 2 : 𝕜) • ((d.y : 𝕜), (d.z : 𝕜)) =
        ((((a.yz.1 : ℤ) : 𝕜) + (c.yz.1 : ℤ)) / 2, (((a.yz.2 : ℤ) : 𝕜) + (c.yz.2 : ℤ)) / 2) := by
      have hy : (b.y : 𝕜) + d.y = a.y + c.y := by exact_mod_cast h.midpoint_y.symm
      have hz : (b.z : 𝕜) + d.z = a.z + c.z := by exact_mod_cast h.midpoint_z.symm
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
        Vertex.yz_fst, Vertex.yz_snd, Int.cast_natCast] <;> linarith
    rw [hpt, interpolation, yzInterp_midpoint _ (Vertex.sqDist_eq_two_iff.mp h.short),
      yzExtend_yz, yzExtend_yz] at hmid
    simp only [smul_eq_mul] at hmid
    linarith
  · intro hf
    have hg := yzConcave_yzExtend hf
    refine ⟨convex_yzTriangle, fun x hx y hy a b ha hb hab => ?_⟩
    obtain ⟨c₀, c₁, c₂, hz, hmaj⟩ := hg.exists_affine (convex_yzTriangle hx hy ha hb hab)
    have hx' := yzInterp_le_of_forall_le hmaj hx
    have hy' := yzInterp_le_of_forall_le hmaj hy
    simp only [interpolation, smul_eq_mul, hz, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd]
    have hxa := mul_le_mul_of_nonneg_left hx' ha
    have hyb := mul_le_mul_of_nonneg_left hy' hb
    linear_combination hxa + hyb + c₀ * hab

/-- The interpolation of a hive is concave on the triangle. -/
theorem concaveOn_interpolation (h : Hive n 𝕜) :
    ConcaveOn 𝕜 (yzTriangle 𝕜 n) (interpolation h) :=
  (concaveOn_interpolation_iff h).2 h.isRhombusConcave

end Interpolation

end TauCeti.Hive
