/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme
public import TauCeti.Analysis.InnerProductSpace.Projection.Diagonal

/-!
# The moment polygon of the word `121` Bott–Samelson variety

Let `P₀ = span(e₀, e₁) ⊆ ℂ³` (`TauCeti.BottSamelson.initialPlane`). The Bott–Samelson variety of
the word `121` in the flag variety of `ℂ³` is the incidence variety

`X = {(L₁, P, L) | L₁ ⊆ P₀, L₁ ⊆ P, L ⊆ P}`

of lines `L₁, L` and planes `P` of `ℂ³`, a smooth projective threefold. The torus `T = (S¹)³` acts
on `ℂ³` diagonally, preserves `P₀`, and so acts on `X`. Identifying lines and planes with their
orthogonal projectors `Π_V`, that is with coadjoint orbits of `U(3)`, the moment map of this action
for the weights `a, b, c` of the Kirillov–Kostant–Souriau forms of the three factors is the diagonal
of the Hermitian matrix `a Π_{L₁} + b Π_P + c Π_L`:

`μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)`

(`TauCeti.BottSamelson.moment`, built on `Submodule.projectorDiagonal`). This file works with this
map on triples of subspaces directly and describes its values combinatorially; no symplectic form
enters the statements.

The torus-fixed points of `X` are triples of coordinate subspaces. Writing `ij` for the plane
`span(eᵢ, eⱼ)` and `eᵢ` for the line it spans, eight such triples satisfy the incidence conditions,
and their moment values are the rows of `TauCeti.BottSamelson.fixedMoment`:

| `(L₁, P, L)` | `μ` |
| --- | --- |
| `(e₀, 01, e₀)` | `(a + b + c, b, 0)` |
| `(e₀, 01, e₁)` | `(a + b, b + c, 0)` |
| `(e₀, 02, e₀)` | `(a + b + c, 0, b)` |
| `(e₀, 02, e₂)` | `(a + b, 0, b + c)` |
| `(e₁, 01, e₀)` | `(b + c, a + b, 0)` |
| `(e₁, 01, e₁)` | `(b, a + b + c, 0)` |
| `(e₁, 12, e₁)` | `(0, a + b + c, b)` |
| `(e₁, 12, e₂)` | `(0, a + b, b + c)` |

For positive weights their convex hull is the hexagon (`TauCeti.BottSamelson.momentPolygon`)

`x + y + z = a + 2b + c,  0 ≤ x, y, z,  x ≤ a + b + c,  y ≤ a + b + c,  z ≤ b + c`

in the trace plane (`TauCeti.BottSamelson.convexHull_range_fixedMoment`). Its vertices are the
rows `0, 2, 3, 7, 6, 5` in cyclic order (`TauCeti.BottSamelson.extremePoints_momentPolygon`); the
rows `1` and `4` lie in the interior of the edge `z = 0` joining the rows `0` and `5`
(`TauCeti.BottSamelson.fixedMoment_one`, `TauCeti.BottSamelson.fixedMoment_four`). So, unlike for
a symplectic toric manifold, fixed points do not correspond to vertices; the effective torus is
two-dimensional, while `X` has real dimension six.

Every value of `μ` lies in the hexagon (`TauCeti.BottSamelson.moment_mem_convexHull`). The
diagonal entries of a projector lie in `[0, 1]` and sum to its rank, which gives the trace and the
first four bounds, and the third diagonal entry of `Π_{L₁}` vanishes because `L₁ ⊆ P₀`, which gives
`z ≤ b + c`. This is one inclusion of the description of the image of `μ` as the hexagon; the other
one, that every point of the hexagon is a moment value, is the content of the convexity theorem for
torus actions.

## Main definitions

* `TauCeti.BottSamelson.initialPlane`: the coordinate plane `P₀ = span(e₀, e₁)`.
* `TauCeti.BottSamelson.moment`: the weighted diagonal `a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)`.
* `TauCeti.BottSamelson.fixedMoment`: the moment values of the eight torus-fixed points.
* `TauCeti.BottSamelson.momentPolygon`: the hexagon cut out by the six inequalities above.

## Main results

* `TauCeti.BottSamelson.exists_moment_eq_fixedMoment`: each row of `fixedMoment` is the moment
  value of a triple of coordinate subspaces in `X`.
* `TauCeti.BottSamelson.sum_moment`: on `X`, the coordinates of `μ` sum to `a + 2b + c`.
* `TauCeti.BottSamelson.convexHull_range_fixedMoment`: the convex hull of the eight fixed values is
  the hexagon.
* `TauCeti.BottSamelson.extremePoints_momentPolygon`: the vertices of the hexagon are six of the
  eight fixed values.
* `TauCeti.BottSamelson.moment_mem_convexHull`: every moment value lies in that hexagon.

## References

* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin. 23
  (2016), §3.2 and §4.1 (Bott–Samelson varieties inside products of Grassmannians).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15;
  V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513 (the convexity theorem).
-/

public section

noncomputable section

namespace TauCeti.BottSamelson

open Module Set Submodule

/-! ### The weighted moment map -/

/-- The coordinate plane `P₀ = span(e₀, e₁)` of `ℂ³` containing the first line of a point of the
Bott–Samelson variety of the word `121`. -/
def initialPlane : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
  span ℂ {EuclideanSpace.single 0 1, EuclideanSpace.single 1 1}

/-- The plane `P₀` is the coordinate subspace of the coordinates `0` and `1`. -/
theorem initialPlane_eq_span_image :
    initialPlane =
      span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ({0, 1} : Set (Fin 3))) := by
  rw [initialPlane, image_pair]

/-- The diagonal of the projector onto `P₀` is `(1, 1, 0)`. -/
@[simp]
theorem projectorDiagonal_initialPlane : initialPlane.projectorDiagonal = ![1, 1, 0] := by
  rw [initialPlane_eq_span_image, projectorDiagonal_span_single]
  ext i
  fin_cases i <;> simp

theorem finrank_initialPlane : finrank ℂ initialPlane = 2 := by
  rw [initialPlane_eq_span_image, ← Finset.coe_pair, finrank_span_image_single]
  rfl

/-- The weighted moment map `μ(L₁, P, L) = a diag(Π_{L₁}) + b diag(Π_P) + c diag(Π_L)` of the
diagonal torus on triples of subspaces of `ℂ³`, the diagonal of the Hermitian matrix
`a Π_{L₁} + b Π_P + c Π_L`. -/
def moment (a b c : ℝ) (L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) : Fin 3 → ℝ :=
  a • L₁.projectorDiagonal + b • P.projectorDiagonal + c • L.projectorDiagonal

section Moment

variable (a b c : ℝ) (L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))

@[simp]
theorem moment_apply (i : Fin 3) :
    moment a b c L₁ P L i =
      a * L₁.projectorDiagonal i + b * P.projectorDiagonal i + c * L.projectorDiagonal i := (rfl)

/-- The moment map is additive in the weights. -/
theorem moment_add (a' b' c' : ℝ) :
    moment (a + a') (b + b') (c + c') L₁ P L = moment a b c L₁ P L + moment a' b' c' L₁ P L := by
  ext i
  simp only [moment_apply, Pi.add_apply]
  ring

/-- The moment map is homogeneous in the weights. -/
theorem moment_mul (r : ℝ) : moment (r * a) (r * b) (r * c) L₁ P L = r • moment a b c L₁ P L := by
  ext i
  simp only [moment_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {L₁ P L}

/-- On triples of a line, a plane and a line, the coordinates of the moment map sum to
`a + 2b + c`, the trace of `a Π_{L₁} + b Π_P + c Π_L`. -/
theorem sum_moment (hL₁ : finrank ℂ L₁ = 1) (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) :
    ∑ i, moment a b c L₁ P L i = a + 2 * b + c := by
  simp only [moment_apply, Finset.sum_add_distrib, ← Finset.mul_sum, sum_projectorDiagonal, hL₁,
    hP, hL]
  ring

end Moment

/-! ### The eight fixed values and the hexagon -/

/-- The moment values of the eight triples of coordinate subspaces in the Bott–Samelson variety of
the word `121`, in the order `(e₀, 01, e₀)`, `(e₀, 01, e₁)`, `(e₀, 02, e₀)`, `(e₀, 02, e₂)`,
`(e₁, 01, e₀)`, `(e₁, 01, e₁)`, `(e₁, 12, e₁)`, `(e₁, 12, e₂)`, where `ij` is the plane
`span(eᵢ, eⱼ)` (`TauCeti.BottSamelson.exists_moment_eq_fixedMoment`). -/
def fixedMoment (a b c : ℝ) : Fin 8 → Fin 3 → ℝ :=
  ![![a + b + c, b, 0], ![a + b, b + c, 0], ![a + b + c, 0, b], ![a + b, 0, b + c],
    ![b + c, a + b, 0], ![b, a + b + c, 0], ![0, a + b + c, b], ![0, a + b, b + c]]

/-- The hexagon `x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`,
`z ≤ b + c` in the trace plane of `ℝ³`; for positive weights it is the convex hull of the eight
fixed values (`TauCeti.BottSamelson.convexHull_range_fixedMoment`). -/
def momentPolygon (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {x | x 0 + x 1 + x 2 = a + 2 * b + c ∧ (∀ i, 0 ≤ x i) ∧ x 0 ≤ a + b + c ∧ x 1 ≤ a + b + c ∧
    x 2 ≤ b + c}

@[simp]
theorem mem_momentPolygon {a b c : ℝ} {x : Fin 3 → ℝ} :
    x ∈ momentPolygon a b c ↔ x 0 + x 1 + x 2 = a + 2 * b + c ∧ (∀ i, 0 ≤ x i) ∧
      x 0 ≤ a + b + c ∧ x 1 ≤ a + b + c ∧ x 2 ≤ b + c := Iff.rfl

theorem convex_momentPolygon (a b c : ℝ) : Convex ℝ (momentPolygon a b c) := by
  intro x hx y hy s t hs ht hst
  simp only [mem_momentPolygon, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  have hA : s * (a + b + c) + t * (a + b + c) = a + b + c := by rw [← add_mul, hst, one_mul]
  have hB : s * (b + c) + t * (b + c) = b + c := by rw [← add_mul, hst, one_mul]
  refine ⟨?_, fun i ↦ ?_, ?_, ?_, ?_⟩
  · linear_combination s * hx1 + t * hy1 + (a + 2 * b + c) * hst
  · have := hx2 i; have := hy2 i; positivity
  · linarith [mul_le_mul_of_nonneg_left hx3 hs, mul_le_mul_of_nonneg_left hy3 ht]
  · linarith [mul_le_mul_of_nonneg_left hx4 hs, mul_le_mul_of_nonneg_left hy4 ht]
  · linarith [mul_le_mul_of_nonneg_left hx5 hs, mul_le_mul_of_nonneg_left hy5 ht]

/-- For nonnegative weights, the eight fixed values lie in the hexagon. -/
theorem fixedMoment_mem_momentPolygon {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k : Fin 8) : fixedMoment a b c k ∈ momentPolygon a b c := by
  fin_cases k <;>
  · refine ⟨?_, fun i ↦ ?_, ?_, ?_, ?_⟩ <;> (try fin_cases i) <;> simp [fixedMoment] <;> linarith

/-- **The moment polygon of the word `121` Bott–Samelson variety.** For positive weights, the
convex hull of the moment values of the eight torus-fixed points is the hexagon
`momentPolygon a b c`. -/
theorem convexHull_range_fixedMoment {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    convexHull ℝ (range (fixedMoment a b c)) = momentPolygon a b c := by
  refine (convexHull_min ?_ (convex_momentPolygon a b c)).antisymm fun x hx ↦ ?_
  · rintro _ ⟨k, rfl⟩
    exact fixedMoment_mem_momentPolygon ha.le hb.le hc.le k
  -- Slice the hexagon at `z = b` into two trapezoids, and in each write `x` as a convex
  -- combination of the four corners: first along the `z`-direction between the two parallel
  -- sides, then proportionally along those sides.
  obtain ⟨hsum, hnn, hx0, hx1, hx2⟩ := hx
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  have key : ∀ w : Fin 8 → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
      ∑ k, w k • fixedMoment a b c k = x → x ∈ convexHull ℝ (range (fixedMoment a b c)) :=
    fun w hw0 hw1 hwx ↦ hwx ▸ (convex_convexHull ℝ _).sum_mem (fun k _ ↦ hw0 k) hw1
      fun k _ ↦ subset_convexHull ℝ _ (mem_range_self k)
  rcases le_total (x 2) b with hzb | hzb
  · -- the lower trapezoid `0 ≤ z ≤ b`, with vertices the rows `0, 5, 2, 6`
    set t := x 2 / b
    set l := (x 0 - b + x 2) / (a + c + x 2)
    have ht0 : 0 ≤ t := div_nonneg h2 hb.le
    have ht1 : t ≤ 1 := (div_le_one hb).2 hzb
    have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
    have hl1 : l ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    refine key ![(1 - t) * l, 0, t * l, 0, 0, (1 - t) * (1 - l), t * (1 - l), 0]
      (fun k ↦ by fin_cases k <;> simp <;> nlinarith) (by simp [Fin.sum_univ_eight]; ring) ?_
    have htb : t * b = x 2 := div_mul_cancel₀ _ hb.ne'
    have hl : l * (a + c + x 2) = x 0 - b + x 2 := div_mul_cancel₀ _ (by linarith)
    funext i
    fin_cases i <;> simp [Fin.sum_univ_eight, fixedMoment]
    · linear_combination hl - (1 - l) * htb
    · linear_combination -hsum - hl - l * htb
    · linear_combination htb
  · -- the upper trapezoid `b ≤ z ≤ b + c`, with vertices the rows `6, 2, 7, 3`
    set s := (x 2 - b) / c
    set m := x 0 / (a + 2 * b + c - x 2)
    have hsc : s * c = x 2 - b := div_mul_cancel₀ _ hc.ne'
    have hm : m * (a + 2 * b + c - x 2) = x 0 := div_mul_cancel₀ _ (by linarith)
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hc.le
    have hs1 : s ≤ 1 := (div_le_one hc).2 (by linarith)
    have hm0 : 0 ≤ m := div_nonneg h0 (by linarith)
    have hm1 : m ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    refine key ![0, 0, (1 - s) * m, s * m, 0, 0, (1 - s) * (1 - m), s * (1 - m)]
      (fun k ↦ by fin_cases k <;> simp <;> nlinarith) (by simp [Fin.sum_univ_eight]; ring) ?_
    funext i
    fin_cases i <;> simp [Fin.sum_univ_eight, fixedMoment]
    · linear_combination hm - m * hsc
    · linear_combination -hsum - hm - (1 - m) * hsc
    · linear_combination hsc

/-- The fixed value `(a + b, b + c, 0)` of `(e₀, 01, e₁)` lies on the edge `z = 0` of the hexagon,
between the vertices `(a + b + c, b, 0)` and `(b, a + b + c, 0)`, with barycentric coordinates
`a / (a + c)` and `c / (a + c)`. -/
theorem fixedMoment_one {a b c : ℝ} (h : a + c ≠ 0) :
    fixedMoment a b c 1 =
      (a / (a + c)) • fixedMoment a b c 0 + (c / (a + c)) • fixedMoment a b c 5 := by
  ext i
  fin_cases i <;> simp [fixedMoment] <;> field_simp <;> ring

/-- The fixed value `(b + c, a + b, 0)` of `(e₁, 01, e₀)` lies on the edge `z = 0` of the hexagon,
between the vertices `(a + b + c, b, 0)` and `(b, a + b + c, 0)`, with barycentric coordinates
`c / (a + c)` and `a / (a + c)`. -/
theorem fixedMoment_four {a b c : ℝ} (h : a + c ≠ 0) :
    fixedMoment a b c 4 =
      (c / (a + c)) • fixedMoment a b c 0 + (a / (a + c)) • fixedMoment a b c 5 := by
  ext i
  fin_cases i <;> simp [fixedMoment] <;> field_simp <;> ring

/-- **The vertices of the moment polygon.** For positive weights, the extreme points of the
hexagon are the six fixed values of the rows `0, 2, 3, 7, 6, 5`, in cyclic order. The fixed values
of the rows `1` and `4` lie in the interior of an edge and are not extreme. -/
theorem extremePoints_momentPolygon {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (momentPolygon a b c).extremePoints ℝ = fixedMoment a b c '' {0, 2, 3, 7, 6, 5} := by
  have hmem := fixedMoment_mem_momentPolygon ha.le hb.le hc.le
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨k, rfl⟩ : x ∈ range (fixedMoment a b c) := by
      rw [← convexHull_range_fixedMoment ha hb hc] at hx
      exact extremePoints_convexHull_subset hx
    refine mem_image_of_mem _ ?_
    have hD : a + c ≠ 0 := by positivity
    -- an extreme point lying in the open segment between the rows `0` and `5` equals the row `0`
    have hseg : ∀ u v : ℝ, 0 < u → 0 < v → u + v = 1 →
        fixedMoment a b c k = u • fixedMoment a b c 0 + v • fixedMoment a b c 5 →
          fixedMoment a b c 0 = fixedMoment a b c k := fun u v hu hv huv h ↦
      (mem_extremePoints_iff_left.1 hx).2 _ (hmem 0) _ (hmem 5) ⟨u, v, hu, hv, huv, h.symm⟩
    fin_cases k <;> simp
    · have := congrFun (hseg _ _ (by positivity) (by positivity) (by field_simp)
        (fixedMoment_one hD)) 0
      simp [fixedMoment] at this
      linarith
    · have := congrFun (hseg _ _ (by positivity) (by positivity) (by field_simp; ring)
        (fixedMoment_four hD)) 0
      simp [fixedMoment] at this
      linarith
  · rintro _ ⟨k, hk, rfl⟩
    refine mem_extremePoints_iff_left.2 ⟨hmem k, fun p hp q hq ⟨θ, φ, hθ, hφ, hθφ, hv⟩ ↦ ?_⟩
    -- a bound attained by a proper convex combination is attained by both points
    have tight : ∀ {u v M : ℝ}, u ≤ M → v ≤ M → θ * u + φ * v = M → u = M := by
      intro u v M hu hv h
      have h₁ : θ * (M - u) + φ * (M - v) = 0 := by linear_combination M * hθφ - h
      have h₂ := mul_nonneg hθ.le (sub_nonneg.2 hu)
      have h₃ := mul_nonneg hφ.le (sub_nonneg.2 hv)
      have h₄ : θ * (M - u) = 0 := by linarith
      linarith [(mul_eq_zero.1 h₄).resolve_left hθ.ne']
    obtain ⟨hp₁, hp₂, hp₃, hp₄, hp₅⟩ := hp
    obtain ⟨hq₁, hq₂, hq₃, hq₄, hq₅⟩ := hq
    have e₀ := congrFun hv 0
    have e₁ := congrFun hv 1
    have e₂ := congrFun hv 2
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    -- at each vertex two of the six inequalities are equalities
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fixedMoment,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Matrix.cons_val] at e₀ e₁ e₂
    · have h₀ := tight hp₃ hq₃ e₀
      have h₂ := tight (neg_nonpos.2 (hp₂ 2)) (neg_nonpos.2 (hq₂ 2)) (by linarith)
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith
    · have h₀ := tight hp₃ hq₃ e₀
      have h₁ := tight (neg_nonpos.2 (hp₂ 1)) (neg_nonpos.2 (hq₂ 1)) (by linarith)
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith
    · have h₁ := tight (neg_nonpos.2 (hp₂ 1)) (neg_nonpos.2 (hq₂ 1)) (by linarith)
      have h₂ := tight hp₅ hq₅ e₂
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith
    · have h₀ := tight (neg_nonpos.2 (hp₂ 0)) (neg_nonpos.2 (hq₂ 0)) (by linarith)
      have h₂ := tight hp₅ hq₅ e₂
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith
    · have h₀ := tight (neg_nonpos.2 (hp₂ 0)) (neg_nonpos.2 (hq₂ 0)) (by linarith)
      have h₁ := tight hp₄ hq₄ e₁
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith
    · have h₁ := tight hp₄ hq₄ e₁
      have h₂ := tight (neg_nonpos.2 (hp₂ 2)) (neg_nonpos.2 (hq₂ 2)) (by linarith)
      funext i; fin_cases i <;> simp [fixedMoment] <;> linarith

/-! ### Moment values -/

/-- Each fixed value is the moment value of a triple of coordinate subspaces in the Bott–Samelson
variety of the word `121`: a line `L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line `L ⊆ P`. -/
theorem exists_moment_eq_fixedMoment (a b c : ℝ) (k : Fin 8) :
    ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
      finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
        moment a b c L₁ P L = fixedMoment a b c k := by
  -- the coordinate subspace spanned by the `eᵢ` with `i ∈ s`
  let C : Finset (Fin 3) → Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
    fun s ↦ span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' s)
  have hC : ∀ {s t : Finset (Fin 3)}, s ⊆ t → C s ≤ C t :=
    fun h ↦ span_mono (image_mono (Finset.coe_subset.2 h))
  have key : ∀ i j l : Fin 3, i ≠ j → i ∈ ({0, 1} : Finset (Fin 3)) → l ∈ ({i, j} : Finset _) →
      moment a b c (C {i}) (C {i, j}) (C {l}) = fixedMoment a b c k →
      ∃ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 ∧ finrank ℂ P = 2 ∧
        finrank ℂ L = 1 ∧ L₁ ≤ initialPlane ∧ L₁ ≤ P ∧ L ≤ P ∧
          moment a b c L₁ P L = fixedMoment a b c k := by
    intro i j l hij hi hl hμ
    refine ⟨C {i}, C {i, j}, C {l}, finrank_span_image_single _, ?_, finrank_span_image_single _,
      ?_, hC (by simp), hC (by simpa using hl), hμ⟩
    · rw [finrank_span_image_single, Finset.card_pair hij]
    · rw [initialPlane_eq_span_image, ← Finset.coe_pair]
      exact hC (by simpa using hi)
  have hμ : ∀ s t u : Finset (Fin 3), moment a b c (C s) (C t) (C u) =
      a • (s : Set (Fin 3)).indicator 1 + b • (t : Set (Fin 3)).indicator 1 +
        c • (u : Set (Fin 3)).indicator 1 := by
    intro s t u
    simp only [moment, C, projectorDiagonal_span_single]
  -- the indices `(i, j, l)` of the triple `(eᵢ, span(eᵢ, eⱼ), eₗ)` with moment value the row `k`
  let f : Fin 8 → Fin 3 × Fin 3 × Fin 3 := ![(0, 1, 0), (0, 1, 1), (0, 2, 0), (0, 2, 2),
    (1, 0, 0), (1, 0, 1), (1, 2, 1), (1, 2, 2)]
  refine key (f k).1 (f k).2.1 (f k).2.2 (by fin_cases k <;> decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide) ?_
  rw [hμ]
  ext i
  fin_cases k <;> fin_cases i <;> simp [f, fixedMoment]

/-- Every moment value of the Bott–Samelson variety of the word `121` lies in the hexagon, for
nonnegative weights. The incidences `L₁ ⊆ P` and `L ⊆ P` are not needed. -/
theorem moment_mem_momentPolygon {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))} (hL₁ : finrank ℂ L₁ = 1)
    (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) (h : L₁ ≤ initialPlane) :
    moment a b c L₁ P L ∈ momentPolygon a b c := by
  -- the third basis vector is orthogonal to `P₀`, hence to `L₁`
  have h₂ : L₁.projectorDiagonal 2 = 0 := by
    refine (projectorDiagonal_eq_zero_iff _).2 (orthogonal_le h ?_)
    rw [← projectorDiagonal_eq_zero_iff, projectorDiagonal_initialPlane]
    rfl
  have hsum := sum_moment a b c hL₁ hP hL
  rw [Fin.sum_univ_three] at hsum
  have h0 := fun i ↦ L₁.projectorDiagonal_nonneg i
  have h1 := fun i ↦ P.projectorDiagonal_nonneg i
  have h2 := fun i ↦ L.projectorDiagonal_nonneg i
  have h3 := fun i ↦ L₁.projectorDiagonal_le_one i
  have h4 := fun i ↦ P.projectorDiagonal_le_one i
  have h5 := fun i ↦ L.projectorDiagonal_le_one i
  refine ⟨hsum, fun i ↦ ?_, ?_, ?_, ?_⟩ <;> simp only [moment_apply]
  · have := h0 i; have := h1 i; have := h2 i; positivity
  · nlinarith [mul_le_mul_of_nonneg_left (h3 0) ha, mul_le_mul_of_nonneg_left (h4 0) hb,
      mul_le_mul_of_nonneg_left (h5 0) hc]
  · nlinarith [mul_le_mul_of_nonneg_left (h3 1) ha, mul_le_mul_of_nonneg_left (h4 1) hb,
      mul_le_mul_of_nonneg_left (h5 1) hc]
  · rw [h₂, mul_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left (h4 2) hb, mul_le_mul_of_nonneg_left (h5 2) hc]

/-- For positive weights, every moment value of the Bott–Samelson variety of the word `121` lies in
the convex hull of the moment values of its eight torus-fixed points. -/
theorem moment_mem_convexHull {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))} (hL₁ : finrank ℂ L₁ = 1)
    (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1) (h : L₁ ≤ initialPlane) :
    moment a b c L₁ P L ∈ convexHull ℝ (range (fixedMoment a b c)) := by
  rw [convexHull_range_fixedMoment ha hb hc]
  exact moment_mem_momentPolygon ha.le hb.le hc.le hL₁ hP hL h

end TauCeti.BottSamelson
