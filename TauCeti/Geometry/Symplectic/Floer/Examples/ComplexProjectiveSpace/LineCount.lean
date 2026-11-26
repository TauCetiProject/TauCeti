/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Lines through two points meeting a hyperplane

The three-point Gromov–Witten class `⟨x, x^n, x^n⟩_L` of `ℙⁿ` in the line class `L` counts, with
signs and once the evaluation map is transverse to `H × {p} × {q}`, the lines through two given
points `p` and `q` that meet a given hyperplane `H`, marked at their point on `H`, at `p` and at
`q`. It is the number to which
`TauCeti.ComplexProjectiveSpace.trilinearProduct_pow_succ_apply_eq_single_smul` reduces the
quantum relation `x^(⋆(n+1)) = q^L · 1` of `ℙⁿ`. This file proves, in linear algebra over any
field `K`, that there is exactly one such marked line and that the linearized incidence
conditions are onto.

A degree-one map `ℙ¹ → ℙ(V)` is the projectivization of an injective linear map
`A : K × K →ₗ[K] V`, and `A` and `c • A`, for `c ≠ 0`, give the same map. A three-pointed
domain of genus zero has no moduli and its marks may be put at `[1 : 1]`, `[1 : 0]` and
`[0 : 1]`. Let `H = ℙ(ker f)` for a linear functional `f`, and let `p = [v]` and `q = [w]`.
The incidence conditions

* `[A (1, 1)] ∈ H`, that is `f (A (1, 1)) = 0`,
* `[A (1, 0)] = p`, that is `A (1, 0) ∈ K ∙ v`,
* `[A (0, 1)] = q`, that is `A (0, 1) ∈ K ∙ w`,

are linear in `A`: they cut out the kernel of the linear map
`TauCeti.ComplexProjectiveSpace.lineIncidenceMap f v w`,
`A ↦ (f (A (1, 1)), [A (1, 0)], [A (0, 1)]) ∈ K × V ⧸ K ∙ v × V ⧸ K ∙ w`.
For an injective `A` they say exactly that the map `ℙ(A)` sends the three marks to `H`, `p` and
`q` (`TauCeti.ComplexProjectiveSpace.mem_ker_lineIncidenceMap_iff_map`).

* **The solution.** The map `TauCeti.ComplexProjectiveSpace.markedLine f v w`,
  `(s, t) ↦ s • f w • v - t • f v • w`, satisfies the conditions, and when `p` or `q` lies off
  `H` every solution is a multiple of it
  (`TauCeti.ComplexProjectiveSpace.ker_lineIncidenceMap`). So the solutions form a line
  (`TauCeti.ComplexProjectiveSpace.finrank_ker_lineIncidenceMap`), and there is exactly one
  point of `ℙ(K × K →ₗ[K] V)` satisfying the conditions
  (`TauCeti.ComplexProjectiveSpace.existsUnique_submodule_le_ker_lineIncidenceMap`).
* **It is the line through `p` and `q`.** If `p ≠ q` and both lie off `H`, the solution is
  injective (`TauCeti.ComplexProjectiveSpace.injective_markedLine`), so it is a degree-one map,
  and its image is the plane `span {v, w}`
  (`TauCeti.ComplexProjectiveSpace.range_markedLine`): the line through `p` and `q`, which
  `Projectivization.line_unique` shows is the only line through them. That line meets `H` in
  exactly one point, the image of the mark `[1 : 1]`
  (`TauCeti.ComplexProjectiveSpace.range_markedLine_inf_ker`).
* **Transversality.** The linear map `lineIncidenceMap f v w` is onto as soon as `p` or `q` lies
  off `H` (`TauCeti.ComplexProjectiveSpace.surjective_lineIncidenceMap`). Its target is the
  normal space of `H × {p} × {q}` in `ℙ(V)³` at the image of the marks, written in the
  representatives `A (1, 1)`, `v` and `w`, and its source is the space of parametrizations,
  whose quotient by the scalar direction `K ∙ A` is the tangent space of the space of
  degree-one maps at `[A]`. Its surjectivity is the linear form of the transversality of the
  evaluation map to `H × {p} × {q}`, and its kernel `K ∙ markedLine f v w`, the scalar
  direction itself, is the infinitesimal form of the intersection being a single reduced point.
  For
  `V = ℂⁿ⁺¹` the dimensions are `2 (n + 1)`, `1 + n + n` and `1`.

The identification of the three-pointed stable maps in the line class with these
parametrizations, of the tangent spaces of `ℙ(V)` and of the space of stable maps with the
quotients above, and the orientation sign of the intersection point, are not treated here.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, in *Algebraic
  geometry, Santa Cruz 1995*, Proc. Sympos. Pure Math. 62, Part 2 (1997), 45–96, §10.
-/

public section

open Module Submodule

namespace TauCeti.ComplexProjectiveSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The **linearized incidence conditions** of a parametrized line `A : K × K →ₗ[K] V` with marks
`[1 : 1]`, `[1 : 0]` and `[0 : 1]`: `A ↦ (f (A (1, 1)), [A (1, 0)], [A (0, 1)])`, with values in
`K × V ⧸ K ∙ v × V ⧸ K ∙ w`. Its kernel consists of the parametrizations sending the three marks
into the hyperplane `ker f`, to `[v]` and to `[w]`. -/
def lineIncidenceMap (f : Dual K V) (v w : V) :
    (K × K →ₗ[K] V) →ₗ[K] K × (V ⧸ K ∙ v) × (V ⧸ K ∙ w) :=
  (f ∘ₗ LinearMap.applyₗ (1, 1)).prod
    (((K ∙ v).mkQ ∘ₗ LinearMap.applyₗ (1, 0)).prod ((K ∙ w).mkQ ∘ₗ LinearMap.applyₗ (0, 1)))

@[simp]
theorem lineIncidenceMap_apply (f : Dual K V) (v w : V) (A : K × K →ₗ[K] V) :
    lineIncidenceMap f v w A =
      (f (A (1, 1)), (K ∙ v).mkQ (A (1, 0)), (K ∙ w).mkQ (A (0, 1))) :=
  (rfl)

/-- A parametrized line satisfies the incidence conditions exactly when it sends the mark
`[1 : 1]` into `ker f`, the mark `[1 : 0]` into `K ∙ v` and the mark `[0 : 1]` into `K ∙ w`. -/
theorem mem_ker_lineIncidenceMap_iff {f : Dual K V} {v w : V} {A : K × K →ₗ[K] V} :
    A ∈ LinearMap.ker (lineIncidenceMap f v w) ↔
      f (A (1, 1)) = 0 ∧ A (1, 0) ∈ K ∙ v ∧ A (0, 1) ∈ K ∙ w := by
  simp [Prod.ext_iff, Submodule.Quotient.mk_eq_zero]

/-- For an injective parametrization `A`, the incidence conditions say that the degree-one map
`ℙ(A) : ℙ(K × K) → ℙ(V)` sends the mark `[1 : 1]` into the hyperplane `ℙ(ker f)`, the mark
`[1 : 0]` to `[v]` and the mark `[0 : 1]` to `[w]`. -/
theorem mem_ker_lineIncidenceMap_iff_map {f : Dual K V} {v w : V} {A : K × K →ₗ[K] V}
    (hA : Function.Injective A) (hv : v ≠ 0) (hw : w ≠ 0) :
    A ∈ LinearMap.ker (lineIncidenceMap f v w) ↔
      (Projectivization.map A hA (.mk K (1, 1) (by simp))).submodule ≤ LinearMap.ker f ∧
      Projectivization.map A hA (.mk K (1, 0) (by simp)) = .mk K v hv ∧
      Projectivization.map A hA (.mk K (0, 1) (by simp)) = .mk K w hw := by
  rw [mem_ker_lineIncidenceMap_iff]
  simp only [Projectivization.map_mk, Projectivization.submodule_mk, span_singleton_le_iff_mem,
    LinearMap.mem_ker, Projectivization.mk_eq_mk_iff', ← mem_span_singleton]

/-- The **line through `[v]` and `[w]` marked at its point on `ker f`**: the parametrization
`(s, t) ↦ s • f w • v - t • f v • w`, which sends `[1 : 0]` to `[v]`, `[0 : 1]` to `[w]` and
`[1 : 1]` to `[f w • v - f v • w]`, a point of the hyperplane `ker f`. -/
def markedLine (f : Dual K V) (v w : V) : K × K →ₗ[K] V :=
  (LinearMap.toSpanSingleton K V (f w • v)).coprod (LinearMap.toSpanSingleton K V ((-f v) • w))

@[simp]
theorem markedLine_apply (f : Dual K V) (v w : V) (z : K × K) :
    markedLine f v w z = z.1 • f w • v - z.2 • f v • w := by
  simp [markedLine, sub_eq_add_neg, smul_smul]

/-- The marked line satisfies the incidence conditions. -/
theorem markedLine_mem_ker_lineIncidenceMap (f : Dual K V) (v w : V) :
    markedLine f v w ∈ LinearMap.ker (lineIncidenceMap f v w) := by
  rw [mem_ker_lineIncidenceMap_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp [mul_comm]
  · simpa using smul_mem _ (f w) (mem_span_singleton_self v)
  · simpa using smul_mem _ (-f v) (mem_span_singleton_self w)

/-- **The incidence conditions have a unique solution up to scalars.** If `[v]` or `[w]` lies
off the hyperplane `ker f`, every parametrized line sending `[1 : 1]` into `ker f`, `[1 : 0]` to
`[v]` and `[0 : 1]` to `[w]` is a multiple of `markedLine f v w`. -/
theorem ker_lineIncidenceMap {f : Dual K V} {v w : V} (h : f v ≠ 0 ∨ f w ≠ 0) :
    LinearMap.ker (lineIncidenceMap f v w) = K ∙ markedLine f v w := by
  refine le_antisymm (fun A hA ↦ ?_) ((span_singleton_le_iff_mem _ _).2
    (markedLine_mem_ker_lineIncidenceMap f v w))
  obtain ⟨hH, hv, hw⟩ := mem_ker_lineIncidenceMap_iff.1 hA
  obtain ⟨a, ha⟩ := mem_span_singleton.1 hv
  obtain ⟨b, hb⟩ := mem_span_singleton.1 hw
  -- `A` is determined by `A (1, 0) = a • v` and `A (0, 1) = b • w`, and the hyperplane
  -- condition is the linear equation `a * f v + b * f w = 0` on the pair `(a, b)`.
  have hA' : A = (LinearMap.toSpanSingleton K V (a • v)).coprod
      (LinearMap.toSpanSingleton K V (b • w)) := by
    ext <;> simp [ha, hb]
  have hab : a * f v + b * f w = 0 := by
    have : A (1, 1) = A (1, 0) + A (0, 1) := by rw [← map_add]; simp
    simpa [this, ← ha, ← hb] using hH
  -- Solve the equation: `(a, b)` is a multiple of `(f w, -f v)`.
  obtain ⟨c, rfl, rfl⟩ : ∃ c, a = c * f w ∧ b = -(c * f v) := by
    rcases h with h | h
    · refine ⟨-b / f v, ?_, ?_⟩ <;> field_simp
      linear_combination hab
    · refine ⟨a / f w, ?_, ?_⟩ <;> field_simp
      linear_combination hab
  refine mem_span_singleton.2 ⟨c, ?_⟩
  rw [hA']
  ext <;> simp [smul_smul]

/-- The marked line is nonzero when `v` and `w` are nonzero and `[v]` or `[w]` lies off the
hyperplane `ker f`. -/
theorem markedLine_ne_zero {f : Dual K V} {v w : V} (h : f v ≠ 0 ∨ f w ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) : markedLine f v w ≠ 0 := by
  intro h0
  rcases h with h | h
  · simpa [h, hw] using LinearMap.congr_fun h0 (0, 1)
  · simpa [h, hv] using LinearMap.congr_fun h0 (1, 0)

/-- **The solutions of the incidence conditions form a line** when `v` and `w` are nonzero and
`[v]` or `[w]` lies off the hyperplane `ker f`. -/
theorem finrank_ker_lineIncidenceMap {f : Dual K V} {v w : V} (h : f v ≠ 0 ∨ f w ≠ 0)
    (hv : v ≠ 0) (hw : w ≠ 0) : finrank K (LinearMap.ker (lineIncidenceMap f v w)) = 1 := by
  rw [ker_lineIncidenceMap h, finrank_span_singleton (markedLine_ne_zero h hv hw)]

/-- A point of the projective space of parametrized lines satisfies the incidence conditions
exactly when it is the class of `markedLine f v w`. -/
theorem submodule_le_ker_lineIncidenceMap_iff {f : Dual K V} {v w : V} (h : f v ≠ 0 ∨ f w ≠ 0)
    (hv : v ≠ 0) (hw : w ≠ 0) (x : Projectivization K (K × K →ₗ[K] V)) :
    x.submodule ≤ LinearMap.ker (lineIncidenceMap f v w) ↔
      x = .mk K (markedLine f v w) (markedLine_ne_zero h hv hw) := by
  conv_lhs => rw [ker_lineIncidenceMap h, Projectivization.submodule_eq,
    span_singleton_le_iff_mem, mem_span_singleton]
  conv_rhs => rw [← Projectivization.mk_rep x]
  rw [Projectivization.mk_eq_mk_iff']

/-- **The count of marked lines.** If `v` and `w` are nonzero and `[v]` or `[w]` lies off the
hyperplane `ker f`, exactly one point of the projective space of parametrized lines sends the
marks `[1 : 1]`, `[1 : 0]` and `[0 : 1]` into `ker f`, to `[v]` and to `[w]`. -/
theorem existsUnique_submodule_le_ker_lineIncidenceMap {f : Dual K V} {v w : V}
    (h : f v ≠ 0 ∨ f w ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃! x : Projectivization K (K × K →ₗ[K] V),
      x.submodule ≤ LinearMap.ker (lineIncidenceMap f v w) :=
  ⟨_, (submodule_le_ker_lineIncidenceMap_iff h hv hw _).2 rfl,
    fun x hx ↦ (submodule_le_ker_lineIncidenceMap_iff h hv hw x).1 hx⟩

/-- **The incidence conditions are transverse.** If `[v]` or `[w]` lies off the hyperplane
`ker f`, the linearized incidence conditions are onto `K × V ⧸ K ∙ v × V ⧸ K ∙ w`. -/
theorem surjective_lineIncidenceMap {f : Dual K V} {v w : V} (h : f v ≠ 0 ∨ f w ≠ 0) :
    Function.Surjective (lineIncidenceMap f v w) := by
  rintro ⟨c, x, y⟩
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  induction y using Submodule.Quotient.induction_on with | H y => ?_
  -- Send `[1 : 0]` to `x + a • v` and `[0 : 1]` to `y + b • w`, and solve the hyperplane
  -- condition `f x + f y + a * f v + b * f w = c` for `a` or for `b`.
  obtain ⟨a, b, hab⟩ : ∃ a b : K, f (x + a • v) + f (y + b • w) = c := by
    rcases h with h | h
    · exact ⟨(c - f x - f y) / f v, 0, by simp; field_simp; ring⟩
    · exact ⟨0, (c - f x - f y) / f w, by simp; field_simp; ring⟩
  refine ⟨(LinearMap.toSpanSingleton K V (x + a • v)).coprod
    (LinearMap.toSpanSingleton K V (y + b • w)), Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · simpa using hab
  · simp
  · simp

/-- **The marked line is a degree-one map.** If `[v] ≠ [w]` and both lie off the hyperplane
`ker f`, the parametrization `markedLine f v w` is injective. -/
theorem injective_markedLine {f : Dual K V} {v w : V} (hv : f v ≠ 0) (hw : f w ≠ 0)
    (hvw : LinearIndependent K ![v, w]) : Function.Injective (markedLine f v w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨s, t⟩ hst
  rw [markedLine_apply, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul] at hst
  obtain ⟨hs, ht⟩ := LinearIndependent.pair_iff.1 hvw _ _ hst
  simp_all

/-- **The marked line passes through `[v]` and `[w]`**: if both lie off the hyperplane `ker f`,
its image is the plane `span {v, w}`. -/
theorem range_markedLine {f : Dual K V} {v w : V} (hv : f v ≠ 0) (hw : f w ≠ 0) :
    LinearMap.range (markedLine f v w) = span K {v, w} := by
  rw [markedLine, LinearMap.range_coprod, LinearMap.range_toSpanSingleton,
    LinearMap.range_toSpanSingleton, span_singleton_smul_eq (Ne.isUnit hw),
    span_singleton_smul_eq (neg_ne_zero.2 hv).isUnit, span_insert]

/-- **The marked line meets the hyperplane only at its mark `[1 : 1]`**: the image of
`markedLine f v w` meets `ker f` in the span of its value at `(1, 1)`. -/
theorem range_markedLine_inf_ker (f : Dual K V) (v w : V) :
    LinearMap.range (markedLine f v w) ⊓ LinearMap.ker f = K ∙ markedLine f v w (1, 1) := by
  refine le_antisymm (fun x hx ↦ ?_) (le_inf ?_ ?_)
  · obtain ⟨⟨⟨s, t⟩, rfl⟩, hfx⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, markedLine_apply] at hfx
    rw [mem_span_singleton]
    by_cases h : f v * f w = 0
    · -- Then `f v • w = 0` or `f w • v = 0`, and the line is spanned by the other vector.
      rcases mul_eq_zero.1 h with h | h
      · exact ⟨s, by simp [h]⟩
      · exact ⟨t, by simp [h]⟩
    · -- Otherwise the hyperplane condition `(s - t) * f v * f w = 0` forces `s = t`.
      have hst : s = t := by
        have : (s - t) * (f v * f w) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul] at hfx
          linear_combination hfx
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h)
      subst hst
      exact ⟨s, by simp [smul_sub]⟩
  · exact (span_singleton_le_iff_mem _ _).2 (LinearMap.mem_range_self _ _)
  · rw [span_singleton_le_iff_mem, LinearMap.mem_ker]
    simp [mul_comm]

end TauCeti.ComplexProjectiveSpace
