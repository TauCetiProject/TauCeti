/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.ScalarComposition
public import TauCeti.Geometry.Manifold.Morse.Sphere.Degenerate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Morse–Bott functions of the height on the sphere

Let `h` be the height function on the unit sphere `Sⁿ` in the direction of a unit vector `v`
(`TauCeti.sphereHeight`) and `φ : ℝ → ℝ` a change of values. The critical points of `φ ∘ h` are
the two poles and the latitudes `h = c` at the critical points `c` of `φ`
(`TauCeti.criticalPoints_comp_sphereHeight`). This file describes their nondegeneracy and their
Morse indices.

* **The poles.** The poles are nondegenerate critical points of `h`, so they remain nondegenerate
  for `φ ∘ h` when `φ'(±1) ≠ 0`. The north pole has Morse index `n` when `φ'(1) > 0` and `0` when
  `φ'(1) < 0`; the south pole has index `0` when `φ'(-1) > 0` and `n` when `φ'(-1) < 0`.
* **The latitudes.** Every level `h = c` with `c ≠ ±1` is a regular level of `h`
  (`TauCeti.isRegularValue_sphereHeight`), hence, when `n ≥ 1`, an embedded hypersurface
  (`TauCeti.isSmoothEmbedding_coe_regularLevel`). If `φ'(c) = 0` and `φ''(c) ≠ 0`, it is a
  Morse–Bott critical submanifold of `φ ∘ h`
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_sphereHeight`). At each of its
  points the Morse index is `0` when `φ''(c) > 0`
  (`TauCeti.manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg`) and `1` when
  `φ''(c) < 0` (`TauCeti.manifoldMorseIndex_comp_sphereHeight_eq_one_of_iteratedDeriv_two_neg`).

Two examples are worked out, the standard test cases for Morse–Bott complexes on the sphere.

* **Two caps.** For `f = h²` the critical set is the equator `h = 0` and the two poles
  (`TauCeti.criticalPoints_sq_comp_sphereHeight`). The equator is a Morse–Bott critical
  submanifold of index `0`, and both poles are nondegenerate critical points of index `n`.
* **Four critical levels.** For `f = b h - h³` with `0 < b < 3` put `a = √(b / 3)`, which lies
  in `(0, 1)`. The critical set consists of the latitudes `h = -a` and `h = a` and the two poles
  (`TauCeti.criticalPoints_mul_sub_pow_three_comp_sphereHeight`). The latitude `h = -a` is a
  Morse–Bott critical submanifold of index `0` with value `-2ab/3`; the south pole is a
  nondegenerate local maximum of index `n` with value `1 - b`; the north pole is a nondegenerate
  local minimum of index `0` with value `b - 1`; and the latitude `h = a` is a Morse–Bott critical
  submanifold of index `1` with value `2ab/3`. For `b = 5/4` these values are
  `-5a/6 < -1/4 < 1/4 < 5a/6`. When `n ≥ 2` the latitudes are connected (this is not proved here),
  so the critical set has four components, and on `S²` their negative normal ranks in this order
  are `0, 2, 0, 1`.

The Morse–Bott statements are made for any smooth embedding of a hypersurface into the level, such
as, when `n ≥ 1`, the inclusion of the level with the atlas `TauCeti.regularLevelChartedSpace`.
The Morse index statements are made pointwise.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {φ : ℝ → ℝ}

/-! ### The poles -/

/-- The north pole is a nondegenerate critical point of `φ ∘ h` when `φ'(1) ≠ 0`. -/
theorem isManifoldNondegenerateCriticalPoint_comp_sphereHeight_self (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ 1) (hφ' : deriv φ 1 ≠ 0) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (φ ∘ sphereHeight v) v :=
  (isManifoldNondegenerateCriticalPoint_sphereHeight_self v).scalar_comp
    (by rwa [sphereHeight_self]) (by rwa [sphereHeight_self])

/-- The south pole is a nondegenerate critical point of `φ ∘ h` when `φ'(-1) ≠ 0`. -/
theorem isManifoldNondegenerateCriticalPoint_comp_sphereHeight_neg (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ (-1)) (hφ' : deriv φ (-1) ≠ 0) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (φ ∘ sphereHeight v) (-v) :=
  (isManifoldNondegenerateCriticalPoint_sphereHeight_neg v).scalar_comp
    (by rwa [sphereHeight_neg_self]) (by rwa [sphereHeight_neg_self])

/-- The Morse index of `φ ∘ h` at the north pole is `n` when `φ'(1) > 0`. -/
theorem manifoldMorseIndex_comp_sphereHeight_self_of_pos (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ 1) (hφ' : 0 < deriv φ 1) :
    manifoldMorseIndex (𝓡 n) (φ ∘ sphereHeight v) v = n := by
  rw [manifoldMorseIndex_scalar_comp_of_pos (contMDiff_sphereHeight v v)
    (by rwa [sphereHeight_self]) (by simp) (by rwa [sphereHeight_self]),
    manifoldMorseIndex_sphereHeight_self]

/-- The Morse index of `φ ∘ h` at the north pole is `0` when `φ'(1) < 0`. -/
theorem manifoldMorseIndex_comp_sphereHeight_self_of_neg (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ 1) (hφ' : deriv φ 1 < 0) :
    manifoldMorseIndex (𝓡 n) (φ ∘ sphereHeight v) v = 0 := by
  have h := (isManifoldNondegenerateCriticalPoint_sphereHeight_self (n := n)
    v).manifoldMorseIndex_scalar_comp_add_manifoldMorseIndex_eq_finrank
      (by rwa [sphereHeight_self]) (by rwa [sphereHeight_self])
  rw [manifoldMorseIndex_sphereHeight_self, finrank_euclideanSpace_fin] at h
  omega

/-- The Morse index of `φ ∘ h` at the south pole is `0` when `φ'(-1) > 0`. -/
theorem manifoldMorseIndex_comp_sphereHeight_neg_of_pos (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ (-1)) (hφ' : 0 < deriv φ (-1)) :
    manifoldMorseIndex (𝓡 n) (φ ∘ sphereHeight v) (-v) = 0 := by
  rw [manifoldMorseIndex_scalar_comp_of_pos (contMDiff_sphereHeight v (-v))
    (by rwa [sphereHeight_neg_self]) (by simp) (by rwa [sphereHeight_neg_self]),
    manifoldMorseIndex_sphereHeight_neg]

/-- The Morse index of `φ ∘ h` at the south pole is `n` when `φ'(-1) < 0`. -/
theorem manifoldMorseIndex_comp_sphereHeight_neg_of_neg (v : sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ 2 φ (-1)) (hφ' : deriv φ (-1) < 0) :
    manifoldMorseIndex (𝓡 n) (φ ∘ sphereHeight v) (-v) = n := by
  have h := (isManifoldNondegenerateCriticalPoint_sphereHeight_neg (n := n)
    v).manifoldMorseIndex_scalar_comp_add_manifoldMorseIndex_eq_finrank
      (by rwa [sphereHeight_neg_self]) (by rwa [sphereHeight_neg_self])
  rw [manifoldMorseIndex_sphereHeight_neg, finrank_euclideanSpace_fin] at h
  omega

/-! ### The latitudes -/

section Latitude

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {k : ℕ∞ω}
  {i : SmoothEmbedding J (𝓡 n) k S (sphere (0 : E) 1)} {v : sphere (0 : E) 1} {c : ℝ}

/-- **The critical latitudes of `φ ∘ h` are Morse–Bott.** A hypersurface embedded in the latitude
`h = c`, `c ≠ ±1`, is a nondegenerate critical submanifold of `φ ∘ h` when `φ'(c) = 0` and
`φ''(c) ≠ 0`. -/
theorem SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_sphereHeight (hk : k ≠ 0)
    (hi : ∀ s, sphereHeight v (i s) = c) (hc₁ : c ≠ 1) (hc₂ : c ≠ -1)
    (hdim : finrank ℝ E' + 1 = n) (hφ : ContDiffAt ℝ 2 φ c) (hφ' : deriv φ c = 0)
    (hφ'' : iteratedDeriv 2 φ c ≠ 0) :
    i.IsNondegenerateCriticalSubmanifold (φ ∘ sphereHeight v) :=
  i.isNondegenerateCriticalSubmanifold_scalar_comp hk (fun s ↦ contMDiff_sphereHeight v _) hi
    (fun s ↦ (isRegularValue_sphereHeight v hc₁ hc₂).isRegularPoint (hi s)) (by simpa using hdim)
    hφ hφ' hφ''

/-- The Morse index of `φ ∘ h` at a point of a latitude `h = c`, `c ≠ ±1`, with `φ'(c) = 0` and
`φ''(c) < 0` is `1`. -/
theorem manifoldMorseIndex_comp_sphereHeight_eq_one_of_iteratedDeriv_two_neg
    {x : sphere (0 : E) 1} (hx : sphereHeight v x = c) (hc₁ : c ≠ 1) (hc₂ : c ≠ -1)
    (hφ : ContDiffAt ℝ 2 φ c) (hφ' : deriv φ c = 0) (hφ'' : iteratedDeriv 2 φ c < 0) :
    manifoldMorseIndex (𝓡 n) (φ ∘ sphereHeight v) x = 1 := by
  subst hx
  exact manifoldMorseIndex_scalar_comp_eq_one_of_iteratedDeriv_two_neg
    (contMDiff_sphereHeight v x) ((isRegularValue_sphereHeight v hc₁ hc₂).isRegularPoint rfl)
    hφ hφ' hφ''

/-! ### Two caps: the function `h²` -/

/-- **The equator is a Morse–Bott critical submanifold of `h²`.** -/
theorem SmoothEmbedding.isNondegenerateCriticalSubmanifold_sq_comp_sphereHeight (hk : k ≠ 0)
    (hi : ∀ s, sphereHeight v (i s) = 0) (hdim : finrank ℝ E' + 1 = n) :
    i.IsNondegenerateCriticalSubmanifold ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) :=
  i.isNondegenerateCriticalSubmanifold_comp_sphereHeight hk hi zero_ne_one (by norm_num) hdim
    (by fun_prop) (by simp) (by simp)

/-- The Morse index of `h²` along the equator is `0`. -/
theorem manifoldMorseIndex_sq_comp_sphereHeight_of_eq_zero {x : sphere (0 : E) 1}
    (hx : sphereHeight v x = 0) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) x = 0 :=
  manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg (contMDiff_sphereHeight v x)
    (by fun_prop) (by rw [hx]; simp) (by simp)

/-- The north pole is a nondegenerate critical point of `h²`. -/
theorem isManifoldNondegenerateCriticalPoint_sq_comp_sphereHeight_self (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) v :=
  isManifoldNondegenerateCriticalPoint_comp_sphereHeight_self v (by fun_prop) (by simp)

/-- The south pole is a nondegenerate critical point of `h²`. -/
theorem isManifoldNondegenerateCriticalPoint_sq_comp_sphereHeight_neg (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) (-v) :=
  isManifoldNondegenerateCriticalPoint_comp_sphereHeight_neg v (by fun_prop) (by simp)

/-- The Morse index of `h²` at the north pole is `n`. -/
theorem manifoldMorseIndex_sq_comp_sphereHeight_self (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) v = n :=
  manifoldMorseIndex_comp_sphereHeight_self_of_pos v (by fun_prop) (by simp)

/-- The Morse index of `h²` at the south pole is `n`. -/
theorem manifoldMorseIndex_sq_comp_sphereHeight_neg (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v) (-v) = n :=
  manifoldMorseIndex_comp_sphereHeight_neg_of_neg v (by fun_prop) (by simp)

/-! ### Four critical levels: the function `b h - h³` -/

variable {b : ℝ}

/-- The derivative of `b t - t³` is `b - 3 t²`. -/
private theorem deriv_mul_sub_pow_three :
    deriv (fun t : ℝ ↦ b * t - t ^ 3) = fun t ↦ b - 3 * t ^ 2 :=
  funext fun t ↦ (((hasDerivAt_id t).const_mul b).fun_sub (hasDerivAt_pow 3 t)).deriv.trans
    (by simp)

/-- The second derivative of `b t - t³` is `-6 t`. -/
private theorem iteratedDeriv_two_mul_sub_pow_three (t : ℝ) :
    iteratedDeriv 2 (fun t : ℝ ↦ b * t - t ^ 3) t = -6 * t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_mul_sub_pow_three]
  exact (((hasDerivAt_pow 2 t).const_mul 3).const_sub b).deriv.trans (by ring)

/-- For `0 ≤ b`, the square of the critical latitude `√(b / 3)` is `b / 3`. -/
private theorem sq_sqrt_div_three (hb : 0 ≤ b) : √(b / 3) ^ 2 = b / 3 :=
  Real.sq_sqrt (by positivity)

/-- The derivative of `b t - t³` vanishes where `t² = b / 3`, in particular at `t = ±√(b / 3)`. -/
private theorem deriv_mul_sub_pow_three_eq_zero_of_sq_eq {t : ℝ} (ht : t ^ 2 = b / 3) :
    deriv (fun t : ℝ ↦ b * t - t ^ 3) t = 0 := by
  simp only [deriv_mul_sub_pow_three, ht]
  ring

/-- For `0 < b < 3`, the critical latitude `√(b / 3)` lies strictly between `0` and `1`. -/
private theorem sqrt_div_three_mem_Ioo (hb₀ : 0 < b) (hb₃ : b < 3) : √(b / 3) ∈ Ioo 0 1 :=
  ⟨Real.sqrt_pos.2 (by positivity), (Real.sqrt_lt' one_pos).2 (by linarith)⟩

/-- For `0 < b`, the second derivative of `b t - t³` at `√(b / 3)` is negative. -/
private theorem iteratedDeriv_two_mul_sub_pow_three_sqrt_neg (hb₀ : 0 < b) :
    iteratedDeriv 2 (fun t : ℝ ↦ b * t - t ^ 3) √(b / 3) < 0 := by
  rw [iteratedDeriv_two_mul_sub_pow_three]
  linarith [Real.sqrt_pos.2 (by positivity : 0 < b / 3)]

/-- **The critical points of `b h - h³`** for `0 ≤ b` are the latitudes `h = ±√(b / 3)` and the
two poles. -/
theorem criticalPoints_mul_sub_pow_three_comp_sphereHeight (hb : 0 ≤ b) (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) =
      sphereHeight v ⁻¹' {-√(b / 3), √(b / 3)} ∪ {v, -v} := by
  rw [criticalPoints_comp_sphereHeight (by fun_prop)]
  congr 2
  ext t
  simp only [deriv_mul_sub_pow_three, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  rw [← sq_eq_sq_iff_eq_or_eq_neg.trans or_comm, sq_sqrt_div_three hb]
  constructor <;> intro h <;> linarith

/-- The value of `b h - h³` at the north pole is `b - 1`. -/
theorem mul_sub_pow_three_comp_sphereHeight_self (v : sphere (0 : E) 1) :
    ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) v = b - 1 := by
  simp

/-- The value of `b h - h³` at the south pole is `1 - b`. -/
theorem mul_sub_pow_three_comp_sphereHeight_neg (v : sphere (0 : E) 1) :
    ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) (-v) = 1 - b := by
  simp only [comp_apply, sphereHeight_neg_self]
  ring

/-- For `0 ≤ b`, the value of `b h - h³` on the latitude `h = √(b / 3)` is
`(2 b / 3) √(b / 3)`. -/
theorem mul_sub_pow_three_comp_sphereHeight_of_eq_sqrt (hb : 0 ≤ b) {x : sphere (0 : E) 1}
    (hx : sphereHeight v x = √(b / 3)) :
    ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) x = 2 * b / 3 * √(b / 3) := by
  simp only [comp_apply, hx]
  linear_combination -√(b / 3) * sq_sqrt_div_three hb

/-- For `0 ≤ b`, the value of `b h - h³` on the latitude `h = -√(b / 3)` is
`-(2 b / 3) √(b / 3)`. -/
theorem mul_sub_pow_three_comp_sphereHeight_of_eq_neg_sqrt (hb : 0 ≤ b) {x : sphere (0 : E) 1}
    (hx : sphereHeight v x = -√(b / 3)) :
    ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) x = -(2 * b / 3 * √(b / 3)) := by
  simp only [comp_apply, hx]
  linear_combination √(b / 3) * sq_sqrt_div_three hb

namespace SmoothEmbedding

/-- For `0 < b < 3`, the latitude `h = √(b / 3)` is a Morse–Bott critical submanifold of
`b h - h³`. -/
theorem isNondegenerateCriticalSubmanifold_mul_sub_pow_three_comp_sphereHeight_of_eq_sqrt
    (hk : k ≠ 0) (hb₀ : 0 < b) (hb₃ : b < 3) (hi : ∀ s, sphereHeight v (i s) = √(b / 3))
    (hdim : finrank ℝ E' + 1 = n) :
    i.IsNondegenerateCriticalSubmanifold ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) := by
  have ha := sqrt_div_three_mem_Ioo hb₀ hb₃
  exact i.isNondegenerateCriticalSubmanifold_comp_sphereHeight hk hi ha.2.ne
    (by linarith [ha.1]) hdim (by fun_prop)
    (deriv_mul_sub_pow_three_eq_zero_of_sq_eq (sq_sqrt_div_three hb₀.le))
    (iteratedDeriv_two_mul_sub_pow_three_sqrt_neg hb₀).ne

end SmoothEmbedding

/-- For `0 < b < 3`, the Morse index of `b h - h³` at a point of the latitude `h = √(b / 3)` is
`1`. -/
theorem manifoldMorseIndex_mul_sub_pow_three_comp_sphereHeight_of_eq_sqrt (hb₀ : 0 < b)
    (hb₃ : b < 3) {x : sphere (0 : E) 1} (hx : sphereHeight v x = √(b / 3)) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) x = 1 := by
  have ha := sqrt_div_three_mem_Ioo hb₀ hb₃
  exact manifoldMorseIndex_comp_sphereHeight_eq_one_of_iteratedDeriv_two_neg hx ha.2.ne
    (by linarith [ha.1]) (by fun_prop)
    (deriv_mul_sub_pow_three_eq_zero_of_sq_eq (sq_sqrt_div_three hb₀.le))
    (iteratedDeriv_two_mul_sub_pow_three_sqrt_neg hb₀)

namespace SmoothEmbedding

/-- For `0 < b < 3`, the latitude `h = -√(b / 3)` is a Morse–Bott critical submanifold of
`b h - h³`. -/
theorem isNondegenerateCriticalSubmanifold_mul_sub_pow_three_comp_sphereHeight_of_eq_neg_sqrt
    (hk : k ≠ 0) (hb₀ : 0 < b) (hb₃ : b < 3) (hi : ∀ s, sphereHeight v (i s) = -√(b / 3))
    (hdim : finrank ℝ E' + 1 = n) :
    i.IsNondegenerateCriticalSubmanifold ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) := by
  have ha := sqrt_div_three_mem_Ioo hb₀ hb₃
  refine i.isNondegenerateCriticalSubmanifold_comp_sphereHeight hk hi (by linarith [ha.1])
    (by linarith [ha.2]) hdim (by fun_prop)
    (deriv_mul_sub_pow_three_eq_zero_of_sq_eq ((neg_sq _).trans (sq_sqrt_div_three hb₀.le))) ?_
  rw [iteratedDeriv_two_mul_sub_pow_three]
  linarith [ha.1]

end SmoothEmbedding

/-- For `0 ≤ b`, the Morse index of `b h - h³` at a point of the latitude `h = -√(b / 3)` is
`0`. -/
theorem manifoldMorseIndex_mul_sub_pow_three_comp_sphereHeight_of_eq_neg_sqrt (hb : 0 ≤ b)
    {x : sphere (0 : E) 1} (hx : sphereHeight v x = -√(b / 3)) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) x = 0 := by
  refine manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg
    (contMDiff_sphereHeight v x) (by fun_prop)
    (hx ▸ deriv_mul_sub_pow_three_eq_zero_of_sq_eq ((neg_sq _).trans (sq_sqrt_div_three hb))) ?_
  rw [iteratedDeriv_two_mul_sub_pow_three, hx]
  nlinarith [Real.sqrt_nonneg (b / 3)]

/-- For `b ≠ 3`, the north pole is a nondegenerate critical point of `b h - h³`. -/
theorem isManifoldNondegenerateCriticalPoint_mul_sub_pow_three_comp_sphereHeight_self
    (hb : b ≠ 3) (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) v :=
  isManifoldNondegenerateCriticalPoint_comp_sphereHeight_self v (by fun_prop)
    (by simpa [deriv_mul_sub_pow_three, sub_eq_zero] using hb)

/-- For `b ≠ 3`, the south pole is a nondegenerate critical point of `b h - h³`. -/
theorem isManifoldNondegenerateCriticalPoint_mul_sub_pow_three_comp_sphereHeight_neg
    (hb : b ≠ 3) (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v)
      (-v) :=
  isManifoldNondegenerateCriticalPoint_comp_sphereHeight_neg v (by fun_prop)
    (by simpa [deriv_mul_sub_pow_three, sub_eq_zero] using hb)

/-- For `b < 3`, the Morse index of `b h - h³` at the north pole, a local minimum, is `0`. -/
theorem manifoldMorseIndex_mul_sub_pow_three_comp_sphereHeight_self (hb : b < 3)
    (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) v = 0 :=
  manifoldMorseIndex_comp_sphereHeight_self_of_neg v (by fun_prop)
    (by simp only [deriv_mul_sub_pow_three]; linarith)

/-- For `b < 3`, the Morse index of `b h - h³` at the south pole, a local maximum, is `n`. -/
theorem manifoldMorseIndex_mul_sub_pow_three_comp_sphereHeight_neg (hb : b < 3)
    (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v) (-v) = n :=
  manifoldMorseIndex_comp_sphereHeight_neg_of_neg v (by fun_prop)
    (by simp only [deriv_mul_sub_pow_three]; linarith)

end Latitude

end TauCeti
