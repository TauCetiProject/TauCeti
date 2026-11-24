/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.IndexOne
public import TauCeti.Geometry.Manifold.Morse.Sphere.Saddle
import TauCeti.Analysis.Calculus.Deriv.SignChange
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional

/-!
# The Morse complex of the sphere with two maxima

Let `u` and `v` be orthogonal unit vectors of a real inner product space of dimension `n + 1`, and
`0 < t < 2`. Write `hᵤ = sphereHeight u` for the height function `x ↦ ⟪x, u⟫` on the sphere `Sⁿ`.
On `Sⁿ` the function `f = hᵤ² + t hᵥ` (`TauCeti.isMorse_sphereHeight_sq_add_smul_sphereHeight`)
has a minimum `-v` of index `0`, a saddle `v` of index `n - 1` and two maxima
`m₁, m₂ = ±√(1 - t² / 4) u + (t / 2) v` of index `n`. For `n ≥ 2`, this file computes its Morse
complex, over `ℤ` and modulo two, for every adapted pseudo-gradient `X` and every choice of
orientations of the unstable manifolds. (For `n = 1` the saddle and the minimum both have index
`0`.) On `S²` it is the complex `ℤ² → ℤ → ℤ` of a sphere with two maxima, one saddle and one
minimum.

* `X` is Morse–Smale whatever its choice, since the saddle is the only critical point of index
  neither `0` nor `n`.
* **Exactly one trajectory runs from each maximum to the saddle.** The stable manifold of the
  saddle is a line through `v` whose two halves are trajectories. Along a trajectory into the
  saddle `f > t`, whereas `f = t hᵥ ≤ t` on the great sphere `hᵤ = 0`; so a trajectory into the
  saddle stays on one side of `hᵤ = 0` and comes from the maximum on that side. The two halves lie
  on opposite sides: in a Morse chart at `v` the stable line is the coordinate line of positive
  weight, along which `f = t + r² / 2 ≤ hᵤ² + t`, so `hᵤ` has a nonzero derivative along it.
* So the boundary of `mᵢ` is `εᵢ v` with a sign `εᵢ = ±1`. The boundary of the saddle vanishes:
  for `n = 2` its two trajectories to the minimum carry opposite signs (see
  `IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero`), and for `n > 2` no
  critical point has index `n - 2`.

Hence the integral Morse boundary sends a chain `c` to `(ε₁ c(m₁) + ε₂ c(m₂)) v`. Its boundaries
are the multiples of `v`, and a chain is a cycle exactly when `ε₁ c(m₁) + ε₂ c(m₂) = 0`.
Reversing the orientations of the maxima where needed makes `ε₁ = ε₂ = 1`, and then the signed sum
`m₁ - m₂` of the maxima is a cycle. Modulo two the boundary sends `c` to `(c(m₁) + c(m₂)) v`,
unlike that of the torus or of `ℝℙ²`, which vanishes.

The file does not formalise the resulting homology. From these formulas, for `n = 2` the integral
Morse homology is `ℤ`, `0`, `ℤ` in degrees `2`, `1`, `0`, that of `S²`, with `m₁ - m₂`
generating `H₂`. Forgetting the signs would give `∂ m₁ = ∂ m₂ = v` but `∂ v = 2 (-v)`, and
`H₀ = ℤ / 2`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `mem_unstableSet_iff_sphereHeight_mul_sphereHeight_pos`: a point of the stable manifold of
  the saddle lies on a trajectory from the maximum `m` exactly when it is on the side of `m`.
* `exists_unstableSet_inter_stableSet_eq_orbit_sphereHeight_sq_add_smul_sphereHeight` and
  `ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight`: the trajectories from a
  maximum to the saddle form one orbit, so exactly one trajectory.
* `isMorseSmale_sphereHeight_sq_add_smul_sphereHeight`: every adapted pseudo-gradient is
  Morse–Smale.
* `signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_one_or_eq_neg_one` and
  `signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_zero`: the integral boundary
  coefficients.
* `signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight`: the integral Morse boundary, with
  its cycles (`signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight_eq_zero_iff`) and its
  boundaries (`range_signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight`).
* `exists_signedMorseBoundary_reverse_sphereHeight_sq_add_smul_sphereHeight_eq`: for suitable
  orientations of the maxima, `∂ c = (c(m₁) + c(m₂)) v`, so `m₁ - m₂` is a cycle.
* `IsMorseSmale.morseBoundary_sphereHeight_sq_add_smul_sphereHeight`: the mod-two Morse boundary.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the sphere with two maxima, and why the integral Morse
  complex needs signs).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and its computation for simple examples).
-/

public section

open Filter Function Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {u v : sphere (0 : E) 1} {t : ℝ}

/-! ### Values of `hᵤ² + t hᵥ` -/

omit [Fact (finrank ℝ E = n + 1)] in
/-- Where `hᵤ` vanishes, `hᵤ² + t hᵥ = t hᵥ` is at most `t`, for `t ≥ 0`. -/
private theorem apply_le_of_sphereHeight_eq_zero (ht : 0 ≤ t) {x : sphere (0 : E) 1}
    (hx : sphereHeight u x = 0) : (sphereHeight u ^ 2 + t • sphereHeight v) x ≤ t := by
  simp only [Pi.add_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul, hx]
  nlinarith [sphereHeight_le_one v x]

omit [Fact (finrank ℝ E = n + 1)] in
private theorem apply_self (huv : ⟪(u : E), (v : E)⟫ = 0) :
    (sphereHeight u ^ 2 + t • sphereHeight v) v = t := by
  simp [sphereHeight_apply, real_inner_comm, huv]

omit [Fact (finrank ℝ E = n + 1)] in
private theorem apply_neg_self (huv : ⟪(u : E), (v : E)⟫ = 0) :
    (sphereHeight u ^ 2 + t • sphereHeight v) (-v) = -t := by
  simp [sphereHeight_apply, real_inner_comm, huv, inner_neg_left]

omit [Fact (finrank ℝ E = n + 1)] in
/-- Two points of the sphere with `hᵥ = t / 2` and the same value of `hᵤ`, with
`hᵤ² = 1 - t² / 4`, are equal: both lie in the plane spanned by `u` and `v`. -/
private theorem eq_of_sphereHeight_eq (huv : ⟪(u : E), (v : E)⟫ = 0) {x y : sphere (0 : E) 1}
    (hx : sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4)
    (hy : sphereHeight v y = t / 2) (hxy : sphereHeight u x = sphereHeight u y) : x = y := by
  have h₁ := coe_eq_sphereHeight_smul_add_sphereHeight_smul huv (x := x)
    (by rw [hx.1, hx.2]; ring)
  have h₂ := coe_eq_sphereHeight_smul_add_sphereHeight_smul huv (x := y)
    (by rw [hy, ← hxy, hx.2]; ring)
  exact Subtype.ext (by rw [h₁, h₂, hxy, hx.1, hy])

/-! ### The critical points of `hᵤ² + t hᵥ` -/

/-- The critical points of `hᵤ² + t hᵥ`, for `0 < t < 2`, with their Morse indices: the saddle `v`
of index `n - 1`, the minimum `-v` of index `0` and the two maxima of index `n`. -/
private theorem mem_criticalPoints_cases (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t)
    (ht₂ : t < 2) {x : sphere (0 : E) 1}
    (hx : x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)) :
    (x = v ∧ manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = n - 1) ∨
      (x = -v ∧ manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = 0) ∨
      (sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4 ∧
        manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = n) := by
  rcases (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne').1 hx with
    rfl | rfl | ⟨h1, h2⟩
  · exact Or.inl ⟨rfl, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂⟩
  · exact Or.inr (Or.inl ⟨rfl, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self
      huv ht₀⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_of_eq
      huv h1 h2 (by nlinarith)⟩)

/-- `hᵤ² + t hᵥ` is a Morse function for `0 < t < 2`. -/
private theorem isMorse_sphereHeight_sq_add_smul_sphereHeight_of_lt (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht₀ : 0 < t) (ht₂ : t < 2) : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) :=
  isMorse_sphereHeight_sq_add_smul_sphereHeight huv ht₀.ne' (by nlinarith)

/-- The saddle `v` is a critical point of `hᵤ² + t hᵥ`. -/
private theorem mfderiv_sphereHeight_sq_add_smul_sphereHeight_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : t ≠ 0) :
    mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) v = 0 :=
  mem_criticalPoints_iff_mfderiv_eq_zero.1
    ((mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀).2 (Or.inl rfl))

/-- For `n ≥ 1`, the saddle `v` has index one less than the dimension of the sphere. -/
private theorem manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self_add_one
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2) (hn : 1 ≤ n) :
    manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) v + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  rw [manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂,
    finrank_euclideanSpace_fin]
  omega

/-- A critical point of `hᵤ² + t hᵥ` with `hᵥ = t / 2` is one of the two maxima. -/
private theorem sq_sphereHeight_of_mem_criticalPoints (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht₀ : 0 < t) (ht₂ : t < 2) {x : sphere (0 : E) 1}
    (hx : x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (h1 : sphereHeight v x = t / 2) :
    sphereHeight u x ^ 2 = 1 - t ^ 2 / 4 ∧
      manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = n := by
  rcases mem_criticalPoints_cases huv ht₀ ht₂ hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h2, hi⟩
  · rw [sphereHeight_self] at h1
    linarith
  · rw [sphereHeight_neg_self] at h1
    linarith
  · exact ⟨h2, hi⟩

/-- Any critical point of `hᵤ² + t hᵥ` with `hᵥ = t / 2` is one of two distinct such points. -/
private theorem eq_or_eq_of_sphereHeight_eq (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t)
    (ht₂ : t < 2) {x m₁ m₂ : sphere (0 : E) 1}
    (hx : x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (hm₁ : m₁ ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (hm₂ : m₂ ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (hx1 : sphereHeight v x = t / 2) (h₁ : sphereHeight v m₁ = t / 2)
    (h₂ : sphereHeight v m₂ = t / 2) (hm : m₁ ≠ m₂) : x = m₁ ∨ x = m₂ := by
  have hx2 := (sq_sphereHeight_of_mem_criticalPoints huv ht₀ ht₂ hx hx1).1
  have hm₁2 := (sq_sphereHeight_of_mem_criticalPoints huv ht₀ ht₂ hm₁ h₁).1
  have hm₂2 := (sq_sphereHeight_of_mem_criticalPoints huv ht₀ ht₂ hm₂ h₂).1
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hm₁2.symm) with h | h
  · exact Or.inl (eq_of_sphereHeight_eq huv ⟨hx1, hx2⟩ h₁ h)
  -- The two maxima lie on opposite sides of `hᵤ = 0`, and `x` on the side of `m₂`.
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hm₂2.trans hm₁2.symm) with h' | h'
  · exact (hm (eq_of_sphereHeight_eq huv ⟨h₂, hm₂2⟩ h₁ h').symm).elim
  · exact Or.inr (eq_of_sphereHeight_eq huv ⟨hx1, hx2⟩ h₂ (h.trans h'.symm))

/-- Read in a chart of the maximal atlas of the sphere, a height function is differentiable along
each line through the origin of the chart, when the origin lies in its target. -/
private theorem differentiableAt_sphereHeight_symm_smul
    {e : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (sphere (0 : E) 1)) (h0 : 0 ∈ e.target)
    (a : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun r : ℝ ↦ sphereHeight u (e.symm (r • a))) 0 := by
  have hc : ContMDiffAt 𝓘(ℝ) (𝓡 n) 1 (fun r : ℝ ↦ e.symm (r • a)) 0 :=
    ((contMDiffAt_symm_of_mem_maximalAtlas he (by rwa [zero_smul])).of_le (by simp)).comp 0
      (contDiff_id.smul contDiff_const).contMDiff.contMDiffAt
  exact mdifferentiableAt_iff_differentiableAt.1
    (((contMDiff_sphereHeight (n := n) (m := 1) u).contMDiffAt.comp 0 hc).mdifferentiableAt
      one_ne_zero)

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}

/-- **Trajectories into the saddle come from the maximum on their side.** Let `y` be a point of
`W^s(v)` other than `v`, on a trajectory leaving the critical point `m`. Then `m` is one of the two
maxima, and `hᵤ y` has the sign of `hᵤ m`. Along the trajectory `f > t` before `y`, whereas
`f ≤ t` on the great sphere `hᵤ = 0`, so the trajectory never crosses it. -/
private theorem isMax_and_pos_of_mem_unstableSet_inter_stableSet
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {m y : sphere (0 : E) 1}
    (hm : m ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (hy : y ∈ hX.flow.unstableSet m ∩ hX.flow.stableSet v) (hyv : y ≠ v) :
    (sphereHeight v m = t / 2 ∧ sphereHeight u m ^ 2 = 1 - t ^ 2 / 4) ∧
      0 < sphereHeight u y * sphereHeight u m := by
  have hmv : m ≠ v := by
    rintro rfl
    exact hyv (hX.eq_of_mem_unstableSet_inter_stableSet hy)
  have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hmv hy
  rw [apply_self huv] at hval
  have hmax : sphereHeight v m = t / 2 ∧ sphereHeight u m ^ 2 = 1 - t ^ 2 / 4 := by
    rcases (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne').1 hm with
      rfl | rfl | hm
    · exact (hmv rfl).elim
    · have := hval.1.trans hval.2
      rw [apply_neg_self huv] at this
      linarith
    · exact hm
  refine ⟨hmax, ?_⟩
  -- `hᵤ m ≠ 0`: otherwise `t < f m = t² / 2` and `t² = 4`.
  have hm0 : 0 < sphereHeight u m * sphereHeight u m := by
    have hfm := hval.1.trans hval.2
    simp only [Pi.add_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul, hmax.1] at hfm
    nlinarith [hmax.2, sq_nonneg (sphereHeight u m), sq_nonneg (t - 2)]
  by_contra hneg
  push Not at hneg
  -- `k s = hᵤ (φ_s y) hᵤ m` is at most `0` at `s = 0` and tends to `hᵤ m² > 0` as `s → -∞`.
  set k : ℝ → ℝ := fun s ↦ sphereHeight u (hX.flow s y) * sphereHeight u m
  have hcont : Continuous k :=
    (((contMDiff_sphereHeight (n := n) (m := 0) u).continuous.comp
      (hX.flow.continuous continuous_id continuous_const))).mul continuous_const
  have hlim : Tendsto k atBot (𝓝 (sphereHeight u m * sphereHeight u m)) :=
    (((contMDiff_sphereHeight (n := n) (m := 0) u).continuous.tendsto m).comp
      (Flow.mem_unstableSet.1 hy.1)).mul_const _
  obtain ⟨S, hkS, hS⟩ := ((hlim.eventually (lt_mem_nhds hm0)).and (eventually_le_atBot 0)).exists
  obtain ⟨s, hs, hks⟩ := isPreconnected_Iic.intermediate_value (a := (0 : ℝ)) (b := S)
    self_mem_Iic hS hcont.continuousOn ⟨by simpa [k] using hneg, hkS.le⟩
  have hus : sphereHeight u (hX.flow s y) = 0 :=
    (mul_eq_zero.1 hks).resolve_right fun h ↦ by rw [h, mul_zero] at hm0; exact hm0.false
  have hle := apply_le_of_sphereHeight_eq_zero (v := v) ht₀.le hus
  have hge : (sphereHeight u ^ 2 + t • sphereHeight v) y ≤
      (sphereHeight u ^ 2 + t • sphereHeight v) (hX.flow s y) := by
    simpa using hX.antitone_flow y (Set.mem_Iic.1 hs)
  linarith [hval.1]

/-- **The stable manifold of the saddle reaches both sides of `hᵤ = 0`.** Near the saddle `v`, the
stable manifold is the coordinate line of positive weight of a Morse chart, along which
`f = t + r² / 2`. Since `f ≤ hᵤ² + t`, the function `hᵤ` grows at least linearly along this line,
so it is not a local extremum of `hᵤ` there and the line has points on both sides. -/
private theorem exists_mem_stableSet_sphereHeight_neg_and_pos
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2) (hn : 1 ≤ n)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X) :
    (∃ y ∈ hX.flow.stableSet v, sphereHeight u y < 0) ∧
      ∃ y ∈ hX.flow.stableSet v, 0 < sphereHeight u y := by
  obtain ⟨φ, hφ⟩ :=
    hX.exists_morseChart v (mfderiv_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀.ne')
  obtain ⟨ε, hε, hεs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨R, hR, hRT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  obtain ⟨j, hj, hneg⟩ := φ.exists_weight_eq_one_of_add_one_eq_finrank
    (manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self_add_one huv ht₀ ht₂ hn)
  -- The coordinate line `γ r` of positive weight through `v`.
  set a : EuclideanSpace ℝ (Fin n) := φ.coord.symm (Pi.single j 1)
  set γ : ℝ → sphere (0 : E) 1 := fun r ↦ φ.toChart.symm (r • a)
  have hcoord (r : ℝ) : φ.coord (r • a) = r • Pi.single j 1 := by
    rw [map_smul, LinearEquiv.apply_symm_apply]
  have hnorm (r : ℝ) : ‖φ.coord (r • a)‖ = |r| := by
    simp [hcoord, norm_smul, Pi.norm_single]
  have hT (r : ℝ) (hr : |r| < R) : r • a ∈ φ.toChart.target := by
    simpa [hcoord] using hRT _ ((hnorm r).trans_lt hr)
  have hγ (r : ℝ) (hr : |r| < R) : γ r ∈ φ.toChart.source ∧
      φ.coord (φ.toChart (γ r)) = r • Pi.single j 1 :=
    ⟨φ.toChart.map_target (hT r hr), by rw [φ.toChart.right_inv (hT r hr), hcoord]⟩
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, |r| < min R ε :=
    (continuous_abs.tendsto' 0 0 abs_zero).eventually (gt_mem_nhds (lt_min hR hε))
  have hmem : ∀ᶠ r in 𝓝 0, γ r ∈ hX.flow.stableSet v := hsmall.mono fun r hr ↦ by
    obtain ⟨hsrc, hc⟩ := hγ r (hr.trans_le (min_le_left _ _))
    refine (hεs _ hsrc ?_).2 fun i hi ↦ ?_
    · rw [φ.toChart.right_inv (hT r (hr.trans_le (min_le_left _ _))), hnorm]
      exact hr.trans_le (min_le_right _ _)
    · rw [hc, Pi.smul_apply, Pi.single_eq_of_ne (by rintro rfl; linarith), smul_zero]
  -- Along the line `f = t + r² / 2`, while `f ≤ hᵤ² + t`.
  have hsq : ∀ᶠ r in 𝓝 0, r ^ 2 ≤ 2 * sphereHeight u (γ r) ^ 2 := hsmall.mono fun r hr ↦ by
    obtain ⟨hsrc, hc⟩ := hγ r (hr.trans_le (min_le_left _ _))
    have hq := φ.eq_quadratic _ hsrc
    rw [hc, apply_self huv] at hq
    simp [Pi.single_apply, hj, -sphereHeight_apply] at hq
    nlinarith [sphereHeight_le_one v (γ r)]
  have h0 : sphereHeight u (γ 0) = 0 := by
    simp only [γ, zero_smul]
    rw [← φ.apply_self, φ.toChart.left_inv φ.mem_source,
      sphereHeight_eq_zero_of_inner_eq_zero huv]
  have hdiff := differentiableAt_sphereHeight_symm_smul (u := u) φ.mem_maximalAtlas
    (by simpa using hT 0 (by rwa [abs_zero])) a
  -- So `hᵤ` grows at least linearly along the line, and takes both signs near `v`.
  have hO : (fun r ↦ r - 0) =O[𝓝 0] fun r ↦ sphereHeight u (γ r) - sphereHeight u (γ 0) :=
    Asymptotics.IsBigO.of_bound 2 (hsq.mono fun r hr ↦ by
      simp only [h0, sub_zero, Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq (by nlinarith [sq_abs (sphereHeight u (γ r))]) (by positivity))
  obtain ⟨hl, hp⟩ := frequently_lt_and_frequently_gt_of_isBigO_sub_rev hdiff hO
  obtain ⟨r, hr, hrs⟩ := (hl.and_eventually hmem).exists
  obtain ⟨r', hr', hrs'⟩ := (hp.and_eventually hmem).exists
  exact ⟨⟨γ r, hrs, hr.trans_eq h0⟩, ⟨γ r', hrs', h0.symm.trans_lt hr'⟩⟩

/-- **The trajectories from a maximum into the saddle are those on its side.** Let `m` be one of
the two maxima of `hᵤ² + t hᵥ`, the points with `hᵥ = t / 2` and `hᵤ² = 1 - t² / 4`. A point `y`
of the stable manifold of the saddle `v` lies on a trajectory from `m` exactly when `hᵤ y` has the
sign of `hᵤ m`. The saddle itself satisfies neither condition. -/
theorem mem_unstableSet_iff_sphereHeight_mul_sphereHeight_pos
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {m y : sphere (0 : E) 1} (h1 : sphereHeight v m = t / 2)
    (h2 : sphereHeight u m ^ 2 = 1 - t ^ 2 / 4) (hy : y ∈ hX.flow.stableSet v) :
    y ∈ hX.flow.unstableSet m ↔ 0 < sphereHeight u y * sphereHeight u m := by
  -- The saddle is on neither side: `hᵤ v = 0`, and the rest point `v` lies only in `W^u(v)`.
  rcases eq_or_ne y v with rfl | hyv
  · rw [sphereHeight_eq_zero_of_inner_eq_zero huv, zero_mul, lt_self_iff_false, iff_false]
    intro hym
    obtain rfl := hX.eq_of_mem_unstableSet_of_mfderiv_eq_zero
      (mfderiv_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀.ne') hym
    rw [sphereHeight_self] at h1
    linarith
  have hcrit (x : sphere (0 : E) 1) (h1 : sphereHeight v x = t / 2)
      (h2 : sphereHeight u x ^ 2 = 1 - t ^ 2 / 4) :
      x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) :=
    (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne').2
      (Or.inr (Or.inr ⟨h1, h2⟩))
  refine ⟨fun hym ↦ (isMax_and_pos_of_mem_unstableSet_inter_stableSet huv ht₀ hX
    (hcrit m h1 h2) ⟨hym, hy⟩ hyv).2, fun hpos ↦ ?_⟩
  -- The trajectory through `y` leaves a maximum `m'` on the side of `y`, which is `m`.
  have hf := isMorse_sphereHeight_sq_add_smul_sphereHeight_of_lt (n := n) huv ht₀ ht₂
  obtain ⟨m', hm', hym'⟩ := hX.exists_mem_unstableSet hf y
  obtain ⟨⟨h1', h2'⟩, hpos'⟩ := isMax_and_pos_of_mem_unstableSet_inter_stableSet huv ht₀ hX
    (mem_criticalPoints_iff_mfderiv_eq_zero.2 hm') ⟨hym', hy⟩ hyv
  have hsame : sphereHeight u m' = sphereHeight u m := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h2'.trans h2.symm) with h | h
    · exact h
    · rw [h] at hpos'
      nlinarith
  rwa [eq_of_sphereHeight_eq huv ⟨h1', h2'⟩ h1 hsame] at hym'

/-- **A single trajectory from each maximum into the saddle.** For `n ≥ 1`, `0 < t < 2` and a
maximum `m` of `hᵤ² + t hᵥ`, the trajectories of any adapted pseudo-gradient from `m` to the saddle
`v` form a single orbit. The stable manifold of `v` is a line, whose two halves lie on the two
sides of `hᵤ = 0` and so come from the two different maxima. -/
theorem exists_unstableSet_inter_stableSet_eq_orbit_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2) (hn : 1 ≤ n)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {m : sphere (0 : E) 1} (h1 : sphereHeight v m = t / 2)
    (h2 : sphereHeight u m ^ 2 = 1 - t ^ 2 / 4) :
    ∃ z, hX.flow.unstableSet m ∩ hX.flow.stableSet v = hX.flow.orbit z := by
  -- Points of `W^s(v)` on both sides of `hᵤ = 0`: the one on the side of `m` comes from `m`, the
  -- other does not.
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ :=
    exists_mem_stableSet_sphereHeight_neg_and_pos huv ht₀ ht₂ hn hX
  obtain ⟨y, hy, hpos, z, hz, hneg⟩ : ∃ y ∈ hX.flow.stableSet v,
      0 < sphereHeight u y * sphereHeight u m ∧
        ∃ z ∈ hX.flow.stableSet v, sphereHeight u z * sphereHeight u m < 0 := by
    rcases lt_or_gt_of_ne (show sphereHeight u m ≠ 0 by intro h; rw [h] at h2; nlinarith) with
      hm | hm
    · exact ⟨a, ha, mul_pos_of_neg_of_neg ha' hm, b, hb, mul_neg_of_pos_of_neg hb' hm⟩
    · exact ⟨b, hb, mul_pos hb' hm, a, ha, mul_neg_of_neg_of_pos ha' hm⟩
  have hiff {w : sphere (0 : E) 1} (hw : w ∈ hX.flow.stableSet v) :=
    mem_unstableSet_iff_sphereHeight_mul_sphereHeight_pos huv ht₀ ht₂ hX h1 h2 hw
  -- The saddle `v` is not `z`, since `hᵤ v = 0`.
  have hzv : z ≠ v := by
    rintro rfl
    rw [sphereHeight_eq_zero_of_inner_eq_zero huv, zero_mul] at hneg
    exact hneg.false
  exact ⟨y, hX.unstableSet_inter_stableSet_eq_orbit
    (mfderiv_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀.ne')
    (manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self_add_one huv ht₀ ht₂ hn)
    ⟨(hiff hy).2 hpos, hy⟩ hz hzv fun h ↦ ((hiff hz).1 h).not_gt hneg⟩

/-- **One trajectory from each maximum to the saddle.** For `n ≥ 1`, `0 < t < 2`, a maximum `m`
of `hᵤ² + t hᵥ` and any adapted pseudo-gradient, exactly one trajectory runs from `m` to the saddle
`v`: the middle-level slice of these trajectories is a single point. -/
theorem ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2) (hn : 1 ≤ n)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {m : sphere (0 : E) 1} (h1 : sphereHeight v m = t / 2)
    (h2 : sphereHeight u m ^ 2 = 1 - t ^ 2 / 4) :
    (hX.morseTrajectorySlice m v).ncard = 1 := by
  obtain ⟨z, hz⟩ :=
    exists_unstableSet_inter_stableSet_eq_orbit_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂
      hn hX h1 h2
  refine hX.ncard_morseTrajectorySlice_eq_one_of_unstableSet_inter_stableSet_eq_orbit ?_ hz
  rintro rfl
  rw [sphereHeight_self] at h1
  linarith

/-! ### The Morse complex -/

/-- **Every pseudo-gradient adapted to `hᵤ² + t hᵥ` is Morse–Smale**, for `0 < t < 2`: the saddle
`v` is its only critical point whose index is neither `0` nor `n`. -/
theorem isMorseSmale_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X) :
    hX.IsMorseSmale := by
  refine IsMorseSmale.of_subsingleton (isMorse_sphereHeight_sq_add_smul_sphereHeight_of_lt huv ht₀
    ht₂) ((subsingleton_singleton (a := v)).anti ?_)
  rintro x ⟨hx, hx0, hxn⟩
  rcases mem_criticalPoints_cases huv ht₀ ht₂ (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) with
    ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
  · rfl
  · exact (hx0 h).elim
  · exact (hxn (h.trans finrank_euclideanSpace_fin.symm)).elim

variable (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2)
  (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
  (𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X)
include huv ht₀ ht₂

/-- **The boundary coefficient from a maximum to the saddle is `±1`.** For `n ≥ 1`, any adapted
pseudo-gradient and any orientations of the unstable manifolds, the single trajectory from a
maximum `p` to the saddle `v` counts with a sign. -/
theorem signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_one_or_eq_neg_one
    (hn : 1 ≤ n)
    {p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hp : sphereHeight v p = t / 2) (hq : (q : sphere (0 : E) 1) = v) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 1 ∨ hX.signedMorseBoundaryCoeff 𝔬 p q = -1 := by
  obtain ⟨h2, hpi⟩ := sq_sphereHeight_of_mem_criticalPoints huv ht₀ ht₂ p.property hp
  have hqi : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
      (q : sphere (0 : E) 1) = n - 1 := by
    rw [hq, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂]
  have hpq : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
      (p : sphere (0 : E) 1) = manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (q : sphere (0 : E) 1) + 1 := by
    omega
  obtain ⟨y, hy⟩ := ncard_eq_one.1
    (ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hn hX hp h2)
  have hs : hX.morseTrajectorySlice (p : sphere (0 : E) 1) q = {y} := by rwa [hq]
  have hmem := (mem_morseTrajectorySlice _).1 (hs.symm ▸ mem_singleton y)
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def, hs,
    finsum_mem_singleton]
  exact trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q)
    (isMorseSmale_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX)
    (isMorse_sphereHeight_sq_add_smul_sphereHeight_of_lt huv ht₀ ht₂) ⟨hmem.1, hmem.2.1⟩

/-- **The other boundary coefficients vanish.** For `n ≥ 2`, any adapted pseudo-gradient and any
orientations, the coefficient of `q` in the integral boundary of `p` is zero unless `p` is a
maximum and `q` the saddle `v`. For `n = 2` this includes the cancellation of the two trajectories
from the saddle to the minimum. -/
theorem signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_zero (hn : 2 ≤ n)
    {p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (h : sphereHeight v p = t / 2 → (q : sphere (0 : E) 1) ≠ v) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  by_cases hpq : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
      (p : sphere (0 : E) 1) = manifoldMorseIndex (𝓡 n)
        (sphereHeight u ^ 2 + t • sphereHeight v) (q : sphere (0 : E) 1) + 1
  swap
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq
  rcases mem_criticalPoints_cases huv ht₀ ht₂ p.property with
    ⟨-, hpi⟩ | ⟨-, hpi⟩ | ⟨hp1, -, hpi⟩ <;>
    rcases mem_criticalPoints_cases huv ht₀ ht₂ q.property with
      ⟨hqv, hqi⟩ | ⟨-, hqi⟩ | ⟨-, -, hqi⟩ <;>
    try omega
  · -- From the saddle to the minimum, for `n = 2`: the minimum is the only critical point of index
    -- `0`, so the integral boundary of the saddle, of index `1`, vanishes.
    have hmin : {x | mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) x = 0 ∧
        manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = 0}.Subsingleton :=
      (subsingleton_singleton (a := -v)).anti fun x ⟨hx, hx0⟩ ↦ by
        rcases mem_criticalPoints_cases huv ht₀ ht₂ (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx)
          with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨-, -, h⟩
        · omega
        · rfl
        · omega
    have := congr($((isMorseSmale_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX
      ).signedMorseBoundary_single_eq_zero_of_unique_index_zero
        (isMorse_sphereHeight_sq_add_smul_sphereHeight_of_lt huv ht₀ ht₂) 𝔬 (p := p)
        (by omega) hmin
        (1 : ℤ)) q)
    simpa using this
  · exact (h hp1 hqv).elim

variable (hf : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)) {R : Type*} [Ring R]
  {m₁ m₂ s : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}

/-- **The integral Morse complex of the sphere with two maxima.** For `n ≥ 2`, `0 < t < 2`, any
adapted pseudo-gradient and any orientations of the unstable manifolds, let `m₁` and `m₂` be the two
maxima of `hᵤ² + t hᵥ` and `s` the saddle `v`. The Morse boundary, with coefficients in any ring,
sends a chain `c` to `(ε₁ c(m₁) + ε₂ c(m₂)) s`, where `εᵢ = ±1` is the sign of the trajectory from
`mᵢ` to `s`; the saddle and the minimum are cycles. -/
theorem signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight (hn : 2 ≤ n)
    (hm₁ : sphereHeight v m₁ = t / 2) (hm₂ : sphereHeight v m₂ = t / 2) (hm : m₁ ≠ m₂)
    (hs : (s : sphere (0 : E) 1) = v)
    (c : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) →₀ R) :
    hX.signedMorseBoundary 𝔬 hf R c = Finsupp.single s
      (c m₁ * hX.signedMorseBoundaryCoeff 𝔬 m₁ s + c m₂ * hX.signedMorseBoundaryCoeff 𝔬 m₂ s) := by
  classical
  ext q
  rw [signedMorseBoundary_apply, Finsupp.single_apply, Finsupp.sum]
  split_ifs with hsq
  · -- Only the two maxima contribute to the coefficient of the saddle.
    subst hsq
    have hzero (p) (hp : p ∉ ({m₁, m₂} : Finset _)) :
        c p * (hX.signedMorseBoundaryCoeff 𝔬 p s : R) = 0 := by
      rw [signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_zero huv ht₀ ht₂ hX 𝔬
        hn fun hp1 _ ↦ ?_, Int.cast_zero, mul_zero]
      rcases eq_or_eq_of_sphereHeight_eq huv ht₀ ht₂ p.property m₁.property m₂.property hp1 hm₁ hm₂
        (Subtype.coe_injective.ne hm) with h | h <;>
      · exact hp (by simp [Subtype.ext h])
    rw [Finset.sum_subset (s₂ := c.support ∪ {m₁, m₂}) Finset.subset_union_left
        fun p _ hp ↦ by rw [Finsupp.notMem_support_iff.1 hp, zero_mul],
      ← Finset.sum_subset Finset.subset_union_right fun p _ hp ↦ hzero p hp, Finset.sum_pair hm]
  · -- No other critical point is reached.
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    rw [signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_zero huv ht₀ ht₂ hX 𝔬 hn
      fun _ hq ↦ hsq (Subtype.ext (hs.trans hq.symm)), Int.cast_zero, mul_zero]

/-- **The integral cycles of the sphere with two maxima.** A chain is a cycle exactly when the
signed combination `ε₁ c(m₁) + ε₂ c(m₂)` of its coefficients at the two maxima vanishes. -/
theorem signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight_eq_zero_iff (hn : 2 ≤ n)
    (hm₁ : sphereHeight v m₁ = t / 2) (hm₂ : sphereHeight v m₂ = t / 2) (hm : m₁ ≠ m₂)
    (hs : (s : sphere (0 : E) 1) = v)
    (c : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) →₀ R) :
    hX.signedMorseBoundary 𝔬 hf R c = 0 ↔
      c m₁ * hX.signedMorseBoundaryCoeff 𝔬 m₁ s + c m₂ * hX.signedMorseBoundaryCoeff 𝔬 m₂ s =
        0 := by
  rw [signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX 𝔬 hf hn hm₁ hm₂ hm
    hs, Finsupp.single_eq_zero]

/-- **The integral boundaries of the sphere with two maxima.** The boundaries are the multiples of
the saddle `s`: the trajectory from either maximum to `s` counts with a sign `±1`, a unit. -/
theorem range_signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight (hn : 2 ≤ n)
    (hm₁ : sphereHeight v m₁ = t / 2) (hm₂ : sphereHeight v m₂ = t / 2) (hm : m₁ ≠ m₂)
    (hs : (s : sphere (0 : E) 1) = v) :
    LinearMap.range (hX.signedMorseBoundary 𝔬 hf R) = LinearMap.range (Finsupp.lsingle s) := by
  ext d
  simp only [LinearMap.mem_range, Finsupp.lsingle_apply]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX 𝔬 hf hn
      hm₁ hm₂ hm hs c).symm⟩
  · rintro ⟨r, rfl⟩
    set ε := hX.signedMorseBoundaryCoeff 𝔬 m₁ s
    refine ⟨Finsupp.single m₁ (r * ε), ?_⟩
    rw [signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX 𝔬 hf hn hm₁ hm₂
      hm hs, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hm.symm, zero_mul, add_zero]
    rcases signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_one_or_eq_neg_one huv
      ht₀ ht₂ hX 𝔬 (by omega) hm₁ hs with h | h <;>
      simp [ε, h]

open scoped Classical in
/-- **The signed sum of the maxima.** The orientations of the unstable manifolds of the maxima can
be reversed so that both trajectories into the saddle count positively. For these orientations the
Morse boundary sends `c` to `(c(m₁) + c(m₂)) s`, so the difference `m₁ - m₂` of the maxima is a
cycle. -/
theorem exists_signedMorseBoundary_reverse_sphereHeight_sq_add_smul_sphereHeight_eq (hn : 2 ≤ n)
    (hm₁ : sphereHeight v m₁ = t / 2) (hm₂ : sphereHeight v m₂ = t / 2) (hm : m₁ ≠ m₂)
    (hs : (s : sphere (0 : E) 1) = v) :
    ∃ S : Set (criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)), S ⊆ {m₁, m₂} ∧
      ∀ c : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) →₀ R,
        hX.signedMorseBoundary (𝔬.reverse S) hf R c = Finsupp.single s (c m₁ + c m₂) := by
  obtain ⟨S, hS⟩ : ∃ S : Set (criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)),
      ∀ p, p ∈ S ↔ (p = m₁ ∨ p = m₂) ∧ hX.signedMorseBoundaryCoeff 𝔬 p s = -1 :=
    ⟨{p | (p = m₁ ∨ p = m₂) ∧ hX.signedMorseBoundaryCoeff 𝔬 p s = -1}, fun _ ↦ Iff.rfl⟩
  refine ⟨S, fun p hp ↦ by simpa using ((hS p).1 hp).1, fun c ↦ ?_⟩
  -- The saddle is not a maximum, so its orientation is kept.
  have hsm : s ∉ S := by
    have hsv : sphereHeight v s = 1 := by rw [hs, sphereHeight_self]
    rw [hS]
    rintro ⟨rfl | rfl, -⟩ <;> linarith
  -- After the reversal both coefficients into the saddle are `1`.
  have hone {m : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
      (hmS : m = m₁ ∨ m = m₂) (hmv : sphereHeight v m = t / 2) :
      hX.signedMorseBoundaryCoeff (𝔬.reverse S) m s = 1 := by
    rcases signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_one_or_eq_neg_one huv
      ht₀ ht₂ hX 𝔬 (by omega) hmv hs with h | h <;>
      simp [signedMorseBoundaryCoeff_reverse, h, hmS, hsm, hS]
  rw [signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX _ hf hn hm₁ hm₂ hm
    hs, hone (Or.inl rfl) hm₁, hone (Or.inr rfl) hm₂, Int.cast_one, mul_one, mul_one]

/-- **The mod-two Morse complex of the sphere with two maxima.** For `n ≥ 2` and every adapted
pseudo-gradient, the mod-two Morse boundary sends a chain `c` to `(c(m₁) + c(m₂)) s`: one
trajectory runs from each maximum to the saddle `s`, and the saddle and the minimum are cycles. -/
theorem IsMorseSmale.morseBoundary_sphereHeight_sq_add_smul_sphereHeight (h : hX.IsMorseSmale)
    (hn : 2 ≤ n) (hm₁ : sphereHeight v m₁ = t / 2) (hm₂ : sphereHeight v m₂ = t / 2)
    (hm : m₁ ≠ m₂) (hs : (s : sphere (0 : E) 1) = v)
    (c : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) →₀ ZMod 2) :
    h.morseBoundary hf c = Finsupp.single s (c m₁ + c m₂) := by
  obtain ⟨𝔬⟩ := hX.nonempty_morseOrientation
  have hone {m : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
      (hmv : sphereHeight v m = t / 2) : (hX.signedMorseBoundaryCoeff 𝔬 m s : ZMod 2) = 1 := by
    rcases signedMorseBoundaryCoeff_sphereHeight_sq_add_smul_sphereHeight_eq_one_or_eq_neg_one huv
      ht₀ ht₂ hX 𝔬 (by omega) hmv hs with h | h <;>
      simp [h]
  rw [← h.signedMorseBoundary_eq_morseBoundary (𝔬 := 𝔬) hf,
    signedMorseBoundary_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂ hX 𝔬 hf hn hm₁ hm₂ hm hs,
    hone hm₁, hone hm₂, mul_one, mul_one]

end IsAdaptedPseudoGradient

end TauCeti
