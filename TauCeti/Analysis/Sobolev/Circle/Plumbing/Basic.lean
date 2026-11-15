/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Neck
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Ambient holomorphic evaluation of plumbing neck maps

For logarithmic boundary data `(F, G)` in the neck graph of `xy = a`, write `P` and `Q` for
its nonnegative parts. The Laurent series on the neck are
`P(x) - Q(a/x) + Q(0)` and `Q(y) - P(a/y) + P(0)`.
Substituting the independent ambient coordinates `x, y` gives holomorphic functions on the
bidisc, even at the node. Exponentiating and multiplying by `x, y` gives `neckEvaluation`.
We prove agreement with the original boundary maps on both outer circles, joint holomorphy
with varying Sobolev data, and the equation for the target smoothing parameter.

If the data depend holomorphically on `(a, t)`, their ambient evaluation uses `a = xy`.
Only after making this substitution may one restrict to a singular pullback `xy = s(t)`.
The product formula proves that this restriction maps into the target node equation, including
permanent nodes and smoothing parameters with zero derivative. No smoothness of the total
hypersurface is required. The construction does not by itself assert local invertibility or
the universal mapping property of a family.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§10–12.
-/

public noncomputable section

open Complex Filter Topology

namespace TauCeti.CircleSobolev

variable {s : ℝ}

/-- The ambient neck map in exponential coordinates. Only the nonnegative Fourier coefficients
of `p = (F, G)` are used. On `xy = a`, when `p ∈ neckGraph s ℂ a`, this extends the boundary
maps `x exp(F)` and `y exp(G)` to the bidisc. Outside the closed bidisc its series may diverge. -/
def neckEvaluation (p : CircleSobolev s ℂ × CircleSobolev s ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (z.1 * exp (diskFunction p.1 z.1 - diskFunction p.2 z.2 + p.2.coeff 0),
    z.2 * exp (diskFunction p.2 z.2 - diskFunction p.1 z.1 + p.1.coeff 0))

/-- The first coordinate of the ambient neck map. -/
@[simp]
theorem neckEvaluation_fst (p : CircleSobolev s ℂ × CircleSobolev s ℂ) (z : ℂ × ℂ) :
    (neckEvaluation p z).1 =
      z.1 * exp (diskFunction p.1 z.1 - diskFunction p.2 z.2 + p.2.coeff 0) :=
  (rfl)

/-- The second coordinate of the ambient neck map. -/
@[simp]
theorem neckEvaluation_snd (p : CircleSobolev s ℂ × CircleSobolev s ℂ) (z : ℂ × ℂ) :
    (neckEvaluation p z).2 =
      z.2 * exp (diskFunction p.2 z.2 - diskFunction p.1 z.1 + p.1.coeff 0) :=
  (rfl)

/-- The ambient map depends only on the nonnegative logarithmic modes. -/
@[simp]
theorem neckEvaluation_indicator_Ici (p : CircleSobolev s ℂ × CircleSobolev s ℂ)
    (z : ℂ × ℂ) :
    neckEvaluation (indicator (Set.Ici 0) p.1, indicator (Set.Ici 0) p.2) z =
      neckEvaluation p z := by
  simp [neckEvaluation]

/-- Interchanging the branches interchanges the coordinates of the ambient map. -/
@[simp]
theorem neckEvaluation_swap (p : CircleSobolev s ℂ × CircleSobolev s ℂ) (z : ℂ × ℂ) :
    neckEvaluation p.swap z.swap = (neckEvaluation p z).swap :=
  (rfl)

/-- Zero logarithmic boundary data give the identity map. -/
@[simp]
theorem neckEvaluation_zero (z : ℂ × ℂ) : neckEvaluation (0 : CircleSobolev s ℂ × _) z = z := by
  simp [neckEvaluation]

/-- The ambient map carries the node to the node. -/
@[simp]
theorem neckEvaluation_apply_zero (p : CircleSobolev s ℂ × CircleSobolev s ℂ) :
    neckEvaluation p 0 = 0 := by
  simp [neckEvaluation]

/-- The target smoothing parameter is the source parameter times the exponential of the sum
of the constant logarithmic modes. This identity is also valid at a permanent node. -/
theorem neckEvaluation_fst_mul_snd (p : CircleSobolev s ℂ × CircleSobolev s ℂ) (z : ℂ × ℂ) :
    (neckEvaluation p z).1 * (neckEvaluation p z).2 =
      z.1 * z.2 * exp (p.1.coeff 0 + p.2.coeff 0) := by
  simp only [neckEvaluation_fst, neckEvaluation_snd]
  rw [mul_mul_mul_comm, ← exp_add]
  congr 2
  ring

/-- Ambient neck evaluation is jointly holomorphic in both disc coordinates and any
holomorphically varying logarithmic Sobolev data. No lower bound on the Sobolev order is needed
in the open bidisc. -/
theorem analyticAt_neckEvaluation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {p : X → CircleSobolev s ℂ × CircleSobolev s ℂ} {z : X → ℂ × ℂ} {x : X}
    (hp : AnalyticAt ℂ p x) (hz : AnalyticAt ℂ z x)
    (hx : ‖(z x).1‖ < 1) (hy : ‖(z x).2‖ < 1) :
    AnalyticAt ℂ (fun t ↦ neckEvaluation (p t) (z t)) x := by
  have hP := analyticAt_fst.comp hp
  have hQ := analyticAt_snd.comp hp
  have hX := analyticAt_fst.comp hz
  have hY := analyticAt_snd.comp hz
  have hPX := analyticAt_diskFunction hP hX hx
  have hQY := analyticAt_diskFunction hQ hY hy
  have hP₀ := ((coeffCLM 0).analyticAt _).comp hP
  have hQ₀ := ((coeffCLM 0).analyticAt _).comp hQ
  simpa only [neckEvaluation, Function.comp_def, coeffCLM_apply, Pi.mul_apply, Pi.add_apply,
    Pi.sub_apply] using (hX.mul ((hPX.sub hQY).add hQ₀).cexp').prod
      (hY.mul ((hQY.sub hPX).add hP₀).cexp')

/-- If the boundary data depend on a smoothing parameter and additional parameters, their
ambient evaluation substitutes `xy` for the smoothing parameter before evaluating. This is
holomorphic on the bidisc wherever the given data are holomorphic at `(xy, t)`. -/
theorem analyticAt_neckEvaluation_mul {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {p : ℂ × A → CircleSobolev s ℂ × CircleSobolev s ℂ} {z : ℂ × ℂ} {t : A}
    (hp : AnalyticAt ℂ p (z.1 * z.2, t)) (hx : ‖z.1‖ < 1) (hy : ‖z.2‖ < 1) :
    AnalyticAt ℂ (fun w : (ℂ × ℂ) × A ↦
      neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1) (z, t) := by
  apply analyticAt_neckEvaluation
    (p := fun w : (ℂ × ℂ) × A ↦ p (w.1.1 * w.1.2, w.2))
    (z := Prod.fst) (x := (z, t)) _ analyticAt_fst hx hy
  exact hp.comp (f := fun w : (ℂ × ℂ) × A ↦ (w.1.1 * w.1.2, w.2))
    (((analyticAt_fst.comp analyticAt_fst).mul
      (analyticAt_snd.comp analyticAt_fst)).prod analyticAt_snd)

section Boundary

variable {T : ℝ} [Fact (0 < T)] {a : ℂ}

/-- On the first outer boundary circle, the ambient map agrees with `x exp(F)`. This remains
valid when `a = 0`. -/
theorem neckEvaluation_fst_boundary (hs : 1 / 2 < s) (ha : ‖a‖ ≤ 1)
    {p : CircleSobolev s ℂ × CircleSobolev s ℂ} (hp : p ∈ neckGraph s ℂ a)
    (x : AddCircle T) :
    (neckEvaluation p (fourier 1 x, a / fourier 1 x)).1 =
      fourier 1 x * exp (toContinuousMap T hs p.1 x) := by
  rw [neckEvaluation_fst, toContinuousMap_eq_diskFunction_sub_of_mem_neckGraph hs ha hp]

/-- On the second outer boundary circle, the ambient map agrees with `y exp(G)`, also for
permanent nodes. -/
theorem neckEvaluation_snd_boundary (hs : 1 / 2 < s) (ha : ‖a‖ ≤ 1)
    {p : CircleSobolev s ℂ × CircleSobolev s ℂ} (hp : p ∈ neckGraph s ℂ a)
    (y : AddCircle T) :
    (neckEvaluation p (a / fourier 1 y, fourier 1 y)).2 =
      fourier 1 y * exp (toContinuousMap T hs p.2 y) := by
  have hswap : p.swap ∈ neckGraph s ℂ a := mem_neckGraph.mpr fun n hn ↦
    ⟨(mem_neckGraph.mp hp n hn).2, (mem_neckGraph.mp hp n hn).1⟩
  simpa using neckEvaluation_fst_boundary hs ha hswap y

end Boundary

end TauCeti.CircleSobolev
