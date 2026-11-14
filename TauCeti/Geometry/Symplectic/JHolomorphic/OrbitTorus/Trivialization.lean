/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.NormalOperator
public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Complex.Inner
import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# The normal operator of an orbit torus in a unitary trivialization

Let `φ` be a diffeomorphism of a surface `M` and `x` a periodic point of period `d`. In the
covering `(ℝ × ℝ) × M` of `(ℝ / ℤ) × Y_φ`, the orbit torus of `x` lifts to the constant section
`(s, t) ↦ ((s, t), x)`, and an `s`-independent block almost complex structure is
`J'(a ∂s + b ∂t + w) = -b ∂s + a ∂t + K(t, y) w` at `((s, t), y)`, with `K(t, y)` complex
structures on the fibre. A vertical deformation `(s, t) ↦ ((s, t), y(s, t))` is
pseudoholomorphic exactly when `∂t y = K(t, y) ∂s y`, so the linearized Cauchy–Riemann operator of
the torus in vertical directions is `-K(t)` times

`D v = ∂s v + K(t) ∂t v`,  `K(t) = K(t, x)`

(`TauCeti.orbitTorusVerticalOperator`, `TauCeti.hasDerivAt_cauchyRiemannOperator_vertical`). The
deck transformation `((s, t), y) ↦ ((s, t + d), φ^(-d) y)` identifies the normal fibres at `t + d`
and `t` through the linearized return map `P = dφ^d_x`. So the normal sections of the torus twisted
by a real sign character `ε₂` along the orbit are the maps with `P v(s, t + d) = ε₂ v(s, t)`, and
the structures satisfy the seam identity `P K(t + d) = K(t) P`.

This file compares `D` with the model operator `∂s + J₀ ∂t + S(t)` of
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.NormalOperator`, whose kernel is governed by
the return map of the loop equation `w' = J₀ S(t) w`. A *unitary frame* is a `C²` path of
isomorphisms `Φ(t) : W → V` from a model space `W` with an orthogonal complex structure `J₀`,
such that

* `K(t) Φ(t) = Φ(t) J₀`, so that `Φ(t)` is complex linear;
* `σ(Φ(t) x, Φ(t) y) = ⟪J₀ x, y⟫` for the area form `σ` of the fibre;
* `P Φ(t + d) = Φ(t)`, so that the frame is compatible with the identification at the seam.

Its *connection* is `S(t) = J₀ Φ(t)⁻¹ Φ'(t)` (`TauCeti.frameConnection`). Then:

* `D (Φ w) = Φ (∂s w + J₀ ∂t w + S w)` (`TauCeti.orbitTorusVerticalOperator_frame_apply`);
* `S` is `d`-periodic, and symmetric because `Φ(t)` is symplectic
  (`TauCeti.frameConnection_periodic`, `TauCeti.isSymmetric_frameConnection`);
* the propagator `Ψ` of `w' = J₀ S(t) w` satisfies `Φ(t) Ψ(t) = Φ(0)`
  (`TauCeti.comp_dysonSeriesLeft_frameConnection`), so the model return map
  `Ψ(d) = Φ(d)⁻¹ P Φ(d)` is conjugate to the actual return map `P`.

Hence the twisted normal operators of the orbit torus, on every finite cover, have the kernels
predicted by the actual return map: on the cover with deck group spanned by `(k ℓ, 0)` and
`(a ℓ, n d)`, the operator twisted by `ε₁, ε₂` has a nonzero kernel exactly when `ε₁ = 1` and
`det (ε₂ - P ^ n) = 0`
(`TauCeti.exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_eq_one_and_det_eq_zero`), and
all four twisted operators on such a cover are nondegenerate exactly when
`det (1 - P ^ (2 n)) ≠ 0`
(`TauCeti.forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_det_ne_zero`). The conclusions
do not involve the frame. The untwisted operator and the operator twisted along the orbit are thus
compared with `det (1 - P)` and `det (1 + P)`.

When the fibre is a plane, unitary frames exist (`TauCeti.exists_unitary_frame_of_finrank_eq_two`):
transporting a complex-linear symplectic frame by `Φ' = -K' K Φ / 2` preserves both properties,
and the resulting monodromy across the seam is a rotation `exp (i θ)`, removed by the factor
`exp (-i θ t / d)`. So for orbits of a surface map the kernel criteria hold with hypotheses on
`K`, `σ` and `P` alone
(`TauCeti.exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two`,
`TauCeti.forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two`).

These are statements about classical `C²` sections over the parameter plane, with the twists
recorded as quasi-periodicity conditions. The determinant signs of the twisted operators, which
need a Fredholm realization and a homotopy to a complex-linear reference, are not treated here.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301--354.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped RealInnerProductSpace

namespace TauCeti

section VerticalOperator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u v : ℝ × ℝ → V} {z : ℝ × ℝ}

section
variable {K : ℝ → V →L[ℝ] V}

/-- The normal operator `D v = ∂s v + K(t) ∂t v` of an orbit torus in the vertical coordinates
of the suspension cover, acting on maps `v : ℝ × ℝ → V` with `s` the first and `t` the second
coordinate; `K(t)` is the vertical almost complex structure along the orbit. -/
def orbitTorusVerticalOperator (K : ℝ → V →L[ℝ] V) (v : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ v z stdComplexLineReal + K z.2 (fderiv ℝ v z stdComplexLineImag)

/-- Unfolding `orbitTorusVerticalOperator` at a point. -/
theorem orbitTorusVerticalOperator_apply :
    orbitTorusVerticalOperator K v z =
      fderiv ℝ v z stdComplexLineReal + K z.2 (fderiv ℝ v z stdComplexLineImag) :=
  (rfl)

/-- The vertical operator vanishes on the zero map. -/
@[simp]
theorem orbitTorusVerticalOperator_zero : orbitTorusVerticalOperator K (0 : ℝ × ℝ → V) = 0 := by
  funext z
  simp [orbitTorusVerticalOperator_apply]

/-- The vertical operator is additive on maps differentiable at the point. -/
theorem orbitTorusVerticalOperator_add (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    orbitTorusVerticalOperator K (u + v) z =
      orbitTorusVerticalOperator K u z + orbitTorusVerticalOperator K v z := by
  simp only [orbitTorusVerticalOperator_apply, fderiv_add hu hv, add_apply, map_add]
  abel

/-- The vertical operator commutes with multiplication by a real scalar. -/
@[simp]
theorem orbitTorusVerticalOperator_smul (c : ℝ) :
    orbitTorusVerticalOperator K (c • v) = c • orbitTorusVerticalOperator K v := by
  funext z
  simp only [orbitTorusVerticalOperator_apply, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, map_smul, smul_add]

end

/-- **The vertical operator is the normal linearization of an orbit torus.** On `(ℝ × ℝ) × V`, let
the block structure `J'` act at `((s, t), y)` by `(a, b, w) ↦ (-b, a, K(t, y) w)`, and let the
source `ℝ × ℝ` carry `j (a, b) = (-b, a)`. For a vertical deformation `u_ε(z) = (z, y₀ + ε v(z))`
of the constant section `z ↦ (z, y₀)`, the Cauchy–Riemann defect `du_ε ∘ j - J'(u_ε) du_ε` on `∂s`
has derivative `(0, -K(t, y₀) D v)` at `ε = 0`, where `D = ∂s + K(t, y₀) ∂t` is the vertical
operator. Since `K(t, y₀)` is invertible, the linearized Cauchy–Riemann equation in vertical
directions is `D v = 0`. -/
theorem hasDerivAt_cauchyRiemannOperator_vertical {K : ℝ → V → V →L[ℝ] V} {y₀ : V}
    (hv : DifferentiableAt ℝ v z) (hK : DifferentiableAt ℝ (K z.2) y₀)
    (hKsq : ∀ x, K z.2 y₀ (K z.2 y₀ x) = -x) :
    HasDerivAt (fun ε : ℝ => cauchyRiemannOperator ((-snd ℝ ℝ ℝ).prod (fst ℝ ℝ ℝ))
        (fun p : (ℝ × ℝ) × V => ((-snd ℝ ℝ ℝ).prod (fst ℝ ℝ ℝ)).prodMap (K p.1.2 p.2))
        (fun z => (z, y₀ + ε • v z)) z stdComplexLineReal)
      (0, -K z.2 y₀ (orbitTorusVerticalOperator (fun t => K t y₀) v z)) 0 := by
  set g : ℝ → V := fun ε => fderiv ℝ v z stdComplexLineImag -
    K z.2 (y₀ + ε • v z) (fderiv ℝ v z stdComplexLineReal)
  -- The defect of `u_ε` on `∂s` is `(0, ε g(ε))`.
  have hdefect (ε : ℝ) : cauchyRiemannOperator ((-snd ℝ ℝ ℝ).prod (fst ℝ ℝ ℝ))
      (fun p : (ℝ × ℝ) × V => ((-snd ℝ ℝ ℝ).prod (fst ℝ ℝ ℝ)).prodMap (K p.1.2 p.2))
      (fun z => (z, y₀ + ε • v z)) z stdComplexLineReal = (0, ε • g ε) := by
    have hu : HasFDerivAt (fun z => (z, y₀ + ε • v z))
        ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (ε • fderiv ℝ v z)) z :=
      (hasFDerivAt_id z).prodMk ((hv.hasFDerivAt.const_smul ε).const_add y₀)
    rw [cauchyRiemannOperator_apply, hu.fderiv]
    simp [g, stdComplexLineReal, stdComplexLineImag, smul_sub]
  have hKε : DifferentiableAt ℝ (fun ε : ℝ => K z.2 (y₀ + ε • v z)) 0 := by
    refine DifferentiableAt.comp (𝕜 := ℝ) (g := K z.2) 0 (by simpa using hK) ?_
    fun_prop
  have hgd : DifferentiableAt ℝ g 0 :=
    (differentiableAt_const _).sub (hKε.clm_apply (differentiableAt_const _))
  have h := ((hasDerivAt_id (0 : ℝ)).smul hgd.hasDerivAt)
  rw [funext hdefect]
  refine (HasDerivAt.prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ × ℝ)) h).congr_deriv ?_
  simp [g, orbitTorusVerticalOperator_apply, hKsq, sub_eq_add_neg]

end VerticalOperator

section Frame

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The connection `S(t) = J₀ Φ(t)⁻¹ Φ'(t)` of a path of frames `Φ(t) : W → V`. When `Φ(t)`
intertwines `J₀` with the complex structures of the fibres, conjugating the vertical operator of an
orbit torus by `Φ` gives the model operator `∂s + J₀ ∂t + S(t)`
(`TauCeti.orbitTorusVerticalOperator_frame_apply`). -/
def frameConnection (J₀ : W →L[ℝ] W) (Φ : ℝ → W →L[ℝ] V) (t : ℝ) : W →L[ℝ] W :=
  J₀ ∘L (Φ t).inverse ∘L deriv Φ t

variable {J₀ : W →L[ℝ] W} {Φ : ℝ → W →L[ℝ] V} {t : ℝ}

/-- Unfolding `frameConnection`. -/
theorem frameConnection_apply (x : W) :
    frameConnection J₀ Φ t x = J₀ ((Φ t).inverse (deriv Φ t x)) :=
  (rfl)

/-- The derivative of a frame is recovered from its connection: `Φ' = -Φ J₀ S`, when `J₀² = -1`. -/
theorem deriv_eq_neg_comp_frameConnection (hΦ : (Φ t).IsInvertible)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) :
    deriv Φ t = -(Φ t ∘L J₀ ∘L frameConnection J₀ Φ t) := by
  ext x
  simp [frameConnection_apply, hJ₀sq, hΦ]

/-- A frame differentiable `m + 1` times, with invertible values, has a connection differentiable
`m` times. -/
theorem contDiff_frameConnection [CompleteSpace W] {m : ℕ} (hΦ : ContDiff ℝ (m + 1) Φ)
    (hinv : ∀ t, (Φ t).IsInvertible) : ContDiff ℝ m (frameConnection J₀ Φ) := by
  have hderiv : ContDiff ℝ m (deriv Φ) := (contDiff_succ_iff_deriv.1 hΦ).2.2
  have hinverse : ContDiff ℝ m fun t => (Φ t).inverse :=
    contDiff_iff_contDiffAt.2 fun t =>
      (hinv t).contDiffAt_map_inverse.comp t (hΦ.of_le (by simp)).contDiffAt
  exact contDiff_const.clm_comp (hinverse.clm_comp hderiv)

/-- **The propagator of the connection undoes the frame.** For a differentiable frame with
invertible values and a continuous connection `S`, with `J₀² = -1`, the propagator `Ψ` of the
loop equation `w' = J₀ S(t) w` satisfies `Φ(t) Ψ(t) = Φ(0)`. Hence `Ψ(t) = Φ(t)⁻¹ Φ(0)`. -/
theorem comp_dysonSeriesLeft_frameConnection [CompleteSpace W] (hΦd : Differentiable ℝ Φ)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : Continuous (frameConnection J₀ Φ)) (t : ℝ) :
    Φ t ∘L dysonSeriesLeft (fun t => J₀ ∘L frameConnection J₀ Φ t) t = Φ 0 := by
  set Ψ := dysonSeriesLeft (fun t => J₀ ∘L frameConnection J₀ Φ t)
  have hM : Continuous fun t => J₀ ∘L frameConnection J₀ Φ t := continuous_const.clm_comp hS
  have hd (s : ℝ) : HasDerivAt (fun s => Φ s ∘L Ψ s) 0 s := by
    refine ((hΦd s).hasDerivAt.clm_comp (hasDerivAt_dysonSeriesLeft hM s)).congr_deriv ?_
    rw [deriv_eq_neg_comp_frameConnection (hΦ s) hJ₀sq, mul_def]
    ext x
    simp
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    fun s => (hd s).deriv
  simpa [Ψ, one_def] using hconst t 0

/-- Differentiating a seam identity `P Φ(t + d) = G(t)` gives `P Φ'(t + d) = G'(t)`. -/
private theorem comp_deriv_add_eq {P : V →L[ℝ] V} {d : ℝ} {G : ℝ → W →L[ℝ] V} {G' : W →L[ℝ] V}
    (hΦd : DifferentiableAt ℝ Φ (t + d)) (hG : HasDerivAt G G' t)
    (hseam : ∀ t, P ∘L Φ (t + d) = G t) : P ∘L deriv Φ (t + d) = G' := by
  have h : HasDerivAt (fun s => P ∘L Φ (s + d)) (P ∘L deriv Φ (t + d)) t := by
    simpa using (hasDerivAt_const t P).clm_comp (hΦd.hasDerivAt.comp_add_const t d)
  rw [funext hseam] at h
  exact h.unique hG

/-- **Periodicity of the connection.** If the frame is compatible with the seam,
`P Φ(t + d) = Φ(t)`, then its connection is `d`-periodic. -/
theorem frameConnection_periodic {P : V →L[ℝ] V} {d : ℝ} (hΦd : Differentiable ℝ Φ)
    (hΦ : ∀ t, (Φ t).IsInvertible) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t) :
    Function.Periodic (frameConnection J₀ Φ) d := by
  intro t
  ext x
  rw [frameConnection_apply, frameConnection_apply]
  congr 1
  refine (hΦ t).injective ?_
  rw [(hΦ t).self_apply_inverse, ← comp_deriv_add_eq (hΦd _) (hΦd t).hasDerivAt hseam, ← hseam t,
    coe_comp, Function.comp_apply, (hΦ (t + d)).self_apply_inverse, coe_comp, Function.comp_apply]

/-- Iterating the seam identity: `P ^ n Φ(t + n d) = Φ(t)`. -/
private theorem pow_comp_add_natCast_mul {P : V →L[ℝ] V} {d : ℝ}
    (hseam : ∀ t, P ∘L Φ (t + d) = Φ t) (n : ℕ) (t : ℝ) : (P ^ n) ∘L Φ (t + n * d) = Φ t := by
  induction n generalizing t with
  | zero => simp [one_def]
  | succ n ih =>
    rw [pow_succ, mul_def, comp_assoc, Nat.cast_succ, add_one_mul, ← add_assoc, hseam, ih]

end Frame

section InnerFrame

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {J₀ : W →L[ℝ] W} {Φ : ℝ → W →L[ℝ] V} {t : ℝ}

/-- **Conjugating the vertical operator by a frame.** If `Φ(t)` is invertible and intertwines
`J₀` with `K(t)`, then `D (Φ w) = Φ (∂s w + J₀ ∂t w + S w)`, where `D = ∂s + K(t) ∂t` is the
vertical operator and `S` the connection of `Φ`. -/
theorem orbitTorusVerticalOperator_frame_apply {K : ℝ → V →L[ℝ] V} {w : ℝ × ℝ → W}
    {z : ℝ × ℝ} (hΦd : DifferentiableAt ℝ Φ z.2) (hw : DifferentiableAt ℝ w z)
    (hΦ : (Φ z.2).IsInvertible) (hK : K z.2 ∘L Φ z.2 = Φ z.2 ∘L J₀) :
    orbitTorusVerticalOperator K (fun z => Φ z.2 (w z)) z =
      Φ z.2 (orbitTorusOperator J₀ (frameConnection J₀ Φ) w z) := by
  have hd : HasFDerivAt (fun z : ℝ × ℝ => Φ z.2 (w z))
      ((Φ z.2).comp (fderiv ℝ w z) +
        ((fderiv ℝ Φ z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).flip (w z)) z :=
    (hΦd.hasFDerivAt.comp z hasFDerivAt_snd).clm_apply hw.hasFDerivAt
  have hKx (x : W) : K z.2 (Φ z.2 x) = Φ z.2 (J₀ x) := congrArg (· x) hK
  have hKΦ' : K z.2 (deriv Φ z.2 (w z)) = Φ z.2 (frameConnection J₀ Φ z.2 (w z)) := by
    rw [frameConnection_apply, ← hKx, hΦ.self_apply_inverse]
  rw [orbitTorusVerticalOperator_apply, hd.fderiv, orbitTorusOperator_apply]
  simp only [add_apply, coe_comp, Function.comp_apply, flip_apply, coe_snd',
    stdComplexLineReal_snd, stdComplexLineImag_snd, map_zero, zero_apply, add_zero,
    fderiv_apply_one_eq_deriv, map_add, hKx, hKΦ']

/-- **Symmetry of the connection of a unitary frame.** If `J₀` is skew-adjoint and the frame
pulls a continuous bilinear form `ω` on `V` back to the form `⟪J₀ x, y⟫`, then its connection is
symmetric. -/
theorem isSymmetric_frameConnection (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hΦd : DifferentiableAt ℝ Φ t) (hΦ : (Φ t).IsInvertible) {ω : V →L[ℝ] V →L[ℝ] ℝ}
    (hω : ∀ t x y, ω (Φ t x) (Φ t y) = ⟪J₀ x, y⟫) :
    (frameConnection J₀ Φ t : W →ₗ[ℝ] W).IsSymmetric := by
  intro x y
  have hx := hΦd.hasDerivAt.clm_apply (hasDerivAt_const t x)
  have hy := hΦd.hasDerivAt.clm_apply (hasDerivAt_const t y)
  simp only [map_zero, add_zero] at hx hy
  have h0 := ω.apply_add_apply_eq_zero_of_const hx hy (hω · x y)
  rw [← hΦ.self_apply_inverse (deriv Φ t x), ← hΦ.self_apply_inverse (deriv Φ t y), hω, hω,
    hJ₀ x] at h0
  rw [coe_coe, frameConnection_apply, frameConnection_apply]
  linarith

end InnerFrame

section Kernel

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  {J₀ : W →L[ℝ] W} {Φ : ℝ → W →L[ℝ] V} {K : ℝ → V →L[ℝ] V} {P : V →L[ℝ] V}
  {ℓ d ε₁ ε₂ : ℝ}

/-- **Transport of twisted kernels along a frame.** For a `C²` frame with invertible values,
intertwining `J₀` with `K(t)` and compatible with the seam, the vertical operator `∂s + K(t) ∂t`
has a nonzero `C²` kernel element twisted by `ε₁` along `(k ℓ, 0)` and, through the return map,
by `ε₂` along `(a ℓ, n d)` (`P ^ n v(s + a ℓ, t + n d) = ε₂ v(s, t)`), exactly when the model
operator `∂s + J₀ ∂t + S(t)` has a nonzero `C²` kernel element with the plain twists `ε₁` and
`ε₂`. The two correspond by `v(s, t) = Φ(t) w(s, t)`. -/
theorem exists_orbitTorusVerticalOperator_eq_zero_iff_exists_orbitTorusOperator_eq_zero
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hΦ2 : ContDiff ℝ 2 Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hK : ∀ t, K t ∘L Φ t = Φ t ∘L J₀) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t) (k n : ℕ) (a : ℤ) :
    (∃ v : ℝ × ℝ → V, ContDiff ℝ 2 v ∧ v ≠ 0 ∧ (∀ s t, v (s + k * ℓ, t) = ε₁ • v (s, t)) ∧
      (∀ s t, (P ^ n) (v (s + a * ℓ, t + n * d)) = ε₂ • v (s, t)) ∧
      ∀ z, orbitTorusVerticalOperator K v z = 0) ↔
      ∃ w : ℝ × ℝ → W, ContDiff ℝ 2 w ∧ w ≠ 0 ∧ (∀ s t, w (s + k * ℓ, t) = ε₁ • w (s, t)) ∧
        (∀ s t, w (s + a * ℓ, t + n * d) = ε₂ • w (s, t)) ∧
        ∀ z, orbitTorusOperator J₀ (frameConnection J₀ Φ) w z = 0 := by
  have hΦd : Differentiable ℝ Φ := hΦ2.differentiable (by norm_num)
  have hS1 : ContDiff ℝ 1 (frameConnection J₀ Φ) := contDiff_frameConnection (m := 1) hΦ2 hΦ
  set Ψ := dysonSeriesLeft (fun t => J₀ ∘L frameConnection J₀ Φ t)
  have hΨ : ContDiff ℝ 2 Ψ := contDiff_dysonSeriesLeft (n := 1) (contDiff_const.clm_comp hS1)
  have hΦΨ (t : ℝ) (x : W) : Φ t (Ψ t x) = Φ 0 x :=
    congrArg (· x) (comp_dysonSeriesLeft_frameConnection hΦd hΦ hJ₀sq hS1.continuous t)
  have hseamn (t : ℝ) (x : W) : (P ^ n) (Φ (t + n * d) x) = Φ t x :=
    congrArg (· x) (pow_comp_add_natCast_mul hseam n t)
  -- The vertical operator on `Φ w` is `Φ` applied to the model operator on `w`.
  have hD (w : ℝ × ℝ → W) (hw : ContDiff ℝ 2 w) (z : ℝ × ℝ) :
      orbitTorusVerticalOperator K (fun z => Φ z.2 (w z)) z =
        Φ z.2 (orbitTorusOperator J₀ (frameConnection J₀ Φ) w z) :=
    orbitTorusVerticalOperator_frame_apply (hΦd _) ((hw.differentiable (by norm_num)) z) (hΦ _)
      (hK _)
  constructor
  · rintro ⟨v, hv, hne, hs, ht, hDv⟩
    -- `w(s, t) = Φ(t)⁻¹ v(s, t) = Ψ(t) Φ(0)⁻¹ v(s, t)`.
    set w : ℝ × ℝ → W := fun z => Ψ z.2 ((Φ 0).inverse (v z)) with hw_def
    have hvw : v = fun z => Φ z.2 (w z) := funext fun z => by
      rw [hw_def, hΦΨ, (hΦ 0).self_apply_inverse]
    have hw : ContDiff ℝ 2 w :=
      (hΨ.comp contDiff_snd).clm_apply ((contDiff_const (c := (Φ 0).inverse)).clm_apply hv)
    refine ⟨w, hw, fun h => hne (by rw [hvw, h]; funext z; simp), fun s t => ?_, fun s t => ?_,
      fun z => (hΦ z.2).injective ?_⟩
    · simp only [hw_def, hs, map_smul]
    · refine (hΦ t).injective ?_
      have h1 := hseamn t (w (s + a * ℓ, t + n * d))
      rw [← h1, map_smul]
      have h2 := congrFun hvw (s + a * ℓ, t + n * d)
      have h3 := congrFun hvw (s, t)
      simp only at h2 h3
      rw [← h2, ← h3, ht]
    · rw [← hD w hw z, ← hvw, hDv, map_zero]
  · rintro ⟨w, hw, hne, hs, ht, hDw⟩
    refine ⟨fun z => Φ z.2 (w z), (hΦ2.comp contDiff_snd).clm_apply hw, fun h => hne ?_,
      fun s t => ?_, fun s t => ?_, fun z => ?_⟩
    · funext z
      exact (hΦ z.2).injective (by simpa using congrFun h z)
    · simp only [hs, map_smul]
    · simp only [ht, map_smul, hseamn]
    · rw [hD w hw z, hDw, map_zero]

/-- The model return map is conjugate to the actual return map: `Ψ(d) = Φ(d)⁻¹ P Φ(d)`, so
`det (c - Ψ(d) ^ n) = det (c - P ^ n)` for every scalar `c`. -/
private theorem det_smul_one_sub_dysonSeriesLeft_pow (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hΦ2 : ContDiff ℝ 2 Φ) (hΦ : ∀ t, (Φ t).IsInvertible) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t)
    (c : ℝ) (n : ℕ) :
    LinearMap.det
      ((c • 1 - dysonSeriesLeft (fun t => J₀ ∘L frameConnection J₀ Φ t) d ^ n : W →L[ℝ] W) :
        W →ₗ[ℝ] W) =
      LinearMap.det ((c • 1 - P ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
  have hΦd : Differentiable ℝ Φ := hΦ2.differentiable (by norm_num)
  have hS : Continuous (frameConnection J₀ Φ) :=
    (contDiff_frameConnection (m := 1) hΦ2 hΦ).continuous
  set Ψ := dysonSeriesLeft (fun t => J₀ ∘L frameConnection J₀ Φ t)
  obtain ⟨e, he⟩ := hΦ d
  -- `Φ(d) Ψ(d) = Φ(0) = P Φ(d)`, hence `Φ(d) Ψ(d) ^ n = P ^ n Φ(d)`.
  have h1 : Φ d ∘L Ψ d = P ∘L Φ d := by
    rw [comp_dysonSeriesLeft_frameConnection hΦd hΦ hJ₀sq hS d, ← hseam 0, zero_add]
  have hn : Φ d ∘L (Ψ d ^ n) = (P ^ n) ∘L Φ d := by
    induction n with
    | zero => simp [one_def]
    | succ n ih => rw [pow_succ, mul_def, ← comp_assoc, ih, comp_assoc, h1, ← comp_assoc,
        ← mul_def, ← pow_succ]
  have hx (x : W) : e ((Ψ d ^ n) x) = (P ^ n) (e x) := by
    simpa [← he] using congrArg (· x) hn
  have hconj : ((c • 1 - Ψ d ^ n : W →L[ℝ] W) : W →ₗ[ℝ] W) =
      (e.symm.toLinearEquiv : V →ₗ[ℝ] W) ∘ₗ ((c • 1 - P ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V) ∘ₗ
        (e.symm.toLinearEquiv.symm : W →ₗ[ℝ] V) := by
    ext x
    apply e.injective
    simp [-toLinearMap_pow, hx]
  rw [hconj, LinearMap.det_conj]

variable [FiniteDimensional ℝ W]

/-- **Kernels of the twisted normal operators of an orbit torus on finite covers.** Let `W` be
finite-dimensional with an orthogonal complex structure `J₀`, and let `Φ` be a unitary frame for
the vertical structures `K(t)`: a `C²` path of isomorphisms `Φ(t) : W → V` with
`K(t) Φ(t) = Φ(t) J₀`, `ω(Φ(t) x, Φ(t) y) = ⟪J₀ x, y⟫` and `P Φ(t + d) = Φ(t)`. On the cover with
deck group spanned by `(k ℓ, 0)` and `(a ℓ, n d)`, `k, n ≥ 1`, the vertical operator
`∂s + K(t) ∂t` twisted by `ε₁` along `(k ℓ, 0)`, and by `ε₂` along `(a ℓ, n d)` through the
return map `P`, has a nonzero `C²` kernel element exactly when `ε₁ = 1` and
`det (ε₂ - P ^ n) = 0`. -/
theorem exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_eq_one_and_det_eq_zero
    (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hΦ2 : ContDiff ℝ 2 Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hK : ∀ t, K t ∘L Φ t = Φ t ∘L J₀) {ω : V →L[ℝ] V →L[ℝ] ℝ}
    (hω : ∀ t x y, ω (Φ t x) (Φ t y) = ⟪J₀ x, y⟫) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t)
    (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    (∃ v : ℝ × ℝ → V, ContDiff ℝ 2 v ∧ v ≠ 0 ∧ (∀ s t, v (s + k * ℓ, t) = ε₁ • v (s, t)) ∧
      (∀ s t, (P ^ n) (v (s + a * ℓ, t + n * d)) = ε₂ • v (s, t)) ∧
      ∀ z, orbitTorusVerticalOperator K v z = 0) ↔
      ε₁ = 1 ∧ LinearMap.det ((ε₂ • 1 - P ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V) = 0 := by
  have hΦd : Differentiable ℝ Φ := hΦ2.differentiable (by norm_num)
  rw [exists_orbitTorusVerticalOperator_eq_zero_iff_exists_orbitTorusOperator_eq_zero hJ₀sq hΦ2
      hΦ hK hseam k n a,
    exists_ne_zero_orbitTorusOperator_eq_zero_iff_eq_one_and_det_eq_zero hℓ hd hJ₀ hJ₀sq
      (fun t => isSymmetric_frameConnection hJ₀ (hΦd t) (hΦ t) hω)
      (contDiff_frameConnection (m := 1) hΦ2 hΦ) (frameConnection_periodic hΦd hΦ hseam) hε₁ hε₂
      hk hn a,
    det_smul_one_sub_dysonSeriesLeft_pow hJ₀sq hΦ2 hΦ hseam]

/-- **Nondegeneracy of an orbit torus on finite covers through twice the period.** Under the
hypotheses of `exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_eq_one_and_det_eq_zero`, the
vertical operators twisted by all four real sign characters of the cover with deck group spanned
by `(k ℓ, 0)` and `(a ℓ, n d)` have no nonzero `C²` kernel element exactly when
`det (1 - P ^ (2 n)) ≠ 0`. Consequently, if no iterate `P ^ j` with `1 ≤ j ≤ 2 N` of the return
map has eigenvalue `1`, all twisted normal operators of the orbit torus on all covers of degree at
most `N` along the orbit are nondegenerate. -/
theorem forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_det_ne_zero
    (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hΦ2 : ContDiff ℝ 2 Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hK : ∀ t, K t ∘L Φ t = Φ t ∘L J₀) {ω : V →L[ℝ] V →L[ℝ] ℝ}
    (hω : ∀ t x y, ω (Φ t x) (Φ t y) = ⟪J₀ x, y⟫) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t)
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    (∀ ε₁ ε₂ : ℝ, ε₁ ^ 2 = 1 → ε₂ ^ 2 = 1 → ∀ v : ℝ × ℝ → V, ContDiff ℝ 2 v →
      (∀ s t, v (s + k * ℓ, t) = ε₁ • v (s, t)) →
      (∀ s t, (P ^ n) (v (s + a * ℓ, t + n * d)) = ε₂ • v (s, t)) →
      (∀ z, orbitTorusVerticalOperator K v z = 0) → v = 0) ↔
      LinearMap.det ((1 - P ^ (2 * n) : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0 := by
  have hΦd : Differentiable ℝ Φ := hΦ2.differentiable (by norm_num)
  have hmodel := forall_eq_zero_of_orbitTorusOperator_eq_zero_iff_det_ne_zero hℓ hd hJ₀ hJ₀sq
    (fun t => isSymmetric_frameConnection hJ₀ (hΦd t) (hΦ t) hω)
    (contDiff_frameConnection (m := 1) hΦ2 hΦ) (frameConnection_periodic hΦd hΦ hseam) hk hn a
  have hdet := det_smul_one_sub_dysonSeriesLeft_pow hJ₀sq hΦ2 hΦ hseam 1 (2 * n)
  rw [one_smul, one_smul] at hdet
  rw [← hdet, ← hmodel]
  refine forall₂_congr fun ε₁ ε₂ => forall₂_congr fun _ _ => ?_
  have htr := exists_orbitTorusVerticalOperator_eq_zero_iff_exists_orbitTorusOperator_eq_zero
    (ℓ := ℓ) (ε₁ := ε₁) (ε₂ := ε₂) hJ₀sq hΦ2 hΦ hK hseam k n a
  constructor
  · intro h w hw hs ht hD
    by_contra hne
    obtain ⟨v, hv, hvne, hvs, hvt, hvD⟩ := htr.2 ⟨w, hw, hne, hs, ht, hD⟩
    exact hvne (h v hv hvs hvt hvD)
  · intro h v hv hs ht hD
    by_contra hne
    obtain ⟨w, hw, hwne, hws, hwt, hwD⟩ := htr.1 ⟨v, hv, hne, hs, ht, hD⟩
    exact hwne (h w hw hws hwt hwD)

end Kernel

section FrameExistence

/-! ### Unitary frames along an orbit of a surface map

For a two-dimensional fibre `V` the model space is `ℂ` with `J₀ z = i z`. A unitary frame is
built in three steps: an initial complex-linear symplectic frame at `t = 0`
(`TauCeti.exists_frame_of_tame_of_finrank_eq_two`); its transport by the equation `Φ' = A Φ`
with `A = -K' K / 2`, which preserves `K Φ = Φ J₀` and `σ`; and a rotation `z ↦ exp(-i θ t / d) z`
removing the monodromy `exp(i θ)` of the transported frame across the seam
(`Complex.exists_apply_eq_mul_exp`). -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : ℝ → V →L[ℝ] V}
  {σ : V →L[ℝ] V →L[ℝ] ℝ}

/-- The transport generator `A = -K' K / 2` satisfies `A K - K A = K'`. -/
private theorem comp_sub_comp_eq_deriv (hKd : Differentiable ℝ K)
    (hKsq : ∀ t x, K t (K t x) = -x) (t : ℝ) :
    (-(1 / 2 : ℝ) • (deriv K t ∘L K t)) ∘L K t - K t ∘L (-(1 / 2 : ℝ) • (deriv K t ∘L K t)) =
      deriv K t := by
  -- Differentiating `K ∘ K = -1` gives `K' K + K K' = 0`.
  have h : deriv K t ∘L K t + K t ∘L deriv K t = 0 := by
    simpa using (compL ℝ V V V).apply_add_apply_eq_zero_of_const (hKd t).hasDerivAt
      (hKd t).hasDerivAt (c := -1) fun s => by ext x; simp [hKsq]
  have hKD (x : V) : K t (deriv K t x) = -deriv K t (K t x) := by
    have := congrArg (· x) h
    simp only [add_apply, coe_comp, Function.comp_apply, zero_apply] at this
    linear_combination (norm := module) this
  ext x
  simp only [sub_apply, coe_comp, Function.comp_apply, smul_apply, map_smul, hKsq, map_neg, hKD]
  module

/-- The transport generator `A = -K' K / 2` is infinitesimally symplectic for a form preserved by
every `K t`. -/
private theorem apply_comp_add_apply_comp (hKd : Differentiable ℝ K)
    (hKsq : ∀ t x, K t (K t x) = -x) (hσK : ∀ t x y, σ (K t x) (K t y) = σ x y) (t : ℝ)
    (u w : V) :
    σ ((-(1 / 2 : ℝ) • (deriv K t ∘L K t)) u) w +
      σ u ((-(1 / 2 : ℝ) • (deriv K t ∘L K t)) w) = 0 := by
  -- Differentiating `σ (K a) (K b) = σ a b` gives `σ (K' a) (K b) + σ (K a) (K' b) = 0`.
  have hd (a b : V) : σ (deriv K t a) (K t b) + σ (K t a) (deriv K t b) = 0 := by
    have ha := (hKd t).hasDerivAt.clm_apply (hasDerivAt_const t a)
    have hb := (hKd t).hasDerivAt.clm_apply (hasDerivAt_const t b)
    simp only [map_zero, add_zero] at ha hb
    exact σ.apply_add_apply_eq_zero_of_const ha hb (hσK · a b)
  have h := hd (K t u) (-K t w)
  simp only [map_neg, hKsq, neg_neg, neg_apply] at h
  simp only [smul_apply, coe_comp, Function.comp_apply, map_smul, smul_apply, smul_eq_mul]
  linarith

/-- The seam identity `P K(t + d) = K(t) P` intertwines the transport generators:
`P A(t + d) = A(t) P` for `A = -K' K / 2`. -/
private theorem comp_transportGenerator_add (hKd : Differentiable ℝ K) {P : V →L[ℝ] V} {d : ℝ}
    (hPK : ∀ t, P ∘L K (t + d) = K t ∘L P) (t : ℝ) :
    P ∘L (-(1 / 2 : ℝ) • (deriv K (t + d) ∘L K (t + d))) =
      (-(1 / 2 : ℝ) • (deriv K t ∘L K t)) ∘L P := by
  have hD : P ∘L deriv K (t + d) = deriv K t ∘L P :=
    comp_deriv_add_eq (hKd _) (by simpa using (hKd t).hasDerivAt.clm_comp (hasDerivAt_const t P))
      hPK
  rw [comp_smul, smul_comp, ← comp_assoc, hD, comp_assoc, hPK, comp_assoc]

/-- The transported frame `Φ₁(t) = Γ(t) Φ₀`, `Γ` the propagator of `A = -K' K / 2`, is a `C²`
complex-linear symplectic frame, and across the seam it differs from itself by the monodromy
`C = Φ₀⁻¹ P Φ₁(d)`: `P Φ₁(t + d) = Φ₁(t) C`. -/
private theorem exists_frame_transport [CompleteSpace V] (hK2 : ContDiff ℝ 2 K)
    (hKsq : ∀ t x, K t (K t x) = -x) (hσK : ∀ t x y, σ (K t x) (K t y) = σ x y)
    {Φ₀ : ℂ →L[ℝ] V} (hΦ₀ : Φ₀.IsInvertible) (hK₀ : K 0 ∘L Φ₀ = Φ₀ ∘L lsmul ℝ ℂ Complex.I)
    (hσ₀ : ∀ x y, σ (Φ₀ x) (Φ₀ y) = ⟪lsmul ℝ ℂ Complex.I x, y⟫)
    {P : V →L[ℝ] V} {d : ℝ} (hPK : ∀ t, P ∘L K (t + d) = K t ∘L P) :
    ∃ Φ₁ : ℝ → ℂ →L[ℝ] V, ContDiff ℝ 2 Φ₁ ∧ (∀ t, (Φ₁ t).IsInvertible) ∧
      (∀ t, K t ∘L Φ₁ t = Φ₁ t ∘L lsmul ℝ ℂ Complex.I) ∧
      (∀ t x y, σ (Φ₁ t x) (Φ₁ t y) = ⟪lsmul ℝ ℂ Complex.I x, y⟫) ∧
      ∀ t z, P (Φ₁ (t + d) z) = Φ₁ t (Φ₀.inverse (P (Φ₁ d z))) := by
  have hKd : Differentiable ℝ K := hK2.differentiable (by norm_num)
  set A : ℝ → V →L[ℝ] V := fun t => -(1 / 2 : ℝ) • (deriv K t ∘L K t)
  have hA1 : ContDiff ℝ 1 A :=
    (((contDiff_succ_iff_deriv (n := 1)).1 hK2).2.2.clm_comp (hK2.of_le (by norm_num))).const_smul _
  have hAc : Continuous A := hA1.continuous
  set Γ := dysonSeriesLeft A
  have hΓ : ContDiff ℝ 2 Γ := contDiff_dysonSeriesLeft (n := 1) hA1
  have hΓ0 : Γ 0 = 1 := dysonSeriesLeft_zero A
  set Φ₁ : ℝ → ℂ →L[ℝ] V := fun t => Γ t ∘L Φ₀
  have hΦ₁0 : Φ₁ 0 = Φ₀ := by simp [Φ₁, hΓ0, one_def]
  -- `Φ₁` and its images of fixed vectors solve the transport equation `Φ' = A Φ`.
  have hΦ₁' (t : ℝ) (z : ℂ) : HasDerivAt (fun t => Φ₁ t z) (A t (Φ₁ t z)) t := by
    simpa [Φ₁] using hasDerivAt_dysonSeriesLeft_apply hAc (Φ₀ z) t
  refine ⟨Φ₁, hΓ.clm_comp contDiff_const, fun t => ?_, fun t => ?_, fun t x y => ?_,
    fun t z => ?_⟩
  · refine IsInvertible.comp (IsInvertible.of_inverse (g := dysonSeries (-A) t) ?_ ?_) hΦ₀
    · rw [← mul_def, dysonSeriesLeft_mul_dysonSeries_neg hAc, one_def]
    · rw [← mul_def, dysonSeries_neg_mul_dysonSeriesLeft hAc, one_def]
  · -- `X(t) = K(t) Φ₁(t) z - Φ₁(t) (i z)` solves `X' = A X` and vanishes at `0`.
    ext z
    have hX (s : ℝ) : HasDerivAt (fun s => K s (Φ₁ s z) - Φ₁ s (Complex.I • z))
        (A s (K s (Φ₁ s z) - Φ₁ s (Complex.I • z))) s := by
      refine (((hKd s).hasDerivAt.clm_apply (hΦ₁' s z)).sub (hΦ₁' s _)).congr_deriv ?_
      have hcomm := congrArg (· (Φ₁ s z)) (comp_sub_comp_eq_deriv hKd hKsq s)
      simp only [sub_apply, coe_comp, Function.comp_apply] at hcomm
      rw [map_sub, ← hcomm]
      abel
    have h := eq_dysonSeriesLeft_apply hAc hX t
    have h0 : K 0 (Φ₁ 0 z) - Φ₁ 0 (Complex.I • z) = 0 := by
      rw [hΦ₁0, sub_eq_zero]
      simpa using congrArg (· z) hK₀
    rw [h0, map_zero, sub_eq_zero] at h
    simpa using h
  · -- `σ (Φ₁ s x) (Φ₁ s y)` has derivative zero.
    have hd (s : ℝ) : HasDerivAt (fun s => σ (Φ₁ s x) (Φ₁ s y)) 0 s := by
      have h : HasDerivAt (fun s => σ (Φ₁ s x) (Φ₁ s y))
          (σ (A s (Φ₁ s x)) (Φ₁ s y) + σ (Φ₁ s x) (A s (Φ₁ s y))) s :=
        (σ.hasFDerivAt.comp_hasDerivAt s (hΦ₁' s x)).clm_apply (hΦ₁' s y)
      exact h.congr_deriv (apply_comp_add_apply_comp hKd hKsq hσK s _ _)
    have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      fun s => (hd s).deriv
    rw [hconst t 0, hΦ₁0, hσ₀]
  · -- Both sides solve the transport equation and agree at `t = 0`.
    have hY (s : ℝ) : HasDerivAt (fun s => P (Φ₁ (s + d) z)) (A s (P (Φ₁ (s + d) z))) s := by
      refine ((hasDerivAt_const s P).clm_apply ((hΦ₁' (s + d) z).comp_add_const s d)).congr_deriv
        ?_
      rw [zero_apply, zero_add]
      exact congrArg (· (Φ₁ (s + d) z)) (comp_transportGenerator_add hKd hPK s)
    rw [eq_dysonSeriesLeft_apply hAc hY t, zero_add]
    simp only [Φ₁, Γ, coe_comp, Function.comp_apply, hΦ₀.self_apply_inverse]

/-- **Unitary frames along an orbit of a surface map.** Let `V` be a real plane with a `C²` path
of complex structures `K(t)` preserving an antisymmetric form `σ`, which tames `K(0)`, and let `P`
preserve `σ` and satisfy the seam identity `P K(t + d) = K(t) P`, with `d ≠ 0`. Then there is a
unitary frame from `ℂ`, with `J₀ z = i z`: a `C²` path of isomorphisms `Φ(t) : ℂ → V` with
`K(t) Φ(t) = Φ(t) J₀`, `σ(Φ(t) x, Φ(t) y) = ⟪i x, y⟫` and `P Φ(t + d) = Φ(t)`. -/
theorem exists_unitary_frame_of_finrank_eq_two [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V = 2) (hK2 : ContDiff ℝ 2 K) (hKsq : ∀ t x, K t (K t x) = -x)
    (hσ : ∀ x y, σ x y = -σ y x) (hσK : ∀ t x y, σ (K t x) (K t y) = σ x y)
    (htame : ∀ x, x ≠ 0 → 0 < σ x (K 0 x)) {P : V →L[ℝ] V} {d : ℝ} (hd : d ≠ 0)
    (hPσ : ∀ x y, σ (P x) (P y) = σ x y) (hPK : ∀ t, P ∘L K (t + d) = K t ∘L P) :
    ∃ Φ : ℝ → ℂ →L[ℝ] V, ContDiff ℝ 2 Φ ∧ (∀ t, (Φ t).IsInvertible) ∧
      (∀ t, K t ∘L Φ t = Φ t ∘L lsmul ℝ ℂ Complex.I) ∧
      (∀ t x y, σ (Φ t x) (Φ t y) = ⟪lsmul ℝ ℂ Complex.I x, y⟫) ∧
      ∀ t, P ∘L Φ (t + d) = Φ t := by
  obtain ⟨Φ₀, hΦ₀, hK₀, hσ₀⟩ := exists_frame_of_tame_of_finrank_eq_two hV (hKsq 0) hσ htame
  obtain ⟨Φ₁, hΦ₁2, hΦ₁, hK₁, hσ₁, hseam₁⟩ := exists_frame_transport hK2 hKsq hσK hΦ₀ hK₀ hσ₀ hPK
  -- The monodromy `C = Φ₀⁻¹ P Φ₁(d)` is complex linear and unitary, so it is a rotation.
  set C : ℂ →L[ℝ] ℂ := Φ₀.inverse ∘L P ∘L Φ₁ d
  have hΦ₀C (z : ℂ) : Φ₀ (C z) = P (Φ₁ d z) := hΦ₀.self_apply_inverse _
  have hCI (z : ℂ) : C (Complex.I * z) = Complex.I * C z := by
    refine hΦ₀.injective ?_
    have h1 := congrArg (· z) (hK₁ d)
    have h2 := congrArg (· (Φ₁ d z)) (hPK 0)
    have h3 := congrArg (· (C z)) hK₀
    simp only [coe_comp, Function.comp_apply, lsmul_apply, smul_eq_mul, zero_add] at h1 h2 h3
    rw [hΦ₀C, ← h1, h2, ← hΦ₀C, h3]
  have hCω : ⟪Complex.I * C 1, C Complex.I⟫ = ⟪Complex.I, Complex.I⟫ := by
    have h := hσ₁ d 1 Complex.I
    rw [← hPσ, ← hΦ₀C, ← hΦ₀C, hσ₀] at h
    simpa using h
  obtain ⟨θ, hθ⟩ := Complex.exists_apply_eq_mul_exp (C := (C : ℂ →ₗ[ℝ] ℂ)) (by simpa using hCI)
    (by simpa using hCω)
  have hC (w : ℂ) : Φ₀.inverse (P (Φ₁ d w)) = w * Complex.exp (θ * Complex.I) := by
    simpa [C] using hθ w
  -- Correct the monodromy by the rotation `R(t) z = exp(-i θ t / d) z`.
  set e : ℝ → ℂ := fun t => Complex.exp (↑(-(θ / d) * t) * Complex.I)
  have he (t : ℝ) : ‖e t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he2 : ContDiff ℝ 2 e := by
    have h : ContDiff ℝ 2 fun t : ℝ => ((-(θ / d) * t : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    exact (h.mul contDiff_const).cexp
  have hR2 : ContDiff ℝ 2 fun t => (lsmul ℝ ℂ (e t) : ℂ →L[ℝ] ℂ) :=
    (lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).contDiff.comp he2
  refine ⟨fun t => Φ₁ t ∘L lsmul ℝ ℂ (e t), hΦ₁2.clm_comp hR2, fun t => ?_, fun t => ?_,
    fun t x y => ?_, fun t => ?_⟩
  · refine (hΦ₁ t).comp (IsInvertible.of_inverse (g := lsmul ℝ ℂ (e t)⁻¹) ?_ ?_) <;>
      ext z <;> simp [Complex.exp_ne_zero, e]
  · ext z
    have h := congrArg (· (e t * z)) (hK₁ t)
    simp only [coe_comp, Function.comp_apply, lsmul_apply, smul_eq_mul] at h ⊢
    rw [h, mul_left_comm]
  · simp only [coe_comp, Function.comp_apply, lsmul_apply, smul_eq_mul, hσ₁]
    rw [mul_left_comm, Complex.inner_mul_mul_of_norm_eq_one (he t)]
  · ext z
    simp only [coe_comp, Function.comp_apply, lsmul_apply, smul_eq_mul]
    rw [hseam₁, hC, mul_assoc, mul_comm z, ← mul_assoc, ← Complex.exp_add]
    have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd
    congr 3
    push_cast
    field_simp
    ring

end FrameExistence

section Plane

/-! ### Orbit tori of surface maps

For a two-dimensional fibre the unitary frame exists, so the kernels of the twisted normal
operators are determined by the return map alone. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {K : ℝ → V →L[ℝ] V} {σ : V →L[ℝ] V →L[ℝ] ℝ} {P : V →L[ℝ] V} {ℓ d ε₁ ε₂ : ℝ}

/-- **Kernels of the twisted normal operators of an orbit torus of a surface map.** Let `V` be a
real plane with a `C²` path of complex structures `K(t)` preserving an antisymmetric form `σ`,
which tames `K(0)`, and let the return map `P` preserve `σ` and satisfy the seam identity
`P K(t + d) = K(t) P`, with `d > 0`. On the cover with deck group spanned by `(k ℓ, 0)` and
`(a ℓ, n d)`, `k, n ≥ 1`, the vertical operator `∂s + K(t) ∂t` twisted by `ε₁` along `(k ℓ, 0)`,
and by `ε₂` along `(a ℓ, n d)` through `P`, has a nonzero `C²` kernel element exactly when
`ε₁ = 1` and `det (ε₂ - P ^ n) = 0`. -/
theorem exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two
    (hV : Module.finrank ℝ V = 2) (hK2 : ContDiff ℝ 2 K) (hKsq : ∀ t x, K t (K t x) = -x)
    (hσ : ∀ x y, σ x y = -σ y x) (hσK : ∀ t x y, σ (K t x) (K t y) = σ x y)
    (htame : ∀ x, x ≠ 0 → 0 < σ x (K 0 x)) (hPσ : ∀ x y, σ (P x) (P y) = σ x y)
    (hPK : ∀ t, P ∘L K (t + d) = K t ∘L P) (hℓ : 0 < ℓ) (hd : 0 < d) (hε₁ : ε₁ ^ 2 = 1)
    (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    (∃ v : ℝ × ℝ → V, ContDiff ℝ 2 v ∧ v ≠ 0 ∧ (∀ s t, v (s + k * ℓ, t) = ε₁ • v (s, t)) ∧
      (∀ s t, (P ^ n) (v (s + a * ℓ, t + n * d)) = ε₂ • v (s, t)) ∧
      ∀ z, orbitTorusVerticalOperator K v z = 0) ↔
      ε₁ = 1 ∧ LinearMap.det ((ε₂ • 1 - P ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V) = 0 := by
  obtain ⟨Φ, hΦ2, hΦ, hKΦ, hσΦ, hseam⟩ :=
    exists_unitary_frame_of_finrank_eq_two hV hK2 hKsq hσ hσK htame hd.ne' hPσ hPK
  exact exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_eq_one_and_det_eq_zero hℓ hd
    (fun x y => by simpa using Complex.real_inner_I_mul_left x y) (fun x => by simp) hΦ2 hΦ hKΦ
    hσΦ hseam hε₁ hε₂ hk hn a

/-- **Nondegeneracy of the orbit tori of a surface map through twice the period.** Under the
hypotheses of `exists_ne_zero_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two`, the
vertical operators twisted by all four real sign characters of the cover with deck group spanned
by `(k ℓ, 0)` and `(a ℓ, n d)` have no nonzero `C²` kernel element exactly when
`det (1 - P ^ (2 n)) ≠ 0`. -/
theorem forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two
    (hV : Module.finrank ℝ V = 2) (hK2 : ContDiff ℝ 2 K) (hKsq : ∀ t x, K t (K t x) = -x)
    (hσ : ∀ x y, σ x y = -σ y x) (hσK : ∀ t x y, σ (K t x) (K t y) = σ x y)
    (htame : ∀ x, x ≠ 0 → 0 < σ x (K 0 x)) (hPσ : ∀ x y, σ (P x) (P y) = σ x y)
    (hPK : ∀ t, P ∘L K (t + d) = K t ∘L P) (hℓ : 0 < ℓ) (hd : 0 < d) {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) (a : ℤ) :
    (∀ ε₁ ε₂ : ℝ, ε₁ ^ 2 = 1 → ε₂ ^ 2 = 1 → ∀ v : ℝ × ℝ → V, ContDiff ℝ 2 v →
      (∀ s t, v (s + k * ℓ, t) = ε₁ • v (s, t)) →
      (∀ s t, (P ^ n) (v (s + a * ℓ, t + n * d)) = ε₂ • v (s, t)) →
      (∀ z, orbitTorusVerticalOperator K v z = 0) → v = 0) ↔
      LinearMap.det ((1 - P ^ (2 * n) : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0 := by
  obtain ⟨Φ, hΦ2, hΦ, hKΦ, hσΦ, hseam⟩ :=
    exists_unitary_frame_of_finrank_eq_two hV hK2 hKsq hσ hσK htame hd.ne' hPσ hPK
  exact forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_det_ne_zero hℓ hd
    (fun x y => by simpa using Complex.real_inner_I_mul_left x y) (fun x => by simp) hΦ2 hΦ hKΦ
    hσΦ hseam hk hn a

end Plane

end TauCeti
