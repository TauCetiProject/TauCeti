/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Topology.Instances.Sign
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Analysis.Calculus.Bifurcation
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.Deriv.Parity
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Pitchfork bifurcations of the zeros of an odd family of maps

Let `f s : E → E` be a one-parameter family of maps of a finite-dimensional real normed space,
jointly `C³` near `(t, 0)` and odd near `(t, 0)`, `f s (-x) = -f s x`. Then `0` is a zero of
`f s` for every `s` near `t`, the *trivial zero*. Suppose that it degenerates at `s = t`: the
kernel of `D = D(f t)₀` is the line through `v`, and `φ` is a functional vanishing on the range of
`D`, so that `φ` spans the cokernel. Since `f t` is odd, `D²(f t)₀ = 0`, and the point `(t, 0)` is a
*pitchfork point* when

`κ = φ (D³(f t)₀ (v, v, v)) · φ (∂ₛ D(f s)₀ v) ≠ 0`.

The second factor is the transversality of the family, the first the nondegeneracy of the
pitchfork; the sign of `κ` depends neither on `v` nor on `φ`. This file proves that near a
pitchfork point a single orbit `{x₀, -x₀}` of the symmetry `x ↦ -x` is born or dies
(`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_pitchfork`): there are a sign `ε ≠ 0` and a
neighbourhood `U` of `0` such that for `s` near `t`

* the trivial zero has Jacobian sign `sign det D(f s)₀ = ε · sign (κ (s - t))`, so it is
  nondegenerate for `s ≠ t` and changes sign at `s = t`;
* if `κ (s - t) ≥ 0`, then `0` is the only zero of `f s` in `U`;
* if `κ (s - t) < 0`, then the zeros of `f s` in `U` are exactly `0`, `x₀` and `-x₀` for some
  `x₀ ≠ 0`, and both `x₀` and `-x₀` have Jacobian sign `ε`.

So the signed count of all zeros in `U` is `ε` on both sides of `t`, while the signed count of
the orbits, in which `{x₀, -x₀}` counts once, changes by `ε`
(`TauCeti.exists_mem_nhds_finsum_sign_det_fderiv_eq_pitchfork`).

This is meant as the finite-dimensional model of the period doubling of a torus in Taubes's count
of pseudoholomorphic curves. There the deformation problem of the doubly covered torus is
expected to reduce to such an odd family, odd under the deck transformation of the double cover,
with the trivial zero the doubly covered torus and the orbit `{x₀, -x₀}` a single embedded torus
in twice its class; the change of the orbit count would then be what Taubes's four-twist weights
of the tori account for. Nothing in this file proves that reduction. The one-dimensional case is
`TauCeti.eventually_pitchfork`;
the fold point, where a pair of zeros of opposite signs is born, is
`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_eq_pair`.

The proof is a Lyapunov–Schmidt reduction to `TauCeti.eventually_pitchfork`. Choose `ℓ` with
`ℓ v = 1` and `c` with `φ c = 1`. The map `Φ (s, x) = (s, f s x - φ (f s x) • c + ℓ x • c)` has
an invertible derivative at `(t, 0)`, so its local inverse gives a `C³` map `X` with
`ℓ (X s σ) = σ` and `f s (X s σ) = h s σ • c`, where `h s σ = φ (f s (X s σ))`, and every zero
`x` of `f s` near `0` is `X s (ℓ x)`. By uniqueness `X s` is odd, so `h s` is odd and its zeros
are those of a one-dimensional odd family. Differentiating the identities defining `X` gives
`∂σ X(t, 0) = v`, hence `∂σ h (t, 0) = 0`,
`∂σ³ h (t, 0) = φ (D³(f t)₀ (v, v, v))` (since `D²(f t)₀ = 0` and `∂σ² X (t, 0) = 0`), and
`∂ₛ ∂σ h (t, 0) = φ (∂ₛ D(f s)₀ v)`. Finally, with `M = D(f s) - (φ ∘ D(f s)) ⊗ c + ℓ ⊗ c`
the derivative of the chart at `X s σ`, `D(f s) = M ∘ (1 + μ ⊗ ∂σ X)` with
`μ = φ ∘ D(f s) - ℓ`, so the matrix determinant lemma (`LinearMap.transvection.det`) gives

`det D(f s)_{X s σ} = det M · ∂σ h (s, σ)`,

and `det M` has a constant sign near `(t, 0)`. So the Jacobian signs of the zeros of `f s` are
`ε` times the signs of `∂σ h` at the corresponding zeros of `h s`.

## Main results

* `TauCeti.exists_mem_nhds_setOf_apply_eq_zero_pitchfork`: the zeros of an odd family near a
  pitchfork point and their Jacobian signs.
* `TauCeti.exists_mem_nhds_finsum_sign_det_fderiv_eq_pitchfork`: the signed counts of all zeros
  and of the nontrivial zeros near a pitchfork point.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory, Vol. I*,
  Applied Mathematical Sciences 51, Springer, 1985, Chapter VI (bifurcation with `ℤ/2`
  symmetry) and Chapter VII (the Liapunov–Schmidt reduction).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

open Function Module Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E} {t : ℝ}

/-- If the kernel of `D` is the line through `v`, `φ` vanishes on the range of `D`, `ℓ v = 1` and
`φ c = 1`, then `h ↦ D h + ℓ h • c` is injective. -/
private theorem eq_zero_of_apply_add_smul_eq_zero {D : E →L[ℝ] E} {v : E}
    (hker : LinearMap.ker (D : E →ₗ[ℝ] E) = ℝ ∙ v) {φ ℓ : StrongDual ℝ E}
    (hφ : ∀ y, φ (D y) = 0) (hℓ : ℓ v = 1) {c : E} (hc : φ c = 1) {h : E}
    (hz : D h + ℓ h • c = 0) : h = 0 := by
  have hℓh : ℓ h = 0 := by simpa [hφ, hc] using congrArg φ hz
  have hDh : h ∈ LinearMap.ker (D : E →ₗ[ℝ] E) := by simpa [hℓh] using hz
  rw [hker, Submodule.mem_span_singleton] at hDh
  obtain ⟨r, rfl⟩ := hDh
  simp_all

omit [NormedSpace ℝ E] in
/-- If `uncurry X` is continuous at `(t, 0)` and `X t 0 = 0`, then `(s, σ) ↦ (s, X s σ)` tends to
`(t, 0)` at `(t, 0)`. -/
private theorem tendsto_prodMk_reduction {X : ℝ → ℝ → E} (hX : ContinuousAt (uncurry X) (t, 0))
    (hX0 : X t 0 = 0) :
    Tendsto (fun p : ℝ × ℝ ↦ (p.1, X p.1 p.2)) (𝓝 (t, 0)) (𝓝 (t, 0)) := by
  have h : Tendsto (fun p : ℝ × ℝ ↦ (p.1, X p.1 p.2)) (𝓝 (t, 0)) (𝓝 (t, X t 0)) :=
    (continuousAt_fst.prodMk hX).tendsto
  rwa [hX0] at h

/-- **The derivative of the reduction.** In the setting of `exists_reduction`, near `(t, 0)` the
function `σ ↦ φ (f s (X s σ))` has derivative `φ (D(f s) u)` at `σ`, where `u` is the derivative
of `X s` at `σ`; moreover `D(f s) u = φ (D(f s) u) • c` and `ℓ u = 1`. -/
private theorem eventually_hasDerivAt_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    {X : ℝ → ℝ → E} (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : X t 0 = 0)
    {φ ℓ : StrongDual ℝ E} {c : E}
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2) :
    ∀ᶠ p in 𝓝 (t, (0 : ℝ)),
      HasDerivAt (fun σ ↦ φ (f p.1 (X p.1 σ)))
        (φ (fderiv ℝ (f p.1) (X p.1 p.2) (deriv (X p.1) p.2))) p.2 ∧
      fderiv ℝ (f p.1) (X p.1 p.2) (deriv (X p.1) p.2) =
        φ (fderiv ℝ (f p.1) (X p.1 p.2) (deriv (X p.1) p.2)) • c ∧
      ℓ (deriv (X p.1) p.2) = 1 := by
  have hXt := tendsto_prodMk_reduction hX.continuousAt hX0
  -- The identities hold on a neighbourhood of `σ` in the slice through each nearby point.
  have hslice : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), ∀ᶠ σ in 𝓝 p.2,
      f p.1 (X p.1 σ) = φ (f p.1 (X p.1 σ)) • c ∧ ℓ (X p.1 σ) = σ := by
    filter_upwards [hev.eventually_nhds] with p hp
    exact ((continuous_const.prodMk continuous_id).continuousAt (x := p.2)).tendsto.eventually hp
  filter_upwards [hXt.eventually (hf.eventually (by simp)), hX.eventually (by simp), hslice]
    with p hfp hXp hsl
  -- `X s` and `f s` are slices of the jointly differentiable `uncurry X` and `uncurry f`.
  have hXd : HasDerivAt (X p.1) (deriv (X p.1) p.2) p.2 :=
    (hXp.uncurry_left.differentiableAt (by norm_num)).hasDerivAt
  have hfd : HasFDerivAt (f p.1) (fderiv ℝ (f p.1) (X p.1 p.2)) (X p.1 p.2) :=
    (hfp.uncurry_left.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := hfd.comp_hasDerivAt p.2 hXd
  have hh := φ.hasFDerivAt.comp_hasDerivAt p.2 hcomp
  refine ⟨hh, hcomp.unique ((hh.smul_const c).congr_of_eventuallyEq
    (hsl.mono fun σ hσ ↦ hσ.1)), ?_⟩
  exact (ℓ.hasFDerivAt.comp_hasDerivAt p.2 hXd).unique
    ((hasDerivAt_id p.2).congr_of_eventuallyEq (hsl.mono fun σ hσ ↦ hσ.2))

/-- At `(t, 0)` the reduction has velocity `v` in `σ`, and `σ ↦ φ (f t (X t σ))` has derivative
`0` at `0`. -/
private theorem deriv_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0)) {X : ℝ → ℝ → E}
    (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : X t 0 = 0) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ ℓ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) (hℓ : ℓ v = 1) {c : E}
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2) :
    deriv (X t) 0 = v ∧ HasDerivAt (fun σ ↦ φ (f t (X t σ))) 0 0 := by
  obtain ⟨hh, hD, hℓu⟩ := (eventually_hasDerivAt_reduction hf hX hX0 hev).self_of_nhds
  simp only [hX0, hφ, zero_smul] at hh hD hℓu
  refine ⟨?_, hh⟩
  have hu : deriv (X t) 0 ∈ LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) := LinearMap.mem_ker.2 hD
  rw [hker, Submodule.mem_span_singleton] at hu
  obtain ⟨r, hr⟩ := hu
  rw [← hr, map_smul, hℓ, smul_eq_mul, mul_one] at hℓu
  rw [← hr, hℓu, one_smul]

/-- **The transversality coefficient of the reduction.** The derivative in `s` at `t` of the
`σ`-derivative at `0` of `φ (f s (X s σ))` is `φ (∂ₛ D(f s)₀ v)`. -/
private theorem deriv_deriv_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0)) {X : ℝ → ℝ → E}
    (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : ∀ᶠ s in 𝓝 t, X s 0 = 0) {v : E}
    (hv : deriv (X t) 0 = v) {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) :
    deriv (fun s ↦ deriv (fun σ ↦ φ (f s (X s σ))) 0) t =
      φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) := by
  set A : ℝ → E →L[ℝ] E := fun s ↦ fderiv ℝ (f s) 0
  have hA : ContDiffAt ℝ 2 A t :=
    ContDiffAt.fderiv (g := fun _ ↦ (0 : E)) hf contDiffAt_const (by norm_num)
  -- `deriv (X s) 0 = fderiv ℝ (X s) 0 1` by definition of `deriv`.
  have hu : ContDiffAt ℝ 2 (fun s ↦ deriv (X s) 0) t :=
    (ContDiffAt.fderiv (g := fun _ ↦ (0 : ℝ)) hX contDiffAt_const (by norm_num)).clm_apply
      contDiffAt_const
  have hA' : HasDerivAt A (deriv A t) t := (hA.differentiableAt (by norm_num)).hasDerivAt
  have hu' := (hu.differentiableAt (by norm_num)).hasDerivAt
  have hslice : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 3 (uncurry f) (s, 0) ∧ ContDiffAt ℝ 3 (uncurry X) (s, 0)
      ∧ X s 0 = 0 := by
    have hτ : Tendsto (fun s : ℝ ↦ (s, (0 : ℝ))) (𝓝 t) (𝓝 (t, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    have hτ' : Tendsto (fun s : ℝ ↦ (s, (0 : E))) (𝓝 t) (𝓝 (t, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [hτ'.eventually (hf.eventually (by simp)),
      hτ.eventually (hX.eventually (by simp)), hX0] with s h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
  have heq : (fun s ↦ deriv (fun σ ↦ φ (f s (X s σ))) 0) =ᶠ[𝓝 t]
      fun s ↦ φ (A s (deriv (X s) 0)) := by
    filter_upwards [hslice] with s ⟨hfs, hXs, hXs0⟩
    have hXd : HasDerivAt (X s) (deriv (X s) 0) 0 :=
      (hXs.uncurry_left.differentiableAt (by norm_num)).hasDerivAt
    have hfd : HasFDerivAt (f s) (A s) (X s 0) := by
      rw [hXs0]
      exact (hfs.uncurry_left.differentiableAt (by norm_num)).hasFDerivAt
    exact (φ.hasFDerivAt.comp_hasDerivAt 0 (hfd.comp_hasDerivAt 0 hXd)).deriv
  have hR : deriv (fun r ↦ fderiv ℝ (f r) 0 v) t = deriv A t v := by
    simpa using (hA'.clm_apply (hasDerivAt_const t v)).deriv
  rw [heq.deriv_eq, hR]
  exact (φ.hasFDerivAt.comp_hasDerivAt t (hA'.clm_apply hu')).deriv.trans (by simp [A, hv, hφ])

/-- The function `(s, σ) ↦ φ (f s (X s σ))` is `C³` at `(t, 0)`. -/
private theorem contDiffAt_apply_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    {X : ℝ → ℝ → E} (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : X t 0 = 0)
    (φ : StrongDual ℝ E) :
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ ↦ φ (f q.1 (X q.1 q.2))) (t, 0) := by
  have h₁ : ContDiffAt ℝ 3 (uncurry f) (t, uncurry X (t, 0)) := by simpa [hX0] using hf
  exact ContDiffAt.comp (g := φ) (t, (0 : ℝ)) φ.contDiff.contDiffAt
    (ContDiffAt.comp (g := uncurry f) (f := fun q : ℝ × ℝ ↦ (q.1, uncurry X q))
      (t, (0 : ℝ)) h₁ (contDiffAt_fst.prodMk hX))

/-- **The one-dimensional pitchfork of the reduction.** In the setting of `exists_reduction`, with
cubic coefficient `0 < φ (D³(f t)₀ (v, v, v))` and transversality coefficient
`β = φ (∂ₛ D(f s)₀ v) ≠ 0`, the scalar family `σ ↦ φ (f s (X s σ))` has the zeros and derivative
signs of `TauCeti.eventually_pitchfork` near `σ = 0`, for `s` near `t`. -/
private theorem eventually_pitchfork_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    (hodd : ∀ᶠ p in 𝓝 (t, (0 : E)), f p.1 (-p.2) = -f p.1 p.2) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ ℓ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) (hℓ : ℓ v = 1)
    (hγ : 0 < φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v))
    (hβ : φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) ≠ 0) {c : E} {X : ℝ → ℝ → E}
    (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : X t 0 = 0)
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2 ∧ X p.1 (-p.2) = -X p.1 p.2) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 t,
      (0 ≤ φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) →
        {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0} = {0}) ∧
      (0 < φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) →
        0 < deriv (fun σ ↦ φ (f s (X s σ))) 0) ∧
      (φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) < 0 →
        deriv (fun σ ↦ φ (f s (X s σ))) 0 < 0 ∧ ∃ σ₀ ∈ Ioo 0 δ,
          {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0} = {-σ₀, 0, σ₀} ∧
          0 < deriv (fun σ ↦ φ (f s (X s σ))) σ₀ ∧
          deriv (fun σ ↦ φ (f s (X s σ))) (-σ₀) = deriv (fun σ ↦ φ (f s (X s σ))) σ₀) := by
  -- A real vector space has no additive torsion.
  have : HasUniqueDiv E := .of_isTorsionFree ℝ E
  have hev' : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2 := hev.mono fun p hp ↦ ⟨hp.1, hp.2.1⟩
  obtain ⟨hv, hh0⟩ := deriv_reduction hf hX hX0 hker hφ hℓ hev'
  have hXt := tendsto_prodMk_reduction hX.continuousAt hX0
  -- The reduced function `F (σ, r) = φ (f (t + r) (X (t + r) σ))` of the one-variable pitchfork.
  set F : ℝ × ℝ → ℝ := fun p ↦ φ (f (t + p.2) (X (t + p.2) p.1))
  have hsm : ContDiff ℝ 3 fun p : ℝ × ℝ ↦ (t + p.2, p.1) := by fun_prop
  have hFC : ContDiffAt ℝ 3 F 0 := by
    have h : ContDiffAt ℝ 3 (fun q : ℝ × ℝ ↦ φ (f q.1 (X q.1 q.2)))
        (t + (0 : ℝ × ℝ).2, (0 : ℝ × ℝ).1) := by
      simpa using contDiffAt_apply_reduction hf hX hX0 φ
    exact ContDiffAt.comp (g := fun q : ℝ × ℝ ↦ φ (f q.1 (X q.1 q.2)))
      (f := fun p : ℝ × ℝ ↦ (t + p.2, p.1)) (0 : ℝ × ℝ) h hsm.contDiffAt
  have hoddF : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), F (-p.1, p.2) = -F p := by
    have hshift : Tendsto (fun p : ℝ × ℝ ↦ (t + p.2, p.1)) (𝓝 0) (𝓝 (t, 0)) := by
      simpa using hsm.continuous.tendsto (0 : ℝ × ℝ)
    have hq : ∀ᶠ q in 𝓝 (t, (0 : ℝ)), φ (f q.1 (X q.1 (-q.2))) = -φ (f q.1 (X q.1 q.2)) := by
      filter_upwards [hev, hXt.eventually hodd] with q hq hq'
      rw [hq.2.2, hq', map_neg]
    exact hshift.eventually hq
  have hgodd : ∀ᶠ σ in 𝓝 (0 : ℝ), X t (-σ) = -X t σ :=
    ((continuous_const.prodMk continuous_id).tendsto 0).eventually (hev.mono fun q hq ↦ hq.2.2)
  have h₃ : iteratedDeriv 3 (fun x ↦ F (x, 0)) 0 =
      φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) := by
    simpa [F] using iteratedDeriv_three_comp_of_eventually_odd (g := f t) (f := X t)
      hf.uncurry_left hX.uncurry_left hX0 hv hgodd hφ
  have hXs0 : ∀ᶠ s in 𝓝 t, X s 0 = 0 :=
    eventually_apply_zero_eq_zero_of_eventually_odd (hev.mono fun _ hq ↦ hq.2.2)
  have hb : deriv (fun s ↦ deriv (fun x ↦ F (x, s)) 0) 0 =
      φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) := by
    simp only [F]
    rw [deriv_comp_const_add (fun r ↦ deriv (fun x ↦ φ (f r (X r x))) 0) t 0, add_zero]
    exact deriv_deriv_reduction hf hX hXs0 hv hφ
  have hP := eventually_pitchfork hFC hoddF (by simpa [F] using hh0.deriv) (h₃ ▸ hγ) (hb ▸ hβ)
  rw [hb] at hP
  -- Pass from the shifted parameter `r = s - t` back to `s`.
  filter_upwards [hP] with δ hδ
  filter_upwards [(tendsto_sub_nhds_zero_iff.2 tendsto_id).eventually hδ] with s hs
  simpa only [F, id, add_sub_cancel] using hs

/-- **The zeros near `0` are the points of the reduction.** In the setting of `exists_reduction`,
there is `η > 0` such that for every `0 < δ < η` some neighbourhood `U` of `0` meets the zeros of
`f s`, for `|s - t| < η`, exactly in the points `X s σ` with `|σ| < δ` and `φ (f s (X s σ)) = 0`.
-/
private theorem exists_pos_forall_setOf_apply_eq_zero_eq_image {X : ℝ → ℝ → E}
    (hX : ContinuousAt (uncurry X) (t, 0)) (hX0 : X t 0 = 0) {φ ℓ : StrongDual ℝ E} {c : E}
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2)
    {N : Set (ℝ × E)} (hN : N ∈ 𝓝 (t, (0 : E)))
    (hNX : ∀ z ∈ N, f z.1 z.2 = 0 → X z.1 (ℓ z.2) = z.2) :
    ∃ η > 0, ∀ δ ∈ Ioo 0 η, ∃ U ∈ 𝓝 (0 : E), ∀ s, dist s t < η →
      {x ∈ U | f s x = 0} = X s '' {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0} := by
  obtain ⟨η₁, hη₁, hη₁N⟩ := Metric.mem_nhds_iff.1 hN
  have hXb : ∀ᶠ q in 𝓝 (t, (0 : ℝ)), X q.1 q.2 ∈ Metric.ball (0 : E) η₁ := by
    have h := hX.tendsto
    rw [uncurry_apply_pair, hX0] at h
    simpa only [uncurry_def] using h.eventually_mem (Metric.ball_mem_nhds 0 hη₁)
  obtain ⟨η₂, hη₂, hη₂G⟩ := Metric.mem_nhds_iff.1 (hev.and hXb)
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun δ hδ ↦ ?_⟩
  refine ⟨Metric.ball 0 η₁ ∩ {x | |ℓ x| < δ}, inter_mem (Metric.ball_mem_nhds 0 hη₁)
    ((isOpen_lt (continuous_abs.comp ℓ.continuous) continuous_const).mem_nhds
      (by simp [hδ.1])), fun s hs ↦ ?_⟩
  ext x
  constructor
  · -- A zero `x` of `f s` near `0` is `X s (ℓ x)`.
    rintro ⟨⟨hxb, hxℓ⟩, hx0⟩
    have hxN : (s, x) ∈ N :=
      hη₁N ((ball_prod_same t (0 : E) η₁).subset ⟨hs.trans_le (min_le_left _ _), hxb⟩)
    have hXx : X s (ℓ x) = x := hNX (s, x) hxN hx0
    refine ⟨ℓ x, ⟨abs_lt.1 hxℓ, ?_⟩, hXx⟩
    rw [hXx, hx0, map_zero]
  · -- Conversely `f s (X s σ) = φ (f s (X s σ)) • c` vanishes with `φ (f s (X s σ))`.
    rintro ⟨σ, ⟨hσ, hσ0⟩, rfl⟩
    obtain ⟨⟨hfX, hℓX⟩, hXb'⟩ := hη₂G ((ball_prod_same t (0 : ℝ) η₂).subset
      (mk_mem_prod (Metric.mem_ball.2 (hs.trans_le (min_le_right _ _))) (Metric.mem_ball.2
        ((Real.dist_0_eq_abs σ).trans_lt
          ((abs_lt.2 hσ).trans (hδ.2.trans_le (min_le_right _ _)))))))
    exact ⟨⟨hXb', by simpa [hℓX] using abs_lt.2 hσ⟩, by rw [hfX, hσ0, zero_smul]⟩

/-- **Assembling the pitchfork.** If the scalar family `σ ↦ φ (f s (X s σ))` has the zeros and
derivative signs of the one-dimensional pitchfork with coefficient `β`, its derivative gives the
Jacobian signs of `f s` along `X s` up to `ε`, and the zeros of `f s` near `0` are the points
`X s σ` with `φ (f s (X s σ)) = 0`, then the zeros of `f s` near `0` and their signs are those of
`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_pitchfork`, with `β (s - t)` in place of
`κ (s - t)`. -/
private theorem exists_mem_nhds_of_reduction {X : ℝ → ℝ → E} {φ ℓ : StrongDual ℝ E} {β : ℝ}
    {ε : SignType} (hβ : β ≠ 0)
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), (ℓ (X p.1 p.2) = p.2 ∧ X p.1 (-p.2) = -X p.1 p.2) ∧
      SignType.sign (LinearMap.det (fderiv ℝ (f p.1) (X p.1 p.2) : E →ₗ[ℝ] E)) =
        ε * SignType.sign (deriv (fun σ ↦ φ (f p.1 (X p.1 σ))) p.2))
    (hh0 : deriv (fun σ ↦ φ (f t (X t σ))) 0 = 0)
    (hZ : ∃ η > 0, ∀ δ ∈ Ioo 0 η, ∃ U ∈ 𝓝 (0 : E), ∀ s, dist s t < η →
      {x ∈ U | f s x = 0} = X s '' {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0})
    (hP : ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 t,
      (0 ≤ β * (s - t) → {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0} = {0}) ∧
      (0 < β * (s - t) → 0 < deriv (fun σ ↦ φ (f s (X s σ))) 0) ∧
      (β * (s - t) < 0 → deriv (fun σ ↦ φ (f s (X s σ))) 0 < 0 ∧ ∃ σ₀ ∈ Ioo 0 δ,
        {σ ∈ Ioo (-δ) δ | φ (f s (X s σ)) = 0} = {-σ₀, 0, σ₀} ∧
        0 < deriv (fun σ ↦ φ (f s (X s σ))) σ₀ ∧
        deriv (fun σ ↦ φ (f s (X s σ))) (-σ₀) = deriv (fun σ ↦ φ (f s (X s σ))) σ₀)) :
    ∃ U ∈ 𝓝 (0 : E), ∀ᶠ s in 𝓝 t,
      SignType.sign (LinearMap.det (fderiv ℝ (f s) 0 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (β * (s - t)) ∧
      (0 ≤ β * (s - t) → {x ∈ U | f s x = 0} = {0}) ∧
      (β * (s - t) < 0 → ∃ x₀, x₀ ≠ 0 ∧ {x ∈ U | f s x = 0} = {0, x₀, -x₀} ∧
        SignType.sign (LinearMap.det (fderiv ℝ (f s) x₀ : E →ₗ[ℝ] E)) = ε ∧
        SignType.sign (LinearMap.det (fderiv ℝ (f s) (-x₀) : E →ₗ[ℝ] E)) = ε) := by
  -- A real vector space has no additive torsion.
  have : HasUniqueDiv E := .of_isTorsionFree ℝ E
  obtain ⟨η₁, hη₁, hZ⟩ := hZ
  obtain ⟨η₂, hη₂, hη₂G⟩ := Metric.mem_nhds_iff.1 hev
  set η := min η₁ η₂
  have hgood {s σ : ℝ} (hs : dist s t < η) (hσ : |σ| < η) :=
    hη₂G ((ball_prod_same t (0 : ℝ) η₂).subset
      (mk_mem_prod (Metric.mem_ball.2 (hs.trans_le (min_le_right _ _)))
        (Metric.mem_ball.2 ((Real.dist_0_eq_abs σ).trans_lt (hσ.trans_le (min_le_right _ _))))))
  obtain ⟨δ, hδP, hδ⟩ := (hP.and (Ioo_mem_nhdsGT (lt_min hη₁ hη₂))).exists
  obtain ⟨U, hU, hUZ⟩ := hZ δ ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
  refine ⟨U, hU, ?_⟩
  filter_upwards [hδP, Metric.ball_mem_nhds t (lt_min hη₁ hη₂),
    eventually_apply_zero_eq_zero_of_eventually_odd (hev.mono fun _ hq ↦ hq.1.2)]
    with s hQ hs hXs
  have hs' : dist s t < η := Metric.mem_ball.1 hs
  have hη0 : |(0 : ℝ)| < η := by rw [abs_zero]; exact lt_min hη₁ hη₂
  rw [hUZ s (lt_of_lt_of_le hs' (min_le_left _ _))]
  refine ⟨?_, fun hle ↦ by rw [hQ.1 hle, image_singleton, hXs], fun hlt ↦ ?_⟩
  · -- The trivial zero has the sign of `∂σ φ (f s (X s σ))` at `0`, which is that of `β (s - t)`.
    rw [← hXs, (hgood hs' hη0).2]
    congr 1
    rcases lt_trichotomy (β * (s - t)) 0 with hn | hz | hp
    · rw [sign_neg hn, sign_neg (hQ.2.2 hn).1]
    · obtain rfl : s = t := by
        rcases mul_eq_zero.1 hz with h | h
        · exact absurd h hβ
        · linarith
      rw [hz, sign_zero, hh0, sign_zero]
    · rw [sign_pos hp, sign_pos (hQ.2.1 hp)]
  · -- The nontrivial zeros `±X s σ₀` both carry the sign `ε`.
    obtain ⟨-, σ₀, hσ₀, hset, hpos, hdeq⟩ := hQ.2.2 hlt
    have hσ₀η : |σ₀| < η := by
      rw [abs_of_pos hσ₀.1]
      exact lt_trans hσ₀.2 hδ.2
    have hg := hgood hs' hσ₀η
    have hg' := hgood hs' (by rwa [abs_neg])
    refine ⟨X s σ₀, fun h0 ↦ hσ₀.1.ne (by simpa [h0] using hg.1.1), ?_, ?_, ?_⟩
    · rw [hset, image_insert_eq, image_insert_eq, image_singleton, hXs, hg.1.2]
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    · rw [hg.2, sign_pos hpos, mul_one]
    · rw [← hg.1.2, hg'.2, hdeq, sign_pos hpos, mul_one]

variable [FiniteDimensional ℝ E]

/-- **The Lyapunov–Schmidt chart.** In the setting of `exists_reduction`, the map
`Φ (s, x) = (s, f s x - φ (f s x) • c + ℓ x • c)` has a `C³` local inverse `ψ` at `(t, 0)`: it
fixes `(t, 0)`, preserves the parameter, and inverts `Φ` on both sides near `(t, 0)`. -/
private theorem exists_chart_inverse (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0)) (h0 : f t 0 = 0)
    {v : E} (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v)
    {φ ℓ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) (hℓ : ℓ v = 1) {c : E}
    (hc : φ c = 1) :
    ∃ ψ : ℝ × E → ℝ × E, ContDiffAt ℝ 3 ψ (t, 0) ∧ ψ (t, 0) = (t, 0) ∧
      (∀ᶠ y in 𝓝 (t, (0 : E)), (ψ y).1 = y.1 ∧
        f y.1 (ψ y).2 - φ (f y.1 (ψ y).2) • c + ℓ (ψ y).2 • c = y.2) ∧
      ∃ S ∈ 𝓝 (t, (0 : E)), ∀ z ∈ S,
        ψ (z.1, f z.1 z.2 - φ (f z.1 z.2) • c + ℓ z.2 • c) = z := by
  have hfd : DifferentiableAt ℝ (uncurry f) (t, 0) := hf.differentiableAt (by norm_num)
  set Φ : ℝ × E → ℝ × E := fun p ↦ (p.1, uncurry f p - φ (uncurry f p) • c + ℓ p.2 • c)
  have hΦ : ContDiffAt ℝ 3 Φ (t, 0) := contDiffAt_fst.prodMk
    ((hf.sub ((φ.contDiff.contDiffAt.comp _ hf).smul contDiffAt_const)).add
      ((ℓ.contDiff.contDiffAt.comp _ contDiffAt_snd).smul contDiffAt_const))
  set Df := fderiv ℝ (uncurry f) (t, 0)
  set L : ℝ × E →L[ℝ] ℝ × E := (ContinuousLinearMap.fst ℝ ℝ E).prod
    (Df - (φ.comp Df).smulRight c + (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E)).smulRight c)
  have hL : HasFDerivAt Φ L (t, 0) := hasFDerivAt_fst.prodMk
    ((hfd.hasFDerivAt.sub ((φ.hasFDerivAt.comp _ hfd.hasFDerivAt).smul_const c)).add
      ((ℓ.hasFDerivAt.comp _ hasFDerivAt_snd).smul_const c))
  -- The derivative `(a, h) ↦ (a, a ∂ₛf + D h - φ (a ∂ₛf + D h) • c + ℓ h • c)` is injective.
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero _).2 fun ⟨a, h⟩ hz ↦ ?_
    simp only [L, ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hz
    obtain ⟨rfl, hz⟩ := hz
    simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', Df,
      fderiv_uncurry_apply hfd, zero_smul, zero_add, hφ, sub_zero] at hz
    simpa using eq_zero_of_apply_add_smul_eq_zero hker hφ hℓ hc hz
  set e : (ℝ × E) ≃L[ℝ] ℝ × E :=
    (LinearMap.linearEquivOfInjective L.toLinearMap hinj rfl).toContinuousLinearEquiv
  have he : (e : ℝ × E →L[ℝ] ℝ × E) = L := by
    ext x <;> simp [e]
  have hΦ' : HasFDerivAt Φ (e : ℝ × E →L[ℝ] ℝ × E) (t, 0) := hL.congr_fderiv he.symm
  set P := hΦ.toOpenPartialHomeomorph Φ hΦ' (by norm_num)
  have hΦ0 : Φ (t, 0) = (t, 0) := by simp [Φ, h0]
  have hsrc : (t, (0 : E)) ∈ P.source :=
    hΦ.mem_toOpenPartialHomeomorph_source hΦ' (by norm_num)
  have htgt : (t, (0 : E)) ∈ P.target :=
    hΦ0 ▸ hΦ.image_mem_toOpenPartialHomeomorph_target hΦ' (by norm_num)
  refine ⟨P.symm, hΦ0 ▸ hΦ.to_localInverse hΦ' (by norm_num),
    by
      have h := P.left_inv hsrc
      rwa [hΦ.toOpenPartialHomeomorph_coe, hΦ0] at h, ?_, P.source, P.open_source.mem_nhds hsrc,
    fun z hz ↦ P.left_inv hz⟩
  filter_upwards [P.open_target.mem_nhds htgt] with y hy
  have h := P.right_inv hy
  rw [hΦ.toOpenPartialHomeomorph_coe] at h
  have h1 : (P.symm y).1 = y.1 := by simpa [Φ] using congrArg Prod.fst h
  refine ⟨h1, ?_⟩
  have h2 := congrArg Prod.snd h
  simp only [Φ, uncurry_def] at h2
  rwa [h1] at h2

/-- **The Lyapunov–Schmidt reduction of an odd family.** Let `f s` be a family of maps of a
finite-dimensional space, jointly `C³` near `(t, 0)` and odd near `(t, 0)`, let the kernel of
`D = D(f t)₀` be the line through `v`, and let `φ` vanish on the range of `D`. For `ℓ v = 1` and
`φ c = 1` there is a jointly `C³` map `X` with `X t 0 = 0` such that, near `(t, 0)`, `X s σ` is
the point with `ℓ (X s σ) = σ` at which `f s` takes a value on the line through `c`, `X s` is odd,
and every zero `x` of `f s` near `0` is `X s (ℓ x)`. -/
private theorem exists_reduction (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    (hodd : ∀ᶠ p in 𝓝 (t, (0 : E)), f p.1 (-p.2) = -f p.1 p.2) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v)
    {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) {ℓ : StrongDual ℝ E}
    (hℓ : ℓ v = 1) {c : E} (hc : φ c = 1) :
    ∃ X : ℝ → ℝ → E, ContDiffAt ℝ 3 (uncurry X) (t, 0) ∧ X t 0 = 0 ∧
      (∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
        ℓ (X p.1 p.2) = p.2 ∧ X p.1 (-p.2) = -X p.1 p.2) ∧
      ∃ N ∈ 𝓝 (t, (0 : E)), ∀ z ∈ N, f z.1 z.2 = 0 → X z.1 (ℓ z.2) = z.2 := by
  -- A real vector space has no additive torsion.
  have : HasUniqueDiv E := .of_isTorsionFree ℝ E
  obtain ⟨ψ, hψ, hψ0, hright, S, hS, hleft⟩ :=
    exists_chart_inverse hf (eventually_apply_zero_eq_zero_of_eventually_odd hodd).self_of_nhds
      hker hφ hℓ hc
  -- The reduced map `X s σ`, the space component of `ψ (s, σ • c)`.
  set y : ℝ × ℝ → ℝ × E := fun p ↦ (p.1, p.2 • c)
  have hy : ContDiff ℝ 3 y := contDiff_fst.prodMk (contDiff_snd.smul contDiff_const)
  have hyt : Tendsto y (𝓝 (t, 0)) (𝓝 (t, 0)) := by simpa [y] using hy.continuous.tendsto (t, 0)
  set X : ℝ → ℝ → E := fun s σ ↦ (ψ (s, σ • c)).2
  have hψ0' : ψ (y (t, 0)) = (t, 0) := by simpa [y] using hψ0
  have hX : ContDiffAt ℝ 3 (uncurry X) (t, 0) :=
    contDiffAt_snd.comp _ ((show ContDiffAt ℝ 3 ψ (y (t, 0)) by simpa [y] using hψ).comp
      (t, (0 : ℝ)) hy.contDiffAt)
  -- Near `(t, 0)`, `ψ (y p) = (p.1, X p.1 p.2)` and the chart sends it back to `y p`.
  have hev₁ : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), ψ (y p) = (p.1, X p.1 p.2) ∧
      f p.1 (X p.1 p.2) - φ (f p.1 (X p.1 p.2)) • c + ℓ (X p.1 p.2) • c = p.2 • c := by
    filter_upwards [hyt.eventually hright] with p hp
    exact ⟨Prod.ext hp.1 rfl, hp.2⟩
  have hX0 : X t 0 = 0 := by simpa [X, y] using congrArg Prod.snd hψ0'
  have hXt := tendsto_prodMk_reduction hX.continuousAt hX0
  have hXt' : Tendsto (fun p : ℝ × ℝ ↦ (p.1, -X p.1 p.2)) (𝓝 (t, 0)) (𝓝 (t, 0)) := by
    simpa [Function.comp_def] using
      (continuous_fst.prodMk continuous_snd.neg).continuousAt.tendsto.comp hXt
  -- Applying `φ` to the chart identity gives `ℓ (X s σ) = σ`, and then `f s (X s σ) ∈ ℝ c`.
  have hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2 := by
    filter_upwards [hev₁] with p hp
    have hℓX : ℓ (X p.1 p.2) = p.2 := by simpa [hc] using congrArg φ hp.2
    refine ⟨?_, hℓX⟩
    have h := hp.2
    rw [hℓX] at h
    exact sub_eq_zero.1 (add_eq_right.1 h)
  refine ⟨X, hX, hX0, ?_, S, hS, fun z hz hz0 ↦ ?_⟩
  · filter_upwards [hev, hev₁, hXt.eventually hodd, hXt'.eventually hS] with p hp hp₁ hodd' hS'
    refine ⟨hp.1, hp.2, ?_⟩
    -- The chart sends `(s, -X s σ)` to `(s, -σ • c)`, so `ψ (s, -σ • c) = (s, -X s σ)`.
    have h := hleft _ hS'
    have hneg : f p.1 (-X p.1 p.2) - φ (f p.1 (-X p.1 p.2)) • c + ℓ (-X p.1 p.2) • c =
        (-p.2) • c := by
      rw [hodd', map_neg, map_neg, neg_smul, neg_smul, neg_smul, ← hp₁.2]
      abel
    rw [hneg] at h
    exact congrArg Prod.snd h
  · have h := hleft z hz
    simp only [hz0, map_zero, zero_smul, sub_zero, zero_add] at h
    exact congrArg Prod.snd h

/-- **The Jacobian sign of the reduction.** Near `(t, 0)`, the sign of `det D(f s)` at `X s σ` is
a fixed nonzero sign times the sign of the `σ`-derivative of `φ (f s (X s σ))`. -/
private theorem exists_eventually_sign_det_fderiv_eq (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    {X : ℝ → ℝ → E} (hX : ContDiffAt ℝ 3 (uncurry X) (t, 0)) (hX0 : X t 0 = 0) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ ℓ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0) (hℓ : ℓ v = 1) {c : E} (hc : φ c = 1)
    (hev : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∀ᶠ p in 𝓝 (t, (0 : ℝ)),
      SignType.sign (LinearMap.det (fderiv ℝ (f p.1) (X p.1 p.2) : E →ₗ[ℝ] E)) =
        ε * SignType.sign (deriv (fun σ ↦ φ (f p.1 (X p.1 σ))) p.2) := by
  -- `M p = D(f s) - (φ ∘ D(f s)) ⊗ c + ℓ ⊗ c` at `X s σ`, the derivative of the chart.
  set A : ℝ × ℝ → E →L[ℝ] E := fun p ↦ fderiv ℝ (f p.1) (X p.1 p.2)
  set M : ℝ × ℝ → E →L[ℝ] E := fun p ↦ (1 - φ.smulRight c) ∘L A p + ℓ.smulRight c
  have hf' : ContDiffAt ℝ 3 (uncurry fun (p : ℝ × ℝ) (x : E) ↦ f p.1 x)
      ((t, (0 : ℝ)), uncurry X (t, 0)) := by
    have h : ContDiffAt ℝ 3 (uncurry f) (t, uncurry X (t, 0)) := by simpa [hX0] using hf
    exact h.comp ((t, (0 : ℝ)), uncurry X (t, 0)) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hAc : ContinuousAt A (t, 0) :=
    (ContDiffAt.fderiv hf' (hX.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).continuousAt
  have hMc : ContinuousAt (fun p ↦ (M p).det) (t, 0) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((continuousAt_const.clm_comp hAc).add continuousAt_const)
  have hM (p : ℝ × ℝ) (x : E) : M p x = A p x - φ (A p x) • c + ℓ x • c := by simp [M]
  -- At `(t, 0)` the chart derivative is injective, so its determinant is nonzero.
  have hM0 : (M (t, 0)).det ≠ 0 := by
    have hinj : Injective (M (t, 0)) := by
      refine (injective_iff_map_eq_zero _).2 fun h hz ↦ ?_
      simp only [hM, A, hX0, hφ, zero_smul, sub_zero] at hz
      exact eq_zero_of_apply_add_smul_eq_zero hker hφ hℓ hc hz
    exact (LinearMap.isUnit_det _ ((LinearMap.isUnit_iff_ker_eq_bot _).2
      (LinearMap.ker_eq_bot.2 hinj))).ne_zero
  have hsgn : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), SignType.sign (M p).det = SignType.sign (M (t, 0)).det :=
    (ContinuousAt.comp (g := SignType.sign) (f := fun p ↦ (M p).det)
      (continuousAt_sign_of_ne_zero hM0) hMc).eventually_mem
      ((isOpen_discrete {SignType.sign (M (t, 0)).det}).mem_nhds rfl)
  refine ⟨SignType.sign (M (t, 0)).det, sign_ne_zero.2 hM0, ?_⟩
  filter_upwards [hsgn, eventually_hasDerivAt_reduction hf hX hX0 hev] with p hp ⟨hh, hD, hℓu⟩
  set u := deriv (X p.1) p.2
  -- `M p u = c`, so `D(f s) = M p ∘ (1 + μ ⊗ u)` with `μ = φ ∘ D(f s) - ℓ`.
  have hMu : M p u = c := by
    rw [hM, hℓu, one_smul, ← hD]
    abel
  set μ : Dual ℝ E := ((φ.comp (A p) - ℓ : StrongDual ℝ E) : E →ₗ[ℝ] ℝ)
  have hfac : (A p : E →ₗ[ℝ] E) = (M p : E →ₗ[ℝ] E) ∘ₗ LinearMap.transvection μ u := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.transvection.apply,
      ContinuousLinearMap.coe_coe, map_add, map_smul, hMu]
    rw [hM]
    simp only [μ, ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.comp_apply,
      sub_smul]
    abel
  -- `set A` does not abstract `fderiv ℝ (f p.1) (X p.1 p.2)` under the coercion to a linear map.
  have hAp : (fderiv ℝ (f p.1) (X p.1 p.2) : E →ₗ[ℝ] E) = (A p : E →ₗ[ℝ] E) := rfl
  rw [hh.deriv, hAp, hfac, LinearMap.det_comp, LinearMap.transvection.det, sign_mul, ← hp]
  congr 2
  simp [μ, A, u, hℓu]

/-- **The pitchfork for a positive cubic coefficient.** This is
`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_pitchfork` under the additional assumption
`0 < φ (D³(f t)₀ (v, v, v))`; the general case applies it to `φ` or `-φ`. -/
private theorem exists_mem_nhds_pitchfork_of_pos (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    (hodd : ∀ᶠ p in 𝓝 (t, (0 : E)), f p.1 (-p.2) = -f p.1 p.2) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0)
    (hγ : 0 < φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v))
    (hβ : φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) ≠ 0) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∃ U ∈ 𝓝 (0 : E), ∀ᶠ s in 𝓝 t,
      SignType.sign (LinearMap.det (fderiv ℝ (f s) 0 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t)) ∧
      (0 ≤ φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) →
        {x ∈ U | f s x = 0} = {0}) ∧
      (φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) < 0 →
        ∃ x₀, x₀ ≠ 0 ∧ {x ∈ U | f s x = 0} = {0, x₀, -x₀} ∧
          SignType.sign (LinearMap.det (fderiv ℝ (f s) x₀ : E →ₗ[ℝ] E)) = ε ∧
          SignType.sign (LinearMap.det (fderiv ℝ (f s) (-x₀) : E →ₗ[ℝ] E)) = ε) := by
  set γ := φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v)
  set β := φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t)
  -- Auxiliary vectors and functionals: `φ c = 1` and `ℓ v = 1`.
  have hv0 : v ≠ 0 := by rintro rfl; simp [γ] at hγ
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra! h
    exact hβ (h _)
  set c : E := (φ w)⁻¹ • w
  have hc : φ c = 1 := by simp [c, hw]
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  -- Reduce to the scalar family `σ ↦ φ (f s (X s σ))`.
  obtain ⟨X, hX, hX0, hev, N, hN, hNX⟩ := exists_reduction hf hodd hker hφ hℓ hc
  have hev' : ∀ᶠ p in 𝓝 (t, (0 : ℝ)), f p.1 (X p.1 p.2) = φ (f p.1 (X p.1 p.2)) • c ∧
      ℓ (X p.1 p.2) = p.2 := hev.mono fun p hp ↦ ⟨hp.1, hp.2.1⟩
  obtain ⟨ε, hε, hsgn⟩ := exists_eventually_sign_det_fderiv_eq hf hX hX0 hker hφ hℓ hc hev'
  obtain ⟨U, hU, hUs⟩ := exists_mem_nhds_of_reduction hβ
    ((hev.and hsgn).mono fun p hp ↦ ⟨⟨hp.1.2.1, hp.1.2.2⟩, hp.2⟩)
    (deriv_reduction hf hX hX0 hker hφ hℓ hev').2.deriv
    (exists_pos_forall_setOf_apply_eq_zero_eq_image hX.continuousAt hX0 hev' hN hNX)
    (eventually_pitchfork_reduction hf hodd hker hφ hℓ hγ hβ hX hX0 hev)
  -- Since `γ > 0`, `γ β (s - t)` has the sign of `β (s - t)`.
  refine ⟨ε, hε, U, hU, hUs.mono fun s hs ↦ ?_⟩
  simp only [mul_assoc γ]
  refine ⟨by rw [sign_mul, sign_pos hγ, one_mul]; exact hs.1, fun hle ↦ hs.2.1 ?_,
    fun hlt ↦ hs.2.2 ?_⟩
  · exact nonneg_of_mul_nonneg_right hle hγ
  · exact neg_of_mul_neg_right hlt hγ.le

/-- **A pitchfork of zeros at the trivial zero of an odd family.** Let `f s : E → E` be a
one-parameter family of maps of a finite-dimensional real normed space, jointly `C³` near
`(t, 0)` and odd near `(t, 0)`, `f s (-x) = -f s x`, so that `0` is a zero of `f s` for every
`s` near `t`. Let the kernel of `D(f t)₀` be the line through `v`, let `φ` vanish on the range
of `D(f t)₀`, and suppose that `κ = φ (D³(f t)₀ (v, v, v)) · φ (∂ₛ D(f s)₀ v) ≠ 0`. Then there
are a sign `ε ≠ 0` and a neighbourhood `U` of `0` such that for every `s` near `t`:

* the trivial zero `0` of `f s` has Jacobian sign `ε · sign (κ (s - t))`, so it is nondegenerate
  for `s ≠ t` and its sign changes as `s` crosses `t`;
* if `κ (s - t) ≥ 0`, then `0` is the only zero of `f s` in `U`;
* if `κ (s - t) < 0`, then the zeros of `f s` in `U` are exactly `0`, `x₀` and `-x₀` for some
  `x₀ ≠ 0`, and `x₀` and `-x₀` both have Jacobian sign `ε`, opposite to that of `0`.

So a single orbit `{x₀, -x₀}` of the symmetry `x ↦ -x` is born on one side of `t`, carrying the
sign that the trivial zero has on the other side. -/
theorem exists_mem_nhds_setOf_apply_eq_zero_pitchfork (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    (hodd : ∀ᶠ p in 𝓝 (t, (0 : E)), f p.1 (-p.2) = -f p.1 p.2) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0)
    (hκ : φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
      φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) ≠ 0) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∃ U ∈ 𝓝 (0 : E), ∀ᶠ s in 𝓝 t,
      SignType.sign (LinearMap.det (fderiv ℝ (f s) 0 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t)) ∧
      (0 ≤ φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) →
        {x ∈ U | f s x = 0} = {0}) ∧
      (φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t) < 0 →
        ∃ x₀, x₀ ≠ 0 ∧ {x ∈ U | f s x = 0} = {0, x₀, -x₀} ∧
          SignType.sign (LinearMap.det (fderiv ℝ (f s) x₀ : E →ₗ[ℝ] E)) = ε ∧
          SignType.sign (LinearMap.det (fderiv ℝ (f s) (-x₀) : E →ₗ[ℝ] E)) = ε) := by
  rcases (left_ne_zero_of_mul hκ).lt_or_gt with hγ | hγ
  · -- For a negative cubic coefficient use `-φ`, which leaves the product `κ` unchanged.
    have h := exists_mem_nhds_pitchfork_of_pos hf hodd hker (φ := -φ) (by simp [hφ])
      (by simpa using hγ) (by simpa using right_ne_zero_of_mul hκ)
    simpa only [neg_apply, neg_mul_neg] using h
  · exact exists_mem_nhds_pitchfork_of_pos hf hodd hker hφ hγ (right_ne_zero_of_mul hκ)

/-- **The signed counts of zeros across a pitchfork point.** Under the hypotheses of
`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_pitchfork`, there are a sign `ε ≠ 0` and a
neighbourhood `U` of `0` such that for every `s ≠ t` near `t` the zeros `y` of `f s` in `U`,
counted with the signs of `det D(f s)_y`, add up to `ε`, while the nontrivial zeros `y ≠ 0` add
up to `ε (1 - sign (κ (s - t)))`, that is to `0` if `κ (s - t) > 0` and to `2 ε` if
`κ (s - t) < 0`. So the signed count of the orbits of `x ↦ -x`, the sign of the trivial zero plus
half that of the nontrivial zeros, is `ε` if `κ (s - t) > 0` and `0` if `κ (s - t) < 0`: it
changes by `ε` across `t`. -/
theorem exists_mem_nhds_finsum_sign_det_fderiv_eq_pitchfork
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, 0))
    (hodd : ∀ᶠ p in 𝓝 (t, (0 : E)), f p.1 (-p.2) = -f p.1 p.2) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) 0 : E →ₗ[ℝ] E) = ℝ ∙ v) {φ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) 0 y) = 0)
    (hκ : φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
      φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) ≠ 0) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∃ U ∈ 𝓝 (0 : E), ∀ᶠ s in 𝓝[≠] t,
      ∑ᶠ y ∈ U ∩ f s ⁻¹' {0},
          (SignType.sign (LinearMap.det (fderiv ℝ (f s) y : E →ₗ[ℝ] E)) : ℤ) = ε ∧
      ∑ᶠ y ∈ (U \ {0}) ∩ f s ⁻¹' {0},
          (SignType.sign (LinearMap.det (fderiv ℝ (f s) y : E →ₗ[ℝ] E)) : ℤ) =
        ε * (1 - SignType.sign (φ (fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) 0 v v v) *
          φ (deriv (fun r ↦ fderiv ℝ (f r) 0 v) t) * (s - t))) := by
  obtain ⟨ε, hε, U, hU, h⟩ := exists_mem_nhds_setOf_apply_eq_zero_pitchfork hf hodd hker hφ hκ
  refine ⟨ε, hε, U, hU, ?_⟩
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with s ⟨h0, hle, hlt⟩ hst
  have hS : U ∩ f s ⁻¹' {0} = {y ∈ U | f s y = 0} := by
    ext
    simp
  have hS' : (U \ {0}) ∩ f s ⁻¹' {0} = {y ∈ U | f s y = 0} \ {0} := by
    ext
    simp only [mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_ofPred_eq]
    tauto
  rw [hS, hS']
  rcases (mul_ne_zero hκ (sub_ne_zero.2 hst)).lt_or_gt with hneg | hpos
  · -- The zeros are `0`, of sign `-ε`, and `±x₀`, both of sign `ε`.
    obtain ⟨x₀, hx₀, hset, h₁, h₂⟩ := hlt hneg
    have hne : x₀ ≠ -x₀ := fun h ↦ hx₀ (eq_zero_of_eq_neg_of_invertible_two (R := ℝ) h)
    have h0x : (0 : E) ∉ ({x₀, -x₀} : Set E) := by simp [hx₀, eq_comm (a := (0 : E))]
    have hnt : ({0, x₀, -x₀} : Set E) \ {0} = {x₀, -x₀} := by
      rw [insert_sdiff_of_mem _ (mem_singleton 0), sdiff_singleton_eq_self h0x]
    rw [hset, hnt, finsum_mem_insert _ h0x (toFinite _)]
    -- Each of `x₀` and `-x₀` contributes `ε`.
    have hpair : ∑ᶠ y ∈ ({x₀, -x₀} : Set E),
        (SignType.sign (LinearMap.det (fderiv ℝ (f s) y : E →ₗ[ℝ] E)) : ℤ) = ε + ε := by
      rw [finsum_mem_pair hne, h₁, h₂]
    simp only [hpair, h0, sign_neg hneg, SignType.coe_mul, SignType.coe_neg_one]
    constructor <;> ring
  · -- The only zero is `0`, of sign `ε`.
    rw [sign_pos hpos] at h0
    rw [hle hpos.le]
    simp [h0, sign_pos hpos]

end TauCeti
