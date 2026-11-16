/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve

/-!
# The variational equation of a time-dependent flow

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional boundaryless
manifold `M`, with time-dependent flow `φ_{s,t} = TauCeti.timeDependentFlowOf X s t`, and let `∇`
be a torsion-free connection on `TM`. For a point `x` and a tangent vector `v ∈ T_x M`, the
linearized flow `V(t) = dφ_{s,t}(x) v` is a vector field along the trajectory
`γ(t) = φ_{s,t}(x)`. It solves the **variational equation**

`D_t V = ∇_V X_t`,  `V(s) = v`,

wherever the flow is defined (`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`,
with the initial value `TauCeti.mfderiv_timeDependentFlowOf_self`). No completeness of `X` is
assumed: the equation holds at every time `t` with `((s, t), x)` in the flow domain.

The proof differentiates the two-parameter variation `F(r, u) = φ_{s,u}(c(r))` along a curve `c`
with `c(0) = x` and `c'(0) = v`. Each curve `F(r, ·)` is an integral curve of `X`, so the
autonomous variational equation
`CovariantDerivative.alongCurve_curveVelocity_eq_covariantDerivative` applies to the frozen field
`X_t` at the time `t`, and the transverse velocity `∂_r F(0, u)` is `dφ_{s,u}(x) v` by the chain
rule.

For a time-dependent Hamiltonian `H`, with `X_t` the Hamiltonian vector field of `H_t`, this is
the equation satisfied by the linearized Hamiltonian flow along a trajectory, whose solutions at
a one-periodic orbit give the linearized return map entering the Conley–Zehnder index and the
asymptotic operators of Floer cylinders.

## Main results

* `CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`: the variational equation
  `D_t (dφ_{s,t} v) = ∇_{dφ_{s,t} v} X_t` along the trajectory through `x`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, the linearized flow along a periodic orbit.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  {X : ℝ → Π x : M, TangentSpace I x} {s t : ℝ} {x : M}

/-- **The variational equation of a time-dependent flow.** Let `X` be a jointly `C²`
time-dependent vector field with time-dependent flow `φ_{s,t}`, and `∇` a torsion-free
connection. If the flow from time `s` is defined at `x` up to time `t`, the linearized flow
`V(u) = dφ_{s,u}(x) v` along the trajectory `u ↦ φ_{s,u}(x)` satisfies
`D_t V = ∇_{V(t)} X_t` at `t`. -/
theorem alongCurve_mfderiv_timeDependentFlowOf
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) (v : TangentSpace I x) :
    alongCurve cov (fun u ↦ timeDependentFlowOf X s u x)
        (fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v) t =
      cov (X t) (timeDependentFlowOf X s t x) (mfderiv I I (timeDependentFlowOf X s t) x v) := by
  have hX₁ := hX.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hopen := isOpen_timeDependentFlowDomain hX₁
  have hflow := contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX
  -- Realize `v` as the velocity at `0` of a `C²` curve `c` through `x`.
  obtain ⟨c, rfl, hc, hcv⟩ := exists_contMDiffAt_curveVelocity_eq (I := I) (n := 2)
    (by norm_num) x v 0
  -- The variation `F (r, u) = φ_{s,u}(c r)` is `C²` near `(0, t)`.
  set F : ℝ → ℝ → M := fun r u ↦ timeDependentFlowOf X s u (c r)
  have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 2
      (fun z : ℝ × ℝ ↦ ((s, z.2), c z.1)) (0, t) := by
    refine ContMDiffAt.prodMk ?_ (hc.comp (0, t) (contMDiff_iff_contDiff.mpr
      (contDiff_fst : ContDiff ℝ 2 (Prod.fst : ℝ × ℝ → ℝ))).contMDiffAt)
    exact contMDiffAt_const.prodMk (contMDiff_iff_contDiff.mpr
      (contDiff_snd : ContDiff ℝ 2 (Prod.snd : ℝ × ℝ → ℝ))).contMDiffAt
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    (hflow.contMDiffAt (hopen.mem_nhds h)).comp (0, t) hg
  -- Each curve `F r` is an integral curve of `X` at the time `t`.
  have hcurve : ∀ᶠ r in 𝓝 0, curveVelocity I (F r) t = X t (F r t) := by
    have hdom : ∀ᶠ r in 𝓝 (0 : ℝ), ((s, t), c r) ∈ timeDependentFlowDomain X :=
      (continuousAt_const.prodMk hc.continuousAt).preimage_mem_nhds (hopen.mem_nhds h)
    filter_upwards [hdom] with r hr
    simpa only [curveVelocityWithin_univ] using
      curveVelocityWithin_eq_of_hasMFDerivWithinAt
        (hasMFDerivAt_timeDependentFlowOf hX₁ hr).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  have hXt : MDiffAt (T% (X t)) (F 0 t) :=
    ((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by norm_num)) _
  -- The transverse velocity of the variation is the linearized flow applied to `v`.
  have hvel : ∀ᶠ u in 𝓝 t, curveVelocity I (fun r ↦ F r u) 0 =
      mfderiv I I (timeDependentFlowOf X s u) (c 0) v := by
    have hdom : ∀ᶠ u in 𝓝 t, ((s, u), c 0) ∈ timeDependentFlowDomain X :=
      (continuousAt_const.prodMk continuousAt_id |>.prodMk continuousAt_const).preimage_mem_nhds
        (hopen.mem_nhds h)
    filter_upwards [hdom] with u hu
    have hφ : MDifferentiableAt I I (timeDependentFlowOf X s u) (c 0) :=
      (((hflow.contMDiffAt (hopen.mem_nhds hu)).comp (c 0)
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num))
    have hmap := curveVelocityWithin_map hφ uniqueDiffWithinAt_univ
      (hc.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt
    rw [curveVelocityWithin_univ, curveVelocityWithin_univ, hcv] at hmap
    -- The curve `timeDependentFlowOf X s u ∘ c` is `fun r ↦ F r u` by the definition of `F`.
    exact hmap
  have key := alongCurve_curveVelocity_eq_covariantDerivative cov htor hF hXt hcurve
  rw [alongCurve_congr cov (F 0) _ hvel, hvel.self_of_nhds] at key
  exact key

end CovariantDerivative
