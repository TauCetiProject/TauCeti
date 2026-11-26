/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.TriangleBase
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
public import TauCeti.Geometry.Manifold.VectorField.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.IntegralCurve.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Triangle fields and their strict Lyapunov function

Let `X₀`, `X₁` and `X₂` be vector fields on a manifold `M`, such as pseudo-gradients adapted to
Morse functions `f₀`, `f₁` and `f₂`. The composite of the continuations `f₀ ⇝ f₁ ⇝ f₂` and the
direct continuation `f₀ ⇝ f₂` are compared through a vector field `W` on `M × ℝ²` over the ordered
triangle `0 ≤ v ≤ u ≤ 1` (`TauCeti.triangleBase`). A **triangle field** from `X₀` through `X₁` to
`X₂` at rate `C` (`TauCeti.IsTriangleField`) is such a field whose base component is the field
`(C u (1 - u²), C v (1 - v²))` of the ordered-triangle base, and whose space component is `X₀`, `X₁`
and `X₂` near the source `(0, 0)`, the corner `(1, 0)` and the sink `(1, 1)` of the triangle. The
product of a field `X` with the base field is one (`TauCeti.isTriangleField_prodVectorField`).

This file proves that the trajectories of a triangle field through the triangle are confined to it,
run between the vertices, and admit a strict Lyapunov function.

* **Confinement.** The base component of every trajectory is a trajectory of the triangle base
  (`TauCeti.IsTriangleField.isIntegralCurve_snd`), and of a trajectory meeting the triangle it is a
  flow line of the triangle base (`TauCeti.IsTriangleField.snd_eq_triangleBaseFlow`). So a
  trajectory meeting the triangle stays in it, and one meeting it away from the vertices never
  reaches a vertex (`TauCeti.IsTriangleField.gradient_snd_ne_zero`).
* **Limits at the vertices.** For `C > 0`, a trajectory through the triangle tends at `-∞` to
  `(p, (0, 0))` for a critical point `p` of `f₀` when `u < 1`, and to `(q, (1, 0))` for a critical
  point `q` of `f₁` on the edge `u = 1` away from the sink; at `+∞` it tends to `(r, (1, 1))` for a
  critical point `r` of `f₂` when `0 < v`, and to `(q, (1, 0))` on the edge `v = 0` away from the
  source. These follow from the limits of a trajectory of a field on a product whose base component
  converges (`TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atBot_of_tendsto_snd` and
  `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atTop_of_tendsto_snd`).
* **The Lyapunov function.** Let `F` be a `C¹` function on `M × ℝ²` equal to `f₀ (x)`, `f₁ (x)`
  and `f₂ (x)` near the three vertices, uniformly in `x`, and suppose that `fᵢ` does not increase
  along `Xᵢ`. For a large constant `K` the function

  `L (x, (u, v)) = K (u + v) - F (x, (u, v))`

  strictly increases along every trajectory through the triangle away from its vertices
  (`TauCeti.IsTriangleField.eventually_strictMono_mul_add_sub`). Its derivative along `W` is
  `K C (u (1 - u²) + v (1 - v²)) - dF(W)`. Near the vertices `dF(W) = dfᵢ(Xᵢ) ≤ 0`, while the base
  speed `u (1 - u²) + v (1 - v²)` is positive on the triangle away from them; on the compact rest of
  the triangle the base speed is bounded below and `dF(W)` above, so a large `K` dominates
  (`TauCeti.IsTriangleField.eventually_forall_mvfderiv_apply_lt_mul_add`). Along a trajectory from
  `(p, (0, 0))` to `(r, (1, 1))` through the triangle, `L` stays strictly between its limits
  `-f₀ (p)` and `2 K - f₂ (r)` (`TauCeti.IsTriangleField.eventually_mul_add_sub_mem_Ioo`). For `C¹`
  functions `f₀`, `f₁`, `f₂` such an `F` exists
  (`TauCeti.IsTriangleField.exists_strictMono_mul_add_sub`).

This is the triangle counterpart of the Lyapunov function `K t - F` of a continuation field over the
interval base in `TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Lyapunov`: it makes a
triangle field gradient-like on the triangle away from its vertices, as the compactification of the
triangle trajectory spaces requires.

## Main declarations

* `TauCeti.IsTriangleField`: the triangle fields, and the product witness
  `TauCeti.isTriangleField_prodVectorField`.
* `TauCeti.IsTriangleField.isIntegralCurve_snd`, `TauCeti.IsTriangleField.snd_eq_triangleBaseFlow`,
  `TauCeti.IsTriangleField.snd_mem_triangleBase`, `TauCeti.IsTriangleField.gradient_snd_ne_zero`:
  confinement of the base component.
* `TauCeti.IsTriangleField.tendsto_snd_atBot_of_tendsto_triangleBaseFlow`,
  `TauCeti.IsTriangleField.tendsto_snd_atTop_of_tendsto_triangleBaseFlow`: the base component of a
  trajectory through the triangle tends, within the triangle, to the limits of its base flow line.
* `TauCeti.IsTriangleField.exists_tendsto_atBot_source`,
  `TauCeti.IsTriangleField.exists_tendsto_atBot_corner`,
  `TauCeti.IsTriangleField.exists_tendsto_atTop_sink`,
  `TauCeti.IsTriangleField.exists_tendsto_atTop_corner`: the limits at the vertices.
* `TauCeti.IsTriangleField.eventually_forall_mvfderiv_apply_lt_mul_add`,
  `TauCeti.IsTriangleField.eventually_strictMono_mul_add_sub`,
  `TauCeti.IsTriangleField.eventually_mul_add_sub_mem_Ioo`,
  `TauCeti.IsTriangleField.exists_strictMono_mul_add_sub`: the strict Lyapunov function.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2, Lemma 4.3 (the composition of continuation maps, through
  a two-parameter family of functions).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Gradient Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-! ### Triangle fields -/

section Definition

/-- A vector field `W` on `M × ℝ²` is a **triangle field** from `X₀` through `X₁` to `X₂` at rate
`C` if its base component is the field `(C u (1 - u²), C v (1 - v²))` of the ordered-triangle base,
the negative gradient of `TauCeti.triangleBasePotential C`, and if near the source `(0, 0)`, the
corner `(1, 0)` and the sink `(1, 1)` of the triangle its space component is `X₀`, `X₁` and `X₂`.
These are the fields over the triangle of the composition of continuations: the edge `v = 0`
carries a continuation from `X₀` to `X₁`, the edge `u = 1` one from `X₁` to `X₂`, and the diagonal
one from `X₀` to `X₂`. -/
structure IsTriangleField (X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x) (C : ℝ)
    (W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z) :
    Prop where
  /-- The base component is the field of the ordered-triangle base. -/
  snd_eq : ∀ z : M × WithLp 2 (ℝ × ℝ),
    (W z : E × WithLp 2 (ℝ × ℝ)).2 = -∇ (triangleBasePotential C) z.2
  /-- Near the source `(0, 0)` of the triangle, the space component is `X₀`. -/
  eventually_fst_eq_source : ∀ᶠ b in 𝓝[triangleBase] WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)),
    ∀ x, (W (x, b) : E × WithLp 2 (ℝ × ℝ)).1 = X₀ x
  /-- Near the corner `(1, 0)` of the triangle, the space component is `X₁`. -/
  eventually_fst_eq_corner : ∀ᶠ b in 𝓝[triangleBase] WithLp.toLp 2 ((1 : ℝ), (0 : ℝ)),
    ∀ x, (W (x, b) : E × WithLp 2 (ℝ × ℝ)).1 = X₁ x
  /-- Near the sink `(1, 1)` of the triangle, the space component is `X₂`. -/
  eventually_fst_eq_sink : ∀ᶠ b in 𝓝[triangleBase] WithLp.toLp 2 ((1 : ℝ), (1 : ℝ)),
    ∀ x, (W (x, b) : E × WithLp 2 (ℝ × ℝ)).1 = X₂ x

/-- **The product triangle field.** For a vector field `X` on `M`, the product of `X` with the field
of the ordered-triangle base is a triangle field from `X` through `X` to `X`. -/
theorem isTriangleField_prodVectorField (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (C : ℝ) :
    IsTriangleField X X X C
      (Manifold.prodVectorField X fun b ↦ -∇ (triangleBasePotential C) b) where
  snd_eq z := Manifold.prodVectorField_snd _ _ z
  eventually_fst_eq_source := .of_forall fun b x ↦ Manifold.prodVectorField_fst _ _ (x, b)
  eventually_fst_eq_corner := .of_forall fun b x ↦ Manifold.prodVectorField_fst _ _ (x, b)
  eventually_fst_eq_sink := .of_forall fun b x ↦ Manifold.prodVectorField_fst _ _ (x, b)

end Definition

namespace IsTriangleField

variable {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
  {γ : ℝ → M × WithLp 2 (ℝ × ℝ)} {s₀ : ℝ}

/-- The sum of the coordinates of the base component of a triangle field is `C` times the base
speed `u (1 - u²) + v (1 - v²)`. -/
theorem snd_fst_add_snd_snd (hW : IsTriangleField X₀ X₁ X₂ C W) (z : M × WithLp 2 (ℝ × ℝ)) :
    (W z : E × WithLp 2 (ℝ × ℝ)).2.fst + (W z : E × WithLp 2 (ℝ × ℝ)).2.snd =
      C * (z.2.fst * (1 - z.2.fst ^ 2) + z.2.snd * (1 - z.2.snd ^ 2)) := by
  rw [hW.snd_eq z, gradient_triangleBasePotential]
  simp only [WithLp.neg_fst, WithLp.neg_snd, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

/-! ### Confinement -/

section Confinement

variable (hW : IsTriangleField X₀ X₁ X₂ C W) (hγ : IsMIntegralCurve γ W)
include hW hγ

/-- **The base component of a trajectory is a trajectory of the triangle base.** -/
theorem isIntegralCurve_snd :
    IsIntegralCurve (fun s ↦ (γ s).2) (fun _ b ↦ -∇ (triangleBasePotential C) b) := fun s ↦ by
  simpa only [hW.snd_eq] using hγ.hasDerivAt_snd s

/-- **The base component of a trajectory is a flow line of the triangle base.** For an integral
curve `γ` of a triangle field whose base component lies in the triangle at time `s₀`, the base
component at time `s` is the image of `(γ s₀).2` under the flow of the base for time `s - s₀`. -/
theorem snd_eq_triangleBaseFlow (h₀ : (γ s₀).2 ∈ triangleBase) (s : ℝ) :
    (γ s).2 = triangleBaseFlow C (s - s₀) (γ s₀).2 :=
  have h := mem_triangleBase.1 h₀
  eq_triangleBaseFlow_of_isIntegralCurve (γ := fun s ↦ (γ s).2) (hW.isIntegralCurve_snd hγ)
    ⟨by linarith [h.1, h.2.1], h.2.2⟩ ⟨by linarith [h.1], h.2.1.trans h.2.2⟩ s

/-- **A trajectory meeting the triangle stays in it.** -/
theorem snd_mem_triangleBase (h₀ : (γ s₀).2 ∈ triangleBase) (s : ℝ) : (γ s).2 ∈ triangleBase := by
  rw [hW.snd_eq_triangleBaseFlow hγ h₀ s]
  exact mapsTo_triangleBaseFlow C _ h₀

/-- **A trajectory not at a vertex never reaches one.** If the base component of an integral curve
of a triangle field is not a zero of the base field at one time, it is not one at any time: the
zeros are stationary points of the base, so a trajectory through one of them stays there. On the
triangle these zeros are its three vertices (`TauCeti.gradient_triangleBasePotential_eq_zero_iff`).
-/
theorem gradient_snd_ne_zero (h₀ : ∇ (triangleBasePotential C) (γ s₀).2 ≠ 0) (s : ℝ) :
    ∇ (triangleBasePotential C) (γ s).2 ≠ 0 := by
  intro hs
  -- The constant curve at the zero `(γ s).2` is a trajectory, so it is the base component.
  have hconst : IsIntegralCurve (fun _ : ℝ ↦ (γ s).2)
      (fun _ b ↦ -∇ (triangleBasePotential C) b) := fun _ ↦ by
    simpa [hs] using hasDerivAt_const _ (γ s).2
  have h := congrFun (eq_of_isIntegralCurve_triangleBasePotential (hW.isIntegralCurve_snd hγ)
    hconst (t₀ := s) rfl) s₀
  exact h₀ (h ▸ hs)

/-- **Base limits at `-∞`.** If the flow line of the triangle base through the base component
`(γ s₀).2 ∈ triangleBase` of a trajectory tends to `b` at `-∞`, the base component of the
trajectory tends to `b` within the triangle. -/
theorem tendsto_snd_atBot_of_tendsto_triangleBaseFlow (h₀ : (γ s₀).2 ∈ triangleBase)
    {b : WithLp 2 (ℝ × ℝ)} (hb : Tendsto (fun s ↦ triangleBaseFlow C s (γ s₀).2) atBot (𝓝 b)) :
    Tendsto (fun s ↦ (γ s).2) atBot (𝓝[triangleBase] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (hW.snd_mem_triangleBase hγ h₀)⟩
  rw [funext (hW.snd_eq_triangleBaseFlow hγ h₀)]
  exact hb.comp (tendsto_atBot_add_const_right _ _ tendsto_id)

/-- **Base limits at `+∞`.** If the flow line of the triangle base through the base component
`(γ s₀).2 ∈ triangleBase` of a trajectory tends to `b` at `+∞`, the base component of the
trajectory tends to `b` within the triangle. -/
theorem tendsto_snd_atTop_of_tendsto_triangleBaseFlow (h₀ : (γ s₀).2 ∈ triangleBase)
    {b : WithLp 2 (ℝ × ℝ)} (hb : Tendsto (fun s ↦ triangleBaseFlow C s (γ s₀).2) atTop (𝓝 b)) :
    Tendsto (fun s ↦ (γ s).2) atTop (𝓝[triangleBase] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall (hW.snd_mem_triangleBase hγ h₀)⟩
  rw [funext (hW.snd_eq_triangleBaseFlow hγ h₀)]
  exact hb.comp (tendsto_atTop_add_const_right _ _ tendsto_id)

end Confinement

end IsTriangleField

/-! ### Limits at the vertices -/

section Limits

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsTriangleField

variable {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
  {γ : ℝ → M × WithLp 2 (ℝ × ℝ)} {s₀ : ℝ}
  (hW : IsTriangleField X₀ X₁ X₂ C W) (hC : 0 < C) (hγ : IsMIntegralCurve γ W)
  (h₀ : (γ s₀).2 ∈ triangleBase)
include hW hC hγ h₀

/-- **A trajectory off the edge `u = 1` comes from the source.** For `C > 0`, an integral curve of
a triangle field from a pseudo-gradient `X₀` adapted to `f₀`, whose base component lies in the
triangle with `u < 1`, tends at `-∞` to `(p, (0, 0))` for a critical point `p` of `f₀`. -/
theorem exists_tendsto_atBot_source (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hu : (γ s₀).2.fst < 1) :
    ∃ p ∈ criticalPoints 𝓘(ℝ, E) f₀, Tendsto γ atBot (𝓝 (p, WithLp.toLp 2 (0, 0))) := by
  have hb := mem_triangleBase.1 h₀
  exact hX₀.exists_tendsto_atBot_of_tendsto_snd hW.eventually_fst_eq_source hγ
    (hW.tendsto_snd_atBot_of_tendsto_triangleBaseFlow hγ h₀
      (tendsto_triangleBaseFlow_atBot_toLp_zero_zero hC ⟨by linarith [hb.1, hb.2.1], hu⟩
        ⟨by linarith [hb.1], by linarith [hb.2.1]⟩))

/-- **A trajectory on the edge `u = 1` comes from the corner.** For `C > 0`, an integral curve of
a triangle field through a pseudo-gradient `X₁` adapted to `f₁`, whose base component lies on the
edge `u = 1` away from the sink, tends at `-∞` to `(q, (1, 0))` for a critical point `q` of `f₁`. -/
theorem exists_tendsto_atBot_corner (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
    (hu : (γ s₀).2.fst = 1) (hv : (γ s₀).2.snd < 1) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E) f₁, Tendsto γ atBot (𝓝 (q, WithLp.toLp 2 (1, 0))) := by
  have hb := mem_triangleBase.1 h₀
  exact hX₁.exists_tendsto_atBot_of_tendsto_snd hW.eventually_fst_eq_corner hγ
    (hW.tendsto_snd_atBot_of_tendsto_triangleBaseFlow hγ h₀
      (tendsto_triangleBaseFlow_atBot_toLp_one_zero hC hu ⟨by linarith [hb.1], hv⟩))

/-- **A trajectory off the edge `v = 0` goes to the sink.** For `C > 0`, an integral curve of a
triangle field to a pseudo-gradient `X₂` adapted to `f₂`, whose base component lies in the
triangle with `0 < v`, tends at `+∞` to `(r, (1, 1))` for a critical point `r` of `f₂`. -/
theorem exists_tendsto_atTop_sink (hX₂ : IsAdaptedPseudoGradient f₂ X₂)
    (hv : 0 < (γ s₀).2.snd) :
    ∃ r ∈ criticalPoints 𝓘(ℝ, E) f₂, Tendsto γ atTop (𝓝 (r, WithLp.toLp 2 (1, 1))) := by
  have hb := mem_triangleBase.1 h₀
  exact hX₂.exists_tendsto_atTop_of_tendsto_snd hW.eventually_fst_eq_sink hγ
    (hW.tendsto_snd_atTop_of_tendsto_triangleBaseFlow hγ h₀
      (tendsto_triangleBaseFlow_atTop_toLp_one_one hC ⟨hv.trans_le hb.2.1, hb.2.2⟩
        ⟨hv, hb.2.1.trans hb.2.2⟩))

/-- **A trajectory on the edge `v = 0` goes to the corner.** For `C > 0`, an integral curve of a
triangle field through a pseudo-gradient `X₁` adapted to `f₁`, whose base component lies on the
edge `v = 0` away from the source, tends at `+∞` to `(q, (1, 0))` for a critical point `q` of
`f₁`. -/
theorem exists_tendsto_atTop_corner (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
    (hu : 0 < (γ s₀).2.fst) (hv : (γ s₀).2.snd = 0) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E) f₁, Tendsto γ atTop (𝓝 (q, WithLp.toLp 2 (1, 0))) := by
  exact hX₁.exists_tendsto_atTop_of_tendsto_snd hW.eventually_fst_eq_corner hγ
    (hW.tendsto_snd_atTop_of_tendsto_triangleBaseFlow hγ h₀
      (tendsto_triangleBaseFlow_atTop_toLp_one_zero hC ⟨hu, (mem_triangleBase.1 h₀).2.2⟩ hv))

end IsTriangleField

end Limits

/-! ### The Lyapunov function -/

namespace IsTriangleField

section Lyapunov

variable [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
  {F : M × WithLp 2 (ℝ × ℝ) → ℝ}

omit [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M] in
/-- Near a vertex `v` where the space component of `W` is `X` and `F` is `f`, with `f`
nonincreasing along `X`, the derivative of `F` along `W` is nonpositive on the triangle. -/
private theorem exists_isOpen_forall_mvfderiv_apply_nonpos {v : WithLp 2 (ℝ × ℝ)}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hWv : ∀ᶠ b in 𝓝[triangleBase] v, ∀ x, (W (x, b) : E × WithLp 2 (ℝ × ℝ)).1 = X x)
    (hFv : ∀ᶠ b in 𝓝 v, ∀ x, F (x, b) = f x) (hX : ∀ x, mvfderiv 𝓘(ℝ, E) f x (X x) ≤ 0) :
    ∃ O : Set (WithLp 2 (ℝ × ℝ)), IsOpen O ∧ v ∈ O ∧ ∀ b ∈ O ∩ triangleBase, ∀ x,
      mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F (x, b) (W (x, b)) ≤ 0 := by
  obtain ⟨U, hUo, hvU, hU⟩ := mem_nhdsWithin.1 hWv
  obtain ⟨V, hV, hVo, hvV⟩ := eventually_nhds_iff.1 hFv
  refine ⟨U ∩ V, hUo.inter hVo, ⟨hvU, hvV⟩, fun b ⟨⟨hbU, hbV⟩, hb⟩ x ↦ ?_⟩
  -- Near `(x, b)`, `F` is `f ∘ Prod.fst`, so its derivative along `W` is that of `f` along `X`.
  rw [mvfderiv_apply_eq_of_eventually_forall_eq (eventually_of_mem (hVo.mem_nhds hbV) hV),
    hU ⟨hbU, hb⟩ x]
  exact hX x

variable (hW : IsTriangleField X₀ X₁ X₂ C W) (hC : 0 < C)
  (hWc : Continuous fun z ↦ (⟨z, W z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ)))
    (M × WithLp 2 (ℝ × ℝ))))
  (hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) 𝓘(ℝ) 1 F)
  (hF₀ : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))), ∀ x, F (x, b) = f₀ x)
  (hF₁ : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((1 : ℝ), (0 : ℝ))), ∀ x, F (x, b) = f₁ x)
  (hF₂ : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((1 : ℝ), (1 : ℝ))), ∀ x, F (x, b) = f₂ x)
  (hX₀ : ∀ x, mvfderiv 𝓘(ℝ, E) f₀ x (X₀ x) ≤ 0) (hX₁ : ∀ x, mvfderiv 𝓘(ℝ, E) f₁ x (X₁ x) ≤ 0)
  (hX₂ : ∀ x, mvfderiv 𝓘(ℝ, E) f₂ x (X₂ x) ≤ 0)
include hW hC hWc hF hF₀ hF₁ hF₂ hX₀ hX₁ hX₂

/-- **The derivative of the interpolation along a triangle field is dominated by the base field.**
For all large `K`, at every point of `M` times the triangle away from its vertices (the zeros of the
base field), the derivative `dF(W)` of `F` along the triangle field `W` is less than `K` times the
sum `C (u (1 - u²) + v (1 - v²))` of the coordinates of the base component of `W`. Equivalently,
`K (u + v) - F` has positive derivative along `W` there. -/
theorem eventually_forall_mvfderiv_apply_lt_mul_add :
    ∀ᶠ K in atTop, ∀ z : M × WithLp 2 (ℝ × ℝ), z.2 ∈ triangleBase →
      ∇ (triangleBasePotential C) z.2 ≠ 0 →
        mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F z (W z) <
          K * ((W z : E × WithLp 2 (ℝ × ℝ)).2.fst + (W z : E × WithLp 2 (ℝ × ℝ)).2.snd) := by
  -- Near the three vertices the derivative along `W` is nonpositive.
  obtain ⟨O₀, hO₀, hv₀, hd₀⟩ :=
    exists_isOpen_forall_mvfderiv_apply_nonpos hW.eventually_fst_eq_source hF₀ hX₀
  obtain ⟨O₁, hO₁, hv₁, hd₁⟩ :=
    exists_isOpen_forall_mvfderiv_apply_nonpos hW.eventually_fst_eq_corner hF₁ hX₁
  obtain ⟨O₂, hO₂, hv₂, hd₂⟩ :=
    exists_isOpen_forall_mvfderiv_apply_nonpos hW.eventually_fst_eq_sink hF₂ hX₂
  -- The rest `S` of the triangle is compact and contains no vertex, so the base speed `g` has a
  -- positive lower bound `m` on it.
  set S := triangleBase \ (O₀ ∪ O₁ ∪ O₂)
  have hS : IsCompact S := isCompact_triangleBase.diff ((hO₀.union hO₁).union hO₂)
  set g : WithLp 2 (ℝ × ℝ) → ℝ := fun b ↦ b.fst * (1 - b.fst ^ 2) + b.snd * (1 - b.snd ^ 2)
  have hg : Continuous g := by fun_prop
  have hgS : ∀ b ∈ S, 0 < g b := fun b hb ↦
    add_pos_of_mem_triangleBase_of_gradient_ne_zero hb.1 fun h ↦ hb.2 <| by
      rcases (gradient_triangleBasePotential_eq_zero_iff hC.ne' hb.1).1 h with rfl | rfl | rfl
      exacts [Or.inl (Or.inl hv₀), Or.inl (Or.inr hv₁), Or.inr hv₂]
  obtain ⟨m, hm, hmS⟩ := hS.exists_forall_le' hg.continuousOn hgS
  -- On the compact set `M × S` the derivative along `W` is bounded above by some `B`.
  have hcont : Continuous fun z : M × WithLp 2 (ℝ × ℝ) ↦
      mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F z (W z) :=
    ((hF.contMDiff_mvfderiv_apply (m := 0) (by simp)).comp
      (contMDiff_zero_iff.2 hWc : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ)))
        (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))).tangent 0 _)).continuous
  obtain ⟨B, hB⟩ := (isCompact_univ.prod hS).bddAbove_image hcont.continuousOn
  filter_upwards [eventually_gt_atTop (max 0 (B / (C * m)))] with K hK z hz hgrad
  have hK₀ : 0 < K := (le_max_left _ _).trans_lt hK
  rw [hW.snd_fst_add_snd_snd z]
  have hpos : 0 < z.2.fst * (1 - z.2.fst ^ 2) + z.2.snd * (1 - z.2.snd ^ 2) :=
    add_pos_of_mem_triangleBase_of_gradient_ne_zero hz hgrad
  by_cases hO : z.2 ∈ O₀ ∪ O₁ ∪ O₂
  · -- Near a vertex the derivative is nonpositive, while the base speed is positive.
    have hle : mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F z (W z) ≤ 0 := by
      rcases hO with (h | h) | h
      exacts [hd₀ z.2 ⟨h, hz⟩ z.1, hd₁ z.2 ⟨h, hz⟩ z.1, hd₂ z.2 ⟨h, hz⟩ z.1]
    exact hle.trans_lt (by positivity)
  · -- Elsewhere the derivative is at most `B < K C m ≤ K C g`.
    have hzS : z.2 ∈ S := ⟨hz, hO⟩
    have hBz := hB ⟨z, ⟨trivial, hzS⟩, rfl⟩
    have hKB : B < K * (C * m) := (div_lt_iff₀ (by positivity)).1 ((le_max_right _ _).trans_lt hK)
    calc mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F z (W z) ≤ B := hBz
      _ < K * (C * m) := hKB
      _ ≤ K * (C * g z.2) := by gcongr; exact hmS z.2 hzS

/-- **A strict Lyapunov function for a triangle field.** For all large `K`, the function
`K (u + v) - F` strictly increases along every integral curve of the triangle field `W` which meets
the triangle away from its vertices (the zeros of the base field). -/
theorem eventually_strictMono_mul_add_sub :
    ∀ᶠ K in atTop, ∀ γ : ℝ → M × WithLp 2 (ℝ × ℝ), IsMIntegralCurve γ W → ∀ s₀,
      (γ s₀).2 ∈ triangleBase → ∇ (triangleBasePotential C) (γ s₀).2 ≠ 0 →
        StrictMono fun s ↦ K * ((γ s).2.fst + (γ s).2.snd) - F (γ s) := by
  filter_upwards [hW.eventually_forall_mvfderiv_apply_lt_mul_add hC hWc hF hF₀ hF₁ hF₂ hX₀ hX₁ hX₂]
    with K hK γ hγ s₀ h₀ hgrad₀
  -- The derivative of `u + v` along `γ` is the sum of the coordinates of the base component.
  set ℓ : WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ := WithLp.fstL 2 ℝ ℝ ℝ + WithLp.sndL 2 ℝ ℝ ℝ
  have hd (s : ℝ) : HasDerivAt (fun s ↦ K * ((γ s).2.fst + (γ s).2.snd) - F (γ s))
      (K * ((W (γ s) : E × WithLp 2 (ℝ × ℝ)).2.fst + (W (γ s) : E × WithLp 2 (ℝ × ℝ)).2.snd) -
        mvfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) F (γ s) (W (γ s))) s := by
    have hℓ : HasDerivAt (fun s ↦ ℓ (γ s).2) (ℓ (W (γ s) : E × WithLp 2 (ℝ × ℝ)).2) s :=
      ℓ.hasFDerivAt.comp_hasDerivAt s (hγ.hasDerivAt_snd s)
    simp only [ℓ, FunLike.coe_add, Pi.add_apply, WithLp.fstL_apply,
      WithLp.sndL_apply] at hℓ
    exact (hℓ.const_mul K).sub
      (Manifold.hasDerivAt_comp_curve ((hF (γ s)).mdifferentiableAt one_ne_zero) (hγ s))
  exact strictMono_of_hasDerivAt_pos hd fun s ↦ sub_pos.2 <|
    hK (γ s) (hW.snd_mem_triangleBase hγ h₀ s) (hW.gradient_snd_ne_zero hγ hgrad₀ s)

/-- **The Lyapunov function along a triangle trajectory.** For all large `K`, along an integral
curve `γ` of the triangle field `W` from `(p, (0, 0))` at `-∞` to `(r, (1, 1))` at `+∞` which meets
the triangle, the function `K (u + v) - F` takes values strictly between its limits `-f₀ (p)` and
`2 K - f₂ (r)`. In particular `f₂ (r) - f₀ (p) < 2 K`. -/
theorem eventually_mul_add_sub_mem_Ioo :
    ∀ᶠ K in atTop, ∀ {p r : M} (γ : ℝ → M × WithLp 2 (ℝ × ℝ)), IsMIntegralCurve γ W →
      ∀ s₀, (γ s₀).2 ∈ triangleBase →
        Tendsto γ atBot (𝓝 (p, WithLp.toLp 2 (0, 0))) →
          Tendsto γ atTop (𝓝 (r, WithLp.toLp 2 (1, 1))) →
            ∀ s, K * ((γ s).2.fst + (γ s).2.snd) - F (γ s) ∈ Ioo (-f₀ p) (2 * K - f₂ r) := by
  filter_upwards [hW.eventually_strictMono_mul_add_sub hC hWc hF hF₀ hF₁ hF₂ hX₀ hX₁ hX₂]
    with K hK p r γ hγ s₀ h₀ hp hr s
  -- A trajectory of the base from the source to the sink stays in the open square `(0, 1)²`, so
  -- it never meets a vertex.
  have hsq := mem_Ioo_of_isIntegralCurve_triangleBasePotential hC (hW.isIntegralCurve_snd hγ)
    ((continuous_snd.tendsto _).comp hp) ((continuous_snd.tendsto _).comp hr) s₀
  have hgrad₀ : ∇ (triangleBasePotential C) (γ s₀).2 ≠ 0 := fun h ↦ by
    rcases (gradient_triangleBasePotential_eq_zero_iff hC.ne' h₀).1 h with h | h | h <;>
      · rw [h] at hsq
        norm_num at hsq
  have hmono := hK γ hγ s₀ h₀ hgrad₀
  have hL : Continuous fun z : M × WithLp 2 (ℝ × ℝ) ↦ K * (z.2.fst + z.2.snd) - F z := by
    have := hF.continuous
    fun_prop
  -- The limits of the Lyapunov function along `γ` are its values at the two ends.
  have hbot : Tendsto (fun s ↦ K * ((γ s).2.fst + (γ s).2.snd) - F (γ s)) atBot (𝓝 (-f₀ p)) := by
    have hv : K * ((WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))).fst +
        (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))).snd) - F (p, WithLp.toLp 2 (0, 0)) = -f₀ p := by
      rw [hF₀.self_of_nhds p, WithLp.toLp_fst, WithLp.toLp_snd]
      ring
    exact hv ▸ (hL.tendsto (p, WithLp.toLp 2 (0, 0))).comp hp
  have htop : Tendsto (fun s ↦ K * ((γ s).2.fst + (γ s).2.snd) - F (γ s)) atTop
      (𝓝 (2 * K - f₂ r)) := by
    have hv : K * ((WithLp.toLp 2 ((1 : ℝ), (1 : ℝ))).fst +
        (WithLp.toLp 2 ((1 : ℝ), (1 : ℝ))).snd) - F (r, WithLp.toLp 2 (1, 1)) = 2 * K - f₂ r := by
      rw [hF₂.self_of_nhds r, WithLp.toLp_fst, WithLp.toLp_snd]
      ring
    exact hv ▸ (hL.tendsto (r, WithLp.toLp 2 (1, 1))).comp hr
  exact ⟨(hmono.monotone.le_of_tendsto hbot (s - 1)).trans_lt (hmono (by linarith)),
    (hmono (by linarith : s < s + 1)).trans_le (hmono.monotone.ge_of_tendsto htop (s + 1))⟩

end Lyapunov

/-- An interpolation of three `C¹` functions over the triangle: a `C¹` function on `M × ℝ²` equal
to `f₀` where `u, v ≤ 1 / 3`, to `f₁` where `2 / 3 ≤ u` and `v ≤ 1 / 3`, and to `f₂` where
`2 / 3 ≤ u, v`. -/
private theorem exists_contMDiff_interpolation {f₀ f₁ f₂ : M → ℝ}
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₀) (hf₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₁)
    (hf₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₂) :
    ∃ F : M × WithLp 2 (ℝ × ℝ) → ℝ, ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) 𝓘(ℝ) 1 F ∧
      (∀ x b, b.fst ≤ 1 / 3 → b.snd ≤ 1 / 3 → F (x, b) = f₀ x) ∧
      (∀ x b, 2 / 3 ≤ b.fst → b.snd ≤ 1 / 3 → F (x, b) = f₁ x) ∧
      (∀ x b, 2 / 3 ≤ b.fst → 2 / 3 ≤ b.snd → F (x, b) = f₂ x) := by
  -- Interpolate: `F (x, (u, v)) = f₀ x + ρ (3 u - 1) (f₁ x - f₀ x) + ρ (3 v - 1) (f₂ x - f₁ x)`
  -- for the smooth transition `ρ` from `0` to `1`.
  set ρ := Real.smoothTransition
  set Φ : ℝ × ℝ × ℝ × WithLp 2 (ℝ × ℝ) → ℝ := fun w ↦
    w.1 + ρ (3 * w.2.2.2.fst - 1) * (w.2.1 - w.1) + ρ (3 * w.2.2.2.snd - 1) * (w.2.2.1 - w.2.1)
  have hΦ : ContDiff ℝ 1 Φ := by
    have hρ : ContDiff ℝ 1 ρ := Real.smoothTransition.contDiff
    have hu : ContDiff ℝ 1 fun w : ℝ × ℝ × ℝ × WithLp 2 (ℝ × ℝ) ↦ w.2.2.2.fst :=
      (WithLp.fstL 2 ℝ ℝ ℝ).contDiff.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
    have hv : ContDiff ℝ 1 fun w : ℝ × ℝ × ℝ × WithLp 2 (ℝ × ℝ) ↦ w.2.2.2.snd :=
      (WithLp.sndL 2 ℝ ℝ ℝ).contDiff.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
    exact (contDiff_fst.add ((hρ.comp ((contDiff_const.mul hu).sub contDiff_const)).mul
      ((contDiff_fst.comp contDiff_snd).sub contDiff_fst))).add
        ((hρ.comp ((contDiff_const.mul hv).sub contDiff_const)).mul
          ((contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).sub
            (contDiff_fst.comp contDiff_snd)))
  set F : M × WithLp 2 (ℝ × ℝ) → ℝ := fun z ↦ Φ (f₀ z.1, f₁ z.1, f₂ z.1, z.2)
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) 𝓘(ℝ) 1 F :=
    hΦ.contMDiff.comp ((hf₀.comp contMDiff_fst).prodMk_space ((hf₁.comp contMDiff_fst).prodMk_space
      ((hf₂.comp contMDiff_fst).prodMk_space contMDiff_snd)))
  have hρ₀ {t : ℝ} (ht : t ≤ 1 / 3) : ρ (3 * t - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hρ₁ {t : ℝ} (ht : 2 / 3 ≤ t) : ρ (3 * t - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hF₀ (x : M) (b : WithLp 2 (ℝ × ℝ)) (hu : b.fst ≤ 1 / 3) (hv : b.snd ≤ 1 / 3) :
      F (x, b) = f₀ x := by
    simp [F, Φ, hρ₀ hu, hρ₀ hv]
  have hF₁ (x : M) (b : WithLp 2 (ℝ × ℝ)) (hu : 2 / 3 ≤ b.fst) (hv : b.snd ≤ 1 / 3) :
      F (x, b) = f₁ x := by
    simp [F, Φ, hρ₁ hu, hρ₀ hv]
  have hF₂ (x : M) (b : WithLp 2 (ℝ × ℝ)) (hu : 2 / 3 ≤ b.fst) (hv : 2 / 3 ≤ b.snd) :
      F (x, b) = f₂ x := by
    simp [F, Φ, hρ₁ hu, hρ₁ hv]
  exact ⟨F, hF, hF₀, hF₁, hF₂⟩

/-- **Existence of a strict Lyapunov function for a triangle field.** Let `W` be a continuous
triangle field from `X₀` through `X₁` to `X₂` at rate `C > 0`, and let `f₀`, `f₁` and `f₂` be `C¹`
functions that do not increase along `X₀`, `X₁` and `X₂`. Then there is a `C¹` function `F` on
`M × ℝ²`, equal to `f₀` where `u, v ≤ 1 / 3`, to `f₁` where `2 / 3 ≤ u` and `v ≤ 1 / 3`, and to
`f₂` where `2 / 3 ≤ u, v`, such that for all large `K` the function `K (u + v) - F` strictly
increases along every integral curve of `W` meeting the triangle away from its vertices, and along
every such curve from `(p, (0, 0))` at `-∞` to `(r, (1, 1))` at `+∞` takes values strictly between
`-f₀ (p)` and `2 K - f₂ (r)`. -/
theorem exists_strictMono_mul_add_sub [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M] {f₀ f₁ f₂ : M → ℝ}
    {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
    {W : (z : M × WithLp 2 (ℝ × ℝ)) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) z}
    (hW : IsTriangleField X₀ X₁ X₂ C W) (hC : 0 < C)
    (hWc : Continuous fun z ↦ (⟨z, W z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ)))
      (M × WithLp 2 (ℝ × ℝ))))
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₀) (hf₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₁)
    (hf₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 f₂)
    (hX₀ : ∀ x, mvfderiv 𝓘(ℝ, E) f₀ x (X₀ x) ≤ 0) (hX₁ : ∀ x, mvfderiv 𝓘(ℝ, E) f₁ x (X₁ x) ≤ 0)
    (hX₂ : ∀ x, mvfderiv 𝓘(ℝ, E) f₂ x (X₂ x) ≤ 0) :
    ∃ F : M × WithLp 2 (ℝ × ℝ) → ℝ, ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, WithLp 2 (ℝ × ℝ))) 𝓘(ℝ) 1 F ∧
      (∀ x b, b.fst ≤ 1 / 3 → b.snd ≤ 1 / 3 → F (x, b) = f₀ x) ∧
      (∀ x b, 2 / 3 ≤ b.fst → b.snd ≤ 1 / 3 → F (x, b) = f₁ x) ∧
      (∀ x b, 2 / 3 ≤ b.fst → 2 / 3 ≤ b.snd → F (x, b) = f₂ x) ∧
      ∀ᶠ K in atTop,
        (∀ γ : ℝ → M × WithLp 2 (ℝ × ℝ), IsMIntegralCurve γ W → ∀ s₀,
          (γ s₀).2 ∈ triangleBase → ∇ (triangleBasePotential C) (γ s₀).2 ≠ 0 →
            StrictMono fun s ↦ K * ((γ s).2.fst + (γ s).2.snd) - F (γ s)) ∧
        ∀ {p r : M} (γ : ℝ → M × WithLp 2 (ℝ × ℝ)), IsMIntegralCurve γ W →
          ∀ s₀, (γ s₀).2 ∈ triangleBase →
            Tendsto γ atBot (𝓝 (p, WithLp.toLp 2 (0, 0))) →
              Tendsto γ atTop (𝓝 (r, WithLp.toLp 2 (1, 1))) →
                ∀ s, K * ((γ s).2.fst + (γ s).2.snd) - F (γ s) ∈ Ioo (-f₀ p) (2 * K - f₂ r) := by
  obtain ⟨F, hF, hF₀, hF₁, hF₂⟩ := exists_contMDiff_interpolation hf₀ hf₁ hf₂
  -- The three conditions hold on neighbourhoods of the three vertices.
  have hfst := (WithLp.continuous_fst 2 ℝ ℝ).tendsto
  have hsnd := (WithLp.continuous_snd 2 ℝ ℝ).tendsto
  have hF₀' : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))), ∀ x, F (x, b) = f₀ x := by
    filter_upwards [(hfst _).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)),
      (hsnd _).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with b hu hv x
    exact hF₀ x b hu.le hv.le
  have hF₁' : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((1 : ℝ), (0 : ℝ))), ∀ x, F (x, b) = f₁ x := by
    filter_upwards [(hfst _).eventually (lt_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)),
      (hsnd _).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with b hu hv x
    exact hF₁ x b hu.le hv.le
  have hF₂' : ∀ᶠ b in 𝓝 (WithLp.toLp 2 ((1 : ℝ), (1 : ℝ))), ∀ x, F (x, b) = f₂ x := by
    filter_upwards [(hfst _).eventually (lt_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1)),
      (hsnd _).eventually (lt_mem_nhds (by norm_num : (2 / 3 : ℝ) < 1))] with b hu hv x
    exact hF₂ x b hu.le hv.le
  exact ⟨F, hF, hF₀, hF₁, hF₂,
    (hW.eventually_strictMono_mul_add_sub hC hWc hF hF₀' hF₁' hF₂' hX₀ hX₁ hX₂).and
      (hW.eventually_mul_add_sub_mem_Ioo hC hWc hF hF₀' hF₁' hF₂' hX₀ hX₁ hX₂)⟩

end IsTriangleField

end TauCeti
