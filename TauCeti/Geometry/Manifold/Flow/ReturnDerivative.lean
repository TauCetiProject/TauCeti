/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Transition
public import TauCeti.LinearAlgebra.Eigenspace.Range
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import TauCeti.LinearAlgebra.Charpoly.Comp

/-!
# Derivatives of return germs

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold, and let `p` be a point
returning to itself at time `T₀`. For a function `g` with `dg_p (v p) ≠ 0`, whose level through `p`
is a local section transverse to `v`, the return branch `P_p = TauCeti.flowTransition v g T₀ p`
flows every point near `p` back into that section. This file studies its derivative
`DP_p : T_p M → T_p M` at `p`, the linearized return map `TauCeti.returnDerivative v g T₀ p`.

The derivative of a transition kills the field (`TauCeti.mfderiv_flowTransition_apply_eq_zero`),
since a transition is constant along flow lines, and lands in the kernel of the derivative of the
function cutting out the target section (`TauCeti.mvfderiv_comp_mfderiv_flowTransition`). For a
return branch, `DP_p` is therefore zero on the line spanned by `v p` and maps `T_p M` into the
tangent space `ker dg_p` of the section (`TauCeti.range_returnDerivative_le_ker`). Its restriction
to `ker dg_p` is the normal return derivative `TauCeti.normalReturnDerivative`, the derivative of
the return map of the section. The generalized eigenvectors of `DP_p` for a nonzero eigenvalue lie
in `ker dg_p` (`TauCeti.genEigenspace_returnDerivative_le_ker`), so the nonzero eigenvalues of the
normal return derivative are those of `DP_p` (`TauCeti.hasEigenvalue_normalReturnDerivative_iff`).
The derivative of the time-`0` transition to a section through `p` is the projection of `T_p M`
onto `ker dg_p` along `v p` (`TauCeti.mfderiv_flowTransition_zero_apply`). It comes from the
derivative `w ↦ w + dτ_p(w) • v p` of `z ↦ flowOf v (τ z) z` for a time `τ` vanishing at `p`
(`TauCeti.hasMFDerivAt_flowOf_comp_of_eq_zero` in `TauCeti.Geometry.Manifold.Flow.Basic`).

Derivatives of transitions compose as the transitions do (`TauCeti.mfderiv_flowTransition_comp`).
If the flow carries `p` to `q` at time `T`, the transition `h` from the section through `p` to a
section through `q` therefore intertwines the derivatives of the return branches,
`Dh ∘ DP_p = DP_q ∘ Dh` (`TauCeti.mfderiv_flowTransition_semiconj`). The derivative
`Dh` is not invertible, as it kills `v p`, so this does not by itself conjugate `DP_p` to `DP_q`.
The reverse transition `h'` repairs this: `Dh' ∘ Dh` and `Dh ∘ Dh'` are the derivatives of the
time-`0` transitions onto the two sections, which `DP_p` and `DP_q` absorb. Hence
`DP_p = Dh' ∘ (DP_q ∘ Dh)` and `DP_q = (DP_q ∘ Dh) ∘ Dh'`, so the two derivatives have the same
characteristic polynomial (`TauCeti.charpoly_mfderiv_flowTransition_eq`), by
`LinearMap.charpoly_comp_comm`. This is the linear content of the conjugacy
`P_q = h ∘ P_p ∘ h⁻¹` of `TauCeti.eventually_flowTransition_eq_conj`: the spectrum of the return
derivative `DP_p`, and in particular whether `1` is an eigenvalue of `DP_p`
(`TauCeti.hasEigenvalue_mfderiv_flowTransition_iff`), depend neither on the section nor on the
base point on the orbit. Since the `k`-fold iterate of a return branch is the return branch at time
`k * T₀`, the same holds for every iterate (`TauCeti.charpoly_mfderiv_iterate_flowTransition_eq`),
and the linearized return map at time `k * T₀` is the `k`-th power of the one at time `T₀`
(`TauCeti.returnDerivative_natCast_mul`).

On the tangent space of the source section the derivative of the reverse transition is a left
inverse of `Dh` (`TauCeti.mfderiv_flowTransition_neg_apply_mfderiv_flowTransition`). So `Dh`
restricts to an isomorphism between the generalized eigenspaces of `DP_p` and `DP_q` for every
nonzero eigenvalue and every exponent
(`TauCeti.exists_linearEquiv_genEigenspace_returnDerivative`): the geometric and algebraic
multiplicities of the nonzero eigenvalues do not depend on the section or the base point
(`TauCeti.finrank_genEigenspace_returnDerivative_eq`), and neither does the eigenvalue-one test
for the normal return derivative (`TauCeti.hasEigenvalue_one_normalReturnDerivative_iff`).

As in `TauCeti.Geometry.Manifold.Flow.Transition`, `T₀` need not be the least period, and the
return branch need not be the first return to the section.

## Main definitions

* `TauCeti.returnDerivative v g T₀ p`: the linearized return map, the derivative at `p` of the
  return branch at time `T₀` of the section `{g = g p}`.
* `TauCeti.normalReturnDerivative v g T₀ p h`: the normal return derivative, the restriction of
  the linearized return map to the tangent space `ker dg_p` of the section.

## Main results

* `TauCeti.mfderiv_flowTransition_apply_eq_zero`: the derivative of a transition kills the field.
* `TauCeti.mvfderiv_comp_mfderiv_flowTransition`: the derivative of a transition lands in the
  tangent space of the target section; `TauCeti.range_returnDerivative_le_ker` is the same for the
  linearized return map.
* `TauCeti.mfderiv_flowTransition_comp`: derivatives of transitions compose.
* `TauCeti.mfderiv_flowTransition_zero_apply`: the derivative of the time-`0` transition is the
  projection onto the tangent space of the section along the field.
* `TauCeti.mfderiv_flowTransition_neg_apply_mfderiv_flowTransition`: on the tangent space of the
  source section, the derivative of the reverse transition is a left inverse.
* `TauCeti.hasEigenvalue_normalReturnDerivative_iff`: the normal return derivative and the
  linearized return map have the same nonzero eigenvalues.
* `TauCeti.mfderiv_flowTransition_semiconj`: transitions intertwine the derivatives of
  return germs; `TauCeti.returnDerivative_comp_mfderiv_flowTransition` is the same for the
  linearized return maps, as an identity of linear maps.
* `TauCeti.charpoly_mfderiv_flowTransition_eq`: the characteristic polynomial of the derivative of
  a return germ is independent of the section and the base point.
* `TauCeti.hasEigenvalue_mfderiv_flowTransition_iff`: so are its eigenvalues.
* `TauCeti.charpoly_mfderiv_iterate_flowTransition_eq`: the same for every iterate.
* `TauCeti.exists_linearEquiv_genEigenspace_returnDerivative`,
  `TauCeti.finrank_genEigenspace_returnDerivative_eq`: the nonzero generalized eigenspaces of
  linearized return maps at two points of a periodic orbit are isomorphic;
  `TauCeti.exists_linearEquiv_eigenspace_returnDerivative` and
  `TauCeti.finrank_eigenspace_returnDerivative_eq` are the same for eigenspaces.
* `TauCeti.hasEigenvalue_one_normalReturnDerivative_iff`: the eigenvalue-one test for the normal
  return derivative does not depend on the section or the base point.
* `TauCeti.returnDerivative_natCast_mul`: the linearized return map of an iterate.

## References

* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS Graduate Studies in
  Mathematics 140, 2012, §12.2 (the Poincaré map and its derivative; Theorem 12.4).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1
  (the Poincaré maps of a closed orbit at different sections are conjugate).
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g g' : M → ℝ} {T T' T₀ : ℝ} {p q r : M}

/-- The derivative at `p` of the return branch `flowTransition v g T₀ p` at time `T₀` of the
section `{g = g p}`, as an endomorphism of `T_pM`: the linearized return map. When `p` returns to
itself at time `T₀` and the section is transverse to `v`, it takes values in the tangent space
`ker dg_p` of the section (`TauCeti.range_returnDerivative_le_ker`), and its nonzero eigenvalues
are those of its restriction `TauCeti.normalReturnDerivative` to that tangent space
(`TauCeti.hasEigenvalue_normalReturnDerivative_iff`). -/
def returnDerivative (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T₀ : ℝ) (p : M) :
    Module.End ℝ (TangentSpace I p) :=
  -- All tangent spaces of `M` are the model space `E`, so the derivative, which lands in the
  -- tangent space at `flowTransition v g T₀ p p`, is read as an endomorphism of `T_pM`.
  (show TangentSpace I p →L[ℝ] TangentSpace I p from
    mfderiv I I (flowTransition v g T₀ p) p).toLinearMap

@[simp]
theorem returnDerivative_apply (w : TangentSpace I p) :
    returnDerivative v g T₀ p w = mfderiv I I (flowTransition v g T₀ p) p w :=
  (rfl)

/-- The normal return derivative: the restriction of the linearized return map
`TauCeti.returnDerivative v g T₀ p` to the tangent space `ker dg_p` of the section `{g = g p}`,
given that the linearized return map takes values there. When `p` returns to itself at time `T₀`
and the section is transverse to `v`, this holds by `TauCeti.range_returnDerivative_le_ker`. -/
def normalReturnDerivative (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T₀ : ℝ) (p : M)
    (h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)) :
    Module.End ℝ (LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)) :=
  (returnDerivative v g T₀ p).restrict fun w _ ↦ h (LinearMap.mem_range_self _ w)

@[simp]
theorem coe_normalReturnDerivative_apply
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    (w : LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)) :
    (normalReturnDerivative v g T₀ p h w : TangentSpace I p) = returnDerivative v g T₀ p w :=
  (rfl)

/-- **The normal return derivative has the nonzero eigenvalues of the linearized return map.** -/
theorem hasEigenvalue_normalReturnDerivative_iff
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} {μ : ℝ} (hμ : μ ≠ 0) :
    (normalReturnDerivative v g T₀ p h).HasEigenvalue μ ↔
      (returnDerivative v g T₀ p).HasEigenvalue μ :=
  Module.End.hasEigenvalue_restrict_iff_of_range_le h hμ

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
include hv

section Transition

variable (hT : (T, p) ∈ flowDomain v) (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hT hg hgv

/-- **The derivative of a transition kills the field.** The transition to a section through
`flowOf v T p` is constant along the trajectory through `p`, so its derivative at `p` vanishes on
the field `v p`. -/
theorem mfderiv_flowTransition_apply_eq_zero :
    mfderiv I I (flowTransition v g T p) p (v p) = 0 := by
  have hconst : flowTransition v g T p ∘ (fun s ↦ flowOf v s p) =ᶠ[𝓝 0]
      fun _ ↦ flowOf v T p :=
    eventually_flowTransition_flowOf hv hT hg hgv
  -- The tangent spaces at `x` and at `p` are both the model space, so this equation is well
  -- typed; it holds by substituting `x = p`.
  have hvp : ∀ x, x = p → v x = v p := by
    rintro x rfl
    rfl
  -- The velocity of the trajectory at time `0` is `v p`.
  have hvel : mfderiv 𝓘(ℝ) I (fun s ↦ flowOf v s p) 0 (1 : ℝ) = v p :=
    Manifold.curveVelocity_apply.symm.trans <|
      (curveVelocity_flowOf hv (mem_flowDomain_zero hv p)).trans (hvp _ (flowOf_zero hv p))
  have hzero : mfderiv 𝓘(ℝ) I (flowTransition v g T p ∘ fun s ↦ flowOf v s p) 0 (1 : ℝ) = 0 := by
    rw [hconst.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
    exact zero_apply _
  rw [← hvel]
  exact (mfderiv_comp_apply_of_eq (0 : ℝ) (mdifferentiableAt_flowTransition hv hT hg hgv)
    (mdifferentiableAt_flowOf hv (mem_flowDomain_zero hv p)) (flowOf_zero hv p) (1 : ℝ)).symm.trans
    hzero

/-- **The derivative of a transition lands in the tangent space of the section.** The transition
carries a neighbourhood of `p` into the level of `g` through `flowOf v T p`, so the derivative of
`g` vanishes on the range of the derivative of the transition. -/
theorem mvfderiv_comp_mfderiv_flowTransition :
    mvfderiv I g (flowOf v T p) ∘L mfderiv I I (flowTransition v g T p) p = 0 := by
  have hconst : g ∘ flowTransition v g T p =ᶠ[𝓝 p] fun _ ↦ g (flowOf v T p) := by
    filter_upwards [eventually_flowHittingTime hv hT hg hgv] with z hz
    rw [comp_apply, flowTransition_apply]
    exact hz.2
  ext w
  have hzero : mvfderiv I (g ∘ flowTransition v g T p) p w = 0 := by
    simp [mvfderiv, hconst.mfderiv_eq]
  exact (mvfderiv_comp_apply_of_eq p (hg.mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_flowTransition hv hT hg hgv) (flowTransition_self ..) w).symm.trans hzero

end Transition

/-- **Derivatives of transitions compose.** If the flow carries `p` to `q` at time `T` and `q` to
`r` at time `T'`, then the derivative at `p` of the transition to a section through `q`, followed
by the derivative at `q` of the transition to a section through `r`, is the derivative at `p` of
the transition to the section through `r` at time `T + T'`. -/
theorem mfderiv_flowTransition_comp (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g q) (hgv : mvfderiv I g q (v q) ≠ 0)
    (hT' : (T', q) ∈ flowDomain v) (hr : flowOf v T' q = r) (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' r)
    (hg'v : mvfderiv I g' r (v r) ≠ 0) :
    mfderiv I I (flowTransition v g' T' q) q ∘L mfderiv I I (flowTransition v g T p) p =
      mfderiv I I (flowTransition v g' (T + T') p) p := by
  have hh := mdifferentiableAt_flowTransition hv hT (by rwa [hq]) (by rwa [hq])
  have hh' := mdifferentiableAt_flowTransition hv hT' (by rwa [hr]) (by rwa [hr])
  ext w
  have hcomp := flowTransition_comp_eventuallyEq hv hT hq hg hgv hT' hr hg' hg'v
  exact (mfderiv_comp_apply_of_eq p hh' hh (by rw [flowTransition_self, hq]) w).symm.trans
    (DFunLike.congr_fun hcomp.mfderiv_eq w)

/-- **The derivative of the time-zero transition.** For a section `{g = g p}` through `p`
transverse to `v`, the derivative at `p` of the transition at time `0` to this section is the
projection onto its tangent space `ker dg_p` along `v p`. -/
theorem mfderiv_flowTransition_zero_apply (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) (w : TangentSpace I p) :
    mfderiv I I (flowTransition v g 0 p) p w =
      w - (mvfderiv I g p w / mvfderiv I g p (v p)) • v p := by
  have h0 : ((0 : ℝ), p) ∈ flowDomain v := mem_flowDomain_zero hv p
  have hp0 : flowOf v 0 p = p := flowOf_zero hv p
  have hg0 : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v 0 p) := by rwa [hp0]
  have hgv0 : mvfderiv I g (flowOf v 0 p) (v (flowOf v 0 p)) ≠ 0 := by rwa [hp0]
  have hτ := mdifferentiableAt_flowHittingTime hv h0 hg0 hgv0
  have hD := (hasMFDerivAt_flowOf_comp_of_eq_zero hv hτ.hasMFDerivAt
    (flowHittingTime_self v g 0 p)).mfderiv
  -- The derivative of the hitting time is read as a real number, so that it can scale `v p`.
  have hπ : ∀ u : TangentSpace I p, @Eq E (mfderiv I I (flowTransition v g 0 p) p u)
      (u + (show ℝ from mfderiv I 𝓘(ℝ) (flowHittingTime v g 0 p) p u) • v p) := fun u ↦ by
    rw [flowTransition_def, hD]
    -- The evaluation of `id + dτ.smulRight (v p)` at `u` is closed definitionally: `dτ` takes
    -- values in the tangent space of `ℝ` at `τ p` rather than in `ℝ`, so the goal does not
    -- typecheck at the transparency `rw` and `simp` use for `add_apply` and `smulRight_apply`.
    rfl
  have hker : mvfderiv I g (flowOf v 0 p) (mfderiv I I (flowTransition v g 0 p) p w) = 0 :=
    DFunLike.congr_fun (mvfderiv_comp_mfderiv_flowTransition hv h0 hg0 hgv0) w
  rw [hp0, hπ, map_add, map_smul, smul_eq_mul] at hker
  have hτw : @Eq ℝ (mfderiv I 𝓘(ℝ) (flowHittingTime v g 0 p) p w)
      (-(mvfderiv I g p w / mvfderiv I g p (v p))) := by
    have key : ∀ a b t : ℝ, b ≠ 0 → a + t * b = 0 → t = -(a / b) := fun a b t hb h ↦ by
      field_simp
      linear_combination h
    exact key _ _ _ hgv hker
  rw [hπ, hτw, neg_smul, ← sub_eq_add_neg]

/-- On the tangent space of the section through `p`, the derivative of the time-zero transition
is the identity. -/
theorem mfderiv_flowTransition_zero_apply_of_mvfderiv_eq_zero (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) {w : TangentSpace I p} (hw : mvfderiv I g p w = 0) :
    mfderiv I I (flowTransition v g 0 p) p w = w := by
  rw [mfderiv_flowTransition_zero_apply hv hg hgv, hw, zero_div, zero_smul, sub_zero]

section Inverse

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0) (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q)
  (hg'v : mvfderiv I g' q (v q) ≠ 0)
include hT hq hg hgv hg' hg'v

/-- The left-inverse property of the reverse transition, with the reverse time `S = -T` given as
a separate variable. -/
private theorem mfderiv_flowTransition_apply_mfderiv_flowTransition_of_add_eq_zero {S : ℝ}
    (hS : T + S = 0) {w : TangentSpace I p} (hw : mvfderiv I g p w = 0) :
    mfderiv I I (flowTransition v g S q) q (mfderiv I I (flowTransition v g' T p) p w) = w := by
  obtain rfl : S = -T := by linarith
  have hneg : (-T, q) ∈ flowDomain v := hq ▸ neg_mem_flowDomain_flowOf hv hT
  have hback : flowOf v (-T) q = p := hq ▸ flowOf_neg_flowOf hv hT
  have hcomp := DFunLike.congr_fun
    (mfderiv_flowTransition_comp hv hT hq hg' hg'v hneg hback hg hgv) w
  rw [add_neg_cancel] at hcomp
  exact hcomp.trans (mfderiv_flowTransition_zero_apply_of_mvfderiv_eq_zero hv hg hgv hw)

/-- **The derivative of the reverse transition is a left inverse on the section.** If the flow
carries `p` to `q` at time `T`, the derivative at `p` of the transition `h` to a section through
`q`, followed by the derivative at `q` of the reverse transition at time `-T` back to the section
`{g = g p}`, is the identity on the tangent space `ker dg_p` of that section. -/
theorem mfderiv_flowTransition_neg_apply_mfderiv_flowTransition {w : TangentSpace I p}
    (hw : mvfderiv I g p w = 0) :
    mfderiv I I (flowTransition v g (-T) q) q (mfderiv I I (flowTransition v g' T p) p w) = w :=
  mfderiv_flowTransition_apply_mfderiv_flowTransition_of_add_eq_zero hv hT hq hg hgv hg' hg'v
    (add_neg_cancel T) hw

/-- **The derivative of a transition is injective on the section.** -/
theorem mfderiv_flowTransition_injOn :
    InjOn (mfderiv I I (flowTransition v g' T p) p) {w | mvfderiv I g p w = 0} :=
  fun _ hw _ hu h ↦ by
    rw [← mfderiv_flowTransition_neg_apply_mfderiv_flowTransition hv hT hq hg hgv hg' hg'v hw,
      h, mfderiv_flowTransition_neg_apply_mfderiv_flowTransition hv hT hq hg hgv hg' hg'v hu]

end Inverse

/-- If `p` returns to itself at time `T₀`, the linearized return map of a transverse section
through `p` takes values in the tangent space `ker dg_p` of the section. -/
theorem range_returnDerivative_le_ker (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0) :
    LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) :=
  fun _ ⟨w, hw⟩ ↦ by
    have h : mvfderiv I g (flowOf v T₀ p) (mfderiv I I (flowTransition v g T₀ p) p w) = 0 :=
      DFunLike.congr_fun
        (mvfderiv_comp_mfderiv_flowTransition hv hP (by rwa [hp]) (by rwa [hp])) w
    rw [hp] at h
    rw [← hw]
    exact h

/-- The generalized eigenvectors of the linearized return map for a nonzero eigenvalue lie in the
tangent space `ker dg_p` of the section. -/
theorem genEigenspace_returnDerivative_le_ker (hP : (T₀, p) ∈ flowDomain v)
    (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
    {μ : ℝ} (hμ : μ ≠ 0) (k : ℕ∞) :
    (returnDerivative v g T₀ p).genEigenspace μ k ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) :=
  Module.End.genEigenspace_le_of_range_le (range_returnDerivative_le_ker hv hP hp hg hgv) hμ k

/-- The eigenvectors of the linearized return map for a nonzero eigenvalue lie in the tangent space
`ker dg_p` of the section. -/
theorem eigenspace_returnDerivative_le_ker (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    (returnDerivative v g T₀ p).eigenspace μ ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) :=
  genEigenspace_returnDerivative_le_ker hv hP hp hg hgv hμ 1

/-- **The linearized return map of an iterate is the iterate of the linearized return map.** If
`p` returns to itself at time `T₀`, then for `k ≠ 0` the linearized return map at time `k * T₀` of
a transverse section through `p` is the `k`-th power of the one at time `T₀`. -/
theorem returnDerivative_natCast_mul (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    returnDerivative v g (k * T₀) p = returnDerivative v g T₀ p ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  clear hk
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp (k + 1)
    have hmul : ((k + 1 + 1 : ℕ) : ℝ) * T₀ = ((k + 1 : ℕ) : ℝ) * T₀ + T₀ := by
      push_cast
      ring
    have hcomp := mfderiv_flowTransition_comp hv hkP hkp hg hgv hP hp hg hgv
    rw [hmul, pow_succ', ← ih]
    exact LinearMap.ext fun w ↦ (DFunLike.congr_fun hcomp w).symm

section Return

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hP : (T₀, p) ∈ flowDomain v)
  (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0)
include hT hq hP hp hg hgv hg' hg'v

/-- **Transitions intertwine the derivatives of return germs.** If the flow carries `p` to `q` at
time `T` and `p` returns to itself at time `T₀`, then the derivative `Dh` of the transition from a
section through `p` to a section through `q` satisfies `Dh ∘ DP_p = DP_q ∘ Dh`, where `P_p` and
`P_q` are the return branches at time `T₀` of these sections. -/
theorem mfderiv_flowTransition_semiconj :
    mfderiv I I (flowTransition v g' T p) p ∘L mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  rw [mfderiv_flowTransition_comp hv hP hp hg hgv hT hq hg' hg'v,
    mfderiv_flowTransition_comp hv hT hq hg' hg'v hQ hq' hg' hg'v, add_comm]

/-- **The characteristic polynomial of a return derivative is independent of the section and of
the base point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time
`T₀`, then the derivatives at `p` and at `q` of the return branches at time `T₀` of sections
through `p` and through `q` have the same characteristic polynomial. Taking `q = p` and `T = 0`,
two sections through the same point give return derivatives with the same characteristic
polynomial. -/
theorem charpoly_mfderiv_flowTransition_eq :
    (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap.charpoly =
      (mfderiv I I (flowTransition v g' T₀ q) q).toLinearMap.charpoly := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  have hback : flowOf v (-T) q = p := hq ▸ flowOf_neg_flowOf hv hT
  have hTback : (-T, q) ∈ flowDomain v := hq ▸ neg_mem_flowDomain_flowOf hv hT
  -- Write `A`, `B` for the two return derivatives, `h` for the derivative of the transition from
  -- `p` to `q` and `h'` for that of the reverse transition. Then `h' ∘ h` is the derivative of the
  -- time-`0` transition onto the section through `p`, which `A` absorbs on the left, and likewise
  -- `h ∘ h'` onto the section through `q`, absorbed by `B` on the right.
  have hh'h : mfderiv I I (flowTransition v g (-T) q) q ∘L
      mfderiv I I (flowTransition v g' T p) p = mfderiv I I (flowTransition v g 0 p) p := by
    rw [mfderiv_flowTransition_comp hv hT hq hg' hg'v hTback hback hg hgv, add_neg_cancel]
  have hA : mfderiv I I (flowTransition v g 0 p) p ∘L mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g T₀ p) p := by
    rw [mfderiv_flowTransition_comp hv hP hp hg hgv (mem_flowDomain_zero hv p) (flowOf_zero hv p)
      hg hgv, add_zero]
  have hhh' : mfderiv I I (flowTransition v g' T p) p ∘L
      mfderiv I I (flowTransition v g (-T) q) q = mfderiv I I (flowTransition v g' 0 q) q := by
    rw [mfderiv_flowTransition_comp hv hTback hback hg hgv hT hq hg' hg'v, neg_add_cancel]
  have hB : mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' 0 q) q =
      mfderiv I I (flowTransition v g' T₀ q) q := by
    rw [mfderiv_flowTransition_comp hv (mem_flowDomain_zero hv q) (flowOf_zero hv q) hg' hg'v hQ
      hq' hg' hg'v, zero_add]
  have hAeq : mfderiv I I (flowTransition v g T₀ p) p =
      mfderiv I I (flowTransition v g (-T) q) q ∘L
        (mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p) := by
    conv_lhs => rw [← hA, ← hh'h]
    refine (ContinuousLinearMap.comp_assoc _ _ _).trans ?_
    congr 1
    exact mfderiv_flowTransition_semiconj hv hT hq hP hp hg hgv hg' hg'v
  have hBeq : mfderiv I I (flowTransition v g' T₀ q) q =
      (mfderiv I I (flowTransition v g' T₀ q) q ∘L mfderiv I I (flowTransition v g' T p) p) ∘L
        mfderiv I I (flowTransition v g (-T) q) q := by
    conv_lhs => rw [← hB, ← hhh']
    exact (ContinuousLinearMap.comp_assoc _ _ _).symm
  -- Both tangent spaces are the model space `E`, so they have the same rank.
  have hrank : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ (TangentSpace I q) := rfl
  rw [hAeq]
  conv_rhs => rw [hBeq]
  -- `(f ∘L g).toLinearMap` is `f.toLinearMap ∘ₗ g.toLinearMap` by definition
  -- (`ContinuousLinearMap.toLinearMap_comp`). Rewriting with that lemma fails here, as the module
  -- structures on `TangentSpace I q` and on `TangentSpace I (flowTransition v g' T p p)` agree
  -- only after unfolding both to that of `E`.
  exact LinearMap.charpoly_comp_comm _ _ hrank

/-- **The eigenvalues of a return derivative are independent of the section and of the base
point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time `T₀`, then
`μ` is an eigenvalue of the derivative at `p` of the return branch of a section through `p` exactly
when it is one at `q` for a section through `q`. For `μ = 1`, whether `1` is an eigenvalue of the
full derivative `DP_p` on `T_p M` is independent of these choices; for the normal return
derivative on the section, see `TauCeti.hasEigenvalue_one_normalReturnDerivative_iff`. -/
theorem hasEigenvalue_mfderiv_flowTransition_iff (μ : ℝ) :
    Module.End.HasEigenvalue (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowTransition v g' T₀ q) q).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowTransition_eq hv hT hq hP hp hg hgv hg' hg'v]

/-- **The same holds for every iterate.** If the flow carries `p` to `q` at time `T` and `p`
returns to itself at time `T₀`, then for every `k` the derivatives at `p` and at `q` of the
`k`-fold iterates of the return branches at time `T₀` of sections through `p` and through `q`
have the same characteristic polynomial. -/
theorem charpoly_mfderiv_iterate_flowTransition_eq (k : ℕ) :
    (mfderiv I I (flowTransition v g T₀ p)^[k] p).toLinearMap.charpoly =
      (mfderiv I I (flowTransition v g' T₀ q)^[k] q).toLinearMap.charpoly := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [iterate_zero, mfderiv_id]
    -- Both sides are the characteristic polynomial of the identity of the model space `E`.
    rfl
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  rw [(flowTransition_iterate_eventuallyEq hv hP hp hg hgv hk).mfderiv_eq,
    (flowTransition_iterate_eventuallyEq hv hQ hq' hg' hg'v hk).mfderiv_eq]
  exact charpoly_mfderiv_flowTransition_eq hv hT hq hkP hkp hg hgv hg' hg'v

/-- **The linearized return maps along an orbit are conjugate.** If the flow carries `p` to `q`
at time `T` and `p` returns to itself at time `T₀`, the derivative `dh` of the transition between
transverse sections through `p` and through `q`, read as a linear map into `T_qM`, intertwines the
linearized return maps at time `T₀`: `dP_q ∘ dh = dh ∘ dP_p`. -/
theorem returnDerivative_comp_mfderiv_flowTransition :
    -- The derivative lands in the tangent space at `flowTransition v g' T p p`, which is `q` only
    -- propositionally; it is read as a map into the tangent space at `q`, which is the same `E`.
    returnDerivative v g' T₀ q ∘ₗ (show TangentSpace I p →L[ℝ] TangentSpace I q from
      mfderiv I I (flowTransition v g' T p) p).toLinearMap =
    (show TangentSpace I p →L[ℝ] TangentSpace I q from
      mfderiv I I (flowTransition v g' T p) p).toLinearMap ∘ₗ returnDerivative v g T₀ p :=
  have h := mfderiv_flowTransition_semiconj hv hT hq hP hp hg hgv hg' hg'v
  LinearMap.ext fun w ↦ (DFunLike.congr_fun h w).symm

/-- **The nonzero generalized eigenspaces of linearized return maps do not depend on the section or
the base point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time
`T₀`, then for every `μ ≠ 0` and every `k : ℕ∞` the generalized eigenspaces for `μ` and exponent
`k` of the linearized return maps at time `T₀` of transverse sections through `p` and through `q`
are isomorphic, through the derivative of the transition between the sections. -/
theorem exists_linearEquiv_genEigenspace_returnDerivative {μ : ℝ} (hμ : μ ≠ 0) (k : ℕ∞) :
    ∃ e : (returnDerivative v g T₀ p).genEigenspace μ k ≃ₗ[ℝ]
        (returnDerivative v g' T₀ q).genEigenspace μ k,
      ∀ w, (e w : TangentSpace I q) = mfderiv I I (flowTransition v g' T p) p w := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  have hneg : (-T, q) ∈ flowDomain v := hq ▸ neg_mem_flowDomain_flowOf hv hT
  have hback : flowOf v (-T) q = p := hq ▸ flowOf_neg_flowOf hv hT
  let f : (returnDerivative v g T₀ p).genEigenspace μ k →ₗ[ℝ]
      (returnDerivative v g' T₀ q).genEigenspace μ k :=
    (show TangentSpace I p →L[ℝ] TangentSpace I q from
      mfderiv I I (flowTransition v g' T p) p).toLinearMap.restrict fun _ hw ↦
        Module.End.mapsTo_genEigenspace_of_comp _ (returnDerivative_comp_mfderiv_flowTransition hv
          hT hq hP hp hg hgv hg' hg'v) μ k hw
  let f' : (returnDerivative v g' T₀ q).genEigenspace μ k →ₗ[ℝ]
      (returnDerivative v g T₀ p).genEigenspace μ k :=
    -- As in `returnDerivative_comp_mfderiv_flowTransition`, the derivative lands in the tangent
    -- space at `flowTransition v g (-T) q q`, which is `p` only propositionally; it is read as a
    -- map into the tangent space at `p`, which is the same `E`.
    (show TangentSpace I q →L[ℝ] TangentSpace I p from
      mfderiv I I (flowTransition v g (-T) q) q).toLinearMap.restrict fun _ hw ↦
        Module.End.mapsTo_genEigenspace_of_comp _ (returnDerivative_comp_mfderiv_flowTransition hv
          hneg hback hQ hq' hg' hg'v hg hgv) μ k hw
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, fun w ↦ rfl⟩
  · refine LinearMap.ext fun u ↦ Subtype.ext ?_
    exact mfderiv_flowTransition_apply_mfderiv_flowTransition_of_add_eq_zero hv hneg hback hg'
      hg'v hg hgv (neg_add_cancel T)
      (genEigenspace_returnDerivative_le_ker hv hQ hq' hg' hg'v hμ k u.2)
  · refine LinearMap.ext fun w ↦ Subtype.ext ?_
    exact mfderiv_flowTransition_neg_apply_mfderiv_flowTransition hv hT hq hg hgv hg' hg'v
      (genEigenspace_returnDerivative_le_ker hv hP hp hg hgv hμ k w.2)

/-- **The nonzero eigenspaces of linearized return maps do not depend on the section or the
base point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time `T₀`,
then for every `μ ≠ 0` the eigenspaces for `μ` of the linearized return maps at time `T₀` of
transverse sections through `p` and through `q` are isomorphic, through the derivative of the
transition between the sections. -/
theorem exists_linearEquiv_eigenspace_returnDerivative {μ : ℝ} (hμ : μ ≠ 0) :
    ∃ e : (returnDerivative v g T₀ p).eigenspace μ ≃ₗ[ℝ]
        (returnDerivative v g' T₀ q).eigenspace μ,
      ∀ w, (e w : TangentSpace I q) = mfderiv I I (flowTransition v g' T p) p w :=
  exists_linearEquiv_genEigenspace_returnDerivative hv hT hq hP hp hg hgv hg' hg'v hμ 1

/-- The nonzero generalized eigenspaces of the linearized return maps at time `T₀` of transverse
sections through two points of a periodic orbit have the same dimension. For `k = ⊤` these
dimensions are the algebraic multiplicities. -/
theorem finrank_genEigenspace_returnDerivative_eq {μ : ℝ} (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.finrank ℝ ((returnDerivative v g T₀ p).genEigenspace μ k) =
      Module.finrank ℝ ((returnDerivative v g' T₀ q).genEigenspace μ k) :=
  (exists_linearEquiv_genEigenspace_returnDerivative hv hT hq hP hp hg hgv hg' hg'v hμ k).choose
    |>.finrank_eq

/-- The nonzero eigenspaces of the linearized return maps at time `T₀` of transverse sections
through two points of a periodic orbit have the same dimension. -/
theorem finrank_eigenspace_returnDerivative_eq {μ : ℝ} (hμ : μ ≠ 0) :
    Module.finrank ℝ ((returnDerivative v g T₀ p).eigenspace μ) =
      Module.finrank ℝ ((returnDerivative v g' T₀ q).eigenspace μ) :=
  finrank_genEigenspace_returnDerivative_eq hv hT hq hP hp hg hgv hg' hg'v hμ 1

/-- **The eigenvalue-one test for the normal return derivative does not depend on the section or
the base point.** The normal return derivative at time `T₀` of a transverse section through `p`
has eigenvalue `1` exactly when that of a transverse section through any point `q` of the orbit
does. -/
theorem hasEigenvalue_one_normalReturnDerivative_iff
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    {h' : LinearMap.range (returnDerivative v g' T₀ q) ≤
      LinearMap.ker (mvfderiv I g' q : TangentSpace I q →ₗ[ℝ] ℝ)} :
    (normalReturnDerivative v g T₀ p h).HasEigenvalue 1 ↔
      (normalReturnDerivative v g' T₀ q h').HasEigenvalue 1 := by
  rw [hasEigenvalue_normalReturnDerivative_iff one_ne_zero,
    hasEigenvalue_normalReturnDerivative_iff one_ne_zero]
  exact hasEigenvalue_mfderiv_flowTransition_iff hv hT hq hP hp hg hgv hg' hg'v 1

end Return

end TauCeti
