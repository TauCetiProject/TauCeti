/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Transition
public import TauCeti.LinearAlgebra.Eigenspace.Range

/-!
# Derivatives of return germs

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold whose flow carries `p`
back to itself at time `T₀`. A local transverse section through `p` is a level `{g = g p}` of a
function `g`, `C¹` at `p`, with `dg_p (v p) ≠ 0`, and the return branch
`P_p = TauCeti.flowTransition v g T₀ p` flows each point near `p` for its hitting time back into
this section. Its derivative at `p` is the linearized return map
`TauCeti.returnDerivative v g T₀ p`, an endomorphism of `T_pM`.

The germ-level statements of `TauCeti.Geometry.Manifold.Flow.Transition` are differentiated here.
The derivative of the time-`0` transition to a section through `p` is the projection of `T_pM`
onto the tangent space `ker dg_p` of the section along `v p`
(`TauCeti.mfderiv_flowTransition_zero_apply`). It comes from the derivative
`w ↦ w + dτ_p(w) • v p` of `z ↦ flowOf v (τ z) z` for a time `τ` vanishing at `p`
(`TauCeti.hasMFDerivAt_flowOf_comp_of_eq_zero` in `TauCeti.Geometry.Manifold.Flow.Basic`). The
derivative of a transition takes values in the tangent space of the target section
(`TauCeti.mvfderiv_mfderiv_flowTransition_eq_zero`), and on the tangent space of the source section
the derivative of the reverse transition is its left inverse
(`TauCeti.mfderiv_flowTransition_neg_apply_mfderiv_flowTransition`). If the flow carries `p` to
`q` at time `T`, the chain rule turns the conjugacy of return germs into
`dh ∘ dP_p = dP_q ∘ dh` for the transition `h` from a section through `p` to one through `q`
(`TauCeti.mfderiv_flowTransition_apply_mfderiv_flowTransition`).

Since `dP_p` maps `T_pM` into `ker dg_p` (`TauCeti.range_returnDerivative_le_ker`), its generalized
eigenvectors for a nonzero eigenvalue lie in `ker dg_p`
(`TauCeti.genEigenspace_returnDerivative_le_ker`), so its nonzero eigenvalues are those of the
normal return derivative `TauCeti.normalReturnDerivative`, the restriction of `dP_p` to the tangent
space of the section (`TauCeti.hasEigenvalue_normalReturnDerivative_iff`). On these generalized
eigenspaces `dh` is an isomorphism, with inverse the derivative of the reverse transition
(`TauCeti.exists_linearEquiv_genEigenspace_returnDerivative`). Hence the nonzero eigenvalues of the
linearized return map, with their geometric and algebraic multiplicities, and in particular the
test whether `1` is an eigenvalue, do not depend on the section or on the base point along the
orbit (`TauCeti.finrank_genEigenspace_returnDerivative_eq`,
`TauCeti.hasEigenvalue_returnDerivative_iff`, `TauCeti.hasEigenvalue_one_returnDerivative_iff`,
`TauCeti.hasEigenvalue_one_normalReturnDerivative_iff`). The linearized return map at time
`k * T₀` is the `k`-th power of the one at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), so
the same holds for every positive iterate.

As in `TauCeti.Geometry.Manifold.Flow.Transition`, `T₀` need not be the least period and the
return branch need not be the first return to the section.

## Main definitions

* `TauCeti.returnDerivative v g T₀ p`: the linearized return map, the derivative at `p` of the
  return branch at time `T₀` of the section `{g = g p}`.
* `TauCeti.normalReturnDerivative v g T₀ p h`: the normal return derivative, the restriction of
  the linearized return map to the tangent space `ker dg_p` of the section.

## Main results

* `TauCeti.mfderiv_flowTransition_zero_apply`: the derivative of the time-`0` transition is the
  projection onto the tangent space of the section along the field.
* `TauCeti.mvfderiv_mfderiv_flowTransition_eq_zero`: the derivative of a transition takes values
  in the tangent space of the target section; `TauCeti.range_returnDerivative_le_ker` is the same
  for the linearized return map.
* `TauCeti.hasEigenvalue_normalReturnDerivative_iff`: the normal return derivative and the
  linearized return map have the same nonzero eigenvalues.
* `TauCeti.mfderiv_flowTransition_neg_apply_mfderiv_flowTransition`: on the tangent space of the
  source section, the derivative of the reverse transition is a left inverse.
* `TauCeti.mfderiv_flowTransition_apply_mfderiv_flowTransition`: transitions conjugate the
  derivatives of return germs.
* `TauCeti.returnDerivative_comp_mfderiv_flowTransition`: the same conjugacy of the linearized
  return maps, as an identity of linear maps.
* `TauCeti.exists_linearEquiv_genEigenspace_returnDerivative`,
  `TauCeti.finrank_genEigenspace_returnDerivative_eq`: the nonzero generalized eigenspaces of
  linearized return maps at two points of a periodic orbit are isomorphic.
* `TauCeti.exists_linearEquiv_eigenspace_returnDerivative`,
  `TauCeti.finrank_eigenspace_returnDerivative_eq`, `TauCeti.hasEigenvalue_returnDerivative_iff`,
  `TauCeti.hasEigenvalue_one_returnDerivative_iff`: the same for eigenspaces and eigenvalues.
* `TauCeti.hasEigenvalue_one_normalReturnDerivative_iff`: the eigenvalue-one test for the normal
  return derivative does not depend on the section or the base point.
* `TauCeti.returnDerivative_natCast_mul`: the linearized return map of an iterate.

## References

* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, AMS, 2012, §12.2 (the Poincaré map of a periodic orbit and its derivative,
  Theorem 12.4).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g g' : M → ℝ} {T T₀ : ℝ} {p q : M}

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

/-- The derivative at `p` of the transition to the section `{g = g q}` through
`q = flowOf v T p` takes values in the tangent space `ker dg_q` of that section. -/
theorem mvfderiv_mfderiv_flowTransition_eq_zero (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g q) (hgv : mvfderiv I g q (v q) ≠ 0) (w : TangentSpace I p) :
    mvfderiv I g q (mfderiv I I (flowTransition v g T p) p w) = 0 := by
  have hh := mdifferentiableAt_flowTransition_of_eq hv hT hq hg hgv
  subst hq
  have hconst : (fun _ ↦ g (flowOf v T p)) =ᶠ[𝓝 p] g ∘ flowTransition v g T p := by
    filter_upwards [eventually_flowHittingTime hv hT hg hgv] with z hz
    rw [comp_apply, flowTransition_apply]
    exact hz.2.symm
  have h0 : mfderiv I 𝓘(ℝ) (g ∘ flowTransition v g T p) p = 0 :=
    ((hasMFDerivAt_const (g (flowOf v T p)) p).congr_of_eventuallyEq_abuse hconst.symm).mfderiv
  rw [← mvfderiv_comp_apply_of_eq p (hg.mdifferentiableAt one_ne_zero) hh
    (flowTransition_self ..)]
  -- `mvfderiv` is `mfderiv` followed by the identification of the tangent space of `ℝ` with `ℝ`.
  -- Mathlib has no congruence lemma for `mvfderiv` under eventual equality, and rewriting with
  -- the one for `mfderiv` leaves a cast between tangent spaces at different points, so the
  -- vanishing of `mfderiv` is transported by unfolding `mvfderiv`.
  simp only [mvfderiv, h0, ContinuousLinearMap.comp_zero, zero_apply]

/-- **The derivative of the time-zero transition.** For a section `{g = g p}` through `p`
transverse to `v`, the derivative at `p` of the transition at time `0` to this section is the
projection onto its tangent space `ker dg_p` along `v p`. -/
theorem mfderiv_flowTransition_zero_apply (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (v p) ≠ 0) (w : TangentSpace I p) :
    mfderiv I I (flowTransition v g 0 p) p w =
      w - (mvfderiv I g p w / mvfderiv I g p (v p)) • v p := by
  have h0 : ((0 : ℝ), p) ∈ flowDomain v := mem_flowDomain_zero hv p
  have hp0 : flowOf v 0 p = p := flowOf_zero hv p
  have hτ := mdifferentiableAt_flowHittingTime_of_eq hv h0 hp0 hg hgv
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
  have hker := mvfderiv_mfderiv_flowTransition_eq_zero hv h0 hp0 hg hgv w
  rw [hπ, map_add, map_smul, smul_eq_mul] at hker
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
  subst hq
  have hneg := neg_mem_flowDomain_flowOf hv hT
  have hback := flowOf_neg_flowOf hv hT
  have hcomp := flowTransition_comp_eventuallyEq hv hT rfl hg' hg'v hneg hback hg hgv
  rw [add_neg_cancel] at hcomp
  have hπ := mdifferentiableAt_flowTransition_of_eq hv (mem_flowDomain_zero hv p)
    (flowOf_zero hv p) hg hgv
  have hh := mdifferentiableAt_flowTransition_of_eq hv hT rfl hg' hg'v
  have hh' := mdifferentiableAt_flowTransition_of_eq hv hneg hback hg hgv
  have hD := (hπ.hasMFDerivAt.congr_of_eventuallyEq_abuse hcomp).mfderiv
  rw [← mfderiv_comp_apply_of_eq p hh' hh (flowTransition_self ..), hD]
  exact mfderiv_flowTransition_zero_apply_of_mvfderiv_eq_zero hv hg hgv hw

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
  fun _ ⟨w, hw⟩ ↦ hw ▸ mvfderiv_mfderiv_flowTransition_eq_zero hv hP hp hg hgv w

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
    have hcomp := flowTransition_comp_eventuallyEq hv hkP hkp hg hgv hP hp hg hgv
    have hPk := mdifferentiableAt_flowTransition_of_eq hv hkP hkp hg hgv
    have hP1 := mdifferentiableAt_flowTransition_of_eq hv hP hp hg hgv
    have hPkp : flowTransition v g (((k + 1 : ℕ) : ℝ) * T₀) p p = p :=
      (flowTransition_self ..).trans hkp
    have hD := ((hP1.comp_of_eq p hPk hPkp).hasMFDerivAt.congr_of_eventuallyEq_abuse
      hcomp.symm).mfderiv
    rw [hmul, pow_succ', ← ih]
    refine LinearMap.ext fun w ↦ ?_
    rw [mul_apply_eq_comp, returnDerivative_apply, returnDerivative_apply,
      returnDerivative_apply, hD]
    exact mfderiv_comp_apply_of_eq p hP1 hPk hPkp w

section Return

variable (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q) (hP : (T₀, p) ∈ flowDomain v)
  (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0)
include hT hq hP hp hg hgv hg' hg'v

/-- **Transitions conjugate the derivatives of return germs.** If the flow carries `p` to `q`
at time `T` and `p` returns to itself at time `T₀`, the derivatives at `p` and `q` of the return
branches `P_p` and `P_q` at time `T₀` of sections through `p` and `q` are intertwined by the
derivative of the transition `h` between the sections: `dh ∘ dP_p = dP_q ∘ dh`. -/
theorem mfderiv_flowTransition_apply_mfderiv_flowTransition (w : TangentSpace I p) :
    mfderiv I I (flowTransition v g' T p) p (mfderiv I I (flowTransition v g T₀ p) p w) =
      mfderiv I I (flowTransition v g' T₀ q) q (mfderiv I I (flowTransition v g' T p) p w) := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  have hPp : flowTransition v g T₀ p p = p := (flowTransition_self ..).trans hp
  have hhp : flowTransition v g' T p p = q := (flowTransition_self ..).trans hq
  have hP' := mdifferentiableAt_flowTransition_of_eq hv hP hp hg hgv
  have hh := mdifferentiableAt_flowTransition_of_eq hv hT hq hg' hg'v
  have hQ' := mdifferentiableAt_flowTransition_of_eq hv hQ hq' hg' hg'v
  have hQh : MDifferentiableAt I I (flowTransition v g' T₀ q) (flowTransition v g' T p p) := by
    rwa [hhp]
  have hsemi := flowTransition_semiconj_eventuallyEq hv hT hq hP hp hg hgv hg' hg'v
  have hD := ((hQh.comp p hh).hasMFDerivAt.congr_of_eventuallyEq_abuse hsemi).mfderiv
  rw [← mfderiv_comp_apply_of_eq p hh hP' hPp, hD]
  exact mfderiv_comp_apply_of_eq p hQ' hh hhp w

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
  LinearMap.ext fun w ↦
    (mfderiv_flowTransition_apply_mfderiv_flowTransition hv hT hq hP hp hg hgv hg' hg'v w).symm

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

/-- **The nonzero eigenvalues of linearized return maps do not depend on the section or the base
point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at time `T₀`, a
nonzero number is an eigenvalue of the linearized return map at time `T₀` of a transverse
section through `p` exactly when it is one for a transverse section through `q`. -/
theorem hasEigenvalue_returnDerivative_iff {μ : ℝ} (hμ : μ ≠ 0) :
    (returnDerivative v g T₀ p).HasEigenvalue μ ↔ (returnDerivative v g' T₀ q).HasEigenvalue μ := by
  simp only [Module.End.hasEigenvalue_iff, ne_eq, ← Submodule.finrank_eq_zero,
    finrank_eigenspace_returnDerivative_eq hv hT hq hP hp hg hgv hg' hg'v hμ]

/-- **The eigenvalue-one test does not depend on the section or the base point.** The linearized
return map at time `T₀` of a transverse section through `p` has eigenvalue `1` exactly when that of
a transverse section through any point `q` of the orbit does. -/
theorem hasEigenvalue_one_returnDerivative_iff :
    (returnDerivative v g T₀ p).HasEigenvalue 1 ↔ (returnDerivative v g' T₀ q).HasEigenvalue 1 :=
  hasEigenvalue_returnDerivative_iff hv hT hq hP hp hg hgv hg' hg'v one_ne_zero

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
  exact hasEigenvalue_one_returnDerivative_iff hv hT hq hP hp hg hgv hg' hg'v

end Return

end TauCeti
