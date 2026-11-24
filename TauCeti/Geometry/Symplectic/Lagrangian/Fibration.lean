/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive

/-!
# Lagrangian fibrations

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M`. A **Lagrangian fibration**
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration`) is a smooth submersion
`π : M → B` whose fibres are Lagrangian: at every point `x` the vertical space `ker dπ_x`, the
tangent space of the fibre through `x`, is a Lagrangian subspace of `(T_x M, σ_x)`. A **regular
Lagrangian torus fibration** (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
is moreover proper with connected fibres. This is the global setting of the Liouville–Arnold
theorem: for a symplectic form its fibres are tori
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`
in `TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Fibration`), and the torus bundle `T*B / Λ`
of a closed coframe is the model example
(`TauCeti.CotangentBundle.LatticeQuotient.isLagrangianTorusFibration_proj`).

With the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, the functions pulled
back from the base generate the vertical motions:

* for a Lagrangian fibration `dim M = 2 dim B` (`IsLagrangianFibration.two_mul_finrank`);
* so a differentiable section of a Lagrangian fibration, an immersion of the base, is a
  Lagrangian map as soon as it is isotropic
  (`IsLagrangianFibration.isLagrangianMap_iff_isIsotropicMap`);
* the Hamiltonian vector field of a pulled-back function `g ∘ π` is vertical, tangent to the fibres
  (`IsLagrangianFibration.hamiltonianVectorField_comp_mem_ker_mfderiv`), because `d(g ∘ π)`
  vanishes on `ker dπ`, so `X_(g ∘ π)` lies in the symplectic complement of `ker dπ`, which is
  `ker dπ` itself;
* consequently pulled-back functions Poisson-commute
  (`IsLagrangianFibration.poissonBracket_comp_eq_zero`): the coordinates of a chart of `B`, pulled
  back to `M`, form an involutive family with independent differentials;
* every maximal integral curve of such a vertical field stays in one fibre, so for a proper `π` the
  Hamiltonian vector field of every smooth pulled-back function is complete
  (`IsLagrangianFibration.isCompleteVectorField_hamiltonianVectorField_comp`).

* for a proper `π`, the flow of `g ∘ π` moves a point `x` in a way that depends only on the
  differential of `g` at `π x`
  (`IsLagrangianFibration.flowOf_hamiltonianVectorField_comp_eq`), since along the fibre through
  `x` its Hamiltonian vector field is determined by `d(g ∘ π) = dg_(π x) ∘ dπ`.

These vertical Hamiltonian flows generate the fibrewise action of `T*B` from which the period
lattice `Λ ⊆ T*B` of the fibration is built; for a regular Lagrangian torus fibration the action of
`T*_b B` on the fibre over `b` and its stabilizer, the period lattice `Λ_b`, are constructed in
`TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

variable (hσ J) in
/-- A **Lagrangian fibration** is a smooth submersion `π : M → B` whose fibres are Lagrangian: at
every point the vertical space `ker dπ_x` is a Lagrangian subspace of `(T_x M, σ_x)`. -/
structure IsLagrangianFibration (π : M → B) : Prop where
  /-- The projection of a Lagrangian fibration is a smooth submersion. -/
  isSubmersion : Manifold.IsSubmersion I J ∞ π
  /-- The vertical spaces of a Lagrangian fibration are Lagrangian. -/
  isLagrangian_ker_mfderiv : ∀ x, (hσ.symplecticFormAt x).IsLagrangian (mfderiv I J π x).ker

variable (hσ J) in
/-- A **regular Lagrangian torus fibration** is a proper Lagrangian fibration with connected
fibres. Its fibres are then compact, connected and nonempty, and for a symplectic form each of them
is a torus (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`). -/
structure IsLagrangianTorusFibration (π : M → B) : Prop extends IsLagrangianFibration J hσ π where
  /-- The projection of a regular Lagrangian torus fibration is proper. -/
  isProperMap : IsProperMap π
  /-- The fibres of a regular Lagrangian torus fibration are connected, in particular nonempty. -/
  isConnected_preimage_singleton : ∀ b, IsConnected (π ⁻¹' {b})

namespace IsLagrangianFibration

variable (h : hσ.IsLagrangianFibration J π)
include h

/-- The projection of a Lagrangian fibration is smooth. -/
theorem contMDiff : ContMDiff I J ∞ π :=
  h.isSubmersion.contMDiff

/-- The projection of a Lagrangian fibration is differentiable. -/
theorem mdifferentiableAt (x : M) : MDifferentiableAt I J π x :=
  h.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

/-- The derivative of the projection of a Lagrangian fibration is surjective. -/
theorem surjective_mfderiv (x : M) : Surjective (mfderiv I J π x) :=
  h.isSubmersion.surjective_mfderiv (by simp) x

/-- **A Lagrangian fibration halves the dimension**: the base of a Lagrangian fibration of a
nonempty manifold has half its dimension, `2 dim B = dim M`. -/
theorem two_mul_finrank [FiniteDimensional ℝ E] [Nonempty M] :
    2 * finrank ℝ F = finrank ℝ E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hL := (h.isLagrangian_ker_mfderiv x).two_mul_finrank
  have hrn := LinearMap.finrank_range_add_finrank_ker (mfderiv I J π x).toLinearMap
  rw [LinearMap.range_eq_top.2 (h.surjective_mfderiv x), finrank_top] at hrn
  -- Both tangent spaces are their model spaces.
  change finrank ℝ F + finrank ℝ (mfderiv I J π x).ker = finrank ℝ E at hrn
  change 2 * finrank ℝ (mfderiv I J π x).ker = finrank ℝ E at hL
  omega

/-- The dimension of `M` is twice the number of coordinates `Fin (dim B)` on the base. This is
`two_mul_finrank`, in the form taken by the Liouville–Arnold theorem for `dim B` functions. -/
theorem two_mul_card_fin_finrank [FiniteDimensional ℝ E] [Nonempty M] :
    2 * Fintype.card (Fin (finrank ℝ F)) = finrank ℝ E := by
  rw [Fintype.card_fin, h.two_mul_finrank]

/-- **A section of a Lagrangian fibration is Lagrangian as soon as it is isotropic.** A
differentiable section `s` of the projection `π` of a Lagrangian fibration is an immersion of the
base, which has half the dimension of `M`, so its tangent images are Lagrangian as soon as they
are isotropic. -/
theorem isLagrangianMap_iff_isIsotropicMap [FiniteDimensional ℝ E] {s : B → M}
    (hs : ∀ b, π (s b) = b) (hsm : MDifferentiable J I s) :
    hσ.IsLagrangianMap J s ↔ hσ.IsIsotropicMap J s := by
  refine ⟨fun hL ↦ hL.isIsotropicMap, fun hiso ↦ isLagrangianMap_iff_forall.2 fun b ↦ ?_⟩
  have : Nonempty M := ⟨s b⟩
  -- `π` is a left inverse of `s`, so `ds` is injective.
  exact isLagrangianMap_iff_forall.1 (hiso.isLagrangianMap_of_finrank
    (fun b ↦ mfderiv_injective_of_leftInverse (h.mdifferentiableAt (s b)) (hsm b) hs)
    h.two_mul_finrank) b

/-- **Hamiltonian vector fields of pulled-back functions are vertical.** If `g` is differentiable
at `π x`, the Hamiltonian vector of `g ∘ π` at `x` is tangent to the fibre: it lies in `ker dπ_x`.
-/
theorem hamiltonianVectorField_comp_mem_ker_mfderiv [FiniteDimensional ℝ E] {g : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) :
    σ.hamiltonianVectorField (g ∘ π) x ∈ (mfderiv I J π x).ker :=
  -- `d(g ∘ π)` vanishes on `ker dπ`, which is Lagrangian and hence coisotropic.
  hσ.hamiltonianVectorField_mem_of_forall_mvfderiv_eq_zero
    (h.isLagrangian_ker_mfderiv x).isCoisotropic fun v hv ↦ by
      have hv' : mfderiv I J π x v = 0 := LinearMap.mem_ker.1 hv
      rw [mvfderiv_comp_apply x hg (h.mdifferentiableAt x), hv', map_zero]

/-- The projection of a Lagrangian fibration kills the Hamiltonian vector field of a pulled-back
function. -/
theorem mfderiv_hamiltonianVectorField_comp_eq_zero [FiniteDimensional ℝ E] {g : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) :
    mfderiv I J π x (σ.hamiltonianVectorField (g ∘ π) x) = 0 :=
  LinearMap.mem_ker.1 (h.hamiltonianVectorField_comp_mem_ker_mfderiv hg)

/-- **Pulled-back functions Poisson-commute.** For a Lagrangian fibration `π` and functions `g`,
`k` on the base, differentiable at `π x`, the Poisson bracket `{g ∘ π, k ∘ π}` vanishes at `x`. -/
theorem poissonBracket_comp_eq_zero [FiniteDimensional ℝ E] {g k : B → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (π x)) (hk : MDifferentiableAt J 𝓘(ℝ) k (π x)) :
    σ.poissonBracket (g ∘ π) (k ∘ π) x = 0 := by
  rw [σ.poissonBracket_eq_mvfderiv, mvfderiv_comp_apply x hg (h.mdifferentiableAt x),
    h.mfderiv_hamiltonianVectorField_comp_eq_zero hk, map_zero]

/-- The components of a family `κ ∘ π` of functions pulled back from the base Poisson-commute at
`x` when `κ` is differentiable at `π x`. -/
theorem poissonBracket_comp_apply_eq_zero [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {κ : B → ι → ℝ} {x : M} (hκ : MDifferentiableAt J 𝓘(ℝ, ι → ℝ) κ (π x)) (i j : ι) :
    σ.poissonBracket ((κ ∘ π) · i) ((κ ∘ π) · j) x = 0 :=
  h.poissonBracket_comp_eq_zero (mdifferentiableAt_pi_space.1 hκ i)
    (mdifferentiableAt_pi_space.1 hκ j)

/-- The Hamiltonian vector field of a `C²` pulled-back function `g ∘ π` is `C¹`. -/
theorem contMDiff_hamiltonianVectorField_comp [FiniteDimensional ℝ E] {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) :
    ContMDiff I I.tangent 1 (T% (σ.hamiltonianVectorField (g ∘ π))) :=
  hσ.contMDiff_hamiltonianVectorField (by simp)
    (by rw [one_add_one_eq_two]; exact hg.comp (h.contMDiff.of_le (by simp)))

/-- **Vertical Hamiltonian flows stay in their fibre.** Along the maximal integral curve through
`x` of the Hamiltonian vector field of a `C²` pulled-back function `g ∘ π`, the projection `π` is
constant. -/
theorem apply_maximalIntegralCurve_hamiltonianVectorField_comp [FiniteDimensional ℝ E]
    [T2Space M] [BoundarylessManifold I M] [IsManifold J 1 B] {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : M} {t : ℝ}
    (ht : t ∈ maximalIntegralCurveInterval (σ.hamiltonianVectorField (g ∘ π)) x) :
    π (maximalIntegralCurve (σ.hamiltonianVectorField (g ∘ π)) x t) = π x := by
  have hv := h.contMDiff_hamiltonianVectorField_comp hg
  have h0 := zero_mem_maximalIntegralCurveInterval_of_mem ht
  conv_rhs => rw [← maximalIntegralCurve_zero (v := σ.hamiltonianVectorField (g ∘ π)) (x := x)]
  exact (isMIntegralCurveOn_maximalIntegralCurve hv).apply_eq_of_mfderiv_apply_eq_zero
    isOpen_maximalIntegralCurveInterval isPreconnected_maximalIntegralCurveInterval
    (fun _ _ ↦ h.mdifferentiableAt _)
    (fun _ _ ↦ h.mfderiv_hamiltonianVectorField_comp_eq_zero ((hg _).mdifferentiableAt (by simp)))
    h0 ht

/-- **Vertical Hamiltonian flows of a proper Lagrangian fibration are complete.** If the projection
`π` is proper, the Hamiltonian vector field of every `C²` pulled-back function `g ∘ π` is complete:
its integral curves stay in the compact fibres of `π`. -/
theorem isCompleteVectorField_hamiltonianVectorField_comp [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold J 1 B] (hπ : IsProperMap π) {g : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) :
    IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π)) :=
  isCompleteVectorField_of_isProperMap (h.contMDiff_hamiltonianVectorField_comp hg) hπ
    fun _ _ ht ↦ h.apply_maximalIntegralCurve_hamiltonianVectorField_comp hg ht

/-- **Vertical Hamiltonian flows depend only on the differential at the base point.** Let `π` be
proper. If two `C²` functions `g` and `g'` on the base have the same differential at `π x`, the
Hamiltonian flows of `g ∘ π` and `g' ∘ π` move `x` alike: both flow lines stay in the fibre through
`x`, along which `d(g ∘ π) = dg_(π x) ∘ dπ` and `d(g' ∘ π)` agree, so the two fields agree there. -/
theorem flowOf_hamiltonianVectorField_comp_eq [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold J 1 B] (hπ : IsProperMap π) {g g' : B → ℝ}
    (hg : ContMDiff J 𝓘(ℝ) 2 g) (hg' : ContMDiff J 𝓘(ℝ) 2 g') {x : M}
    (hgg' : mvfderiv J g (π x) = mvfderiv J g' (π x)) (t : ℝ) :
    flowOf (σ.hamiltonianVectorField (g ∘ π)) t x =
      flowOf (σ.hamiltonianVectorField (g' ∘ π)) t x := by
  have hc := h.isCompleteVectorField_hamiltonianVectorField_comp hπ hg
  set γ := maximalIntegralCurve (σ.hamiltonianVectorField (g ∘ π)) x
  have hγ : IsMIntegralCurve γ (σ.hamiltonianVectorField (g ∘ π)) :=
    isMIntegralCurve_maximalIntegralCurve_of_eq_univ (h.contMDiff_hamiltonianVectorField_comp hg)
      (hc.maximalIntegralCurveInterval_eq_univ x)
  -- The flow line of `g ∘ π` through `x` is also an integral curve of `g' ∘ π`.
  have hγ' : IsMIntegralCurve γ (σ.hamiltonianVectorField (g' ∘ π)) := by
    intro s
    have hπγ : π (γ s) = π x := h.apply_maximalIntegralCurve_hamiltonianVectorField_comp hg
      (hc.mem_maximalIntegralCurveInterval x s)
    have hd : mvfderiv J g (π (γ s)) = mvfderiv J g' (π (γ s)) := by rw [hπγ]; exact hgg'
    have hX : σ.hamiltonianVectorField (g ∘ π) (γ s) =
        σ.hamiltonianVectorField (g' ∘ π) (γ s) := by
      rw [hamiltonianVectorField_def, hamiltonianVectorField_def,
        mvfderiv_comp (γ s) ((hg _).mdifferentiableAt (by simp)) (h.mdifferentiableAt _),
        mvfderiv_comp (γ s) ((hg' _).mdifferentiableAt (by simp)) (h.mdifferentiableAt _), hd]
    rw [← hX]
    exact hγ s
  have h0 : γ 0 = x := maximalIntegralCurve_zero
  have h1 := hγ'.maximalIntegralCurve_eq (h.contMDiff_hamiltonianVectorField_comp hg') t
  rw [h0] at h1
  rw [flowOf_apply, flowOf_apply, h1]

end IsLagrangianFibration

namespace IsLagrangianTorusFibration

variable (h : hσ.IsLagrangianTorusFibration J π)
include h

/-- The fibres of a regular Lagrangian torus fibration are compact. -/
theorem isCompact_preimage_singleton (b : B) : IsCompact (π ⁻¹' {b}) :=
  h.isProperMap.isCompact_preimage isCompact_singleton

/-- The projection of a regular Lagrangian torus fibration is surjective, since its fibres are
connected, hence nonempty. -/
theorem surjective : Surjective π := fun b ↦
  (h.isConnected_preimage_singleton b).nonempty

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
