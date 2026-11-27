/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConnectedLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Free
import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Hessian
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice.MomentMap
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Semidefinite
import TauCeti.Geometry.Manifold.GroupAction.InvariantForm
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The torus acts freely over the interior of the moment polytope

Let a compact commutative Lie group `G` with Lie algebra `𝔤`, such as a torus, act smoothly and
effectively on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ : M → 𝔤*`, and suppose that `dim M = 2 dim G`. So `(M, σ, μ)` is a symplectic
toric manifold. This file proves that `G` acts freely at every point `x` whose image `μ(x)` lies in
the interior of the moment polytope `conv μ(M)`
(`TauCeti.SmoothTwoForm.IsMomentMap.stabilizer_eq_bot_of_mem_interior_convexHull_range`).

Since locally free points of a symplectic toric manifold are free
(`TauCeti.SmoothTwoForm.IsMomentMap.stabilizer_eq_bot_of_isotropy_eq_bot`), it suffices to show
that a point `x` with nonzero isotropy algebra `𝔥 = 𝔤_x` maps to the boundary. Effectiveness is
used only to pass from locally free to free; the boundary argument, and
`TauCeti.SmoothTwoForm.IsMomentMap.isotropy_eq_bot_of_mem_interior_convexHull_range`, do not need
it. Such a point is a global minimum of a component `μ^ξ` for some
nonzero `ξ ∈ 𝔥` (`TauCeti.SmoothTwoForm.IsMomentMap.exists_ne_zero_isMinOn_of_isotropy_ne_bot`):

* **The linearized isotropy action.** Every `ξ ∈ 𝔥` acts on `T_x M` by the generator `A_ξ` of
  `t ↦ d(exp (t ξ))_x` (`TauCeti.isotropyLinearization`). These operators are skew-adjoint for
  `σ_x`, complex linear for the value at `x` of a `G`-invariant compatible almost complex
  structure (`exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap` in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`), and pairwise commuting, since `G` is
  commutative. They vanish on the orbit tangent space `W = 𝔤 · x`, which is fixed by the
  stabilizer, and `W` is isotropic with `dim W = dim G - dim 𝔥`, so
  `dim T_x M = 2 (dim W + dim 𝔥)`.
* **A semidefinite Hessian.** The linear algebra of
  `TauCeti.SymplecticForm.exists_ne_zero_forall_apply_apply_nonneg` gives `ξ ≠ 0` in `𝔥` with
  `σ_x(A_ξ v, v) ≥ 0`. This is the Hessian of `μ^ξ` at its critical point `x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.exists_ne_zero_forall_criticalHessian_nonneg`), so the Morse
  index of `μ^ξ` there is zero.
* **Local minima are global.** The Morse–Bott component `μ^ξ` has even indices and convexity
  charts, so its local minimum `x` is a global minimum
  (`TauCeti.SmoothTwoForm.IsMomentMap.isMinOn_of_manifoldMorseIndex_eq_zero`).

Then `μ(x)` minimizes the nonzero linear functional `ν ↦ ν(ξ)` on `μ(M)`, hence on its convex hull,
so it is not an interior point.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `exists_ne_zero_forall_criticalHessian_nonneg`: at a point with nonzero isotropy algebra some
  nonzero component of the moment map has a positive semidefinite Hessian.
* `exists_ne_zero_isMinOn_of_isotropy_ne_bot`: a point with nonzero isotropy algebra is a global
  minimum of some nonzero component of the moment map.
* `isotropy_eq_bot_of_mem_interior_convexHull_range`: over the interior of the moment polytope the
  action is locally free.
* `stabilizer_eq_bot_of_mem_interior_convexHull_range`: for an effective action, over the interior
  of the moment polytope the action is free.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 27–29.
-/

public section

noncomputable section

open Filter Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **A point with nonzero isotropy algebra has a semidefinite Hessian.** Let a compact commutative
Lie group `G` act smoothly on a compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`. If the isotropy algebra `𝔤_x` is
nonzero, then there is a nonzero `ξ ∈ 𝔤_x` such that the Hessian of the component `μ^ξ` at its
critical point `x` is positive semidefinite. -/
theorem exists_ne_zero_forall_criticalHessian_nonneg
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M}
    (hx : (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M).isotropy x ≠ ⊥) :
    ∃ ξ ∈ (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M).isotropy x, ξ ≠ 0 ∧
      ∀ v, 0 ≤ criticalHessian 𝓘(ℝ, E') (fun y ↦ μ y ξ) x v v := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have hσG := SmoothForm.eval₂_mfderiv_smul_of_mpullback_smul_eq (I := I) hG
  set a := InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M with ha
  -- The linearized isotropy action `A : 𝔤_x → sp(T_x M, σ_x)`, `A_ξ = d/dt|₀ d(exp (t ξ))_x`.
  have hσx : ∀ g ∈ MulAction.stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ := fun g _ ↦ hG g
  let A : a.isotropy x →ₗ[ℝ] Module.End ℝ (TangentSpace 𝓘(ℝ, E') x) :=
    (skewAdjointLieSubalgebra
      (hσ.isNondegenerate.symplecticFormAt x).toBilinForm).toSubmodule.subtype.comp
        (hσ.isNondegenerate.isotropySkewAdjoint hσx)
  have hAv (ξ : a.isotropy x) (v : TangentSpace 𝓘(ℝ, E') x) :
      A ξ v = isotropyLinearization 𝓘(ℝ, E') x ξ v :=
    hσ.isNondegenerate.coe_isotropySkewAdjoint_apply hσx ξ v
  have hAeq (ξ : a.isotropy x) :
      A ξ = ((isotropyLinearization 𝓘(ℝ, E') x ξ : E' →ₗ[ℝ] E') :
        Module.End ℝ (TangentSpace 𝓘(ℝ, E') x)) :=
    hσ.isNondegenerate.coe_isotropySkewAdjoint hσx ξ
  -- They lie in `sp(T_x M, σ_x)` and are complex linear for a compatible complex structure `J`.
  obtain ⟨J, hJ, hA⟩ :=
    hσ.isNondegenerate.exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap
      (I := I) hσG x
  have hcomm (ξ η : a.isotropy x) : Commute (A ξ) (A η) := by
    rw [hAeq, hAeq]
    exact (commute_isotropyLinearization ξ η).map ContinuousLinearMap.toLinearMapRingHom
  have hAW (ξ : a.isotropy x) (w : TangentSpace 𝓘(ℝ, E') x) (hw : w ∈ a.orbitTangent x) :
      A ξ w = 0 := by
    obtain ⟨ζ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hw
    rw [hAv, ha, InfinitesimalAction.fundamental_apply]
    exact isotropyLinearization_apply_fundamentalVectorField ξ ζ
  -- The orbit tangent space is isotropic, of dimension `dim G - dim 𝔤_x`.
  have hW := h.isIsotropic_orbitTangent hσ.isNondegenerate
    (h.momentCocycle_eq_zero_of_isLieAbelian hσ.isClosed x) (x := x)
  have hdim' : finrank ℝ (TangentSpace 𝓘(ℝ, E') x) ≤
      2 * (finrank ℝ (a.orbitTangent x) + finrank ℝ (a.isotropy x)) := by
    have := a.finrank_orbitTangent_add_finrank_isotropy x
    rw [finrank_tangentSpace (I := I) (1 : G)] at this
    rw [finrank_tangentSpace (I := 𝓘(ℝ, E')) x]
    omega
  have : Nontrivial (a.isotropy x) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h0 ↦ hx ((LieSubalgebra.toSubmodule_eq_bot _).1 h0)
  obtain ⟨ξ, hξ0, hξ⟩ := SymplecticForm.exists_ne_zero_forall_apply_apply_nonneg hJ A hcomm
    (fun ξ ↦ (hσ.isNondegenerate.isotropySkewAdjoint hσx ξ).property)
    (fun ξ ↦ hAeq ξ ▸ (hA ξ).2) hW hAW hdim'
  -- The Hessian of `μ^ξ` at `x` is `σ_x(A_ξ v, w)`.
  refine ⟨ξ, ξ.property, fun h' ↦ hξ0 (Subtype.ext h'), fun v ↦ ?_⟩
  rw [h.criticalHessian_apply_eq_eval₂_isotropyLinearization hσ.isNondegenerate, ← hAv]
  exact (hξ v).trans_eq (hσ.isNondegenerate.symplecticFormAt_apply x _ v)

/-- **A point with nonzero isotropy algebra is a minimum of a moment map component.** Let a compact
commutative Lie group `G` act smoothly on a compact connected symplectic manifold `(M, σ)`
without boundary, preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`. If the isotropy
algebra `𝔤_x` is nonzero, then there is a nonzero `ξ ∈ 𝔤_x` such that the component `μ^ξ` attains
its minimum at `x`. -/
theorem exists_ne_zero_isMinOn_of_isotropy_ne_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M}
    (hx : (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M).isotropy x ≠ ⊥) :
    ∃ ξ ∈ (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M).isotropy x, ξ ≠ 0 ∧
      IsMinOn (fun y ↦ μ y ξ) univ x := by
  obtain ⟨ξ, hξx, hξ0, hξ⟩ := h.exists_ne_zero_forall_criticalHessian_nonneg hσ hG hdim hx
  -- A positive semidefinite Hessian has Morse index zero, so the local minimum `x` of the
  -- Morse–Bott function `μ^ξ` is a global minimum.
  have h0 : manifoldMorseIndex 𝓘(ℝ, E') (fun y ↦ μ y ξ) x = 0 := by
    rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
    refine (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).1 fun v ↦ ?_
    rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply]
    exact hξ v
  exact ⟨ξ, hξx, hξ0, h.isMinOn_of_manifoldMorseIndex_eq_zero hσ.isNondegenerate
    (SmoothForm.eval₂_mfderiv_smul_of_mpullback_smul_eq (I := I) hG)
    ((h.mem_criticalPoints_iff_mem_isotropy (hσ.isNondegenerate.nondegenerate_bilinFormAt x) _).2
      hξx) h0⟩

/-- **The action is locally free over the interior of the moment polytope.** Let a compact
commutative Lie group `G` act smoothly on a compact connected symplectic manifold `(M, σ)` without
boundary, preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`. If `μ(x)`, read in the
continuous dual `𝔤*`, is an interior point of the moment polytope `conv μ(M)`, then the isotropy
algebra `𝔤_x` is trivial. -/
theorem isotropy_eq_bot_of_mem_interior_convexHull_range
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M}
    (hx : (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E) ∈
      interior (convexHull ℝ
        (range fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)))) :
    (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M).isotropy x = ⊥ := by
  by_contra hne
  obtain ⟨ξ, -, hξ0, hmin⟩ := h.exists_ne_zero_isMinOn_of_isotropy_ne_bot hσ hG hdim hne
  set f : M → StrongDual ℝ E := fun y ↦ LinearMap.toContinuousLinearMap (μ y)
  -- `ξ : GroupLieAlgebra I G` is a tangent vector at `1`, a vector of `E` by definition, and
  -- evaluation at it is a linear functional on `𝔤*` that `μ(x)` minimizes on the moment image.
  set φ : StrongDual ℝ E →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (show E from ξ)
  have hφ (y : M) : φ (f y) = μ y ξ := rfl
  have hhull : convexHull ℝ (range f) ⊆ {ν | φ (f x) ≤ φ ν} :=
    convexHull_min (range_subset_iff.2 fun y ↦ by
      simpa only [mem_ofPred_eq, hφ] using isMinOn_univ_iff.1 hmin y)
      (convex_halfSpace_ge φ.isLinear _)
  -- So `φ` has a local minimum at the interior point `f x`, and its derivative `φ` vanishes.
  have hloc : IsLocalMin φ (f x) :=
    Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hx) hhull
  have hφ0 : φ = 0 := hloc.hasFDerivAt_eq_zero φ.hasFDerivAt
  have hξE : (show E from ξ) ≠ 0 := hξ0
  obtain ⟨ψ, hψ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) (V := E) hξE
  exact hψ (congrArg (fun L : StrongDual ℝ E →L[ℝ] ℝ ↦ L ψ) hφ0)

/-- **The torus acts freely over the interior of the moment polytope.** Let a compact commutative
Lie group `G`, such as a torus, act smoothly and effectively on a compact connected symplectic
manifold `(M, σ)` without boundary, preserving `σ`, with moment map `μ`, and with
`dim M = 2 dim G`. If `μ(x)`, read in the continuous dual `𝔤*`, is an interior point of the moment
polytope `conv μ(M)`, then the stabilizer of `x` is trivial. -/
theorem stabilizer_eq_bot_of_mem_interior_convexHull_range [FaithfulSMul G M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {x : M}
    (hx : (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E) ∈
      interior (convexHull ℝ
        (range fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)))) :
    MulAction.stabilizer G x = ⊥ :=
  h.stabilizer_eq_bot_of_isotropy_eq_bot hσ hG hdim
    (h.isotropy_eq_bot_of_mem_interior_convexHull_range hσ hG hdim hx)

end TauCeti.SmoothTwoForm.IsMomentMap
