/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Submersion
import TauCeti.Topology.Algebra.Module.CompactQuotient

/-!
# The fibrewise action and the period lattice of a Lagrangian fibration

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a Lagrangian
fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianFibration`) onto a Hausdorff
manifold `B` of dimension `n`, with proper projection. With the convention `ι_{X_f} σ = df`, the
Hamiltonian vector field of a pulled-back function `g ∘ π` is tangent to the fibres, and along the
fibre `π⁻¹(b)` it only depends on the covector `dg_b ∈ T*_b B`.

**The fibrewise action.** A covector `ξ ∈ T*_b B` acts on the fibre `π⁻¹(b)`
(`IsLagrangianFibration.fiberAction`). For every function `g` on `B` differentiable at `b` with
`dg_b = ξ`, the curve `t ↦ (t ξ) • x` is an integral curve of `X_{g ∘ π}`
(`IsLagrangianFibration.isMIntegralCurve_fiberAction`). So when `X_{g ∘ π}` is `C¹`, for instance
for a `C²` function `g`, the action of `t ξ` is the time-`t` map of the flow of `X_{g ∘ π}`
(`IsLagrangianFibration.coe_fiberAction_smul_apply_eq_flowOf`,
`IsLagrangianFibration.coe_fiberAction_smul_apply_eq_globalFlow`); in particular `ξ` acts by its
time-one map (`IsLagrangianFibration.coe_fiberAction_apply_eq_globalFlow`). The action is
additive because the functions pulled back from the base Poisson-commute. It is built from the
action of `ℝⁿ` by the flows of the coordinates of a chart of `B` at `b`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`), but by the characterization above it
does not depend on that chart. More generally, for a family `κ : B → ℝ^ι` the covector
`∑ i, vᵢ dκᵢ` acts as `v` does under the Hamiltonian flow action of `κ ∘ π`
(`IsLagrangianFibration.coe_fiberAction_apply_eq_hamiltonianFlowAction`). The orbit maps are smooth
immersions, with derivative `η ↦ X_{g ∘ π}` for `dg_b = η`
(`IsLagrangianFibration.contMDiff_fiberAction_apply`,
`IsLagrangianFibration.mfderiv_fiberAction_apply`,
`IsLagrangianFibration.injective_mfderiv_fiberAction_apply`).

**The period lattice.** The *period lattice* `Λ_b ⊆ T*_b B` is the group of covectors acting
trivially on the fibre (`IsLagrangianFibration.periodLattice`). It is discrete whenever the fibre
is nonempty (`IsLagrangianFibration.discreteTopology_periodLattice`). For a regular Lagrangian
torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`), whose
fibres are moreover connected:

* the action is transitive on each fibre (`IsLagrangianTorusFibration.exists_fiberAction_apply_eq`),
  and `Λ_b` is the stabilizer of every point of `π⁻¹(b)`
  (`IsLagrangianTorusFibration.mem_periodLattice_iff_fiberAction_apply_eq`,
  `IsLagrangianTorusFibration.mem_periodLattice_iff_mem_hamiltonianFlowStabilizer`);
* the orbit map descends to an equivariant homeomorphism `T*_b B ⧸ Λ_b ≃ₜ π⁻¹(b)`
  (`IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph`,
  `IsLagrangianTorusFibration.quotientPeriodLatticeHomeomorph_add`);
* `Λ_b` is a discrete, full lattice in `T*_b B`, of rank `n`
  (`IsLagrangianTorusFibration.discreteTopology_periodLattice`,
  `IsLagrangianTorusFibration.isZLattice_periodLattice`,
  `IsLagrangianTorusFibration.finrank_periodLattice`);
* every fibre `π⁻¹(b)` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`
  (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`).

Assembling the lattices `Λ_b` into a period lattice `Λ ⊆ T*B` is not done here. When a lattice
`Λ ⊆ T*B` is spanned by a closed coframe `α`, the quotient `T*B / Λ` is the model torus bundle
`TauCeti.CotangentBundle.LatticeQuotient α hα`.

Covectors at `b` are read in the model space: the cotangent space `T*_b B` is
`TangentSpace J b →L[ℝ] ℝ`, which is `F →L[ℝ] ℝ` by definition of the tangent space, and the
statements use the latter so that it carries its normed space structure.

The proofs reduce to the Liouville–Arnold theory of the family `G = κ ∘ π : M → ℝⁿ`, where `κ` is a
smooth map agreeing with a chart of `B` near `b` (localized by a bump function), read in a basis.
Its components Poisson-commute because the fibres are Lagrangian
(`IsLagrangianFibration.poissonBracket_comp_eq_zero`); their Hamiltonian vector fields are
vertical, so complete because `π` is proper
(`IsLagrangianFibration.isCompleteVectorField_hamiltonianVectorField_comp`); `G` is regular along
`π⁻¹(b)` because `dκ_b` is invertible and `π` is a submersion; and since `κ` is injective near `b`,
a connected fibre `π⁻¹(b)` is exactly the connected component of the level `G⁻¹(G x)` through any
of its points `x`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the action of `T*B` on the fibres and the period lattice).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

noncomputable section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

namespace IsLagrangianFibration

/-! ### Chart families -/

/-- A smooth map `B → F` with the germ of the extended chart of `B` at `b`. -/
private def chartMap (b : B) : C^∞⟮J, B; 𝓘(ℝ, F), F⟯ :=
  (exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b).choose

private theorem chartMap_eventuallyEq (b : B) :
    (chartMap (J := J) b : B → F) =ᶠ[𝓝 b] extChartAt J b :=
  (exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b).choose_spec

/-- The `i`-th coordinate of `chartMap b` in the standard basis of `F`. -/
private def chartCoord (b : B) (i : Fin (finrank ℝ F)) (c : B) : ℝ :=
  (Module.finBasis ℝ F).equivFunL (chartMap (J := J) b c) i

private theorem contMDiff_chartCoord (b : B) (i : Fin (finrank ℝ F)) :
    ContMDiff J 𝓘(ℝ) ∞ (chartCoord (J := J) b i) :=
  ((ContinuousLinearMap.proj i).comp
    ((Module.finBasis ℝ F).equivFunL : F →L[ℝ] Fin (finrank ℝ F) → ℝ)).contMDiff.comp
    (chartMap b).contMDiff

/-- The family `G = κ ∘ π : M → ℝⁿ` of the coordinates of a chart of `B` at `b`, pulled back to
`M`. -/
private def chartFamily (π : M → B) (b : B) (y : M) : Fin (finrank ℝ F) → ℝ :=
  fun i ↦ chartCoord (J := J) b i (π y)

omit [TopologicalSpace M] in
private theorem chartFamily_apply (b : B) (y : M) :
    chartFamily (J := J) π b y = fun i ↦ chartCoord (J := J) b i (π y) :=
  rfl

/-- The coordinates of a covector `ξ` at `b` in the basis dual to the standard basis of `F`.
This is Mathlib's coordinate equivalence `Module.Basis.equivFunL` of that dual basis. -/
private def covectorCoords : (F →L[ℝ] ℝ) ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) :=
  ((Module.finBasis ℝ F).dualBasis.map LinearMap.toContinuousLinearMap).equivFunL

private theorem covectorCoords_apply (ξ : F →L[ℝ] ℝ) (i : Fin (finrank ℝ F)) :
    covectorCoords ξ i = ξ (Module.finBasis ℝ F i) := by
  simp [covectorCoords]

/-- A covector at `b` is the combination of the coordinate functions of the chart at `b` with
coefficients its coordinates: `∑ i, ξ(eᵢ) κᵢ = ξ ∘ κ`. -/
private theorem sum_covectorCoords_mul_chartCoord (b : B) (ξ : F →L[ℝ] ℝ) (c : B) :
    ∑ i, covectorCoords ξ i * chartCoord (J := J) b i c = ξ (chartMap (J := J) b c) := by
  conv_rhs => rw [← (Module.finBasis ℝ F).sum_repr (chartMap b c), map_sum]
  simp only [chartCoord, covectorCoords_apply, map_smul, smul_eq_mul,
    Module.Basis.equivFunL_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The covector `ξ ∘ dκ_b` of the pulled-back chart function is `ξ`, since the chart map has the
identity as derivative at `b`. -/
private theorem mvfderiv_comp_chartMap (b : B) (ξ : F →L[ℝ] ℝ) :
    mvfderiv J (ξ ∘ chartMap (J := J) b) b = ξ := by
  ext v
  rw [ξ.mvfderiv_comp_apply ((chartMap b).contMDiff.mdifferentiableAt (by simp)),
    mvfderiv_apply_of_eventuallyEq_extChartAt (chartMap_eventuallyEq b)]
  -- Both sides are `ξ v`, the tangent vector `v` at `b` being read in the model space `F`.
  rfl

variable (h : hσ.IsLagrangianFibration J π)
include h

private theorem contMDiff_chartFamily (b : B) :
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ (chartFamily (J := J) π b) :=
  contMDiff_pi_module_iff.2 fun i ↦ (contMDiff_chartCoord b i).comp h.contMDiff

/-- The Hamiltonian vector field of `(ξ ∘ κ) ∘ π`, where `κ` is the chart map at `b`, is the
combination `∑ i, ξ(eᵢ) X_{Gᵢ}` of the Hamiltonian vector fields of the chart family. -/
private theorem hamiltonianVectorField_comp_chartMap (b : B) (ξ : F →L[ℝ] ℝ) (y : M) :
    σ.hamiltonianVectorField ((ξ ∘ chartMap (J := J) b) ∘ π) y =
      ∑ i, covectorCoords ξ i • σ.hamiltonianVectorField (chartFamily (J := J) π b · i) y := by
  -- `(ξ ∘ κ) ∘ π = ∑ i, ξ(eᵢ) Gᵢ`, and the coordinate functions are differentiable.
  have hfun : (ξ ∘ chartMap (J := J) b) ∘ π =
      fun y ↦ ∑ i, covectorCoords ξ i • chartFamily (J := J) π b y i := by
    funext y
    simp only [comp_apply, smul_eq_mul, chartFamily_apply, sum_covectorCoords_mul_chartCoord]
  have hd (i : Fin (finrank ℝ F)) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ covectorCoords ξ i • chartFamily (J := J) π b y i) y :=
    (((contMDiff_chartCoord b i).comp h.contMDiff).mdifferentiableAt (by simp)).const_smul _
  rw [hfun, hamiltonianVectorField_fun_sum fun i _ ↦ hd i]
  exact Finset.sum_congr rfl fun i _ ↦
    hamiltonianVectorField_const_smul (f := fun y ↦ chartFamily (J := J) π b y i) _ _

/-- The chart family at `b` is regular along the fibre over `b`. -/
private theorem isRegularPoint_chartFamily {b : B} {y : M} (hy : π y = b) :
    IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (chartFamily (J := J) π b) y := by
  have he : chartFamily (J := J) π b =
      ((Module.finBasis ℝ F).equivFunL : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∘
        (chartMap (J := J) b ∘ π) := by
    funext y i
    rfl
  rw [he]
  refine isRegularPoint_iff_surjective_mvfderiv.2
    (mvfderiv_comp_surjective ?_ _ (Module.finBasis ℝ F).equivFunL.surjective)
  -- `d(κ ∘ π)_y = dκ_b ∘ dπ_y`, and `dκ_b` is the derivative of the chart at `b`.
  rw [mfderiv_comp y ((chartMap b).contMDiff.mdifferentiableAt (by simp)) (h.mdifferentiableAt y),
    hy, (chartMap_eventuallyEq b).mfderiv_eq, mfderiv_extChartAt_self]
  exact h.surjective_mfderiv y

/-- A connected fibre `π⁻¹(b)` is the connected component of each of its points in its level of
the chart family at `b`. -/
private theorem connectedComponentIn_chartFamily {b : B} (hb : IsConnected (π ⁻¹' {b})) {x : M}
    (hx : π x = b) :
    connectedComponentIn (chartFamily (J := J) π b ⁻¹' {chartFamily (J := J) π b x}) x =
      π ⁻¹' {b} := by
  set G := chartFamily (J := J) π b
  -- `κ` is injective near `b`: it agrees there with the chart.
  obtain ⟨W, hWsub, hWo, hbW⟩ := mem_nhds_iff.1
    ((chartMap_eventuallyEq (J := J) b).and (extChartAt_source_mem_nhds (I := J) b))
  have hinj (y : M) (hy : π y ∈ W) (hyG : G y = G x) : π y = b := by
    have h1 := hWsub hy
    have h2 := hWsub hbW
    refine (extChartAt J b).injOn h1.2 h2.2 ?_
    rw [← h1.1, ← h2.1]
    refine (Module.finBasis ℝ F).equivFunL.injective (funext fun i ↦ ?_)
    have := congrFun hyG i
    simp only [G, chartFamily, chartCoord, hx] at this
    exact this
  refine Subset.antisymm ?_ (hb.isPreconnected.subset_connectedComponentIn (by simp [hx])
    fun y hy ↦ ?_)
  · -- The level splits into the closed sets over `b` and over the complement of `W`.
    have hcover : connectedComponentIn (G ⁻¹' {G x}) x ⊆ π ⁻¹' {b} ∪ π ⁻¹' Wᶜ := by
      intro y hy
      have hyG := connectedComponentIn_subset _ _ hy
      rw [mem_preimage, mem_singleton_iff] at hyG
      by_cases hyW : π y ∈ W
      · exact Or.inl (hinj y hyW hyG)
      · exact Or.inr hyW
    have hdisj : connectedComponentIn (G ⁻¹' {G x}) x ∩ (π ⁻¹' {b} ∩ π ⁻¹' Wᶜ) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff,
        mem_empty_iff_false, iff_false, not_and, not_not]
      intro _ hyb
      exact hyb ▸ hbW
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
      (π ⁻¹' {b}) (π ⁻¹' Wᶜ) (isClosed_singleton.preimage h.contMDiff.continuous)
      (hWo.isClosed_compl.preimage h.contMDiff.continuous) hcover hdisj with hsub | hW
    · exact hsub
    · exact absurd (hW (mem_connectedComponentIn (by simp))) (by simpa [hx] using hbW)
  · rw [mem_preimage, mem_singleton_iff] at hy
    simp only [mem_preimage, mem_singleton_iff, G, chartFamily_apply, hy, hx]

variable [FiniteDimensional ℝ E]

private theorem poissonBracket_chartFamily (b : B) (i j : Fin (finrank ℝ F)) (y : M) :
    σ.poissonBracket (chartFamily (J := J) π b · i) (chartFamily (J := J) π b · j) y = 0 :=
  h.poissonBracket_comp_eq_zero ((contMDiff_chartCoord b i).mdifferentiableAt (by simp))
    ((contMDiff_chartCoord b j).mdifferentiableAt (by simp))

variable [T2Space M]

private theorem isCompleteVectorField_chartFamily [BoundarylessManifold I M] (hπ : IsProperMap π)
    (b : B) (i : Fin (finrank ℝ F)) :
    IsCompleteVectorField (σ.hamiltonianVectorField (chartFamily (J := J) π b · i)) :=
  h.isCompleteVectorField_hamiltonianVectorField_comp hπ
    ((contMDiff_chartCoord b i).of_le (by simp))

/-! ### The fibrewise action of `T*_b B` -/

variable [I.Boundaryless] (hπ : IsProperMap π) (hσc : σ.IsClosed)

/-- The action of `ℝⁿ` by the Hamiltonian flows of the coordinates of a chart of `B` at `b`. -/
private def chartAction (b : B) :
    (Fin (finrank ℝ F) → ℝ) →+ Additive (M ≃ₘ^∞⟮I, I⟯ M) :=
  IsSymplectic.hamiltonianFlowAction ⟨hσc, hσ⟩ (h.contMDiff_chartFamily (J := J) b)
    (h.poissonBracket_chartFamily b) (h.isCompleteVectorField_chartFamily hπ b)

/-- The orbit of `x` along the line through the coordinates of a covector `ξ` at `b` under the
chart action is an integral curve of the Hamiltonian vector field of `(ξ ∘ κ) ∘ π`, where `κ` is
the chart map at `b`. -/
private theorem isMIntegralCurve_chartAction (b : B) (ξ : F →L[ℝ] ℝ) (x : M) :
    IsMIntegralCurve (fun t : ℝ ↦ (h.chartAction hπ hσc b (t • covectorCoords ξ)).toMul x)
      (σ.hamiltonianVectorField ((ξ ∘ chartMap (J := J) b) ∘ π)) := by
  have hγ : IsMIntegralCurve (fun t : ℝ ↦ (h.chartAction hπ hσc b (t • covectorCoords ξ)).toMul x)
      fun y ↦ ∑ i, covectorCoords ξ i • σ.hamiltonianVectorField (chartFamily (J := J) π b · i) y :=
    IsSymplectic.isMIntegralCurve_hamiltonianFlowAction_smul ⟨hσc, hσ⟩
      (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
      (h.isCompleteVectorField_chartFamily hπ b) (covectorCoords ξ) x
  refine fun t ↦ (hγ t).congr_mfderiv ?_
  rw [h.hamiltonianVectorField_comp_chartMap]

/-- The chart action preserves the fibres of `π`. -/
private theorem apply_chartAction (b : B) (v : Fin (finrank ℝ F) → ℝ) (x : M) :
    π ((h.chartAction hπ hσc b v).toMul x) = π x := by
  set ξ := covectorCoords.symm v
  have hg : MDifferentiable J 𝓘(ℝ) (ξ ∘ chartMap (J := J) b) :=
    (ξ.contMDiff.comp (chartMap b).contMDiff).mdifferentiable (by simp)
  simpa [ξ, (h.chartAction hπ hσc b).map_zero] using
    h.apply_eq_of_isMIntegralCurve_hamiltonianVectorField_comp
      (h.isMIntegralCurve_chartAction hπ hσc b ξ x) (fun _ ↦ hg _) 0 1

private theorem chartAction_mem (b : B) (v : Fin (finrank ℝ F) → ℝ) (x : π ⁻¹' {b}) :
    (h.chartAction hπ hσc b v).toMul x ∈ π ⁻¹' {b} := by
  rw [mem_preimage, h.apply_chartAction hπ hσc b]
  exact x.2

/-- The chart action of `v` restricted to the fibre over `b`. -/
private def chartHomeomorph (b : B) (v : Fin (finrank ℝ F) → ℝ) : π ⁻¹' {b} ≃ₜ π ⁻¹' {b} :=
  (h.chartAction hπ hσc b v).toMul.toHomeomorph.subtype fun x ↦ by
    rw [mem_preimage, mem_preimage, Diffeomorph.coe_toHomeomorph, h.apply_chartAction]

private theorem coe_chartHomeomorph_apply (b : B) (v : Fin (finrank ℝ F) → ℝ) (x : π ⁻¹' {b}) :
    (h.chartHomeomorph hπ hσc b v x : M) = (h.chartAction hπ hσc b v).toMul x :=
  rfl

/-- **The fibrewise action of the cotangent space.** For a Lagrangian fibration `π` with proper
projection and a closed form `σ`, a covector `ξ ∈ T*_b B` acts on the fibre `π⁻¹(b)` by the
time-one map of the Hamiltonian flow of `g ∘ π`, for any function `g` on `B` differentiable at `b`
with `dg_b = ξ` whose Hamiltonian vector field `X_{g ∘ π}` is `C¹`, for instance any `C²` function
`g` with `dg_b = ξ` (`IsLagrangianFibration.coe_fiberAction_smul_apply_eq_flowOf`,
`IsLagrangianFibration.coe_fiberAction_apply_eq_globalFlow`). For any `g` differentiable at `b`
with `dg_b = ξ`, the curve `t ↦ (t ξ) • x` is an integral curve of `X_{g ∘ π}`
(`IsLagrangianFibration.isMIntegralCurve_fiberAction`). Covectors at `b` are read in the
model space `F` of `B`. This is a homomorphism to the group of self-homeomorphisms of the fibre,
written additively: `ξ + η` acts as `ξ` after `η`. -/
def fiberAction (b : B) : (F →L[ℝ] ℝ) →+ Additive (π ⁻¹' {b} ≃ₜ π ⁻¹' {b}) where
  toFun ξ := Additive.ofMul (h.chartHomeomorph hπ hσc b (covectorCoords ξ))
  map_zero' := by
    refine Additive.toMul.injective (Homeomorph.ext fun x ↦ Subtype.ext ?_)
    rw [toMul_ofMul, coe_chartHomeomorph_apply, map_zero, map_zero, toMul_zero, toMul_zero,
      Diffeomorph.coe_one, Homeomorph.one_apply, id_eq]
  map_add' ξ η := by
    refine Additive.toMul.injective (Homeomorph.ext fun x ↦ Subtype.ext ?_)
    rw [toMul_ofMul, coe_chartHomeomorph_apply, map_add, map_add, toMul_add, toMul_add,
      Homeomorph.mul_apply, toMul_ofMul, toMul_ofMul, Diffeomorph.mul_apply,
      coe_chartHomeomorph_apply, coe_chartHomeomorph_apply]

private theorem coe_fiberAction_apply (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) :
    ((h.fiberAction hπ hσc b ξ).toMul x : M) =
      (h.chartAction hπ hσc b (covectorCoords ξ)).toMul x :=
  rfl

/-- **The fibrewise action is generated by vertical Hamiltonian flows.** If `g : B → ℝ` is
differentiable at `b` with `dg_b = ξ`, then `t ↦ (t ξ) • x` is an integral curve of the
Hamiltonian vector field of `g ∘ π`, for every point `x` of the fibre over `b`. -/
theorem isMIntegralCurve_fiberAction (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) {g : B → ℝ}
    (hg : MDifferentiableAt J 𝓘(ℝ) g b) (hgξ : mvfderiv J g b = ξ) :
    IsMIntegralCurve (fun t : ℝ ↦ ((h.fiberAction hπ hσc b (t • ξ)).toMul x : M))
      (σ.hamiltonianVectorField (g ∘ π)) := by
  have hcurve : (fun t : ℝ ↦ ((h.fiberAction hπ hσc b (t • ξ)).toMul x : M)) =
      fun t ↦ (h.chartAction hπ hσc b (t • covectorCoords ξ)).toMul x := by
    funext t
    rw [coe_fiberAction_apply, map_smul]
  rw [hcurve]
  refine fun t ↦ (h.isMIntegralCurve_chartAction hπ hσc b ξ x t).congr_mfderiv ?_
  -- The curve stays in the fibre over `b`, where both fields only depend on the covector `ξ`.
  have hb : π ((h.chartAction hπ hσc b (t • covectorCoords ξ)).toMul x) = b :=
    h.chartAction_mem hπ hσc b _ x
  have hd : MDifferentiableAt J 𝓘(ℝ) (ξ ∘ chartMap (J := J) b) b :=
    (ξ.contMDiff.comp (chartMap b).contMDiff).mdifferentiableAt (by simp)
  rw [hamiltonianVectorField_comp_eq_of_mvfderiv_eq (h.mdifferentiableAt _)
    (by rw [hb]; exact hd) (by rw [hb]; exact hg) (by rw [hb, mvfderiv_comp_chartMap, hgξ])]

/-- **The fibrewise action is a vertical Hamiltonian flow.** If `g : B → ℝ` is differentiable at
`b` with `dg_b = ξ` and the Hamiltonian vector field of `g ∘ π` is `C¹`, then `t ξ` moves each point
of the fibre over `b` by the time-`t` map of the maximal flow of `g ∘ π`. In particular the action
does not depend on the chart used to construct it. -/
theorem coe_fiberAction_smul_apply_eq_flowOf (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) {g : B → ℝ}
    (hg : MDifferentiableAt J 𝓘(ℝ) g b) (hgξ : mvfderiv J g b = ξ)
    (hv : ContMDiff I I.tangent 1
      fun y ↦ (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M)) (t : ℝ) :
    ((h.fiberAction hπ hσc b (t • ξ)).toMul x : M) =
      flowOf (σ.hamiltonianVectorField (g ∘ π)) t x := by
  have := flowOf_eq_of_isMIntegralCurve hv (h.isMIntegralCurve_fiberAction hπ hσc b ξ x hg hgξ) t
  simpa using this.symm

/-- **The fibrewise action of a `C²` function is its vertical Hamiltonian flow.** If `g : B → ℝ` is
`C²` with `dg_b = ξ`, then `t ξ` moves each point of the fibre over `b` by the time-`t` map of the
maximal flow of `g ∘ π`. -/
theorem coe_fiberAction_smul_apply_eq_flowOf_of_contMDiff (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b})
    {g : B → ℝ} (hg : ContMDiff J 𝓘(ℝ) 2 g) (hgξ : mvfderiv J g b = ξ) (t : ℝ) :
    ((h.fiberAction hπ hσc b (t • ξ)).toMul x : M) =
      flowOf (σ.hamiltonianVectorField (g ∘ π)) t x :=
  h.coe_fiberAction_smul_apply_eq_flowOf hπ hσc b ξ x ((hg b).mdifferentiableAt (by simp)) hgξ
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp)
      (by rw [one_add_one_eq_two]; exact hg.comp (h.contMDiff.of_le (by simp)))) t

/-- If `g : B → ℝ` is differentiable at `b` with `dg_b = ξ` and the Hamiltonian vector field of
`g ∘ π` is `C¹` and complete, then `t ξ` moves each point of the fibre over `b` by the time-`t` map
of the flow of `g ∘ π`. -/
theorem coe_fiberAction_smul_apply_eq_globalFlow (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b})
    {g : B → ℝ} (hg : MDifferentiableAt J 𝓘(ℝ) g b) (hgξ : mvfderiv J g b = ξ)
    (hv : ContMDiff I I.tangent 1
      fun y ↦ (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M))
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π))) (t : ℝ) :
    ((h.fiberAction hπ hσc b (t • ξ)).toMul x : M) =
      globalFlow (σ.hamiltonianVectorField (g ∘ π)) hv hc t x := by
  rw [h.coe_fiberAction_smul_apply_eq_flowOf hπ hσc b ξ x hg hgξ hv, flowOf_eq_globalFlow hv hc]

/-- **The fibrewise action is the time-one map of a vertical Hamiltonian flow.** If `g : B → ℝ` is
differentiable at `b` with `dg_b = ξ` and the Hamiltonian vector field of `g ∘ π` is `C¹` and
complete, then `ξ` moves each point of the fibre over `b` by the time-one map of the flow of
`g ∘ π`. -/
theorem coe_fiberAction_apply_eq_globalFlow (b : B) (ξ : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) {g : B → ℝ}
    (hg : MDifferentiableAt J 𝓘(ℝ) g b) (hgξ : mvfderiv J g b = ξ)
    (hv : ContMDiff I I.tangent 1
      fun y ↦ (⟨y, σ.hamiltonianVectorField (g ∘ π) y⟩ : TangentBundle I M))
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField (g ∘ π))) :
    ((h.fiberAction hπ hσc b ξ).toMul x : M) =
      globalFlow (σ.hamiltonianVectorField (g ∘ π)) hv hc 1 x := by
  simpa using h.coe_fiberAction_smul_apply_eq_globalFlow hπ hσc b ξ x hg hgξ hv hc 1

/-- **The fibrewise action through the flows of a family of functions on the base.** Let
`κ : B → ℝ^ι` be differentiable at `b`, such that the functions `κᵢ ∘ π` form a smooth family with
complete Hamiltonian vector fields (they Poisson-commute by
`IsLagrangianFibration.poissonBracket_comp_eq_zero`). Then the covector `∑ i, vᵢ dκᵢ` at `b` acts
on the fibre over `b` as `v` does under the Hamiltonian flow action of the family `κ ∘ π`. -/
theorem coe_fiberAction_apply_eq_hamiltonianFlowAction {ι : Type*} [Fintype ι] {κ : B → ι → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ fun y ↦ κ (π y))
    (hcomm : ∀ i j y, σ.poissonBracket (fun y ↦ κ (π y) i) (fun y ↦ κ (π y) j) y = 0)
    (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (fun y ↦ κ (π y) i))) {b : B}
    (hκ : ∀ i, MDifferentiableAt J 𝓘(ℝ) (κ · i) b) (v : ι → ℝ) (x : π ⁻¹' {b}) :
    ((h.fiberAction hπ hσc b (∑ i, v i • mvfderiv J (κ · i) b : F →L[ℝ] ℝ)).toMul x : M) =
      (IsSymplectic.hamiltonianFlowAction ⟨hσc, hσ⟩ hF hcomm hc v).toMul x := by
  set g : B → ℝ := fun c ↦ ∑ i, v i • κ c i
  have hFi (i : ι) : ContMDiff I 𝓘(ℝ) ∞ (fun y ↦ κ (π y) i) := contMDiff_pi_module_iff.1 hF i
  have hgπ : ContMDiff I 𝓘(ℝ) ∞ (g ∘ π) :=
    contMDiff_finsetSum fun i _ ↦
      (contMDiff_const : ContMDiff I 𝓘(ℝ) ∞ fun _ : M ↦ v i).smul (hFi i)
  -- `X_{g ∘ π} = ∑ i, vᵢ X_{κᵢ ∘ π}`, the vector field generating the line through `v`.
  have hX : σ.hamiltonianVectorField (g ∘ π) =
      fun y ↦ ∑ i, v i • σ.hamiltonianVectorField (fun y ↦ κ (π y) i) y := by
    funext y
    have hfun : g ∘ π = fun y ↦ ∑ i, v i • κ (π y) i := rfl
    rw [hfun, hamiltonianVectorField_fun_sum (F := fun i y ↦ v i • κ (π y) i) fun i _ ↦
      ((hFi i).mdifferentiableAt (by simp)).const_smul (v i)]
    exact Finset.sum_congr rfl fun i _ ↦
      hamiltonianVectorField_const_smul (f := fun y ↦ κ (π y) i) _ _
  have hκv (i : ι) : MDifferentiableAt J 𝓘(ℝ) (fun c ↦ v i • κ c i) b := (hκ i).const_smul (v i)
  have hg : MDifferentiableAt J 𝓘(ℝ) g b := by
    convert MDifferentiableAt.sum (t := Finset.univ) fun i _ ↦ hκv i using 1
    funext c
    simp [g]
  have hgξ : mvfderiv J g b = (∑ i, v i • mvfderiv J (κ · i) b : F →L[ℝ] ℝ) := by
    rw [mvfderiv_fun_sum (f := fun i c ↦ v i • κ c i) fun i _ ↦ hκv i]
    exact Finset.sum_congr rfl fun i _ ↦ mvfderiv_const_smul (hκ i) (v i)
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (f := g ∘ π) (by simp)
    (hgπ.of_le (by simp))
  have hγ := IsSymplectic.isMIntegralCurve_hamiltonianFlowAction_smul ⟨hσc, hσ⟩ hF hcomm hc v x
  rw [← hX] at hγ
  have h1 := h.coe_fiberAction_smul_apply_eq_flowOf hπ hσc b _ x hg hgξ hv 1
  have h2 := flowOf_eq_of_isMIntegralCurve hv hγ 1
  simp only [one_smul, zero_smul, map_zero, toMul_zero, Diffeomorph.coe_one, id_eq] at h1 h2
  exact h1.trans h2

/-- **The orbit maps of the fibrewise action are smooth.** -/
theorem contMDiff_fiberAction_apply (b : B) (x : π ⁻¹' {b}) :
    ContMDiff 𝓘(ℝ, F →L[ℝ] ℝ) I ∞ fun ξ ↦ ((h.fiberAction hπ hσc b ξ).toMul x : M) :=
  (IsSymplectic.contMDiff_hamiltonianFlowAction_apply ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily hπ b) x).comp
    covectorCoords.toContinuousLinearMap.contMDiff

/-- The orbit maps of the fibrewise action are continuous. -/
theorem continuous_fiberAction_apply (b : B) (x : π ⁻¹' {b}) :
    Continuous fun ξ ↦ (h.fiberAction hπ hσc b ξ).toMul x :=
  (h.contMDiff_fiberAction_apply hπ hσc b x).continuous.subtype_mk _

/-- The derivative of an orbit map of the fibrewise action is that of the chart action, read in
the coordinates of covectors. -/
private theorem mfderiv_fiberAction_apply_eq_comp (b : B) (x : π ⁻¹' {b}) (ξ : F →L[ℝ] ℝ) :
    mfderiv 𝓘(ℝ, F →L[ℝ] ℝ) I (fun ξ ↦ ((h.fiberAction hπ hσc b ξ).toMul x : M)) ξ =
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) I
          (fun v ↦ (h.chartAction hπ hσc b v).toMul (x : M)) (covectorCoords ξ)).comp
        (covectorCoords (F := F)).toContinuousLinearMap :=
  ((IsSymplectic.contMDiff_hamiltonianFlowAction_apply ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily hπ b) x).mdifferentiableAt (by simp)
    (x := covectorCoords ξ)).hasMFDerivAt.comp ξ
    (covectorCoords (F := F)).toContinuousLinearMap.hasMFDerivAt |>.mfderiv

/-- **The derivative of an orbit map of the fibrewise action.** If `g : B → ℝ` is differentiable at
`b` with `dg_b = η`, the derivative at `ξ` of the orbit map `ξ ↦ ξ • x` sends `η` to the
Hamiltonian vector of `g ∘ π` at `ξ • x`. -/
theorem mfderiv_fiberAction_apply (b : B) (x : π ⁻¹' {b}) (ξ η : F →L[ℝ] ℝ) {g : B → ℝ}
    (hg : MDifferentiableAt J 𝓘(ℝ) g b) (hgη : mvfderiv J g b = η) :
    mfderiv 𝓘(ℝ, F →L[ℝ] ℝ) I (fun ξ ↦ ((h.fiberAction hπ hσc b ξ).toMul x : M)) ξ η =
      σ.hamiltonianVectorField (g ∘ π) ((h.fiberAction hπ hσc b ξ).toMul x) := by
  rw [h.mfderiv_fiberAction_apply_eq_comp hπ hσc b x ξ]
  refine (IsSymplectic.mfderiv_hamiltonianFlowAction_apply ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily hπ b) x _ _).trans ?_
  refine (h.hamiltonianVectorField_comp_chartMap b η _).symm.trans ?_
  -- The point `ξ • x` lies in the fibre over `b`, where both fields only depend on the covector.
  have hd : MDifferentiableAt J 𝓘(ℝ) (η ∘ chartMap (J := J) b) b :=
    (η.contMDiff.comp (chartMap b).contMDiff).mdifferentiableAt (by simp)
  have key (y : M) (hy : π y = b) : σ.hamiltonianVectorField ((η ∘ chartMap (J := J) b) ∘ π) y =
      σ.hamiltonianVectorField (g ∘ π) y :=
    hamiltonianVectorField_comp_eq_of_mvfderiv_eq (h.mdifferentiableAt _) (by rw [hy]; exact hd)
      (by rw [hy]; exact hg) (by rw [hy, mvfderiv_comp_chartMap, hgη])
  exact key _ (h.chartAction_mem hπ hσc b _ x)

/-- **The orbit maps of the fibrewise action are immersions.** -/
theorem injective_mfderiv_fiberAction_apply (b : B) (x : π ⁻¹' {b}) (ξ : F →L[ℝ] ℝ) :
    Injective
      (mfderiv 𝓘(ℝ, F →L[ℝ] ℝ) I (fun ξ ↦ ((h.fiberAction hπ hσc b ξ).toMul x : M)) ξ) := by
  rw [h.mfderiv_fiberAction_apply_eq_comp hπ hσc b x ξ]
  exact (IsSymplectic.injective_mfderiv_hamiltonianFlowAction_apply ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily hπ b)
    (h.isRegularPoint_chartFamily (h.chartAction_mem hπ hσc b _ x))).comp
    covectorCoords.injective

/-! ### The period lattice -/

/-- **The period lattice** `Λ_b ⊆ T*_b B` of a Lagrangian fibration: the subgroup of covectors at
`b` acting trivially on the fibre `π⁻¹(b)`. It is discrete when the fibre is nonempty
(`IsLagrangianFibration.discreteTopology_periodLattice`), and for a regular Lagrangian torus
fibration it is a full lattice (`IsLagrangianTorusFibration.isZLattice_periodLattice`). -/
def periodLattice (b : B) : AddSubgroup (F →L[ℝ] ℝ) :=
  (h.fiberAction hπ hσc b).ker

@[simp]
theorem ker_fiberAction (b : B) : (h.fiberAction hπ hσc b).ker = h.periodLattice hπ hσc b :=
  (rfl)

/-- A covector lies in the period lattice exactly when it fixes every point of the fibre. -/
@[simp]
theorem mem_periodLattice {b : B} {ξ : F →L[ℝ] ℝ} :
    ξ ∈ h.periodLattice hπ hσc b ↔ ∀ x, (h.fiberAction hπ hσc b ξ).toMul x = x := by
  simp only [periodLattice, AddMonoidHom.mem_ker, ← toMul_eq_one, Homeomorph.ext_iff,
    Homeomorph.one_apply]

/-- **The period lattice is discrete.** If the fibre over `b` is nonempty, the period lattice at
`b` is a discrete subgroup of `T*_b B`. -/
theorem discreteTopology_periodLattice {b : B} (hb : (π ⁻¹' {b}).Nonempty) :
    DiscreteTopology (h.periodLattice hπ hσc b) := by
  obtain ⟨x, hx⟩ := hb
  have hxb : π x = b := hx
  -- `Λ_b` embeds, by its coordinates, into the stabilizer of `x` for the chart action, which is
  -- discrete because `x` is a regular point of the chart family.
  have := IsSymplectic.discreteTopology_hamiltonianFlowStabilizer ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily hπ b) (h.isRegularPoint_chartFamily hxb)
  let f : h.periodLattice hπ hσc b → IsSymplectic.hamiltonianFlowStabilizer ⟨hσc, hσ⟩
      (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
      (h.isCompleteVectorField_chartFamily hπ b) x :=
    fun ξ ↦ ⟨covectorCoords ξ, (IsSymplectic.mem_hamiltonianFlowStabilizer _ _ _ _).2 <|
      congrArg Subtype.val ((h.mem_periodLattice hπ hσc).1 ξ.2 ⟨x, hx⟩)⟩
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.1
      (covectorCoords.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  exact hf.discreteTopology

end IsLagrangianFibration

namespace IsLagrangianTorusFibration

open IsLagrangianFibration

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]
  (h : hσ.IsLagrangianTorusFibration J π)
include h

omit [FiniteDimensional ℝ F] [IsManifold J ∞ B] [T2Space B] [T2Space M] [I.Boundaryless] in
/-- The dimension count `2 n = dim M` in the form the Liouville–Arnold lemmas expect. -/
private theorem two_mul_card_eq_finrank [Nonempty M] :
    2 * Fintype.card (Fin (finrank ℝ F)) = finrank ℝ E := by
  rw [Fintype.card_fin, h.two_mul_finrank]

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] in
/-- The connected component through a point of the fibre over `b` of its level of the chart family
at `b` consists of regular points of the chart family. -/
private theorem isRegularPoint_chartFamily_of_mem_connectedComponentIn {b : B} {x : M}
    (hx : π x = b) {y : M}
    (hy : y ∈ connectedComponentIn (chartFamily (J := J) π b ⁻¹' {chartFamily (J := J) π b x}) x) :
    IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (chartFamily (J := J) π b) y := by
  rw [h.connectedComponentIn_chartFamily (h.isConnected_preimage_singleton b) hx] at hy
  exact h.isRegularPoint_chartFamily hy

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] in
/-- The connected component through a point of the fibre over `b` of its level of the chart family
at `b` is compact. -/
private theorem isCompact_connectedComponentIn_chartFamily {b : B} {x : M} (hx : π x = b) :
    IsCompact
      (connectedComponentIn (chartFamily (J := J) π b ⁻¹' {chartFamily (J := J) π b x}) x) := by
  rw [h.connectedComponentIn_chartFamily (h.isConnected_preimage_singleton b) hx]
  exact h.isCompact_preimage_singleton b

/-- **The fibres of a regular Lagrangian torus fibration are tori.** If `σ` is closed, so
symplectic, every fibre of a regular Lagrangian torus fibration `π : M → B` over a Hausdorff
manifold of dimension `n` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus (hσc : σ.IsClosed) (b : B) :
    Nonempty (π ⁻¹' {b} ≃ₜ UnitAddTorus (Fin (finrank ℝ F))) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have hxb : π x = b := hx
  have : Nonempty M := ⟨x⟩
  have hcomp := h.connectedComponentIn_chartFamily (J := J) (h.isConnected_preimage_singleton b)
    hxb
  obtain ⟨φ⟩ := IsSymplectic.nonempty_homeomorph_unitAddTorus ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (fun _ ↦ h.isRegularPoint_chartFamily_of_mem_connectedComponentIn hxb)
    h.two_mul_card_eq_finrank (h.isCompact_connectedComponentIn_chartFamily hxb)
  exact ⟨(Homeomorph.setCongr hcomp.symm).trans φ⟩

variable (hσc : σ.IsClosed)

/-- **The period lattice is discrete.** For a regular Lagrangian torus fibration, the period
lattice at `b` is a discrete subgroup of `T*_b B`, the fibres being nonempty. -/
theorem discreteTopology_periodLattice (b : B) :
    DiscreteTopology (h.periodLattice h.isProperMap hσc b) :=
  IsLagrangianFibration.discreteTopology_periodLattice h.toIsLagrangianFibration h.isProperMap hσc
    (h.isConnected_preimage_singleton b).nonempty

/-- **The fibrewise action is transitive.** For a regular Lagrangian torus fibration, any two
points of a fibre are related by a covector. -/
theorem exists_fiberAction_apply_eq {b : B} (x y : π ⁻¹' {b}) :
    ∃ ξ, (h.fiberAction h.isProperMap hσc b ξ).toMul x = y := by
  have hxb : π x = b := x.2
  have : Nonempty M := ⟨x⟩
  have hcomp := h.connectedComponentIn_chartFamily (J := J) (h.isConnected_preimage_singleton b)
    hxb
  obtain ⟨v, hv⟩ := IsSymplectic.exists_hamiltonianFlowAction_apply_eq ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily h.isProperMap b) h.two_mul_card_eq_finrank
    (fun _ ↦ h.isRegularPoint_chartFamily_of_mem_connectedComponentIn hxb)
    (by rw [hcomp]; exact y.2)
  refine ⟨covectorCoords.symm v, Subtype.ext ?_⟩
  rw [coe_fiberAction_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact hv

/-- For a regular Lagrangian torus fibration, the period lattice at `b` is the stabilizer of every
point of the fibre over `b`. -/
theorem mem_periodLattice_iff_fiberAction_apply_eq {b : B} (x : π ⁻¹' {b}) {ξ : F →L[ℝ] ℝ} :
    ξ ∈ h.periodLattice h.isProperMap hσc b ↔
      (h.fiberAction h.isProperMap hσc b ξ).toMul x = x := by
  refine ⟨fun hξ ↦ (h.mem_periodLattice h.isProperMap hσc).1 hξ x, fun hξ ↦ ?_⟩
  refine (h.mem_periodLattice h.isProperMap hσc).2 fun y ↦ ?_
  -- Write `y = η • x`; the action is commutative.
  obtain ⟨η, rfl⟩ := h.exists_fiberAction_apply_eq hσc x y
  rw [← Homeomorph.mul_apply, ← toMul_add, ← map_add, add_comm, map_add, toMul_add,
    Homeomorph.mul_apply, hξ]

/-- For a regular Lagrangian torus fibration and a family `κ : B → ℝ^ι` as in
`IsLagrangianFibration.coe_fiberAction_apply_eq_hamiltonianFlowAction`, the covector `∑ i, vᵢ dκᵢ`
at `b` is a period exactly when `v` stabilizes a point `x` of the fibre over `b` under the
Hamiltonian flow action of `κ ∘ π`. -/
theorem mem_periodLattice_iff_mem_hamiltonianFlowStabilizer {ι : Type*} [Fintype ι]
    {κ : B → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ fun y ↦ κ (π y))
    (hcomm : ∀ i j y, σ.poissonBracket (fun y ↦ κ (π y) i) (fun y ↦ κ (π y) j) y = 0)
    (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (fun y ↦ κ (π y) i))) {b : B}
    (hκ : ∀ i, MDifferentiableAt J 𝓘(ℝ) (κ · i) b) (v : ι → ℝ) (x : π ⁻¹' {b}) :
    (∑ i, v i • mvfderiv J (κ · i) b : F →L[ℝ] ℝ) ∈ h.periodLattice h.isProperMap hσc b ↔
      v ∈ IsSymplectic.hamiltonianFlowStabilizer ⟨hσc, hσ⟩ hF hcomm hc x := by
  rw [h.mem_periodLattice_iff_fiberAction_apply_eq hσc x,
    IsSymplectic.mem_hamiltonianFlowStabilizer, Subtype.ext_iff,
    h.coe_fiberAction_apply_eq_hamiltonianFlowAction h.isProperMap hσc hF hcomm hc hκ v x]

/-- Two covectors act alike on a point of a fibre exactly when they differ by a period. -/
theorem fiberAction_apply_eq_iff {b : B} (x : π ⁻¹' {b}) {ξ η : F →L[ℝ] ℝ} :
    (h.fiberAction h.isProperMap hσc b ξ).toMul x = (h.fiberAction h.isProperMap hσc b η).toMul x ↔
      -ξ + η ∈ h.periodLattice h.isProperMap hσc b := by
  rw [h.mem_periodLattice_iff_fiberAction_apply_eq hσc x, map_add, toMul_add, Homeomorph.mul_apply,
    map_neg, toMul_neg, Homeomorph.inv_apply, Homeomorph.symm_apply_eq, eq_comm]

/-- **The period lattice is cocompact.** For a regular Lagrangian torus fibration, the quotient of
`T*_b B` by the period lattice at `b` is compact. -/
theorem compactSpace_quotient_periodLattice (b : B) :
    CompactSpace ((F →L[ℝ] ℝ) ⧸ h.periodLattice h.isProperMap hσc b) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have hxb : π x = b := hx
  have : Nonempty M := ⟨x⟩
  set S := IsSymplectic.hamiltonianFlowStabilizer ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily h.isProperMap b) x
  have := IsSymplectic.compactSpace_quotient_hamiltonianFlowStabilizer ⟨hσc, hσ⟩
    (h.contMDiff_chartFamily (J := J) b) (h.poissonBracket_chartFamily b)
    (h.isCompleteVectorField_chartFamily h.isProperMap b) h.two_mul_card_eq_finrank
    (fun _ ↦ h.isRegularPoint_chartFamily_of_mem_connectedComponentIn hxb)
    (h.isCompact_connectedComponentIn_chartFamily hxb)
  -- The coordinates of covectors carry the stabilizer of `x` into the period lattice, so they
  -- induce a continuous surjection between the quotients.
  have hle : S ≤ (h.periodLattice h.isProperMap hσc b).comap
      ((covectorCoords (F := F)).symm : (Fin (finrank ℝ F) → ℝ) →+ F →L[ℝ] ℝ) := by
    intro v hv
    rw [AddSubgroup.mem_comap, h.mem_periodLattice_iff_fiberAction_apply_eq hσc ⟨x, hx⟩]
    refine Subtype.ext ?_
    simp only [coe_fiberAction_apply, AddMonoidHom.coe_ofClass,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (IsSymplectic.mem_hamiltonianFlowStabilizer _ _ _ _).1 hv
  let q := QuotientAddGroup.map S (h.periodLattice h.isProperMap hσc b) _ hle
  have hq : Continuous q :=
    (QuotientAddGroup.isQuotientMap_mk S).continuous_iff.2 <|
      QuotientAddGroup.continuous_mk.comp covectorCoords.symm.continuous
  refine Function.Surjective.compactSpace hq fun ξ ↦ ?_
  obtain ⟨ξ, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  exact ⟨covectorCoords ξ, by simp [q]⟩

/-- **A fibre of a regular Lagrangian torus fibration is the quotient of the cotangent space by the
period lattice.** For a point `x` of the fibre over `b`, the orbit map `ξ ↦ ξ • x` descends to a
homeomorphism `T*_b B ⧸ Λ_b ≃ₜ π⁻¹(b)`. -/
def quotientPeriodLatticeHomeomorph {b : B} (x : π ⁻¹' {b}) :
    (F →L[ℝ] ℝ) ⧸ h.periodLattice h.isProperMap hσc b ≃ₜ π ⁻¹' {b} :=
  haveI := h.compactSpace_quotient_periodLattice hσc b
  let f : (F →L[ℝ] ℝ) ⧸ h.periodLattice h.isProperMap hσc b → π ⁻¹' {b} :=
    Quotient.lift (fun ξ ↦ (h.fiberAction h.isProperMap hσc b ξ).toMul x) fun ξ η hξη ↦
      (h.fiberAction_apply_eq_iff hσc x).2 (QuotientAddGroup.leftRel_apply.1 hξη)
  have hf : Bijective f := by
    refine ⟨fun ξ η hξη ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨ξ, rfl⟩ := QuotientAddGroup.mk_surjective ξ
      obtain ⟨η, rfl⟩ := QuotientAddGroup.mk_surjective η
      exact QuotientAddGroup.eq.2 ((h.fiberAction_apply_eq_iff hσc x).1 hξη)
    · obtain ⟨ξ, hξ⟩ := h.exists_fiberAction_apply_eq hσc x y
      exact ⟨ξ, hξ⟩
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (h.continuous_fiberAction_apply h.isProperMap hσc b x))

@[simp]
theorem quotientPeriodLatticeHomeomorph_mk {b : B} (x : π ⁻¹' {b}) (ξ : F →L[ℝ] ℝ) :
    h.quotientPeriodLatticeHomeomorph hσc x ξ = (h.fiberAction h.isProperMap hσc b ξ).toMul x :=
  (rfl)

@[simp]
theorem quotientPeriodLatticeHomeomorph_zero {b : B} (x : π ⁻¹' {b}) :
    h.quotientPeriodLatticeHomeomorph hσc x 0 = x := by
  rw [← QuotientAddGroup.mk_zero, quotientPeriodLatticeHomeomorph_mk, map_zero, toMul_zero,
    Homeomorph.one_apply]

/-- The homeomorphism `T*_b B ⧸ Λ_b ≃ₜ π⁻¹(b)` intertwines the actions of `T*_b B`. -/
@[simp]
theorem quotientPeriodLatticeHomeomorph_add {b : B} (x : π ⁻¹' {b}) (ξ : F →L[ℝ] ℝ)
    (q : (F →L[ℝ] ℝ) ⧸ h.periodLattice h.isProperMap hσc b) :
    h.quotientPeriodLatticeHomeomorph hσc x (ξ + q) =
      (h.fiberAction h.isProperMap hσc b ξ).toMul (h.quotientPeriodLatticeHomeomorph hσc x q) := by
  obtain ⟨η, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [← QuotientAddGroup.mk_add, quotientPeriodLatticeHomeomorph_mk,
    quotientPeriodLatticeHomeomorph_mk, map_add, toMul_add, Homeomorph.mul_apply]

@[simp]
theorem quotientPeriodLatticeHomeomorph_symm_fiberAction_apply {b : B} (x : π ⁻¹' {b})
    (ξ : F →L[ℝ] ℝ) :
    (h.quotientPeriodLatticeHomeomorph hσc x).symm ((h.fiberAction h.isProperMap hσc b ξ).toMul x) =
      ξ := by
  rw [Homeomorph.symm_apply_eq, quotientPeriodLatticeHomeomorph_mk]

@[simp]
theorem quotientPeriodLatticeHomeomorph_symm_apply_self {b : B} (x : π ⁻¹' {b}) :
    (h.quotientPeriodLatticeHomeomorph hσc x).symm x = 0 := by
  rw [Homeomorph.symm_apply_eq, quotientPeriodLatticeHomeomorph_zero]

/-- **The period lattice is a full lattice.** For a regular Lagrangian torus fibration, the period
lattice at `b` spans `T*_b B`, with the discreteness instance
`IsLagrangianTorusFibration.discreteTopology_periodLattice`. -/
theorem isZLattice_periodLattice (b : B) :
    letI := h.discreteTopology_periodLattice hσc b
    IsZLattice ℝ (h.periodLattice h.isProperMap hσc b).toIntSubmodule := by
  have := h.discreteTopology_periodLattice hσc b
  have := h.compactSpace_quotient_periodLattice hσc b
  refine ⟨?_⟩
  rw [AddSubgroup.coe_toIntSubmodule]
  exact AddSubgroup.span_eq_top_of_compactSpace_quotient _

/-- **The period lattice has rank `n`.** For a regular Lagrangian torus fibration over a manifold
of dimension `n`, the period lattice at `b` is a free abelian group of rank `n`. -/
theorem finrank_periodLattice (b : B) :
    finrank ℤ (h.periodLattice h.isProperMap hσc b).toIntSubmodule = finrank ℝ F := by
  have := h.discreteTopology_periodLattice hσc b
  have := h.isZLattice_periodLattice hσc b
  rw [ZLattice.rank ℝ, covectorCoords.toLinearEquiv.finrank_eq, finrank_fin_fun]

end IsLagrangianTorusFibration

end TauCeti.SmoothTwoForm.IsNondegenerate
