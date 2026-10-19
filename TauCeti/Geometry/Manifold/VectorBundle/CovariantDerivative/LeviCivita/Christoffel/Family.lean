/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Joint regularity of Christoffel symbols in metric families

For a family of nondegenerate bilinear forms `g p x` in linear coordinates, the Christoffel
symbols of `g p` depend jointly on the parameter `p` and the base point `x`. The parameter may
range over an arbitrary smooth manifold. Only the base direction is differentiated when forming
the Christoffel symbols. For symmetric forms these are the coefficients of the individual
Levi-Civita connections.

The results apply on open subsets of the parameter/base product, as required for families of
metrics read in local charts. A `C^m` family has `C^n` Christoffel symbols when `n + 1 ≤ m`.
Nondegeneracy is needed at the point in the local theorem and throughout the domain in the
setwise theorem. Symmetry is unnecessary for regularity; no signature or positivity is assumed.

The construction reuses `christoffelSecondKind` and Mathlib's
`ContMDiffAt.mfderiv` for the smooth dependence of partial derivatives, followed by smooth
inversion of the metric. This supplies the local analytic input for smooth families of
Levi-Civita connections.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press (1983),
  Chapter 3, the coordinate formula for the Levi-Civita connection.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → E →L[ℝ] E →L[ℝ] ℝ} {m n : ℕ∞ω} {z : P × E}

/-- The Christoffel symbols of a `C^m` family of nondegenerate bilinear forms are jointly `C^n`
in parameter and base point at every nondegenerate point, for `n + 1 ≤ m`. -/
theorem contMDiffAt_christoffelSecondKind_family
    (hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) (hnd : (g z.1 z.2).toBilinForm.Nondegenerate) :
    ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) z := by
  -- Explicit scalar parameters let instance synthesis read the nested operator space.
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  -- Differentiate only in the base variable, while both inputs of the family vary.
  have hD : ContMDiffAt (J.prod 𝓘(ℝ, E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) n
      (fun q : P × E ↦ fderiv ℝ (g q.1) q.2) z := by
    have hfamily : ContMDiffAt ((J.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, E))
        𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
        (fun q : (P × E) × E ↦ g q.1.1 q.2) (z, z.2) :=
      hg.comp (z, z.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
    have h := hfamily.mfderiv (fun q : P × E ↦ g q.1) Prod.snd contMDiffAt_snd hnm
    -- Both differentiated manifolds are model vector spaces, so their tangent coordinate
    -- changes are identities. The parameter manifold is not being trivialized here.
    convert h using 1
    ext q : 1
    rw [inTangentCoordinates_eq_mfderiv_comp_abuse (by simp) (by simp)]
    simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq,
      OpenPartialHomeomorph.refl_partialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.coe_trans, PartialEquiv.refl_coe, Function.comp_apply, id_eq,
      Function.comp_id, mfderiv_id, PartialEquiv.coe_trans_symm, PartialEquiv.refl_symm,
      modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
    rw [mfderiv_eq_fderiv]
    -- Evaluate the canonical identifications of tangent spaces to vector spaces.
    ext u v w
    rfl
  -- Raise the index by the inverse metric, which is smooth near the nondegenerate point.
  have hinv : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) n
      (fun q : P × E ↦ (g q.1 q.2).inverse) z :=
    ContDiffAt.comp_contMDiffAt (f := Function.uncurry g)
      (isInvertible_of_separatingLeft hnd.1).contDiffAt_map_inverse
      (hg.of_le (le_self_add.trans hnm))
  have hflip : ContMDiffAt (J.prod 𝓘(ℝ, E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) n
      (fun q : P × E ↦ (fderiv ℝ (g q.1) q.2).flip) z :=
    (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt.comp
      z hD
  -- Compose this inverse with the three permutations of the differentiated metric.
  let : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
  have hcomp : ContMDiffAt (J.prod 𝓘(ℝ, E))
      𝓘(ℝ, (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ compL ℝ E (E →L[ℝ] ℝ) E (g q.1 q.2).inverse) z :=
    (compL ℝ E (E →L[ℝ] ℝ) E).contMDiffAt.comp z hinv
  have hperm : ContMDiffAt (J.prod 𝓘(ℝ, E))
      𝓘(ℝ, (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ compL ℝ E (E →L[ℝ] ℝ) E (g q.1 q.2).inverse ∘L
        (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap) z :=
    ContMDiffAt.clm_comp (𝕜 := ℝ) (F₁ := E →L[ℝ] E →L[ℝ] ℝ)
      (F₂ := E →L[ℝ] E →L[ℝ] ℝ) (F₃ := E →L[ℝ] E) hcomp
      (contMDiffAt_const (c :=
        (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap))
  have hlast := ContMDiffAt.clm_comp (𝕜 := ℝ) (F₁ := E →L[ℝ] E →L[ℝ] ℝ)
    (F₂ := E) (F₃ := E →L[ℝ] E) hperm hflip
  have hfirst := ContMDiffAt.clm_comp (𝕜 := ℝ) (F₁ := E →L[ℝ] E →L[ℝ] ℝ)
    (F₂ := E) (F₃ := E →L[ℝ] E) hcomp hD
  have hsecond := ContMDiffAt.clm_comp (𝕜 := ℝ) (F₁ := E →L[ℝ] E →L[ℝ] ℝ)
    (F₂ := E) (F₃ := E →L[ℝ] E) hcomp hflip
  have : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] E) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] E)
  have hscale : ContDiff ℝ n
      (fun A : E →L[ℝ] E →L[ℝ] E ↦ (2⁻¹ : ℝ) • A) :=
    (contDiff_const (𝕜 := ℝ) (c := (2⁻¹ : ℝ))).smul
      (contDiff_id (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] E) (n := n))
  -- Assemble the Koszul combination and identify it through the evaluation API.
  have hscaled := hscale.contMDiff.contMDiffAt.comp z ((hfirst.add hsecond).sub hlast)
  convert hscaled using 1
  ext q u v
  have hFK : christoffelFirstKind (g q.1) q.2 u v = (2⁻¹ : ℝ) •
      (fderiv ℝ (g q.1) q.2 u v + fderiv ℝ (g q.1) q.2 v u -
        ((fderiv ℝ (g q.1) q.2).flip u).flip v) := by
    ext w
    simp [christoffelFirstKind_apply, div_eq_inv_mul]
  rw [christoffelSecondKind_apply, hFK]
  simp

/-- On an open parameter/base domain, the Christoffel symbols of a `C^m` nondegenerate family
are jointly `C^n`, for `n + 1 ≤ m`. No product decomposition of the domain is required. -/
theorem contMDiffOn_christoffelSecondKind_family {U : Set (P × E)} (hU : IsOpen U)
    (hg : ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) U)
    (hnm : n + 1 ≤ m) (hnd : ∀ q ∈ U, (g q.1 q.2).toBilinForm.Nondegenerate) :
    ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) U :=
  fun q hq ↦ (contMDiffAt_christoffelSecondKind_family
    (hg.contMDiffAt (hU.mem_nhds hq)) hnm (hnd q hq)).contMDiffWithinAt

/-- A globally `C^m` nondegenerate metric family has globally joint `C^n` Christoffel symbols,
for `n + 1 ≤ m`. In particular, a smooth family has smooth Christoffel symbols. -/
theorem contMDiff_christoffelSecondKind_family
    (hg : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g))
    (hnm : n + 1 ≤ m) (hnd : ∀ p x, (g p x).toBilinForm.Nondegenerate) :
    ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) :=
  fun q ↦ contMDiffAt_christoffelSecondKind_family (hg q) hnm (hnd q.1 q.2)

end TauCeti.Manifold
