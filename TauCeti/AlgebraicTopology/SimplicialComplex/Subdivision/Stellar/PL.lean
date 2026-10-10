/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.Topology.PL.FiniteInf
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Piecewise-linear stellar identifications

The inverse of a barycentric stellar identification removes the least coordinate on the
starred face from each of its vertices and transfers the total removed mass to the new
vertex. This formula extends to the whole coordinate space, where it is piecewise affine:
on the polyhedral cell where a particular coordinate is least, the formula is linear.

We identify this formula with the inverse of the existing stellar homeomorphism of finite
weak polyhedra. Both directions therefore have globally PL coordinate extensions. These
are the regularity assertions needed to transport PL charts across stellar moves.
The ambient vertex type may be infinite; only the starred face must be nonempty and finite.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 1–2 (PL maps and barycentric stellar subdivisions).
-/

public section

noncomputable section

open Set TauCeti

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- The continuous linear extension of the barycentric stellar map to coordinate space.
It fixes all old vertices and sends the new vertex to the barycenter of a nonempty starred
face, or to zero if the face is empty. -/
def stellarSubdivisionContinuousLinearMap (σ : Finset ι) (v : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.id ℝ (ι → ℝ) +
    (ContinuousLinearMap.proj v : (ι → ℝ) →L[ℝ] ℝ).smulRight
      (((∑ i ∈ σ, (Finsupp.single i ((σ.card : ℝ)⁻¹) : ι →₀ ℝ)) -
        Finsupp.single v 1 : ι →₀ ℝ) : ι → ℝ)

/-- The forward stellar map's coordinate formula. -/
@[simp]
theorem stellarSubdivisionContinuousLinearMap_apply (σ : Finset ι) (v : ι)
    (x : ι → ℝ) (i : ι) :
    stellarSubdivisionContinuousLinearMap σ v x i =
      x i + x v * ((if i ∈ σ then (σ.card : ℝ)⁻¹ else 0) - if i = v then 1 else 0) := by
  simp [stellarSubdivisionContinuousLinearMap, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- The coordinate extension agrees with the finitely supported stellar map. -/
@[simp]
theorem stellarSubdivisionContinuousLinearMap_coe (σ : Finset ι) (v : ι) (x : ι →₀ ℝ) :
    stellarSubdivisionContinuousLinearMap σ v x =
      (stellarSubdivisionLinearMap σ v x : ι → ℝ) := by
  classical
  ext i
  simp

/-- Extend the inverse stellar identification to coordinate space by transferring the least
coordinate on `σ` to `v`. On an original polyhedron with unused vertex `v`, this is the inverse
of the barycentric stellar map. -/
def stellarSubdivisionInverseExtension (σ : Finset ι) (hσ : σ.Nonempty) (v : ι)
    (x : ι → ℝ) : ι → ℝ :=
  x + σ.inf' hσ x •
    (((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1 : ι →₀ ℝ) : ι → ℝ)

/-- The inverse stellar extension's coordinate formula. -/
@[simp]
theorem stellarSubdivisionInverseExtension_apply (σ : Finset ι) (hσ : σ.Nonempty) (v : ι)
    (x : ι → ℝ) (i : ι) :
    stellarSubdivisionInverseExtension σ hσ v x i =
      x i + σ.inf' hσ x *
        ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
  simp [stellarSubdivisionInverseExtension, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- The inverse stellar extension is piecewise affine on the entire coordinate space.
Its cells are the regions on which one of the starred-face coordinates is least. -/
theorem isPiecewiseAffineOn_stellarSubdivisionInverseExtension (σ : Finset ι) (hσ : σ.Nonempty)
    (v : ι) : IsPiecewiseAffineOn (stellarSubdivisionInverseExtension σ hσ v) Set.univ := by
  let f (i : ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).toContinuousAffineMap
  let d : ι → ℝ :=
    ((σ.card : ℝ) • Finsupp.single v 1 - ∑ i ∈ σ, Finsupp.single i 1 : ι →₀ ℝ)
  let A (i : σ) : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
    (ContinuousLinearMap.id ℝ (ι → ℝ) +
      (ContinuousLinearMap.proj (i : ι)).smulRight d).toContinuousAffineMap
  refine isPiecewiseAffineOn_of_finite (C := σ.infCell f) (A := A)
    (σ.isConvexPolyhedron_infCell f) (σ.subset_iUnion_infCell hσ f) ?_
  intro i x hx
  have hmin : σ.inf' hσ x = x i :=
    σ.infAffine_eq_of_mem_infCell hσ f i hx.2
  simp [stellarSubdivisionInverseExtension, A, d, hmin]

omit [DecidableEq ι] in
/-- The barycentric coordinate extension cancels the inverse extension on coordinates
vanishing at the new vertex. No positivity, support, or normalization is needed. -/
@[simp]
theorem stellarSubdivisionContinuousLinearMap_stellarSubdivisionInverseExtension
    {σ : Finset ι} (hσ : σ.Nonempty) {v : ι} (hvσ : v ∉ σ)
    {x : ι → ℝ} (hxv : x v = 0) :
    stellarSubdivisionContinuousLinearMap σ v (stellarSubdivisionInverseExtension σ hσ v x) =
      x := by
  classical
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  ext i
  simp only [stellarSubdivisionContinuousLinearMap_apply, stellarSubdivisionInverseExtension_apply]
  by_cases hiv : i = v
  · subst i
    simp [hvσ, hxv]
  · by_cases his : i ∈ σ <;> simp [hiv, his, hvσ, hxv, hc]

/-- On nonnegative coordinates supported on a stellar face, the inverse extension cancels
the barycentric map. No normalization or finiteness of the complex or vertex type is needed. -/
theorem stellarSubdivisionInverseExtension_stellarSubdivisionLinearMap
    {K : PreAbstractSimplicialComplex ι} {σ : Finset ι} (hσ : σ.Nonempty)
    {v : ι} (hvσ : v ∉ σ) {x : ι →₀ ℝ}
    (hxpos : ∀ i, 0 ≤ x i)
    (hxface : x.support ∈ PreAbstractSimplicialComplex.stellarSubdivision K σ v) :
    stellarSubdivisionInverseExtension σ hσ v (stellarSubdivisionLinearMap σ v x) =
      (x : ι → ℝ) := by
  have hnot : ¬ σ ⊆ x.support := fun h =>
    PreAbstractSimplicialComplex.self_notMem_stellarSubdivision hvσ
      ((PreAbstractSimplicialComplex.stellarSubdivision K σ v).isRelLowerSet_faces.mem_of_le
        hxface h hσ)
  obtain ⟨a, ha, hxa⟩ := Finset.not_subset.mp hnot
  have hc : (σ.card : ℝ) ≠ 0 := by exact_mod_cast hσ.card_pos.ne'
  have hcoord (i : ι) (hi : i ∈ σ) :
      stellarSubdivisionLinearMap σ v x i = x i + x v * (σ.card : ℝ)⁻¹ := by
    have hiv : i ≠ v := fun h => hvσ (h ▸ hi)
    simp [stellarSubdivisionLinearMap_apply, hi, hiv]
  have hmin : σ.inf' hσ (stellarSubdivisionLinearMap σ v x) =
      x v * (σ.card : ℝ)⁻¹ := by
    apply le_antisymm
    · exact (σ.inf'_le _ ha).trans_eq (by
        simp [hcoord a ha, Finsupp.notMem_support_iff.mp hxa])
    · apply σ.le_inf' hσ
      intro i hi
      rw [hcoord i hi]
      linarith [hxpos i]
  ext i
  rw [stellarSubdivisionInverseExtension_apply, hmin, stellarSubdivisionLinearMap_apply]
  by_cases hiv : i = v
  · subst i
    simp [hvσ, hc]
  · by_cases his : i ∈ σ <;> simp [hiv, his]

end Finset

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- The finite stellar homeomorphism has the barycentric continuous linear coordinate map
as its forward extension and the piecewise-affine minimum-transfer map as its inverse extension.
Thus stellar moves identify finite weak polyhedra by PL maps in both directions. -/
theorem exists_homeomorph_stellarSubdivision_with_inverse
    (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) (hfin : K.faces.Finite)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision K σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ K},
      (∀ x, ((e x).1.1 : ι → ℝ) = Finset.stellarSubdivisionContinuousLinearMap σ v x.1.1) ∧
      ∀ y, ((e.symm y).1.1 : ι → ℝ) =
        Finset.stellarSubdivisionInverseExtension σ (K.isRelLowerSet_faces hσ).1 v y.1.1 := by
  obtain ⟨e, he⟩ := exists_homeomorph_stellarSubdivision hσ hv hfin hK hS
  refine ⟨e, fun x => ?_, fun y => ?_⟩
  · simp [he x]
  · obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply, he x]
    exact (Finset.stellarSubdivisionInverseExtension_stellarSubdivisionLinearMap
      (K.isRelLowerSet_faces hσ).1 (notMem_of_singleton_notMem hv hσ)
      (Realization.nonneg A x.1) x.2).symm

end PreAbstractSimplicialComplex
