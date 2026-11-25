/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Symplectic.Manifold.Prod.Area
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
import TauCeti.Algebra.Order.Ring.IntMul
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical
import TauCeti.AlgebraicTopology.UniversalCover.Torus.HigherHomotopy
import TauCeti.Geometry.Manifold.DeRham.SimplyConnected

/-!
# Spherical areas of a product with a torus

Let `T = ∀ i : ι ⊕ ι, AddCircle (p i)` be a torus with its standard symplectic form
`ω_T = ∑ j, dt_(inl j) ∧ dt_(inr j)` (`TauCeti.torusSymplecticForm`), and let `S` be a connected
oriented boundaryless surface carrying a two-form `σ`, such as the round sphere `S²(a)` with `a`
times its Fubini–Study form. This file computes the area `∫_C u^*(pr₁^*σ + pr₂^*ω_T)` of a smooth
map `u : C → S × T` from a compact oriented boundaryless simply connected surface `C`, for
instance the Riemann sphere `OnePoint ℂ`:

`∫_C u^*(pr₁^*σ + pr₂^*ω_T) = deg(pr₁ ∘ u) · ∫_S σ`

(`TauCeti.integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul`). So all spherical
areas of `S × T` are integer multiples of the area `∫_S σ` of the first factor
(`TauCeti.exists_integralTopForm_mpullback_prod_torusSymplecticForm_eq_intCast_mul`), and a
positive spherical area is at least `∫_S σ`
(`TauCeti.integralTopForm_le_integralTopForm_mpullback_prod_torusSymplecticForm`). This is the
area gap of `S²(a) × T²ⁿ⁻²` in Gromov's proof of the nonsqueezing theorem: every sphere of
positive area there, such as a nonconstant pseudoholomorphic sphere for a tame almost complex
structure, has area at least `a`.

The area splits as the sum of the areas of the two components `pr₁ ∘ u` and `pr₂ ∘ u`
(`TauCeti.integralTopForm_mpullback_prod`, in
`TauCeti.Geometry.Symplectic.Manifold.Prod.Area`). The first is `deg(pr₁ ∘ u) · ∫_S σ` by the
degree formula. The second vanishes because `C` is simply connected
(`TauCeti.integralTopForm_mpullback_torusSymplecticForm_eq_zero`): the pullbacks of the closed
one-forms `dt_i` are closed, hence exact on `C`, say `w^* dt_i = d gᵢ`, so each term
`w^*(dt_i ∧ dt_j) = d (gᵢ w^* dt_j)` is exact
(`TauCeti.mpullback_torusSymplecticForm_mem_exactForms`), and exact top forms integrate to zero on
a closed manifold. This replaces the homotopy-theoretic input `π₂(T) = 0` by the vanishing of
`H¹_dR(C)`.

The homotopy-theoretic form of the area gap holds for any homomorphism `ω` from the second
integral homology group, such as integration of a closed two-form, and is proved for `Sⁿ⁺¹ × Y`
with `Y` path-connected and `πₙ₊₁(Y)` trivial in
`TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical`: the value of `ω` on a spherical class is
an integer multiple of `a = ω [S² × {y}]` (`TauCeti.exists_apply_eq_zsmul_apply_sphereSliceClass`),
and if `a > 0`, every positive value of `ω` on a spherical class is at least `a`
(`TauCeti.apply_sphereSliceClass_le`). For a product `Tᵏ` of circles both hypotheses are found by
instance resolution, the second by `AddCircle.subsingleton_homotopyGroup_pi`, so these statements
apply to `S² × Tᵏ` directly. The example at the end of this file checks this.

## Main results

* `TauCeti.mpullback_torusSymplecticForm_mem_exactForms`: the torus form pulls back to an exact
  form on a simply connected manifold.
* `TauCeti.integralTopForm_mpullback_torusSymplecticForm_eq_zero`: maps from a closed simply
  connected surface to a torus have zero symplectic area.
* `TauCeti.integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul`: the area of a map
  to `S × T` is the degree of its first component times `∫_S σ`.
* `TauCeti.exists_integralTopForm_mpullback_prod_torusSymplecticForm_eq_intCast_mul`,
  `TauCeti.integralTopForm_le_integralTopForm_mpullback_prod_torusSymplecticForm`: spherical areas
  are integer multiples of `∫_S σ`, and positive ones are at least `∫_S σ`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T^(2n-2)`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 9.3 (the proof of the nonsqueezing theorem).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C]

/-! ### Maps to a torus -/

variable [T2Space C] {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)]

/-- **The torus form pulls back to an exact form on a simply connected manifold.** Along a smooth
map `w` from a simply connected manifold to the torus, each closed one-form `dt_i` pulls back to an
exact one, so every term `w^*(dt_(inl j) ∧ dt_(inr j))` of `w^* ω_T` is exact. -/
theorem mpullback_torusSymplecticForm_mem_exactForms [SimplyConnectedSpace C]
    {w : C → ∀ i, AddCircle (p i)} (hw : ContMDiff I (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)) ∞ w) :
    SmoothForm.mpullback w hw (torusSymplecticForm p) ∈ exactForms I C 2 := by
  have hclosed (i : ι ⊕ ι) :
      SmoothForm.mpullback w hw (torusTimeForm p i) ∈ closedForms I C 1 :=
    (mem_closedForms I _).mpr
      ((SmoothForm.isClosed_def _).mp ((isClosed_torusTimeForm p i).mpullback w hw))
  rw [torusSymplecticForm_def, map_sum]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  have h := SmoothForm.wedge_mem_exactForms_of_simplyConnectedSpace (hclosed (.inl j))
    (hclosed (.inr j))
  rw [← SmoothForm.mpullback_wedge] at h
  -- `h` is stated in degree `1 + 1`, which reduces to `2`.
  exact h

/-- **Spheres in a torus have zero area.** A smooth map `w` from a compact oriented boundaryless
simply connected surface to the torus satisfies `∫_C w^* ω_T = 0`. -/
theorem integralTopForm_mpullback_torusSymplecticForm_eq_zero [BoundarylessManifold I C]
    [CompactSpace C] [SimplyConnectedSpace C] (o : Manifold.Orientation I C (Fin 2))
    {w : C → ∀ i, AddCircle (p i)} (hw : ContMDiff I (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)) ∞ w) :
    integralTopForm o (SmoothForm.mpullback w hw (torusSymplecticForm p)).val = 0 :=
  integralTopForm_eq_zero_of_mem_exactForms o (mpullback_torusSymplecticForm_mem_exactForms hw)

/-! ### Spherical areas of a product with a torus -/

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S] [BoundarylessManifold J S] [T2Space S] [SigmaCompactSpace S]
  [ConnectedSpace S]
  [BoundarylessManifold I C] [CompactSpace C] [SimplyConnectedSpace C]
  (o : Manifold.Orientation I C (Fin 2)) (o' : Manifold.Orientation J S (Fin 2))
  {σ : SmoothTwoForm J S}
  (hσ : IsCompact (_root_.tsupport (α := E' [⋀^Fin 2]→L[ℝ] ℝ) σ.val))
  {u : C → S × ∀ i, AddCircle (p i)}
  (hu : ContMDiff I (J.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) ∞ u)
include hσ

/-- **The area of a sphere in `S × T` is the degree of its first component times `∫_S σ`.** For a
smooth map `u` from a compact oriented boundaryless simply connected surface `C` to the product
of a connected oriented boundaryless surface `S` with the torus `T`, and a compactly supported
two-form `σ` on `S`, `∫_C u^*(pr₁^*σ + pr₂^*ω_T) = deg(pr₁ ∘ u) · ∫_S σ`. -/
theorem integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul :
    integralTopForm o (SmoothForm.mpullback u hu (σ.prod (torusSymplecticForm p))).val =
      degree o o' (Prod.fst ∘ u) * integralTopForm o' σ.val := by
  rw [integralTopForm_mpullback_prod, integralTopForm_mpullback_torusSymplecticForm_eq_zero,
    add_zero, SmoothForm.coe_mpullback]
  exact integralTopForm_mpullback_eq_degree_mul o o' (contMDiff_fst.comp hu)
    (contMDiff_fst.comp hu).continuous.isProperMap (SmoothForm.isSmoothForm _) hσ

/-- **Spherical areas of `S × T` are integer multiples of `∫_S σ`.** For a smooth map `u` from a
compact oriented boundaryless simply connected surface to the product of a connected oriented
boundaryless surface `S` with the torus, the area `∫_C u^*(pr₁^*σ + pr₂^*ω_T)` lies in
`ℤ · ∫_S σ`. -/
theorem exists_integralTopForm_mpullback_prod_torusSymplecticForm_eq_intCast_mul :
    ∃ m : ℤ, integralTopForm o (SmoothForm.mpullback u hu (σ.prod (torusSymplecticForm p))).val =
      m * integralTopForm o' σ.val :=
  ⟨_, integralTopForm_mpullback_prod_torusSymplecticForm_eq_degree_mul o o' hσ hu⟩

/-- **A positive spherical area of `S × T` is at least `∫_S σ`.** For a smooth map `u` from a
compact oriented boundaryless simply connected surface to the product of a connected oriented
boundaryless surface `S` with the torus, if `∫_C u^*(pr₁^*σ + pr₂^*ω_T)` is positive then it is
at least `∫_S σ`: it is a positive integer multiple of `∫_S σ`. -/
theorem integralTopForm_le_integralTopForm_mpullback_prod_torusSymplecticForm
    (hpos : 0 < integralTopForm o
      (SmoothForm.mpullback u hu (σ.prod (torusSymplecticForm p))).val) :
    integralTopForm o' σ.val ≤
      integralTopForm o (SmoothForm.mpullback u hu (σ.prod (torusSymplecticForm p))).val := by
  obtain ⟨m, hm⟩ :=
    exists_integralTopForm_mpullback_prod_torusSymplecticForm_eq_intCast_mul o o' hσ hu
  rw [hm] at hpos ⊢
  exact le_intCast_mul_of_mul_pos hpos

end TauCeti

/-! ### The homological area gap for a torus -/

open CategoryTheory AlgebraicTopology Metric

namespace TauCeti

/-- The area gap applies to `S² × Tᵏ` for every product `Tᵏ` of circles: instance resolution
finds that the torus is path-connected and has trivial second homotopy group. -/
example {ι : Type} {p : ι → ℝ} {y : ∀ i, AddCircle (p i)}
    (area : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i))) →+ ℝ)
    (ha : 0 < area (sphereSliceClass _ y 1))
    {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i)))}
    (hc : c ∈ sphericalClasses (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ∀ i, AddCircle (p i)) 1)
    (hpos : 0 < area c) :
    area (sphereSliceClass _ y 1) ≤ area c :=
  apply_sphereSliceClass_le area ha hc hpos

end TauCeti
