/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Torus.HigherHomotopy
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Covering
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic

/-!
# The standard symplectic torus is aspherical but not atoroidal

Let `T = ∀ i : ι ⊕ ι, AddCircle (p i)` be a torus with its standard symplectic form
`ω_T = ∑ j, dt_(inl j) ∧ dt_(inr j)` (`TauCeti.torusSymplecticForm`). This file shows that `ω_T`
satisfies the area condition of symplectic asphericity, in both of its formulations, but not that
of symplectic atoroidality:

* `ω_T` is weakly exact (`TauCeti.isWeaklyExact_torusSymplecticForm`) and vanishes on spheres
  (`TauCeti.vanishesOnSpheres_torusSymplecticForm`). The covering map
  `π : (ι → ℂ) → T` (`TauCeti.complexPiTorusCover`) pulls `ω_T` back to the constant form `ω₀` of
  complex coordinate space, which is exact, with primitive `λₓ(v) = ω₀(x, v) / 2`
  (`TauCeti.SymplecticForm.radialPrimitive`, `TauCeti.SymplecticForm.mextDeriv_radialPrimitive`).
  Spheres in `T` lift to spheres in `ι → ℂ` (`TauCeti.IsWeaklyExact.of_mpullback`,
  `TauCeti.VanishesOnSpheres.of_mpullback`), over which exact forms integrate to zero.
* The first Chern number `c₁ : π₂(T, x) → ℤ` of `ω_T` vanishes
  (`TauCeti.firstChernHom_torusSymplecticForm_eq_zero`), since `π₂(T, x)` is trivial. With the
  area condition, this is symplectic asphericity of `T`.
* As soon as `ι` is nonempty, `ω_T` does not vanish on tori
  (`TauCeti.not_vanishesOnTori_torusSymplecticForm`). The coordinate torus of the `j`-th pair of
  circles, the image under `π` of `(s, t) ↦ (s p_(inl j) + i t p_(inr j)) e_j` on the unit square,
  has area `p_(inl j) p_(inr j) ≠ 0`
  (`TauCeti.rectangleIntegral_torusSymplecticForm_coordinateTorus`).
  For the square torus `T² = ℝ² / ℤ²` with `ω = dx ∧ dy` this is the identity map, of area `1`.

So the two area conditions on a symplectic manifold, asphericity and atoroidality, are different:
the results on the action of contractible loops that assume vanishing on spheres apply to `T`, and
those on the action of all free loops that assume vanishing on tori do not.

## Main results

* `TauCeti.isWeaklyExact_torusSymplecticForm`, `TauCeti.vanishesOnSpheres_torusSymplecticForm`:
  the area condition of symplectic asphericity.
* `TauCeti.firstChernHom_torusSymplecticForm_eq_zero`: the Chern condition of symplectic
  asphericity.
* `TauCeti.rectangleIntegral_torusSymplecticForm_coordinateTorus`: the area of a coordinate torus.
* `TauCeti.not_vanishesOnTori_torusSymplecticForm`: `ω_T` is not atoroidal.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (symplectically aspherical manifolds).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (symplectically aspherical and
  atoroidal manifolds).
-/

public section

noncomputable section

open Set Complex
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} (p : ι ⊕ ι → ℝ)

section Aspherical

variable [Fintype ι] [∀ i, Fact (0 < p i)]

/-- The covering map pulls the standard symplectic form of the torus back to the exterior
derivative of the radial primitive of the standard symplectic form of `ι → ℂ`. -/
private theorem mpullback_complexPiTorusCover_torusSymplecticForm_eq_mextDeriv :
    TauCeti.mpullback 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
        (complexPiTorusCover p) (torusSymplecticForm p).val =
      mextDeriv (stdComplexPiSymplecticForm ι).radialPrimitive.val := by
  have h := congrArg Subtype.val (mpullback_complexPiTorusCover_torusSymplecticForm p)
  rw [SmoothForm.coe_mpullback] at h
  rw [h, SymplecticForm.mextDeriv_radialPrimitive]

/-- **The standard symplectic form of the torus is weakly exact**: its integral over every sphere,
a cylinder between two constant loops, vanishes. -/
theorem isWeaklyExact_torusSymplecticForm : IsWeaklyExact (torusSymplecticForm p).val := by
  refine IsWeaklyExact.of_mpullback (isCoveringMap_complexPiTorusCover p)
    (complexPiTorusCover_surjective p)
    ((isLocalDiffeomorph_complexPiTorusCover p).of_le (by simp)) ?_
  rw [mpullback_complexPiTorusCover_torusSymplecticForm_eq_mextDeriv]
  exact isWeaklyExact_mextDeriv
    ((stdComplexPiSymplecticForm ι).radialPrimitive.isSmoothForm.of_le (by simp))

/-- **The standard symplectic form of the torus vanishes on spheres**: its integral over every
smooth map of the square that factors through a sphere vanishes. -/
theorem vanishesOnSpheres_torusSymplecticForm : VanishesOnSpheres (torusSymplecticForm p).val := by
  refine VanishesOnSpheres.of_mpullback (isCoveringMap_complexPiTorusCover p)
    (complexPiTorusCover_surjective p) (isLocalDiffeomorph_complexPiTorusCover p) ?_
  rw [mpullback_complexPiTorusCover_torusSymplecticForm_eq_mextDeriv]
  exact vanishesOnSpheres_mextDeriv
    ((stdComplexPiSymplecticForm ι).radialPrimitive.isSmoothForm.of_le (by simp))

/-- **The first Chern number of the standard symplectic torus vanishes**: `c₁ : π₂(T, x) → ℤ` is
zero at every point, since `π₂(T, x)` is trivial. -/
theorem firstChernHom_torusSymplecticForm_eq_zero (x : ∀ i, AddCircle (p i)) :
    (isSymplectic_torusSymplecticForm p).isNondegenerate.firstChernHom x = 0 :=
  AddMonoidHom.ext fun a ↦ by rw [Subsingleton.elim a 0, map_zero, map_zero]

end Aspherical

/-! ### The area of a coordinate torus -/

section CoordinateTorus

variable [DecidableEq ι]

/-- The linear map `(s, t) ↦ (s p_(inl j) + i t p_(inr j)) e_j` of the plane into `ι → ℂ`, whose
image of the unit square is a fundamental domain of the coordinate torus of the `j`-th pair of
circles. -/
private def coordPlane (j : ι) : ℝ × ℝ →L[ℝ] ι → ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Pi.single j (p (.inl j) : ℂ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Pi.single j (p (.inr j) * I))

private theorem coordPlane_apply (j : ι) (z : ℝ × ℝ) :
    coordPlane p j z = Pi.single j (⟨z.1 * p (.inl j), z.2 * p (.inr j)⟩ : ℂ) := by
  funext k
  by_cases hk : k = j
  · subst hk
    apply Complex.ext <;> simp [coordPlane]
  · simp [coordPlane, hk]

/-- The **coordinate torus** of the `j`-th pair of circles,
`(s, t) ↦ π((s p_(inl j) + i t p_(inr j)) e_j)`: it winds once around the circle `inl j` as `s`
runs over `[0, 1]`, once around the circle `inr j` as `t` does, and is constant in the other
circles. -/
def coordinateTorus (j : ι) (z : ℝ × ℝ) : ∀ i, AddCircle (p i) :=
  complexPiTorusCover p (Pi.single j (⟨z.1 * p (.inl j), z.2 * p (.inr j)⟩ : ℂ))

theorem coordinateTorus_def (j : ι) (z : ℝ × ℝ) :
    coordinateTorus p j z =
      complexPiTorusCover p (Pi.single j (⟨z.1 * p (.inl j), z.2 * p (.inr j)⟩ : ℂ)) :=
  (rfl)

private theorem coordinateTorus_eq_comp (j : ι) :
    coordinateTorus p j = complexPiTorusCover p ∘ coordPlane p j :=
  funext fun z ↦ by rw [Function.comp_apply, coordPlane_apply, coordinateTorus_def]

/-- The coordinate torus takes the same values on the two vertical edges of the unit square. -/
theorem coordinateTorus_one_fst (j : ι) (t : ℝ) :
    coordinateTorus p j (1, t) = coordinateTorus p j (0, t) := by
  refine (complexPiTorusCover_eq_complexPiTorusCover_iff p).2 fun k ↦ ?_
  by_cases hk : k = j
  · subst hk
    exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
  · exact ⟨⟨0, by simp [hk]⟩, ⟨0, by simp [hk]⟩⟩

/-- The coordinate torus takes the same values on the two horizontal edges of the unit square. -/
theorem coordinateTorus_one_snd (j : ι) (s : ℝ) :
    coordinateTorus p j (s, 1) = coordinateTorus p j (s, 0) := by
  refine (complexPiTorusCover_eq_complexPiTorusCover_iff p).2 fun k ↦ ?_
  by_cases hk : k = j
  · subst hk
    exact ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩
  · exact ⟨⟨0, by simp [hk]⟩, ⟨0, by simp [hk]⟩⟩

variable [Fintype ι] [∀ i, Fact (0 < p i)]

/-- The coordinate torus is smooth. -/
theorem contMDiff_coordinateTorus (j : ι) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) ∞
      (coordinateTorus p j) := by
  rw [coordinateTorus_eq_comp]
  exact (contMDiff_complexPiTorusCover p).comp (coordPlane p j).contDiff.contMDiff

/-- **The area of a coordinate torus**: the integral of `ω_T` over the coordinate torus of the
`j`-th pair of circles is the product `p_(inl j) p_(inr j)` of their periods. -/
theorem rectangleIntegral_torusSymplecticForm_coordinateTorus (j : ι) :
    rectangleIntegral (torusSymplecticForm p).val (coordinateTorus p j) (0, 0) (1, 1) =
      p (.inl j) * p (.inr j) := by
  -- The derivative of the coordinate torus is `complexToRealPi ∘ coordPlane` at every point.
  have hd (z v : ℝ × ℝ) :
      mfderiv 𝓘(ℝ, ℝ × ℝ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (coordinateTorus p j) z v =
        complexToRealPi ι (coordPlane p j v) := by
    rw [coordinateTorus_eq_comp, ((hasMFDerivAt_complexPiTorusCover p _).comp z
      (coordPlane p j).hasMFDerivAt).mfderiv]
    -- `ContinuousLinearMap.comp_apply` up to the tangent spaces of the model spaces, which are the
    -- model spaces themselves; the rewrite does not see through them.
    rfl
  rw [rectangleIntegral_eq]
  have hval (s t : ℝ) : (torusSymplecticForm p).val (coordinateTorus p j (s, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (coordinateTorus p j)
          (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (coordinateTorus p j)
          (s, t) (0, 1)] = p (.inl j) * p (.inr j) := by
    rw [torusSymplecticForm_apply]
    simp only [hd, coordPlane_apply]
    -- Only the `j`-th pair of coordinates contributes.
    rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp
  simp [hval]

omit [DecidableEq ι] in
/-- **The standard symplectic torus is not atoroidal**: for nonempty `ι`, the form `ω_T` does not
vanish on tori, since a coordinate torus has positive area. -/
theorem not_vanishesOnTori_torusSymplecticForm [Nonempty ι] :
    ¬VanishesOnTori (torusSymplecticForm p).val := by
  classical
  rw [vanishesOnTori_iff]
  intro h
  obtain ⟨j⟩ := ‹Nonempty ι›
  have h₀ := h (coordinateTorus p j) (contMDiff_coordinateTorus p j)
    (fun t _ ↦ coordinateTorus_one_fst p j t) (fun s _ ↦ coordinateTorus_one_snd p j s)
  rw [rectangleIntegral_torusSymplecticForm_coordinateTorus] at h₀
  exact (mul_pos (Fact.out : 0 < p (.inl j)) (Fact.out : 0 < p (.inr j))).ne' h₀

end CoordinateTorus

end TauCeti
