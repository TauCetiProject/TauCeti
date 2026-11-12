/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Roots
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Glued

/-!
# Roots of overlattices in ADE glue coordinates

For a finite family of valid ADE components, let `R` be the orthogonal sum of their root
lattices, let `H` be a quadratically isotropic subgroup of their glue alphabets, and glue `R`
along `H` by `TauCeti.DynkinType.gluedLattice`.

If every nonzero word in `H` has minimum squared norm at least `r`, gluing preserves every
norm shell below `r`. When `2 < r`, the integral span of the glued lattice's roots in the
common rational ambient space is exactly `R.carrier`. Thus the finite inequality on glue
words proves the literal root-sublattice equality, including that the old roots span `R`.

This combines `isLeast_sum_glueMinimum` with the short-vector exclusion theorem in
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Roots`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 4 §6 and Chapter 16 §1, for the exclusion of additional roots using glue norms.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType)
  (ht : ∀ i, (t i).IsSimplyLaced)

variable (hv : ∀ i, (t i).Valid)

private theorem norm_bound_of_mem_map_glueWordIsometry
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    {r : ℚ} (hmin : ∀ w ∈ H, w ≠ 0 → r ≤ ∑ i, (t i).glueMinimum (ht i) (w i))
    (x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier)
    (hx : (Submodule.Quotient.mk x :
      (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) ∈
        H.map (glueWordIsometry t ht hv).toAddEquiv.toAddMonoidHom)
    (hne : (Submodule.Quotient.mk x :
      (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) ≠ 0) :
    r ≤ (pi fun i ↦ (t i).rootLattice (ht i)).norm x := by
  obtain ⟨w, hw, hwx⟩ := hx
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hne (hwx.symm.trans (map_zero _))
  exact (hmin w hw hw0).trans
    ((isLeast_sum_glueMinimum t hv ht w).2 ⟨x, hwx.symm, (norm_apply _ _).symm⟩)

/-- Gluing by words whose nonzero coset minima are at least `r` adds no vectors to any
norm shell below `r`. The two shells are compared in the common rational ambient space. -/
theorem image_vectorsOfNorm_gluedLattice_eq
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {r n : ℚ} (hmin : ∀ w ∈ H, w ≠ 0 → r ≤ ∑ i, (t i).glueMinimum (ht i) (w i))
    (hn : n < r) :
    (fun x : gluedLattice t ht hv H hH ↦ (x : ∀ i, Fin (t i).rank → ℚ)) ''
        (gluedLattice t ht hv H hH).vectorsOfNorm n =
      (fun x : pi fun i ↦ (t i).rootLattice (ht i) ↦ (x : ∀ i, Fin (t i).rank → ℚ)) ''
        (pi fun i ↦ (t i).rootLattice (ht i)).vectorsOfNorm n := by
  rw [gluedLattice_def]
  exact image_vectorsOfNorm_ofIsotropicSubgroup_eq _ _ _ _
    (norm_bound_of_mem_map_glueWordIsometry t ht hv H hmin) hn

/-- If the nonzero glue words have a common minimum-norm lower bound `r > 2`, the root
sublattice of the glued ADE lattice is literally the original root-lattice carrier.
The usual glue-table check uses `r = 4`. -/
theorem span_vectorsOfNorm_two_gluedLattice
    (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
    (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)
    {r : ℚ} (hmin : ∀ w ∈ H, w ≠ 0 → r ≤ ∑ i, (t i).glueMinimum (ht i) (w i))
    (hr : 2 < r) :
    Submodule.span ℤ ((fun x : gluedLattice t ht hv H hH ↦ (x : ∀ i, Fin (t i).rank → ℚ)) ''
        (gluedLattice t ht hv H hH).vectorsOfNorm 2) =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [image_vectorsOfNorm_gluedLattice_eq t ht hv H hH hmin hr]
  exact span_vectorsOfNorm_two_pi_rootLattice t ht

end TauCeti.DynkinType
