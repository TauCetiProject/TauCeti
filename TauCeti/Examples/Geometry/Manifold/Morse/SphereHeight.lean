/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Sphere.Cell

/-!
# Examples: the homology of the sphere from the cells of the height function

The height function `h x = ⟪x, v⟫` on the unit sphere `Sⁿ` has a minimum of index `0` at the
south pole and a maximum of index `n` at the north pole. Below the maximum its sublevels are
contractible (`TauCeti.contractibleSpace_sublevel_sphereHeight`), and the band across the maximum
has the relative homology of one `n`-cell
(`TauCeti.nonempty_singularHomology_sublevelPair_sphereHeight_iso`,
`TauCeti.isZero_singularHomology_sublevelPair_sphereHeight`). Since the sublevel above the maximum
is the whole sphere, the homology of `Sⁿ` in positive degrees is this relative homology
(`TauCeti.singularHomologyIsoSublevelPairOfContractibleSpace`). The examples below read off the
homology of the sphere from the cells of the height in this way:

* in positive degrees `k + 1`, the homology `Hₖ₊₁(Sᵐ)` of the sphere of dimension `m = n + 1` is
  one copy of the coefficients for `k = n`, carried by the cell at the north pole, and vanishes
  otherwise;
* on the circle, the cell at the maximum is made of two descending arcs, whose ends both attach to
  the lower sublevel, an arc around the minimum: the connecting map
  `H₁({h ≤ 2}, {h ≤ 0}; ℤ) ⟶ H₀({h ≤ 0}; ℤ)` vanishes
  (`TauCeti.singularHomologyδ_sublevelPair_sphereHeight_eq_zero`), and `H₁(S¹; ℤ) ≅ ℤ`.

The same homology is computed, independently of Morse theory, by the Mayer–Vietoris sequence
(`TauCeti.reducedSingularHomologySphereIso`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorems 3.1, 3.2 and 3.5.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

namespace TauCeti.Examples

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1 + 1)] (v : sphere (0 : E) 1)
  {A : Type*} [Category.{0} A] [Abelian A] [HasCoproducts.{0} A] (R : A)

/-- The top homology `Hₙ₊₁(Sⁿ⁺¹)` is one copy of the coefficients, carried by the cell of the
height at the north pole. -/
example :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor A (n + 1)).obj R).obj
      (TopCat.of (sphere (0 : E) 1)) ≅ R) :=
  have := contractibleSpace_sublevel_sphereHeight v (a := 0) (by norm_num) (by norm_num)
  ⟨singularHomologyIsoSublevelPairOfContractibleSpace (a := 0) (b := 2) (by norm_num)
      (fun x ↦ (sphereHeight_le_one v x).trans (by norm_num)) R n ≪≫
    (nonempty_singularHomology_sublevelPair_sphereHeight_iso R v (a := 0) (b := 2) (by norm_num)
      (by norm_num) (by norm_num)).some⟩

/-- In a positive degree `k + 1` other than the dimension `n + 1`, the homology of `Sⁿ⁺¹`
vanishes: the height has no critical point of index `k + 1`. -/
example {k : ℕ} (hk : k ≠ n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A (k + 1)).obj R).obj
      (TopCat.of (sphere (0 : E) 1))) :=
  have := contractibleSpace_sublevel_sphereHeight v (a := 0) (by norm_num) (by norm_num)
  (isZero_singularHomology_sublevelPair_sphereHeight R v (a := 0) (b := 2) (by norm_num)
      (by norm_num) (by norm_num) (n := n + 1) (k := k + 1) (by omega)).of_iso
    (singularHomologyIsoSublevelPairOfContractibleSpace (a := 0) (b := 2) (by norm_num)
      (fun x ↦ (sphereHeight_le_one v x).trans (by norm_num)) R k)

end Sphere

section Circle

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable (p : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

/-- On the circle, the two descending arcs of the cell at the maximum attach to the same component
of the lower sublevel: the connecting map `H₁({h ≤ 2}, {h ≤ 0}; ℤ) ⟶ H₀({h ≤ 0}; ℤ)` vanishes. -/
example : (sublevelPair (sphereHeight p) (by norm_num : (0 : ℝ) ≤ 2)).singularHomologyδ
    (ModuleCat.of ℤ ℤ) 1 0 = 0 :=
  singularHomologyδ_sublevelPair_sphereHeight_eq_zero _ p (by norm_num) (by norm_num) _ 0

/-- The cells of the height give `H₁(S¹; ℤ) ≅ ℤ`. -/
example :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ≅
        ModuleCat.of ℤ ℤ) :=
  have := contractibleSpace_sublevel_sphereHeight p (a := 0) (by norm_num) (by norm_num)
  ⟨singularHomologyIsoSublevelPairOfContractibleSpace (a := 0) (b := 2) (by norm_num)
      (fun x ↦ (sphereHeight_le_one p x).trans (by norm_num)) _ 0 ≪≫
    (nonempty_singularHomology_sublevelPair_sphereHeight_iso (n := 1) _ p (a := 0) (b := 2)
      (by norm_num) (by norm_num) (by norm_num)).some⟩

end Circle

end TauCeti.Examples
