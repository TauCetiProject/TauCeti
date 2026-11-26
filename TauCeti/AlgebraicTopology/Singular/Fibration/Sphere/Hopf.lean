/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere.SpectralSequence
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Sphere2
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space

/-!
# The Serre spectral sequence of the Hopf fibration

The Hopf map `S³ → S²` (`TauCeti.hopfSphere2Hom`) is a Serre fibration with fibre the circle
(`TauCeti.hopfSphere2Hom_mem_serreFibrations`, `TauCeti.hopfSphere2FiberHomeomorph`). Its Serre
spectral sequence (`TauCeti.TopCat.hopfSerreSpectralSequence`), over the CW structure of `S²` with
one `0`-cell and one `2`-cell, is computed here from the general shape of the spectral sequence of a
fibration over a sphere (`TauCeti.AlgebraicTopology.Singular.Fibration.Sphere.SpectralSequence`).
In the classical indexing:

* the second page is the homology of the circle in the columns `0` and `2`,
  `E²_{0,q} ≅ Hq(S¹; R)` and `E²_{2,q} ≅ Hq(S¹; R)`
  (`TauCeti.TopCat.hopfSerreSpectralSequenceSecondPageXIsoPole`,
  `TauCeti.TopCat.hopfSerreSpectralSequenceSecondPageXIsoTopCell`), and vanishes in every other
  column; since `H₀(S¹; ℤ) ≅ H₁(S¹; ℤ) ≅ ℤ` and the higher homology of the circle vanishes, over
  `ℤ` it is `ℤ` at `(0, 0)`, `(0, 1)`, `(2, 0)` and `(2, 1)` and zero elsewhere;
* the differential `d² : E²_{2,0} ⟶ E²_{0,1}` is an isomorphism
  (`TauCeti.TopCat.isIso_hopfSerreSpectralSequence_page_three_d`), since its kernel and cokernel
  are graded pieces of `H₂(S³; R)` and `H₁(S³; R)`, which vanish.

So trivial monodromy does not make a Serre spectral sequence collapse: for comparison, the product
`S² × S¹ → S²` has the same second page, but there `d² = 0`, since `H₂(S² × S¹; ℤ) ≅ ℤ`.

In Mathlib's cohomological indexing the second page is the page numbered `3`, and the classical
position `(k, q)` is `(1 - q - 2k, k - 1)`, so `d²` goes from `(-3, 1)` to `(0, -1)`.

## References

* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1.
* H. Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*, Math. Ann.
  104 (1931), 637–665.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Metric

namespace TauCeti

namespace TopCat

variable (R : Type) [Ring R]

/-- **The Serre spectral sequence of the Hopf fibration** `S¹ → S³ → S²`, for the CW structure on
`S²` with one `0`-cell and one `2`-cell. -/
abbrev hopfSerreSpectralSequence :=
  sphereSerreSpectralSequence (rfl : Fintype.card (Fin 3) = 2 + 1) hopfSphere2Hom R

/-- **The transgression of the Hopf fibration is an isomorphism.** In the Serre spectral sequence of
the Hopf fibration `S¹ → S³ → S²`, the differential `d² : E²_{2,0} ⟶ E²_{0,1}`, at the positions
`(-3, 1)` and `(0, -1)` of the page `3`, is an isomorphism: its kernel and cokernel are graded
pieces of `H₂(S³; R)` and `H₁(S³; R)`, which vanish. -/
theorem isIso_hopfSerreSpectralSequence_page_three_d :
    IsIso (((hopfSerreSpectralSequence R).page 3).d (-3, 1) (0, -1)) := by
  -- `S³` has no homology in the degrees `1` and `2`.
  have hS (m : ℕ) (hm₀ : m ≠ 0) (hm₃ : m ≠ 3) :
      IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))) :=
    (ContinuousMap.HomotopyEquiv.refl _).isZero_singularHomology_of_sphere_of_ne
      (ModuleCat.of R R) (finrank_real_euclideanSpace_complex 1) hm₀ hm₃
  have := mono_sphereSerreSpectralSequence_page_d (ι := Fin 3) (n := 2) rfl hopfSphere2Hom R
    (by norm_num) 3 (by norm_num) (-3, 1) (0, -1) (by norm_num) (by ext <;> norm_num) (m := 2)
    (by norm_num) (hS 2 (by lia) (by lia))
  have := epi_sphereSerreSpectralSequence_page_d (ι := Fin 3) (n := 2) rfl hopfSphere2Hom R
    (by norm_num) 3 (by norm_num) (-3, 1) (0, -1) (by norm_num) (by ext <;> norm_num) (m := 1)
    (by norm_num) (hS 1 (by lia) (by lia))
  exact isIso_of_mono_of_epi _

/-- **The column `0` of the second page of the Serre spectral sequence of the Hopf fibration** is
the homology of the circle: `E²_{0,q} ≅ Hq(S¹; R)`, through the fibre over the pole. -/
def hopfSerreSpectralSequenceSecondPageXIsoPole (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = -1)
    (ha : pq.1 + pq.2 = -(q : ℕ)) :
    ((hopfSerreSpectralSequence R).page 3).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (sphere (0 : ℂ) 1)) :=
  sphereSerreSpectralSequencePageXIsoFirstPageX (ι := Fin 3) (n := 2) rfl hopfSphere2Hom R 3
      (by lia) (by lia) pq (Or.inl hb) ≪≫
    sphereSerreSpectralSequenceFirstPageXIsoPole (ι := Fin 3) (n := 2) rfl hopfSphere2Hom R
      (by norm_num) q pq hb ha ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) q).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (hopfSphere2FiberHomeomorph _
        (hopfSphere2_surjective _).choose_spec)).symm

/-- **The column `2` of the second page of the Serre spectral sequence of the Hopf fibration** is
the homology of the circle: `E²_{2,q} ≅ Hq(S¹; R)`, through the fibre over the centre of the
`2`-cell. -/
def hopfSerreSpectralSequenceSecondPageXIsoTopCell (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = 1)
    (ha : pq.1 + pq.2 = -(q + 2 : ℕ)) :
    ((hopfSerreSpectralSequence R).page 3).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (sphere (0 : ℂ) 1)) :=
  sphereSerreSpectralSequencePageXIsoFirstPageX (ι := Fin 3) (n := 2) rfl hopfSphere2Hom R 3
      (by lia) (by lia) pq (Or.inr hb) ≪≫
    sphereSerreSpectralSequenceFirstPageXIsoTopCell (ι := Fin 3) (n := 2) rfl R
      hopfSphere2Hom_mem_serreFibrations (by norm_num) q pq hb ha ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) q).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (hopfSphere2FiberHomeomorph _
        (hopfSphere2_surjective _).choose_spec)).symm

end TopCat

end TauCeti
