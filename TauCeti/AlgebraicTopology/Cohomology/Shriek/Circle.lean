/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Shriek
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Degree.Circle
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Degree.Homological

/-!
# Shriek maps of the power maps of the circle

For an integer `k`, the power map `z ↦ zᵏ` of the circle `S¹ = Circle` has homological degree `k`
for every orientation of `S¹` (`TauCeti.degree_toHomologicalOrientation_zpow_circle`): by the
comparison of the homological degree with the smooth mapping degree, this is the smooth degree
computation `TauCeti.degree_zpow_id_circle`. Its shriek map
`f_! = D ∘ f^* ∘ D⁻¹ : H_q(S¹; L) → H_q(S¹; L)` (`TauCeti.HomologicalOrientation.shriek`)
therefore satisfies:

* `f_* ∘ f_! = k • id` on `H_q(S¹; L)` in degrees `0` and `1`
  (`TauCeti.map_shriek_zpow_circle`);
* `f_!` sends the class `[y]` of a point to `k • [x]` for any point `x`
  (`TauCeti.shriek_zpow_circle_singularHomology₀Section`).

For the double cover `z ↦ z²` the point `x²` has the two preimages `x` and `-x`, and `f_!` sends
its class to the sum `[x] + [-x]` of their classes
(`TauCeti.shriek_sq_circle_singularHomology₀Section`), as the transfer of a covering does. In the
top degree `f_![S¹] = [S¹]`, as for every map
(`TauCeti.HomologicalOrientation.shriek_fundamentalClass`), while `f_*[S¹] = 2 • [S¹]`. So
`f_* ∘ f_! = 2 • id` in degrees `0` and `1`.

## Main results

* `TauCeti.degree_toHomologicalOrientation_zpow_circle`: `z ↦ zᵏ` has homological degree `k`.
* `TauCeti.map_shriek_zpow_circle`: `f_* ∘ f_! = k • id` for `f = (· ^ k)`.
* `TauCeti.shriek_zpow_circle_singularHomology₀Section`: `f_![y] = k • [x]`.
* `TauCeti.shriek_sq_circle_singularHomology₀Section`: for the double cover,
  `f_![x²] = [x] + [-x]`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 10.6.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (Poincaré duality) and Section 3.G (transfer homomorphisms).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module
open scoped Manifold

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (L : ModuleCat.{0} ℤ)

/-- **The power map `z ↦ zᵏ` of the circle has homological degree `k`**, for every orientation of
the circle. -/
@[simp]
theorem degree_toHomologicalOrientation_zpow_circle (k : ℤ) :
    (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin).degree
        (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin ⟨(· ^ k), continuous_zpow k⟩ = k :=
  (Manifold.Orientation.degree_toHomologicalOrientation_eq_degree (E := EuclideanSpace ℝ (Fin 1))
    finrank_euclideanSpace_fin o o (f := ⟨(· ^ k), continuous_zpow k⟩) (contMDiff_zpow k)
    (continuous_zpow k).isProperMap).trans (degree_zpow_id_circle o k)

/-- **`f_* ∘ f_! = k • id` for the power map `f = (· ^ k)` of the circle**: pushing forward the
shriek image of a class `y ∈ H_q(S¹; L)` gives `k • y`. -/
theorem map_shriek_zpow_circle (k : ℤ) {p q : ℕ} (hq : p + q = 1)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Circle)) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom ⟨(· ^ k), continuous_zpow k⟩)).hom
        ((o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1))
          finrank_euclideanSpace_fin).shriek finrank_euclideanSpace_fin
          (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin)
          finrank_euclideanSpace_fin L ⟨(· ^ k), continuous_zpow k⟩ hq hq y) =
      k • y := by
  rw [HomologicalOrientation.map_shriek_eq_degree_smul,
    degree_toHomologicalOrientation_zpow_circle]

/-- **The shriek map of the power map `f = (· ^ k)` of the circle on the class of a point**: `f_!`
sends the class `[y] r ∈ H₀(S¹; L)` of a point `y` to `k • [x] r` for any point `x`. -/
theorem shriek_zpow_circle_singularHomology₀Section (k : ℤ) (x y : Circle) (r : L) :
    (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1))
        finrank_euclideanSpace_fin).shriek finrank_euclideanSpace_fin
        (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin L ⟨(· ^ k), continuous_zpow k⟩ (Nat.add_zero 1) (Nat.add_zero 1)
        ((singularHomology₀Section L (X := TopCat.of Circle) y).hom r) =
      k • (singularHomology₀Section L (X := TopCat.of Circle) x).hom r := by
  rw [HomologicalOrientation.shriek_singularHomology₀Section_eq_degree_smul _ _ _ _ _ _ x,
    degree_toHomologicalOrientation_zpow_circle]

/-- **The shriek map of the double cover of the circle on the class of a point**: for the double
cover `f = (· ^ 2)`, `f_!` sends the class of the point `x²` to the sum `[x] + [-x]` of the classes
of its two preimages. -/
theorem shriek_sq_circle_singularHomology₀Section (x : Circle) (r : L) :
    (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1))
        finrank_euclideanSpace_fin).shriek finrank_euclideanSpace_fin
        (o.toHomologicalOrientation (E := EuclideanSpace ℝ (Fin 1)) finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin L ⟨(· ^ (2 : ℤ)), continuous_zpow 2⟩ (Nat.add_zero 1)
        (Nat.add_zero 1)
        ((singularHomology₀Section L (X := TopCat.of Circle) (x ^ 2)).hom r) =
      (singularHomology₀Section L (X := TopCat.of Circle) x).hom r +
        (singularHomology₀Section L (X := TopCat.of Circle) (-x)).hom r := by
  rw [shriek_zpow_circle_singularHomology₀Section o L 2 x, two_zsmul,
    singularHomology₀Section_eq_of_pathConnectedSpace L (X := TopCat.of Circle) (-x) x]

end TauCeti
