/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Plucker
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Checks for the Plücker map

The point of the chart of `G(2, A⁴)` indexed by the first two basis vectors with quotient matrix
`((1, 0, a, b), (0, 1, c, d))` has Plücker coordinates `(1 : c : d : -a : -b : ad - bc)`, and these
satisfy the Plücker relation `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`.
-/

public section

namespace TauCeti.Grassmannian

variable {A : Type*} [CommRing A]

/-- **The Plücker coordinates of a point of `G(2, A⁴)`.** The quotient `q : A⁴ → A²` with matrix
`((1, 0, a, b), (0, 1, c, d))`, the point of the chart indexed by the first two basis vectors,
has `⋀² q (eᵢ ∧ eⱼ) = pᵢⱼ f₁ ∧ f₂` with
`(p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄) = (1, c, d, -a, -b, ad - bc)`, and these satisfy the Plücker
relation `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`. By
`Module.Grassmannian.toSubmodule_plucker_ofSurjective`, the Plücker point of `ker q` is the kernel
of `⋀² q`, the linear form with these coordinates. Without the signs of the exterior power, the
coordinates `(1, c, d, a, b, ad - bc)` would give `2(ad - bc)` in the relation. -/
theorem exteriorPower_map_two_mulVecLin (a b c d : A) :
    let q := (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A).mulVecLin
    let e : Fin 4 → Fin 4 → A := fun i ↦ Pi.single i 1
    let w := exteriorPower.ιMulti A 2 ![(Pi.single 0 1 : Fin 2 → A), Pi.single 1 1]
    exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 1]) = (1 : A) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 2]) = c • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 3]) = d • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 1, e 2]) = (-a) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 1, e 3]) = (-b) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 2, e 3]) = (a * d - b * c) • w ∧
      1 * (a * d - b * c) - c * (-b) + d * (-a) = 0 := by
  intro q e w
  let P : Matrix (Fin 2) (Fin 4) A := !![1, 0, a, b; 0, 1, c, d]
  -- the `j`-th column of `P` gives `q (e j)`
  have hcol (j : Fin 4) : q (e j) = ∑ i, P i j • (Pi.single i 1 : Fin 2 → A) := by
    ext l
    fin_cases l <;> simp [q, e, P, Matrix.mulVec, dotProduct, Pi.single_apply]
  -- `⋀² q (eᵢ ∧ eⱼ)` is the `2 × 2` minor of `P` on the columns `i, j`
  have key (i j : Fin 4) : exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e i, e j]) =
      (P 0 i * P 1 j - P 1 i * P 0 j) • w := by
    rw [exteriorPower.map_apply_ιMulti_two, hcol, hcol, ← Matrix.det_fin_two_of]
    convert exteriorPower.ιMulti_sum_smul !![P 0 i, P 1 i; P 0 j, P 1 j] ![_, _] using 2
    ext l : 1
    fin_cases l <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by ring⟩ <;> rw [key] <;> congr 1 <;> simp [P, mul_comm]

end TauCeti.Grassmannian
