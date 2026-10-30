/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.WeightedTrace

/-!
# Unit-weighted pairings between zero-DG vertex projectives

Homogeneous DG morphisms of degrees `d` and `2 - d` between the actual zero-DG vertex
projectives have a perfect pairing induced by the unit-weighted graded corner trace.
Its value is the source weight times the trace of their actual enriched composition.
Opposite weights at adjacent selected endpoints give the sign `(-1) ^ (d * (2 - d))`
under reversal.

These are generator pairings in the chosen zero-DG model, whose DG degree is path degree.
The ordinary derived category of internally graded modules retains its separate external
cohomological degree. The enriched statements use the common universe of the existing
DG-right-module category.

## References

* B. Keller, *Calabi-Yau triangulated categories*, Proposition 2.2(b), for the graded trace sign.
* The existing zero-DG projective corner dictionary and unit-weighted graded corner pairings.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "L" => zigzagAlgebraProjectiveDGHomEquivCorner k G

/-- The weighted corner trace pulled back to complementary homogeneous DG morphisms. -/
def zigzagAlgebraProjectiveDGHomWeightedTracePairing
    (c : V → kˣ) (i j : V) (d : ℤ) :
    DGHom k d (D i) (D j) →ₗ[k] DGHom k (2 - d) (D j) (D i) →ₗ[k] k :=
  (zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d).compl₁₂
    (zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G i j d).toLinearMap
    (zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G j i (2 - d)).toLinearMap

/-- The generator pairing is perfect in every pair of complementary DG degrees. -/
instance zigzagAlgebraProjectiveDGHomWeightedTracePairing_isPerfPair
    (c : V → kˣ) (i j : V) (d : ℤ) :
    (zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d).IsPerfPair := by
  dsimp only [zigzagAlgebraProjectiveDGHomWeightedTracePairing]
  infer_instance

/-- The pairing evaluates the genuine enriched composition through its degree-two corner. -/
@[simp]
theorem zigzagAlgebraProjectiveDGHomWeightedTracePairing_apply
    (c : V → kˣ) (i j : V) (d : ℤ)
    (f : DGHom k d (D i) (D j)) (g : DGHom k (2 - d) (D j) (D i)) :
    zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d f g =
      (c i : k) * zigzagAlgebraTrace k G
        (L i i (-2) (dgComp k f g (by omega)) : Z) := by
  rw [zigzagAlgebraProjectiveDGHomWeightedTracePairing, LinearMap.compl₁₂_apply,
    zigzagAlgebraGradedCornerWeightedTracePairing_apply]
  simp only [LinearEquiv.coe_coe]
  rw [← coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_comp
    k G i j i d (2 - d) 2 (by omega) f g]
  norm_num only [coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply, castDeg_self]

/-- Reversal has the graded trace sign under the edge condition at the selected endpoints. -/
theorem zigzagAlgebraProjectiveDGHomWeightedTracePairing_flip
    (c : V → kˣ) (i j : V)
    (hc : G.Adj i j → (c j : k) = -(c i : k))
    (d : ℤ) (f : DGHom k d (D i) (D j))
    (g : DGHom k (2 - d) (D j) (D i)) :
    zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d f g =
      (d * (2 - d)).negOnePow • ((c j : k) * zigzagAlgebraTrace k G
        (L j j (-2) (dgComp k g f (by omega)) : Z)) := by
  have h := zigzagAlgebraGradedCornerWeightedTracePairing_flip k G c i j hc d
    (zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G i j d f)
    (zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G j i (2 - d) g)
  rw [← coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_comp
    k G j i j (2 - d) d 2 (by omega) g f,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply] at h
  norm_num only [castDeg_self] at h
  simpa only [zigzagAlgebraProjectiveDGHomWeightedTracePairing, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe] using h

end TauCeti
