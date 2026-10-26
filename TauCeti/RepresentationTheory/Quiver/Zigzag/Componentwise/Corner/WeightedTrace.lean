/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Trace

/-!
# Unit-weighted trace pairings between graded corners

A unit at each vertex scales the trace pairing on the corresponding graded corner without
changing its perfectness. Graded cyclicity in complementary internal degrees `d` and `2 - d`
only requires opposite weights at the selected endpoints when they are adjacent.
The sign is `(-1) ^ (d * (2 - d))`: the degree-one reverse-arrow pairing is antisymmetric,
while the degree-zero/degree-two vertex-volume pairings are symmetric. Alternating weights
on a path supply the edge condition, also in characteristic two.

## References

* B. Keller, *Calabi-Yau triangulated categories*, Proposition 2.2(b), for graded trace cyclicity.
* The corner classifications and trace pairings in
  `TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Trace`.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "C" => fun (i j : V) (d : ℤ) ↦
  cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d

/-- The graded corner trace pairing multiplied by the unit at its source vertex. -/
noncomputable def zigzagAlgebraGradedCornerWeightedTracePairing
    (c : V → kˣ) (i j : V) (d : ℤ) :
    ↥(C i j d) →ₗ[k] ↥(C j i (2 - d)) →ₗ[k] k :=
  (zigzagAlgebraGradedCornerTracePairing k G i j d).compl₁₂
    (LinearEquiv.smulOfUnit (M := ↥(C i j d)) (c i)).toLinearMap
    (LinearEquiv.refl k ↥(C j i (2 - d))).toLinearMap

/-- The weighted pairing is the vertex weight times the trace of the actual product. -/
@[simp]
theorem zigzagAlgebraGradedCornerWeightedTracePairing_apply
    (c : V → kˣ) (i j : V) (d : ℤ) (x : C i j d) (y : C j i (2 - d)) :
    zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d x y =
      (c i : k) * zigzagAlgebraTrace k G ((x : Z) * (y : Z)) := by
  -- The unit equivalence acts through a subtype coercion; expose its scalar action once.
  change zigzagAlgebraGradedCornerTracePairing k G i j d ((c i : k) • x) y = _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
    zigzagAlgebraGradedCornerTracePairing_apply]

/-- Unit vertex weights preserve perfectness of the complementary graded corner pairings. -/
instance zigzagAlgebraGradedCornerWeightedTracePairing_isPerfPair
    (c : V → kˣ) (i j : V) (d : ℤ) :
    (zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d).IsPerfPair := by
  dsimp only [zigzagAlgebraGradedCornerWeightedTracePairing]
  infer_instance

/-- Opposite edge weights give graded cyclicity. The reverse order is expressed in the ambient
algebra, so both factors retain their original signed graded corner types. -/
theorem zigzagAlgebraGradedCornerWeightedTracePairing_flip
    (c : V → kˣ) (i j : V)
    (hc : G.Adj i j → (c j : k) = -(c i : k))
    (d : ℤ) (x : C i j d) (y : C j i (2 - d)) :
    zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d x y =
      (d * (2 - d)).negOnePow •
        ((c j : k) * zigzagAlgebraTrace k G ((y : Z) * (x : Z))) := by
  rw [zigzagAlgebraGradedCornerWeightedTracePairing_apply]
  by_cases hij : i = j
  · subst j
    by_cases h0 : d = 0
    · subst d
      simp only [zero_mul, Int.negOnePow_zero, one_smul,
        zigzagAlgebraTrace_mul_comm]
    by_cases h2 : d = 2
    · subst d
      simp only [sub_self, mul_zero, Int.negOnePow_zero, one_smul,
        zigzagAlgebraTrace_mul_comm]
    have hx : (x : Z) = 0 := by
      have hx := x.property
      simpa only [cornerSubmodule_zigzagAlgebra_self_inf_integerGrade,
        ite_eq_right h0, ite_eq_right h2, Submodule.mem_bot] using hx
    simp [hx]
  · by_cases hadj : G.Adj j i
    · by_cases h1 : d = 1
      · subst d
        rw [show (1 : ℤ) * (2 - 1) = 1 by decide, Int.negOnePow_one]
        simp only [Units.neg_smul, one_smul]
        have hci : (c i : k) = -(c j : k) := by
          rw [hc hadj.symm, neg_neg]
        rw [hci, neg_mul, zigzagAlgebraTrace_mul_comm]
      · have hx : (x : Z) = 0 := by
          have hx := x.property
          simpa only [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj,
            ite_eq_right h1, Submodule.mem_bot] using hx
        simp [hx]
    · have hx : (x : Z) = 0 := by
        have hx : (x : Z) ∈ (⊥ : Submodule k Z) := by
          rw [← cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij
            (fun h ↦ hadj h.symm)]
          exact x.property.1
        exact (Submodule.mem_bot k).mp hx
      simp [hx]

end TauCeti
