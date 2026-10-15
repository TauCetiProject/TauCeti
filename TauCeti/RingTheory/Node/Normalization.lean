/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.BranchSequence
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Normalization of a split node

Over an integrally closed domain `R`, the normalization of `R[x,y]/(xy)` is
`R[t] × R[t]`, with the inclusion given by `NodeAlgebra.branchMap`. If `K` is a
fraction field of `R[t]`, then `K × K` is the total ring of fractions of the node,
and the branch algebra is its integral closure there.

The total ring of fractions is a product, not a field: the node has two irreducible
components. A node function is a nonzerodivisor exactly when its restrictions to
both branches are nonzero. Multiplying by the diagonal function `t` makes any pair
of branch functions descend to the node, which permits simultaneous clearing of
denominators on the two branches.

Together with the branch exact sequence and conductor calculation, this identifies
the normalization and the two points above a split node on a curve over a field.
The assertion about normalization needs normality of the base; the branch exact
sequence itself does not.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Polynomial
open scoped nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDomain R]

/-- A function on a split node is a nonzerodivisor precisely when it is nonzero on
both branches. -/
@[simp]
theorem mem_nonZeroDivisors_iff_branchMap (z : NodeAlgebra R 0) :
    z ∈ (NodeAlgebra R 0)⁰ ↔ (branchMap R z).1 ≠ 0 ∧ (branchMap R z).2 ≠ 0 := by
  constructor
  · intro hz
    constructor
    · intro h
      have hmul : z * coord (0 : R) 0 = 0 := by
        apply branchMap_injective R
        ext <;> simp [h]
      have hc := (mem_nonZeroDivisors_iff_left.mp hz _ hmul)
      have := congrArg (branchMap R) hc
      simpa using congrArg Prod.fst this
    · intro h
      have hmul : z * coord (0 : R) 1 = 0 := by
        apply branchMap_injective R
        ext <;> simp [h]
      have hc := (mem_nonZeroDivisors_iff_left.mp hz _ hmul)
      have := congrArg (branchMap R) hc
      simpa using congrArg Prod.snd this
  · rintro ⟨h₁, h₂⟩
    apply mem_nonZeroDivisors_iff_left.mpr
    intro w hw
    apply branchMap_injective R
    have he := congrArg (branchMap R) hw
    exact Prod.ext
      (by simpa [h₁] using congrArg Prod.fst he)
      (by simpa [h₂] using congrArg Prod.snd he)

variable (K : Type*) [CommRing K] [Algebra R[X] K] [IsFractionRing R[X] K]

/-- Restriction to the two branches followed by passage to their fraction fields. -/
def branchFractionMap : NodeAlgebra R 0 →+* K × K :=
  ((algebraMap R[X] K).prodMap (algebraMap R[X] K)).comp (branchMap R).toRingHom

omit [IsDomain R] [IsFractionRing R[X] K] in
/-- The comparison is the branch inclusion followed by the two fraction-ring maps. -/
theorem branchFractionMap_def :
    branchFractionMap R K =
      ((algebraMap R[X] K).prodMap (algebraMap R[X] K)).comp (branchMap R).toRingHom :=
  (rfl)

omit [IsDomain R] [IsFractionRing R[X] K] in
/-- The fraction-ring comparison is the componentwise image of the branch functions. -/
@[simp]
theorem branchFractionMap_apply (z : NodeAlgebra R 0) :
    branchFractionMap R K z =
      (algebraMap R[X] K (branchMap R z).1, algebraMap R[X] K (branchMap R z).2) :=
  (rfl)

omit [IsDomain R] in
/-- Passage to the two branch fraction fields is injective. -/
theorem branchFractionMap_injective : Function.Injective (branchFractionMap R K) := by
  intro z w h
  apply branchMap_injective R
  exact Prod.ext
    (IsFractionRing.injective R[X] K (congrArg Prod.fst h))
    (IsFractionRing.injective R[X] K (congrArg Prod.snd h))

/-- The product of the two branch fraction fields is the total ring of fractions
of the split node, with the algebra structure induced by `branchFractionMap`. -/
theorem isFractionRing_branchFractionMap :
    letI := (branchFractionMap R K).toAlgebra
    IsFractionRing (NodeAlgebra R 0) (K × K) := by
  let := (branchFractionMap R K).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hz := (mem_nonZeroDivisors_iff_branchMap R z).mp z.property
    -- Each coordinate of the image is a unit in the corresponding fraction field.
    exact Prod.isUnit_iff.mpr
      ⟨IsLocalization.map_units K ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr hz.1⟩,
        IsLocalization.map_units K ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr hz.2⟩⟩
  · intro q
    obtain ⟨⟨p₁, s₁⟩, h₁⟩ := IsLocalization.surj R[X]⁰ q.1
    obtain ⟨⟨p₂, s₂⟩, h₂⟩ := IsLocalization.surj R[X]⁰ q.2
    -- Multiplication by `t` kills both constant coefficients, so these pairs descend.
    obtain ⟨d, hd⟩ := (mem_range_branchMap_iff R
      (s₁.val * s₂.val * X, s₁.val * s₂.val * X)).mpr rfl
    obtain ⟨n, hn⟩ := (mem_range_branchMap_iff R
      (p₁ * s₂.val * X, p₂ * s₁.val * X)).mpr (by simp [mul_coeff_zero])
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hd hn
    have hs₁ : s₁.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₁.property
    have hs₂ : s₂.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₂.property
    have hdreg : d ∈ (NodeAlgebra R 0)⁰ := by
      rw [mem_nonZeroDivisors_iff_branchMap, hd]
      exact ⟨mul_ne_zero (mul_ne_zero hs₁ hs₂) X_ne_zero,
        mul_ne_zero (mul_ne_zero hs₁ hs₂) X_ne_zero⟩
    refine ⟨⟨n, ⟨d, hdreg⟩⟩, ?_⟩
    -- The algebra maps are the named comparison, not arbitrary maps to a product ring.
    simp only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, hd, hn,
      Prod.mul_def, map_mul]
    apply Prod.ext
    · dsimp
      calc
        q.1 * (algebraMap R[X] K s₁.val * algebraMap R[X] K s₂.val *
            algebraMap R[X] K X) =
            (q.1 * algebraMap R[X] K s₁.val) * algebraMap R[X] K s₂.val *
              algebraMap R[X] K X := by ring
        _ = _ := by rw [h₁]
    · dsimp
      calc
        q.2 * (algebraMap R[X] K s₁.val * algebraMap R[X] K s₂.val *
            algebraMap R[X] K X) =
            (q.2 * algebraMap R[X] K s₂.val) * algebraMap R[X] K s₁.val *
              algebraMap R[X] K X := by ring
        _ = _ := by rw [h₂]
  · intro z w h
    exact ⟨1, by simpa using branchFractionMap_injective R K h⟩

/-- A split node over a domain is not integrally closed: the idempotent separating
its two branches is integral in the total ring of fractions but does not descend. -/
theorem not_isIntegrallyClosed : ¬ IsIntegrallyClosed (NodeAlgebra R 0) := by
  let F := FractionRing R[X]
  let := (branchFractionMap R F).toAlgebra
  have : IsFractionRing (NodeAlgebra R 0) (F × F) :=
    isFractionRing_branchFractionMap R F
  have hint : IsIntegral (NodeAlgebra R 0) ((1, 0) : F × F) := by
    rw [IsIntegral, RingHom.algebraMap_toAlgebra, branchFractionMap_def]
    simpa only [RingHom.coe_prodMap, Prod.map, map_one, map_zero] using
      ((finite_branchMap R).to_isIntegral (1, 0)).map
        ((algebraMap R[X] F).prodMap (algebraMap R[X] F))
  intro h
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff (F × F)).mp h hint
  have h₁ : (branchMap R z).1 = 1 :=
    IsFractionRing.injective R[X] F (by
      simpa only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, map_one] using
        congrArg Prod.fst hz)
  have h₂ : (branchMap R z).2 = 0 :=
    IsFractionRing.injective R[X] F (by
      simpa only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, map_zero] using
        congrArg Prod.snd hz)
  have he := (mem_range_branchMap_iff R (branchMap R z)).mp ⟨z, rfl⟩
  simp [h₁, h₂] at he

variable [IsIntegrallyClosed R]

/-- The branch algebra is the integral closure of the split node in its total ring
of fractions. The embeddings are the branch inclusion and the componentwise maps
from the polynomial rings to their fraction fields. -/
theorem isIntegralClosure_branchFractionMap :
    letI := (branchFractionMap R K).toAlgebra
    letI := ((algebraMap R[X] K).prodMap (algebraMap R[X] K)).toAlgebra
    IsIntegralClosure (R[X] × R[X]) (NodeAlgebra R 0) (K × K) := by
  let := (branchFractionMap R K).toAlgebra
  let := ((algebraMap R[X] K).prodMap (algebraMap R[X] K)).toAlgebra
  refine ⟨?_, ?_⟩
  · intro p q h
    exact Prod.ext
      (IsFractionRing.injective R[X] K (congrArg Prod.fst h))
      (IsFractionRing.injective R[X] K (congrArg Prod.snd h))
  · intro q
    constructor
    · intro hq
      have h₁ : IsIntegral R[X] q.1 := hq.map_of_comp_eq
        ((RingHom.fst R[X] R[X]).comp (branchMap R).toRingHom)
        (RingHom.fst K K) (by ext; rfl)
      have h₂ : IsIntegral R[X] q.2 := hq.map_of_comp_eq
        ((RingHom.snd R[X] R[X]).comp (branchMap R).toRingHom)
        (RingHom.snd K K) (by ext; rfl)
      obtain ⟨p₁, hp₁⟩ := (isIntegrallyClosed_iff K).mp inferInstance h₁
      obtain ⟨p₂, hp₂⟩ := (isIntegrallyClosed_iff K).mp inferInstance h₂
      exact ⟨(p₁, p₂), Prod.ext hp₁ hp₂⟩
    · rintro ⟨p, rfl⟩
      exact ((finite_branchMap R).to_isIntegral p).map
        ((algebraMap R[X] K).prodMap (algebraMap R[X] K))

end TauCeti.NodeAlgebra
