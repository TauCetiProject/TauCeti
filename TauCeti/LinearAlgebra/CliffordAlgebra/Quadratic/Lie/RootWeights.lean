/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Casimir
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Coordinates
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.LeftRegular

/-!
# Cartan weights of the adjoint Clifford lift

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form and let `H` be a
Cartan subalgebra. The coordinate formula for the adjoint Clifford lift can be decomposed into
opposite root-space projections:

```text
adjointCliffordHom K L x =
  1 / 4 • ∑ χ, ∑ i, adjointBivector Q x (πχ (b i)) (π(-χ) (b* i)).
```

For `h ∈ H`, the first projected vector is an eigenvector of `ad h`, so its bracket contributes
the scalar `χ(h)`. This gives the Cartan-weight formula for the lift with the same `1 / 4`
normalization.

The final two results concern Kostant's left-regular action on the Clifford algebra. If `y` lies
in the root space of `χ`, then left multiplication by the Clifford generator `ι(y)` sends a
simultaneous eigenvector of weight `μ` to one of weight `χ + μ`. This is a statement about the
left-regular action, not the inner derivation action.

## Main results

* `CliffordAlgebra.adjointCliffordHom_eq_sum_weight`: the adjoint lift split into opposite
  root-space projections.
* `CliffordAlgebra.adjointCliffordHom_cartan_eq_sum_weight`: the Cartan specialization.
* `CliffordAlgebra.kostant_lie_ι_mul_of_mem_rootSpace`: the pointwise weight-shift identity.
* `CliffordAlgebra.mem_genWeightSpace_ι_mul_of_mem_rootSpace`: multiplication by a root
  generator raises Kostant weights.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapters
  5--10.
-/

public section

universe u v w

open TauCeti LieAlgebra LieModule

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H L]

omit [CharZero K] [IsAlgClosed K] in
/-- The adjoint Clifford lift, decomposed using the `χ` and `-χ` projections of a basis and its
Killing-dual basis. The coefficient is the quadratic normalization of the Killing form. -/
theorem adjointCliffordHom_eq_sum_weight
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (x : L) :
    adjointCliffordHom K L x =
      (4 : K)⁻¹ • ∑ χ : Weight K H L, ∑ i,
        adjointBivector (TauCeti.LieAlgebra.killingQuadraticForm K L) x
          (TauCeti.genWeightSpaceProjection K H L χ (b i))
          (TauCeti.genWeightSpaceProjection K H L (-χ) (TauCeti.killingDualBasis b i)) := by
  rw [adjointCliffordHom_eq_sum_bivector b x]
  congr 1
  exact TauCeti.sum_apply_killingDualBasis_eq_sum_weight H
    (adjointBivector (TauCeti.LieAlgebra.killingQuadraticForm K L) x) b

/-- For a Cartan element `h`, the `χ` summand of the adjoint Clifford lift is scaled by `χ h`.
The second vector in each bivector belongs to the opposite root-space projection. -/
theorem adjointCliffordHom_cartan_eq_sum_weight
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (h : H) :
    adjointCliffordHom K L (h : L) =
      (4 : K)⁻¹ • ∑ χ : Weight K H L, χ h • ∑ i,
        bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
          (TauCeti.genWeightSpaceProjection K H L χ (b i))
          (TauCeti.genWeightSpaceProjection K H L (-χ) (TauCeti.killingDualBasis b i)) := by
  rw [adjointCliffordHom_eq_sum_weight H b (h : L)]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [adjointBivector_apply]
  have hroot := (TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp
    (TauCeti.genWeightSpaceProjection_apply_mem χ (b i))) h
  rw [hroot]
  simp only [bivector_def, map_smul, smul_mul_assoc, mul_smul_comm]
  module

open scoped CliffordAlgebra in
omit [LieModule.IsTriangularizable K H L] in
/-- If `y` is a root vector of weight `χ` and `c` is a simultaneous eigenvector of weight `μ`,
then `ι(y) * c` is a simultaneous eigenvector of weight `χ + μ` for Kostant's left-regular
action. -/
theorem kostant_lie_ι_mul_of_mem_rootSpace
    {χ : Weight K H L} {y : L} (hy : y ∈ rootSpace H χ)
    {mu : H → K} {c : CliffordAlgebra (TauCeti.LieAlgebra.killingQuadraticForm K L)}
    (hc : ∀ h : H, ⁅(h : L), c⁆ = mu h • c) (h : H) :
    ⁅(h : L), ι (TauCeti.LieAlgebra.killingQuadraticForm K L) y * c⁆ =
      (χ h + mu h) • (ι (TauCeti.LieAlgebra.killingQuadraticForm K L) y * c) := by
  rw [kostant_lie_def, ← mul_assoc, ← kostant_lie_def, kostant_lie_ι]
  have hy' := (TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hy) h
  rw [hy']
  simp only [add_mul, map_smul, smul_mul_assoc, mul_assoc]
  rw [← kostant_lie_def, hc h, mul_smul_comm]
  module

open scoped CliffordAlgebra in
omit [LieModule.IsTriangularizable K H L] in
/-- Left multiplication by the Clifford generator of a root vector raises a generalized weight
by that root for Kostant's left-regular action. -/
theorem mem_genWeightSpace_ι_mul_of_mem_rootSpace
    {χ : Weight K H L} {y : L} (hy : y ∈ rootSpace H χ)
    {mu : H → K} {c : CliffordAlgebra (TauCeti.LieAlgebra.killingQuadraticForm K L)}
    (hc : c ∈ genWeightSpace (CliffordAlgebra
      (TauCeti.LieAlgebra.killingQuadraticForm K L)) mu) :
    ι (TauCeti.LieAlgebra.killingQuadraticForm K L) y * c ∈
      genWeightSpace (CliffordAlgebra (TauCeti.LieAlgebra.killingQuadraticForm K L))
        (fun h ↦ χ h + mu h) := by
  rw [TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul]
  intro h
  apply kostant_lie_ι_mul_of_mem_rootSpace H hy
  intro h'
  simpa only using (TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hc) h'

end CliffordAlgebra
