/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Borel
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
* `CliffordAlgebra.adjointCliffordHom_cartan_eq_sum_posRoots`: the same lift regrouped over the
  positive roots.
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

omit [CharZero K] [IsAlgClosed K] in
private theorem projectedBivectorSum_neg
    {iota : Type w} [Fintype iota] [DecidableEq iota]
    (b : Module.Basis iota K L) (chi : Weight K H L) :
    (∑ i, bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
      (TauCeti.genWeightSpaceProjection K H L (-chi) (b i))
      (TauCeti.genWeightSpaceProjection K H L chi (TauCeti.killingDualBasis b i))) =
      -∑ i, bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
        (TauCeti.genWeightSpaceProjection K H L chi (b i))
        (TauCeti.genWeightSpaceProjection K H L (-chi) (TauCeti.killingDualBasis b i)) := by
  let f : L →ₗ[K] L →ₗ[K]
      CliffordAlgebra (TauCeti.LieAlgebra.killingQuadraticForm K L) :=
    (bivectorBilinear (TauCeti.LieAlgebra.killingQuadraticForm K L)).comp
      (TauCeti.genWeightSpaceProjection K H L (-chi)) |>.compl₂
        (TauCeti.genWeightSpaceProjection K H L chi)
  have hb := TauCeti.sum_apply_killingDualBasis_eq f b (TauCeti.killingDualBasis b)
  simp only [f, LinearMap.compl₂_apply, LinearMap.comp_apply,
    TauCeti.killingDualBasis_killingDualBasis] at hb
  have hb' : (∑ i, bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
        (TauCeti.genWeightSpaceProjection K H L (-chi) (b i))
        (TauCeti.genWeightSpaceProjection K H L chi (TauCeti.killingDualBasis b i))) =
      ∑ i, bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
        (TauCeti.genWeightSpaceProjection K H L (-chi) (TauCeti.killingDualBasis b i))
        (TauCeti.genWeightSpaceProjection K H L chi (b i)) := by
    simpa only [bivectorBilinear_apply] using hb
  rw [hb']
  calc
    _ = ∑ i, -bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
        (TauCeti.genWeightSpaceProjection K H L chi (b i))
        (TauCeti.genWeightSpaceProjection K H L (-chi) (TauCeti.killingDualBasis b i)) :=
      Finset.sum_congr rfl fun i _ ↦ bivector_swap _ _ _
    _ = _ := by rw [← Finset.sum_neg_distrib]

/-- The Cartan adjoint Clifford lift, regrouped over the positive roots. The terms at a root and
its negative agree: negating the weight scalar and swapping the projected bivector each contribute
one sign. Hence the two terms turn the quadratic coefficient `1 / 4` into `1 / 2`. -/
theorem adjointCliffordHom_cartan_eq_sum_posRoots
    {iota : Type w} [Fintype iota] [DecidableEq iota] (b : Module.Basis iota K L)
    (base : (LieAlgebra.IsKilling.rootSystem H).Base) (h : H) :
    adjointCliffordHom K L (h : L) =
      (2 : K)⁻¹ • ∑ a ∈ TauCeti.posRootsFinset (LieAlgebra.IsKilling.rootSystem H) base,
        ((a : H.root) : Weight K H L) h • ∑ i,
          bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
            (TauCeti.genWeightSpaceProjection K H L (a : H.root) (b i))
            (TauCeti.genWeightSpaceProjection K H L (-(a : H.root))
              (TauCeti.killingDualBasis b i)) := by
  classical
  let c : Weight K H L →
      CliffordAlgebra (TauCeti.LieAlgebra.killingQuadraticForm K L) := fun chi ↦ ∑ i,
    bivector (TauCeti.LieAlgebra.killingQuadraticForm K L)
      (TauCeti.genWeightSpaceProjection K H L chi (b i))
      (TauCeti.genWeightSpaceProjection K H L (-chi) (TauCeti.killingDualBasis b i))
  have hcneg (chi : Weight K H L) : c (-chi) = -c chi := by
    simpa only [c, neg_neg] using projectedBivectorSum_neg H b chi
  have hregroup :
      (4 : K)⁻¹ • ∑ chi : Weight K H L, chi h • c chi =
        (2 : K)⁻¹ • ∑ a ∈
          TauCeti.posRootsFinset (LieAlgebra.IsKilling.rootSystem H) base,
          ((a : Weight K H L) h • c (a : Weight K H L)) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ H.root)]
    have hzero : ∑ chi ∈ Finset.univ \ H.root, chi h • c chi = 0 := by
      refine Finset.sum_eq_zero fun chi hchi ↦ ?_
      have hz : chi.IsZero := not_not.mp (by simpa [LieSubalgebra.root] using
        (Finset.mem_sdiff.mp hchi).2)
      rw [hz.eq]
      simp
    rw [hzero, zero_add, ← Finset.sum_coe_sort H.root,
      TauCeti.sum_root_eq_sum_posRootsFinset (H := H) base]
    have hpair : ∀ a : H.root,
        ((a : Weight K H L) h • c a + ((-a : H.root) : Weight K H L) h •
          c ((-a : H.root) : Weight K H L)) =
          (2 : K) • ((a : Weight K H L) h • c a) := by
      intro a
      -- `val_neg_root` is the named interface exposing the definitional compatibility between
      -- root-subtype negation and weight negation; evaluation compatibility follows from it.
      have hneg_coe : ((-a : H.root) : Weight K H L) = -(a : Weight K H L) :=
        LieAlgebra.IsKilling.val_neg_root
      have hneg_apply : ((-a : H.root) : Weight K H L) h = -((a : Weight K H L) h) := by
        exact congrArg (fun chi : Weight K H L ↦ chi h) hneg_coe
      rw [hneg_apply, hneg_coe, hcneg]
      simp only [smul_neg]
      module
    have hsum :
        ∑ a ∈ TauCeti.posRootsFinset (LieAlgebra.IsKilling.rootSystem H) base,
            ((a : Weight K H L) h • c (a : Weight K H L) +
              ((-a : H.root) : Weight K H L) h •
                c ((-a : H.root) : Weight K H L)) =
          (2 : K) • ∑ a ∈ TauCeti.posRootsFinset (LieAlgebra.IsKilling.rootSystem H) base,
            ((a : Weight K H L) h • c (a : Weight K H L)) := by
      rw [Finset.sum_congr rfl fun a _ ↦ hpair a, ← Finset.smul_sum]
    calc
      _ = (4 : K)⁻¹ • ((2 : K) •
          ∑ a ∈ TauCeti.posRootsFinset (LieAlgebra.IsKilling.rootSystem H) base,
            ((a : Weight K H L) h • c (a : Weight K H L))) :=
        congrArg ((4 : K)⁻¹ • ·) hsum
      _ = _ := by
        rw [smul_smul]
        congr 1
        norm_num
  rw [adjointCliffordHom_cartan_eq_sum_weight H b h]
  simpa only [c] using hregroup

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
