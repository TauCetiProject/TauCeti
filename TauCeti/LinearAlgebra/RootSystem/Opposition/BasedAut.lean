/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Submatrix
public import TauCeti.LinearAlgebra.RootSystem.Negation
public import TauCeti.LinearAlgebra.RootSystem.Opposition.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# The opposition involution as a based automorphism

Let `P` be a finite reduced crystallographic root pairing over a characteristic-zero domain, with
a base `b` and longest Weyl-group element `w₀`. The opposition involution
`TauCeti.opposition P b`, the map `i ↦ -w₀ i` on root indices, is the action on indices of the
automorphism `δ = -w₀` of `P`. This file constructs `δ` as the based automorphism
`TauCeti.oppositionAut P b ∈ Aut(P, b)` and reads off its standard properties.

* `δ` is the based factor of `-1`. In the decomposition `Aut(P) = W ⋊ Aut(P, b)` of
  `RootPairing.Base.semidirectProductMulEquiv`, the automorphism `-1` factors as `w₀ δ`. Indeed `δ`
  is the only based automorphism differing from `-1` by an element of the Weyl group.
* `δ` is an involution and preserves the pairing, so the permutation `TauCeti.oppositionPerm P b`
  of the simple roots that it induces is a symmetry of the Cartan matrix of `b`.
* Changing the base along an automorphism `g` conjugates `δ` by `g`.
* `δ` is trivial exactly when `w₀ = -1`, which happens exactly when `-1` lies in the Weyl group;
  for a root system this is also the triviality of `TauCeti.oppositionPerm P b`.

These are the root-system inputs to the duality of highest-weight modules. By the self-duality
criterion `TauCeti.nonempty_lieModuleEquiv_dual_iff`, a finite-dimensional irreducible module of
highest weight `λ` is self-dual exactly when `δ` fixes `λ`; in particular, when `w₀ = -1` every
such module is self-dual.

## Main definitions

* `TauCeti.oppositionAut`: the based automorphism `δ = -w₀`.

## Main results

* `TauCeti.oppositionAut_indexEquiv_apply`, `TauCeti.oppositionAut_smul`,
  `TauCeti.coroot_opposition`: `δ` realises the opposition involution on root indices, acts on
  weights by `-w₀`, and transports coroots like roots.
* `TauCeti.semidirectProductMulEquiv_symm_neg` and
  `TauCeti.neg_mul_mem_weylGroup_iff_eq_oppositionAut`: `-1 = w₀ δ` is the decomposition of `-1`,
  and `δ` is the only based automorphism in the coset `-W`.
* `TauCeti.oppositionAut_mul_self`: `δ` is an involution.
* `TauCeti.pairingIn_opposition`, `TauCeti.cartanMatrix_oppositionPerm` and
  `TauCeti.oppositionPerm_mem_matrixSymmetryGroup`: the opposition involution preserves the
  pairing and the Cartan matrix.
* `TauCeti.coe_oppositionAut_map` and `TauCeti.opposition_map_indexEquiv`: the change-of-base
  comparison.
* `TauCeti.oppositionAut_eq_one_iff`, `TauCeti.neg_mem_weylGroup_iff` and
  `TauCeti.oppositionPerm_eq_one_iff`: `δ` is trivial exactly when `w₀ = -1`, exactly when `-1` is
  in the Weyl group.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1.5 and §1.6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 and
  §12.2.
-/

public section

namespace TauCeti

open RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic]
  [P.IsReduced] (b : P.Base)

/-- The automorphism `-w₀` acts on root indices by the opposition involution. -/
private theorem indexEquiv_neg_mul_longestElement (i : ι) :
    (RootPairing.Equiv.neg P * (longestElement P b : P.Aut)).indexEquiv i = opposition P b i :=
  P.root.injective <| by
    rw [Equiv.root_indexEquiv_eq_smul, mul_smul, RootPairing.Equiv.neg_smul, root_opposition,
      Subgroup.smul_def]

/-- **The opposition automorphism** `δ = -w₀` of a base `b`: the product of the negation
automorphism and the longest element of the Weyl group. It carries the simple roots of `b` onto
themselves, so it is a based automorphism; on root indices it is the opposition involution
`TauCeti.opposition P b`. -/
noncomputable def oppositionAut : b.basedAut :=
  ⟨RootPairing.Equiv.neg P * longestElement P b,
    Base.mem_basedAut_iff_forall_mem_support.mpr fun i hi ↦ by
      rw [indexEquiv_neg_mul_longestElement]
      exact opposition_mem_support P b hi⟩

/-- The opposition automorphism is the product of `-1` and `w₀`. -/
theorem coe_oppositionAut :
    (oppositionAut P b : P.Aut) = RootPairing.Equiv.neg P * longestElement P b :=
  (rfl)

/-- **The opposition automorphism realises the opposition involution** on root indices. -/
@[simp]
theorem oppositionAut_indexEquiv_apply (i : ι) :
    (oppositionAut P b : P.Aut).indexEquiv i = opposition P b i :=
  indexEquiv_neg_mul_longestElement P b i

/-- **The opposition automorphism acts on weights by `-w₀`.** -/
@[simp]
theorem oppositionAut_smul (y : M) :
    (oppositionAut P b : P.Aut) • y = -(longestElement P b • y) := by
  rw [coe_oppositionAut, mul_smul, RootPairing.Equiv.neg_smul, Subgroup.smul_def]

/-- **The coroot of the opposite root** is the negative of the image of the coroot under the
longest element, the coroot-side companion of `TauCeti.root_opposition`. The Weyl group acts on
the coweights contravariantly, through `MulOpposite`; no inverse appears because `w₀` is an
involution. -/
@[simp]
theorem coroot_opposition (i : ι) :
    P.coroot (opposition P b i) =
      -(MulOpposite.op (longestElement P b : P.Aut) • P.coroot i) := by
  have h := Hom.coroot_coweightMap_apply P P i (longestElement P b : P.Aut).toHom
  have hsymm : (longestElement P b : P.Aut).indexEquiv.symm i =
      (longestElement P b : P.Aut).indexEquiv i :=
    (_root_.Equiv.symm_apply_eq _).mpr (weylGroupToPerm_longestElement_involutive P b i).symm
  rw [← indexEquiv_neg_mul_longestElement, Equiv.mul_eq_comp, Equiv.toHom_comp,
    Hom.comp_indexEquiv_apply, RootPairing.Equiv.neg_indexEquiv_apply,
    coroot_reflectionPerm, coreflection_apply_self, ← hsymm, ← h]
  -- The action of `P.Autᵐᵒᵖ` on coweights is by definition through the coweight maps.
  rfl

/-! ### The based factor of `-1` -/

/-- **The decomposition of `-1`**: in `Aut(P) = W ⋊ Aut(P, b)` the automorphism `-1` factors as
`w₀ δ`, with Weyl factor the longest element and based factor the opposition automorphism. -/
theorem semidirectProductMulEquiv_symm_neg :
    b.semidirectProductMulEquiv.symm (RootPairing.Equiv.neg P) =
      ⟨longestElement P b, oppositionAut P b⟩ := by
  rw [← Base.semidirectProductMulEquiv_symm_mul, coe_oppositionAut, ← mul_assoc,
    ← (RootPairing.Equiv.commute_neg P _).eq, mul_assoc, ← Subgroup.coe_mul,
    ← sq, longestElement_sq, Subgroup.coe_one, mul_one]

/-- **The opposition automorphism is the only based automorphism in the coset `-W`.** A based
automorphism `δ` differs from `-1` by an element of the Weyl group exactly when it is the
opposition automorphism. -/
theorem neg_mul_mem_weylGroup_iff_eq_oppositionAut {δ : P.Aut} (hδ : δ ∈ b.basedAut) :
    RootPairing.Equiv.neg P * δ ∈ P.weylGroup ↔ δ = oppositionAut P b := by
  refine ⟨fun hw ↦ ?_, fun h ↦ ?_⟩
  · -- `δ⁻¹ (-w₀)` lies both in the Weyl group and among the based automorphisms.
    have hW : δ⁻¹ * oppositionAut P b ∈ P.weylGroup := by
      rw [coe_oppositionAut, ← RootPairing.Equiv.neg_inv P, ← mul_assoc, ← mul_inv_rev]
      exact mul_mem (inv_mem hw) (longestElement P b).2
    have hB : δ⁻¹ * oppositionAut P b ∈ b.basedAut := mul_mem (inv_mem hδ) (oppositionAut P b).2
    exact inv_mul_eq_one.mp <| Subgroup.disjoint_def.mp
      (Base.isComplement'_weylGroup_basedAut b).disjoint hW hB
  · rw [h, coe_oppositionAut, ← mul_assoc, RootPairing.Equiv.neg_mul_neg, one_mul]
    exact (longestElement P b).2

/-- **The opposition automorphism is an involution.** -/
@[simp]
theorem oppositionAut_mul_self : oppositionAut P b * oppositionAut P b = 1 :=
  Subtype.ext <| by
    rw [Subgroup.coe_mul, coe_oppositionAut,
      ((RootPairing.Equiv.commute_neg P _).symm).mul_mul_mul_comm, RootPairing.Equiv.neg_mul_neg,
      one_mul, ← Subgroup.coe_mul, ← sq, longestElement_sq, Subgroup.coe_one, Subgroup.coe_one]

/-- The opposition automorphism is its own inverse. -/
@[simp]
theorem oppositionAut_inv : (oppositionAut P b)⁻¹ = oppositionAut P b :=
  inv_eq_of_mul_eq_one_right (oppositionAut_mul_self P b)

/-! ### The Cartan matrix -/

/-- **The opposition involution preserves the pairing.** -/
@[simp]
theorem pairing_opposition (i j : ι) :
    P.pairing (opposition P b i) (opposition P b j) = P.pairing i j := by
  simpa only [oppositionAut_indexEquiv_apply] using (oppositionAut P b : P.Aut).toHom.pairing

/-- **The opposition involution preserves the pairing** valued in a coefficient subring. -/
@[simp]
theorem pairingIn_opposition (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S (opposition P b i) (opposition P b j) = P.pairingIn S i j := by
  simpa only [oppositionAut_indexEquiv_apply] using
    (oppositionAut P b : P.Aut).toHom.pairingIn_indexEquiv S i j

/-- **The opposition involution preserves the Cartan matrix** of the base. -/
@[simp]
theorem cartanMatrix_oppositionPerm (i j : b.support) :
    b.cartanMatrix (oppositionPerm P b i) (oppositionPerm P b j) = b.cartanMatrix i j := by
  simp only [Base.cartanMatrix, Base.cartanMatrixIn_def, coe_oppositionPerm, pairingIn_opposition]

/-- **The opposition involution is a symmetry of the Cartan matrix.** -/
theorem oppositionPerm_mem_matrixSymmetryGroup :
    oppositionPerm P b ∈ matrixSymmetryGroup b.cartanMatrix :=
  mem_matrixSymmetryGroup_iff.mpr <| Matrix.ext fun i j ↦ cartanMatrix_oppositionPerm P b i j

/-! ### Change of base -/

/-- **Changing the base conjugates the opposition automorphism**: for the base `b.map g`
transported along an automorphism `g`, the opposition automorphism is `g δ g⁻¹`. -/
theorem coe_oppositionAut_map (g : P.Aut) :
    (oppositionAut P (b.map g) : P.Aut) = g * oppositionAut P b * g⁻¹ := by
  have hB : g * oppositionAut P b * g⁻¹ ∈ (b.map g).basedAut := by
    rw [Base.mem_basedAut_iff_map_eq, ← Base.map_mul, inv_mul_cancel_right, Base.map_mul,
      Base.map_eq_of_mem_basedAut (oppositionAut P b).2]
  refine ((neg_mul_mem_weylGroup_iff_eq_oppositionAut P (b.map g) hB).mp ?_).symm
  -- `-(g δ g⁻¹) = g (-δ) g⁻¹`, and `-δ = w₀` lies in the normal subgroup `W`.
  have hw := (neg_mul_mem_weylGroup_iff_eq_oppositionAut P b (oppositionAut P b).2).mpr rfl
  rw [← mul_assoc, ← mul_assoc, (RootPairing.Equiv.commute_neg P g).eq, mul_assoc g, ← mul_assoc]
  exact (inferInstance : P.weylGroup.Normal).conj_mem _ hw g

/-- **Changing the base transports the opposition involution**: the opposition involution of the
base `b.map g` corresponds to that of `b` under the action of `g` on root indices. -/
theorem opposition_map_indexEquiv (g : P.Aut) (i : ι) :
    opposition P (b.map g) (g.indexEquiv i) = g.indexEquiv (opposition P b i) :=
  P.root.injective <| by
    rw [← oppositionAut_indexEquiv_apply, ← oppositionAut_indexEquiv_apply,
      Equiv.root_indexEquiv_eq_smul, Equiv.root_indexEquiv_eq_smul,
      Equiv.root_indexEquiv_eq_smul, Equiv.root_indexEquiv_eq_smul, coe_oppositionAut_map,
      smul_smul, inv_mul_cancel_right, mul_smul]

/-! ### Trivial opposition -/

/-- **The opposition automorphism is trivial exactly when `w₀ = -1`.** -/
theorem oppositionAut_eq_one_iff :
    oppositionAut P b = 1 ↔ (longestElement P b : P.Aut) = RootPairing.Equiv.neg P := by
  rw [← Subtype.coe_inj, coe_oppositionAut, Subgroup.coe_one, mul_eq_one_iff_inv_eq,
    RootPairing.Equiv.neg_inv, eq_comm]

/-- **`-1` lies in the Weyl group exactly when it is the longest element.** -/
theorem neg_mem_weylGroup_iff :
    RootPairing.Equiv.neg P ∈ P.weylGroup ↔
      (longestElement P b : P.Aut) = RootPairing.Equiv.neg P := by
  refine ⟨fun h ↦ (oppositionAut_eq_one_iff P b).mp ?_, fun h ↦ h ▸ (longestElement P b).2⟩
  -- `δ = -w₀` is then a based automorphism in the Weyl group, so it is trivial.
  have hW : (oppositionAut P b : P.Aut) ∈ P.weylGroup := mul_mem h (longestElement P b).2
  exact Subtype.ext <| Subgroup.disjoint_def.mp
    (Base.isComplement'_weylGroup_basedAut b).disjoint hW (oppositionAut P b).2

/-- **For a root system, the opposition involution of the simple roots is trivial exactly when
`w₀ = -1`.** An automorphism of a root system fixing every simple root is the identity. -/
theorem oppositionPerm_eq_one_iff [P.IsRootSystem] :
    oppositionPerm P b = 1 ↔ (longestElement P b : P.Aut) = RootPairing.Equiv.neg P := by
  rw [← oppositionAut_eq_one_iff]
  refine ⟨fun h ↦ Subtype.ext <| b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ ?_, fun h ↦ ?_⟩
  · simpa using congrArg Subtype.val (_root_.Equiv.ext_iff.mp h ⟨i, hi⟩)
  · refine _root_.Equiv.ext fun i ↦ Subtype.ext ?_
    simp [← oppositionAut_indexEquiv_apply, h]

end TauCeti
