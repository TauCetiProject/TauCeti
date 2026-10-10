/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Kernel
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange

/-!
# Connected kernels of homomorphisms of multiplicative-type groups

In characteristic `p`, a finite kernel of a homomorphism of multiplicative-type groups
is geometrically connected exactly when the geometric character cokernel is a `p`-group.
Equivalently, its coordinate-algebra dimension is a power of `p`, including `p ^ 0 = 1`
for the trivial kernel.

The sufficient condition works in exponential characteristic and does not require the
kernel to be finite. The proofs identify the geometric kernel with the group algebra of
the character cokernel and descend geometric connectedness to the original field.
No smoothness or perfectness assumption is imposed. In particular, connected kernels
include the nonreduced groups `μ_(p ^ n)`, whose coordinate-algebra dimension records
their infinitesimal structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable (hH : multiplicativeTypeCommHopfAlgProperty k H)
variable (hK : multiplicativeTypeCommHopfAlgProperty k K) (f : H.obj ⟶ K.obj)

include hH hK

/-- In exponential characteristic `p`, a `p`-group geometric character cokernel gives a
geometrically connected kernel. No finiteness assumption on the kernel is required. -/
theorem geometricallyConnected_kernelCoordinate_of_isPGroup
    (p : ℕ) [ExpChar k p]
    (hp : IsPGroup p (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
      (CommHopfAlgCat.geometricCharacterMap f).range)) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) := by
  let _ : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  apply geometricallyConnectedCommHopfAlgProperty.of_baseChange k (AlgebraicClosure k)
  exact ((geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_iff_of_iso
    (geometricKernelCoordinateIso hH hK f)).mpr
      (DiagonalizableGroup.geometricallyConnected_of_isPGroup (AlgebraicClosure k) p hp)

variable [Module.Finite k
  (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f))]

/-- In prime characteristic `p`, a finite multiplicative-type kernel is geometrically
connected exactly when the geometric character cokernel is a `p`-group. -/
theorem geometricallyConnected_kernelCoordinate_iff_isPGroup
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    geometricallyConnectedCommHopfAlgProperty k
        (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ↔
      IsPGroup p (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
        (CommHopfAlgCat.geometricCharacterMap f).range) := by
  let _ := (moduleFinite_kernelCoordinate_iff_finite_quotient hH hK f).mp inferInstance
  exact (geometricallyConnectedCommHopfAlgProperty.baseChange_iff k (AlgebraicClosure k)
    _).symm.trans <|
      ((geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_iff_of_iso
        (geometricKernelCoordinateIso hH hK f)).trans
          (DiagonalizableGroup.geometricallyConnected_iff_isPGroup (AlgebraicClosure k) p _)

/-- A finite multiplicative-type kernel in prime characteristic `p` is geometrically
connected exactly when its scheme-theoretic degree is a power of `p`. -/
theorem geometricallyConnected_kernelCoordinate_iff_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    geometricallyConnectedCommHopfAlgProperty k
        (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ↔
      ∃ n : ℕ, Module.finrank k
        (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) = p ^ n := by
  let _ := (moduleFinite_kernelCoordinate_iff_finite_quotient hH hK f).mp inferInstance
  rw [geometricallyConnected_kernelCoordinate_iff_isPGroup hH hK f p,
    IsPGroup.iff_card, finrank_kernelCoordinate hH hK f]

end TauCeti.multiplicativeTypeCommHopfAlgProperty
