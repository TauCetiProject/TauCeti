/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Kernel
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Isogeny
public import TauCeti.Algebra.MonoidAlgebra.Etale
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Unramified.Finite

/-!
# Étale kernels of multiplicative-type groups

A homomorphism of groups of multiplicative type has étale kernel precisely when the
order of its geometric character cokernel is invertible in the ground field. Finiteness
of the kernel or cokernel need not be assumed: an étale algebra over a field is finite,
and `Nat.card` of an infinite cokernel is zero, which is not a unit.

The geometric kernel comparison identifies its coordinate algebra over the algebraic
closure with the corresponding group algebra. Étaleness then descends along the field
extension. Together with the character criterion for central isogenies, this distinguishes
étale kernels from infinitesimal kernels such as `μ_p` in characteristic `p`.
The field need not be perfect, and the ambient groups need not be smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9 and §12.d.
-/

public section

open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable (hH : multiplicativeTypeCommHopfAlgProperty k H)
variable (hK : multiplicativeTypeCommHopfAlgProperty k K) (f : H.obj ⟶ K.obj)

include hH hK

/-- A multiplicative-type kernel is étale exactly when the order of the geometric
character cokernel is invertible in the ground field. In particular, this condition
forces the kernel and the cokernel to be finite. -/
theorem etale_kernelCoordinate_iff_isUnit_card :
    Algebra.Etale k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ↔
      IsUnit (Nat.card (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
        (CommHopfAlgCat.geometricCharacterMap f).range) : k) := by
  let L := AlgebraicClosure k
  let Q := CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)
  let C := CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
    (CommHopfAlgCat.geometricCharacterMap f).range
  let e : L ⊗[k] Q ≃ₐ[L] MonoidAlgebra L C :=
    (CommHopfAlgCat.ofIso (geometricKernelCoordinateIso hH hK f)).toAlgEquiv
  change Algebra.Etale k Q ↔ IsUnit (Nat.card C : k)
  constructor
  · intro h
    let _ := h
    let _ : Module.Finite k Q := Algebra.FormallyUnramified.finite_of_free k Q
    let _ : Finite C :=
      (moduleFinite_kernelCoordinate_iff_finite_quotient hH hK f).mp inferInstance
    let _ : Algebra.Etale L (MonoidAlgebra L C) := Algebra.Etale.of_equiv e
    have hu := (MonoidAlgebra.etale_iff_isUnit_card C L).mp inferInstance
    rw [isUnit_iff_ne_zero] at hu ⊢
    intro hz
    apply hu
    simpa only [map_natCast, map_zero] using congrArg (algebraMap k L) hz
  · intro h
    let _ : Finite C := Nat.finite_of_card_ne_zero (by
      intro hz
      simp [hz] at h)
    let _ : Algebra.Etale L (MonoidAlgebra L C) :=
      MonoidAlgebra.etale_of_isUnit_card L C (by
        simpa only [map_natCast] using h.map (algebraMap k L))
    let _ : Algebra.Etale L (L ⊗[k] Q) := Algebra.Etale.of_equiv (A := MonoidAlgebra L C) e.symm
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L

/-- A homomorphism of multiplicative-type groups is a central isogeny with étale
kernel precisely when its geometric character map is injective and its cokernel
has order invertible in the ground field. -/
theorem isCentralIsogeny_and_etale_kernelCoordinate_iff :
    (CommHopfAlgCat.IsCentralIsogeny f ∧
      Algebra.Etale k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f))) ↔
      Function.Injective (CommHopfAlgCat.geometricCharacterMap f) ∧
        IsUnit (Nat.card (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
          (CommHopfAlgCat.geometricCharacterMap f).range) : k) := by
  rw [isCentralIsogeny_iff_geometricCharacterMap_injective_and_finite_quotient hH hK f,
    etale_kernelCoordinate_iff_isUnit_card hH hK f]
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
  apply Nat.finite_of_card_ne_zero
  intro hz
  simpa [hz] using h.2

end TauCeti.multiplicativeTypeCommHopfAlgProperty
