/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Detecting subcomodules on geometric points

Let `C` be a reduced commutative algebra of finite type over a field `k`, equipped with a
coalgebra structure, and let `M` be a right `C`-comodule. A `k`-submodule `N` of `M` is a
subcomodule if its scalar extension is
preserved by every point of `C` valued in an algebraically closed extension of `k`.

The substantive direction is descent from pointwise stability. For `m ∈ N`, apply the quotient
map `M ⟶ M/N` to `coact m`. Every coordinate of the resulting tensor vanishes at every
geometric point, because the corresponding point action preserves the scalar extension of `N`.
Reduced finite-type point separation makes every coordinate zero. Right exactness of tensor
product then identifies `coact m` with a tensor in `N ⊗ C`.

## Main declarations

* `Submodule.coact_mem_range_of_forall_endOfPoint_tmul_mem_baseChange`: pointwise
  stability implies the tensor-product stability condition defining a subcomodule.
* `TauCeti.Subcomodule.ofEndOfPointStable`: promote a point-stable submodule to a subcomodule.
* `TauCeti.Subcomodule.endOfPoint_mapsTo_baseChange`: every algebra-valued point preserves
  the scalar extension of a subcomodule.
* `TauCeti.Subcomodule.lid_rTensor_endOfPoint_mem`: contracting the action of an
  algebra-valued point against a linear functional preserves every subcomodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.2.

This supplies the point-separation step in Layer 6 of the ReductiveGroups roadmap: for a normal
closed subgroup, pointwise normality makes its fixed subspace stable under the ambient group, and
the result here promotes that stable subspace to an ambient-group subcomodule.
-/

public section

open scoped TensorProduct

universe u v w x

noncomputable section

namespace Submodule

open TauCeti

variable {k : Type u} {C : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing C] [Algebra k C] [Coalgebra k C]
variable [Algebra.FiniteType k C] [IsReduced C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- If every geometric point preserves the scalar extension of a submodule, the coaction of
each element of that submodule belongs to its tensor product with the coefficient coalgebra.

It is enough to test the pure tensors `1 ⊗ m`: the point action is linear over the value field,
so this is equivalent to preservation of the whole scalar-extended submodule. -/
theorem coact_mem_range_of_forall_endOfPoint_tmul_mem_baseChange
    (N : Submodule k M)
    (hN : ∀ (g : C →ₐ[k] K) {m : M}, m ∈ N →
      Comodule.endOfPoint M g (1 ⊗ₜ[k] m) ∈ N.baseChange K)
    {m : M} (hm : m ∈ N) :
    Comodule.coact (R := k) (C := C) (M := M) m ∈
      LinearMap.range (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[k] C)) := by
  rw [N.coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
  intro ψ
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
  intro g
  rw [map_zero]
  exact N.apply_matrixCoefficient_comp_mkQ_eq_zero_of_endOfPoint_mem_baseChange g (hN g hm) ψ

end Submodule

namespace TauCeti

namespace Subcomodule

section Preservation

variable {R : Type u} {C : Type v} {M : Type w} {A : Type x}
variable [CommSemiring R] [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [CommSemiring A] [Algebra R A]

/-- Every algebra-valued point preserves the scalar extension of a subcomodule. -/
theorem endOfPoint_tmul_mem_baseChange (N : Subcomodule R C M) (g : C →ₐ[R] A)
    (a : A) {m : M} (hm : m ∈ N) :
    Comodule.endOfPoint M g (a ⊗ₜ[R] m) ∈ N.toSubmodule.baseChange A := by
  have hmap (t : N.toSubmodule ⊗[R] C) :
      a • TensorProduct.comm R M A
          (LinearMap.lTensor M g.toLinearMap
            (TensorProduct.map N.toSubmodule.subtype LinearMap.id t)) ∈
        N.toSubmodule.baseChange A := by
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => simpa only [map_add, smul_add] using add_mem hs ht
    | tmul n c =>
        simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_coe, id_eq,
          LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem _ n.2
  obtain ⟨t, ht⟩ := N.coact_mem hm
  rw [Comodule.endOfPoint_tmul, ← ht]
  exact hmap t

/-- Every algebra-valued point maps the scalar extension of a subcomodule into itself. -/
theorem endOfPoint_mapsTo_baseChange (N : Subcomodule R C M) (g : C →ₐ[R] A) :
    Set.MapsTo (Comodule.endOfPoint M g) (N.toSubmodule.baseChange A)
      (N.toSubmodule.baseChange A) := by
  intro x hx
  rw [Submodule.baseChange] at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.inductionOn with
  | add s t hs ht =>
      rw [map_add, map_add]
      exact (N.toSubmodule.baseChange A).add_mem hs ht
  | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      exact N.endOfPoint_tmul_mem_baseChange g a m.2

/-- Contracting the action of an algebra-valued point against a linear functional on the value
algebra preserves every subcomodule. -/
theorem lid_rTensor_endOfPoint_mem (N : Subcomodule R C M) (g : C →ₐ[R] A) (ψ : A →ₗ[R] R)
    {m : M} (hm : m ∈ N) :
    TensorProduct.lid R M (LinearMap.rTensor M ψ (Comodule.endOfPoint M g (1 ⊗ₜ m))) ∈ N := by
  have key (x : M ⊗[R] C) :
      TensorProduct.lid R M (LinearMap.rTensor M ψ
        (TensorProduct.comm R M A (LinearMap.lTensor M g.toLinearMap x))) =
      TensorProduct.rid R M (LinearMap.lTensor M (ψ ∘ₗ g.toLinearMap) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul p h => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Comodule.endOfPoint_tmul, one_smul, key]
  exact N.rid_lTensor_coact_mem _ hm

end Preservation

variable {k : Type u} {C : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing C] [Algebra k C] [Coalgebra k C]
variable [Algebra.FiniteType k C] [IsReduced C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- Promote a submodule whose scalar extension is preserved by every geometric point to a
subcomodule. -/
def ofEndOfPointStable (N : Submodule k M)
    (hN : ∀ (g : C →ₐ[k] K) {m : M}, m ∈ N →
      Comodule.endOfPoint M g (1 ⊗ₜ[k] m) ∈ N.baseChange K) :
    Subcomodule k C M :=
  ofSubmodule N
    (fun _ hm ↦
      Submodule.coact_mem_range_of_forall_endOfPoint_tmul_mem_baseChange N hN hm)

/-- The point-stable subcomodule has the prescribed underlying submodule. -/
@[simp]
theorem ofEndOfPointStable_toSubmodule (N : Submodule k M)
    (hN : ∀ (g : C →ₐ[k] K) {m : M}, m ∈ N →
      Comodule.endOfPoint M g (1 ⊗ₜ[k] m) ∈ N.baseChange K) :
    (ofEndOfPointStable N hN).toSubmodule = N :=
  (rfl)

end Subcomodule

end TauCeti

end
