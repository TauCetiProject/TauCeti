/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.TwoStrand
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Symmetric
public import TauCeti.LinearAlgebra.Trace.Exact

import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic.FinCases
import TauCeti.Data.Fin.Basic

/-!
# Decomposing a tensor square

When `2` is invertible, the tensor square of a module is the direct sum of its symmetric and
alternating parts. This file constructs the natural equivalence

`⨂[R]^2 M ≃ₗ[R] Sym[R]^2 M × ⋀[R]^2 M`

using the half-symmetrizer and half-antisymmetrizer. No freeness or finite-generation hypothesis
is needed. Before that splitting, it proves the characteristic-free exactness of
`⋀²M → M ⊗ M → Sym²M` and the resulting trace sum and difference identities for finite free
modules over any commutative ring.

It then transfers the decomposition to the **binary** tensor square `M ⊗[R] M`, where the two
summands are the eigenspaces `TauCeti.symmetricTensors` and `TauCeti.antisymmetricTensors` of the
flip `x ⊗ₜ y ↦ y ⊗ₜ x`. The bridge is
`TauCeti.tensorProductEquivTensorSquare : M ⊗[R] M ≃ₗ[R] ⨂[R]^2 M`, which carries the flip to
`TauCeti.tensorSwap`; the two embeddings above have images the `+1`- and `-1`-eigenspaces, so the
eigenspaces *are* `Sym[R]^2 M` and `⋀[R]^2 M`, canonically and `f ⊗ f`-equivariantly. The
eigenspace presentation is the one a topological or analytic development has to use — a submodule
of `M ⊗[R] M` carries a topology where a quotient of a `PiTensorProduct` carries none — so these
comparisons are what let a statement proved there be read as a statement about `Sym²` and `⋀²`.

## Main definitions

* `TauCeti.tensorSwap` exchanges the two factors of a tensor square; it needs no hypothesis on
  `2`, and is what the two orders on a tensor square are compared by.
* `TauCeti.tensorProductEquivTensorSquare` identifies the binary tensor square `M ⊗[R] M` with
  the second tensor power `⨂[R]^2 M`.
* `SymmetricPower.toTensorSquare` embeds a symmetric square by averaging the two orders.
* `exteriorPower.toTensorSquare` embeds an exterior square by alternating the two orders.
* `TauCeti.tensorSquareEquivSymmetricExterior` is the resulting direct-sum decomposition.
* `TauCeti.symmetricTensorsEquivSymmetricPower` and
  `TauCeti.antisymmetricTensorsEquivExteriorPower` identify the two flip eigenspaces of
  `M ⊗[R] M` with `Sym[R]^2 M` and `⋀[R]^2 M`.

## Main results

* `exteriorPower.range_toTensorPower_two_eq_ker_symmetricPower_mk`: antisymmetrization and
  the symmetric quotient are exact without an assumption on `2`.
* `exteriorPower.exact_toTensorPower_two_symmetricPower_mk`: the same exactness in the
  `Function.Exact` API.
* `LinearMap.trace_piTensorProduct_map_two` and
  `LinearMap.trace_symmetricPower_sub_trace_exteriorPower`: the trace sum and difference
  identities on the symmetric and exterior squares of a finite free module over a
  commutative ring, valid in every characteristic.
* `LinearMap.trace_piTensorProduct_map_comp_tensorSwap`: the trace of the diagonal action
  composed with the swap is the trace of the square of the endomorphism.
* `TauCeti.tensorProductEquivTensorSquare_comm` and
  `TauCeti.tensorProductEquivTensorSquare_comp_map`: the bridge carries the flip to the swap and
  `f ⊗ f` to the diagonal `PiTensorProduct.map`.
* `SymmetricPower.toTensorSquare_comp_mk` and
  `exteriorPower.toTensorSquare_comp_lift_ιMulti`: the two embeddings compose with their
  projections to the symmetrizer `⅟2 • (1 + swap)` and the antisymmetrizer `⅟2 • (1 - swap)`.
* `LinearMap.symmetricTensorsEquivSymmetricPower_symmetricTensorsRestrict` and
  `LinearMap.antisymmetricTensorsEquivExteriorPower_antisymmetricTensorsRestrict`: both
  comparisons turn the restriction of `f ⊗ f` into `SymmetricPower.map f` and
  `exteriorPower.map 2 f`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
* Mathlib's `SymmetricPower` quotient API, by Kenny Lau.
* Mathlib's `exteriorPower` universal-property API, by Sophie Morel and Joël Riou.
-/

public section

open scoped TensorProduct

universe v w

variable (R : Type) (M : Type v)

namespace TauCeti

section Swap

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The swap of the two factors of a tensor square, `x ⊗ₜ y ↦ y ⊗ₜ x`. -/
noncomputable def tensorSwap : (⨂[R]^2 M) ≃ₗ[R] ⨂[R]^2 M :=
  PiTensorProduct.reindex R (fun _ : Fin 2 ↦ M) (Equiv.swap 0 1)

/-- The swap reads a pure tensor in the other order. -/
@[simp]
theorem tensorSwap_tprod (f : Fin 2 → M) :
    tensorSwap R M (PiTensorProduct.tprod R f) =
      PiTensorProduct.tprod R fun i ↦ f (Equiv.swap 0 1 i) := by
  rw [tensorSwap, PiTensorProduct.reindex_tprod, Equiv.symm_swap]

/-- The swap is its own inverse. -/
@[simp]
theorem tensorSwap_symm : (tensorSwap R M).symm = tensorSwap R M := by
  rw [tensorSwap, PiTensorProduct.reindex_symm, Equiv.symm_swap]

/-- Swapping the two factors of an arbitrary tensor twice is the identity. -/
@[simp]
theorem tensorSwap_tensorSwap (x : ⨂[R]^2 M) :
    tensorSwap R M (tensorSwap R M x) = x := by
  have h := (tensorSwap R M).symm_apply_apply x
  rwa [tensorSwap_symm] at h

/-- The second tensor power is the binary tensor square: both are the universal target of a
bilinear map out of `M × M`, and the equivalence matches `x ⊗ₜ y` with `x ⊗ y`. The characterising
value is `TauCeti.tensorProductEquivTensorSquare_tmul`. -/
noncomputable def tensorProductEquivTensorSquare : M ⊗[R] M ≃ₗ[R] ⨂[R]^2 M :=
  (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0).symm
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0).symm).trans
    TensorPower.mulEquiv

/-- The comparison with the second tensor power sends `x ⊗ₜ y` to the pure tensor `x ⊗ y`. -/
@[simp]
theorem tensorProductEquivTensorSquare_tmul (x y : M) :
    tensorProductEquivTensorSquare R M (x ⊗ₜ[R] y) = PiTensorProduct.tprod R ![x, y] := by
  rw [tensorProductEquivTensorSquare]
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    PiTensorProduct.subsingletonEquiv_symm_apply', TensorPower.mulEquiv,
    PiTensorProduct.tmulEquiv_apply, PiTensorProduct.reindex_tprod]
  refine congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_)
  -- Both index values of `Fin 2` are checked separately against `finSumFinEquiv.symm`.
  fin_cases i <;> rfl

/-- The inverse comparison reads a pure tensor as the product of its two entries. -/
@[simp]
theorem tensorProductEquivTensorSquare_symm_tprod (f : Fin 2 → M) :
    (tensorProductEquivTensorSquare R M).symm (PiTensorProduct.tprod R f) =
      f 0 ⊗ₜ[R] f 1 := by
  rw [LinearEquiv.symm_apply_eq, tensorProductEquivTensorSquare_tmul]
  exact tprod_fin_two f

/-- **The comparison turns the flip into the swap**: the flip `x ⊗ₜ y ↦ y ⊗ₜ x` of the binary
tensor square is `TauCeti.tensorSwap` read through
`TauCeti.tensorProductEquivTensorSquare`. -/
theorem tensorProductEquivTensorSquare_comp_comm :
    (tensorProductEquivTensorSquare R M).toLinearMap ∘ₗ
        (TensorProduct.comm R M M).toLinearMap =
      (tensorSwap R M).toLinearMap ∘ₗ (tensorProductEquivTensorSquare R M).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    tensorProductEquivTensorSquare_tmul, tensorSwap_tprod]
  refine congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_)
  fin_cases i <;> rfl

/-- The flip of the binary tensor square agrees with the swap of the second tensor power. -/
@[simp]
theorem tensorProductEquivTensorSquare_comm (x : M ⊗[R] M) :
    tensorProductEquivTensorSquare R M (TensorProduct.comm R M M x) =
      tensorSwap R M (tensorProductEquivTensorSquare R M x) :=
  DFunLike.congr_fun (tensorProductEquivTensorSquare_comp_comm R M) x

/-- **The comparison is natural in the module**: `f ⊗ f` on the binary tensor square is the
diagonal `PiTensorProduct.map` on the second tensor power. -/
theorem tensorProductEquivTensorSquare_comp_map {N : Type w} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    (tensorProductEquivTensorSquare R N).toLinearMap ∘ₗ TensorProduct.map f f =
      (PiTensorProduct.map fun _ : Fin 2 ↦ f) ∘ₗ
        (tensorProductEquivTensorSquare R M).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    tensorProductEquivTensorSquare_tmul, PiTensorProduct.map_tprod]
  refine congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_)
  fin_cases i <;> rfl

end Swap

end TauCeti


namespace exteriorPower

/-- Antisymmetrizing a pure exterior square is the difference of its two tensor orders. -/
@[simp high]
theorem toTensorPower_ιMulti_two {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (f : Fin 2 → M) :
    exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 f) =
      PiTensorProduct.tprod R f -
        PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i)) := by
  classical
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact TauCeti.perm_fin_two_eq_one_or_swap e
  rw [exteriorPower.toTensorPower_apply_ιMulti, hperm,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [sub_eq_add_neg]

end exteriorPower

namespace SymmetricPower

/-- The symmetric quotient kills antisymmetrization of an exterior square. -/
theorem mk_comp_exteriorPower_toTensorPower {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] : (SymmetricPower.mk R (Fin 2) M).comp
      (exteriorPower.toTensorPower R M 2) = 0 := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  -- `SymmetricPower.tprod` is `SymmetricPower.mk` of a pure tensor power, so `tprod_equiv`
  -- says the two orders have the same symmetric class once that definition is unfolded.
  have hswap : SymmetricPower.mk R (Fin 2) M (PiTensorProduct.tprod R f) =
      SymmetricPower.mk R (Fin 2) M
        (PiTensorProduct.tprod R fun i ↦ f (Equiv.swap 0 1 i)) := by
    simpa only [SymmetricPower.tprod, LinearMap.compMultilinearMap_apply] using
      (SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) f).symm
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorPower_ιMulti_two, map_sub, hswap, sub_self]
  simp

/-- The symmetric quotient kills every antisymmetrized exterior square. -/
@[simp]
theorem mk_exteriorPower_toTensorPower {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (x : ⋀[R]^2 M) :
    mk R (Fin 2) M (exteriorPower.toTensorPower R M 2 x) = 0 := by
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (mk_comp_exteriorPower_toTensorPower (R := R) (M := M)) x

end SymmetricPower

namespace TauCeti.TensorSquare

private theorem symToAlternatingQuotient_rel {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    addConGen (SymmetricPower.Rel R (Fin 2) M) ≤
      AddCon.ker (Submodule.mkQ (LinearMap.range
        (exteriorPower.toTensorPower R M 2))).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e f =>
    apply (AddCon.ker_rel _).2
    apply (Submodule.Quotient.eq _).2
    rcases TauCeti.perm_fin_two_eq_one_or_swap e with rfl | rfl
    · simp
    · exact ⟨exteriorPower.ιMulti R 2 f, exteriorPower.toTensorPower_ιMulti_two f⟩

/-- The symmetric-square map to the quotient of the tensor square by alternating tensors. -/
private noncomputable def symToAlternatingQuotient {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    Sym[R]^2 M →ₗ[R]
      (⨂[R]^2 M) ⧸ LinearMap.range (exteriorPower.toTensorPower R M 2) where
  toFun :=
    (addConGen (SymmetricPower.Rel R (Fin 2) M)).lift
      (LinearMap.toAddMonoidHom
        (Submodule.mkQ (LinearMap.range (exteriorPower.toTensorPower R M 2))))
      symToAlternatingQuotient_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x ↦ by
    exact congrArg
      (Submodule.Quotient.mk
        (p := LinearMap.range (exteriorPower.toTensorPower R M 2)))
      ((LinearMap.id.map_smul r x))

private theorem symToAlternatingQuotient_mk {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (x : ⨂[R]^2 M) :
    symToAlternatingQuotient (R := R) (M := M)
        (SymmetricPower.mk R (Fin 2) M x) =
      Submodule.Quotient.mk x := by
  -- `SymmetricPower.mk` and the linear lift wrap the two additive quotient maps, so their
  -- computation is `AddCon.lift_mk'`, followed by the submodule quotient's computation law.
  exact (AddCon.lift_mk' symToAlternatingQuotient_rel x).trans
    (Submodule.mkQ_apply _ x)

end TauCeti.TensorSquare

namespace exteriorPower

/-- Antisymmetrization and the symmetric quotient form the characteristic-free exact sequence
`⋀²M → M ⊗ M → Sym²M`. -/
theorem range_toTensorPower_two_eq_ker_symmetricPower_mk {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    LinearMap.range (exteriorPower.toTensorPower R M 2) =
      LinearMap.ker (SymmetricPower.mk R (Fin 2) M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact SymmetricPower.mk_exteriorPower_toTensorPower x
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (exteriorPower.toTensorPower R M 2))).mp
    rw [← TauCeti.TensorSquare.symToAlternatingQuotient_mk x, hx, map_zero]

/-- The antisymmetrization into the tensor square and its symmetric quotient are exact over
every commutative ring. -/
theorem exact_toTensorPower_two_symmetricPower_mk {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    Function.Exact (toTensorPower R M 2) (SymmetricPower.mk R (Fin 2) M) :=
  LinearMap.exact_iff.mpr range_toTensorPower_two_eq_ker_symmetricPower_mk.symm

end exteriorPower

namespace TauCeti

/-- The swap acts as `-1` on the alternating part: it exchanges the two pure tensors whose
difference is the image of a wedge. -/
theorem tensorSwap_comp_exteriorPower_toTensorPower {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] :
    (TauCeti.tensorSwap R M).toLinearMap.comp (exteriorPower.toTensorPower R M 2)
      = -exteriorPower.toTensorPower R M 2 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearEquiv.coe_coe]
  rw [exteriorPower.toTensorPower_ιMulti_two, map_sub, tensorSwap_tprod, tensorSwap_tprod]
  simp only [Equiv.swap_apply_self, neg_sub]

/-- Swapping an antisymmetrized exterior square negates it. -/
@[simp]
theorem tensorSwap_exteriorPower_toTensorPower {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (x : ⋀[R]^2 M) :
    tensorSwap R M (exteriorPower.toTensorPower R M 2 x) =
      -exteriorPower.toTensorPower R M 2 x := by
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearEquiv.coe_coe] using
    LinearMap.congr_fun (tensorSwap_comp_exteriorPower_toTensorPower (R := R) (M := M)) x

end TauCeti

namespace SymmetricPower

/-- The swap acts as `+1` on the symmetric part: that is exactly the relation defining `Sym²`. -/
theorem mk_comp_tensorSwap {R : Type} {M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (SymmetricPower.mk R (Fin 2) M).comp (TauCeti.tensorSwap R M).toLinearMap
      = SymmetricPower.mk R (Fin 2) M := by
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TauCeti.tensorSwap_tprod]
  simpa only [SymmetricPower.tprod, LinearMap.compMultilinearMap_apply] using
    SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) v

/-- Swapping any tensor square preserves its symmetric class. -/
@[simp]
theorem mk_tensorSwap {R : Type} {M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (x : ⨂[R]^2 M) :
    mk R (Fin 2) M (TauCeti.tensorSwap R M x) = mk R (Fin 2) M x := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    LinearMap.congr_fun (mk_comp_tensorSwap (R := R) (M := M)) x

end SymmetricPower

namespace LinearMap

/-- The trace of the diagonal tensor-square map composed with the swap is the trace of
the square of the endomorphism. -/
theorem trace_piTensorProduct_map_comp_tensorSwap {R : Type} {M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    trace R (⨂[R]^2 M)
        ((PiTensorProduct.map fun _ : Fin 2 ↦ f) ∘ₗ (TauCeti.tensorSwap R M).toLinearMap)
      = trace R M (f ∘ₗ f) := by
  classical
  let b := Module.Free.chooseBasis R M
  let B := Basis.piTensorProduct fun _ : Fin 2 ↦ b
  refine b.trace_eq_trace_comp_self_of_toMatrix_diag B
    (finTwoArrowEquiv _) f _ fun p ↦ ?_
  simp [B, Module.Basis.toMatrix_apply, Basis.piTensorProduct_apply,
    TauCeti.tensorSwap_tprod, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply, Fin.prod_univ_two]

/-- The trace of the diagonal tensor-square map of a finite free module over a commutative
ring is the sum of the traces on its symmetric and exterior squares. -/
theorem trace_piTensorProduct_map_two {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    trace R (⨂[R]^2 M) (PiTensorProduct.map fun _ : Fin 2 ↦ f) =
      trace R (Sym[R]^2 M) (SymmetricPower.map (ι := Fin 2) f) +
        trace R (⋀[R]^2 M) (exteriorPower.map 2 f) := by
  have hq : (SymmetricPower.mk R (Fin 2) M) ∘ₗ (PiTensorProduct.map fun _ : Fin 2 ↦ f)
      = (SymmetricPower.map (ι := Fin 2) f) ∘ₗ (SymmetricPower.mk R (Fin 2) M) :=
    LinearMap.ext fun x ↦ (SymmetricPower.map_mk f x).symm
  have h := trace_eq_add_of_exact
    exteriorPower.toTensorPower_injective_of_free
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk R (Fin 2) M))
    exteriorPower.exact_toTensorPower_two_symmetricPower_mk
    (exteriorPower.toTensorPower_comp_map 2 f).symm hq
  simpa only [add_comm] using h

/-- **The trace form of the two square characters.** For a finite free module over a
commutative ring, the traces of an endomorphism on the symmetric and exterior squares differ
by the trace of its own square. -/
theorem trace_symmetricPower_sub_trace_exteriorPower {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    LinearMap.trace R (Sym[R]^2 M) (SymmetricPower.map (ι := Fin 2) f)
        - LinearMap.trace R (⋀[R]^2 M) (exteriorPower.map 2 f)
      = LinearMap.trace R M (f.comp f) := by
  -- Read the exact sequence `⋀²M → M ⊗ M → Sym²M` against `(f ⊗ f) ∘ swap`, which covers
  -- `-⋀²f` on the alternating part and `Sym²f` on the symmetric quotient.
  have hfi :
      ((PiTensorProduct.map fun _ : Fin 2 ↦ f).comp
            (TauCeti.tensorSwap R M).toLinearMap).comp (exteriorPower.toTensorPower R M 2)
        = (exteriorPower.toTensorPower R M 2).comp (-exteriorPower.map 2 f) := by
    rw [LinearMap.comp_assoc, TauCeti.tensorSwap_comp_exteriorPower_toTensorPower,
      LinearMap.comp_neg, LinearMap.comp_neg,
      ← exteriorPower.toTensorPower_comp_map 2 f]
  have hfq :
      (SymmetricPower.mk R (Fin 2) M).comp
          ((PiTensorProduct.map fun _ : Fin 2 ↦ f).comp (TauCeti.tensorSwap R M).toLinearMap)
        = (SymmetricPower.map (ι := Fin 2) f).comp (SymmetricPower.mk R (Fin 2) M) := by
    exact LinearMap.ext fun x ↦ by simp [← SymmetricPower.map_mk]
  have h := LinearMap.trace_eq_add_of_exact
    exteriorPower.toTensorPower_injective_of_free
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk R (Fin 2) M))
    exteriorPower.exact_toTensorPower_two_symmetricPower_mk
    hfi hfq
  have hneg : LinearMap.trace R (⋀[R]^2 M) (-exteriorPower.map 2 f)
      = -LinearMap.trace R (⋀[R]^2 M) (exteriorPower.map 2 f) :=
    map_neg (LinearMap.trace R (⋀[R]^2 M)) (exteriorPower.map 2 f)
  rw [trace_piTensorProduct_map_comp_tensorSwap, hneg] at h
  rw [h]
  ring

end LinearMap

variable [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

namespace TauCeti

/-- Projection onto the symmetric part of a tensor square. -/
private noncomputable def symmetricProjection : (⨂[R]^2 M) →ₗ[R] ⨂[R]^2 M :=
  (⅟ (2 : R)) • (LinearMap.id + (tensorSwap R M).toLinearMap)

private theorem symmetricProjection_rel :
    addConGen (SymmetricPower.Rel R (Fin 2) M) ≤
      AddCon.ker (symmetricProjection R M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e f =>
      apply (AddCon.ker_rel _).2
      rcases perm_fin_two_eq_one_or_swap e with rfl | rfl
      · rfl
      · change symmetricProjection R M (PiTensorProduct.tprod R f) =
          symmetricProjection R M
            (PiTensorProduct.tprod R fun i ↦ f (Equiv.swap 0 1 i))
        -- Unfold the quotient relation to the corresponding equality of pure tensor powers.
        simp [symmetricProjection, tensorSwap, Equiv.symm_swap, add_comm]

end TauCeti

namespace SymmetricPower

/-- The embedding of the symmetric square in the tensor square, given on a pure symmetric
tensor by `x ⊗ₛ y ↦ ⅟2 • (x ⊗ₜ y + y ⊗ₜ x)`. -/
noncomputable def toTensorSquare : Sym[R]^2 M →ₗ[R] ⨂[R]^2 M where
  toFun :=
    (addConGen (Rel R (Fin 2) M)).lift
      (TauCeti.symmetricProjection R M).toAddMonoidHom
      (TauCeti.symmetricProjection_rel R M)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x ↦ by
    exact (TauCeti.symmetricProjection R M).map_smul r x

/-- The symmetric-square embedding is the half-sum of the two orders on pure tensors. -/
@[simp]
theorem toTensorSquare_tprod (f : Fin 2 → M) :
    toTensorSquare R M (⨂ₛ[R] i, f i) =
      (⅟ (2 : R)) •
        (PiTensorProduct.tprod R f +
          PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i))) := by
  change TauCeti.symmetricProjection R M (PiTensorProduct.tprod R f) = _
  simp [TauCeti.symmetricProjection, TauCeti.tensorSwap]

end SymmetricPower

namespace exteriorPower

/-- The embedding of the exterior square in the tensor square, given on a pure wedge by
`x ∧ y ↦ ⅟2 • (x ⊗ₜ y - y ⊗ₜ x)`. -/
noncomputable def toTensorSquare : ⋀[R]^2 M →ₗ[R] ⨂[R]^2 M :=
  (⅟ (2 : R)) • exteriorPower.toTensorPower R M 2

/-- The exterior-square embedding is the half-difference of the two orders on pure wedges. -/
@[simp]
theorem toTensorSquare_ιMulti (f : Fin 2 → M) :
    toTensorSquare R M (ιMulti R 2 f) =
      (⅟ (2 : R)) •
        (PiTensorProduct.tprod R f -
          PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i))) := by
  rw [toTensorSquare, LinearMap.smul_apply, toTensorPower_ιMulti_two]

end exteriorPower

namespace TauCeti

/-- The comparison map from a tensor square to its symmetric and exterior square quotients. -/
private noncomputable def tensorSquareToSymmetricExterior :
    (⨂[R]^2 M) →ₗ[R] (Sym[R]^2 M) × (⋀[R]^2 M) :=
  (SymmetricPower.mk R (Fin 2) M).prod
    (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap)

/-- The sum of the canonical maps from the symmetric and exterior squares into the tensor square. -/
private noncomputable def symmetricExteriorToTensorSquare :
    (Sym[R]^2 M) × (⋀[R]^2 M) →ₗ[R] ⨂[R]^2 M :=
  (SymmetricPower.toTensorSquare R M).coprod
    (exteriorPower.toTensorSquare R M)

end TauCeti

namespace SymmetricPower

/-- The symmetric quotient composed with the symmetric-square embedding is the identity. -/
theorem mk_comp_toTensorSquare : (SymmetricPower.mk R (Fin 2) M).comp
        (SymmetricPower.toTensorSquare R M) = LinearMap.id := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := Fin 2) (M := M))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, SymmetricPower.toTensorSquare_tprod, map_smul, map_add]
  -- `SymmetricPower.mk` sends each tensor-power generator to its symmetric class.
  change (⅟ (2 : R)) • (⨂ₛ[R] i, f i) +
    (⅟ (2 : R)) • (⨂ₛ[R] i, f (Equiv.swap 0 1 i)) = ⨂ₛ[R] i, f i
  rw [SymmetricPower.tprod_equiv (Equiv.swap 0 1) f, ← add_smul,
    invOf_two_add_invOf_two, one_smul]

/-- Projecting the symmetric-square embedding back to the symmetric square is the identity. -/
@[simp]
theorem mk_toTensorSquare (x : Sym[R]^2M) :
    mk R (Fin 2) M (toTensorSquare R M x) = x :=
  DFunLike.congr_fun (mk_comp_toTensorSquare R M) x

/-- The map from the symmetric square to the tensor square is injective. -/
theorem toTensorSquare_injective :
    Function.Injective (toTensorSquare R M) := by
  intro x y h
  rw [← mk_toTensorSquare R M x, ← mk_toTensorSquare R M y, h]

end SymmetricPower

namespace exteriorPower

/-- The exterior projection vanishes on the symmetric-square embedding. -/
theorem lift_ιMulti_comp_symmetricPower_toTensorSquare : (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap).comp
        (SymmetricPower.toTensorSquare R M) = 0 := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := Fin 2) (M := M))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, SymmetricPower.toTensorSquare_tprod, map_smul,
    map_add, PiTensorProduct.lift.tprod, LinearMap.zero_apply]
  -- The lifted wedge projection evaluates on pure tensors as `exteriorPower.ιMulti`.
  change (⅟ (2 : R)) •
    ((exteriorPower.ιMulti R 2) f +
      (exteriorPower.ιMulti R 2) (f ∘ Equiv.swap 0 1)) = 0
  rw [(exteriorPower.ιMulti R 2).map_swap f (by decide)]
  simp

/-- The exterior projection of an element embedded from the symmetric square vanishes. -/
@[simp]
theorem lift_ιMulti_symmetricPower_toTensorSquare (x : Sym[R]^2M) :
    PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap
        (SymmetricPower.toTensorSquare R M x) = 0 :=
  DFunLike.congr_fun (lift_ιMulti_comp_symmetricPower_toTensorSquare R M) x

end exteriorPower

namespace SymmetricPower

/-- The symmetric projection vanishes on the exterior-square embedding. -/
theorem mk_comp_exteriorPower_toTensorSquare : (SymmetricPower.mk R (Fin 2) M).comp
        (exteriorPower.toTensorSquare R M) = 0 := by
  rw [exteriorPower.toTensorSquare, LinearMap.comp_smul,
    mk_comp_exteriorPower_toTensorPower, smul_zero]

/-- The symmetric projection of an element embedded from the exterior square vanishes. -/
@[simp]
theorem mk_exteriorPower_toTensorSquare (x : ⋀[R]^2 M) :
    mk R (Fin 2) M (exteriorPower.toTensorSquare R M x) = 0 :=
  DFunLike.congr_fun (mk_comp_exteriorPower_toTensorSquare R M) x

end SymmetricPower

namespace exteriorPower

/-- The exterior projection composed with the exterior-square embedding is the identity. -/
theorem lift_ιMulti_comp_toTensorSquare : (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap).comp
        (exteriorPower.toTensorSquare R M) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorSquare_ιMulti, map_smul, map_sub,
    PiTensorProduct.lift.tprod, LinearMap.id_apply]
  -- Expose the swapped family as precomposition so `AlternatingMap.map_swap` applies.
  rw [show (fun i ↦ f (Equiv.swap 0 1 i)) = f ∘ Equiv.swap 0 1 by rfl]
  have hswap :
      (exteriorPower.ιMulti R 2).toMultilinearMap
          (f ∘ Equiv.swap (0 : Fin 2) 1) =
        -(exteriorPower.ιMulti R 2).toMultilinearMap f :=
    (exteriorPower.ιMulti R 2).map_swap f (by decide)
  rw [hswap]
  simp

/-- Projecting the exterior-square embedding back to the exterior square is the identity. -/
@[simp]
theorem lift_ιMulti_toTensorSquare (x : ⋀[R]^2 M) :
    PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap
        (toTensorSquare R M x) = x :=
  DFunLike.congr_fun (lift_ιMulti_comp_toTensorSquare R M) x

/-- The map from the exterior square to the tensor square is injective. -/
theorem toTensorSquare_injective :
    Function.Injective (toTensorSquare R M) := by
  intro x y h
  rw [← lift_ιMulti_toTensorSquare R M x, ← lift_ιMulti_toTensorSquare R M y, h]

end exteriorPower

namespace TauCeti

private theorem symmetricExteriorToTensorSquare_comp : (symmetricExteriorToTensorSquare R M).comp
        (tensorSquareToSymmetricExterior R M) = LinearMap.id := by
  rw [symmetricExteriorToTensorSquare, tensorSquareToSymmetricExterior,
    LinearMap.coprod_comp_prod]
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.comp_apply, PiTensorProduct.lift.tprod,
    LinearMap.id_apply]
  -- The two components of the product map reduce to the symmetric class and wedge.
  change SymmetricPower.toTensorSquare R M (⨂ₛ[R] i, f i) +
      exteriorPower.toTensorSquare R M ((exteriorPower.ιMulti R 2) f) =
    PiTensorProduct.tprod R f
  rw [SymmetricPower.toTensorSquare_tprod, exteriorPower.toTensorSquare_ιMulti]
  rw [smul_add, smul_sub]
  abel_nf
  rw [two_smul, ← add_smul, invOf_two_add_invOf_two, one_smul]

private theorem tensorSquareToSymmetricExterior_comp : (tensorSquareToSymmetricExterior R M).comp
        (symmetricExteriorToTensorSquare R M) = LinearMap.id := by
  rw [tensorSquareToSymmetricExterior, symmetricExteriorToTensorSquare,
    LinearMap.prod_comp, LinearMap.comp_coprod, LinearMap.comp_coprod,
    SymmetricPower.mk_comp_toTensorSquare,
    exteriorPower.lift_ιMulti_comp_symmetricPower_toTensorSquare,
    SymmetricPower.mk_comp_exteriorPower_toTensorSquare,
    exteriorPower.lift_ιMulti_comp_toTensorSquare]
  rw [← LinearMap.fst_eq_coprod, ← LinearMap.snd_eq_coprod,
    LinearMap.pair_fst_snd]

/-- The tensor square is naturally the direct sum of its symmetric and exterior squares when
`2` is invertible. The forward map sends a tensor to its symmetric quotient and exterior
product. -/
noncomputable def tensorSquareEquivSymmetricExterior : (⨂[R]^2 M) ≃ₗ[R] (Sym[R]^2 M) × (⋀[R]^2 M) :=
  LinearEquiv.mk
    (tensorSquareToSymmetricExterior R M)
    (symmetricExteriorToTensorSquare R M)
    (fun x ↦ DFunLike.congr_fun (symmetricExteriorToTensorSquare_comp R M) x)
    (fun x ↦ DFunLike.congr_fun (tensorSquareToSymmetricExterior_comp R M) x)

/-- The tensor-square decomposition sends a pure tensor to its symmetric and exterior
classes. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_tprod (f : Fin 2 → M) :
    tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f) =
      (⨂ₛ[R] i, f i, exteriorPower.ιMulti R 2 f) := by
  simp [tensorSquareEquivSymmetricExterior, tensorSquareToSymmetricExterior]
  rfl

/-- The inverse tensor-square decomposition is the sum of the symmetric and exterior
embeddings. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_symm_apply (x : (Sym[R]^2M) × (⋀[R]^2 M)) :
    (tensorSquareEquivSymmetricExterior R M).symm x =
      SymmetricPower.toTensorSquare R M x.1 + exteriorPower.toTensorSquare R M x.2 := by
  rfl

end TauCeti

namespace TauCeti

/-! ### The flip eigenspaces of the binary tensor square

`TauCeti.symmetricTensors` and `TauCeti.antisymmetricTensors` are the `±1`-eigenspaces of the
flip on `M ⊗[R] M`. Through `TauCeti.tensorProductEquivTensorSquare` the flip is
`TauCeti.tensorSwap`, whose eigenspaces are the images of the two embeddings
`SymmetricPower.toTensorSquare` and `exteriorPower.toTensorSquare`; so the two eigenspaces *are*
`Sym[R]^2 M` and `⋀[R]^2 M`, and not merely modules of the same rank. -/

/-- The swap fixes the symmetric-square embedding. -/
theorem tensorSwap_comp_symmetricPower_toTensorSquare :
    (tensorSwap R M).toLinearMap ∘ₗ SymmetricPower.toTensorSquare R M =
      SymmetricPower.toTensorSquare R M := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := Fin 2) (M := M))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, SymmetricPower.toTensorSquare_tprod,
    map_smul, map_add, tensorSwap_tprod, Equiv.swap_apply_self]
  rw [add_comm]

/-- The swap negates the exterior-square embedding. -/
theorem tensorSwap_comp_exteriorPower_toTensorSquare :
    (tensorSwap R M).toLinearMap ∘ₗ exteriorPower.toTensorSquare R M =
      -exteriorPower.toTensorSquare R M := by
  rw [exteriorPower.toTensorSquare, LinearMap.comp_smul,
    tensorSwap_comp_exteriorPower_toTensorPower, smul_neg]

end TauCeti

namespace SymmetricPower

/-- **The symmetric embedding is the symmetrizer**: composing the symmetric quotient with the
symmetric-square embedding is `⅟2 • (1 + swap)`. -/
theorem toTensorSquare_comp_mk :
    toTensorSquare R M ∘ₗ mk R (Fin 2) M =
      ⅟(2 : R) • (LinearMap.id + (TauCeti.tensorSwap R M).toLinearMap) := by
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
  rintro _ ⟨f, rfl⟩
  have hmk : mk R (Fin 2) M (PiTensorProduct.tprod R f) = ⨂ₛ[R] i, f i := rfl
  simp only [LinearMap.comp_apply, hmk, toTensorSquare_tprod,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    TauCeti.tensorSwap_tprod]

end SymmetricPower

namespace exteriorPower

/-- **The exterior embedding is the antisymmetrizer**: composing the exterior projection with the
exterior-square embedding is `⅟2 • (1 - swap)`. -/
theorem toTensorSquare_comp_lift_ιMulti :
    toTensorSquare R M ∘ₗ
        PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap =
      ⅟(2 : R) • (LinearMap.id - (TauCeti.tensorSwap R M).toLinearMap) := by
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, PiTensorProduct.lift.tprod,
    AlternatingMap.coe_multilinearMap, toTensorSquare_ιMulti,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    TauCeti.tensorSwap_tprod]

end exteriorPower

namespace TauCeti

/-- A swap-invariant tensor is recovered from its symmetric class. -/
theorem symmetricPower_toTensorSquare_mk_of_tensorSwap_eq {y : ⨂[R]^2 M}
    (hy : tensorSwap R M y = y) :
    SymmetricPower.toTensorSquare R M (SymmetricPower.mk R (Fin 2) M y) = y := by
  have h := DFunLike.congr_fun (SymmetricPower.toTensorSquare_comp_mk R M) y
  rw [LinearMap.comp_apply] at h
  rw [h]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    hy]
  rw [← two_smul R y, invOf_smul_smul]

/-- A swap-anti-invariant tensor is recovered from its wedge. -/
theorem exteriorPower_toTensorSquare_lift_ιMulti_of_tensorSwap_eq_neg {y : ⨂[R]^2 M}
    (hy : tensorSwap R M y = -y) :
    exteriorPower.toTensorSquare R M
        (PiTensorProduct.lift (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap y) = y := by
  have h := DFunLike.congr_fun (exteriorPower.toTensorSquare_comp_lift_ιMulti R M) y
  rw [LinearMap.comp_apply] at h
  rw [h]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    hy, sub_neg_eq_add]
  rw [← two_smul R y, invOf_smul_smul]

/-- The symmetric-square embedding lands in the symmetric tensors. -/
theorem tensorProductEquivTensorSquare_symm_symmetricPower_toTensorSquare_mem_symmetricTensors
    (x : Sym[R]^2M) :
    (tensorProductEquivTensorSquare R M).symm (SymmetricPower.toTensorSquare R M x) ∈
      symmetricTensors R M := by
  have hswap : tensorSwap R M (SymmetricPower.toTensorSquare R M x) =
      SymmetricPower.toTensorSquare R M x := by
    simpa using DFunLike.congr_fun (tensorSwap_comp_symmetricPower_toTensorSquare R M) x
  rw [mem_symmetricTensors]
  refine (tensorProductEquivTensorSquare R M).injective ?_
  rw [tensorProductEquivTensorSquare_comm, LinearEquiv.apply_symm_apply, hswap]

/-- The exterior-square embedding lands in the antisymmetric tensors. -/
theorem tensorProductEquivTensorSquare_symm_exteriorPower_toTensorSquare_mem_antisymmetricTensors
    (x : ⋀[R]^2 M) :
    (tensorProductEquivTensorSquare R M).symm (exteriorPower.toTensorSquare R M x) ∈
      antisymmetricTensors R M := by
  have hswap : tensorSwap R M (exteriorPower.toTensorSquare R M x) =
      -exteriorPower.toTensorSquare R M x := by
    simpa using DFunLike.congr_fun (tensorSwap_comp_exteriorPower_toTensorSquare R M) x
  rw [mem_antisymmetricTensors]
  refine (tensorProductEquivTensorSquare R M).injective ?_
  rw [map_neg, tensorProductEquivTensorSquare_comm, LinearEquiv.apply_symm_apply, hswap]

/-- **The symmetric tensors are the symmetric square.** The flip-fixed submodule of `M ⊗[R] M`
is `Sym[R]^2 M`, by the symmetric quotient read through
`TauCeti.tensorProductEquivTensorSquare`; the inverse is the symmetrizer
`x ⊗ₛ y ↦ ⅟2 • (x ⊗ₜ y + y ⊗ₜ x)`. This is what justifies calling
`TauCeti.symmetricTensors` a symmetric square: the two modules are not merely of the same
rank, they are canonically the same. -/
noncomputable def symmetricTensorsEquivSymmetricPower :
    symmetricTensors R M ≃ₗ[R] Sym[R]^2 M :=
  LinearEquiv.ofLinearMap
    (SymmetricPower.mk R (Fin 2) M ∘ₗ (tensorProductEquivTensorSquare R M).toLinearMap ∘ₗ
      (symmetricTensors R M).subtype)
    (LinearMap.codRestrict _
      ((tensorProductEquivTensorSquare R M).symm.toLinearMap ∘ₗ
        SymmetricPower.toTensorSquare R M)
      (tensorProductEquivTensorSquare_symm_symmetricPower_toTensorSquare_mem_symmetricTensors R M))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, SymmetricPower.mk_toTensorSquare,
        LinearMap.id_apply])
    (by
      refine LinearMap.ext fun z ↦ ?_
      have hz : tensorSwap R M (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) =
          tensorProductEquivTensorSquare R M (z : M ⊗[R] M) := by
        rw [← tensorProductEquivTensorSquare_comm]
        exact congrArg _ (mem_symmetricTensors.mp z.2)
      refine Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply,
        symmetricPower_toTensorSquare_mk_of_tensorSwap_eq R M hz,
        LinearEquiv.symm_apply_apply])

/-- The forward map of `TauCeti.symmetricTensorsEquivSymmetricPower` is the symmetric
quotient. -/
@[simp]
theorem symmetricTensorsEquivSymmetricPower_apply (z : symmetricTensors R M) :
    symmetricTensorsEquivSymmetricPower R M z =
      SymmetricPower.mk R (Fin 2) M
        (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) :=
  (rfl)

/-- The inverse of `TauCeti.symmetricTensorsEquivSymmetricPower` is the symmetric-square
embedding. -/
@[simp]
theorem coe_symmetricTensorsEquivSymmetricPower_symm_apply (x : Sym[R]^2M) :
    (((symmetricTensorsEquivSymmetricPower R M).symm x : symmetricTensors R M) : M ⊗[R] M) =
      (tensorProductEquivTensorSquare R M).symm (SymmetricPower.toTensorSquare R M x) :=
  (rfl)

/-- **The symmetrizer, explicitly**: the symmetric tensor matching `x ⊗ₛ y` is
`⅟2 • (x ⊗ₜ y + y ⊗ₜ x)`. -/
theorem coe_symmetricTensorsEquivSymmetricPower_symm_tprod (x y : M) :
    (((symmetricTensorsEquivSymmetricPower R M).symm (⨂ₛ[R] i, (![x, y] : Fin 2 → M) i) :
          symmetricTensors R M) : M ⊗[R] M) =
      ⅟(2 : R) • (x ⊗ₜ[R] y + y ⊗ₜ[R] x) := by
  rw [coe_symmetricTensorsEquivSymmetricPower_symm_apply,
    SymmetricPower.toTensorSquare_tprod, map_smul, map_add,
    tensorProductEquivTensorSquare_symm_tprod, tensorProductEquivTensorSquare_symm_tprod]
  norm_num

/-- **The symmetric quotient, explicitly**: the symmetrization of `x ⊗ₜ y` has symmetric class
`2 • (x ⊗ₛ y)`. -/
theorem symmetricTensorsEquivSymmetricPower_apply_tmul_add_tmul (x y : M) :
    symmetricTensorsEquivSymmetricPower R M
        ⟨x ⊗ₜ[R] y + y ⊗ₜ[R] x, by
          rw [← TensorProduct.comm_tmul R M M x y]
          exact add_comm_mem_symmetricTensors _⟩ =
      (2 : R) • (⨂ₛ[R] i, (![x, y] : Fin 2 → M) i) := by
  rw [symmetricTensorsEquivSymmetricPower_apply]
  have h : tensorProductEquivTensorSquare R M (x ⊗ₜ[R] y + y ⊗ₜ[R] x) =
      PiTensorProduct.tprod R ![x, y] +
        PiTensorProduct.tprod R fun i ↦ (![x, y] : Fin 2 → M) (Equiv.swap 0 1 i) := by
    rw [map_add, tensorProductEquivTensorSquare_tmul, tensorProductEquivTensorSquare_tmul]
    refine congrArg (PiTensorProduct.tprod R ![x, y] + ·)
      (congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_))
    fin_cases i <;> rfl
  rw [h, map_add]
  have hmk : ∀ f : Fin 2 → M,
      SymmetricPower.mk R (Fin 2) M (PiTensorProduct.tprod R f) = ⨂ₛ[R] i, f i := fun _ ↦ rfl
  rw [hmk, hmk, SymmetricPower.tprod_equiv (Equiv.swap 0 1), ← two_smul R]

/-- **The antisymmetric tensors are the exterior square.** The `-1`-eigenspace of the flip on
`M ⊗[R] M` is `⋀[R]^2 M`, by the wedge map read through
`TauCeti.tensorProductEquivTensorSquare`; the inverse is the antisymmetrizer
`x ∧ y ↦ ⅟2 • (x ⊗ₜ y - y ⊗ₜ x)`. -/
noncomputable def antisymmetricTensorsEquivExteriorPower :
    antisymmetricTensors R M ≃ₗ[R] ⋀[R]^2 M :=
  LinearEquiv.ofLinearMap
    (PiTensorProduct.lift (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap ∘ₗ
      (tensorProductEquivTensorSquare R M).toLinearMap ∘ₗ
        (antisymmetricTensors R M).subtype)
    (LinearMap.codRestrict _
      ((tensorProductEquivTensorSquare R M).symm.toLinearMap ∘ₗ
        exteriorPower.toTensorSquare R M)
      (tensorProductEquivTensorSquare_symm_exteriorPower_toTensorSquare_mem_antisymmetricTensors
        R M))
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        exteriorPower.lift_ιMulti_toTensorSquare, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun z ↦ ?_
      have hz : tensorSwap R M (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) =
          -tensorProductEquivTensorSquare R M (z : M ⊗[R] M) := by
        rw [← tensorProductEquivTensorSquare_comm, mem_antisymmetricTensors.mp z.2, map_neg]
      refine Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply,
        exteriorPower_toTensorSquare_lift_ιMulti_of_tensorSwap_eq_neg R M hz,
        LinearEquiv.symm_apply_apply])

/-- The forward map of `TauCeti.antisymmetricTensorsEquivExteriorPower` is the wedge map. -/
@[simp]
theorem antisymmetricTensorsEquivExteriorPower_apply (z : antisymmetricTensors R M) :
    antisymmetricTensorsEquivExteriorPower R M z =
      PiTensorProduct.lift (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap
        (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) :=
  (rfl)

/-- The inverse of `TauCeti.antisymmetricTensorsEquivExteriorPower` is the exterior-square
embedding. -/
@[simp]
theorem coe_antisymmetricTensorsEquivExteriorPower_symm_apply (x : ⋀[R]^2 M) :
    (((antisymmetricTensorsEquivExteriorPower R M).symm x : antisymmetricTensors R M) :
        M ⊗[R] M) =
      (tensorProductEquivTensorSquare R M).symm (exteriorPower.toTensorSquare R M x) :=
  (rfl)

/-- **The antisymmetrizer, explicitly**: the antisymmetric tensor matching `x ∧ y` is
`⅟2 • (x ⊗ₜ y - y ⊗ₜ x)`. -/
theorem coe_antisymmetricTensorsEquivExteriorPower_symm_ιMulti (x y : M) :
    (((antisymmetricTensorsEquivExteriorPower R M).symm
            (exteriorPower.ιMulti R 2 ![x, y]) : antisymmetricTensors R M) : M ⊗[R] M) =
      ⅟(2 : R) • (x ⊗ₜ[R] y - y ⊗ₜ[R] x) := by
  rw [coe_antisymmetricTensorsEquivExteriorPower_symm_apply,
    exteriorPower.toTensorSquare_ιMulti, map_smul, map_sub,
    tensorProductEquivTensorSquare_symm_tprod, tensorProductEquivTensorSquare_symm_tprod]
  norm_num

/-- **The wedge map, explicitly**: the antisymmetrization of `x ⊗ₜ y` wedges to `2 • (x ∧ y)`. -/
theorem antisymmetricTensorsEquivExteriorPower_apply_tmul_sub_tmul (x y : M) :
    antisymmetricTensorsEquivExteriorPower R M
        ⟨x ⊗ₜ[R] y - y ⊗ₜ[R] x, by
          rw [← TensorProduct.comm_tmul R M M x y]
          exact sub_comm_mem_antisymmetricTensors _⟩ =
      (2 : R) • exteriorPower.ιMulti R 2 ![x, y] := by
  rw [antisymmetricTensorsEquivExteriorPower_apply]
  have h : tensorProductEquivTensorSquare R M (x ⊗ₜ[R] y - y ⊗ₜ[R] x) =
      PiTensorProduct.tprod R ![x, y] -
        PiTensorProduct.tprod R (![x, y] ∘ Equiv.swap (0 : Fin 2) 1) := by
    rw [map_sub, tensorProductEquivTensorSquare_tmul, tensorProductEquivTensorSquare_tmul]
    refine congrArg (PiTensorProduct.tprod R ![x, y] - ·)
      (congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_))
    fin_cases i <;> rfl
  rw [h, map_sub, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod,
    AlternatingMap.coe_multilinearMap,
    (exteriorPower.ιMulti R 2).map_swap (![x, y] : Fin 2 → M) (by decide),
    sub_neg_eq_add, ← two_smul R]

end TauCeti

namespace exteriorPower

omit [Invertible (2 : R)] in
/-- The wedge map is natural in the module. -/
theorem lift_ιMulti_comp_piTensorProduct_map {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    PiTensorProduct.lift (ιMulti R 2 (M := N)).toMultilinearMap ∘ₗ
        (PiTensorProduct.map fun _ : Fin 2 ↦ f) =
      map 2 f ∘ₗ PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap := by
  rw [PiTensorProduct.lift_comp_map]
  refine (PiTensorProduct.lift.unique' (MultilinearMap.ext fun g ↦ ?_)).symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap, map_apply_ιMulti,
    MultilinearMap.compLinearMap_apply, Function.comp_def]

end exteriorPower

namespace LinearMap

open TauCeti

variable {R M}

/-- **The symmetric comparison is equivariant**: the restriction of `f ⊗ f` to the symmetric
tensors is `SymmetricPower.map f`. With `TauCeti.symmetricTensorsEquivSymmetricPower` this is
what makes the symmetric tensors a *symmetric square* of representations, not only of
modules. -/
-- Prefer these naturality rules to expanding the comparison maps.
@[simp high]
theorem symmetricTensorsEquivSymmetricPower_symmetricTensorsRestrict (f : M →ₗ[R] M)
    (z : symmetricTensors R M) :
    symmetricTensorsEquivSymmetricPower R M (f.symmetricTensorsRestrict z) =
      SymmetricPower.map f (symmetricTensorsEquivSymmetricPower R M z) := by
  have h : tensorProductEquivTensorSquare R M (TensorProduct.map f f (z : M ⊗[R] M)) =
      PiTensorProduct.map (fun _ : Fin 2 ↦ f)
        (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) := by
    simpa using
      DFunLike.congr_fun (tensorProductEquivTensorSquare_comp_map R M f) (z : M ⊗[R] M)
  rw [symmetricTensorsEquivSymmetricPower_apply, symmetricTensorsEquivSymmetricPower_apply,
    LinearMap.coe_symmetricTensorsRestrict_apply, SymmetricPower.map_mk, h]

/-- **The exterior comparison is equivariant**: the restriction of `f ⊗ f` to the antisymmetric
tensors is `exteriorPower.map 2 f`. -/
@[simp high]
theorem antisymmetricTensorsEquivExteriorPower_antisymmetricTensorsRestrict (f : M →ₗ[R] M)
    (z : antisymmetricTensors R M) :
    antisymmetricTensorsEquivExteriorPower R M (f.antisymmetricTensorsRestrict z) =
      exteriorPower.map 2 f (antisymmetricTensorsEquivExteriorPower R M z) := by
  have h : tensorProductEquivTensorSquare R M (TensorProduct.map f f (z : M ⊗[R] M)) =
      PiTensorProduct.map (fun _ : Fin 2 ↦ f)
        (tensorProductEquivTensorSquare R M (z : M ⊗[R] M)) := by
    simpa using
      DFunLike.congr_fun (tensorProductEquivTensorSquare_comp_map R M f) (z : M ⊗[R] M)
  have hnat := DFunLike.congr_fun (exteriorPower.lift_ιMulti_comp_piTensorProduct_map R M f)
    (tensorProductEquivTensorSquare R M (z : M ⊗[R] M))
  rw [antisymmetricTensorsEquivExteriorPower_apply,
    antisymmetricTensorsEquivExteriorPower_apply,
    LinearMap.coe_antisymmetricTensorsRestrict_apply, h]
  simpa using hnat

end LinearMap
