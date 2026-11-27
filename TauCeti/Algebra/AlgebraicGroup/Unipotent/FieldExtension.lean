/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Comodule
public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.RestrictScalars
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Unipotence and extension of the base field

Let `H` be the coordinate Hopf algebra of an affine group `G` over a field `k`, and let `K / k` be
a field extension. In the comodule sense `TauCeti.unipotentCommHopfAlgProperty`, `G` is unipotent
exactly when `G_K`, with coordinate Hopf algebra `K ⊗[k] H`, is unipotent (Milne, Corollary 14.9).

* If `G` is unipotent, so is `G_K`: a `K ⊗[k] H`-comodule `W` is an `H`-comodule over `k` by
  restriction of scalars (`TauCeti.Comodule.restrictScalars`), possibly infinite-dimensional over
  `k`, with the same fixed vectors (`TauCeti.Comodule.mem_fixedSubcomodule_restrictScalars_iff`).
  A unipotent group fixes a nonzero vector of every nonzero comodule, of any dimension.
* If `G_K` is unipotent, so is `G`: for a nonzero `H`-comodule `M`, the fixed vectors of `M` are
  the kernel of `φ : m ↦ ρ(m) - m ⊗ 1`, and those of `K ⊗[k] M` (`TauCeti.Comodule.baseChange`)
  are the kernel of `id_K ⊗ φ`. If `φ` were injective, so would be `id_K ⊗ φ`, since `K` is flat
  over `k`, and `K ⊗[k] M` would have no nonzero fixed vector.

No finiteness of `H` is needed in either direction.

## Main results

* `TauCeti.unipotentCommHopfAlgProperty.baseChange`: unipotence is preserved by field extension.
* `TauCeti.unipotentCommHopfAlgProperty.of_baseChange`: unipotence is reflected by field extension.
* `TauCeti.unipotentCommHopfAlgProperty.baseChange_iff`: the two together.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 14.9, p. 282.
-/

public section

open scoped TensorProduct

namespace TauCeti

open Comodule TensorProduct.AlgebraTensorModule

universe u v w

variable {k : Type u} {K : Type w} {H : Type v} [Field k] [Field K] [Algebra k K]
  [CommRing H] [HopfAlgebra k H]

namespace unipotentCommHopfAlgProperty

/-- **Unipotence is preserved by extension of the base field**: if `H` is unipotent over `k`, then
`K ⊗[k] H` is unipotent over `K`. A `K ⊗[k] H`-comodule is an `H`-comodule over `k` with the same
fixed vectors. -/
theorem baseChange (hH : unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H)) :
    unipotentCommHopfAlgProperty K (CommHopfAlgCat.of K (K ⊗[k] H)) := by
  refine (unipotentCommHopfAlgProperty_iff K _).mpr fun W _ _ _ _ _ ↦ ?_
  let _ : Module k W := Module.compHom W (algebraMap k K)
  let _ := IsScalarTower.of_compHom k K W
  let _ := Comodule.restrictScalars (R := k) (A := K) (C := H) (M := W)
  obtain ⟨v, hv, hvc⟩ := hasNonzeroFixedVector_iff.mp (hH.hasNonzeroFixedVector (M := W))
  exact hasNonzeroFixedVector_iff.mpr ⟨v, hv, mem_fixedSubcomodule.mp
    ((mem_fixedSubcomodule_restrictScalars_iff v).mp (mem_fixedSubcomodule.mpr hvc))⟩

end unipotentCommHopfAlgProperty

/-- **Unipotence is reflected by extension of the base field**: if `K ⊗[k] H` is unipotent over
`K`, then `H` is unipotent over `k`. If `m ↦ ρ(m) - m ⊗ 1` were injective on a nonzero comodule
`M`, its scalar extension would be injective by flatness, and `K ⊗[k] M` would have no nonzero
fixed vector. -/
theorem unipotentCommHopfAlgProperty.of_baseChange
    (hH : unipotentCommHopfAlgProperty K (CommHopfAlgCat.of K (K ⊗[k] H))) :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) := by
  refine (unipotentCommHopfAlgProperty_iff k _).mpr fun M _ _ _ _ _ ↦ ?_
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  have : Nontrivial (K ⊗[k] M) := Module.FaithfullyFlat.lTensor_nontrivial k K M
  obtain ⟨v, hv, hvc⟩ := hasNonzeroFixedVector_iff.mp
    (hH.hasNonzeroFixedVector (M := K ⊗[k] M))
  by_contra hM
  let φ : M →ₗ[k] M ⊗[k] H := coact (R := k) (C := H) (M := M) - (TensorProduct.mk k M H).flip 1
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    by_contra hm0
    refine hM (hasNonzeroFixedVector_iff.mpr ⟨m, hm0, ?_⟩)
    simpa [φ, sub_eq_zero] using hm
  refine hv (Module.Flat.lTensor_preserves_injective_linearMap (M := K) φ hφ ?_)
  rw [map_zero, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
  apply (distribBaseChange k K M H).injective
  rw [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor,
    distribBaseChange_baseChange_mk_flip, ← Algebra.TensorProduct.one_def, ← hvc, baseChange_coact,
    baseChangeCoact_apply]

/-- **Unipotence is invariant under extension of the base field** (Milne, Corollary 14.9):
`K ⊗[k] H` is unipotent over `K` exactly when `H` is unipotent over `k`. -/
theorem unipotentCommHopfAlgProperty.baseChange_iff :
    unipotentCommHopfAlgProperty K (CommHopfAlgCat.of K (K ⊗[k] H)) ↔
      unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) :=
  ⟨unipotentCommHopfAlgProperty.of_baseChange, unipotentCommHopfAlgProperty.baseChange⟩

end TauCeti
