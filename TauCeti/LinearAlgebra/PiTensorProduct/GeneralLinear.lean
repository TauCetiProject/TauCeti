/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`, the detection of a subspace by the
-- functionals vanishing on it.
public import Mathlib.LinearAlgebra.Dual.Lemmas
-- `Matrix.toLinAlgEquiv`, the algebra isomorphism between matrices and endomorphisms.
public import Mathlib.LinearAlgebra.Matrix.ToLin
-- `PiTensorProduct.map` and `PiTensorProduct.mapMultilinear`, the diagonal operators.
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Multilinear

/-!
# The diagonal operators of the invertible endomorphisms span all of them

A `V`-endomorphism `f` acts on the tensor power `⨂[K] (_ : ι), V` diagonally, by
`f^{⊗ι} = PiTensorProduct.map (fun _ ↦ f)`. These diagonal operators are not closed under addition,
so the span of the ones coming from *invertible* `f` is not visibly all of the span of them all.
Over an infinite field and for a finite-dimensional `V` the two spans nonetheless coincide
(`PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`), because the invertible
endomorphisms are Zariski dense. That is what lets the general linear group replace the whole
endomorphism algebra in Schur-Weyl duality, where the commutant of the symmetric-group action is
the span of the diagonal operators and one wants it to be the image of `K[GL(V)]`.

## The argument

A vector of a vector space lies in a subspace as soon as every functional vanishing on the subspace
kills it (`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`). So fix a functional `φ` on
`End (⨂[K] (_ : ι), V)` vanishing on the span of the invertible diagonal operators. Composing `φ`
with `PiTensorProduct.mapMultilinear`, which is multilinear in the family of endomorphisms, and with
the matrix-to-endomorphism isomorphism attached to a basis, produces a multilinear form `Θ` in `ι`
matrix arguments whose diagonal is `Θ (Y, …, Y) = φ (Y^{⊗ι})`. That diagonal vanishes on the
invertible matrices, hence identically, by
`MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

## Main results

* `PiTensorProduct.map_const_mem_span_range_map_const_units`: the diagonal operator of an
  endomorphism is a combination of the diagonal operators of the invertible ones.
* `PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`: consequently the two spans
  agree.
-/

public section

open Matrix

open scoped TensorProduct

namespace PiTensorProduct

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite ι]

/-- **The diagonal operator of an endomorphism is a combination of the diagonal operators of the
invertible ones**, over an infinite field and for a finite-dimensional `V`. -/
theorem map_const_mem_span_range_map_const_units (f : V →ₗ[K] V) :
    map (fun _ : ι => f) ∈ Submodule.span K
      (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) := by
  classical
  cases nonempty_fintype ι
  set S := Submodule.span K
    (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) with hSdef
  suffices h : ∀ φ : Module.Dual K ((⨂[K] _ : ι, V) →ₗ[K] (⨂[K] _ : ι, V)),
      (∀ y ∈ S, φ y = 0) → φ (map fun _ : ι => f) = 0 by
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp fun φ hφ =>
      h φ ((Submodule.mem_dualAnnihilator _).mp hφ)
  intro φ hφ
  set e := Module.finBasis K V with hedef
  set Θ : MultilinearMap K
      (fun _ : ι => Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) K :=
    (LinearMap.compMultilinearMap φ
      (mapMultilinear K (fun _ : ι => V) fun _ : ι => V)).compLinearMap
        fun _ => (Matrix.toLinAlgEquiv e).toLinearMap with hΘdef
  have hΘ : ∀ X, (Θ fun _ => X) = φ (map fun _ : ι => Matrix.toLinAlgEquiv e X) := fun _ => by
    simp only [hΘdef, MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply,
      mapMultilinear_apply, AlgEquiv.toLinearMap_apply]
  have hgl : ∀ g : GL (Fin (Module.finrank K V)) K,
      (Θ fun _ => (g : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K)) = 0 := by
    intro g
    rw [hΘ]
    obtain ⟨u, hu⟩ := g.isUnit.map (Matrix.toLinAlgEquiv e)
    exact hφ _ (Submodule.subset_span ⟨u, congrArg _ (funext fun _ => hu)⟩)
  have hf := Θ.apply_const_eq_zero_of_eq_zero_on_gl hgl (LinearMap.toMatrixAlgEquiv e f)
  rwa [hΘ, Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at hf

/-- **The diagonal operators of the invertible endomorphisms span the same subspace as all the
diagonal operators**, over an infinite field and for a finite-dimensional `V`. -/
theorem span_range_map_const_units_eq_span_range_map_const :
    Submodule.span K (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) =
      Submodule.span K (Set.range fun f : V →ₗ[K] V => map fun _ : ι => f) :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩; exact map_const_mem_span_range_map_const_units f))

end PiTensorProduct
