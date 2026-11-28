/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake.UpperTriangularBlock

/-!
# Composition snake diagram for continuous linear maps

Specializing `ContinuousLinearMap.upperTriangularBlock` to
`ContinuousLinearMap.compSnakeMiddle T S = upperTriangularBlock T (-id) S` models the middle
vertical map `(x, y) ↦ (T x - y, S y)` in the composition snake diagram
`0 → E → E × F → F → 0` over `0 → F → F × G → G → 0`.

## Main declarations

* `ContinuousLinearMap.compSnakeMiddle`: middle map `(x, y) ↦ (T x - y, S y)`.
* `ContinuousLinearMap.snakeδL_compSnakeMiddle_eq`: the connecting map `ker S →L[R] F ⧸ range T`
  is `-(T.range.mkQL ∘L S.ker.subtypeL)`.
* `ContinuousLinearMap.compSnakeMiddleDomEquiv`, `ContinuousLinearMap.compSnakeMiddleCodEquiv`, and
  `ContinuousLinearMap.compSnakeMiddle_eq_comp_prodMap_comp`: shear factorization diagonalizing
  `compSnakeMiddle T S` to `(id).prodMap (S ∘L T)`.
* `ContinuousLinearMap.index_compSnakeMiddle`: `(compSnakeMiddle T S).index = (S ∘L T).index`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1.
* Mathlib's `CategoryTheory.kernelCokernelCompSequence`.
-/

public section

namespace ContinuousLinearMap

section CompSnakeEquiv

variable {R E F G : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]

/-- Domain shear-and-swap equivalence `(x, y) ↦ (T x - y, x)` used to diagonalize
`compSnakeMiddle`, with inverse `(v, x) ↦ (x, T x - v)`. -/
def compSnakeMiddleDomEquiv [IsTopologicalAddGroup F] (T : E →L[R] F) : (E × F) ≃L[R] F × E :=
  ((ContinuousLinearEquiv.refl R E).skewProd (ContinuousLinearEquiv.neg R) T).trans
    (ContinuousLinearEquiv.prodComm R E F)

@[simp] theorem compSnakeMiddleDomEquiv_apply [IsTopologicalAddGroup F] (T : E →L[R] F)
    (xy : E × F) :
    T.compSnakeMiddleDomEquiv xy = (T xy.1 - xy.2, xy.1) := by
  simp [compSnakeMiddleDomEquiv, sub_eq_add_neg, add_comm]

@[simp] theorem compSnakeMiddleDomEquiv_symm_apply [IsTopologicalAddGroup F] (T : E →L[R] F)
    (vx : F × E) :
    T.compSnakeMiddleDomEquiv.symm vx = (vx.2, T vx.2 - vx.1) := by
  simp [compSnakeMiddleDomEquiv, sub_eq_add_neg, add_comm]

/-- Codomain shear equivalence `(v, w) ↦ (v, w - S v)` used to diagonalize `compSnakeMiddle`,
with inverse `(v, w) ↦ (v, w + S v)`. -/
def compSnakeMiddleCodEquiv [IsTopologicalAddGroup G] (S : F →L[R] G) : (F × G) ≃L[R] F × G :=
  ((ContinuousLinearEquiv.refl R F).skewProd (ContinuousLinearEquiv.refl R G) S).symm

@[simp] theorem compSnakeMiddleCodEquiv_apply [IsTopologicalAddGroup G] (S : F →L[R] G)
    (vw : F × G) :
    S.compSnakeMiddleCodEquiv vw = (vw.1, vw.2 - S vw.1) := by
  simp [compSnakeMiddleCodEquiv]

@[simp] theorem compSnakeMiddleCodEquiv_symm_apply [IsTopologicalAddGroup G] (S : F →L[R] G)
    (vw : F × G) :
    S.compSnakeMiddleCodEquiv.symm vw = (vw.1, vw.2 + S vw.1) := by
  simp [compSnakeMiddleCodEquiv]

end CompSnakeEquiv

section CompSnake

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]
  (T : E →L[R] F) (S : F →L[R] G)

/-- The middle vertical map `(x, y) ↦ (T x - y, S y)` of the composition snake diagram
`0 → E → E × F → F → 0` over `0 → F → F × G → G → 0`, realizing
`CategoryTheory.kernelCokernelCompSequence.φ` for continuous linear maps. -/
def compSnakeMiddle : E × F →L[R] F × G :=
  upperTriangularBlock T (-ContinuousLinearMap.id R F) S

theorem compSnakeMiddle_def :
    compSnakeMiddle T S = upperTriangularBlock T (-ContinuousLinearMap.id R F) S := (rfl)

@[simp] theorem compSnakeMiddle_apply (xy : E × F) :
    compSnakeMiddle T S xy = (T xy.1 - xy.2, S xy.2) := by simp [compSnakeMiddle, sub_eq_add_neg]

@[simp] theorem compSnakeMiddle_comp_inl :
    compSnakeMiddle T S ∘L inl R E F = inl R F G ∘L T :=
  T.upperTriangularBlock_comp_inl (-ContinuousLinearMap.id R F) S

@[simp] theorem compSnakeMiddle_comp_inr :
    compSnakeMiddle T S ∘L inr R E F = (-ContinuousLinearMap.id R F).prod S :=
  T.upperTriangularBlock_comp_inr (-ContinuousLinearMap.id R F) S

@[simp] theorem fst_comp_compSnakeMiddle :
    fst R F G ∘L compSnakeMiddle T S = T.coprod (-ContinuousLinearMap.id R F) :=
  T.fst_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

@[simp] theorem snd_comp_compSnakeMiddle :
    snd R F G ∘L compSnakeMiddle T S = S ∘L snd R E F :=
  T.snd_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

/-- In the composition snake diagram `(T, compSnakeMiddle T S, S)`, the continuous connecting map
`ker S →L[R] F ⧸ range T` equals `-(T.range.mkQL ∘L S.ker.subtypeL)`, matching
`CategoryTheory.kernelCokernelCompSequence.δ_fac`. -/
theorem snakeδL_compSnakeMiddle_eq
    {σ : F →L[R] E × F} (hσ : Function.RightInverse σ (snd R E F))
    {ρ : F × G →L[R] F} (hρ : Function.LeftInverse ρ (inl R F G)) :
    (Function.Exact.inl_snd).snakeδL .inl_snd
      (T.compSnakeMiddle_comp_inl S).symm (T.snd_comp_compSnakeMiddle S) hσ hρ =
        -(T.range.mkQL ∘L S.ker.subtypeL) :=
  (snakeδL_upperTriangularBlock_eq T (-ContinuousLinearMap.id R F) S hσ hρ).trans (by ext; simp)

/-- Explicit domain and codomain equivalence factorization of `compSnakeMiddle T S`:
`compSnakeMiddle T S = S.compSnakeMiddleCodEquiv ∘L ((id R F).prodMap (S ∘L T)) ∘L`
`T.compSnakeMiddleDomEquiv`, allowing consumers to transport kernels, cokernels, invertibility,
and Fredholmness while tracking exact representatives. -/
theorem compSnakeMiddle_eq_comp_prodMap_comp [IsTopologicalAddGroup G] :
    compSnakeMiddle T S =
      (S.compSnakeMiddleCodEquiv : F × G →L[R] F × G) ∘L
        ((ContinuousLinearMap.id R F).prodMap (S ∘L T)) ∘L
          (T.compSnakeMiddleDomEquiv : E × F →L[R] F × E) := by
  apply ContinuousLinearMap.ext; rintro ⟨x, y⟩
  ext <;> simp [sub_eq_add_neg]

/-- `compSnakeMiddle T S` has the same index as the composite `S ∘L T`, with no finiteness or
topological-group assumptions on `E` or `G`. -/
@[simp] theorem index_compSnakeMiddle : (compSnakeMiddle T S).index = (S ∘L T).index := by
  -- Use `LinearEquiv` for the codomain shear so no `[IsTopologicalAddGroup G]` is needed.
  let eCod : (F × G) ≃ₗ[R] (F × G) :=
    (LinearEquiv.refl R F).skewProd (LinearEquiv.refl R G) S.toLinearMap
  let eDom : (F × E) ≃ₗ[R] (E × F) := T.compSnakeMiddleDomEquiv.symm.toLinearEquiv
  have hconj : eCod.toLinearMap ∘ₗ (compSnakeMiddle T S).toLinearMap ∘ₗ eDom.toLinearMap =
      LinearMap.id.prodMap (S ∘L T).toLinearMap := by
    apply LinearMap.ext; rintro ⟨v, x⟩; ext <;> simp [eCod, eDom, sub_eq_add_neg]
  have hidx := congrArg LinearMap.index hconj
  rw [LinearMap.index_equiv_comp, LinearMap.index_comp_equiv, LinearMap.index_id_prodMap] at hidx
  rw [index_def, index_def]
  exact hidx

end CompSnake

end ContinuousLinearMap
