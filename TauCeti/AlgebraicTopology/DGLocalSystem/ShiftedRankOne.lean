/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Shift
public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne

/-!
# Tensoring with a rank-one local system placed in a nonzero degree

A rank-one local system `L` on a pointed space `(B, b)` is the free module `R` in degree `0` on
which a loop `γ` acts by a unit `ρ(γ)`, and the tensor product `𝓕 ⊗ L` of a DG local system with
it is `TauCeti.RankOneLocalSystem.tensor`. Placing the generator of `L` in homological degree
`-n` instead gives the shifted local system `L[n]`, with `C[n]_j = C_{j+n}`, and the tensor product
`𝓕 ⊗ L[n]` (`TauCeti.RankOneLocalSystem.shiftedTensor`). An element `α ⊗ ℓ` with `α` of
homological degree `p` has degree `p - n`; the differential is that of `𝓕`, since `L[n]` has none;
and a cube `σ` of dimension `k` has to pass the generator of `L[n]` to act, so it acts by the
Koszul sign `(-1)^(n k)` times its action `ρ(σ 0) σ` on `𝓕 ⊗ L`
(`TauCeti.RankOneLocalSystem.shiftedTensorEquiv_op_smul_lof_ofCube`).

This is the right shift `(𝓕 ⊗ L) ⊗ R[-n]` of `TauCeti.DGRightModuleCat.rightShift`, read in the
cohomological grading `C^{-j} = C_j` of DG local systems. Exchanging the two suspensions compares
it with the shift `(𝓕 ⊗ L)[n]`, whose differential is `(-1)^n d`
(`TauCeti.RankOneLocalSystem.shiftedTensorIsoShift`): on `α ⊗ ℓ` with `α` of homological degree
`p` the comparison is multiplication by `(-1)^(n p)`
(`TauCeti.RankOneLocalSystem.shiftEquiv_shiftedTensorIsoShift_hom_app_of_mem`), natural in `𝓕`.

In the Viterbo isomorphism of Barraud–Damian–Humilière–Oancea for a closed `n`-manifold `Q`, the
graded twist is `η_gr = η₀[n]` for a degree-zero twist `η₀` on the free loop space, and this
comparison is the identification `𝓕 ⊗ η_gr ≅ (𝓕 ⊗ η₀)[n]`, with its Koszul factor, between the
twisted coefficients written with the graded twist and the shifted ones written with `η₀`.

## Main definitions

* `TauCeti.RankOneLocalSystem.shiftedTensor`: `𝓕 ⊗ L[n]`.
* `TauCeti.RankOneLocalSystem.shiftedTensorEquiv`: its underlying module is that of `𝓕`.
* `TauCeti.RankOneLocalSystem.shiftedTensorIsoShift`: `𝓕 ⊗ L[n] ≅ (𝓕 ⊗ L)[n]`, natural in `𝓕`.

## Main results

* `TauCeti.RankOneLocalSystem.shiftedTensorEquiv_op_smul_lof_ofCube`: a cube of dimension `k`
  acts on `𝓕 ⊗ L[n]` by `(-1)^(n k) ρ(σ 0) σ`.
* `TauCeti.RankOneLocalSystem.shiftEquiv_shiftedTensorIsoShift_hom_app_of_mem`: on an element of
  homological degree `p` of `𝓕`, the comparison is multiplication by `(-1)^(n p)`, and
  `TauCeti.RankOneLocalSystem.shiftedTensorEquiv_shiftedTensorIsoShift_inv_app_of_mem`, the same
  for its inverse.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.RankOneLocalSystem

universe uM

variable {B : Type*} [TopologicalSpace B] {b : B} {R : Type*} [CommRing R]
  (L : RankOneLocalSystem B b R)

/-- **The tensor product with a shifted rank-one local system** `𝓕 ⊗ L[n]`, with the generator of
`L` in homological degree `-n`: the right shift by `-n` of `𝓕 ⊗ L` in the cohomological grading. -/
abbrev shiftedTensor (n : ℤ) : DGLocalSystem.{uM} B b R ⥤ DGLocalSystem.{uM} B b R :=
  L.tensor ⋙ DGRightModuleCat.rightShiftFunctor (-n)

/-- The underlying module of `𝓕 ⊗ L[n]` over the ground ring is that of `𝓕`, through
`α ⊗ ℓ ↦ α`. -/
-- The source is `(L.shiftedTensor n).obj 𝓕` in simp-normal form, so that the characteristic
-- lemmas below can be simp lemmas.
def shiftedTensorEquiv (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.tensor.obj 𝓕).rightShift (-n) ≃ₗ[R] 𝓕 :=
  ((L.tensor.obj 𝓕).rightShiftEquiv (-n)).trans (DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕)

/-- An element of `𝓕 ⊗ L[n]` has cohomological degree `q` exactly when the corresponding element
of `𝓕` has degree `q - n`. -/
@[simp]
theorem shiftedTensorEquiv_mem_grading_iff (n q : ℤ) (𝓕 : DGLocalSystem.{uM} B b R)
    (x : (L.tensor.obj 𝓕).rightShift (-n)) :
    L.shiftedTensorEquiv n 𝓕 x ∈ 𝓕.grading (q - n) ↔
      x ∈ ((L.tensor.obj 𝓕).rightShift (-n)).grading q := by
  have hx := (L.tensor.obj 𝓕).rightShiftEquiv_mem_grading_iff (-n) q x
  rw [DGRightModuleCat.mem_restrictScalars_obj_grading, ← sub_eq_add_neg] at hx
  exact hx

/-- The differential of `𝓕 ⊗ L[n]` is that of `𝓕`, with no sign. -/
@[simp]
theorem shiftedTensorEquiv_differential (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R)
    (x : (L.tensor.obj 𝓕).rightShift (-n)) :
    L.shiftedTensorEquiv n 𝓕 (((L.tensor.obj 𝓕).rightShift (-n)).differential x) =
      𝓕.differential (L.shiftedTensorEquiv n 𝓕 x) := by
  rw [shiftedTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact (congrArg _ ((L.tensor.obj 𝓕).rightShiftEquiv_differential (-n) x)).trans
    (DGRightModuleCat.restrictScalarsEquiv_differential L.twist 𝓕 _)

/-- **The action on `𝓕 ⊗ L[n]`**: a cube `σ` of dimension `k` acts by the Koszul sign
`(-1)^(n k)` times `ρ(σ 0)` times its action on `𝓕`. -/
theorem shiftedTensorEquiv_op_smul_lof_ofCube (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R) {k : ℕ}
    (σ : SingularCube (MooreLoopSpace B b) k) (x : (L.shiftedTensor n).obj 𝓕) :
    L.shiftedTensorEquiv n 𝓕 (op (cubicalChainLof (MooreLoopSpace B b) R k
        (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ)) • x) =
      (n * k).negOnePow • (L.ρ (σ 0) : R) • (op (cubicalChainLof (MooreLoopSpace B b) R k
        (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ)) •
          L.shiftedTensorEquiv n 𝓕 x) := by
  rw [shiftedTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    DGRightModuleCat.rightShiftEquiv_op_smul_of_mem _ _ (cubicalChainLof_mem _ _ _),
    map_zsmul_unit, tensor_smul_lof_ofCube, neg_mul_neg]

/-- **Exchanging the suspensions** `𝓕 ⊗ L[n] ≅ (𝓕 ⊗ L)[n]`, natural in `𝓕`: on `α ⊗ ℓ` with `α`
of homological degree `p` it is multiplication by the Koszul sign `(-1)^(n p)`. -/
def shiftedTensorIsoShift (n : ℤ) :
    L.shiftedTensor.{uM} n ≅ L.tensor ⋙ DGRightModuleCat.shiftFunctor (-n) :=
  Functor.isoWhiskerLeft L.tensor (DGRightModuleCat.rightShiftFunctorIsoShiftFunctor (-n))

/-- The component of `shiftedTensorIsoShift` at `𝓕` is the exchange of the suspensions of
`𝓕 ⊗ L`. -/
@[simp]
theorem shiftedTensorIsoShift_hom_app (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.shiftedTensorIsoShift n).hom.app 𝓕 = ((L.tensor.obj 𝓕).rightShiftIsoShift (-n)).hom := by
  rw [shiftedTensorIsoShift, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    DGRightModuleCat.rightShiftFunctorIsoShiftFunctor_hom_app]

/-- The inverse component of `shiftedTensorIsoShift` at `𝓕` is the inverse exchange of the
suspensions of `𝓕 ⊗ L`. -/
@[simp]
theorem shiftedTensorIsoShift_inv_app (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.shiftedTensorIsoShift n).inv.app 𝓕 = ((L.tensor.obj 𝓕).rightShiftIsoShift (-n)).inv := by
  rw [shiftedTensorIsoShift, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    DGRightModuleCat.rightShiftFunctorIsoShiftFunctor_inv_app]

/-- **The Koszul factor** of `𝓕 ⊗ L[n] ≅ (𝓕 ⊗ L)[n]`: on `α ⊗ ℓ` with `α` of homological degree
`p`, that is of cohomological degree `-p`, it is multiplication by `(-1)^(n p)`. -/
theorem shiftEquiv_shiftedTensorIsoShift_hom_app_of_mem (n : ℤ) (𝓕 : DGLocalSystem.{uM} B b R)
    {p : ℤ} {x : (L.shiftedTensor n).obj 𝓕} (hx : L.shiftedTensorEquiv n 𝓕 x ∈ 𝓕.grading (-p)) :
    DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕
        ((L.tensor.obj 𝓕).shiftEquiv (-n) ((L.shiftedTensorIsoShift n).hom.app 𝓕 x)) =
      (n * p).negOnePow • L.shiftedTensorEquiv n 𝓕 x := by
  have hx' : (L.tensor.obj 𝓕).rightShiftEquiv (-n) x ∈ (L.tensor.obj 𝓕).grading (-p) :=
    (DGRightModuleCat.mem_restrictScalars_obj_grading _ _ _ _).2 hx
  rw [shiftedTensorIsoShift_hom_app,
    DGRightModuleCat.shiftEquiv_rightShiftIsoShift_hom_apply_of_mem _ _ hx', map_zsmul_unit,
    neg_mul_neg, shiftedTensorEquiv, LinearEquiv.trans_apply]

/-- The Koszul factor of the inverse `(𝓕 ⊗ L)[n] ≅ 𝓕 ⊗ L[n]`: on `α ⊗ ℓ` with `α` of homological
degree `p`, it is again multiplication by `(-1)^(n p)`. -/
theorem shiftedTensorEquiv_shiftedTensorIsoShift_inv_app_of_mem (n : ℤ)
    (𝓕 : DGLocalSystem.{uM} B b R) {p : ℤ}
    {x : (L.tensor ⋙ DGRightModuleCat.shiftFunctor (-n)).obj 𝓕}
    (hx : DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕 ((L.tensor.obj 𝓕).shiftEquiv (-n) x) ∈
      𝓕.grading (-p)) :
    L.shiftedTensorEquiv n 𝓕 ((L.shiftedTensorIsoShift n).inv.app 𝓕 x) =
      (n * p).negOnePow •
        DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕 ((L.tensor.obj 𝓕).shiftEquiv (-n) x) := by
  have hx' : (L.tensor.obj 𝓕).shiftEquiv (-n) x ∈ (L.tensor.obj 𝓕).grading (-p) :=
    (DGRightModuleCat.mem_restrictScalars_obj_grading _ _ _ _).2 hx
  rw [shiftedTensorIsoShift_inv_app, shiftedTensorEquiv, LinearEquiv.trans_apply,
    DGRightModuleCat.rightShiftEquiv_rightShiftIsoShift_inv_apply_of_mem _ _ hx', map_zsmul_unit,
    neg_mul_neg]

end TauCeti.RankOneLocalSystem
