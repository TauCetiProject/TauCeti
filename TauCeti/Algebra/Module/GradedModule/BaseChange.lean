/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.Algebra.Module.GradedModule.Dual.Basic
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
import TauCeti.Algebra.DirectSum.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Scalar extension of internal gradings

An internal grading extends along any homomorphism of commutative semirings. Its pieces are
Mathlib's scalar-extended submodules; their internality is `DirectSum.IsInternal.baseChange`.
Thus no flatness hypothesis is needed.

This file packages that construction as `TauCeti.InternalGrading.baseChange` and establishes its
interaction with homogeneous projections, coarsening, parity, homogeneous linear maps, graded
monoid structures, linear duals, and tensor products.

## Main definitions and results

* `TauCeti.InternalGrading.baseChange`: the internal `S`-grading on `S ⊗[R] M`.
* `TauCeti.coarsenGrading_baseChange`, `TauCeti.parityGrading_baseChange`,
  `TauCeti.parityGrading_baseChange_eq_bot`, `TauCeti.InternalGrading.coarsen_baseChange`,
  `TauCeti.InternalGrading.parity_baseChange`,
  `TauCeti.InternalGrading.parityGrading_baseChange_piece_eq_bot`: coarsening and parity commute
  with base change, so vanishing of any parity piece is preserved.
* `TauCeti.InternalGrading.instGradedOneBaseChange`,
  `TauCeti.InternalGrading.instGradedMulBaseChange`,
  `TauCeti.InternalGrading.instGradedMonoidBaseChange`: scalar extension preserves graded unit,
  multiplication, and monoid structures on internal gradings.
* `TauCeti.InternalGrading.isHomogeneous_distribBaseChange`,
  `TauCeti.InternalGrading.isHomogeneous_distribBaseChange_symm`: the canonical isomorphism
  `S ⊗[R] (M ⊗[R] N) ≃ₗ[S] (S ⊗[R] M) ⊗[S] (S ⊗[R] N)` and its inverse have degree zero.
* `TauCeti.InternalGrading.dualBaseChange_mem_dualPiece`,
  `TauCeti.InternalGrading.isHomogeneous_dualBaseChange`,
  `TauCeti.InternalGrading.isHomogeneous_restrictScalars_dualBaseChange`: `Module.Dual.baseChange`
  preserves degree.
* `LinearMap.IsHomogeneous.baseChange`, `LinearMap.IsHomogeneous.baseChange_internalGrading`:
  scalar extension preserves the degree of homogeneous linear maps.
-/

public section

open scoped TensorProduct

namespace TauCeti

section Coarsen

variable {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Coarsening a family of submodules commutes with scalar extension. -/
theorem coarsenGrading_baseChange (ℳ : ι → Submodule R M) (S : Type*) [Semiring S] [Algebra R S]
    (f : ι → κ) (k : κ) :
    coarsenGrading (fun i ↦ (ℳ i).baseChange S) f k = (coarsenGrading ℳ f k).baseChange S := by
  simp only [coarsenGrading_apply, Submodule.baseChange_iSup]

/-- Taking parity pieces commutes with scalar extension. -/
theorem parityGrading_baseChange (ℳ : ℤ → Submodule R M) (S : Type*) [Semiring S] [Algebra R S]
    (i : ZMod 2) :
    parityGrading (fun n ↦ (ℳ n).baseChange S) i = (parityGrading ℳ i).baseChange S :=
  coarsenGrading_baseChange ℳ S _ i

/-- Scalar extension preserves vanishing of a parity piece (in particular, even support when
`i = 1`). -/
theorem parityGrading_baseChange_eq_bot {ℳ : ℤ → Submodule R M} (S : Type*) [Semiring S]
    [Algebra R S] {i : ZMod 2} (h : parityGrading ℳ i = ⊥) :
    parityGrading (fun n ↦ (ℳ n).baseChange S) i = ⊥ := by
  rw [parityGrading_baseChange, h, Submodule.baseChange_bot]

end Coarsen

namespace InternalGrading

section GeneralIndex

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq ι]

/-- Extend every homogeneous summand along the coefficient homomorphism. -/
noncomputable def baseChange (G : InternalGrading R M ι) (S : Type*) [CommSemiring S]
    [Algebra R S] : InternalGrading S (S ⊗[R] M) ι where
  piece i := (G.piece i).baseChange S
  isInternal := G.isInternal.baseChange

/-- The pieces of the extended grading are the scalar extensions of the original pieces. -/
@[simp, grind =]
theorem baseChange_piece (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S]
    (i : ι) : (G.baseChange S).piece i = (G.piece i).baseChange S := (rfl)

/-- A pure tensor `s ⊗ₜ x` with `x ∈ G.piece p` lies in degree `p` of `G.baseChange S`. -/
theorem tmul_mem_baseChange (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S]
    {p : ι} (s : S) {x : M} (hx : x ∈ G.piece p) :
    s ⊗ₜ[R] x ∈ (G.baseChange S).piece p := by
  rw [baseChange_piece]
  exact Submodule.tmul_mem_baseChange_of_mem s hx

/-- An `S`-submodule containing `1 ⊗ₜ x` for every `x ∈ G.piece p` contains the whole degree-`p`
piece of `G.baseChange S`. -/
theorem baseChange_piece_le (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S]
    {p : ι} {C : Submodule S (S ⊗[R] M)} (h : ∀ x ∈ G.piece p, 1 ⊗ₜ[R] x ∈ C) :
    (G.baseChange S).piece p ≤ C := by
  rw [baseChange_piece]
  exact Submodule.baseChange_le_iff_le_comap.mpr h

/-- The homogeneous component of a pure tensor is the tensor of its homogeneous component. -/
@[simp]
theorem coe_decompose_baseChange_tmul (G : InternalGrading R M ι) (S : Type*) [CommSemiring S]
    [Algebra R S] (s : S) (x : M) (i : ι) :
    (DirectSum.decompose (G.baseChange S).piece (s ⊗ₜ[R] x) i : S ⊗[R] M) =
      s ⊗ₜ[R] (DirectSum.decompose G.piece x i : M) := by
  have hd : (inferInstance : DirectSum.Decomposition (G.baseChange S).piece) =
      DirectSum.Decomposition.baseChange G.piece := Subsingleton.elim _ _
  dsimp only [inferInstance] at hd
  rw [hd]
  exact DirectSum.coe_decompose_baseChange_tmul G.piece s x i

/-- Coarsening an internal grading commutes with scalar extension. -/
@[simp]
theorem coarsen_baseChange {κ : Type*} [DecidableEq κ] (G : InternalGrading R M ι) (S : Type*)
    [CommSemiring S] [Algebra R S] (f : ι → κ) :
    (G.baseChange S).coarsen f = (G.coarsen f).baseChange S := by
  refine InternalGrading.ext fun k ↦ ?_
  rw [coarsen_piece, baseChange_piece, coarsen_piece, funext (G.baseChange_piece S)]
  exact coarsenGrading_baseChange G.piece S f k

/-- Scalar extension preserves `1 ∈ G.piece 0` on internal gradings of unital algebras. -/
instance instGradedOneBaseChange {A : Type*} [NonAssocSemiring A] [Module R A] [Zero ι]
    (G : InternalGrading R A ι) [SetLike.GradedOne G.piece] (S : Type*) [CommSemiring S]
    [Algebra R S] : SetLike.GradedOne (G.baseChange S).piece where
  one_mem := G.tmul_mem_baseChange S 1 (SetLike.one_mem_graded G.piece)

/-- Scalar extension preserves graded multiplication on internal gradings of algebras. -/
instance instGradedMulBaseChange {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [Add ι]
    (G : InternalGrading R A ι) [SetLike.GradedMul G.piece] (S : Type*) [CommSemiring S]
    [Algebra R S] : SetLike.GradedMul (G.baseChange S).piece where
  mul_mem i j u v hu hv := by
    refine G.baseChange_piece_le S
      (C := ((G.baseChange S).piece (i + j)).comap (_root_.LinearMap.mulRight S v))
      (fun a ha ↦ ?_) hu
    refine G.baseChange_piece_le S
      (C := ((G.baseChange S).piece (i + j)).comap (_root_.LinearMap.mulLeft S (1 ⊗ₜ[R] a)))
      (fun b hb ↦ ?_) hv
    simpa using G.tmul_mem_baseChange S 1 (SetLike.mul_mem_graded ha hb)

/-- Scalar extension preserves graded monoid compatibility on internal gradings of algebras. -/
instance instGradedMonoidBaseChange {A : Type*} [Semiring A] [Algebra R A] [AddMonoid ι]
    (G : InternalGrading R A ι) [SetLike.GradedMonoid G.piece] (S : Type*) [CommSemiring S]
    [Algebra R S] : SetLike.GradedMonoid (G.baseChange S).piece where

/-- The canonical isomorphism `S ⊗[R] (M ⊗[R] N) ≃ₗ[S] (S ⊗[R] M) ⊗[S] (S ⊗[R] N)` has degree zero
for the base-changed total-degree gradings. -/
theorem isHomogeneous_distribBaseChange [AddMonoid ι] (G : InternalGrading R M ι)
    (H : InternalGrading R N ι) (S : Type*) [CommSemiring S] [Algebra R S] :
    LinearMap.IsHomogeneous
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).toLinearMap
      ((G.tensorProduct H).baseChange S).piece
      ((G.baseChange S).tensorProduct (H.baseChange S)).piece 0 := by
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange R S M N
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (G.tensorProduct H).baseChange_piece_le S
    (C := (((G.baseChange S).tensorProduct (H.baseChange S)).piece (n + 0)).comap e.toLinearMap)
    (fun t ht ↦ ?_) hz
  let g := (e.toLinearMap.restrictScalars R) ∘ₗ TensorProduct.mk R S (M ⊗[R] N) 1
  let C' :=
    (((G.baseChange S).tensorProduct (H.baseChange S)).piece (n + 0)).restrictScalars R
  refine G.tensorProduct_piece_le_of_add_eq H (C := C'.comap g) (fun p q hpq x hx y hy ↦ ?_) ht
  simp only [Submodule.mem_comap, C', Submodule.restrictScalars_mem,
    _root_.LinearMap.comp_apply, _root_.LinearMap.coe_restrictScalars,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, g, e,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, add_zero, ← hpq]
  exact tmul_mem_tensorProduct (G.baseChange S) (H.baseChange S)
    (G.tmul_mem_baseChange S 1 hx) (H.tmul_mem_baseChange S 1 hy)

/-- The inverse of `TensorProduct.AlgebraTensorModule.distribBaseChange` also has degree zero. -/
theorem isHomogeneous_distribBaseChange_symm [AddMonoid ι] (G : InternalGrading R M ι)
    (H : InternalGrading R N ι) (S : Type*) [CommSemiring S] [Algebra R S] :
    LinearMap.IsHomogeneous
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).symm.toLinearMap
      ((G.baseChange S).tensorProduct (H.baseChange S)).piece
      ((G.tensorProduct H).baseChange S).piece 0 :=
  (G.isHomogeneous_distribBaseChange H S).linearEquiv_symm

end GeneralIndex

section IntGrading

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Parity pieces of `G.baseChange S` are scalar extensions of the parity pieces of `G`. -/
theorem parityGrading_baseChange_piece (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S]
    [Algebra R S] (i : ZMod 2) :
    parityGrading (G.baseChange S).piece i = (parityGrading G.piece i).baseChange S := by
  rw [funext (G.baseChange_piece S)]
  exact coarsenGrading_baseChange G.piece S (Int.castAddHom (ZMod 2)) i

/-- Taking the parity internal grading commutes with scalar extension. -/
theorem parity_baseChange (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S] [Algebra R S] :
    (G.baseChange S).parity = G.parity.baseChange S :=
  G.coarsen_baseChange S (Int.castAddHom (ZMod 2))

/-- Scalar extension of an internal grading preserves vanishing of a parity piece. -/
theorem parityGrading_baseChange_piece_eq_bot {G : InternalGrading R M ℤ} (S : Type*)
    [CommSemiring S] [Algebra R S] {i : ZMod 2} (h : parityGrading G.piece i = ⊥) :
    parityGrading (G.baseChange S).piece i = ⊥ := by
  rw [G.parityGrading_baseChange_piece S i, h, Submodule.baseChange_bot]

/-- Extending scalars of a functional via `Module.Dual.baseChange` preserves its dual degree. -/
theorem dualBaseChange_mem_dualPiece (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S]
    [Algebra R S] {p : ℤ} {φ : Module.Dual R M} (hφ : φ ∈ G.dualPiece p) :
    Module.Dual.baseChange S φ ∈ (G.baseChange S).dualPiece p := by
  rw [mem_dualPiece_iff]
  intro q z hz hq
  have hle : (G.baseChange S).piece q ≤ _root_.LinearMap.ker (Module.Dual.baseChange S φ) :=
    G.baseChange_piece_le S fun x hx ↦ by
      simp [(mem_dualPiece_iff G p φ).mp hφ q x hx hq]
  exact hle hz

/-- Extending scalars of a degree-`d` functional `φ : M →ₗ[R] R` along an ungraded commutative
`R`-algebra `S` gives an `S`-linear functional of degree `d` for `G.baseChange S`. -/
theorem isHomogeneous_dualBaseChange (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S]
    [Algebra R S] {φ : Module.Dual R M} {d : ℤ}
    (hφ : LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) d) :
    LinearMap.IsHomogeneous (Module.Dual.baseChange S φ)
      (G.baseChange S).piece (trivialGrading S S) d := by
  rw [← mem_dualPiece_iff_isHomogeneous_trivialGrading] at hφ ⊢
  exact G.dualBaseChange_mem_dualPiece S hφ

/-- When `S` carries an internal `ℤ`-grading `GS` over `R`, the scalar-extended functional
`Module.Dual.baseChange S φ : S ⊗[R] M →ₗ[S] S` restricted to `R` has degree `d` from
`(GS.tensorProduct G).piece` into `GS.piece`. -/
theorem isHomogeneous_restrictScalars_dualBaseChange (G : InternalGrading R M ℤ) {S : Type*}
    [CommSemiring S] [Algebra R S] (GS : InternalGrading R S ℤ) {φ : Module.Dual R M} {d : ℤ}
    (hφ : LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) d) :
    LinearMap.IsHomogeneous ((Module.Dual.baseChange S φ).restrictScalars R)
      (GS.tensorProduct G).piece GS.piece d := by
  have hφ' := (G.mem_dualPiece_iff_isHomogeneous_trivialGrading d φ).mpr hφ
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine GS.tensorProduct_piece_le G
    (C := (GS.piece (n + d)).comap ((Module.Dual.baseChange S φ).restrictScalars R))
    (fun p s hs x hx ↦ ?_) hz
  simp only [Submodule.mem_comap, _root_.LinearMap.coe_restrictScalars,
    Module.Dual.baseChange_apply_tmul]
  by_cases hx_deg : n - p = -d
  · have hp : p = n + d := by omega
    rw [← hp]
    exact Submodule.smul_mem _ (φ x) hs
  · rw [G.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hφ' hx (by omega), zero_smul]
    exact Submodule.zero_mem _

end IntGrading

end InternalGrading

end TauCeti

namespace LinearMap.IsHomogeneous

open TauCeti (InternalGrading)

section Families

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddMonoid ι]
  {f : M →ₗ[R] N} {ℳ : ι → Submodule R M} {𝓝 : ι → Submodule R N} {q : ι}

/-- Scalar extension preserves the degree of a homogeneous linear map between submodule
families. No decomposition or flatness hypothesis is needed. -/
@[grind =>]
theorem baseChange (hf : IsHomogeneous f ℳ 𝓝 q) (S : Type*) [Semiring S] [Algebra R S] :
    IsHomogeneous (f.baseChange S) (fun p ↦ (ℳ p).baseChange S)
      (fun p ↦ (𝓝 p).baseChange S) q := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx => ?_
  have hmap : (ℳ p).map f ≤ 𝓝 (p + q) :=
    Submodule.map_le_iff_le_comap.mpr fun _ hx ↦ hf.map_mem hx
  have hbase := Submodule.baseChange_mono S hmap
  rw [Submodule.baseChange_map] at hbase
  exact hbase (Submodule.mem_map_of_mem hx)

end Families

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddMonoid ι] [DecidableEq ι] {f : M →ₗ[R] N} {q : ι}

/-- Scalar extension preserves the degree of a homogeneous map of internally graded modules. -/
@[grind ←]
theorem baseChange_internalGrading {G : InternalGrading R M ι} {H : InternalGrading R N ι}
    (hf : IsHomogeneous f G.piece H.piece q) (S : Type*) [CommSemiring S] [Algebra R S] :
    IsHomogeneous (f.baseChange S) (G.baseChange S).piece (H.baseChange S).piece q := by
  simpa only [LinearMap.isHomogeneous_def, InternalGrading.baseChange_piece] using hf.baseChange S

end LinearMap.IsHomogeneous
