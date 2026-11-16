/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.DirectSum.BaseChange
public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.Algebra.Module.GradedModule.Dual.Basic
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Scalar extension of internally graded modules

Extending scalars of an internally graded `R`-module `M` along a commutative `R`-algebra `S` gives
an internally graded `S`-module `S ⊗[R] M` whose degree-`p` piece is `(G.piece p).baseChange S`,
with internality supplied by Mathlib's `DirectSum.Decomposition.baseChange`.

This file packages that construction for `TauCeti.InternalGrading` and establishes its interaction
with coarsening, parity, homogeneous linear maps, linear duals, graded monoid structures, and
tensor products.

## Main definitions and results

* `TauCeti.InternalGrading.baseChange`: the internal `S`-grading on `S ⊗[R] M`.
* `TauCeti.coarsenGrading_baseChange`, `TauCeti.parityGrading_baseChange`,
  `TauCeti.parityGrading_baseChange_eq_bot`, `TauCeti.InternalGrading.coarsen_baseChange`,
  `TauCeti.InternalGrading.parity_baseChange`,
  `TauCeti.InternalGrading.parityGrading_baseChange_piece_eq_bot`: coarsening and parity commute
  with base change, so even support is preserved.
* `TauCeti.LinearMap.IsHomogeneous.baseChange`,
  `TauCeti.LinearMap.IsHomogeneous.baseChange_piece`: base-changing a homogeneous linear map
  preserves its degree.
* `TauCeti.InternalGrading.instGradedMonoidBaseChange`: scalar extension preserves graded monoid
  structures on internal gradings.
* `TauCeti.InternalGrading.dualBaseChange_mem_dualPiece`,
  `TauCeti.InternalGrading.isHomogeneous_dualBaseChange`,
  `TauCeti.InternalGrading.isHomogeneous_restrictScalars_dualBaseChange`: `Module.Dual.baseChange`
  preserves degree.
* `TauCeti.InternalGrading.isHomogeneous_distribBaseChange`,
  `TauCeti.InternalGrading.isHomogeneous_distribBaseChange_symm`: the canonical isomorphism
  `S ⊗[R] (M ⊗[R] N) ≃ₗ[S] (S ⊗[R] M) ⊗[S] (S ⊗[R] N)` and its inverse have degree zero.
-/

public section

open TensorProduct

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

namespace LinearMap.IsHomogeneous

variable {R M N ι : Type*} [CommSemiring R] [AddMonoid ι]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extending scalars of a homogeneous linear map preserves its degree. -/
theorem baseChange {f : M →ₗ[R] N} {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N} {q : ι}
    (hf : LinearMap.IsHomogeneous f ℳ 𝒩 q) (S : Type*) [Semiring S] [Algebra R S] :
    LinearMap.IsHomogeneous (f.baseChange S) (fun p ↦ (ℳ p).baseChange S)
      (fun p ↦ (𝒩 p).baseChange S) q := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  have hle : (ℳ p).baseChange S ≤ ((𝒩 (p + q)).baseChange S).comap (f.baseChange S) :=
    Submodule.baseChange_le_iff_le_comap.mpr fun x hx ↦
      Submodule.tmul_mem_baseChange_of_mem 1 (hf.map_mem hx)
  exact hle hz

end LinearMap.IsHomogeneous

namespace InternalGrading

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

section GeneralIndex

variable [DecidableEq ι]

/-- Scalar extension of an internal grading along a commutative `R`-algebra `S`. -/
noncomputable def baseChange (G : InternalGrading R M ι) (S : Type*) [CommSemiring S]
    [Algebra R S] : InternalGrading S (S ⊗[R] M) ι :=
  ofDecomposition fun p ↦ (G.piece p).baseChange S

/-- The homogeneous pieces of `G.baseChange S` are the scalar extensions of `G.piece`. -/
@[simp]
theorem baseChange_piece (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S] :
    (G.baseChange S).piece = fun p ↦ (G.piece p).baseChange S := by
  simp [baseChange]

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

/-- Homogeneous projection for `G.baseChange S` acts on pure tensors via the second factor. -/
@[simp]
theorem coe_decompose_baseChange_tmul (G : InternalGrading R M ι) (S : Type*) [CommSemiring S]
    [Algebra R S] (s : S) (x : M) (p : ι) :
    (DirectSum.decompose (G.baseChange S).piece (s ⊗ₜ[R] x) p : S ⊗[R] M) =
      s ⊗ₜ[R] (DirectSum.decompose G.piece x p : M) := by
  rw [baseChange, coe_decompose_ofDecomposition_piece_apply,
    DirectSum.coe_decompose_baseChange_tmul]

/-- Coarsening an internal grading commutes with scalar extension. -/
@[simp]
theorem coarsen_baseChange {κ : Type*} [DecidableEq κ] (G : InternalGrading R M ι) (S : Type*)
    [CommSemiring S] [Algebra R S] (f : ι → κ) :
    (G.baseChange S).coarsen f = (G.coarsen f).baseChange S := by
  refine InternalGrading.ext fun k ↦ ?_
  simpa using coarsenGrading_baseChange G.piece S f k

/-- Scalar extension preserves graded monoid compatibility on internal gradings of algebras. -/
instance instGradedMonoidBaseChange {A : Type*} [Semiring A] [Algebra R A] [AddMonoid ι]
    (G : InternalGrading R A ι) [SetLike.GradedMonoid G.piece] (S : Type*) [CommSemiring S]
    [Algebra R S] : SetLike.GradedMonoid (G.baseChange S).piece where
  one_mem := G.tmul_mem_baseChange S 1 (SetLike.one_mem_graded G.piece)
  mul_mem i j u v hu hv := by
    refine G.baseChange_piece_le S
      (C := ((G.baseChange S).piece (i + j)).comap ((_root_.LinearMap.mul S (S ⊗[R] A)).flip v))
      (fun a ha ↦ ?_) hu
    refine G.baseChange_piece_le S
      (C := ((G.baseChange S).piece (i + j)).comap (_root_.LinearMap.mul S (S ⊗[R] A) (1 ⊗ₜ[R] a)))
      (fun b hb ↦ ?_) hv
    simpa using G.tmul_mem_baseChange S 1 (SetLike.mul_mem_graded ha hb)

end GeneralIndex

section IntGrading

/-- Parity pieces of `G.baseChange S` are scalar extensions of the parity pieces of `G`. -/
theorem parityGrading_baseChange_piece (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S]
    [Algebra R S] (i : ZMod 2) :
    parityGrading (G.baseChange S).piece i = (parityGrading G.piece i).baseChange S := by
  rw [baseChange_piece]
  exact coarsenGrading_baseChange G.piece S (Int.castAddHom (ZMod 2)) i

/-- Taking the parity internal grading commutes with scalar extension. -/
@[simp]
theorem parity_baseChange (G : InternalGrading R M ℤ) (S : Type*) [CommSemiring S] [Algebra R S] :
    (G.baseChange S).parity = G.parity.baseChange S := by
  refine InternalGrading.ext fun i ↦ ?_
  rw [parity_piece, G.parityGrading_baseChange_piece S i, G.parity.baseChange_piece S,
    parity_piece]

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
  rw [isHomogeneous_trivialGrading_iff_mem_dualPiece] at hφ ⊢
  exact G.dualBaseChange_mem_dualPiece S hφ

/-- When `S` carries an internal `ℤ`-grading `GS` over `R`, the scalar-extended functional
`Module.Dual.baseChange S φ : S ⊗[R] M →ₗ[S] S` restricted to `R` has degree `d` from
`(GS.tensorProduct G).piece` into `GS.piece`. -/
theorem isHomogeneous_restrictScalars_dualBaseChange (G : InternalGrading R M ℤ) {S : Type*}
    [CommSemiring S] [Algebra R S] (GS : InternalGrading R S ℤ) {φ : Module.Dual R M} {d : ℤ}
    (hφ : LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) d) :
    LinearMap.IsHomogeneous ((Module.Dual.baseChange S φ).restrictScalars R)
      (GS.tensorProduct G).piece GS.piece d := by
  have hφ' := (G.isHomogeneous_trivialGrading_iff_mem_dualPiece φ d).mp hφ
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

/-- The canonical isomorphism `S ⊗[R] (M ⊗[R] N) ≃ₗ[S] (S ⊗[R] M) ⊗[S] (S ⊗[R] N)` has degree zero
for the base-changed total-degree gradings. -/
theorem isHomogeneous_distribBaseChange (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    (S : Type*) [CommSemiring S] [Algebra R S] :
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
  refine G.tensorProduct_piece_le H (C := C'.comap g) (fun p x hx y hy ↦ ?_) ht
  simp only [Submodule.mem_comap, C', Submodule.restrictScalars_mem,
    _root_.LinearMap.comp_apply, _root_.LinearMap.coe_restrictScalars,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, g, e,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have hdeg : n + 0 = p + (n - p) := by omega
  rw [hdeg]
  exact tmul_mem_tensorProduct (G.baseChange S) (H.baseChange S)
    (G.tmul_mem_baseChange S 1 hx) (H.tmul_mem_baseChange S 1 hy)

/-- The inverse of `TensorProduct.AlgebraTensorModule.distribBaseChange` also has degree zero. -/
theorem isHomogeneous_distribBaseChange_symm (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    LinearMap.IsHomogeneous
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).symm.toLinearMap
      ((G.baseChange S).tensorProduct (H.baseChange S)).piece
      ((G.tensorProduct H).baseChange S).piece 0 :=
  (G.isHomogeneous_distribBaseChange H S).linearEquiv_symm

end IntGrading

end InternalGrading

namespace LinearMap.IsHomogeneous

/-- Extending scalars of a homogeneous linear map between internally graded modules preserves its
degree for `InternalGrading.baseChange`. -/
theorem baseChange_piece {R M N ι : Type*} [CommSemiring R] [DecidableEq ι] [AddMonoid ι]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {G : InternalGrading R M ι} {H : InternalGrading R N ι} {f : M →ₗ[R] N} {q : ι}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece q) (S : Type*) [CommSemiring S]
    [Algebra R S] :
    LinearMap.IsHomogeneous (f.baseChange S) (G.baseChange S).piece (H.baseChange S).piece q := by
  simpa using hf.baseChange S

end LinearMap.IsHomogeneous

end TauCeti
