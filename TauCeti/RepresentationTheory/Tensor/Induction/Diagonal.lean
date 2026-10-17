/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Diagonal invariant tensors in tensor induction

An invariant vector of a subgroup representation gives an invariant vector of its tensor
induction: put the same vector in every coset factor. The monomial action fixes this tensor
because its subgroup coordinates fix the vector and its permutation only reorders identical
factors. The resulting function is natural in intertwining maps and agrees under the existing
change-of-transversal comparisons. For finitely many cosets it is homogeneous of degree the
number of cosets, and for one coset it recovers the original vector.

Applied to an invariant element of a coinduced resolution term, this is the diagonal tensor
used on representatives in the multiplicative transfer. This file concerns invariant vectors;
preservation of differentials and descent to cohomology are separate assertions.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

universe u v w y

namespace Representation

variable {R : Type u} [CommRing R] {G : Type v} [Group G] {U : Subgroup G}
  {M : Type w} [AddCommGroup M] [Module R M]

/-- Put an invariant vector in every coset factor of tensor induction. This is a function
between invariant submodules; it need not be additive. -/
noncomputable def tensorInducedDiagonal (ρ : Representation R U M) (s : U.LeftTransversal) :
    ρ.invariants → (U.tensorInducedRepresentation s ρ).invariants := fun x ↦
  ⟨PiTensorProduct.tprod R (fun _ ↦ (x : M)), by
    intro g
    rw [Subgroup.tensorInducedRepresentation_apply_tprod]
    congr 1
    funext i
    exact x.property ((U.monomialHom s g).left i)⟩

/-- The underlying tensor of the invariant diagonal has the same vector in every factor. -/
@[simp] theorem coe_tensorInducedDiagonal (ρ : Representation R U M)
    (s : U.LeftTransversal) (x : ρ.invariants) :
    (ρ.tensorInducedDiagonal s x : ⨂[R] _ : G ⧸ U, M) =
      PiTensorProduct.tprod R (fun _ ↦ (x : M)) := (rfl)

/-- The invariant diagonal sends zero to zero. A coset family is always nonempty. -/
@[simp] theorem tensorInducedDiagonal_zero (ρ : Representation R U M)
    (s : U.LeftTransversal) : ρ.tensorInducedDiagonal s 0 = 0 := by
  apply Subtype.ext
  simp only [coe_tensorInducedDiagonal, Submodule.coe_zero]
  exact (PiTensorProduct.tprod R).map_coord_zero (QuotientGroup.mk (1 : G)) rfl

/-- Scaling an invariant vector scales its diagonal tensor by the scalar raised to the
number of cosets. The caller's finite enumeration of the cosets is retained. -/
@[simp] theorem tensorInducedDiagonal_smul (ρ : Representation R U M) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] (r : R) (x : ρ.invariants) :
    ρ.tensorInducedDiagonal s (r • x) = r ^ Fintype.card (G ⧸ U) •
      ρ.tensorInducedDiagonal s x := by
  apply Subtype.ext
  simpa using (PiTensorProduct.tprod R : MultilinearMap R (fun _ : G ⧸ U ↦ M) _).map_smul_univ
    (fun _ ↦ r) (fun _ ↦ (x : M))

/-- The change-of-transversal comparison fixes the invariant diagonal tensor. -/
theorem tensorInducedChangeTransversal_tensorInducedDiagonal (ρ : Representation R U M)
    (s t : U.LeftTransversal) (x : ρ.invariants) :
    U.tensorInducedChangeTransversal s t ρ (ρ.tensorInducedDiagonal t x) =
      (ρ.tensorInducedDiagonal s x : ⨂[R] _ : G ⧸ U, M) := by
  simp only [coe_tensorInducedDiagonal,
    Subgroup.tensorInducedChangeTransversal_apply_tprod]
  congr 1
  funext i
  exact x.property ((U.monomialChangeTransversal s t).left i)

namespace IntertwiningMap

variable {N : Type y} [AddCommGroup N] [Module R N]
  {ρ : Representation R U M} {τ : Representation R U N}

/-- Tensor induction of an intertwining map carries the invariant diagonal to the diagonal
of its image. The image is read in the target's invariant submodule. -/
theorem tensorInduced_tensorInducedDiagonal (f : ρ.IntertwiningMap τ)
    (s : U.LeftTransversal) (x : ρ.invariants) :
    f.tensorInduced s (ρ.tensorInducedDiagonal s x) =
      (τ.tensorInducedDiagonal s ⟨f x, fun g ↦
        (IntertwiningMap.isIntertwining ρ τ f g x).symm.trans
          (congrArg f (x.property g))⟩ :
          ⨂[R] _ : G ⧸ U, N) := by
  simp only [coe_tensorInducedDiagonal, tensorInduced_apply_tprod]

end IntertwiningMap

end Representation

/-! For the trivial subgroup of `C₂`, the diagonal has two tensor factors. On the trivial
module `𝔽₂²`, the vectors `(1, 0)` and `(0, 1)` witness its failure of additivity. The tensor
functional multiplying the first coordinate of one factor by the second of the other reads
their separate diagonals as zero and the diagonal of their sum as one. -/
example (s : (⊥ : Subgroup (Multiplicative (ZMod 2))).LeftTransversal) :
    let ρ := Representation.trivial (ZMod 2) (⊥ : Subgroup (Multiplicative (ZMod 2)))
      (ZMod 2 × ZMod 2)
    ∃ x y : ρ.invariants, ρ.tensorInducedDiagonal s (x + y) ≠
      ρ.tensorInducedDiagonal s x + ρ.tensorInducedDiagonal s y := by
  classical
  let F := ZMod 2
  let G₂ := Multiplicative F
  let U₂ : Subgroup G₂ := ⊥
  let ρ := Representation.trivial F U₂ (F × F)
  let x : ρ.invariants := ⟨(1, 0), fun _ ↦ rfl⟩
  let y : ρ.invariants := ⟨(0, 1), fun _ ↦ rfl⟩
  refine ⟨x, y, ?_⟩
  let e : G₂ ⧸ U₂ ≃ Fin 2 := QuotientGroup.quotientBot.toEquiv.trans
    (Multiplicative.toAdd.trans (ZMod.finEquiv 2).toEquiv.symm)
  let μ : MultilinearMap F (fun _ : G₂ ⧸ U₂ ↦ F × F) F :=
    (MultilinearMap.mkPiAlgebra F (G₂ ⧸ U₂) F).compLinearMap fun i ↦
      if e i = 0 then LinearMap.fst F F F else LinearMap.snd F F F
  let L := PiTensorProduct.lift μ
  have hx : L (ρ.tensorInducedDiagonal s x) = 0 := by
    simp [L, μ, x, MultilinearMap.mkPiAlgebra_apply, ← Equiv.prod_comp e.symm]
  have hy : L (ρ.tensorInducedDiagonal s y) = 0 := by
    simp [L, μ, y, MultilinearMap.mkPiAlgebra_apply, ← Equiv.prod_comp e.symm]
  have hxy : L (ρ.tensorInducedDiagonal s (x + y)) = 1 := by
    simp only [L, Representation.coe_tensorInducedDiagonal, PiTensorProduct.lift.tprod]
    have hv : ∀ i, (if e i = 0 then LinearMap.fst F F F else LinearMap.snd F F F)
        ((x + y : ρ.invariants) : F × F) = 1 := by
      intro i
      split_ifs <;> simp [x, y]
    simp only [μ, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      hv, Finset.prod_const_one]
  intro h
  have he := congrArg (fun z : (U₂.tensorInducedRepresentation s ρ).invariants ↦ L z.val) h
  have he' : L (ρ.tensorInducedDiagonal s (x + y)) =
      L (ρ.tensorInducedDiagonal s x) + L (ρ.tensorInducedDiagonal s y) := by
    simpa only [Submodule.coe_add, map_add] using he
  rw [hxy, hx, hy, zero_add] at he'
  exact one_ne_zero he'
