/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Complex

/-!
# Equivariant tensor differentials

A differential commuting with a group representation induces a differential commuting with its
finite wreath tensor representation and hence with tensor induction along a subgroup. In
characteristic two the induced differential squares to zero. If the original action preserves
a grading, both actions preserve each total-degree piece `PiTensorProduct.degreePiece`.

These identities supply the permutation-compatible differential for tensor induction of
complexes. The ground ring need not have characteristic two for equivariance or preservation of
degree; that hypothesis enters only the square-zero law without Koszul signs.

## Main definitions and lemmas

* `TauCeti.wreathTensorDifferential d ι`: the equivariant
  differential on a finite tensor power.
* `TauCeti.tensorInducedDifferential d s`: its restriction along
  a transversal's monomial map.
* `TauCeti.wreathTensor_mem_degreePiece ρ ι`: preservation of total degree by
  the wreath action.
* `TauCeti.tensorInducedRepresentation_mem_degreePiece U s τ`: preservation of total
  degree by tensor induction.

Open `TauCeti` and write `wreathTensorDifferential d ι` or `tensorInducedDifferential d s`
to construct the differentials. The action lemmas likewise take their representation or
subgroup as an explicit argument.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

universe u v w x

namespace TauCeti

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] {ρ : Representation R D M}
  (d : ρ.IntertwiningMap ρ) (ι : Type x) [Fintype ι]

/-- The finite tensor differential, bundled as an endomorphism of the wreath tensor
representation. It applies the original endomorphism in one factor at a time and sums. -/
noncomputable def wreathTensorDifferential :
    (ρ.wreathTensor ι).IntertwiningMap (ρ.wreathTensor ι) where
  toLinearMap := TauCeti.PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap)
  isIntertwining' a := by
    rw [wreathTensor_apply, ← LinearMap.comp_assoc,
      TauCeti.PiTensorProduct.differential_comp_map _ _ _ (fun i ↦ d.isIntertwining' (a.left i)),
      LinearMap.comp_assoc,
      TauCeti.PiTensorProduct.differential_comp_reindex a.right (fun _ ↦ d.toLinearMap),
      LinearMap.comp_assoc]

/-- The underlying map of the wreath tensor differential is the finite tensor differential. -/
@[simp]
theorem wreathTensorDifferential_toLinearMap :
    (wreathTensorDifferential d ι).toLinearMap =
      TauCeti.PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap) :=
  (rfl)

/-- The wreath tensor differential replaces one pure-tensor factor at a time. -/
@[simp]
theorem wreathTensorDifferential_apply_tprod [DecidableEq ι] (x : ι → M) :
    wreathTensorDifferential d ι (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) := by
  exact TauCeti.PiTensorProduct.differential_tprod (fun _ ↦ d.toLinearMap) x

/-- The induced differential squares to zero in characteristic two. -/
theorem wreathTensorDifferential_comp_self [CharP R 2]
    (hd : d.comp d = 0) :
    (wreathTensorDifferential d ι).comp (wreathTensorDifferential d ι) = 0 := by
  apply Representation.IntertwiningMap.ext
  exact TauCeti.PiTensorProduct.differential_comp_self _
    (fun _ ↦ congrArg Representation.IntertwiningMap.toLinearMap hd)

variable {G : Type*} [Group G] {U : Subgroup G}
  {τ : Representation R U M}

/-- The finite tensor differential on the tensor-induced representation, obtained by
restricting the wreath tensor differential along the monomial homomorphism. -/
noncomputable def tensorInducedDifferential (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedRepresentation s τ).IntertwiningMap
      (U.tensorInducedRepresentation s τ) where
  toLinearMap := (wreathTensorDifferential d (G ⧸ U)).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Subgroup.tensorInducedRepresentation_apply]
    exact LinearMap.congr_fun
      ((wreathTensorDifferential d (G ⧸ U)).isIntertwining' (U.monomialHom s g)) z

/-- Tensor induction uses the finite tensor differential on the coset-indexed tensor power. -/
@[simp]
theorem tensorInducedDifferential_toLinearMap (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (tensorInducedDifferential d s).toLinearMap =
      TauCeti.PiTensorProduct.differential (fun _ : G ⧸ U ↦ d.toLinearMap) :=
  (rfl)

/-- The tensor-induced differential replaces one coset-indexed pure-tensor factor at a time. -/
@[simp]
theorem tensorInducedDifferential_apply_tprod (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (x : G ⧸ U → M) :
    tensorInducedDifferential d s (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) :=
  wreathTensorDifferential_apply_tprod d (G ⧸ U) x

/-- The tensor-induced differential squares to zero in characteristic two. -/
theorem tensorInducedDifferential_comp_self [CharP R 2] (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] (hd : d.comp d = 0) :
    (tensorInducedDifferential d s).comp (tensorInducedDifferential d s) = 0 := by
  apply Representation.IntertwiningMap.ext
  simpa only [Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.zero_toLinearMap, tensorInducedDifferential_toLinearMap,
    wreathTensorDifferential_toLinearMap] using
    congrArg Representation.IntertwiningMap.toLinearMap
      (wreathTensorDifferential_comp_self d (G ⧸ U) hd)

end TauCeti

namespace TauCeti

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] (ρ : Representation R D M)
  (ι : Type x) [Fintype ι]

/-- A grading-preserving action gives a wreath tensor action preserving total tensor degree. -/
theorem wreathTensor_mem_degreePiece (ℳ : ℤ → Submodule R M)
    (hρ : ∀ g, LinearMap.IsHomogeneous (ρ g) ℳ ℳ 0)
    (a : WreathProduct D ι) {n : ℤ} {z : ⨂[R] _ : ι, M}
    (hz : z ∈ PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n) :
    ρ.wreathTensor ι a z ∈ PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n := by
  rw [wreathTensor_apply, LinearMap.comp_apply]
  exact PiTensorProduct.map_mem_degreePiece _ _ _ (fun i ↦ hρ (a.left i))
    (PiTensorProduct.reindex_mem_degreePiece a.right (fun _ ↦ ℳ) hz)

end TauCeti

namespace TauCeti

variable {R : Type u} [CommSemiring R] {M : Type w} [AddCommMonoid M] [Module R M]

/-- A grading-preserving subgroup action gives a tensor-induced action preserving total degree. -/
theorem tensorInducedRepresentation_mem_degreePiece {G : Type v} [Group G]
    (U : Subgroup G) (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (τ : Representation R U M) (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0)
    (g : G) {n : ℤ} {z : ⨂[R] _ : G ⧸ U, M}
    (hz : z ∈ PiTensorProduct.degreePiece (fun _ : G ⧸ U ↦ ℳ) n) :
    U.tensorInducedRepresentation s τ g z ∈
      PiTensorProduct.degreePiece (fun _ : G ⧸ U ↦ ℳ) n := by
  rw [Subgroup.tensorInducedRepresentation_apply]
  exact wreathTensor_mem_degreePiece τ (G ⧸ U) ℳ hτ
    (U.monomialHom s g) hz

end TauCeti
