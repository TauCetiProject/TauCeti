/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Resolution
public import TauCeti.LinearAlgebra.PiTensorProduct.Pairing

/-!
# The cup pairing on tensor-induced resolutions

Apply the total Alexander–Whitney cup in each coset factor to pair two tensor-induced
resolutions. The resulting bilinear map is equivariant, adds total degrees, extends the
factorwise coefficient pairing along augmentation, and satisfies the unsigned Leibniz rule
when the target coefficients have exponent two.

On diagonal tensors of homogeneous cochains the pairing gives the diagonal tensor of their
cup. This is the representative formula needed to compare multiplicative cohomological norms
and cups. This file constructs the resolution-level pairing, not an identity of cohomology
classes. It uses the underlying tensor modules and their tensor-induced actions: smoothness
and compactness are not needed for the algebraic identities. For smooth discrete coefficients,
the slot sums here are precisely the differentials of the smooth tensor-induced resolutions.

For example, with two cosets and trivial `𝔽₂` coefficients, let `e` be the augmentation of `1`
in the total resolution. Since `1 · 1 = 1`, the pairing sends `(e ⊗ e, e ⊗ e)` to `e ⊗ e`.
Each factor has degree zero and differential zero, so the result does too.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §§2–6.
* K. S. Brown, *Cohomology of Groups*, Chapter V, §3, for the Alexander–Whitney pairing.
-/

public section

namespace TauCeti.TopPairing

open CategoryTheory
open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] {U : Subgroup G}
  [TopologicalSpace U] [IsTopologicalGroup U]
  {X Y Z : TopRep.{max v w} R U} (P : TopPairing X Y Z)

/-- The factorwise Alexander–Whitney cup on the underlying modules of tensor-induced total
resolutions. The bilinear map is independent of the transversal used for their actions. -/
noncomputable def tensorInducedGradedResolutionCupPairing :
    (⨂[R] _ : G ⧸ U, X.gradedResolutionModule) →ₗ[R]
      (⨂[R] _ : G ⧸ U, Y.gradedResolutionModule) →ₗ[R]
        ⨂[R] _ : G ⧸ U, Z.gradedResolutionModule :=
  PiTensorProduct.map₂ fun _ ↦ P.gradedResolutionCupPairing

/-- The induced cup is the factorwise pairing `PiTensorProduct.map₂` of the total cup. -/
theorem tensorInducedGradedResolutionCupPairing_def :
    P.tensorInducedGradedResolutionCupPairing (G := G) (U := U) =
      PiTensorProduct.map₂ fun _ ↦ P.gradedResolutionCupPairing :=
  (rfl)

/-- On pure tensors the induced cup applies the total cup in every coset factor. -/
@[simp]
theorem tensorInducedGradedResolutionCupPairing_tprod
    (a : G ⧸ U → X.gradedResolutionModule) (b : G ⧸ U → Y.gradedResolutionModule) :
    P.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.tprod R a) (PiTensorProduct.tprod R b) =
      PiTensorProduct.tprod R fun i ↦ P.gradedResolutionCupPairing (a i) (b i) :=
  PiTensorProduct.map₂_tprod_tprod _ a b

/-- The tensor-induced cup is equivariant for the ambient group, including its permutation
of the coset factors, for every transversal. -/
theorem tensorInducedGradedResolutionCupPairing_ρ (s : U.LeftTransversal) (g : G)
    (a : ⨂[R] _ : G ⧸ U, X.gradedResolutionModule)
    (b : ⨂[R] _ : G ⧸ U, Y.gradedResolutionModule) :
    P.tensorInducedGradedResolutionCupPairing
        (U.tensorInducedRepresentation s X.gradedResolutionRepresentation g a)
        (U.tensorInducedRepresentation s Y.gradedResolutionRepresentation g b) =
      U.tensorInducedRepresentation s Z.gradedResolutionRepresentation g
        (P.tensorInducedGradedResolutionCupPairing a b) :=
  U.map₂_tensorInducedRepresentation s _ P.gradedResolutionCupPairing_ρ g a b

/-- The induced cup extends the factorwise coefficient pairing along the tensor powers
of the augmentations. -/
@[simp]
theorem tensorInducedGradedResolutionCupPairing_augmentation
    (a : ⨂[R] _ : G ⧸ U, X.V) (b : ⨂[R] _ : G ⧸ U, Y.V) :
    P.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.map (fun _ : G ⧸ U ↦ X.gradedResolutionAugmentation) a)
        (PiTensorProduct.map (fun _ : G ⧸ U ↦ Y.gradedResolutionAugmentation) b) =
      PiTensorProduct.map (fun _ : G ⧸ U ↦ Z.gradedResolutionAugmentation)
        (PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ P.bil) a b) :=
  (PiTensorProduct.map_map₂ _ _ _ _ _
    (fun _ x y ↦ (P.gradedResolutionCupPairing_augmentation x y).symm) a b).symm

/-- Tensor powers of coefficient maps compatible with a pairing preserve the induced cup. -/
theorem tensorInducedGradedResolutionCupPairing_naturality
    {X' Y' Z' : TopRep.{max v w} R U} (P' : TopPairing X' Y' Z')
    (fX : X ⟶ X') (fY : Y ⟶ Y') (fZ : Z ⟶ Z')
    (hpair : ∀ (x : X.V) (y : Y.V), fZ (P.bil x y) = P'.bil (fX x) (fY y))
    (a : ⨂[R] _ : G ⧸ U, X.gradedResolutionModule)
    (b : ⨂[R] _ : G ⧸ U, Y.gradedResolutionModule) :
    PiTensorProduct.map (fun _ : G ⧸ U ↦
        TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) fZ)
        (P.tensorInducedGradedResolutionCupPairing a b) =
      P'.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.map (fun _ : G ⧸ U ↦
          TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) fX) a)
        (PiTensorProduct.map (fun _ : G ⧸ U ↦
          TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) fY) b) :=
  PiTensorProduct.map_map₂ _ _ _ _ _ (fun _ ↦
    P.gradedResolutionCupPairing_gradedResolutionMap P' (ContinuousMonoidHom.id U)
      fX fY fZ hpair) a b

/-- Pairing the diagonal tensors of two homogeneous cochains gives the diagonal tensor of
their canonical homogeneous-cochain cup. -/
theorem tensorInducedGradedResolutionCupPairing_diagonal (m n : ℕ)
    (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X n) :
    P.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ X.cochainToGradedResolution m a)
        (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ Y.cochainToGradedResolution n b) =
      PiTensorProduct.tprod R fun _ : G ⧸ U ↦
        Z.cochainToGradedResolution (m + n) (P.cupCochain m n a b) := by
  rw [tensorInducedGradedResolutionCupPairing_tprod]
  exact congrArg (PiTensorProduct.tprod R) (funext fun _ ↦
    P.gradedResolutionCupPairing_cochainToGradedResolution m n a b)

variable [Fintype (G ⧸ U)]

/-- The tensor-induced cup adds the total degrees, including the zero negative-degree pieces. -/
theorem tensorInducedGradedResolutionCupPairing_mem {m n : ℤ}
    {a : ⨂[R] _ : G ⧸ U, X.gradedResolutionModule}
    {b : ⨂[R] _ : G ⧸ U, Y.gradedResolutionModule}
    (ha : a ∈ PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ X.gradedResolutionPiece) m)
    (hb : b ∈ PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ Y.gradedResolutionPiece) n) :
    P.tensorInducedGradedResolutionCupPairing a b ∈
      PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ Z.gradedResolutionPiece) (m + n) :=
  PiTensorProduct.map₂_mem_totalDegreePiece _ _ _ _
    (fun _ _ _ _ _ ↦ P.gradedResolutionCupPairing_mem) ha hb

/-- For exponent-two target coefficients, the tensor-induced cup satisfies the unsigned
Leibniz rule for the slot-sum differentials of the tensor-induced resolutions. -/
theorem tensorInducedGradedResolutionCupPairing_leibniz [DecidableEq (G ⧸ U)]
    (hZ : ∀ z : Z.V, z + z = 0)
    (a : ⨂[R] _ : G ⧸ U, X.gradedResolutionModule)
    (b : ⨂[R] _ : G ⧸ U, Y.gradedResolutionModule) :
    PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ Z.gradedResolutionDifferential)
        (P.tensorInducedGradedResolutionCupPairing a b) =
      P.tensorInducedGradedResolutionCupPairing
          (PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ X.gradedResolutionDifferential) a) b +
        P.tensorInducedGradedResolutionCupPairing a
          (PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ Y.gradedResolutionDifferential) b) :=
  PiTensorProduct.slotSum_map₂ _ _ _ _
    (fun _ ↦ P.gradedResolutionCupPairing_leibniz_of_add_self_eq_zero hZ) a b

end TauCeti.TopPairing
