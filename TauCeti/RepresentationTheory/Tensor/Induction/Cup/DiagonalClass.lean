/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Cup.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Contraction

/-!
# Cup products of tensor-induced diagonal classes

Let `U` be a compact open finite-index subgroup of a topological group `G` with `l` cosets, and
let `P : A × B → C` be a coefficient pairing of smooth discrete `U`-representations in which every
element is its own additive inverse. For a cocycle `z` of the total resolution of `A`, the class
`TauCeti.smoothTensorInducedDiagonalClass` of its diagonal tensor `z ⊗ ⋯ ⊗ z` is Evens' norm of
`z`. This file proves that the norm is multiplicative on cocycles: the norm of the cup `z ⌣ z'`
is the cup product of the norms, for the pairing `TauCeti.TopPairing.smoothTensorInduced` of the
tensor inductions that applies `P` in every coset factor
(`TauCeti.smoothTensorInducedDiagonalClass_gradedResolutionCupPairing`).

The factorwise cup of the tensor-induced resolutions pairs diagonal tensors to diagonal tensors,
so the theorem amounts to computing the class of a factorwise product. The contraction of the
tensor-induced resolution is not multiplicative, but pairing on the left with a tensor of
augmented coefficients commutes with its retraction and with its slot homotopy
(`TauCeti.smoothTensorInducedGradedResolutionProjection_tensorInducedGradedResolutionCupPairing`,
`TauCeti.smoothTensorInducedGradedResolutionHomotopy_tensorInducedGradedResolutionCupPairing`),
because in each factor the contraction of the total resolution commutes with the cup with an
augmented coefficient. This is what `TopRep.ResolutionContraction.gradedCohomologyClass_pairing`
needs to identify the class of a product with the cup product of the classes.

## Main definitions

* `TauCeti.TopPairing.smoothTensorInducedGradedResolutionCupPairing`: the factorwise cup, read on
  the carriers of the smooth tensor-induced total resolutions.

## Main results

* `TauCeti.gradedCohomologyClass_smoothTensorInducedGradedResolutionCupPairing`: the class of the
  factorwise cup of two invariant cocycles of the tensor-induced resolutions is the cup product of
  their classes.
* `TauCeti.smoothTensorInducedDiagonalClass_gradedResolutionCupPairing`: the norm of a cup of
  cocycles is the cup product of their norms, read in degree `l m + l n = l (m + n)`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. **108** (1963), §6, Proposition 1, for the multiplicativity of the norm.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the cup
  product and its independence of the resolution.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U]
  {A B C : SmoothDiscreteTopRep.{u, v, max v w} R U} (P : TopPairing A.obj B.obj C.obj)

/-! ### Left multiplication by augmented tensors and the contraction -/

section Contraction

variable [Fintype (G ⧸ U)]

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] [Fintype (G ⧸ U)] in
/-- The projection of the tensor-induced total resolution carries the induced cup with a tensor
of augmented coefficients `x` on the left to the factorwise coefficient pairing of `x` with the
projection. -/
theorem smoothTensorInducedGradedResolutionProjection_tensorInducedGradedResolutionCupPairing
    (x : ⨂[R] _ : G ⧸ U, A.obj.V) (w : ⨂[R] _ : G ⧸ U, B.obj.gradedResolutionModule) :
    smoothTensorInducedGradedResolutionProjection U C
        (P.tensorInducedGradedResolutionCupPairing
          (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) w) =
      PiTensorProduct.map₂ (fun _ ↦ P.bil) x
        (smoothTensorInducedGradedResolutionProjection U B w) := by
  -- absorb the augmentation into the factor pairing, then project factorwise
  have h := PiTensorProduct.map_map₂
    (fun _ ↦ P.gradedResolutionCupPairing ∘ₗ A.obj.gradedResolutionAugmentation)
    (fun _ ↦ P.gradedResolutionCupPairing) (fun _ ↦ A.obj.gradedResolutionAugmentation)
    (fun _ ↦ LinearMap.id) (fun _ ↦ LinearMap.id) (fun _ _ _ ↦ rfl) x w
  rw [PiTensorProduct.map_id, PiTensorProduct.map_id, LinearMap.id_apply, LinearMap.id_apply] at h
  rw [TopPairing.tensorInducedGradedResolutionCupPairing_def, ← h,
    smoothTensorInducedGradedResolutionProjection_def,
    smoothTensorInducedGradedResolutionProjection_def,
    PiTensorProduct.map_map₂ _ (fun _ ↦ P.bil) (fun _ ↦ LinearMap.id) _ _
      (fun _ ↦ P.gradedResolutionProjection_gradedResolutionCupPairing_augmentation),
    PiTensorProduct.map_id, LinearMap.id_apply]

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] in
/-- The contracting homotopy of the tensor-induced total resolution commutes with the induced cup
with a tensor of augmented coefficients on the left. -/
theorem smoothTensorInducedGradedResolutionHomotopy_tensorInducedGradedResolutionCupPairing
    [LinearOrder (G ⧸ U)] (x : ⨂[R] _ : G ⧸ U, A.obj.V)
    (w : ⨂[R] _ : G ⧸ U, B.obj.gradedResolutionModule) :
    smoothTensorInducedGradedResolutionHomotopy U C
        (P.tensorInducedGradedResolutionCupPairing
          (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) w) =
      P.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x)
        (smoothTensorInducedGradedResolutionHomotopy U B w) := by
  rw [smoothTensorInducedGradedResolutionHomotopy_def,
    smoothTensorInducedGradedResolutionHomotopy_def,
    TopPairing.tensorInducedGradedResolutionCupPairing_def]
  exact PiTensorProduct.slotHomotopy_map₂_map _ _
    (e := B.obj.gradedResolutionAugmentation ∘ₗ B.obj.gradedResolutionProjection)
    (e' := C.obj.gradedResolutionAugmentation ∘ₗ C.obj.gradedResolutionProjection)
    (fun m n ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        P.gradedResolutionProjection_gradedResolutionCupPairing_augmentation,
        P.gradedResolutionCupPairing_augmentation])
    P.gradedResolutionHomotopy_gradedResolutionCupPairing_augmentation x w

end Contraction

/-! ### The norm of a cup product -/

/-- **The induced cup on the tensor-induced total resolutions**: the factorwise cup
`TopPairing.tensorInducedGradedResolutionCupPairing`, read on the carriers of the smooth
tensor-induced total resolutions, so that it pairs their elements with no change of type. -/
noncomputable def TopPairing.smoothTensorInducedGradedResolutionCupPairing :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V →ₗ[R]
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V →ₗ[R]
        ((smoothTensorInducedGradedResolutionFunctor U hU s).obj C).obj.V :=
  P.tensorInducedGradedResolutionCupPairing

/-- The induced cup on the tensor-induced total resolutions is the factorwise cup. -/
theorem TopPairing.smoothTensorInducedGradedResolutionCupPairing_apply
    (a : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V)
    (b : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V) :
    P.smoothTensorInducedGradedResolutionCupPairing U hU s a b =
      P.tensorInducedGradedResolutionCupPairing a b :=
  (rfl)

/-- The induced cup of two diagonal tensors is the diagonal tensor of the cup. -/
@[simp]
theorem TopPairing.smoothTensorInducedGradedResolutionCupPairing_tprod_const
    (z : A.obj.gradedResolutionModule) (z' : B.obj.gradedResolutionModule) :
    P.smoothTensorInducedGradedResolutionCupPairing U hU s
        (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ z) (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ z') =
      PiTensorProduct.tprod R fun _ : G ⧸ U ↦ P.gradedResolutionCupPairing z z' :=
  P.tensorInducedGradedResolutionCupPairing_tprod _ _

/-- The induced cup on the tensor-induced total resolutions is equivariant. -/
theorem TopPairing.smoothTensorInducedGradedResolutionCupPairing_ρ (g : G)
    (a : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V)
    (b : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V) :
    P.smoothTensorInducedGradedResolutionCupPairing U hU s
        (((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g a)
        (((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.ρ g b) =
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj C).obj.ρ g
        (P.smoothTensorInducedGradedResolutionCupPairing U hU s a b) :=
  (congrArg₂ (fun a b ↦ P.tensorInducedGradedResolutionCupPairing a b)
    (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply' U hU s A g a)
    (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply' U hU s B g b)).trans
      ((P.tensorInducedGradedResolutionCupPairing_ρ s g a b).trans
        (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply' U hU s C g _).symm)

variable [Fintype (G ⧸ U)]

/-- The induced cup on the tensor-induced total resolutions adds total degrees. -/
theorem TopPairing.smoothTensorInducedGradedResolutionCupPairing_mem {p q : ℤ}
    {a : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V}
    {b : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V}
    (ha : a ∈ smoothTensorInducedGradedResolutionPiece U hU s A p)
    (hb : b ∈ smoothTensorInducedGradedResolutionPiece U hU s B q) :
    P.smoothTensorInducedGradedResolutionCupPairing U hU s a b ∈
      smoothTensorInducedGradedResolutionPiece U hU s C (p + q) :=
  P.tensorInducedGradedResolutionCupPairing_mem ha hb

/-- In characteristic two, the differential of the tensor-induced total resolution applied to an
induced cup with a cocycle on the right differentiates the left factor. -/
theorem TopPairing.smoothTensorInducedGradedResolutionDifferential_cupPairing
    (hC : ∀ c : C.obj.V, c + c = 0)
    (a : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V)
    (b : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V)
    (hb : (smoothTensorInducedGradedResolutionDifferential U hU s B).hom.hom b = 0) :
    (smoothTensorInducedGradedResolutionDifferential U hU s C).hom.hom
        (P.smoothTensorInducedGradedResolutionCupPairing U hU s a b) =
      P.smoothTensorInducedGradedResolutionCupPairing U hU s
        ((smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom a) b := by
  classical
  have hb' := (smoothTensorInducedGradedResolutionDifferential_apply U hU s B b).symm.trans hb
  refine (smoothTensorInducedGradedResolutionDifferential_apply U hU s C _).trans ?_
  refine ((P.tensorInducedGradedResolutionCupPairing_leibniz hC a b).trans ?_).trans
    (congrArg (fun a' ↦ P.tensorInducedGradedResolutionCupPairing a' b)
      (smoothTensorInducedGradedResolutionDifferential_apply U hU s A a).symm)
  rw [hb']
  exact (congrArg (_ + ·) (map_zero _)).trans (add_zero _)

variable [LinearOrder (G ⧸ U)]

/-- The retraction of the contraction of the tensor-induced total resolution of `C` carries the
induced cup with an augmented element on the left to the tensor-induced coefficient pairing. -/
private theorem smoothTensorInducedGradedResolutionContraction_proj_cupPairing
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0)
    (hC : ∀ c : C.obj.V, c + c = 0)
    (x : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V)
    (w : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V)
    (hw : w ∈ smoothTensorInducedGradedResolutionPiece U hU s B (0 : ℕ))
    (hxw : P.smoothTensorInducedGradedResolutionCupPairing U hU s
      ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w ∈
        smoothTensorInducedGradedResolutionPiece U hU s C (0 : ℕ)) :
    (smoothTensorInducedGradedResolutionContraction U hU s C hC).proj
        ⟨P.smoothTensorInducedGradedResolutionCupPairing U hU s
          ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w, hxw⟩ =
      (P.smoothTensorInduced U hU s).bil x
        ((smoothTensorInducedGradedResolutionContraction U hU s B hB).proj ⟨w, hw⟩) := calc
  _ = smoothTensorInducedGradedResolutionProjection U C
        (P.tensorInducedGradedResolutionCupPairing
          ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w) :=
      smoothTensorInducedGradedResolutionContraction_proj_apply U hU s C hC _
  _ = smoothTensorInducedGradedResolutionProjection U C
        (P.tensorInducedGradedResolutionCupPairing
          (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) w) := by
      rw [smoothTensorInducedGradedResolutionContraction_ι_apply]
  _ = PiTensorProduct.map₂ (fun _ ↦ P.bil) x
        (smoothTensorInducedGradedResolutionProjection U B w) :=
      smoothTensorInducedGradedResolutionProjection_tensorInducedGradedResolutionCupPairing U P x w
  _ = _ := (congrArg _
      (smoothTensorInducedGradedResolutionContraction_proj_apply U hU s B hB ⟨w, hw⟩).symm).trans
      (LinearMap.congr_fun₂ (P.smoothTensorInduced_bil U hU s).symm _ _)

/-- The contracting homotopy of the contraction of the tensor-induced total resolution of `C`
commutes with the induced cup with an augmented element on the left. -/
private theorem smoothTensorInducedGradedResolutionContraction_hom_cupPairing
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0)
    (hC : ∀ c : C.obj.V, c + c = 0) (q : ℕ)
    (x : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V)
    (w : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V)
    (hw : w ∈ smoothTensorInducedGradedResolutionPiece U hU s B (q + 1 : ℕ))
    (hxw : P.smoothTensorInducedGradedResolutionCupPairing U hU s
      ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w ∈
        smoothTensorInducedGradedResolutionPiece U hU s C (q + 1 : ℕ)) :
    ((smoothTensorInducedGradedResolutionContraction U hU s C hC).hom q
        ⟨P.smoothTensorInducedGradedResolutionCupPairing U hU s
          ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w, hxw⟩).1 =
      P.smoothTensorInducedGradedResolutionCupPairing U hU s
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1
        ((smoothTensorInducedGradedResolutionContraction U hU s B hB).hom q ⟨w, hw⟩).1 := calc
  _ = smoothTensorInducedGradedResolutionHomotopy U C
        (P.tensorInducedGradedResolutionCupPairing
          ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 w) :=
      smoothTensorInducedGradedResolutionContraction_hom_apply U hU s C hC q _
  _ = smoothTensorInducedGradedResolutionHomotopy U C
        (P.tensorInducedGradedResolutionCupPairing
          (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) w) := by
      rw [smoothTensorInducedGradedResolutionContraction_ι_apply]
  _ = P.tensorInducedGradedResolutionCupPairing
        (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x)
        (smoothTensorInducedGradedResolutionHomotopy U B w) :=
      smoothTensorInducedGradedResolutionHomotopy_tensorInducedGradedResolutionCupPairing U P x w
  _ = _ := congrArg₂ (fun a b ↦ P.tensorInducedGradedResolutionCupPairing a b)
      (smoothTensorInducedGradedResolutionContraction_ι_apply U hU s A hA x).symm
      (smoothTensorInducedGradedResolutionContraction_hom_apply U hU s B hB q ⟨w, hw⟩).symm

/-- **The class of an induced cup is the cup product of the classes.** For an order on the cosets,
the class through the contraction of the tensor-induced total resolution of the induced cup of two
homogeneous `G`-invariant cocycles is the cup product, for the tensor-induced coefficient pairing,
of their classes. -/
theorem gradedCohomologyClass_smoothTensorInducedGradedResolutionCupPairing
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0)
    (hC : ∀ c : C.obj.V, c + c = 0) {p q : ℕ}
    {a : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V}
    (ha : a ∈ smoothTensorInducedGradedResolutionPiece U hU s A p)
    (hainv : ∀ g, ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g a = a)
    (hda : (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom a = 0)
    {b : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.V}
    (hb : b ∈ smoothTensorInducedGradedResolutionPiece U hU s B q)
    (hbinv : ∀ g, ((smoothTensorInducedGradedResolutionFunctor U hU s).obj B).obj.ρ g b = b)
    (hdb : (smoothTensorInducedGradedResolutionDifferential U hU s B).hom.hom b = 0) :
    (smoothTensorInducedGradedResolutionContraction U hU s C hC).gradedCohomologyClass
        (P.smoothTensorInducedGradedResolutionCupPairing U hU s a b)
        (by
          rw [Nat.cast_add]
          exact P.smoothTensorInducedGradedResolutionCupPairing_mem U hU s ha hb)
        (fun g ↦ by rw [← P.smoothTensorInducedGradedResolutionCupPairing_ρ, hainv, hbinv])
        (by rw [P.smoothTensorInducedGradedResolutionDifferential_cupPairing U hU s hC a b hdb, hda,
          LinearMap.map_zero₂]) =
      (P.smoothTensorInduced U hU s).cup p q
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).gradedCohomologyClass a ha
          hainv hda)
        ((smoothTensorInducedGradedResolutionContraction U hU s B hB).gradedCohomologyClass b hb
          hbinv hdb) :=
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace U›).locallyCompactSpace_of_mem_nhds_of_group
      (hU.mem_nhds U.one_mem)
  (smoothTensorInducedGradedResolutionContraction U hU s A hA).gradedCohomologyClass_pairing
    (smoothTensorInducedGradedResolutionContraction U hU s B hB)
    (smoothTensorInducedGradedResolutionContraction U hU s C hC) (P.smoothTensorInduced U hU s)
    (P.smoothTensorInducedGradedResolutionCupPairing U hU s)
    (P.smoothTensorInducedGradedResolutionCupPairing_mem U hU s)
    (P.smoothTensorInducedGradedResolutionCupPairing_ρ U hU s)
    (fun b ↦ by
      have := ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).property.discreteTopology
      exact continuous_of_discreteTopology)
    (P.smoothTensorInducedGradedResolutionDifferential_cupPairing U hU s hC)
    (smoothTensorInducedGradedResolutionContraction_proj_cupPairing U hU s P hA hB hC)
    (smoothTensorInducedGradedResolutionContraction_hom_cupPairing U hU s P hA hB hC)
    ha hainv hda hb hbinv hdb

omit [LinearOrder (G ⧸ U)]

/-- **The norm of a cup product is the cup product of the norms.** Let `P : A × B → C` be a
coefficient pairing of smooth discrete `U`-representations of characteristic two, and let `z` and
`z'` be `U`-invariant cocycles of degrees `m` and `n` of their total resolutions. Then the class of
the diagonal tensor of `z ⌣ z'` is the cup product, for the tensor-induced pairing, of the classes
of the diagonal tensors of `z` and `z'`, read in degree `l m + l n = l (m + n)`. -/
theorem smoothTensorInducedDiagonalClass_gradedResolutionCupPairing
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0)
    (hC : ∀ c : C.obj.V, c + c = 0) {m n : ℕ} {z : A.obj.gradedResolutionModule}
    (hz : z ∈ A.obj.gradedResolutionPiece m) (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0) {z' : B.obj.gradedResolutionModule}
    (hz' : z' ∈ B.obj.gradedResolutionPiece n)
    (hinv' : ∀ u, B.obj.gradedResolutionTopRep.ρ u z' = z')
    (hdz' : B.obj.gradedResolutionDifferential z' = 0) :
    smoothTensorInducedDiagonalClass.{u, v, w} U hU s C hC (P.gradedResolutionCupPairing z z')
        (by rw [Nat.cast_add]; exact P.gradedResolutionCupPairing_mem hz hz')
        (fun u ↦ by
          rw [TopRep.gradedResolutionTopRep_ρ_apply, ← P.gradedResolutionCupPairing_ρ,
            ← TopRep.gradedResolutionTopRep_ρ_apply, ← TopRep.gradedResolutionTopRep_ρ_apply,
            hinv, hinv'])
        (P.gradedResolutionDifferential_cup_eq_zero hz hz' hdz hdz') =
      (ContinuousCohomology.degreeCast _ (mul_add _ m n).symm).hom
        ((P.smoothTensorInduced U hU s).cup _ _
          (smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z hz hinv hdz)
          (smoothTensorInducedDiagonalClass.{u, v, w} U hU s B hB z' hz' hinv' hdz')) := by
  let : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  -- the diagonal tensor of the cup is the induced cup of the diagonal tensors, in equal degrees
  have e := (smoothTensorInducedGradedResolutionContraction U hU s C hC
    ).gradedCohomologyClass_degreeCast (mul_add (Fintype.card (G ⧸ U)) m n).symm
    (P.smoothTensorInducedGradedResolutionCupPairing_tprod_const U hU s z z').symm
  exact ((smoothTensorInducedDiagonalClass_eq U hU s C hC _ _ _ _).trans (e _ _ _ _ _ _)).trans
    (congrArg (ContinuousCohomology.degreeCast _ _).hom
      ((gradedCohomologyClass_smoothTensorInducedGradedResolutionCupPairing U hU s P hA hB hC
        (tprod_const_mem_smoothTensorInducedGradedResolutionPiece U hU s A hz)
        (smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const U hU s A hinv)
        (smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero U hU s A hdz)
        (tprod_const_mem_smoothTensorInducedGradedResolutionPiece U hU s B hz')
        (smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const U hU s B hinv')
        (smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero U hU s B hdz')).trans
        (congrArg₂ (fun x y ↦ (P.smoothTensorInduced U hU s).cup _ _ x y)
          (smoothTensorInducedDiagonalClass_eq U hU s A hA z hz hinv hdz).symm
          (smoothTensorInducedDiagonalClass_eq U hU s B hB z' hz' hinv' hdz').symm)))

end TauCeti
