/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Base change of infinite adeles

For a finite extension of number fields `L/K`, scalar extension identifies
`K∞ ⊗[K] L` with `L∞`. The comparison is an algebra equivalence over `K∞` and a
homeomorphism when the tensor product carries the module topology over `K∞`.
Its component at a place of `L` is the semilocal comparison at the place below it.

The construction assembles `infiniteSemilocalEquiv` through Mathlib's
`TensorProduct.piLeft`. This includes the real-to-complex factors of local degree two.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace
open scoped TensorProduct NumberField.LiesOver InfiniteAdeleExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

-- The diagonal `K`-action on the infinite adeles of `L` is the composite through `L`.
private local instance (priority := 50) : Algebra K (InfiniteAdeleRing L) :=
  inferInstanceAs (Algebra K ((w : InfinitePlace L) → w.Completion))

private local instance (priority := 50) : IsScalarTower K L (InfiniteAdeleRing L) :=
  inferInstanceAs (IsScalarTower K L ((w : InfinitePlace L) → w.Completion))

private local instance (priority := 50) :
    IsScalarTower K (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_infiniteAdeleExtensionAlgebra]
    exact (infiniteAdeleExtension_algebraMap K L x).symm

/-- The scalar-extension map of infinite adeles, using the completion maps at the places above
each base place. -/
def infiniteAdeleBaseChangeHom :
    InfiniteAdeleRing K ⊗[K] L →ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom K L (InfiniteAdeleRing L)) fun _ _ ↦ .all _ _

/-- On pure tensors, the base-change map multiplies the extended adele by the diagonal field
element. -/
@[simp]
theorem infiniteAdeleBaseChangeHom_tmul (a : InfiniteAdeleRing K) (x : L) :
    infiniteAdeleBaseChangeHom K L (a ⊗ₜ x) =
      infiniteAdeleExtension K L a * algebraMap L (InfiniteAdeleRing L) x := by
  simp [infiniteAdeleBaseChangeHom, Algebra.ofId_apply,
    algebraMap_infiniteAdeleExtensionAlgebra]

/-- At a place of `L`, a pure tensor is evaluated using the completion map from the place
below it and the local embedding of the field element. -/
@[simp]
theorem infiniteAdeleBaseChangeHom_tmul_apply (a : InfiniteAdeleRing K) (x : L)
    (w : InfinitePlace L) :
    infiniteAdeleBaseChangeHom K L (a ⊗ₜ x) w =
      LiesOver.completionMap _ w (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by
  rw [infiniteAdeleBaseChangeHom_tmul]
  -- Evaluate multiplication in the infinite-adele type synonym before rewriting its factors.
  change (infiniteAdeleExtension K L a) w *
    (algebraMap L (InfiniteAdeleRing L) x) w = _
  rw [infiniteAdeleExtension_apply, InfiniteAdeleRing.algebraMap_apply]
  rfl

variable [NumberField K] [NumberField L]

private def groupedInfiniteAdeles :
    InfiniteAdeleRing L ≃ₗ[K]
      ((v : InfinitePlace K) → (w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completion) where
  toFun a _ w := a w.1
  invFun a w := a (w.comap (algebraMap K L)) ⟨w, inferInstance⟩
  left_inv _ := rfl
  right_inv a := by
    funext v ⟨w, hw⟩
    have := hw
    have h := InfinitePlace.LiesOver.comap_eq w v
    subst v
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
private def baseChangeLinearEquiv :
    InfiniteAdeleRing K ⊗[K] L ≃ₗ[K] InfiniteAdeleRing L :=
  (TensorProduct.piLeft K L (fun v : InfinitePlace K ↦ v.Completion)).trans
    ((LinearEquiv.piCongrRight fun v ↦
      (infiniteSemilocalEquiv L v).toLinearEquiv.restrictScalars K).trans
        (groupedInfiniteAdeles K L).symm)

private theorem baseChangeLinearEquiv_apply (t : InfiniteAdeleRing K ⊗[K] L) :
    baseChangeLinearEquiv K L t = infiniteAdeleBaseChangeHom K L t := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    funext w
    rw [infiniteAdeleBaseChangeHom_tmul]
    -- The finite-product tensor equivalence and regrouping are implementation maps;
    -- reduce their component projections before applying the public semilocal formula.
    change infiniteSemilocalEquiv L (w.comap (algebraMap K L))
      (a (w.comap (algebraMap K L)) ⊗ₜ x) ⟨w, inferInstance⟩ = _
    rw [infiniteSemilocalEquiv_tmul]
    -- Product evaluation in the infinite-adele type synonym does not rewrite by `Pi.mul_apply`.
    change _ = (infiniteAdeleExtension K L a) w *
      (algebraMap L (InfiniteAdeleRing L) x) w
    rw [infiniteAdeleExtension_apply, InfiniteAdeleRing.algebraMap_apply]
    rfl
  | add t u ht hu => simp [ht, hu]

/-- The archimedean semilocal decompositions assemble to a bijective base-change map. -/
theorem infiniteAdeleBaseChangeHom_bijective :
    Function.Bijective (infiniteAdeleBaseChangeHom K L) := by
  have h : ⇑(baseChangeLinearEquiv K L) = ⇑(infiniteAdeleBaseChangeHom K L) :=
    funext (baseChangeLinearEquiv_apply K L)
  rw [← h]
  exact (baseChangeLinearEquiv K L).bijective

/-- Base change of infinite adeles is an algebra equivalence over the infinite adele ring of
the base field, independently of a topology on the tensor product. -/
def infiniteAdeleBaseChangeAlgEquiv :
    InfiniteAdeleRing K ⊗[K] L ≃ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L :=
  AlgEquiv.ofBijective (infiniteAdeleBaseChangeHom K L)
    (infiniteAdeleBaseChangeHom_bijective K L)

/-- Forgetting invertibility recovers the canonical base-change homomorphism. -/
@[simp]
theorem infiniteAdeleBaseChangeAlgEquiv_toAlgHom :
    (infiniteAdeleBaseChangeAlgEquiv K L).toAlgHom = infiniteAdeleBaseChangeHom K L :=
  (rfl)

/-- The algebraic inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem infiniteAdeleBaseChangeAlgEquiv_symm_algebraMap (x : L) :
    (infiniteAdeleBaseChangeAlgEquiv K L).symm
      (algebraMap L (InfiniteAdeleRing L) x) = 1 ⊗ₜ[K] x := by
  apply (infiniteAdeleBaseChangeAlgEquiv K L).injective
  simp [infiniteAdeleBaseChangeAlgEquiv]

variable [TopologicalSpace (InfiniteAdeleRing K ⊗[K] L)]
  [IsModuleTopology (InfiniteAdeleRing K) (InfiniteAdeleRing K ⊗[K] L)]

/-- Base change of infinite adeles is a continuous algebra equivalence over the infinite adele
ring of the base field. The source carries its module topology over that ring. -/
def infiniteAdeleBaseChangeEquiv :
    InfiniteAdeleRing K ⊗[K] L ≃A[InfiniteAdeleRing K] InfiniteAdeleRing L := by
  let e := infiniteAdeleBaseChangeAlgEquiv K L
  letI : ContinuousSMul (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
    continuousSMul_of_algebraMap _ _ (by
      rw [algebraMap_infiniteAdeleExtensionAlgebra]
      exact continuous_infiniteAdeleExtension K L)
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  -- A finite scalar-extended basis presents the tensor product as a finite product of
  -- sigma-compact infinite adele rings. The additive open mapping theorem then gives the inverse.
  letI := IsModuleTopology.isTopologicalAddGroup (InfiniteAdeleRing K)
    (InfiniteAdeleRing K ⊗[K] L)
  letI : SecondCountableTopology (InfiniteAdeleRing K) :=
    (InfiniteAdeleRing.homeomorphMixedSpace K).secondCountableTopology
  let b := (Module.finBasis K L).baseChange (InfiniteAdeleRing K)
  have hs := isSigmaCompact_range
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
  have hb : Function.Surjective b.equivFun.symm.toLinearMap := b.equivFun.symm.surjective
  rw [hb.range_eq] at hs
  letI : SigmaCompactSpace (InfiniteAdeleRing K ⊗[K] L) := isSigmaCompact_univ_iff.mp hs
  have ho : IsOpenMap e := e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective hc
  exact
    { toAlgEquiv := e
      continuous_toFun := hc
      continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

/-- Forgetting continuity recovers the algebraic base-change equivalence. -/
@[simp]
theorem infiniteAdeleBaseChangeEquiv_toAlgEquiv :
    (infiniteAdeleBaseChangeEquiv K L).toAlgEquiv = infiniteAdeleBaseChangeAlgEquiv K L :=
  (rfl)

/-- The continuous comparison sends a pure tensor to the extended adele times the diagonal
field element. -/
@[simp]
theorem infiniteAdeleBaseChangeEquiv_tmul (a : InfiniteAdeleRing K) (x : L) :
    infiniteAdeleBaseChangeEquiv K L (a ⊗ₜ x) =
      infiniteAdeleExtension K L a * algebraMap L (InfiniteAdeleRing L) x := by
  have h : (infiniteAdeleBaseChangeEquiv K L).toAlgHom =
      infiniteAdeleBaseChangeHom K L := by simp
  exact (AlgHom.congr_fun h (a ⊗ₜ[K] x)).trans
    (infiniteAdeleBaseChangeHom_tmul K L a x)

/-- At a place of `L`, the continuous comparison evaluates a pure tensor using the completion
map from the place below it and the local embedding of the field element. -/
@[simp]
theorem infiniteAdeleBaseChangeEquiv_tmul_apply (a : InfiniteAdeleRing K) (x : L)
    (w : InfinitePlace L) :
    infiniteAdeleBaseChangeEquiv K L (a ⊗ₜ x) w =
      LiesOver.completionMap _ w (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by
  have h : (infiniteAdeleBaseChangeEquiv K L).toAlgHom =
      infiniteAdeleBaseChangeHom K L := by simp
  exact (congrArg (fun b : InfiniteAdeleRing L ↦ b w)
    (AlgHom.congr_fun h (a ⊗ₜ[K] x))).trans
      (infiniteAdeleBaseChangeHom_tmul_apply K L a x w)

/-- The inverse comparison sends a diagonal field element to `1 ⊗ x`. -/
@[simp]
theorem infiniteAdeleBaseChangeEquiv_symm_algebraMap (x : L) :
    (infiniteAdeleBaseChangeEquiv K L).symm
      (algebraMap L (InfiniteAdeleRing L) x) = 1 ⊗ₜ[K] x := by
  exact infiniteAdeleBaseChangeAlgEquiv_symm_algebraMap K L x

end TauCeti.GlobalNumberFields
