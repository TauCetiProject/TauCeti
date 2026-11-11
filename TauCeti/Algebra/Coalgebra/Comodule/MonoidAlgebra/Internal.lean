/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Comodules from internal weight decompositions

An internal direct sum indexed by `G` determines a comodule over the coalgebra `R[G]`:
a vector in the `g`-summand coacts as `v ↦ v ⊗ [g]`. No basis of a summand is needed.
When `G` is an abelian group, this is the representation of the diagonalizable group
with character group `G` attached to the decomposition.

`DirectSum.IsInternal.monoidAlgebraComodule` constructs this comodule, and
`DirectSum.IsInternal.weightSpace_monoidAlgebraComodule` recovers the original summands.
The homogeneous-vector equation uniquely determines the comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 (diagonalizable groups).
-/

public section

open scoped TensorProduct DirectSum

namespace DirectSum.IsInternal

variable {R G V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  [DecidableEq G] {A : G → Submodule R V}

private noncomputable def homogeneousCoact (hA : IsInternal A) :
    V →ₗ[R] V ⊗[R] MonoidAlgebra R G :=
  letI := hA.chooseDecomposition
  DirectSum.toModule R G _ (fun g =>
    ((TensorProduct.mk R V (MonoidAlgebra R G)).flip (MonoidAlgebra.single g 1)).comp
      (A g).subtype) ∘ₗ (DirectSum.decomposeLinearEquiv A).toLinearMap

private theorem homogeneousCoact_of (hA : IsInternal A) (g : G) (v : A g) :
    homogeneousCoact hA v = (v : V) ⊗ₜ[R] MonoidAlgebra.single g 1 := by
  simp [homogeneousCoact]

/-- The comodule whose homogeneous vectors have their direct-sum indices as weights.
Only the coalgebra of the monoid algebra is used, so the index needs no multiplication. -/
@[instance_reducible]
noncomputable def monoidAlgebraComodule (hA : IsInternal A) :
    TauCeti.Comodule R (MonoidAlgebra R G) V where
  coact := homogeneousCoact hA
  coassoc := by
    let _ := hA.chooseDecomposition
    apply DirectSum.decompose_lhom_ext A
    intro g
    ext v
    simp [homogeneousCoact_of, TensorProduct.assoc_tmul]
  lTensor_counit_comp_coact := by
    let _ := hA.chooseDecomposition
    apply DirectSum.decompose_lhom_ext A
    intro g
    ext v
    simp [homogeneousCoact_of]

/-- The coaction on a vector in one of the specified summands.
Supply the weight explicitly when rewriting: the coaction of zero does not determine it. -/
theorem coact_monoidAlgebraComodule_of_mem (hA : IsInternal A) {g : G} {v : V}
    (hv : v ∈ A g) :
    letI := hA.monoidAlgebraComodule
    TauCeti.Comodule.coact (R := R) (C := MonoidAlgebra R G) v =
      v ⊗ₜ[R] MonoidAlgebra.single g 1 :=
  homogeneousCoact_of hA g ⟨v, hv⟩

/-- Projection to a character of the constructed comodule is the original direct-sum
coordinate followed by its inclusion. -/
theorem weightProj_monoidAlgebraComodule (hA : IsInternal A) (g : G) (v : V) :
    letI := hA.chooseDecomposition
    letI := hA.monoidAlgebraComodule
    TauCeti.Comodule.weightProj R G V g v = (DirectSum.decompose A v g : V) := by
  let _ := hA.chooseDecomposition
  let _ := hA.monoidAlgebraComodule
  suffices TauCeti.Comodule.weightProj R G V g =
      (A g).subtype ∘ₗ DirectSum.component R G (fun g => A g) g ∘ₗ
        (DirectSum.decomposeLinearEquiv A).toLinearMap from LinearMap.congr_fun this v
  apply DirectSum.decompose_lhom_ext A
  intro i
  ext v
  by_cases hi : i = g
  · subst i
    simp [TauCeti.Comodule.weightProj_apply,
      coact_monoidAlgebraComodule_of_mem hA v.property]
  · simp [TauCeti.Comodule.weightProj_apply, DirectSum.component.of,
      coact_monoidAlgebraComodule_of_mem hA v.property, hi, Ne.symm hi]

/-- The weight spaces of the constructed comodule are exactly the original summands. -/
@[simp]
theorem weightSpace_monoidAlgebraComodule (hA : IsInternal A) (g : G) :
    letI := hA.monoidAlgebraComodule
    TauCeti.Comodule.weightSpace R G V g = A g := by
  let _ := hA.monoidAlgebraComodule
  apply le_antisymm
  · intro v hv
    rw [← TauCeti.Comodule.weightProj_of_mem hv, weightProj_monoidAlgebraComodule]
    exact Submodule.coe_mem _
  · intro v hv
    rw [TauCeti.Comodule.mem_weightSpace]
    exact coact_monoidAlgebraComodule_of_mem hA hv

/-- A coaction is uniquely determined by its values on the homogeneous summands. -/
theorem monoidAlgebraComodule_unique (hA : IsInternal A)
    (c : TauCeti.Comodule R (MonoidAlgebra R G) V)
    (hc : ∀ g (v : A g), c.coact v = (v : V) ⊗ₜ[R] MonoidAlgebra.single g 1) :
    c = hA.monoidAlgebraComodule := by
  apply TauCeti.Comodule.ext
  -- Specify the right-hand coaction rather than infer a second class-field instance.
  suffices c.coact = homogeneousCoact hA from this
  let _ := hA.chooseDecomposition
  apply DirectSum.decompose_lhom_ext A
  intro g
  ext v
  exact (hc g v).trans (homogeneousCoact_of hA g v).symm

end DirectSum.IsInternal
