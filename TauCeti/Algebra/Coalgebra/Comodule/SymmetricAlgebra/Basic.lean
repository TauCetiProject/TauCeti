/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
public import TauCeti.RingTheory.GradedAlgebra.DecomposeTensor

/-!
# The graded symmetric algebra of a comodule

The symmetric algebra of a right comodule over a commutative bialgebra has a multiplicative
coaction extending the coaction of its generators. Every homogeneous piece is stable under this
coaction. Applied to the dual of a finite-dimensional representation, this is the graded
homogeneous-coordinate algebra for its projective space, used in constructing projective orbits
and homogeneous spaces.

The construction works over commutative semirings and requires neither freeness nor flatness.
The comodule structure is selected explicitly, rather than installed as a global instance.
Comodule morphisms induce morphisms of symmetric algebras, and algebra-valued points act by
algebra homomorphisms on scalar extensions.

The construction and proof organization adapt
`TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Basic`; the symmetric algebra uses Mathlib's
`SymmetricAlgebra.lift` without the square-zero relation needed for the exterior algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. S. Milne, *Algebraic Groups* (2017), §§7.d--7.f, for projective orbits and linear actions.
-/

public section

open scoped TensorProduct

open CategoryTheory

namespace TauCeti

namespace Comodule

-- Normalize the algebra-tensor maps to the ordinary linear tensor maps used by comodules.
attribute [local simp] TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq

variable {R H M N P : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [AddCommMonoid N] [Module R N] [Comodule R H N]
  [AddCommMonoid P] [Module R P] [Comodule R H P]

variable (R H M) in
/-- The coaction of the symmetric algebra of a comodule, as an algebra homomorphism: it sends a
generator `ι m` to `ι m₍₀₎ ⊗ m₍₁₎`, the coaction of `m` followed by the inclusion of generators. -/
noncomputable def symmetricAlgebraCoact :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M ⊗[R] H :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R M).rTensor H ∘ₗ coact (R := R) (C := H) (M := M))

@[simp]
theorem symmetricAlgebraCoact_ι (m : M) :
    symmetricAlgebraCoact R H M (SymmetricAlgebra.ι R M m) =
      (SymmetricAlgebra.ι R M).rTensor H (coact (R := R) (C := H) m) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Coassociativity of `symmetricAlgebraCoact`, as an equality of algebra homomorphisms. -/
private theorem symmetricAlgebraCoact_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (SymmetricAlgebra R M) H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (symmetricAlgebraCoact R H M) (AlgHom.id R H)).comp
          (symmetricAlgebraCoact R H M)) =
      (Algebra.TensorProduct.map (AlgHom.id R (SymmetricAlgebra R M))
        (Bialgebra.comulAlgHom R H)).comp (symmetricAlgebraCoact R H M) := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  have hassoc (z : M ⊗[R] H) :
      Algebra.TensorProduct.assoc R R R (SymmetricAlgebra R M) H H
          (Algebra.TensorProduct.map (symmetricAlgebraCoact R H M) (AlgHom.id R H)
            ((SymmetricAlgebra.ι R M).rTensor H z)) =
        (SymmetricAlgebra.ι R M).rTensor (H ⊗[R] H)
          (TensorProduct.assoc R M H H ((coact (R := R) (C := H) (M := M)).rTensor H z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul m h =>
      simp only [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, symmetricAlgebraCoact_ι,
        AlgHom.coe_id, id_eq]
      induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
      | tmul n k => simp
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    symmetricAlgebraCoact_ι, AlgEquiv.coe_toAlgHom, hassoc, coassoc_apply]
  simp only [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
    AlgHom.toLinearMap_id, TensorProduct.AlgebraTensorModule.map_eq,
    LinearMap.map_rTensor, LinearMap.id_comp, Bialgebra.toLinearMap_comulAlgHom,
    LinearMap.lTensor_def, LinearMap.rTensor_map, LinearMap.comp_id]

/-- Coassociativity of the coaction of the symmetric algebra. -/
private theorem symmetricAlgebraCoact_coassoc :
    TensorProduct.assoc R (SymmetricAlgebra R M) H H ∘ₗ
        (symmetricAlgebraCoact R H M).toLinearMap.rTensor H ∘ₗ
          (symmetricAlgebraCoact R H M).toLinearMap =
      Coalgebra.comul.lTensor (SymmetricAlgebra R M) ∘ₗ
        (symmetricAlgebraCoact R H M).toLinearMap := by
  simpa [LinearMap.rTensor_def, LinearMap.lTensor_def,
    Algebra.TensorProduct.assoc_toLinearEquiv] using
    congrArg AlgHom.toLinearMap (symmetricAlgebraCoact_coassoc_algHom (R := R) (H := H)
      (M := M))

/-- The counit law for the coaction of the symmetric algebra. -/
private theorem symmetricAlgebraCoact_counit :
    Coalgebra.counit.lTensor (SymmetricAlgebra R M) ∘ₗ (symmetricAlgebraCoact R H M).toLinearMap =
      (TensorProduct.mk R (SymmetricAlgebra R M) R).flip 1 := by
  have h : (Algebra.TensorProduct.map (AlgHom.id R (SymmetricAlgebra R M))
      (Bialgebra.counitAlgHom R H)).comp (symmetricAlgebraCoact R H M) =
      Algebra.TensorProduct.includeLeft := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      symmetricAlgebraCoact_ι, Algebra.TensorProduct.includeLeft_apply]
    simp only [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
      AlgHom.toLinearMap_id, TensorProduct.AlgebraTensorModule.map_eq,
      Bialgebra.toLinearMap_counitAlgHom]
    rw [LinearMap.map_rTensor, LinearMap.id_comp]
    simpa only [LinearMap.comp_id, ← LinearMap.lTensor_def, lTensor_counit_coact,
      LinearMap.rTensor_tmul] using
      (LinearMap.rTensor_map M (SymmetricAlgebra.ι R M) LinearMap.id
        (Coalgebra.counit (R := R) (A := H)) (coact m)).symm
  have h' : Coalgebra.counit.lTensor (SymmetricAlgebra R M) ∘ₗ
      (symmetricAlgebraCoact R H M).toLinearMap =
      (Algebra.TensorProduct.includeLeft (R := R) (A := SymmetricAlgebra R M)
        (B := R)).toLinearMap := by
    simpa [LinearMap.lTensor_def] using congrArg AlgHom.toLinearMap h
  rw [h']
  ext x
  simp

variable (R H M) in
/-- The symmetric algebra of a right comodule over a commutative bialgebra, with the
multiplicative coaction `symmetricAlgebraCoact`.

Following `Comodule.tensor`, this is deliberately *not* a global instance. Select it explicitly,
or register it as a local instance. -/
@[implicit_reducible]
noncomputable def symmetricAlgebra : Comodule R H (SymmetricAlgebra R M) where
  coact := (symmetricAlgebraCoact R H M).toLinearMap
  coassoc := symmetricAlgebraCoact_coassoc
  lTensor_counit_comp_coact := symmetricAlgebraCoact_counit

attribute [local instance] symmetricAlgebra

/-- The coaction of the symmetric-algebra comodule is `symmetricAlgebraCoact`. -/
@[simp]
theorem symmetricAlgebra_coact :
    coact (R := R) (C := H) (M := SymmetricAlgebra R M) =
      (symmetricAlgebraCoact R H M).toLinearMap :=
  (rfl)

namespace Hom

variable (R H M) in
/-- The inclusion `ι : M → SymmetricAlgebra R M` of generators, as a comodule morphism. -/
noncomputable def symmetricAlgebraι : Hom R H M (SymmetricAlgebra R M) where
  toLinearMap := SymmetricAlgebra.ι R M
  map_coact := by
    ext m
    simp [LinearMap.rTensor_def]

@[simp]
theorem symmetricAlgebraι_toLinearMap :
    (symmetricAlgebraι R H M).toLinearMap = SymmetricAlgebra.ι R M :=
  (rfl)

@[simp]
theorem symmetricAlgebraι_apply (m : M) :
    symmetricAlgebraι R H M m = SymmetricAlgebra.ι R M m :=
  (rfl)

/-- The algebra homomorphism `SymmetricAlgebra.map f` induced by a comodule morphism commutes
with the coactions. -/
private theorem symmetricAlgebraCoact_comp_map (f : Hom R H M N) :
    (Algebra.TensorProduct.map (SymmetricAlgebra.map R f.toLinearMap) (AlgHom.id R H)).comp
        (symmetricAlgebraCoact R H M) =
      (symmetricAlgebraCoact R H N).comp (SymmetricAlgebra.map R f.toLinearMap) := by
  apply SymmetricAlgebra.algHom_ext
  ext m
  have hmap (z : M ⊗[R] H) :
      Algebra.TensorProduct.map (SymmetricAlgebra.map R f.toLinearMap) (AlgHom.id R H)
          ((SymmetricAlgebra.ι R M).rTensor H z) =
        (SymmetricAlgebra.ι R N).rTensor H (TensorProduct.map f.toLinearMap LinearMap.id z) := by
    induction z using TensorProduct.inductionOn with
    | tmul m h => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    symmetricAlgebraCoact_ι, hmap, Hom.map_coact_apply, SymmetricAlgebra.map_apply_ι,
    Hom.coe_toLinearMap]

/-- The map of symmetric algebras induced by a comodule morphism, as a comodule morphism. -/
noncomputable def symmetricAlgebraMap (f : Hom R H M N) :
    Hom R H (SymmetricAlgebra R M) (SymmetricAlgebra R N) where
  toLinearMap := (SymmetricAlgebra.map R f.toLinearMap).toLinearMap
  map_coact := by
    simpa using congrArg AlgHom.toLinearMap (symmetricAlgebraCoact_comp_map f)

@[simp]
theorem symmetricAlgebraMap_toLinearMap (f : Hom R H M N) :
    (symmetricAlgebraMap f).toLinearMap = (SymmetricAlgebra.map R f.toLinearMap).toLinearMap :=
  (rfl)

@[simp]
theorem symmetricAlgebraMap_apply (f : Hom R H M N) (x : SymmetricAlgebra R M) :
    symmetricAlgebraMap f x = SymmetricAlgebra.map R f.toLinearMap x :=
  (rfl)

/-- The symmetric-algebra functor on comodules preserves identities. -/
@[simp]
theorem symmetricAlgebraMap_id :
    symmetricAlgebraMap (𝟙 (ComoduleCat.of R H M)) =
      𝟙 (ComoduleCat.of R H (SymmetricAlgebra R M)) := by
  ext x
  simp [← ComoduleCat.ofHom_id]

/-- The symmetric-algebra functor on comodules preserves composition. -/
@[simp]
theorem symmetricAlgebraMap_comp (g : Hom R H N P) (f : Hom R H M N) :
    symmetricAlgebraMap (g.comp f) = (symmetricAlgebraMap g).comp (symmetricAlgebraMap f) := by
  ext x
  simp [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map]

/-- The symmetric-algebra functor is compatible with the inclusion of generators. -/
@[simp]
theorem symmetricAlgebraMap_comp_symmetricAlgebraι (f : Hom R H M N) :
    (symmetricAlgebraMap f).comp (symmetricAlgebraι R H M) = (symmetricAlgebraι R H N).comp f := by
  ext m
  simp

end Hom

section SymmetricPower

/-- The coaction preserves the symmetric grading: the coaction of a degree-`n` element lies
in the image of the degree-`n` piece tensored with `H`. -/
theorem symmetricAlgebraCoact_mem_decomposeTensor {n : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ SymmetricAlgebra.homogeneousSubmodule R M n) :
    symmetricAlgebraCoact R H M x ∈
      DirectSum.decomposeTensor (SymmetricAlgebra.homogeneousSubmodule R M) H n := by
  have hι (z : M ⊗[R] H) : (SymmetricAlgebra.ι R M).rTensor H z ∈
      DirectSum.decomposeTensor (SymmetricAlgebra.homogeneousSubmodule R M) H 1 := by
    induction z using TensorProduct.inductionOn with
    | tmul m h =>
      exact DirectSum.tmul_mem_decomposeTensor
        (by simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m) h
    | add x y hx hy => exact map_add (SymmetricAlgebra.ι R M |>.rTensor H) x y ▸ add_mem hx hy
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (SetLike.one_mem_graded _)
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, symmetricAlgebraCoact_ι, Nat.succ_eq_one_add]
    exact SetLike.mul_mem_graded (hι _) hx

variable (R H M) in
/-- The degree-`n` homogeneous piece as a subcomodule of the symmetric algebra. -/
noncomputable def symmetricPowerSubcomodule (n : ℕ) : Subcomodule R H (SymmetricAlgebra R M) :=
  Subcomodule.ofSubmodule (SymmetricAlgebra.homogeneousSubmodule R M n) fun _ hx ↦ by
    rw [symmetricAlgebra_coact, AlgHom.toLinearMap_apply, ← LinearMap.rTensor_def,
      ← DirectSum.decomposeTensor_apply]
    exact symmetricAlgebraCoact_mem_decomposeTensor hx

@[simp]
theorem symmetricPowerSubcomodule_toSubmodule (n : ℕ) :
    (symmetricPowerSubcomodule R H M n).toSubmodule = SymmetricAlgebra.homogeneousSubmodule R M n :=
  (rfl)

@[simp]
theorem mem_symmetricPowerSubcomodule {n : ℕ} {x : SymmetricAlgebra R M} :
    x ∈ symmetricPowerSubcomodule R H M n ↔ x ∈ SymmetricAlgebra.homogeneousSubmodule R M n :=
  Iff.rfl

end SymmetricPower

section Points

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- The action of an `A`-point `g` of `H` on the scalar extension `A ⊗[R] SymmetricAlgebra R M`,
as an `A`-algebra homomorphism. Its underlying linear map is `endOfPoint`
(`symmetricAlgebraEndOfPoint_toLinearMap`), so points act on the symmetric algebra
multiplicatively. -/
noncomputable def symmetricAlgebraEndOfPoint (g : H →ₐ[R] A) :
    A ⊗[R] SymmetricAlgebra R M →ₐ[A] A ⊗[R] SymmetricAlgebra R M :=
  Algebra.TensorProduct.lift (Algebra.ofId A _)
    ((Algebra.TensorProduct.comm R (SymmetricAlgebra R M) A).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R (SymmetricAlgebra R M)) g).comp
        (symmetricAlgebraCoact R H M)))
    fun a _ ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left a _

/-- The algebra homomorphism `symmetricAlgebraEndOfPoint g` is the action `endOfPoint` of the
point `g` on the symmetric-algebra comodule. -/
theorem symmetricAlgebraEndOfPoint_toLinearMap (g : H →ₐ[R] A) :
    (symmetricAlgebraEndOfPoint (M := M) g).toLinearMap = endOfPoint (SymmetricAlgebra R M) g := by
  apply LinearMap.restrictScalars_injective R
  refine TensorProduct.ext' fun a x ↦ ?_
  have hcomm (z : SymmetricAlgebra R M ⊗[R] H) :
      Algebra.TensorProduct.comm R (SymmetricAlgebra R M) A
          (Algebra.TensorProduct.map (AlgHom.id R (SymmetricAlgebra R M)) g z) =
        TensorProduct.comm R (SymmetricAlgebra R M) A (g.toLinearMap.lTensor _ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul y h => simp
    | add z w hz hw => simp only [map_add, hz, hw]
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, symmetricAlgebraEndOfPoint,
    Algebra.TensorProduct.lift_tmul, endOfPoint_tmul, symmetricAlgebra_coact, Algebra.ofId_apply,
    ← Algebra.smul_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hcomm]

@[simp]
theorem symmetricAlgebraEndOfPoint_apply (g : H →ₐ[R] A) (x : A ⊗[R] SymmetricAlgebra R M) :
    symmetricAlgebraEndOfPoint g x = endOfPoint (SymmetricAlgebra R M) g x := by
  rw [← AlgHom.toLinearMap_apply, symmetricAlgebraEndOfPoint_toLinearMap]

end Points

end Comodule

end TauCeti
