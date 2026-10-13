/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Flat.EffectiveDescent
import TauCeti.RingTheory.Flat.TensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent of affine closed inclusions

A closed inclusion of affine schemes is a surjection of coordinate algebras. This file
proves that a morphism of faithfully flat descent data is surjective exactly when its
descended morphism is surjective, and identifies the original defining ideal as the
extension of the descended kernel, uniquely. Thus effective descent for commutative algebras
retains affine closed inclusions, including their nonreduced scheme structures. Combined with
`DescentDatum.Hom.spec` and `DescentDatum.specDescendedHom`, these results supply the coordinate
algebra and ideal of a descended affine closed inclusion; cocycles and the comparison with
base change are provided by the existing algebra and affine-scheme descent APIs.

The argument uses the effectivity comparison `DescentDatum.baseChangeEquiv`, Mathlib's
`Module.FaithfullyFlat.lTensor_surjective_iff_surjective`, and
`Algebra.TensorProduct.lTensor_ker_of_flat`. The surjectivity and kernel identities work for
possibly noncommutative algebras; uniqueness of the ideal uses a commutative ambient algebra.
The kernel identity needs only flatness.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1.
* The Stacks Project, Descent, descent of closed immersions.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.DescentDatum

universe u v w w'

variable {R : Type u} {S : Type v} {B : Type w} {B' : Type w'}
  [CommRing R] [CommRing S] [Algebra R S]
  [Ring B'] [Algebra R B'] [Algebra S B'] [IsScalarTower R S B']

section

variable [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {D : DescentDatum R S B} {D' : DescentDatum R S B'}

/-- Surjectivity of a morphism of algebras with faithfully flat descent data is equivalent
to surjectivity of the descended morphism. -/
@[simp]
theorem Hom.surjective_descend_iff [Module.FaithfullyFlat R S] (f : Hom D D') :
    Function.Surjective f.descend ↔ Function.Surjective f.toAlgHom := by
  have h : f.toAlgHom ∘ D.baseChangeEquiv =
      D'.baseChangeEquiv ∘ f.descend.toLinearMap.lTensor S :=
    funext f.toAlgHom_baseChangeEquiv
  refine (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S
    f.descend.toLinearMap).symm.trans ?_
  rw [← EquivLike.comp_surjective _ D'.baseChangeEquiv, ← h,
    EquivLike.surjective_comp D.baseChangeEquiv]

/-- The defining ideal of a morphism of flat descent data is the extension of the kernel
of its descended morphism. No surjectivity hypothesis is needed. -/
@[simp]
theorem Hom.map_ker_descend [Module.Flat R S] (f : Hom D D') :
    Ideal.map (D.descended.val : D.descended →+* B) (RingHom.ker f.descend) =
      RingHom.ker f.toAlgHom := by
  have hval : D.baseChangeEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : D.descended →ₐ[R] S ⊗[R] D.descended).toRingHom =
      (D.descended.val : D.descended →+* B) := by
    ext a
    simp
  rw [← hval, ← Ideal.map_map]
  have hker : Ideal.map
      (Algebra.TensorProduct.includeRight : D.descended →ₐ[R] S ⊗[R] D.descended).toRingHom
      (RingHom.ker f.descend) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f.descend) :=
    (Algebra.TensorProduct.lTensor_ker_of_flat f.descend).symm
  rw [hker]
  have hmap : (Algebra.TensorProduct.map (AlgHom.id S S) f.descend).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) f.descend).toRingHom := by
    ext <;> simp
  have hbase (x : S ⊗[R] D.descended) : f.toAlgHom (D.baseChangeEquiv x) =
      D'.baseChangeEquiv (Algebra.TensorProduct.map (AlgHom.id R S) f.descend x) :=
    (f.toAlgHom_baseChangeEquiv x).trans <| congrArg D'.baseChangeEquiv <|
      congrArg (fun g : S ⊗[R] D.descended →+* S ⊗[R] D'.descended ↦ g x) hmap
  ext b
  rw [Ideal.mem_map_iff_of_surjective D.baseChangeEquiv.toRingHom
    D.baseChangeEquiv.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [RingHom.mem_ker] at hx ⊢
    exact (hbase x).trans (by rw [hx, map_zero])
  · intro hb
    refine ⟨D.baseChangeEquiv.symm b, ?_, D.baseChangeEquiv.apply_symm_apply b⟩
    rw [RingHom.mem_ker] at hb ⊢
    apply D'.baseChangeEquiv.injective
    rw [← hbase, D.baseChangeEquiv.apply_symm_apply, hb, map_zero]

end

variable [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {D : DescentDatum R S B} {D' : DescentDatum R S B'}

/-- The original kernel has a unique ideal of definition in the descended algebra.
Its existence includes the infinitesimal structure, not merely the underlying closed set. -/
theorem Hom.existsUnique_ideal_map_eq_ker [Module.FaithfullyFlat R S] (f : Hom D D') :
    ∃! I : Ideal D.descended, Ideal.map (D.descended.val : D.descended →+* B) I =
      RingHom.ker f.toAlgHom := by
  refine ⟨RingHom.ker f.descend, f.map_ker_descend, fun I hI ↦ ?_⟩
  let j : D.descended →+* S ⊗[R] D.descended :=
    (Algebra.TensorProduct.includeRight : D.descended →ₐ[R] S ⊗[R] D.descended).toRingHom
  have hval : D.baseChangeEquiv.toRingHom.comp j =
      (D.descended.val : D.descended →+* B) := by
    ext a
    simp [j]
  have hext : Ideal.map D.baseChangeEquiv.toRingHom (Ideal.map j I) =
      Ideal.map D.baseChangeEquiv.toRingHom (Ideal.map j (RingHom.ker f.descend)) := by
    rw [Ideal.map_map, Ideal.map_map, hval]
    exact hI.trans f.map_ker_descend.symm
  have hmap : Ideal.map j I = Ideal.map j (RingHom.ker f.descend) := by
    have h := congrArg (Ideal.map D.baseChangeEquiv.symm.toRingHom) hext
    simpa only [RingEquiv.toRingHom_eq_coe, ← AlgEquiv.toRingEquiv_symm,
      Ideal.map_of_equiv] using h
  have hc : (Algebra.TensorProduct.comm R S D.descended).toRingHom.comp j =
      algebraMap D.descended (D.descended ⊗[R] S) := by
    ext a
    simp [j, Algebra.TensorProduct.algebraMap_apply]
  have hcomm := congrArg (Ideal.map (Algebra.TensorProduct.comm R S D.descended).toRingHom) hmap
  rw [Ideal.map_map, Ideal.map_map, hc] at hcomm
  exact Ideal.map_injective_of_faithfullyFlat hcomm

end TauCeti.Algebra.DescentDatum
