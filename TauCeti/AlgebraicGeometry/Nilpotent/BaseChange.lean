/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Nilpotent.AdjointQuotient
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of the nilpotent cone

After extending scalars to a commutative algebra, the base change of the cone is cut out in
the base change of the Lie algebra by the extension of the original invariant ideal.
The comparison and its projection equations come from
`Algebra.TensorProduct.tensorQuotientEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TauCeti

universe u

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
  (A : Type u) [CommRing A] [Algebra k A]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "P" => SymmetricAlgebra k (Module.Dual k 𝔤)
local notation "I" => nilpotentConeIdeal k H
local notation "J" => Ideal.map
  (AlgHom.toRingHom (Algebra.TensorProduct.includeRight : P →ₐ[k] A ⊗[k] P)) I

local notation "e" => Algebra.TensorProduct.tensorQuotientEquiv (R := k) A P A I

local notation "ιA" => Spec.algebraMap k A

/-- The base change of the cone to `Spec A` is the spectrum of the quotient of the
base-changed Lie algebra coordinate ring by the extended cone ideal. -/
noncomputable def nilpotentConeBaseChangeIso :
    pullback ιA (nilpotentConeToSpec k H) ≅ Spec (.of ((A ⊗[k] P) ⧸ J)) :=
  (pullback.congrHom rfl (nilpotentConeToSpec_eq k H)) ≪≫
    pullbackSpecIso k A (P ⧸ I) ≪≫ Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.symm.op

/-- Under the base-change comparison the first projection is the structure map over `A`. -/
@[reassoc]
theorem nilpotentConeBaseChangeIso_inv_fst :
    (nilpotentConeBaseChangeIso k H A).inv ≫ pullback.fst ιA (nilpotentConeToSpec k H) =
      Spec.algebraMap A ((A ⊗[k] P) ⧸ J) := by
  rw [nilpotentConeBaseChangeIso, Iso.trans_inv, Iso.trans_inv]
  simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst', Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv, Scheme.Spec_map,
    Spec.algebraMap, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (e).commutes a

/-- In the polynomial presentation of the Lie algebra, the other projection followed by the
cone inclusion evaluates polynomials modulo the extended ideal. -/
@[reassoc]
theorem nilpotentConeBaseChangeIso_inv_snd_comp_ι :
    (nilpotentConeBaseChangeIso k H A).inv ≫ pullback.snd ιA (nilpotentConeToSpec k H) ≫
        nilpotentConeι k H ≫ (lieAlgebraSchemeIso k H).hom =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
        (Algebra.TensorProduct.includeRight : P →ₐ[k] A ⊗[k] P).toRingHom)) := by
  have hι : nilpotentConeι k H ≫ (lieAlgebraSchemeIso k H).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [nilpotentConeι_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hι, nilpotentConeBaseChangeIso, Iso.trans_inv, Iso.trans_inv]
  simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_snd_assoc, Category.id_comp,
    pullbackSpecIso_inv_snd_assoc, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv, Scheme.Spec_map,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul A P A I 1 p

/-- The base-changed cone inclusion is induced by quotienting by the extended ideal. -/
theorem nilpotentConeBaseChangeIso_inv_comp_baseChange_ι :
    (nilpotentConeBaseChangeIso k H A).inv ≫
        pullback.map ιA (nilpotentConeToSpec k H) ιA (Spec.algebraMap k P)
          (𝟙 _) (nilpotentConeι k H ≫ (lieAlgebraSchemeIso k H).hom) (𝟙 _)
          (by simp) (by simpa only [Category.assoc, Category.comp_id] using
            (nilpotentConeι_comp_toSpec k H).symm) ≫
        (pullbackSpecIso k A P).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  rw [← cancel_mono (pullbackSpecIso k A P).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst,
      Category.comp_id, nilpotentConeBaseChangeIso_inv_fst, Category.assoc,
      pullbackSpecIso_inv_fst', ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (Ideal.Quotient.mk_comp_algebraMap A J).symm
  · simp only [Category.assoc, pullback.lift_snd, nilpotentConeBaseChangeIso_inv_snd_comp_ι]
    rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      AlgHom.toRingHom_eq_coe]

end TauCeti
