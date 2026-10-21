/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.RingTheory.Etale.Splitting

/-!
# Splitting finite étale schemes over a field

Every finite étale scheme over a field becomes the spectrum of a finite product of copies
of the base field after a finite separable extension. The isomorphism is over the extended
base, so it labels all points as rational points, including their scheme structures.
The empty scheme corresponds to the product indexed by `Fin 0`.

This is the scheme form of `TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct`, transported
through `TauCeti.FiniteEtaleScheme.spec` and Mathlib's affine pullback comparison.

## References

* The Stacks Project, Tag 03QR (schemes étale over a point).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale scheme becomes a disjoint union of rational points after a finite
separable field extension. The splitting is an isomorphism over the extended base. -/
theorem exists_split_of_isFinite_of_etale {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L) (n : ℕ),
      Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
        Over.mk (Spec.algebraMap L (Fin n → L))) := by
  have : (TauCeti.FiniteEtaleScheme.spec.{u} (.of K)).EssSurj := by
    rw [← TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]
    infer_instance
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (TauCeti.FiniteEtaleScheme.spec (.of K)) (TauCeti.FiniteEtaleScheme.ofHom f)
  let eSpec : (algSpec (.of K)).obj (.op A.unop.obj) ≅
      Over.mk (Spec.algebraMap K A.unop.obj) :=
    Over.isoMk (Iso.refl _) (by
      -- The spectrum functor's object wrapper hides the source of its structure map.
      erw [Category.id_comp, algSpec_obj_hom]
      rfl)
  have e' := (TauCeti.finiteEtaleSchemeProperty (Spec (.of K))).ι.mapIso e
  rw [ObjectProperty.ι_obj, ObjectProperty.ι_obj, TauCeti.FiniteEtaleScheme.spec_obj_obj,
    TauCeti.FiniteEtaleScheme.ofHom_obj] at e'
  let e₀ : Over.mk (Spec.algebraMap K A.unop.obj) ≅ Over.mk f := eSpec.symm ≪≫ e'
  obtain ⟨L, _, _, _, _, hL⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A.unop.obj
  obtain ⟨n, ⟨a⟩⟩ := hL.nonempty_algEquiv_fun
  let e₁ : Over.mk (pullback.snd (Spec.algebraMap K A.unop.obj) (Spec.algebraMap K L)) ≅
      Over.mk (Spec.algebraMap L (L ⊗[K] A.unop.obj)) :=
    Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso K L A.unop.obj) (by
      simp [Spec.algebraMap, pullbackSpecIso_hom_fst'])
  let e₂ : Over.mk (Spec.algebraMap L (L ⊗[K] A.unop.obj)) ≅
      Over.mk (Spec.algebraMap L (Fin n → L)) :=
    Over.isoMk (Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.symm.op) (by
      -- Read the contravariant spectrum map as the ring homomorphism of `a.symm`.
      erw [← Spec.map_comp]
      apply congrArg Spec.map
      ext r
      exact a.symm.commutes r)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n,
    ⟨((Over.pullback (Spec.algebraMap K L)).mapIso e₀).symm ≪≫ e₁ ≪≫ e₂⟩⟩

end AlgebraicGeometry.Scheme.Hom
