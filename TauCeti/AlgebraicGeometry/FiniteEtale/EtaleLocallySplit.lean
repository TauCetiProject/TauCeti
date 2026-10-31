/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.RingTheory.Etale.LocallySplit

/-!
# Finite étale morphisms split étale locally

Every finite étale morphism becomes a finite disjoint union of copies of the base on an
affine étale neighbourhood of each base point. The splitting is stated as an isomorphism in
the over-category with the spectrum of a finite product of copies of the neighbourhood's
coordinate ring. Thus it includes the scheme structures, not just the underlying points.
The empty cover is allowed, and no Noetherian hypothesis is needed.

The proof uses the affine comparison for finite étale schemes and the affine neighbourhood
splitting theorem `TauCeti.Algebra.Etale.exists_isFiniteSplit_etaleNeighborhood`.

## References

* [Stacks Project, Lemma 41.18.3](https://stacks.math.columbia.edu/tag/04HN).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale morphism is a finite disjoint union of copies of the base after passage to
an affine étale neighbourhood of any given base point. The splitting is over that neighbourhood,
and `g a = s` guarantees that the neighbourhood contains a point over the prescribed point. -/
@[stacks 04HN]
theorem exists_split_etaleLocally {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) :
    ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ S), Etale g ∧
      ∃ (a : Spec A), g a = s ∧ ∃ n : ℕ,
        Nonempty (Over.mk (pullback.snd f g) ≅
          Over.mk (Spec.algebraMap A (Fin n → A))) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let R := Γ(S, U)
  let j : Spec R ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range j := by
    rw [hU.range_fromSpec]
    exact hsU
  let f₀ := pullback.snd f j
  have : (TauCeti.FiniteEtaleScheme.spec.{u} R).EssSurj := by
    rw [← TauCeti.FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]
    infer_instance
  obtain ⟨B, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (TauCeti.FiniteEtaleScheme.spec R) (TauCeti.FiniteEtaleScheme.ofHom f₀)
  let eSpec : (algSpec R).obj (.op B.unop.obj) ≅
      Over.mk (Spec.algebraMap R B.unop.obj) :=
    Over.isoMk (Iso.refl _) (by
      -- The object wrapper of `algSpec` hides its structure map.
      erw [Category.id_comp, algSpec_obj_hom]
      rfl)
  have e' := (TauCeti.finiteEtaleSchemeProperty (Spec R)).ι.mapIso e
  rw [ObjectProperty.ι_obj, ObjectProperty.ι_obj, TauCeti.FiniteEtaleScheme.spec_obj_obj,
    TauCeti.FiniteEtaleScheme.ofHom_obj] at e'
  let e₀ : Over.mk (Spec.algebraMap R B.unop.obj) ≅ Over.mk f₀ := eSpec.symm ≪≫ e'
  obtain ⟨T, _, _, _, q, hq, hT⟩ :=
    TauCeti.Algebra.Etale.exists_isFiniteSplit_etaleNeighborhood R B.unop.obj p
  obtain ⟨n, ⟨φ⟩⟩ := hT.nonempty_algEquiv_fun
  let t := Spec.algebraMap R T
  let g := t ≫ j
  have : Etale t :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Etale g := inferInstanceAs (Etale (t ≫ j))
  refine ⟨.of T, g, inferInstance, q, ?_, n, ⟨?_⟩⟩
  · -- On points, the spectrum map is comap and composition is function composition.
    exact (congrArg j hq).trans hp
  · let e₁ : Over.mk (pullback.snd (Spec.algebraMap R B.unop.obj) t) ≅
        Over.mk (Spec.algebraMap T (T ⊗[R] B.unop.obj)) :=
      Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T B.unop.obj) (by
        simp [t, Spec.algebraMap, pullbackSpecIso_hom_fst'])
    let e₂ : Over.mk (Spec.algebraMap T (T ⊗[R] B.unop.obj)) ≅
        Over.mk (Spec.algebraMap T (Fin n → T)) :=
      Over.isoMk (Scheme.Spec.mapIso φ.toRingEquiv.toCommRingCatIso.symm.op) (by
        -- Contravariance identifies this spectrum map with `φ.symm` on rings.
        erw [← Spec.map_comp]
        apply congrArg Spec.map
        ext r
        exact φ.symm.commutes r)
    exact ((Over.pullbackComp t j).app (Over.mk f)) ≪≫
      ((Over.pullback t).mapIso e₀).symm ≪≫ e₁ ≪≫ e₂

end AlgebraicGeometry.Scheme.Hom
