/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.EtaleEquivRel

/-!
# The étale equivalence relation of an étale atlas

Let `a : h_U ⟶ F` be an étale atlas of a presheaf `F` on schemes. Since `a` is representable by
schemes, its kernel pair `h_U ×_F h_U` is represented by a scheme `R = U ×_F U`, with projections
`t = ha.relativelyRepresentable.fst' a` and `s = ha.relativelyRepresentable.snd a` to `U`. This
file shows that `(s, t)` is an étale equivalence relation on `U` in the sense of Stacks, Spaces,
Definition 65.9.2 (02WS).

`R` is not the kernel pair of a morphism of schemes, since `F` need not be a scheme, so the
kernel pair criterion `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_isKernelPair` does not
apply directly. Instead, for every scheme `T`, two points `u, v : T ⟶ U` are related by `R`
exactly when they have the same image `h_u ≫ a = h_v ≫ a` in `F(T)`
(`TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.ofPairHom_iff`), which is an equivalence relation;
the projections are jointly monic by the universal property of the pullback. The projection `s`
is a base change of `a`, hence étale, and `t` is `s` composed with the automorphism of `R`
exchanging the factors.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.ofPairHom_iff`: `R` relates `u` to `v` exactly
  when `h_u ≫ a = h_v ≫ a`.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_etaleAtlas`: the kernel pair of an étale
  atlas is an étale equivalence relation.

## References

* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry TauCeti.CategoryTheory

universe u

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F}

/-- Two points `u, v : T ⟶ U` are related by the kernel pair `U ×_F U` of an étale atlas
`a : h_U ⟶ F` exactly when they have the same image in `F(T)`. -/
theorem EtaleAtlas.ofPairHom_iff (ha : EtaleAtlas a) {T : Scheme.{u}} {u v : T ⟶ U} :
    Rel.ofPairHom (ha.relativelyRepresentable.fst' a) (ha.relativelyRepresentable.snd a) T u v ↔
      yoneda.map u ≫ a = yoneda.map v ≫ a := by
  rw [Rel.ofPairHom_iff]
  refine ⟨?_, fun h ↦ ⟨_, ha.relativelyRepresentable.lift'_fst u v h,
    ha.relativelyRepresentable.lift'_snd u v h⟩⟩
  rintro ⟨r, rfl, rfl⟩
  simp only [Functor.map_comp, Category.assoc, (ha.relativelyRepresentable.isPullback' a).w]

/-- **The kernel pair of an étale atlas is an étale equivalence relation.** For an étale atlas
`a : h_U ⟶ F`, the scheme `U ×_F U` representing the kernel pair of `a`, with its two projections
to `U`, is an étale equivalence relation on `U`. -/
theorem EtaleEquivRel.of_etaleAtlas (ha : EtaleAtlas a) :
    EtaleEquivRel (ha.relativelyRepresentable.snd a) (ha.relativelyRepresentable.fst' a) := by
  set hr := ha.relativelyRepresentable
  refine ⟨isEquivalenceRelation_iff.mpr ⟨⟨fun _ _ _ h₁ h₂ ↦ hr.hom_ext' h₁ h₂⟩, fun T ↦ ?_⟩,
    ha.etale_snd a, ?_⟩
  · refine ⟨fun u ↦ ha.ofPairHom_iff.mpr rfl, fun h ↦ ha.ofPairHom_iff.mpr ?_,
      fun h h' ↦ ha.ofPairHom_iff.mpr ?_⟩
    · exact (ha.ofPairHom_iff.mp h).symm
    · exact (ha.ofPairHom_iff.mp h).trans (ha.ofPairHom_iff.mp h')
  · have := ha.etale_snd a
    rw [← hr.symmetry_snd hr]
    infer_instance

end TauCeti.AlgebraicGeometry.Spaces
