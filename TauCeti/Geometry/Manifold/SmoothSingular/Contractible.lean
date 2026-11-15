/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy

/-!
# Smooth and singular chains of smoothly contractible manifolds

The smoothing theorem compares the smooth singular chains of a manifold `M` with its singular
chains: the inclusion `SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R` is a
quasi-isomorphism. Its proof is a Mayer–Vietoris induction over open sets, starting from open sets
that are convex in a chart. This file proves the comparison on every smoothly contractible
manifold, in particular on star-convex open subsets of normed spaces, and transports it along
diffeomorphisms, such as a chart from an open subset of its domain onto the image.

The comparison passes to smooth homotopy retracts. Let `f : M → N` and `g : N → M` be smooth maps
such that a smooth map `F : ℝ × M → M` joins `F (0, ·) = id` to `F (1, ·) = g ∘ f`. Both smooth
and singular homology are homotopy invariant
(`TauCeti.homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff`, and
`SSet.Homotopy.congr_homologyMap` for the restriction of `F` to `[0, 1] × M`), so in every degree
`f` and `g` exhibit the comparison map of `M` as a retract, in the arrow category, of that of `N`.
A retract of an isomorphism is an isomorphism, so if the comparison is a quasi-isomorphism for `N`
then it is one for `M` (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy`).

On a point every singular simplex is constant, hence smooth, so the smooth singular subcomplex is
everything and the comparison is an isomorphism
(`TauCeti.smoothSingularSubcomplex_eq_top`). A smoothly contractible manifold is a smooth homotopy
retract of a point, so the comparison is a quasi-isomorphism for it
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`). In particular it is
one for every star-convex open subset of a real normed space
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`), the empty set
included. Two diffeomorphic manifolds, possibly over different models, have the comparison
together (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph`).

The coefficients `R` lie in any preadditive category with coproducts and homology, as for the
homotopy invariance of smooth singular homology. No separation, countability, dimension or
boundary hypothesis is needed.

## Main results

* `TauCeti.smoothSingularSubcomplex_eq_top`: every singular simplex of a subsingleton charted space
  is smooth.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton`: the comparison on
  a point, or on the empty manifold.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy`: the comparison passes
  to smooth homotopy retracts.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph`: it is
  invariant under diffeomorphisms.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`: it holds on smoothly
  contractible manifolds.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`: it holds on
  star-convex open subsets of real normed spaces.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  base case of the comparison of smooth and singular homology).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

variable (I M) in
/-- **Every singular simplex of a point is smooth.** On a subsingleton charted space, such as a
point or the empty space, every singular simplex is constant, so the smooth singular subcomplex
is the whole singular simplicial set. -/
theorem smoothSingularSubcomplex_eq_top [Subsingleton M] : smoothSingularSubcomplex I M = ⊤ := by
  refine top_unique fun k σ _ ↦ (mem_smoothSingularSubcomplex_iff σ).2 ?_
  -- The simplex is the constant map at any of its values.
  have hσ : ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len) =
      fun _ ↦ (TopCat.of M).toSSetObjEquiv k σ (Convexity.StdSimplex.single 0) :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [hσ]
  exact contMDiffOnSubset_const I ∞ _

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C] [CategoryWithHomology C]
  (R : C)

variable (I M) in
/-- **The comparison on a point.** On a subsingleton charted space, such as a point or the empty
space, the inclusion of smooth singular chains into singular chains is a quasi-isomorphism; it is
even an isomorphism of chain complexes. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton [Subsingleton M] :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  -- The inclusion of the top subcomplex is an isomorphism.
  have key : ∀ A : (TopCat.toSSet.obj (TopCat.of M)).Subcomplex, A = ⊤ →
      QuasiIso (SSet.chainComplexMap A.ι R) := by
    rintro _ rfl
    rw [← SSet.Subcomplex.topIso_hom]
    infer_instance
  exact key _ (smoothSingularSubcomplex_eq_top I M)

/-- **The comparison passes to smooth homotopy retracts.** Let `f : M → N` and `g : N → M` be
smooth maps, and let a smooth map `F : ℝ × M → M` join `F (0, ·) = id` to `F (1, ·) = g ∘ f`. If
the inclusion of smooth singular chains into singular chains of `N` is a quasi-isomorphism, then
so is that of `M`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy {f : M → N} {g : N → M}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J I ∞ g) {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (h₀ : ∀ x, F (0, x) = x) (h₁ : ∀ x, F (1, x) = g (f x))
    (hN : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hNn : IsIso (SSet.homologyMap (smoothSingularSubcomplex J N).ι R n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  let tf : TopCat.of M ⟶ TopCat.of N := TopCat.ofHom ⟨f, hf.continuous⟩
  let tg : TopCat.of N ⟶ TopCat.of M := TopCat.ofHom ⟨g, hg.continuous⟩
  -- The restriction of `F` to `[0, 1] × M` is a homotopy from the identity to `g ∘ f`.
  let K : TopCat.Homotopy (𝟙 (TopCat.of M)) (tf ≫ tg) :=
    { toFun := fun p ↦ F (p.1, p.2)
      continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
      map_zero_left := h₀
      map_one_left := h₁ }
  have hsing : SSet.homologyMap (TopCat.toSSet.map tf) R n ≫
      SSet.homologyMap (TopCat.toSSet.map tg) R n = 𝟙 _ := by
    rw [← SSet.homologyMap_comp, ← Functor.map_comp, ← K.toSSet.congr_homologyMap R n,
      TopCat.toSSet.map_id, SSet.homologyMap_id]
  have hsmooth : SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
      SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n = 𝟙 _ := by
    rw [← SSet.homologyMap_comp, ← smoothSingularSubcomplexMap_comp,
      ← homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id (hg.comp hf) hF h₀
        h₁ n, smoothSingularSubcomplexMap_id, SSet.homologyMap_id]
  -- In degree `n`, `f` and `g` make the comparison of `M` a retract of the comparison of `N`.
  let h : RetractArrow (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)
      (SSet.homologyMap (smoothSingularSubcomplex J N).ι R n) :=
    { i := Arrow.homMk (SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n)
        (SSet.homologyMap (TopCat.toSSet.map tf) R n) (by
          simp only [Arrow.mk_hom, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι, tf])
      r := Arrow.homMk (SSet.homologyMap (smoothSingularSubcomplexMap g hg) R n)
        (SSet.homologyMap (TopCat.toSSet.map tg) R n) (by
          simp only [Arrow.mk_hom, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι, tg])
      retract := Arrow.hom_ext _ _ hsmooth hsing }
  exact (MorphismProperty.isomorphisms C).of_retract h hNn

/-- **The comparison is invariant under diffeomorphisms.** For a diffeomorphism `e : M ≃ N`,
possibly between manifolds over different models, the inclusion of smooth singular chains into
singular chains of `M` is a quasi-isomorphism exactly when that of `N` is. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_of_diffeomorph
    (e : M ≃ₘ⟮I, J⟯ N) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R) :=
  ⟨quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy R e.symm.contMDiff
      e.contMDiff contMDiff_snd (fun _ ↦ rfl) fun y ↦ (e.apply_symm_apply y).symm,
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy R e.contMDiff
      e.symm.contMDiff contMDiff_snd (fun _ ↦ rfl) fun x ↦ (e.symm_apply_apply x).symm⟩

/-- **The comparison on a smoothly contractible manifold.** If a smooth map `F : ℝ × M → M` joins
the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the inclusion of smooth
singular chains into singular chains of `M` is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :=
  -- `M` is a smooth homotopy retract of a point.
  quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_homotopy R
    (contMDiff_const (c := PUnit.unit) (I' := 𝓘(ℝ, PUnit.{u + 1})))
    (contMDiff_const (c := c)) hF h₀ h₁
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton 𝓘(ℝ, PUnit.{u + 1})
      PUnit.{u + 1} R)

/-- **The comparison on a star-convex open set.** For an open subset `U` of a real normed space,
star-convex about some point, the inclusion of smooth singular chains into singular chains of `U`
is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex 𝓘(ℝ, V) U).ι R) := by
  rcases (U : Set V).eq_empty_or_nonempty with hempty | hne
  · -- The empty set is a subsingleton.
    have : IsEmpty U := Set.isEmpty_coe_sort.2 hempty
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_subsingleton _ _ R
  obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex hU (hU.mem hne)
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF _ h₀ h₁

end TauCeti
