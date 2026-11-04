/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# Gluing relative cohomology classes over a filtered union

Relative cohomology does not in general turn filtered unions into inverse limits. If the
relative homology of every member vanishes below degree `n`, it does so in degree `n`:
compatible classes extend uniquely. Compact absorption on both spaces of the pair gives
the homology colimit, and the universal coefficient theorem identifies degree `n`
cohomology with linear maps from degree `n` homology.

This applies to Thom pairs over finite unions of trivializing open sets, whose relative
homology vanishes below the fibre dimension.

## References

* A. Hatcher, *Algebraic Topology*, §3.1 (the universal coefficient theorem).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §10 (local Thom classes).
-/

public section

noncomputable section

open CategoryTheory Limits Topology TopCat

universe w

namespace TopPair

variable {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
  {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ TopPair.{w}} (c : Cocone D)

/-- Compatible relative cohomology classes on a compact-absorbing filtered union extend
uniquely in degree `n` if the homology of every member vanishes below `n`. -/
theorem existsUnique_singularCohomology_of_directedUnion
    (hfst : ∀ j, IsEmbedding (Hom.fst (c.ι.app j)))
    (hfstK : ∀ K : Set c.pt.fst, IsCompact K → ∃ j, K ⊆ Set.range (Hom.fst (c.ι.app j)))
    (hsndK : ∀ K : Set c.pt.snd, IsCompact K → ∃ j, K ⊆ Set.range (Hom.snd (c.ι.app j)))
    (n : ℕ) (hzero : ∀ j m, m < n → IsZero ((D.obj j).singularHomology R m))
    (u : ∀ j, (D.obj j).singularCohomology R k M n)
    (hu : ∀ {i j} (f : i ⟶ j), TopPair.singularCohomologyMap (D.map f) n (u j) = u i) :
    ∃! x : c.pt.singularCohomology R k M n,
      ∀ j, TopPair.singularCohomologyMap (c.ι.app j) n x = u j := by
  let hc (m : ℕ) := isColimitMapCoconeSingularHomology R m c hfst hfstK hsndK
  have hz (m : ℕ) (hm : m < n) : IsZero (c.pt.singularHomology R m) := by
    have hobj : IsZero ((singularHomologyFunctor R m).obj c.pt) := by
      refine (IsZero.iff_id_eq_zero _).2 ((hc m).hom_ext fun j ↦ ?_)
      exact ((hzero j m hm).of_iso
        (eqToIso (singularHomologyFunctor_obj (D.obj j) R m))).eq_of_src _ _
    exact hobj.of_iso (eqToIso (singularHomologyFunctor_obj c.pt R m)).symm
  have hbij := c.pt.singularKronecker_bijective_of_projective_homology_lt R M n
    fun m hm ↦ (hz m hm).projective
  let s : Cocone (D ⋙ singularHomologyFunctor R n) :=
    { pt := M
      ι :=
        { app j := eqToHom (singularHomologyFunctor_obj (D.obj j) R n) ≫
            (D.obj j).singularKronecker k n (u j)
          naturality i j f := by
            simp only [Functor.comp_map, singularHomologyFunctor_map, Category.assoc,
              eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
              ← singularKronecker_naturality, Functor.const_obj_map, Functor.const_obj_obj]
            rw [hu f, Category.comp_id] } }
  let φ := eqToIso (singularHomologyFunctor_obj c.pt R n)
  obtain ⟨x, hx⟩ := hbij.2 (φ.inv ≫ (hc n).desc s)
  have hxj (j : J) : TopPair.singularCohomologyMap (c.ι.app j) n x = u j := by
    apply ((D.obj j).singularKronecker_bijective_of_projective_homology_lt R M n
      fun m hm ↦ (hzero j m hm).projective).1
    rw [singularKronecker_naturality]
    dsimp only [Functor.const_obj_obj]
    rw [hx]
    have hfac := (hc n).fac s j
    apply (cancel_epi (eqToHom (singularHomologyFunctor_obj (D.obj j) R n))).1
    simpa only [Functor.mapCocone_ι_app, singularHomologyFunctor_map, Category.assoc,
      s, φ, eqToIso.inv, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hfac
  refine ⟨x, hxj, fun y hy ↦ hbij.1 ?_⟩
  apply (cancel_epi φ.hom).1
  refine (hc n).hom_ext fun j ↦ ?_
  simp only [Functor.mapCocone_ι_app, singularHomologyFunctor_map, Category.assoc,
    φ, eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← singularKronecker_naturality, ← singularKronecker_naturality, hy j, hxj j]

end TopPair
