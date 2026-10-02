/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Splitting extensions of quiver representations

Surjectivity of the vertex-and-arrow Hom differential implies that every extension of
its source representation by its target splits. Vertexwise linear sections always exist
over a field; the differential corrects their failure to commute with the arrows.

## References

H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1,
for the description of extensions by arrow maps modulo changes of vertex splittings.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open QuiverRep

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- An extension splits if its vertex-and-arrow Hom differential is surjective. No
finiteness or acyclicity hypothesis is needed. -/
theorem nonempty_splitting_of_surjective_homDifferential
    {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)} (hS : S.ShortExact)
    (hsurj : Function.Surjective (homDifferential S.X₃ S.X₁)) : Nonempty S.Splitting := by
  classical
  let E (i : Q) := (evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)
  have (i : Q) : (E i).PreservesZeroMorphisms := inferInstanceAs
    (((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)).PreservesZeroMorphisms)
  have (i : Q) : PreservesFiniteLimits (E i) := inferInstanceAs
    (PreservesFiniteLimits ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)))
  have (i : Q) : PreservesFiniteColimits (E i) := inferInstanceAs
    (PreservesFiniteColimits ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)))
  let sp (i : Q) : (S.map (E i)).Splitting :=
    (hS.map_of_exact (E i)).splittingOfProjective
  -- Choose vertexwise sections; their arrow defects land in the kernel of `g`.
  let s : HomVertex S.X₃ S.X₂ := fun i ↦ (sp i).s.hom
  let f : HomVertex S.X₁ S.X₂ := fun i ↦ (S.f.app i).hom
  let g : HomVertex S.X₂ S.X₃ := fun i ↦ (S.g.app i).hom
  have hsg (i : Q) (x : vertexSpace k Q S.X₃ i) : g i (s i x) = x :=
    congrArg (fun p ↦ p x) (sp i).s_g
  have hid (i : Q) (y : vertexSpace k Q S.X₂ i) :
      f i ((sp i).r.hom y) + s i (g i y) = y :=
    congrArg (fun p ↦ p y) (sp i).id
  let d := homDifferential S.X₃ S.X₂ s
  let c : HomArrow S.X₃ S.X₁ := fun i j a ↦ (sp j).r.hom.comp (d i j a)
  obtain ⟨h, hh⟩ := hsurj c
  have hdef (i j : Q) (a : i ⟶ j) : (f j).comp (c i j a) = d i j a := by
    have hg : (g j).comp (d i j a) = 0 := by
      ext x
      have hn : g j (mapₗ k Q S.X₂ a.toPath (s i x)) =
          mapₗ k Q S.X₃ a.toPath (g i (s i x)) :=
        congrArg (fun p ↦ p (s i x)) (S.g.naturality ((Paths.of Q).map a))
      simp only [d, homDifferential_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.zero_apply, map_sub, hn, hsg, sub_self]
    ext x
    have hz : g j (d i j a x) = 0 := congrArg (fun p ↦ p x) hg
    have hi := hid j (d i j a x)
    simp only [hz, map_zero, add_zero] at hi
    exact hi
  -- Correct the sections by a solution of the arrow defect equation.
  let s' : HomVertex S.X₃ S.X₂ := fun i ↦ s i - (f i).comp (h i)
  have hs' : s' ∈ (homDifferential S.X₃ S.X₂).ker := by
    rw [LinearMap.mem_ker, homDifferential_eq_zero_iff]
    intro i j a
    have hc := congrArg (fun p ↦ (f j).comp (p i j a)) hh
    rw [hdef i j a] at hc
    ext x
    have hx := congrArg (fun p ↦ p x) hc
    have hn : f j (mapₗ k Q S.X₁ a.toPath (h i x)) =
        mapₗ k Q S.X₂ a.toPath (f i (h i x)) :=
      congrArg (fun p ↦ p (h i x)) (S.f.naturality ((Paths.of Q).map a))
    simp only [s', d, homDifferential_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      map_sub] at hx ⊢
    rw [hn] at hx
    exact (sub_eq_sub_iff_sub_eq_sub).mp hx.symm
  -- Arrow-compatible vertex maps extend uniquely to a representation morphism.
  let sectionMap := (homEquivKerDifferential S.X₃ S.X₂).symm ⟨s', hs'⟩
  have hcalc (i : Q) (x : vertexSpace k Q S.X₃ i) : g i (s' i x) = x := by
    have hz : g i (f i (h i x)) = 0 :=
      congrArg (fun p ↦ p (h i x)) (congrArg (fun p ↦ p.app i) S.zero)
    simp only [s', LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hsg, hz, sub_zero]
  have hsectionVertex (i : Q) : sectionMap.app i ≫ S.g.app i = 𝟙 _ := by
    apply ModuleCat.hom_ext
    ext x
    have ha := homEquivKerDifferential_symm_apply S.X₃ S.X₂ ⟨s', hs'⟩ i
    have hv : g i ((sectionMap.app i).hom x) = g i (s' i x) :=
      congrArg (fun p ↦ g i (p.hom x)) ha
    exact hv.trans (hcalc i x)
  have hsection : sectionMap ≫ S.g = 𝟙 _ := by
    apply NatTrans.ext
    funext i
    exact hsectionVertex i
  exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact sectionMap hsection hS.mono_f⟩

end TauCeti
