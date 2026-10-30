/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import TauCeti.Topology.GTopology.SlightlyFiner

/-!
# Sheaves on a slightly finer G-topology

Let `G'` be a G-topology on `X` that is slightly finer than `G` (`GTopology.SlightlyFiner`), and
let `f` be the identity of `X`, viewed as a continuous map from `G'` to `G`. The functor
`f.comapFunctor`, which regards a `G`-admissible open as a `G'`-admissible open, exhibits the site
of `G` as a dense subsite of the site of `G'` (`GTopology.SlightlyFiner.isDenseSubsite`):
every `G'`-admissible open is covered by `G`-admissible opens, and a sieve on a `G`-admissible
open covers for `G` exactly when its image covers for `G'`.

Mathlib's comparison lemma for dense subsites then shows that restriction of sheaves from `G'`
to `G` is an equivalence of categories, for sheaves with values in any category with the
relevant limits (`GTopology.SlightlyFiner.sheafEquiv`). This is [BGR, 9.2.3/1]: every sheaf
on `G` extends uniquely to a sheaf on `G'`. No new category of sheaves is constructed; both
sides are Mathlib's `Sheaf` on the sites `GTopology.grothendieckTopology`. In particular the
sheaves on any G-topology are the sheaves on its finest slightly finer G-topology
`GTopology.finestSlightlyFiner`, which satisfies (G0)–(G2)
(`GTopology.finestSlightlyFinerSheafEquiv`).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§9.1.2 and 9.2.3.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe u v v' w w'

namespace GTopology

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}
  {B' : Type v'} [SemilatticeInf B'] [OrderTop B'] {ι' : B' ↪o Set X}
  {G : GTopology ι} {G' : GTopology ι'}

namespace SlightlyFiner

variable (h : G'.SlightlyFiner G) (f : G'.ContinuousMap G) (hf : ∀ x, f x = x)
include h hf

/-- If `G'` is slightly finer than `G`, the functor regarding `G`-admissible opens as
`G'`-admissible opens exhibits the site of `G` as a dense subsite of the site of `G'`. This is the
comparison behind [BGR, 9.2.3/1]. -/
theorem isDenseSubsite :
    f.comapFunctor.IsDenseSubsite G.grothendieckTopology G'.grothendieckTopology := by
  have hι (U : B) : ι' (f.comapFunctor.obj U) = ι U := by
    rw [ContinuousMap.comapFunctor_obj, f.coe_comap_of_forall_eq hf]
  have := f.full_comapFunctor fun x ↦ ⟨x, hf x⟩
  refine
    { isCoverDense' := ⟨fun V ↦ ?_⟩
      functorPushforward_mem_iff := fun {U S} ↦ ⟨fun hS ↦ ?_, fun hS ↦ ?_⟩ }
  · -- Every `G'`-admissible open has a `G'`-cover by `G`-admissible opens.
    obtain ⟨S, hS, hSG⟩ := h.exists_covers V
    refine (mem_grothendieckTopology_iff G').mpr ⟨S, hS, fun W g hW ↦ ?_⟩
    obtain ⟨U, hU⟩ := hSG W ((coverPresieve_apply _ g).mp hW)
    have hWU : f.comapFunctor.obj U = W := ι'.injective (by rw [hι, hU])
    exact ⟨⟨U, eqToHom hWU.symm, eqToHom hWU ≫ g, Subsingleton.elim _ _⟩⟩
  · -- A `G'`-cover of a `G`-admissible open contained in the image sieve is refined by a
    -- `G`-cover, whose members then lie in the original sieve.
    obtain ⟨S', hS', hS'S⟩ := (mem_grothendieckTopology_iff G').mp hS
    obtain ⟨R, hR, hRS'⟩ := h.exists_refinement (hι U) hS'
    refine (mem_grothendieckTopology_iff G).mpr ⟨R, hR, fun W g hW ↦ ?_⟩
    obtain ⟨W', hW', hWW'⟩ := hRS' W ((coverPresieve_apply _ g).mp hW)
    obtain ⟨Z, g', k, hg', -⟩ :=
      hS'S _ (homOfLE (G'.subset hS' W' hW')) ((coverPresieve_apply _ _).mpr hW')
    have hWZ : W ≤ Z := ι.le_iff_le.mp <|
      hWW'.trans ((ι'.le_iff_le.mpr (leOfHom k)).trans (hι Z).le)
    exact (Subsingleton.elim (homOfLE hWZ ≫ g') g) ▸ S.downward_closed hg' (homOfLE hWZ)
  · exact f.coverPreserving_comapFunctor.cover_preserve hS

variable (A : Type w) [Category.{w'} A]
  [∀ V, HasLimitsOfShape (StructuredArrow V f.comapFunctor.op) A]

/-- If `G'` is slightly finer than `G`, restricting sheaves from `G'` to `G` is an equivalence of
categories [BGR, 9.2.3/1]. -/
theorem isEquivalence_sheafPushforwardContinuous :
    (f.comapFunctor.sheafPushforwardContinuous A G.grothendieckTopology
      G'.grothendieckTopology).IsEquivalence :=
  have := h.isDenseSubsite f hf
  inferInstance

/-- If `G'` is slightly finer than `G`, every sheaf on `G` extends uniquely to a sheaf on `G'`
[BGR, 9.2.3/1]: the categories of sheaves on the two sites are equivalent, and the inverse of the
equivalence is restriction of sheaves from `G'` to `G`. -/
noncomputable def sheafEquiv : Sheaf G.grothendieckTopology A ≌ Sheaf G'.grothendieckTopology A :=
  have := h.isEquivalence_sheafPushforwardContinuous f hf A
  (f.comapFunctor.sheafPushforwardContinuous A _ _).asEquivalence.symm

/-- The inverse of `GTopology.SlightlyFiner.sheafEquiv` is restriction of sheaves. -/
@[simp]
theorem sheafEquiv_inverse : (h.sheafEquiv f hf A).inverse =
    f.comapFunctor.sheafPushforwardContinuous A G.grothendieckTopology G'.grothendieckTopology :=
  (rfl)

end SlightlyFiner

/-- The sheaves on a G-topology are equivalent to the sheaves on the finest G-topology slightly
finer than it, which satisfies (G0)–(G2). The inverse of the equivalence is restriction. -/
noncomputable def finestSlightlyFinerSheafEquiv (G : GTopology ι) (A : Type w) [Category.{w'} A]
    [∀ V, HasLimitsOfShape (StructuredArrow V G.finestSlightlyFinerId.comapFunctor.op) A] :
    Sheaf G.grothendieckTopology A ≌ Sheaf G.finestSlightlyFiner.grothendieckTopology A :=
  G.slightlyFiner_finestSlightlyFiner.sheafEquiv G.finestSlightlyFinerId
    (fun x ↦ by rw [coe_finestSlightlyFinerId, id]) A

end GTopology

end TauCeti
