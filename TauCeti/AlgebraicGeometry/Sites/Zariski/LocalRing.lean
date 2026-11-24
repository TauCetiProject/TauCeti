/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Torsors on the small Zariski site of a local ring

For a local ring `A`, the only open subset of `PrimeSpectrum A` (the underlying space of
`Spec A`) containing the closed point is the whole space, so every covering of the whole space
in the small Zariski site has the whole space as a member. Hence every torsor under a sheaf of
groups on this site has a global section, and `NonabelianH1 G` is a point for every sheaf of
groups `G`.

## Main declarations

* `CategoryTheory.Sheaf.NonabelianH1.subsingleton_of_isLocalRing`: for a local ring `A` and a
  sheaf of groups `G` on the small Zariski site of `PrimeSpectrum A`, `NonabelianH1 G` is a
  subsingleton.
-/

public section

open CategoryTheory TopologicalSpace

universe w u

namespace CategoryTheory.Sheaf.NonabelianH1

/-- On the small Zariski site of the spectrum of a local ring, every torsor under a sheaf of
groups is trivial: a covering of the whole space has a member containing the closed point, and
that member is the whole space. -/
instance subsingleton_of_isLocalRing (A : Type u) [CommRing A] [IsLocalRing A]
    (G : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) GrpCat.{w}) :
    Subsingleton (NonabelianH1 G) :=
  subsingleton_of_isTerminal_of_id_mem Limits.isTerminalTop fun S hS ↦ by
    obtain ⟨V, f, hf, hV⟩ :=
      (Opens.mem_grothendieckTopology _).1 hS (IsLocalRing.closedPoint A) trivial
    obtain rfl := (IsLocalRing.closedPoint_mem_iff V).1 hV
    rwa [Subsingleton.elim f (𝟙 ⊤)] at hf

end CategoryTheory.Sheaf.NonabelianH1
