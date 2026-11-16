/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.Basic
public import TauCeti.Topology.Sober

/-!
# Binary products of prespectral, quasiseparated, and spectral spaces

This file supplies binary product instances for `PrespectralSpace`, `QuasiSeparatedSpace` (on
prespectral factors), and `SpectralSpace`.

Boxes `U ×ˢ V` of compact open subsets form a basis of compact opens of `X × Y`, giving
`PrespectralSpace.prod`; when both factors are also quasiseparated, the intersection of two such
boxes is again a product of compact opens, giving `QuasiSeparatedSpace.prod`. Together with
`QuasiSober.prod` (from `TauCeti.Topology.Sober`) and Mathlib's product instances for `T0Space` and
`CompactSpace`, these assemble directly into `SpectralSpace.prod`.

These instances are used whenever equivalence relations or morphisms are studied through their
graphs in `X × X` or `X × Y`.

## Main results

* `PrespectralSpace.prod`: binary products of prespectral spaces are prespectral.
* `QuasiSeparatedSpace.prod`: binary products of quasiseparated prespectral spaces are
  quasiseparated.
* `SpectralSpace.prod`: binary products of spectral spaces are spectral.
-/

public section

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The product of two prespectral spaces is prespectral. -/
instance PrespectralSpace.prod [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace (X × Y) := by
  refine .of_isTopologicalBasis
    (PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis) ?_
  rintro _ ⟨U, ⟨_, hUc⟩, V, ⟨_, hVc⟩, rfl⟩
  exact hUc.prod hVc

/-- The product of two quasiseparated prespectral spaces is quasiseparated. -/
instance QuasiSeparatedSpace.prod [PrespectralSpace X] [PrespectralSpace Y]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] : QuasiSeparatedSpace (X × Y) := by
  have hb := (PrespectralSpace.isTopologicalBasis (X := X)).prod
    (PrespectralSpace.isTopologicalBasis (X := Y))
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := Subtype.val)
    (by rwa [Subtype.range_coe]) ?_
  rintro ⟨_, U₁, ⟨hU₁o, hU₁c⟩, V₁, ⟨hV₁o, hV₁c⟩, rfl⟩
    ⟨_, U₂, ⟨hU₂o, hU₂c⟩, V₂, ⟨hV₂o, hV₂c⟩, rfl⟩
  rw [Set.prod_inter_prod]
  exact (hU₁c.inter_of_isOpen hU₂c hU₁o hU₂o).prod
    (hV₁c.inter_of_isOpen hV₂c hV₁o hV₂o)

/-- The product of two spectral spaces is spectral. -/
instance SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) where
