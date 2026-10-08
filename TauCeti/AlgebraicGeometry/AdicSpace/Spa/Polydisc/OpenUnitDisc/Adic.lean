/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.OpenUnitDisc.Topology

/-!
# The open unit disc as an adic space

The open unit disc over a complete nonarchimedean Tate field is the open subspace of the closed
unit disc exhausted by the rational subsets

```text
|T|^(n+1) ≤ |c| ≠ 0.
```

Here `c` is a pseudouniformiser.  Restricting the presentation-limit structure of the closed disc
to this open union gives the open unit disc as an adic space.  Each member of the exhaustion is an
open affinoid subspace, with the rational-localisation coordinate ring attached to the
presentation `R({T^(n+1), c}/c)`.

## Main definitions

* `TauCeti.ValuationSpectrum.discExhaustionOpen`: the rational exhaustion members as opens of
  the closed-disc pre-adic space.
* `TauCeti.ValuationSpectrum.openUnitDiscPreAdicSpace`: the restriction of the closed disc to
  their union.
* `TauCeti.ValuationSpectrum.openUnitDiscAdicSpace`: the resulting object of the category of
  adic spaces.

## Main results

* `TauCeti.ValuationSpectrum.discExhaustionOpen_mem_affinoidOpens`: every exhaustion member is
  an open affinoid subspace with its rational-localisation coordinate ring.
* `TauCeti.ValuationSpectrum.isAdic_openUnitDiscPreAdicSpace`: the open unit disc is an adic
  space.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57 and
  Definition 8.22.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §9.1, for the open unit disc.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] [IsTateRing K]

variable (c : K) (P : PairOfDefinition K)

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "X" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-- The `n`-th rational member of the open-disc exhaustion, as an open of the closed-disc
pre-adic space. -/
noncomputable def discExhaustionOpen (n : ℕ) :
    Opens (closedPolydiscPreAdicSpace 1 P) := by
  classical
  exact closedPolydiscBasicOpen 1 P {X ^ (n + 1), C c} (C c)

/-- The open unit disc, as the union of the rational exhaustion opens in the closed-disc
pre-adic space. -/
noncomputable def openUnitDiscOpen (_hc : IsPseudoUniformizer c) :
    Opens (closedPolydiscPreAdicSpace 1 P) :=
  ⨆ n, discExhaustionOpen c P n

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- The open unit disc is the union of its rational exhaustion opens. -/
theorem openUnitDiscOpen_eq_iSup (hc : IsPseudoUniformizer c) :
    openUnitDiscOpen c P hc = ⨆ n, discExhaustionOpen c P n :=
  (rfl)

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- Every rational exhaustion open lies in the open unit disc. -/
theorem discExhaustionOpen_le_openUnitDiscOpen (hc : IsPseudoUniformizer c) (n : ℕ) :
    discExhaustionOpen c P n ≤ openUnitDiscOpen c P hc := by
  rw [openUnitDiscOpen_eq_iSup]
  exact le_iSup (discExhaustionOpen c P) n

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- Each member of the open-disc exhaustion is an open affinoid subspace of the closed disc.
Its coordinate ring is the completed rational localisation for
`R({T^(n+1), c}/c)`. -/
theorem discExhaustionOpen_mem_affinoidOpens (hc : IsPseudoUniformizer c) (n : ℕ) :
    discExhaustionOpen c P n ∈ (closedPolydiscPreAdicSpace 1 P).affinoidOpens := by
  classical
  have hspan : Ideal.span (({X ^ (n + 1), C c} : Finset 𝒯) : Set 𝒯) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) (hc.isUnit.map C)
  apply closedPolydiscBasicOpen_mem_affinoidOpens
  rw [hspan]
  exact isOpen_univ

/-- The open unit disc as the restriction of the closed-disc pre-adic space to its rational
exhaustion. -/
noncomputable def openUnitDiscPreAdicSpace (hc : IsPseudoUniformizer c) : PreAdicSpace.{u} :=
  (closedPolydiscPreAdicSpace 1 P).restrict (openUnitDiscOpen c P hc).isOpenEmbedding

omit [IsUltrametricDist K] [CompleteSpace K] [IsTateRing K] in
/-- The open-disc pre-adic space is the restriction of the closed disc to the union of its
rational exhaustion opens. -/
lemma openUnitDiscPreAdicSpace_def (hc : IsPseudoUniformizer c) :
    openUnitDiscPreAdicSpace c P hc =
      (closedPolydiscPreAdicSpace 1 P).restrict (openUnitDiscOpen c P hc).isOpenEmbedding :=
  (rfl)

/-- The open unit disc is an adic space. -/
theorem isAdic_openUnitDiscPreAdicSpace (hc : IsPseudoUniformizer c) :
    PreAdicSpace.isAdic (openUnitDiscPreAdicSpace c P hc) :=
  PreAdicSpace.isAdic_restrict (openUnitDiscOpen c P hc).isOpenEmbedding
    (isAdic_closedPolydiscPreAdicSpace 1 P)

/-- The open unit disc as an object of the category of adic spaces. -/
noncomputable def openUnitDiscAdicSpace (hc : IsPseudoUniformizer c) : AdicSpace.{u} :=
  ⟨openUnitDiscPreAdicSpace c P hc, isAdic_openUnitDiscPreAdicSpace c P hc⟩

/-- The pre-adic space underlying `openUnitDiscAdicSpace` is the open-disc restriction. -/
@[simp]
theorem openUnitDiscAdicSpace_obj (hc : IsPseudoUniformizer c) :
    (openUnitDiscAdicSpace c P hc).obj = openUnitDiscPreAdicSpace c P hc :=
  (rfl)

end TauCeti.ValuationSpectrum

end
