/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.OpenUnitDisc.Adic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Quotient
import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Coordinate rings of the rational exhaustion of the open unit disc

For a complete nonarchimedean Tate field `K`, a unit `c`, and `n : ℕ`, the sections of the
closed-disc structure sheaf on `|T|^(n+1) ≤ |c|` are the topological ring

```text
K⟨T⟩⟨Y⟩ / (T^(n+1) - c Y).
```

Thus the notation `K⟨T, T^(n+1)/c⟩` describes an actual quotient presentation of the
coordinate ring, with the quotient topology. Taking `K = ℚ_[p]` and `c = p` gives the
coordinate rings of the rational closed discs exhausting the open p-adic unit disc.
The variable `Y` represents `T^(n+1)/c`; the denominator itself needs no extra variable.

The construction combines `presentationLimitRationalIso`, which computes sections on a
rational open, with `PairOfDefinition.rationalQuotientRingEquiv`, which presents its completed
localisation by generators and relations. Closedness of the relation ideal follows from
strong noetherianness of the Tate algebra, rather than being assumed.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 6.38 and Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §9.1.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] [IsTateRing K]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "X" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight
local notation "𝒯₂" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set 𝒯))
  isWeightFamily_one_weight
local notation "Y" => weightedX (fun _ : Fin 1 ↦ ({1} : Set 𝒯))
  isWeightFamily_one_weight 0
local notation "D" => weightedC (fun _ : Fin 1 ↦ ({1} : Set 𝒯)) isWeightFamily_one_weight

open scoped Classical in
/-- **The sections on an exhaustion disc have the presentation `K⟨T⟩⟨Y⟩/(T^(n+1)-cY)`**,
with its quotient topology. In particular both directions of this identification are continuous.
The result applies to every unit `c`; topological nilpotence is needed only when assembling
these discs into an exhaustion of the open unit disc. -/
noncomputable def discExhaustionSectionsIso (P : PairOfDefinition K) {c : K} (hc : IsUnit c)
    (n : ℕ) :
    ((closedPolydiscPreAdicSpace 1 P).toPresheafedSpace.presheaf.obj
      (op (discExhaustionOpen c P n))).obj ≅
        TopCommRingCat.of (𝒯₂ ⧸ Ideal.span {D (X ^ (n + 1)) - D (C c) * Y}) := by
  classical
  let Q := P.weighted (T := fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight
  let F : Finset 𝒯 := {X ^ (n + 1), C c}
  let hF := isOpen_span_discExhaustionNumerators hc n
  let hden := hasDenominatorPower_of_isOpen_span Q F (C c) (Localization.Away (C c)) hF
  let d : Presentation Q := ⟨F, C c, hden⟩
  letI := locUniformSpace Q F (C c) (Localization.Away (C c)) hden
  letI := isUniformAddGroup_locUniformSpace Q F (C c) (Localization.Away (C c)) hden
  letI := isTopologicalRing_locUniformSpace Q F (C c) (Localization.Away (C c)) hden
  let t : Fin 1 → 𝒯 := fun _ ↦ X ^ (n + 1)
  have ht : ∀ i, t i ∈ F := fun _ ↦ by simp [t, F]
  have hsplit : ∀ u ∈ F, u = C c ∨ u ∈ Set.range t := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl (Finset.mem_singleton.mp hu)
  have hspan : Ideal.span (insert (C c) (F : Set 𝒯)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) (hc.map C)
  have hcl := (rationalRelationIdeal t (C c)).isClosed_weightedRestrictedSubring_one_weight
  let e := rationalQuotientRingEquiv Q F (C c) (Localization.Away (C c)) hden
    t ht hsplit hspan hcl
  let E : TopCommRingCat.of (𝒯₂ ⧸ rationalRelationIdeal t (C c)) ≅
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away (C c))) :=
    { hom := ⟨e.toRingHom, continuous_rationalQuotientRingEquiv ..⟩
      inv := ⟨e.symm.toRingHom, continuous_rationalQuotientRingEquiv_symm ..⟩
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }
  have hJ : rationalRelationIdeal t (C c) =
      Ideal.span {D (X ^ (n + 1)) - D (C c) * Y} := by
    simp [rationalRelationIdeal_def, t, Fin.eq_zero]
  have hsource : ((closedPolydiscPreAdicSpace 1 P).toPresheafedSpace.presheaf.obj
      (op (discExhaustionOpen c P n))).obj =
      (presentationLimit (P := Q) (powerBoundedSubring 𝒯)
        (spaBasicOpen (powerBoundedSubring 𝒯) F (C c))).obj := by
    rw [discExhaustionOpen_def, closedPolydiscBasicOpen_sections]
  exact (eqToIso hsource ≪≫ (TopCommRingCat.isCompleteSeparated.ι.mapIso
      (presentationLimitRationalIso (powerBoundedSubring 𝒯)
        (fun _ ha ↦ mem_powerBoundedSubring.mp ha) d hF)) ≪≫
      eqToIso (completionLocObj_obj Q F (C c) (Localization.Away (C c)) hden) ≪≫ E.symm ≪≫
      eqToIso (congrArg (fun I : Ideal 𝒯₂ ↦ TopCommRingCat.of (𝒯₂ ⧸ I)) hJ) :)

section Padic

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

local notation "𝒜" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p]))
  isWeightFamily_one_weight
local notation "Xp" => weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p]))
  isWeightFamily_one_weight 0
local notation "Cp" => weightedC (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight
local notation "𝒜₂" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set 𝒜))
  isWeightFamily_one_weight
local notation "Yp" => weightedX (fun _ : Fin 1 ↦ ({1} : Set 𝒜))
  isWeightFamily_one_weight 0
local notation "Dp" => weightedC (fun _ : Fin 1 ↦ ({1} : Set 𝒜)) isWeightFamily_one_weight

open scoped Classical in
/-- The sections on the `n`-th rational closed disc of the open p-adic unit disc are
`ℚ_p⟨T⟩⟨Y⟩/(T^(n+1)-pY)`, with the quotient topology. -/
noncomputable example :
    ((closedPolydiscPreAdicSpace 1 (Padic.pairOfDefinition (p := p))).toPresheafedSpace.presheaf.obj
      (op (discExhaustionOpen (p : ℚ_[p]) Padic.pairOfDefinition n))).obj ≅
        TopCommRingCat.of (𝒜₂ ⧸ Ideal.span {Dp (Xp ^ (n + 1)) - Dp (Cp p) * Yp}) :=
  discExhaustionSectionsIso Padic.pairOfDefinition Padic.isPseudoUniformizer_p.isUnit n

end Padic

end TauCeti.ValuationSpectrum
