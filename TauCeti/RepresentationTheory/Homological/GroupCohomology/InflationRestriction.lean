/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.DimensionShift
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The inflation-restriction sequence in every positive degree

Let `S` be a normal subgroup of a group `G` and `A` a representation of `G`. Inflation and
restriction form a complex

`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)`,

and if `Hⁱ(S, A) = 0` for `0 < i ≤ n`, it is exact and inflation is injective (Milne II 1.34).
Mathlib proves the case `n = 0`, where there is no hypothesis, as `groupCohomology.H1InfRes`.

The hypotheses concern the cohomology of `A` restricted to `S` in degrees below the degree of
the complex. The file provides injectivity and exactness under these hypotheses.

When `Hⁱ(S, A)` vanishes also in degree `n + 1`, inflation is an isomorphism
(`isIso_infRes_f`). This is the form used for Tate's cohomological triviality criterion, where a
module is shown to be cohomologically trivial by induction along a normal series.

## Main definitions

* `TauCeti.groupCohomology.infRes`: the complex `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)`.

## Main statements

* `TauCeti.groupCohomology.mono_infRes_f`: inflation is injective.
* `TauCeti.groupCohomology.infRes_exact`: the inflation-restriction sequence is exact.
* `TauCeti.groupCohomology.isIso_infRes_f`: inflation is an isomorphism when `Hⁱ(S, A) = 0` for
  `0 < i ≤ n + 1`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, Proposition 1.34.
* J.-P. Serre, *Local Fields*, Chapter VII, §6, Proposition 5.
* `ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean` in `kbuzzard/ClassFieldTheory`,
  commit `ccc3323c6750abca25b49b35106f54eb3a398509`, states `inflation_restriction_mono` and
  `inflation_restriction_exact` and uses the same dimension-shifting argument.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- Inflation followed by restriction vanishes in every positive degree. -/
theorem map_mk'_comp_map_subtype_succ (n : ℕ) :
    (map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) (n + 1) :
      groupCohomology (A.quotientToInvariants S) (n + 1) ⟶ groupCohomology A (n + 1)) ≫
      map S.subtype (𝟙 _) (n + 1) = 0 := by
  rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ (n + 1)), map_one_succ]

/-- The **inflation-restriction complex** `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)` in degree
`n + 1`. In degree one it is Mathlib's `groupCohomology.H1InfRes`. -/
-- The exported component lemmas below require exposure: without it Lean cannot type-check their
-- dependent morphism types or validate their definitional equalities across the module boundary.
@[expose] def infRes (n : ℕ) : ShortComplex (ModuleCat k) :=
  ShortComplex.mk
    (map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) (n + 1) :
      groupCohomology (A.quotientToInvariants S) (n + 1) ⟶ groupCohomology A (n + 1))
    (map S.subtype (𝟙 _) (n + 1)) (map_mk'_comp_map_subtype_succ A S n)

/-- The inflation-restriction complex as a short complex of the two maps. -/
theorem infRes_def (n : ℕ) :
    infRes A S n = ShortComplex.mk
      (map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) (n + 1) :
        groupCohomology (A.quotientToInvariants S) (n + 1) ⟶ groupCohomology A (n + 1))
      (map S.subtype (𝟙 _) (n + 1)) (map_mk'_comp_map_subtype_succ A S n) := by
  rfl

/-- The first term of the inflation-restriction complex. -/
@[simp]
theorem infRes_X₁ (n : ℕ) :
    (infRes A S n).X₁ = groupCohomology (A.quotientToInvariants S) (n + 1) := rfl

/-- The middle term of the inflation-restriction complex. -/
@[simp]
theorem infRes_X₂ (n : ℕ) : (infRes A S n).X₂ = groupCohomology A (n + 1) := rfl

/-- The last term of the inflation-restriction complex. -/
@[simp]
theorem infRes_X₃ (n : ℕ) :
    (infRes A S n).X₃ = groupCohomology (res S.subtype A) (n + 1) := rfl

/-- The inflation map in the inflation-restriction complex. -/
@[simp]
theorem infRes_f (n : ℕ) :
    (infRes A S n).f =
      map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) (n + 1) := rfl

/-- The restriction map in the inflation-restriction complex. -/
@[simp]
theorem infRes_g (n : ℕ) :
    (infRes A S n).g = map S.subtype (𝟙 _) (n + 1) := rfl

/-- In degree one, `infRes` is Mathlib's `H1InfRes`. -/
@[simp]
theorem infRes_zero : infRes A S 0 = H1InfRes A S := rfl

-- The two statements are proved together, by induction on the degree.
private theorem mono_infRes_f_and_exact (n : ℕ) : ∀ A : Rep k G,
    (∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) →
      Mono (infRes A S n).f ∧ (infRes A S n).Exact := by
  induction n with
  | zero =>
    intro A _
    rw [infRes_zero]
    exact ⟨inferInstance, H1InfRes_exact A S⟩
  | succ n ih =>
    intro A hA
    -- The upward dimension-shifting sequence `0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0`.
    let X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)
    have hX : X.ShortExact := by
      simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A
    have hXS : (X.map (resFunctor S.subtype)).ShortExact := by
      simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_res_shortExact A S.subtype
    have hY : (X.map (quotientToInvariantsFunctor k S)).ShortExact :=
      shortExact_map_quotientToInvariantsFunctor S hX (hA 0 n.succ_pos)
    obtain ⟨hmono, hexact⟩ := ih (dimensionShiftUp A) fun i hi =>
      (isZero_res_dimensionShiftUp_iff A S i).2 (hA (i + 1) (by omega))
    let e₁ : (infRes (dimensionShiftUp A) S n).X₁ ≅ (infRes A S (n + 1)).X₁ :=
      (map_cochainsFunctor_shortExact hY).δIso (n + 1) (n + 2) rfl
      (isZero_quotientToInvariants_coindBot_succ S A.V n)
      (isZero_quotientToInvariants_coindBot_succ S A.V (n + 1))
    let Φ : (X.map (quotientToInvariantsFunctor k S)).map (resFunctor (QuotientGroup.mk' S)) ⟶ X :=
      { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
        τ₂ := ofHom ((coindBot k G A.V).ρ.quotientToInvariants_lift S)
        τ₃ := ofHom ((dimensionShiftUp A).ρ.quotientToInvariants_lift S)
        -- `quotientToInvariantsFunctor.map` acts by the underlying representation map.
        comm₁₂ := by ext; rfl
        comm₂₃ := by ext; rfl }
    have h₁₂ : e₁.hom ≫ (infRes A S (n + 1)).f =
        (infRes (dimensionShiftUp A) S n).f ≫ (dimensionShiftUpIso A n).hom := by
      rw [dimensionShiftUpIso_hom]
      exact δ_naturality (QuotientGroup.mk' S) hY hX Φ (n + 1) (n + 2) rfl
    have h₂₃ : (dimensionShiftUpIso A n).hom ≫ (infRes A S (n + 1)).g =
        (infRes (dimensionShiftUp A) S n).g ≫ (dimensionShiftUpResIso A S n).hom := by
      rw [dimensionShiftUpIso_hom, dimensionShiftUpResIso_hom]
      exact δ_naturality S.subtype hX hXS (𝟙 _) (n + 1) (n + 2) rfl
    have hf : (infRes A S (n + 1)).f =
        e₁.inv ≫ (infRes (dimensionShiftUp A) S n).f ≫ (dimensionShiftUpIso A n).hom := by
      rw [← h₁₂]
      exact (e₁.inv_hom_id_assoc _).symm
    refine ⟨?_, ShortComplex.exact_of_iso ?_ hexact⟩
    · rw [hf]
      have : Mono (dimensionShiftUpIso A n).hom := IsIso.mono_of_iso _
      -- Instance search does not see through `(infRes _ S n).X₂ = Hⁿ⁺¹(G, _)`, so the
      -- composite is assembled by hand.
      exact @mono_comp _ _ _ _ _ e₁.inv _ _ (@mono_comp _ _ _ _ _ _ hmono _ this)
    · exact ShortComplex.isoMk e₁ (dimensionShiftUpIso A n) (dimensionShiftUpResIso A S n) h₁₂ h₂₃

variable {S}

/-- **Inflation is injective** (Milne II 1.34): if `Hⁱ(S, A) = 0` for `0 < i ≤ n`, then inflation
`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A)` is a monomorphism. -/
theorem mono_infRes_f (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    Mono (infRes A S n).f :=
  (mono_infRes_f_and_exact S n A hA).1

/-- **The inflation-restriction sequence is exact** (Milne II 1.34): if `Hⁱ(S, A) = 0` for
`0 < i ≤ n`, then `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)` is exact. -/
theorem infRes_exact (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    (infRes A S n).Exact :=
  (mono_infRes_f_and_exact S n A hA).2

/-- **Inflation is an isomorphism** when `Hⁱ(S, A) = 0` for `0 < i ≤ n + 1`: then
`Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A)` is injective, and surjective because restriction lands in
`Hⁿ⁺¹(S, A) = 0`. -/
theorem isIso_infRes_f (n : ℕ)
    (hA : ∀ i ≤ n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    IsIso (infRes A S n).f :=
  have := mono_infRes_f A n fun i hi => hA i hi.le
  have := (infRes_exact A n fun i hi => hA i hi.le).epi_f ((hA n le_rfl).eq_of_tgt _ _)
  isIso_of_mono_of_epi _

end TauCeti.groupCohomology
