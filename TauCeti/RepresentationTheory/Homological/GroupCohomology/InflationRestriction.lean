/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.DimensionShift
import TauCeti.GroupTheory.Index.Exact
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
module is shown to be cohomologically trivial by induction along a normal series. Counting along
the exact sequence instead bounds the order of `Hⁿ⁺¹(G, A)` by those of its outer terms
(`natCard_groupCohomology_succ_dvd_mul`), the form used to bound the order of a cohomology group of
a solvable group by induction on the order of the group.

The same sequence is exact for any extension `1 → H → G → Q → 1` and representations `B` of `Q`
and `C` of `H` identified with `A^H` and with `A` restricted to `H`
(`range_map_succ_eq_ker_map_succ`). This is the form in which it applies to a tower of Galois
extensions `K ⊆ L ⊆ M`, where `Gal(M/L) → Gal(M/K) → Gal(L/K)` and the units of `M` fixed by
`Gal(M/L)` are the units of `L`.

## Main definitions

* `TauCeti.groupCohomology.infRes`: the complex `Hⁿ⁺¹(G ⧸ S, A^S) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(S, A)`.

## Main statements

* `TauCeti.groupCohomology.mono_infRes_f`: inflation is injective.
* `TauCeti.groupCohomology.infRes_exact`: the inflation-restriction sequence is exact.
* `TauCeti.groupCohomology.isIso_infRes_f`: inflation is an isomorphism when `Hⁱ(S, A) = 0` for
  `0 < i ≤ n + 1`.
* `TauCeti.groupCohomology.natCard_groupCohomology_succ_dvd_mul`: the order of `Hⁿ⁺¹(G, A)` divides
  the product of the orders of `Hⁿ⁺¹(G ⧸ S, A^S)` and `Hⁿ⁺¹(S, A)`.
* `TauCeti.groupCohomology.map_succ_injective`,
  `TauCeti.groupCohomology.range_map_succ_eq_ker_map_succ`: injectivity and exactness for an
  extension `1 → H → G → Q → 1`.

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

/-- **Counting along the inflation-restriction sequence.** If `Hⁱ(S, A) = 0` for `0 < i ≤ n`, the
order of `Hⁿ⁺¹(G, A)` divides the product of the orders of `Hⁿ⁺¹(G ⧸ S, A^S)` and `Hⁿ⁺¹(S, A)`.
No finiteness is assumed; in particular `Hⁿ⁺¹(G, A)` is finite when the two outer groups are. -/
theorem natCard_groupCohomology_succ_dvd_mul (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res S.subtype A) (i + 1))) :
    Nat.card (groupCohomology A (n + 1)) ∣
      Nat.card (groupCohomology (A.quotientToInvariants S) (n + 1)) *
        Nat.card (groupCohomology (res S.subtype A) (n + 1)) := by
  -- the middle term of an exact sequence of modules, counted through its underlying groups
  have key (T : ShortComplex (ModuleCat k)) (hT : T.Exact) :
      Nat.card T.X₂ ∣ Nat.card T.X₁ * Nat.card T.X₃ :=
    AddMonoidHom.card_dvd_card_mul_card_of_exact T.f.hom.toAddMonoidHom T.g.hom.toAddMonoidHom <| by
      rw [← LinearMap.range_toAddSubgroup, ← LinearMap.ker_toAddSubgroup, hT.moduleCat_range_eq_ker]
  exact key _ (infRes_exact A n hA)

section Extension

variable {A} {Q H : Type u} [Group Q] [Group H] {π : G →* Q} (hπ : Function.Surjective π)
  {B : Rep k Q} {φ : res π B ⟶ A} (hφ : Function.Injective φ.hom)
  (hφA : LinearMap.range φ.hom.toLinearMap = Representation.invariants (A.ρ.comp π.ker.subtype))
  {ι : H →* G} (hι : Function.Injective ι) (hιπ : ι.range = π.ker)
  {C : Rep k H} {ψ : res ι A ⟶ C} (hψ : Function.Bijective ψ.hom)

include hπ hφ hφA in
/-- The cohomology of `B` is that of the `ker π`-invariants of `A` over `G ⧸ ker π`. -/
private def quotientIso (m : ℕ) :
    groupCohomology B m ≅ groupCohomology (A.quotientToInvariants π.ker) m :=
  mapIso (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm
    ((LinearEquiv.ofInjective φ.hom.toLinearMap hφ).trans (LinearEquiv.ofEq _ _ hφA)) (fun q => by
      obtain ⟨g, rfl⟩ := hπ q
      ext b
      have hg : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) = g :=
        (MulEquiv.symm_apply_eq _).2 rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hg]
      exact hom_comm_apply φ g b) m

/-- Inflation along `π` is inflation along `G → G ⧸ ker π` after `quotientIso`. -/
private theorem map_eq_quotientIso_hom_comp (n : ℕ) :
    (map π φ (n + 1)).hom =
      (map (QuotientGroup.mk' π.ker) (ofHom <| A.ρ.quotientToInvariants_lift π.ker) (n + 1)).hom ∘ₗ
        (quotientIso hπ hφ hφA (n + 1)).hom.hom := by
  rw [← ModuleCat.hom_comp, quotientIso, mapIso_hom]
  refine congrArg ModuleCat.Hom.hom ?_
  refine Eq.symm <| (map_comp _ _ _ _ _).symm.trans (map_congr ?_ ?_ (n + 1))
  -- `G ⧸ ker π ≃* Q` is induced by `π`, and the coefficient map is `φ` followed by the inclusion
  -- of the invariants, both by definition.
  · ext g
    rfl
  · ext b
    rfl

include hι hιπ hψ in
/-- The cohomology of `A` restricted to `ker π` is that of `C` over `H`. -/
private def kerIso (m : ℕ) :
    groupCohomology (res π.ker.subtype A) m ≅ groupCohomology C m :=
  mapIso ((MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hιπ)).symm
    (LinearEquiv.ofBijective ψ.hom.toLinearMap hψ) (fun s => by
      obtain ⟨h, rfl⟩ :=
        ((MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hιπ)).surjective s
      ext a
      rw [LinearMap.comp_apply, LinearMap.comp_apply, MulEquiv.symm_apply_apply]
      exact hom_comm_apply ψ h a) m

/-- Restriction along `ι` is restriction to `ker π` followed by `kerIso`. -/
private theorem map_eq_kerIso_hom_comp (n : ℕ) :
    (map ι ψ (n + 1)).hom =
      (kerIso hι hιπ hψ (n + 1)).hom.hom ∘ₗ
        (map π.ker.subtype (𝟙 (res π.ker.subtype A)) (n + 1)).hom := by
  rw [← ModuleCat.hom_comp, kerIso, mapIso_hom]
  refine congrArg ModuleCat.Hom.hom ?_
  refine Eq.symm <| (map_comp _ _ _ _ _).symm.trans (map_congr ?_ ?_ (n + 1))
  -- `H ≃* ker π` is `ι` with its codomain restricted, and the coefficient map is `ψ`, both by
  -- definition.
  · ext h
    rfl
  · ext a
    rfl

include hπ hφ hφA in
/-- **Inflation along a quotient map is injective.** Let `π : G →* Q` be surjective and let
`φ : B ⟶ A` identify the `Q`-representation `B` with the invariants of `A` under `ker π`. If
`Hⁱ(ker π, A) = 0` for `0 < i ≤ n`, then inflation `Hⁿ⁺¹(Q, B) ⟶ Hⁿ⁺¹(G, A)` is injective. -/
theorem map_succ_injective (n : ℕ)
    (hA : ∀ i < n, IsZero (groupCohomology (res π.ker.subtype A) (i + 1))) :
    Function.Injective (map π φ (n + 1)).hom := by
  rw [map_eq_quotientIso_hom_comp hπ hφ hφA n, LinearMap.coe_comp]
  -- `(infRes A π.ker n).f` is inflation along `G → G ⧸ ker π` by definition (`infRes_f`).
  exact ((ModuleCat.mono_iff_injective _).1 (mono_infRes_f A n hA)).comp
    (quotientIso hπ hφ hφA (n + 1)).toLinearEquiv.injective

include hπ hφ hφA hι hιπ hψ in
/-- **The inflation-restriction sequence of a group extension.** Let `1 → H → G → Q → 1` be exact,
given by `ι` and `π`, let `φ : B ⟶ A` identify the `Q`-representation `B` with the invariants of
`A` under `ker π`, and let `ψ : A ⟶ C` identify `A`, restricted to `H`, with `C`. If
`Hⁱ(H, C) = 0` for `0 < i ≤ n`, then inflation and restriction
`Hⁿ⁺¹(Q, B) ⟶ Hⁿ⁺¹(G, A) ⟶ Hⁿ⁺¹(H, C)` form an exact sequence. -/
theorem range_map_succ_eq_ker_map_succ (n : ℕ)
    (hC : ∀ i < n, IsZero (groupCohomology C (i + 1))) :
    LinearMap.range (map π φ (n + 1)).hom = LinearMap.ker (map ι ψ (n + 1)).hom := by
  have h := (infRes_exact A n fun i hi =>
    (hC i hi).of_iso (kerIso hι hιπ hψ (i + 1))).moduleCat_range_eq_ker
  rw [map_eq_quotientIso_hom_comp hπ hφ hφA n, map_eq_kerIso_hom_comp hι hιπ hψ n,
    LinearMap.range_comp_of_range_eq_top (f := (quotientIso hπ hφ hφA (n + 1)).hom.hom) _
      (LinearMap.range_eq_top.2 (quotientIso hπ hφ hφA (n + 1)).toLinearEquiv.surjective),
    LinearMap.ker_comp_of_ker_eq_bot _ (g := (kerIso hι hιπ hψ (n + 1)).hom.hom)
      (LinearMap.ker_eq_bot.2 (kerIso hι hιπ hψ (n + 1)).toLinearEquiv.injective)]
  -- The two maps of `infRes A π.ker n` are these by definition (`infRes_f`, `infRes_g`); `simp`
  -- cannot rewrite them, as the terms of the short complex are not syntactically the cohomology
  -- groups.
  exact h

end Extension

end TauCeti.groupCohomology
