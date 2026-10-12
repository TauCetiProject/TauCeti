/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Boundary
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupHomology
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Delta

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology

/-!
# Restriction commutes with the connecting maps of Tate cohomology

Let `H` be a subgroup of a finite group `G` and `S` a short exact sequence of
`G`-representations. Restricting `S` to `H` keeps it short exact, and in every degree Tate
restriction commutes with the connecting maps of the two long exact sequences:

`H_Tateʳ(G, X₃) ⟶ H_Tateʳ⁺¹(G, X₁)`
`    ↓               ↓`
`H_Tateʳ(H, X₃) ⟶ H_Tateʳ⁺¹(H, X₁)`

for every `r : ℤ` (`TauCeti.TateCohomology.δ_comp_res`). This is what lets a statement about
restriction be moved across degrees by dimension shifting, as in the proof that restriction is
compatible with the Tate cup product. The boundary case `r = -1` is supplied by
`TauCeti.TateCohomology.δ_comp_res_neg_one`.

In nonnegative degrees the Tate complex is the complex of inhomogeneous cochains. Restriction of
cochains, extended by zero to negative degrees, is not a map of Tate complexes: the norm map from
the negative half of the Tate complex over `G` lands in `G`-invariant cochains of degree zero, which
restriction does not annihilate. It is, however, a map to the Tate complex over `H` from the complex
of inhomogeneous cochains over `G` extended by zero to negative degrees, and that complex also maps
to the Tate complex over `G` by the identity in nonnegative degrees. Both maps are natural, so the
connecting maps commute with them. In positive degrees the second map induces an isomorphism on
cohomology, and the first one induces its composite with Tate restriction. In degree zero the second
map induces the epimorphism from the invariants onto `H_Tate⁰`, and the first one again induces its
composite with Tate restriction, which is induced by the inclusion `Mᴳ ⊆ Mᴴ`.

Below degree `-1` the comparison is made in group homology instead. The injective comparison
`TauCeti.TateCohomology.toGroupHomology` of `H_Tate^{-(n+1)}` with `Hₙ` commutes with the connecting
maps, and through it Tate restriction is the transfer of group homology
(`TauCeti.TateCohomology.res_comp_toGroupHomology`), which commutes with the connecting maps by
`TauCeti.groupHomology.δ_comp_transfer`.

## Main results

* `TauCeti.TateCohomology.res_comp_toGroupHomology`: in negative degrees, Tate restriction is the
  transfer of group homology through `toGroupHomology`.
* `TauCeti.TateCohomology.δ_comp_res`: Tate restriction commutes with the connecting maps in every
  degree.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep groupCohomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G]

section ZeroExtension

variable [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- Restriction of cochains in nonnegative degrees, from the extended complex of cochains over `G`
to the Tate complex over `H`. -/
private def cochainsExtToTateRes (H : Subgroup G) :
    cochainsExtFunctor R G ⟶ resFunctor H.subtype ⋙ tateComplexFunctor R H where
  app M := CochainComplex.ConnectData.map _ (tateComplexConnectData (Rep.res H.subtype M)) 0
    (cochainsMap H.subtype (𝟙 (Rep.res H.subtype M)))
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp])
  naturality M N f := by
    ext (n | n) : 1
    -- In nonnegative degrees both composites are, by definition of `cochainsMap`, the map sending
    -- a cochain `c` to `(h₁, …, hₙ) ↦ f (c (h₁, …, hₙ))`.
    · rfl
    · exact (isZero_zero _).eq_of_src _ _

/-- In positive degrees, the identity of cochains followed by Tate restriction is restriction of
cochains. -/
private theorem homologyMap_cochainsExtToTate_comp_posRes (M : Rep R G) (H : Subgroup G)
    (n : ℕ) :
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) ((n + 1 : ℕ) : ℤ) ≫
        posRes M H n =
      HomologicalComplex.homologyMap ((cochainsExtToTateRes H).app M) ((n + 1 : ℕ) : ℤ) := by
  have h₂ := CochainComplex.ConnectData.homologyMap_map_of_eq_succ (cochainsConnectData M)
    (tateComplexConnectData (Rep.res H.subtype M)) 0 (cochainsMap H.subtype (𝟙 _))
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp]) (n + 1) _ rfl
  refine (congrArg (· ≫ posRes M H n) (homologyMap_cochainsExtToTate M n)).trans
    (Eq.trans ?_ h₂.symm)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 ?_).trans (Category.assoc _ _ _))
  exact posRes_comp_isoGroupCohomology_hom M H n

/-- On degree-zero cycles, the extended complex of cochains over `G` maps to the invariants `Mᴴ`
in the same way through the identity of cochains followed by the inclusion `Mᴳ ⊆ Mᴴ`, and through
restriction of cochains: both send a cycle to its value, a `G`-invariant element of `M`. -/
private theorem cyclesMap_cochainsExtToTate_zero_comp_inclusion (M : Rep R G) (H : Subgroup G) :
    HomologicalComplex.cyclesMap ((cochainsExtToTate R G).app M) 0 ≫
        (H0CyclesIso M).hom ≫ ModuleCat.ofHom (Submodule.inclusion
          (Representation.invariants_le_invariants_comp_subtype (ρ := M.ρ) (H := H))) =
      HomologicalComplex.cyclesMap ((cochainsExtToTateRes H).app M) 0 ≫
        (H0CyclesIso (Rep.res H.subtype M)).hom := by
  have : Mono (ModuleCat.ofHom (Rep.res H.subtype M).ρ.invariants.subtype) :=
    (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
  refine (cancel_mono (ModuleCat.ofHom (Rep.res H.subtype M).ρ.invariants.subtype)).1 ?_
  calc _ = HomologicalComplex.cyclesMap ((cochainsExtToTate R G).app M) 0 ≫
        (H0CyclesIso M).hom ≫ ModuleCat.ofHom M.ρ.invariants.subtype := by
        -- The inclusion `Mᴳ ⊆ Mᴴ` followed by the embedding of `Mᴴ` is the embedding of `Mᴳ`.
        simp only [Category.assoc]; rfl
    _ = HomologicalComplex.iCycles ((cochainsExtFunctor R G).obj M) 0 ≫ (cochainsIso₀ M).hom :=
        by
          erw [H0CyclesIso_hom_comp_subtype, HomologicalComplex.cyclesMap_i_assoc,
            cochainsExtToTate_app_f_ofNat, Category.id_comp]
    _ = HomologicalComplex.iCycles ((cochainsExtFunctor R G).obj M) 0 ≫
        ((cochainsExtToTateRes H).app M).f 0 ≫ (cochainsIso₀ (Rep.res H.subtype M)).hom :=
        congrArg (_ ≫ ·) (cochainsMap_f_0_comp_cochainsIso₀ H.subtype (𝟙 _)).symm
    _ = _ :=
        ((reassoc_of% HomologicalComplex.cyclesMap_i ((cochainsExtToTateRes H).app M) 0)
          _).symm.trans
          ((congrArg (_ ≫ ·) (H0CyclesIso_hom_comp_subtype (Rep.res H.subtype M)).symm).trans
            (Category.assoc _ _ _).symm)

/-- In degree zero, the identity of cochains followed by Tate restriction is restriction of
cochains. -/
private theorem homologyMap_cochainsExtToTate_comp_H0Res (M : Rep R G) (H : Subgroup G) :
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) 0 ≫ H0Res M H =
      HomologicalComplex.homologyMap ((cochainsExtToTateRes H).app M) 0 := by
  refine (cancel_epi (HomologicalComplex.homologyπ _ 0)).1 ?_
  refine (HomologicalComplex.homologyπ_naturality_assoc _ _ _).trans (Eq.trans ?_
    (HomologicalComplex.homologyπ_naturality _ _).symm)
  refine (congrArg (_ ≫ · ≫ H0Res M H) (H0CyclesIso_hom_comp_H0π M).symm).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (H0π_comp_H0Res M H)))).trans ?_
  exact ((reassoc_of% cyclesMap_cochainsExtToTate_zero_comp_inclusion M H) _).trans
    (congrArg (_ ≫ ·) (H0CyclesIso_hom_comp_H0π (Rep.res H.subtype M)))

/-- In nonnegative degrees, the identity of cochains followed by Tate restriction is restriction
of cochains. -/
private theorem homologyMap_cochainsExtToTate_comp_res (M : Rep R G) (H : Subgroup G) {r : ℤ}
    (hr : 0 ≤ r) :
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) r ≫ res M H r =
      HomologicalComplex.homologyMap ((cochainsExtToTateRes H).app M) r := by
  obtain ⟨_ | n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  · rw [Nat.cast_zero, res_zero]
    exact homologyMap_cochainsExtToTate_comp_H0Res M H
  · rw [Nat.cast_succ, res_ofNat_succ]
    exact homologyMap_cochainsExtToTate_comp_posRes M H n

end ZeroExtension

variable [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- Tate restriction commutes with the connecting maps from degree minus one onward. -/
private theorem δ_comp_res_of_neg_one_le {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) {r : ℤ} (hr : -1 ≤ r) :
    _root_.TateCohomology.δ hS r ≫ res S.X₁ H (r + 1) =
      res S.X₃ H r ≫ _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) r := by
  by_cases hboundary : r = -1
  · subst r
    simpa only [Int.reduceNeg, Int.reduceAdd, res_zero, res_neg_one] using
      δ_comp_res_neg_one hS H
  have hr : 0 ≤ r := by omega
  have hE := map_cochainsExtFunctor_shortExact hS
  -- The connecting maps commute with the identity of cochains and with restriction of cochains.
  have hι := HomologicalComplex.HomologySequence.δ_naturality
    (S.mapNatTrans (cochainsExtToTate R G)) hE
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS) r _ rfl
  have hρ := HomologicalComplex.HomologySequence.δ_naturality
    (S₂ := (S.map (resFunctor H.subtype)).map (tateComplexFunctor R H))
    { τ₁ := (cochainsExtToTateRes H).app S.X₁
      τ₂ := (cochainsExtToTateRes H).app S.X₂
      τ₃ := (cochainsExtToTateRes H).app S.X₃
      comm₁₂ := ((cochainsExtToTateRes H).naturality S.f).symm
      comm₂₃ := ((cochainsExtToTateRes H).naturality S.g).symm } hE
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact ((shortExact_res H.subtype).2 hS))
    r _ rfl
  have := epi_homologyMap_cochainsExtToTate S.X₃ hr
  refine (cancel_epi (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app S.X₃) r)).1 ?_
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hι.symm).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (homologyMap_cochainsExtToTate_comp_res S.X₁ H (by omega))).trans <|
    hρ.trans <|
    (congrArg (· ≫ _) (homologyMap_cochainsExtToTate_comp_res S.X₃ H hr).symm).trans <|
    Category.assoc _ _ _

/-- **In negative degrees Tate restriction is the transfer of group homology**: through the
comparison `toGroupHomology` of `H_Tate^{-(n+1)}` with `Hₙ`, restriction to `H` is the transfer. -/
@[reassoc]
theorem res_comp_toGroupHomology (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    res M H (Int.negSucc n) ≫ toGroupHomology (Rep.res H.subtype M) n =
      toGroupHomology M n ≫ TauCeti.groupHomology.transfer M H n := by
  cases n with
  | zero =>
    -- On the class of a norm-zero `z`, both sides are the class of the relative transfer of `z`
    -- in `H₀(H, M)`. `Int.negSucc 0` is `-1`, where Tate restriction is `HNegOneRes`.
    change res M H (-1) ≫ _ = _
    rw [res_neg_one]
    refine (cancel_epi (HNegOneπ M)).1 ?_
    have h₁ := HNegOneπ_comp_HNegOneRes_assoc M H (toGroupHomology (Rep.res H.subtype M) 0)
    rw [HNegOneπ_comp_toGroupHomology] at h₁
    refine h₁.trans ?_
    rw [HNegOneπ_comp_toGroupHomology_assoc]
    ext z
    simp
  | succ n =>
    rw [res_negSucc_succ, toGroupHomology_eq_negSuccIso_hom, toGroupHomology_eq_negSuccIso_hom,
      negSuccRes_comp_negSuccIso_hom]

/-- Tate restriction commutes with the connecting maps in degrees `-(n+2) ⟶ -(n+1)`: through
the injective comparison `toGroupHomology`, this is the compatibility of the transfer with the
connecting maps of group homology. -/
private theorem δ_comp_res_negSucc {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) (n : ℕ) :
    _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) ≫ res S.X₁ H (Int.negSucc n) =
      res S.X₃ H (Int.negSucc (n + 1)) ≫
        _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (Int.negSucc (n + 1)) := by
  refine (cancel_mono (toGroupHomology (Rep.res H.subtype S.X₁) n)).1 ?_
  calc _ = toGroupHomology S.X₃ (n + 1) ≫ groupHomology.δ hS (n + 1) n rfl ≫
        TauCeti.groupHomology.transfer S.X₁ H n := by
        rw [Category.assoc, res_comp_toGroupHomology, δ_comp_toGroupHomology_assoc]
    _ = toGroupHomology S.X₃ (n + 1) ≫ TauCeti.groupHomology.transfer S.X₃ H (n + 1) ≫
        groupHomology.δ ((shortExact_res H.subtype).2 hS) (n + 1) n rfl := by
        rw [TauCeti.groupHomology.δ_comp_transfer]
    _ = _ := by
        rw [← res_comp_toGroupHomology_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) (δ_comp_toGroupHomology ((shortExact_res H.subtype).2 hS) n).symm

/-- **Tate restriction commutes with the connecting maps.** For a short exact sequence `S` of
`G`-representations and a subgroup `H`, restriction to `H` intertwines the connecting map
`H_Tateʳ(G, X₃) ⟶ H_Tateʳ⁺¹(G, X₁)` of `S` with the connecting map of its restriction to `H`, in
every degree `r`. -/
@[reassoc (attr := simp)]
theorem δ_comp_res {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (H : Subgroup G) (r : ℤ) :
    _root_.TateCohomology.δ hS r ≫ res S.X₁ H (r + 1) =
      res S.X₃ H r ≫ _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) r := by
  rcases le_or_gt (-1) r with hr | hr
  · exact δ_comp_res_of_neg_one_le hS H hr
  obtain ⟨n, rfl⟩ : ∃ n, r = Int.negSucc (n + 1) := ⟨(-r - 2).toNat, by omega⟩
  exact δ_comp_res_negSucc hS H n

end TauCeti.TateCohomology
