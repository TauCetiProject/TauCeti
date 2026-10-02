/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Boundary

/-!
# Restriction commutes with the connecting maps from Tate degree minus one onward

Let `H` be a subgroup of a finite group `G` and `S` a short exact sequence of
`G`-representations. Restricting `S` to `H` keeps it short exact, and from degree minus one onward
Tate restriction commutes with the connecting maps of the two long exact sequences:

`H_Tateʳ(G, X₃) ⟶ H_Tateʳ⁺¹(G, X₁)`
`    ↓               ↓`
`H_Tateʳ(H, X₃) ⟶ H_Tateʳ⁺¹(H, X₁)`

for `r ≥ -1` (`TauCeti.TateCohomology.δ_comp_res`). This is what lets a statement about restriction
be moved up in degree by dimension shifting, as in the proof that restriction is compatible with
the Tate cup product. The boundary case `r = -1` is supplied by
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

## Main results

* `TauCeti.TateCohomology.δ_comp_res`: Tate restriction commutes with the connecting maps in
  degrees at least minus one.

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

/-- The complex of inhomogeneous cochains of `M`, connected to the zero chain complex by the
zero map: the complex of inhomogeneous cochains extended by zero to negative degrees. -/
private def cochainsConnectData (M : Rep R G) :
    CochainComplex.ConnectData HomologicalComplex.zero (inhomogeneousCochains M) where
  d₀ := 0
  comp_d₀ := by simp
  d₀_comp := by simp

@[simp]
private theorem cochainsConnectData_d₀ (M : Rep R G) : (cochainsConnectData M).d₀ = 0 :=
  rfl

variable (R G) in
/-- The complex of inhomogeneous cochains extended by zero to negative degrees, as a functor. -/
private def cochainsExtFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := (cochainsConnectData M).cochainComplex
  map f := CochainComplex.ConnectData.map _ _ (𝟙 _) (cochainsMap (.id G) f) (by simp)
  map_id M := by
    rw [cochainsMap_id]
    exact CochainComplex.ConnectData.map_id _
  map_comp f g := by
    rw [cochainsMap_id_comp, CochainComplex.ConnectData.map_comp_map, Category.comp_id]

private instance : (cochainsExtFunctor R G).PreservesZeroMorphisms where
  map_zero M N := by
    ext (n | n) : 1
    · rfl
    · exact (isZero_zero _).eq_of_src _ _

/-- The extended complexes of a short exact sequence form a short exact sequence. -/
private theorem map_cochainsExtFunctor_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map (cochainsExtFunctor R G)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  rintro (n | n)
  · exact map_cochainsFunctor_eval_shortExact hS n
  · have h : IsZero ((HomologicalComplex.zero : ChainComplex (ModuleCat R) ℕ).X n) :=
      isZero_zero _
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h)
      ⟨fun _ _ _ ↦ h.eq_of_tgt _ _⟩ ⟨fun _ _ _ ↦ h.eq_of_src _ _⟩

variable [Fintype G]

variable (R G) in
/-- The identity in nonnegative degrees, from the extended complex of cochains to the Tate
complex. -/
private def cochainsExtToTate : cochainsExtFunctor R G ⟶ tateComplexFunctor R G where
  app M := CochainComplex.ConnectData.map _ _ 0 (𝟙 _)
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp])
  naturality M N f := by
    ext (n | n) : 1
    -- In nonnegative degrees both composites are `cochainsMap (.id G) f`.
    · rfl
    · exact (isZero_zero _).eq_of_src _ _

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

/-- In positive degrees, the identity of cochains induces on cohomology the composite of the two
comparisons with the cohomology of the complex of inhomogeneous cochains. -/
private theorem homologyMap_cochainsExtToTate (M : Rep R G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) ((n + 1 : ℕ) : ℤ) =
      ((cochainsConnectData M).homologyIsoPos (n + 1) _ rfl).hom ≫
        ((tateComplexConnectData M).homologyIsoPos (n + 1) _ rfl).inv := by
  refine (CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp])
    (n + 1) _ rfl).trans ?_
  rw [HomologicalComplex.homologyMap_id, Category.id_comp]

/-- In positive degrees, the identity of cochains induces an isomorphism from the cohomology of
the extended complex of cochains to Tate cohomology. -/
private theorem isIso_homologyMap_cochainsExtToTate (M : Rep R G) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) ((n + 1 : ℕ) : ℤ)) := by
  rw [homologyMap_cochainsExtToTate]
  exact Iso.isIso_hom ((cochainsConnectData M).homologyIsoPos (n + 1) _ rfl ≪≫
    ((tateComplexConnectData M).homologyIsoPos (n + 1) _ rfl).symm)

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

/-- In degree zero, the identity of cochains induces an epimorphism from the cohomology of the
extended complex of cochains, the invariants, onto Tate cohomology. -/
private theorem epi_homologyMap_cochainsExtToTate_zero (M : Rep R G) :
    Epi (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) 0) := by
  let φ := (HomologicalComplex.shortComplexFunctor _ _ 0).map ((cochainsExtToTate R G).app M)
  -- In nonnegative degrees the map is the identity of the cochains of `M`, and in negative
  -- degrees its source is zero.
  have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 ((inhomogeneousCochains M).X 0)))
  have hmono : ∀ j, Mono (((cochainsExtToTate R G).app M).f j) := by
    rintro (n | n)
    · exact (inferInstance : Mono (𝟙 ((inhomogeneousCochains M).X n)))
    · exact ⟨fun _ _ _ ↦ (isZero_zero _).eq_of_tgt _ _⟩
  have : Mono φ.τ₃ := hmono _
  exact inferInstanceAs (Epi (ShortComplex.homologyMap φ))

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
        -- The identity of cochains is the identity in degree zero.
        (congrArg (_ ≫ ·) (H0CyclesIso_hom_comp_subtype M)).trans
          ((reassoc_of% HomologicalComplex.cyclesMap_i ((cochainsExtToTate R G).app M) 0) _)
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
  -- On degree-zero cycles, the projection to Tate cohomology is `H0π` on invariants.
  have hπ : ∀ {K : Type u} [Group K] [Fintype K] (N : Rep R K),
      (tateComplex N).homologyπ 0 = (H0CyclesIso N).hom ≫ H0π N :=
    fun N ↦ by rw [H0π_eq_cyclesIso_inv_comp_homologyπ]; exact (Iso.hom_inv_id_assoc _ _).symm
  refine (congrArg (_ ≫ · ≫ H0Res M H) (hπ M)).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (H0π_comp_H0Res M H)))).trans ?_
  exact ((reassoc_of% cyclesMap_cochainsExtToTate_zero_comp_inclusion M H) _).trans
    (congrArg (_ ≫ ·) (hπ (Rep.res H.subtype M)).symm)

/-- In nonnegative degrees, the identity of cochains induces an epimorphism from the cohomology of
the extended complex of cochains onto Tate cohomology. -/
private theorem epi_homologyMap_cochainsExtToTate (M : Rep R G) {r : ℤ} (hr : 0 ≤ r) :
    Epi (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) r) := by
  obtain ⟨_ | n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  · exact epi_homologyMap_cochainsExtToTate_zero M
  · have := isIso_homologyMap_cochainsExtToTate M n
    infer_instance

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

/-- **Tate restriction commutes with the connecting maps from degree minus one onward.** For a short
exact sequence `S` of `G`-representations and a subgroup `H`, restriction to `H` intertwines the
connecting map `H_Tateʳ(G, X₃) ⟶ H_Tateʳ⁺¹(G, X₁)` of `S` with the connecting map of its
restriction to `H`, for every `r ≥ -1`. -/
@[reassoc (attr := simp)]
theorem δ_comp_res {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (H : Subgroup G) {r : ℤ}
    (hr : -1 ≤ r) :
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

end TauCeti.TateCohomology
