/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.Algebra.Homology.Embedding.ExtendHomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Connecting maps and the comparison from group cohomology to Tate cohomology

The identity on nonnegative cochains gives a natural map from ordinary group cohomology to
Tate cohomology. It is the quotient of invariants by norms in degree zero and the canonical
comparison isomorphism in positive degrees, and it intertwines the connecting maps. These
properties allow ordinary cohomological functoriality to be transported across degree zero.

The intermediate cochain complex is extended by zero in negative degrees; its map to the
Tate complex is the identity in every nonnegative degree.

## Main results

* `Rep.cochainsExtToTate_app_f_ofNat`: the comparison is the identity on nonnegative cochains.
* `Rep.cochainsExtToTate_app_f_negSucc`: the comparison is zero in negative degrees.
* `Rep.fromGroupCohomology`: the comparison from ordinary cohomology to
  Tate cohomology in every nonnegative degree.
* `Rep.fromGroupCohomology_zero`: the degree-zero comparison is the
  quotient of invariants by norms.
* `Rep.fromGroupCohomology_succ`: the positive comparison is inverse to
  Mathlib's canonical Tate-to-ordinary comparison.
* `TauCeti.TateCohomology.δ_comp_fromGroupCohomology`: the comparison intertwines the
  connecting maps, including the map from degree zero to degree one.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep groupCohomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G]

/-- The complex of inhomogeneous cochains of `M`, connected to the zero chain complex by the
zero map: the complex of inhomogeneous cochains extended by zero to negative degrees. -/
def _root_.Rep.cochainsConnectData (M : Rep R G) :
    CochainComplex.ConnectData HomologicalComplex.zero (inhomogeneousCochains M) where
  d₀ := 0
  comp_d₀ := by simp
  d₀_comp := by simp

@[simp]
theorem _root_.Rep.cochainsConnectData_d₀ (M : Rep R G) : (cochainsConnectData M).d₀ = 0 :=
  (rfl)

variable (R G) in
/-- The complex of inhomogeneous cochains extended by zero to negative degrees, as a functor. -/
-- The object must remain exposed: public comparisons use the connected complex as their
-- source, and consumers construct maps with the same cochain carriers.
@[expose]
def cochainsExtFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := (cochainsConnectData M).cochainComplex
  map f := CochainComplex.ConnectData.map _ _ (𝟙 _) (cochainsMap (.id G) f) (by simp)
  map_id M := by
    simpa only [cochainsMap_id] using CochainComplex.ConnectData.map_id (cochainsConnectData M)
  map_comp f g := by
    simp only [cochainsMap_id_comp, CochainComplex.ConnectData.map_comp_map, Category.comp_id]

attribute [local implicit_reducible] cochainsExtFunctor

/-- The zero extension has the original cochain carrier in each nonnegative degree. -/
@[simp]
theorem _root_.Rep.cochainsExtFunctor_obj_X_ofNat (M : Rep R G) (n : ℕ) :
    ((cochainsExtFunctor R G).obj M).X (n : ℤ) = (inhomogeneousCochains M).X n := by
  rfl

/-- The zero extension has zero carrier in each negative degree. -/
@[simp]
theorem _root_.Rep.cochainsExtFunctor_obj_X_negSucc (M : Rep R G) (n : ℕ) :
    ((cochainsExtFunctor R G).obj M).X (Int.negSucc n) =
      (HomologicalComplex.zero : ChainComplex (ModuleCat R) ℕ).X n := by
  rfl

/-- The extended coefficient map agrees with the cochain map in nonnegative degrees. -/
@[simp]
theorem cochainsExtFunctor_map_f_ofNat {M N : Rep R G} (f : M ⟶ N) (n : ℕ) :
    ((cochainsExtFunctor R G).map f).f (n : ℤ) = (cochainsMap (.id G) f).f n := by
  rfl

/-- The extended coefficient map is zero in negative degrees. -/
@[simp]
theorem cochainsExtFunctor_map_f_negSucc {M N : Rep R G} (f : M ⟶ N) (n : ℕ) :
    ((cochainsExtFunctor R G).map f).f (Int.negSucc n) = 0 := by
  exact (isZero_zero _).eq_of_src _ _

instance : (cochainsExtFunctor R G).PreservesZeroMorphisms where
  map_zero M N := by
    ext (n | n) : 1
    · rfl
    · exact (isZero_zero _).eq_of_src _ _

/-- The extended complexes of a short exact sequence form a short exact sequence. -/
theorem map_cochainsExtFunctor_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map (cochainsExtFunctor R G)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  rintro (n | n)
  · exact map_cochainsFunctor_eval_shortExact hS n
  · have h : IsZero ((HomologicalComplex.zero : ChainComplex (ModuleCat R) ℕ).X n) :=
      isZero_zero _
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h)
      ⟨fun _ _ _ ↦ h.eq_of_tgt _ _⟩ ⟨fun _ _ _ ↦ h.eq_of_src _ _⟩

private theorem cochainsExtToExtend_hasLift (M : Rep R G) :
    (ComplexShape.embeddingUpIntGE 0).HasLift (cochainsConnectData M).restrictionGEIso.hom := by
  intro j hj i hij
  obtain rfl := (ComplexShape.boundaryGE_embeddingUpIntGE_iff 0 j).1 hj
  have hi : i = -1 := by simp at hij; omega
  subst i
  -- The only incoming boundary differential is the zero map from degree minus one.
  ext x
  rfl

/-- The extended cochains identify with Mathlib's extension along `n ↦ n`. -/
private def cochainsExtToExtendApp (M : Rep R G) :
    (cochainsConnectData M).cochainComplex ⟶
      (inhomogeneousCochains M).extend (ComplexShape.embeddingUpIntGE 0) :=
  (ComplexShape.embeddingUpIntGE 0).liftExtend (cochainsConnectData M).restrictionGEIso.hom
    (cochainsExtToExtend_hasLift M)

private theorem cochainsExtToExtendApp_f (M : Rep R G) (n : ℕ) :
    (cochainsExtToExtendApp M).f n =
      ((inhomogeneousCochains M).extendXIso (ComplexShape.embeddingUpIntGE 0)
        (i := n) (i' := n) (by simp)).inv := by
  rw [cochainsExtToExtendApp, ComplexShape.Embedding.liftExtend_f _ _ _
    (i := n) (i' := (n : ℤ)) (by simp)]
  exact Iso.inv_hom_id_assoc
    ((cochainsConnectData M).cochainComplex.restrictionXIso
      (ComplexShape.embeddingUpIntGE 0) (i := n) (i' := n) (by simp)) _

private instance (M : Rep R G) : IsIso (cochainsExtToExtendApp M) := by
  have : ∀ i, IsIso ((cochainsExtToExtendApp M).f i) := by
    rintro (n | n)
    · rw [Int.ofNat_eq_natCast, cochainsExtToExtendApp_f]
      exact Iso.isIso_inv _
    · have hSource : IsZero ((cochainsConnectData M).cochainComplex.X (Int.negSucc n)) :=
        isZero_zero _
      rw [hSource.eq_of_src ((cochainsExtToExtendApp M).f _) 0,
        isIsoZero_iff_source_target_isZero]
      exact ⟨hSource, HomologicalComplex.isZero_extend_X (inhomogeneousCochains M)
        (ComplexShape.embeddingUpIntGE 0) (Int.negSucc n) (fun i ↦ by
          simp only [ComplexShape.embeddingUpIntGE_f, zero_add, Int.negSucc_eq]; omega)⟩
  exact HomologicalComplex.Hom.isIso_of_components _

variable (R G) in
/-- The natural identification of the zero extension of cochains with Mathlib's extension. -/
private def cochainsExtToExtend : cochainsExtFunctor R G ⟶
    cochainsFunctor R G ⋙ (ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat R) where
  app M := cochainsExtToExtendApp M
  naturality M N f := by
    ext (n | n) : 1
    · -- Both maps are the coefficient map in each nonnegative degree.
      change (cochainsMap (.id G) f).f n ≫ (cochainsExtToExtendApp N).f n =
        (cochainsExtToExtendApp M).f n ≫
          (HomologicalComplex.extendMap (cochainsMap (.id G) f)
            (ComplexShape.embeddingUpIntGE 0)).f (n : ℤ)
      rw [cochainsExtToExtendApp_f, cochainsExtToExtendApp_f,
        HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) (by simp)]
      exact (Iso.inv_hom_id_assoc _ _).symm
    · exact (isZero_zero _).eq_of_src _ _

/-- The cohomology of the zero extension of cochains is ordinary group cohomology. -/
def _root_.Rep.cochainsExtIso (M : Rep R G) (n : ℕ) :
    (cochainsConnectData M).cochainComplex.homology n ≅ groupCohomology M n :=
  HomologicalComplex.homologyMapIso (asIso (cochainsExtToExtendApp M)) n ≪≫
    (inhomogeneousCochains M).extendHomologyIso (ComplexShape.embeddingUpIntGE 0)
      (j := n) (j' := n) (by simp)

private theorem cochainsExtIso_hom (M : Rep R G) (n : ℕ) :
    (cochainsExtIso M n).hom = HomologicalComplex.homologyMap (cochainsExtToExtendApp M) n ≫
      ((inhomogeneousCochains M).extendHomologyIso (ComplexShape.embeddingUpIntGE 0)
        (j := n) (j' := n) (by simp)).hom := (rfl)

/-- The identification of extended cochains with ordinary cohomology commutes with
connecting maps, including the map from degree zero to degree one. -/
@[reassoc]
theorem δ_comp_cochainsExtIso_hom {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℕ) :
    (map_cochainsExtFunctor_shortExact hS).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
        (cochainsExtIso S.X₁ (n + 1)).hom =
      (cochainsExtIso S.X₃ n).hom ≫ groupCohomology.δ hS n (n + 1) rfl := by
  have h₁ := HomologicalComplex.HomologySequence.δ_naturality
    (S.mapNatTrans (cochainsExtToExtend R G)) (map_cochainsExtFunctor_shortExact hS)
    ((map_cochainsFunctor_shortExact hS).extend (ComplexShape.embeddingUpIntGE 0))
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)
  have h₂ := (map_cochainsFunctor_shortExact hS).extend_δ_comp_extendHomologyIso_hom
    (ComplexShape.embeddingUpIntGE 0) (i := n) (j := n + 1) rfl
    (i' := n) (j' := ((n + 1 : ℕ) : ℤ)) (by simp) (by simp) (by simp)
  exact ((reassoc_of% h₁) _).trans (congrArg (_ ≫ ·) h₂)

private theorem cochainsExtIso_hom_eq_homologyIsoPos (M : Rep R G) (n : ℕ) [NeZero n] :
    (cochainsExtIso M n).hom = ((cochainsConnectData M).homologyIsoPos n n rfl).hom := by
  -- The functor's object is the explicitly connected complex; fixing that carrier makes
  -- the comparison with the restriction of the connected complex type-correct.
  dsimp only [groupCohomology]
  rw [← cancel_epi ((cochainsConnectData M).cochainComplex.homologyπ (n : ℤ))]
  simp only [cochainsExtIso_hom, CochainComplex.ConnectData.homologyIsoPos, Iso.trans_hom,
    Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom,
    HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc,
    HomologicalComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((inhomogeneousCochains M).iCycles n)]
  simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i_assoc, cochainsExtToExtendApp_f,
    HomologicalComplex.cyclesMap_i,
    HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc]
  simp only [CochainComplex.ConnectData.restrictionGEIso_hom_f]
  exact congrArg (_ ≫ ·)
    ((Iso.inv_hom_id ((inhomogeneousCochains M).extendXIso
      (ComplexShape.embeddingUpIntGE 0) (i := n) (i' := (n : ℤ)) (by simp))).trans
      (Iso.inv_hom_id ((cochainsConnectData M).cochainComplex.restrictionXIso
        (ComplexShape.embeddingUpIntGE 0) (i := n) (i' := (n : ℤ)) (by simp))).symm)

variable [Fintype G]

variable (R G) in
/-- The identity in nonnegative degrees, from the extended complex of cochains to the Tate
complex. -/
def cochainsExtToTate : cochainsExtFunctor R G ⟶ tateComplexFunctor R G where
  app M := CochainComplex.ConnectData.map _ _ 0 (𝟙 _)
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp])
  naturality M N f := by
    ext (n | n) : 1
    -- In nonnegative degrees both composites are `cochainsMap (.id G) f`.
    · rfl
    · exact (isZero_zero _).eq_of_src _ _

/-- The comparison with the Tate complex is the identity on every nonnegative cochain. -/
@[simp]
theorem _root_.Rep.cochainsExtToTate_app_f_ofNat (M : Rep R G) (n : ℕ) :
    ((cochainsExtToTate R G).app M).f (n : ℤ) = 𝟙 ((inhomogeneousCochains M).X n) := by
  rfl

/-- The comparison with the Tate complex is zero in every negative degree. -/
@[simp]
theorem _root_.Rep.cochainsExtToTate_app_f_negSucc (M : Rep R G) (n : ℕ) :
    ((cochainsExtToTate R G).app M).f (Int.negSucc n) = 0 := by
  rfl

/-- In positive degrees, the identity of cochains induces on cohomology the composite of the two
comparisons with the cohomology of the complex of inhomogeneous cochains. -/
theorem _root_.Rep.homologyMap_cochainsExtToTate (M : Rep R G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) ((n + 1 : ℕ) : ℤ) =
      ((cochainsConnectData M).homologyIsoPos (n + 1) _ rfl).hom ≫
        ((tateComplexConnectData M).homologyIsoPos (n + 1) _ rfl).inv := by
  refine (CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _
    (by rw [HomologicalComplex.zero_f, zero_comp, cochainsConnectData_d₀, zero_comp])
    (n + 1) _ rfl).trans ?_
  rw [HomologicalComplex.homologyMap_id, Category.id_comp]

/-- In positive degrees, the identity of cochains induces an isomorphism from the cohomology of
the extended complex of cochains to Tate cohomology. -/
theorem _root_.Rep.isIso_homologyMap_cochainsExtToTate (M : Rep R G) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) ((n + 1 : ℕ) : ℤ)) := by
  rw [homologyMap_cochainsExtToTate]
  exact Iso.isIso_hom ((cochainsConnectData M).homologyIsoPos (n + 1) _ rfl ≪≫
    ((tateComplexConnectData M).homologyIsoPos (n + 1) _ rfl).symm)

/-- In degree zero, the identity of cochains induces an epimorphism from the cohomology of the
extended complex of cochains, the invariants, onto Tate cohomology. -/
theorem _root_.Rep.epi_homologyMap_cochainsExtToTate_zero (M : Rep R G) :
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

/-- In nonnegative degrees, the identity of cochains induces an epimorphism from the cohomology of
the extended complex of cochains onto Tate cohomology. -/
theorem _root_.Rep.epi_homologyMap_cochainsExtToTate (M : Rep R G) {r : ℤ} (hr : 0 ≤ r) :
    Epi (HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) r) := by
  obtain ⟨_ | n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  · exact epi_homologyMap_cochainsExtToTate_zero M
  · have := isIso_homologyMap_cochainsExtToTate M n
    infer_instance


private theorem cochainsExt_homologyπ_comp_iso_zero (M : Rep R G) :
    (cochainsConnectData M).cochainComplex.homologyπ 0 ≫ (cochainsExtIso M 0).hom ≫
        (groupCohomology.H0Iso M).hom =
      HomologicalComplex.cyclesMap ((cochainsExtToTate R G).app M) 0 ≫
        (H0CyclesIso M).hom := by
  let e := (inhomogeneousCochains M).extendHomologyIso (ComplexShape.embeddingUpIntGE 0)
    (j := 0) (j' := (0 : ℤ)) (by simp)
  let c := (inhomogeneousCochains M).extendCyclesIso (ComplexShape.embeddingUpIntGE 0)
    (j := 0) (j' := (0 : ℤ)) (by simp)
  have hπ : (cochainsConnectData M).cochainComplex.homologyπ 0 ≫
      (cochainsExtIso M 0).hom =
      HomologicalComplex.cyclesMap (cochainsExtToExtendApp M) 0 ≫ c.hom ≫
        (inhomogeneousCochains M).homologyπ 0 := by
    refine (congrArg (_ ≫ ·) (cochainsExtIso_hom M 0)).trans ?_
    exact ((reassoc_of% HomologicalComplex.homologyπ_naturality
      (cochainsExtToExtendApp M) 0) e.hom).trans
      (congrArg (_ ≫ ·) (HomologicalComplex.homologyπ_extendHomologyIso_hom
        (inhomogeneousCochains M) (ComplexShape.embeddingUpIntGE 0)
        (j := 0) (j' := (0 : ℤ)) (by simp)))
  have : Mono (ModuleCat.ofHom M.ρ.invariants.subtype) :=
    (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
  refine (cancel_mono (ModuleCat.ofHom M.ρ.invariants.subtype)).1 ?_
  -- Compare the two maps by their underlying degree-zero cochain values.
  calc
    _ = HomologicalComplex.cyclesMap (cochainsExtToExtendApp M) 0 ≫ c.hom ≫
        (groupCohomology.cocyclesIso₀ M).hom ≫ ModuleCat.ofHom M.ρ.invariants.subtype := by
      have hH0 : (inhomogeneousCochains M).homologyπ 0 ≫
          (groupCohomology.H0Iso M).hom = (groupCohomology.cocyclesIso₀ M).hom :=
        groupCohomology.π_comp_H0Iso_hom M
      have h₁ := congrArg (fun f =>
        f ≫ (groupCohomology.H0Iso M).hom ≫ ModuleCat.ofHom M.ρ.invariants.subtype) hπ
      have h₂ := congrArg (fun f =>
        HomologicalComplex.cyclesMap (cochainsExtToExtendApp M) 0 ≫ c.hom ≫
          f ≫ ModuleCat.ofHom M.ρ.invariants.subtype) hH0
      simp only [Category.assoc] at h₁ h₂ ⊢
      exact h₁.trans h₂
    _ = (cochainsConnectData M).cochainComplex.iCycles 0 ≫ (cochainsIso₀ M).hom := by
      -- The connected complex has exactly the ordinary cochain carrier in degree zero.
      erw [groupCohomology.cocyclesIso₀_hom_comp_f,
        HomologicalComplex.extendCyclesIso_hom_iCycles_assoc,
        HomologicalComplex.cyclesMap_i_assoc, cochainsExtToExtendApp_f M 0]
      exact congrArg ((cochainsConnectData M).cochainComplex.iCycles 0 ≫ ·)
        (Iso.inv_hom_id_assoc
          ((inhomogeneousCochains M).extendXIso (ComplexShape.embeddingUpIntGE 0)
            (i := 0) (i' := (0 : ℤ)) (by simp)) (cochainsIso₀ M).hom)
    _ = _ := by
      -- The same carrier identity identifies the map to the Tate complex with the identity.
      erw [Category.assoc, H0CyclesIso_hom_comp_subtype,
        HomologicalComplex.cyclesMap_i_assoc]
      rfl

/-- The canonical map from ordinary group cohomology to Tate cohomology in nonnegative
degrees: quotient by norms in degree zero, and inverse to the usual comparison in positive
degrees. -/
def _root_.Rep.fromGroupCohomology (M : Rep R G) (n : ℕ) :
    groupCohomology M n ⟶ tateCohomology M n :=
  (cochainsExtIso M n).inv ≫
    HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) n

private theorem cochainsExtIso_hom_comp_fromGroupCohomology (M : Rep R G) (n : ℕ) :
    (cochainsExtIso M n).hom ≫ fromGroupCohomology M n =
      HomologicalComplex.homologyMap ((cochainsExtToTate R G).app M) n :=
  Iso.hom_inv_id_assoc _ _

/-- In positive degrees, the comparison from ordinary cohomology is inverse to Mathlib's
canonical Tate-to-ordinary comparison. -/
@[simp]
theorem _root_.Rep.fromGroupCohomology_succ (M : Rep R G) (n : ℕ) :
    fromGroupCohomology M (n + 1) =
      ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M).inv := by
  -- Both comparisons have the same cochain carrier, written using the functor and the
  -- connected complex respectively.
  erw [fromGroupCohomology, homologyMap_cochainsExtToTate,
    ← cochainsExtIso_hom_eq_homologyIsoPos, Iso.inv_hom_id_assoc]
  rfl

/-- In degree zero, the ordinary-to-Tate comparison is the quotient map on invariants. -/
@[simp]
theorem _root_.Rep.fromGroupCohomology_zero (M : Rep R G) :
    fromGroupCohomology M 0 = (groupCohomology.H0Iso M).hom ≫ H0π M := by
  have hπ : (tateComplex M).homologyπ 0 = (H0CyclesIso M).hom ≫ H0π M := by
    rw [H0π_eq_cyclesIso_inv_comp_homologyπ]
    exact (Iso.hom_inv_id_assoc _ _).symm
  refine (cancel_epi ((cochainsConnectData M).cochainComplex.homologyπ 0 ≫
    (cochainsExtIso M 0).hom)).1 ?_
  have h₁ := (Category.assoc
    ((cochainsConnectData M).cochainComplex.homologyπ 0) (cochainsExtIso M 0).hom
    (fromGroupCohomology M 0)).trans
      (congrArg ((cochainsConnectData M).cochainComplex.homologyπ 0 ≫ ·)
        (cochainsExtIso_hom_comp_fromGroupCohomology M 0))
  have h₂ := (HomologicalComplex.homologyπ_naturality ((cochainsExtToTate R G).app M) 0).trans
    (congrArg (HomologicalComplex.cyclesMap ((cochainsExtToTate R G).app M) 0 ≫ ·) hπ)
  have h₃ := congrArg (· ≫ H0π M) (cochainsExt_homologyπ_comp_iso_zero M).symm
  simp only [Category.assoc] at h₁ h₂ h₃ ⊢
  exact h₁.trans (h₂.trans h₃)

/-- The comparison from ordinary cohomology is surjective in every nonnegative degree. -/
instance (M : Rep R G) (n : ℕ) : Epi (fromGroupCohomology M n) := by
  cases n with
  | zero =>
    rw [fromGroupCohomology_zero]
    infer_instance
  | succ n =>
    rw [fromGroupCohomology_succ]
    have := Iso.isIso_inv ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M)
    exact CategoryTheory.IsIso.epi_of_iso
      ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M).inv

/-- Ordinary and Tate connecting maps agree through the canonical comparison, including
the connecting map from degree zero to degree one. -/
@[reassoc]
theorem δ_comp_fromGroupCohomology {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl ≫ fromGroupCohomology S.X₁ (n + 1) =
      fromGroupCohomology S.X₃ n ≫ _root_.TateCohomology.δ hS n := by
  rw [← cancel_epi (cochainsExtIso S.X₃ n).hom]
  have hδ := δ_comp_cochainsExtIso_hom hS n
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (S.mapNatTrans (cochainsExtToTate R G)) (map_cochainsExtFunctor_shortExact hS)
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS)
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)
  dsimp only [ShortComplex.mapNatTrans] at h
  calc
    _ = (map_cochainsExtFunctor_shortExact hS).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
        HomologicalComplex.homologyMap ((cochainsExtToTate R G).app S.X₁) (n + 1) := by
      rw [← reassoc_of% hδ, cochainsExtIso_hom_comp_fromGroupCohomology]
      -- Normalize the whole square so the cast of `n + 1` keeps its dependent endpoints.
      simp only [Int.natCast_add, Int.cast_ofNat_Int]
      rfl
    _ = _ := h.trans
      (congrArg (· ≫ _)
        (cochainsExtIso_hom_comp_fromGroupCohomology S.X₃ n).symm)

end TauCeti.TateCohomology
