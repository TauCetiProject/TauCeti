/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Connecting maps of Tate cohomology in negative degrees

Let `G` be a finite group and `S` a short exact sequence of representations of `G`. In degrees at
most `-2` Tate cohomology is group homology, `\hat{H}^{-(n+1)}(G, M) ≅ Hₙ(G, M)` for `n > 0`
(`TauCeti.TateCohomology.negSuccIso`), and in degree `-1` it is the kernel of the norm modulo the
augmentation submodule, a submodule of `H₀(G, M) = M_G`. This file compares the connecting maps of
the long exact sequence of Tate cohomology of `S` below degree `-1` with those of group homology.

The comparison `TauCeti.TateCohomology.toGroupHomology : \hat{H}^{-(n+1)}(G, M) ⟶ Hₙ(G, M)` is
`negSuccIso` for `n > 0` and the inclusion of `\hat{H}^{-1}(G, M)` into `H₀(G, M)` for `n = 0`.
It is induced by the identity in negative degrees, from the Tate complex to the complex of
inhomogeneous chains reindexed by `n ↦ -(n + 1)` and extended by zero, so it is injective, natural
in `M`, and commutes with the connecting maps. These properties allow Tate restriction, which is the
transfer of group homology in negative degrees, to be compared with the connecting maps there.

## Main definitions

* `TauCeti.TateCohomology.toGroupHomology`: the comparison `\hat{H}^{-(n+1)}(G, M) ⟶ Hₙ(G, M)`.

## Main results

* `TauCeti.TateCohomology.tateCohomologyFunctor_map_comp_toGroupHomology`: the comparison is natural
  in the coefficient representation.
* `TauCeti.TateCohomology.δ_comp_toGroupHomology`: the comparison commutes with the connecting maps.
* `TauCeti.TateCohomology.toGroupHomology_eq_negSuccIso_hom`,
  `TauCeti.TateCohomology.HNegOneπ_comp_toGroupHomology`: the comparison is `negSuccIso` for
  `n > 0`, and sends the class of a norm-zero element to its class in `H₀(G, M)` for `n = 0`.
* `TauCeti.TateCohomology.δ_comp_negSuccIso_hom`: through `negSuccIso`, the Tate connecting map
  `\hat{H}^{-(n+2)}(G, X₃) ⟶ \hat{H}^{-(n+1)}(G, X₁)` is the connecting map
  `H_{n+1}(G, X₃) ⟶ Hₙ(G, X₁)` of group homology, for `n > 0`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.

## Attribution

This file is adapted from the unmerged
[TauCetiProject/TauCeti#10141](https://github.com/TauCetiProject/TauCeti/pull/10141).
-/

public noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex groupCohomology groupHomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The identity in negative degrees, from the Tate complex of `M` to the complex of inhomogeneous
chains of `M` reindexed by `n ↦ -(n+1)` and extended by zero to the nonnegative degrees. -/
private def toExtendChainsApp (M : Rep R G) :
    tateComplex M ⟶ (inhomogeneousChains M).extend (ComplexShape.embeddingUpIntLE (-1)) :=
  (ComplexShape.embeddingUpIntLE (-1)).liftExtend (tateComplexConnectData M).restrictionLEIso.hom
    -- The embedding has no lower boundary, so every morphism lifts.
    (show (ComplexShape.embeddingUpIntLE (-1)).HasLift _ from
      fun _ hj ↦ hj.false_of_isTruncLE.elim)

/-- The embedding of the chains into the Tate complex sends `n` to `-(n+1)`. -/
private theorem embeddingUpIntLE_f_eq_negSucc (n : ℕ) :
    (ComplexShape.embeddingUpIntLE (-1)).f n = Int.negSucc n := by
  simp only [ComplexShape.embeddingUpIntLE_f]
  omega

/-- In degree `-(n+1)`, the identification of the Tate complex restricted to negative degrees with
the complex of chains is the identity. -/
private theorem restrictionXIso_inv_comp_restrictionLEIso_hom_f (M : Rep R G) (n : ℕ) :
    ((tateComplex M).restrictionXIso _ (embeddingUpIntLE_f_eq_negSucc n)).inv ≫
      (tateComplexConnectData M).restrictionLEIso.hom.f n = 𝟙 _ := by
  simp only [CochainComplex.ConnectData.restrictionLEIso_hom_f, restrictionXIso, eqToIso.inv,
    eqToIso.hom]
  exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)

private theorem toExtendChainsApp_f (M : Rep R G) (n : ℕ) :
    (toExtendChainsApp M).f (Int.negSucc n) =
      ((inhomogeneousChains M).extendXIso _ (embeddingUpIntLE_f_eq_negSucc n)).inv := by
  rw [toExtendChainsApp, ComplexShape.Embedding.liftExtend_f _ _ _
    (embeddingUpIntLE_f_eq_negSucc n), ← Category.assoc,
    restrictionXIso_inv_comp_restrictionLEIso_hom_f]
  exact Category.id_comp _

variable (R G) in
/-- The identity in negative degrees, from the Tate complex to the complex of inhomogeneous chains
reindexed by `n ↦ -(n+1)` and extended by zero to the nonnegative degrees, as a natural
transformation. -/
private def toExtendChains : tateComplexFunctor R G ⟶
    chainsFunctor R G ⋙ (ComplexShape.embeddingUpIntLE (-1)).extendFunctor (ModuleCat R) where
  app M := toExtendChainsApp M
  naturality M N f := by
    ext (n | n) : 1
    · exact (isZero_extend_X _ _ _ (fun i ↦ by simp; omega)).eq_of_tgt _ _
    · -- The functors are unfolded to state the square with the underlying complexes.
      change (tateComplex.map f ≫ toExtendChainsApp N).f _ =
        (toExtendChainsApp M ≫ extendMap (chainsMap (MonoidHom.id G) f) _).f _
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toExtendChainsApp_f,
        toExtendChainsApp_f, extendMap_f _ _ (embeddingUpIntLE_f_eq_negSucc n)]
      -- In degree `-(n+1)` the Tate map of `f` is its map on `n`-chains, by definition.
      exact (Iso.inv_hom_id_assoc _ _).symm

/-- The comparison `\hat{H}^{-(n+1)}(G, M) ⟶ Hₙ(G, M)` induced on homology by the identity in
negative degrees. It is `negSuccIso` for `n > 0` (`toGroupHomology_eq_negSuccIso_hom`), and the
inclusion of `\hat{H}^{-1}(G, M)` into `H₀(G, M)` for `n = 0` (`HNegOneπ_comp_toGroupHomology`). -/
def toGroupHomology (M : Rep R G) (n : ℕ) :
    tateCohomology M (Int.negSucc n) ⟶ groupHomology M n :=
  homologyMap (toExtendChainsApp M) (Int.negSucc n) ≫
    ((inhomogeneousChains M).extendHomologyIso _ (embeddingUpIntLE_f_eq_negSucc n)).hom

/-- **The comparison with group homology commutes with the connecting maps**: through
`toGroupHomology`, the Tate connecting map `\hat{H}^{-(n+2)}(G, X₃) ⟶ \hat{H}^{-(n+1)}(G, X₁)` is
the connecting map `H_{n+1}(G, X₃) ⟶ Hₙ(G, X₁)` of group homology, for every `n : ℕ`. -/
@[reassoc]
theorem δ_comp_toGroupHomology {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
    _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) ≫ toGroupHomology S.X₁ n =
      toGroupHomology S.X₃ (n + 1) ≫ groupHomology.δ hS (n + 1) n rfl := by
  have h₁ := HomologySequence.δ_naturality (S.mapNatTrans (toExtendChains R G))
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS)
    ((map_chainsFunctor_shortExact hS).extend (ComplexShape.embeddingUpIntLE (-1)))
    (Int.negSucc (n + 1)) (Int.negSucc n) rfl
  have h₂ := (map_chainsFunctor_shortExact hS).extend_δ_comp_extendHomologyIso_hom
    (ComplexShape.embeddingUpIntLE (-1)) (i := n + 1) (j := n) rfl
    (embeddingUpIntLE_f_eq_negSucc (n + 1)) (embeddingUpIntLE_f_eq_negSucc n) rfl
  exact ((reassoc_of% h₁) _).trans (congrArg (_ ≫ ·) h₂)

/-- The identity in negative degrees induces Mathlib's comparison `homologyIsoNeg` of the Tate
complex, stated for the homology of the underlying complexes. -/
private theorem homologyMap_toExtendChainsApp_comp_extendHomologyIso_hom (M : Rep R G) (n : ℕ)
    [NeZero n] :
    homologyMap (toExtendChainsApp M) (Int.negSucc n) ≫
        ((inhomogeneousChains M).extendHomologyIso _ (embeddingUpIntLE_f_eq_negSucc n)).hom =
      ((tateComplexConnectData M).homologyIsoNeg n (Int.negSucc n) (Int.negSucc_eq n)).hom := by
  rw [← cancel_epi ((tateComplex M).homologyπ (Int.negSucc n))]
  simp only [CochainComplex.ConnectData.homologyIsoNeg, Iso.trans_hom,
    Iso.symm_hom, homologyMapIso_hom, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom,
    homologyπ_restrictionHomologyIso_inv_assoc, homologyπ_naturality]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((inhomogeneousChains M).iCycles n)]
  simp only [Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc, toExtendChainsApp_f,
    cyclesMap_i, restrictionCyclesIso_inv_iCycles_assoc]
  exact congrArg (_ ≫ ·) ((Iso.inv_hom_id _).trans
    (restrictionXIso_inv_comp_restrictionLEIso_hom_f M n).symm)

/-- For `n > 0` the comparison with group homology is `negSuccIso`. -/
@[simp]
theorem toGroupHomology_eq_negSuccIso_hom (M : Rep R G) (n : ℕ) [NeZero n] :
    toGroupHomology M n = (negSuccIso M n).hom :=
  (homologyMap_toExtendChainsApp_comp_extendHomologyIso_hom M n).trans (negSuccIso_hom M n).symm

/-- **The connecting maps of Tate cohomology below degree `-1` are those of group homology**:
through `negSuccIso`, the Tate connecting map `\hat{H}^{-(n+2)}(G, X₃) ⟶ \hat{H}^{-(n+1)}(G, X₁)`
is the connecting map `H_{n+1}(G, X₃) ⟶ Hₙ(G, X₁)` of group homology, for `n > 0`. -/
@[reassoc]
theorem δ_comp_negSuccIso_hom {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ)
    [NeZero n] :
    _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) ≫ (negSuccIso S.X₁ n).hom =
      (negSuccIso S.X₃ (n + 1)).hom ≫ groupHomology.δ hS (n + 1) n rfl := by
  rw [← toGroupHomology_eq_negSuccIso_hom, ← toGroupHomology_eq_negSuccIso_hom,
    δ_comp_toGroupHomology]

/-- In degree `-1` the comparison with group homology sends the class of a norm-zero element to its
class in `H₀(G, M)`. -/
@[reassoc (attr := simp)]
theorem HNegOneπ_comp_toGroupHomology (M : Rep R G) :
    HNegOneπ M ≫ toGroupHomology M 0 =
      ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ groupHomology.H0π M := by
  have h₀ : (ComplexShape.embeddingUpIntLE (-1)).f 0 = -1 := by simp
  -- The comparison, with its degree written `-1` rather than `Int.negSucc 0`.
  have key : (HNegOneCyclesIso M).inv ≫ (tateComplex M).homologyπ (-1) ≫
      homologyMap (toExtendChainsApp M) (-1) ≫
        ((inhomogeneousChains M).extendHomologyIso _ h₀).hom =
      ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ (cyclesIso₀ M).inv ≫ π M 0 := by
    rw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom]
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono ((inhomogeneousChains M).iCycles 0)]
    simp only [Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc,
      cyclesIso₀_inv_comp_iCycles]
    have e₁ : (toExtendChainsApp M).f (-1) ≫
        ((inhomogeneousChains M).extendXIso _ h₀).hom = 𝟙 _ :=
      (congrArg (· ≫ _) (toExtendChainsApp_f M 0)).trans (Iso.inv_hom_id _)
    rw [e₁]
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans (HNegOneCyclesIso_inv_comp_iCycles M)
  rw [HNegOneπ_eq_HNegOneCyclesIso_inv_comp_homologyπ]
  exact (Category.assoc _ _ _).trans key

/-- The comparison with group homology is natural in the coefficient representation. -/
@[reassoc]
theorem tateCohomologyFunctor_map_comp_toGroupHomology {M N : Rep R G} (f : M ⟶ N) (n : ℕ) :
    (tateCohomologyFunctor (Int.negSucc n)).map f ≫ toGroupHomology N n =
      toGroupHomology M n ≫ groupHomology.map (MonoidHom.id G) f n := by
  have hf : M.ρ.IsIntertwiningMap
      (N.ρ.comp ((MulEquiv.refl G : G ≃* G) : G →* G)) f.hom.toLinearMap :=
    ⟨fun g v ↦ Rep.hom_comm_apply f g v⟩
  cases n with
  | zero =>
      -- `Int.negSucc 0` is `-1`, the degree in which `HNegOneπ` is stated.
      change (tateCohomologyFunctor (-1)).map f ≫ toGroupHomology N 0 =
        toGroupHomology M 0 ≫ groupHomology.map (MonoidHom.id G) f 0
      have h : map hf (-1) = (tateCohomologyFunctor (-1)).map f := map_refl hf (-1)
      rw [← cancel_epi (HNegOneπ M)]
      rw [← h, HNegOneπ_comp_map_assoc, HNegOneπ_comp_toGroupHomology,
        HNegOneπ_comp_toGroupHomology_assoc, groupHomology.H0π_comp_map]
      have hmap : ModuleCat.ofHom (mapKerNorm hf) ≫
          ModuleCat.ofHom (LinearMap.ker N.ρ.norm).subtype =
          ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ f.toModuleCatHom :=
        ModuleCat.hom_ext <| LinearMap.ext <| mapKerNorm_apply_coe hf
      exact congrArg (· ≫ groupHomology.H0π N) hmap
  | succ n =>
      have h : map hf (Int.negSucc (n + 1)) =
          (tateCohomologyFunctor (Int.negSucc (n + 1))).map f :=
        map_refl hf (Int.negSucc (n + 1))
      rw [toGroupHomology_eq_negSuccIso_hom, toGroupHomology_eq_negSuccIso_hom,
        ← h, map_comp_negSuccIso_hom]
      exact congrArg ((negSuccIso M (n + 1)).hom ≫ ·) <|
        groupHomology.map_congr (by ext; rfl)
          (Representation.IsIntertwiningMap.toRes_hom_toLinearMap hf) (n + 1)

/-- The comparison with group homology is injective. -/
instance (M : Rep R G) (n : ℕ) : Mono (toGroupHomology M n) := by
  have hiso (i : ℤ) (hi : i < 0) : IsIso ((toExtendChainsApp M).f i) := by
    obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
    rw [toExtendChainsApp_f]
    exact Iso.isIso_inv _
  -- The identity in negative degrees is an isomorphism in degree `-(n+1)` and in the degree
  -- before it, so it is an isomorphism on opcycles, and homology injects into opcycles.
  let φ := (shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) (Int.negSucc n)).map
    (toExtendChainsApp M)
  have : IsIso φ.τ₂ := hiso _ (Int.negSucc_lt_zero n)
  have : IsIso φ.τ₁ := hiso _ (by simp)
  have : Mono (ShortComplex.homologyMap φ) :=
    ShortComplex.mono_homologyMap_of_mono_opcyclesMap' φ
      (ShortComplex.isIso_opcyclesMap_of_isIso_of_epi' φ inferInstance inferInstance).mono_of_iso
  exact mono_comp' this (inferInstance : Mono ((inhomogeneousChains M).extendHomologyIso _
    (embeddingUpIntLE_f_eq_negSucc n)).hom)

end TauCeti.TateCohomology
