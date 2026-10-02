/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Connect
public import TauCeti.Algebra.Homology.Embedding.HomologySequence
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Tate connecting maps in negative degrees are those of group homology

In degrees at most `-2` the Tate complex of a representation `M` of a finite group is the complex of
inhomogeneous chains, and Mathlib identifies Tate cohomology in degree `-(n + 1)` with group
homology in degree `n` (`TauCeti.TateCohomology.negSuccIso`). This file shows that the connecting
maps of the two long exact sequences of a short exact sequence of representations agree through
this identification (`TauCeti.TateCohomology.δ_comp_negSuccIso_hom`).

In degree `-1` the Tate complex is the complex of chains in degree zero, but its differential is the
norm rather than zero, so Tate cohomology `H_Tate⁻¹(G, M) = ker N / I_G M` is only a submodule of
group homology `H₀(G, M) = M / I_G M`. The inclusion is `TauCeti.TateCohomology.HNegOneι`, and the
connecting map from degree `-2` to degree `-1` followed by it is the connecting map of group
homology from degree one to degree zero (`TauCeti.TateCohomology.δ_neg_two_comp_HNegOneι`).

These comparisons transfer statements about group homology, such as the compatibility of the
connecting maps with the transfer, to the negative half of Tate cohomology. Both are deduced from
the general fact that the connecting maps of a short exact sequence of complexes commute with
restriction along an embedding of complex shapes
(`CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_restrictionHomologyIso_hom` and
`CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_homologyι`), applied to the restriction
of the Tate complex to negative degrees.

## Main definitions

* `TauCeti.TateCohomology.HNegOneι`: the inclusion `H_Tate⁻¹(G, M) ⟶ H₀(G, M)`.

## Main results

* `TauCeti.TateCohomology.δ_comp_negSuccIso_hom`: below degree `-2` the Tate connecting maps are
  those of group homology.
* `TauCeti.TateCohomology.HNegOneπ_comp_HNegOneι`: `HNegOneι` sends the class of a norm-zero
  element to its class in the coinvariants.
* `TauCeti.TateCohomology.δ_neg_two_comp_HNegOneι`: from degree `-2` to degree `-1` the Tate
  connecting map is the connecting map of group homology from degree one to degree zero.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §2.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep groupHomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

section Restriction

/-- Restricting the Tate complexes of a short complex of representations to negative degrees
gives the complexes of inhomogeneous chains. -/
private def restrictionChainsHom (S : ShortComplex (Rep R G)) :
    (S.map (tateComplexFunctor R G)).map
        ((ComplexShape.embeddingUpIntLE (-1)).restrictionFunctor (ModuleCat R)) ⟶
      S.map (chainsFunctor R G) where
  τ₁ := (tateComplexConnectData S.X₁).restrictionLEIso.hom
  τ₂ := (tateComplexConnectData S.X₂).restrictionLEIso.hom
  τ₃ := (tateComplexConnectData S.X₃).restrictionLEIso.hom
  comm₁₂ := (CochainComplex.ConnectData.restrictionMap_map_comp_restrictionLEIso_hom _ _ _ _
    ((tateComplex.map S.f).comm (-1) 0)).symm
  comm₂₃ := (CochainComplex.ConnectData.restrictionMap_map_comp_restrictionLEIso_hom _ _ _ _
    ((tateComplex.map S.g).comm (-1) 0)).symm

variable (M : Rep R G) in
/-- Mathlib's comparison of Tate cohomology in degree `-(n + 1)` with group homology in degree `n`
is the comparison of the homology of a complex with that of its restriction, followed by the
identification of the restricted Tate complex with the complex of chains. -/
private theorem negSuccIso_hom_eq (n : ℕ) [NeZero n] :
    (negSuccIso M n).hom =
      ((tateComplex M).restrictionHomologyIso (ComplexShape.embeddingUpIntLE (-1)) (n + 1) n (n - 1)
        (by simp) (by cases n <;> simp) (i' := Int.negSucc n - 1) (j' := Int.negSucc n)
        (k' := Int.negSucc n + 1) (by simp; lia) (by simp; lia)
        (by have := NeZero.ne n; cases n <;> simp <;> lia) (by simp) (by simp)).inv ≫
        HomologicalComplex.homologyMap (tateComplexConnectData M).restrictionLEIso.hom n := by
  rw [negSuccIso_hom]
  -- This is the definition of Mathlib's `CochainComplex.ConnectData.homologyIsoNeg`.
  rfl

end Restriction

section NegOne

variable (M : Rep R G)

/-- The cokernel of the Tate differential into degree `-1` is the cokernel of the differential of
chains into degree zero. -/
private def opcyclesNegOneToOpcyclesZero :
    (tateComplex M).opcycles (-1) ⟶ (inhomogeneousChains M).opcycles 0 :=
  (tateComplex M).descOpcycles ((inhomogeneousChains M).pOpcycles 0) (-2) (by simp)
    (by
      rw [CochainComplex.ConnectData.cochainComplex_d,
        CochainComplex.ConnectData.d_sub_two_sub_one]
      exact (inhomogeneousChains M).d_pOpcycles 1 0)

/-- **The inclusion of Tate cohomology in degree `-1` into group homology in degree zero.** In
degree `-1` the Tate complex consists of the chains of degree zero, with the norm as outgoing
differential, so `H_Tate⁻¹(G, M) = ker N / I_G M` is a submodule of the coinvariants
`H₀(G, M) = M / I_G M`. -/
def HNegOneι : tateCohomology M (-1) ⟶ groupHomology M 0 :=
  (tateComplex M).homologyι (-1) ≫ opcyclesNegOneToOpcyclesZero M ≫
    (inhomogeneousChains M).isoHomologyι₀.inv

/-- Through the restriction of the Tate complex to negative degrees, the comparison of opcycles
`opcyclesNegOneToOpcyclesZero` is induced by the identification with the complex of chains. -/
private theorem restrictionOpcyclesIso_hom_comp_opcyclesNegOneToOpcyclesZero :
    ((tateComplex M).restrictionOpcyclesIso (ComplexShape.embeddingUpIntLE (-1)) 1 0 (by simp)
        (i' := Int.negSucc 1) (j' := Int.negSucc 1 + 1) (by simp) (by simp) (by simp)).hom ≫
        opcyclesNegOneToOpcyclesZero M =
      HomologicalComplex.opcyclesMap (tateComplexConnectData M).restrictionLEIso.hom 0 := by
  rw [← cancel_epi (((tateComplex M).restriction (ComplexShape.embeddingUpIntLE (-1))).pOpcycles 0),
    HomologicalComplex.pOpcycles_restrictionOpcyclesIso_hom_assoc, HomologicalComplex.p_opcyclesMap]
  -- Both comparisons of the restricted complex in degree zero are identities, read at the
  -- definitionally equal degrees `-1` and `Int.negSucc 0`.
  exact congrArg (_ ≫ ·) (HomologicalComplex.p_descOpcycles ..)

private instance : IsIso (opcyclesNegOneToOpcyclesZero M) := by
  rw [← (Iso.inv_comp_eq _).2 (restrictionOpcyclesIso_hom_comp_opcyclesNegOneToOpcyclesZero M).symm]
  infer_instance

instance : Mono (HNegOneι M) := by
  -- The instance arguments of `homologyι` in `HNegOneι` come from `tateCohomology`, so the
  -- composite is assembled from factors elaborated on their own.
  have h₁ : Mono ((tateComplex M).homologyι (-1)) := inferInstance
  have h₂ : Mono (opcyclesNegOneToOpcyclesZero M ≫ (inhomogeneousChains M).isoHomologyι₀.inv) :=
    mono_comp' (IsIso.mono_of_iso _) (IsIso.mono_of_iso _)
  exact mono_comp' h₁ h₂

/-- **`HNegOneι` sends the class of a norm-zero element to its class in the coinvariants.** -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegOneπ_comp_HNegOneι :
    HNegOneπ M ≫ HNegOneι M =
      ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ _root_.groupHomology.H0π M := by
  have h : (HNegOneCyclesIso M).inv ≫ (tateComplex M).iCycles (-1) =
      ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ (chainsIso₀ M).inv :=
    (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (HNegOneCyclesIso_hom_comp_subtype M).symm).trans
        (Iso.inv_hom_id_assoc _ _)))
  -- The steps are applied as terms: in degree `-1` the Tate complex is the complex of chains in
  -- degree zero only up to definitional unfolding.
  refine Eq.trans ?_ ((((reassoc_of% h) _).trans (Category.assoc _ _ _)).trans
    (congrArg (ModuleCat.ofHom (LinearMap.ker M.ρ.norm).subtype ≫ ·)
      ((Iso.inv_comp_eq _).2 (TauCeti.groupHomology.pOpcycles_comp_isoHomologyι₀_inv M))))
  refine (congrArg (· ≫ HNegOneι M) (HNegOneπ_eq_cyclesIso_inv_comp_homologyπ M)).trans
    ((Category.assoc _ _ _).trans ?_)
  exact congrArg (_ ≫ ·) ((HomologicalComplex.homology_π_ι_assoc ..).trans
    (congrArg (_ ≫ ·) (HomologicalComplex.p_descOpcycles_assoc ..)))

end NegOne

variable {S : ShortComplex (Rep R G)} (hS : S.ShortExact)

/-- **Below degree `-2` the Tate connecting map is the connecting map of group homology**, through
Mathlib's comparison of Tate cohomology in degree `-(n + 1)` with group homology in degree `n`. -/
@[reassoc]
theorem δ_comp_negSuccIso_hom (n : ℕ) [NeZero n] :
    _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) ≫ (negSuccIso S.X₁ n).hom =
      (negSuccIso S.X₃ (n + 1)).hom ≫ groupHomology.δ hS (n + 1) n rfl := by
  have hT := _root_.TateCohomology.map_tateComplexFunctor_shortExact hS
  -- The connecting maps of the restricted Tate complexes are those of the Tate complexes, and the
  -- connecting maps of group homology.
  have hR := hT.restriction_δ_comp_restrictionHomologyIso_hom (ComplexShape.embeddingUpIntLE (-1))
    (n + 1) n rfl (i' := Int.negSucc n - 1) (j' := Int.negSucc n) (by simp; lia) (by simp; lia)
    (by simp; lia) (n + 1 + 1) (n - 1) (h' := Int.negSucc n - 1 - 1) (k' := Int.negSucc n + 1)
    (by simp) (by cases n <;> simp) (by simp; lia)
    (by have := NeZero.ne n; cases n <;> simp <;> lia) (by simp) (by simp)
  have hN := HomologicalComplex.HomologySequence.δ_naturality (restrictionChainsHom S)
    (hT.restriction (ComplexShape.embeddingUpIntLE (-1))) (map_chainsFunctor_shortExact hS)
    (n + 1) n rfl
  rw [negSuccIso_hom_eq, negSuccIso_hom_eq]
  have h := (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hR).trans (Category.assoc _ _ _))
  -- The remaining steps are applied as terms: the two sides use different but definitionally
  -- equal names for the degrees and objects involved.
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hN).trans (Category.assoc _ _ _).symm)))

/-- **From degree `-2` to degree `-1` the Tate connecting map is the connecting map of group
homology** from degree one to degree zero, followed by the inclusion `HNegOneι` of `H_Tate⁻¹` into
the coinvariants. -/
@[reassoc]
theorem δ_neg_two_comp_HNegOneι :
    _root_.TateCohomology.δ hS (-2) ≫ HNegOneι S.X₁ =
      (negSuccIso S.X₃ 1).hom ≫ groupHomology.δ hS 1 0 rfl := by
  have hT := _root_.TateCohomology.map_tateComplexFunctor_shortExact hS
  -- The connecting maps of the restricted Tate complexes are those of the Tate complexes, read in
  -- the opcycles in degree `-1`, and the connecting maps of group homology.
  have hR := hT.restriction_δ_comp_homologyι (ComplexShape.embeddingUpIntLE (-1)) 1 0 rfl
    (i' := Int.negSucc 1) (j' := Int.negSucc 1 + 1) (by simp) (by simp) rfl 2
    (h' := Int.negSucc 1 - 1) (by simp) (by simp) (by simp)
  have hN := HomologicalComplex.HomologySequence.δ_naturality (restrictionChainsHom S)
    (hT.restriction (ComplexShape.embeddingUpIntLE (-1))) (map_chainsFunctor_shortExact hS) 1 0 rfl
  have h₁ := ((Iso.inv_comp_eq _).2 hR).symm
  have h₂ := restrictionOpcyclesIso_hom_comp_opcyclesNegOneToOpcyclesZero S.X₁
  rw [negSuccIso_hom_eq]
  refine (cancel_mono (inhomogeneousChains S.X₁).isoHomologyι₀.hom).1 ?_
  have hι := HomologicalComplex.homologyι_naturality (restrictionChainsHom S).τ₁ 0
  -- The chain is assembled from terms: Tate cohomology, the restricted Tate complexes and the
  -- complexes of chains are related only by definitional unfolding, which `rw` cannot cross.
  refine (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _)))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₁).trans ?_
  refine (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂))))).trans ?_
  refine (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hι.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hN).trans
      (Category.assoc _ _ _))))).trans ?_
  exact (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm

end TauCeti.TateCohomology
