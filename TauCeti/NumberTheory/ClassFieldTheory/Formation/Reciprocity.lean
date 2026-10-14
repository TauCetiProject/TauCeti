/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Reciprocity for abelian layers and the lattice of norm subgroups

Let `cf` be a class formation on a formation `F` over a profinite group `G`, with ground level
`A^G`. An open normal subgroup `V` of `G` cuts out the layer `V ◁ G`, whose norm subgroup
`F.normSubgroup V ⊆ A^G` is read in the common ground level. When the layer is abelian, that is
when `G ⧸ V` is commutative, the Artin map of the layer needs no abelianization: it is a
surjection `A^G → G ⧸ V` onto the Galois group of the layer itself
(`ClassFormation.abelianArtinMap`), with kernel the norm subgroup
(`ClassFormation.ker_abelianArtinMap`). In particular the norm subgroup has index the degree
`[G : V]` (`ClassFormation.index_normSubgroup`).

For abelian `U ≤ V` the Artin symbol in `G ⧸ V` is the image of the one in `G ⧸ U`
(`ClassFormation.galHom_abelianArtinMap`). So, inside one finite abelian quotient `G ⧸ U`, the
norm subgroups of all layers between `U` and `G` are the preimages of the corresponding subgroups
of `G ⧸ U` (`ClassFormation.toAddSubgroup_normSubgroup_eq_comap`). This turns the lattice of norm
subgroups into the lattice of subgroups of a finite abelian group:

* the compositum of two abelian layers has the intersection of their norm subgroups as its norm
  subgroup (`ClassFormation.normSubgroup_inf_of_isAbelian`);
* the intersection of any two layers has the sum of their norm subgroups as its norm subgroup
  (`ClassFormation.normSubgroup_sup`; by norm limitation no abelianity is needed);
* a layer lies below an abelian layer exactly when its norm subgroup lies in that of the abelian
  layer (`ClassFormation.normSubgroup_le_iff_of_isAbelian`), so an abelian layer is determined by
  its norm subgroup (`ClassFormation.eq_of_normSubgroup_eq_of_isAbelian`);
* **upward closure**: a subgroup of `A^G` containing the norm subgroup of a layer is the norm
  subgroup of an abelian layer (`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_le`), and
  so is one containing the norm group of any open subgroup, normal or not
  (`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le`);
* **descent along a finite extension**: a subgroup of `A^G` whose preimage under the norm from an
  open subgroup `U` contains the norm subgroup of a layer over `U` is the norm subgroup of an
  abelian layer of `G`
  (`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_normSubgroup_le_comap`).

None of these is an existence theorem: the class-formation axioms do not say which subgroups of
`A^G` contain a norm subgroup. The local and global class-field correspondences combine these
statements with the arithmetic existence theorems of their own settings.

## Main definitions

* `TauCeti.ClassFieldTheory.ClassFormation.abelianArtinMap`: the Artin map `A^G → G ⧸ V` of an
  abelian layer, written additively.

## Main results

* `TauCeti.ClassFieldTheory.ClassFormation.ker_abelianArtinMap` and
  `TauCeti.ClassFieldTheory.ClassFormation.surjective_abelianArtinMap`: reciprocity for an
  abelian layer, `A^G / N(V) ≃ G ⧸ V`.
* `TauCeti.ClassFieldTheory.ClassFormation.index_normSubgroup`: `[A^G : N(V)] = [G : V]` for an
  abelian layer.
* `TauCeti.ClassFieldTheory.ClassFormation.normSubgroup_inf_of_isAbelian` and
  `TauCeti.ClassFieldTheory.ClassFormation.normSubgroup_sup`: the lattice laws.
* `TauCeti.ClassFieldTheory.ClassFormation.normSubgroup_le_iff_of_isAbelian`: layers are ordered
  against an abelian layer by their norm subgroups.
* `TauCeti.ClassFieldTheory.ClassFormation.exists_abelianLayer_normSubgroup_eq_of_le`: upward
  closure of norm subgroups.
* `ClassFormation.exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le`: upward closure
  from the norm group of an open subgroup.
* `ClassFormation.exists_abelianLayer_normSubgroup_eq_of_normSubgroup_le_comap`: descent of norm
  subgroups along a finite extension.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J. S. Milne, *Class Field Theory*, Chapter VII, Lemmas 9.1 and 9.4.
* J.-P. Serre, *Local Fields*, Chapter XIV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory.ClassFormation

open NormalLayer
open LayerRefinement (galHom_ofOpenNormal_mk_eq_one_iff)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F : Formation G} (cf : ClassFormation F)

/-! ### Reciprocity onto the Galois group of an abelian layer -/

section Reciprocity

variable {V : OpenNormalSubgroup G}

/-- The **Artin map of an abelian layer** `V ◁ G`, read on the ground level `A^G` and with values
in the Galois group `G ⧸ V` of the layer itself, written additively. Since the layer is abelian,
`abelianizationGalEquiv` removes the abelianization from the target of `ClassFormation.artinMap`
(`ofMul_of_abelianArtinMap`). -/
def abelianArtinMap (hV : V.IsAbelianClassFieldLayer) :
    F.level ⊤ →+ Additive (ofOpenNormal V).Gal :=
  (MulEquiv.toAdditive (abelianizationGalEquiv hV)).toAddMonoidHom.comp <|
    (cf.artinMap (ofOpenNormal V)).comp (groundEquivOfOpenNormal F V).toLinearMap.toAddMonoidHom

/-- The abelianization class of the Artin symbol `abelianArtinMap` is the Artin map of the
layer. -/
@[simp]
theorem ofMul_of_abelianArtinMap (hV : V.IsAbelianClassFieldLayer) (a : F.level ⊤) :
    Additive.ofMul (Abelianization.of (cf.abelianArtinMap hV a).toMul) =
      cf.artinMap (ofOpenNormal V) (groundEquivOfOpenNormal F V a) := by
  rw [← abelianizationGalEquiv_symm_apply hV]
  simp [abelianArtinMap]

/-- The Artin symbol of an abelian layer vanishes exactly on the norm subgroup. -/
theorem abelianArtinMap_eq_zero_iff (hV : V.IsAbelianClassFieldLayer) {a : F.level ⊤} :
    cf.abelianArtinMap hV a = 0 ↔ a ∈ F.normSubgroup V := by
  rw [Formation.mem_normSubgroup, ← cf.artinMap_eq_zero_iff]
  exact (MulEquiv.toAdditive (abelianizationGalEquiv hV)).map_eq_zero_iff

/-- **The kernel of the Artin map of an abelian layer is its norm subgroup.** -/
theorem ker_abelianArtinMap (hV : V.IsAbelianClassFieldLayer) :
    (cf.abelianArtinMap hV).ker = (F.normSubgroup V).toAddSubgroup := by
  ext a
  exact cf.abelianArtinMap_eq_zero_iff hV

/-- **The Artin map of an abelian layer is surjective.** -/
theorem surjective_abelianArtinMap (hV : V.IsAbelianClassFieldLayer) :
    Function.Surjective (cf.abelianArtinMap hV) :=
  (MulEquiv.toAdditive (abelianizationGalEquiv hV)).surjective.comp <|
    (cf.surjective_artinMap _).comp (groundEquivOfOpenNormal F V).surjective

include cf in
/-- **The norm index of an abelian layer** is its degree: `[A^G : N(V)] = [G : V]`. -/
theorem index_normSubgroup (hV : V.IsAbelianClassFieldLayer) :
    (F.normSubgroup V).toAddSubgroup.index = (ofOpenNormal V).degree := by
  rw [← cf.ker_abelianArtinMap hV, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (cf.surjective_abelianArtinMap hV), AddSubgroup.card_top,
    degree_eq_natCard_gal]
  exact Nat.card_congr Additive.toMul

end Reciprocity

/-! ### Norm subgroups through a common abelian refinement -/

section Refinement

variable {U V : OpenNormalSubgroup G}

/-- **The Artin symbol of a quotient layer.** For abelian `U ≤ V`, the Artin symbol of `a ∈ A^G`
in `G ⧸ V` is the image of its Artin symbol in `G ⧸ U` under the quotient map. -/
@[simp]
theorem galHom_abelianArtinMap (hU : U.IsAbelianClassFieldLayer) (h : U ≤ V) (a : F.level ⊤) :
    (LayerRefinement.ofOpenNormal h).galHom (cf.abelianArtinMap hU a).toMul =
      (cf.abelianArtinMap (hU.mono h) a).toMul := by
  apply (abelianizationGalEquiv (hU.mono h)).symm.injective
  apply Additive.ofMul.injective
  rw [abelianizationGalEquiv_symm_apply, abelianizationGalEquiv_symm_apply,
    ← LayerRefinement.quotientHom_of, ofMul_of_abelianArtinMap, ofMul_of_abelianArtinMap,
    cf.artinMap_quotient (LayerRefinement.ofOpenNormal h),
    LayerRefinement.groundEquiv_groundEquivOfOpenNormal F h]

/-- **The norm subgroup of a quotient layer, read in a refinement.** For abelian `U ≤ V`, an
element of `A^G` is a norm from the layer of `V` exactly when its Artin symbol in `G ⧸ U` lies in
the kernel of the quotient map `G ⧸ U → G ⧸ V`. -/
theorem toAddSubgroup_normSubgroup_eq_comap (hU : U.IsAbelianClassFieldLayer) (h : U ≤ V) :
    (F.normSubgroup V).toAddSubgroup =
      (Subgroup.toAddSubgroup (LayerRefinement.ofOpenNormal h).galHom.ker).comap
        (cf.abelianArtinMap hU) := by
  ext a
  rw [AddSubgroup.mem_comap, Additive.mem_toAddSubgroup, MonoidHom.mem_ker,
    cf.galHom_abelianArtinMap hU h, toMul_eq_one, cf.abelianArtinMap_eq_zero_iff,
    Submodule.mem_toAddSubgroup]

end Refinement

/-! ### Composita and intersections -/

section Lattice

variable {V W : OpenNormalSubgroup G}

include cf in
/-- **Composita.** For abelian layers `V` and `W`, the norm subgroup of their compositum, cut out
by `V ⊓ W`, is the intersection of the two norm subgroups. Abelianity is needed: by norm
limitation the left side only sees the maximal abelian sublayer of `V ⊓ W`, which can be larger
than the compositum of the maximal abelian sublayers of `V` and `W`. -/
theorem normSubgroup_inf_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    F.normSubgroup (V ⊓ W) = F.normSubgroup V ⊓ F.normSubgroup W := by
  have hU : (V ⊓ W).IsAbelianClassFieldLayer := hV.inf hW
  have hUV : V ⊓ W ≤ V := inf_le_left
  have hUW : V ⊓ W ≤ W := inf_le_right
  ext a
  rw [Submodule.mem_inf, ← Submodule.mem_toAddSubgroup, ← Submodule.mem_toAddSubgroup,
    ← Submodule.mem_toAddSubgroup, cf.toAddSubgroup_normSubgroup_eq_comap hU le_rfl,
    cf.toAddSubgroup_normSubgroup_eq_comap hU hUV, cf.toAddSubgroup_normSubgroup_eq_comap hU hUW]
  simp only [AddSubgroup.mem_comap, Additive.mem_toAddSubgroup, MonoidHom.mem_ker]
  generalize (cf.abelianArtinMap hU a).toMul = g
  induction g using QuotientGroup.induction_on with
  | H w =>
    rw [galHom_ofOpenNormal_mk_eq_one_iff le_rfl, galHom_ofOpenNormal_mk_eq_one_iff hUV,
      galHom_ofOpenNormal_mk_eq_one_iff hUW]
    -- Membership in an open normal subgroup is membership in its underlying subgroup.
    exact (SetLike.ext_iff.1 (OpenNormalSubgroup.toSubgroup_inf V W) _).trans Subgroup.mem_inf

include cf in
/-- **Intersections, for abelian layers.** -/
private theorem normSubgroup_sup_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    F.normSubgroup (V ⊔ W) = F.normSubgroup V ⊔ F.normSubgroup W := by
  have hU : (V ⊓ W).IsAbelianClassFieldLayer := hV.inf hW
  have hUV : V ⊓ W ≤ V := inf_le_left
  have hUW : V ⊓ W ≤ W := inf_le_right
  have hUVW : V ⊓ W ≤ V ⊔ W := hUV.trans le_sup_left
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.sup_toAddSubgroup, cf.toAddSubgroup_normSubgroup_eq_comap hU hUVW,
    cf.toAddSubgroup_normSubgroup_eq_comap hU hUV, cf.toAddSubgroup_normSubgroup_eq_comap hU hUW,
    AddSubgroup.comap_sup_eq _ _ _ (cf.surjective_abelianArtinMap hU), ← map_sup]
  congr 2
  refine le_antisymm (fun g hg ↦ ?_) (sup_le (fun g hg ↦ ?_) fun g hg ↦ ?_)
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [MonoidHom.mem_ker, galHom_ofOpenNormal_mk_eq_one_iff hUVW] at hg
      have hg' : (w : G) ∈ V.toSubgroup ⊔ W.toSubgroup := by
        -- Membership in an open normal subgroup is membership in its underlying subgroup.
        rw [← OpenNormalSubgroup.toSubgroup_sup]
        exact hg
      obtain ⟨v, hv, v', hv', hvv'⟩ := Subgroup.mem_sup_of_normal_right.1 hg'
      have hmk : (QuotientGroup.mk w : (ofOpenNormal (V ⊓ W)).Gal) =
          QuotientGroup.mk ⟨v, by simp⟩ * QuotientGroup.mk ⟨v', by simp⟩ := by
        rw [← QuotientGroup.mk_mul]
        exact congrArg QuotientGroup.mk (Subtype.ext hvv'.symm)
      rw [hmk]
      exact Subgroup.mul_mem_sup ((galHom_ofOpenNormal_mk_eq_one_iff hUV _).2 hv)
        ((galHom_ofOpenNormal_mk_eq_one_iff hUW _).2 hv')
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [MonoidHom.mem_ker, galHom_ofOpenNormal_mk_eq_one_iff hUV] at hg
      rw [MonoidHom.mem_ker, galHom_ofOpenNormal_mk_eq_one_iff hUVW]
      exact Subgroup.mem_sup_left hg
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [MonoidHom.mem_ker, galHom_ofOpenNormal_mk_eq_one_iff hUW] at hg
      rw [MonoidHom.mem_ker, galHom_ofOpenNormal_mk_eq_one_iff hUVW]
      exact Subgroup.mem_sup_right hg

include cf in
/-- **Intersections.** The norm subgroup of the intersection of the layers of `V` and `W`, which
is cut out by `V ⊔ W`, is the sum of the two norm subgroups. No abelianity is needed: by norm
limitation every norm subgroup is that of its maximal abelian sublayer, and the maximal abelian
sublayer of `V ⊔ W` is the join of those of `V` and `W`. -/
theorem normSubgroup_sup (V W : OpenNormalSubgroup G) :
    F.normSubgroup (V ⊔ W) = F.normSubgroup V ⊔ F.normSubgroup W := by
  rw [← cf.normSubgroup_maximalAbelianLayer, OpenNormalSubgroup.maximalAbelianLayer_sup,
    cf.normSubgroup_sup_of_isAbelian V.isAbelianClassFieldLayer_maximalAbelianLayer
      W.isAbelianClassFieldLayer_maximalAbelianLayer,
    cf.normSubgroup_maximalAbelianLayer, cf.normSubgroup_maximalAbelianLayer]

/-! ### Abelian layers are determined by their norm subgroups -/

include cf in
/-- For abelian layers `V` and `W`, an inclusion of norm subgroups forces `V ≤ W`: the norm
subgroup of the compositum `V ⊓ W` is then that of `V`, so the two layers have the same degree. -/
private theorem le_of_normSubgroup_le_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) (h : F.normSubgroup V ≤ F.normSubgroup W) : V ≤ W := by
  have hinf : F.normSubgroup (V ⊓ W) = F.normSubgroup V := by
    rw [cf.normSubgroup_inf_of_isAbelian hV hW, inf_eq_left.mpr h]
  have hdegree : (ofOpenNormal (V ⊓ W)).degree = (ofOpenNormal V).degree := by
    rw [← cf.index_normSubgroup (hV.inf hW), hinf, cf.index_normSubgroup hV]
  have hindex : (V ⊓ W).toSubgroup.index = V.toSubgroup.index := by
    simpa only [NormalLayer.degree_eq_relIndex, NormalLayer.top_ofOpenNormal,
      NormalLayer.ground_ofOpenNormal, OpenSubgroup.toSubgroup_top,
      Subgroup.relIndex_top_right] using hdegree
  have hle : (V ⊓ W).toSubgroup ≤ V.toSubgroup := fun _ hx ↦ (inf_le_left : V ⊓ W ≤ V) hx
  have heq : (V ⊓ W).toSubgroup = V.toSubgroup := by
    rcases hle.lt_or_eq with hlt | heq
    · exact False.elim ((Subgroup.index_strictAnti hlt).ne hindex.symm)
    · exact heq
  rw [← OpenNormalSubgroup.toSubgroup_injective heq]
  exact inf_le_right

include cf in
/-- **Abelian layers are ordered by their norm subgroups.** For an abelian layer `W` and any
layer `V`, the norm subgroup of `V` lies in that of `W` exactly when `V ≤ W`; on the extensions
they cut out, the inclusion is reversed. No abelianity of `V` is needed: by norm limitation `V`
has the norm subgroup of its maximal abelian sublayer. -/
theorem normSubgroup_le_iff_of_isAbelian (hW : W.IsAbelianClassFieldLayer) :
    F.normSubgroup V ≤ F.normSubgroup W ↔ V ≤ W := by
  refine ⟨fun h ↦ ?_, fun h ↦ F.normSubgroup_mono h⟩
  rw [← cf.normSubgroup_maximalAbelianLayer] at h
  exact V.le_maximalAbelianLayer.trans <|
    cf.le_of_normSubgroup_le_of_isAbelian V.isAbelianClassFieldLayer_maximalAbelianLayer hW h

include cf in
/-- **An abelian layer is determined by its norm subgroup.** The abelianity hypotheses are
essential: by norm limitation every layer has the norm subgroup of its maximal abelian
sublayer. -/
theorem eq_of_normSubgroup_eq_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) (h : F.normSubgroup V = F.normSubgroup W) : V = W :=
  le_antisymm ((cf.normSubgroup_le_iff_of_isAbelian hW).1 h.le)
    ((cf.normSubgroup_le_iff_of_isAbelian hV).1 h.ge)

end Lattice

/-! ### Upward closure -/

include cf in
/-- **Upward closure of norm subgroups.** In a class formation, a subgroup `N` of `A^G` containing
the norm subgroup of the layer `V ◁ G` is the norm subgroup of an abelian layer `W ≥ V`. By norm
limitation `V` may be replaced by its maximal abelian sublayer `U`, whose Artin map
`A^G → G ⧸ U` is surjective with kernel the norm subgroup; `W` is the preimage in `G` of the image
of `N`. This is not an existence theorem: it only applies to subgroups already known to contain a
norm subgroup. -/
theorem exists_abelianLayer_normSubgroup_eq_of_le {V : OpenNormalSubgroup G}
    {N : Submodule ℤ (F.level ⊤)} (h : F.normSubgroup V ≤ N) :
    ∃ W : OpenNormalSubgroup G, W.IsAbelianClassFieldLayer ∧ V ≤ W ∧ F.normSubgroup W = N := by
  -- replace `V` by its maximal abelian sublayer `U`, which has the same norm subgroup
  set U := V.maximalAbelianLayer
  have hU : U.IsAbelianClassFieldLayer := V.isAbelianClassFieldLayer_maximalAbelianLayer
  rw [← cf.normSubgroup_maximalAbelianLayer] at h
  have : IsMulCommutative (G ⧸ U.toSubgroup) :=
    (U.isAbelianClassFieldLayer_iff_isMulCommutative).1 hU
  -- the Artin map of `U`, read in `G ⧸ U`, and the image of `N` there
  let ψ : Multiplicative (F.level ⊤) →* G ⧸ U.toSubgroup :=
    (galOfOpenNormalEquiv U).toMonoidHom.comp
      (AddMonoidHom.toMultiplicativeLeft (cf.abelianArtinMap hU))
  let H : Subgroup (G ⧸ U.toSubgroup) := (AddSubgroup.toSubgroup N.toAddSubgroup).map ψ
  -- its preimage in `G` is an open normal subgroup containing `U`
  have hUW : U.toSubgroup ≤ H.comap (QuotientGroup.mk' U.toSubgroup) := fun g hg ↦ by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact H.one_mem
  let W : OpenNormalSubgroup G :=
    { toSubgroup := H.comap (QuotientGroup.mk' U.toSubgroup)
      isOpen' := Subgroup.isOpen_mono hUW U.isOpen
      isNormal' := inferInstance }
  -- the order on open normal subgroups is inclusion of the underlying subgroups
  have hle : U ≤ W := hUW
  refine ⟨W, hU.mono hle, V.le_maximalAbelianLayer.trans hle, ?_⟩
  -- the Artin symbol of `a` in `G ⧸ U` dies in `G ⧸ W` exactly when its image lies in `H`
  have hker (γ : (ofOpenNormal U).Gal) :
      (LayerRefinement.ofOpenNormal hle).galHom γ = 1 ↔ galOfOpenNormalEquiv U γ ∈ H := by
    induction γ using QuotientGroup.induction_on with
    | H w =>
      rw [galHom_ofOpenNormal_mk_eq_one_iff hle, galOfOpenNormalEquiv_mk]
      -- membership in `W` is membership of the class in `H`
      exact Iff.rfl
  ext a
  rw [← Submodule.mem_toAddSubgroup, cf.toAddSubgroup_normSubgroup_eq_comap hU hle,
    AddSubgroup.mem_comap, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, hker, Subgroup.mem_map]
  simp only [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup]
  refine ⟨fun ⟨b, hb, hba⟩ ↦ ?_, fun ha ↦ ⟨Multiplicative.ofAdd a, ha, rfl⟩⟩
  -- `a` and an element `b` of `N` have the same Artin symbol, so `a - b` is a norm from `U`
  have hab : a - b.toAdd ∈ F.normSubgroup U := by
    rw [← cf.abelianArtinMap_eq_zero_iff hU, map_sub, sub_eq_zero]
    exact Additive.toMul.injective ((galOfOpenNormalEquiv U).injective hba).symm
  simpa using N.add_mem (h hab) hb

include cf in
/-- **Upward closure from an open subgroup.** In a class formation, a subgroup `N` of `A^G`
containing the image of the norm `N_{G/W} : A^W → A^G` from an open subgroup `W`, normal or not,
is the norm subgroup of an abelian layer. In field notation: a subgroup containing the norm group
`N_{E/K}(A_E)` of a finite, not necessarily Galois, extension `E/K` is a norm subgroup. The
open normal subgroups below `W`, which cut out the Galois extensions containing `E`, have smaller
norm subgroups (`Formation.normSubgroup_le_range_levelNorm`), so upward closure applies. -/
theorem exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le {W : OpenSubgroup G}
    {N : Submodule ℤ (F.level ⊤)} (h : (F.levelNorm (le_top : W ≤ ⊤)).range ≤ N.toAddSubgroup) :
    ∃ V : OpenNormalSubgroup G, V.IsAbelianClassFieldLayer ∧ F.normSubgroup V = N := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one W.isOpen W.one_mem
  obtain ⟨V, hV, -, hVN⟩ := cf.exists_abelianLayer_normSubgroup_eq_of_le
    ((F.normSubgroup_le_range_levelNorm (W := W) hU).trans h)
  exact ⟨V, hV, hVN⟩

include cf in
/-- **Descent of norm subgroups along a finite extension.** Let `L` be a layer `W ◁ U`, cutting
out a Galois extension `M/E` above a finite extension `E/K`. In a class formation, if the preimage
of a subgroup `N ⊆ A^G` under the norm `N_{G/U} : A^U → A^G` contains the norm subgroup
`N_{U/W}(A^W)` of `L`, then `N` is the norm subgroup of an abelian layer of `G`. In field
notation: if `N_{E/K}⁻¹(N)` contains `N_{M/E}(A_M)`, then `N` contains `N_{M/K}(A_M)` by
transitivity of the norm, so it is a norm subgroup by
`exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le`. This is the step of the proof of the
existence theorem that passes from `K` to `K(ζ_p)` (Milne VII, Lemma 9.4). -/
theorem exists_abelianLayer_normSubgroup_eq_of_normSubgroup_le_comap (L : NormalLayer G)
    {N : Submodule ℤ (F.level ⊤)}
    (h : (L.normSubgroup F).toAddSubgroup ≤
      N.toAddSubgroup.comap (F.levelNorm (le_top : L.ground ≤ ⊤))) :
    ∃ V : OpenNormalSubgroup G, V.IsAbelianClassFieldLayer ∧ F.normSubgroup V = N := by
  refine cf.exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le (W := L.top) ?_
  rintro _ ⟨x, rfl⟩
  rw [F.levelNorm_trans le_top L.top_le_ground, AddMonoidHom.comp_apply]
  exact h ((L.mem_normSubgroup F).2 ⟨x, DFunLike.congr_fun (L.toAddMonoidHom_norm F) x⟩)

end TauCeti.ClassFieldTheory.ClassFormation
