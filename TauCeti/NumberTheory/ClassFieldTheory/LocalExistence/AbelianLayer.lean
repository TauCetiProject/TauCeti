/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup

import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.NumberTheory.ClassFieldTheory.Formation.GaloisMaps

/-!
# Norm subgroups of abelian local layers

Let `K` be a nonarchimedean local field and `V` an open normal subgroup of its absolute Galois
group `G_K` containing the closed commutator subgroup, so that `V` cuts out a finite abelian
extension `L/K` with Galois group `G_K ⧸ V`. Local reciprocity for the local class formation then
reads as an isomorphism onto the Galois group of the layer itself,

`Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)`,

with no abelianization left in the target (`localAbelianGaloisEquiv`). In particular the norm
subgroup has index `[L : K]` (`index_localNormSubgroup`).

Comparing Artin symbols along the quotient maps `G_K ⧸ (V ⊓ W) → G_K ⧸ V` turns statements about
the norm subgroups of `V` and `W` into statements about subgroups of the finite group
`G_K ⧸ (V ⊓ W)`. This gives the lattice laws of local norm subgroups: the compositum of two finite
abelian extensions has the intersection of their norm subgroups as its norm subgroup
(`localNormSubgroup_inf_of_isAbelian`), and the intersection of two finite Galois extensions has
the product of their norm subgroups (`localNormSubgroup_sup`; by norm limitation this needs no
abelianity).

## Main definitions

* `TauCeti.ClassFieldTheory.localAbelianGaloisEquiv`: local reciprocity for an abelian layer,
  `Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)`.

## Main results

* `TauCeti.ClassFieldTheory.localAbelianGaloisEquiv_artinMap`: `localAbelianGaloisEquiv` is the
  Artin map of the local class formation.
* `TauCeti.ClassFieldTheory.index_localNormSubgroup`: `[Kˣ : N_{L/K}(Lˣ)] = [L : K]` for an
  abelian layer.
* `TauCeti.ClassFieldTheory.localNormSubgroup_inf_of_isAbelian`: the norm subgroup of a compositum
  of finite abelian extensions is the intersection of their norm subgroups.
* `TauCeti.ClassFieldTheory.localNormSubgroup_sup`: the norm subgroup of an intersection of finite
  Galois extensions is the product of their norm subgroups.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Reciprocity onto the Galois group of an abelian layer -/

section Reciprocity

variable {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- The Artin map of the local class formation on the layer `V ◁ G_K`, as a homomorphism from
`Kˣ`; for an abelian layer it is read in the Galois group itself rather than in its
abelianization. -/
def localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Kˣ →* (ofOpenNormal V).Gal :=
  (abelianizationGalEquiv hV).toMonoidHom.comp <| MonoidHom.toAdditive.symm <|
    ((localClassFormation K).artinMap (ofOpenNormal V)).comp
      (localGroundEquiv K V).toAddMonoidHom

variable {K}

/-- The abelianization class of `localAbelianArtinHom` is the Artin map of the local class
formation. -/
@[simp]
theorem of_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    Additive.ofMul (Abelianization.of (localAbelianArtinHom K hV x)) =
      (localClassFormation K).artinMap (ofOpenNormal V)
        (localGroundEquiv K V (Additive.ofMul x)) := by
  rw [← abelianizationGalEquiv_symm_apply hV]
  simp [localAbelianArtinHom]

/-- The kernel of `localAbelianArtinHom` is the local norm subgroup. -/
theorem ker_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    (localAbelianArtinHom K hV).ker = localNormSubgroup K V := by
  ext x
  rw [MonoidHom.mem_ker, ← (abelianizationGalEquiv hV).symm.map_eq_one_iff,
    abelianizationGalEquiv_symm_apply, ← ofMul_eq_zero, of_localAbelianArtinHom,
    ClassFormation.artinMap_eq_zero_iff, localGroundEquiv_mem_normSubgroup_iff]

/-- `localAbelianArtinHom` is surjective. -/
theorem surjective_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Function.Surjective (localAbelianArtinHom K hV) :=
  (abelianizationGalEquiv hV).surjective.comp <|
    ((localClassFormation K).surjective_artinMap _).comp (localGroundEquiv K V).surjective

variable (K) in
/-- **Local reciprocity for an abelian layer**, `Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)`. Its target is the
Galois group `G_K ⧸ V` of the layer itself: since the layer is abelian, `abelianizationGalEquiv`
removes the abelianization from the target of the Artin equivalence of the local class formation
(`localAbelianGaloisEquiv_artinMap`). -/
def localAbelianGaloisEquiv (hV : V.IsAbelianClassFieldLayer) :
    Kˣ ⧸ localNormSubgroup K V ≃* (ofOpenNormal V).Gal :=
  (QuotientGroup.quotientMulEquivOfEq (ker_localAbelianArtinHom hV).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_localAbelianArtinHom hV))

/-- `localAbelianGaloisEquiv` sends the class of `x` to its Artin symbol
`localAbelianArtinHom K hV x`. -/
@[simp]
theorem localAbelianGaloisEquiv_mk (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    localAbelianGaloisEquiv K hV (QuotientGroup.mk x) = localAbelianArtinHom K hV x := by
  rw [localAbelianGaloisEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **`localAbelianGaloisEquiv` is the Artin map of the local class formation**: composed with
`Abelianization.of`, which is injective because the layer is abelian, it is
`ClassFormation.artinMap`. -/
theorem localAbelianGaloisEquiv_artinMap (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    Additive.ofMul (Abelianization.of (localAbelianGaloisEquiv K hV (QuotientGroup.mk x))) =
      (localClassFormation K).artinMap (ofOpenNormal V)
        (localGroundEquiv K V (Additive.ofMul x)) := by
  rw [localAbelianGaloisEquiv_mk, of_localAbelianArtinHom]

/-- **The norm index of an abelian layer**: `[Kˣ : N_{L/K}(Lˣ)] = [L : K]`, the degree of the
layer being the order of its Galois group `G_K ⧸ V`. -/
theorem index_localNormSubgroup (hV : V.IsAbelianClassFieldLayer) :
    (localNormSubgroup K V).index = (ofOpenNormal V).degree := by
  rw [Subgroup.index_eq_card, degree_eq_natCard_gal,
    Nat.card_congr (localAbelianGaloisEquiv K hV).toEquiv]

end Reciprocity

/-! ### Norm subgroups through a common abelian refinement -/

section Refinement

variable {K} {U V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- **The norm subgroup of a quotient layer, read in a refinement.** If `U ≤ V` and `U` is
abelian, then `x ∈ Kˣ` is a norm from the field of `V` exactly when its Artin symbol in
`G_K ⧸ U` lies in the kernel of the quotient map `G_K ⧸ U → G_K ⧸ V`. -/
theorem localNormSubgroup_eq_comap_ker (hU : U.IsAbelianClassFieldLayer) (h : U ≤ V) :
    localNormSubgroup K V =
      (LayerRefinement.ofOpenNormal h).galHom.ker.comap (localAbelianArtinHom K hU) := by
  have hV : V.IsAbelianClassFieldLayer := hU.mono h
  ext x
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, ← (abelianizationGalEquiv hV).symm.map_eq_one_iff,
    abelianizationGalEquiv_symm_apply, ← ofMul_eq_zero,
    ← LayerRefinement.quotientHom_of, of_localAbelianArtinHom,
    ← groundEquiv_localGroundEquiv K h, ← ClassFormation.artinMap_quotient,
    ClassFormation.artinMap_eq_zero_iff, localGroundEquiv_mem_normSubgroup_iff]

end Refinement

/-! ### Composita and intersections -/

section Lattice

open LayerRefinement (mk_mem_ker_galHom_ofOpenNormal_iff)

variable {K} {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- **Composita.** For finite abelian extensions cut out by `V` and `W`, the norm subgroup of their
compositum, cut out by `V ⊓ W`, is the intersection of the two norm subgroups. Abelianity is
needed: by norm limitation the left side only sees the maximal abelian subextension of the
compositum, which can be larger than the compositum of the maximal abelian subextensions. -/
theorem localNormSubgroup_inf_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    localNormSubgroup K (V ⊓ W) = localNormSubgroup K V ⊓ localNormSubgroup K W := by
  have hU : (V ⊓ W).IsAbelianClassFieldLayer := hV.inf hW
  have hUV : V ⊓ W ≤ V := inf_le_left
  have hUW : V ⊓ W ≤ W := inf_le_right
  rw [localNormSubgroup_eq_comap_ker hU le_rfl, localNormSubgroup_eq_comap_ker hU hUV,
    localNormSubgroup_eq_comap_ker hU hUW, ← Subgroup.comap_inf]
  congr 1
  ext g
  induction g using QuotientGroup.induction_on with
  | H w =>
    rw [Subgroup.mem_inf, mk_mem_ker_galHom_ofOpenNormal_iff le_rfl,
      mk_mem_ker_galHom_ofOpenNormal_iff hUV, mk_mem_ker_galHom_ofOpenNormal_iff hUW]
    -- Membership in an open normal subgroup is membership in its underlying subgroup.
    exact (SetLike.ext_iff.1 (OpenNormalSubgroup.toSubgroup_inf V W) _).trans Subgroup.mem_inf

/-- **Intersections, for abelian layers.** -/
private theorem localNormSubgroup_sup_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    localNormSubgroup K (V ⊔ W) = localNormSubgroup K V ⊔ localNormSubgroup K W := by
  have hU : (V ⊓ W).IsAbelianClassFieldLayer := hV.inf hW
  have hUV : V ⊓ W ≤ V := inf_le_left
  have hUW : V ⊓ W ≤ W := inf_le_right
  have hUVW : V ⊓ W ≤ V ⊔ W := hUV.trans le_sup_left
  rw [localNormSubgroup_eq_comap_ker hU hUVW, localNormSubgroup_eq_comap_ker hU hUV,
    localNormSubgroup_eq_comap_ker hU hUW,
    Subgroup.comap_sup_eq _ _ _ (surjective_localAbelianArtinHom hU)]
  congr 1
  refine le_antisymm (fun g hg ↦ ?_) (sup_le (fun g hg ↦ ?_) fun g hg ↦ ?_)
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [mk_mem_ker_galHom_ofOpenNormal_iff hUVW] at hg
      have hg' : (w : AbsoluteGaloisGroup K) ∈ V.toSubgroup ⊔ W.toSubgroup := by
        -- Membership in an open normal subgroup is membership in its underlying subgroup.
        rw [← OpenNormalSubgroup.toSubgroup_sup]
        exact hg
      obtain ⟨v, hv, v', hv', hvv'⟩ := Subgroup.mem_sup_of_normal_right.1 hg'
      have hmk : (QuotientGroup.mk w : (ofOpenNormal (V ⊓ W)).Gal) =
          QuotientGroup.mk ⟨v, by simp⟩ * QuotientGroup.mk ⟨v', by simp⟩ := by
        rw [← QuotientGroup.mk_mul]
        exact congrArg QuotientGroup.mk (Subtype.ext hvv'.symm)
      rw [hmk]
      exact Subgroup.mul_mem_sup ((mk_mem_ker_galHom_ofOpenNormal_iff hUV _).2 hv)
        ((mk_mem_ker_galHom_ofOpenNormal_iff hUW _).2 hv')
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [mk_mem_ker_galHom_ofOpenNormal_iff hUV] at hg
      rw [mk_mem_ker_galHom_ofOpenNormal_iff hUVW]
      exact Subgroup.mem_sup_left hg
  · induction g using QuotientGroup.induction_on with
    | H w =>
      rw [mk_mem_ker_galHom_ofOpenNormal_iff hUW] at hg
      rw [mk_mem_ker_galHom_ofOpenNormal_iff hUVW]
      exact Subgroup.mem_sup_right hg

/-- **Intersections.** The norm subgroup of the intersection of the finite Galois extensions cut
out by `V` and `W`, which is cut out by `V ⊔ W`, is the product of the two norm subgroups. No
abelianity is needed: by norm limitation every norm subgroup is that of its maximal abelian
sublayer, and the maximal abelian sublayer of `V ⊔ W` is the join of those of `V` and `W`. -/
@[simp]
theorem localNormSubgroup_sup (V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    localNormSubgroup K (V ⊔ W) = localNormSubgroup K V ⊔ localNormSubgroup K W := by
  rw [← localNormSubgroup_maximalAbelianLayer, OpenNormalSubgroup.maximalAbelianLayer_sup,
    localNormSubgroup_sup_of_isAbelian V.isAbelianClassFieldLayer_maximalAbelianLayer
      W.isAbelianClassFieldLayer_maximalAbelianLayer,
    localNormSubgroup_maximalAbelianLayer, localNormSubgroup_maximalAbelianLayer]

end Lattice

end TauCeti.ClassFieldTheory
