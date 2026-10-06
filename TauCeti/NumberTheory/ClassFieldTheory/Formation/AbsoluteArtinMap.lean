/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# The absolute Artin map of a class formation

Let `cf` be a class formation on a formation `F` over a profinite group `G`, with ground level
`A^G`. Every open normal subgroup `V` of `G` gives a finite normal layer `V ◁ G`, with Artin map
`cf.artinMap (NormalLayer.ofOpenNormal V) : A^G → (G/V)^ab`. These maps are compatible with the
quotient maps between the Galois groups of nested layers (`ClassFormation.artinMap_quotient`), so
they pass to the inverse limit. The limit of the finite quotients `(G/V)^ab` is the topological
abelianization `G^ab = G ⧸ closure [G, G]`, which is again profinite. This gives the **absolute
Artin map**

```text
cf.absoluteArtinMap : A^G → G^ab.
```

The map is characterized by its finite restrictions. Write
`NormalLayer.abelianizationRestrict V : G^ab → (G/V)^ab` for the projection. The composite of the
absolute map with this projection is the finite Artin map of the layer `V ◁ G`
(`abelianizationRestrict_absoluteArtinMap`), and no other homomorphism has this property
(`eq_absoluteArtinMap_of_forall_abelianizationRestrict`). Every finite Artin map is surjective,
so the absolute map has dense image (`denseRange_absoluteArtinMap`). It need not be surjective:
for a local field the source is `Kˣ` and the target is the abelianized absolute Galois group.
Since the kernel of each finite Artin map is the norm subgroup of its layer, the preimage of every
open subgroup of `G^ab` is the norm subgroup of a layer (`exists_absoluteArtinMap_mem_iff`), and
the kernel of the absolute map is the intersection of all norm subgroups
(`absoluteArtinMap_eq_zero_iff`).

The construction runs over the open normal subgroups `U` of `G^ab`. Each of them is the image of
the open normal subgroup `V` of `G` it pulls back to, and `G^ab ⧸ U` is the abelianized Galois
group `(G/V)^ab` of the layer of `V`. The limit description of the profinite group `G^ab`
(`TauCeti.existsUnique_monoidHom_mk'_comp_eq`) then assembles the finite Artin maps into a single
homomorphism.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.abelianizationRestrict`: the projection
  `G^ab → (G/V)^ab` onto the abelianized Galois group of the layer of an open normal subgroup.
* `TauCeti.ClassFieldTheory.ClassFormation.absoluteArtinMap`: the absolute Artin map
  `A^G → G^ab`.

## Main results

* `TauCeti.ClassFieldTheory.ClassFormation.abelianizationRestrict_absoluteArtinMap`: the finite
  restrictions of the absolute Artin map are the finite Artin maps.
* `TauCeti.ClassFieldTheory.ClassFormation.eq_absoluteArtinMap_of_forall_abelianizationRestrict`:
  the absolute Artin map is the unique homomorphism with these restrictions.
* `TauCeti.ClassFieldTheory.NormalLayer.eq_of_forall_le_abelianizationRestrict_eq`: elements of
  `G^ab` are determined by their projections to the layers below any fixed open normal subgroup.
* `TauCeti.ClassFieldTheory.ClassFormation.denseRange_absoluteArtinMap`: the absolute Artin map
  has dense image.
* `TauCeti.ClassFieldTheory.ClassFormation.exists_absoluteArtinMap_mem_iff`: the preimage of an
  open subgroup of `G^ab` under the absolute Artin map is the norm subgroup of a layer.
* `TauCeti.ClassFieldTheory.ClassFormation.absoluteArtinMap_eq_zero_iff`: the kernel of the
  absolute Artin map is the intersection of the norm subgroups of all layers.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV.
* J. Neukirch, *Algebraic Number Theory*, Chapter IV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

-- The closed commutator subgroup is closed, so `TopologicalAbelianization G` is profinite
-- (`TauCeti.QuotientGroup.instTotallyDisconnectedSpace`).
attribute [local instance] Subgroup.isClosed_topologicalClosure

/-! ### The projections of the topological abelianization -/

namespace NormalLayer

/-- The ground level of the layer `V ◁ G` of an open normal subgroup `V` is the level `A^G` of the
whole group. -/
def groundEquivOfOpenNormal (F : Formation G) (V : OpenNormalSubgroup G) :
    F.level ⊤ ≃ₗ[ℤ] F.level (ofOpenNormal V).ground :=
  LinearEquiv.ofEq _ _ (congrArg F.level (ground_ofOpenNormal V).symm)

/-- The identification of `A^G` with the ground level of `V ◁ G` moves no element of the ambient
module. -/
@[simp]
theorem groundEquivOfOpenNormal_apply_coe (F : Formation G) (V : OpenNormalSubgroup G)
    (a : F.level ⊤) : (dsimp% only (groundEquivOfOpenNormal F V a : F.toRep.V)) = a :=
  (rfl)

/-- The projection `G^ab → (G/V)^ab` from the topological abelianization of `G` onto the
abelianized Galois group of the layer `V ◁ G` of an open normal subgroup `V`, written additively.
It sends the class of `g ∈ G` to the class of `g` (`abelianizationRestrict_mk`). In Galois
language, it restricts an automorphism of the maximal abelian extension to the maximal abelian
subextension of the finite layer cut out by `V`. -/
def abelianizationRestrict (V : OpenNormalSubgroup G) :
    Additive (TopologicalAbelianization G) →+ Additive (Abelianization (ofOpenNormal V).Gal) :=
  MonoidHom.toAdditive <|
    QuotientGroup.lift _
      (Abelianization.of.comp
        ((galOfOpenNormalEquiv V).symm.toMonoidHom.comp (QuotientGroup.mk' V.toSubgroup))) <| by
      -- The kernel contains `V`, so it is open, hence closed; it contains every commutator.
      refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _) ?_
      refine Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (fun g hg ↦ ?_) V.isOpen)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).mpr hg, map_one, map_one]

/-- The projection `G^ab → (G/V)^ab` sends the class of `g` to the class of `g`. -/
@[simp]
theorem abelianizationRestrict_mk (V : OpenNormalSubgroup G) (g : (ofOpenNormal V).ground) :
    abelianizationRestrict V (Additive.ofMul ((g : G) : TopologicalAbelianization G)) =
      Additive.ofMul (Abelianization.of (g : (ofOpenNormal V).Gal)) := by
  rw [abelianizationRestrict, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.lift_mk, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    MulEquiv.coe_toMonoidHom,
    (galOfOpenNormalEquiv V).symm_apply_eq.mpr (galOfOpenNormalEquiv_mk V g).symm]

/-- The projection `G^ab → (G/V)^ab` is surjective. -/
theorem abelianizationRestrict_surjective (V : OpenNormalSubgroup G) :
    Function.Surjective (abelianizationRestrict V) := by
  intro y
  obtain ⟨γ, hγ⟩ : ∃ γ, Abelianization.of γ = y.toMul := QuotientGroup.mk_surjective y.toMul
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  exact ⟨_, (abelianizationRestrict_mk V g).trans (congrArg Additive.ofMul hγ)⟩

end NormalLayer

/-- **The projections of `G^ab` are compatible with refinement**: for open normal subgroups
`W ≤ V` of `G`, projecting to `(G/W)^ab` and then to the quotient `(G/V)^ab` is the projection to
`(G/V)^ab`. -/
@[simp]
theorem LayerRefinement.quotientHom_abelianizationRestrict {V W : OpenNormalSubgroup G}
    (T : LayerRefinement (NormalLayer.ofOpenNormal V) (NormalLayer.ofOpenNormal W))
    (x : Additive (TopologicalAbelianization G)) :
    T.quotientHom (NormalLayer.abelianizationRestrict W x) =
      NormalLayer.abelianizationRestrict V x := by
  obtain ⟨x, rfl⟩ : ∃ y, Additive.ofMul y = x := ⟨x.toMul, ofMul_toMul x⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg (U : OpenNormalSubgroup G) : g ∈ (NormalLayer.ofOpenNormal U).ground := by simp
    rw [NormalLayer.abelianizationRestrict_mk W ⟨g, hg W⟩,
      NormalLayer.abelianizationRestrict_mk V ⟨g, hg V⟩, quotientHom_of, galHom_mk]
    exact congrArg (fun w ↦ Additive.ofMul (Abelianization.of
      (QuotientGroup.mk w : (NormalLayer.ofOpenNormal V).Gal)))
      (Subtype.ext (Subgroup.coe_inclusion _ _))

/-! ### Finite quotients of the topological abelianization -/

section Quotient

open NormalLayer

/-- The open normal subgroup of `G` cut out by an open normal subgroup `U` of `G^ab`: its preimage
under the projection `G → G^ab`. Its layer has abelianized Galois group `G^ab ⧸ U`. -/
private def comapAb (U : OpenNormalSubgroup (TopologicalAbelianization G)) :
    OpenNormalSubgroup G :=
  U.comap (QuotientGroup.mk' _) (by rw [QuotientGroup.coe_mk']; exact QuotientGroup.continuous_mk)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem mem_comapAb {U : OpenNormalSubgroup (TopologicalAbelianization G)} {g : G} :
    g ∈ (comapAb U).toSubgroup ↔ (g : TopologicalAbelianization G) ∈ U.toSubgroup := by
  rw [comapAb, OpenNormalSubgroup.toSubgroup_comap, Subgroup.mem_comap, QuotientGroup.mk'_apply]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem comapAb_le_comap (U : OpenNormalSubgroup (TopologicalAbelianization G)) :
    (comapAb U).toSubgroup ≤ U.toSubgroup.comap (QuotientGroup.mk' _) :=
  fun _ hg ↦ mem_comapAb.mp hg

/-- The map `(G/V)^ab → G^ab ⧸ U` for `V` the preimage of `U`, sending the class of `g` to the
class of `g`. It inverts the projection `abelianizationRestrict V` modulo `U`
(`quotientOfAbelianizationGal_abelianizationRestrict`). -/
private def quotientOfAbelianizationGal (U : OpenNormalSubgroup (TopologicalAbelianization G)) :
    Abelianization (ofOpenNormal (comapAb U)).Gal →* TopologicalAbelianization G ⧸ U.toSubgroup :=
  Abelianization.lift <|
    (QuotientGroup.map _ _ (QuotientGroup.mk' _) (comapAb_le_comap U)).comp
      (galOfOpenNormalEquiv (comapAb U)).toMonoidHom

private theorem quotientOfAbelianizationGal_of_mk
    (U : OpenNormalSubgroup (TopologicalAbelianization G))
    (g : (ofOpenNormal (comapAb U)).ground) :
    quotientOfAbelianizationGal U (Abelianization.of (g : (ofOpenNormal (comapAb U)).Gal)) =
      (((g : G) : TopologicalAbelianization G) : TopologicalAbelianization G ⧸ U.toSubgroup) := by
  rw [quotientOfAbelianizationGal, Abelianization.lift_apply_of, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, galOfOpenNormalEquiv_mk, QuotientGroup.map_mk,
    QuotientGroup.mk'_apply]

/-- Reducing `x ∈ G^ab` modulo `U` factors through the projection onto `(G/V)^ab`, for `V` the
preimage of `U`. -/
private theorem quotientOfAbelianizationGal_abelianizationRestrict
    (U : OpenNormalSubgroup (TopologicalAbelianization G)) (x : TopologicalAbelianization G) :
    quotientOfAbelianizationGal U (abelianizationRestrict (comapAb U) (Additive.ofMul x)).toMul =
      (x : TopologicalAbelianization G ⧸ U.toSubgroup) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∈ (ofOpenNormal (comapAb U)).ground := by simp
    exact (congrArg _ (congrArg Additive.toMul
      (abelianizationRestrict_mk (comapAb U) ⟨g, hg⟩))).trans
      (quotientOfAbelianizationGal_of_mk U ⟨g, hg⟩)

/-- The maps `(G/V)^ab → G^ab ⧸ U` are compatible with the quotient maps of nested layers. -/
private theorem mapOfLE_quotientOfAbelianizationGal
    {U U' : OpenNormalSubgroup (TopologicalAbelianization G)} (hle : U ≤ U')
    (T : LayerRefinement (ofOpenNormal (comapAb U')) (ofOpenNormal (comapAb U)))
    (z : Abelianization (ofOpenNormal (comapAb U)).Gal) :
    QuotientGroup.mapOfLE hle (quotientOfAbelianizationGal U z) =
      quotientOfAbelianizationGal U' (T.quotientHom (Additive.ofMul z)).toMul := by
  obtain ⟨γ, rfl⟩ : ∃ γ, Abelianization.of γ = z := QuotientGroup.mk_surjective z
  induction γ using QuotientGroup.induction_on with
    | H g =>
      rw [LayerRefinement.quotientHom_of, toMul_ofMul, LayerRefinement.galHom_mk,
        quotientOfAbelianizationGal_of_mk, quotientOfAbelianizationGal_of_mk,
        QuotientGroup.mapOfLE_mk, Subgroup.coe_inclusion]

/-- **Every open subgroup of `G^ab` is cut out by a finite layer.** For every open subgroup `U` of
`G^ab` there is an open normal subgroup `V` of `G` (the preimage of `U`) such that `U` is the kernel
of the projection `G^ab → (G/V)^ab`. -/
theorem NormalLayer.exists_abelianizationRestrict_eq_zero_iff
    (U : OpenSubgroup (TopologicalAbelianization G)) :
    ∃ V : OpenNormalSubgroup G, ∀ x : TopologicalAbelianization G,
      abelianizationRestrict V (Additive.ofMul x) = 0 ↔ x ∈ U := by
  -- `G^ab` is commutative, so `U` is normal.
  let U' : OpenNormalSubgroup (TopologicalAbelianization G) :=
    { toOpenSubgroup := U, isNormal' := inferInstance }
  refine ⟨comapAb U', fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · have hx := quotientOfAbelianizationGal_abelianizationRestrict U' x
    rw [h, toMul_zero, map_one] at hx
    exact (QuotientGroup.eq_one_iff x).mp hx.symm
  · induction x using QuotientGroup.induction_on with
    | H g =>
      have hg : g ∈ (ofOpenNormal (comapAb U')).ground := by simp
      have hgV : g ∈ (comapAb U').toSubgroup := mem_comapAb.mpr h
      rw [abelianizationRestrict_mk (comapAb U') ⟨g, hg⟩, ofMul_eq_zero,
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hgV)),
        map_one]

end Quotient

/-! ### The absolute Artin map -/

namespace ClassFormation

open NormalLayer

variable {F : Formation G} (cf : ClassFormation F)

/-- The finite Artin map of the layer of the preimage of `U`, read in `G^ab ⧸ U`. -/
private def quotientArtinMap (U : OpenNormalSubgroup (TopologicalAbelianization G)) :
    Multiplicative (F.level ⊤) →* TopologicalAbelianization G ⧸ U.toSubgroup :=
  (quotientOfAbelianizationGal U).comp <| AddMonoidHom.toMultiplicativeLeft <|
    (cf.artinMap (ofOpenNormal (comapAb U))).comp
      (groundEquivOfOpenNormal F (comapAb U)).toLinearMap.toAddMonoidHom

private theorem quotientArtinMap_ofAdd (U : OpenNormalSubgroup (TopologicalAbelianization G))
    (a : F.level ⊤) :
    cf.quotientArtinMap U (Multiplicative.ofAdd a) = quotientOfAbelianizationGal U
      (cf.artinMap (ofOpenNormal (comapAb U)) (groundEquivOfOpenNormal F (comapAb U) a)).toMul :=
  (rfl)

/-- The finite Artin maps read in the finite quotients of `G^ab` form a compatible family. -/
private theorem mapOfLE_comp_quotientArtinMap
    {U U' : OpenNormalSubgroup (TopologicalAbelianization G)} (hle : U ≤ U') :
    (QuotientGroup.mapOfLE hle).comp (cf.quotientArtinMap U) = cf.quotientArtinMap U' := by
  have T := LayerRefinement.ofOpenNormal
    (OpenNormalSubgroup.toSubgroup_le.mp fun _ hg ↦ mem_comapAb.mpr (hle (mem_comapAb.mp hg)))
  refine MonoidHom.ext fun a ↦ ?_
  have hground : T.groundEquiv F (groundEquivOfOpenNormal F (comapAb U') a.toAdd) =
      groundEquivOfOpenNormal F (comapAb U) a.toAdd :=
    Subtype.ext (by simp)
  rw [MonoidHom.comp_apply, ← ofAdd_toAdd a, quotientArtinMap_ofAdd, quotientArtinMap_ofAdd,
    mapOfLE_quotientOfAbelianizationGal hle T, ofMul_toMul, cf.artinMap_quotient T, hground]

/-- The **absolute Artin map** `A^G → G^ab` of a class formation over a profinite group `G`: the
inverse limit of the finite Artin maps `A^G → (G/V)^ab` of the layers `V ◁ G`. Its composite with
the projection onto each `(G/V)^ab` is the finite Artin map
(`abelianizationRestrict_absoluteArtinMap`), and it is the only homomorphism with this property
(`eq_absoluteArtinMap_of_forall_abelianizationRestrict`). -/
def absoluteArtinMap : F.level ⊤ →+ Additive (TopologicalAbelianization G) :=
  MonoidHom.toAdditiveRight
    (existsUnique_monoidHom_mk'_comp_eq cf.quotientArtinMap
      fun _ _ hle ↦ cf.mapOfLE_comp_quotientArtinMap hle).exists.choose

/-- Modulo each open normal subgroup `U` of `G^ab`, the absolute Artin map is the finite Artin map
of the layer of the preimage of `U`. -/
private theorem mk_absoluteArtinMap (U : OpenNormalSubgroup (TopologicalAbelianization G))
    (a : F.level ⊤) :
    ((cf.absoluteArtinMap a).toMul : TopologicalAbelianization G ⧸ U.toSubgroup) =
      cf.quotientArtinMap U (Multiplicative.ofAdd a) :=
  DFunLike.congr_fun ((existsUnique_monoidHom_mk'_comp_eq cf.quotientArtinMap
    fun _ _ hle ↦ cf.mapOfLE_comp_quotientArtinMap hle).exists.choose_spec U)
    (Multiplicative.ofAdd a)

/-- **The finite restrictions of the absolute Artin map are the finite Artin maps**: projecting
the absolute Artin symbol of `a ∈ A^G` to the abelianized Galois group `(G/V)^ab` of the layer
`V ◁ G` gives the Artin symbol of `a` for that layer. -/
@[simp]
theorem abelianizationRestrict_absoluteArtinMap (V : OpenNormalSubgroup G) (a : F.level ⊤) :
    abelianizationRestrict V (cf.absoluteArtinMap a) =
      cf.artinMap (ofOpenNormal V) (groundEquivOfOpenNormal F V a) := by
  set ρ := MonoidHom.toAdditive.symm (abelianizationRestrict V) with hρdef
  have hmem (g : G) : g ∈ (ofOpenNormal V).ground := by simp
  have hρ (g : G) : ρ (g : TopologicalAbelianization G) =
      Abelianization.of ((⟨g, hmem g⟩ : (ofOpenNormal V).ground) : (ofOpenNormal V).Gal) := by
    rw [hρdef, MonoidHom.toAdditive_symm_apply_apply]
    exact congrArg Additive.toMul (abelianizationRestrict_mk V ⟨g, hmem g⟩)
  -- The kernel `U` of the projection is open in `G^ab`: its preimage in `G` contains `V`.
  have hVU : V.toSubgroup ≤ ρ.ker.comap (QuotientGroup.mk' _) := fun g hg ↦ by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, QuotientGroup.mk'_apply, hρ,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hg)), map_one]
  let U : OpenNormalSubgroup (TopologicalAbelianization G) :=
    { toSubgroup := ρ.ker
      isOpen' := (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.mp
        (Subgroup.isOpen_mono hVU V.isOpen') }
  -- The layer of `V` refines the layer of the preimage of `U`. Modulo `U`, the absolute Artin
  -- symbol is the Artin symbol for the latter layer, hence the image of that for `V`.
  have T := LayerRefinement.ofOpenNormal
    (OpenNormalSubgroup.toSubgroup_le.mp fun g hg ↦ mem_comapAb.mpr (hVU hg) : V ≤ comapAb U)
  have hcomp (y : Additive (Abelianization (ofOpenNormal V).Gal)) :
      QuotientGroup.lift U.toSubgroup ρ (fun _ h ↦ h)
        (quotientOfAbelianizationGal U (T.quotientHom y).toMul) = y.toMul := by
    obtain ⟨z, rfl⟩ : ∃ z, Additive.ofMul z = y := ⟨y.toMul, ofMul_toMul y⟩
    obtain ⟨γ, rfl⟩ : ∃ γ, Abelianization.of γ = z := QuotientGroup.mk_surjective z
    induction γ using QuotientGroup.induction_on with
      | H g =>
        rw [LayerRefinement.quotientHom_of, toMul_ofMul, LayerRefinement.galHom_mk,
          quotientOfAbelianizationGal_of_mk, Subgroup.coe_inclusion, QuotientGroup.lift_mk, hρ,
          toMul_ofMul]
  have hground : T.groundEquiv F (groundEquivOfOpenNormal F (comapAb U) a) =
      groundEquivOfOpenNormal F V a :=
    Subtype.ext (by simp)
  have key : QuotientGroup.lift U.toSubgroup ρ (fun _ h ↦ h)
      ((cf.absoluteArtinMap a).toMul : TopologicalAbelianization G ⧸ U.toSubgroup) =
      (cf.artinMap (ofOpenNormal V) (groundEquivOfOpenNormal F V a)).toMul := by
    rw [mk_absoluteArtinMap, quotientArtinMap_ofAdd, cf.artinMap_quotient T, hground]
    exact hcomp _
  rw [QuotientGroup.lift_mk, hρdef, MonoidHom.toAdditive_symm_apply_apply, ofMul_toMul] at key
  exact Additive.toMul.injective key

/-- Elements of `G^ab` with the same projection to `(G/V)^ab` for every open normal subgroup `V`
of `G` are equal. -/
theorem _root_.TauCeti.ClassFieldTheory.NormalLayer.eq_of_forall_abelianizationRestrict_eq
    {x y : Additive (TopologicalAbelianization G)}
    (h : ∀ V : OpenNormalSubgroup G, abelianizationRestrict V x = abelianizationRestrict V y) :
    x = y := by
  refine Additive.toMul.injective (eq_of_forall_mk_eq fun U ↦ ?_)
  rw [← quotientOfAbelianizationGal_abelianizationRestrict,
    ← quotientOfAbelianizationGal_abelianizationRestrict, ofMul_toMul, ofMul_toMul, h]

/-- Elements of `G^ab` with the same projection to `(G/V)^ab` for every open normal subgroup `V`
of `G` contained in a fixed open normal subgroup `N` are equal: the layers below `N` are cofinal. -/
theorem _root_.TauCeti.ClassFieldTheory.NormalLayer.eq_of_forall_le_abelianizationRestrict_eq
    (N : OpenNormalSubgroup G) {x y : Additive (TopologicalAbelianization G)}
    (h : ∀ V ≤ N, abelianizationRestrict V x = abelianizationRestrict V y) : x = y :=
  eq_of_forall_abelianizationRestrict_eq fun V ↦ by
    have T := LayerRefinement.ofOpenNormal (inf_le_left : V ⊓ N ≤ V)
    rw [← T.quotientHom_abelianizationRestrict, h _ inf_le_right,
      T.quotientHom_abelianizationRestrict]

/-- **Uniqueness of the absolute Artin map**: a homomorphism `A^G → G^ab` whose projection to
`(G/V)^ab` is the finite Artin map of the layer `V ◁ G`, for every open normal subgroup `V`, is
the absolute Artin map. -/
theorem eq_absoluteArtinMap_of_forall_abelianizationRestrict
    (φ : F.level ⊤ →+ Additive (TopologicalAbelianization G))
    (hφ : ∀ (V : OpenNormalSubgroup G) (a : F.level ⊤),
      abelianizationRestrict V (φ a) =
        cf.artinMap (ofOpenNormal V) (groundEquivOfOpenNormal F V a)) :
    φ = cf.absoluteArtinMap :=
  AddMonoidHom.ext fun a ↦ eq_of_forall_abelianizationRestrict_eq fun V ↦ by
    rw [hφ, abelianizationRestrict_absoluteArtinMap]

/-- The absolute Artin symbol of `a ∈ A^G` dies in `(G/V)^ab` exactly when `a` is a norm from the
layer `V ◁ G`. -/
theorem abelianizationRestrict_absoluteArtinMap_eq_zero_iff (V : OpenNormalSubgroup G)
    (a : F.level ⊤) :
    abelianizationRestrict V (cf.absoluteArtinMap a) = 0 ↔
      groundEquivOfOpenNormal F V a ∈ (ofOpenNormal V).normSubgroup F := by
  rw [abelianizationRestrict_absoluteArtinMap, artinMap_eq_zero_iff]

/-- **The preimage of an open subgroup under the absolute Artin map is a norm subgroup.** For every
open subgroup `U` of `G^ab` there is an open normal subgroup `V` of `G` such that the absolute Artin
symbol of `a ∈ A^G` lies in `U` exactly when `a` is a norm from the layer `V ◁ G`. -/
theorem exists_absoluteArtinMap_mem_iff (U : OpenSubgroup (TopologicalAbelianization G)) :
    ∃ V : OpenNormalSubgroup G, ∀ a : F.level ⊤,
      (cf.absoluteArtinMap a).toMul ∈ U ↔
        groundEquivOfOpenNormal F V a ∈ (ofOpenNormal V).normSubgroup F := by
  obtain ⟨V, hV⟩ := exists_abelianizationRestrict_eq_zero_iff U
  exact ⟨V, fun a ↦ by
    rw [← hV, ofMul_toMul, abelianizationRestrict_absoluteArtinMap_eq_zero_iff]⟩

/-- **The kernel of the absolute Artin map is the intersection of the norm subgroups**: the
absolute Artin symbol of `a ∈ A^G` vanishes exactly when `a` is a norm from every layer `V ◁ G`. -/
theorem absoluteArtinMap_eq_zero_iff (a : F.level ⊤) :
    cf.absoluteArtinMap a = 0 ↔
      ∀ V : OpenNormalSubgroup G,
        groundEquivOfOpenNormal F V a ∈ (ofOpenNormal V).normSubgroup F := by
  refine ⟨fun h V ↦ ?_, fun h ↦ eq_of_forall_abelianizationRestrict_eq fun V ↦ ?_⟩
  · rw [← abelianizationRestrict_absoluteArtinMap_eq_zero_iff, h, map_zero]
  · rw [map_zero, abelianizationRestrict_absoluteArtinMap_eq_zero_iff]
    exact h V

/-- **The absolute Artin map has dense image**: modulo every open normal subgroup of `G^ab` it is
a finite Artin map, which is surjective. -/
theorem denseRange_absoluteArtinMap : DenseRange cf.absoluteArtinMap := by
  refine (denseRange_iff_forall_surjective_mk (G := TopologicalAbelianization G)
    (f := fun a ↦ (cf.absoluteArtinMap a).toMul)).mpr fun U q ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a', ha'⟩ := cf.surjective_artinMap (ofOpenNormal (comapAb U))
    (abelianizationRestrict (comapAb U) (Additive.ofMul x))
  obtain ⟨a, rfl⟩ := (groundEquivOfOpenNormal F (comapAb U)).surjective a'
  refine ⟨a, ?_⟩
  rw [← quotientOfAbelianizationGal_abelianizationRestrict, ← ha']
  exact (cf.mk_absoluteArtinMap U a).trans (cf.quotientArtinMap_ofAdd U a)

end ClassFormation

end TauCeti.ClassFieldTheory
