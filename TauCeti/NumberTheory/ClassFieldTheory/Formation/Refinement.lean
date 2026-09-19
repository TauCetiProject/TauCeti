/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Refinements of a finite normal layer, and inflation

Let `V ◁ U` be a finite normal layer of a formation, the layer `K/F` in field notation. Enlarging
the top field to a field `K ⊆ L` that is still Galois over `F` gives a layer `L/F`: its top
subgroup `V' ≤ V` is again normal in the *same* ground subgroup `U`. Two layers are related by a
**refinement** when they have the same ground subgroup and the top subgroup of the second lies in
the top subgroup of the first; `LayerRefinement old new` is that relation. Its **relative degree**
is `[V : V']`, the degree `[L : K]` of the new top field over the old one.

A refinement is the dual of a restriction (`LayerRestriction`): there the top subgroup is fixed
and the ground subgroup shrinks. Where a restriction induces an *injection* of Galois groups and
leaves the coefficient module alone, a refinement induces the *surjection*

`LayerRefinement.galHom : U/V' → U/V`,

whose kernel is `V/V'` (`LayerRefinement.galHom_mk_eq_one_iff`), and a genuine enlargement of
coefficient modules, the inclusion `A^V ⊆ A^{V'}` of levels. That inclusion is equivariant along
`galHom` (`LayerRefinement.repHom`), and Mathlib's change-of-group map for the pair is
**inflation**

`LayerRefinement.cohomologyInfl : H^n(U/V, A^V) ⟶ H^n(U/V', A^{V'})`,

the map along the quotient `U/V' → U/V` which reads a cochain on `U/V` with values in
`(A^{V'})^{V/V'} = A^V` as a cochain on `U/V'`. In degree zero it is the identity of the common
ground level `A^U` (`LayerRefinement.groundLevelEquiv_cohomologyInfl_zero_apply`).

Refinements compose (`LayerRefinement.trans`): along a tower `F ⊆ K ⊆ L ⊆ M` of top fields the
relative degree is multiplicative, the Galois-group quotients compose, and inflation is
functorial. In positive degree the Tate groups are the ordinary cohomology groups, and inflation
of Tate cohomology, `LayerRefinement.tateInfl`, is `cohomologyInfl` read through that
identification. Any two layers over the same ground, in particular any two refinements of one
layer, have a common refinement, the compositum of the two top fields, whose top subgroup is the
intersection of the two top subgroups (`LayerRefinement.exists_commonRefinement`). This is what
lets the invariant of a class, defined by inflating it to *some* refinement, be compared across
refinements.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRefinement`: the relation `new` is `old` with its top field
  enlarged.
* `TauCeti.ClassFieldTheory.LayerRefinement.relativeDegree`: the relative degree `[V : V']`.
* `TauCeti.ClassFieldTheory.LayerRefinement.galHom`: the quotient map `U/V' → U/V`.
* `TauCeti.ClassFieldTheory.LayerRefinement.repHom`: the inclusion `A^V ⊆ A^{V'}` of coefficient
  modules, equivariant along `galHom`.
* `TauCeti.ClassFieldTheory.LayerRefinement.groundEquiv`: the identity of the common ground level.
* `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl`: inflation of layer cohomology.
* `TauCeti.ClassFieldTheory.LayerRefinement.tateInfl`: inflation of layer Tate cohomology, in
  positive degrees.

## Main statements

* `TauCeti.ClassFieldTheory.LayerRefinement.galHom_surjective` and
  `TauCeti.ClassFieldTheory.LayerRefinement.galHom_mk_eq_one_iff`: the map of Galois groups is the
  quotient by `V/V'`.
* `TauCeti.ClassFieldTheory.LayerRefinement.degree_mul_relativeDegree`:
  `[U : V] * [V : V'] = [U : V']`.
* `TauCeti.ClassFieldTheory.LayerRefinement.relativeDegree_trans`,
  `TauCeti.ClassFieldTheory.LayerRefinement.galHom_trans`,
  `TauCeti.ClassFieldTheory.LayerRefinement.cohomologyInfl_trans` and
  `TauCeti.ClassFieldTheory.LayerRefinement.tateInfl_trans`: towers of refinements.
* `TauCeti.ClassFieldTheory.LayerRefinement.groundLevelEquiv_cohomologyInfl_zero_apply`: in degree
  zero, inflation is the identity of the ground level.
* `TauCeti.ClassFieldTheory.LayerRefinement.tateInfl_comp_tateHIsoH_hom`: in positive degree, Tate
  inflation is ordinary inflation.
* `TauCeti.ClassFieldTheory.LayerRefinement.exists_commonRefinement`: two layers over the same
  ground have a common refinement.

## Implementation notes

As for `LayerRestriction`, a refinement is a `Prop`-valued relation between two layers that
already exist, so refinements of arbitrary pairs of layers can be composed without transporting a
layer along an equality. The two ground subgroups are equal but their coercions to types are not
the same type, which is why `galHom` is Mathlib's `QuotientGroup.quotientMapSubgroupOfOfLe` rather
than a quotient map on one fixed group.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–2.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
* J.-P. Serre, *Local Fields*, Chapter VII, §5, and Chapter XI, §1.
-/

-- The signatures of `LayerRefinement`, `relativeDegree`, `cohomologyInfl`, `tateInfl`,
-- `groundEquiv`, the tower lemmas and `exists_commonRefinement` below follow the Tau Ceti
-- `ClassFieldTheory` blueprint, `README.md` and `Suggested.lean`, which write down the refinement
-- relation between two normal layers formalised here.

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-! ### Refinements -/

/-- A **refinement** of finite normal layers: `new` is `old` with its top field enlarged. In field
notation, `F ⊆ K ⊆ L` takes the layer `K/F` to the layer `L/F`, so the ground subgroup is
unchanged and the top subgroup shrinks. -/
structure LayerRefinement (old new : NormalLayer G) : Prop where
  /-- a refinement does not move the ground subgroup -/
  same_ground : old.ground = new.ground
  /-- a refinement shrinks the top subgroup -/
  top_le : new.top ≤ old.top

namespace LayerRefinement

variable {old new : NormalLayer G}

/-- The ground subgroups of a refinement, compared as subgroups of the ambient group. -/
theorem same_ground_toSubgroup (T : LayerRefinement old new) :
    old.ground.toSubgroup = new.ground.toSubgroup :=
  congrArg OpenSubgroup.toSubgroup T.same_ground

/-- The top subgroups of a refinement, compared as subgroups of the ambient group. -/
theorem top_toSubgroup_le (T : LayerRefinement old new) :
    new.top.toSubgroup ≤ old.top.toSubgroup :=
  OpenSubgroup.toSubgroup_le.2 T.top_le

/-- The **relative degree** `[V : V']` of a refinement, the degree of the new top field over the
old one. -/
def relativeDegree (_T : LayerRefinement old new) : ℕ :=
  new.top.toSubgroup.relIndex old.top.toSubgroup

/-- The relative degree is the relative index of the two top subgroups. -/
@[simp]
theorem relativeDegree_def (T : LayerRefinement old new) :
    T.relativeDegree = new.top.toSubgroup.relIndex old.top.toSubgroup :=
  (rfl)

/-- **The degree of a layer is multiplicative along a refinement:** `[U : V] * [V : V'] =
[U : V']`. -/
theorem degree_mul_relativeDegree (T : LayerRefinement old new) :
    old.degree * T.relativeDegree = new.degree := by
  rw [NormalLayer.degree_eq_relIndex, NormalLayer.degree_eq_relIndex, relativeDegree_def,
    ← T.same_ground_toSubgroup, mul_comm]
  exact Subgroup.relIndex_mul_relIndex _ _ _ T.top_toSubgroup_le
    (OpenSubgroup.toSubgroup_le.2 old.top_le_ground)

/-- The relative degree of a refinement is positive: the Galois groups involved are finite. -/
theorem relativeDegree_pos (T : LayerRefinement old new) : 0 < T.relativeDegree :=
  Nat.pos_of_mul_pos_left (T.degree_mul_relativeDegree ▸ new.degree_pos)

/-- The homomorphism `U/V' → U/V` of Galois groups induced by a refinement. It is surjective
(`galHom_surjective`) with kernel `V/V'` (`galHom_mk_eq_one_iff`). -/
def galHom (T : LayerRefinement old new) : new.Gal →* old.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ new.top.toSubgroup new.ground.toSubgroup
    old.top.toSubgroup old.ground.toSubgroup new.normal old.normal
    T.top_toSubgroup_le T.same_ground_toSubgroup.ge

/-- The homomorphism of Galois groups sends the class of an element of `U` to its class. -/
@[simp]
theorem galHom_mk (T : LayerRefinement old new) (w : new.ground) :
    T.galHom (QuotientGroup.mk w) =
      QuotientGroup.mk (Subgroup.inclusion T.same_ground_toSubgroup.ge w) :=
  (rfl)

/-- **The Galois group of the old layer is a quotient of the Galois group of the new one.** -/
theorem galHom_surjective (T : LayerRefinement old new) : Function.Surjective T.galHom := by
  intro γ
  induction γ using QuotientGroup.induction_on with
  | H u =>
    exact ⟨QuotientGroup.mk (Subgroup.inclusion T.same_ground_toSubgroup.le u),
      congrArg QuotientGroup.mk (Subtype.ext rfl)⟩

/-- **The kernel of the homomorphism of Galois groups is `V/V'`:** the class of an element of `U`
dies in `U/V` exactly when the element lies in the old top subgroup. -/
theorem galHom_mk_eq_one_iff (T : LayerRefinement old new) (w : new.ground) :
    T.galHom (QuotientGroup.mk w) = 1 ↔ (w : G) ∈ old.top := by
  rw [galHom_mk, QuotientGroup.eq_one_iff (N := old.relativeTop), Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion, OpenSubgroup.mem_toSubgroup]

/-- The old top level sits inside the new one: a smaller subgroup fixes more elements. -/
theorem level_top_le (T : LayerRefinement old new) (F : Formation G) :
    F.level old.top ≤ F.level new.top :=
  F.level_antitone T.top_le

/-- **The inclusion `A^V ⊆ A^{V'}` of coefficient modules**, equivariant along the quotient map
`galHom` of Galois groups: an element of `U` acts on an element of `A^V` in the same way whether
the element is read in `A^V` or in `A^{V'}`. -/
def repHom (T : LayerRefinement old new) (F : Formation G) :
    Rep.res T.galHom (old.rep F) ⟶ new.rep F :=
  Rep.ofHom
    { toLinearMap := Submodule.inclusion (T.level_top_le F)
      isIntertwining' := fun γ ↦ by
        induction γ using QuotientGroup.induction_on with
        | H w =>
          ext x
          -- Both sides are the action of `w` on `x` in the ambient module; the goal is stated on
          -- the linear maps underlying the two representations, so it is read there.
          change ((Submodule.inclusion (T.level_top_le F)
              ((old.rep F).ρ (T.galHom (QuotientGroup.mk w)) x) : F.level new.top) :
                F.toRep.V) =
            (((new.rep F).ρ (QuotientGroup.mk w)
              (Submodule.inclusion (T.level_top_le F) x) : F.level new.top) : F.toRep.V)
          rw [galHom_mk, Submodule.coe_inclusion, NormalLayer.rep_ρ_mk_apply_coe,
            NormalLayer.rep_ρ_mk_apply_coe, Submodule.coe_inclusion, Subgroup.coe_inclusion] }

/-- The inclusion of coefficient modules moves no element of the ambient module. -/
@[simp]
theorem repHom_hom_apply_coe (T : LayerRefinement old new) (F : Formation G)
    (x : F.level old.top) :
    (((T.repHom F).hom x : F.level new.top) : F.toRep.V) = (x : F.toRep.V) :=
  (rfl)

/-- The **ground-level identification** of a refinement: both layers have the same ground
subgroup `U`, hence the same ground level `A^U`. -/
def groundEquiv (T : LayerRefinement old new) (F : Formation G) :
    F.level old.ground ≃ₗ[ℤ] F.level new.ground :=
  LinearEquiv.ofEq _ _ (congrArg F.level T.same_ground)

@[simp]
theorem groundEquiv_apply_coe (T : LayerRefinement old new) (F : Formation G)
    (x : F.level old.ground) :
    ((T.groundEquiv F x : F.level new.ground) : F.toRep.V) = (x : F.toRep.V) :=
  (rfl)

/-- The layers `V ◁ ⊤` of two nested open normal subgroups `V' ≤ V` form a refinement: the finite
Galois extension cut out by `V'` contains the one cut out by `V`. -/
theorem ofOpenNormal {V V' : OpenNormalSubgroup G} (h : V' ≤ V) :
    LayerRefinement (NormalLayer.ofOpenNormal V) (NormalLayer.ofOpenNormal V') := by
  refine ⟨?_, ?_⟩
  · rw [NormalLayer.ground_ofOpenNormal, NormalLayer.ground_ofOpenNormal]
  · rw [NormalLayer.top_ofOpenNormal, NormalLayer.top_ofOpenNormal]
    exact h

/-! ### Towers of refinements -/

/-- **Every layer is a refinement of itself.** -/
theorem refl (L : NormalLayer G) : LayerRefinement L L :=
  ⟨rfl, le_rfl⟩

/-- The homomorphism of Galois groups attached to the trivial refinement is the identity. -/
@[simp]
theorem galHom_self {L : NormalLayer G} (T : LayerRefinement L L) :
    T.galHom = MonoidHom.id L.Gal :=
  MonoidHom.ext fun γ ↦ by
    induction γ using QuotientGroup.induction_on with
    | H w => exact congrArg QuotientGroup.mk (Subtype.ext rfl)

/-- The coefficient map attached to the trivial refinement is the identity on underlying linear
maps. -/
theorem repHom_self_toLinearMap {L : NormalLayer G} (T : LayerRefinement L L)
    (F : Formation G) :
    (T.repHom F).hom.toLinearMap =
      (𝟙 (L.rep F) : L.rep F ⟶ L.rep F).hom.toLinearMap := by
  ext x
  rfl

variable {a b c : NormalLayer G}

/-- **Refinements compose:** enlarging the top field twice is one refinement. In field notation
this is the tower `F ⊆ K ⊆ L ⊆ M`. -/
theorem trans (T : LayerRefinement a b) (T' : LayerRefinement b c) : LayerRefinement a c :=
  ⟨T.same_ground.trans T'.same_ground, T'.top_le.trans T.top_le⟩

/-- **The relative degree is multiplicative along a tower of refinements:**
`[V : V''] = [V : V'] * [V' : V'']`. -/
theorem relativeDegree_trans (T : LayerRefinement a b) (T' : LayerRefinement b c) :
    (T.trans T').relativeDegree = T.relativeDegree * T'.relativeDegree := by
  rw [relativeDegree_def, relativeDegree_def, relativeDegree_def, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex _ _ _ T'.top_toSubgroup_le T.top_toSubgroup_le).symm

/-- **The quotient maps of Galois groups compose along a tower of refinements.** -/
theorem galHom_trans (T : LayerRefinement a b) (T' : LayerRefinement b c) :
    (T.trans T').galHom = T.galHom.comp T'.galHom :=
  MonoidHom.ext fun γ ↦ by
    induction γ using QuotientGroup.induction_on with
    | H w => exact congrArg QuotientGroup.mk (Subtype.ext rfl)

/-- The coefficient inclusions compose along a tower of refinements, on underlying linear maps. -/
theorem repHom_trans_toLinearMap (T : LayerRefinement a b) (T' : LayerRefinement b c)
    (F : Formation G) :
    ((T.trans T').repHom F).hom.toLinearMap =
      (((Rep.resFunctor T'.galHom).map (T.repHom F) ≫ T'.repHom F).hom.toLinearMap) := by
  ext x
  rfl

/-! ### Inflation of layer cohomology -/

/-- **Inflation of cohomology along a refinement of layers**, the map

`H^n(U/V, A^V) ⟶ H^n(U/V', A^{V'})`

induced by the quotient map `U/V' → U/V` of Galois groups and the inclusion `A^V ⊆ A^{V'}` of
coefficient modules: Mathlib's change-of-group map for that pair. It has the shape of Mathlib's
inflation `groupCohomology.infNatTrans`, the change-of-group map along `G → G ⧸ S` and the
inclusion of `S`-invariants, with `U/V' → U/V` in place of `G → G ⧸ S` and `A^V = (A^{V'})^{V/V'}`
in place of the invariants. -/
def cohomologyInfl (T : LayerRefinement old new) (F : Formation G) (n : ℕ) :
    old.H F n ⟶ new.H F n :=
  groupCohomology.map T.galHom (T.repHom F) n

/-- Inflation is Mathlib's cohomology map for the quotient homomorphism and coefficient
inclusion attached to the refinement. -/
theorem cohomologyInfl_def (T : LayerRefinement old new) (F : Formation G) (n : ℕ) :
    T.cohomologyInfl F n = groupCohomology.map T.galHom (T.repHom F) n :=
  (rfl)

/-- **Inflating along the trivial refinement does nothing.** -/
@[simp]
theorem cohomologyInfl_self {L : NormalLayer G} (T : LayerRefinement L L) (F : Formation G)
    (n : ℕ) : T.cohomologyInfl F n = 𝟙 (L.H F n) := by
  rw [cohomologyInfl_def, groupCohomology.map_congr T.galHom_self
    (T.repHom_self_toLinearMap F) n, groupCohomology.map_id]

/-- **Inflation of cohomology is functorial along a tower of refinements.** Inflating from `K/F`
to `L/F` and then to `M/F` is inflating from `K/F` to `M/F`. -/
theorem cohomologyInfl_trans (T : LayerRefinement a b) (T' : LayerRefinement b c)
    (F : Formation G) (n : ℕ) :
    (T.trans T').cohomologyInfl F n = T.cohomologyInfl F n ≫ T'.cohomologyInfl F n := by
  rw [cohomologyInfl_def, cohomologyInfl_def, cohomologyInfl_def,
    ← groupCohomology.map_comp T.galHom T'.galHom (T.repHom F) (T'.repHom F) n]
  exact groupCohomology.map_congr (galHom_trans T T') (repHom_trans_toLinearMap T T' F) n

/-- **In degree zero, inflation of cohomology is the identity of the ground level.** Read through
the identification of `H⁰(U/V, A^V)` with the ground level `A^U`, inflating a class from the layer
`K/F` to the layer `L/F` does not move it. -/
theorem groundLevelEquiv_cohomologyInfl_zero_apply (T : LayerRefinement old new)
    (F : Formation G) (x : old.H F 0) :
    new.groundLevelEquiv F
        ((groupCohomology.H0Iso (new.rep F)).hom.hom (T.cohomologyInfl F 0 x)) =
      T.groundEquiv F (old.groundLevelEquiv F
        ((groupCohomology.H0Iso (old.rep F)).hom.hom x)) := by
  refine Subtype.ext ?_
  rw [NormalLayer.groundLevelEquiv_apply_coe, groundEquiv_apply_coe,
    NormalLayer.groundLevelEquiv_apply_coe]
  have h := groupCohomology.map_H0Iso_hom_f_apply T.galHom (T.repHom F) x
  exact (congrArg Subtype.val h).trans (T.repHom_hom_apply_coe F _)

/-- **Inflation of Tate cohomology along a refinement of layers**, in positive degrees only:
`Ĥ^r(U/V, A^V) ⟶ Ĥ^r(U/V', A^{V'})` for `r ≠ 0`. In positive degree the Tate groups of a
layer are its ordinary cohomology groups (`NormalLayer.tateHIsoH`), and Tate inflation is
`cohomologyInfl` read through that identification at both layers. -/
def tateInfl (T : LayerRefinement old new) (F : Formation G) (r : ℕ) [NeZero r] :
    old.TateH F r ⟶ new.TateH F r :=
  (old.tateHIsoH F r).hom ≫ T.cohomologyInfl F r ≫ (new.tateHIsoH F r).inv

/-- **Tate inflation is ordinary inflation read through the identifications** `tateHIsoH` of
positive-degree Tate cohomology with ordinary cohomology at the two layers. -/
theorem tateInfl_def (T : LayerRefinement old new) (F : Formation G) (r : ℕ) [NeZero r] :
    T.tateInfl F r = (old.tateHIsoH F r).hom ≫ T.cohomologyInfl F r ≫ (new.tateHIsoH F r).inv :=
  (rfl)

/-- **Tate inflation commutes with the identifications of positive-degree Tate cohomology with
ordinary cohomology:** inflating a Tate class and reading it as an ordinary class is inflating the
ordinary class. -/
@[reassoc]
theorem tateInfl_comp_tateHIsoH_hom (T : LayerRefinement old new) (F : Formation G) (r : ℕ)
    [NeZero r] :
    T.tateInfl F r ≫ (new.tateHIsoH F r).hom = (old.tateHIsoH F r).hom ≫ T.cohomologyInfl F r := by
  rw [tateInfl_def, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Inflating Tate cohomology along the trivial refinement does nothing.** -/
@[simp]
theorem tateInfl_self {L : NormalLayer G} (T : LayerRefinement L L) (F : Formation G) (r : ℕ)
    [NeZero r] : T.tateInfl F r = 𝟙 (L.TateH F r) := by
  rw [tateInfl_def, cohomologyInfl_self, Category.id_comp, Iso.hom_inv_id]

/-- **Inflation of Tate cohomology is functorial along a tower of refinements**, in every positive
degree. -/
theorem tateInfl_trans (T : LayerRefinement a b) (T' : LayerRefinement b c) (F : Formation G)
    (r : ℕ) [NeZero r] :
    (T.trans T').tateInfl F r = T.tateInfl F r ≫ T'.tateInfl F r := by
  rw [tateInfl_def, tateInfl_def, tateInfl_def, cohomologyInfl_trans T T']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-! ### Common refinements -/

/-- **Two layers over the same ground have a common refinement.** In field notation, two Galois
extensions `L₁/F` and `L₂/F` are both contained in their compositum, whose layer has top subgroup
`V₁ ⊓ V₂`. Applied to two refinements of one layer, this is what lets a construction made at "some
refinement" of a layer be compared across refinements. -/
theorem exists_commonRefinement {L₁ L₂ : NormalLayer G} (h : L₁.ground = L₂.ground) :
    ∃ newer : NormalLayer G, LayerRefinement L₁ newer ∧ LayerRefinement L₂ newer := by
  refine ⟨{ ground := L₁.ground
            top := L₁.top ⊓ L₂.top
            top_le_ground := inf_le_left.trans L₁.top_le_ground
            normal := ⟨fun v hv u ↦ Subgroup.mem_subgroupOf.2 ?_⟩ },
    ⟨rfl, inf_le_left⟩, ⟨h.symm, inf_le_right⟩⟩
  have hv' : (v : G) ∈ L₁.top ∧ (v : G) ∈ L₂.top :=
    OpenSubgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hv)
  exact OpenSubgroup.mem_inf.2
    ⟨L₁.conj_mem_top u.2 hv'.1, L₂.conj_mem_top (h ▸ u.2) hv'.2⟩

end LayerRefinement

end TauCeti.ClassFieldTheory
