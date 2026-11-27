/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.Topology.Compactness.LocallyCompact
import TauCeti.Topology.Homeomorph.Quotient

/-!
# Continuous maps from group quotients and compact orbit spaces

This file records continuity results for maps out of group quotients that do not require
transitivity of an action, and a compactness criterion for orbit spaces.

The orbit space of an action is compact as soon as some compact set meets every orbit, since the
orbit space is then the image of that set under the continuous orbit projection. When the action
is by homeomorphisms and the space is weakly locally compact, for instance a finite-dimensional
manifold, this is also necessary: the orbit projection is open, so the compact orbit space is the
image of a compact set. For a free properly discontinuous action this is how compactness of a
quotient manifold is read off from a compact fundamental domain upstairs.

## Main results

* `Topology.IsQuotientMap.orbitRelQuotientHomeomorph`: a quotient map whose fibres are the
  orbits identifies the orbit space with its target.
* `TauCeti.continuous_ofQuotientStabilizer` proves continuity of the orbit map descended to a
  stabilizer quotient when the corresponding orbit map is continuous.
* `TauCeti.continuous_orbitRelQuotientLift_iff`: the descent of a `G`-invariant map to the orbit
  space is continuous exactly when the map is.
* `TauCeti.continuous_section_orbitRelQuotientRec_iff`: the descent of a `G`-invariant section of
  the pullback of a family `V` over the orbit space is continuous, as a map into the total space,
  exactly when the section upstairs is.
* `MulActionHom.isEmbedding_orbitRelQuotientMap`: an equivariant embedding descends to an
  embedding of orbit spaces when the acting-group map is surjective and the target action is by
  homeomorphisms.
* `SubMulAction.isOpenEmbedding_orbitRelQuotientMap`: for an open slice `S` for a subgroup `H`, an
  `H`-invariant open set moved into itself only by elements of `H`, the map `S / H → X / G` of
  orbit spaces is an open embedding. For `H = ⊥` this recovers
  `TauCeti.isOpenEmbedding_quotientMk_domRestrict_of_disjoint_smul`.
* `TauCeti.MulAction.compactSpace_orbitRelQuotient_of_isCompact`: if a compact set meets every
  orbit, the orbit space is compact.
* `TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact`: for an action by
  homeomorphisms of a weakly locally compact space, the orbit space is compact exactly when some
  compact set meets every orbit.
* `QuotientGroup.compactSpace_iff_exists_isCompact_mul_eq_univ`: its specialization to the right
  action of a subgroup `Γ`: in a weakly locally compact group with separately continuous
  multiplication, `G ⧸ Γ` is compact exactly when `K * Γ = G` for a compact set `K`.
* `TauCeti.AddAction.orbitRelQuotientHomeomorphMultiplicative` and
  `TauCeti.MulAction.orbitRelQuotientHomeomorphAdditive`: canonical homeomorphisms identifying the
  orbit space of an action of `G` with that of `Multiplicative G` or `Additive G`.

The compactness statements have additive versions, for `AddAction.orbitRel.Quotient` and for
`G ⧸ Γ` with `K + Γ = G`.
-/

public section

open MulAction

namespace TauCeti

section Lift

variable {G X Y : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {hf : ∀ (g : G) (x : X), f (g • x) = f x}

/-- The descent of a `G`-invariant map to the orbit space is continuous exactly when the map is. -/
theorem continuous_orbitRelQuotientLift_iff :
    Continuous (MulAction.orbitRelQuotientLift f hf) ↔ Continuous f := by
  have hq : Topology.IsQuotientMap (Quotient.mk (MulAction.orbitRel G X)) := isQuotientMap_quot_mk
  rw [hq.continuous_iff, MulAction.orbitRelQuotientLift_comp_mk]

open Bundle in
/-- The descent of an invariant section is continuous, as a map into the total space, exactly when
the section upstairs is. -/
theorem continuous_section_orbitRelQuotientRec_iff {F : Type*}
    {V : MulAction.orbitRel.Quotient G X → Type*} [TopologicalSpace (TotalSpace F V)]
    {t : ∀ x : X, V (Quotient.mk (MulAction.orbitRel G X) x)}
    {ht : ∀ (g : G) (x : X), t (g • x) ≍ t x} :
    Continuous (fun q ↦ TotalSpace.mk' F q (MulAction.orbitRelQuotientRec t ht q)) ↔
      Continuous fun x ↦ TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G X) x) (t x) := by
  have hq : Topology.IsQuotientMap (Quotient.mk (MulAction.orbitRel G X)) := isQuotientMap_quot_mk
  rw [hq.continuous_iff]
  simp only [Function.comp_def, MulAction.orbitRelQuotientRec_mk]

end Lift

section Slice

open Set Topology

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]

/-- **Orbit spaces of open slices.** Let `S` be an open `H`-invariant subset of `X` such that every
element of `G` carrying a point of `S` into `S` lies in `H`. Then the map `S / H → X / G` sending
an `H`-orbit to its `G`-orbit is an open embedding of orbit spaces. -/
theorem _root_.SubMulAction.isOpenEmbedding_orbitRelQuotientMap {H : Subgroup G}
    (S : SubMulAction H X) (hS_open : IsOpen (S : Set X))
    (hS : ∀ (g : G) (y : X), y ∈ S → g • y ∈ S → g ∈ H) :
    IsOpenEmbedding S.orbitRelQuotientMap := by
  -- Composed with the orbit projection of `S`, the map is the orbit projection of `X` on `S`.
  have hcont : Continuous S.orbitRelQuotientMap := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    exact S.orbitRelQuotientMap_comp_mk ▸ continuous_quot_mk.comp continuous_subtypeVal
  refine .of_continuous_injective_isOpenMap hcont (S.orbitRelQuotientMap_injective hS)
    fun U hU ↦ ?_
  -- The image of `U` is the image in `X / G` of the open set of points of `S` lying over `U`.
  rw [← Quotient.mk_surjective.image_preimage U, ← image_comp, S.orbitRelQuotientMap_comp_mk,
    image_comp]
  exact isOpenMap_quotient_mk'_mul _
    (hS_open.isOpenMap_subtypeVal _ (hU.preimage continuous_quot_mk))

end Slice

/-- An equivariant embedding descends to an embedding of orbit spaces when the map of acting
groups is surjective and the target action is by homeomorphisms. -/
theorem _root_.MulActionHom.isEmbedding_orbitRelQuotientMap
    {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    [TopologicalSpace X] [TopologicalSpace Y] [ContinuousConstSMul H Y]
    {σ : G → H} (φ : X →ₑ[σ] Y) (hφ : Topology.IsEmbedding φ)
    (hσ : Function.Surjective σ) : Topology.IsEmbedding φ.orbitRelQuotientMap := by
  refine isEmbedding_of_isOpenQuotientMap_of_isInducing φ φ.orbitRelQuotientMap
    (Quotient.mk _) (Quotient.mk _) φ.orbitRelQuotientMap_comp_mk
    hφ.isInducing isQuotientMap_quotient_mk'
    MulAction.isOpenQuotientMap_quotientMk (φ.orbitRelQuotientMap_injective hφ.injective hσ) ?_
  rintro y ⟨_, ⟨x, rfl⟩, hx⟩
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hx)
  obtain ⟨k, hk⟩ := hσ g⁻¹
  exact ⟨k • x, by simpa [map_smulₛₗ, hk] using congrArg (fun z ↦ g⁻¹ • z) hg.symm⟩

section Compact

open Set

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

/-- **Compact fundamental domain.** If a compact set `K` meets every orbit, the orbit space is
compact: it is the image of `K` under the continuous orbit projection. -/
@[to_additive AddAction.compactSpace_orbitRelQuotient_of_isCompact /-- **Compact fundamental
domain.** If a compact set `K` meets every orbit of an additive action, the orbit space is compact:
it is the image of `K` under the continuous orbit projection. -/]
theorem MulAction.compactSpace_orbitRelQuotient_of_isCompact {K : Set X} (hK : IsCompact K)
    (hKG : ∀ x : X, ∃ g : G, g • x ∈ K) : CompactSpace (MulAction.orbitRel.Quotient G X) := by
  have himage : Quotient.mk (MulAction.orbitRel G X) '' K = univ := by
    refine eq_univ_of_forall fun q ↦ ?_
    induction q using Quotient.inductionOn with | h x =>
    obtain ⟨g, hg⟩ := hKG x
    exact ⟨g • x, hg, Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit x g))⟩
  exact isCompact_univ_iff.1 (himage ▸ hK.image continuous_quotient_mk')

/-- For an action by homeomorphisms of a weakly locally compact space, the orbit space is compact
exactly when some compact set meets every orbit. -/
@[to_additive AddAction.compactSpace_orbitRelQuotient_iff_exists_isCompact /-- For an additive
action by homeomorphisms of a weakly locally compact space, the orbit space is compact exactly when
some compact set meets every orbit. -/]
theorem MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact [ContinuousConstSMul G X]
    [WeaklyLocallyCompactSpace X] :
    CompactSpace (MulAction.orbitRel.Quotient G X) ↔
      ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, g • x ∈ K := by
  refine ⟨fun _ ↦ ?_, fun ⟨K, hK, hKG⟩ ↦ compactSpace_orbitRelQuotient_of_isCompact hK hKG⟩
  -- The orbit projection is open, so the compact orbit space is the image of a compact set.
  obtain ⟨K, hK, hsub⟩ := (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)).isOpenMap
    |>.exists_isCompact_subset_image isCompact_univ Quotient.mk_surjective.range_eq.ge
  refine ⟨K, hK, fun x ↦ ?_⟩
  obtain ⟨y, hy, hyx⟩ := hsub (mem_univ (Quotient.mk (MulAction.orbitRel G X) x))
  obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hyx)
  exact ⟨g, hy⟩

end Compact

end TauCeti

namespace QuotientGroup

open Set

open scoped Pointwise

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- In a weakly locally compact group with separately continuous multiplication, `G ⧸ Γ` is
compact exactly when `K * Γ = G` for some compact set `K`. This is
`TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact` for the right action of `Γ`
on `G`, whose orbit space is `G ⧸ Γ`. -/
@[to_additive /-- In a weakly locally compact additive group with separately continuous addition,
`G ⧸ Γ` is compact exactly when `K + Γ = G` for some compact set `K`. This is
`TauCeti.AddAction.compactSpace_orbitRelQuotient_iff_exists_isCompact` for the action of `Γ` on `G`
by right addition, whose orbit space is `G ⧸ Γ`. -/]
theorem compactSpace_iff_exists_isCompact_mul_eq_univ [TopologicalSpace G]
    [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G] :
    CompactSpace (G ⧸ Γ) ↔ ∃ K : Set G, IsCompact K ∧ K * (Γ : Set G) = univ := by
  -- `G ⧸ Γ` is by definition `MulAction.orbitRel.Quotient Γ.op G`, since `QuotientGroup.leftRel Γ`
  -- is by definition `MulAction.orbitRel Γ.op G`.
  refine (TauCeti.MulAction.compactSpace_orbitRelQuotient_iff_exists_isCompact (G := Γ.op)
    (X := G)).trans (exists_congr fun K ↦ and_congr_right fun _ ↦ ?_)
  -- A compact set meets every orbit of `Γ.op` exactly when it meets every left coset of `Γ`.
  rw [← image_mk_eq_univ_iff, eq_univ_iff_forall, mk_surjective.forall]
  refine forall_congr' fun x ↦ ⟨fun ⟨γ, hγ⟩ ↦ ⟨_, hγ, ?_⟩, fun ⟨y, hy, hyx⟩ ↦ ?_⟩
  · rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    exact mk_mul_of_mem x (Subgroup.mem_op.1 γ.property)
  · refine ⟨⟨MulOpposite.op (x⁻¹ * y), Subgroup.mem_op.2 (QuotientGroup.eq.1 hyx.symm)⟩, ?_⟩
    rwa [Subgroup.mk_smul, op_smul_eq_mul, mul_inv_cancel_left]

end QuotientGroup

namespace TauCeti

section TypeTags

/-- Canonical homeomorphism identifying the orbit space of an additive action of `G` on `X` with
the orbit space of the corresponding multiplicative action of `Multiplicative G` on `X`. -/
def AddAction.orbitRelQuotientHomeomorphMultiplicative {G X : Type*} [AddGroup G] [AddAction G X]
    [TopologicalSpace X] :
    _root_.AddAction.orbitRel.Quotient G X ≃ₜ MulAction.orbitRel.Quotient (Multiplicative G) X :=
  Homeomorph.Quotient.congrRight fun _ _ ↦ by
    simp [_root_.AddAction.orbitRel_apply, MulAction.orbitRel_apply]

/-- `AddAction.orbitRelQuotientHomeomorphMultiplicative` preserves orbit representatives. -/
@[simp]
theorem AddAction.orbitRelQuotientHomeomorphMultiplicative_mk {G X : Type*} [AddGroup G]
    [AddAction G X] [TopologicalSpace X] (x : X) :
    AddAction.orbitRelQuotientHomeomorphMultiplicative
      (Quotient.mk (_root_.AddAction.orbitRel G X) x) =
      Quotient.mk (MulAction.orbitRel (Multiplicative G) X) x :=
  (rfl)

/-- The inverse of `AddAction.orbitRelQuotientHomeomorphMultiplicative` preserves orbit
representatives. -/
@[simp]
theorem AddAction.orbitRelQuotientHomeomorphMultiplicative_symm_mk {G X : Type*} [AddGroup G]
    [AddAction G X] [TopologicalSpace X] (x : X) :
    (AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := X)).symm
      (Quotient.mk (MulAction.orbitRel (Multiplicative G) X) x) =
      Quotient.mk (_root_.AddAction.orbitRel G X) x :=
  (rfl)

/-- The underlying equivalence of `AddAction.orbitRelQuotientHomeomorphMultiplicative` is
`AddAction.orbitRelQuotientEquivMultiplicative`. -/
@[simp]
theorem AddAction.orbitRelQuotientHomeomorphMultiplicative_toEquiv {G X : Type*} [AddGroup G]
    [AddAction G X] [TopologicalSpace X] :
    (AddAction.orbitRelQuotientHomeomorphMultiplicative (G := G) (X := X)).toEquiv =
      AddAction.orbitRelQuotientEquivMultiplicative := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x => simp

/-- Canonical homeomorphism identifying the orbit space of a multiplicative action of `G` on `X`
with the orbit space of the corresponding additive action of `Additive G` on `X`. -/
def MulAction.orbitRelQuotientHomeomorphAdditive {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] :
    MulAction.orbitRel.Quotient G X ≃ₜ _root_.AddAction.orbitRel.Quotient (Additive G) X :=
  Homeomorph.Quotient.congrRight fun _ _ ↦ by
    simp [MulAction.orbitRel_apply, _root_.AddAction.orbitRel_apply]

/-- `MulAction.orbitRelQuotientHomeomorphAdditive` preserves orbit representatives. -/
@[simp]
theorem MulAction.orbitRelQuotientHomeomorphAdditive_mk {G X : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] (x : X) :
    MulAction.orbitRelQuotientHomeomorphAdditive (Quotient.mk (MulAction.orbitRel G X) x) =
      Quotient.mk (_root_.AddAction.orbitRel (Additive G) X) x :=
  (rfl)

/-- The inverse of `MulAction.orbitRelQuotientHomeomorphAdditive` preserves orbit
representatives. -/
@[simp]
theorem MulAction.orbitRelQuotientHomeomorphAdditive_symm_mk {G X : Type*} [Group G]
    [MulAction G X] [TopologicalSpace X] (x : X) :
    (MulAction.orbitRelQuotientHomeomorphAdditive (G := G) (X := X)).symm
      (Quotient.mk (_root_.AddAction.orbitRel (Additive G) X) x) =
      Quotient.mk (MulAction.orbitRel G X) x :=
  (rfl)

/-- The underlying equivalence of `MulAction.orbitRelQuotientHomeomorphAdditive` is
`MulAction.orbitRelQuotientEquivAdditive`. -/
@[simp]
theorem MulAction.orbitRelQuotientHomeomorphAdditive_toEquiv {G X : Type*} [Group G]
    [MulAction G X] [TopologicalSpace X] :
    (MulAction.orbitRelQuotientHomeomorphAdditive (G := G) (X := X)).toEquiv =
      MulAction.orbitRelQuotientEquivAdditive := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | h x => simp

end TypeTags

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X]

/-- The orbit map descended to the stabilizer quotient is continuous when the orbit map is. -/
@[fun_prop]
theorem continuous_ofQuotientStabilizer (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (ofQuotientStabilizer G b) := by
  unfold ofQuotientStabilizer
  exact hb.quotient_liftOn' _

end TauCeti

namespace Topology.IsQuotientMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E] {q : E → X}

/-- A quotient map whose fibres are the orbits identifies the orbit space with its target. -/
@[to_additive addOrbitRelQuotientHomeomorph
  /-- A quotient map whose fibres are the additive orbits identifies the additive orbit space
  with its target. -/]
noncomputable def orbitRelQuotientHomeomorph (hq : IsQuotientMap q)
    (h : ∀ e e', q e = q e' ↔ e ∈ MulAction.orbit G e') :
    MulAction.orbitRel.Quotient G E ≃ₜ X :=
  (Homeomorph.Quotient.congrRight
    (r' := Setoid.ker q)
    (fun e e' ↦ MulAction.orbitRel_apply.trans (h e e').symm)).trans
    (hq.homeomorph (f := ⟨q, hq.continuous⟩))

/-- The orbit quotient homeomorphism sends a representative to its image in the target. -/
@[to_additive (attr := simp) addOrbitRelQuotientHomeomorph_mk
  /-- The additive orbit quotient homeomorphism sends a representative to its image in the
  target. -/]
theorem orbitRelQuotientHomeomorph_mk (hq : IsQuotientMap q)
    (h : ∀ e e', q e = q e' ↔ e ∈ MulAction.orbit G e') (e : E) :
    hq.orbitRelQuotientHomeomorph h (Quotient.mk _ e) = q e := by
  simp only [orbitRelQuotientHomeomorph, Homeomorph.trans_apply,
    Homeomorph.Quotient.congrRight_mk, homeomorph_apply (f := ⟨q, hq.continuous⟩),
    ContinuousMap.coe_mk, Setoid.kerLift_mk]

/-- The inverse homeomorphism sends the image of a representative to its orbit. -/
@[to_additive (attr := simp) addOrbitRelQuotientHomeomorph_symm_apply
  /-- The inverse homeomorphism sends the image of a representative to its additive orbit. -/]
theorem orbitRelQuotientHomeomorph_symm_apply (hq : IsQuotientMap q)
    (h : ∀ e e', q e = q e' ↔ e ∈ MulAction.orbit G e') (e : E) :
    (hq.orbitRelQuotientHomeomorph h).symm (q e) = Quotient.mk _ e :=
  (hq.orbitRelQuotientHomeomorph h).symm_apply_eq.2
    (hq.orbitRelQuotientHomeomorph_mk h e).symm

end Topology.IsQuotientMap
