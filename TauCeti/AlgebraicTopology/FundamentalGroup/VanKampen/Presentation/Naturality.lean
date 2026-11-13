/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Presentation.Cover

/-!
# Naturality of van Kampen cover presentations

A continuous map carrying each member of one based family into a specified member of another,
and the basepoint `x` to a point `y` common to the target members, induces a homomorphism
between the free products of their fundamental groups, built factorwise from
`FundamentalGroup.mapOfEq`. This map preserves the overlap relations and hence descends to the
van Kampen presentation quotients, without cover or connectedness assumptions. Identity and
composition laws make these quotient maps functorial, and they depend only on the restrictions
of the map to the source members.

For neighborhood covers with path-connected triple intersections, the presentation
isomorphisms `TauCeti.vanKampenCoverQuotientEquiv` of
`TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Presentation.Cover`, derived from the
fundamental-groupoid gluing in `TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Cover`,
commute with the induced map of ambient fundamental groups, in both directions. In particular,
a refinement of such covers induces a bijective homomorphism of presentations, independent of
the chosen index assignment, bundled as the isomorphism `TauCeti.vanKampenCoverRefinementEquiv`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.2, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

/-- Two factorizations of the same composite induce the same map on fundamental groups. -/
private lemma mapOfEq_mapOfEq_eq_mapOfEq {A B D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace D] {a : A} {b : B} {d : D} {f : C(A, B)}
    {g : C(B, D)} {k : C(A, D)} (h : g.comp f = k) (hf : f a = b) (hg : g b = d) (hk : k a = d)
    (p : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf p) =
      FundamentalGroup.mapOfEq k hk p := by
  rw [FundamentalGroup.mapOfEq_comp]
  exact FundamentalGroup.mapOfEq_congr h _ _ p

/-- Two factorizations of the same map through different spaces induce the same map on
fundamental groups. -/
private lemma mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq {A B C D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] {a : A} {b : B} {c : C}
    {d : D} {f₁ : C(A, B)} {g₁ : C(B, D)} {f₂ : C(A, C)} {g₂ : C(C, D)}
    (h : g₁.comp f₁ = g₂.comp f₂) (hf₁ : f₁ a = b) (hg₁ : g₁ b = d)
    (hf₂ : f₂ a = c) (hg₂ : g₂ c = d) (p : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq g₁ hg₁ (FundamentalGroup.mapOfEq f₁ hf₁ p) =
      FundamentalGroup.mapOfEq g₂ hg₂ (FundamentalGroup.mapOfEq f₂ hf₂ p) := by
  rw [FundamentalGroup.mapOfEq_comp, FundamentalGroup.mapOfEq_comp]
  exact FundamentalGroup.mapOfEq_congr h _ _ p

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {ι κ η : Type*} {U : ι → Set X} {V : κ → Set Y} {W : η → Set Z}
  {x : X} {y : Y} (hx : ∀ i, x ∈ U i) (f : C(X, Y)) (r : ι → κ)
  (hf : ∀ i, MapsTo f (U i) (V (r i))) (hy : ∀ j, y ∈ V j) (hxy : f x = y)

/-- The free-product map induced by a continuous map sending the basepoint `x` to `y` and an
assignment of target members. -/
def vanKampenCoverFreeMap :
    Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) →*
      Monoid.CoprodI (fun j ↦ FundamentalGroup (V j) ⟨y, hy j⟩) :=
  Monoid.CoprodI.lift fun i ↦ Monoid.CoprodI.of.comp
    (FundamentalGroup.mapOfEq
      ((f.restrictPreimage (V (r i))).comp (ContinuousMap.inclusion (hf i).subset_preimage))
      (Subtype.ext hxy))

/-- On a factor the free-product map is the map of fundamental groups of the restricted map. -/
@[simp]
lemma vanKampenCoverFreeMap_of (i : ι) (a : FundamentalGroup (U i) ⟨x, hx i⟩) :
    vanKampenCoverFreeMap hx f r hf hy hxy (Monoid.CoprodI.of a) =
      Monoid.CoprodI.of (i := r i) (FundamentalGroup.mapOfEq
        ((f.restrictPreimage (V (r i))).comp (ContinuousMap.inclusion (hf i).subset_preimage))
        (x := ⟨x, hx i⟩) (y := ⟨y, hy (r i)⟩) (Subtype.ext hxy) a) := by
  unfold vanKampenCoverFreeMap
  rw [Monoid.CoprodI.lift_of]
  rfl

/-- The free-product map commutes with the inclusion-induced maps to the ambient groups. -/
@[simp]
lemma vanKampenWideLift_comp_vanKampenCoverFreeMap :
    (vanKampenWideLift V y hy).comp (vanKampenCoverFreeMap hx f r hf hy hxy) =
      (FundamentalGroup.mapOfEq f hxy).comp (vanKampenWideLift U x hx) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply, vanKampenCoverFreeMap_of, vanKampenWideLift_of,
    ← FundamentalGroup.mapOfEq_rfl]
  -- Both sides map the loop into `Y` by the restriction of `f` to `U i`.
  exact mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq (by ext; rfl) _ _ _ _ a

/-- Pointwise form of `vanKampenWideLift_comp_vanKampenCoverFreeMap`. -/
@[simp]
lemma vanKampenWideLift_vanKampenCoverFreeMap
    (a : Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) :
    vanKampenWideLift V y hy (vanKampenCoverFreeMap hx f r hf hy hxy a) =
      FundamentalGroup.mapOfEq f hxy (vanKampenWideLift U x hx a) :=
  DFunLike.congr_fun (vanKampenWideLift_comp_vanKampenCoverFreeMap hx f r hf hy hxy) a

/-- Maps of based families preserve the normal subgroups generated by overlap relations. -/
lemma vanKampenCoverRelations_le_comap_vanKampenCoverFreeMap :
    vanKampenCoverRelations U x hx ≤
      (vanKampenCoverRelations V y hy).comap (vanKampenCoverFreeMap hx f r hf hy hxy) := by
  rw [vanKampenCoverRelations_def]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i, j, a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
  let t : C(↥(U i ∩ U j), ↥(V (r i) ∩ V (r j))) :=
    (f.restrictPreimage (V (r i) ∩ V (r j))).comp
      (ContinuousMap.inclusion fun z hz ↦ ⟨hf i hz.1, hf j hz.2⟩)
  -- Both overlap squares factor the restriction of `f` through `t`. The overlap relators use
  -- the intersection basepoint, which is the member basepoint only definitionally.
  convert mul_inv_mem_vanKampenCoverRelations V y hy (r i) (r j)
    (FundamentalGroup.mapOfEq t (x := ⟨x, hx i, hx j⟩) (y := ⟨y, hy (r i), hy (r j)⟩)
      (Subtype.ext hxy) a) using 3
  · refine (vanKampenCoverFreeMap_of hx f r hf hy hxy i _).trans (congrArg Monoid.CoprodI.of ?_)
    simp only [← FundamentalGroup.mapOfEq_rfl]
    exact mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq (by ext; rfl) _ _ _ _ a
  · refine (vanKampenCoverFreeMap_of hx f r hf hy hxy j _).trans (congrArg Monoid.CoprodI.of ?_)
    simp only [← FundamentalGroup.mapOfEq_rfl]
    exact mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq (by ext; rfl) _ _ _ _ a

/-- The quotient map between van Kampen presentations induced by a map of based families.
Neither family needs to cover, and intersections need not be path connected. -/
def vanKampenCoverQuotientMap :
    (Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩)) ⧸
        vanKampenCoverRelations U x hx →*
      (Monoid.CoprodI (fun j ↦ FundamentalGroup (V j) ⟨y, hy j⟩)) ⧸
        vanKampenCoverRelations V y hy :=
  QuotientGroup.map _ _ (vanKampenCoverFreeMap hx f r hf hy hxy)
    (vanKampenCoverRelations_le_comap_vanKampenCoverFreeMap hx f r hf hy hxy)

/-- On quotient representatives the presentation map is induced by the free-product map. -/
@[simp]
lemma vanKampenCoverQuotientMap_mk
    (a : Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) :
    vanKampenCoverQuotientMap hx f r hf hy hxy (QuotientGroup.mk a) =
      QuotientGroup.mk (vanKampenCoverFreeMap hx f r hf hy hxy a) := by
  simp [vanKampenCoverQuotientMap]

/-- The identity of a based family induces the identity on its free product. -/
@[simp]
lemma vanKampenCoverFreeMap_id (hid : ∀ i, MapsTo (ContinuousMap.id X) (U i) (U (id i)))
    (h : ContinuousMap.id X x = x) :
    vanKampenCoverFreeMap hx (ContinuousMap.id X) id hid hx h = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro a
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.id_apply]
  refine (vanKampenCoverFreeMap_of hx _ _ _ hx h i a).trans (congrArg Monoid.CoprodI.of ?_)
  -- The restriction of the identity to a member is the identity of that member.
  exact (FundamentalGroup.mapOfEq_congr (f₂ := ContinuousMap.id (U i))
    (ContinuousMap.ext fun _ ↦ rfl) _ rfl a).trans (FundamentalGroup.mapOfEq_id _ a)

variable (g : C(Y, Z)) (s : κ → η) (hg : ∀ j, MapsTo g (V j) (W (s j))) {z : Z}
  (hz : ∀ k, z ∈ W k) (hyz : g y = z)

/-- Free-product maps compose according to the maps of spaces and index assignments. -/
@[simp]
lemma vanKampenCoverFreeMap_comp :
    (vanKampenCoverFreeMap hy g s hg hz hyz).comp (vanKampenCoverFreeMap hx f r hf hy hxy) =
      vanKampenCoverFreeMap hx (g.comp f) (s ∘ r)
        (fun i ↦ mapsTo_iff_subset_preimage.2 ((hg (r i)).comp (hf i))) hz
        ((g.comp_apply f x).trans ((congrArg g hxy).trans hyz)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply]
  rw [vanKampenCoverFreeMap_of, vanKampenCoverFreeMap_of]
  refine Eq.trans ?_ (vanKampenCoverFreeMap_of hx (g.comp f) (s ∘ r) _ hz _ i a).symm
  -- Both restricted composites apply `g` after `f`.
  exact congrArg Monoid.CoprodI.of
    (mapOfEq_mapOfEq_eq_mapOfEq (by ext; rfl) _ _ _ a)

/-- Pointwise form of `vanKampenCoverFreeMap_comp`. -/
@[simp]
lemma vanKampenCoverFreeMap_vanKampenCoverFreeMap
    (a : Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) :
    vanKampenCoverFreeMap hy g s hg hz hyz (vanKampenCoverFreeMap hx f r hf hy hxy a) =
      vanKampenCoverFreeMap hx (g.comp f) (s ∘ r)
        (fun i ↦ mapsTo_iff_subset_preimage.2 ((hg (r i)).comp (hf i))) hz
        ((g.comp_apply f x).trans ((congrArg g hxy).trans hyz)) a :=
  DFunLike.congr_fun (vanKampenCoverFreeMap_comp hx f r hf hy hxy g s hg hz hyz) a

/-- The identity of a based family induces the identity on its presentation quotient. -/
@[simp]
lemma vanKampenCoverQuotientMap_id (hid : ∀ i, MapsTo (ContinuousMap.id X) (U i) (U (id i)))
    (h : ContinuousMap.id X x = x) :
    vanKampenCoverQuotientMap hx (ContinuousMap.id X) id hid hx h =
      MonoidHom.id _ := by
  simp only [vanKampenCoverQuotientMap, vanKampenCoverFreeMap_id]
  exact QuotientGroup.map_id _ _

/-- Presentation quotient maps compose according to the maps of spaces and index assignments. -/
@[simp]
lemma vanKampenCoverQuotientMap_comp :
    (vanKampenCoverQuotientMap hy g s hg hz hyz).comp
        (vanKampenCoverQuotientMap hx f r hf hy hxy) =
      vanKampenCoverQuotientMap hx (g.comp f) (s ∘ r)
        (fun i ↦ mapsTo_iff_subset_preimage.2 ((hg (r i)).comp (hf i))) hz
        ((g.comp_apply f x).trans ((congrArg g hxy).trans hyz)) := by
  refine (QuotientGroup.map_comp_map _ _ _ _ _ _ _).trans ?_
  congr 1
  exact vanKampenCoverFreeMap_comp hx f r hf hy hxy g s hg hz hyz

/-- Pointwise form of `vanKampenCoverQuotientMap_comp`. -/
@[simp]
lemma vanKampenCoverQuotientMap_vanKampenCoverQuotientMap
    (a : (Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) ⧸
      vanKampenCoverRelations U x hx) :
    vanKampenCoverQuotientMap hy g s hg hz hyz (vanKampenCoverQuotientMap hx f r hf hy hxy a) =
      vanKampenCoverQuotientMap hx (g.comp f) (s ∘ r)
        (fun i ↦ mapsTo_iff_subset_preimage.2 ((hg (r i)).comp (hf i))) hz
        ((g.comp_apply f x).trans ((congrArg g hxy).trans hyz)) a :=
  DFunLike.congr_fun (vanKampenCoverQuotientMap_comp hx f r hf hy hxy g s hg hz hyz) a

/-- The quotient map is independent of the assignment of target members, and depends only on
the restrictions of the map to the source members, even when the families do not cover and
their intersections are disconnected. -/
lemma vanKampenCoverQuotientMap_eq {f' : C(X, Y)} (hff' : ∀ i, EqOn f f' (U i)) (r' : ι → κ)
    (hf' : ∀ i, MapsTo f' (U i) (V (r' i))) (hxy' : f' x = y) :
    vanKampenCoverQuotientMap hx f r hf hy hxy =
      vanKampenCoverQuotientMap hx f' r' hf' hy hxy' := by
  apply QuotientGroup.monoidHom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, vanKampenCoverQuotientMap_mk,
    vanKampenCoverFreeMap_of]
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [div_eq_mul_inv]
  let t : C(U i, ↥(V (r i) ∩ V (r' i))) :=
    (f.restrictPreimage (V (r i) ∩ V (r' i))).comp
      (ContinuousMap.inclusion fun _ ha ↦ ⟨hf i ha, (hff' i ha).symm ▸ hf' i ha⟩)
  -- Both restrictions of `f` and `f'` to `U i` factor through the target overlap via `t`.
  convert mul_inv_mem_vanKampenCoverRelations V y hy (r i) (r' i)
    (FundamentalGroup.mapOfEq t (x := ⟨x, hx i⟩) (y := ⟨y, hy (r i), hy (r' i)⟩)
      (Subtype.ext hxy) a) using 3
  · rw [← FundamentalGroup.mapOfEq_rfl]
    exact congrArg Monoid.CoprodI.of
      (mapOfEq_mapOfEq_eq_mapOfEq (by ext; rfl) _ _ _ a).symm
  · rw [← FundamentalGroup.mapOfEq_rfl]
    refine congrArg Monoid.CoprodI.of
      (mapOfEq_mapOfEq_eq_mapOfEq ?_ _ _ _ a).symm
    exact ContinuousMap.ext fun z ↦ Subtype.ext (hff' i z.2)

variable (hU : ∀ z, ∃ i, U i ∈ 𝓝 z)
  (hUt : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
  (hV : ∀ z, ∃ j, V j ∈ 𝓝 z)
  (hVt : ∀ i j k, IsPathConnected (V i ∩ V j ∩ V k))

/-- The van Kampen presentation isomorphisms are natural under maps of based covers. -/
lemma vanKampenCoverQuotientEquiv_naturality :
    (vanKampenCoverQuotientEquiv (hx := hy) hV hVt).toMonoidHom.comp
        (vanKampenCoverQuotientMap hx f r hf hy hxy) =
      (FundamentalGroup.mapOfEq f hxy).comp
        (vanKampenCoverQuotientEquiv (hx := hx) hU hUt).toMonoidHom := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, vanKampenCoverQuotientMap_mk,
    MulEquiv.coe_toMonoidHom, vanKampenCoverQuotientEquiv_mk,
    vanKampenWideLift_vanKampenCoverFreeMap]

/-- Pointwise form of `vanKampenCoverQuotientEquiv_naturality`. -/
lemma vanKampenCoverQuotientEquiv_vanKampenCoverQuotientMap
    (a : (Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) ⧸
      vanKampenCoverRelations U x hx) :
    vanKampenCoverQuotientEquiv (hx := hy) hV hVt (vanKampenCoverQuotientMap hx f r hf hy hxy a) =
      FundamentalGroup.mapOfEq f hxy (vanKampenCoverQuotientEquiv (hx := hx) hU hUt a) :=
  DFunLike.congr_fun (vanKampenCoverQuotientEquiv_naturality hx f r hf hy hxy hU hUt hV hVt) a

/-- The inverse van Kampen presentation isomorphisms are natural under maps of based covers. -/
lemma vanKampenCoverQuotientMap_vanKampenCoverQuotientEquiv_symm (a : FundamentalGroup X x) :
    vanKampenCoverQuotientMap hx f r hf hy hxy
        ((vanKampenCoverQuotientEquiv (hx := hx) hU hUt).symm a) =
      (vanKampenCoverQuotientEquiv (hx := hy) hV hVt).symm (FundamentalGroup.mapOfEq f hxy a) := by
  rw [MulEquiv.eq_symm_apply, vanKampenCoverQuotientEquiv_vanKampenCoverQuotientMap hx f r hf hy
    hxy hU hUt, MulEquiv.apply_symm_apply]

/-- Homomorphism form of `vanKampenCoverQuotientMap_vanKampenCoverQuotientEquiv_symm`. -/
lemma vanKampenCoverQuotientEquiv_symm_naturality :
    (vanKampenCoverQuotientMap hx f r hf hy hxy).comp
        (vanKampenCoverQuotientEquiv (hx := hx) hU hUt).symm.toMonoidHom =
      (vanKampenCoverQuotientEquiv (hx := hy) hV hVt).symm.toMonoidHom.comp
        (FundamentalGroup.mapOfEq f hxy) :=
  MonoidHom.ext (vanKampenCoverQuotientMap_vanKampenCoverQuotientEquiv_symm hx f r hf hy hxy hU
    hUt hV hVt)

include hU hUt in
/-- A refinement of based neighborhood covers with path-connected triple intersections induces
a bijective homomorphism between their van Kampen presentations. The coarser family is
automatically a neighborhood cover. -/
theorem vanKampenCoverQuotientMap_id_bijective
    {V : κ → Set X} (hy : ∀ j, x ∈ V j) (r : ι → κ) (hf : ∀ i, U i ⊆ V (r i))
    (hVt : ∀ i j k, IsPathConnected (V i ∩ V j ∩ V k)) :
    Function.Bijective
      (vanKampenCoverQuotientMap hx (ContinuousMap.id X) r
        (fun i ↦ mapsTo_iff_subset_preimage.2 (hf i)) hy (ContinuousMap.id_apply x)) := by
  have hV : ∀ z, ∃ j, V j ∈ 𝓝 z := fun z ↦
    let ⟨i, hi⟩ := hU z
    ⟨r i, Filter.mem_of_superset hi (hf i)⟩
  -- By naturality for the identity, the map is the composite of the presentation isomorphisms.
  have h : ⇑(vanKampenCoverQuotientMap hx (ContinuousMap.id X) r
      (fun i ↦ mapsTo_iff_subset_preimage.2 (hf i)) hy (ContinuousMap.id_apply x)) =
      (vanKampenCoverQuotientEquiv (hx := hy) hV hVt).symm ∘
        vanKampenCoverQuotientEquiv (hx := hx) hU hUt := by
    ext a
    rw [Function.comp_apply, MulEquiv.eq_symm_apply,
      vanKampenCoverQuotientEquiv_vanKampenCoverQuotientMap, FundamentalGroup.mapOfEq_id]
  rw [h]
  exact (MulEquiv.bijective _).comp (MulEquiv.bijective _)

/-- The isomorphism of van Kampen presentations induced by a refinement of based neighborhood
covers with path-connected triple intersections. -/
def vanKampenCoverRefinementEquiv
    {V : κ → Set X} (hy : ∀ j, x ∈ V j) (r : ι → κ) (hf : ∀ i, U i ⊆ V (r i))
    (hVt : ∀ i j k, IsPathConnected (V i ∩ V j ∩ V k)) :
    (Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) ⧸
        vanKampenCoverRelations U x hx ≃*
      (Monoid.CoprodI fun j ↦ FundamentalGroup (V j) ⟨x, hy j⟩) ⧸
        vanKampenCoverRelations V x hy :=
  MulEquiv.ofBijective _ (vanKampenCoverQuotientMap_id_bijective hx hU hUt hy r hf hVt)

/-- The refinement isomorphism is the presentation map induced by the identity. -/
@[simp]
lemma vanKampenCoverRefinementEquiv_apply
    {V : κ → Set X} (hy : ∀ j, x ∈ V j) (r : ι → κ) (hf : ∀ i, U i ⊆ V (r i))
    (hVt : ∀ i j k, IsPathConnected (V i ∩ V j ∩ V k))
    (a : (Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) ⧸
      vanKampenCoverRelations U x hx) :
    vanKampenCoverRefinementEquiv hx hU hUt hy r hf hVt a =
      vanKampenCoverQuotientMap hx (ContinuousMap.id X) r
        (fun i ↦ mapsTo_iff_subset_preimage.2 (hf i)) hy (ContinuousMap.id_apply x) a := by
  rw [vanKampenCoverRefinementEquiv, MulEquiv.ofBijective_apply]

/-- The refinement isomorphism is the composite of the presentation isomorphisms of the two
covers, so its inverse is the reverse composite. Any proof `hV` that the coarser family is a
neighborhood cover may be used, since one always follows from the refinement. -/
lemma vanKampenCoverRefinementEquiv_eq_trans
    {V : κ → Set X} (hy : ∀ j, x ∈ V j) (r : ι → κ) (hf : ∀ i, U i ⊆ V (r i))
    (hV : ∀ z, ∃ j, V j ∈ 𝓝 z) (hVt : ∀ i j k, IsPathConnected (V i ∩ V j ∩ V k)) :
    vanKampenCoverRefinementEquiv hx hU hUt hy r hf hVt =
      (vanKampenCoverQuotientEquiv (hx := hx) hU hUt).trans
        (vanKampenCoverQuotientEquiv (hx := hy) hV hVt).symm := by
  ext a
  rw [vanKampenCoverRefinementEquiv_apply, MulEquiv.trans_apply, MulEquiv.eq_symm_apply,
    vanKampenCoverQuotientEquiv_vanKampenCoverQuotientMap, FundamentalGroup.mapOfEq_id]

end TauCeti
