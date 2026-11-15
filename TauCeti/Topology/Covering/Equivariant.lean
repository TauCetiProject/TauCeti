/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Recovering an equivariant space by pulling back its orbit space

Suppose `p : X → Y` is equivariant for actions of `G` and `β : Y → Z` is a quotient
covering by `G`. If `f : X/G → Z` is the descent of `β ∘ p`, then
`x ↦ (p x, [x])` identifies `X` with the literal fibre product `Y ×_Z (X/G)`.
Its topology is the inherited product and subtype topology. The inverse chooses a
representative of an orbit and translates it to the prescribed point of `Y`; freeness
on `Y` makes the result independent of that choice.

Restricting to a single sheet `y : Y` over `z = β y` identifies the fibre `p ⁻¹' {y}`
homeomorphically with the descended fibre `f ⁻¹' {z}`
(`MulActionHom.orbitRelQuotientFiberHomeomorph`), with sheet transition from `g • y` back
to `y` given by the inverse action `g⁻¹ • ·`. Combining the pullback comparison with a local
inverse of `β` at `y` descends any local trivialization of `p` near `y` to a local
trivialization of `f` near `β y` (`MulActionHom.orbitRelQuotientTrivialization`).

This comparison applies to families with nontrivial fibre monodromy: pulling back a
quotient family through the base covering recovers the upstairs family.

## References

* A. Hatcher, *Algebraic Topology*, §1.3 (quotient coverings and their pullbacks).
-/

public section

open Function Set Topology

namespace MulActionHom

variable {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
  (p : X →[G] Y) (β : Y → Z)
  (f : MulAction.orbitRel.Quotient G X → Z)
  (hf : ∀ x, f (Quotient.mk _ x) = β (p x))

/-- The canonical map to the pullback of the descended projection through the base map. -/
def orbitRelQuotientPullback : X → β.Pullback f :=
  fun x ↦ ⟨(p x, Quotient.mk _ x), (hf x).symm⟩

/-- The two coordinates of the canonical comparison are the projection and the orbit class. -/
@[simp] theorem orbitRelQuotientPullback_val (x : X) :
    (p.orbitRelQuotientPullback β f hf x).1 = (p x, Quotient.mk _ x) := (rfl)

/-- A quotient covering of the base makes the canonical comparison bijective. -/
theorem bijective_orbitRelQuotientPullback [TopologicalSpace Y] [TopologicalSpace Z]
    (hβ : IsQuotientCoveringMap β G) : Bijective (p.orbitRelQuotientPullback β f hf) := by
  have := hβ.isCancelSMul
  constructor
  · intro a b hab
    have hp : p a = p b := congrArg (fun w ↦ w.1.1) hab
    obtain ⟨g, hg⟩ := Quotient.exact (congrArg (fun w ↦ w.1.2) hab)
    have hg1 : g = 1 := by
      apply isCancelSMul_iff_eq_one_of_smul_eq.mp ‹IsCancelSMul G Y› g (p b)
      exact (p.map_smul g b).symm.trans ((congrArg p hg).trans hp)
    simpa [hg1] using hg.symm
  · rintro ⟨⟨y, q⟩, hq⟩
    induction q using Quotient.inductionOn with | h x =>
      obtain ⟨g, hg⟩ := hβ.apply_eq_iff_mem_orbit.1 (hq.trans (hf x))
      refine ⟨g • x, Subtype.ext (Prod.ext ?_ ?_)⟩
      · exact (p.map_smul g x).trans hg
      · exact MulAction.orbitRel.Quotient.quotient_smul_eq

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

omit [TopologicalSpace Z] in
/-- The canonical pullback comparison is continuous for the inherited subtype topology. -/
theorem continuous_orbitRelQuotientPullback (hp : Continuous p) :
    Continuous (p.orbitRelQuotientPullback β f hf) :=
  (hp.prodMk continuous_quot_mk).subtype_mk _

variable [ContinuousConstSMul G X]

/-- An equivariant map into the source of a quotient covering pulls back disjoint
neighbourhoods, so its own orbit projection is a quotient covering. -/
theorem isQuotientCoveringMap_orbitRelQuotientMk (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G X)) G where
  __ := isQuotientMap_quot_mk
  apply_eq_iff_mem_orbit := Quotient.eq
  disjoint x := by
    obtain ⟨U, hU, hdisj⟩ := hβ.disjoint (p x)
    refine ⟨p ⁻¹' U, hp.continuousAt.preimage_mem_nhds hU, fun g hg ↦ ?_⟩
    apply hdisj g
    obtain ⟨_, ⟨a, ha, rfl⟩, hga⟩ := hg
    exact ⟨p (g • a), ⟨p a, ha, (p.map_smul g a).symm⟩, hga⟩

/-- Pulling the descended projection back through the base quotient covering recovers
the original equivariant space. No local triviality of `p` is required. -/
noncomputable def orbitRelQuotientPullbackHomeomorph (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) : X ≃ₜ β.Pullback f :=
  ((p.isQuotientCoveringMap_orbitRelQuotientMk β hp hβ).isLocalHomeomorph.of_comp
    (f := p.orbitRelQuotientPullback β f hf) (g := Pullback.snd)
    (hβ.isLocalHomeomorph.pullback_snd hfc)
    (p.continuous_orbitRelQuotientPullback β f hf hp)).toHomeomorphOfBijective
      (p.bijective_orbitRelQuotientPullback β f hf hβ)

/-- The homeomorphism is the canonical comparison on points. -/
@[simp] theorem orbitRelQuotientPullbackHomeomorph_apply (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (x : X) :
    p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc x =
      p.orbitRelQuotientPullback β f hf x := (rfl)

/-- The inverse over the orbit of `x`, at the base point `g • p x`, is `g • x`. -/
@[simp] theorem orbitRelQuotientPullbackHomeomorph_symm_mk (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (g : G) (x : X) :
    (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm
      ⟨(g • p x, Quotient.mk _ x), (hβ.map_smul g).trans (hf x).symm⟩ = g • x := by
  apply (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).injective
  apply Subtype.ext
  simp [p.map_smul]

/-- The inverse has the prescribed projection to the base. -/
@[simp] theorem map_orbitRelQuotientPullbackHomeomorph_symm (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (w : β.Pullback f) :
    p ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm w) = w.fst := by
  exact congrArg (fun v ↦ v.1.1)
    ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).apply_symm_apply w)

/-- The inverse belongs to the prescribed orbit. -/
@[simp] theorem mk_orbitRelQuotientPullbackHomeomorph_symm (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (w : β.Pullback f) :
    Quotient.mk (MulAction.orbitRel G X)
      ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm w) = w.snd := by
  exact congrArg (fun v ↦ v.1.2)
    ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).apply_symm_apply w)

/-- For any sheet `y : Y` over `z : Z` (`β y = z`), the orbit projection restricts to a
homeomorphism between the fibre `p ⁻¹' {y}` upstairs and the fibre `f ⁻¹' {z}` of the descended
projection downstairs. -/
noncomputable def orbitRelQuotientFiberHomeomorph (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y)
    (hy : β y = z := by rfl) : p ⁻¹' {y} ≃ₜ f ⁻¹' {z} where
  toFun u := ⟨Quotient.mk _ u.1, (hf u.1).trans ((congrArg β u.2).trans hy)⟩
  invFun v :=
    ⟨(p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm ⟨(y, v.1), hy.trans v.2.symm⟩,
      p.map_orbitRelQuotientPullbackHomeomorph_symm β f hf hp hβ hfc _⟩
  left_inv u := by
    apply Subtype.ext
    apply (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).injective
    apply Subtype.ext
    rw [Homeomorph.apply_symm_apply]
    exact Prod.ext (u.2 : p u.1 = y).symm rfl
  right_inv v := Subtype.ext (p.mk_orbitRelQuotientPullbackHomeomorph_symm β f hf hp hβ hfc _)
  continuous_toFun := (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).continuous_symm.comp
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)).subtype_mk _

/-- `MulActionHom.orbitRelQuotientFiberHomeomorph` sends `u : p ⁻¹' {y}` to its `G`-orbit
`[u.1]`. -/
@[simp] theorem orbitRelQuotientFiberHomeomorph_coe (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y) (hy : β y = z)
    (u : p ⁻¹' {y}) :
    (p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc y hy u :
      MulAction.orbitRel.Quotient G X) = Quotient.mk _ u.1 :=
  (rfl)

/-- The inverse of `MulActionHom.orbitRelQuotientFiberHomeomorph` evaluates via
`MulActionHom.orbitRelQuotientPullbackHomeomorph`. -/
theorem orbitRelQuotientFiberHomeomorph_symm_coe (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y) (hy : β y = z)
    (v : f ⁻¹' {z}) :
    ((p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc y hy).symm v : X) =
      (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm ⟨(y, v.1), hy.trans v.2.symm⟩ :=
  (rfl)

/-- Pulling an orbit class `[x]` with `p x = g • y` back to the `y`-sheet fibre translates `x` by
the inverse group element `g⁻¹`. -/
theorem orbitRelQuotientFiberHomeomorph_symm_mk_of_smul (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y) (hy : β y = z)
    (g : G) {x : X} (hx : p x = g • y) (hq : f (Quotient.mk _ x) = z) :
    ((p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc y hy).symm ⟨Quotient.mk _ x, hq⟩ : X) =
      g⁻¹ • x := by
  rw [orbitRelQuotientFiberHomeomorph_symm_coe]
  apply (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).injective
  apply Subtype.ext
  rw [Homeomorph.apply_symm_apply, orbitRelQuotientPullbackHomeomorph_apply,
    orbitRelQuotientPullback_val]
  exact Prod.ext ((p.map_smul g⁻¹ x).trans ((congrArg (g⁻¹ • ·) hx).trans (inv_smul_smul g y))).symm
    MulAction.orbitRel.Quotient.quotient_smul_eq.symm

/-- Identifying the `(g • y)`-sheet fibre back with the `y`-sheet fibre through the common
descended fibre `f ⁻¹' {z}` acts by the inverse element `g⁻¹`. -/
@[simp] theorem orbitRelQuotientFiberHomeomorph_symm_apply_smul (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y) (hy : β y = z)
    (g : G) (hgy : β (g • y) = z) (v : p ⁻¹' {g • y}) :
    ((p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc y hy).symm
      (p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc (g • y) hgy v) : X) = g⁻¹ • v.1 :=
  p.orbitRelQuotientFiberHomeomorph_symm_mk_of_smul β f hf hp hβ hfc y hy g v.2 _

/-- Identifying the `y`-sheet fibre with the `(g • y)`-sheet fibre through the common descended
fibre `f ⁻¹' {z}` acts by `g`. -/
@[simp] theorem orbitRelQuotientFiberHomeomorph_smul_symm_apply (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {z : Z} (y : Y) (hy : β y = z)
    (g : G) (hgy : β (g • y) = z) (u : p ⁻¹' {y}) :
    ((p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc (g • y) hgy).symm
      (p.orbitRelQuotientFiberHomeomorph β f hf hp hβ hfc y hy u) : X) = g • u.1 := by
  have hu : p u.1 = g⁻¹ • (g • y) := u.2.trans (inv_smul_smul g y).symm
  exact (p.orbitRelQuotientFiberHomeomorph_symm_mk_of_smul β f hf hp hβ hfc (g • y) hgy g⁻¹ hu
    ((hf u.1).trans ((congrArg β u.2).trans hy))).trans (by rw [inv_inv])

open Classical in
/-- Over the intersection of the source of `hβ.isLocalHomeomorph.localInverseAt y` with the
preimage of `e.baseSet`, a local trivialization `e` of `p` descends along the local inverse of `β`
to a local trivialization of `f`. -/
noncomputable def orbitRelQuotientTrivialization (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {F : Type*} [TopologicalSpace F]
    (e : Bundle.Trivialization F p) (y : Y) : Bundle.Trivialization F f :=
  let s := hβ.isLocalHomeomorph.localInverseAt y
  let Φ := p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc
  let U : Set Z := s.source ∩ s ⁻¹' e.baseSet
  have hUo : IsOpen U := s.continuousOn_toFun.isOpen_inter_preimage s.open_source e.open_baseSet
  { toFun q :=
      (f q,
        if hz : f q ∈ s.source then
          (e (Φ.symm ⟨(s (f q), q), hβ.isLocalHomeomorph.apply_localInverseAt_of_mem hz⟩)).2
        else (e q.out).2)
    invFun w := Quotient.mk (MulAction.orbitRel G X) (e.toOpenPartialHomeomorph.symm (s w.1, w.2))
    source := f ⁻¹' U
    target := U ×ˢ univ
    map_source' _ hq := ⟨hq, mem_univ _⟩
    map_target' w hw := by
      have hwU : w.1 ∈ U := hw.1
      have hx : p (e.toOpenPartialHomeomorph.symm (s w.1, w.2)) = s w.1 :=
        e.proj_symm_apply' hwU.2
      have hfw : f (Quotient.mk _ (e.toOpenPartialHomeomorph.symm (s w.1, w.2))) = w.1 :=
        (hf _).trans ((congrArg β hx).trans
          (hβ.isLocalHomeomorph.apply_localInverseAt_of_mem hwU.1))
      exact Set.mem_preimage.2 (hfw.symm ▸ hwU)
    left_inv' q hq := by
      dsimp only
      rw [dite_eq_left hq.1]
      set x₀ := Φ.symm ⟨(s (f q), q), hβ.isLocalHomeomorph.apply_localInverseAt_of_mem hq.1⟩
      have hx₀ : p x₀ = s (f q) := p.map_orbitRelQuotientPullbackHomeomorph_symm β f hf hp hβ hfc _
      rw [← hx₀, e.symm_apply_mk_proj (e.mem_source.2 (hx₀.symm ▸ hq.2))]
      exact p.mk_orbitRelQuotientPullbackHomeomorph_symm β f hf hp hβ hfc _
    right_inv' w hw := by
      have hwU : w.1 ∈ U := hw.1
      set x := e.toOpenPartialHomeomorph.symm (s w.1, w.2)
      have hx : p x = s w.1 := e.proj_symm_apply' hwU.2
      have hfw : f (Quotient.mk _ x) = w.1 :=
        (hf x).trans ((congrArg β hx).trans
          (hβ.isLocalHomeomorph.apply_localInverseAt_of_mem hwU.1))
      have hΦx : Φ.symm ⟨(s (f (Quotient.mk _ x)), Quotient.mk _ x),
          hβ.isLocalHomeomorph.apply_localInverseAt_of_mem (hfw.symm ▸ hwU.1)⟩ = x := by
        apply Φ.injective
        apply Subtype.ext
        rw [Φ.apply_symm_apply]
        exact Prod.ext ((congrArg s hfw).trans hx.symm) rfl
      refine Prod.ext hfw ?_
      dsimp only
      rw [dite_eq_left (hfw.symm ▸ hwU.1), hΦx]
      exact congrArg Prod.snd (e.apply_symm_apply ((e.mem_target (x := (s w.1, w.2))).2 hwU.2))
    open_source := hUo.preimage hfc
    open_target := hUo.prod isOpen_univ
    continuousOn_toFun := by
      refine continuousOn_iff_continuous_domRestrict.2 ?_
      have hsf : Continuous fun u : f ⁻¹' U ↦ s (f u.1) :=
        s.continuousOn.comp_continuous (hfc.comp continuous_subtype_val) fun u ↦ u.2.1
      let ψ : f ⁻¹' U → X := fun u ↦
        Φ.symm ⟨(s (f u.1), u.1), hβ.isLocalHomeomorph.apply_localInverseAt_of_mem u.2.1⟩
      have hψ : Continuous ψ :=
        Φ.continuous_symm.comp ((hsf.prodMk continuous_subtype_val).subtype_mk _)
      have hψs : ∀ u : f ⁻¹' U, ψ u ∈ e.toOpenPartialHomeomorph.source := fun u ↦ e.mem_source.2 <|
        by
          rw [p.map_orbitRelQuotientPullbackHomeomorph_symm]
          exact u.2.2
      refine ((hfc.comp continuous_subtype_val).prodMk
        (continuous_snd.comp
          (e.toOpenPartialHomeomorph.continuousOn.comp_continuous hψ hψs))).congr fun u ↦ ?_
      refine Prod.ext rfl ?_
      dsimp only [Set.domRestrict_apply, Function.comp_apply, ψ, Bundle.Trivialization.coe_coe]
      rw [dite_eq_left u.2.1]
    continuousOn_invFun := by
      refine continuousOn_iff_continuous_domRestrict.2 ?_
      have hsw : Continuous fun u : U ×ˢ (univ : Set F) ↦ (s u.1.1, u.1.2) :=
        (s.continuousOn.comp_continuous (continuous_fst.comp continuous_subtype_val)
          fun u ↦ u.2.1.1).prodMk (continuous_snd.comp continuous_subtype_val)
      exact continuous_quot_mk.comp
        (e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hsw
          fun u ↦ (e.mem_target (x := (s u.1.1, u.1.2))).2 u.2.1.2)
    baseSet := U
    open_baseSet := hUo
    source_eq := rfl
    target_eq := rfl
    proj_toFun _ _ := rfl }

/-- The base set of `MulActionHom.orbitRelQuotientTrivialization` at a sheet `y`. -/
@[simp] theorem orbitRelQuotientTrivialization_baseSet (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {F : Type*} [TopologicalSpace F]
    (e : Bundle.Trivialization F p) (y : Y) :
    (p.orbitRelQuotientTrivialization β f hf hp hβ hfc e y).baseSet =
      (hβ.isLocalHomeomorph.localInverseAt y).source ∩
        (hβ.isLocalHomeomorph.localInverseAt y) ⁻¹' e.baseSet :=
  (rfl)

/-- If `y ∈ e.baseSet`, then `β y` lies in the base set of
`MulActionHom.orbitRelQuotientTrivialization`. -/
theorem apply_mem_orbitRelQuotientTrivialization_baseSet (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {F : Type*} [TopologicalSpace F]
    {e : Bundle.Trivialization F p} {y : Y} (hy : y ∈ e.baseSet) :
    β y ∈ (p.orbitRelQuotientTrivialization β f hf hp hβ hfc e y).baseSet :=
  ⟨hβ.isLocalHomeomorph.apply_self_mem_localInverseAt_source, by
    simpa [hβ.isLocalHomeomorph.localInverseAt_apply_self] using hy⟩

include hf in
/-- If `p : X →[G] Y` is locally trivial with model fibre `F` and `β : Y → Z` is a quotient
covering by `G`, then the descended projection `f : X/G → Z` is locally trivial with model fibre
`F`. -/
theorem exists_orbitRelQuotientTrivialization (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) {F : Type*} [TopologicalSpace F]
    (htriv : ∀ y, ∃ e : Bundle.Trivialization F p, y ∈ e.baseSet) (z : Z) :
    ∃ e' : Bundle.Trivialization F f, z ∈ e'.baseSet := by
  obtain ⟨y, rfl⟩ := hβ.surjective z
  obtain ⟨e, hy⟩ := htriv y
  exact ⟨p.orbitRelQuotientTrivialization β f hf hp hβ hfc e y,
    p.apply_mem_orbitRelQuotientTrivialization_baseSet β f hf hp hβ hfc hy⟩

end MulActionHom
