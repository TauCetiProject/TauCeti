/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# Sections of associated bundles

A section of `P ×_G F` is equivalent to a function on the principal total space satisfying
`u(p • g) = g⁻¹ • u(p)`. The correspondence is characterized by `s(b) = [p,u(p)]` for
**every** frame `p` over `b`, so it does not depend on a choice of local section.
It restricts to continuous sections and continuous equivariant functions. This dictionary is
used to describe associated tensor fields and, subsequently, their covariant derivatives.

The fibre may be any space with a continuous group action; vector-space, finite-rank and
nonempty-base assumptions are unnecessary.

A continuous global section `s` of the principal bundle trivializes every associated bundle:
`(b, v) ↦ [s b, v]` is a homeomorphism `B × F ≃ₜ P ×_G F`
(`TauCeti.AssociatedBundle.prodHomeomorphOfSection`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §10.12 (sections of associated bundles).
-/

public section

open Bundle MulOpposite Set Topology

namespace TauCeti.AssociatedBundle

variable {G B F : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]

/-- The function of frames representing a section, characterized by
`mk G p (sectionFunction s ⟨b,p⟩) = s b`. -/
noncomputable def sectionFunction (s : ∀ b, AssociatedBundle G P F b) (p : TotalSpace G P) : F :=
  (Equiv.ofBijective (mk G p.2) (mk_bijective p.2)).symm (s p.proj)

/-- Reconstruct a section in any frame, not just a preferred local frame. -/
@[simp]
theorem mk_sectionFunction (s : ∀ b, AssociatedBundle G P F b) {b : B} (p : P b) :
    mk G p (sectionFunction s ⟨b, p⟩) = s b :=
  (Equiv.ofBijective (mk G p) (mk_bijective p)).apply_symm_apply _

/-- A value represents a section in a frame exactly when it reconstructs that section. -/
theorem sectionFunction_eq_iff (s : ∀ b, AssociatedBundle G P F b) {b : B} (p : P b)
    (v : F) : sectionFunction s ⟨b, p⟩ = v ↔ mk G p v = s b := by
  rw [← (mk_bijective (G := G) (F := F) p).1.eq_iff, mk_sectionFunction, eq_comm]

/-- A section constructed in a family of frames has the prescribed representing values. -/
@[simp]
theorem sectionFunction_mk (p : ∀ b, P b) (v : B → F) (b : B) :
    sectionFunction (fun b ↦ mk G (p b) (v b)) ⟨b, p b⟩ = v b :=
  (sectionFunction_eq_iff _ _ _).2 rfl

/-- Changing frame acts by the inverse group element on the representing function. -/
@[simp]
theorem sectionFunction_smul (s : ∀ b, AssociatedBundle G P F b) {b : B} (p : P b) (g : G) :
    sectionFunction s ⟨b, op g • p⟩ = g⁻¹ • sectionFunction s ⟨b, p⟩ := by
  apply (mk_bijective (G := G) (F := F) (op g • p)).1
  simp only [mk_sectionFunction, mk_smul, smul_inv_smul]

/-- The representing function in a local chart is the section coordinate acted on by the
inverse principal coordinate. -/
theorem sectionFunction_eq_inv_smul (s : ∀ b, AssociatedBundle G P F b) {b₀ b : B}
    (hb : b ∈ (trivializationAt G P b₀).baseSet) (p : P b) :
    sectionFunction s ⟨b, p⟩ = (trivializationAt G P b₀ ⟨b, p⟩).2⁻¹ •
      (trivializationAt F (AssociatedBundle G P F) b₀ ⟨b, s b⟩).2 := by
  rw [eq_inv_smul_iff, ← trivializationAt_mk_snd hb, mk_sectionFunction]

/-- Sections correspond to inverse-equivariant functions on the principal total space. -/
noncomputable def sectionEquiv :
    (∀ b, AssociatedBundle G P F b) ≃
      {u : TotalSpace G P → F // ∀ (b : B) (p : P b) (g : G),
        u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩} where
  toFun s := ⟨sectionFunction s, fun _ p g ↦ sectionFunction_smul s p g⟩
  invFun u b := mk G ((FiberBundle.homeomorphAt G P b).symm 1)
    (u.1 ⟨b, (FiberBundle.homeomorphAt G P b).symm 1⟩)
  left_inv s := by
    funext b
    exact mk_sectionFunction s _
  right_inv u := by
    apply Subtype.ext
    funext ⟨b, p⟩
    apply (mk_bijective (G := G) (F := F) p).1
    rw [mk_sectionFunction]
    set q := (FiberBundle.homeomorphAt G P b).symm 1
    have h := u.2 b q (PrincipalBundle.division G q p)
    rw [PrincipalBundle.smul_division] at h
    rw [h]
    simpa only [PrincipalBundle.smul_division] using
      (mk_smul_inv_smul q (PrincipalBundle.division G q p) (u.1 ⟨b, q⟩)).symm

/-- The forward section correspondence is the representing function. -/
@[simp]
theorem sectionEquiv_apply (s : ∀ b, AssociatedBundle G P F b) :
    (sectionEquiv s).1 = sectionFunction s :=
  (rfl)

/-- The representing function of the inverse correspondence is the original function. -/
@[simp]
theorem sectionFunction_sectionEquiv_symm
    (u : {u : TotalSpace G P → F // ∀ (b : B) (p : P b) (g : G),
      u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩}) :
    sectionFunction (sectionEquiv.symm u) = u.1 :=
  congrArg Subtype.val (sectionEquiv.apply_symm_apply u)

/-- The inverse section correspondence can be evaluated using any frame. -/
theorem sectionEquiv_symm_apply
    (u : {u : TotalSpace G P → F // ∀ (b : B) (p : P b) (g : G),
      u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩}) {b : B} (p : P b) :
    sectionEquiv.symm u b = mk G p (u.1 ⟨b, p⟩) := by
  rw [← mk_sectionFunction (sectionEquiv.symm u) p]
  exact congrArg (mk G p) (congrFun (congrArg Subtype.val (sectionEquiv.apply_symm_apply u)) ⟨b, p⟩)

/-- A section is determined by its representing function. -/
theorem sectionFunction_injective :
    Function.Injective (sectionFunction (G := G) (P := P) (F := F)) := by
  intro s t h
  apply sectionEquiv.injective
  exact Subtype.ext h

variable [ContinuousInv G]

/-- A continuous section has a continuous representing function on frames. -/
theorem continuous_sectionFunction (s : ∀ b, AssociatedBundle G P F b)
    (hs : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F (AssociatedBundle G P F))) :
    Continuous (sectionFunction s) := by
  apply continuous_iff_continuousAt.2
  intro p
  have hb := mem_baseSet_trivializationAt G P p.proj
  have hπ := FiberBundle.continuous_proj G P
  have hp := (trivializationAt G P p.proj).continuousAt
    ((trivializationAt G P p.proj).mem_source.2 hb)
  have hs' := ((trivializationAt F (AssociatedBundle G P F) p.proj).continuousAt
    ((trivializationAt F (AssociatedBundle G P F) p.proj).mem_source.2
      (by simpa using hb))).comp (hs.continuousAt.comp hπ.continuousAt)
  refine (hp.snd.inv.smul hs'.snd).congr_of_eventuallyEq ?_
  filter_upwards [hπ.continuousAt ((trivializationAt G P p.proj).open_baseSet.mem_nhds hb)]
    with q hq
  exact sectionFunction_eq_inv_smul s hq q.2

/-- Continuity of a section is equivalent to continuity of its representing function. -/
theorem continuous_sectionFunction_iff (s : ∀ b, AssociatedBundle G P F b) :
    Continuous (sectionFunction s) ↔
      Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F (AssociatedBundle G P F)) := by
  refine ⟨fun hu ↦ ?_, continuous_sectionFunction s⟩
  apply (FiberBundle.isQuotientMap_proj (F := G) (E := P)).continuous_iff.2
  exact (continuous_id.totalSpaceMk_associatedBundleMk hu).congr
    fun ⟨b, p⟩ ↦ congrArg (TotalSpace.mk b) (mk_sectionFunction s p)

/-- The section correspondence restricts to continuous sections and continuous
inverse-equivariant functions. -/
noncomputable def continuousSectionEquiv :
    {s : ∀ b, AssociatedBundle G P F b //
      Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F (AssociatedBundle G P F))} ≃
    {u : C(TotalSpace G P, F) // ∀ (b : B) (p : P b) (g : G),
      u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩} where
  toFun s := ⟨⟨sectionFunction s.1, continuous_sectionFunction s.1 s.2⟩,
    fun _ p g ↦ sectionFunction_smul s.1 p g⟩
  invFun u := ⟨sectionEquiv.symm ⟨u.1, u.2⟩, by
    apply (continuous_sectionFunction_iff _).1
    simpa only [sectionFunction_sectionEquiv_symm] using u.1.continuous⟩
  left_inv s := Subtype.ext (sectionEquiv.symm_apply_apply s.1)
  right_inv u := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact congrFun (congrArg Subtype.val (sectionEquiv.apply_symm_apply ⟨u.1, u.2⟩))

/-- The continuous correspondence has the same underlying representing function. -/
@[simp]
theorem continuousSectionEquiv_apply
    (s : {s : ∀ b, AssociatedBundle G P F b //
      Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F (AssociatedBundle G P F))})
    (p : TotalSpace G P) :
    (continuousSectionEquiv s).1 p = sectionFunction s.1 p :=
  (rfl)

/-- The continuous inverse correspondence has the same underlying section as the raw one. -/
@[simp]
theorem continuousSectionEquiv_symm_val
    (u : {u : C(TotalSpace G P, F) // ∀ (b : B) (p : P b) (g : G),
      u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩}) :
    (continuousSectionEquiv.symm u).1 = sectionEquiv.symm ⟨u.1, u.2⟩ :=
  (rfl)

/-- Evaluate the continuous inverse correspondence in any frame. -/
theorem continuousSectionEquiv_symm_apply
    (u : {u : C(TotalSpace G P, F) // ∀ (b : B) (p : P b) (g : G),
      u ⟨b, op g • p⟩ = g⁻¹ • u ⟨b, p⟩}) {b : B} (p : P b) :
    (continuousSectionEquiv.symm u).1 b = mk G p (u.1 ⟨b, p⟩) :=
  sectionEquiv_symm_apply ⟨u.1, u.2⟩ p

/-! ### Global sections of the principal bundle -/

/-- **A global section of the principal bundle trivializes its associated bundles.** For a
continuous section `s` of `P`, the map `(b, v) ↦ [s b, v]` is a homeomorphism from `B × F` onto
the total space of the associated bundle. -/
noncomputable def prodHomeomorphOfSection (s : ∀ b, P b)
    (hs : Continuous fun b ↦ TotalSpace.mk' G b (s b)) :
    B × F ≃ₜ TotalSpace F (AssociatedBundle G P F) where
  toFun x := ⟨x.1, mk G (s x.1) x.2⟩
  invFun y := (y.proj, (Equiv.ofBijective _ (mk_bijective (F := F) (s y.proj))).symm y.2)
  left_inv x := Prod.ext rfl (Equiv.ofBijective_symm_apply_apply _ _ x.2)
  right_inv y := congrArg (TotalSpace.mk y.proj) (Equiv.ofBijective_apply_symm_apply _ _ y.2)
  continuous_toFun := (hs.comp continuous_fst).totalSpaceMk_associatedBundleMk continuous_snd
  continuous_invFun := by
    have hπ := FiberBundle.continuous_proj F (AssociatedBundle G P F)
    refine hπ.prodMk (continuous_iff_continuousAt.2 fun y₀ ↦ ?_)
    set e := trivializationAt G P y₀.proj
    set eA := trivializationAt F (AssociatedBundle G P F) y₀.proj
    have hb₀ := mem_baseSet_trivializationAt G P y₀.proj
    -- Near `y₀`, the representative of `y` in the frame `s y.proj` is `g⁻¹ • (eA y).2`, where
    -- `g` is the coordinate of `s y.proj` in the chart `e`.
    have hg : ContinuousAt (fun y : TotalSpace F (AssociatedBundle G P F) ↦
        (e ⟨y.proj, s y.proj⟩).2) y₀ :=
      continuous_snd.continuousAt.comp
        ((e.continuousAt (e.mem_source.2 hb₀)).comp (hs.comp hπ).continuousAt)
    have hA : ContinuousAt (fun y ↦ (eA y).2) y₀ :=
      continuous_snd.continuousAt.comp
        (eA.continuousAt (eA.mem_source.2 (by simpa [eA] using hb₀)))
    refine (hg.inv.smul hA).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt (e.open_baseSet.mem_nhds hb₀)] with y hy
    obtain ⟨b, w⟩ := y
    obtain ⟨v, rfl⟩ := (mk_bijective (F := F) (s b)).2 w
    change (Equiv.ofBijective _ _).symm (mk G (s b) v) =
      (e ⟨b, s b⟩).2⁻¹ • (eA ⟨b, mk G (s b) v⟩).2
    rw [Equiv.ofBijective_symm_apply_apply, trivializationAt_mk_snd hy, inv_smul_smul]

/-- The trivialization by a global section sends `(b, v)` to `[s b, v]`. -/
@[simp]
theorem prodHomeomorphOfSection_apply (s : ∀ b, P b)
    (hs : Continuous fun b ↦ TotalSpace.mk' G b (s b)) (x : B × F) :
    prodHomeomorphOfSection s hs x = ⟨x.1, mk G (s x.1) x.2⟩ :=
  (rfl)

/-- The inverse of the trivialization by a global section sends `[s b, v]` to `(b, v)`. -/
@[simp]
theorem prodHomeomorphOfSection_symm_mk (s : ∀ b, P b)
    (hs : Continuous fun b ↦ TotalSpace.mk' G b (s b)) (b : B) (v : F) :
    (prodHomeomorphOfSection s hs).symm ⟨b, mk G (s b) v⟩ = (b, v) :=
  (prodHomeomorphOfSection s hs).symm_apply_apply (b, v)

/-- The trivialization by a global section preserves the base point. -/
@[simp]
theorem fst_prodHomeomorphOfSection_symm (s : ∀ b, P b)
    (hs : Continuous fun b ↦ TotalSpace.mk' G b (s b)) (y : TotalSpace F (AssociatedBundle G P F)) :
    ((prodHomeomorphOfSection s hs).symm y).1 = y.proj :=
  (rfl)

end TauCeti.AssociatedBundle
