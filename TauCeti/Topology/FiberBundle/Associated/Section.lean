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

end TauCeti.AssociatedBundle
