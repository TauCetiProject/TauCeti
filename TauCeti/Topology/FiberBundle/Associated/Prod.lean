/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Fibrewise products of associated bundles

For a principal right `G`-bundle `P`, association commutes with products of left `G`-spaces:
`P ×_G (F₁ × F₂)` is canonically homeomorphic to the fibrewise product of `P ×_G F₁` and
`P ×_G F₂`. Both factors must use the same principal frame. This comparison lets equivariant
operations with two inputs, such as Clifford multiplication and invariant pairings, descend to
operations on the associated bundles.

The comparison retains the existing glued carriers and their topologies. In the preferred
principal frame its fibre map is the identity on the pair of coordinates.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§10.7 and 10.9.
-/

public section

noncomputable section

open Bundle MulOpposite Set Topology

namespace TauCeti.AssociatedBundle

variable {G B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {F₁ F₂ : Type*} [TopologicalSpace F₁] [TopologicalSpace F₂]
  [MulAction G F₁] [MulAction G F₂] [ContinuousSMul G F₁] [ContinuousSMul G F₂]

/-- The canonical fibre equivalence for association and products, obtained by representing
both factors in the same principal frame. -/
def prodEquiv (b : B) : AssociatedBundle G P (F₁ × F₂) b ≃
    AssociatedBundle G P F₁ b × AssociatedBundle G P F₂ b :=
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  (Equiv.ofBijective (mk G p) (mk_bijective p)).symm.trans
    ((Equiv.ofBijective (mk G p) (mk_bijective p)).prodCongr
      (Equiv.ofBijective (mk G p) (mk_bijective p)))

/-- A pair represented in one principal frame is sent to its two associated classes. -/
@[simp]
theorem prodEquiv_mk {b : B} (p : P b) (v : F₁) (w : F₂) :
    prodEquiv b (mk G p (v, w)) = (mk G p v, mk G p w) := by
  let q := (FiberBundle.homeomorphAt G P b).symm 1
  have hpair : mk G p (v, w) =
      mk G q (PrincipalBundle.division G q p • v, PrincipalBundle.division G q p • w) := by
    rw [← Prod.smul_mk, ← mk_smul, PrincipalBundle.smul_division]
  have h₁ : mk G p v = mk G q (PrincipalBundle.division G q p • v) := by
    rw [← mk_smul, PrincipalBundle.smul_division]
  have h₂ : mk G p w = mk G q (PrincipalBundle.division G q p • w) := by
    rw [← mk_smul, PrincipalBundle.smul_division]
  rw [hpair, h₁, h₂]
  exact congrArg (fun z : F₁ × F₂ ↦ (mk G q z.1, mk G q z.2))
    ((Equiv.ofBijective (mk G q) (mk_bijective q)).symm_apply_apply _)

/-- The inverse product comparison pairs two classes represented in the same frame. -/
@[simp]
theorem prodEquiv_symm_mk {b : B} (p : P b) (v : F₁) (w : F₂) :
    (prodEquiv b).symm (mk G p v, mk G p w) = mk G p (v, w) := by
  rw [Equiv.symm_apply_eq, prodEquiv_mk]

/-- The product comparison is the identity on the two coordinates in every principal chart. -/
theorem trivializationAt_prodEquiv {b b' : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : AssociatedBundle G P (F₁ × F₂) b) :
    ((trivializationAt F₁ (AssociatedBundle G P F₁) b' ⟨b, (prodEquiv b v).1⟩).2,
      (trivializationAt F₂ (AssociatedBundle G P F₂) b' ⟨b, (prodEquiv b v).2⟩).2) =
      (trivializationAt (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂)) b' ⟨b, v⟩).2 := by
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨⟨v, w⟩, rfl⟩ := (mk_bijective (F := F₁ × F₂) p).surjective v
  simp only [prodEquiv_mk, trivializationAt_mk_snd hb, Prod.smul_mk]

/-- Continuity of a family in the associated product is equivalent to continuity of its two
associated components in the native fibrewise-product topology. -/
theorem continuousWithinAt_prodEquiv_iff
    {X : Type*} [TopologicalSpace X] {f : X → B}
    {v : ∀ x, AssociatedBundle G P (F₁ × F₂) (f x)} {s : Set X} {x₀ : X} :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' (F₁ × F₂) (f x) (v x)) s x₀ ↔
      ContinuousWithinAt (fun x ↦ (⟨f x, prodEquiv (f x) (v x)⟩ :
        TotalSpace (F₁ × F₂) (AssociatedBundle G P F₁ ×ᵇ AssociatedBundle G P F₂))) s x₀ := by
  let d := FiberBundle.Prod.isInducing_diag F₁ (AssociatedBundle G P F₁)
    F₂ (AssociatedBundle G P F₂)
  rw [d.continuousWithinAt_iff, continuousWithinAt_prod_iff]
  simp only [Function.comp_def]
  rw [FiberBundle.continuousWithinAt_totalSpace, FiberBundle.continuousWithinAt_totalSpace,
    FiberBundle.continuousWithinAt_totalSpace]
  have hcoord (hf : ContinuousWithinAt f s x₀) :
      (fun x ↦
        ((trivializationAt F₁ (AssociatedBundle G P F₁) (f x₀)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩).2,
        (trivializationAt F₂ (AssociatedBundle G P F₂) (f x₀)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩).2)) =ᶠ[𝓝[s] x₀]
      (fun x ↦ (trivializationAt (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        (f x₀) ⟨f x, v x⟩).2) := by
    filter_upwards [hf ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt G P (f x₀)))] with x hx
    exact trivializationAt_prodEquiv hx (v x)
  have h₀ := trivializationAt_prodEquiv (mem_baseSet_trivializationAt G P (f x₀)) (v x₀)
  constructor
  · rintro ⟨hf, hv⟩
    have h := hv.congr_of_eventuallyEq (hcoord hf) h₀
    exact ⟨⟨hf, h.fst⟩, ⟨hf, h.snd⟩⟩
  · rintro ⟨⟨hf, hv⟩, ⟨_, hw⟩⟩
    exact ⟨hf, (hv.prodMk hw).congr_of_eventuallyEq (hcoord hf).symm h₀.symm⟩

variable (G P F₁ F₂) in
/-- Association commutes with fibrewise products, on the existing total-space topologies. -/
def prodHomeomorph : TotalSpace (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂)) ≃ₜ
    TotalSpace (F₁ × F₂) (AssociatedBundle G P F₁ ×ᵇ AssociatedBundle G P F₂) where
  toFun v := ⟨v.proj, prodEquiv v.proj v.2⟩
  invFun v := ⟨v.proj, (prodEquiv v.proj).symm v.2⟩
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := continuous_iff_continuousAt.mpr fun v ↦ by
    exact (continuousWithinAt_univ _ _).mp
      (continuousWithinAt_prodEquiv_iff.mp continuousAt_id.continuousWithinAt)
  continuous_invFun := continuous_iff_continuousAt.mpr fun v ↦ by
    apply (continuousWithinAt_univ _ _).mp
    apply continuousWithinAt_prodEquiv_iff.mpr
    simp only [Equiv.apply_symm_apply, TotalSpace.eta]
    exact continuousWithinAt_id

/-- The product homeomorphism preserves the base point. -/
@[simp]
theorem prodHomeomorph_proj
    (v : TotalSpace (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))) :
    (prodHomeomorph G P F₁ F₂ v).proj = v.proj := (rfl)

/-- The inverse product homeomorphism preserves the base point. -/
@[simp]
theorem prodHomeomorph_symm_proj
    (v : TotalSpace (F₁ × F₂) (AssociatedBundle G P F₁ ×ᵇ AssociatedBundle G P F₂)) :
    ((prodHomeomorph G P F₁ F₂).symm v).proj = v.proj := (rfl)

/-- The product homeomorphism acts fibrewise by `prodEquiv`. -/
@[simp]
theorem prodHomeomorph_apply {b : B} (v : AssociatedBundle G P (F₁ × F₂) b) :
    prodHomeomorph G P F₁ F₂ ⟨b, v⟩ = ⟨b, prodEquiv b v⟩ := (rfl)

/-- The inverse product homeomorphism acts by the inverse fibre equivalence. -/
@[simp]
theorem prodHomeomorph_symm_apply {b : B}
    (v : AssociatedBundle G P F₁ b × AssociatedBundle G P F₂ b) :
    (prodHomeomorph G P F₁ F₂).symm ⟨b, v⟩ = ⟨b, (prodEquiv b).symm v⟩ := (rfl)

end TauCeti.AssociatedBundle
