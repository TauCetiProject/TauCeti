/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Type-tag equivalences on `AddUCB` and `UCB`

The Banach algebra `TauCeti.AddUCB A` of bounded functions on a topological additive group `A`
that are uniformly continuous under small left addition, together with its left and right
translations `TauCeti.AddUCB.leftTranslation`, `TauCeti.AddUCB.rightTranslation`, and pullback
`TauCeti.AddUCB.compRightAlgHom`, lives in `TauCeti.Topology.Algebra.Group.UCB.Basic`,
`Translation`, and `CompRight`.

This file supplies the order-preserving isometric `ℝ`-algebra equivalences identifying `AddUCB A`
with `TauCeti.UCB (Multiplicative A)` and `TauCeti.UCB G` with `AddUCB (Additive G)`, intertwining
additive and multiplicative left and right translations.

## Main definitions

* `TauCeti.AddUCB.equivMultiplicative`: the unital algebra isomorphism
  `AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A)`.
* `TauCeti.AddUCB.linearIsometryEquivMultiplicative`: the linear isometry equivalence
  `AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A)`.
* `TauCeti.UCB.equivAdditive`: the unital algebra isomorphism `UCB G ≃ₐ[ℝ] AddUCB (Additive G)`.
* `TauCeti.UCB.linearIsometryEquivAdditive`: the linear isometry equivalence
  `UCB G ≃ₗᵢ[ℝ] AddUCB (Additive G)`.

## Main results

* `TauCeti.mem_addUcb_iff_compContinuous_mem_ucb`,
  `TauCeti.mem_ucb_iff_compContinuous_mem_addUcb`: membership in `addUcb` and `ucb` corresponds
  under precomposition with `Multiplicative.toAdd` and `Additive.toMul`.
* `TauCeti.AddUCB.equivMultiplicative_leftTranslation`,
  `TauCeti.AddUCB.equivMultiplicative_rightTranslation`,
  `TauCeti.AddUCB.equivMultiplicative_symm_rightTranslation`,
  `TauCeti.UCB.equivAdditive_leftTranslation`,
  `TauCeti.UCB.equivAdditive_rightTranslation`,
  `TauCeti.UCB.equivAdditive_symm_rightTranslation`: the type-tag equivalences intertwine
  additive and multiplicative left and right translations.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and
  Definition G.1.4.
-/

public section

noncomputable section

open Filter Topology Multiplicative Additive
open scoped BoundedContinuousFunction

namespace TauCeti

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- `f ∈ addUcb A` if and only if its transport to `Multiplicative A` lies in
`ucb (Multiplicative A)`. -/
theorem mem_addUcb_iff_compContinuous_mem_ucb {f : A →ᵇ ℝ} :
    f ∈ addUcb A ↔
      f.compContinuous ⟨toAdd, continuous_toAdd⟩ ∈ ucb (Multiplicative A) := by
  simp only [mem_addUcb_iff, mem_ucb_iff]
  refine forall₂_congr fun ε _ => ?_
  rw [← ofAdd_zero, nhds_ofAdd, eventually_map]
  exact Filter.eventually_congr (Eventually.of_forall fun u =>
    ⟨fun h x => by simpa using h x.toAdd, fun h x => by simpa using h (ofAdd x)⟩)

/-- `f ∈ ucb (Multiplicative A)` if and only if its transport to `A` lies in `addUcb A`. -/
theorem mem_ucb_multiplicative_iff_compContinuous_mem_addUcb {f : Multiplicative A →ᵇ ℝ} :
    f ∈ ucb (Multiplicative A) ↔
      f.compContinuous ⟨ofAdd, continuous_ofAdd⟩ ∈ addUcb A := by
  rw [mem_addUcb_iff_compContinuous_mem_ucb]
  have hf : (f.compContinuous ⟨ofAdd, continuous_ofAdd⟩).compContinuous ⟨toAdd, continuous_toAdd⟩ =
      f := by ext x; simp
  rw [hf]

/-- `f ∈ ucb G` if and only if its transport to `Additive G` lies in `addUcb (Additive G)`. -/
theorem mem_ucb_iff_compContinuous_mem_addUcb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ f.compContinuous ⟨toMul, continuous_toMul⟩ ∈ addUcb (Additive G) := by
  rw [mem_addUcb_iff_compContinuous_mem_ucb]
  let φ : Multiplicative (Additive G) →ₜ* G := ContinuousMulEquiv.multiplicativeAdditive G
  let ψ : G →ₜ* Multiplicative (Additive G) := (ContinuousMulEquiv.multiplicativeAdditive G).symm
  have hcomp :
      (f.compContinuous ⟨toMul, continuous_toMul⟩).compContinuous ⟨toAdd, continuous_toAdd⟩ =
        f.compContinuous (φ : C(Multiplicative (Additive G), G)) := by
    ext x
    simp [φ]
  rw [hcomp]
  refine ⟨fun hf => compContinuous_mem_ucb hf φ, fun hf => ?_⟩
  have hback :
      (f.compContinuous (φ : C(Multiplicative (Additive G), G))).compContinuous
        (ψ : C(G, Multiplicative (Additive G))) = f := by
    ext x
    simp [φ, ψ]
  rw [← hback]
  exact compContinuous_mem_ucb hf ψ

/-- `f ∈ addUcb (Additive G)` if and only if its transport to `G` lies in `ucb G`. -/
theorem mem_addUcb_additive_iff_compContinuous_mem_ucb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : Additive G →ᵇ ℝ} :
    f ∈ addUcb (Additive G) ↔ f.compContinuous ⟨ofMul, continuous_ofMul⟩ ∈ ucb G := by
  rw [mem_ucb_iff_compContinuous_mem_addUcb]
  have hf : (f.compContinuous ⟨ofMul, continuous_ofMul⟩).compContinuous ⟨toMul, continuous_toMul⟩ =
      f := by ext x; simp
  rw [hf]

namespace AddUCB

/-- Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with `UCB (Multiplicative A)`
as a unital ℝ-algebra. -/
def equivMultiplicative : AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A) where
  toFun f := ⟨(f : A →ᵇ ℝ).compContinuous ⟨toAdd, continuous_toAdd⟩,
    mem_addUcb_iff_compContinuous_mem_ucb.1 f.property⟩
  invFun f := ⟨(f : Multiplicative A →ᵇ ℝ).compContinuous ⟨ofAdd, continuous_ofAdd⟩,
    mem_ucb_multiplicative_iff_compContinuous_mem_addUcb.1 f.property⟩
  left_inv _ := ext fun _ => by simp
  right_inv _ := UCB.ext fun _ => by simp
  map_mul' _ _ := UCB.ext fun _ => rfl
  map_add' _ _ := UCB.ext fun _ => rfl
  commutes' _ := UCB.ext fun _ => rfl

@[simp]
theorem equivMultiplicative_apply (f : AddUCB A) (x : Multiplicative A) :
    (equivMultiplicative f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

@[simp]
theorem equivMultiplicative_symm_apply (f : UCB (Multiplicative A)) (x : A) :
    (equivMultiplicative.symm f : A →ᵇ ℝ) x = (f : Multiplicative A →ᵇ ℝ) (ofAdd x) :=
  (rfl)

/-- `equivMultiplicative` preserves and reflects the pointwise order. -/
@[simp]
theorem equivMultiplicative_le_equivMultiplicative_iff {f g : AddUCB A} :
    equivMultiplicative f ≤ equivMultiplicative g ↔ f ≤ g := by
  simp only [UCB.le_def, equivMultiplicative_apply, le_def]
  exact ⟨fun h x => h (ofAdd x), fun h x => h x.toAdd⟩

/-- `equivMultiplicative.symm` preserves and reflects the pointwise order. -/
@[simp]
theorem equivMultiplicative_symm_le_equivMultiplicative_symm_iff
    {f g : UCB (Multiplicative A)} :
    equivMultiplicative.symm f ≤ equivMultiplicative.symm g ↔ f ≤ g := by
  simp only [le_def, equivMultiplicative_symm_apply, UCB.le_def]
  exact ⟨fun h x => h x.toAdd, fun h x => h (ofAdd x)⟩

/-- `equivMultiplicative` preserves the supremum norm. -/
@[simp]
theorem norm_equivMultiplicative (f : AddUCB A) :
    ‖(equivMultiplicative f : Multiplicative A →ᵇ ℝ)‖ = ‖(f : A →ᵇ ℝ)‖ := by
  refine le_antisymm ((f : A →ᵇ ℝ).norm_compContinuous_le ⟨toAdd, continuous_toAdd⟩) ?_
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
    (equivMultiplicative f : Multiplicative A →ᵇ ℝ).norm_coe_le_norm (ofAdd x)

/-- `equivMultiplicative.symm` preserves the supremum norm. -/
@[simp]
theorem norm_equivMultiplicative_symm (f : UCB (Multiplicative A)) :
    ‖(equivMultiplicative.symm f : A →ᵇ ℝ)‖ = ‖(f : Multiplicative A →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_equivMultiplicative (equivMultiplicative.symm f)).symm

variable (A) in
/-- Precomposition with `Multiplicative.toAdd` as a real linear isometry equivalence between
`AddUCB A` and `UCB (Multiplicative A)`. -/
def linearIsometryEquivMultiplicative : AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A) :=
  { equivMultiplicative.toLinearEquiv with norm_map' := norm_equivMultiplicative }

@[simp]
theorem linearIsometryEquivMultiplicative_apply (f : AddUCB A) :
    linearIsometryEquivMultiplicative A f = equivMultiplicative f :=
  (rfl)

@[simp]
theorem linearIsometryEquivMultiplicative_symm_apply (f : UCB (Multiplicative A)) :
    (linearIsometryEquivMultiplicative A).symm f = equivMultiplicative.symm f :=
  (rfl)

/-- `equivMultiplicative` intertwines additive left translation by `a` with multiplicative left
translation by `Multiplicative.ofAdd a`. -/
@[simp]
theorem equivMultiplicative_leftTranslation (a : A) (f : AddUCB A) :
    equivMultiplicative (leftTranslation a f) =
      UCB.leftTranslation (ofAdd a) (equivMultiplicative f) := by
  ext x
  simp

/-- `equivMultiplicative.symm` intertwines multiplicative left translation by `g` with additive left
translation by `g.toAdd`. -/
@[simp]
theorem equivMultiplicative_symm_leftTranslation (g : Multiplicative A)
    (f : UCB (Multiplicative A)) :
    equivMultiplicative.symm (UCB.leftTranslation g f) =
      leftTranslation g.toAdd (equivMultiplicative.symm f) := by
  ext x
  simp

/-- `equivMultiplicative` intertwines additive right translation by `a` with multiplicative right
translation by `Multiplicative.ofAdd a`. -/
@[simp]
theorem equivMultiplicative_rightTranslation (a : A) (f : AddUCB A) :
    equivMultiplicative (rightTranslation a f) =
      UCB.rightTranslation (ofAdd a) (equivMultiplicative f) := by
  ext x
  simp

/-- `equivMultiplicative.symm` intertwines multiplicative right translation by `g` with additive
right translation by `g.toAdd`. -/
@[simp]
theorem equivMultiplicative_symm_rightTranslation (g : Multiplicative A)
    (f : UCB (Multiplicative A)) :
    equivMultiplicative.symm (UCB.rightTranslation g f) =
      rightTranslation g.toAdd (equivMultiplicative.symm f) := by
  ext x
  simp

end AddUCB

namespace UCB

section Additive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposition with `Additive.toMul` identifies `UCB G` with `AddUCB (Additive G)` as a unital
ℝ-algebra. -/
def equivAdditive : UCB G ≃ₐ[ℝ] AddUCB (Additive G) :=
  (AlgEquiv.ofAlgHom
    (compRightAlgHom (ContinuousMulEquiv.multiplicativeAdditive G :
      Multiplicative (Additive G) →ₜ* G))
    (compRightAlgHom ((ContinuousMulEquiv.multiplicativeAdditive G).symm :
      G →ₜ* Multiplicative (Additive G)))
    (by ext f x; simp) (by ext f x; simp)).trans
    (AddUCB.equivMultiplicative (A := Additive G)).symm

@[simp]
theorem equivAdditive_apply (f : UCB G) (x : Additive G) :
    (equivAdditive f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul := by
  simp [equivAdditive]

@[simp]
theorem equivAdditive_symm_apply (f : AddUCB (Additive G)) (x : G) :
    (equivAdditive.symm f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (ofMul x) := by
  simp [equivAdditive]

/-- `equivAdditive` preserves and reflects the pointwise order. -/
@[simp]
theorem equivAdditive_le_equivAdditive_iff {f g : UCB G} :
    equivAdditive f ≤ equivAdditive g ↔ f ≤ g := by
  have hsurj : Function.Surjective
      (ContinuousMulEquiv.multiplicativeAdditive G : Multiplicative (Additive G) →ₜ* G) :=
    (ContinuousMulEquiv.multiplicativeAdditive G).surjective
  simp [equivAdditive, compRightAlgHom_le_compRightAlgHom_iff hsurj]

/-- `equivAdditive.symm` preserves and reflects the pointwise order. -/
@[simp]
theorem equivAdditive_symm_le_equivAdditive_symm_iff {f g : AddUCB (Additive G)} :
    equivAdditive.symm f ≤ equivAdditive.symm g ↔ f ≤ g := by
  have hsurj : Function.Surjective
      ((ContinuousMulEquiv.multiplicativeAdditive G).symm : G →ₜ* Multiplicative (Additive G)) :=
    (ContinuousMulEquiv.multiplicativeAdditive G).symm.surjective
  simp [equivAdditive, compRightAlgHom_le_compRightAlgHom_iff hsurj]

/-- `equivAdditive` preserves the supremum norm. -/
@[simp]
theorem norm_equivAdditive (f : UCB G) :
    ‖(equivAdditive f : Additive G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ := by
  have hsurj : Function.Surjective
      (ContinuousMulEquiv.multiplicativeAdditive G : Multiplicative (Additive G) →ₜ* G) :=
    (ContinuousMulEquiv.multiplicativeAdditive G).surjective
  rw [equivAdditive, AlgEquiv.trans_apply, AlgEquiv.ofAlgHom_apply,
    AddUCB.norm_equivMultiplicative_symm, ← AddSubgroupClass.coe_norm, ← AddSubgroupClass.coe_norm]
  exact norm_compRightAlgHom_apply hsurj f

/-- `equivAdditive.symm` preserves the supremum norm. -/
@[simp]
theorem norm_equivAdditive_symm (f : AddUCB (Additive G)) :
    ‖(equivAdditive.symm f : G →ᵇ ℝ)‖ = ‖(f : Additive G →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_equivAdditive (equivAdditive.symm f)).symm

variable (G) in
/-- Precomposition with `Additive.toMul` as a real linear isometry equivalence between
`UCB G` and `AddUCB (Additive G)`. -/
def linearIsometryEquivAdditive : UCB G ≃ₗᵢ[ℝ] AddUCB (Additive G) :=
  { equivAdditive.toLinearEquiv with norm_map' := norm_equivAdditive }

@[simp]
theorem linearIsometryEquivAdditive_apply (f : UCB G) :
    linearIsometryEquivAdditive G f = equivAdditive f :=
  (rfl)

@[simp]
theorem linearIsometryEquivAdditive_symm_apply (f : AddUCB (Additive G)) :
    (linearIsometryEquivAdditive G).symm f = equivAdditive.symm f :=
  (rfl)

/-- `equivAdditive` intertwines multiplicative left translation by `g` with additive left
translation by `Additive.ofMul g`. -/
@[simp]
theorem equivAdditive_leftTranslation (g : G) (f : UCB G) :
    equivAdditive (leftTranslation g f) = AddUCB.leftTranslation (ofMul g) (equivAdditive f) := by
  ext x
  simp

/-- `equivAdditive.symm` intertwines additive left translation by `a` with multiplicative left
translation by `a.toMul`. -/
@[simp]
theorem equivAdditive_symm_leftTranslation (a : Additive G) (f : AddUCB (Additive G)) :
    equivAdditive.symm (AddUCB.leftTranslation a f) =
      leftTranslation a.toMul (equivAdditive.symm f) := by
  ext x
  simp

/-- `equivAdditive` intertwines multiplicative right translation by `g` with additive right
translation by `Additive.ofMul g`. -/
@[simp]
theorem equivAdditive_rightTranslation (g : G) (f : UCB G) :
    equivAdditive (rightTranslation g f) = AddUCB.rightTranslation (ofMul g) (equivAdditive f) := by
  ext x
  simp

/-- `equivAdditive.symm` intertwines additive right translation by `a` with multiplicative right
translation by `a.toMul`. -/
@[simp]
theorem equivAdditive_symm_rightTranslation (a : Additive G) (f : AddUCB (Additive G)) :
    equivAdditive.symm (AddUCB.rightTranslation a f) =
      rightTranslation a.toMul (equivAdditive.symm f) := by
  ext x
  simp

end Additive

end UCB

end TauCeti
