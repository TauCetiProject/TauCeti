/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.RepresentationTheory.Intertwining

/-!
# Intertwining maps between direct sums of representations

For families of representations `ρ i` and `σ i` of a monoid `G`, Mathlib forms the direct-sum
representations `Representation.directSum ρ` and `Representation.directSum σ`. This file makes
the direct sum functorial in intertwining maps, reindexes a direct sum of representations along an
equivalence of index types, and distributes left tensor products over direct sums. It also includes
each summand into the direct sum, and transports a direct-sum decomposition along an equivalence to
an internal decomposition into subrepresentations. None of these constructions involves the group
algebra, so the scalars only need to form a semiring.

## Main definitions

* `Representation.IntertwiningMap.directSumMap`: the direct sum of a family of intertwining maps,
  compatible with identities and composition.
* `Representation.directSumEquivCongrLeft`: reindexing a direct sum of representations along an
  equivalence of index types; its underlying linear equivalence is `DirectSum.lequivCongrLeft`.
* `Representation.tprodDirectSumEquiv`: distributing `Representation.tprod` on the left over
  `Representation.directSum`.
* `Representation.IntertwiningMap.lof`: the inclusion of a summand into a direct sum of
  representations; its underlying linear map is `DirectSum.lof`.

## Main results

* `Representation.Equiv.exists_isInternal`: a representation equivalent to a direct sum of
  representations `σ i` is the internal direct sum of subrepresentations equivalent to the `σ i`.
-/

public section

open DirectSum
open scoped TensorProduct

namespace Representation

variable {k G ι : Type*} [Semiring k] [Monoid G]
  {V W : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]

section Naturality

variable {ρ : ∀ i, Representation k G (V i)} {σ : ∀ i, Representation k G (W i)}

/-- **The direct sum of a family of intertwining maps**, acting summand by summand. -/
noncomputable def IntertwiningMap.directSumMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    IntertwiningMap (directSum ρ) (directSum σ) where
  toLinearMap := DirectSum.lmap fun i ↦ (f i).toLinearMap
  isIntertwining' g := by
    ext x i
    simp [directSum_apply, (f i).isIntertwining]

@[simp]
theorem IntertwiningMap.directSumMap_toLinearMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    (directSumMap f).toLinearMap = DirectSum.lmap fun i ↦ (f i).toLinearMap :=
  (rfl)

@[simp]
theorem IntertwiningMap.directSumMap_apply (f : ∀ i, IntertwiningMap (ρ i) (σ i))
    (x : ⨁ i, V i) (i : ι) : directSumMap f x i = f i (x i) :=
  (rfl)

/-- The direct sum of intertwining maps sends `v` in summand `i` to `f i v` in summand `i`. -/
@[simp]
theorem IntertwiningMap.directSumMap_lof [DecidableEq ι] (f : ∀ i, IntertwiningMap (ρ i) (σ i))
    (i : ι) (v : V i) : directSumMap f (lof k ι V i v) = lof k ι W i (f i v) :=
  DirectSum.lmap_lof _ i v

/-- The direct sum of identity maps is the identity. -/
@[simp]
theorem IntertwiningMap.directSumMap_id :
    directSumMap (fun i ↦ IntertwiningMap.id (ρ i)) = IntertwiningMap.id (directSum ρ) := by
  ext x i
  simp

/-- The direct sum of composites is the composite of the direct sums. -/
@[simp]
theorem IntertwiningMap.directSumMap_comp {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] {τ : ∀ i, Representation k G (U i)}
    (f : ∀ i, IntertwiningMap (σ i) (τ i)) (g : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    directSumMap (fun i ↦ (f i).comp (g i)) = (directSumMap f).comp (directSumMap g) := by
  ext x i
  simp

end Naturality

section Reindex

variable (ρ : ∀ i, Representation k G (V i)) {κ : Type*} (h : ι ≃ κ)

/-- **Reindexing a direct sum of representations** along an equivalence `h : ι ≃ κ`: the
summand of index `j` of the reindexed family is the summand of index `h.symm j` of the original
one. The underlying linear equivalence is `DirectSum.lequivCongrLeft`. -/
noncomputable def directSumEquivCongrLeft :
    (directSum ρ).Equiv (directSum fun j ↦ ρ (h.symm j)) :=
  .mk (DirectSum.lequivCongrLeft k h) fun g ↦ by
    ext x j
    simp [directSum_apply, DirectSum.lequivCongrLeft_apply]

@[simp]
theorem directSumEquivCongrLeft_toLinearEquiv :
    (directSumEquivCongrLeft ρ h).toLinearEquiv = DirectSum.lequivCongrLeft k h :=
  (rfl)

@[simp]
theorem directSumEquivCongrLeft_apply (x : ⨁ i, V i) (j : κ) :
    directSumEquivCongrLeft ρ h x j = x (h.symm j) :=
  (rfl)

/-- The inverse reindexing reads the summand of index `h.symm j` off the summand of index `j`. -/
@[simp]
theorem directSumEquivCongrLeft_symm_apply (y : ⨁ j, V (h.symm j)) (j : κ) :
    (directSumEquivCongrLeft ρ h).symm y (h.symm j) = y j := by
  rw [← directSumEquivCongrLeft_apply ρ h, Representation.Equiv.apply_symm_apply]

/-- Reindexing sends `v` in summand `h.symm j` to `v` in summand `j`. -/
@[simp]
theorem directSumEquivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] (j : κ) (v : V (h.symm j)) :
    directSumEquivCongrLeft ρ h (lof k ι V (h.symm j) v) =
      lof k κ (fun j ↦ V (h.symm j)) j v :=
  DirectSum.lequivCongrLeft_lof _ rfl _ _ rfl

/-- The inverse reindexing sends `v` in summand `j` to `v` in summand `h.symm j`. -/
@[simp]
theorem directSumEquivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] (j : κ)
    (v : V (h.symm j)) :
    (directSumEquivCongrLeft ρ h).symm (lof k κ (fun j ↦ V (h.symm j)) j v) =
      lof k ι V (h.symm j) v :=
  DirectSum.lequivCongrLeft_symm_lof k

end Reindex

section TensorProduct

variable {R H V₀ κ : Type*} [CommSemiring R] [Monoid H] [AddCommMonoid V₀] [Module R V₀]
  (ρ₀ : Representation R H V₀) [DecidableEq κ]
  {U : κ → Type*} [∀ i, AddCommMonoid (U i)] [∀ i, Module R (U i)]
  (τ : ∀ i, Representation R H (U i))

/-- **Left tensor product distributes over `Representation.directSum`.** -/
noncomputable def tprodDirectSumEquiv :
    (ρ₀.tprod (directSum τ)).Equiv (directSum fun i ↦ ρ₀.tprod (τ i)) :=
  .mk (_root_.TensorProduct.directSumRight R R V₀ U) fun g ↦
    _root_.TensorProduct.ext' fun v w ↦ by
      induction w using DirectSum.induction_on with
      | zero => simp
      | of i x => simp [directSum_apply, ← DirectSum.lof_eq_of R]
      | add x y hx hy => simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]

@[simp]
theorem toLinearEquiv_tprodDirectSumEquiv :
    (tprodDirectSumEquiv ρ₀ τ).toLinearEquiv = _root_.TensorProduct.directSumRight R R V₀ U :=
  (rfl)

@[simp]
theorem tprodDirectSumEquiv_tmul_lof (v : V₀) (i : κ) (u : U i) :
    tprodDirectSumEquiv ρ₀ τ (v ⊗ₜ[R] lof R κ U i u) =
      lof R κ (fun j ↦ V₀ ⊗[R] U j) i (v ⊗ₜ[R] u) := by
  simp [tprodDirectSumEquiv]

/-- The inverse equivalence recovers a pure tensor from a summand inclusion. -/
@[simp]
theorem tprodDirectSumEquiv_symm_lof (v : V₀) (i : κ) (u : U i) :
    (tprodDirectSumEquiv ρ₀ τ).symm (lof R κ (fun j ↦ V₀ ⊗[R] U j) i (v ⊗ₜ[R] u)) =
      v ⊗ₜ[R] lof R κ U i u := by
  rw [← tprodDirectSumEquiv_tmul_lof ρ₀ τ v i u, Representation.Equiv.symm_apply_apply]

end TensorProduct

section Internal

variable [DecidableEq ι]

variable (ρ : ∀ i, Representation k G (V i)) in
/-- **The inclusion of a summand** into a direct sum of representations. The underlying linear
map is `DirectSum.lof`. -/
noncomputable def IntertwiningMap.lof (i : ι) : IntertwiningMap (ρ i) (directSum ρ) where
  toLinearMap := DirectSum.lof k ι V i
  isIntertwining' g := by
    ext v
    simp [directSum_apply]

variable (ρ : ∀ i, Representation k G (V i)) in
@[simp]
theorem IntertwiningMap.lof_toLinearMap (i : ι) :
    (IntertwiningMap.lof ρ i).toLinearMap = DirectSum.lof k ι V i :=
  (rfl)

variable (ρ : ∀ i, Representation k G (V i)) in
@[simp]
theorem IntertwiningMap.lof_apply (i : ι) (v : V i) :
    IntertwiningMap.lof ρ i v = DirectSum.lof k ι V i v :=
  (rfl)

variable (ρ : ∀ i, Representation k G (V i)) in
/-- The inclusion of a summand into a direct sum of representations is injective. -/
theorem IntertwiningMap.lof_injective (i : ι) : Function.Injective (IntertwiningMap.lof ρ i) :=
  of_injective i

/-- The direct sum of intertwining maps restricts on summand `i` to the map of index `i`. -/
@[simp]
theorem IntertwiningMap.directSumMap_comp_lof {ρ : ∀ i, Representation k G (V i)}
    {σ : ∀ i, Representation k G (W i)} (f : ∀ i, IntertwiningMap (ρ i) (σ i)) (i : ι) :
    (directSumMap f).comp (IntertwiningMap.lof ρ i) = (IntertwiningMap.lof σ i).comp (f i) := by
  ext v
  simp

/-- Two intertwining maps out of a direct sum agree if they agree on every summand. -/
@[ext 1100]
theorem IntertwiningMap.directSum_ext {U : Type*} [AddCommMonoid U] [Module k U]
    {ρ : ∀ i, Representation k G (V i)} {τ : Representation k G U}
    {f g : IntertwiningMap (directSum ρ) τ}
    (h : ∀ i, f.comp (IntertwiningMap.lof ρ i) = g.comp (IntertwiningMap.lof ρ i)) : f = g :=
  ext <| DirectSum.linearMap_ext k fun i ↦ congrArg IntertwiningMap.toLinearMap (h i)

/-- **An internal direct-sum decomposition from an equivalence.** If `ρ` is equivalent to the
direct sum of a family of representations `σ i`, then the carrier of `ρ` is the internal direct
sum of a family of subrepresentations, the one of index `i` being equivalent to `σ i`. They are
the images of the summands under the inverse equivalence. -/
theorem Equiv.exists_isInternal {U : Type*} [AddCommMonoid U] [Module k U]
    {ρ : Representation k G U} {σ : ∀ i, Representation k G (V i)} (φ : ρ.Equiv (directSum σ)) :
    ∃ W : ι → Subrepresentation ρ, IsInternal (fun i ↦ (W i).toSubmodule) ∧
      ∀ i, Nonempty ((W i).toRepresentation.Equiv (σ i)) := by
  -- The summand of index `i`, included into `ρ` through `φ.symm`.
  let f i : IntertwiningMap (σ i) ρ := φ.symm.toIntertwiningMap.comp (IntertwiningMap.lof σ i)
  have hf i : Function.Injective (f i) :=
    φ.symm.toLinearEquiv.injective.comp (IntertwiningMap.lof_injective σ i)
  let e i := (f i).equivOfRange (P := (f i).range) (hf i) rfl
  exact ⟨fun i ↦ (f i).range,
    TauCeti.DirectSum.isInternal_of_lof (fun i ↦ (e i).toLinearEquiv) φ.symm.toLinearEquiv
      fun i x ↦ ((f i).equivOfRange_apply_coe (hf i) rfl x).symm,
    fun i ↦ ⟨(e i).symm⟩⟩

end Internal

end Representation
