/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension

/-!
# The decomposition group of an infinite place acts on the completion

Let `L/K` be an extension of number fields, `v` an infinite place of `K`, and `w` an infinite
place of `L` above `v`. An automorphism `σ ∈ Aut(L/K)` carries `w` to the place `σ • w`, and it
is an isometry from `L` with the absolute value `w` to `L` with the absolute value `σ • w`
(`apply_eq_of_eq_smul`). It therefore extends by continuity to an isomorphism of completions
`L_w ≃ₐ[K_v] L_{σ • w}`, `completionCongr`. Restricted to the stabilizer of `w`, its
decomposition group, this gives

```text
decompositionHom v w : MulAction.stabilizer (L ≃ₐ[K] L) w →* (L_w ≃ₐ[K_v] L_w).
```

When `L/K` is Galois this homomorphism is an isomorphism, `decompositionEquiv`: the
decomposition group of `w` *is* the Galois group of `L_w/K_v`. Injectivity is density of `L` in
`L_w`; surjectivity is a count. The decomposition group has one element when `w` is unramified
over `K` and two when it is ramified, which is the local degree `[L_w : K_v]`, and a finite
extension of fields has at most `[L_w : K_v]` automorphisms.

The target place of `completionCongr` is an arbitrary `w'` together with the equation
`w' = σ • w`, so that no transport along an equality of places is needed. Both completions carry
the `K_v`-algebra structure `NumberField.LiesOver.completionMap`, available in the
`NumberField.LiesOver` scope.

These are the archimedean counterparts of `IsDedekindDomain.HeightOneSpectrum.completionCongr`,
`IsDedekindDomain.HeightOneSpectrum.decompositionHom` and
`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv` at the finite places. Like them, they
are what identifies the units of `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` with a representation coinduced
from the decomposition group.

## Main definitions

* `NumberField.InfinitePlace.completionCongr`: the isomorphism `L_w ≃ₐ[K_v] L_{w'}` induced by
  `σ` when `w' = σ • w`.
* `NumberField.InfinitePlace.decompositionHom`: the action of the decomposition group of `w` on
  `L_w`.
* `NumberField.InfinitePlace.decompositionEquiv`: that action, as an isomorphism onto the local
  Galois group, when `L/K` is Galois.

## Main results

* `NumberField.InfinitePlace.completionCongr_algebraMap` and
  `NumberField.InfinitePlace.eq_completionCongr_of_continuous`: `completionCongr` extends `σ`,
  uniquely among continuous maps.
* `NumberField.InfinitePlace.decompositionHom_injective`: the decomposition group embeds into
  `Aut(L_w/K_v)`.
* `NumberField.InfinitePlace.card_stabilizer_eq_finrank_completion`: for `L/K` Galois the
  decomposition group has `[L_w : K_v]` elements.
* `NumberField.InfinitePlace.decompositionHom_surjective`: for `L/K` Galois every
  `K_v`-automorphism of `L_w` comes from the decomposition group.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8 and §9.
-/

public section
noncomputable section

open Module
open scoped NumberField.LiesOver

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An automorphism `σ` of `L/K` carries the absolute value `w` to the absolute value `w'` when
`w' = σ • w`. -/
theorem apply_eq_of_eq_smul (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : w' = σ • w) (x : L) :
    w' (σ x) = w x := by
  subst h
  simp

/-- The Galois action on the places of `L` preserves the places above a place `v` of `K`. -/
instance liesOver_smul (v : InfinitePlace K) (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    [w.LiesOver v] : (σ • w).LiesOver v := by
  have h : (σ • w).comap (algebraMap K L) = v := by
    rw [comap_smul, ← LiesOver.comap_eq w v]
    congr 1
    ext x
    simp
  exact ⟨congrArg Subtype.val h⟩

/-- Two continuous maps out of `L_w` into a Hausdorff space agree once they agree on `L`. -/
private theorem completion_funext {w : InfinitePlace L} {B : Type*} [TopologicalSpace B]
    [T2Space B] {f g : w.Completion → B} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L w.Completion x) = g (algebraMap L w.Completion x)) : f = g := by
  funext a
  induction a using Completion.induction_on with
  | hp => exact isClosed_eq hf hg
  | ih a => exact h a.ofAbs

/-- `σ` is an isometry from `L` with the absolute value `w` to `L` with the absolute value
`σ • w`. -/
private theorem isometry_withAbsCongr (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L}
    (h : w' = σ • w) : Isometry (WithAbs.congr w.1 w'.1 σ.toRingEquiv) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact apply_eq_of_eq_smul σ h x.ofAbs

/-- The ring isomorphism `L_w ≃ L_{w'}` extending the isometry `σ`. -/
private def completionRingEquiv (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : w' = σ • w) :
    w.Completion ≃+* w'.Completion :=
  (Completion.equiv w).trans ((UniformSpace.Completion.mapRingEquiv _
    (isometry_withAbsCongr σ h).continuous
    ((isometry_withAbsCongr σ h).right_inv
      (WithAbs.congr w.1 w'.1 σ.toRingEquiv).right_inv).continuous).trans
    (Completion.equiv w').symm)

private theorem continuous_completionRingEquiv (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L}
    (h : w' = σ • w) : Continuous (completionRingEquiv σ h) :=
  (Completion.continuous_ofCompletion w').comp <|
    UniformSpace.Completion.continuous_map.comp (Completion.continuous_toCompletion w)

private theorem completionRingEquiv_coe (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L}
    (h : w' = σ • w) (x : WithAbs w.1) :
    completionRingEquiv σ h x = (WithAbs.congr w.1 w'.1 σ.toRingEquiv x : WithAbs w'.1) :=
  Completion.ext <| UniformSpace.Completion.mapRingHom_coe (isometry_withAbsCongr σ h).continuous x

variable (v : InfinitePlace K)

/-- The isomorphism of completions `L_w ≃ₐ[K_v] L_{w'}` induced by an automorphism `σ` of `L/K`
carrying `w` to `w'`: the continuous extension of `σ`. -/
def completionCongr (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} [w.LiesOver v] [w'.LiesOver v]
    (h : w' = σ • w) : w.Completion ≃ₐ[v.Completion] w'.Completion :=
  AlgEquiv.ofRingEquiv (f := completionRingEquiv σ h) fun a ↦ by
    -- both sides are continuous in `a`, and `σ` fixes the image of `K`
    induction a using Completion.induction_on with
    | hp =>
      exact isClosed_eq ((continuous_completionRingEquiv σ h).comp
        (LiesOver.continuous_completionMap v w)) (LiesOver.continuous_completionMap v w')
    | ih a =>
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, LiesOver.completionMap_coe,
        LiesOver.completionMap_coe, completionRingEquiv_coe]
      congr 2
      apply WithAbs.ofAbs_injective
      simp [WithAbs.ofAbs_algebraMap]

variable {v}

section completionCongr

variable {w w' : InfinitePlace L} [w.LiesOver v] [w'.LiesOver v]

/-- `completionCongr v σ h` extends `σ`. -/
@[simp]
theorem completionCongr_algebraMap (σ : L ≃ₐ[K] L) (h : w' = σ • w) (x : L) :
    completionCongr v σ h (x : w.Completion) = (σ x : w'.Completion) :=
  completionRingEquiv_coe σ h (WithAbs.toAbs w.1 x)

variable (v) in
/-- `completionCongr` is continuous. -/
theorem continuous_completionCongr (σ : L ≃ₐ[K] L) (h : w' = σ • w) :
    Continuous (completionCongr v σ h) :=
  continuous_completionRingEquiv σ h

/-- `completionCongr` is the only continuous map `L_w → L_{w'}` extending `σ`. -/
theorem eq_completionCongr_of_continuous (σ : L ≃ₐ[K] L) (h : w' = σ • w)
    {f : w.Completion → w'.Completion} (hf : Continuous f)
    (hfL : ∀ x : L, f (algebraMap L w.Completion x) = algebraMap L w'.Completion (σ x)) :
    f = completionCongr v σ h :=
  completion_funext hf (continuous_completionCongr v σ h) fun x ↦ by
    rw [hfL, Completion.algebraMap_apply, Completion.algebraMap_apply,
      completionCongr_algebraMap]

/-- `completionCongr` depends only on the automorphism, not on the proof that it carries `w`
to `w'`. -/
private theorem completionCongr_congr {σ σ' : L ≃ₐ[K] L} (hσσ' : σ = σ')
    (h : w' = σ • w) (h' : w' = σ' • w) :
    completionCongr v σ h = completionCongr v σ' h' := by
  subst hσσ'
  rfl

/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_one :
    completionCongr (w := w) (w' := w) v (1 : L ≃ₐ[K] L) (by simp) = AlgEquiv.refl :=
  AlgEquiv.ext fun a ↦ (congrFun (eq_completionCongr_of_continuous (v := v) (w := w) (w' := w) 1
    (by simp) continuous_id fun _ ↦ rfl) a).symm

/-- `completionCongr` is multiplicative: transporting along `σ` and then along `τ` is
transporting along `τ * σ`. -/
@[simp]
theorem completionCongr_trans {w'' : InfinitePlace L} [w''.LiesOver v]
    (σ τ : L ≃ₐ[K] L) (hσ : w' = σ • w) (hτ : w'' = τ • w') :
    (completionCongr v σ hσ).trans (completionCongr v τ hτ) =
      completionCongr v (τ * σ) (by rw [hτ, hσ, mul_smul]) :=
  AlgEquiv.ext (congrFun (eq_completionCongr_of_continuous (τ * σ) _
    ((continuous_completionCongr v τ hτ).comp (continuous_completionCongr v σ hσ)) fun x ↦ by
      rw [AlgEquiv.trans_apply, Completion.algebraMap_apply, Completion.algebraMap_apply,
        completionCongr_algebraMap, completionCongr_algebraMap, AlgEquiv.mul_apply]))

/-- The inverse of `completionCongr v σ h` is `completionCongr` of `σ⁻¹`. -/
@[simp]
theorem completionCongr_symm (σ : L ≃ₐ[K] L) (h : w' = σ • w) :
    (completionCongr v σ h).symm = completionCongr v σ⁻¹ (by rw [h, inv_smul_smul]) := by
  refine AlgEquiv.ext fun x ↦ ?_
  rw [AlgEquiv.symm_apply_eq, ← AlgEquiv.trans_apply, completionCongr_trans,
    completionCongr_congr (mul_inv_cancel σ) _ (by simp), completionCongr_one]
  rfl

end completionCongr

variable (v) (w : InfinitePlace L) [w.LiesOver v]

/-- The action of the decomposition group of `w` on the completion `L_w`: each element of the
stabilizer of `w` extends by continuity to a `K_v`-algebra automorphism of `L_w`. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w →* (w.Completion ≃ₐ[v.Completion] w.Completion) where
  toFun τ := completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm
  map_one' := completionCongr_one
  map_mul' σ τ := (completionCongr_trans (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp τ.2).symm
      (MulAction.mem_stabilizer_iff.mp σ.2).symm).symm

variable {v w}

/-- An element of the decomposition group acts on `L_w` by `completionCongr`. -/
theorem decompositionHom_apply (τ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    decompositionHom v w τ =
      completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm :=
  (rfl)

/-- The defining property of `decompositionHom`: on `L` it is the action of the automorphism. -/
@[simp]
theorem decompositionHom_algebraMap (τ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    decompositionHom v w τ (x : w.Completion) = ((τ : L ≃ₐ[K] L) x : w.Completion) := by
  rw [decompositionHom_apply, completionCongr_algebraMap]

variable (v w) in
/-- The decomposition group of `w` acts faithfully on `L_w`. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext x
  have := congr($hτ (x : w.Completion))
  rw [decompositionHom_algebraMap, AlgEquiv.one_apply, ← Completion.algebraMap_apply,
    ← Completion.algebraMap_apply] at this
  exact (algebraMap L w.Completion).injective this

/-! ### The decomposition group is the local Galois group -/

section IsGalois

variable (v w) [IsGalois K L]

/-- **The decomposition group of `w` has order the local degree.** For `L/K` Galois the
decomposition group of `w` has one element when `w` is unramified over `K` and two when it is
ramified, and that is the degree of `L_w` over `K_v`. -/
theorem card_stabilizer_eq_finrank_completion :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = finrank v.Completion w.Completion := by
  classical
  rw [card_stabilizer]
  split_ifs with hw
  · exact (IsUnramified.finrank_eq_one v hw).symm
  · exact (IsRamified.finrank_eq_two v hw).symm

/-- **The decomposition group of `w` exhausts `Aut(L_w/K_v)`.** For `L/K` Galois every
`K_v`-algebra automorphism of `L_w` is the continuous extension of an automorphism of `L/K`
stabilizing `w`. -/
-- The decomposition group has `[L_w : K_v]` elements and a finite extension of fields has at
-- most that many automorphisms, so the injection of the previous lemma is already onto.
theorem decompositionHom_surjective : Function.Surjective (decompositionHom v w) := by
  refine ((Nat.bijective_iff_injective_and_card (decompositionHom v w)).mpr
    ⟨decompositionHom_injective v w, le_antisymm ?_ ?_⟩).surjective
  · exact Nat.card_le_card_of_injective _ (decompositionHom_injective v w)
  · rw [card_stabilizer_eq_finrank_completion v w]
    exact Nat.card_eq_fintype_card.trans_le AlgEquiv.card_le

/-- **The decomposition group of `w` is the Galois group of `L_w/K_v`.** -/
def decompositionEquiv :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃* (w.Completion ≃ₐ[v.Completion] w.Completion) :=
  MulEquiv.ofBijective (decompositionHom v w)
    ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩

@[simp]
theorem coe_decompositionEquiv : ⇑(decompositionEquiv v w) = decompositionHom v w := (rfl)

end IsGalois

end NumberField.InfinitePlace
