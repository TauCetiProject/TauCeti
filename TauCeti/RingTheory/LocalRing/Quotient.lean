/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The maximal ideal and the cotangent space of a quotient of a local ring

Let `π : Q → A` be a surjective homomorphism of local rings. Then `π` maps `𝔪_Q` onto `𝔪_A`, and
an element of `Q` maps into `𝔪_A²` exactly when it lies in `ker π + 𝔪_Q²`. Consequently
lifts to `Q` of a basis of the cotangent space `𝔪_A / 𝔪_A²` span `𝔪_Q` modulo `ker π + 𝔪_Q²`,
and they are linearly independent modulo it.

## Main results

* `TauCeti.IsLocalRing.apply_mem_maximalIdeal_sq_iff`: `π a ∈ 𝔪_A²` if and only if
  `a ∈ ker π + 𝔪_Q²`.
* `TauCeti.IsLocalRing.maximalIdeal_quotient_eq_span_range`: if `𝔪_Q = J + (yⱼ)`, then the images
  of the `yⱼ` generate the maximal ideal of `Q ⧸ J`.
* `TauCeti.IsLocalRing.exists_lift_finBasis_cotangentSpace`: lifts to `Q` of a basis of the
  cotangent space of `A`.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Module

variable {Q A : Type*} [CommRing Q] [IsLocalRing Q] [CommRing A] [IsLocalRing A]

/-- Along a surjective homomorphism of local rings `π : Q → A`, an element `a` maps into `𝔪_A²`
if and only if it lies in `ker π + 𝔪_Q²`. -/
theorem apply_mem_maximalIdeal_sq_iff {π : Q →+* A} (hπ : Function.Surjective π) (a : Q) :
    π a ∈ maximalIdeal A ^ 2 ↔ a ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
  rw [← map_maximalIdeal_of_surjective π hπ, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective' _ hπ, sup_comm]

omit [IsLocalRing A] in
/-- If the maximal ideal of `Q` is `J + (yⱼ)`, then the images of the `yⱼ` generate the maximal
ideal of the local ring `Q ⧸ J`. -/
theorem maximalIdeal_quotient_eq_span_range {κ : Type*} {J : Ideal Q} [IsLocalRing (Q ⧸ J)]
    {y : κ → Q} (h : maximalIdeal Q = J ⊔ Ideal.span (Set.range y)) :
    maximalIdeal (Q ⧸ J) = Ideal.span (Set.range (Ideal.Quotient.mk J ∘ y)) := by
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, h, Ideal.map_sup,
    Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.range_comp]

/-- **Lifts of a basis of the cotangent space of a quotient.** Let `π : Q → A` be a surjective
homomorphism of local rings, where `𝔪_Q` is finitely generated. Then there are lifts
`y : Fin e → Q` of a basis of `𝔪_A / 𝔪_A²`, where `e` is its dimension. They lie in `𝔪_Q`, span
`𝔪_Q` modulo `ker π + 𝔪_Q²`, and are linearly independent modulo it: a combination `∑ cⱼ yⱼ` lies
in `ker π + 𝔪_Q²` only if every `cⱼ ∈ 𝔪_Q`. -/
theorem exists_lift_finBasis_cotangentSpace (hfg : (maximalIdeal Q).FG) {π : Q →+* A}
    (hπ : Function.Surjective π) :
    ∃ y : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
      (∀ j, y j ∈ maximalIdeal Q) ∧
      maximalIdeal Q ≤ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) ∧
      ∀ c : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
        ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 → ∀ j, c j ∈ maximalIdeal Q := by
  set e := finrank (ResidueField A) (CotangentSpace A)
  have hπ𝔪 : (maximalIdeal Q).map π = maximalIdeal A := map_maximalIdeal_of_surjective π hπ
  have : IsLocalHom π := .of_surjective π hπ
  have : Module.Finite A (maximalIdeal A) := Module.Finite.iff_fg.2 (hπ𝔪 ▸ hfg.map π)
  have : Module.Finite A (CotangentSpace A) :=
    .of_surjective _ (maximalIdeal A).toCotangent_surjective
  have : Module.Finite (ResidueField A) (CotangentSpace A) :=
    .of_restrictScalars_finite A _ _
  let bA := Module.finBasisOfFinrankEq (ResidueField A) (CotangentSpace A) rfl
  choose m hm using fun j ↦ (maximalIdeal A).toCotangent_surjective (bA j)
  choose y hy using fun j ↦ hπ (m j : A)
  have hy𝔪 (j : Fin e) : y j ∈ maximalIdeal Q := by
    rw [← maximalIdeal_comap π, Ideal.mem_comap, hy]
    exact (m j).2
  have hsum𝔪 (c : Fin e → Q) : π (∑ j, c j * y j) ∈ maximalIdeal A :=
    hπ𝔪 ▸ Ideal.mem_map_of_mem π (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (hy𝔪 j))
  have hcot (c : Fin e → Q) : (maximalIdeal A).toCotangent ⟨_, hsum𝔪 c⟩ =
      ∑ j, residue A (π (c j)) • bA j := by
    have : (⟨_, hsum𝔪 c⟩ : maximalIdeal A) = ∑ j, π (c j) • m j := by
      ext
      simp [hy]
    rw [this, map_sum]
    simp [hm, ← ResidueField.algebraMap_eq, algebraMap_smul]
  -- The `yⱼ` together with `ker π` span `𝔪` modulo `𝔪²` ...
  have hcov (a : Q) (ha : a ∈ maximalIdeal Q) :
      a ∈ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) := by
    have haA : π a ∈ maximalIdeal A := hπ𝔪 ▸ Ideal.mem_map_of_mem π ha
    choose c hc using fun j ↦ (residue_surjective.comp hπ) (bA.repr
      ((maximalIdeal A).toCotangent ⟨_, haA⟩) j)
    have hspan : ∑ j, c j * y j ∈ Ideal.span (Set.range y) :=
      Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hrest : a - ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
      have hmem : π (a - ∑ j, c j * y j) ∈ maximalIdeal A :=
        (map_sub π _ _) ▸ sub_mem haA (hsum𝔪 c)
      rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hmem⟩]
      have : (⟨_, hmem⟩ : maximalIdeal A) = ⟨_, haA⟩ - ⟨_, hsum𝔪 c⟩ :=
        Subtype.ext (map_sub π _ _)
      rw [this, map_sub, hcot]
      simp only [Function.comp_apply] at hc
      simp [hc, Basis.sum_repr]
    simpa using Submodule.add_mem_sup hspan hrest
  -- ... and are linearly independent modulo `ker π + 𝔪²`.
  have hind (c : Fin e → Q) (hc : ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2)
      (j : Fin e) : c j ∈ maximalIdeal Q := by
    rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hsum𝔪 c⟩,
      hcot] at hc
    have := (Fintype.linearIndependent_iff.1 bA.linearIndependent _ hc) j
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap] at this
    exact this
  exact ⟨y, hy𝔪, fun a ha ↦ hcov a ha, hind⟩

end TauCeti.IsLocalRing
