/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.PicardGroup

/-!
# Lattice indices and tensor products with invertible modules

Let `M` be an invertible module over a commutative ring `R`. Tensoring with `M` does not change
the cardinality of a finite module `T` (`Module.Invertible.card_tensorProduct`): `T` is a module
over the finite ring `R / Ann(T)`, over which `M` becomes free of rank one, since the Picard group
of a ring with finitely many maximal ideals is trivial (Mathlib).

Consequently the index of the line spanned by a pure tensor is multiplicative
(`Submodule.cardQuot_span_tmul`): if `s ∈ L` has trivial annihilator and `L / R s` is finite, then
for every `t ∈ M`,

`#((L ⊗ M) / R (s ⊗ t)) = #(L / R s) · #(M / R t)`.

The proof filters `R (s ⊗ t) ⊆ s ⊗ M ⊆ L ⊗ M`. The map `m ↦ s ⊗ m` is injective because `M` is
flat, so the first index is `#(M / R t)`, and the second quotient is `(L / R s) ⊗ M`, of
cardinality `#(L / R s)`.

This is the lattice-index part of the additivity of the Arakelov degree on tensor products of
hermitian line bundles (roadmap ArakelovGeometryAndAbelianHeights, §1.5).
-/

public section

open TensorProduct

namespace Module.Invertible

variable {R : Type*} [CommRing R] {T M : Type*} [AddCommGroup T] [Module R T]
  [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- **Tensoring with an invertible module preserves the cardinality of a finite module.** -/
theorem card_tensorProduct [Finite T] : Nat.card (T ⊗[R] M) = Nat.card T := by
  -- `T` is a module over `R / Ann(T)`, which acts faithfully on the finite set `T`.
  let I := Module.annihilator R T
  let : Module (R ⧸ I) T := Module.quotientAnnihilator
  have : IsScalarTower R (R ⧸ I) T := .of_algebraMap_smul fun r t ↦ rfl
  have : Finite (R ⧸ I) := by
    refine _root_.Finite.of_injective (fun r : R ⧸ I ↦ fun t : T ↦ r • t) fun a b hab ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, Module.mem_annihilator]
    intro t
    have := congrFun hab t
    simp only at this
    rw [sub_smul]
    exact sub_eq_zero.2 this
  -- `R / Ann(T)` is finite, so the invertible module `(R / Ann(T)) ⊗ M` over it is free.
  obtain ⟨e⟩ : Nonempty ((R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] R ⧸ I) :=
    free_iff_linearEquiv.mp inferInstance
  exact Nat.card_congr ((AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) T M).symm ≪≫ₗ
    (AlgebraTensorModule.congr (LinearEquiv.refl (R ⧸ I) T) e) ≪≫ₗ
      TensorProduct.rid (R ⧸ I) T).toEquiv

end Module.Invertible

namespace Submodule

variable {R : Type*} [CommRing R] {L M : Type*} [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- **The index of a pure tensor line is multiplicative.** If `s ∈ L` has trivial annihilator and
`L / R s` is finite, then for `t` in an invertible module `M`,
`#((L ⊗ M) / R (s ⊗ t)) = #(L / R s) · #(M / R t)`. -/
theorem cardQuot_span_tmul {s : L} (hs : Function.Injective (LinearMap.toSpanSingleton R L s))
    [Finite (L ⧸ R ∙ s)] (t : M) :
    (R ∙ (s ⊗ₜ[R] t)).cardQuot = (R ∙ s).cardQuot * (R ∙ t).cardQuot := by
  -- `φ : M → L ⊗ M`, `m ↦ s ⊗ m`, is injective since `M` is flat.
  let φ : M →ₗ[R] L ⊗[R] M :=
    (LinearMap.toSpanSingleton R L s).rTensor M ∘ₗ (TensorProduct.lid R M).symm.toLinearMap
  have hφ : Function.Injective φ :=
    (Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hs).comp
      (TensorProduct.lid R M).symm.injective
  have hφt : (R ∙ t).map φ = R ∙ (s ⊗ₜ[R] t) := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [φ]
  -- The image of `φ` is the image of `(R ∙ s) ⊗ M`.
  have hrange : LinearMap.range φ = LinearMap.range ((R ∙ s).subtype.rTensor M) := by
    have hfac : LinearMap.toSpanSingleton R L s =
        (R ∙ s).subtype ∘ₗ
          (LinearMap.toSpanSingleton R (R ∙ s) ⟨s, Submodule.mem_span_singleton_self s⟩) := by
      ext; simp
    have hsurj : Function.Surjective
        (LinearMap.toSpanSingleton R (R ∙ s) ⟨s, Submodule.mem_span_singleton_self s⟩) := by
      rintro ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨r, by simp⟩
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), hfac,
      LinearMap.rTensor_comp,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.2 (LinearMap.rTensor_surjective M hsurj))]
  have hidx : (LinearMap.range φ).cardQuot = (R ∙ s).cardQuot := by
    rw [hrange, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    -- `rTensor M f` is `TensorProduct.map f id` by definition.
    exact (Nat.card_congr (TensorProduct.quotientTensorEquiv M (R ∙ s)).toEquiv).symm.trans
      Module.Invertible.card_tensorProduct
  unfold Submodule.cardQuot at hidx ⊢
  rw [← hφt, Submodule.map_toAddSubgroup, AddSubgroup.index_map_of_injective _ hφ, mul_comm]
  rw [← hidx]
  rfl

end Submodule
