/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.NonUnitalSubalgebra.Finite
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# AF algebras

A C⋆-algebra `A` is *AF* (approximately finite-dimensional) when it is the closure of an increasing
sequence of finite-dimensional C⋆-subalgebras. Nonunital algebras and the zero algebra are
included, and the stages need not contain a unit of `A`.

This file defines the predicate and proves the facts that need no perturbation theory: every
finite-dimensional C⋆-algebra is AF, AF passes to images under surjective ⋆-homomorphisms (so to
quotients and along ⋆-isomorphisms), to products of two algebras and to the minimal unitization, an
AF algebra is separable, and every finite subset of an AF algebra is approximated to every positive
tolerance inside a finite-dimensional C⋆-subalgebra. The converse of the last statement for
separable algebras is Bratteli's local characterization, which needs the perturbation theory of
finite-dimensional C⋆-subalgebras.

## Main definitions

* `TauCeti.IsAF A`: `A` is the closure of an increasing sequence of finite-dimensional
  C⋆-subalgebras.

## Main statements

* `TauCeti.isAF_of_finiteDimensional`: a finite-dimensional C⋆-algebra is AF.
* `TauCeti.IsAF.of_surjective`, `StarAlgEquiv.isAF_iff`: AF passes to images under surjective
  ⋆-homomorphisms and is invariant under ⋆-isomorphisms.
* `TauCeti.IsAF.prod`, `TauCeti.IsAF.unitization`: products of two AF algebras and minimal
  unitizations of AF algebras are AF.
* `TauCeti.IsAF.separableSpace`: an AF algebra is separable.
* `TauCeti.IsAF.exists_finiteDimensional_approx`: in an AF algebra every finite subset is
  approximated to every positive tolerance inside a finite-dimensional C⋆-subalgebra.

## References

* O. Bratteli, *Inductive limits of finite dimensional C*-algebras*, Trans. Amer. Math. Soc. 171
  (1972), 195–234: Theorem 2.2 (the local characterization).
-/

public section

open Set TopologicalSpace
open scoped CStarAlgebra

namespace TauCeti

variable (A : Type*) [NonUnitalCStarAlgebra A]

/-- `A` is **AF**: it is the closure of an increasing sequence of finite-dimensional
C⋆-subalgebras. Nonunital algebras and the zero algebra are included, and the stages need not
contain a unit of `A`. -/
def IsAF : Prop :=
  ∃ S : ℕ → NonUnitalStarSubalgebra ℂ A,
    Monotone S ∧ (∀ n, FiniteDimensional ℂ (S n)) ∧ Dense (⋃ n, (S n : Set A))

variable {A}

/-- Unfolding lemma for `TauCeti.IsAF`. -/
theorem isAF_iff : IsAF A ↔ ∃ S : ℕ → NonUnitalStarSubalgebra ℂ A,
    Monotone S ∧ (∀ n, FiniteDimensional ℂ (S n)) ∧ Dense (⋃ n, (S n : Set A)) :=
  Iff.rfl

end TauCeti

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A finite-dimensional C⋆-algebra is AF, with every stage the whole algebra. -/
theorem isAF_of_finiteDimensional [FiniteDimensional ℂ A] : IsAF A :=
  ⟨fun _ ↦ ⊤, monotone_const, fun _ ↦ inferInstance,
    by simpa only [NonUnitalStarAlgebra.coe_top, iUnion_const] using dense_univ⟩

namespace IsAF

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The image of an AF algebra under a surjective ⋆-homomorphism is AF: the images of the stages
are finite-dimensional, increasing and have dense union. In particular quotients of AF algebras
are AF. -/
theorem of_surjective (hA : IsAF A) (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Surjective f) : IsAF B := by
  obtain ⟨S, hmono, hfin, hdense⟩ := hA
  refine ⟨fun n ↦ (S n).map f, fun m n h ↦ NonUnitalStarSubalgebra.map_mono (hmono h),
    fun n ↦ have := hfin n; inferInstance, ?_⟩
  have h : (⋃ n, (((S n).map f : NonUnitalStarSubalgebra ℂ B) : Set B)) =
        f '' ⋃ n, (S n : Set A) := by
    simp [image_iUnion]
  rw [h]
  exact hf.denseRange.dense_image (map_continuous f) hdense

end IsAF

/-- AF is invariant under ⋆-isomorphisms. -/
theorem _root_.StarAlgEquiv.isAF_iff {B : Type*} [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) :
    IsAF A ↔ IsAF B :=
  ⟨fun h ↦ h.of_surjective e.toNonUnitalStarAlgHom e.surjective,
    fun h ↦ h.of_surjective e.symm.toNonUnitalStarAlgHom e.symm.surjective⟩

namespace IsAF

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The product of two AF algebras is AF, with the products of the stages as stages. -/
theorem prod (hA : IsAF A) (hB : IsAF B) : IsAF (A × B) := by
  obtain ⟨S, hS, hSfin, hSdense⟩ := hA
  obtain ⟨T, hT, hTfin, hTdense⟩ := hB
  refine ⟨fun n ↦ (S n).prod (T n), fun m n h ↦ NonUnitalStarSubalgebra.prod_mono (hS h) (hT h),
    fun n ↦ have := hSfin n; have := hTfin n; inferInstance, ?_⟩
  refine (hSdense.prod hTdense).mono ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  obtain ⟨m, ha⟩ := mem_iUnion.1 ha
  obtain ⟨n, hb⟩ := mem_iUnion.1 hb
  exact mem_iUnion.2 ⟨max m n, hS (le_max_left m n) ha, hT (le_max_right m n) hb⟩

/-- In an AF algebra every finite subset is approximated to every positive tolerance inside a
finite-dimensional C⋆-subalgebra. Bratteli's local characterization is the converse for
separable algebras. -/
theorem exists_finiteDimensional_approx (hA : IsAF A) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : NonUnitalStarSubalgebra ℂ A, FiniteDimensional ℂ S ∧ ∀ a ∈ F, ∃ b ∈ S, ‖a - b‖ < ε := by
  obtain ⟨S, hmono, hfin, hdense⟩ := hA
  have h (a : A) : ∃ n, ∃ b ∈ S n, ‖a - b‖ < ε := by
    obtain ⟨b, hab, hb⟩ := Metric.dense_iff.1 hdense a ε hε
    obtain ⟨n, hb⟩ := mem_iUnion.1 hb
    exact ⟨n, b, hb, by simpa [dist_eq_norm'] using hab⟩
  choose n b hb hab using h
  refine ⟨S (F.sup n), hfin _, fun a ha ↦ ⟨b a, hmono (Finset.le_sup ha) (hb a), hab a⟩⟩

/-- An AF algebra is separable: each stage is finite-dimensional, hence separable, and the union of
the stages is dense. -/
theorem separableSpace (hA : IsAF A) : SeparableSpace A := by
  obtain ⟨S, -, hfin, hdense⟩ := hA
  refine (hdense.isSeparable_iff).1 (.iUnion fun n ↦ ?_)
  have := hfin n
  have : ProperSpace (S n) := FiniteDimensional.proper_rclike ℂ _
  exact IsSeparable.of_subtype (S n : Set A)

/-- The minimal unitization of an AF algebra is AF: its stages are the images of the unitizations
`ℂ ⊕ Sₙ` of the stages `Sₙ`. -/
theorem unitization (hA : IsAF A) : IsAF (Unitization ℂ A) := by
  obtain ⟨S, hmono, hfin, hdense⟩ := hA
  let ι (n : ℕ) := Unitization.starMap (NonUnitalStarSubalgebraClass.subtype (S n))
  let T (n : ℕ) : NonUnitalStarSubalgebra ℂ (Unitization ℂ A) := (ι n).toNonUnitalStarAlgHom.range
  have hT (n : ℕ) (x : Unitization ℂ A) : x ∈ T n ↔ x.snd ∈ S n := by
    rw [NonUnitalStarAlgHom.mem_range, StarAlgHom.coe_toNonUnitalStarAlgHom]
    refine ⟨?_, fun hx ↦ ⟨Unitization.inl x.fst + Unitization.inr ⟨x.snd, hx⟩, ?_⟩⟩
    · rintro ⟨y, rfl⟩
      simp [ι]
    · ext <;> simp [ι]
  refine ⟨T, fun m n h x ↦ by simpa only [hT] using fun hx ↦ hmono h hx, fun n ↦ ?_, ?_⟩
  · have := hfin n
    have : FiniteDimensional ℂ (Unitization ℂ (S n)) :=
      (Unitization.linearEquiv ℂ ℂ (S n)).symm.finiteDimensional
    infer_instance
  · have h : (⋃ n, (T n : Set (Unitization ℂ A))) =
        Unitization.addEquiv ℂ A ⁻¹' (univ ×ˢ ⋃ n, (S n : Set A)) := by
      ext x
      simp [hT]
    rw [h]
    exact (dense_univ.prod hdense).preimage <|
      Unitization.isUniformEmbedding_addEquiv.isEmbedding.isInducing.isOpenMap <| by
        simp [(Unitization.addEquiv ℂ A).surjective.range_eq]

end IsAF

end TauCeti
