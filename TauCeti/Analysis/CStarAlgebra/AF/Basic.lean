/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
* `NonUnitalStarSubalgebra.isClosed_of_finiteDimensional`: finite-dimensional ⋆-subalgebras are
  closed, so the stages of an AF algebra are C⋆-subalgebras.
* `TauCeti.IsAF.separableSpace`: an AF algebra is separable.
* `TauCeti.IsAF.exists_finiteDimensional_approx`: in an AF algebra every finite subset is
  approximated to every positive tolerance inside a finite-dimensional C⋆-subalgebra.

## References

* O. Bratteli, *Inductive limits of finite dimensional C*-algebras*, Trans. Amer. Math. Soc. 171
  (1972), 195–234: Theorem 2.2 (the local characterization) and Theorem 3.3 (ideals).
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

namespace NonUnitalStarSubalgebra

variable {R A B : Type*} [Field R] [NonUnitalRing A] [StarRing A] [Module R A]
  [NonUnitalRing B] [StarRing B] [Module R B]

/-- A ⋆-subalgebra is finite-dimensional exactly when its underlying submodule is. -/
theorem finiteDimensional_iff_toSubmodule (S : NonUnitalStarSubalgebra R A) :
    FiniteDimensional R S ↔ FiniteDimensional R S.toNonUnitalSubalgebra.toSubmodule :=
  Iff.rfl

/-- A ⋆-subalgebra of a finite-dimensional ⋆-algebra is finite-dimensional. -/
instance instFiniteDimensional [FiniteDimensional R A] (S : NonUnitalStarSubalgebra R A) :
    FiniteDimensional R S :=
  inferInstanceAs (FiniteDimensional R S.toNonUnitalSubalgebra.toSubmodule)

/-- The image of a finite-dimensional ⋆-subalgebra under a ⋆-homomorphism is finite-dimensional. -/
instance instFiniteDimensionalMap (S : NonUnitalStarSubalgebra R A)
    [h : FiniteDimensional R S] (f : A →⋆ₙₐ[R] B) : FiniteDimensional R (S.map f) := by
  have : FiniteDimensional R S.toNonUnitalSubalgebra.toSubmodule := h
  have e : (S.map f).toNonUnitalSubalgebra.toSubmodule =
      S.toNonUnitalSubalgebra.toSubmodule.map (f : A →ₗ[R] B) := rfl
  rw [finiteDimensional_iff_toSubmodule, e]
  infer_instance

/-- The product of two finite-dimensional ⋆-subalgebras is finite-dimensional. -/
instance instFiniteDimensionalProd (S : NonUnitalStarSubalgebra R A)
    (T : NonUnitalStarSubalgebra R B) [hS : FiniteDimensional R S] [hT : FiniteDimensional R T] :
    FiniteDimensional R (S.prod T) := by
  have : FiniteDimensional R S.toNonUnitalSubalgebra.toSubmodule := hS
  have : FiniteDimensional R T.toNonUnitalSubalgebra.toSubmodule := hT
  have e : (S.prod T).toNonUnitalSubalgebra.toSubmodule =
      S.toNonUnitalSubalgebra.toSubmodule.prod T.toNonUnitalSubalgebra.toSubmodule := rfl
  rw [finiteDimensional_iff_toSubmodule, e]
  exact (Submodule.prodEquiv _ _).symm.finiteDimensional

/-- A finite-dimensional ⋆-subalgebra of a Hausdorff topological ⋆-algebra over a complete field
is closed. -/
theorem isClosed_of_finiteDimensional {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [TopologicalSpace A] [T2Space A] [IsTopologicalAddGroup A] [Module 𝕜 A] [ContinuousSMul 𝕜 A]
    (S : NonUnitalStarSubalgebra 𝕜 A) [h : FiniteDimensional 𝕜 S] : IsClosed (S : Set A) :=
  have : FiniteDimensional 𝕜 S.toNonUnitalSubalgebra.toSubmodule := h
  S.toNonUnitalSubalgebra.toSubmodule.isClosed_of_finiteDimensional

end NonUnitalStarSubalgebra

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A finite-dimensional C⋆-algebra is AF, with every stage the whole algebra. -/
theorem isAF_of_finiteDimensional [FiniteDimensional ℂ A] : IsAF A :=
  ⟨fun _ ↦ ⊤, monotone_const, fun _ ↦ NonUnitalStarSubalgebra.instFiniteDimensional _,
    by simpa only [NonUnitalStarAlgebra.coe_top, iUnion_const] using dense_univ⟩

namespace IsAF

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The image of an AF algebra under a surjective ⋆-homomorphism is AF: the images of the stages
are finite-dimensional, increasing and have dense union. In particular quotients of AF algebras
are AF. -/
theorem of_surjective (hA : IsAF A) (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Surjective f) : IsAF B := by
  obtain ⟨S, hmono, hfin, hdense⟩ := hA
  refine ⟨fun n ↦ (S n).map f, fun m n h ↦ NonUnitalStarSubalgebra.map_mono (hmono h),
    fun n ↦ have := hfin n; (S n).instFiniteDimensionalMap f, ?_⟩
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
    fun n ↦ have := hSfin n; have := hTfin n; (S n).instFiniteDimensionalProd (T n), ?_⟩
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
  let T (n : ℕ) : NonUnitalStarSubalgebra ℂ (Unitization ℂ A) :=
    (⊤ : NonUnitalStarSubalgebra ℂ (Unitization ℂ (S n))).map (ι n).toNonUnitalStarAlgHom
  have hT (n : ℕ) (x : Unitization ℂ A) : x ∈ T n ↔ x.snd ∈ S n := by
    refine ⟨?_, fun hx ↦ ⟨Unitization.inl x.fst + Unitization.inr ⟨x.snd, hx⟩, trivial, ?_⟩⟩
    · rintro ⟨y, -, rfl⟩
      exact (show (ι n y).snd ∈ S n by simp [ι])
    · exact (show ι n (Unitization.inl x.fst + Unitization.inr ⟨x.snd, hx⟩) = x by
        ext <;> simp [ι])
  refine ⟨T, fun m n h x ↦ by simpa only [hT] using fun hx ↦ hmono h hx, fun n ↦ ?_, ?_⟩
  · have := hfin n
    have : FiniteDimensional ℂ (Unitization ℂ (S n)) :=
      (Unitization.linearEquiv ℂ ℂ (S n)).symm.finiteDimensional
    exact NonUnitalStarSubalgebra.instFiniteDimensionalMap _ _
  · have h : (⋃ n, (T n : Set (Unitization ℂ A))) =
        Unitization.uniformEquivProd ⁻¹' (univ ×ˢ ⋃ n, (S n : Set A)) := by
      ext x
      simp only [mem_iUnion, SetLike.mem_coe, hT, mem_preimage, mem_prod, mem_univ, true_and]
      rfl
    rw [h]
    exact (dense_univ.prod hdense).preimage Unitization.uniformEquivProd.toHomeomorph.isOpenMap

end IsAF

end TauCeti
