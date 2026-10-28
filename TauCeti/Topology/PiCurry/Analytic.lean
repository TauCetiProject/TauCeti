/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Topology.PiCurry
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-!
# Linear and analytic regrouping of families

The regrouping homeomorphisms from `TauCeti.Topology.PiCurry` are coordinate projections and
finite products, so they and their inverses are analytic. The constant-space regrouping is also
a continuous linear equivalence for arbitrary families of topological modules. These facts are kept
beside the homeomorphisms, so applications can reuse them without importing a root or polynomial
development.
-/

public section

open Topology

namespace TauCeti

/-- Regrouping a family of tuples along a bijection of the sigma index, as a continuous linear
equivalence. The underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`. -/
def piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → E) ≃L[R] (ι' → E) where
  toLinearEquiv :=
    { toFun := piSigmaConstHomeomorph E e
      invFun := (piSigmaConstHomeomorph E e).symm
      left_inv := (piSigmaConstHomeomorph E e).left_inv
      right_inv := (piSigmaConstHomeomorph E e).right_inv
      map_add' := by
        intro x y
        ext j
        simp only [piSigmaConstHomeomorph_apply, Pi.add_apply]
      map_smul' := by
        intro a x
        ext j
        simp only [piSigmaConstHomeomorph_apply, Pi.smul_apply, RingHom.id_apply] }
  continuous_toFun := (piSigmaConstHomeomorph E e).continuous
  continuous_invFun := (piSigmaConstHomeomorph E e).symm.continuous

/-- The continuous linear regrouping has the existing regrouping homeomorphism as its function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (piSigmaConstContinuousLinearEquiv R E e : (∀ i, κ i → E) → (ι' → E)) =
      piSigmaConstHomeomorph E e := (rfl)

/-- The inverse continuous linear regrouping has the inverse regrouping homeomorphism as its
function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((piSigmaConstContinuousLinearEquiv R E e).symm : (ι' → E) → ∀ i, κ i → E) =
      (piSigmaConstHomeomorph E e).symm := (rfl)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] {m : ι → ℕ} {n : ℕ}

/-- Regrouping a finite family of tuples is analytic. -/
theorem analyticAt_piSigmaConstHomeomorph
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : ∀ i, Fin (m i) → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e) c := by
  refine AnalyticAt.pi fun j => ?_
  have hblock : AnalyticAt 𝕜 (fun p : (∀ i, Fin (m i) → 𝕜) => p (e.symm j).1) c :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i => Fin (m i) → 𝕜)
      (e.symm j).1).analyticAt c
  have hcoord : AnalyticAt 𝕜
      (fun p : Fin (m (e.symm j).1) → 𝕜 => p (e.symm j).2)
      (c (e.symm j).1) :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (m (e.symm j).1) => 𝕜)
      (e.symm j).2).analyticAt _
  convert hcoord.comp hblock using 1
  ext x
  exact piSigmaConstHomeomorph_apply 𝕜 e x j

/-- The inverse regrouping from one tuple to a finite family of tuples is analytic. -/
theorem analyticAt_piSigmaConstHomeomorph_symm
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : Fin n → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e).symm c := by
  refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
  convert (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)
    (e ⟨i, j⟩)).analyticAt c using 1
  ext x
  exact piSigmaConstHomeomorph_symm_apply 𝕜 e x i j

end TauCeti

end
