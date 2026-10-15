/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Leaf
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Transversals and taut foliations

A closed transversal to a foliation is a C¹ periodic curve whose velocity is everywhere
transverse to the tangent distribution.  The definition uses complementary submodules, so it
does not silently assume a codimension: a one-dimensional transversal can exist only when the
distribution has the corresponding codimension.  A foliation is taut when every leaf meets one
of these curves.

The obstruction theorem gives a concrete example.  The foliation of a finite-dimensional normed
space by the affine cosets of the kernel of a continuous linear functional has a global first
integral.  Rolle's theorem forces every closed C¹ curve to have velocity in that kernel
somewhere, so this foliation is not taut.

The terminology follows Calegari, *Foliations and the Geometry of 3-Manifolds*, Chapter 4.
-/

public section

noncomputable section

open Set
open TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace Foliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} [IsManifold I (n + 1) M]
  (F : Foliation I n M k)

/-- A C¹ closed curve is transverse to `F` when its velocity and the leaf tangent space are
complementary at every parameter value. -/
def IsClosedTransversal (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ Function.Periodic γ 1 ∧
    ∀ t, curveVelocity I γ t ≠ 0 ∧
      IsCompl (Submodule.span ℝ {curveVelocity I γ t}) (F.distribution (γ t))

/-- A closed transversal is characterized by pointwise periodicity and its defining fields. -/
@[simp]
theorem isClosedTransversal_iff (γ : ℝ → M) : F.IsClosedTransversal γ ↔
    ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ (∀ t : ℝ, γ (t + 1) = γ t) ∧
      ∀ t, curveVelocity I γ t ≠ 0 ∧
        IsCompl (Submodule.span ℝ {curveVelocity I γ t}) (F.distribution (γ t)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩
  · rintro ⟨hγdiff, hperiod, htrans⟩
    exact ⟨hγdiff, hperiod, htrans⟩

/-- A foliation is taut when every leaf meets a C¹ closed transversal. -/
def Taut : Prop :=
  ∀ x : M, ∃ γ : ℝ → M, F.IsClosedTransversal γ ∧ ∃ t : ℝ, γ t ∈ F.leaf x

/-- Construct a taut foliation from a closed transversal meeting every leaf. -/
theorem Taut.mk
    {F : Foliation I n M k}
    (h : ∀ x : M, ∃ γ : ℝ → M, F.IsClosedTransversal γ ∧ ∃ t : ℝ, γ t ∈ F.leaf x) :
    F.Taut :=
  h

/-- A taut foliation has a closed transversal meeting each specified leaf. -/
theorem Taut.exists_transversal {F : Foliation I n M k} (h : F.Taut) (x : M) :
    ∃ γ : ℝ → M, F.IsClosedTransversal γ ∧ ∃ t : ℝ, γ t ∈ F.leaf x :=
  h x

variable {F}

/-- The C¹ regularity field of a closed transversal. -/
theorem IsClosedTransversal.contMDiff (hγ : F.IsClosedTransversal γ) :
    ContMDiff 𝓘(ℝ, ℝ) I 1 γ :=
  hγ.1

/-- The nonzero velocity field of a closed transversal. -/
theorem IsClosedTransversal.velocity_ne_zero (hγ : F.IsClosedTransversal γ) (t : ℝ) :
    curveVelocity I γ t ≠ 0 :=
  (hγ.2.2 t).1

/-- The complementary-distribution field of a closed transversal. -/
theorem IsClosedTransversal.isCompl (hγ : F.IsClosedTransversal γ) (t : ℝ) :
    IsCompl (Submodule.span ℝ {curveVelocity I γ t}) (F.distribution (γ t)) :=
  (hγ.2.2 t).2

/-- A closed transversal is 1-periodic. -/
theorem IsClosedTransversal.periodic (hγ : F.IsClosedTransversal γ) :
    Function.Periodic γ 1 := hγ.2.1

/-- The velocity of a closed transversal never belongs to the leaf distribution. -/
theorem IsClosedTransversal.velocity_not_mem (hγ : F.IsClosedTransversal γ) (t : ℝ) :
    curveVelocity I γ t ∉ F.distribution (γ t) := by
  exact (Submodule.disjoint_span_singleton' (hγ.2.2 t).1).mp
    (hγ.2.2 t).2.disjoint.symm

section FirstIntegral

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (ℓ : V →L[ℝ] ℝ) (hn : 1 ≤ n)

/-- The foliation by kernels of a continuous linear functional admits no closed transversal. -/
theorem not_isClosedTransversal_ofSubmodule_ker
    {γ : ℝ → V}
    (hγ : (Foliation.ofSubmodule (LinearMap.ker ℓ.toLinearMap) hn).IsClosedTransversal γ) :
    False := by
  obtain ⟨hγdiff, hperiod, htrans⟩ := hγ
  have hperiod01 : γ 0 = γ 1 := by
    simpa using (hperiod 0).symm
  have hγ' : ContDiff ℝ 1 γ := (contMDiff_iff_contDiff.mp hγdiff)
  let g : ℝ → ℝ := ℓ ∘ γ
  have hg : ContinuousOn g (Icc 0 1) :=
    (ℓ.continuous.comp hγ'.continuous).continuousOn
  have hgperiod : g 0 = g 1 := by simp [g, hperiod01]
  obtain ⟨c, _hc, hdc⟩ := exists_deriv_eq_zero (a := (0 : ℝ)) (b := 1) zero_lt_one hg hgperiod
  have hderiv : deriv g c = ℓ (deriv γ c) := by
    simpa [g] using
      (ℓ.hasFDerivAt.comp c (hγ'.differentiable one_ne_zero c).hasFDerivAt).hasDerivAt.deriv
  have hvzero : ℓ (curveVelocity 𝓘(ℝ, V) γ c) = 0 := by
    rw [curveVelocity_eq_deriv, ← hderiv, hdc]
  have hnot := IsClosedTransversal.velocity_not_mem
    (F := Foliation.ofSubmodule (LinearMap.ker ℓ.toLinearMap) hn)
      ⟨hγdiff, hperiod, htrans⟩ c
  apply hnot
  rw [Foliation.ofSubmodule_distribution]
  exact hvzero

/-- The foliation by affine cosets of the kernel of a continuous linear functional is not taut. -/
theorem not_taut_ofSubmodule_ker :
    ¬ (Foliation.ofSubmodule (LinearMap.ker ℓ.toLinearMap) hn).Taut := by
  intro htaut
  obtain ⟨γ, hγ, -⟩ := htaut.exists_transversal 0
  exact not_isClosedTransversal_ofSubmodule_ker ℓ hn hγ

end FirstIntegral

end Foliation

end TauCeti
