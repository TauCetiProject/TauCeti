/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Distribution

/-!
# Basic functions of a distribution

A smooth function `a` on a manifold is **basic** for a distribution `D` when its differential
annihilates `D`: `da_x(v) = 0` for every `v ∈ D x`. When `D` is the tangent distribution of a
foliation these are the functions that are locally constant along the leaves, the functions that
descend to a leaf space when one exists. By the Leibniz rule the basic functions form a subalgebra
`TauCeti.basicFunctions I D` of the algebra of smooth functions. For a real polarization of a
symplectic manifold this is the algebra `A_P` of geometric quantization, which acts on the
observables preserving the polarization
(`TauCeti.Geometry.Symplectic.Polarization.Observable`).

## Main definitions

* `TauCeti.basicFunctions I D`: the subalgebra of smooth functions whose differential annihilates
  `D`.

## Main results

* `TauCeti.mem_basicFunctions_iff`: the defining property.
* `TauCeti.basicFunctions_bot`: every smooth function is basic for the zero distribution.
* `TauCeti.mem_basicFunctions_top_iff`: for the whole tangent bundle, the basic functions are the
  smooth functions with vanishing differential.
* `TauCeti.basicFunctions_antitone`: a larger distribution has fewer basic functions.

## References

* P. Molino, *Riemannian Foliations*, Birkhäuser, 1988, Section 2.1 (basic functions of a
  foliation).
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- The **basic functions** of a distribution `D`: the smooth functions `a` whose differential
annihilates `D`, `da_x(v) = 0` for every `v ∈ D x`. They form a subalgebra of the smooth
functions. -/
def basicFunctions (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    Subalgebra 𝕜 C^∞⟮I, M; 𝕜⟯ where
  carrier := {a | ∀ x, ∀ v ∈ D x, mvfderiv I a x v = 0}
  mul_mem' {a b} ha hb x v hv := by
    simp [mvfderiv_mul a.mdifferentiableAt b.mdifferentiableAt, ha x v hv, hb x v hv]
  add_mem' {a b} ha hb x v hv := by
    simp [mvfderiv_add a.mdifferentiableAt b.mdifferentiableAt, ha x v hv, hb x v hv]
  algebraMap_mem' c x v _ := by
    simp [Algebra.algebraMap_eq_smul_one, Pi.one_def, Pi.smul_def, mvfderiv_const]

variable {D D' : Π x : M, Submodule 𝕜 (TangentSpace I x)} {a : C^∞⟮I, M; 𝕜⟯}

/-- A smooth function is basic for `D` when its differential annihilates `D`. -/
@[simp]
theorem mem_basicFunctions_iff :
    a ∈ basicFunctions I D ↔ ∀ x, ∀ v ∈ D x, mvfderiv I a x v = 0 :=
  Iff.rfl

/-- The differential of a basic function annihilates the distribution. -/
theorem mvfderiv_apply_eq_zero_of_mem_basicFunctions (ha : a ∈ basicFunctions I D) {x : M}
    {v : TangentSpace I x} (hv : v ∈ D x) : mvfderiv I a x v = 0 :=
  ha x v hv

/-- A larger distribution has fewer basic functions. -/
theorem basicFunctions_antitone :
    Antitone (basicFunctions I : (Π x : M, Submodule 𝕜 (TangentSpace I x)) → _) :=
  fun _ _ h _ ha x v hv ↦ ha x v (h x hv)

/-- Every smooth function is basic for the zero distribution. -/
@[simp]
theorem basicFunctions_bot : basicFunctions I (fun _ : M ↦ ⊥) = ⊤ :=
  eq_top_iff.2 fun _ _ x v hv ↦ by rw [(Submodule.mem_bot 𝕜).1 hv, map_zero]

/-- The basic functions of the whole tangent bundle are the smooth functions with vanishing
differential. -/
theorem mem_basicFunctions_top_iff :
    a ∈ basicFunctions I (fun _ : M ↦ ⊤) ↔ ∀ x, mvfderiv I a x = 0 := by
  simp only [mem_basicFunctions_iff, Submodule.mem_top, forall_const,
    ContinuousLinearMap.ext_iff, zero_apply]

end TauCeti
