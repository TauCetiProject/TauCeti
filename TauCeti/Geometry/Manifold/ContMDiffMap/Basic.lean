/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Basic lemmas on bundled `C^n` maps

This file evaluates Mathlib's basic bundled `C^n` maps (`ContMDiffMap.id`, `ContMDiffMap.const`,
`ContMDiffMap.fst`, `ContMDiffMap.snd`, and `ContMDiffMap.prodMk`) pointwise.
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-- The identity `C^n` map evaluates to the identity at every point. -/
@[simp, grind =]
theorem id_apply (x : M) : (ContMDiffMap.id : C^n⟮I, M; I, M⟯) x = x :=
  rfl

/-- The constant `C^n` map with value `y` takes the value `y` at every point. -/
@[simp, grind =]
theorem const_apply (y : M') (x : M) : (const y : C^n⟮I, M; I', M'⟯) x = y :=
  rfl

/-- The first projection `C^n` map evaluates to `Prod.fst`. -/
@[simp, grind =]
theorem fst_apply (p : M × M') : (fst : C^n⟮I.prod I', M × M'; I, M⟯) p = p.1 :=
  rfl

/-- The second projection `C^n` map evaluates to `Prod.snd`. -/
@[simp, grind =]
theorem snd_apply (p : M × M') : (snd : C^n⟮I.prod I', M × M'; I', M'⟯) p = p.2 :=
  rfl

/-- The product of two `C^n` maps evaluates to the pair of their values. -/
@[simp, grind =]
theorem prodMk_apply (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) (x : N) :
    f.prodMk g x = (f x, g x) :=
  rfl

end ContMDiffMap
