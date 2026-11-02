/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Products of `C^n` maps on finite products

A finite family of maps `f i : E i → F i`, each `C^n` on a set `s i`, assembles into the map
`Pi.map f : (∀ i, E i) → (∀ i, F i)`, `x ↦ (f i (x i))ᵢ`, which is `C^n` on the product set
`univ.pi s`. This is the finite-product analogue of `ContDiffOn.prodMap`; it shows that the
transition maps of product charts of finitely many manifolds are `C^n`.

## Main declarations

* `ContDiffOn.piMap`: a finite product of maps `C^n` on sets is `C^n` on the product set.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)] {n : WithTop ℕ∞}

/-- A finite product of maps, each `C^n` on a set, is `C^n` on the product of these sets. -/
theorem ContDiffOn.piMap {f : ∀ i, E i → F i} {s : ∀ i, Set (E i)}
    (hf : ∀ i, ContDiffOn 𝕜 n (f i) (s i)) : ContDiffOn 𝕜 n (Pi.map f) (univ.pi s) :=
  contDiffOn_pi.2 fun i ↦ (hf i).comp (contDiff_apply 𝕜 (F' := E) i).contDiffOn
    fun _ hx ↦ hx i (mem_univ i)
