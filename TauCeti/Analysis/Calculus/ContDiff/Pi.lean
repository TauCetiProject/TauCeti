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
* `ContDiff.piSingle_apply`, `ContDiff.uncurry_piSingle_apply`: the family which is a `C^n` map
  `f` at one index and zero at the others is `C^n` at every index, and so is its uncurried form
  when `f` is a two-variable map with `C^n` uncurried form.
* `iteratedFDeriv_pi_apply`, `norm_iteratedFDeriv_pi_le`: the iterated derivatives of a map into a
  finite product are computed componentwise, and are bounded by a common bound on those of the
  components.

Replacing one coordinate by a function of the whole argument also preserves smoothness
(`ContDiff.update_self`). This extends the coordinate-replacement argument in
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/CoordinateChange.lean`.
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

open scoped ContDiff

/-- Replacing one coordinate of the argument by a `C^r` function preserves `C^r` regularity. -/
theorem ContDiff.update_self {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    {r : ℕ∞ω} (i : ι) {w : (∀ j, E j) → E i} (hw : ContDiff 𝕜 r w) :
    ContDiff 𝕜 r (fun x ↦ Function.update x i (w x)) := by
  refine contDiff_pi.2 fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hji
  · simpa using hw
  · simpa [Function.update_apply, hji] using contDiff_apply (𝕜 := 𝕜) (F' := E) j

/-- The family which is a `C^n` map `f` at the index `i` and zero at the other indices is `C^n` at
every index. -/
theorem ContDiff.piSingle_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {κ : Type*} [DecidableEq κ]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} (hf : ContDiff 𝕜 n f) (i j : κ) :
    ContDiff 𝕜 n ((Pi.single i f : κ → E → F) j) := by
  rcases eq_or_ne j i with rfl | h
  · simpa using hf
  · rw [Pi.single_eq_of_ne h]
    exact contDiff_const

/-- If the uncurried map `uncurry f` is `C^n`, then so is the uncurried map at every index of the
family which is `f` at the index `i` and zero at the other indices. -/
theorem ContDiff.uncurry_piSingle_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {κ : Type*}
    [DecidableEq κ] {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {f : E → E' → F} (hf : ContDiff 𝕜 n (Function.uncurry f)) (i j : κ) :
    ContDiff 𝕜 n (Function.uncurry ((Pi.single i f : κ → E → E' → F) j)) := by
  rw [Pi.apply_single (fun _ ↦ Function.uncurry) (fun _ ↦ rfl) i f j]
  exact hf.piSingle_apply i j

section IteratedFDeriv

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace 𝕜 (F i)] {f : ∀ i, G → F i} {x : G} {n : ℕ}

/-- The iterated derivative of a map into a finite product is computed componentwise: the `i`-th
component of `Dⁿ (y ↦ (f j y)ⱼ)` is `Dⁿ (f i)`. -/
theorem iteratedFDeriv_pi_apply (hf : ∀ i, ContDiffAt 𝕜 n (f i) x) (m : Fin n → G) (i : ι) :
    iteratedFDeriv 𝕜 n (fun y j ↦ f j y) x m i = iteratedFDeriv 𝕜 n (f i) x m := by
  have h := (ContinuousLinearMap.proj (R := 𝕜) (φ := F) i).iteratedFDeriv_comp_left
    (contDiffAt_pi.2 hf) le_rfl
  exact (congrArg (· m) h).symm

/-- A common bound on the iterated derivatives of the components of a map into a finite product
bounds the iterated derivative of the map, for the supremum norm. -/
theorem norm_iteratedFDeriv_pi_le {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i, ContDiffAt 𝕜 n (f i) x)
    (h : ∀ i, ‖iteratedFDeriv 𝕜 n (f i) x‖ ≤ C) :
    ‖iteratedFDeriv 𝕜 n (fun y j ↦ f j y) x‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun m ↦
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [iteratedFDeriv_pi_apply hf]
  exact ((iteratedFDeriv 𝕜 n (f i) x).le_opNorm m).trans
    (mul_le_mul_of_nonneg_right (h i) (by positivity))

end IteratedFDeriv
