/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Fibrewise linear partial diffeomorphisms

Let `L : M → F₁ →L[𝕜] F₂` be a `C^n` family of invertible continuous linear maps on an open subset
`s` of a charted space `M`, where `F₁` is a Banach space and `F₂` is a normed space. Operator
inversion is `C^n` on invertible operators
(`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), so the fibrewise inverses
`x ↦ (L x).inverse` also form a `C^n` family on `s`. Consequently, the map `(x, v) ↦ (x, L x v)`
defines a `C^n` partial diffeomorphism `TauCeti.fiberwiseLinearPartialDiffeomorph` from
`s ×ˢ univ ⊆ M × F₁` onto `s ×ˢ univ ⊆ M × F₂`, with inverse `(x, w) ↦ (x, (L x).inverse w)`.

Unlike `FiberwiseLinear.openPartialHomeomorph`, the family need only be `C^n` in the forward
direction and invertible on `s`, and the source and target fibres `F₁` and `F₂` need not coincide.
In parameterized normal-form constructions (such as straightening a `C^n` vector subbundle in
bundle trivializations using a fixed complement), this turns a `C^n` family of split injections
completed by a complement into a local `C^n` coordinate change on the trivialized bundle.

## Main definitions and results

* `TauCeti.fiberwiseLinearPartialDiffeomorph`: the `C^n` partial diffeomorphism
  `(x, v) ↦ (x, L x v)` from `M × F₁` to `M × F₂` over `s ×ˢ univ`.
* `TauCeti.fiberwiseLinearPartialDiffeomorph_source`,
  `TauCeti.fiberwiseLinearPartialDiffeomorph_target`,
  `TauCeti.fiberwiseLinearPartialDiffeomorph_apply`,
  `TauCeti.fiberwiseLinearPartialDiffeomorph_symm_apply`,
  `TauCeti.fiberwiseLinearPartialDiffeomorph_toPartialEquiv_symm_apply`: characteristic lemmas for
  its source, target, forward map, and inverse map.

## Formal sources

This is the `PartialDiffeomorph` counterpart of `FiberwiseLinear.openPartialHomeomorph` in
`Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear`, by Floris van Doorn and Heather Macbeth,
inferring inverse regularity from `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` and
allowing distinct source and target fibres.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {n : ℕ∞ω}

variable [CompleteSpace F₁] (L : M → F₁ →L[𝕜] F₂) {s : Set M} (hs : IsOpen s)
  (hL : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n L s) (hInv : ∀ x ∈ s, (L x).IsInvertible)

/-- A `C^n` family of invertible continuous linear maps `L : M → F₁ →L[𝕜] F₂` on an open set
`s ⊆ M`, with `F₁` complete, defines a `C^n` partial diffeomorphism `(x, v) ↦ (x, L x v)` from
`s ×ˢ univ ⊆ M × F₁` onto `s ×ˢ univ ⊆ M × F₂` with inverse `(x, w) ↦ (x, (L x).inverse w)`. -/
def fiberwiseLinearPartialDiffeomorph :
    PartialDiffeomorph (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₂)) (M × F₁) (M × F₂) n where
  toFun p := (p.1, L p.1 p.2)
  invFun q := (q.1, (L q.1).inverse q.2)
  source := s ×ˢ univ
  target := s ×ˢ univ
  map_source' _ hp := ⟨hp.1, mem_univ _⟩
  map_target' _ hq := ⟨hq.1, mem_univ _⟩
  left_inv' p hp := Prod.ext rfl ((hInv p.1 hp.1).inverse_apply_self p.2)
  right_inv' q hq := Prod.ext rfl ((hInv q.1 hq.1).self_apply_inverse q.2)
  open_source := hs.prod isOpen_univ
  open_target := hs.prod isOpen_univ
  contMDiffOn_toFun :=
    contMDiffOn_fst.prodMk
      ((hL.comp (s := s ×ˢ univ) contMDiffOn_fst fun _ hp ↦ hp.1).clm_apply contMDiffOn_snd)
  contMDiffOn_invFun := by
    have hinv : ContMDiffOn (I.prod 𝓘(𝕜, F₂)) 𝓘(𝕜, F₂ →L[𝕜] F₁) n
        (fun q : M × F₂ ↦ (L q.1).inverse) (s ×ˢ univ) :=
      fun q hq ↦ (hInv q.1 hq.1).contDiffAt_map_inverse.contMDiffAt.comp_contMDiffWithinAt q
        ((hL.comp (s := s ×ˢ univ) contMDiffOn_fst fun _ hr ↦ hr.1) q hq)
    exact contMDiffOn_fst.prodMk (hinv.clm_apply contMDiffOn_snd)

/-- The source of `fiberwiseLinearPartialDiffeomorph L hs hL hInv` is `s ×ˢ univ`. -/
@[simp]
theorem fiberwiseLinearPartialDiffeomorph_source :
    (fiberwiseLinearPartialDiffeomorph L hs hL hInv).source = s ×ˢ univ := (rfl)

/-- The target of `fiberwiseLinearPartialDiffeomorph L hs hL hInv` is `s ×ˢ univ`. -/
@[simp]
theorem fiberwiseLinearPartialDiffeomorph_target :
    (fiberwiseLinearPartialDiffeomorph L hs hL hInv).target = s ×ˢ univ := (rfl)

/-- `fiberwiseLinearPartialDiffeomorph` preserves the first coordinate and applies `L` to the
second coordinate. -/
@[simp]
theorem fiberwiseLinearPartialDiffeomorph_apply (p : M × F₁) :
    fiberwiseLinearPartialDiffeomorph L hs hL hInv p = (p.1, L p.1 p.2) := (rfl)

/-- The inverse partial diffeomorphism of `fiberwiseLinearPartialDiffeomorph` preserves the first
coordinate and applies `(L ·).inverse` to the second coordinate. -/
theorem fiberwiseLinearPartialDiffeomorph_symm_apply (q : M × F₂) :
    (fiberwiseLinearPartialDiffeomorph L hs hL hInv).symm q = (q.1, (L q.1).inverse q.2) := (rfl)

/-- The inverse of the underlying `PartialEquiv` of `fiberwiseLinearPartialDiffeomorph` preserves
the first coordinate and applies `(L ·).inverse` to the second coordinate. -/
@[simp]
theorem fiberwiseLinearPartialDiffeomorph_toPartialEquiv_symm_apply (q : M × F₂) :
    (fiberwiseLinearPartialDiffeomorph L hs hL hInv).toPartialEquiv.symm q =
      (q.1, (L q.1).inverse q.2) := (rfl)

end TauCeti
