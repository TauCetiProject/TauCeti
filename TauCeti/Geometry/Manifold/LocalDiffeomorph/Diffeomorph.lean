/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Composing local diffeomorphisms with diffeomorphisms

Precomposing or postcomposing a map with a `C^n` diffeomorphism preserves and reflects being a
`C^m` local diffeomorphism (`m ≤ n`), at a point, on a set, or globally. These equivalences mirror
Mathlib's `Diffeomorph.contMDiffAt_comp_diffeomorph_iff` family and require neither `IsManifold`
nor boundarylessness hypotheses.

## Main results

* `Diffeomorph.isLocalDiffeomorph_of_le`: a `C^n` diffeomorphism is a `C^m` local diffeomorphism
  for `m ≤ n`.
* `Diffeomorph.isLocalDiffeomorphAt_comp_diffeomorph_iff`,
  `Diffeomorph.isLocalDiffeomorphOn_comp_diffeomorph_iff`,
  `Diffeomorph.isLocalDiffeomorph_comp_diffeomorph_iff`: precomposing with a diffeomorphism.
* `Diffeomorph.isLocalDiffeomorphAt_diffeomorph_comp_iff`,
  `Diffeomorph.isLocalDiffeomorphOn_diffeomorph_comp_iff`,
  `Diffeomorph.isLocalDiffeomorph_diffeomorph_comp_iff`: postcomposing with a diffeomorphism.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 2.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n m : ℕ∞ω}

/-- View a `C^n` diffeomorphism as a `C^m` diffeomorphism for `m ≤ n`. -/
private def ofLe (h : M ≃ₘ^n⟮I, J⟯ N) (hm : m ≤ n) : M ≃ₘ^m⟮I, J⟯ N where
  toEquiv := h.toEquiv
  contMDiff_toFun := h.contMDiff.of_le hm
  contMDiff_invFun := h.symm.contMDiff.of_le hm

/-- A `C^n` diffeomorphism is a `C^m` local diffeomorphism for every `m ≤ n`. -/
theorem isLocalDiffeomorph_of_le (h : M ≃ₘ^n⟮I, J⟯ N) (hm : m ≤ n) :
    IsLocalDiffeomorph I J m h :=
  (h.ofLe hm).isLocalDiffeomorph

/-- Precomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism at `x`,
for `m ≤ n`, if and only if the map is a `C^m` local diffeomorphism at `h x`. -/
@[simp]
theorem isLocalDiffeomorphAt_comp_diffeomorph_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → P} {x : M}
    (hm : m ≤ n) :
    IsLocalDiffeomorphAt I K m (f ∘ h) x ↔ IsLocalDiffeomorphAt J K m f (h x) := by
  refine ⟨fun hfh ↦ ?_, fun hf ↦ (h.isLocalDiffeomorph_of_le hm x).comp (hg := hf)⟩
  have hfh' : IsLocalDiffeomorphAt I K m (f ∘ h) (h.symm (h x)) := by
    rwa [h.symm_apply_apply]
  have hcomp := (h.symm.isLocalDiffeomorph_of_le hm (h x)).comp (hg := hfh')
  have heq : (f ∘ ⇑h) ∘ ⇑h.symm = f := funext fun y ↦ congrArg f (h.apply_symm_apply y)
  rwa [heq] at hcomp

/-- Precomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism on `s`,
for `m ≤ n`, if and only if the map is a `C^m` local diffeomorphism on `h.symm ⁻¹' s`. -/
@[simp]
theorem isLocalDiffeomorphOn_comp_diffeomorph_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → P} {s : Set M}
    (hm : m ≤ n) :
    IsLocalDiffeomorphOn I K m (f ∘ h) s ↔ IsLocalDiffeomorphOn J K m f (h.symm ⁻¹' s) := by
  constructor
  · rintro hf ⟨y, hy⟩
    simpa only [h.apply_symm_apply] using
      (h.isLocalDiffeomorphAt_comp_diffeomorph_iff (f := f) (x := h.symm y) hm).1
        (hf ⟨h.symm y, hy⟩)
  · rintro hf ⟨x, hx⟩
    exact (h.isLocalDiffeomorphAt_comp_diffeomorph_iff (f := f) (x := x) hm).2
      (hf ⟨h x, by simpa only [mem_preimage, h.symm_apply_apply] using hx⟩)

/-- Precomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism, for
`m ≤ n`, if and only if the map is a `C^m` local diffeomorphism. -/
@[simp]
theorem isLocalDiffeomorph_comp_diffeomorph_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : N → P} (hm : m ≤ n) :
    IsLocalDiffeomorph I K m (f ∘ h) ↔ IsLocalDiffeomorph J K m f :=
  h.toEquiv.forall_congr fun _ ↦ h.isLocalDiffeomorphAt_comp_diffeomorph_iff hm

/-- Postcomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism at `x`,
for `m ≤ n`, if and only if the map is a `C^m` local diffeomorphism at `x`. -/
@[simp]
theorem isLocalDiffeomorphAt_diffeomorph_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : P → M} (hm : m ≤ n)
    {x : P} :
    IsLocalDiffeomorphAt K J m (h ∘ f) x ↔ IsLocalDiffeomorphAt K I m f x := by
  refine ⟨fun hhf ↦ ?_, fun hf ↦ hf.comp (hg := h.isLocalDiffeomorph_of_le hm (f x))⟩
  have hcomp := hhf.comp (hg := h.symm.isLocalDiffeomorph_of_le hm (h (f x)))
  have heq : ⇑h.symm ∘ (⇑h ∘ f) = f := funext fun y ↦ h.symm_apply_apply (f y)
  rwa [heq] at hcomp

/-- Postcomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism on `s`,
for `m ≤ n`, if and only if the map is a `C^m` local diffeomorphism on `s`. -/
@[simp]
theorem isLocalDiffeomorphOn_diffeomorph_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : P → M} (hm : m ≤ n)
    {s : Set P} :
    IsLocalDiffeomorphOn K J m (h ∘ f) s ↔ IsLocalDiffeomorphOn K I m f s :=
  forall_congr' fun _ ↦ h.isLocalDiffeomorphAt_diffeomorph_comp_iff hm

/-- Postcomposing a map with a `C^n` diffeomorphism `h` is a `C^m` local diffeomorphism, for
`m ≤ n`, if and only if the map is a `C^m` local diffeomorphism. -/
@[simp]
theorem isLocalDiffeomorph_diffeomorph_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) {f : P → M} (hm : m ≤ n) :
    IsLocalDiffeomorph K J m (h ∘ f) ↔ IsLocalDiffeomorph K I m f :=
  forall_congr' fun _ ↦ h.isLocalDiffeomorphAt_diffeomorph_comp_iff hm

end Diffeomorph
