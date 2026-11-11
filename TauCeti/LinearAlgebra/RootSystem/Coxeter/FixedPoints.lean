/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.LinearAlgebra.Reflection
import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

/-!
# Fixed vectors of Coxeter elements of a Weyl group

Let `b` be a base of a root pairing. A word in the simple reflections of `b` that uses each simple
reflection at most once spells an element whose fixed vectors are exactly the vectors killed by
the simple coroots of its letters: if `s_{i₁} ⋯ s_{iₖ} x = x` with distinct `iⱼ`, then
`⟨x, α_{iⱼ}^∨⟩ = 0` for every `j`. The reason is that `s_{i₁} ⋯ s_{iₖ} x - x` is a combination of
the simple roots `α_{iⱼ}` in which the coefficient of `α_{i₁}` is `-⟨s_{i₂} ⋯ s_{iₖ} x, α_{i₁}^∨⟩`,
and the simple roots are linearly independent
(`Module.list_prod_map_preReflection_apply_eq_self_iff`).

A *Coxeter element* is the product of all the simple reflections, each exactly once, in some
order. Its fixed vectors are the vectors killed by every simple coroot, hence by every coroot, and
these are exactly the vectors fixed by the whole Weyl group. For a root system the coroots separate
the vectors, so a Coxeter element fixes no nonzero vector: `1` is not an eigenvalue of a Coxeter
element on the reflection representation. This holds for every ordering of the simple
reflections, with no finiteness, crystallographic or reducedness hypothesis. For a finite Weyl
group, where a Coxeter element has finite order `h` and so its eigenvalues have the form
`exp (2πi e / h)` with `0 ≤ e < h`, it excludes `e = 0`.

## Main results

* `TauCeti.wordProd_smul_eq_self_iff`: a product of distinct simple reflections fixes `x` exactly
  when the simple coroots of its letters vanish on `x`.
* `TauCeti.wordProd_smul_eq_self_iff_forall_coroot'_eq_zero` and
  `TauCeti.wordProd_smul_eq_self_iff_forall_smul_eq_self`: a Coxeter element fixes `x` exactly when
  every coroot vanishes on `x`, that is, exactly when the whole Weyl group fixes `x`.
* `TauCeti.wordProd_smul_eq_self_iff_eq_zero` and `TauCeti.not_hasEigenvalue_one_wordProd`: for a
  root system, a Coxeter element fixes no nonzero vector, so `1` is not one of its eigenvalues.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

namespace TauCeti

open RootPairing Submodule

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

/-- A word in the simple reflections acts on the weight space as the product of the corresponding
reflections `y ↦ y - ⟨y, αᵢ^∨⟩ • αᵢ`, in the same order. -/
theorem wordProd_smul_eq_list_prod_map_preReflection (l : List b.support) (y : M) :
    wordProd P b l • y =
      (l.map fun i : b.support ↦ Module.preReflection (P.root i) (P.coroot' i)).prod y := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wordProd_cons, mul_smul, ih, weylGroup.ofIdx_smul, Equiv.reflection_smul,
      reflection_apply, List.map_cons, List.prod_cons, mul_apply_eq_comp,
      Module.preReflection_apply]

/-- **Fixed vectors of a product of distinct simple reflections.** A word in the simple
reflections of a base, with no letter repeated, spells an element fixing `y` exactly when the
simple coroots of its letters all vanish on `y`. -/
theorem wordProd_smul_eq_self_iff {l : List b.support} (hl : l.Nodup) {y : M} :
    wordProd P b l • y = y ↔ ∀ i ∈ l, P.coroot' i y = 0 := by
  rw [wordProd_smul_eq_list_prod_map_preReflection]
  exact Module.list_prod_map_preReflection_apply_eq_self_iff b.linearIndepOn_root hl

/-- **Fixed vectors of a Coxeter element.** A product of all the simple reflections of a base, each
exactly once and in any order, fixes `y` exactly when every coroot vanishes on `y`. -/
theorem wordProd_smul_eq_self_iff_forall_coroot'_eq_zero {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) {y : M} :
    wordProd P b l • y = y ↔ ∀ j, P.coroot' j y = 0 := by
  rw [wordProd_smul_eq_self_iff b hl]
  exact ⟨fun h ↦ P.coroot'_eq_zero_of_forall_mem_support b fun i hi ↦ h ⟨i, hi⟩ (hl' _),
    fun h i _ ↦ h i⟩

/-- **A Coxeter element has the same fixed vectors as the Weyl group.** A product of all the simple
reflections of a base, each exactly once and in any order, fixes `y` exactly when every element of
the Weyl group fixes `y`. -/
theorem wordProd_smul_eq_self_iff_forall_smul_eq_self {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) {y : M} :
    wordProd P b l • y = y ↔ ∀ w : P.weylGroup, w • y = y :=
  ⟨fun h ↦ smul_eq_self_of_forall_coroot'_eq_zero b fun i hi ↦
    (wordProd_smul_eq_self_iff b hl).mp h ⟨i, hi⟩ (hl' _), fun h ↦ h _⟩

/-- **A Coxeter element of a root system fixes no nonzero vector.** For a root system, a product
of all the simple reflections of a base, each exactly once and in any order, fixes only `0`. -/
theorem wordProd_smul_eq_self_iff_eq_zero [P.IsRootSystem] {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) {y : M} :
    wordProd P b l • y = y ↔ y = 0 := by
  rw [wordProd_smul_eq_self_iff_forall_coroot'_eq_zero b hl hl',
    P.eq_zero_iff_forall_coroot'_eq_zero]

/-- **`1` is not an eigenvalue of a Coxeter element.** For a root system, a product of all the
simple reflections of a base, each exactly once and in any order, does not have `1` as an
eigenvalue on the weight space. -/
theorem not_hasEigenvalue_one_wordProd [P.IsRootSystem] {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) :
    ¬ Module.End.HasEigenvalue (P.weylGroupRootRep (wordProd P b l)) 1 := by
  rw [Module.End.hasEigenvalue_iff, not_ne_iff, eq_bot_iff]
  intro y hy
  rw [Module.End.mem_eigenspace_iff, one_smul, weylGroupRootRep,
    Representation.ofDistribMulAction_apply_apply, wordProd_smul_eq_self_iff_eq_zero b hl hl'] at hy
  exact (mem_bot R).mpr hy

end TauCeti
