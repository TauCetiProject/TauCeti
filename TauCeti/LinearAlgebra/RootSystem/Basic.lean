/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Module

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root pairing or root system that need no further
theory.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
* `RootPairing.linearIndependent_root_reflection_iff` and
  `RootPairing.linearIndependent_root_reflectionPerm_iff`: reflecting across a root preserves and
  reflects linear independence with that root.
* `RootPairing.exists_root'_eq_zero_and_eq_one`: for two linearly independent roots over a field,
  some coweight pairs to `0` with the first and to `1` with the second.
* `RootPairing.coroot_eq_smul_of_root_eq_smul`, `RootPairing.reflection_eq_of_root_eq_smul`,
  `RootPairing.coreflection_eq_of_root_eq_smul`, and
  `RootPairing.reflectionPerm_eq_of_root_eq_smul`: proportional roots have inversely proportional
  coroots and induce the same reflection, coreflection, and root-index permutation.
-/

public section

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] :
    Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

private theorem linearIndependent_root_reflection_of_linearIndependent
    (P : RootPairing ι R M N) {i : ι} {x : M} (hli : LinearIndependent R ![P.root i, x]) :
    LinearIndependent R ![P.root i, P.reflection i x] := by
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro c d hcd
  have h1 : (c - d * P.coroot' i x) • P.root i + d • x = 0 := by
    rw [P.reflection_apply] at hcd
    exact (by module : (c - d * P.coroot' i x) • P.root i + d • x =
      c • P.root i + d • (x - P.coroot' i x • P.root i)).trans hcd
  obtain ⟨h2, hd0⟩ := hli _ _ h1
  rw [hd0, zero_mul, sub_zero] at h2
  exact ⟨h2, hd0⟩

/-- Reflecting a weight across a root preserves and reflects linear independence with that root. -/
@[simp]
theorem linearIndependent_root_reflection_iff (P : RootPairing ι R M N) (i : ι) (x : M) :
    LinearIndependent R ![P.root i, P.reflection i x] ↔ LinearIndependent R ![P.root i, x] :=
  ⟨fun h ↦ by
    simpa only [P.reflection_same] using P.linearIndependent_root_reflection_of_linearIndependent h,
    P.linearIndependent_root_reflection_of_linearIndependent⟩

/-- Reflecting one root across another preserves and reflects linear independence of the pair. -/
theorem linearIndependent_root_reflectionPerm_iff (P : RootPairing ι R M N) (i j : ι) :
    LinearIndependent R ![P.root i, P.root (P.reflectionPerm i j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  rw [P.root_reflectionPerm, P.linearIndependent_root_reflection_iff]

section Proportional

variable {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]

/-- If `P.root j = t • P.root i`, then `P.coroot i = t • P.coroot j`. -/
theorem coroot_eq_smul_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coroot i = t • P.coroot j :=
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  have := Module.IsReflexive.of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv M := .of_isTorsionFree R M
  have : HasUniqueDiv N := .of_isTorsionFree R N
  P.coroot_eq_smul_coroot_iff.mpr h

/-- Proportional roots define the same reflection on the weight space. -/
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflection j = P.reflection i := by
  ext x
  simp only [reflection_apply, sub_right_inj, h, smul_smul]
  congr 1
  rw [mul_comm]
  simp [coroot', P.coroot_eq_smul_of_root_eq_smul h]

/-- Proportional roots define the same coreflection on the coweight space. -/
theorem coreflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coreflection j = P.coreflection i :=
  (P.flip.reflection_eq_of_root_eq_smul (P.coroot_eq_smul_of_root_eq_smul h)).symm

/-- Proportional roots induce the same permutation of root indices. -/
theorem reflectionPerm_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflectionPerm j = P.reflectionPerm i := by
  ext k
  refine P.root.injective ?_
  rw [P.root_reflectionPerm, P.root_reflectionPerm, P.reflection_eq_of_root_eq_smul h]

end Proportional

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- For two linearly independent roots of a root pairing over a field, some coweight pairs to `0`
with the first and to `1` with the second. -/
theorem exists_root'_eq_zero_and_eq_one {P : RootPairing ι K M N} {i j : ι}
    (hli : LinearIndependent K ![P.root i, P.root j]) :
    ∃ y : N, P.root' i y = 0 ∧ P.root' j y = 1 := by
  have hnotMem : P.root j ∉ Submodule.span K {P.root i} := fun hmem ↦ by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact neg_ne_zero.mpr one_ne_zero
      (LinearIndependent.pair_iff.mp hli c (-1) (by simp [hc])).2
  obtain ⟨g, hgi, hgj⟩ :=
    LinearMap.exists_extend_of_notMem (0 : Submodule.span K {P.root i} →ₗ[K] K) hnotMem (1 : K)
  exact ⟨P.flip.toPerfPair.symm g,
    by simpa [RootPairing.root'] using congr($hgi ⟨P.root i, Submodule.mem_span_singleton_self _⟩),
    by simpa [RootPairing.root'] using hgj⟩

end Field

end RootPairing
