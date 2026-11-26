/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Int.Basic
public import TauCeti.LinearAlgebra.FreeModule.Filtration

/-!
# Submodules of free modules with a countable basis over a PID

Over a principal ideal domain `R`, every submodule of a free module with a countable basis is free.
Mathlib proves this for free modules of finite rank (`Submodule.basisOfPid`); the countable case is
what the free presentations of countable abelian groups use.

Enumerate the basis `b` injectively by `enc : ι → ℕ` and filter `M` by the spans
`Mₙ = span {b i | enc i < n}`. A submodule `N` is filtered by `N ∩ Mₙ`; the successive quotient
`(N ∩ Mₙ₊₁) ⧸ (N ∩ Mₙ)` is zero when `n` is not in the range of `enc`, and is otherwise carried
injectively by the `i`-th coordinate (`enc i = n`) onto an ideal of `R`, which is free. The
filtration criterion `Module.Free.of_filtration` then makes `N` free; no finiteness is assumed.

## Main declarations

* `Module.Free.submodule_of_basis`: a submodule of a module with a countable basis over a PID is
  free.
* `Module.Free.submodule_of_countable`: the same for free modules whose chosen basis is indexed by
  a countable type, in particular (`Module.Free.submodule_of_countable'`) for countable free
  modules.
* `AddSubgroup.free_of_countable`: every subgroup of a countable free abelian group is free.

## References

The OperatorKTheory roadmap, K8.2 ("Prove freeness of subgroups of countable free abelian
groups").
-/

public section

namespace Module.Free

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- **Submodules of countable-rank free modules over a PID are free.** If `M` has a basis indexed
by a countable type, every submodule of `M` is free. -/
theorem submodule_of_basis {ι : Type*} [Countable ι] (b : Basis ι R M) (N : Submodule R M) :
    Module.Free R N := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat ι
  -- The filtration of `M` by the spans of the first basis vectors, restricted to `N`.
  let F : ℕ → Submodule R M := fun n ↦ Submodule.span R (b '' {i | enc i < n})
  have hF (n : ℕ) (x : M) : x ∈ F n ↔ ∀ i ∈ (b.repr x).support, enc i < n :=
    b.mem_span_image.trans ⟨fun h i hi ↦ h hi, fun h i hi ↦ h i hi⟩
  let G : ℕ → Submodule R N := fun n ↦ (F n).comap N.subtype
  have hG (n : ℕ) (x : N) : x ∈ G n ↔ ∀ i ∈ (b.repr x).support, enc i < n := hF n x
  have hGmono : Monotone G := fun m n hmn x hx ↦
    (hG n x).2 fun i hi ↦ ((hG m x).1 hx i hi).trans_le hmn
  refine of_filtration G hGmono ?_ ?_ fun n ↦ ?_
  · -- The first step is zero.
    have : Subsingleton (G 0) := by
      refine ⟨fun x y ↦ Subtype.ext ?_⟩
      have h0 (z : G 0) : (z : N) = 0 := by
        have hz := (hG 0 z).1 z.property
        refine Subtype.ext (b.repr.injective ?_)
        rw [Submodule.coe_zero, map_zero, ← Finsupp.support_eq_empty]
        exact Finset.eq_empty_of_forall_notMem fun i hi ↦ Nat.not_lt_zero _ (hz i hi)
      rw [h0 x, h0 y]
    infer_instance
  · -- Every element lies in some step of the filtration.
    refine eq_top_iff.2 fun x _ ↦ Submodule.mem_iSup_of_mem
      ((b.repr x).support.sup enc + 1) ((hG _ x).2 fun i hi ↦ Nat.lt_succ_of_le ?_)
    exact Finset.le_sup (f := enc) hi
  · by_cases hn : ∃ i, enc i = n
    · -- The `i`-th coordinate embeds the successive quotient into `R`.
      obtain ⟨i, rfl⟩ := hn
      let f : G (enc i + 1) →ₗ[R] R := b.coord i ∘ₗ N.subtype ∘ₗ (G (enc i + 1)).subtype
      have hker : LinearMap.ker f = (G (enc i)).submoduleOf (G (enc i + 1)) := by
        ext x
        simp only [LinearMap.mem_ker, Submodule.submoduleOf, Submodule.mem_comap,
          Submodule.coe_subtype, f, LinearMap.coe_comp, Function.comp_apply, Basis.coord_apply]
        have hx := (hG _ x.val).1 x.property
        refine ⟨fun h ↦ (hG _ x.val).2 fun j hj ↦ ?_, fun h ↦ ?_⟩
        · refine lt_of_le_of_ne (Nat.lt_succ_iff.1 (hx j hj)) fun hji ↦ ?_
          rw [henc hji] at hj
          exact (Finsupp.mem_support_iff.1 hj) h
        · by_contra hi
          exact lt_irrefl _ ((hG _ x.val).1 h i (Finsupp.mem_support_iff.2 hi))
      exact .of_equiv ((Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange).symm
    · -- Otherwise the successive quotient is zero.
      push Not at hn
      have hle : G (n + 1) ≤ G n := fun x hx ↦ (hG n x).2 fun i hi ↦
        lt_of_le_of_ne (Nat.lt_succ_iff.1 ((hG _ x).1 hx i hi)) (hn i)
      have : Subsingleton (G (n + 1) ⧸ (G n).submoduleOf (G (n + 1))) :=
        Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ ↦ hle x.property)
      infer_instance

/-- Over a PID, every submodule of a free module whose chosen basis is indexed by a countable type
is free. -/
theorem submodule_of_countable [Module.Free R M] [Countable (ChooseBasisIndex R M)]
    (N : Submodule R M) : Module.Free R N :=
  submodule_of_basis (chooseBasis R M) N

/-- Over a PID, every submodule of a countable free module is free. -/
theorem submodule_of_countable' [Module.Free R M] [Countable M] (N : Submodule R M) :
    Module.Free R N :=
  have : Countable (ChooseBasisIndex R M) := (chooseBasis R M).injective.countable
  submodule_of_countable N

end Module.Free

/-- **Subgroups of countable free abelian groups are free.** -/
theorem AddSubgroup.free_of_countable {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Countable G]
    (H : AddSubgroup G) : Module.Free ℤ H :=
  Module.Free.submodule_of_countable' H.toIntSubmodule
