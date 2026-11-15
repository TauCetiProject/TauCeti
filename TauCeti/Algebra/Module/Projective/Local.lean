/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.LocalRing.Defs
public import TauCeti.LinearAlgebra.End.Basic

/-!
# Projective modules with local endomorphism rings

Let `P` be a projective module whose endomorphism ring is local. Then the sum of two proper
submodules of `P` is proper: if `N ⊔ N' = P`, the surjection `N × N' ⟶ P` splits since `P` is
projective, writing the identity of `P` as `a + b` with `a` factoring through `N` and `b` through
`N'`; as `End P` is local, `a` or `b` is invertible, so `N` or `N'` is all of `P`.

Consequently every proper submodule lies in the radical `Module.jacobson R P`, and a finitely
generated such module is *local*: its radical is its unique maximal submodule.

## Main results

* `Module.Projective.sup_ne_top_of_isLocalRing_end`: the sum of two proper submodules is proper.
* `Module.Projective.le_jacobson_of_isLocalRing_end`: every proper submodule lies in the radical.
* `Module.Projective.isCoatom_jacobson_of_isLocalRing_end`: for `P` finitely generated, the radical
  is the unique maximal submodule.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001), (21.18)
  and the proof of Theorem (23.6).
-/

public section

namespace Module.Projective

section Semiring

variable {R P : Type*} [Semiring R] [AddCommMonoid P] [Module R P] [Module.Projective R P]
  [IsLocalRing (Module.End R P)]

/-- **In a projective module with local endomorphism ring, the sum of two proper submodules is
proper.** -/
theorem sup_ne_top_of_isLocalRing_end {N N' : Submodule R P} (hN : N ≠ ⊤) (hN' : N' ≠ ⊤) :
    N ⊔ N' ≠ ⊤ := by
  intro h
  -- The surjection `N × N' ⟶ P` splits, as `P` is projective.
  let f : (N × N') →ₗ[R] P := N.subtype.coprod N'.subtype
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, Submodule.range_subtype,
      Submodule.range_subtype, h]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let a : Module.End R P := N.subtype ∘ₗ LinearMap.fst R N N' ∘ₗ s
  let b : Module.End R P := N'.subtype ∘ₗ LinearMap.snd R N N' ∘ₗ s
  have hab : a + b = 1 := by
    ext x
    simpa [a, b, f] using LinearMap.congr_fun hs x
  -- As `End P` is local, `a` or `b` is invertible, hence onto.
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with ha | hb
  · refine hN (eq_top_iff.2 fun x _ ↦ ?_)
    obtain ⟨y, rfl⟩ := ((Module.End.isUnit_iff a).1 ha).2 x
    exact (s y).1.2
  · refine hN' (eq_top_iff.2 fun x _ ↦ ?_)
    obtain ⟨y, rfl⟩ := ((Module.End.isUnit_iff b).1 hb).2 x
    exact (s y).2.2

end Semiring

variable {R P : Type*} [Ring R] [AddCommGroup P] [Module R P] [Module.Projective R P]
  [IsLocalRing (Module.End R P)]

/-- In a projective module with local endomorphism ring, every proper submodule lies in the
radical: a proper submodule not below a maximal submodule `M` would sum with `M` to the whole
module. -/
theorem le_jacobson_of_isLocalRing_end {N : Submodule R P} (hN : N ≠ ⊤) :
    N ≤ Module.jacobson R P := by
  refine le_sInf fun M (hM : IsCoatom M) ↦ ?_
  by_contra hNM
  exact sup_ne_top_of_isLocalRing_end hN hM.1
    (hM.2 _ (lt_of_le_of_ne le_sup_right fun h ↦ hNM (h ▸ le_sup_left)))

/-- **A finitely generated projective module with local endomorphism ring is local**: its radical
is its unique maximal submodule. -/
theorem isCoatom_jacobson_of_isLocalRing_end [Module.Finite R P] :
    IsCoatom (Module.jacobson R P) := by
  have : Nontrivial P := TauCeti.nontrivial_of_nontrivial_end (R := R)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R P)).resolve_left bot_ne_top
  have hle : M ≤ Module.jacobson R P := le_jacobson_of_isLocalRing_end hM.1
  have hge : Module.jacobson R P ≤ M := sInf_le hM
  exact le_antisymm hge hle ▸ hM

end Module.Projective
