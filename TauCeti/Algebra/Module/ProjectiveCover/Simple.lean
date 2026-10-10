/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveCover.Basic
public import TauCeti.Algebra.Module.LinearMap.EndQuotient
public import TauCeti.RingTheory.Jacobson.Semiprimary
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Simple heads of indecomposable projective modules

Over a ring with semisimple radical quotient, a projective module with local
endomorphism ring and coatomic submodule lattice has simple head `P / J P`. In particular this
holds for indecomposable projective modules of finite length. Every nonzero map from a module
with simple head into a semisimple module has kernel `J P`. A surjection from such a projective
module with coatomic submodule lattice onto a nonzero semisimple module is a projective cover.
Thus its simple quotient is unique up to isomorphism.

The locality argument uses `Ideal.endMapQ`: projectivity makes reduction of endomorphisms
surjective, so the endomorphism ring of the head is local as well.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., §§23–24.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, §I.4.
-/

public section

namespace TauCeti

variable {R P S : Type*} [Ring R] [AddCommGroup P] [Module R P]
  [AddCommGroup S] [Module R S]

/-- A projective module with local endomorphism ring and coatomic submodule lattice has
simple head, provided the ring's radical quotient is semisimple. -/
theorem isSimpleModule_quotient_jacobson_smul_top_of_isLocalRing_end
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] [IsCoatomic (Submodule R P)]
    [Module.Projective R P] [IsLocalRing (Module.End R P)] :
    IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) := by
  have := nontrivial_of_isLocalRing_end (A := R) (M := P)
  have : Nontrivial (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) :=
    Submodule.Quotient.nontrivial_iff.mpr (Submodule.jacobson_smul_lt_top ⊤).ne
  have := isSemisimpleModule_quotient_smul_top R (Ring.jacobson R) P
  have : IsLocalRing (Module.End R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P))) :=
    IsLocalRing.of_surjective' (Ideal.endMapQ (Ring.jacobson R) P)
      (Ideal.endMapQ_surjective _ _)
  exact isIndecomposableModule_of_isLocalRing_end.isSimpleModule

/-- An indecomposable projective module of finite length has simple head over any ring whose
radical quotient is semisimple. -/
theorem IsIndecomposableModule.isSimpleModule_quotient_jacobson_smul_top
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] [Module.Projective R P]
    (hP : IsIndecomposableModule R P) (hfin : IsFiniteLength R P) :
    IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
  have := isLocalRing_end_of_isIndecomposable hfin hP
  exact isSimpleModule_quotient_jacobson_smul_top_of_isLocalRing_end

/-- If a module has simple head, every nonzero map into a semisimple module has kernel exactly
`J P`. In particular, this identifies all its nonzero semisimple quotients with its head. -/
theorem ker_eq_jacobson_smul_top_of_ne_zero
    [IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P))]
    [IsSemisimpleModule R S] {f : P →ₗ[R] S} (hf : f ≠ 0) :
    LinearMap.ker f = Ring.jacobson R • (⊤ : Submodule R P) := by
  let N := Ring.jacobson R • (⊤ : Submodule R P)
  have hle : N ≤ LinearMap.ker f :=
    (Ring.jacobson_smul_top_le R P).trans (IsSemisimpleModule.jacobson_le_ker R R P S f)
  have hN : IsCoatom N := isSimpleModule_iff_isCoatom.mp inferInstance
  exact (hN.le_iff_eq (LinearMap.ker_eq_top.not.mpr hf)).mp hle

/-- A surjection from a projective module with simple head and coatomic submodule lattice
onto a nonzero semisimple module is a projective cover. -/
theorem isProjectiveCover_of_isSimpleModule_quotient_jacobson_smul_top
    [IsCoatomic (Submodule R P)] [Module.Projective R P]
    [IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P))]
    [IsSemisimpleModule R S] [Nontrivial S] {f : P →ₗ[R] S} (hf : Function.Surjective f) :
    IsProjectiveCover f where
  projective := inferInstance
  surjective := hf
  isSuperfluous_ker := by
    rw [ker_eq_jacobson_smul_top_of_ne_zero (LinearMap.ne_zero_of_surjective hf)]
    exact isSuperfluous_of_le_jacobson (Ring.jacobson_smul_top_le R P)

/-- A projective cover of a simple module is indecomposable. No finiteness or assumption on
the radical of the ring is needed. -/
theorem IsProjectiveCover.isIndecomposableModule [IsSimpleModule R S] {f : P →ₗ[R] S}
    (hf : IsProjectiveCover f) : IsIndecomposableModule R P := by
  have := IsSimpleModule.nontrivial R S
  have : Nontrivial P := hf.surjective.nontrivial
  refine isIndecomposableModule_of_forall_isCompl fun N Q hNQ ↦ ?_
  have hsup : N.map f ⊔ Q.map f = ⊤ := by
    rw [← Submodule.map_sup, hNQ.sup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hf.surjective]
  have htop {L : Submodule R P} (hL : L.map f = ⊤) : L = ⊤ := by
    apply hf.isSuperfluous_ker.eq_top_of_sup_eq_top
    rw [sup_comm, ← Submodule.comap_map_eq, hL, Submodule.comap_top]
  rcases eq_bot_or_eq_top (N.map f) with hN | hN
  · have hQ := htop (by simpa [hN] using hsup)
    exact Or.inl (by simpa [hQ] using hNQ.inf_eq_bot)
  · have hN' := htop hN
    exact Or.inr (by simpa [hN'] using hNQ.inf_eq_bot)

end TauCeti
