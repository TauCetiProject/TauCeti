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
module with coatomic submodule lattice onto any nonzero module is a projective cover.
Its nonzero semisimple quotients are necessarily simple and unique up to isomorphism. Without any
hypothesis on the ring, every proper submodule of a projective module with local endomorphism ring
lies in its radical.

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

/-- **Every proper submodule of a projective module with local endomorphism ring lies in its
radical.** -/
theorem le_jacobson_of_ne_top_of_isLocalRing_end [Module.Projective R P]
    [IsLocalRing (Module.End R P)] {N : Submodule R P} (hN : N ≠ ⊤) : N ≤ Module.jacobson R P := by
  -- If `N` is not contained in a maximal submodule `K`, then `N` maps onto `P / K`, and
  -- projectivity gives `φ : P ⟶ N ⊆ P` agreeing with the identity modulo `K`. By locality `φ` or
  -- `1 - φ` is invertible; the first forces `N = P`, the second `K = P`.
  refine le_sInf fun K hK ↦ ?_
  by_contra hNK
  have hsup : N ⊔ K = ⊤ := hK.2 _ (lt_of_le_of_ne le_sup_right fun h ↦ hNK (h ▸ le_sup_left))
  have hsurj : Function.Surjective (K.mkQ ∘ₗ N.subtype) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype,
      Submodule.map_mkQ_eq_top, sup_comm, hsup]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property _ K.mkQ hsurj
  let φ : Module.End R P := N.subtype ∘ₗ h
  have hφ (x : P) : (1 - φ) x ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [φ, sub_eq_zero] using LinearMap.congr_fun hh.symm x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self φ with hu | hu
  · refine hN (Submodule.eq_top_iff'.2 fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := (Module.End.isUnit_iff φ).1 hu |>.2 x
    exact (h y).2
  · refine hK.1 (Submodule.eq_top_iff'.2 fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := (Module.End.isUnit_iff _).1 hu |>.2 x
    exact hφ y

/-- A projective module with local endomorphism ring and coatomic submodule lattice has
simple head, provided the ring's radical quotient is semisimple. -/
theorem isSimpleModule_quotient_jacobson_smul_top_of_isLocalRing_end
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] [IsCoatomic (Submodule R P)]
    [Module.Projective R P] [IsLocalRing (Module.End R P)] :
    IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) := by
  have := nontrivial_of_nontrivial_end (R := R) (M := P)
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
onto any nonzero module is a projective cover. -/
theorem isProjectiveCover_of_isSimpleModule_quotient_jacobson_smul_top
    [IsCoatomic (Submodule R P)] [Module.Projective R P]
    [IsSimpleModule R (P ⧸ Ring.jacobson R • (⊤ : Submodule R P))]
    [Nontrivial S] {f : P →ₗ[R] S} (hf : Function.Surjective f) :
    IsProjectiveCover f where
  projective := inferInstance
  surjective := hf
  isSuperfluous_ker := by
    have hJ := isSuperfluous_of_le_jacobson (Ring.jacobson_smul_top_le R P)
    have hcoatom : IsCoatom (Ring.jacobson R • (⊤ : Submodule R P)) :=
      isSimpleModule_iff_isCoatom.mp inferInstance
    have hsup : Ring.jacobson R • (⊤ : Submodule R P) ⊔ LinearMap.ker f ≠ ⊤ := fun h ↦
      (LinearMap.ker_eq_top.not.mpr (LinearMap.ne_zero_of_surjective hf))
        (hJ.eq_top_of_sup_eq_top h)
    exact hJ.mono (le_sup_right.trans ((hcoatom.le_iff_eq hsup).mp le_sup_left).le)

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
