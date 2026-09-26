/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite morphisms of group algebras

For a homomorphism `p : M →* N` of commutative groups, `R[N]` is finite over `R[M]`
through `mapDomainRingHom R p` if the cokernel of `p` is finite. Over a nonzero coefficient
ring the converse holds as well. No injectivity or finite generation of the groups is needed.

Coset representatives span the target as a module over the source. Conversely, the group
algebra of the cokernel is a quotient of the target on which the source acts through its
augmentation, so finiteness forces its standard basis to be finite.

This is the coordinate-ring finiteness criterion for morphisms of diagonalizable groups;
it supplies the finiteness condition in the character description of their isogenies.
-/

public section

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

variable (R : Type*) {M N : Type*} [CommGroup M] [CommGroup N]

/-- Monomials indexed by representatives of the cokernel span the target group
algebra as a module over the source group algebra. -/
theorem span_range_single_quotient_eq_top [CommSemiring R] (p : M →* N)
    (s : N ⧸ p.range → N) (hs : Function.RightInverse s (QuotientGroup.mk' p.range)) :
    let := (mapDomainRingHom R p).toAlgebra
    Submodule.span (MonoidAlgebra R M) (Set.range fun q ↦ single (s q) (1 : R)) =
      (⊤ : Submodule (MonoidAlgebra R M) (MonoidAlgebra R N)) := by
  let := (mapDomainRingHom R p).toAlgebra
  apply top_unique
  intro x hx
  clear hx
  induction x using induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | single n r =>
    have hmem : n / s (QuotientGroup.mk' p.range n) ∈ p.range :=
      QuotientGroup.eq_iff_div_mem.mp (hs (QuotientGroup.mk' p.range n)).symm
    obtain ⟨m, hm⟩ := hmem
    have hn : p m * s (QuotientGroup.mk' p.range n) = n := by
      rw [hm, div_mul_cancel]
    have h := Submodule.smul_mem
      (Submodule.span (MonoidAlgebra R M) (Set.range fun q ↦ single (s q) (1 : R)))
      (single m r) (Submodule.subset_span ⟨QuotientGroup.mk' p.range n, rfl⟩)
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      mapDomainRingHom_apply, mapDomain_single, single_mul_single, mul_one, hn] using h

variable [CommRing R]

/-- A homomorphism of commutative groups with finite cokernel induces a finite morphism of
group algebras, over any commutative coefficient ring. -/
theorem mapDomainRingHom_finite_of_finite_quotient (p : M →* N) [Finite (N ⧸ p.range)] :
    (mapDomainRingHom R p).Finite := by
  classical
  let := (mapDomainRingHom R p).toAlgebra
  apply Module.Finite.of_fg_top
  rw [← span_range_single_quotient_eq_top R p Quotient.out
    (fun q ↦ Quotient.out_eq' q)]
  exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩

/-- Over a nonzero commutative ring, the group-algebra map induced by a homomorphism of
commutative groups is finite exactly when its cokernel is finite. -/
@[simp]
theorem mapDomainRingHom_finite_iff_finite_quotient [Nontrivial R] (p : M →* N) :
    (mapDomainRingHom R p).Finite ↔ Finite (N ⧸ p.range) := by
  constructor
  · intro hp
    let q := QuotientGroup.mk' p.range
    have hq : (mapDomainRingHom R q).Finite :=
      RingHom.Finite.of_surjective _ (mapDomain_surjective (QuotientGroup.mk'_surjective _))
    have hcomp : (mapDomainRingHom R q).comp (mapDomainRingHom R p) =
        (algebraMap R (MonoidAlgebra R (N ⧸ p.range))).comp (augmentation R M) := by
      have hqp (m : M) : (p m : N ⧸ p.range) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨m, rfl⟩
      apply ringHom_ext <;> intro <;> simp [q, hqp]
    have hfinite := hq.comp hp
    rw [hcomp] at hfinite
    have : Module.Finite R (MonoidAlgebra R (N ⧸ p.range)) :=
      RingHom.finite_algebraMap.mp (RingHom.Finite.of_comp_finite hfinite)
    exact Module.Finite.finite_basis (MonoidAlgebra.basis (N ⧸ p.range) R)
  · intro h
    exact mapDomainRingHom_finite_of_finite_quotient R p

end TauCeti.MonoidAlgebra
