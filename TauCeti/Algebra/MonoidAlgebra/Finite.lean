/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Submonoid.Finiteness
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Finsupp

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

Without commutativity, `R[N]` is still a finitely generated `R[M]`-module through any monoid
homomorphism `p : M →* N` into a finite monoid, since it is already finitely generated over `R`
(`TauCeti.MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite`). This is the finiteness behind
restricting representations of a finite group along a homomorphism. For any homomorphism
`p : M →* N` of commutative monoids whose target is covered by translates of the image of `p` along
a family `s : ι → N`, the monomials `single (s i) 1` span `R[N]` as an `R[M]`-module
(`TauCeti.MonoidAlgebra.span_range_single_eq_top_of_forall_exists_mul`). When the translate family
is finite, `R[N]` is a finite `R[M]`-module over any commutative semiring `R`
(`TauCeti.MonoidAlgebra.mapDomainRingHom_moduleFinite_of_exists_finset_mul`), and hence
`(mapDomainRingHom R p).Finite` holds over any commutative ring `R`
(`TauCeti.MonoidAlgebra.mapDomainRingHom_finite_of_exists_finset_mul`). Combining this with
bounded-shift representatives for submonoid saturations shows that, for a finitely generated
submonoid `S` of a torsion-free abelian group, the algebra of its saturation in an ambient free
abelian group or in `AddSubgroup.closure (S : Set G)` is finite over `R[S]`
(`TauCeti.AddMonoidAlgebra.mapDomainRingHom_inclusion_nsmulSaturation_finite` and
`TauCeti.AddMonoidAlgebra.mapDomainRingHom_inclusion_nsmulSaturation_inf_closure_finite`).
-/

public section

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

/-- If every element of `N` is a translate `s i * p m` of an element of `p`'s image by a member of
a family `s : ι → N`, then the monomials `single (s i) 1` span `R[N]` as an `R[M]`-module along
`mapDomainRingHom R p` over any commutative semiring `R`. -/
@[to_additive (dont_translate := R)
  TauCeti.AddMonoidAlgebra.span_range_single_eq_top_of_forall_exists_add
  /-- If every element of `N` is a shift `s i + p m` of an element of `p`'s image by a member of a
  family `s : ι → N`, then the monomials `single (s i) 1` span `R[N]` as an `R[M]`-module along
  `mapDomainRingHom R p` over any commutative semiring `R`. -/]
theorem span_range_single_eq_top_of_forall_exists_mul {ι M N : Type*} [CommMonoid M]
    [CommMonoid N] (R : Type*) [CommSemiring R] (p : M →* N) (s : ι → N)
    (hs : ∀ n : N, ∃ i : ι, ∃ m : M, n = s i * p m) :
    letI := (mapDomainRingHom R p).toAlgebra
    Submodule.span (MonoidAlgebra R M) (Set.range fun i ↦ single (s i) (1 : R)) =
      (⊤ : Submodule (MonoidAlgebra R M) (MonoidAlgebra R N)) := by
  let := (mapDomainRingHom R p).toAlgebra
  rw [eq_top_iff]
  rintro x -
  induction x using induction_linear with
  | zero => exact Submodule.zero_mem _
  | add _ _ hx hy => exact Submodule.add_mem _ hx hy
  | single n r =>
    obtain ⟨i, m, hnm⟩ := hs n
    have hprod : p m * s i = n := by rw [mul_comm, hnm]
    have hmem := Submodule.smul_mem
      (Submodule.span (MonoidAlgebra R M) (Set.range fun i ↦ single (s i) (1 : R)))
      (single m r) (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply,
      mapDomain_single, single_mul_single, mul_one, hprod] using hmem

section CommGroup

variable (R : Type*) {M N : Type*} [CommGroup M] [CommGroup N]

/-- Monomials indexed by representatives of the cokernel span the target group
algebra as a module over the source group algebra. -/
theorem span_range_single_quotient_eq_top [CommSemiring R] (p : M →* N)
    (s : N ⧸ p.range → N) (hs : Function.RightInverse s (QuotientGroup.mk' p.range)) :
    let := (mapDomainRingHom R p).toAlgebra
    Submodule.span (MonoidAlgebra R M) (Set.range fun q ↦ single (s q) (1 : R)) =
      (⊤ : Submodule (MonoidAlgebra R M) (MonoidAlgebra R N)) := by
  refine span_range_single_eq_top_of_forall_exists_mul R p s fun n ↦ ?_
  obtain ⟨m, hm⟩ : n / s (QuotientGroup.mk' p.range n) ∈ p.range :=
    QuotientGroup.eq_iff_div_mem.mp (hs (QuotientGroup.mk' p.range n)).symm
  exact ⟨QuotientGroup.mk' p.range n, m, by rw [hm, mul_comm, div_mul_cancel]⟩

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
    exact Module.Finite.finite_basis (_root_.MonoidAlgebra.basis (N ⧸ p.range) R)
  · intro h
    exact mapDomainRingHom_finite_of_finite_quotient R p

end CommGroup

/-- **Finiteness over the algebra of any monoid mapping to a finite one.** For a monoid
homomorphism `p : M →* N` with `N` finite, `R[N]` is a finitely generated `R[M]`-module through
`mapDomainRingHom R p`, because it is already finitely generated over `R`. Neither monoid need be
commutative, so the algebras need not be, and the statement uses the module structure
`RingHom.toModule` rather than `RingHom.Finite`. -/
theorem mapDomainRingHom_moduleFinite_of_finite {R : Type*} [Semiring R] {M N : Type*}
    [Monoid M] [Monoid N] [Finite N] (p : M →* N) :
    letI := (mapDomainRingHom R p).toModule
    Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N) := by
  let := (mapDomainRingHom R p).toModule
  have : IsScalarTower R (MonoidAlgebra R M) (MonoidAlgebra R N) := ⟨fun c a b ↦ by
    simp [RingHom.toModule_smul, mapDomain_smul, smul_mul_assoc]⟩
  exact Module.Finite.of_restrictScalars_finite R (MonoidAlgebra R M) (MonoidAlgebra R N)

/-- If the target of a commutative-monoid homomorphism `p : M →* N` is covered by finitely many
translates of the image of `p`, then `R[N]` is a finite `R[M]`-module along `mapDomainRingHom R p`
over any commutative semiring `R`. -/
@[to_additive (dont_translate := R)
  TauCeti.AddMonoidAlgebra.mapDomainRingHom_moduleFinite_of_exists_finset_add
  /-- If the target of a commutative additive-monoid homomorphism `p : M →+ N` is covered by
  finitely many shifts of the image of `p`, then `R[N]` is a finite `R[M]`-module along
  `mapDomainRingHom R p` over any commutative semiring `R`. -/]
theorem mapDomainRingHom_moduleFinite_of_exists_finset_mul {M N : Type*} [CommMonoid M]
    [CommMonoid N] (p : M →* N) (hF : ∃ F : Finset N, ∀ x : N, ∃ z ∈ F, ∃ s : M, x = z * p s)
    (R : Type*) [CommSemiring R] :
    letI := (mapDomainRingHom R p).toAlgebra
    Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N) := by
  obtain ⟨F, hF_mul⟩ := hF
  let := (mapDomainRingHom R p).toAlgebra
  apply Module.Finite.of_fg_top
  refine Submodule.fg_def.mpr ⟨Set.range fun z : F => single z.1 (1 : R), Set.finite_range _, ?_⟩
  exact span_range_single_eq_top_of_forall_exists_mul R p Subtype.val fun x =>
    let ⟨z, hz, s, hx⟩ := hF_mul x
    ⟨⟨z, hz⟩, s, hx⟩

/-- If the target of a commutative-monoid homomorphism `p : M →* N` is covered by finitely many
translates of the image of `p`, then `mapDomainRingHom R p` is a finite ring homomorphism over any
commutative ring `R` (`RingHom.Finite` requires commutative rings; see
`TauCeti.MonoidAlgebra.mapDomainRingHom_moduleFinite_of_exists_finset_mul` for commutative
semirings). -/
@[to_additive (dont_translate := R)
  TauCeti.AddMonoidAlgebra.mapDomainRingHom_finite_of_exists_finset_add
  /-- If the target of a commutative additive-monoid homomorphism `p : M →+ N` is covered by
  finitely many shifts of the image of `p`, then `mapDomainRingHom R p` is a finite ring
  homomorphism over any commutative ring `R` (`RingHom.Finite` requires commutative rings; see
  `TauCeti.AddMonoidAlgebra.mapDomainRingHom_moduleFinite_of_exists_finset_add` for commutative
  semirings). -/]
theorem mapDomainRingHom_finite_of_exists_finset_mul {M N : Type*} [CommMonoid M] [CommMonoid N]
    (p : M →* N) (hF : ∃ F : Finset N, ∀ x : N, ∃ z ∈ F, ∃ s : M, x = z * p s)
    (R : Type*) [CommRing R] :
    (mapDomainRingHom R p).Finite :=
  mapDomainRingHom_moduleFinite_of_exists_finset_mul p hF R

end TauCeti.MonoidAlgebra

namespace TauCeti.AddMonoidAlgebra

open _root_.AddMonoidAlgebra

/-- For a finitely generated submonoid `S` of a free abelian group `L`, `R[S.nsmulSaturation]` is
a finite `R[S]`-algebra over any commutative ring `R`. -/
theorem mapDomainRingHom_inclusion_nsmulSaturation_finite {L : Type*} [AddCommGroup L]
    [Module.Free ℤ L] {S : AddSubmonoid L} (hS : S.FG) (R : Type*) [CommRing R] :
    (mapDomainRingHom R (AddSubmonoid.inclusion S.le_nsmulSaturation)).Finite :=
  mapDomainRingHom_finite_of_exists_finset_add _
    (AddSubmonoid.exists_finset_inclusion_add S.le_nsmulSaturation
      hS.exists_finset_subset_nsmulSaturation_add) R

/-- For a finitely generated submonoid `S` of a torsion-free abelian group `G`, the algebra of the
saturation of `S` inside `AddSubgroup.closure (S : Set G)` is a finite `R[S]`-algebra over any
commutative ring `R`. -/
theorem mapDomainRingHom_inclusion_nsmulSaturation_inf_closure_finite {G : Type*} [AddCommGroup G]
    [HasUniqueDiv G] {S : AddSubmonoid G} (hS : S.FG) (R : Type*) [CommRing R] :
    (mapDomainRingHom R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))).Finite :=
  mapDomainRingHom_finite_of_exists_finset_add _
    (AddSubmonoid.exists_finset_inclusion_add
      (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)
      hS.exists_finset_subset_nsmulSaturation_inf_closure_add) R

end TauCeti.AddMonoidAlgebra
