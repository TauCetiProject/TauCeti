/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness

/-!
# Short exact sequences of affine groups

A sequence of affine groups `1 → N → G → Q → 1` is **exact** when `G → Q` is faithfully flat (a
quotient map) and `N → G` is a closed immersion identifying `N` with the scheme-theoretic kernel
of `G → Q` (Milne, *Algebraic Groups*, §5.c). In coordinate Hopf algebras the arrows reverse:
such a sequence is a pair of morphisms

```text
O(Q) --p--> O(G) --i--> O(N)
```

of commutative Hopf algebras with `p` faithfully flat, `i` surjective, and `ker i` equal to the
kernel Hopf ideal `O(G) · p(O(Q)⁺)`. This file records that notion,
`TauCeti.CommHopfAlgCat.IsShortExact`, over an arbitrary commutative base ring, with no
smoothness, reducedness or finite-type hypotheses, and derives its basic consequences.

* Up to isomorphism, the closed subgroup in a short exact sequence is the scheme-theoretic kernel:
  `p` together with the quotient map by `kernelHopfIdeal p` is short exact, and every short exact
  sequence is isomorphic to this one (`isShortExact_iff_exists_iso`).
* The quotient is recovered from the subgroup: the functions on `G` invariant under `N` are
  exactly the functions pulled back from `Q` (`IsShortExact.coinvariants_eq_range`).
* On `A`-points, for every commutative `R`-algebra `A`, the sequence
  `N(A) → G(A) → Q(A)` is exact at `G(A)` (`IsShortExact.ker_mapPointsFunctor_app_eq_range`),
  and `N(A) → G(A)` is injective (`mapPointsFunctor_app_injective_of_surjective`). In general
  `G(A) → Q(A)` is surjective only after a faithfully flat extension of `A`; it is surjective when
  `A` is an algebraically closed field and `p` is of finite type
  (`mapPointsFunctor_app_surjective_of_faithfullyFlat`).
* The quotient map is an isogeny exactly when the subgroup is finite
  (`IsShortExact.isIsogeny_iff_moduleFinite`).

## Main declarations

* `TauCeti.CommHopfAlgCat.IsShortExact`: short exactness of `O(Q) ⟶ O(G) ⟶ O(N)`.
* `TauCeti.CommHopfAlgCat.IsShortExact.comp_eq_unit_comp_counit`: the composite `N → Q` is
  trivial.
* `TauCeti.CommHopfAlgCat.IsShortExact.kernelIso`: the identification of `N` with the kernel.
* `TauCeti.CommHopfAlgCat.isShortExact_mkQuotient_kernelHopfIdeal`: the canonical short exact
  sequence of a faithfully flat morphism.
* `TauCeti.CommHopfAlgCat.isShortExact_iff_exists_iso`: short exact sequences are, up to
  isomorphism, the canonical ones.
* `TauCeti.CommHopfAlgCat.IsShortExact.coinvariants_eq_range`: `O(Q) = O(G)^N`.
* `TauCeti.CommHopfAlgCat.IsShortExact.ker_mapPointsFunctor_app_eq_range`: exactness on points.
* `TauCeti.CommHopfAlgCat.IsShortExact.isIsogeny_iff_moduleFinite`: finite kernels and isogenies.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c, exact sequences of algebraic groups.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R] {Q G N : _root_.CommHopfAlgCat.{v} R}

/-- Coordinate morphisms `p : O(Q) ⟶ O(G)` and `i : O(G) ⟶ O(N)` form a **short exact
sequence** of affine groups `1 → N → G → Q → 1` when `G → Q` is faithfully flat, `N → G` is a
closed immersion, and `N` is the scheme-theoretic kernel of `G → Q`: the ideal cutting out `N`
is the kernel Hopf ideal of `p`. -/
structure IsShortExact (p : Q ⟶ G) (i : G ⟶ N) : Prop where
  /-- The quotient map `G → Q` is faithfully flat. -/
  faithfullyFlat : p.hom.toAlgHom.toRingHom.FaithfullyFlat
  /-- The map `N → G` is a closed immersion. -/
  surjective : Function.Surjective i.hom
  /-- The closed subgroup `N` of `G` is the kernel of `G → Q`. -/
  ker_eq : RingHom.ker i.hom.toAlgHom.toRingHom = (kernelHopfIdeal p).toIdeal

namespace IsShortExact

variable {p : Q ⟶ G} {i : G ⟶ N}

/-- In a short exact sequence, the Hopf ideal cutting out the subgroup is the kernel Hopf ideal
of the quotient map. -/
theorem kerOfSurjective_eq_kernelHopfIdeal (h : IsShortExact p i) :
    HopfIdeal.kerOfSurjective i.hom h.surjective = kernelHopfIdeal p := by
  ext x
  rw [HopfIdeal.mem_kerOfSurjective, ← HopfIdeal.mem_toIdeal, ← h.ker_eq, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]

/-- The composite `N → G → Q` of a short exact sequence is the trivial homomorphism. -/
@[reassoc (attr := simp)]
theorem comp_eq_unit_comp_counit (h : IsShortExact p i) :
    p ≫ i = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom R N).comp (Bialgebra.counitBialgHom R Q)) :=
  (comp_eq_unit_comp_counit_iff p i).mpr h.ker_eq.ge

/-- The subgroup in a short exact sequence is isomorphic to the scheme-theoretic kernel of the
quotient map, compatibly with the inclusions into `G` (`mkQuotient_comp_kernelIso_hom`). -/
noncomputable def kernelIso (h : IsShortExact p i) : quotient G (kernelHopfIdeal p) ≅ N :=
  quotientIsoOfKerOfSurjectiveEq i h.surjective h.kerOfSurjective_eq_kernelHopfIdeal

/-- The identification of the subgroup with the kernel respects the inclusions into `G`. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelIso_hom (h : IsShortExact p i) :
    mkQuotient G (kernelHopfIdeal p) ≫ h.kernelIso.hom = i :=
  mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom i h.surjective
    h.kerOfSurjective_eq_kernelHopfIdeal

/-- The inverse identification of the subgroup with the kernel respects the inclusions into
`G`. -/
@[reassoc (attr := simp)]
theorem comp_kernelIso_inv (h : IsShortExact p i) :
    i ≫ h.kernelIso.inv = mkQuotient G (kernelHopfIdeal p) :=
  comp_quotientIsoOfKerOfSurjectiveEq_inv i h.surjective h.kerOfSurjective_eq_kernelHopfIdeal

/-- The functions on `G` invariant under the subgroup `N` of a short exact sequence are exactly
the functions pulled back from the quotient `Q`. -/
theorem coinvariants_eq_range (h : IsShortExact p i) :
    (HopfIdeal.kerOfSurjective i.hom h.surjective).coinvariants = p.hom.toAlgHom.range := by
  rw [h.kerOfSurjective_eq_kernelHopfIdeal]
  exact coinvariants_kernelHopfIdeal_eq_range p h.faithfullyFlat

/-- Exactness on points: for every commutative `R`-algebra `A`, an `A`-point of `G` maps to the
identity of `Q(A)` exactly when it comes from an `A`-point of `N`. -/
theorem ker_mapPointsFunctor_app_eq_range (h : IsShortExact p i) (A : CommAlgCat.{w} R) :
    ((mapPointsFunctor p).app A).hom.ker = ((mapPointsFunctor i).app A).hom.range := by
  rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor i h.surjective A,
    h.kerOfSurjective_eq_kernelHopfIdeal,
    quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor]

/-- The quotient map of a short exact sequence is an isogeny exactly when the subgroup is
finite over the base. -/
theorem isIsogeny_iff_moduleFinite (h : IsShortExact p i) : IsIsogeny p ↔ Module.Finite R N := by
  rw [CommHopfAlgCat.isIsogeny_iff, and_iff_left h.faithfullyFlat,
    finite_iff_moduleFinite_quotient_kernelHopfIdeal p h.faithfullyFlat]
  let e := (CommHopfAlgCat.ofIso h.kernelIso).toAlgEquiv.toLinearEquiv
  exact ⟨fun _ ↦ Module.Finite.equiv e, fun _ ↦ Module.Finite.equiv e.symm⟩

end IsShortExact

/-- A faithfully flat morphism and the quotient map onto its scheme-theoretic kernel form a
short exact sequence. -/
theorem isShortExact_mkQuotient_kernelHopfIdeal (p : Q ⟶ G)
    (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    IsShortExact p (mkQuotient G (kernelHopfIdeal p)) :=
  ⟨hp, mkQuotient_surjective G _, mkQuotient_ker G _⟩

/-- A pair of coordinate morphisms is short exact exactly when the first is faithfully flat and
the second is, up to isomorphism of its target, the quotient map onto the kernel Hopf ideal of
the first. -/
theorem isShortExact_iff_exists_iso (p : Q ⟶ G) (i : G ⟶ N) :
    IsShortExact p i ↔ p.hom.toAlgHom.toRingHom.FaithfullyFlat ∧
      ∃ e : quotient G (kernelHopfIdeal p) ≅ N, mkQuotient G (kernelHopfIdeal p) ≫ e.hom = i := by
  refine ⟨fun h ↦ ⟨h.faithfullyFlat, h.kernelIso, h.mkQuotient_comp_kernelIso_hom⟩, ?_⟩
  rintro ⟨hp, e, rfl⟩
  have he := ConcreteCategory.bijective_of_isIso e.hom
  refine ⟨hp, ?_, ?_⟩
  · rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact he.2.comp (mkQuotient_surjective G _)
  · ext x
    rw [← mkQuotient_ker G, RingHom.mem_ker, RingHom.mem_ker, _root_.CommHopfAlgCat.hom_comp,
      BialgHom.comp_toAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.coe_coe, AlgHom.comp_apply]
    exact map_eq_zero_iff _ he.1

end TauCeti.CommHopfAlgCat
