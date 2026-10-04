/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule

/-!
# Invariants of group representations

Mathlib names the group sum `∑ g, ρ g` of a finite-group representation `Representation.norm`,
builds the averaging projection `Representation.averageMap` separately out of the group-algebra
element `GroupAlgebra.average`, and records that the latter projects onto the invariants
(`Representation.isProj_averageMap`). What it does not record is how the two operators relate.
The group sum is the shape a symmetrization operator actually takes at a use site, where the
normalizing factor `⅟(#G)` is usually left implicit, and reinstating it by hand is the step that
gets rewritten.

This file supplies the bridge. Unfolding the group algebra once identifies `averageMap` with
`norm` scaled by `⅟(#G)`, and since scaling by a unit changes no image, `norm` has the same range
as the projection: the invariants.

There is a different integral reason for the norm to map onto the invariants. The norm does so on
the regular representation over any commutative ring, hence on every finitely generated projective
group-algebra module by passage to a finite free module and a direct summand. As a consequence,
taking invariants preserves a surjection onto a projective representation. This exactness property
is the input needed to lift modular invariant vectors to an integral projective lattice.

The file also records the companion description of the invariants available when `G` is cyclic.
Invariance is a condition on every group element, but a vector fixed by a generator is fixed by all
of its powers, so testing a single generator `g` suffices and the invariants are cut out by the one
linear map `ρ(g) - 1`. Mathlib states this elementwise, in
`Representation.mem_invariants_iff_of_forall_mem_zpowers`; the submodule-level equality with
`ker (ρ(g) - 1)` is the form used to present the (co)homology of a finite cyclic group as a
subquotient of `M`, where each group is the homology of `ρ(g) - 1` and the norm in one order or
the other.

Finally, a nontrivial irreducible representation has no nonzero invariant vector. This is what makes
the Haar integral of a nontrivial irreducible character vanish. A dimension-based corollary handles
the common case where nontriviality follows from the dimension being other than one.

Taking invariants under a normal subgroup `S`, Mathlib's `Rep.quotientToInvariantsFunctor`, is an
additive functor from representations of `G` to representations of `G ⧸ S`.

## Main results

* `Representation.averageMap_eq_invOf_card_smul_norm`: the averaging projection is the group sum
  `Representation.norm` scaled by the inverse of the group order.
* `Representation.range_norm_eq_invariants`: the group sum `Representation.norm ρ` has the
  invariants as its range.
* `Representation.range_norm_eq_invariants_of_projective`: the same conclusion without
  inverting the group order, when the underlying group-algebra module is finitely generated and
  projective.
* `Representation.exists_invariant_preimage_of_projective`: a surjective equivariant additive map,
  possibly between representations over different coefficient rings, lifts invariant vectors
  when its target is finitely generated and projective over the target group algebra.
* `Rep.invariantsFunctor_map_surjective_of_projective`: taking invariants preserves a surjective
  morphism of representations whose target is projective over the group algebra.
* `Rep.FiniteCyclicGroup.invariants_eq_ker_apply_sub`: for a cyclic group, the invariants are the
  kernel of the action of a generator minus the identity.
* `Representation.IsIrreducible.invariants_eq_bot`: a nontrivial irreducible representation has no
  nonzero invariant vector.
* `Representation.IsIrreducible.invariants_eq_bot_of_finrank_ne_one`: the dimension-based
  specialization.
* `Representation.IsIrreducible.eq_trivial_of_invariants_ne_bot` and
  `Representation.IsIrreducible.finrank_eq_one_of_invariants_ne_bot`: the two contrapositives, which
  turn a nonzero invariant vector of an irreducible representation into triviality and into
  dimension one.
* `Rep.quotientToInvariantsFunctor` is additive.
-/
public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]

/-- **The averaging projection is the normalized group sum.** Mathlib defines
`Representation.averageMap` through the group algebra; this unfolds that definition to the group sum
`Representation.norm`, scaled by the inverse of the group order. -/
theorem averageMap_eq_invOf_card_smul_norm :
    ρ.averageMap = ⅟(Fintype.card G : k) • ρ.norm := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, norm]

/-- **The group sum has the invariants as its range.** When `#G` is invertible in `k`, the operator
`Representation.norm ρ = ∑ g, ρ g` maps onto the invariants of `ρ`: it agrees with the averaging
projection up to the unit `#G`, so the two have the same image. -/
@[simp]
theorem range_norm_eq_invariants : LinearMap.range ρ.norm = ρ.invariants := by
  rw [← ρ.isProj_averageMap.range, averageMap_eq_invOf_card_smul_norm]
  refine le_antisymm ?_ (LinearMap.range_smul_le_range _ _)
  convert LinearMap.range_smul_le_range (⅟(Fintype.card G : k) • ρ.norm) (Fintype.card G : k)
  rw [smul_smul, mul_invOf_self, one_smul]

end Representation

namespace Representation

open scoped MonoidAlgebra

variable {k G V W : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

section Finite

variable [Fintype G]

/-- The group norm commutes with an intertwining map. -/
theorem IntertwiningMap.map_norm {ρ : Representation k G V} {σ : Representation k G W}
    (f : IntertwiningMap ρ σ) (x : V) : f (ρ.norm x) = σ.norm (f x) := by
  simp only [norm, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => IntertwiningMap.isIntertwining ρ σ f g x

/-- The norm of the left regular representation maps onto its invariant submodule, over an
arbitrary commutative ring. -/
private theorem range_norm_leftRegular_eq_invariants :
    LinearMap.range (leftRegular k G).norm = (leftRegular k G).invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    let y : MonoidAlgebra k G := MonoidAlgebra.single 1 (x.coeff 1)
    refine ⟨y, ?_⟩
    ext g
    have hcoeff : x.coeff g = x.coeff 1 := by
      have h := congrArg (fun z : MonoidAlgebra k G => z.coeff g) (hx g)
      simpa using h.symm
    simp [y, norm, hcoeff]

omit [Fintype G] in
private theorem ofModule'_groupAlgebra_apply (g : G) (x : MonoidAlgebra k G) :
    ofModule' (k := k) (G := G) (MonoidAlgebra k G) g x = leftRegular k G g x := by
  ext h
  simp [TauCeti.Representation.ofModule'_apply, coeff_ofMulAction,
    MonoidAlgebra.coeff_single_mul_apply]

/-- The norm maps onto the invariants of a finite direct sum of left regular representations. -/
private theorem range_norm_free_eq_invariants (n : ℕ) :
    LinearMap.range (ofModule' (k := k) (G := G) (Fin n → MonoidAlgebra k G)).norm =
      (ofModule' (k := k) (G := G) (Fin n → MonoidAlgebra k G)).invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    have hxi (i : Fin n) : x i ∈ (leftRegular k G).invariants := by
      intro g
      have h := congrFun (hx g) i
      change MonoidAlgebra.single g 1 * x i = x i at h
      rw [← ofModule'_groupAlgebra_apply]
      exact h
    choose y hy using fun i => LinearMap.mem_range.mp
      (show x i ∈ LinearMap.range (leftRegular k G).norm by
        rw [range_norm_leftRegular_eq_invariants]
        exact hxi i)
    refine ⟨y, funext fun i => ?_⟩
    simp only [norm, LinearMap.sum_apply, Finset.sum_apply,
      TauCeti.Representation.ofModule'_apply, Pi.smul_apply]
    rw [← hy i]
    simp only [norm, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro g _
    rw [← ofModule'_groupAlgebra_apply, TauCeti.Representation.ofModule'_apply]

/-- **The norm maps onto the invariants of a projective representation.** Let `G` be finite over
an arbitrary commutative ring `k`. If the `k[G]`-module underlying `ρ` is finitely generated and
projective, then every invariant vector is the norm of a vector.

This is the integral replacement for `Representation.range_norm_eq_invariants`, which assumes
that the order of `G` is invertible in `k`. -/
theorem range_norm_eq_invariants_of_projective (ρ : Representation k G V)
    [Module.Finite k[G] ρ.asModule] [Module.Projective k[G] ρ.asModule] :
    LinearMap.range ρ.norm = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    obtain ⟨n, f, s, -, -, hfs⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective k[G] ρ.asModule
    let τ := ofModule' (k := k) (G := G) (Fin n → MonoidAlgebra k G)
    let E : τ.asModule ≃ₗ[k[G]] (Fin n → MonoidAlgebra k G) :=
      TauCeti.Representation.ofModule'AsModuleEquiv _
    let F : IntertwiningMap τ ρ :=
      (IntertwiningMap.equivLinearMapAsModule τ ρ).symm (f ∘ₗ E.toLinearMap)
    let S : IntertwiningMap ρ τ :=
      (IntertwiningMap.equivLinearMapAsModule ρ τ).symm (E.symm.toLinearMap ∘ₗ s)
    have hSx : S x ∈ τ.invariants := fun g => by
      rw [← IntertwiningMap.isIntertwining ρ τ S g x, hx g]
    obtain ⟨y, hy⟩ : S x ∈ LinearMap.range τ.norm := by
      rw [range_norm_free_eq_invariants]
      exact hSx
    refine ⟨F y, ?_⟩
    rw [← F.map_norm, hy]
    have hFS : F (S x) = x := by
      simp only [F, S, IntertwiningMap.equivLinearMapAsModule_symm_apply,
        LinearMap.comp_apply]
      rw [τ.asModuleEquiv.symm_apply_apply]
      change ρ.asModuleEquiv
        (f (E (E.symm (s (ρ.asModuleEquiv.symm x))))) = x
      rw [E.apply_symm_apply]
      rw [← LinearMap.comp_apply, hfs, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
    exact hFS

end Finite

section ChangeRings

variable {l : Type*} [CommRing l] [Finite G]
variable {X : Type*} [AddCommGroup X] [Module l X]

/-- **Equivariant surjections lift invariants when the target is projective.** Let `ρ` and `σ` be
representations of the same finite group, possibly over different commutative rings. If an
equivariant additive map `f : V →+ X` is surjective and `σ.asModule` is finitely generated and
projective over `l[G]`, then every invariant vector of `σ` has an invariant preimage under `f`.

Allowing the coefficient rings to differ is essential for reduction of an integral projective
lattice modulo a prime. The proof writes the target invariant as a group norm, lifts a preimage
before taking the norm, and uses equivariance to commute `f` with the two norms. -/
theorem exists_invariant_preimage_of_projective
    (ρ : Representation k G V) (σ : Representation l G X)
    (f : V →+ X) (hf : Function.Surjective f)
    (hfg : ∀ g x, f (ρ g x) = σ g (f x))
    [Module.Finite l[G] σ.asModule] [Module.Projective l[G] σ.asModule]
    (y : σ.invariants) : ∃ x : ρ.invariants, f x = y := by
  let _ := Fintype.ofFinite G
  have hy : (y : X) ∈ LinearMap.range σ.norm := by
    rw [range_norm_eq_invariants_of_projective]
    exact y.2
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, rfl⟩ := hf z
  refine ⟨⟨ρ.norm x, fun g => self_norm_apply ρ g x⟩, ?_⟩
  change f (ρ.norm x) = y
  rw [← hz]
  simp only [norm, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => hfg g x

end ChangeRings

end Representation

namespace Rep

open CategoryTheory
open scoped MonoidAlgebra

variable {k G : Type*} [CommRing k] [Group G]

/-- **Invariants preserve surjections onto projective representations.** If `f : A ⟶ B` is
surjective and the `k[G]`-module underlying `B` is projective, then every invariant of `B` lifts
to an invariant of `A`. -/
theorem invariantsFunctor_map_surjective_of_projective {A B : Rep k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) [Module.Projective k[G] B.ρ.asModule] :
    Function.Surjective ((invariantsFunctor k G).map f).hom := by
  let F : A.ρ.asModule →ₗ[k[G]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := hf (B.ρ.asModuleEquiv y)
    refine ⟨A.ρ.asModuleEquiv.symm x, ?_⟩
    apply B.ρ.asModuleEquiv.injective
    calc
      B.ρ.asModuleEquiv (F (A.ρ.asModuleEquiv.symm x)) = f.hom x := by
        rfl
      _ = B.ρ.asModuleEquiv y := hx
  obtain ⟨s, hFs⟩ := Module.projective_lifting_property F LinearMap.id hF
  let S : Representation.IntertwiningMap B.ρ A.ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule B.ρ A.ρ).symm s
  rintro ⟨y, hy⟩
  have hSy : S y ∈ A.ρ.invariants := fun g => by
    rw [← Representation.IntertwiningMap.isIntertwining B.ρ A.ρ S g y, hy g]
  refine ⟨⟨S y, hSy⟩, Subtype.ext ?_⟩
  calc
    f.hom (S y) = B.ρ.asModuleEquiv (F (s (B.ρ.asModuleEquiv.symm y))) := by
      rfl
    _ = B.ρ.asModuleEquiv (B.ρ.asModuleEquiv.symm y) := by
      rw [← LinearMap.comp_apply, hFs, LinearMap.id_apply]
    _ = y := LinearEquiv.apply_symm_apply _ _

end Rep

namespace Representation.IsIrreducible

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **A nontrivial irreducible representation has no nonzero invariant vector.** -/
theorem invariants_eq_bot {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hρ : ρ ≠ trivial k G V) : ρ.invariants = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => by_contra fun hv0 => hρ ?_
  let f : IntertwiningMap (trivial k G k) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      rw [trivial_apply, LinearMap.toSpanSingleton_apply, map_smul]
      exact congrArg (c • ·) (hv g).symm
  have hf_one : f.toLinearMap 1 = v := by
    simp [f]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv0 <| calc
        v = f.toLinearMap 1 := hf_one.symm
        _ = (0 : IntertwiningMap (trivial k G k) ρ).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) ρ => φ.toLinearMap 1) hf
        _ = 0 := rfl
  ext g x
  obtain ⟨c, rfl⟩ := hsurj x
  simpa using (IntertwiningMap.isIntertwining (trivial k G k) ρ f g c).symm

/-- **An irreducible representation of dimension other than one has no nonzero invariant
vector.** -/
theorem invariants_eq_bot_of_finrank_ne_one {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hV : Module.finrank k V ≠ 1) : ρ.invariants = ⊥ := by
  refine h.invariants_eq_bot fun hρ => hV ?_
  subst ρ
  let _ := h.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : IntertwiningMap (trivial k G k) (trivial k G V) :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c => by
      simp only [trivial_apply, LinearMap.toSpanSingleton_apply, map_smul]
  have hsurj : Function.Surjective f.toLinearMap :=
    (IsIrreducible.surjective_or_eq_zero f).resolve_right fun hf =>
      hv <| calc
        v = f.toLinearMap 1 := by simp [f]
        _ = (0 : IntertwiningMap (trivial k G k) (trivial k G V)).toLinearMap 1 :=
          congrArg (fun φ : IntertwiningMap (trivial k G k) (trivial k G V) =>
            φ.toLinearMap 1) hf
        _ = 0 := rfl
  apply finrank_eq_one v hv
  intro w
  obtain ⟨c, hc⟩ := hsurj w
  exact ⟨c, by simpa only [f, LinearMap.intertwiningMap_of_isIntertwiningMap,
    LinearMap.toSpanSingleton_apply] using hc⟩

/-- **An irreducible representation with a nonzero invariant vector is the trivial
representation**, the contrapositive of `Representation.IsIrreducible.invariants_eq_bot`. -/
theorem eq_trivial_of_invariants_ne_bot {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hne : ρ.invariants ≠ ⊥) : ρ = trivial k G V :=
  not_not.1 (mt h.invariants_eq_bot hne)

/-- **An irreducible representation with a nonzero invariant vector is a line**, the contrapositive
of `Representation.IsIrreducible.invariants_eq_bot_of_finrank_ne_one`. -/
theorem finrank_eq_one_of_invariants_ne_bot {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hne : ρ.invariants ≠ ⊥) : Module.finrank k V = 1 :=
  not_not.1 (mt h.invariants_eq_bot_of_finrank_ne_one hne)

end Representation.IsIrreducible

namespace Rep.FiniteCyclicGroup

variable {R G : Type*} [CommRing R] [Group G] (M : Rep R G) (g : G)

/-- If `g` generates `G`, the invariants of a representation are the kernel of `ρ(g) - 1`. -/
theorem invariants_eq_ker_apply_sub (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    M.ρ.invariants = LinearMap.ker (M.ρ g - LinearMap.id) := by
  ext x
  simpa [sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x

end Rep.FiniteCyclicGroup

namespace TauCeti

variable {k G : Type*} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

/-- Taking `S`-invariants is additive, so it maps short complexes of representations of `G` to
short complexes of representations of `G ⧸ S`. -/
instance : (Rep.quotientToInvariantsFunctor k S).Additive where

end TauCeti
