/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RepresentationTheory.Rep.Iso
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Finsupp
import TauCeti.RepresentationTheory.Intertwining

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
the regular representation over any commutative ring, hence on every projective group-algebra
module by passage to a free module and a direct summand. As a consequence, taking invariants
preserves a surjection onto a projective representation. This exactness property is the input
needed to lift modular invariant vectors to an integral projective lattice.

The file also records the companion description of the invariants available when `G` is cyclic.
Invariance is a condition on every group element, but a vector fixed by a generator is fixed by all
of its powers, so testing a single generator `g` suffices and the invariants are cut out by the one
linear map `ρ(g) - 1`. Mathlib states this elementwise, in
`Representation.mem_invariants_iff_of_forall_mem_zpowers`; the submodule-level equality with
`ker (ρ(g) - 1)` is the form used to present the (co)homology of a finite cyclic group as a
subquotient of `M`, where each group is the homology of `ρ(g) - 1` and the norm in one order or
the other. More generally, a vector is invariant as soon as it is fixed by each element of a
generating set of `G`.

Finally, a nontrivial irreducible representation has no nonzero invariant vector. This is what makes
the Haar integral of a nontrivial irreducible character vanish. A dimension-based corollary handles
the common case where nontriviality follows from the dimension being other than one.

Taking invariants under a normal subgroup `S`, Mathlib's `Rep.quotientToInvariantsFunctor`, is an
additive functor from representations of `G` to representations of `G ⧸ S`.

When `G` is finite and `#G` is invertible in the commutative ring `k`, an invariant vector lifts
along any surjection: average an arbitrary preimage. Taking invariants is then an exact functor
`Rep k G ⥤ ModuleCat k`. It preserves finite limits as a right adjoint, and epimorphisms,
homology and finite colimits by averaging; in particular it preserves short exact sequences and
quasi-isomorphisms of complexes of representations. Invertibility of `#G` is also necessary:
invariants preserve epimorphisms exactly when `#G` is a unit, as the augmentation `k[G] ⟶ k`
shows, since an invariant of `k[G]` has constant coefficients. Over `ZMod 2` and a group of order
two, the augmentation is onto while its restriction to invariants is zero. Without any
hypothesis on `#G`, invariants of a finitely generated group, in particular of a finite group,
commute with filtered colimits: invariance is tested on a finite generating set, and finitely
many equations `g • v = v` that hold in a filtered colimit already hold at a common stage. In
particular the dimension of the invariants is additive in short exact sequences of
finite-dimensional representations over a field in which `#G` is invertible.

A functor `F : ModuleCat A ⥤ ModuleCat B` carries a representation `σ` of `G` by `A`-linear maps
on `M` to the representation `g ↦ F(σ g)` on `F(M)`, the representation-level form of Mathlib's
`CategoryTheory.Functor.mapAction`. When `G` is finite and `#G` is invertible in `A`, the averaging
projection exhibits the invariants `M^G` as a direct summand of `M`. Applying an additive `F` to
this splitting shows that the invariants of `F(M)` are exactly `F(M^G)`, embedded by the
inclusion. The main example is `F = Tor'ₙ(N, -)`, the derived functor of the tensor product in its
first variable: its invariants are `Tor'ₙ(N, M^G)`.

## Main results

* `Representation.averageMap_eq_invOf_card_smul_norm`: the averaging projection is the group sum
  `Representation.norm` scaled by the inverse of the group order.
* `Representation.averageMap_apply`: the same identity evaluated at a vector.
* `Representation.averageMap_comp_ρ`: the averaging projection does not see the action.
* `Representation.IntertwiningMap.map_averageMap`: intertwining maps commute with averaging.
* `Convex.averageMap_mem`: an invariant convex set contains the average of the orbit of each of
  its points, which is a fixed point.
* `Representation.range_norm_eq_invariants`: the group sum `Representation.norm ρ` has the
  invariants as its range.
* `Representation.range_norm_eq_invariants_of_projective`: the same conclusion without
  inverting the group order, when the underlying group-algebra module is projective.
* `Representation.range_norm_trivial`: for trivial coefficients, the range of the norm is the ideal
  generated by the group order.
* `Representation.norm_trivial_apply`: for trivial coefficients, the norm is multiplication by
  the group order.
* `Representation.norm_mul_norm`: the group sum squares to the group order times itself,
  `norm ρ * norm ρ = |G| • norm ρ`.
* `Representation.exists_invariant_preimage_of_surjective_of_projective`: a surjective
  equivariant additive map, possibly between representations over different coefficient rings,
  lifts invariant vectors when its target is projective over the target group algebra.
* `Representation.IntertwiningMap.invariantsMap`: an intertwining map induces a linear map on
  invariants, injective when the intertwining map is, functorially
  (`Representation.IntertwiningMap.invariantsMap_id`, `invariantsMap_comp`); for an equivalence it
  is `Representation.Equiv.invariantsLinearEquiv`
  (`Representation.Equiv.toLinearMap_invariantsLinearEquiv`).
* `Representation.Equiv.invariantsLinearEquiv`: equivalent representations have isomorphic
  invariants, and `Representation.Equiv.apply_mem_invariants_iff`: an equivalence detects
  invariance of a vector.
* `Representation.Equiv.quotientToInvariants`: for a normal subgroup `S`, an equivalence of
  representations of `G` is an equivalence of the representations of `G ⧸ S` on the
  `S`-invariants.
* `Representation.invariants_comp_of_surjective`: restriction along a surjective homomorphism
  does not change the invariants.
* `Representation.invariants_comp_comp_subtype`: the invariants of `ρ.comp φ` under a subgroup
  `U` are the invariants of `ρ` under its image `φ(U)`.
* `Representation.map_subtype_invariants_quotientToInvariants`: invariants in stages, for a normal
  subgroup `S` the `G ⧸ S`-invariants of `V^S` are `V^G` as submodules of `V`; as a linear
  equivalence, `Representation.quotientToInvariantsInvariantsEquiv`.
* `Representation.invariants_comp_subtype_subgroupOf`: for `U' ≤ U`, the invariants of `ρ|_U`
  under `U'.subgroupOf U` are the `U'`-invariants of `ρ`.
* `Representation.invariants_prod`, `Representation.invariants_directSum`: the invariants of a
  direct sum are the product of the invariants.
* `Representation.prod_comp`, `Representation.directSum_comp`: restricting a direct sum along a
  homomorphism gives the direct sum of the restrictions.
* `Representation.map_subtype_invariants_subrepresentation`: the invariants of the restriction to
  a `G`-stable submodule `W` are `ρ.invariants ⊓ W`.
* `Representation.tmul_mem_invariants_tprod`: the tensor product of invariant vectors is
  invariant.
* `Representation.finrank_invariants_tprod_of_comp`: invariant dimensions of tensor products may
  be compared along a surjective homomorphism of groups.
* `Rep.invariantsFunctor_map_surjective_of_projective`: taking invariants preserves
  a surjective morphism of representations whose target is projective over the group algebra.
* `Rep.ρ_apply_of_mem_ker`: a vector killed by `ρ(g) - 1` is fixed by `g`.
* `Rep.applyAsHom_trivial_sub_id_apply`, `Rep.norm_trivial_hom_apply`: for the trivial
  representation, `ρ(g) - 𝟙` vanishes and the norm is multiplication by the group order.
* `Rep.trivialHomEquivInvariants`: the intertwiners out of the trivial line are the invariant
  vectors.
* `Rep.FiniteCyclicGroup.invariants_eq_ker_apply_sub`: for a cyclic group, the invariants are the
  kernel of the action of a generator minus the identity.
* `Representation.mem_invariants_iff_of_closure_eq_top`: invariance may be tested on a generating
  set.
* `Representation.IsIrreducible.invariants_eq_bot`: a nontrivial irreducible representation has no
  nonzero invariant vector.
* `Representation.IsIrreducible.invariants_eq_bot_of_finrank_ne_one`: the dimension-based
  specialization.
* `Representation.IsIrreducible.eq_trivial_of_invariants_ne_bot` and
  `Representation.IsIrreducible.finrank_eq_one_of_invariants_ne_bot`: the two contrapositives, which
  turn a nonzero invariant vector of an irreducible representation into triviality and into
  dimension one.
* `Rep.quotientToInvariantsFunctor` is additive.
* `Rep.invariantsFunctor_map_hom_apply_coe`: the image of an invariant under
  `(invariantsFunctor k G).map f` is its image under `f`.
* `Rep.invariantsFunctor_map_surjective`: when `#G` is invertible in `k`, taking invariants
  preserves surjective morphisms of representations; hence instances saying that it preserves
  epimorphisms, homology and finite colimits.
* `Rep.preservesEpimorphisms_invariantsFunctor_iff`: for a finite group, taking invariants
  preserves epimorphisms if and only if `#G` is a unit in `k`.
* `Rep.exists_map_apply_eq_of_isColimit`: if the image in a filtered colimit of a vector is
  fixed by finitely many group elements, so is its image at some later stage.
* An instance saying that invariants of a finitely generated group, in particular of a finite
  group, preserve filtered colimits.
* `CategoryTheory.Functor.mapRepresentation`: the representation `g ↦ F(σ g)` on `F(M)`.
* `CategoryTheory.Functor.invariants_mapRepresentation` and
  `CategoryTheory.Functor.map_ofHom_subtype_invariants_injective`: when `#G` is invertible, an
  additive functor identifies `F(M^G)` with the invariants of `F(M)`.
* `TauCeti.FDRep.finrank_invariants_add_of_shortExact`: when `#G` is invertible, the dimension
  of the invariants is additive in short exact sequences of finite-dimensional representations.
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
  simp only [averageMap, GroupAlgebra.average, map_smul, MonoidAlgebra.of_apply,
    asAlgebraHom_sum_single_one]

/-- The averaging projection of `v` is the normalized group sum `⅟#G • ∑ g, ρ g v`. -/
theorem averageMap_apply (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  rw [averageMap_eq_invOf_card_smul_norm, LinearMap.smul_apply, norm, LinearMap.sum_apply]

/-- **Averaging does not see the action**: `avg ∘ ρ g = avg`, as `average k G * g = average k G`
in the group algebra (`GroupAlgebra.mul_average_right`). -/
theorem averageMap_comp_ρ (g : G) : ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_eq_comp, ← map_mul,
    GroupAlgebra.mul_average_right]

variable {ρ} in
/-- **Intertwining maps commute with averaging**: an intertwining map `f : ρ → σ` carries the
averaging projection of `ρ` to that of `σ`. -/
theorem IntertwiningMap.map_averageMap {W : Type*} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} (f : IntertwiningMap ρ σ) (v : V) :
    f (ρ.averageMap v) = σ.averageMap (f v) := by
  simp only [averageMap_apply, map_smul, map_sum, IntertwiningMap.isIntertwining]

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

namespace Convex

/-- **The orbit average lies in an invariant convex set.** If a finite group `G`, whose order is
invertible in the linearly ordered field `𝕜`, acts linearly on `V` preserving a convex set `s`,
then `s` contains the average `|G|⁻¹ ∑ g, ρ g v` of the orbit of each of its points `v`. This
average is fixed by `G` (`Representation.averageMap_invariant`), so a nonempty invariant convex set
contains a fixed point. -/
theorem averageMap_mem {𝕜 G V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Group G]
    [Fintype G] [Invertible (Fintype.card G : 𝕜)] [AddCommGroup V] [Module 𝕜 V]
    {ρ : Representation 𝕜 G V} {s : Set V} (hs : Convex 𝕜 s)
    (hρs : ∀ g, Set.MapsTo (ρ g) s s) {v : V} (hv : v ∈ s) : ρ.averageMap v ∈ s := by
  rw [Representation.averageMap_apply, Finset.smul_sum]
  refine hs.sum_mem (fun _ _ ↦ invOf_nonneg.2 (Nat.cast_nonneg _)) ?_ fun g _ ↦ hρs g hv
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_invOf_self]

end Convex

namespace Representation

-- Stated over `Representation.trivial k H k`, the form to which `simp` reduces
-- `(Rep.trivial k H k).ρ`, so that it fires.
/-- For trivial coefficients, the range of the norm is the ideal generated by the group order. -/
@[simp]
theorem range_norm_trivial (k H : Type*) [CommSemiring k] [Group H] [Fintype H] :
    LinearMap.range (Representation.trivial k H k).norm = Ideal.span {(Nat.card H : k)} := by
  ext x
  simp [Representation.norm, Ideal.mem_span_singleton', mul_comm]

/-- For the trivial representation, the norm `N = ∑ ρ(h)` is multiplication by the group order. -/
@[simp]
theorem norm_trivial_apply (k H : Type*) {V : Type*} [Semiring k] [Group H] [Fintype H]
    [AddCommMonoid V] [Module k V] (x : V) :
    (Representation.trivial k H V).norm x = (Nat.card H : k) • x := by
  simp [Representation.norm, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

/-- **The square of the group sum**: for a representation of a finite group,
`norm ρ * norm ρ = |G| • norm ρ`, since `norm ρ * ρ g = norm ρ` for every `g`
(`Representation.norm_comp_self`). -/
theorem norm_mul_norm {k G V : Type*} [Semiring k] [Group G] [Fintype G] [AddCommMonoid V]
    [Module k V] (ρ : Representation k G V) : ρ.norm * ρ.norm = Nat.card G • ρ.norm :=
  calc ρ.norm * ρ.norm = ρ.norm * ∑ g : G, ρ g := by rw [norm]
    _ = ∑ g : G, ρ.norm * ρ g := Finset.mul_sum _ _ _
    _ = ∑ _g : G, ρ.norm := Finset.sum_congr rfl fun g _ => by
        rw [Module.End.mul_eq_comp, norm_comp_self]
    _ = Nat.card G • ρ.norm := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]

end Representation

namespace Representation

/-- **Restriction along a surjective homomorphism does not change the invariants**: a vector is
fixed by every `f g` exactly when it is fixed by every element of `H`. -/
theorem invariants_comp_of_surjective {k G H V : Type*} [CommRing k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] (ρ : Representation k H V) (f : G →* H)
    (hf : Function.Surjective f) : invariants (ρ.comp f) = ρ.invariants := by
  ext v
  simp only [mem_invariants, MonoidHom.comp_apply]
  exact ⟨fun h g ↦ by obtain ⟨g, rfl⟩ := hf g; exact h g, fun h g ↦ h (f g)⟩

/-- **Invariants under a subgroup after restriction along a homomorphism**: a vector is fixed by
`φ u` for every `u ∈ U` exactly when it is fixed by the image subgroup `φ(U)`. -/
theorem invariants_comp_comp_subtype {k G H V : Type*} [CommRing k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (φ : H →* G) (U : Subgroup H) :
    invariants ((ρ.comp φ).comp U.subtype) = invariants (ρ.comp (U.map φ).subtype) := by
  have h : (ρ.comp φ).comp U.subtype = (ρ.comp (U.map φ).subtype).comp (φ.subgroupMap U) := by
    ext u : 1
    simp
  rw [h, invariants_comp_of_surjective _ _ (φ.subgroupMap_surjective U)]

/-- The invariants of a direct sum are the product of the invariants. -/
@[simp]
theorem invariants_prod {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W) :
    invariants (ρ.prod σ) = (invariants ρ).prod (invariants σ) := by
  ext x
  simp [mem_invariants, Prod.ext_iff, forall_and]

/-- The invariants of a direct sum of a finite family correspond, under the identification of the
direct sum with the product, to the product of the invariants. -/
theorem invariants_directSum {k G ι : Type*} [CommRing k] [Group G] [Fintype ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i)) :
    invariants (directSum ρ) = (Submodule.pi Set.univ fun i ↦ invariants (ρ i)).comap
      (DirectSum.linearEquivFunOnFintype k ι V).toLinearMap := by
  ext x
  simp only [mem_invariants, directSum_apply, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ,
    true_implies, LinearEquiv.coe_coe, DirectSum.linearEquivFunOnFintype_apply, DirectSum.ext_iff,
    DirectSum.lmap_apply]
  exact forall_comm

/-- Restricting a direct sum along a homomorphism gives the direct sum of the restrictions. -/
@[simp]
theorem prod_comp {k G H V W : Type*} [Semiring k] [Monoid G] [Monoid H] [AddCommMonoid V]
    [Module k V] [AddCommMonoid W] [Module k W] (ρ : Representation k G V)
    (σ : Representation k G W) (f : H →* G) :
    (ρ.prod σ).comp f = Representation.prod (ρ.comp f) (σ.comp f) :=
  MonoidHom.ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

/-- Restricting a direct sum of a family along a homomorphism gives the direct sum of the
restrictions. -/
@[simp]
theorem directSum_comp {k G H ι : Type*} [Semiring k] [Monoid G] [Monoid H] {V : ι → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))
    (f : H →* G) : (directSum ρ).comp f = directSum fun i ↦ (ρ i).comp f :=
  MonoidHom.ext fun _ ↦ by simp

/-- **Invariance may be tested on a generating set**: if `s` generates `G`, a vector is invariant
exactly when every element of `s` fixes it. -/
theorem mem_invariants_iff_of_closure_eq_top {k G V : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {s : Set G}
    (hs : Subgroup.closure s = ⊤) (v : V) : v ∈ ρ.invariants ↔ ∀ g ∈ s, ρ g v = v := by
  refine ⟨fun h g _ ↦ h g, fun h g ↦ ?_⟩
  induction hs.ge (Subgroup.mem_top g) using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul g g' _ _ hg hg' => rw [map_mul, mul_apply_eq_comp, hg', hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

section Subrepresentation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) {W : Submodule k V} (hW : ∀ g, W ≤ W.comap (ρ g))

-- Not `@[simp]`: Mathlib's `@[simp] Representation.mem_invariants` already rewrites the left-hand
-- side, so the attribute would be a `simpNF` violation. This is the `rw`-usable form.
/-- A vector of a `G`-stable submodule `W` is invariant for the restriction of `ρ` to `W` exactly
when it is invariant for `ρ`: the restricted action is the ambient action. -/
theorem mem_invariants_subrepresentation {x : W} :
    x ∈ (ρ.subrepresentation W hW).invariants ↔ (x : V) ∈ ρ.invariants := by
  simp [Subtype.ext_iff]

/-- The invariants of the restriction of `ρ` to a `G`-stable submodule `W` are, as a subspace of
`V`, the invariant vectors of `ρ` lying in `W`. -/
theorem map_subtype_invariants_subrepresentation :
    (ρ.subrepresentation W hW).invariants.map W.subtype = ρ.invariants ⊓ W := by
  ext v
  refine ⟨?_, fun hv ↦ ⟨⟨v, hv.2⟩, (ρ.mem_invariants_subrepresentation hW).2 hv.1, rfl⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨(ρ.mem_invariants_subrepresentation hW).1 hx, x.property⟩

end Subrepresentation

section Quotient

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- **Invariants in stages.** For a normal subgroup `S`, a vector of `V^S` is invariant under
`G ⧸ S` exactly when it is invariant under `G`: `(V^S)^{G/S} = V^G` as submodules of `V`. -/
theorem map_subtype_invariants_quotientToInvariants (S : Subgroup G) [S.Normal] :
    (ρ.quotientToInvariants S).invariants.map (invariants (ρ.comp S.subtype)).subtype =
      ρ.invariants := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ g
    exact congrArg Subtype.val (hw (g : G ⧸ S))
  · intro hv
    refine ⟨⟨v, fun s ↦ hv s⟩, fun q ↦ ?_, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (hv g)

/-- For a normal subgroup `S`, the inclusion identifies the `G ⧸ S`-invariants of `V^S` with the
`G`-invariants of `V`. -/
noncomputable def quotientToInvariantsInvariantsEquiv (S : Subgroup G) [S.Normal] :
    (ρ.quotientToInvariants S).invariants ≃ₗ[k] ρ.invariants :=
  (Submodule.equivMapOfInjective _ (invariants (ρ.comp S.subtype)).injective_subtype _).trans
    (LinearEquiv.ofEq _ _ (map_subtype_invariants_quotientToInvariants ρ S))

@[simp]
theorem coe_quotientToInvariantsInvariantsEquiv_apply (S : Subgroup G) [S.Normal]
    (v : (ρ.quotientToInvariants S).invariants) :
    (ρ.quotientToInvariantsInvariantsEquiv S v : V) = v :=
  (rfl)

@[simp]
theorem coe_coe_quotientToInvariantsInvariantsEquiv_symm_apply (S : Subgroup G) [S.Normal]
    (v : ρ.invariants) :
    (((ρ.quotientToInvariantsInvariantsEquiv S).symm v : invariants (ρ.comp S.subtype)) : V) =
      v := by
  rw [← ρ.coe_quotientToInvariantsInvariantsEquiv_apply S, LinearEquiv.apply_symm_apply]

/-- For subgroups `U' ≤ U`, the invariants of the restriction `ρ|_U` under `U'`, viewed as the
subgroup `U'.subgroupOf U` of `U`, are the `U'`-invariants of `ρ`. Together with
`map_subtype_invariants_quotientToInvariants` applied to `ρ|_U`, this gives
`V^U = (V^{U'})^{U/U'}` when `U'` is normal in `U`. -/
theorem invariants_comp_subtype_subgroupOf {U U' : Subgroup G} (h : U' ≤ U) :
    invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) =
      invariants (ρ.comp U'.subtype) := by
  rw [invariants_comp_comp_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left h]

end Quotient

end Representation

namespace Representation

open scoped MonoidAlgebra

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

section Finite

variable [Fintype G]

/-- An invariant element of the group algebra is the norm of its coefficient at the identity,
over an arbitrary commutative ring. -/
private theorem norm_leftRegular_single_coeff_one {x : MonoidAlgebra k G}
    (hx : x ∈ (leftRegular k G).invariants) :
    (leftRegular k G).norm (MonoidAlgebra.single 1 (x.coeff 1)) = x := by
  ext g
  have hcoeff : x.coeff g = x.coeff 1 := by
    have h := congrArg (fun z : MonoidAlgebra k G => z.coeff g) (hx g)
    simpa using h.symm
  simp [norm, hcoeff]

/-- The norm maps onto the invariants of a free representation, a direct sum of left regular
representations. -/
private theorem range_norm_free_eq_invariants (ι : Type*) :
    LinearMap.range (free k G ι).norm = (free k G ι).invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    have hxi (i : ι) : x i ∈ (leftRegular k G).invariants := fun g => by
      simpa only [finsupp_apply_apply] using DFunLike.congr_fun (hx g) i
    refine ⟨Finsupp.mapRange (fun a => MonoidAlgebra.single 1 (a.coeff 1)) (by simp) x, ?_⟩
    ext i : 1
    rw [← norm_leftRegular_single_coeff_one (hxi i)]
    simp only [norm, LinearMap.sum_apply, Finsupp.finsetSum_apply, finsupp_apply_apply,
      Finsupp.mapRange_apply]

/-- **The norm maps onto the invariants of a projective representation.** Let `G` be finite over
an arbitrary commutative ring `k`. If the `k[G]`-module underlying `ρ` is projective, then every
invariant vector is the norm of a vector.

This is the integral replacement for `Representation.range_norm_eq_invariants`, which assumes
that the order of `G` is invertible in `k`. -/
@[simp]
theorem range_norm_eq_invariants_of_projective (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    LinearMap.range ρ.norm = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact fun g => self_norm_apply _ g x
  · rintro x hx
    obtain ⟨F, S, hFS⟩ := exists_retract_free_of_projective ρ
    have hSx : S x ∈ (free k G V).invariants := fun g => by
      rw [← IntertwiningMap.isIntertwining ρ _ S g x, hx g]
    obtain ⟨y, hy⟩ : S x ∈ LinearMap.range (free k G V).norm := by
      rw [range_norm_free_eq_invariants]
      exact hSx
    have hN : F ((free k G V).norm y) = ρ.norm (F y) := by
      simp only [norm, LinearMap.sum_apply, map_sum, IntertwiningMap.isIntertwining]
    exact ⟨F y, by rw [← hN, hy, hFS]⟩

end Finite

section ChangeRings

variable {l : Type*} [CommRing l] [Finite G]
variable {X : Type*} [AddCommGroup X] [Module l X]

/-- **Equivariant surjections lift invariants when the target is projective.** Let `ρ` and `σ` be
representations of the same finite group, possibly over different commutative rings. If an
equivariant additive map `f : V →+ X` is surjective and `σ.asModule` is projective over `l[G]`,
then every invariant vector of `σ` has an invariant preimage under `f`.

Allowing the coefficient rings to differ is essential for reduction of an integral projective
lattice modulo a prime. -/
-- The target invariant is a group norm; lift a preimage before taking the norm, and use
-- equivariance to commute `f` with the two norms.
theorem exists_invariant_preimage_of_surjective_of_projective
    (ρ : Representation k G V) (σ : Representation l G X)
    (f : V →+ X) (hf : Function.Surjective f)
    (hfg : ∀ g x, f (ρ g x) = σ g (f x))
    [Module.Projective l[G] σ.asModule]
    (y : σ.invariants) : ∃ x : ρ.invariants, f x = y := by
  let _ := Fintype.ofFinite G
  have hy : (y : X) ∈ LinearMap.range σ.norm := by
    rw [range_norm_eq_invariants_of_projective]
    exact y.property
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, rfl⟩ := hf z
  refine ⟨⟨ρ.norm x, fun g => self_norm_apply ρ g x⟩, ?_⟩
  rw [← hz]
  simp only [norm, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => hfg g x

end ChangeRings

end Representation

namespace Representation.IntertwiningMap

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- **An intertwining map preserves invariants.** The linear map `V^G → W^G` induced by an
intertwining map `V → W`. -/
noncomputable def invariantsMap (f : ρ.IntertwiningMap σ) : ρ.invariants →ₗ[k] σ.invariants :=
  f.toLinearMap.restrict fun v hv g ↦ by simpa [f.isIntertwining] using congrArg f (hv g)

@[simp]
theorem coe_invariantsMap_apply (f : ρ.IntertwiningMap σ) (x : ρ.invariants) :
    (f.invariantsMap x : W) = f (x : V) :=
  (rfl)

/-- The map induced on invariants by an injective intertwining map is injective. -/
theorem invariantsMap_injective (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective f.invariantsMap :=
  fun _ _ h ↦ Subtype.ext (hf (by simpa using congrArg Subtype.val h))

/-- The identity intertwining map induces the identity on invariants. -/
@[simp]
theorem invariantsMap_id : (IntertwiningMap.id ρ).invariantsMap = LinearMap.id := by
  ext
  rfl

/-- The map induced on invariants by a composite is the composite of the induced maps. -/
@[simp]
theorem invariantsMap_comp {X : Type*} [AddCommGroup X] [Module k X] {τ : Representation k G X}
    (f : σ.IntertwiningMap τ) (g : ρ.IntertwiningMap σ) :
    (f.comp g).invariantsMap = f.invariantsMap ∘ₗ g.invariantsMap := by
  ext
  rfl

end Representation.IntertwiningMap

namespace Representation.Equiv

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}

/-- **Equivalent representations have isomorphic invariants.** An equivalence of
representations maps invariant vectors to invariant vectors, and so does its inverse. -/
def invariantsLinearEquiv (φ : ρ.Equiv σ) : ρ.invariants ≃ₗ[k] σ.invariants where
  toFun x := ⟨φ x, fun g ↦
    (IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g x).symm.trans
      (congrArg φ (x.property g))⟩
  invFun x := ⟨φ.symm x, fun g ↦
    (IntertwiningMap.isIntertwining σ ρ φ.symm.toIntertwiningMap g x).symm.trans
      (congrArg φ.symm (x.property g))⟩
  map_add' x y := Subtype.ext (map_add φ (x : V) y)
  map_smul' r x := Subtype.ext (map_smul φ r (x : V))
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : V))
  right_inv x := Subtype.ext (φ.apply_symm_apply (x : W))

@[simp]
theorem coe_invariantsLinearEquiv_apply (φ : ρ.Equiv σ) (x : ρ.invariants) :
    (φ.invariantsLinearEquiv x : W) = φ (x : V) :=
  (rfl)

/-- The linear map underlying `invariantsLinearEquiv` is the map induced on invariants by the
underlying intertwining map. -/
theorem toLinearMap_invariantsLinearEquiv (φ : ρ.Equiv σ) :
    φ.invariantsLinearEquiv.toLinearMap = φ.toIntertwiningMap.invariantsMap := by
  ext
  rfl

/-- **Equivalent representations have equivalent quotient representations on invariants.** For a
normal subgroup `S` of `G`, an equivalence `ρ ≃ σ` restricts to the `S`-invariants and there
intertwines the representations `ρ.quotientToInvariants S` and `σ.quotientToInvariants S` of
`G ⧸ S`. -/
noncomputable def quotientToInvariants (φ : ρ.Equiv σ) (S : Subgroup G) [S.Normal] :
    (ρ.quotientToInvariants S).Equiv (σ.quotientToInvariants S) :=
  .mk (φ.res S.subtype).invariantsLinearEquiv fun g ↦ by
    induction g using QuotientGroup.induction_on with | H g => ?_
    ext x
    simpa [ofQuotient_coe_apply] using
      IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g x

@[simp]
theorem coe_quotientToInvariants_apply (φ : ρ.Equiv σ) (S : Subgroup G) [S.Normal]
    (x : invariants (ρ.comp S.subtype)) : (φ.quotientToInvariants S x : W) = φ (x : V) := by
  simp [quotientToInvariants]

@[simp]
theorem symm_quotientToInvariants (φ : ρ.Equiv σ) (S : Subgroup G) [S.Normal] :
    (φ.quotientToInvariants S).symm = φ.symm.quotientToInvariants S := by
  ext x
  obtain ⟨y, rfl⟩ := (φ.quotientToInvariants S).surjective x
  simp

/-- An equivalence of representations maps a vector to an invariant vector exactly when the
vector itself is invariant. -/
theorem apply_mem_invariants_iff (φ : ρ.Equiv σ) {x : V} :
    φ x ∈ σ.invariants ↔ x ∈ ρ.invariants :=
  ⟨fun hx g ↦ φ.toLinearEquiv.injective <|
      (IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g x).trans (hx g),
    fun hx ↦ (φ.invariantsLinearEquiv ⟨x, hx⟩).property⟩

end Representation.Equiv

namespace Representation

variable {k G H V V' W W' : Type*} [CommRing k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

/-- The tensor product of invariant vectors is an invariant vector of the tensor product
representation. -/
theorem tmul_mem_invariants_tprod {X : Representation k G V} {Y : Representation k G W}
    {v : V} {w : W} (hv : v ∈ X.invariants) (hw : w ∈ Y.invariants) :
    v ⊗ₜ[k] w ∈ (X.tprod Y).invariants :=
  fun g ↦ by rw [tprod_apply, TensorProduct.map_tmul, hv g, hw g]

/-- **Invariant dimensions of tensor products along a surjective homomorphism of groups.** If the
restrictions of `X` and `Y` along a surjective `f : G →* H` are equivalent to `X'` and `Y'`, then
`X ⊗ Y` and `X' ⊗ Y'` have invariants of the same dimension: restriction along `f` does not change
the invariants (`Representation.invariants_comp_of_surjective`), and it commutes with tensor
products. -/
theorem finrank_invariants_tprod_of_comp {f : G →* H} (hf : Function.Surjective f)
    {X : Representation k H V} {Y : Representation k H W} {X' : Representation k G V'}
    {Y' : Representation k G W'} (e₁ : Equiv (X.comp f) X') (e₂ : Equiv (Y.comp f) Y') :
    Module.finrank k (X.tprod Y).invariants = Module.finrank k (X'.tprod Y').invariants := by
  rw [← invariants_comp_of_surjective (X.tprod Y) f hf]
  exact (e₁.tprod e₂).invariantsLinearEquiv.finrank_eq

end Representation

namespace Rep

open CategoryTheory
open scoped MonoidAlgebra

/-- A vector in the kernel of `ρ(g) - 1` is fixed by `g`. -/
@[simp]
theorem ρ_apply_of_mem_ker {k G : Type*} [Semiring k] [CommMonoid G] (A : Rep k G) (g : G)
    (x : LinearMap.ker (applyAsHom A g - 𝟙 A).hom.toLinearMap) : A.ρ g x.val = x.val := by
  simpa [sub_hom, sub_eq_zero] using x.property

/-- For the trivial representation, `ρ(g) - 𝟙` vanishes. -/
@[simp]
theorem applyAsHom_trivial_sub_id_apply {k G : Type*} [Semiring k] [CommMonoid G] (g : G)
    (M : Type*) [AddCommGroup M] [Module k M] (x : M) :
    (applyAsHom (Rep.trivial k G M) g - 𝟙 (Rep.trivial k G M)).hom x = 0 := by
  simp [Rep.applyAsHom, sub_hom]

/-- For the trivial representation, the norm is multiplication by the group order. -/
@[simp]
theorem norm_trivial_hom_apply (k : Type*) {G : Type*} [Semiring k] [Group G] [Fintype G]
    {M : Type*} [AddCommGroup M] [Module k M] (x : M) :
    (Rep.trivial k G M).norm.asHom.hom x = (Nat.card G : k) • x :=
  (Rep.norm_apply _).trans (Representation.norm_trivial_apply k G x)

variable {k G : Type*} [CommRing k] [Group G]

/-- **Invariants preserve surjections onto projective representations.** If `f : A ⟶ B` is
surjective and the `k[G]`-module underlying `B` is projective, then every invariant of `B` lifts
to an invariant of `A`. -/
theorem invariantsFunctor_map_surjective_of_projective {A B : Rep k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) [Module.Projective k[G] B.ρ.asModule] :
    Function.Surjective ((invariantsFunctor k G).map f).hom := by
  have : Projective B := by
    rw [← equivalenceModuleMonoidAlgebra.map_projective_iff]
    exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of k[G] B.ρ.asModule)
  have : Epi f := (epi_iff_surjective f).2 hf
  have : IsSplitEpi f := ⟨⟨Projective.factorThru (𝟙 B) f, Projective.factorThru_comp _ _⟩⟩
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- **Intertwiners out of the trivial line are the invariant vectors.** A morphism
`Rep.trivial k G k ⟶ A` is determined by the image of `1`, which is invariant, and an invariant
vector `x` is the image of `1` under `r ↦ r • x`. -/
noncomputable def trivialHomEquivInvariants (A : Rep k G) :
    (Rep.trivial k G k ⟶ A) ≃ₗ[k] A.ρ.invariants where
  toFun f := ⟨f.hom 1, fun g ↦ by simpa using (hom_comm_apply f g 1).symm⟩
  invFun x := ConcreteCategory.ofHom
    ⟨LinearMap.toSpanSingleton k A x, fun g ↦ LinearMap.ext fun r ↦ by simp [x.property g]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext_ring <| one_smul k _
  right_inv x := Subtype.ext (one_smul k (x : A))

@[simp]
theorem coe_trivialHomEquivInvariants_apply (A : Rep k G) (f : Rep.trivial k G k ⟶ A) :
    (trivialHomEquivInvariants A f : A) = f.hom 1 :=
  (rfl)

@[simp]
theorem trivialHomEquivInvariants_symm_apply_hom (A : Rep k G) (x : A.ρ.invariants) (r : k) :
    ((trivialHomEquivInvariants A).symm x).hom r = r • (x : A) :=
  (rfl)

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

namespace Rep

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- The underlying vector of the image of an invariant under `(invariantsFunctor k G).map f` is
its image under `f`. -/
theorem invariantsFunctor_map_hom_apply_coe {k : Type u} {G : Type v} [CommRing k] [Group G]
    {A B : Rep.{w} k G} (f : A ⟶ B) (x : A.ρ.invariants) :
    (((invariantsFunctor k G).map f).hom x : B.ρ.invariants).val = f.hom x :=
  rfl

section Invertible

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

/-- **Invariants preserve surjections when the group order is invertible.** If `#G` is invertible
in `k` and `f : A ⟶ B` is surjective, every invariant `y` of `B` lifts to an invariant of `A`: the
average of any preimage of `y`. No projectivity of `B` over `k[G]` is needed, in contrast with
`Rep.invariantsFunctor_map_surjective_of_projective`. -/
theorem invariantsFunctor_map_surjective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) :
    Function.Surjective ((invariantsFunctor k G).map f).hom := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨⟨A.ρ.averageMap x, A.ρ.averageMap_invariant x⟩, Subtype.ext ?_⟩
  rw [invariantsFunctor_map_hom_apply_coe]
  exact (Representation.IntertwiningMap.map_averageMap f.hom x).trans (B.ρ.averageMap_id _ hy)

/-- When `#G` is invertible in `k`, taking invariants preserves epimorphisms. -/
instance : (invariantsFunctor.{w} k G).PreservesEpimorphisms where
  preserves f hf := (ModuleCat.epi_iff_surjective _).2 <|
    invariantsFunctor_map_surjective f ((epi_iff_surjective f).1 hf)

/-- When `#G` is invertible in `k`, taking invariants is an exact functor: it preserves kernels
as a right adjoint, and epimorphisms by averaging. -/
instance : (invariantsFunctor.{w} k G).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- When `#G` is invertible in `k`, taking invariants preserves finite colimits. -/
instance : PreservesFiniteColimits (invariantsFunctor.{w} k G) :=
  (invariantsFunctor k G).preservesFiniteColimits_of_preservesHomology

end Invertible

/-- **Invariants are exact exactly when the group order is a unit.** For a finite group `G`,
taking invariants preserves epimorphisms of `k`-linear representations if and only if `#G` is a
unit of `k`. For the converse, apply it to the augmentation `k[G] ⟶ k`: an invariant of `k[G]`
has constant coefficients, so the augmentation sends it into the ideal generated by `#G`. Over
`ZMod 2` with `G` of order two, the surjection `k[G] ⟶ k` thus maps the invariants to zero. -/
theorem preservesEpimorphisms_invariantsFunctor_iff {k : Type u} {G : Type v} [CommRing k]
    [Group G] [Finite G] :
    (invariantsFunctor.{max u v} k G).PreservesEpimorphisms ↔ IsUnit (Nat.card G : k) := by
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · -- The augmentation `ε : k[G] ⟶ k`, `[g] ↦ 1`, is surjective. Its target is `k` lifted to the
    -- universe of `k[G]`.
    let ε : leftRegular k G ⟶ trivial k G (ULift.{v} k) :=
      leftRegularHom (trivial k G (ULift.{v} k)) ⟨1⟩
    have : Epi ε := (epi_iff_surjective ε).2 fun r ↦ ⟨.single 1 r.down, by ext; simp [ε]⟩
    obtain ⟨⟨x, hx⟩, hx1⟩ := (ModuleCat.epi_iff_surjective _).1
      ((invariantsFunctor k G).map_epi ε) ⟨⟨1⟩, fun _ ↦ rfl⟩
    have hconst (g : G) : x.coeff g = x.coeff 1 := by
      simpa [Representation.coeff_ofMulAction] using (congrArg (·.coeff g) (hx g)).symm
    have hsum : (ε.hom x).down = ∑ g : G, x.coeff g := by
      simp [ε, leftRegularHom, Finsupp.sum_fintype, ← Finset.sum_smul]
    have h1 : (ε.hom x).down = 1 :=
      congrArg ULift.down
        ((invariantsFunctor_map_hom_apply_coe ε ⟨x, hx⟩).symm.trans (congrArg Subtype.val hx1))
    simp only [hsum, hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card] at h1
    exact IsUnit.of_mul_eq_one _ h1
  · have : Invertible (Fintype.card G : k) := (Nat.card_eq_fintype_card (α := G) ▸ h).invertible
    infer_instance

section Filtered

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

open Types.FilteredColimit in
/-- **Finitely many symmetries of a filtered colimit hold at some stage.** If the image in a
filtered colimit of a vector `v` is fixed by every element of a finite set `s`, then so is the
image of `v` under some map out of its stage: each equation `g • v = v` holds at a later stage, and
one stage serves all of them. -/
theorem exists_map_apply_eq_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Rep.{u} k G} {c : Cocone D} (hc : IsColimit c) {i : J} (v : D.obj i) (s : Finset G)
    (hs : ∀ g ∈ s, c.pt.ρ g ((c.ι.app i).hom v) = (c.ι.app i).hom v) :
    ∃ (j : J) (f : i ⟶ j), ∀ g ∈ s, (D.obj j).ρ g ((D.map f).hom v) = (D.map f).hom v := by
  classical
  -- Filtered colimits of representations are computed on underlying sets, where they are
  -- described elementwise.
  let hT := isColimitOfPreserves (forget₂ (Rep.{u} k G) (ModuleCat.{u} k) ⋙
    forget (ModuleCat.{u} k)) hc
  -- For each `g ∈ s` the vectors `g • v` and `v` have the same image, so they agree at a later
  -- stage, recorded as an object of the filtered category `Under i`.
  have hg (g : s) : ∃ X : Under i, (D.map X.hom).hom ((D.obj i).ρ g v) = (D.map X.hom).hom v := by
    have h : (c.ι.app i).hom ((D.obj i).ρ g v) = (c.ι.app i).hom v := by
      rw [hom_comm_apply]
      exact hs g g.property
    obtain ⟨j, f, hf⟩ := (isColimit_eq_iff' hT _ _).1 h
    exact ⟨Under.mk f, hf⟩
  choose X hX using hg
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (Finset.univ.image X)
  refine ⟨S.right, S.hom, fun g hg ↦ ?_⟩
  obtain ⟨m⟩ := hS (Finset.mem_image_of_mem X (Finset.mem_univ ⟨g, hg⟩))
  rw [← Under.w m, Functor.map_comp]
  simp only [hom_comp, Representation.IntertwiningMap.comp_apply, ← hom_comm_apply, hX]

open Types.FilteredColimit in
/-- **Invariants of a finitely generated group commute with filtered colimits.** An invariant of
the colimit comes from a vector at some stage. It is invariant as soon as it is fixed by a finite
generating set `s`, and the finitely many equations `g • v = v` for `g ∈ s` hold at a common later
stage. In particular this applies to finite groups, and no invertibility of `#G` is needed. -/
instance [IsMulFG G] : PreservesFilteredColimits (invariantsFunctor.{u} k G) where
  preserves_filtered_colimits J _ _ := ⟨fun {D} ↦ ⟨fun {c} hc ↦ by
    obtain ⟨s, hs⟩ := Group.exists_of_isMulFG G
    -- Filtered colimits of representations are computed on underlying sets, where they are
    -- described elementwise.
    let hT := isColimitOfPreserves (forget₂ (Rep.{u} k G) (ModuleCat.{u} k) ⋙
      forget (ModuleCat.{u} k)) hc
    refine ⟨isColimitOfReflects (forget (ModuleCat.{u} k)) (isColimitOf _ _ ?_ ?_)⟩
    · rintro ⟨x, hx⟩
      obtain ⟨i, v, hv⟩ := Types.jointly_surjective_of_isColimit hT x
      -- The underlying function of a morphism of representations, after `forget₂` and `forget`,
      -- is its `hom` by definition.
      replace hv : (c.ι.app i).hom v = x := hv
      obtain ⟨j, f, hf⟩ := exists_map_apply_eq_of_isColimit hc v s fun g _ ↦ hv ▸ hx g
      refine ⟨j, ⟨(D.map f).hom v,
        (Representation.mem_invariants_iff_of_closure_eq_top _ hs _).2 hf⟩, ?_⟩
      -- The image of `D.map f v` in the colimit is that of `v`, by naturality of `c`.
      refine Subtype.ext (hv.symm.trans ?_)
      rw [← c.w f, hom_comp, Representation.IntertwiningMap.comp_apply]
      simp only [Functor.mapCocone_ι_app, TypeCat.ofHom_apply]
      rw [invariantsFunctor_map_hom_apply_coe]
    · intro i j xi xj h
      obtain ⟨l, f, g, hfg⟩ := (isColimit_eq_iff _ hT).1 (congrArg Subtype.val h)
      exact ⟨l, f, g, Subtype.ext hfg⟩⟩⟩

end Filtered

end Rep

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [NeZero (Nat.card G : k)]

/-- Invariant dimension is additive on short exact sequences of finite-dimensional
representations when the group order is invertible in the coefficient field. -/
theorem FDRep.finrank_invariants_add_of_shortExact {S : ShortComplex (FDRep k G)}
    (hS : S.ShortExact) :
    Module.finrank k (Representation.invariants S.X₂.ρ) =
      Module.finrank k (Representation.invariants S.X₁.ρ) +
        Module.finrank k (Representation.invariants S.X₃.ρ) := by
  -- A nonzero cardinality in `k` forces `G` to be finite, with invertible order.
  have : Finite G := Nat.finite_of_card_ne_zero fun h ↦ NeZero.ne (Nat.card G : k) (by simp [h])
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Nat.card_eq_fintype_card (α := G) ▸ NeZero.ne (Nat.card G : k))
  have hInv := (hS.map_of_exact (forget₂ (FDRep k G) (Rep k G))).map_of_exact
    (Rep.invariantsFunctor k G)
  -- `Rep.invariantsFunctor` sends `forget₂ V` to the invariant subspace of `V.ρ`
  -- (`Rep.invariantsFunctor_obj_carrier`, `FDRep.forget₂_ρ`).
  have hfinrank (V : FDRep k G) :
      Module.finrank k ((Rep.invariantsFunctor k G).obj ((forget₂ (FDRep k G) (Rep k G)).obj V)) =
        Module.finrank k (Representation.invariants V.ρ) :=
    rfl
  have hfinite (V : FDRep k G) :
      Module.Finite k ((Rep.invariantsFunctor k G).obj ((forget₂ (FDRep k G) (Rep k G)).obj V)) :=
    Module.Finite.of_injective (Representation.invariants V.ρ).subtype Subtype.coe_injective
  have : Module.Finite k ((S.map (forget₂ (FDRep k G) (Rep k G))).map
      (Rep.invariantsFunctor k G)).X₁ := hfinite S.X₁
  have : Module.Finite k ((S.map (forget₂ (FDRep k G) (Rep k G))).map
      (Rep.invariantsFunctor k G)).X₃ := hfinite S.X₃
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃, hfinrank] using
    ModuleCat.free_shortExact_finrank_add hInv rfl rfl

end TauCeti

namespace CategoryTheory.Functor

universe u v u' v'

section Monoid

variable {A : Type u} {B : Type u'} [Ring A] [Ring B] {G : Type*} [Monoid G]
  {M : Type v} [AddCommGroup M] [Module A M] (F : ModuleCat.{v} A ⥤ ModuleCat.{v'} B)

/-- A functor `F : ModuleCat A ⥤ ModuleCat B` carries a representation `σ` of `G` by `A`-linear
maps on `M` to the representation `g ↦ F(σ g)` of `G` on `F(M)`, through the action
`CategoryTheory.Functor.mapEnd` of `F` on endomorphisms. This is the representation-level form of
`CategoryTheory.Functor.mapAction`. -/
noncomputable def mapRepresentation (σ : Representation A G M) :
    Representation B G (F.obj (ModuleCat.of A M)) :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp <| (Functor.mapEnd (ModuleCat.of A M) F).comp <|
    (ModuleCat.endRingEquiv (ModuleCat.of A M)).symm.toMonoidHom.comp σ

/-- The element `g` acts on `F(M)` by `F(σ g)`. -/
@[simp]
theorem mapRepresentation_apply (σ : Representation A G M) (g : G) :
    F.mapRepresentation σ g = (F.map (ModuleCat.ofHom (σ g))).hom :=
  (rfl)

end Monoid

section Injective

variable {A : Type u} {B : Type u'} [CommRing A] [Ring B] {G : Type*} [Group G]
  {M : Type v} [AddCommGroup M] [Module A M] (F : ModuleCat.{v} A ⥤ ModuleCat.{v'} B)

variable [Fintype G] [Invertible (Fintype.card G : A)] (σ : Representation A G M)

/-- When `#G` is invertible in `A`, every functor `F` carries the inclusion `M^G ⊆ M` of the
invariants to an injective map, since the averaging projection retracts the inclusion. For an
additive `F`, this identifies `F(M^G)` with the invariants of `F(M)`
(`CategoryTheory.Functor.invariants_mapRepresentation`). The target coefficient ring `B` need not
be commutative. -/
theorem map_ofHom_subtype_invariants_injective :
    Function.Injective (F.map (ModuleCat.ofHom σ.invariants.subtype)).hom := by
  -- The inclusion has the retraction given by the averaging projection.
  let π : ModuleCat.of A M ⟶ ModuleCat.of A σ.invariants :=
    ModuleCat.ofHom (σ.averageMap.codRestrict σ.invariants σ.averageMap_invariant)
  have h : ModuleCat.ofHom σ.invariants.subtype ≫ π = 𝟙 _ := by
    ext m
    exact σ.averageMap_id m m.property
  refine Function.LeftInverse.injective (g := (F.map π).hom) fun y ↦ ?_
  rw [← ModuleCat.comp_apply, ← F.map_comp, h, F.map_id, ModuleCat.id_apply]

end Injective

variable {A : Type u} {B : Type u'} [CommRing A] [CommRing B] {G : Type*} [Group G]
  {M : Type v} [AddCommGroup M] [Module A M] (F : ModuleCat.{v} A ⥤ ModuleCat.{v'} B)

variable [Fintype G] [Invertible (Fintype.card G : A)] (σ : Representation A G M) [F.Additive]

/-- **Additive functors commute with invariants.** When `#G` is invertible in `A`, the invariants
of `F(M)` are the image of `F(M^G)` under `F` applied to the inclusion `M^G ⊆ M`. -/
theorem invariants_mapRepresentation :
    (F.mapRepresentation σ).invariants =
      LinearMap.range (F.map (ModuleCat.ofHom σ.invariants.subtype)).hom := by
  -- The averaging projection factors as `π ≫ ι` through the invariants, and is the group sum
  -- `σ.norm` followed by multiplication `u` by `⅟#G`.
  let π : ModuleCat.of A M ⟶ ModuleCat.of A σ.invariants :=
    ModuleCat.ofHom (σ.averageMap.codRestrict σ.invariants σ.averageMap_invariant)
  let ι : ModuleCat.of A σ.invariants ⟶ ModuleCat.of A M := ModuleCat.ofHom σ.invariants.subtype
  let u : ModuleCat.of A M ⟶ ModuleCat.of A M :=
    ModuleCat.ofHom (⅟(Fintype.card G : A) • LinearMap.id)
  have hu : Fintype.card G • u = 𝟙 _ := by
    ext m
    simp [u, ← Nat.cast_smul_eq_nsmul A, smul_smul]
  have havg : ModuleCat.ofHom σ.norm ≫ u = π ≫ ι := by
    ext m
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      u, π, ι, Submodule.subtype_apply, LinearMap.codRestrict_apply, σ.averageMap_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Representation.norm, LinearMap.sum_apply]
  have hnorm : ModuleCat.ofHom σ.norm = ∑ g : G, ModuleCat.ofHom (σ g) := by
    ext m
    simp [Representation.norm]
  apply le_antisymm
  · intro x hx
    refine ⟨(F.map π).hom x, ?_⟩
    -- On an invariant `x`, `F(σ.norm)` is multiplication by `#G`, which `F(u)` inverts.
    have h₁ : (F.map (ModuleCat.ofHom σ.norm)).hom x = Fintype.card G • x := by
      rw [hnorm, F.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
      exact (Finset.sum_congr rfl fun g _ ↦ hx g).trans (by simp)
    have h₂ : (F.map u).hom (Fintype.card G • x) = x := by
      rw [_root_.map_nsmul, ← LinearMap.smul_apply, ← ModuleCat.hom_nsmul, ← F.map_nsmul, hu,
        F.map_id, ModuleCat.id_apply]
    rw [← ModuleCat.comp_apply, ← F.map_comp, ← havg, F.map_comp, ModuleCat.comp_apply, h₁, h₂]
  · rintro _ ⟨y, rfl⟩ g
    have h : ι ≫ ModuleCat.ofHom (σ g) = ι := by
      ext m
      exact m.property g
    rw [mapRepresentation_apply, ← ModuleCat.comp_apply, ← F.map_comp, h]

end CategoryTheory.Functor
