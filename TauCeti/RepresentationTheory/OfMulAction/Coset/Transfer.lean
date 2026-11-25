/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction.Coset.Lift
public import TauCeti.RepresentationTheory.RelativeNorm
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Stabilizer

/-!
# Inclusion and trace of invariants through permutation representations

Let `U' ≤ U` be subgroups of a group `G` (in practice compact open subgroups of a locally
profinite group) and `A` a semiring. When `A` is a commutative ring, through
`V^U = Hom_G(A[G ⧸ U], V)` (`Representation.ofMulActionQuotientMapEquiv`), maps between the
invariants of a representation for `U` and `U'` come from maps between the permutation
representations:

* the projection `A[G ⧸ U'] → A[G ⧸ U]`, `g U' ↦ g U` (`Representation.cosetProjection`), induces
  the inclusion `V^U ⊆ V^{U'}`
  (`Representation.coe_ofMulActionQuotientMapEquiv_comp_cosetProjection`);
* for `U'` of finite index in `U`, the transfer `A[G ⧸ U] → A[G ⧸ U']`,
  `g U ↦ ∑_{u ∈ U ⧸ U'} g u U'` (`Representation.cosetTransfer`), induces the trace
  `tr_{U/U'}(v) = ∑_{u ∈ U ⧸ U'} ρ(u) v`, the relative norm `Representation.relNorm` of `U'` in
  `U` (`Representation.coe_ofMulActionQuotientMapEquiv_comp_cosetTransfer`).

The projection after the transfer is multiplication by the index `[U : U']`
(`Representation.cosetProjection_comp_cosetTransfer`), so `tr_{U/U'} ∘ incl = [U : U']` on `V^U`.

## Main definitions

* `Representation.cosetProjection`: the projection `A[G ⧸ U'] → A[G ⧸ U]`.
* `Representation.cosetTransfer`: the transfer `A[G ⧸ U] → A[G ⧸ U']`.

## Main results

* `Representation.coe_ofMulActionQuotientMapEquiv_comp_cosetProjection`: the projection induces
  the inclusion of invariants.
* `Representation.coe_ofMulActionQuotientMapEquiv_comp_cosetTransfer`: the transfer induces the
  trace.
* `Representation.cosetProjection_comp_cosetTransfer`: projection after transfer is `[U : U']`.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
-/

public section
noncomputable section

namespace Representation

section Semiring

variable {A G : Type*} [Semiring A] [Group G] {U' U : Subgroup G}

variable (A) in
/-- The **projection** `A[G ⧸ U'] → A[G ⧸ U]`, `g U' ↦ g U`, for `U' ≤ U`. -/
def cosetProjection (hU : U' ≤ U) :
    IntertwiningMap (ofMulAction A G (G ⧸ U')) (ofMulAction A G (G ⧸ U)) :=
  (ofMulAction A G (G ⧸ U)).cosetLift U' _
    (hU.trans (IntertwiningMap.id _).le_stabilizer_apply_single_one)

@[simp]
theorem cosetProjection_single (hU : U' ≤ U) (g : G) (c : A) :
    cosetProjection A hU (MonoidAlgebra.single (g : G ⧸ U') c) =
      MonoidAlgebra.single (g : G ⧸ U) c := by
  simp [cosetProjection, ofMulAction_single]

variable [Fintype (U ⧸ U'.subgroupOf U)]

variable (A U' U) in
/-- The sum `∑_{u ∈ U ⧸ U'} u U'` of the cosets of `U'` contained in `U`, a `U`-invariant vector
of `A[G ⧸ U']`. -/
private def cosetSum : MonoidAlgebra A (G ⧸ U') :=
  relNorm ((ofMulAction A G (G ⧸ U')).comp U.subtype) (U'.subgroupOf U)
    (MonoidAlgebra.single ((1 : G) : G ⧸ U') 1)

/-- An element of a subgroup `H` lying in `U` fixes the coset `U` under the restriction of
`A[G ⧸ U]` to `H`. -/
private theorem comp_subtype_apply_single_one {H : Subgroup G} (u : H) (hu : (u : G) ∈ U) :
    (ofMulAction A G (G ⧸ U)).comp H.subtype u (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) =
      MonoidAlgebra.single ((1 : G) : G ⧸ U) 1 := by
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply]
  exact mem_stabilizer.1 ((IntertwiningMap.id _).le_stabilizer_apply_single_one hu)

private theorem le_stabilizer_cosetSum :
    U ≤ (ofMulAction A G (G ⧸ U')).stabilizer (cosetSum A U' U) := fun u hu ↦ by
  rw [mem_stabilizer, cosetSum]
  have := relNorm_apply_eq_self ((ofMulAction A G (G ⧸ U')).comp U.subtype)
    (H := U'.subgroupOf U)
    (fun h ↦ comp_subtype_apply_single_one (h : U) (Subgroup.mem_subgroupOf.1 h.property))
    ⟨u, hu⟩
  rwa [MonoidHom.comp_apply, Subgroup.subtype_apply] at this

variable (A U') in
/-- The **transfer** `A[G ⧸ U] → A[G ⧸ U']`, `g U ↦ ∑_{u ∈ U ⧸ U'} g u U'`, for `U'` of finite
index in `U`. -/
def cosetTransfer : IntertwiningMap (ofMulAction A G (G ⧸ U)) (ofMulAction A G (G ⧸ U')) :=
  (ofMulAction A G (G ⧸ U')).cosetLift U _ le_stabilizer_cosetSum

private theorem cosetTransfer_single_one_eq_cosetSum :
    cosetTransfer A U' (U := U) (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) = cosetSum A U' U := by
  simp [cosetTransfer]

/-- The transfer sends the coset `g U` to the sum of the cosets `g u U'`, `u ∈ U ⧸ U'`. -/
@[simp]
theorem cosetTransfer_single (g : G) (c : A) :
    cosetTransfer A U' (MonoidAlgebra.single (g : G ⧸ U) c) =
      ∑ q : U ⧸ U'.subgroupOf U, MonoidAlgebra.single ((g * ((q.out : U) : G) : G) : G ⧸ U') c := by
  simp [cosetTransfer, cosetSum, relNorm_apply, ofMulAction_single, Finset.smul_sum,
    Subgroup.smul_def]

/-- **Projection after transfer is the index**: `A[G ⧸ U] → A[G ⧸ U'] → A[G ⧸ U]` is
multiplication by `[U : U']`. -/
theorem cosetProjection_comp_cosetTransfer (hU : U' ≤ U) :
    (cosetProjection A hU).comp (cosetTransfer A U') =
      U'.relIndex U • IntertwiningMap.id (ofMulAction A G (G ⧸ U)) := by
  ext1
  simp only [IntertwiningMap.comp_apply, cosetTransfer_single_one_eq_cosetSum, cosetSum,
    IntertwiningMap.map_relNorm_comp, cosetProjection_single]
  rw [relNorm_apply_of_forall_apply_eq ((ofMulAction A G (G ⧸ U)).comp U.subtype) fun u ↦
      comp_subtype_apply_single_one u u.property]
  simp [Subgroup.relIndex]

end Semiring

section CommRing

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  (ρ : Representation A G V) {U' U : Subgroup G}

/-- **The projection induces the inclusion** `V^U ⊆ V^{U'}`: the `U'`-invariant vector attached to
the intertwining map `A[G ⧸ U'] → A[G ⧸ U] → V` of `v ∈ V^U` is `v` itself. -/
theorem coe_ofMulActionQuotientMapEquiv_comp_cosetProjection (hU : U' ≤ U)
    (v : invariants (ρ.comp U.subtype)) :
    (ρ.ofMulActionQuotientMapEquiv U'
        (((ρ.ofMulActionQuotientMapEquiv U).symm v).comp (cosetProjection A hU)) : V) = v := by
  simp [IntertwiningMap.comp_apply]

variable [Fintype (U ⧸ U'.subgroupOf U)]

/-- **The transfer induces the trace**: the `U`-invariant vector attached to the intertwining map
`A[G ⧸ U] → A[G ⧸ U'] → V` of `v ∈ V^{U'}` is `tr_{U/U'}(v) = ∑_{u ∈ U ⧸ U'} ρ(u) v`. -/
theorem coe_ofMulActionQuotientMapEquiv_comp_cosetTransfer (v : invariants (ρ.comp U'.subtype)) :
    (ρ.ofMulActionQuotientMapEquiv U
        (((ρ.ofMulActionQuotientMapEquiv U').symm v).comp (cosetTransfer A U')) : V) =
      relNorm (ρ.comp U.subtype) (U'.subgroupOf U) v := by
  rw [coe_ofMulActionQuotientMapEquiv_apply, IntertwiningMap.comp_apply,
    cosetTransfer_single_one_eq_cosetSum, cosetSum, IntertwiningMap.map_relNorm_comp]
  simp

end CommRing

end Representation
