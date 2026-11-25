/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction.CosetLift
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Inclusion and trace of invariants through permutation representations

Let `U' ≤ U` be subgroups of a group `G` (in practice compact open subgroups of a locally
profinite group) and `A` a commutative ring. Through `V^U = Hom_G(A[G ⧸ U], V)`
(`Representation.ofMulActionQuotientMapEquiv`), maps between the invariants of a representation
for `U` and `U'` come from maps between the permutation representations:

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

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  (ρ : Representation A G V) {U' U : Subgroup G}

/-- An intertwining map commutes with the relative norm of a subgroup of the acting group. -/
private theorem map_relNorm_comp {W : Type*} [AddCommGroup W] [Module A W]
    {σ : Representation A G W} (f : IntertwiningMap ρ σ) (H : Subgroup U)
    [Fintype (U ⧸ H)] (x : V) :
    f (relNorm (ρ.comp U.subtype) H x) = relNorm (σ.comp U.subtype) H (f x) := by
  simp only [relNorm_apply, map_sum, MonoidHom.comp_apply, f.isIntertwining]

/-- The basis vector of the coset `U` is fixed by `U`. -/
private theorem le_stabilizer_single_one (U : Subgroup G) :
    U ≤ (ofMulAction A G (G ⧸ U)).stabilizer (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) :=
  (IntertwiningMap.id (ofMulAction A G (G ⧸ U))).le_stabilizer_apply_single_one

variable (A) in
/-- The **projection** `A[G ⧸ U'] → A[G ⧸ U]`, `g U' ↦ g U`, for `U' ≤ U`. -/
def cosetProjection (hU : U' ≤ U) :
    IntertwiningMap (ofMulAction A G (G ⧸ U')) (ofMulAction A G (G ⧸ U)) :=
  (ofMulAction A G (G ⧸ U)).cosetLift U' _ (hU.trans (le_stabilizer_single_one U))

@[simp]
theorem cosetProjection_single (hU : U' ≤ U) (g : G) (c : A) :
    cosetProjection A hU (MonoidAlgebra.single (g : G ⧸ U') c) =
      MonoidAlgebra.single (g : G ⧸ U) c := by
  simp [cosetProjection, ofMulAction_single]

/-- **The projection induces the inclusion** `V^U ⊆ V^{U'}`: the `U'`-invariant vector attached to
the intertwining map `A[G ⧸ U'] → A[G ⧸ U] → V` of `v ∈ V^U` is `v` itself. -/
theorem coe_ofMulActionQuotientMapEquiv_comp_cosetProjection (hU : U' ≤ U)
    (v : invariants (ρ.comp U.subtype)) :
    (ρ.ofMulActionQuotientMapEquiv U'
        (((ρ.ofMulActionQuotientMapEquiv U).symm v).comp (cosetProjection A hU)) : V) = v := by
  simp [IntertwiningMap.comp_apply]

variable [Fintype (U ⧸ U'.subgroupOf U)]

variable (A U' U) in
/-- The sum `∑_{u ∈ U ⧸ U'} u U'` of the cosets of `U'` contained in `U`, a `U`-invariant vector
of `A[G ⧸ U']`. -/
private def cosetSum : MonoidAlgebra A (G ⧸ U') :=
  relNorm ((ofMulAction A G (G ⧸ U')).comp U.subtype) (U'.subgroupOf U)
    (MonoidAlgebra.single ((1 : G) : G ⧸ U') 1)

private theorem le_stabilizer_cosetSum :
    U ≤ (ofMulAction A G (G ⧸ U')).stabilizer (cosetSum A U' U) := fun u hu ↦ by
  rw [mem_stabilizer]
  refine relNorm_apply_eq_self ((ofMulAction A G (G ⧸ U')).comp U.subtype) (H := U'.subgroupOf U)
    (fun h ↦ ?_) (⟨u, hu⟩ : U)
  have := le_stabilizer_single_one (A := A) U' (Subgroup.mem_subgroupOf.1 h.property)
  rwa [mem_stabilizer] at this

variable (A U') in
/-- The **transfer** `A[G ⧸ U] → A[G ⧸ U']`, `g U ↦ ∑_{u ∈ U ⧸ U'} g u U'`, for `U'` of finite
index in `U`. -/
def cosetTransfer : IntertwiningMap (ofMulAction A G (G ⧸ U)) (ofMulAction A G (G ⧸ U')) :=
  (ofMulAction A G (G ⧸ U')).cosetLift U _ le_stabilizer_cosetSum

private theorem cosetTransfer_single_one_eq_cosetSum :
    cosetTransfer A U' (U := U) (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) = cosetSum A U' U := by
  simp [cosetTransfer]

/-- The transfer sends the coset `U` to the sum of the cosets `u U'`, `u ∈ U ⧸ U'`. -/
theorem cosetTransfer_single_one :
    cosetTransfer A U' (U := U) (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) =
      ∑ q : U ⧸ U'.subgroupOf U, MonoidAlgebra.single (((q.out : U) : G) : G ⧸ U') 1 := by
  simp [cosetTransfer_single_one_eq_cosetSum, cosetSum, relNorm_apply, ofMulAction_single]

/-- **The transfer induces the trace**: the `U`-invariant vector attached to the intertwining map
`A[G ⧸ U] → A[G ⧸ U'] → V` of `v ∈ V^{U'}` is `tr_{U/U'}(v) = ∑_{u ∈ U ⧸ U'} ρ(u) v`. -/
theorem coe_ofMulActionQuotientMapEquiv_comp_cosetTransfer (v : invariants (ρ.comp U'.subtype)) :
    (ρ.ofMulActionQuotientMapEquiv U
        (((ρ.ofMulActionQuotientMapEquiv U').symm v).comp (cosetTransfer A U')) : V) =
      relNorm (ρ.comp U.subtype) (U'.subgroupOf U) v := by
  rw [coe_ofMulActionQuotientMapEquiv_apply, IntertwiningMap.comp_apply,
    cosetTransfer_single_one_eq_cosetSum, cosetSum, map_relNorm_comp,
    ofMulActionQuotientMapEquiv_symm_apply_single, one_smul, map_one, one_apply_eq_self]

/-- **Projection after transfer is the index**: `A[G ⧸ U] → A[G ⧸ U'] → A[G ⧸ U]` is
multiplication by `[U : U']`. -/
theorem cosetProjection_comp_cosetTransfer (hU : U' ≤ U) :
    (cosetProjection A hU).comp (cosetTransfer A U') =
      U'.relIndex U • IntertwiningMap.id (ofMulAction A G (G ⧸ U)) := by
  ext1
  rw [IntertwiningMap.comp_apply, cosetTransfer_single_one_eq_cosetSum, cosetSum, map_relNorm_comp,
    cosetProjection_single,
    relNorm_apply_of_forall_apply_eq _ fun u ↦ by
      have := le_stabilizer_single_one (A := A) U u.property
      rwa [mem_stabilizer] at this]
  rfl

end Representation
