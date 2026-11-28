/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.LinearAlgebra.End.Restrict
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.OfMulAction.Coset.Lift

/-!
# Group-algebra operators away from the level

For subgroups `K` (the level) and `D` (the allowed supports) of a group `G`, the spherical
subalgebra of `R[D]` consists of the elements that preserve `K`-fixed vectors in every
representation of `G`. One can test membership on just the vector of the identity coset in
`R[G ⧸ K]`: every fixed vector is the image of that vector under an intertwining map.

The image on a family of level spaces is a Hecke algebra of simultaneous operators. Taking
one image into the product, rather than a product of separate images, ensures that an operator
on every member of the family is realized by the *same* element supported in `D`.

The spherical subalgebra and its joint image are the constructions `New.Data.sphericalAlgebra`
and `New.Data.heckeAlgebra` in `grh/src/New/Spanning/Multiplicities/HeckeEigensystems.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

namespace Subgroup

open Representation

universe u v

variable {R : Type u} {G : Type v} [CommRing R] [Group G] {K D : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module R V]

private theorem mapsTo_invariants_of_cosetVector (ρ : Representation R G V)
    {a : MonoidAlgebra R G}
    (ha : (ofMulAction R G (G ⧸ K)).asAlgebraHom a
      (MonoidAlgebra.single ((1 : G) : G ⧸ K) 1) ∈
        invariants ((ofMulAction R G (G ⧸ K)).comp K.subtype)) :
    Set.MapsTo (ρ.asAlgebraHom a) (invariants (ρ.comp K.subtype))
      (invariants (ρ.comp K.subtype)) := by
  intro v hv
  let f := (ρ.ofMulActionQuotientMapEquiv K).symm ⟨v, hv⟩
  have hf : f (MonoidAlgebra.single ((1 : G) : G ⧸ K) 1) = v := by
    simp [f]
  rw [← hf, ← f.apply_asAlgebraHom]
  refine (mem_invariants _ _).2 fun k ↦ ?_
  rw [MonoidHom.comp_apply, ← f.isIntertwining]
  exact congrArg f ((mem_invariants _ _).1 ha k)

/-- The subalgebra of `R[D]` whose elements preserve `K`-fixed vectors in every representation
of `G`. Neither subgroup need be normal, and no finiteness of either subgroup is required. -/
noncomputable def sphericalSubalgebra (K : Subgroup G) (R : Type*) [CommRing R]
    (D : Subgroup G) : Subalgebra R (MonoidAlgebra R D) := by
  let ρ := ofMulAction R G (G ⧸ K)
  let A := ρ.asAlgebraHom.comp (MonoidAlgebra.mapDomainAlgHom R R D.subtype)
  let P := invariants (ρ.comp K.subtype)
  exact {
    carrier := {a | ∀ x ∈ P, A a x ∈ P}
    mul_mem' := fun ha hb x hx ↦ by simpa only [map_mul, mul_apply_eq_comp] using ha _ (hb x hx)
    add_mem' := fun ha hb x hx ↦ by
      simpa only [map_add, LinearMap.add_apply] using P.add_mem (ha x hx) (hb x hx)
    algebraMap_mem' := fun r x hx ↦ by
      simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using P.smul_mem r hx
    zero_mem' := fun x _ ↦ by simpa only [map_zero, LinearMap.zero_apply] using P.zero_mem
    one_mem' := fun x hx ↦ by simpa only [map_one, one_apply_eq_self] using hx }

/-- Test sphericality by the image of the single basis vector of the identity coset. -/
theorem mem_sphericalSubalgebra_iff {a : MonoidAlgebra R D} :
    a ∈ K.sphericalSubalgebra R D ↔
      (ofMulAction R G (G ⧸ K)).asAlgebraHom (MonoidAlgebra.mapDomainAlgHom R R D.subtype a)
        (MonoidAlgebra.single ((1 : G) : G ⧸ K) 1) ∈
          invariants ((ofMulAction R G (G ⧸ K)).comp K.subtype) := by
  let ρ := ofMulAction R G (G ⧸ K)
  refine ⟨fun h ↦ h _ ?_, fun h x hx ↦ mapsTo_invariants_of_cosetVector ρ h hx⟩
  simpa only [coe_ofMulActionQuotientMapEquiv_apply, IntertwiningMap.id_apply] using
    ((ρ.ofMulActionQuotientMapEquiv K) (IntertwiningMap.id ρ)).property

/-- A single group element with nonzero coefficient is spherical exactly when its inverse
conjugates the level into itself. This needs an inclusion, not equality of the subgroups. -/
theorem single_mem_sphericalSubalgebra_iff (d : D) (r : R) (hr : r ≠ 0) :
    MonoidAlgebra.single d r ∈ K.sphericalSubalgebra R D ↔
      ∀ k ∈ K, (d : G)⁻¹ * k * d ∈ K := by
  suffices (∀ k ∈ K, (d : G)⁻¹ * k⁻¹ * d ∈ K) ↔ ∀ k ∈ K, (d : G)⁻¹ * k * d ∈ K by
    simpa [mem_sphericalSubalgebra_iff, MulAction.Quotient.smul_mk,
      MonoidAlgebra.single_left_inj hr, QuotientGroup.eq] using this
  exact ⟨fun h k hk ↦ by simpa using h k⁻¹ (K.inv_mem hk),
    fun h k hk ↦ h k⁻¹ (K.inv_mem hk)⟩

/-- A spherical element preserves level invariants in any representation, even if their
ambient module is in a different universe from the coset representation. -/
theorem mapsTo_invariants_of_mem_sphericalSubalgebra {a : MonoidAlgebra R D}
    (ha : a ∈ K.sphericalSubalgebra R D) (ρ : Representation R G V) :
    Set.MapsTo (ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom R R D.subtype a))
      (invariants (ρ.comp K.subtype)) (invariants (ρ.comp K.subtype)) :=
  mapsTo_invariants_of_cosetVector ρ (mem_sphericalSubalgebra_iff.mp ha)

/-- An element is spherical exactly when it preserves the level invariants of every
representation in the universe containing the coset representation. -/
theorem mem_sphericalSubalgebra_iff_forall {a : MonoidAlgebra R D} :
    a ∈ K.sphericalSubalgebra R D ↔
      ∀ (W : Type (max u v)) [AddCommGroup W] [Module R W] (ρ : Representation R G W),
        Set.MapsTo (ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom R R D.subtype a))
          (invariants (ρ.comp K.subtype)) (invariants (ρ.comp K.subtype)) := by
  refine ⟨fun h _ _ _ ρ ↦ mapsTo_invariants_of_mem_sphericalSubalgebra h ρ, fun h x hx ↦ ?_⟩
  exact h _ (ofMulAction R G (G ⧸ K)) hx

/-- The action of spherical elements on one level space. -/
noncomputable def sphericalAction (K D : Subgroup G) (ρ : Representation R G V) :
    K.sphericalSubalgebra R D →ₐ[R] Module.End R (invariants (ρ.comp K.subtype)) :=
  (ρ.asAlgebraHom.comp ((MonoidAlgebra.mapDomainAlgHom R R D.subtype).comp
    (K.sphericalSubalgebra R D).val)).restrictEnd (invariants (ρ.comp K.subtype))
      fun a _ hv ↦ mapsTo_invariants_of_mem_sphericalSubalgebra a.property ρ hv

/-- Evaluate the spherical action by the ambient group-algebra action. -/
@[simp] theorem coe_sphericalAction_apply (K : Subgroup G) (ρ : Representation R G V)
    (a : K.sphericalSubalgebra R D) (v : invariants (ρ.comp K.subtype)) :
    (K.sphericalAction D ρ a v : V) =
      ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom R R D.subtype a.val) v := by
  unfold sphericalAction
  exact AlgHom.coe_restrictEnd_apply _ _ _ a v

/-- A level-preserving operator that commutes with the action of `D` also commutes on the
level space with each spherical operator supported in `D`. -/
theorem _root_.Representation.commute_restrict_sphericalAction (ρ : Representation R G V)
    {T : Module.End R V}
    (hT : ∀ x ∈ invariants (ρ.comp K.subtype), T x ∈ invariants (ρ.comp K.subtype))
    (hD : ∀ d : D, Commute T (ρ (d : G))) (a : K.sphericalSubalgebra R D) :
    Commute (T.restrict hT) (K.sphericalAction D ρ a) := by
  have h := commute_asAlgebraHom_of_forall_commute (ρ.comp D.subtype : Representation R D V) hD
    a.val
  rw [asAlgebraHom_def, ← MonoidAlgebra.lift_mapDomain] at h
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  -- Expose composition on the subtype before rewriting its coercions to the ambient space.
  change T (K.sphericalAction D ρ a x : V) = (K.sphericalAction D ρ a (T.restrict hT x) : V)
  rw [coe_sphericalAction_apply, coe_sphericalAction_apply, LinearMap.coe_restrict_apply]
  exact LinearMap.congr_fun h.eq (x : V)

/-- The simultaneous Hecke algebra on a family of level spaces. -/
noncomputable def heckeAlgebraAwayFromLevel (K D : Subgroup G) {ι : Type*}
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (ρ : ∀ i, Representation R G (W i)) :
    Subalgebra R (∀ i, Module.End R (invariants ((ρ i).comp K.subtype))) :=
  (AlgHom.pi fun i ↦ K.sphericalAction D (ρ i)).range

/-- A family belongs to the simultaneous algebra precisely when a single spherical element
realizes all its components. -/
theorem mem_heckeAlgebraAwayFromLevel_iff {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {ρ : ∀ i, Representation R G (W i)}
    {T : ∀ i, Module.End R (invariants ((ρ i).comp K.subtype))} :
    T ∈ K.heckeAlgebraAwayFromLevel D ρ ↔
      ∃ a : K.sphericalSubalgebra R D, ∀ i, K.sphericalAction D (ρ i) a = T i := by
  simp only [heckeAlgebraAwayFromLevel, AlgHom.mem_range, funext_iff, AlgHom.pi_apply]

end Subgroup
