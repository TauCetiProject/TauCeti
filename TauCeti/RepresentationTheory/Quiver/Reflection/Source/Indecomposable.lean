/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.FullyFaithful

/-!
# Reflecting an indecomposable representation at a source

The Bernstein--Gelfand--Ponomarev reflection at a source `i` replaces the vertex space `Mᵢ` by the
cokernel of the map `TauCeti.outgoingMap` collecting the arrows out of `i`. It acts on dimension
vectors by the simple reflection `sᵢ`, and preserves indecomposability, whenever that map is
injective (`TauCeti.dimVector_sourceReflectRep`, `TauCeti.indecomposable_sourceReflectRep`). This
file discharges that hypothesis: the map out of a source is injective for every indecomposable
representation except the vertex simple `Sᵢ`, which is the representation the reflection
annihilates.

This is the mirror of the sink-side argument in
`TauCeti.RepresentationTheory.Quiver.Reflection.Indecomposable`, and it reuses that file's
construction rather than repeating it. A linear endomorphism `π` of `Mᵢ` extends by the identity
at the other vertices to an endomorphism `TauCeti.vertexEnd` of `M` as soon as the paths through
`i` do not see it; at a source, no path arrives at `i` from elsewhere, so only the condition on
the paths leaving `i` has content, and it follows from the condition on the arrows leaving `i`
because such a path begins with one. An indecomposable representation admits no idempotent
endomorphism but `0` and the identity, so an idempotent `π` of this kind is `0` or the identity
(`TauCeti.sourceIdempotent_eq_id_or_eq_zero_of_indecomposable`). Applied to the projection onto a
complement of the kernel of the outgoing map, this says the kernel vanishes unless `M` vanishes
away from `i`, in which case `M` is `Sᵢ`.

## Main results

* `TauCeti.sourceIdempotent_eq_id_or_eq_zero_of_indecomposable`: an idempotent of `Mᵢ` that every
  arrow out of a source `i` of an indecomposable `M` does not see is the identity, or is zero and
  `M` vanishes away from `i`.
* `TauCeti.outgoingMap_injective_or_forall_subsingleton`: hence the map collecting the arrows out
  of a source is injective, unless the representation is concentrated there.
* `TauCeti.outgoingMap_injective_of_indecomposable`: **the map collecting the arrows out of a
  source is injective for every indecomposable representation not isomorphic to the vertex simple
  there.**
* `TauCeti.not_nonempty_iso_simpleRep_of_vertexPreReflection_nonneg`: the exceptional case is
  detected numerically, by the simple reflection driving the dimension vector negative.
* `TauCeti.dimVector_sourceReflectRep_of_indecomposable` and
  `TauCeti.indecomposable_sourceReflectRep_of_not_nonempty_iso_simpleRep`: consequently reflection
  at a source carries such a representation to an indecomposable one, whose dimension vector is
  the simple reflection of the old one.

## Implementation notes

As in the sink-side file, the results comparing `M` with `TauCeti.simpleRep k Q i` are stated in
the last section, where the quiver, its arrows and the field all live in one universe: the vertex
spaces of a reflected representation are cut out of a product indexed by the arrows, while `Sᵢ`
puts the field itself at `i`.

## References

See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

section General

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}
variable {π : M.obj i →ₗ[k] M.obj i}

/-! ### Idempotents at a source of an indecomposable representation -/

/-- A vector that every arrow out of `i` identifies with its image under `π` is identified with it
by every path out of `i` that ends elsewhere: such a path begins with an arrow out of `i`. -/
private theorem map_path_out_fixed (hi : IsSource i)
    (hπ : ∀ (b : Q) (e : i ⟶ b) (y : M.obj i), (M.map e.toPath).hom (π y) =
      (M.map e.toPath).hom y) :
    ∀ {b : Q} (p : Quiver.Path i b), b ≠ i → ∀ y : M.obj i,
      (M.map p).hom (π y) = (M.map p).hom y := by
  intro b p
  induction p with
  | nil => exact fun hb ↦ absurd rfl hb
  | @cons c d q e ih =>
    intro _ y
    have hcomp : M.map (q.cons e) = M.map q ≫ M.map e.toPath := M.map_comp q e.toPath
    rw [hcomp]
    rcases eq_or_ne c i with rfl | hc
    · rw [hi.path_self_eq_nil q, QuiverRep.map_nil, Category.id_comp]
      exact hπ d e y
    · exact congrArg (M.map e.toPath).hom (ih hc y)

/-- **An idempotent at a source of an indecomposable representation is trivial.** Let `i` be a
source of `Q` and `M` an indecomposable representation. An idempotent endomorphism of `Mᵢ` that
every arrow out of `i` composes away is either the identity, or zero; in the second case `M`
vanishes away from `i`. -/
theorem sourceIdempotent_eq_id_or_eq_zero_of_indecomposable (hi : IsSource i)
    (hM : Indecomposable M) (π : M.obj i →ₗ[k] M.obj i)
    (hπ : ∀ (b : Q) (e : i ⟶ b) (y : M.obj i), (M.map e.toPath).hom (π y) =
      (M.map e.toPath).hom y)
    (hidem : IsIdempotentElem π) :
    π = LinearMap.id ∨ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) :=
  vertexIdempotent_eq_id_or_eq_zero_of_indecomposable hM π
    (fun _ p ha ↦ absurd (hi.eq_of_path p) ha)
    (fun _ p hb y ↦ map_path_out_fixed hi hπ p hb y)
    (fun p ↦ by rw [hi.path_self_eq_nil p, QuiverRep.map_nil, Category.id_comp, Category.comp_id])
    hidem

/-! ### The injectivity of the outgoing map -/

/-- **The map collecting the arrows out of a source of an indecomposable representation is
injective, unless the representation is concentrated at that source.** This is the injectivity
hypothesis of `TauCeti.dimVector_sourceReflectRep`, discharged: the kernel of the outgoing map is
a direct summand of `Mᵢ`, so a nonzero kernel would split `M`, and the only splitting an
indecomposable representation admits leaves nothing outside the source. -/
theorem outgoingMap_injective_or_forall_subsingleton (hi : IsSource i) (hM : Indecomposable M) :
    Function.Injective (outgoingMap M i) ∨ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  -- project onto a complement of the kernel of the outgoing map along that kernel
  obtain ⟨U, hU⟩ := (LinearMap.ker (outgoingMap M i)).exists_isCompl
  have hidem : IsIdempotentElem (U.projection (LinearMap.ker (outgoingMap M i)) hU.symm) :=
    Submodule.isIdempotentElem_projection hU.symm
  have hπ : ∀ (b : Q) (e : i ⟶ b) (y : M.obj i),
      (M.map e.toPath).hom (U.projection (LinearMap.ker (outgoingMap M i)) hU.symm y) =
        (M.map e.toPath).hom y := by
    intro b e y
    have hker := LinearMap.mem_ker.mp (Submodule.sub_projection_mem hU.symm y)
    have h0 := congrFun hker (⟨b, e⟩ : Σ b : Q, (i ⟶ b))
    rw [outgoingMap_apply, Pi.zero_apply, map_sub, sub_eq_zero] at h0
    exact h0.symm
  rcases sourceIdempotent_eq_id_or_eq_zero_of_indecomposable hi hM _ hπ hidem with hid | ⟨-, hsub⟩
  · -- the projection along the kernel is the identity, so the kernel vanishes
    refine Or.inl (LinearMap.ker_eq_bot.mp ?_)
    rw [← Submodule.ker_projection hU.symm, hid, LinearMap.ker_id]
  · exact Or.inr hsub

end General

/-! ### Injectivity from a nonnegative reflected dimension vector -/

section Nonnegative

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}
variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **A nonnegative reflected dimension vector forces the outgoing map to be injective.** For an
indecomposable representation `M` and a source `i`, if the dimension vector of `M` reflected at
`i` is nonnegative, then the outgoing map of `M` at `i` is injective. -/
theorem outgoingMap_injective_of_vertexPreReflection_nonneg [DecidableEq Q]
    (hi : IsSource i) (hM : Indecomposable M)
    (h : 0 ≤ vertexPreReflection Q i fun j ↦ (dimVector M j : ℤ)) :
    Function.Injective (outgoingMap M i) := by
  rcases outgoingMap_injective_or_forall_subsingleton hi hM with hinj | hsub
  · exact hinj
  · obtain ⟨y, hy, hspan⟩ :=
      exists_ne_zero_span_eq_top_of_forall_subsingleton hi.path_self_eq_nil hM hsub
    have hone : dimVector M i = 1 := by
      rw [dimVector_apply]
      exact (finrank_eq_one_iff_of_nonzero (K := k) y hy).mpr hspan
    have hzero : ∀ j : Q, j ≠ i → dimVector M j = 0 := by
      intro j hj
      let : Subsingleton (M.obj ((Paths.of Q).obj j)) := hsub j hj
      rw [dimVector_apply]
      exact Module.finrank_zero_of_subsingleton (R := k)
    have hdim : (fun j : Q ↦ (dimVector M j : ℤ)) = Pi.single i 1 := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.single_eq_same, hone, Nat.cast_one]
      · rw [Pi.single_eq_of_ne hj, hzero j hj, Nat.cast_zero]
    rw [hdim, vertexPreReflection_single_self Q hi.isEmpty_hom_self] at h
    have hfalse : ¬(0 : ℤ) ≤ -1 := by norm_num
    exact (hfalse (by simpa using Pi.le_def.mp h i)).elim

end Nonnegative

/-! ### The vertex simple as the exceptional case -/

section VertexSimple

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u} Q]
variable {M : QuiverRep.{u, u, u, u} k Q} {i : Q}

/-- **The map collecting the arrows out of a source is injective for every indecomposable
representation other than the vertex simple there.** The vertex simple `Sᵢ` is genuinely excluded,
by `TauCeti.outgoingMap_not_injective`. -/
theorem outgoingMap_injective_of_indecomposable (hi : IsSource i) (hM : Indecomposable M)
    (hne : ¬ Nonempty (M ≅ simpleRep k Q i)) : Function.Injective (outgoingMap M i) :=
  (outgoingMap_injective_or_forall_subsingleton hi hM).resolve_right fun h ↦
    hne (nonempty_iso_simpleRep_of_forall_subsingleton hi.path_self_eq_nil hM h)

/-- **Reflection at a source carries an indecomposable representation other than the vertex simple
there to an indecomposable representation of the reflected quiver.** Together with
`TauCeti.dimVector_sourceReflectRep_of_indecomposable`, which computes the dimension vector of the
result as `sᵢ · dim M` under the additional hypothesis that the vertex spaces at the targets of
the arrows out of `i` are finite-dimensional, this is the step that rebuilds an indecomposable
along a reflection sequence, dual to
`TauCeti.indecomposable_reflectRep_of_not_nonempty_iso_simpleRep`. -/
theorem indecomposable_sourceReflectRep_of_not_nonempty_iso_simpleRep
    [Finite (Σ b : Q, (i ⟶ b))] (hi : IsSource i) (hM : Indecomposable M)
    (hne : ¬ Nonempty (M ≅ simpleRep k Q i)) :
    Indecomposable (sourceReflectRep M hi) :=
  indecomposable_sourceReflectRep hi hM (outgoingMap_injective_of_indecomposable hi hM hne)

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **Reflection at a source acts on the dimension vector of an indecomposable representation by
the simple reflection there**, unless that representation is the vertex simple at the source. -/
theorem dimVector_sourceReflectRep_of_indecomposable [DecidableEq Q] (hi : IsSource i)
    (hM : Indecomposable M) (hne : ¬ Nonempty (M ≅ simpleRep k Q i))
    (hfin : ∀ e : Σ b : Q, (i ⟶ b), FiniteDimensional k (M.obj e.1)) :
    (fun j : Q ↦ (dimVector (sourceReflectRep M hi) j : ℤ))
      = vertexPreReflection Q i (fun j ↦ (dimVector M j : ℤ)) :=
  dimVector_sourceReflectRep M hi hfin (outgoingMap_injective_of_indecomposable hi hM hne)

/-- **A representation whose dimension vector the simple reflection keeps nonnegative is not the
vertex simple.** The dimension vector of `Sᵢ` is the simple dimension vector `αᵢ`, which the
reflection at a loopless vertex `i` negates. This is the form in which the reflection induction
rebuilding an indecomposable from a vertex simple checks the exceptional case above: what such an
induction carries along is the nonnegativity of the successive dimension vectors, not a
comparison with `Sᵢ`. -/
theorem not_nonempty_iso_simpleRep_of_vertexPreReflection_nonneg [DecidableEq Q]
    (hloop : IsEmpty (i ⟶ i)) (h : 0 ≤ vertexPreReflection Q i fun j ↦ (dimVector M j : ℤ)) :
    ¬ Nonempty (M ≅ simpleRep k Q i) := by
  rintro ⟨e⟩
  have hdim : (fun j : Q ↦ (dimVector M j : ℤ)) = Pi.single i 1 := by
    funext j
    rw [dimVector_eq_of_iso e, dimVector_simpleRep]
    simp [Pi.single_apply]
  rw [hdim, vertexPreReflection_single_self Q hloop] at h
  simpa using Pi.le_def.mp h i

end VertexSimple

end TauCeti
