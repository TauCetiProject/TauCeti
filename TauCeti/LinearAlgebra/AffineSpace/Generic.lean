/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import TauCeti.LinearAlgebra.AffineSpace.Transverse

/-!
# Generic loci and finite affine arrangements

The generic locus of an affine family consists of the points avoiding every member.
Finite exceptional arrangements support union and transport by affine equivalences,
over an arbitrary ring, with points in an affine space whose direction module is
implicit. No topology or chosen origin is required. The arrangement `point p` has a single
point as its only exception, and a line starting at a generic point meets an arrangement at only
finitely many parameters. Transverse germs avoid affine subspaces and finite arrangements
on the cofinite filter over a division ring, without any scalar topology. For a finite
family of affine maps and directions, each parameter-augmented map being surjective
gives one source arrangement making all germs simultaneously generic cofinitely.

Adapted from `Mei/Geometry/Affine/Generic.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`:
https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Geometry/Affine/Generic.lean

The point arrangement and the finiteness of exceptional parameters along a line are adapted from
`Mei/Geometry/Affine/Generic/Examples.lean` and `Mei/Geometry/Affine/Generic/Line.lean` in Mei at
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`. Original copyright and author credit are
retained.

The cofinite affine-germ results are adapted from
`Mei/Geometry/Affine/IncomingGerm.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`, retaining the original copyright and author.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Affine/Generic/Examples.lean
-/

public section

open Set Filter
open scoped Affine

namespace AffineSubspace

variable {k : Type*} [Ring k] {V P : Type*}
  [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The points avoiding every member of an affine family. -/
def genericLocus {ι : Sort*} (A : ι → AffineSubspace k P) : Set P :=
  {x | ∀ i, x ∉ A i}

/-- Membership in the generic locus means avoiding each exception. -/
@[simp]
theorem mem_genericLocus {ι : Sort*} {A : ι → AffineSubspace k P} {x : P} :
    x ∈ genericLocus A ↔ ∀ i, x ∉ A i := Iff.rfl

/-- The generic locus is the intersection of the complements. -/
theorem genericLocus_eq_iInter {ι : Sort*} (A : ι → AffineSubspace k P) :
    genericLocus A = ⋂ i, (A i : Set P)ᶜ := by
  ext x
  simp

end AffineSubspace

namespace TauCeti

/-- A finite collection of proper affine subspaces to be avoided. Repeated
exceptions are identified. Empty affine subspaces are permitted. -/
structure ExceptionalArrangement (k : Type*) [Ring k] {V : Type*}
    [AddCommGroup V] [Module k V] (P : Type*) [AffineSpace V P] where
  /-- The finite set of affine subspaces to avoid. -/
  exceptions : Finset (AffineSubspace k P)
  /-- No exception contains the whole ambient space. -/
  proper : ∀ S ∈ exceptions, S ≠ ⊤

namespace ExceptionalArrangement

variable {k : Type*} [Ring k] {V W P Q : Type*}
  [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup W] [Module k W] [AffineSpace W Q]

/-- A point is generic if it avoids every affine exception. -/
def IsGeneric (E : ExceptionalArrangement k P) (x : P) : Prop :=
  ∀ S ∈ E.exceptions, x ∉ S

/-- A point is generic exactly when it avoids every exception. -/
theorem isGeneric_iff {E : ExceptionalArrangement k P} {x : P} :
    E.IsGeneric x ↔ ∀ S ∈ E.exceptions, x ∉ S := (Iff.rfl)

/-- Union of the exceptions in two arrangements. -/
noncomputable def union (E F : ExceptionalArrangement k P) : ExceptionalArrangement k P := by
  classical
  exact ⟨E.exceptions ∪ F.exceptions, fun S h =>
    (Finset.mem_union.mp h).elim (E.proper S) (F.proper S)⟩

open Classical in
/-- The exceptions of a union are the union of the exceptions. -/
@[simp]
theorem exceptions_union (E F : ExceptionalArrangement k P) :
    (E.union F).exceptions = E.exceptions ∪ F.exceptions := (rfl)

/-- Genericity for a union is genericity for each arrangement. -/
@[simp]
theorem isGeneric_union {E F : ExceptionalArrangement k P} {x : P} :
    (E.union F).IsGeneric x ↔ E.IsGeneric x ∧ F.IsGeneric x := by
  classical
  simp [IsGeneric, union, or_imp, forall_and]

/-- Transport an arrangement by an affine equivalence. -/
noncomputable def map (E : ExceptionalArrangement k P) (e : P ≃ᵃ[k] Q) :
    ExceptionalArrangement k Q := by
  classical
  refine ⟨E.exceptions.image (AffineSubspace.map e.toAffineMap), ?_⟩
  intro T hT htop
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  apply E.proper S hS
  apply top_unique
  intro x _
  apply (AffineSubspace.mem_map_iff_mem_of_injective (f := e.toAffineMap) e.injective).mp
  rw [htop]
  trivial

open Classical in
/-- Transport maps the finite set of exceptions by the affine equivalence. -/
@[simp]
theorem exceptions_map (E : ExceptionalArrangement k P) (e : P ≃ᵃ[k] Q) :
    (E.map e).exceptions = E.exceptions.image (AffineSubspace.map e.toAffineMap) := (rfl)

/-- Transport preserves genericity of the corresponding points. -/
@[simp]
theorem isGeneric_map_iff {E : ExceptionalArrangement k P} (e : P ≃ᵃ[k] Q) {x : P} :
    (E.map e).IsGeneric (e x) ↔ E.IsGeneric x := by
  classical
  simp [IsGeneric, map]

/-- Pullback under an affine equivalence, expressed by transport under its inverse. -/
noncomputable def comap (E : ExceptionalArrangement k Q) (e : P ≃ᵃ[k] Q) :
    ExceptionalArrangement k P :=
  E.map e.symm

open Classical in
/-- Pullback maps the exceptions by the inverse affine equivalence. -/
@[simp]
theorem exceptions_comap (E : ExceptionalArrangement k Q) (e : P ≃ᵃ[k] Q) :
    (E.comap e).exceptions = E.exceptions.image (AffineSubspace.map e.symm.toAffineMap) :=
  (rfl)

/-- A point is generic in a pullback exactly when its image is generic. -/
@[simp]
theorem isGeneric_comap_iff {E : ExceptionalArrangement k Q} {e : P ≃ᵃ[k] Q} {x : P} :
    (E.comap e).IsGeneric x ↔ E.IsGeneric (e x) := by
  simpa [comap] using (isGeneric_map_iff (E := E) e.symm (x := e x))

section Point

variable [Nontrivial V]

/-- The arrangement whose only exception is a point, in a nontrivial space. -/
noncomputable def point (p : P) : ExceptionalArrangement k P :=
  ⟨{({p} : AffineSubspace k P)}, fun S hS htop => by
    obtain rfl := Finset.mem_singleton.mp hS
    have : Nontrivial P := (vadd_right_injective p).nontrivial
    exact AffineSubspace.singleton_ne_top k V p htop⟩

/-- The only exception of `point p` is the subspace `{p}`. -/
@[simp]
theorem exceptions_point (p : P) :
    (point p : ExceptionalArrangement k P).exceptions = {({p} : AffineSubspace k P)} := (rfl)

/-- A point is generic for `point p` exactly when it differs from `p`. -/
@[simp]
theorem isGeneric_point_iff {p x : P} :
    (point p : ExceptionalArrangement k P).IsGeneric x ↔ x ≠ p := by
  simp [isGeneric_iff]

end Point

section Line

variable {k : Type*} [DivisionRing k] {V P : Type*} [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- A line starting at a generic point meets an arrangement at finitely many parameter values.
No transversality or distinctness assumption on its second endpoint is required. -/
theorem finite_setOf_not_isGeneric_lineMap (E : ExceptionalArrangement k P)
    {x : P} (hx : E.IsGeneric x) (y : P) :
    {t : k | ¬ E.IsGeneric (AffineMap.lineMap x y t)}.Finite := by
  have hS (S : AffineSubspace k P) (hS : S ∈ E.exceptions) :
      {t : k | AffineMap.lineMap x y t ∈ S}.Subsingleton :=
    S.subsingleton_preimage_of_notMem (AffineMap.lineMap x y)
      (t₀ := 0) (by simpa only [AffineMap.lineMap_apply_zero] using isGeneric_iff.mp hx S hS)
  have he : {t : k | ¬ E.IsGeneric (AffineMap.lineMap x y t)} =
      ⋃ S ∈ E.exceptions, {t : k | AffineMap.lineMap x y t ∈ S} := by
    ext t
    simp only [Set.mem_ofPred_eq, isGeneric_iff, not_forall, not_not, Set.mem_iUnion,
      exists_prop]
  rw [he]
  exact E.exceptions.finite_toSet.biUnion fun S hmem => (hS S hmem).finite

end Line

end ExceptionalArrangement

end TauCeti

namespace AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A transverse affine germ avoids a subspace at all but finitely many scalar
parameters, even from an exceptional base point. No scalar topology is required. -/
theorem eventually_smul_vadd_notMem_cofinite (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in cofinite, t • v +ᵥ x ∉ S := by
  have h := S.subsingleton_preimage_lineMap (x := x) (y := v +ᵥ x)
    (by simpa using hv)
  simpa only [Set.mem_preimage, AffineMap.lineMap_vadd_apply, AffineSubspace.mem_coe] using
    h.finite.eventually_cofinite_notMem

end AffineSubspace

namespace TauCeti.ExceptionalArrangement

section FixedDirection

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A direction transverse to every nonempty exception gives a generic affine germ
at all but finitely many parameters from every base point, without scalar topology. -/
theorem eventually_isGeneric_smul_vadd_cofinite (E : ExceptionalArrangement k P)
    {v : V} (hv : ∀ S ∈ E.exceptions, (S : Set P).Nonempty → v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in cofinite, E.IsGeneric (t • v +ᵥ x) := by
  simp_rw [isGeneric_iff]
  apply E.exceptions.eventually_all.mpr
  intro S hS
  by_cases hne : (S : Set P).Nonempty
  · exact S.eventually_smul_vadd_notMem_cofinite (hv S hS hne) x
  · exact Eventually.of_forall fun t ht => hne ⟨_, ht⟩

end FixedDirection

section AffineFamilies

variable {k U V P Q ι : Type*} [DivisionRing k]
  [AddCommGroup U] [Module k U] [AddTorsor U P]
  [AddCommGroup V] [Module k V] [AddTorsor V Q] [Finite ι]

/-- If each map `(x, t) ↦ t • v j +ᵥ g j x` of a finite affine family is surjective,
one source arrangement `F` makes all germs from every `F`-generic point simultaneously
generic at all but finitely many parameters. No scalar topology is required. -/
theorem exists_forall_eventually_isGeneric_smul_vadd_cofinite
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x →
      ∀ᶠ t : k in cofinite, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  classical
  let := Fintype.ofFinite ι
  let F : ExceptionalArrangement k P :=
    ⟨((Finset.univ.product E.exceptions).image
      (fun z : ι × AffineSubspace k Q => z.2.comap (g z.1))).erase ⊤,
      fun _ h => (Finset.mem_erase.mp h).1⟩
  refine ⟨F, fun x hx => eventually_all.mpr fun j => ?_⟩
  simp_rw [isGeneric_iff]
  apply E.exceptions.eventually_all.mpr
  intro S hS
  by_cases hv : v j ∈ S.direction
  · have hproper : S.comap (g j) ≠ ⊤ := by
      intro htop
      apply E.proper S hS
      apply top_unique
      intro y _
      obtain ⟨⟨z, t⟩, rfl⟩ := hg j y
      apply S.vadd_mem_of_mem_direction (S.direction.smul_mem t hv)
      exact AffineSubspace.mem_comap.mp (htop ▸ AffineSubspace.mem_top k U z)
    have hbase : g j x ∉ S := by
      intro hmem
      apply (isGeneric_iff.mp hx) (S.comap (g j))
      · exact Finset.mem_erase.mpr ⟨hproper, Finset.mem_image.mpr
          ⟨(j, S), Finset.mem_product.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩⟩
      · exact AffineSubspace.mem_comap.mpr hmem
    exact Eventually.of_forall fun t ht => hbase
      ((S.vadd_mem_iff_mem_of_mem_direction (S.direction.smul_mem t hv)).mp ht)
  · exact S.eventually_smul_vadd_notMem_cofinite hv (g j x)


end AffineFamilies

end TauCeti.ExceptionalArrangement
