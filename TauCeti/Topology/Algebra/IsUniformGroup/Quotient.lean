/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import TauCeti.Topology.Algebra.IsUniformGroup.Defs
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# Completeness of open quotients of right-uniform groups

Mathlib's `QuotientGroup.completeSpace_right` makes the quotient `G ⧸ N` of a complete first
countable right-uniform group complete for its right uniformity. A group `H` receiving an open
quotient map `f : G → H` is that quotient in disguise: the induced isomorphism
`G ⧸ ker f ≃* H` is a homeomorphism, hence a uniform embedding for the right uniformities.
Consequently `H` is complete. No commutativity is needed.

This is the form in which completeness is needed for a ring presented as an open quotient of a
complete ring, such as an algebra topologically of finite type over a Tate ring.

## Main results

* `IsOpenQuotientMap.completeSpace_mul`: a right-uniform group admitting an open quotient map
  from a complete first countable right-uniform group is complete.
* `IsOpenQuotientMap.completeSpace`: the additive counterpart.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966b], IX.3.1 Proposition 4.
-/

public section

open Topology

variable {G H : Type*} [Group G] [UniformSpace G] [IsRightUniformGroup G] [CompleteSpace G]
  [FirstCountableTopology G] [Group H] [UniformSpace H] [IsRightUniformGroup H]
  {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F}

/-- **An open quotient of a complete first countable right-uniform group is complete.**
If `f : G → H` is a continuous open surjective homomorphism, `G` is complete and first countable,
and `H` is a right-uniform group, then `H` is complete. -/
@[to_additive IsOpenQuotientMap.completeSpace /-- **An open quotient of a complete first countable
right-uniform additive group is complete.** If `f : G → H` is a continuous open surjective additive
homomorphism, `G` is complete and first countable, and `H` is a right-uniform additive group,
then `H` is complete. -/]
theorem IsOpenQuotientMap.completeSpace_mul (hf : IsOpenQuotientMap f) : CompleteSpace H := by
  let N := MonoidHom.ker (f : G →* H)
  let _ : UniformSpace (G ⧸ N) := IsTopologicalGroup.rightUniformSpace (G ⧸ N)
  have _ : CompleteSpace (G ⧸ N) := QuotientGroup.completeSpace_right G N
  have _ : IsRightUniformGroup (G ⧸ N) :=
    IsTopologicalGroup.isRightUniformGroup (G ⧸ N)
  let e := ContinuousMulEquiv.quotientKerEquivOfSurjective (f : G →* H)
    hf.isQuotientMap.isStrictMap hf.surjective
  have he : IsUniformEmbedding e :=
    MonoidHom.isUniformEmbedding_of_isEmbedding_right e.toHomeomorph.isEmbedding
  exact (completeSpace_congr (e := e.toEquiv) he).mp inferInstance
