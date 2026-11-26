/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# The identity of the projective line as a prestable map

Over a commutative ring `k`, the projective line `ℙ¹_k` with no markings is a pointed
prestable family: it is smooth of relative dimension one and proper, and geometrically connected
since it is geometrically integral. The identity `ℙ¹_k → ℙ¹_k` is a prestable map to `ℙ¹_k` over
`Spec k`, and it has trivial automorphism group: an automorphism `σ` of the source with
`id ∘ σ = id` is the identity. The same source with a constant map has automorphism group that of
the source curve (`TauCeti.AlgebraicGeometry.PrestableMap.autConstMulEquiv`).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

/-- The projective line over a commutative ring with no markings, as a pointed prestable family. -/
def projectiveLinePointedPrestableFamily : PointedPrestableFamily (Spec (.of k)) 0 :=
  PointedPrestableFamily.ofSmooth (projectiveLine k ↘ Spec (.of k)) Fin.elim0
    (fun i ↦ i.elim0) fun i ↦ i.elim0

/-- The identity of the projective line over a commutative ring, as a prestable map to `ℙ¹_k` over
`Spec k` with no markings. -/
def projectiveLineIdPrestableMap : PrestableMap (projectiveLine k ↘ Spec (.of k)) 0 where
  curve := projectiveLinePointedPrestableFamily k
  map := 𝟙 (projectiveLine k)
  w := Category.id_comp _

/-- The map of `projectiveLineIdPrestableMap` is the identity, hence a monomorphism. -/
instance : Mono (projectiveLineIdPrestableMap k).map :=
  inferInstanceAs (Mono (𝟙 (projectiveLine k)))

/-- **The identity `ℙ¹_k → ℙ¹_k` with no markings has trivial automorphism group.** -/
example : Subsingleton (Aut (projectiveLineIdPrestableMap k)) :=
  PrestableMap.subsingleton_aut_of_mono _

end TauCeti.AlgebraicGeometry
