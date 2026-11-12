/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Basic

/-!
# Transporting tilts along topological ring isomorphisms

A ring isomorphism between complete Hausdorff uniform Tate rings, continuous in both
directions, induces a ring isomorphism between their tilts. It applies the original map to
every coordinate and is again a homeomorphism. No perfectoid hypothesis is needed.

`RingEquiv.uniformTilt` packages the existing functorial map with the map induced by the
inverse. The coordinate formula, compatibility with inversion, identity and composition,
and the homeomorphism theorem allow a change of presentation of a tilt while retaining
its ring structure and topology. In particular, the zeroth-coordinate formula preserves
the sharp map; it does not assert that sharp itself is additive.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1(d).
* P. Scholze and J. Weinstein, *Berkeley Lectures on p-adic Geometry*, Theorem 6.2.7.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace RingEquiv

variable {p : ℕ} [Fact p.Prime]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))]
  {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))]

/-- A topological ring isomorphism induces an isomorphism of tilts by applying it to each
coordinate. Its inverse is induced by the inverse ring isomorphism. -/
noncomputable def uniformTilt (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    TauCeti.Perfectoid.uniformTilt p B ≃+* TauCeti.Perfectoid.uniformTilt p C :=
  RingEquiv.ofRingHom (uniformTilt.map e.toRingHom he) (uniformTilt.map e.symm.toRingHom he')
    (by ext x n; simp)
    (by ext x n; simp)

/-- The underlying homomorphism is the functorial map on tilts. -/
@[simp]
theorem toRingHom_uniformTilt (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    (e.uniformTilt (p := p) he he' :
      TauCeti.Perfectoid.uniformTilt p B →+* TauCeti.Perfectoid.uniformTilt p C) =
        uniformTilt.map e.toRingHom he := (rfl)

/-- The induced isomorphism applies the original isomorphism to every coordinate. -/
@[simp]
theorem coeff_uniformTilt (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm)
    (x : TauCeti.Perfectoid.uniformTilt p B) (n : ℕ) :
    uniformTilt.coeff p C n (e.uniformTilt he he' x) = e (uniformTilt.coeff p B n x) :=
  uniformTilt.coeff_map e.toRingHom he x n

/-- Tilting commutes with taking the inverse of an isomorphism. -/
@[simp]
theorem uniformTilt_symm (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    e.symm.uniformTilt (p := p) he' he = (e.uniformTilt he he').symm := (rfl)

/-- The inverse isomorphism applies the original inverse to every coordinate. -/
@[simp]
theorem coeff_uniformTilt_symm (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm)
    (x : TauCeti.Perfectoid.uniformTilt p C) (n : ℕ) :
    uniformTilt.coeff p B n ((e.uniformTilt he he').symm x) =
      e.symm (uniformTilt.coeff p C n x) := by
  rw [← uniformTilt_symm]
  exact coeff_uniformTilt e.symm he' he x n

/-- Tilting the identity isomorphism gives the identity isomorphism. -/
@[simp]
theorem uniformTilt_refl :
    (RingEquiv.refl B).uniformTilt (p := p) continuous_id continuous_id =
      RingEquiv.refl (TauCeti.Perfectoid.uniformTilt p B) := by
  ext x n
  simpa using coeff_uniformTilt (p := p) (RingEquiv.refl B) continuous_id continuous_id x n

/-- The induced isomorphism of tilts is continuous. -/
@[fun_prop, continuity]
theorem continuous_uniformTilt (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    Continuous (e.uniformTilt (p := p) he he') :=
  uniformTilt.continuous_map e.toRingHom he

/-- The induced ring isomorphism of tilts is a homeomorphism. -/
theorem isHomeomorph_uniformTilt (e : B ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) : IsHomeomorph (e.uniformTilt (p := p) he he') := by
  -- `ofRingHom` uses the tilted inverse as its inverse function.
  exact (Homeomorph.mk (e.uniformTilt he he').toEquiv
    (e.continuous_uniformTilt he he')
    (uniformTilt.continuous_map e.symm.toRingHom he')).isHomeomorph

variable {D : Type*} [CommRing D] [UniformSpace D] [IsUniformAddGroup D]
  [IsTopologicalRing D] [IsTateRing D] [CompleteSpace D] [T2Space D] [IsUniform D]
  [Fact (IsTopologicallyNilpotent (p : D))]

/-- Tilting preserves composition of topological ring isomorphisms. -/
@[simp]
theorem uniformTilt_trans (e : B ≃+* C) (he : Continuous e) (he' : Continuous e.symm)
    (f : C ≃+* D) (hf : Continuous f) (hf' : Continuous f.symm) :
    (e.trans f).uniformTilt (p := p) (hf.comp he) (he'.comp hf') =
      (e.uniformTilt he he').trans (f.uniformTilt hf hf') := by
  ext x n
  simp [coeff_uniformTilt (e.trans f) (hf.comp he) (he'.comp hf')]

end RingEquiv
