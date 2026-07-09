/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy

/-!
# Deprecated compatibility import for smooth-embedding ambient isotopy

This module preserves the old public import path after the smooth-embedding relation was renamed
to `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic`.
-/

public section

namespace TauCeti

namespace SmoothEmbedding

/-- Deprecated compatibility alias for the old smooth-embedding ambient-isotopy relation name. -/
@[deprecated ContinuousAmbientIsotopic (since := "2026-07-09")]
alias AmbientIsotopic := ContinuousAmbientIsotopic

/-- Deprecated compatibility alias for the old smooth-embedding ambient-isotopy characterisation
name. -/
@[deprecated continuousAmbientIsotopic_def (since := "2026-07-09")]
alias ambientIsotopic_def := continuousAmbientIsotopic_def

namespace AmbientIsotopic

/-- Deprecated compatibility alias for the old ambient-isotopy constructor name. -/
@[deprecated ContinuousAmbientIsotopic.of_ambientIsotopy (since := "2026-07-09")]
alias of_ambientIsotopy := ContinuousAmbientIsotopic.of_ambientIsotopy

/-- Deprecated compatibility alias for the old endpoint-oriented ambient-isotopy constructor
name. -/
@[deprecated ContinuousAmbientIsotopic.of_eq_final_comp (since := "2026-07-09")]
alias of_eq_final_comp := ContinuousAmbientIsotopic.of_eq_final_comp

/-- Deprecated compatibility alias for the old ambient-isotopy reflexivity theorem name. -/
@[deprecated ContinuousAmbientIsotopic.refl (since := "2026-07-09")]
alias refl := ContinuousAmbientIsotopic.refl

/-- Deprecated compatibility alias for the old ambient-isotopy symmetry theorem name. -/
@[deprecated ContinuousAmbientIsotopic.symm (since := "2026-07-09")]
alias symm := ContinuousAmbientIsotopic.symm

/-- Deprecated compatibility alias for the old ambient-isotopy transitivity theorem name. -/
@[deprecated ContinuousAmbientIsotopic.trans (since := "2026-07-09")]
alias trans := ContinuousAmbientIsotopic.trans

/-- Deprecated compatibility alias for the old ambient-isotopy-to-isotopy theorem name. -/
@[deprecated ContinuousAmbientIsotopic.isotopic (since := "2026-07-09")]
alias isotopic := ContinuousAmbientIsotopic.isotopic

/-- Deprecated compatibility alias for the old ambient-isotopy equivalence theorem name. -/
@[deprecated ContinuousAmbientIsotopic.equivalence (since := "2026-07-09")]
alias equivalence := ContinuousAmbientIsotopic.equivalence

/-- Deprecated compatibility alias for the old ambient-isotopy setoid name. -/
@[deprecated ContinuousAmbientIsotopic.setoid (since := "2026-07-09")]
alias setoid := ContinuousAmbientIsotopic.setoid

/-- Deprecated compatibility alias for the old ambient-isotopy setoid relation theorem name. -/
@[deprecated ContinuousAmbientIsotopic.setoid_r_iff (since := "2026-07-09")]
alias setoid_r_iff := ContinuousAmbientIsotopic.setoid_r_iff

end AmbientIsotopic

end SmoothEmbedding

end TauCeti
