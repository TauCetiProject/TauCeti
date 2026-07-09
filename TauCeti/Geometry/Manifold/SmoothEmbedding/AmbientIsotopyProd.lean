/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopyProd
public import TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopy

/-!
# Deprecated compatibility import for products of smooth-embedding ambient isotopies

This module preserves the old public import path after the smooth-embedding product ambient
isotopy API was renamed to
`TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.prodMap`.
-/

public section

namespace TauCeti

namespace SmoothEmbedding

namespace AmbientIsotopic

/-- Deprecated compatibility alias for the old smooth-embedding product ambient-isotopy theorem
name. -/
@[deprecated ContinuousAmbientIsotopic.prodMap (since := "2026-07-09")]
alias prodMap := ContinuousAmbientIsotopic.prodMap

/-- Deprecated compatibility alias for the old smooth-embedding product ambient-isotopy setoid
theorem name. -/
@[deprecated ContinuousAmbientIsotopic.prodMap_setoid (since := "2026-07-09")]
alias prodMap_setoid := ContinuousAmbientIsotopic.prodMap_setoid

end AmbientIsotopic

end SmoothEmbedding

end TauCeti
