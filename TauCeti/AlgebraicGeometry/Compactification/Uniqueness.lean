/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Uniqueness of maps from dense compactifications

Two maps from a compactification with schematically dense interior to any fixed
compactification agree. The target need not be dense, and the source need not be reduced.
Consequently, dense compactifications form a thin category: once refinement maps exist,
all diagrams of such maps commute. This is the uniqueness input for comparing different
compactifications coherently.

The geometric input is `TauCeti.ext_of_isSchemeTheoreticallyDominant`, applied to the
proper, hence separated, structure map of the target compactification. Density is required
only on the source: agreement on the interior does not control extra components of a
nondense compactification.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT), and Section 29.7,
  *Scheme theoretic closure and density* (tag 01RA).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

/-- Maps from a compactification with schematically dense interior to any fixed
compactification are unique. No density assumption on the target is needed. -/
theorem hom_unique {C D : Compactification f} [IsSchemeTheoreticallyDominant C.j]
    (h k : C ⟶ D) : h = k := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  exact ext_of_isSchemeTheoreticallyDominant C.j D.p (by simp) (by simp)

instance {C D : Compactification f} [IsSchemeTheoreticallyDominant C.j] :
    Subsingleton (C ⟶ D) :=
  ⟨hom_unique⟩

end Compactification

namespace DenseCompactification

/-- Dense compactifications have at most one refinement map between any two objects. -/
instance : Quiver.IsThin (DenseCompactification f) := fun _ _ ↦ ⟨fun h k ↦ by
  apply ObjectProperty.hom_ext
  exact Compactification.hom_unique h.hom k.hom⟩

end DenseCompactification

end TauCeti
