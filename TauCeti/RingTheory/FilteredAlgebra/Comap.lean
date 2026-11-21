/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Inverse images of ideal filtrations

The inverse image of a decreasing multiplicative ideal filtration under a ring homomorphism
is again such a filtration. Its ideals are the contractions of the individual terms.
-/

public section

namespace TauCeti.AlgFiltration

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]

/-- Pull back a decreasing multiplicative ideal filtration by contracting each ideal. -/
def comap (F : AlgFiltration S) (f : R →+* S) : AlgFiltration R where
  ideal n := (F.ideal n).comap f
  isTwoSided _ := inferInstance
  antitone := fun _ _ h ↦ Ideal.comap_mono (F.antitone h)
  ideal_zero := by simp
  mul_mem := fun hx hy ↦ by
    rw [Ideal.mem_comap, map_mul]
    exact F.mul_mem (Ideal.mem_comap.mp hx) (Ideal.mem_comap.mp hy)

/-- Each term of the pullback filtration is the contraction of the corresponding ideal. -/
@[simp]
theorem comap_ideal (F : AlgFiltration S) (f : R →+* S) (n : ℕ) :
    (F.comap f).ideal n = (F.ideal n).comap f := (rfl)

/-- Pullback along the identity preserves the filtration. -/
@[simp]
theorem comap_id (F : AlgFiltration R) : F.comap (RingHom.id R) = F := by
  apply AlgFiltration.ext
  funext n
  simp

/-- Successive pullbacks agree with pullback along the composite. -/
@[simp]
theorem comap_comap (F : AlgFiltration T) (g : S →+* T) (f : R →+* S) :
    (F.comap g).comap f = F.comap (g.comp f) := by
  apply AlgFiltration.ext
  funext n
  simp [← Ideal.comap_comap]

end TauCeti.AlgFiltration
