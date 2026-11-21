/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Von Neumann boundedness helpers

A product `s ×ˢ t` of von Neumann bounded subsets of two topological spaces with a `𝕜`-action is
von Neumann bounded in the product space (`Bornology.IsVonNBounded.prod`), and if the image of a
set `s` into a normed space is von Neumann bounded then the norms on `s` are bounded above
(`Bornology.IsVonNBounded.bddAbove_range_norm`).
-/

public section

open Set

namespace Bornology

variable {𝕜 E F : Type*} [SeminormedRing 𝕜]
  [Zero E] [SMul 𝕜 E] [TopologicalSpace E] [Zero F] [SMul 𝕜 F] [TopologicalSpace F]

/-- A product of von Neumann bounded sets is von Neumann bounded. -/
protected theorem IsVonNBounded.prod {s : Set E} {t : Set F} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) : IsVonNBounded 𝕜 (s ×ˢ t) := by
  intro W hW
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  filter_upwards [(hs hU).eventually, (ht hV).eventually] with a ha hb
  grw [← hUV, smul_set_prod, ha, hb]

/-- If the image of a set `s` under `f` into a normed space is von Neumann bounded, then the
norms `‖f x‖` on `s` are bounded above. -/
theorem IsVonNBounded.bddAbove_range_norm {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
    (hs : IsVonNBounded 𝕜 (f '' s)) :
    BddAbove (Set.range fun x : s ↦ ‖f x‖) :=
  let ⟨r, hr⟩ := (NormedSpace.image_isVonNBounded_iff 𝕜).1 hs
  ⟨r, Set.forall_mem_range.2 fun x ↦ hr x.val x.property⟩

end Bornology
