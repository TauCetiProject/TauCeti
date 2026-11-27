/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commensurable

/-!
# Commensurators: the whole group, and transport along injective homomorphisms

The commensurator of a subgroup `H` of `G` is all of `G` exactly when every conjugate `g H g⁻¹`
meets `H` in a subgroup of finite index in `H`. Commensurability of `g H g⁻¹` with `H` also asks
that `H ∩ g H g⁻¹` have finite index in `g H g⁻¹`, but this second condition is the first one for
`g⁻¹`, conjugated by `g`, so only one direction has to be checked for each element.

This is the form in which the commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)` is computed: for each `g`
one exhibits a congruence subgroup of `GL_n(ℤ_p)` inside `g GL_n(ℤ_p) g⁻¹`.

An injective homomorphism `f : G →* G'` identifies the commensurator of `H` with the elements of
the range of `f` that commensurate `f(H)` in `G'`: conjugation by `f g` on `f(H)` is the image of
conjugation by `g` on `H`, and commensurability of images along an injective map is
commensurability of the subgroups. When the range of `f` has finite index, `f(H)` keeps finite index
in its commensurator. This is how the commensurator of a subgroup of `PSL(2, ℝ)` is compared with
the commensurator of its image in `PGL(2, ℝ)`, where the image of `PSL(2, ℝ)` has index two.

## Main results

* `Subgroup.Commensurable.commensurator_eq_top_iff`: `commensurator H = ⊤` if and only if
  `g H g⁻¹ ∩ H` has finite index in `H` for every `g`.
* `Subgroup.Commensurable.comap_commensurator_map`: for injective `f`, the preimage of the
  commensurator of `f(H)` is the commensurator of `H`.
* `Subgroup.Commensurable.map_commensurator`: for injective `f`, the image of the commensurator of
  `H` is the part of the commensurator of `f(H)` lying in the range of `f`.
* `Subgroup.Commensurable.isFiniteRelIndex_commensurator_map`: if `f` is injective with range of
  finite index and `H` has finite index in its commensurator, then so has `f(H)`.
-/

public section

open scoped Pointwise

namespace Subgroup.Commensurable

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **The commensurator of `H` is the whole group** exactly when, for every `g`, the conjugate
`g H g⁻¹` meets `H` in a subgroup of finite index in `H`. The other half of commensurability,
finite index in `g H g⁻¹`, follows by applying the condition to `g⁻¹`. -/
theorem commensurator_eq_top_iff :
    commensurator H = ⊤ ↔ ∀ g : G, (MulAut.conj g • H).IsFiniteRelIndex H := by
  refine ⟨fun h g ↦ ((commensurator_mem_iff H g).mp (h ▸ mem_top g)).1, fun h ↦ ?_⟩
  refine eq_top_iff.mpr fun g _ ↦ (commensurator_mem_iff H g).mpr ⟨h g, ?_⟩
  have hg := h g⁻¹
  rw [isFiniteRelIndex_iff_relIndex_ne_zero] at hg ⊢
  rwa [← relIndex_pointwise_smul (MulAut.conj g)⁻¹, inv_smul_smul, ← map_inv]

variable {G' : Type*} [Group G'] {f : G →* G'}

/-- Along an injective homomorphism `f`, an element `g` commensurates `H` exactly when `f g`
commensurates `f(H)`. -/
theorem comap_commensurator_map (hf : Function.Injective f) (H : Subgroup G) :
    (commensurator (H.map f)).comap f = commensurator H := by
  ext g
  have hconj : MulAut.conj (f g) • H.map f = (MulAut.conj g • H).map f := by
    ext x
    simp [pointwise_smul_def]
  rw [mem_comap, commensurator_mem_iff, commensurator_mem_iff, hconj, map_injective_iff hf]

/-- Along an injective homomorphism `f`, the image of the commensurator of `H` consists of the
elements of the range of `f` that commensurate `f(H)`. -/
theorem map_commensurator (hf : Function.Injective f) (H : Subgroup G) :
    (commensurator H).map f = f.range ⊓ commensurator (H.map f) := by
  rw [← map_comap_eq, comap_commensurator_map hf]

/-- If `f` is injective with range of finite index and `H` has finite index in its commensurator,
then `f(H)` has finite index in its commensurator. -/
theorem isFiniteRelIndex_commensurator_map (hf : Function.Injective f) [f.range.FiniteIndex]
    (hH : H.IsFiniteRelIndex (commensurator H)) :
    (H.map f).IsFiniteRelIndex (commensurator (H.map f)) := by
  have hrange : (H.map f).IsFiniteRelIndex (f.range ⊓ commensurator (H.map f)) := by
    rw [← map_commensurator hf]
    exact hH.map f
  exact hrange.trans (isFiniteRelIndex_of_finiteIndex.inf inferInstance)

end Subgroup.Commensurable
