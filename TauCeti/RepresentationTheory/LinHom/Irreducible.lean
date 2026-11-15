/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Irreducible
import TauCeti.LinearAlgebra.LinearMap.Submodule

/-!
# Irreducibility of the two-sided Hom representation

For finite-dimensional irreducible representations `ρ` of `H` and `σ` of `G` over an
algebraically closed field, `Hom(V, W)` is irreducible under the action of `G × H` given by
`(g, h) • f = σ g ∘ f ∘ ρ h⁻¹`. Burnside density makes an invariant subspace stable under
all precomposition and postcomposition. The result applies to the endomorphism blocks in
the Peter-Weyl decomposition.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Chapter III.
* `Representation.asAlgebraHom_surjective_of_isIrreducible`: Burnside density.
-/

public section

namespace Representation

variable {k G H V W : Type*} [Field k] [IsAlgClosed k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The two-sided Hom representation of a product of groups is irreducible when its source
and target representations are finite-dimensional and irreducible over an algebraically
closed field. The first group acts on the target and the second on the source.

Both acting types are groups because `Representation.linHom` requires its acting type
`G × H` to be a group, although the displayed action only inverts the source factor. -/
theorem isIrreducible_linHom_comp_snd_comp_fst
    (ρ : Representation k H V) (σ : Representation k G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) :
    (linHom (ρ.comp (MonoidHom.snd G H)) (σ.comp (MonoidHom.fst G H))).IsIrreducible := by
  have := hρ.nontrivial
  have := hσ.nontrivial
  refine ⟨fun N ↦ ?_⟩
  have hleft (a : Module.End k W) {f : V →ₗ[k] W} (hf : f ∈ N) : a.comp f ∈ N := by
    obtain ⟨r, rfl⟩ := asAlgebraHom_surjective_of_isIrreducible σ hσ a
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
      rw [map_zero]
      simpa only [LinearMap.zero_comp, LinearMap.comp_zero,
        Subrepresentation.mem_toSubmodule] using N.toSubmodule.zero_mem
    | add a b ha hb => simpa [LinearMap.add_comp] using N.toSubmodule.add_mem ha hb
    | single g c =>
      have h := N.apply_mem_toSubmodule (g, 1) hf
      simpa [linHom_apply, Module.End.one_eq_id, LinearMap.smul_comp] using
        N.toSubmodule.smul_mem c h
  have hright (a : Module.End k V) {f : V →ₗ[k] W} (hf : f ∈ N) : f.comp a ∈ N := by
    obtain ⟨r, rfl⟩ := asAlgebraHom_surjective_of_isIrreducible ρ hρ a
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
      rw [map_zero]
      simpa only [LinearMap.zero_comp, LinearMap.comp_zero,
        Subrepresentation.mem_toSubmodule] using N.toSubmodule.zero_mem
    | add a b ha hb => simpa [LinearMap.comp_add] using N.toSubmodule.add_mem ha hb
    | single h c =>
      have hm := N.apply_mem_toSubmodule (1, h⁻¹) hf
      simpa [linHom_apply, Module.End.one_eq_id, LinearMap.comp_smul] using
        N.toSubmodule.smul_mem c hm
  exact (N.toSubmodule.eq_bot_or_eq_top_of_comp_mem hleft hright).imp
    (fun h ↦ Subrepresentation.toSubmodule_injective (by simpa using h))
    (fun h ↦ Subrepresentation.toSubmodule_injective (by simpa using h))

end Representation
