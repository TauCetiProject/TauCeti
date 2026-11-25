/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.RelativeNorm
public import TauCeti.RepresentationTheory.Subrepresentation
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Relative Maschke theorem

Let `H` be a subgroup of finite index in a group `G`, and suppose the index `[G : H]` is invertible
in the field `k`. A representation `ρ` of `G` over `k` is semisimple as soon as its restriction to
`H` is (`Representation.isSemisimpleRepresentation_of_comp_subtype`). No finiteness of `G`, of `H`
or of the dimension is needed. For `H = ⊥` and `G` finite this is Maschke's theorem.

The proof averages a projection. Given a subrepresentation `W` of `ρ`, semisimplicity of the
restriction gives an `H`-equivariant linear projection `π` of `V` onto `W`
(`Subrepresentation.exists_equivariant_projection`). Its relative norm
`∑_{q ∈ G ⧸ H} ρ(q) π ρ(q)⁻¹` over coset representatives (`Representation.relNorm` of the
conjugation action) is `G`-equivariant, maps into `W`, and is
`[G : H]` on `W`; dividing by the index gives a `G`-equivariant projection onto `W`, whose kernel is
a `G`-stable complement of `W`.

## Main results

* `Representation.isSemisimpleRepresentation_of_comp_subtype`: a representation whose restriction
  to a subgroup of finite index invertible in `k` is semisimple is itself semisimple.

## References

* W. Gaschütz, *Über den Fundamentalsatz von Maschke zur Darstellungstheorie der endlichen
  Gruppen*, Math. Z. **56** (1952), 376–387.
* D. G. Higman, *Modules with a group of operators*, Duke Math. J. **21** (1954), 369–376, for
  the averaging of a projection over a transversal of a subgroup.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The relative Maschke theorem.** If `H` has finite index in `G` that is invertible in `k`, and
the restriction of `ρ` to `H` is semisimple, then `ρ` is semisimple. -/
theorem isSemisimpleRepresentation_of_comp_subtype (ρ : Representation k G V) (H : Subgroup G)
    [NeZero (H.index : k)] [IsSemisimpleRepresentation (ρ.comp H.subtype)] :
    IsSemisimpleRepresentation ρ := by
  classical
  -- An infinite index is `0`, which is not invertible.
  have : H.FiniteIndex := ⟨fun h ↦ NeZero.ne (H.index : k) (by simp [h])⟩
  have : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨fun W ↦ ?_⟩
  -- An `H`-equivariant projection `π` of `V` onto `W`.
  obtain ⟨π₀, hπid₀, hπH₀⟩ := Subrepresentation.exists_equivariant_projection
    (⟨W.toSubmodule, fun h ↦ W.apply_mem_toSubmodule h⟩ : Subrepresentation (ρ.comp H.subtype))
  let π : V →ₗ[k] V := W.toSubmodule.subtype ∘ₗ π₀
  have hπW (x : V) : π x ∈ W.toSubmodule := (π₀ x).property
  have hπid (x : V) (hx : x ∈ W.toSubmodule) : π x = x := congrArg Subtype.val (hπid₀ ⟨x, hx⟩)
  have hπH (h : H) (x : V) : π (ρ h x) = ρ h (π x) := hπH₀ h x
  -- The averaged projection `P = [G : H]⁻¹ ∑ ρ(q) π ρ(q)⁻¹`.
  let P : V →ₗ[k] V := (H.index : k)⁻¹ • relNorm (linHom ρ ρ) H π
  have hP : LinearMap.IsProj W.toSubmodule P :=
    isProj_inv_index_smul_relNorm_linHom ρ (fun g _ hx ↦ W.apply_mem_toSubmodule g hx)
      ⟨hπW, hπid⟩ (NeZero.ne _)
  have hPG (g : G) (x : V) : P (ρ g x) = ρ g (P x) := by
    rw [LinearMap.smul_apply, relNorm_linHom_apply_comm ρ ρ hπH, LinearMap.smul_apply, map_smul]
  -- Its kernel is a `G`-stable complement of `W`.
  let K : Subrepresentation ρ :=
    ⟨LinearMap.ker P, fun g x hx ↦ by
      rw [LinearMap.mem_ker, hPG, LinearMap.mem_ker.mp hx, map_zero]⟩
  exact ⟨K, Subrepresentation.isCompl_toSubmodule.mp hP.isCompl⟩

end Representation
