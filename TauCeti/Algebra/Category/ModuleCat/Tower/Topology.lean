/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic

/-!
# The inverse limit topology on the limit of a tower of modules

The terms `Aₙ` of a tower of modules carry no topology, so its limit `lim A ⊆ ∏ₙ Aₙ` carries the
inverse limit uniform structure of the discrete terms: the coarsest one for which every projection
`lim A → Aₙ` is uniformly continuous into the discrete uniformity. Two compatible families are
close when they agree at a large index, and since a compatible family is determined below an index
by its value there, the sets `{(x, y) | xₙ = yₙ}` form a basis of entourages. Equivalently, the
kernels of the projections form a basis of neighbourhoods of zero.

For this structure `lim A` is a uniform additive group on which every scalar acts continuously,
and it is Hausdorff and complete: a Cauchy filter has eventually constant projections, and these
constants form a compatible family to which it converges. This is the topology of profinite
limits, and of completions such as the `I`-adic completion `lim M ⧸ I^{n+1} M` and the completed
enveloping algebra `lim U ⧸ U · (𝔤 ⊗ tᴺ ℂ[[t]])` of an affine Lie algebra.

## Main results

* `TauCeti.ModuleTower.hasBasis_uniformity`: the entourages `{(x, y) | xₙ = yₙ}` form a basis.
* `TauCeti.ModuleTower.hasBasis_nhds`, `TauCeti.ModuleTower.hasBasis_nhds_zero`: the
  corresponding bases of neighbourhoods, the latter by the kernels of the projections.
* `TauCeti.ModuleTower.isOpen_setOf_limπ_eq`: the fibres of the projections are open, that is,
  the projections are continuous into the discrete terms.
* `TauCeti.ModuleTower.instCompleteSpaceLim`, `TauCeti.ModuleTower.instT2SpaceLim`: the limit is
  complete and Hausdorff.

## References

* N. Bourbaki, *General Topology*, Chapter II, §3.9, for inverse limits of uniform spaces.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite Filter Topology Uniformity

universe v u

variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)

/-- The **inverse limit uniform structure** on the limit of a tower of modules: the coarsest
uniform structure for which every projection `lim A → Aₙ` is uniformly continuous for the
discrete uniformity on `Aₙ`. -/
instance instUniformSpaceLim : UniformSpace F.lim :=
  ⨅ n, (⊥ : UniformSpace (F.obj (op n))).comap (F.limπ n)

/-- Two elements of `lim A` with the same projection to `Aₖ` have the same projection to every
`Aₙ` with `n ≤ k`. -/
theorem limπ_eq_of_le {x y : F.lim} {n k : ℕ} (h : n ≤ k) (hxy : F.limπ k x = F.limπ k y) :
    F.limπ n x = F.limπ n y := by
  simpa using congrArg (F.transitionOfLE h) hxy

/-- The entourages `{(x, y) | xₙ = yₙ}` form a basis of the inverse limit uniformity. -/
theorem hasBasis_uniformity :
    (𝓤 F.lim).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ {p : F.lim × F.lim | F.limπ n p.1 = F.limπ n p.2} := by
  simp only [iInf_uniformity, uniformity_comap, bot_uniformity,
    comap_principal]
  exact hasBasis_iInf_principal <| Antitone.directed_ge fun _ _ h _ hp ↦ F.limπ_eq_of_le h hp

/-- The sets `{y | yₙ = xₙ}` form a basis of neighbourhoods of `x ∈ lim A`. -/
theorem hasBasis_nhds (x : F.lim) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True) fun n ↦ {y | F.limπ n y = F.limπ n x} :=
  nhds_basis_uniformity F.hasBasis_uniformity

/-- The kernels of the projections `lim A → Aₙ` form a basis of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : F.lim)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (LinearMap.ker (F.limπ n) : Set F.lim) := by
  refine (F.hasBasis_nhds 0).congr (fun _ ↦ Iff.rfl) fun n _ ↦ ?_
  ext
  simp

/-- The fibres of each projection `lim A → Aₙ` are open: the projections are continuous for the
discrete topology on the terms. -/
theorem isOpen_setOf_limπ_eq (n : ℕ) (a : F.obj (op n)) : IsOpen {x : F.lim | F.limπ n x = a} :=
  isOpen_iff_mem_nhds.2 fun x hx ↦ (F.hasBasis_nhds x).mem_of_superset (i := n) trivial
    fun _ hy ↦ hy.trans hx

/-- Addition and negation on the limit of a tower are uniformly continuous. -/
instance instIsUniformAddGroupLim : IsUniformAddGroup F.lim :=
  isUniformAddGroup_iInf fun n ↦
    letI : UniformSpace (F.obj (op n)) := ⊥
    IsUniformAddGroup.comap (F.limπ n)

/-- Each scalar acts continuously on the limit of a tower. -/
instance instContinuousConstSMulLim : ContinuousConstSMul R F.lim where
  continuous_const_smul r := continuous_iff_continuousAt.2 fun x ↦
    (F.hasBasis_nhds x).tendsto_iff (F.hasBasis_nhds _) |>.2 fun n _ ↦
      ⟨n, trivial, fun _ hy ↦ by rw [Set.mem_ofPred_eq] at hy ⊢; rw [map_smul, map_smul, hy]⟩

/-- The limit of a tower is Hausdorff: a compatible family is determined by its projections. -/
instance instT2SpaceLim : T2Space F.lim :=
  have : T0Space F.lim := t0Space_iff_uniformity.2 fun x y h ↦ Subtype.ext <| funext fun n ↦
    by simpa using h _ (F.hasBasis_uniformity.mem_of_mem (i := n) trivial)
  inferInstance

/-- **The limit of a tower is complete.** The projections of a Cauchy filter are eventually
constant, and these constants form a compatible family to which the filter converges. -/
instance instCompleteSpaceLim : CompleteSpace F.lim where
  complete {f} hf := by
    obtain ⟨hne, hf⟩ := F.hasBasis_uniformity.cauchy_iff.1 hf
    -- For each `n`, a set `S n ∈ f` on which the projection to `Aₙ` is constant, and a point.
    choose S hS hSc using fun n ↦ hf n trivial
    choose s hs using fun n ↦ hne.nonempty_of_mem (hS n)
    have hcomp (n : ℕ) : F.limπ n (s (n + 1)) = F.limπ n (s n) := by
      obtain ⟨z, hz₁, hz⟩ := hne.nonempty_of_mem (inter_mem (hS (n + 1)) (hS n))
      rw [F.limπ_eq_of_le n.le_succ (hSc _ _ (hs _) z hz₁), hSc n z hz (s n) (hs n)]
    refine ⟨⟨fun n ↦ F.limπ n (s n), F.mem_lim.2 fun n ↦ ?_⟩, ?_⟩
    · exact (LinearMap.congr_fun (F.transition_comp_limπ n) _).trans (hcomp n)
    · exact (F.hasBasis_nhds _).ge_iff.2 fun n _ ↦
        mem_of_superset (hS n) fun y hy ↦ by simpa using hSc n y hy (s n) (hs n)

end TauCeti.ModuleTower
