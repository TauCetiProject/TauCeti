/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Topology.Algebra.Group.Quotient.Prod
public import TauCeti.Topology.Algebra.Module.Submodule
import TauCeti.Topology.Algebra.Module.CompactQuotient

/-!
# The vector part of a cocompact subgroup of `V × K` is a full lattice

Let `V` be a finite-dimensional Hausdorff real topological vector space, `K` a topological group,
and `Γ` a subgroup of `V × K`, written multiplicatively as `Multiplicative V × K`, such that the
quotient `(V × K) ⧸ Γ` is compact and the image of `Γ` in `K` is finite. Then the part of `Γ` in
the first factor,

`Λ = {v | (v, 1) ∈ Γ}`,

spans `V` (`Subgroup.span_toAddSubgroup'_comap_inl_eq_top`). When moreover `V` is a normed
space and `Γ` is discrete, `Λ` is a full lattice in `V`
(`Subgroup.isZLattice_toAddSubgroup'_comap_inl`), so `V ⧸ Λ` is a compact torus. The image `P`
of `Γ` in `V` spans `V`, since `V ⧸ P` is a continuous image of the compact quotient
(`AddSubgroup.span_eq_top_of_compactSpace_quotient`). If the image of `Γ` in `K` has `m`
elements, then `γᵐ` lies in `V × 1` for every `γ ∈ Γ`, so `m • P ⊆ Λ` and `Λ` spans `V` as well.

Together with the finite covering `(V ⧸ Λ) × K → (V × K) ⧸ Γ` of `Subgroup.prodQuotientMap`, this
is the decomposition of a compact connected Lie group `G = (ℝʳ × K) ⧸ Γ` as a finite quotient of
the product of a torus and `K`. The finiteness hypothesis holds when `Γ` is central and `K` has
finite centre (`Subgroup.finite_map_snd_of_le_center`).

## Main results

* `Subgroup.span_toAddSubgroup'_comap_inl_eq_top`: `Λ` spans `V`.
* `Subgroup.isZLattice_toAddSubgroup'_comap_inl`: `Λ` is a full lattice in `V`.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.31).
-/

public section

namespace Subgroup

section Topology

variable {V K : Type*} [AddCommGroup V] [TopologicalSpace V] [Group K] [TopologicalSpace K]
  (Γ : Subgroup (Multiplicative V × K))

/-- The part `{v | (v, 1) ∈ Γ}` of a discrete subgroup `Γ` of `V × K` lying in `V` is discrete. -/
instance discreteTopology_toAddSubgroup'_comap_inl [DiscreteTopology Γ] :
    DiscreteTopology (Γ.comap (MonoidHom.inl (Multiplicative V) K)).toAddSubgroup' :=
  inferInstanceAs (DiscreteTopology (Γ.comap (MonoidHom.inl (Multiplicative V) K)))

variable [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [FiniteDimensional ℝ V]

/-- **The vector part of a cocompact subgroup of `V × K` spans `V`.** If the quotient
`(V × K) ⧸ Γ` is compact and the image of `Γ` in `K` is finite, then `Λ = {v | (v, 1) ∈ Γ}` spans
`V`. -/
theorem span_toAddSubgroup'_comap_inl_eq_top [CompactSpace ((Multiplicative V × K) ⧸ Γ)]
    [Finite (Γ.map (MonoidHom.snd (Multiplicative V) K))] :
    Submodule.span ℝ ((Γ.comap (MonoidHom.inl (Multiplicative V) K)).toAddSubgroup' : Set V) =
      ⊤ := by
  set Λ := (Γ.comap (MonoidHom.inl (Multiplicative V) K)).toAddSubgroup'
  -- The image `P` of `Γ` in `V` has compact quotient, so it spans `V`.
  set P := (Γ.map (MonoidHom.fst (Multiplicative V) K)).toAddSubgroup'
  have hrel : ∀ a b : Multiplicative V × K, QuotientGroup.leftRel Γ a b →
      QuotientAddGroup.leftRel P a.1.toAdd b.1.toAdd := fun a b h ↦ by
    rw [QuotientGroup.leftRel_apply] at h
    rw [QuotientAddGroup.leftRel_apply, mem_toAddSubgroup']
    exact ⟨_, h, rfl⟩
  have hcont : Continuous (Quotient.map' (fun g : Multiplicative V × K ↦ g.1.toAdd) hrel :
      (Multiplicative V × K) ⧸ Γ → V ⧸ P) :=
    (continuous_fst.comp continuous_id).quotient_map' hrel
  have hsurj : Function.Surjective (Quotient.map' (fun g : Multiplicative V × K ↦ g.1.toAdd) hrel :
      (Multiplicative V × K) ⧸ Γ → V ⧸ P) := by
    rintro ⟨v⟩
    exact ⟨Quotient.mk'' (Multiplicative.ofAdd v, 1), rfl⟩
  have : CompactSpace (V ⧸ P) := hsurj.compactSpace hcont
  have hP := AddSubgroup.span_eq_top_of_compactSpace_quotient P
  -- If the image of `Γ` in `K` has `m` elements, then `m • P ⊆ Λ`.
  set m := Nat.card (Γ.map (MonoidHom.snd (Multiplicative V) K))
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hmP : ∀ p ∈ P, m • p ∈ Λ := by
    intro p hp
    obtain ⟨γ, hγ, hγp⟩ := mem_toAddSubgroup' _ p |>.1 hp
    have h2 : γ.2 ^ m = 1 := by
      have := congrArg Subtype.val
        (pow_card_eq_one' (x := (⟨γ.2, γ, hγ, rfl⟩ : Γ.map (MonoidHom.snd (Multiplicative V) K))))
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    have hpow : γ ^ m = MonoidHom.inl (Multiplicative V) K (Multiplicative.ofAdd (m • p)) := by
      ext
      · simp [← hγp]
      · simp [h2]
    rw [mem_toAddSubgroup', mem_comap, ← hpow]
    exact pow_mem hγ m
  rw [eq_top_iff, ← hP, Submodule.span_le]
  intro p hp
  have h : (m : ℝ) • p ∈ Submodule.span ℝ (Λ : Set V) := by
    rw [Nat.cast_smul_eq_nsmul]
    exact Submodule.subset_span (hmP p hp)
  simpa [smul_smul, inv_mul_cancel₀ hm] using Submodule.smul_mem _ (m : ℝ)⁻¹ h

end Topology

section Normed

variable {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Group K]
  [TopologicalSpace K] (Γ : Subgroup (Multiplicative V × K))

/-- **The vector part of a discrete cocompact subgroup of `V × K` is a full lattice.** If `Γ` is a
discrete subgroup of `V × K` with compact quotient and finite image in `K`, then
`Λ = {v | (v, 1) ∈ Γ}` is a full lattice in `V`, so `V ⧸ Λ` is a compact torus. -/
theorem isZLattice_toAddSubgroup'_comap_inl [DiscreteTopology Γ]
    [CompactSpace ((Multiplicative V × K) ⧸ Γ)]
    [Finite (Γ.map (MonoidHom.snd (Multiplicative V) K))] :
    IsZLattice ℝ (Γ.comap (MonoidHom.inl (Multiplicative V) K)).toAddSubgroup'.toIntSubmodule where
  span_top := Γ.span_toAddSubgroup'_comap_inl_eq_top

end Normed

end Subgroup
