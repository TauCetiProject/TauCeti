/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.BracketSpan
public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification

/-!
# The pivot-constrained span statement for basis modifications

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type, and let
`ρ ∈ gr_1(F)` be a class without `p`-power part whose partial derivatives `∂_i ρ` span `gr_0(F)`,
the class of a relator `x₀^q (x₀, x₁) (x₂, x₃) ⋯` with `q ≠ p` in which every generator occurs in a
commutator. The image of the basis-modification map `δ_ρ : gr_m(F)^X → gr_{m+1}(F)` is the
commutator part `[gr_m(F), gr_0(F)]` of `gr_{m+1}(F)`
(`TauCeti.freeProP.range_basisModificationDelta_eq_span_of_repr_inl_eq_zero`). The successive
approximation of such a relator has to keep its exponent vector fixed, so its basis corrections
`x_i ↦ x_i w_i` must take `w_{x₀}` in the commutator subgroup at the pivot `x₀` carrying the
`p`-power: the correction is allowed to be arbitrary at the other generators only.

This file shows that the constraint costs nothing: **every element of `Im δ_ρ` is `δ_ρ(ω)` for a
family `ω` whose component at any prescribed generator `x₀` lies in the bracket span
`C_m(F) = [gr_{m-1}(F), gr_0(F)]`**
(`TauCeti.freeProP.exists_apply_mem_gradedBracketSpan_basisModificationDelta_eq`), hence is the
class of an element of `λ_m(F)` in the commutator subgroup
(`TauCeti.freeProP.exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range`). No
hypothesis on `x₀` is needed.

## Main results

* `TauCeti.freeProP.exists_apply_mem_gradedBracketSpan_basisModificationDelta_eq`: every element
  of `Im δ_ρ` is `δ_ρ(ω)` with `ω_{x₀} ∈ C_m(F)`.
* `TauCeti.freeProP.exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range`: every
  element of `Im δ_ρ` is `δ_ρ(⟦ω⟧)` for a family `ω : X → λ_m(F)` with `ω_{x₀}` in the commutator
  subgroup of `F`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti.freeProP

open Subgroup Submodule

universe u

variable {p : ℕ} {X : Type u} {m : ℕ} [Fact p.Prime] [Finite X] [LinearOrder X]

/-- **The pivot-constrained span statement, graded form.** Let `ρ ∈ gr_1(F)` have no `p`-power part
and partial derivatives spanning `gr_0(F)`. Every element of the image of
`δ_ρ : gr_{k+1}(F)^X → gr_{k+2}(F)` is `δ_ρ(ω)` for a family `ω` whose component at the prescribed
generator `x₀` lies in the bracket span `C_{k+1}(F) = [gr_k(F), gr_0(F)]`. -/
theorem exists_apply_mem_gradedBracketSpan_basisModificationDelta_eq {k : ℕ}
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) (x₀ : X)
    {y : gradedPiece p (freeProP p X) (k + 1 + 1)}
    (hy : y ∈ LinearMap.range (basisModificationDelta p X (Nat.le_add_left 1 k) ρ)) :
    ∃ ω : X → gradedPiece p (freeProP p X) (k + 1),
      ω x₀ ∈ gradedBracketSpan p (freeProP p X) k ∧
        basisModificationDelta p X (Nat.le_add_left 1 k) ρ ω = y := by
  classical
  cases nonempty_fintype X
  -- `W` is the set of values `δ_ρ(ω)` with `ω_{x₀} ∈ C_{k+1}(F)`; the claim is `Im δ_ρ ≤ W`.
  set W : Submodule (ZMod p) (gradedPiece p (freeProP p X) (k + 1 + 1)) :=
    ((gradedBracketSpan p (freeProP p X) k).comap (LinearMap.proj x₀)).map
      (basisModificationDelta p X (Nat.le_add_left 1 k) ρ) with hW
  have hmemW : ∀ ω : X → gradedPiece p (freeProP p X) (k + 1),
      ω x₀ ∈ gradedBracketSpan p (freeProP p X) k →
        basisModificationDelta p X (Nat.le_add_left 1 k) ρ ω ∈ W := fun ω hω ↦
    Submodule.mem_map.mpr ⟨ω, Submodule.mem_comap.mpr (by rwa [LinearMap.proj_apply]), rfl⟩
  have hspan : ∀ z : gradedPiece p (freeProP p X) 0,
      z ∈ span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) := fun z ↦ by
    rw [hρ]
    exact mem_top
  -- Brackets `[c, z]` with `c ∈ C_{k+1}(F)` are values `δ_ρ(b • c)` with pivot component in `C`.
  have hbracket : ∀ c ∈ gradedBracketSpan p (freeProP p X) k,
      ∀ z : gradedPiece p (freeProP p X) 0,
        gradedBracket p (freeProP p X) (k + 1) 0 c z ∈ W := by
    intro c hc' z
    obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun (ZMod p)).mp (hspan z)
    have h := hmemW (fun i ↦ b i • c) (smul_mem _ (b x₀) hc')
    rw [basisModificationDelta_smul, hb] at h
    simpa only [hc, mul_zero, Finset.sum_const_zero, zero_smul, zero_add] using h
  -- Brackets `[π^{k+1} ∂_{x₀} ρ, u]`: write `u = Σ_j b_j ∂_j ρ` and drop the term at `j = x₀`,
  -- which is `b_{x₀} • [π^{k+1} ∂_{x₀} ρ, ∂_{x₀} ρ] = 0`.
  have hpivot : ∀ u : gradedPiece p (freeProP p X) 0,
      gradedBracket p (freeProP p X) (k + 1) 0
        (gradedPowIter p (freeProP p X) (k + 1) (degreeOneDeriv p X x₀ ρ)) u ∈ W := by
    intro u
    obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun (ZMod p)).mp (hspan u)
    have hδ : basisModificationDelta p X (Nat.le_add_left 1 k) ρ
        ((fun i ↦ b i • gradedPowIter p (freeProP p X) (k + 1) (degreeOneDeriv p X x₀ ρ)) -
          Pi.single x₀ (b x₀ • gradedPowIter p (freeProP p X) (k + 1) (degreeOneDeriv p X x₀ ρ))) =
        gradedBracket p (freeProP p X) (k + 1) 0
          (gradedPowIter p (freeProP p X) (k + 1) (degreeOneDeriv p X x₀ ρ)) u := by
      rw [map_sub, basisModificationDelta_smul, hb, basisModificationDelta_single]
      simp only [hc, mul_zero, Finset.sum_const_zero, zero_smul, zero_add]
      rw [← gradedBracketLinear_apply
        (b x₀ • gradedPowIter p (freeProP p X) (k + 1) (degreeOneDeriv p X x₀ ρ)), map_smul,
        LinearMap.smul_apply, gradedBracketLinear_apply, gradedBracket_gradedPowIter_self,
        smul_zero, sub_zero]
    rw [← hδ]
    refine hmemW _ ?_
    rw [Pi.sub_apply, Pi.single_eq_same, sub_self]
    exact zero_mem _
  -- Brackets `[u, ∂_{x₀} ρ]` for every `u ∈ gr_{k+1}(F)`: decompose `u = c + t`.
  have hderiv : ∀ u : gradedPiece p (freeProP p X) (k + 1),
      gradedBracket p (freeProP p X) (k + 1) 0 u (degreeOneDeriv p X x₀ ρ) ∈ W := by
    intro u
    have hu : u ∈ gradedBracketSpan p (freeProP p X) k ⊔
        span (ZMod p) (Set.range (gradedPowIter p (freeProP p X) (k + 1))) := by
      rw [gradedBracketSpan_sup_span_range_gradedPowIter_eq_top
        ((isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out _)]
      exact mem_top
    obtain ⟨c, hc', t, ht, rfl⟩ := mem_sup.mp hu
    rw [map_add, AddMonoidHom.add_apply]
    refine add_mem (hbracket c hc' _) ?_
    -- The set of `t` with `[t, ∂_{x₀} ρ] ∈ W` is a submodule containing every `π^{k+1} x`.
    have hle : span (ZMod p) (Set.range (gradedPowIter p (freeProP p X) (k + 1))) ≤
        W.comap ((gradedBracketLinear p (freeProP p X) (k + 1) 0).flip
          (degreeOneDeriv p X x₀ ρ)) := by
      rw [span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply, gradedBracketLinear_apply]
      -- With `a = ∂_{x₀} ρ`: `[π^{k+1} x, a] = ([π^{k+1} x, a] + [π^{k+1} a, x]) - [π^{k+1} a, x]`.
      have hmap₂ : Submodule.map₂ (gradedBracketLinear p (freeProP p X) (k + 1) 0)
          (gradedBracketSpan p (freeProP p X) k) ⊤ ≤ W :=
        Submodule.map₂_le.mpr fun c hc' z _ ↦ by
          rw [gradedBracketLinear_apply]
          exact hbracket c hc' z
      have h := sub_mem (hmap₂ (gradedBracket_gradedPowIter_add_swap_mem_map₂ k x
        (degreeOneDeriv p X x₀ ρ))) (hpivot x)
      rwa [add_sub_cancel_right] at h
    have h := hle ht
    rwa [Submodule.mem_comap, LinearMap.flip_apply, gradedBracketLinear_apply] at h
  -- Every `δ_ρ(ω)` lies in `W`: split off the pivot component.
  suffices hW : LinearMap.range (basisModificationDelta p X (Nat.le_add_left 1 k) ρ) ≤ W by
    obtain ⟨ω, hω, rfl⟩ := Submodule.mem_map.mp (hW hy)
    exact ⟨ω, by simpa only [LinearMap.proj_apply] using Submodule.mem_comap.mp hω, rfl⟩
  rintro _ ⟨ω, rfl⟩
  have hsplit : basisModificationDelta p X (Nat.le_add_left 1 k) ρ ω =
      basisModificationDelta p X (Nat.le_add_left 1 k) ρ (ω - Pi.single x₀ (ω x₀)) +
        basisModificationDelta p X (Nat.le_add_left 1 k) ρ (Pi.single x₀ (ω x₀)) := by
    rw [← map_add, sub_add_cancel]
  rw [hsplit, basisModificationDelta_single]
  simp only [hc, zero_smul, zero_add]
  refine add_mem (hmemW _ ?_) (hderiv (ω x₀))
  rw [Pi.sub_apply, Pi.single_eq_same, sub_self]
  exact zero_mem _

/-- **The pivot-constrained span statement.** Let `ρ ∈ gr_1(F)` have no `p`-power part and partial
derivatives spanning `gr_0(F)`, and let `m ≥ 1`. Every element of the image of
`δ_ρ : gr_m(F)^X → gr_{m+1}(F)` is `δ_ρ(⟦ω⟧)` for a family `ω : X → λ_m(F)` whose component at the
prescribed generator `x₀` lies in the commutator subgroup of `F`. For a relator whose exponent
vector is supported at `x₀`, the basis modification `x_i ↦ x_i ω_i` therefore preserves the exponent
vector while moving the relator by the class `δ_ρ(⟦ω⟧)`. -/
theorem exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) (x₀ : X)
    {y : gradedPiece p (freeProP p X) (m + 1)}
    (hy : y ∈ LinearMap.range (basisModificationDelta p X hm ρ)) :
    ∃ ω : X → pLowerCentralSeries p (freeProP p X) m,
      (ω x₀ : freeProP p X) ∈ commutator (freeProP p X) ∧
        basisModificationDelta p X hm ρ (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = y := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨ω, hω, rfl⟩ := exists_apply_mem_gradedBracketSpan_basisModificationDelta_eq hρ hc x₀ hy
  obtain ⟨z, hz, hzω⟩ := exists_mem_commutator_gradedMk_eq_of_mem_gradedBracketSpan hω
  choose w hw using gradedMk_surjective (p := p) (G := freeProP p X) (k + 1)
  refine ⟨fun i ↦ if i = x₀ then z else w (ω i), by simpa only [ite_true] using hz, ?_⟩
  congr 1
  funext i
  dsimp only
  split_ifs with h
  · rw [h, hzω]
  · exact hw _

end TauCeti.freeProP
