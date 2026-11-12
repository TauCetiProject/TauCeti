/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.LocallyClosed
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Interior

/-!
# Common stratifications of rational semilinear domains

A finite collection of rational semilinear sets admits one finite rational-normal
affine arrangement whose sign cells determine membership in every set. Its nonempty
sign cells partition the whole space into locally closed convex polyhedra. Each
original set is a union of these strata, including its lower-dimensional pieces.
The strata are relative interiors of closed rational-normal polyhedra. Finite
families of weighted indicator sums take fixed values on a common partition.

A rational semilinear set also decomposes into disjoint relative interiors of
finitely many closed rational-normal polyhedra contained in its closure. These
closed charts retain boundary limits of points in the original set.

This simultaneous construction is useful for endpoint domains of finitely many
affine histories: the set of admitted history labels is constant on each stratum.
It combines the individual arrangements supplied by
`IsRationalSemilinear.exists_eq_biUnion_signCell`, using their dependent disjoint
union as a common row index. Offsets remain arbitrary real numbers.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Stratification.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite J]
  {S : J → Set V}

/-- One finite rational-normal arrangement determines membership in all sets of a
finite semilinear family. In particular, membership is constant on each sign cell. -/
theorem IsRationalSemilinear.exists_common_signCell
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (ι : Type) (_ : Finite ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      (∀ a, Toric.IsRationalFunctional h (g a).toAffineMap.linear) ∧
        ∀ (σ : ι → SignType) (x y : V), x ∈ Convex.signCell g σ →
          y ∈ Convex.signCell g σ → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  classical
  choose κ hκ g hg t ht using fun j => (hS j).exists_eq_biUnion_signCell
  let rows := Σ j, κ j
  let G : rows → (V →ᴬ[ℝ] ℝ) := fun a => g a.1 a.2
  let : ∀ j, Finite (κ j) := hκ
  -- The theorem's small row universe is recovered even when the label universe is larger.
  let := Fintype.ofFinite rows
  let e := Fintype.equivFin rows
  refine ⟨Fin (Fintype.card rows), inferInstance, fun a => G (e.symm a),
    fun a => hg _ _, ?_⟩
  intro σ x y hx hy j
  have he (a : κ j) : SignType.sign (g j a x) = SignType.sign (g j a y) := by
    have hx' := Convex.mem_signCell.mp hx (e ⟨j, a⟩)
    have hy' := Convex.mem_signCell.mp hy (e ⟨j, a⟩)
    simpa only [Equiv.symm_apply_apply, G] using hx'.trans hy'.symm
  rw [← ht j]
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨τ, hτ, hz⟩
  · exact ⟨τ, hτ, Convex.mem_signCell.mpr
      (fun a => (he a).symm.trans (Convex.mem_signCell.mp hz a))⟩
  · exact ⟨τ, hτ, Convex.mem_signCell.mpr
      (fun a => (he a).trans (Convex.mem_signCell.mp hz a))⟩

/-- A finite semilinear family has a common partition into the disjoint relative
interiors of closed rational-normal polyhedra. The interiors are nonempty, cover
all points, and determine membership in every original domain. -/
theorem IsRationalSemilinear.exists_common_intrinsicInteriors
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → Set V),
      (∀ a, (C a).Nonempty ∧ IsRationalNormalPolyhedron h (C a) ∧
        (intrinsicInterior ℝ (C a)).Nonempty ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (C a))) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (C a))
        (intrinsicInterior ℝ (C b))) ∧ (⋃ a, intrinsicInterior ℝ (C a)) = Set.univ ∧
      ∀ a x, x ∈ intrinsicInterior ℝ (C a) → ∀ y,
        y ∈ intrinsicInterior ℝ (C a) → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  obtain ⟨ι, _, g, hg, hmem⟩ := IsRationalSemilinear.exists_common_signCell hS
  let κ := {σ : ι → SignType // (Convex.signCell g σ).Nonempty}
  refine ⟨κ, inferInstance, fun σ => closure (Convex.signCell g σ), ?_, ?_, ?_, ?_⟩
  · intro σ
    refine ⟨σ.property.mono subset_closure,
      (isLocallyClosedPolyhedron_signCell g hg σ).isRationalNormalPolyhedron_closure, ?_⟩
    rw [Convex.intrinsicInterior_closure_signCell]
    exact ⟨σ.property, isLocallyClosedPolyhedron_signCell g hg σ⟩
  · intro σ τ hστ
    simp only [Convex.intrinsicInterior_closure_signCell]
    exact Convex.signCell_disjoint (Subtype.coe_injective.ne hστ)
  · simp only [Convex.intrinsicInterior_closure_signCell]
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨⟨_, x, Convex.mem_signCell_sign g x⟩,
      Convex.mem_signCell_sign g x⟩
  · intro σ x hx y hy
    rw [Convex.intrinsicInterior_closure_signCell] at hx hy
    exact hmem σ x y hx hy

/-- A finite semilinear family has a common partition of the entire space into
nonempty locally closed rational-normal polyhedra, on which all memberships agree.
The strata include boundary pieces, and no closedness of the original sets is needed. -/
theorem IsRationalSemilinear.exists_common_partition
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → Set V),
      (∀ a, (C a).Nonempty ∧ IsLocallyClosedPolyhedron h (C a)) ∧
        (Pairwise fun a b => Disjoint (C a) (C b)) ∧ (⋃ a, C a) = Set.univ ∧
          ∀ a x, x ∈ C a → ∀ y, y ∈ C a → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  obtain ⟨κ, hκ, C, hC, hdisj, hcover, hmem⟩ :=
    IsRationalSemilinear.exists_common_intrinsicInteriors hS
  exact ⟨κ, hκ, fun a => intrinsicInterior ℝ (C a),
    fun a => ⟨(hC a).2.2.1, (hC a).2.2.2⟩, hdisj, hcover, hmem⟩

/-- A rational semilinear set is a finite disjoint union of relative interiors of
nonempty closed rational-normal polyhedra with locally closed polyhedral interiors.
Each closed chart lies in the closure of the original set, so it adds only limits
of valid points. -/
theorem IsRationalSemilinear.exists_disjoint_intrinsicInteriors
    {S : Set V} (hS : IsRationalSemilinear h S) :
    ∃ (κ : Type) (_ : Finite κ) (K : κ → Set V),
      (∀ a, (K a).Nonempty ∧ IsRationalNormalPolyhedron h (K a) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (K a)) ∧ K a ⊆ closure S) ∧
        (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (K a))
          (intrinsicInterior ℝ (K b))) ∧ ⋃ a, intrinsicInterior ℝ (K a) = S := by
  obtain ⟨ι, _, g, hg, s, hs⟩ := hS.exists_eq_biUnion_signCell
  let κ := {σ : ι → SignType // σ ∈ s ∧ (Convex.signCell g σ).Nonempty}
  refine ⟨κ, inferInstance, fun σ => closure (Convex.signCell g σ), ?_, ?_, ?_⟩
  · intro σ
    refine ⟨σ.property.2.mono subset_closure, ?_, ?_, ?_⟩
    · exact (isLocallyClosedPolyhedron_signCell g hg σ).isRationalNormalPolyhedron_closure
    · rw [Convex.intrinsicInterior_closure_signCell]
      exact isLocallyClosedPolyhedron_signCell g hg σ
    · apply closure_mono
      rw [← hs]
      exact Set.subset_iUnion₂_of_subset σ.val σ.property.1 Set.Subset.rfl
  · intro σ τ hστ
    simp only [Convex.intrinsicInterior_closure_signCell]
    exact Convex.signCell_disjoint (Subtype.coe_injective.ne hστ)
  · simp only [Convex.intrinsicInterior_closure_signCell]
    apply Set.Subset.antisymm
    · rw [← hs]
      exact Set.iUnion_subset fun σ =>
        Set.subset_iUnion₂_of_subset σ.val σ.property.1 Set.Subset.rfl
    · intro x hx
      obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp (hs ▸ hx)
      exact Set.mem_iUnion.mpr ⟨⟨σ, hσ, x, hxσ⟩, hxσ⟩

open Classical in
/-- Finitely many finite weighted semilinear sums share a partition into the
disjoint relative interiors of closed rational-normal polyhedra. Each weighted
indicator sum takes a single value on the relative
interior of every stratum, including boundary strata. The summand index types
may differ between the weighted sums. -/
theorem IsRationalSemilinear.exists_common_weighted_polyhedralPartition
    {K β : Type*} [Finite K] [AddCommMonoid β] (J : K → Type*) [∀ k, Fintype (J k)]
    (A : ∀ k, J k → Set V) (hA : ∀ k j, IsRationalSemilinear h (A k j))
    (L : ∀ k, J k → β) :
    ∃ (n : ℕ) (C : Fin n → Set V) (W : Fin n → K → β),
      (∀ a, (C a).Nonempty ∧ IsRationalNormalPolyhedron h (C a) ∧
        (intrinsicInterior ℝ (C a)).Nonempty) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (C a))
        (intrinsicInterior ℝ (C b))) ∧ (⋃ a, intrinsicInterior ℝ (C a)) = Set.univ ∧
      ∀ a k x, x ∈ intrinsicInterior ℝ (C a) →
        (∑ j, if x ∈ A k j then L k j else 0) = W a k := by
  classical
  obtain ⟨κ, _, C, hC, hdisj, hcover, hmem⟩ :=
    IsRationalSemilinear.exists_common_intrinsicInteriors
      (S := fun p : Σ k, J k => A p.1 p.2) (fun p => hA p.1 p.2)
  let x a := (hC a).2.2.1.choose
  have hx a : x a ∈ intrinsicInterior ℝ (C a) := (hC a).2.2.1.choose_spec
  let W a k := ∑ j, if x a ∈ A k j then L k j else 0
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨n, fun a => C (e.symm a), fun a => W (e.symm a),
    fun a => ⟨(hC _).1, (hC _).2.1, (hC _).2.2.1⟩, ?_, ?_, ?_⟩
  · intro a b hab
    exact hdisj (e.symm.injective.ne hab)
  · rw [← hcover]
    exact e.symm.surjective.iUnion_comp (fun a => intrinsicInterior ℝ (C a))
  · intro a k y hy
    apply Finset.sum_congr rfl
    intro j _
    simp only [hmem (e.symm a) y hy (x (e.symm a)) (hx _) ⟨k, j⟩]

open Classical in
/-- A finite semilinear weighted sum has a presentation by relative interiors of
nonempty closed rational-normal polyhedra with fixed weights in any additive
commutative monoid. Charts from different original domains may coincide. -/
theorem IsRationalSemilinear.exists_weighted_polyhedralCharts
    {J β : Type*} [Fintype J] [AddCommMonoid β] (A : J → Set V)
    (hA : ∀ j, IsRationalSemilinear h (A j)) (L : J → β) :
    ∃ (m : ℕ) (B : Fin m → Set V) (L' : Fin m → β),
      (∀ j, (B j).Nonempty ∧ IsRationalNormalPolyhedron h (B j)) ∧
        ∀ Q, (∑ j, if Q ∈ A j then L j else 0) =
          ∑ j, if Q ∈ intrinsicInterior ℝ (B j) then L' j else 0 := by
  classical
  obtain ⟨n, C, W, hC, hdisj, hcover, hval⟩ :=
    IsRationalSemilinear.exists_common_weighted_polyhedralPartition
      (fun _ : Unit => J) (fun _ => A) (fun _ => hA) (fun _ => L)
  refine ⟨n, C, fun j => W j (), fun j => ⟨(hC j).1, (hC j).2.1⟩, ?_⟩
  intro Q
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ Q)
  rw [Finset.sum_eq_single j, ite_eq_left hj]
  · exact hval j () Q hj
  · intro b _ hbj
    exact ite_eq_right (fun hb => Set.disjoint_left.mp (hdisj hbj) hb hj)
  · simp

end TauCeti
