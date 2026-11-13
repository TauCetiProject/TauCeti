/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateIntertwining.Basic
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential

/-!
# Elliott's approximate intertwining from approximate unitary equivalence

Given sequential inductive systems of separable unital C⋆-algebras `A₀ →[α₀] A₁ →[α₁] ⋯` and
`B₀ →[β₀] B₁ →[β₁] ⋯` together with (possibly nonunital) stage maps `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)`
and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` whose triangles `(ψ₀ (n + 1)).comp (φ₀ n)` and `(φ₀ n).comp (ψ₀ n)`
are approximately unitarily equivalent to `α n` and `β n`, a recursive zig-zag of inner
automorphisms replaces `φ₀ n` and `ψ₀ n` by unitarily conjugate maps `φ n` and `ψ n` that form an
honest norm-approximate intertwining (`IsApproximateIntertwining`) on propagating finite subsets
with geometric tolerances `(1 / 2) ^ n`. Because postcomposition with any (even nonunital)
`⋆`-homomorphism `ρ` between unital C⋆-algebras preserves approximate unitary equivalence via the
corner unitization `ρ u + (1 - ρ 1)`, neither the connecting maps `α n`, `β n` nor the stage maps
`φ₀ n`, `ψ₀ n` need be unital.

Passing to sequential colimit cones into unital C⋆-algebras `C` and `D` and using closure of
approximate unitary equivalence under point-norm limits (`of_tendsto_left`) yields a
`⋆`-isomorphism `θ : C ≃⋆ₐ[ℂ] D` whose stage restrictions are approximately unitarily equivalent
to `(ιB (n + 1)).comp (φ₀ n)` in the forward direction and `(ιA n).comp (ψ₀ n)` in the backward
direction (`elliott_intertwining_of_isSeqColimitCone`). Specializing to constant systems recovers
Elliott's two-algebra intertwining theorem (`elliott_intertwining`).

## Main results

* `TauCeti.IsApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent`: recursive
  zig-zag unitary conjugation turning an approximately unitarily commuting diagram of separable
  unital C⋆-systems into an `IsApproximateIntertwining` on finite sets with geometric tolerances
  `(1 / 2) ^ n`.
* `TauCeti.elliott_intertwining_of_isSeqColimitCone`: sequential colimit `⋆`-isomorphism
  `C ≃⋆ₐ[ℂ] D` preserving stagewise approximate unitary equivalence in both directions.
* `TauCeti.elliott_intertwining`: if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` between separable
  unital C⋆-algebras satisfy `ψ ∘ φ ≈_u id_A` and `φ ∘ ψ ≈_u id_B`, then there exists
  `θ : A ≃⋆ₐ[ℂ] B` with `θ ≈_u φ`.

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  443 (1993), Theorem 2.2.
* E. Kirchberg and N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra O₂*,
  J. Reine Angew. Math. 525 (2000), Lemma 0.6.
* M. Rørdam, *Classification of Nuclear C⋆-Algebras*, Encyclopaedia of Mathematical Sciences 126,
  Springer (2002), §2.3, Theorem 2.3.3 and Corollary 2.3.4.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section ZigZag

private noncomputable abbrev conjHom {X Y : Type*} [NonUnitalCStarAlgebra X] [CStarAlgebra Y]
    (w : unitary Y) (f : X →⋆ₙₐ[ℂ] Y) : X →⋆ₙₐ[ℂ] Y :=
  (Unitary.conjStarAlgAut ℂ Y w).toNonUnitalStarAlgHom.comp f

open Classical in
/-- Finite seed at stage `m` collecting one pushed dense-sequence term from each earlier stage
`i ≤ m`, ensuring asymptotic stagewise density along the connecting maps. -/
private noncomputable def denseSeed {X : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (X n)]
    [∀ n, TopologicalSpace.SeparableSpace (X n)]
    (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1)) (m : ℕ) : Finset (X m) :=
  (Finset.Iic m).attach.image fun i ↦
    seqTransHom γ (Finset.mem_Iic.mp i.2) (TopologicalSpace.denseSeq (X i.1) (m - i.1))

private theorem exists_approx_of_denseSeed_subset {X : ℕ → Type*}
    [∀ n, NonUnitalCStarAlgebra (X n)] [∀ n, TopologicalSpace.SeparableSpace (X n)]
    (γ : ∀ n, X n →⋆ₙₐ[ℂ] X (n + 1)) {H : ∀ n, Finset (X n)}
    (hseed : ∀ m, denseSeed γ m ⊆ H m) (n : ℕ) (x : X n) (r : ℝ) (hr : 0 < r) :
    ∃ k, ∃ y ∈ (H (n + k) : Set (X (n + k))),
      ‖seqTransHom γ (Nat.le_add_right n k) x - y‖ < r := by
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq (X n)) x r hr
  refine ⟨k, seqTransHom γ (Nat.le_add_right n k) (TopologicalSpace.denseSeq (X n) k), ?_, ?_⟩
  · apply hseed (n + k)
    classical
    refine Finset.mem_image.mpr ⟨⟨n, Finset.mem_Iic.mpr (Nat.le_add_right n k)⟩,
      Finset.mem_attach _ _, ?_⟩
    simp only [Nat.add_sub_cancel_left]
  · rw [← map_sub]
    refine (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt ?_
    simpa only [dist_eq_norm] using hk

private structure ZigZagStage {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
    (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n) (n : ℕ) where
  u : unitary (A n)
  v : unitary (B (n + 1))
  F : Finset (A n)
  G : Finset (B n)
  norm_φ_ψ_sub_le : ∀ b ∈ G,
    ‖conjHom v (φ₀ n) (conjHom u (ψ₀ n) b) - β n b‖ ≤ (1 / 2 : ℝ) ^ n

section ZigZagRec

variable {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
  [∀ n, TopologicalSpace.SeparableSpace (A n)] [∀ n, TopologicalSpace.SeparableSpace (B n)]
  {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
  {φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)} {ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n}

open Classical in
private noncomputable def zigZagZero
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ZigZagStage β φ₀ ψ₀ 0 :=
  let G₀ : Finset (B 0) := denseSeed β 0
  let u₀ : unitary (A 0) := 1
  let F₀ : Finset (A 0) := G₀.image (conjHom u₀ (ψ₀ 0)) ∪ denseSeed α 0
  let hB₀ : ApproximatelyUnitarilyEquivalent ((φ₀ 0).comp (conjHom u₀ (ψ₀ 0))) (β 0) :=
    ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp u₀ (ψ₀ 0)).postcomp_nonUnital
      (φ₀ 0)).trans (hφψ 0)
  let hex := (approximatelyUnitarilyEquivalent_def _ _).mp hB₀ G₀ ((1 / 2 : ℝ) ^ 0) (by positivity)
  { u := u₀
    v := hex.choose
    F := F₀
    G := G₀
    norm_φ_ψ_sub_le := fun b hb ↦ by
      have hb' := (hex.choose_spec b hb).le
      simpa only [conjHom, NonUnitalStarAlgHom.comp_apply,
        StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
        Unitary.coe_star] using hb' }

open Classical in
private noncomputable def zigZagSucc
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) : ZigZagStage β φ₀ ψ₀ (n + 1) :=
  let G' : Finset (B (n + 1)) :=
    s.G.image (β n) ∪ s.F.image (conjHom s.v (φ₀ n)) ∪ denseSeed β (n + 1)
  let hA : ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (conjHom s.v (φ₀ n))) (α n) :=
    ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp s.v (φ₀ n)).postcomp_nonUnital
      (ψ₀ (n + 1))).trans (hψφ n)
  let hexA := (approximatelyUnitarilyEquivalent_def _ _).mp hA s.F ((1 / 2 : ℝ) ^ n) (by positivity)
  let u' : unitary (A (n + 1)) := hexA.choose
  let F' : Finset (A (n + 1)) :=
    s.F.image (α n) ∪ G'.image (conjHom u' (ψ₀ (n + 1))) ∪ denseSeed α (n + 1)
  let hB : ApproximatelyUnitarilyEquivalent
      ((φ₀ (n + 1)).comp (conjHom u' (ψ₀ (n + 1)))) (β (n + 1)) :=
    ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp u' (ψ₀ (n + 1))).postcomp_nonUnital
      (φ₀ (n + 1))).trans (hφψ (n + 1))
  let hexB := (approximatelyUnitarilyEquivalent_def _ _).mp hB G'
    ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)
  { u := u'
    v := hexB.choose
    F := F'
    G := G'
    norm_φ_ψ_sub_le := fun b hb ↦ by
      have hb' := (hexB.choose_spec b hb).le
      simpa only [conjHom, NonUnitalStarAlgHom.comp_apply,
        StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
        Unitary.coe_star] using hb' }

private noncomputable def zigZag
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∀ n, ZigZagStage β φ₀ ψ₀ n
  | 0 => zigZagZero α β φ₀ ψ₀ hφψ
  | n + 1 => zigZagSucc α β φ₀ ψ₀ hψφ hφψ n (zigZag α β φ₀ ψ₀ hψφ hφψ n)

/-- Given sequential systems `(A, α)` and `(B, β)` of separable unital C⋆-algebras and stage maps
`φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` whose triangles commute up to
approximate unitary equivalence, a recursive zig-zag of target unitaries `u n : unitary (A n)` and
`v n : unitary (B (n + 1))` conjugates `φ₀` and `ψ₀` into an `IsApproximateIntertwining` on finite
subsets `F n` and `G n` with geometric tolerances `(1 / 2) ^ n` (Rørdam, Theorem 2.3.3). -/
theorem IsApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∃ (u : ∀ n, unitary (A n)) (v : ∀ n, unitary (B (n + 1)))
      (F : ∀ n, Finset (A n)) (G : ∀ n, Finset (B n)),
      IsApproximateIntertwining α β
        (fun n ↦ (Unitary.conjStarAlgAut ℂ (B (n + 1)) (v n)).toNonUnitalStarAlgHom.comp (φ₀ n))
        (fun n ↦ (Unitary.conjStarAlgAut ℂ (A n) (u n)).toNonUnitalStarAlgHom.comp (ψ₀ n))
        (fun n ↦ (F n : Set (A n))) (fun n ↦ (G n : Set (B n)))
        (fun n ↦ (1 / 2 : ℝ) ^ n) (fun n ↦ (1 / 2 : ℝ) ^ n) := by
  classical
  let z := zigZag α β φ₀ ψ₀ hψφ hφψ
  have hseedA (m : ℕ) : denseSeed α m ⊆ (z m).F := by
    cases m <;> exact Finset.subset_union_right
  have hseedB (m : ℕ) : denseSeed β m ⊆ (z m).G := by
    cases m with
    | zero => exact Finset.Subset.refl _
    | succ m => exact Finset.subset_union_right
  refine ⟨fun n ↦ (z n).u, fun n ↦ (z n).v, fun n ↦ (z n).F, fun n ↦ (z n).G, ?_⟩
  refine
    { mapsTo_α := fun n a ha ↦ Finset.mem_coe.mpr <|
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
      mapsTo_β := fun n b hb ↦ Finset.mem_coe.mpr <|
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
      mapsTo_φ := fun n a ha ↦ Finset.mem_coe.mpr <|
        Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
      mapsTo_ψ := fun m b hb ↦ by
        cases m with
        | zero =>
          exact Finset.mem_coe.mpr <| Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
        | succ m =>
          exact Finset.mem_coe.mpr <|
            Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
      approx_A := exists_approx_of_denseSeed_subset α hseedA
      approx_B := exists_approx_of_denseSeed_subset β hseedB
      norm_ψ_φ_sub_le := fun n a ha ↦ by
        let s := z n
        let hA : ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (conjHom s.v (φ₀ n))) (α n) :=
          ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp s.v (φ₀ n)).postcomp_nonUnital
            (ψ₀ (n + 1))).trans (hψφ n)
        have hexA := (approximatelyUnitarilyEquivalent_def _ _).mp hA s.F
          ((1 / 2 : ℝ) ^ n) (by positivity)
        have ha' := (hexA.choose_spec a ha).le
        simpa only [z, zigZag, zigZagSucc, s, conjHom, NonUnitalStarAlgHom.comp_apply,
          StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
          Unitary.coe_star] using ha'
      norm_φ_ψ_sub_le := fun n b hb ↦ (z n).norm_φ_ψ_sub_le b hb
      summable_δ := summable_geometric_two
      summable_ε := summable_geometric_two }

end ZigZagRec

end ZigZag

section ColimitIntertwining

/-- Elliott's approximate-intertwining theorem for sequential colimit cones of separable unital
C⋆-algebras into unital C⋆-algebras `C` and `D` (Rørdam, Theorem 2.3.3 and Corollary 2.3.4): if
stage maps `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` satisfy
`(ψ₀ (n + 1)).comp (φ₀ n) ≈_u α n` and `(φ₀ n).comp (ψ₀ n) ≈_u β n`, then there exists a
`⋆`-isomorphism `θ : C ≃⋆ₐ[ℂ] D` whose stage restrictions are approximately unitarily equivalent
to `(ιB (n + 1)).comp (φ₀ n)` and `(ιA n).comp (ψ₀ n)` for every `n`. -/
theorem elliott_intertwining_of_isSeqColimitCone
    {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
    [∀ n, TopologicalSpace.SeparableSpace (A n)] [∀ n, TopologicalSpace.SeparableSpace (B n)]
    {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
    {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
    {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB)
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∃ θ : C ≃⋆ₐ[ℂ] D,
      (∀ n, ApproximatelyUnitarilyEquivalent
        (θ.toNonUnitalStarAlgHom.comp (ιA n)) ((ιB (n + 1)).comp (φ₀ n))) ∧
      (∀ n, ApproximatelyUnitarilyEquivalent
        (θ.symm.toNonUnitalStarAlgHom.comp (ιB n)) ((ιA n).comp (ψ₀ n))) := by
  obtain ⟨u, v, F, G, hinter⟩ :=
    IsApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent φ₀ ψ₀ hψφ hφψ
  let θ := hinter.equiv hιA hιB
  have hstep_φ (m : ℕ) : ApproximatelyUnitarilyEquivalent
      (((ιB (m + 2)).comp (φ₀ (m + 1))).comp (α m)) ((ιB (m + 1)).comp (φ₀ m)) := by
    have h₁ := (hψφ m).symm.postcomp_nonUnital (φ₀ (m + 1))
    have h₂ := (hφψ (m + 1)).precomp (φ₀ m)
    rw [NonUnitalStarAlgHom.comp_assoc] at h₂
    have h₃ := (h₁.trans h₂).postcomp_nonUnital (ιB (m + 2))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
      hιB.comp_eq (m + 1)] at h₃
  have hstep_ψ (m : ℕ) : ApproximatelyUnitarilyEquivalent
      (((ιA (m + 1)).comp (ψ₀ (m + 1))).comp (β m)) ((ιA m).comp (ψ₀ m)) := by
    have h₁ := (hφψ m).symm.postcomp_nonUnital (ψ₀ (m + 1))
    have h₂ := (hψφ m).precomp (ψ₀ m)
    rw [NonUnitalStarAlgHom.comp_assoc] at h₂
    have h₃ := (h₁.trans h₂).postcomp_nonUnital (ιA (m + 1))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
      hιA.comp_eq m] at h₃
  refine ⟨θ, fun n ↦ ?_, fun n ↦ ?_⟩
  · have hiter (k : ℕ) : ApproximatelyUnitarilyEquivalent
        (((ιB (n + k + 1)).comp (φ₀ (n + k))).comp (seqTransHom α (Nat.le_add_right n k)))
        ((ιB (n + 1)).comp (φ₀ n)) := by
      induction k with
      | zero =>
        rw [seqTransHom_self, NonUnitalStarAlgHom.comp_id]
        exact .refl _
      | succ k ih =>
        rw [seqTransHom_succ α (Nat.le_add_right n k), ← NonUnitalStarAlgHom.comp_assoc]
        exact ((hstep_φ (n + k)).precomp _).trans ih
    refine ApproximatelyUnitarilyEquivalent.of_tendsto_left
      (Φ := fun k ↦ ((ιB (n + k + 1)).comp
        ((Unitary.conjStarAlgAut ℂ (B (n + k + 1)) (v (n + k))).toNonUnitalStarAlgHom.comp
          (φ₀ (n + k)))).comp (seqTransHom α (Nat.le_add_right n k)))
      (Eventually.of_forall fun k ↦ ?_) (fun a ↦ hinter.tendsto_equiv hιA hιB n a)
    exact (((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp (v (n + k))
      (φ₀ (n + k))).postcomp_nonUnital (ιB (n + k + 1))).precomp
      (seqTransHom α (Nat.le_add_right n k))).trans (hiter k)
  · have hiter (k : ℕ) : ApproximatelyUnitarilyEquivalent
        (((ιA (n + k)).comp (ψ₀ (n + k))).comp (seqTransHom β (Nat.le_add_right n k)))
        ((ιA n).comp (ψ₀ n)) := by
      induction k with
      | zero =>
        rw [seqTransHom_self, NonUnitalStarAlgHom.comp_id]
        exact .refl _
      | succ k ih =>
        rw [seqTransHom_succ β (Nat.le_add_right n k), ← NonUnitalStarAlgHom.comp_assoc]
        exact ((hstep_ψ (n + k)).precomp _).trans ih
    refine ApproximatelyUnitarilyEquivalent.of_tendsto_left
      (Φ := fun k ↦ ((ιA (n + k)).comp
        ((Unitary.conjStarAlgAut ℂ (A (n + k)) (u (n + k))).toNonUnitalStarAlgHom.comp
          (ψ₀ (n + k)))).comp (seqTransHom β (Nat.le_add_right n k)))
      (Eventually.of_forall fun k ↦ ?_) (fun b ↦ hinter.tendsto_equiv_symm hιA hιB n b)
    exact (((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp (u (n + k))
      (ψ₀ (n + k))).postcomp_nonUnital (ιA (n + k))).precomp
      (seqTransHom β (Nat.le_add_right n k))).trans (hiter k)

/-- Elliott's approximate intertwining theorem (Rørdam, *Classification of Nuclear C⋆-Algebras*,
§2.3; Kirchberg–Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra O₂*, Lemma 0.6):
if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` are `⋆`-homomorphisms between separable unital
C⋆-algebras with `ψ ∘ φ` approximately unitarily equivalent to `id_A` and `φ ∘ ψ` approximately
unitarily equivalent to `id_B`, then there exists a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` approximately
unitarily equivalent to `φ` (and with `θ.symm` approximately unitarily equivalent to `ψ` via
`ApproximatelyUnitarilyEquivalent.symm_of_comp_id`). -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ := by
  obtain ⟨θ, hθ, _⟩ := elliott_intertwining_of_isSeqColimitCone
    (IsSeqColimitCone.const A) (IsSeqColimitCone.const B)
    (fun _ ↦ φ) (fun _ ↦ ψ) (fun _ ↦ hψφ) (fun _ ↦ hφψ)
  refine ⟨θ, ?_⟩
  simpa only [NonUnitalStarAlgHom.comp_id, NonUnitalStarAlgHom.id_comp] using hθ 0

end ColimitIntertwining

end TauCeti
