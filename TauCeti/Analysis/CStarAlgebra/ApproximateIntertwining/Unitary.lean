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
`B₀ →[β₀] B₁ →[β₁] ⋯` together with (possibly non-unital) stage maps `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)`
and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` whose triangles `(ψ₀ (n + 1)).comp (φ₀ n)` and `(φ₀ n).comp (ψ₀ n)`
are approximately unitarily equivalent to `α n` and `β n`, a recursive zig-zag of inner
automorphisms replaces `φ₀ n` and `ψ₀ n` by unitarily conjugate maps `φ n` and `ψ n` that form an
honest norm-approximate intertwining (`IsApproximateIntertwining`) on propagating finite subsets
with geometric tolerances `(1 / 2) ^ n`. Because postcomposition with any (even non-unital)
`⋆`-homomorphism `ρ` between unital C⋆-algebras preserves approximate unitary equivalence via the
corner unitization `ρ u + (1 - ρ 1)`, neither the connecting maps `α n`, `β n` nor the stage maps
`φ₀ n`, `ψ₀ n` need be unital.

Passing to sequential colimit cocones into unital C⋆-algebras `C` and `D` and using closure of
approximate unitary equivalence under point-norm limits
(`IsApproximateCocone.approximatelyUnitarilyEquivalent_hom_comp`) yields a `⋆`-isomorphism
`θ : C ≃⋆ₐ[ℂ] D` whose stage restrictions are approximately unitarily equivalent to
`(ιB (n + 1)).comp (φ₀ n)` in the forward direction and `(ιA n).comp (ψ₀ n)` in the backward
direction (`elliott_intertwining_of_isSeqColimitCocone`), generalizing the two-algebra theorem
`TauCeti.elliott_intertwining` to sequential colimit cocones without unitality assumptions on the
connecting or stage maps.

## Main results

* `TauCeti.IsApproximateCocone.approximatelyUnitarilyEquivalent_hom_comp`: when an approximate
  cocone `ξ` into a unital C⋆-algebra `D` commutes with `α` up to approximate unitary equivalence,
  its induced colimit homomorphism satisfies `(hc.hom hι).comp (ι n) ≈_u ξ n`.
* `TauCeti.IsApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent`: recursive
  zig-zag unitary conjugation turning an approximately unitarily commuting diagram of separable
  unital C⋆-systems into an `IsApproximateIntertwining` on finite sets with geometric tolerances
  `(1 / 2) ^ n`.
* `TauCeti.elliott_intertwining_of_isSeqColimitCocone`: sequential colimit `⋆`-isomorphism
  `C ≃⋆ₐ[ℂ] D` preserving stagewise approximate unitary equivalence in both directions.

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

/-- If an approximate cocone `ξ` from a sequential C⋆-system `(A, α)` into a unital C⋆-algebra `D`
commutes with each connecting map `α n` up to approximate unitary equivalence, then the induced
colimit `⋆`-homomorphism `hc.hom hι` restricts on stage `n` to a map approximately unitarily
equivalent to `ξ n`. Neither the stages `A n` nor the colimit `C` need be unital or separable. -/
theorem IsApproximateCocone.approximatelyUnitarilyEquivalent_hom_comp
    {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
    {C D : Type*} [NonUnitalCStarAlgebra C] [CStarAlgebra D]
    {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}
    {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D} {F : ∀ n, Set (A n)} {τ : ℕ → ℝ}
    (hc : IsApproximateCocone α ξ F τ) (hι : IsSeqColimitCocone α ι)
    (hstep : ∀ n, ApproximatelyUnitarilyEquivalent ((ξ (n + 1)).comp (α n)) (ξ n)) (n : ℕ) :
    ApproximatelyUnitarilyEquivalent ((hc.hom hι).comp (ι n)) (ξ n) := by
  have hiter (k : ℕ) : ApproximatelyUnitarilyEquivalent
      ((ξ (n + k)).comp (seqTransHom α (Nat.le_add_right n k))) (ξ n) := by
    induction k with
    | zero =>
      rw [seqTransHom_self, NonUnitalStarAlgHom.comp_id]
      exact .refl _
    | succ k ih =>
      rw [seqTransHom_succ α (Nat.le_add_right n k), ← NonUnitalStarAlgHom.comp_assoc]
      exact ((hstep (n + k)).precomp _).trans ih
  exact ApproximatelyUnitarilyEquivalent.of_tendsto_left
    (Φ := fun k ↦ (ξ (n + k)).comp (seqTransHom α (Nat.le_add_right n k)))
    (Eventually.of_forall hiter) (fun a ↦ hc.tendsto_hom hι n a)

section ZigZag

private noncomputable abbrev conjHom {X Y : Type*} [NonUnitalCStarAlgebra X] [CStarAlgebra Y]
    (w : unitary Y) (f : X →⋆ₙₐ[ℂ] Y) : X →⋆ₙₐ[ℂ] Y :=
  (Unitary.conjStarAlgAut ℂ Y w).toNonUnitalStarAlgHom.comp f

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
  let hv := (hφψ 0).exists_norm_conjStarAlgAut_comp_sub_lt u₀ G₀ (ε := (1 / 2 : ℝ) ^ 0)
    (by positivity)
  { u := u₀
    v := hv.choose
    F := F₀
    G := G₀
    norm_φ_ψ_sub_le := fun b hb ↦ (hv.choose_spec b hb).le }

open Classical in
private theorem zigZagZero_G
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    (zigZagZero α β φ₀ ψ₀ hφψ).G = denseSeed β 0 :=
  rfl

open Classical in
private theorem zigZagZero_F
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    (zigZagZero α β φ₀ ψ₀ hφψ).F =
      (zigZagZero α β φ₀ ψ₀ hφψ).G.image
        (conjHom (zigZagZero α β φ₀ ψ₀ hφψ).u (ψ₀ 0)) ∪ denseSeed α 0 :=
  rfl

open Classical in
private noncomputable def zigZagSucc
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) : ZigZagStage β φ₀ ψ₀ (n + 1) :=
  let G' : Finset (B (n + 1)) :=
    s.G.image (β n) ∪ s.F.image (conjHom s.v (φ₀ n)) ∪ denseSeed β (n + 1)
  let hu := (hψφ n).exists_norm_conjStarAlgAut_comp_sub_lt s.v s.F (ε := (1 / 2 : ℝ) ^ n)
    (by positivity)
  let u' : unitary (A (n + 1)) := hu.choose
  let F' : Finset (A (n + 1)) :=
    s.F.image (α n) ∪ G'.image (conjHom u' (ψ₀ (n + 1))) ∪ denseSeed α (n + 1)
  let hv := (hφψ (n + 1)).exists_norm_conjStarAlgAut_comp_sub_lt u' G'
    (ε := (1 / 2 : ℝ) ^ (n + 1)) (by positivity)
  { u := u'
    v := hv.choose
    F := F'
    G := G'
    norm_φ_ψ_sub_le := fun b hb ↦ (hv.choose_spec b hb).le }

open Classical in
private theorem zigZagSucc_u
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) :
    (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).u =
      ((hψφ n).exists_norm_conjStarAlgAut_comp_sub_lt s.v s.F (ε := (1 / 2 : ℝ) ^ n)
        (by positivity)).choose :=
  rfl

open Classical in
private theorem zigZagSucc_G
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) :
    (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).G =
      s.G.image (β n) ∪ s.F.image (conjHom s.v (φ₀ n)) ∪ denseSeed β (n + 1) :=
  rfl

open Classical in
private theorem zigZagSucc_F
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) :
    (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).F =
      s.F.image (α n) ∪
        (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).G.image
          (conjHom (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).u (ψ₀ (n + 1))) ∪
        denseSeed α (n + 1) :=
  rfl

private theorem zigZagSucc_norm_ψ_φ_sub_le
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n))
    (n : ℕ) (s : ZigZagStage β φ₀ ψ₀ n) {a : A n} (ha : a ∈ s.F) :
    ‖conjHom (zigZagSucc α β φ₀ ψ₀ hψφ hφψ n s).u (ψ₀ (n + 1)) (conjHom s.v (φ₀ n) a) - α n a‖ ≤
      (1 / 2 : ℝ) ^ n := by
  rw [zigZagSucc_u]
  exact (((hψφ n).exists_norm_conjStarAlgAut_comp_sub_lt s.v s.F (ε := (1 / 2 : ℝ) ^ n)
    (by positivity)).choose_spec a ha).le

private noncomputable def zigZag
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∀ n, ZigZagStage β φ₀ ψ₀ n
  | 0 => zigZagZero α β φ₀ ψ₀ hφψ
  | n + 1 => zigZagSucc α β φ₀ ψ₀ hψφ hφψ n (zigZag α β φ₀ ψ₀ hψφ hφψ n)

private theorem zigZag_zero
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    zigZag α β φ₀ ψ₀ hψφ hφψ 0 = zigZagZero α β φ₀ ψ₀ hφψ :=
  rfl

private theorem zigZag_succ
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hψφ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hφψ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) (n : ℕ) :
    zigZag α β φ₀ ψ₀ hψφ hφψ (n + 1) =
      zigZagSucc α β φ₀ ψ₀ hψφ hφψ n (zigZag α β φ₀ ψ₀ hψφ hφψ n) :=
  rfl

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
  have hseedA (m : ℕ) : (denseSeed α m : Set (A m)) ⊆ (zigZag α β φ₀ ψ₀ hψφ hφψ m).F := by
    intro x hx
    cases m <;> simp [zigZag_zero, zigZag_succ, zigZagZero_F, zigZagSucc_F,
      Finset.mem_coe.mp hx]
  have hseedB (m : ℕ) : (denseSeed β m : Set (B m)) ⊆ (zigZag α β φ₀ ψ₀ hψφ hφψ m).G := by
    intro x hx
    cases m <;> simp [zigZag_zero, zigZag_succ, zigZagZero_G, zigZagSucc_G,
      Finset.mem_coe.mp hx]
  refine ⟨fun n ↦ (zigZag α β φ₀ ψ₀ hψφ hφψ n).u,
    fun n ↦ (zigZag α β φ₀ ψ₀ hψφ hφψ n).v,
    fun n ↦ (zigZag α β φ₀ ψ₀ hψφ hφψ n).F,
    fun n ↦ (zigZag α β φ₀ ψ₀ hψφ hφψ n).G, ?_⟩
  refine
    { mapsTo_α := fun n a ha ↦ by
        simp only [Finset.mem_coe, zigZag_succ, zigZagSucc_F, Finset.mem_union] at ha ⊢
        grind [Finset.mem_image_of_mem]
      mapsTo_β := fun n b hb ↦ by
        simp only [Finset.mem_coe, zigZag_succ, zigZagSucc_G, Finset.mem_union] at hb ⊢
        grind [Finset.mem_image_of_mem]
      mapsTo_φ := fun n a ha ↦ by
        simp only [Finset.mem_coe, zigZag_succ, zigZagSucc_G, Finset.mem_union] at ha ⊢
        grind [Finset.mem_image_of_mem]
      mapsTo_ψ := fun m b hb ↦ by
        cases m <;>
          simp only [Finset.mem_coe, zigZag_zero, zigZag_succ, zigZagZero_F, zigZagSucc_F,
            Finset.mem_union] at hb ⊢ <;>
          grind [Finset.mem_image_of_mem]
      approx_A := exists_approx_of_denseSeed_subset α hseedA
      approx_B := exists_approx_of_denseSeed_subset β hseedB
      norm_ψ_φ_sub_le := fun n a ha ↦ by
        dsimp only
        rw [zigZag_succ]
        exact zigZagSucc_norm_ψ_φ_sub_le α β φ₀ ψ₀ hψφ hφψ n _ (Finset.mem_coe.mp ha)
      norm_φ_ψ_sub_le := fun n b hb ↦ (zigZag α β φ₀ ψ₀ hψφ hφψ n).norm_φ_ψ_sub_le b hb
      summable_δ := summable_geometric_two
      summable_ε := summable_geometric_two }

end ZigZagRec

end ZigZag

section ColimitIntertwining

/-- Elliott's approximate-intertwining theorem for sequential colimit cocones of separable unital
C⋆-algebras into unital C⋆-algebras `C` and `D` (Rørdam, Theorem 2.3.3 and Corollary 2.3.4): if
stage maps `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` satisfy
`(ψ₀ (n + 1)).comp (φ₀ n) ≈_u α n` and `(φ₀ n).comp (ψ₀ n) ≈_u β n`, then there exists a
`⋆`-isomorphism `θ : C ≃⋆ₐ[ℂ] D` whose stage restrictions are approximately unitarily equivalent
to `(ιB (n + 1)).comp (φ₀ n)` and `(ιA n).comp (ψ₀ n)` for every `n`. -/
theorem elliott_intertwining_of_isSeqColimitCocone
    {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
    [∀ n, TopologicalSpace.SeparableSpace (A n)] [∀ n, TopologicalSpace.SeparableSpace (B n)]
    {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
    {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
    {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}
    (hιA : IsSeqColimitCocone α ιA) (hιB : IsSeqColimitCocone β ιB)
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
  have hconj (m : ℕ) : ApproximatelyUnitarilyEquivalent
      ((ιB (m + 1)).comp
        ((Unitary.conjStarAlgAut ℂ (B (m + 1)) (v m)).toNonUnitalStarAlgHom.comp (φ₀ m)))
      ((ιB (m + 1)).comp (φ₀ m)) :=
    (ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp (v m) (φ₀ m)).postcomp
      (ιB (m + 1))
  have hstep₀ (m : ℕ) : ApproximatelyUnitarilyEquivalent
      (((ιB (m + 2)).comp (φ₀ (m + 1))).comp (α m)) ((ιB (m + 1)).comp (φ₀ m)) := by
    have h₁ := (hψφ m).symm.postcomp (φ₀ (m + 1))
    have h₂ := (hφψ (m + 1)).precomp (φ₀ m)
    rw [NonUnitalStarAlgHom.comp_assoc] at h₂
    have h₃ := (h₁.trans h₂).postcomp (ιB (m + 2))
    rwa [← NonUnitalStarAlgHom.comp_assoc, ← NonUnitalStarAlgHom.comp_assoc,
      hιB.comp_eq (m + 1)] at h₃
  have hθ (n : ℕ) : ApproximatelyUnitarilyEquivalent
      (θ.toNonUnitalStarAlgHom.comp (ιA n)) ((ιB (n + 1)).comp (φ₀ n)) := by
    rw [hinter.toNonUnitalStarAlgHom_equiv]
    refine ((hinter.isApproximateCocone_forward hιB).approximatelyUnitarilyEquivalent_hom_comp
      hιA (fun m ↦ ?_) n).trans (hconj n)
    exact ((hconj (m + 1)).precomp (α m)).trans ((hstep₀ m).trans (hconj m).symm)
  refine ⟨θ, hθ, fun n ↦ θ.approximatelyUnitarilyEquivalent_symm_comp_iff.mpr ?_⟩
  rw [← NonUnitalStarAlgHom.comp_assoc, ← hιB.comp_eq n]
  exact ((hθ n).precomp (ψ₀ n)).trans ((hφψ n).postcomp (ιB (n + 1)))

end ColimitIntertwining

end TauCeti
