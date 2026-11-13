/-
Copyright (c) 2026 Mei contributors and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Total-degree grading of the symmetric algebra of a graded module

A decomposition of a module indexed by an additive commutative monoid induces a grading
of its symmetric algebra. The degree of a product is the sum of the original degrees of
its factors, not its word length. The homogeneous pieces are the spans of such products.
No basis, flatness, or positivity assumption is needed.

This grading is used to compare homogeneous components under PBW symmetrization. The
construction follows Mathlib's `TensorAlgebra.gradedAlgebra`: lift the homogeneous
generators into the external direct sum, using the symmetric algebra's universal property,
and show that the resulting map is inverse to recomposition.

The word-span construction and decomposition proof are adapted from
`TauCeti.Algebra.Lie.UniversalEnveloping.Grading`, itself adapted from
`Mei/Algebra/Lie/UniversalEnveloping/Grading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

open scoped DirectSum

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

variable {Γ R M : Type*} [AddCommMonoid Γ] [CommSemiring R]
  [AddCommMonoid M] [Module R M] (ℳ : Γ → Submodule R M)

/-- Products of homogeneous generators with total degree `n`, and their linear span. -/
def totalDegreeSubmodule (n : Γ) : Submodule R (SymmetricAlgebra R M) :=
  Submodule.span R {a | ∃ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n ∧
    (l.map (fun x => ι R M (x.2 : M))).prod = a}

/-- The word-span description of a total-degree homogeneous piece. -/
theorem totalDegreeSubmodule_def (n : Γ) :
    totalDegreeSubmodule ℳ n =
      Submodule.span R {a | ∃ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n ∧
        (l.map (fun x => ι R M (x.2 : M))).prod = a} := (rfl)

/-- A homogeneous piece is contained in a submodule precisely when all its generating
words are contained in that submodule. -/
theorem totalDegreeSubmodule_le_iff (n : Γ) (p : Submodule R (SymmetricAlgebra R M)) :
    totalDegreeSubmodule ℳ n ≤ p ↔
      ∀ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n →
        (l.map (fun x => ι R M (x.2 : M))).prod ∈ p := by
  rw [totalDegreeSubmodule_def, Submodule.span_le]
  constructor
  · intro h l hl
    exact h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- A product of homogeneous generators has the sum of their degrees. -/
theorem prod_mem_totalDegreeSubmodule (l : List (Σ i, ℳ i)) :
    (l.map (fun x => ι R M (x.2 : M))).prod ∈
      totalDegreeSubmodule ℳ (l.map Sigma.fst).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- A generator retains its original degree in the symmetric algebra. -/
theorem ι_mem_totalDegreeSubmodule {n : Γ} {x : M} (hx : x ∈ ℳ n) :
    ι R M x ∈ totalDegreeSubmodule ℳ n := by
  simpa using prod_mem_totalDegreeSubmodule ℳ [⟨n, x, hx⟩]

/-- Multiplication adds the total degrees of homogeneous words. -/
instance totalDegreeSubmodule_gradedMonoid : SetLike.GradedMonoid (totalDegreeSubmodule ℳ) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro m n a b ha hb
    have hmul : totalDegreeSubmodule ℳ m * totalDegreeSubmodule ℳ n ≤
        totalDegreeSubmodule ℳ (m + n) := by
      rw [totalDegreeSubmodule_def, totalDegreeSubmodule_def, Submodule.span_mul_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      simpa [hl, ht] using prod_mem_totalDegreeSubmodule ℳ (l ++ t)
    exact hmul (Submodule.mul_mem_mul ha hb)

/-- A generator belongs to a total-degree piece exactly when it has that degree in the
original module, even when the pieces do not form a decomposition. -/
@[simp]
theorem ι_mem_totalDegreeSubmodule_iff {n : Γ} {x : M} :
    ι R M x ∈ totalDegreeSubmodule ℳ n ↔ x ∈ ℳ n := by
  -- As in SymmetricAlgebra.ι_injective, use the same scalar action on both sides.
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  let f := lift (TrivSqZeroExt.inrHom R M)
  let g := (TrivSqZeroExt.sndHom R M).comp f.toLinearMap
  -- The square-zero projection retains singleton words and kills all other lengths.
  have hle : totalDegreeSubmodule ℳ n ≤ (ℳ n).comap g := by
    rw [totalDegreeSubmodule_le_iff]
    intro l hl
    cases l with
    | nil => simp [g, f]
    | cons a l =>
      cases l with
      | nil =>
        have ha : a.1 = n := by simpa using hl
        simp [g, f, ← ha]
      | cons b l =>
        simp [g, f, map_list_prod, List.map_map, ← mul_assoc,
          TrivSqZeroExt.inr_mul_inr]
  constructor
  · intro hx
    simpa [g, f] using hle hx
  · exact ι_mem_totalDegreeSubmodule ℳ

/-- The lift of a linear map preserving generator degrees preserves total degrees. -/
theorem totalDegreeSubmodule_le_comap_lift {Γ' A : Type*} [AddCommMonoid Γ']
    [CommSemiring A] [Algebra R A] (𝒜 : Γ' → Submodule R A)
    [SetLike.GradedMonoid 𝒜] (T : Γ →+ Γ') (f : M →ₗ[R] A)
    (hf : ∀ i, ∀ x ∈ ℳ i, f x ∈ 𝒜 (T i)) (n : Γ) :
    totalDegreeSubmodule ℳ n ≤ (𝒜 (T n)).comap (lift f).toLinearMap := by
  rw [totalDegreeSubmodule_le_iff]
  intro l hl
  have h := SetLike.list_prod_map_mem_graded (A := 𝒜) l (fun x => T x.1)
    (fun x => f (x.2 : M)) (fun x _ => hf x.1 x.2 x.2.property)
  have hsum : (l.map (fun x => T x.1)).sum = T n := by
    simpa only [map_list_sum, List.map_map, Function.comp_def] using congrArg T hl
  simpa [map_list_prod, List.map_map, Function.comp_def, hsum] using h

variable [DecidableEq Γ] [DirectSum.Decomposition ℳ]

private noncomputable def totalDegreeι : M →ₗ[R] ⨁ n, totalDegreeSubmodule ℳ n :=
  (DirectSum.lmap fun n =>
    (((ι R M).comp (ℳ n).subtype).codRestrict _
      fun x => ι_mem_totalDegreeSubmodule ℳ x.property)).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem totalDegreeι_apply {n : Γ} (x : ℳ n) :
    totalDegreeι ℳ x = DirectSum.of (fun n => ↥(totalDegreeSubmodule ℳ n)) n
      ⟨ι R M (x : M), ι_mem_totalDegreeSubmodule ℳ x.property⟩ := by
  simp only [totalDegreeι, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe, DirectSum.lmap_of]
  -- The codomain restriction has the same underlying value as the displayed subtype.
  rfl

-- This bundled map has a symmetric-algebra receiver, so its name belongs in the type namespace.
private noncomputable def _root_.SymmetricAlgebra.totalDegreeDecompose :
    SymmetricAlgebra R M →ₐ[R] ⨁ n, totalDegreeSubmodule ℳ n :=
  lift (totalDegreeι ℳ)

private theorem totalDegreeDecompose_ι {n : Γ} (x : ℳ n) :
    totalDegreeDecompose ℳ (ι R M (x : M)) =
      DirectSum.of (fun n => ↥(totalDegreeSubmodule ℳ n)) n
        ⟨ι R M (x : M), ι_mem_totalDegreeSubmodule ℳ x.property⟩ := by
  rw [totalDegreeDecompose, lift_ι_apply, totalDegreeι_apply]

private theorem coeAlgHom_comp_totalDegreeDecompose :
    (DirectSum.coeAlgHom (totalDegreeSubmodule ℳ)).comp (totalDegreeDecompose ℳ) =
      AlgHom.id R (SymmetricAlgebra R M) := by
  apply _root_.SymmetricAlgebra.algHom_ext
  ext x
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | homogeneous x =>
    simp [totalDegreeDecompose_ι]

private theorem totalDegreeDecompose_prod (l : List (Σ i, ℳ i)) :
    totalDegreeDecompose ℳ (l.map (fun x => ι R M (x.2 : M))).prod =
      DirectSum.of (fun n => ↥(totalDegreeSubmodule ℳ n)) (l.map Sigma.fst).sum
        ⟨(l.map (fun x => ι R M (x.2 : M))).prod, prod_mem_totalDegreeSubmodule ℳ l⟩ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, DirectSum.one_def]
    -- The graded unit is the subtype whose underlying algebra element is one.
    rfl
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, totalDegreeDecompose_ι, ih,
      DirectSum.of_mul_of]
    -- Graded multiplication is algebra multiplication bundled with its membership proof.
    congr 1

private theorem totalDegreeDecompose_apply (n : Γ) (x : totalDegreeSubmodule ℳ n) :
    totalDegreeDecompose ℳ (x : SymmetricAlgebra R M) =
      DirectSum.of (fun n => ↥(totalDegreeSubmodule ℳ n)) n x := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    subst n
    exact totalDegreeDecompose_prod ℳ l
  | zero =>
    rw [map_zero]
    exact (map_zero (DirectSum.of (fun n => ↥(totalDegreeSubmodule ℳ n)) n)).symm
  | add x y hx hy hxi hyi =>
    rw [map_add, hxi, hyi, ← map_add]
    -- Addition in a submodule is addition of the underlying algebra elements.
    rfl
  | smul r x hx hxi =>
    rw [map_smul, hxi, ← DirectSum.of_smul]
    -- Scalar multiplication in a submodule is inherited from the ambient module.
    rfl

/-- The total-degree pieces decompose the symmetric algebra as an internal direct sum. -/
theorem isInternal_totalDegreeSubmodule : DirectSum.IsInternal (totalDegreeSubmodule ℳ) := by
  let := GradedAlgebra.ofAlgHom _ (totalDegreeDecompose ℳ)
    (coeAlgHom_comp_totalDegreeDecompose ℳ) (totalDegreeDecompose_apply ℳ)
  exact DirectSum.Decomposition.isInternal _

/-- A graded module induces the total-degree grading of its symmetric algebra. -/
noncomputable instance totalDegreeGradedAlgebra : GradedAlgebra (totalDegreeSubmodule ℳ) :=
  (isInternal_totalDegreeSubmodule ℳ).gradedAlgebra

/-- Taking the homogeneous component of a generator is the same as first taking its
component in the original module. -/
@[simp]
theorem coe_decompose_totalDegreeSubmodule_ι (x : M) (n : Γ) :
    (DirectSum.decompose (totalDegreeSubmodule ℳ) (ι R M x) n : SymmetricAlgebra R M) =
      ι R M (DirectSum.decompose ℳ x n : M) :=
  (DirectSum.map_decompose_shift ℳ (totalDegreeSubmodule ℳ) (ι R M).toAddMonoidHom
    (fun i => i) Function.injective_id
    (fun _ _ hx => ι_mem_totalDegreeSubmodule ℳ hx) n x).symm

end TauCeti.SymmetricAlgebra
