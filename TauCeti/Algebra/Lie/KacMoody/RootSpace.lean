/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Algebra.Lie.KacMoody.Morphism
public import TauCeti.Algebra.Lie.Subalgebra.LieSpan
public import TauCeti.Algebra.Lie.Weights.Eigenvector
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice

/-!
# Root-space decomposition of Kac–Moody Lie algebras

Let `A` be a square matrix of integers and `R` a realization of `A` over a field `K` in an ambient
space `H`. For `α : Module.Dual K H`, the weight space `TauCeti.KacMoody.rootSpace R α` of
`TauCeti.KacMoody.PresentedLieAlgebra R` is the simultaneous `α(x)`-eigenspace of
`ad (cartanElement R x)` for `x ∈ H`. Following Kac (§1.3), `rootSpace R 0` is included among the
homogeneous pieces of the `H*`-grading, whereas `0` is not called a root.

Because `n⁺` and `n⁻` are spanned by right-normed brackets in the generators `eᵢ` and `fᵢ`, each of
which is a simultaneous eigenvector with weight in the positive root cone `Q₊` or `-Q₊`, the root
spaces are supremum-independent, exhaust `PresentedLieAlgebra R`, make it an internally `H*`-graded
Lie algebra (`GradedLieAlgebra (rootSpace R)`), and vanish outside `Q₊ ∪ (-Q₊)` over any field and
for any integral matrix `A`.

Over a field of characteristic zero, the simple roots are `ℕ`-linearly independent in `H*`, so `Q₊`
is pointed and every right-normed bracket has positive height. Applying
`TauCeti.iInf_eigenspace_eq_of_iSup_eq_top` identifies:

* `rootSpace R 0 = LinearMap.range (cartanElement R)`;
* `rootSpace R α` (for `0 ≠ α ∈ Q₊`) with the span of right-normed `e`-brackets of weight `α`, and
  similarly for `-α`;
* `(positiveSubalgebra R).toSubmodule` and `(negativeSubalgebra R).toSubmodule` with the direct sums
  of the nonzero root spaces in `Q₊` and `-Q₊`;
* `rootSpace R (R.root i) = K ∙ positiveGenerator R i` and `rootSpace R (m • R.root i) = ⊥` for
  `2 ≤ m`;
* finite-dimensionality of `rootSpace R α` for every `α ≠ 0` (without finiteness hypotheses on `I`
  or `H`), and for all `α` when `H` is finite-dimensional;
* for a generalized Cartan matrix `A`, `finrank K (rootSpace R (R.root i)) = 1`,
  `finrank K (rootSpace R (-R.root i)) = 1`, `finrank K (rootSpace R 0) = finrank K H`, and the Lie
  center of `PresentedLieAlgebra R` equals the image of `R.cartanCenter` (Kac, Proposition 1.6).

## Main definitions

* `TauCeti.KacMoody.rootSpace`: the simultaneous `ad H`-eigenspace of weight `α ∈ H*`.
* `TauCeti.KacMoody.rootSpaceChevalleyEquiv`: the linear equivalence
  `rootSpace R α ≃ₗ[K] rootSpace R (-α)` induced by `chevalleyInvolution R`.
* `TauCeti.KacMoody.instGradedLieAlgebraRootSpace`: the `H*`-graded Lie algebra structure on
  `PresentedLieAlgebra R`.

## Main results

* `TauCeti.KacMoody.iSupIndep_rootSpace`, `TauCeti.KacMoody.iSup_rootSpace_eq_top`,
  `TauCeti.KacMoody.isInternal_rootSpace`: internal direct-sum decomposition into root spaces.
* `TauCeti.KacMoody.mem_posRootCone_or_neg_mem_posRootCone_of_rootSpace_ne_bot`: nonzero root
  spaces have weight in `Q₊ ∪ (-Q₊)`.
* `TauCeti.KacMoody.rootSpace_zero_eq_range_cartanElement`,
  `TauCeti.KacMoody.positiveSubalgebra_toSubmodule_eq_biSup_rootSpace`,
  `TauCeti.KacMoody.negativeSubalgebra_toSubmodule_eq_biSup_rootSpace`: identification of the zero
  piece and triangular subalgebras in characteristic zero.
* `TauCeti.KacMoody.rootSpace_root_eq_span`, `TauCeti.KacMoody.rootSpace_nsmul_root_eq_bot`,
  `TauCeti.KacMoody.finrank_rootSpace_root`, `TauCeti.KacMoody.finrank_rootSpace_zero`: simple root
  spaces, multiples of simple roots, and their dimensions.
* `TauCeti.KacMoody.finiteDimensional_rootSpace_of_ne_zero`,
  `TauCeti.KacMoody.finiteDimensional_rootSpace`,
  `TauCeti.KacMoody.finite_setOf_rootSpace_ne_bot_height_le`: finite-dimensionality of root spaces
  and finiteness of positive roots of bounded height.
* `TauCeti.KacMoody.center_eq_centralIdeal`, `TauCeti.KacMoody.finrank_center`,
  `TauCeti.KacMoody.finrank_center_add_rank_of_isMinimal`: the center of `PresentedLieAlgebra R`
  equals the image of `R.cartanCenter` and has dimension `|I| - rank A` for minimal realizations.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§1.2–1.3 and Proposition 1.6.
-/

public section

open LieAlgebra Module

namespace TauCeti.KacMoody

section Field

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- The simultaneous `α(x)`-eigenspace of `ad (cartanElement R x)` (`x ∈ H`) in
`PresentedLieAlgebra R`. For `α ≠ 0` this is the root space `𝔤_α`; for `α = 0` it is the zero
weight space (equal to the Cartan subalgebra in characteristic zero). -/
noncomputable def rootSpace (α : Module.Dual K H) : Submodule K (PresentedLieAlgebra R) :=
  ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x)

theorem rootSpace_def (α : Module.Dual K H) :
    rootSpace R α = ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x) :=
  (rfl)

@[simp]
theorem mem_rootSpace_iff {α : Module.Dual K H} {z : PresentedLieAlgebra R} :
    z ∈ rootSpace R α ↔ ∀ x : H, ⁅cartanElement R x, z⁆ = α x • z := by
  simp [rootSpace, Submodule.mem_iInf]

/-- The Lie bracket carries `rootSpace R α` and `rootSpace R β` into `rootSpace R (α + β)`. -/
theorem lie_mem_rootSpace {α β : Module.Dual K H} {y z : PresentedLieAlgebra R}
    (hy : y ∈ rootSpace R α) (hz : z ∈ rootSpace R β) :
    ⁅y, z⁆ ∈ rootSpace R (α + β) :=
  lie_mem_iInf_eigenspace_ad hy hz

instance instGradedBracketRootSpace : SetLike.GradedBracket (rootSpace R) (rootSpace R) where
  bracket_mem _ _ _ _ hy hz := by rw [vadd_eq_add]; exact lie_mem_rootSpace R hy hz

theorem cartanElement_mem_rootSpace_zero (x : H) : cartanElement R x ∈ rootSpace R 0 := by
  simp

theorem range_cartanElement_le_rootSpace_zero :
    LinearMap.range (cartanElement R) ≤ rootSpace R 0 := by
  rintro _ ⟨x, rfl⟩
  exact cartanElement_mem_rootSpace_zero R x

theorem positiveGenerator_mem_rootSpace (i : I) :
    positiveGenerator R i ∈ rootSpace R (R.root i) := by
  simp

theorem negativeGenerator_mem_rootSpace (i : I) :
    negativeGenerator R i ∈ rootSpace R (-R.root i) := by
  simp [neg_smul]

/-- The Chevalley involution carries `rootSpace R α` into `rootSpace R (-α)`. -/
theorem chevalleyInvolution_mem_rootSpace {α : Module.Dual K H} {z : PresentedLieAlgebra R}
    (hz : z ∈ rootSpace R α) :
    chevalleyInvolution R z ∈ rootSpace R (-α) := by
  rw [mem_rootSpace_iff] at hz ⊢
  intro x
  calc
    ⁅cartanElement R x, chevalleyInvolution R z⁆
      = ⁅-(chevalleyInvolution R (cartanElement R x)), chevalleyInvolution R z⁆ := by
        rw [chevalleyInvolution_cartanElement, neg_neg]
    _ = -chevalleyInvolution R ⁅cartanElement R x, z⁆ := by rw [neg_lie, LieEquiv.map_lie]
    _ = (-α) x • chevalleyInvolution R z := by rw [hz x, map_smul, LinearMap.neg_apply, neg_smul]

/-- The linear isomorphism `rootSpace R α ≃ₗ[K] rootSpace R (-α)` induced by the Chevalley
involution. -/
noncomputable def rootSpaceChevalleyEquiv (α : Module.Dual K H) :
    rootSpace R α ≃ₗ[K] rootSpace R (-α) :=
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict (rootSpace R (-α))
      ((chevalleyInvolution R).toLinearEquiv.toLinearMap.comp (rootSpace R α).subtype)
      fun z => chevalleyInvolution_mem_rootSpace R z.2)
    (LinearMap.codRestrict (rootSpace R α)
      ((chevalleyInvolution R).toLinearEquiv.toLinearMap.comp (rootSpace R (-α)).subtype)
      fun z => by simpa using chevalleyInvolution_mem_rootSpace R z.2)
    (LinearMap.ext fun z => Subtype.ext (chevalleyInvolution_apply_apply R z.1))
    (LinearMap.ext fun z => Subtype.ext (chevalleyInvolution_apply_apply R z.1))

@[simp]
theorem coe_rootSpaceChevalleyEquiv_apply (α : Module.Dual K H) (z : rootSpace R α) :
    (rootSpaceChevalleyEquiv R α z : PresentedLieAlgebra R) = chevalleyInvolution R z.1 :=
  (rfl)

@[simp]
theorem map_rootSpace_chevalleyInvolution (α : Module.Dual K H) :
    (rootSpace R α).map (chevalleyInvolution R).toLinearEquiv.toLinearMap = rootSpace R (-α) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact chevalleyInvolution_mem_rootSpace R hz
  · intro z hz
    exact ⟨chevalleyInvolution R z, by simpa using chevalleyInvolution_mem_rootSpace R hz,
      chevalleyInvolution_apply_apply R z⟩

@[simp]
theorem rootSpace_neg_eq_bot_iff (α : Module.Dual K H) :
    rootSpace R (-α) = ⊥ ↔ rootSpace R α = ⊥ := by
  have aux : ∀ β : Module.Dual K H, rootSpace R β = ⊥ → rootSpace R (-β) = ⊥ := fun β hβ => by
    rw [← map_rootSpace_chevalleyInvolution, hβ, Submodule.map_bot]
  exact ⟨fun h => by simpa using aux (-α) h, aux α⟩

@[simp]
theorem finrank_rootSpace_neg (α : Module.Dual K H) :
    Module.finrank K (rootSpace R (-α)) = Module.finrank K (rootSpace R α) :=
  (rootSpaceChevalleyEquiv R α).symm.finrank_eq

/-! ### Right-normed brackets and root-space grading -/

private def wordRoot (i : I) (w : List I) : Module.Dual K H :=
  (w.map R.root).sum + R.root i

private theorem wordRoot_nil (i : I) : wordRoot R i [] = R.root i := by
  simp [wordRoot]

private theorem wordRoot_cons (i j : I) (w : List I) :
    wordRoot R i (j :: w) = R.root j + wordRoot R i w := by
  simp [wordRoot, add_assoc]

private theorem wordRoot_mem_posRootCone (i : I) (w : List I) :
    wordRoot R i w ∈ R.posRootCone := by
  induction w with
  | nil => rw [wordRoot_nil]; exact R.root_mem_posRootCone i
  | cons j w ih => rw [wordRoot_cons]; exact add_mem (R.root_mem_posRootCone j) ih

/-- Every right-normed bracket in the raising generators `eᵢ` is a weight vector of weight
`(w.map R.root).sum + R.root i`. -/
theorem rightNormedBracket_positiveGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (positiveGenerator R) i w ∈
      rootSpace R ((w.map R.root).sum + R.root i) := by
  change _ ∈ rootSpace R (wordRoot R i w)
  induction w with
  | nil => rw [rightNormedBracket_nil, wordRoot_nil]; exact positiveGenerator_mem_rootSpace R i
  | cons j w ih =>
    rw [rightNormedBracket_cons, wordRoot_cons]
    exact lie_mem_rootSpace R (positiveGenerator_mem_rootSpace R j) ih

/-- Every right-normed bracket in the lowering generators `fᵢ` is a weight vector of weight
`-((w.map R.root).sum + R.root i)`. -/
theorem rightNormedBracket_negativeGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (negativeGenerator R) i w ∈
      rootSpace R (-((w.map R.root).sum + R.root i)) := by
  change _ ∈ rootSpace R (-wordRoot R i w)
  induction w with
  | nil => rw [rightNormedBracket_nil, wordRoot_nil]; exact negativeGenerator_mem_rootSpace R i
  | cons j w ih =>
    rw [rightNormedBracket_cons, wordRoot_cons, neg_add]
    exact lie_mem_rootSpace R (negativeGenerator_mem_rootSpace R j) ih

theorem positiveSubalgebra_le_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule ≤ ⨆ α ∈ R.posRootCone, rootSpace R α := by
  rw [positiveSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
    Submodule.span_le]
  rintro _ ⟨⟨i, w⟩, rfl⟩
  exact le_biSup (rootSpace R) (wordRoot_mem_posRootCone R i w)
    (rightNormedBracket_positiveGenerator_mem_rootSpace R i w)

theorem negativeSubalgebra_le_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule ≤ ⨆ α ∈ R.posRootCone, rootSpace R (-α) := by
  rw [negativeSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
    Submodule.span_le]
  rintro _ ⟨⟨i, w⟩, rfl⟩
  exact le_biSup (fun α => rootSpace R (-α)) (wordRoot_mem_posRootCone R i w)
    (rightNormedBracket_negativeGenerator_mem_rootSpace R i w)

/-- The root spaces of `PresentedLieAlgebra R` are supremum-independent. -/
theorem iSupIndep_rootSpace : iSupIndep (rootSpace R) :=
  (iSupIndep_iInf_eigenspace fun x => ad K (PresentedLieAlgebra R) (cartanElement R x)).comp
    DFunLike.coe_injective

/-- The root spaces span `PresentedLieAlgebra R`. -/
theorem iSup_rootSpace_eq_top : ⨆ α : Module.Dual K H, rootSpace R α = ⊤ := by
  rw [eq_top_iff, ← negativeSubalgebra_sup_range_cartanElement_sup_positiveSubalgebra R]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (negativeSubalgebra_le_biSup_rootSpace R).trans
      (iSup₂_le fun α _ => le_iSup (rootSpace R) (-α))
  · exact (range_cartanElement_le_rootSpace_zero R).trans (le_iSup (rootSpace R) 0)
  · exact (positiveSubalgebra_le_biSup_rootSpace R).trans
      (iSup₂_le fun α _ => le_iSup (rootSpace R) α)

/-- `PresentedLieAlgebra R` decomposes as the internal direct sum of its root spaces. -/
theorem isInternal_rootSpace [DecidableEq (Module.Dual K H)] :
    DirectSum.IsInternal (rootSpace R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_rootSpace R) (iSup_rootSpace_eq_top R)

noncomputable instance instDecompositionRootSpace [DecidableEq (Module.Dual K H)] :
    DirectSum.Decomposition (rootSpace R) :=
  (isInternal_rootSpace R).chooseDecomposition

noncomputable instance instGradedLieAlgebraRootSpace [DecidableEq (Module.Dual K H)] :
    GradedLieAlgebra (rootSpace R) := {}

/-- **Support of the root-space grading.** Every nonzero weight space of `PresentedLieAlgebra R`
has weight in `Q₊ ∪ (-Q₊)`, hence in the root lattice `Q`. -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_rootSpace_ne_bot {α : Module.Dual K H}
    (hα : rootSpace R α ≠ ⊥) :
    α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  by_contra! h
  rcases h with ⟨hpos, hneg⟩
  have hle : ⊤ ≤ ⨆ (β : Module.Dual K H) (_ : β ≠ α), rootSpace R β := by
    rw [← negativeSubalgebra_sup_range_cartanElement_sup_positiveSubalgebra R]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (negativeSubalgebra_le_biSup_rootSpace R).trans (iSup₂_le fun γ hγ => ?_)
      exact le_iSup₂_of_le (-γ) (fun heq => hneg (by simpa [← heq] using hγ)) le_rfl
    · refine (range_cartanElement_le_rootSpace_zero R).trans ?_
      exact le_iSup₂_of_le 0 (fun heq => hpos (heq ▸ zero_mem R.posRootCone)) le_rfl
    · refine (positiveSubalgebra_le_biSup_rootSpace R).trans (iSup₂_le fun γ hγ => ?_)
      exact le_iSup₂_of_le γ (fun heq => hpos (heq ▸ hγ)) le_rfl
  exact hα (disjoint_top.mp ((iSupIndep_rootSpace R α).mono_right hle))

theorem mem_rootLattice_of_rootSpace_ne_bot {α : Module.Dual K H} (hα : rootSpace R α ≠ ⊥) :
    α ∈ R.rootLattice := by
  rcases mem_posRootCone_or_neg_mem_posRootCone_of_rootSpace_ne_bot R hα with h | h
  · exact R.posRootCone_le_rootLattice h
  · exact neg_neg α ▸ neg_mem (R.posRootCone_le_rootLattice h)

private noncomputable def posWordSpan (α : Module.Dual K H) :
    Submodule K (PresentedLieAlgebra R) :=
  Submodule.span K {z | ∃ (i : I) (w : List I),
    wordRoot R i w = α ∧ rightNormedBracket (positiveGenerator R) i w = z}

private noncomputable def negWordSpan (α : Module.Dual K H) :
    Submodule K (PresentedLieAlgebra R) :=
  Submodule.span K {z | ∃ (i : I) (w : List I),
    wordRoot R i w = α ∧ rightNormedBracket (negativeGenerator R) i w = z}

private theorem posWordSpan_le_rootSpace (α : Module.Dual K H) :
    posWordSpan R α ≤ rootSpace R α := by
  rw [posWordSpan, Submodule.span_le]
  rintro _ ⟨i, w, rfl, rfl⟩
  exact rightNormedBracket_positiveGenerator_mem_rootSpace R i w

private theorem negWordSpan_le_rootSpace (α : Module.Dual K H) :
    negWordSpan R α ≤ rootSpace R (-α) := by
  rw [negWordSpan, Submodule.span_le]
  rintro _ ⟨i, w, rfl, rfl⟩
  exact rightNormedBracket_negativeGenerator_mem_rootSpace R i w

private theorem posWordSpan_le_positiveSubalgebra (α : Module.Dual K H) :
    posWordSpan R α ≤ (positiveSubalgebra R).toSubmodule := by
  rw [posWordSpan, positiveSubalgebra_def, Submodule.span_le]
  rintro _ ⟨i, w, -, rfl⟩
  exact LieSubalgebra.rightNormedBracket_mem_lieSpan (positiveGenerator R) i w

private theorem negWordSpan_le_negativeSubalgebra (α : Module.Dual K H) :
    negWordSpan R α ≤ (negativeSubalgebra R).toSubmodule := by
  rw [negWordSpan, negativeSubalgebra_def, Submodule.span_le]
  rintro _ ⟨i, w, -, rfl⟩
  exact LieSubalgebra.rightNormedBracket_mem_lieSpan (negativeGenerator R) i w

end Field

/-! ## Characteristic-zero structure and finite-dimensionality -/

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem height_wordRoot (i : I) (w : List I) :
    R.height ⟨wordRoot R i w, wordRoot_mem_posRootCone R i w⟩ = w.length + 1 := by
  induction w with
  | nil =>
    have h : (⟨wordRoot R i [], wordRoot_mem_posRootCone R i []⟩ : R.posRootCone) =
        ⟨R.root i, R.root_mem_posRootCone i⟩ := Subtype.ext (wordRoot_nil R i)
    rw [h, R.height_root]; rfl
  | cons j w ih =>
    have h : (⟨wordRoot R i (j :: w), wordRoot_mem_posRootCone R i (j :: w)⟩ : R.posRootCone) =
        ⟨R.root j, R.root_mem_posRootCone j⟩ +
          ⟨wordRoot R i w, wordRoot_mem_posRootCone R i w⟩ :=
      Subtype.ext (wordRoot_cons R i j w)
    rw [h, map_add, R.height_root, ih]
    simp [Nat.add_comm]

private theorem wordRoot_ne_zero (i : I) (w : List I) : wordRoot R i w ≠ 0 := by
  intro hzero
  have h := height_wordRoot R i w
  have h0 : (⟨wordRoot R i w, wordRoot_mem_posRootCone R i w⟩ : R.posRootCone) = 0 :=
    Subtype.ext hzero
  rw [h0, map_zero] at h
  exact Nat.succ_ne_zero w.length h.symm

private abbrev TriIndex : Type _ :=
  {α : R.posRootCone // α ≠ 0} ⊕ Unit ⊕ {α : R.posRootCone // α ≠ 0}

private noncomputable def triPiece : TriIndex R → Submodule K (PresentedLieAlgebra R)
  | .inl a => negWordSpan R a.1.1
  | .inr (.inl _) => LinearMap.range (cartanElement R)
  | .inr (.inr a) => posWordSpan R a.1.1

private def triWeight : TriIndex R → Module.Dual K H
  | .inl a => -a.1.1
  | .inr (.inl _) => 0
  | .inr (.inr a) => a.1.1

omit [CharZero K] in
private theorem triPiece_le_rootSpace (k : TriIndex R) :
    triPiece R k ≤ rootSpace R (triWeight R k) := by
  rcases k with a | (_ | a)
  · exact negWordSpan_le_rootSpace R a.1.1
  · exact range_cartanElement_le_rootSpace_zero R
  · exact posWordSpan_le_rootSpace R a.1.1

private theorem iSup_triPiece_eq_top : ⨆ k : TriIndex R, triPiece R k = ⊤ := by
  rw [eq_top_iff, ← negativeSubalgebra_sup_range_cartanElement_sup_positiveSubalgebra R]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [negativeSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
      Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl⟩
    let a : {α : R.posRootCone // α ≠ 0} := ⟨⟨wordRoot R i w, wordRoot_mem_posRootCone R i w⟩,
      Subtype.coe_ne_coe.mp (wordRoot_ne_zero R i w)⟩
    exact le_iSup (triPiece R) (.inl a) (Submodule.subset_span ⟨i, w, rfl, rfl⟩)
  · exact le_iSup (triPiece R) (.inr (.inl ()))
  · rw [positiveSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
      Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl⟩
    let a : {α : R.posRootCone // α ≠ 0} := ⟨⟨wordRoot R i w, wordRoot_mem_posRootCone R i w⟩,
      Subtype.coe_ne_coe.mp (wordRoot_ne_zero R i w)⟩
    exact le_iSup (triPiece R) (.inr (.inr a)) (Submodule.subset_span ⟨i, w, rfl, rfl⟩)

private theorem triWeight_injective :
    Function.Injective (fun k : TriIndex R => ⇑(triWeight R k)) := by
  refine DFunLike.coe_injective.comp ?_
  intro k₁ k₂ h
  have coe_ne : ∀ a : {α : R.posRootCone // α ≠ 0}, (a.1 : Module.Dual K H) ≠ 0 :=
    fun a h0 => a.2 (Subtype.ext h0)
  rcases k₁ with a₁ | (_ | a₁) <;> rcases k₂ with a₂ | (_ | a₂) <;>
    simp only [triWeight] at h
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (neg_inj.mp h)))
  · exact absurd (neg_eq_zero.mp h) (coe_ne a₁)
  · exfalso
    exact coe_ne a₂ (R.isPointed_posRootCone (a₂.1 : Module.Dual K H) a₂.1.2 (by simp [← h]))
  · exact absurd (neg_eq_zero.mp h.symm) (coe_ne a₂)
  · rfl
  · exact absurd h.symm (coe_ne a₂)
  · exfalso
    exact coe_ne a₁ (R.isPointed_posRootCone (a₁.1 : Module.Dual K H) a₁.1.2 (by simp [h]))
  · exact absurd h (coe_ne a₁)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (Subtype.ext h))

private theorem rootSpace_triWeight_eq (k : TriIndex R) :
    rootSpace R (triWeight R k) = triPiece R k :=
  iInf_eigenspace_eq_of_iSup_eq_top
    (fun x => ad K (PresentedLieAlgebra R) (cartanElement R x))
    (triPiece_le_rootSpace R) (iSup_triPiece_eq_top R) (triWeight_injective R) k

/-- Over a field of characteristic zero, the zero weight space of `PresentedLieAlgebra R` is the
image of `H` under `cartanElement R`. -/
@[simp]
theorem rootSpace_zero_eq_range_cartanElement :
    rootSpace R 0 = LinearMap.range (cartanElement R) :=
  rootSpace_triWeight_eq R (.inr (.inl ()))

/-- Over a field of characteristic zero, for every nonzero `α ∈ Q₊`, `rootSpace R α` is spanned by
the right-normed `e`-brackets of weight `α`. -/
theorem rootSpace_eq_span_rightNormedBracket_of_mem_posRootCone {α : Module.Dual K H}
    (hα : α ∈ R.posRootCone) (hne : α ≠ 0) :
    rootSpace R α = Submodule.span K {z | ∃ (i : I) (w : List I),
      (w.map R.root).sum + R.root i = α ∧ rightNormedBracket (positiveGenerator R) i w = z} :=
  rootSpace_triWeight_eq R (.inr (.inr ⟨⟨α, hα⟩, fun h => hne (congrArg Subtype.val h)⟩))

theorem rootSpace_neg_eq_span_rightNormedBracket_of_mem_posRootCone {α : Module.Dual K H}
    (hα : α ∈ R.posRootCone) (hne : α ≠ 0) :
    rootSpace R (-α) = Submodule.span K {z | ∃ (i : I) (w : List I),
      (w.map R.root).sum + R.root i = α ∧ rightNormedBracket (negativeGenerator R) i w = z} :=
  rootSpace_triWeight_eq R (.inl ⟨⟨α, hα⟩, fun h => hne (congrArg Subtype.val h)⟩)

/-- Over a field of characteristic zero, `positiveSubalgebra R` is the supremum of the nonzero
positive root spaces. -/
theorem positiveSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule =
      ⨆ (α ∈ R.posRootCone) (_ : α ≠ 0), rootSpace R α := by
  refine le_antisymm ?_ ?_
  · rw [positiveSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
      Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem (wordRoot R i w) <|
      Submodule.mem_iSup_of_mem (wordRoot_mem_posRootCone R i w) <|
        Submodule.mem_iSup_of_mem (wordRoot_ne_zero R i w)
          (rightNormedBracket_positiveGenerator_mem_rootSpace R i w)
  · refine iSup₂_le fun α hα => iSup_le fun hne => ?_
    rw [rootSpace_eq_span_rightNormedBracket_of_mem_posRootCone R hα hne]
    exact posWordSpan_le_positiveSubalgebra R α

/-- Over a field of characteristic zero, `negativeSubalgebra R` is the supremum of the nonzero
negative root spaces. -/
theorem negativeSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule =
      ⨆ (α ∈ R.posRootCone) (_ : α ≠ 0), rootSpace R (-α) := by
  refine le_antisymm ?_ ?_
  · rw [negativeSubalgebra_def, LieSubalgebra.coe_lieSpan_range_eq_span_rightNormedBracket,
      Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem (wordRoot R i w) <|
      Submodule.mem_iSup_of_mem (wordRoot_mem_posRootCone R i w) <|
        Submodule.mem_iSup_of_mem (wordRoot_ne_zero R i w)
          (rightNormedBracket_negativeGenerator_mem_rootSpace R i w)
  · refine iSup₂_le fun α hα => iSup_le fun hne => ?_
    rw [rootSpace_neg_eq_span_rightNormedBracket_of_mem_posRootCone R hα hne]
    exact negWordSpan_le_negativeSubalgebra R α

/-! ### Simple root spaces, multiples of simple roots, and finite-dimensionality -/

private noncomputable def wordConeElem (i : I) (w : List I) :
    Submodule.span ℕ (Set.range R.root) :=
  ⟨wordRoot R i w, R.posRootCone_def ▸ wordRoot_mem_posRootCone R i w⟩

private theorem repr_wordConeElem_nil (i : I) :
    R.linearIndependent_nat_root.repr (wordConeElem R i []) = Finsupp.single i 1 :=
  R.linearIndependent_nat_root.repr_eq_single i _ (wordRoot_nil R i)

private theorem repr_wordConeElem_cons (i j : I) (w : List I) :
    R.linearIndependent_nat_root.repr (wordConeElem R i (j :: w)) =
      Finsupp.single j 1 + R.linearIndependent_nat_root.repr (wordConeElem R i w) := by
  have h : wordConeElem R i (j :: w) =
      ⟨R.root j, Submodule.subset_span (Set.mem_range_self j)⟩ + wordConeElem R i w :=
    Subtype.ext (wordRoot_cons R i j w)
  rw [h, map_add, R.linearIndependent_nat_root.repr_eq_single j _ rfl]

private theorem mem_support_repr_wordConeElem {i : I} {w : List I} :
    ∀ {k : I}, k = i ∨ k ∈ w →
      k ∈ (R.linearIndependent_nat_root.repr (wordConeElem R i w)).support := by
  induction w with
  | nil =>
    rintro k (rfl | hk)
    · simp [repr_wordConeElem_nil]
    · simp at hk
  | cons j w ih =>
    intro k hk
    rw [Finsupp.mem_support_iff, repr_wordConeElem_cons, Finsupp.add_apply]
    rcases hk with rfl | hk
    · have := Finsupp.mem_support_iff.mp (ih (Or.inl rfl))
      omega
    · rcases List.mem_cons.mp hk with rfl | hkw
      · simp
      · have := Finsupp.mem_support_iff.mp (ih (Or.inr hkw))
        omega

/-- For each simple root `αᵢ`, `rootSpace R (R.root i)` is spanned by `eᵢ`. -/
@[simp]
theorem rootSpace_root_eq_span (i : I) :
    rootSpace R (R.root i) = K ∙ positiveGenerator R i := by
  have hne : R.root i ≠ 0 := R.root_linearIndependent.ne_zero i
  rw [rootSpace_eq_span_rightNormedBracket_of_mem_posRootCone R (R.root_mem_posRootCone i) hne]
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · rintro _ ⟨j, w, hjw, rfl⟩
    have hht : w.length + 1 = 1 := by
      rw [← height_wordRoot R j w]
      exact (congrArg R.height (Subtype.ext hjw)).trans (R.height_root i)
    have hw : w = [] := List.length_eq_zero_iff.mp (Nat.succ.inj hht)
    subst hw
    obtain rfl := R.root_linearIndependent.injective (by simpa using hjw)
    rw [rightNormedBracket_nil]
    exact Submodule.mem_span_singleton_self (positiveGenerator R j)
  · exact Submodule.subset_span ⟨i, [], by simp, rightNormedBracket_nil _ _⟩

/-- For each simple root `αᵢ`, `rootSpace R (-R.root i)` is spanned by `fᵢ`. -/
@[simp]
theorem rootSpace_neg_root_eq_span (i : I) :
    rootSpace R (-R.root i) = K ∙ negativeGenerator R i := by
  rw [← map_rootSpace_chevalleyInvolution, rootSpace_root_eq_span, Submodule.map_span,
    Set.image_singleton]
  change K ∙ chevalleyInvolution R (positiveGenerator R i) = _
  rw [chevalleyInvolution_positiveGenerator]
  refine le_antisymm (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  · exact neg_mem (Submodule.mem_span_singleton_self _)
  · simpa using neg_mem (Submodule.mem_span_singleton_self (-negativeGenerator R i))

/-- Multiples `m • αᵢ` (`2 ≤ m`) of a simple root have trivial root space. -/
theorem rootSpace_nsmul_root_eq_bot {m : ℕ} (hm : 2 ≤ m) (i : I) :
    rootSpace R (m • R.root i) = ⊥ := by
  have hm0 : m ≠ 0 := by omega
  have hmem : m • R.root i ∈ R.posRootCone := Submodule.smul_mem R.posRootCone m
    (R.root_mem_posRootCone i)
  have hht_m : R.height ⟨m • R.root i, hmem⟩ = m := by
    have h : (⟨m • R.root i, hmem⟩ : R.posRootCone) = m • ⟨R.root i, R.root_mem_posRootCone i⟩ :=
      rfl
    rw [h, map_nsmul, R.height_root, smul_eq_mul, mul_one]
  have hne : m • R.root i ≠ 0 := fun h0 => by
    have h : (⟨m • R.root i, hmem⟩ : R.posRootCone) = 0 := Subtype.ext h0
    rw [h, map_zero] at hht_m
    exact hm0 hht_m.symm
  rw [rootSpace_eq_span_rightNormedBracket_of_mem_posRootCone R hmem hne, Submodule.span_eq_bot]
  rintro _ ⟨j, w, hjw, rfl⟩
  have hlen : w.length + 1 = m :=
    (height_wordRoot R j w).symm.trans ((congrArg R.height (Subtype.ext hjw)).trans hht_m)
  have hw_ne : w ≠ [] := by
    rintro rfl
    simp at hlen
    omega
  have hrepr : R.linearIndependent_nat_root.repr (wordConeElem R j w) = m • Finsupp.single i 1 := by
    have hce : wordConeElem R j w =
        m • ⟨R.root i, Submodule.subset_span (Set.mem_range_self i)⟩ := Subtype.ext hjw
    rw [hce, map_nsmul, R.linearIndependent_nat_root.repr_eq_single i _ rfl]
  have heq_i : ∀ {k : I}, k = j ∨ k ∈ w → k = i := fun hk => by
    have hsupp := mem_support_repr_wordConeElem R hk
    rw [hrepr, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mem_support_iff] at hsupp
    by_contra hki
    exact hsupp (Finsupp.single_eq_of_ne' (Ne.symm hki))
  obtain rfl : j = i := heq_i (Or.inl rfl)
  exact rightNormedBracket_eq_zero_of_forall_mem_eq (positiveGenerator R) hw_ne
    fun k hk => heq_i (Or.inr hk)

theorem rootSpace_neg_nsmul_root_eq_bot {m : ℕ} (hm : 2 ≤ m) (i : I) :
    rootSpace R (-(m • R.root i)) = ⊥ :=
  (rootSpace_neg_eq_bot_iff R (m • R.root i)).mpr (rootSpace_nsmul_root_eq_bot R hm i)

private theorem finite_list_length_eq {s : Set I} (hs : s.Finite) :
    ∀ n : ℕ, {w : List I | w.length = n ∧ ∀ k ∈ w, k ∈ s}.Finite
  | 0 => (Set.finite_singleton []).subset fun _ ⟨hw, _⟩ => List.length_eq_zero_iff.mp hw
  | n + 1 =>
    ((hs.prod (finite_list_length_eq hs n)).image fun p : I × List I => p.1 :: p.2).subset <| by
      rintro (_ | ⟨j, w⟩) ⟨hlen, hmem⟩
      · simp at hlen
      · exact ⟨(j, w), ⟨hmem j List.mem_cons_self, Nat.succ.inj hlen,
          fun k hk => hmem k (List.mem_cons_of_mem j hk)⟩, rfl⟩

/-- **Finite-dimensionality of nonzero root spaces.** Over a field of characteristic zero, every
nonzero weight `α` has a finite-dimensional root space `rootSpace R α`, with no finiteness
assumptions on the index set `I` or the ambient space `H`. -/
theorem finiteDimensional_rootSpace_of_ne_zero {α : Module.Dual K H} (hα : α ≠ 0) :
    FiniteDimensional K (rootSpace R α) := by
  have hpos : ∀ {β : Module.Dual K H}, β ∈ R.posRootCone → β ≠ 0 →
      FiniteDimensional K (rootSpace R β) := by
    intro β hβ hβ0
    rw [rootSpace_eq_span_rightNormedBracket_of_mem_posRootCone R hβ hβ0]
    let c : Submodule.span ℕ (Set.range R.root) := ⟨β, R.posRootCone_def ▸ hβ⟩
    let s : Finset I := (R.linearIndependent_nat_root.repr c).support
    have hsub : {p : I × List I | (p.2.map R.root).sum + R.root p.1 = β} ⊆
        (s : Set I) ×ˢ {w : List I | w.length = R.height ⟨β, hβ⟩ - 1 ∧
          ∀ k ∈ w, k ∈ (s : Set I)} := by
      rintro ⟨i, w⟩ hiw
      have hce : wordConeElem R i w = c := Subtype.ext hiw
      have hht : w.length + 1 = R.height ⟨β, hβ⟩ :=
        (height_wordRoot R i w).symm.trans (congrArg R.height (Subtype.ext hiw))
      refine ⟨?_, ?_, fun k hk => ?_⟩
      · simpa [s, hce] using mem_support_repr_wordConeElem R (i := i) (w := w) (Or.inl rfl)
      · change w.length = R.height ⟨β, hβ⟩ - 1
        omega
      · simpa [s, hce] using mem_support_repr_wordConeElem R (i := i) (w := w) (Or.inr hk)
    have hfin_pairs : {p : I × List I | (p.2.map R.root).sum + R.root p.1 = β}.Finite :=
      (s.finite_toSet.prod
        (finite_list_length_eq s.finite_toSet (R.height ⟨β, hβ⟩ - 1))).subset hsub
    refine Module.Finite.span_of_finite K ?_
    refine (hfin_pairs.image fun p : I × List I =>
      rightNormedBracket (positiveGenerator R) p.1 p.2).subset ?_
    rintro _ ⟨i, w, hiw, rfl⟩
    exact ⟨(i, w), hiw, rfl⟩
  by_cases hbot : rootSpace R α = ⊥
  · rw [hbot]; infer_instance
  · rcases mem_posRootCone_or_neg_mem_posRootCone_of_rootSpace_ne_bot R hbot with h | h
    · exact hpos h hα
    · have := hpos h (neg_ne_zero.mpr hα)
      have hfd := (rootSpaceChevalleyEquiv R (-α)).finiteDimensional
      rwa [neg_neg] at hfd

/-- When `H` is finite-dimensional and `K` has characteristic zero, every weight space
`rootSpace R α` (including `α = 0`) is finite-dimensional. -/
instance finiteDimensional_rootSpace [FiniteDimensional K H] (α : Module.Dual K H) :
    FiniteDimensional K (rootSpace R α) := by
  by_cases hα : α = 0
  · subst hα
    rw [rootSpace_zero_eq_range_cartanElement]
    exact LinearMap.finiteDimensional_range (cartanElement R)
  · exact finiteDimensional_rootSpace_of_ne_zero R hα

/-- **Finiteness of bounded-height positive roots.** For a finite index set `I`, only finitely many
elements of `Q₊` of height at most `n` have a nonzero root space. -/
theorem finite_setOf_rootSpace_ne_bot_height_le [Finite I] (n : ℕ) :
    {α : R.posRootCone | rootSpace R α.1 ≠ ⊥ ∧ R.height α ≤ n}.Finite := by
  have hfin := R.linearIndependent_nat_root.finite_natSpanHeight_le n
  let emb : R.posRootCone → Submodule.span ℕ (Set.range R.root) :=
    fun α => ⟨α.1, R.posRootCone_def ▸ α.2⟩
  have hemb : Function.Injective emb := fun _ _ h =>
    Subtype.ext (show (emb _).1 = (emb _).1 from congrArg Subtype.val h)
  refine (hfin.preimage hemb.injOn).subset fun α ⟨_, hn⟩ => ?_
  change R.linearIndependent_nat_root.natSpanHeight (emb α) ≤ n
  rwa [← R.height_apply]

/-! ### Exact root-space dimensions for generalized Cartan matrices -/

/-- For a generalized Cartan matrix in characteristic zero, each simple root space is
one-dimensional. -/
theorem finrank_rootSpace_root (hA : A.IsGeneralizedCartan) (i : I) :
    Module.finrank K (rootSpace R (R.root i)) = 1 := by
  rw [rootSpace_root_eq_span, finrank_span_singleton (positiveGenerator_ne_zero R hA i)]

/-- For a generalized Cartan matrix in characteristic zero, each negative simple root space is
one-dimensional. -/
theorem finrank_rootSpace_neg_root (hA : A.IsGeneralizedCartan) (i : I) :
    Module.finrank K (rootSpace R (-R.root i)) = 1 :=
  (finrank_rootSpace_neg R (R.root i)).trans (finrank_rootSpace_root R hA i)

/-- For a generalized Cartan matrix in characteristic zero, `cartanElement R` induces a linear
isomorphism `H ≃ₗ[K] rootSpace R 0`. -/
noncomputable def cartanRootSpaceZeroEquiv (hA : A.IsGeneralizedCartan) :
    H ≃ₗ[K] rootSpace R 0 :=
  (LinearEquiv.ofInjective (cartanElement R) (cartanElement_injective R hA)).trans
    (LinearEquiv.ofEq _ _ (rootSpace_zero_eq_range_cartanElement R).symm)

/-- For a generalized Cartan matrix in characteristic zero, the zero weight space has dimension
equal to `finrank K H`. -/
theorem finrank_rootSpace_zero (hA : A.IsGeneralizedCartan) :
    Module.finrank K (rootSpace R 0) = Module.finrank K H :=
  (cartanRootSpaceZeroEquiv R hA).symm.finrank_eq

/-- **Kac, Proposition 1.6.** Over a field of characteristic zero, for a generalized Cartan
matrix `A`, the Lie center of `PresentedLieAlgebra R` equals
`centralIdeal R R.cartanCenter le_rfl`, the image of `R.cartanCenter` under `cartanElement R`. -/
theorem center_eq_centralIdeal (hA : A.IsGeneralizedCartan) :
    LieAlgebra.center K (PresentedLieAlgebra R) = centralIdeal R R.cartanCenter le_rfl := by
  refine le_antisymm ?_ (centralIdeal_le_center R R.cartanCenter le_rfl)
  intro z hz
  have hz0 : z ∈ rootSpace R 0 := by
    rw [mem_rootSpace_iff]
    intro x
    have hx := hz
    rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule] at hx
    simp [hx (cartanElement R x)]
  rw [rootSpace_zero_eq_range_cartanElement] at hz0
  obtain ⟨x, rfl⟩ := hz0
  exact (mem_centralIdeal_iff R R.cartanCenter le_rfl).mpr
    ⟨x, (cartanElement_mem_center_iff R hA).mp hz, rfl⟩

/-- Over a field of characteristic zero, for a generalized Cartan matrix `A`, the dimension of
the center of `PresentedLieAlgebra R` equals `finrank K R.cartanCenter`. -/
theorem finrank_center (hA : A.IsGeneralizedCartan) :
    Module.finrank K (LieAlgebra.center K (PresentedLieAlgebra R)) =
      Module.finrank K R.cartanCenter :=
  (congrArg (fun I : LieIdeal K (PresentedLieAlgebra R) => Module.finrank K I)
    (center_eq_centralIdeal R hA)).trans
    (centralIdealLinearEquiv R hA R.cartanCenter le_rfl).symm.finrank_eq

/-- **Dimension of the center for a minimal realization (Kac, Proposition 1.6).** For a minimal
realization `R` of a finite-index generalized Cartan matrix `A` in characteristic zero,
`finrank K (center (PresentedLieAlgebra R)) + rank A = |I|`. -/
theorem finrank_center_add_rank_of_isMinimal [Fintype I] (hA : A.IsGeneralizedCartan)
    (hR : R.IsMinimal) :
    Module.finrank K (LieAlgebra.center K (PresentedLieAlgebra R)) +
      (A.map (Int.cast : ℤ → K)).rank = Fintype.card I := by
  rw [finrank_center R hA]
  have hle : R.cartanCenter ≤ R.corootSpan := R.isMinimal_iff_cartanCenter_le_corootSpan.mp hR
  have hinf : R.cartanCenter ⊓ R.corootSpan = R.cartanCenter := inf_eq_left.mpr hle
  have h := R.finrank_cartanCenter_inf_corootSpan_add_rank
  rwa [hinf] at h

end CharZero

/-! ### Example: a height-3 root in affine type `A₁⁽¹⁾` -/

section Example

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- For any rational realization `R` of the affine generalized Cartan matrix
`A₁⁽¹⁾ = !![2, -2; -2, 2]`, the bracket `⁅e₀, ⁅e₀, e₁⁆⁆` is nonzero, witnessing that
`2 • R.root 0 + R.root 1` (the real root `α₀ + δ` of height `3`) has a nontrivial root space.
Because `h₀ + h₁ = 0` in the evaluation representation `𝔰𝔩₂(ℚ)`, the proof factors through the
derived presentation `Matrix.ToLieAlgebra ℚ A` via `serreLift` and lifts to `PresentedLieAlgebra R`
via `serreHom_injective`. -/
example {H : Type*} [AddCommGroup H] [Module ℚ H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))
      H) :
    ⁅positiveGenerator R 0, ⁅positiveGenerator R 0, positiveGenerator R 1⁆⁆ ≠ 0 ∧
      rootSpace R (2 • R.root 0 + R.root 1) ≠ ⊥ := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; -2, 2]
  have hA : A.IsGeneralizedCartan := by decide
  let hMat : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![-1, 0; 0, 1], !![1, 0; 0, -1]]
  let eMat : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0, 0; 1, 0], !![0, 1; 0, 0]]
  let fMat : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0, 1; 0, 0], !![0, 0; 1, 0]]
  have hs : IsSerreSystem ℚ A hMat eMat fMat := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
        simp [hMat, LieRing.of_associative_ring_bracket]
    · intro i; fin_cases i <;> ext r s <;> fin_cases r <;> fin_cases s <;>
        simp [hMat, eMat, fMat, LieRing.of_associative_ring_bracket]
    · intro i j hij; fin_cases i <;> fin_cases j <;>
        (try exact absurd rfl hij) <;> ext r s <;> fin_cases r <;> fin_cases s <;>
        simp [eMat, fMat]
    · intro i j; fin_cases i <;> fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
        simp [A, hMat, eMat, LieRing.of_associative_ring_bracket] <;> norm_num
    · intro i j; fin_cases i <;> fin_cases j <;> ext r s <;> fin_cases r <;> fin_cases s <;>
        simp [A, hMat, fMat, LieRing.of_associative_ring_bracket] <;> norm_num
    · intro i j; fin_cases i <;> fin_cases j
      · simp
      · change (ad ℚ _ (eMat 0) ^ 2) ⁅eMat 0, eMat 1⁆ = 0
        rw [sq, mul_apply_eq_comp, ad_apply, ad_apply]
        ext r s; fin_cases r <;> fin_cases s <;>
          simp [eMat, LieRing.of_associative_ring_bracket]
      · change (ad ℚ _ (eMat 1) ^ 2) ⁅eMat 1, eMat 0⁆ = 0
        rw [sq, mul_apply_eq_comp, ad_apply, ad_apply]
        ext r s; fin_cases r <;> fin_cases s <;>
          simp [eMat, LieRing.of_associative_ring_bracket]
      · simp
    · intro i j; fin_cases i <;> fin_cases j
      · simp
      · change (ad ℚ _ (fMat 0) ^ 2) ⁅fMat 0, fMat 1⁆ = 0
        rw [sq, mul_apply_eq_comp, ad_apply, ad_apply]
        ext r s; fin_cases r <;> fin_cases s <;>
          simp [fMat, LieRing.of_associative_ring_bracket]
      · change (ad ℚ _ (fMat 1) ^ 2) ⁅fMat 1, fMat 0⁆ = 0
        rw [sq, mul_apply_eq_comp, ad_apply, ad_apply]
        ext r s; fin_cases r <;> fin_cases s <;>
          simp [fMat, LieRing.of_associative_ring_bracket]
      · simp
  have hmat_ne : ⁅eMat 0, ⁅eMat 0, eMat 1⁆⁆ ≠ 0 := by
    intro h0
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 1 0) h0
    simp [eMat, LieRing.of_associative_ring_bracket] at h10
    norm_num at h10
  have hserre_ne : ⁅serreE ℚ A 0, ⁅serreE ℚ A 0, serreE ℚ A 1⁆⁆ ≠ 0 := fun h0 =>
    hmat_ne <| by simpa using congrArg (serreLift hs) h0
  have he_ne : ⁅positiveGenerator R 0, ⁅positiveGenerator R 0, positiveGenerator R 1⁆⁆ ≠ 0 := by
    intro h0
    apply hserre_ne
    apply serreHom_injective R hA
    simpa [A] using h0
  refine ⟨he_ne, (Submodule.ne_bot_iff _).mpr ⟨_, ?_, he_ne⟩⟩
  have hmem := rightNormedBracket_positiveGenerator_mem_rootSpace R 1 [0, 0]
  simpa [two_smul, add_assoc] using hmem

end Example

end TauCeti.KacMoody
