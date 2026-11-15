/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Graded
public import TauCeti.Algebra.Lie.KacMoody.CartanInjectivity
public import TauCeti.Algebra.Lie.Subalgebra.LieSpan
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Algebra.Lie.Weights.Eigenvector
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.LinearAlgebra.LinearIndependent.NonnegCombination

/-!
# Root-space grading and direct-sum triangular decomposition of Kac–Moody Lie algebras

Let `R : CartanRealization (A.map (Int.cast : ℤ → K)) H` be a realization of an integer matrix `A`
over a field `K`, and let `𝔤 = TauCeti.KacMoody.PresentedLieAlgebra R` be the Lie algebra it
presents. For every linear functional `α : Module.Dual K H`, the **root space**
`TauCeti.KacMoody.rootSpace R α` is the joint eigenspace
`{z ∈ 𝔤 | ∀ x : H, ⁅cartanElement R x, z⁆ = α x • z}` of the Cartan action.

Even when `A` is singular — for instance in affine type, where the null root `δ` vanishes on every
simple coroot — the simple roots `R.root i` are linearly independent in `Module.Dual K H`, so the
adjoint action of the full realization `H` separates all elements of the root lattice
`R.rootLattice`. Combining the spanning triangular decomposition `𝔤 = n⁻ + 𝔥 + n⁺` from
`TauCeti.Algebra.Lie.KacMoody.Triangular` with the pointedness of the positive root cone
`R.posRootCone` over a field of characteristic zero yields:

* **Direct-sum triangular decomposition** (`TauCeti.KacMoody.triangularEquiv`):
  `(negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R`.
* **Internal `Q`-grading** (`TauCeti.KacMoody.isInternal_rootSpace`,
  `TauCeti.KacMoody.isInternal_rootSpace_rootLattice`, and `GradedLieAlgebra` instances):
  `𝔤 = ⨁ α ∈ Q, 𝔤_α`, with `𝔤_0 = 𝔥`, `n⁺ = ⨁_{α ∈ Q₊ \ {0}} 𝔤_α`,
  `n⁻ = ⨁_{-α ∈ Q₊ \ {0}} 𝔤_α`, and `𝔤_α = ⊥` unless `α ∈ Q₊` or `-α ∈ Q₊`.
* **Bracket-word spanning and finite-dimensionality**: every nonzero root space is spanned by
  right-normed brackets of raising (or lowering) generators of fixed word length `ht(α) - 1`,
  hence is finite-dimensional when `I` is finite
  (`TauCeti.KacMoody.finiteDimensional_rootSpace_of_ne_zero`).
* **Simple root multiplicities and `2 αᵢ` vanishing**: `𝔤_{αᵢ} = K ∙ eᵢ` and `𝔤_{-αᵢ} = K ∙ fᵢ`
  (one-dimensional for a generalized Cartan matrix by `TauCeti.KacMoody.finrank_rootSpace_root`),
  while `𝔤_{m • αᵢ} = ⊥` and `𝔤_{-(m • αᵢ)} = ⊥` for `m ≥ 2`.
* **Center of a Kac–Moody Lie algebra** (`TauCeti.KacMoody.center_toSubmodule_eq_map_cartanCenter`
  and `TauCeti.KacMoody.cartanCenterEquiv`): for a generalized Cartan matrix in characteristic
  zero, `LieAlgebra.center K 𝔤` is the isomorphic image of
  `R.cartanCenter = {x ∈ H | ∀ i, αᵢ(x) = 0}` under `cartanElement R` (Kac, Proposition 1.6).

## Main definitions

* `TauCeti.KacMoody.rootSpace`: the joint eigenspace `𝔤_α` for `α : Module.Dual K H`.
* `TauCeti.KacMoody.triangularEquiv`: the linear equivalence
  `(negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R`.
* `TauCeti.KacMoody.cartanCenterEquiv`: the linear equivalence
  `R.cartanCenter ≃ₗ[K] LieAlgebra.center K (PresentedLieAlgebra R)` for a generalized Cartan
  matrix in characteristic zero.

## Main results

* `TauCeti.KacMoody.iSupIndep_rootSpace`, `TauCeti.KacMoody.lie_mem_rootSpace`,
  `TauCeti.KacMoody.map_rootSpace_chevalleyInvolution`.
* `TauCeti.KacMoody.isInternal_rootSpace`, `TauCeti.KacMoody.isInternal_rootSpace_rootLattice`,
  `TauCeti.KacMoody.rootSpace_eq_bot_of_notMem_posRootCone`,
  `TauCeti.KacMoody.rootSpace_zero_eq`,
  `TauCeti.KacMoody.positiveSubalgebra_toSubmodule_eq_biSup_rootSpace`,
  `TauCeti.KacMoody.negativeSubalgebra_toSubmodule_eq_biSup_rootSpace`.
* `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_positiveGenerator`,
  `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_negativeGenerator`,
  `TauCeti.KacMoody.rootSpace_root_eq_span_singleton`,
  `TauCeti.KacMoody.rootSpace_nsmul_root_eq_bot`,
  `TauCeti.KacMoody.finrank_rootSpace_root`,
  `TauCeti.KacMoody.finiteDimensional_rootSpace_of_ne_zero`,
  `TauCeti.KacMoody.center_toSubmodule_eq_map_cartanCenter`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  Theorem 1.2, §1.3, and Proposition 1.6.
-/

public section

open LieAlgebra LieSubalgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## Joint eigenspaces of the Cartan subalgebra over an arbitrary field -/

/-- The **root space** `𝔤_α` of `TauCeti.KacMoody.PresentedLieAlgebra R` attached to a weight
`α : Module.Dual K H`: the joint `α`-eigenspace of the adjoint action of `cartanElement R x` for
`x : H`. -/
noncomputable def rootSpace (α : Module.Dual K H) : Submodule K (PresentedLieAlgebra R) :=
  ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x)

/-- The defining `iInf` of eigenspaces description of `TauCeti.KacMoody.rootSpace`. -/
theorem rootSpace_def (α : Module.Dual K H) :
    rootSpace R α =
      ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x) :=
  (rfl)

/-- An element `z` belongs to `rootSpace R α` if and only if `⁅cartanElement R x, z⁆ = α x • z`
for every `x : H`. -/
theorem mem_rootSpace_iff {α : Module.Dual K H} {z : PresentedLieAlgebra R} :
    z ∈ rootSpace R α ↔ ∀ x : H, ⁅cartanElement R x, z⁆ = α x • z := by
  simp [rootSpace]

/-- Every Cartan element `cartanElement R x` acts on `z ∈ rootSpace R α` by the scalar `α x`. -/
theorem lie_cartanElement_of_mem_rootSpace {α : Module.Dual K H} {z : PresentedLieAlgebra R}
    (hz : z ∈ rootSpace R α) (x : H) :
    ⁅cartanElement R x, z⁆ = α x • z :=
  (mem_rootSpace_iff R).1 hz x

/-- The root spaces of `TauCeti.KacMoody.PresentedLieAlgebra R` are supremum-independent over any
field. -/
theorem iSupIndep_rootSpace : iSupIndep (rootSpace R) :=
  (iSupIndep_iInf_eigenspace fun x : H => ad K (PresentedLieAlgebra R) (cartanElement R x)).comp
    DFunLike.coe_injective

/-- The root spaces indexed by the root lattice `R.rootLattice` are supremum-independent. -/
theorem iSupIndep_rootSpace_rootLattice :
    iSupIndep (fun α : R.rootLattice => rootSpace R α) :=
  (iSupIndep_rootSpace R).comp Subtype.val_injective

/-- The Lie bracket adds root weights: `⁅𝔤_α, 𝔤_β⁆ ⊆ 𝔤_{α + β}`. -/
theorem lie_mem_rootSpace {α β : Module.Dual K H} {y z : PresentedLieAlgebra R}
    (hy : y ∈ rootSpace R α) (hz : z ∈ rootSpace R β) :
    ⁅y, z⁆ ∈ rootSpace R (α + β) :=
  lie_mem_iInf_eigenspace_ad hy hz

instance : SetLike.GradedBracket (rootSpace R) (rootSpace R) where
  bracket_mem _ _ _ _ hy hz := lie_mem_rootSpace R hy hz

instance : SetLike.GradedBracket
    (fun α : R.rootLattice => rootSpace R α) (fun α : R.rootLattice => rootSpace R α) where
  bracket_mem _ _ _ _ hy hz := lie_mem_rootSpace R hy hz

/-- Every Cartan element `cartanElement R x` has root weight `0`. -/
theorem cartanElement_mem_rootSpace_zero (x : H) :
    cartanElement R x ∈ rootSpace R 0 :=
  (mem_rootSpace_iff R).2 fun _ => by simp

/-- The Cartan subalgebra lies in the zero root space. -/
theorem cartanSubalgebra_toSubmodule_le_rootSpace_zero :
    (cartanSubalgebra R).toSubmodule ≤ rootSpace R 0 := by
  rw [cartanSubalgebra_toSubmodule]
  rintro _ ⟨x, rfl⟩
  exact cartanElement_mem_rootSpace_zero R x

/-- The `i`-th raising generator `eᵢ` lies in the simple root space `𝔤_{αᵢ}`. -/
theorem positiveGenerator_mem_rootSpace (i : I) :
    positiveGenerator R i ∈ rootSpace R (R.root i) :=
  (mem_rootSpace_iff R).2 fun x => lie_cartanElement_positiveGenerator R x i

/-- The `i`-th lowering generator `fᵢ` lies in the negative simple root space `𝔤_{-αᵢ}`. -/
theorem negativeGenerator_mem_rootSpace (i : I) :
    negativeGenerator R i ∈ rootSpace R (-R.root i) :=
  (mem_rootSpace_iff R).2 fun x => by simp [lie_cartanElement_negativeGenerator]

private theorem map_rootSpace_chevalleyInvolution_le (α : Module.Dual K H) :
    (rootSpace R α).map (chevalleyInvolution R).toLinearMap ≤ rootSpace R (-α) := by
  rintro _ ⟨z, hz, rfl⟩
  refine (mem_rootSpace_iff R).2 fun x => ?_
  change ⁅cartanElement R x, chevalleyInvolution R z⁆ = (-α) x • chevalleyInvolution R z
  have hx : cartanElement R x = -chevalleyInvolution R (cartanElement R x) := by simp
  conv_lhs => rw [hx]
  rw [neg_lie, ← LieEquiv.map_lie, lie_cartanElement_of_mem_rootSpace R hz x, map_smul,
    LinearMap.neg_apply, neg_smul]

/-- The Chevalley involution maps the root space `𝔤_α` onto `𝔤_{-α}`. -/
@[simp]
theorem map_rootSpace_chevalleyInvolution (α : Module.Dual K H) :
    (rootSpace R α).map (chevalleyInvolution R).toLinearMap = rootSpace R (-α) := by
  refine le_antisymm (map_rootSpace_chevalleyInvolution_le R α) fun z hz =>
    ⟨chevalleyInvolution R z, ?_, chevalleyInvolution_chevalleyInvolution R z⟩
  simpa using map_rootSpace_chevalleyInvolution_le R (-α) ⟨z, hz, rfl⟩

/-- The Chevalley involution sends a right-normed bracket of raising generators to the
corresponding signed right-normed bracket of lowering generators. -/
@[simp]
theorem chevalleyInvolution_rightNormedBracket_positiveGenerator (i : I) (w : List I) :
    chevalleyInvolution R (rightNormedBracket (positiveGenerator R) i w) =
      (-1 : K) ^ (w.length + 1) • rightNormedBracket (negativeGenerator R) i w := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [rightNormedBracket_cons, LieEquiv.map_lie, chevalleyInvolution_positiveGenerator,
      ih, List.length_cons, pow_succ, mul_neg_one, neg_lie, lie_neg, lie_smul, neg_smul, smul_neg]

/-- The Chevalley involution sends a right-normed bracket of lowering generators to the
corresponding signed right-normed bracket of raising generators. -/
@[simp]
theorem chevalleyInvolution_rightNormedBracket_negativeGenerator (i : I) (w : List I) :
    chevalleyInvolution R (rightNormedBracket (negativeGenerator R) i w) =
      (-1 : K) ^ (w.length + 1) • rightNormedBracket (positiveGenerator R) i w := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [rightNormedBracket_cons, LieEquiv.map_lie, chevalleyInvolution_negativeGenerator,
      ih, List.length_cons, pow_succ, mul_neg_one, neg_lie, lie_neg, lie_smul, neg_smul, smul_neg]

/-- A right-normed bracket of raising generators has weight equal to the sum of the simple roots
of its letters. -/
theorem rightNormedBracket_positiveGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (positiveGenerator R) i w ∈ rootSpace R ((i :: w).map R.root).sum := by
  induction w with
  | nil => simpa using positiveGenerator_mem_rootSpace R i
  | cons j w ih =>
    have hsum : ((i :: j :: w).map R.root).sum = R.root j + ((i :: w).map R.root).sum := by
      simp only [List.map_cons, List.sum_cons]
      abel
    rw [rightNormedBracket_cons, hsum]
    exact lie_mem_rootSpace R (positiveGenerator_mem_rootSpace R j) ih

/-- A right-normed bracket of lowering generators has weight equal to the negation of the sum of
the simple roots of its letters. -/
theorem rightNormedBracket_negativeGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (negativeGenerator R) i w ∈ rootSpace R (-((i :: w).map R.root).sum) := by
  induction w with
  | nil => simpa using negativeGenerator_mem_rootSpace R i
  | cons j w ih =>
    have hsum : -((i :: j :: w).map R.root).sum = -R.root j + -((i :: w).map R.root).sum := by
      simp only [List.map_cons, List.sum_cons]
      abel
    rw [rightNormedBracket_cons, hsum]
    exact lie_mem_rootSpace R (negativeGenerator_mem_rootSpace R j) ih

private theorem sum_map_root_mem_posRootCone (l : List I) :
    (l.map R.root).sum ∈ R.posRootCone := by
  induction l with
  | nil => simp
  | cons j w ih =>
    rw [List.map_cons, List.sum_cons]
    exact add_mem (R.root_mem_posRootCone j) ih

/-! ## Characteristic-zero grading and direct-sum triangular decomposition -/

section CharZero

variable [CharZero K]

private theorem height_sum_map_root (l : List I) :
    R.height ⟨(l.map R.root).sum, sum_map_root_mem_posRootCone R l⟩ = l.length := by
  induction l with
  | nil => simp
  | cons j w ih =>
    have hsplit : (⟨((j :: w).map R.root).sum, sum_map_root_mem_posRootCone R (j :: w)⟩ :
        R.posRootCone) =
        ⟨R.root j, R.root_mem_posRootCone j⟩ +
          ⟨(w.map R.root).sum, sum_map_root_mem_posRootCone R w⟩ :=
      Subtype.ext (by simp)
    rw [hsplit, map_add, R.height_root, ih, List.length_cons, add_comm]

private theorem sum_map_root_cons_ne_zero (i : I) (w : List I) :
    ((i :: w).map R.root).sum ≠ 0 := by
  intro h0
  have hh := height_sum_map_root R (i :: w)
  have hzero : (⟨((i :: w).map R.root).sum, sum_map_root_mem_posRootCone R (i :: w)⟩ :
      R.posRootCone) = 0 := Subtype.ext h0
  rw [hzero, map_zero, List.length_cons] at hh
  omega

/-- Every element of `n⁺` lies in the direct sum of the root spaces of nonzero elements of the
positive root cone `Q₊`. -/
theorem positiveSubalgebra_toSubmodule_le_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  rw [positiveSubalgebra_def, coe_lieSpan_range_eq_span_rightNormedBracket, Submodule.span_le]
  rintro _ ⟨⟨i, w⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem ((i :: w).map R.root).sum <|
    Submodule.mem_iSup_of_mem
      ⟨sum_map_root_mem_posRootCone R (i :: w), sum_map_root_cons_ne_zero R i w⟩
      (rightNormedBracket_positiveGenerator_mem_rootSpace R i w)

/-- Every element of `n⁻` lies in the direct sum of the root spaces of weights whose negation is a
nonzero element of `Q₊`. -/
theorem negativeSubalgebra_toSubmodule_le_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  rw [negativeSubalgebra_def, coe_lieSpan_range_eq_span_rightNormedBracket, Submodule.span_le]
  rintro _ ⟨⟨i, w⟩, rfl⟩
  have hne : -((i :: w).map R.root).sum ≠ 0 := neg_ne_zero.2 (sum_map_root_cons_ne_zero R i w)
  exact Submodule.mem_iSup_of_mem (-((i :: w).map R.root).sum) <|
    Submodule.mem_iSup_of_mem
      ⟨by simpa using sum_map_root_mem_posRootCone R (i :: w), hne⟩
      (rightNormedBracket_negativeGenerator_mem_rootSpace R i w)

private theorem disjoint_negCone_posCone :
    Disjoint {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}
      {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0} :=
  Set.disjoint_left.2 fun _ hneg hpos => hpos.2 (R.isPointed_posRootCone _ hpos.1 hneg.1)

private theorem disjoint_negativeSubalgebra_sup_positiveSubalgebra_rootSpace_zero :
    Disjoint ((negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
      (rootSpace R 0) := by
  have hsup : (negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | (-α ∈ R.posRootCone ∨ α ∈ R.posRootCone) ∧ α ≠ 0},
        rootSpace R α :=
    sup_le
      ((negativeSubalgebra_toSubmodule_le_biSup_rootSpace R).trans
        (biSup_mono fun _ h => ⟨Or.inl h.1, h.2⟩))
      ((positiveSubalgebra_toSubmodule_le_biSup_rootSpace R).trans
        (biSup_mono fun _ h => ⟨Or.inr h.1, h.2⟩))
  exact ((iSupIndep_rootSpace R).disjoint_biSup (x := 0) (by simp)).symm.mono hsup le_rfl

/-- Over a field of characteristic zero, `n⁻` and `n⁺` have trivial intersection. -/
theorem disjoint_negativeSubalgebra_positiveSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule (positiveSubalgebra R).toSubmodule :=
  ((iSupIndep_rootSpace R).disjoint_biSup_biSup (disjoint_negCone_posCone R)).mono
    (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R)
    (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R)

/-- Over a field of characteristic zero, `n⁻` and `𝔥` have trivial intersection. -/
theorem disjoint_negativeSubalgebra_cartanSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule (cartanSubalgebra R).toSubmodule :=
  ((iSupIndep_rootSpace R).disjoint_biSup (x := 0) (by simp)).symm.mono
    (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R)
    (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)

/-- Over a field of characteristic zero, `n⁺` and `𝔥` have trivial intersection. -/
theorem disjoint_positiveSubalgebra_cartanSubalgebra :
    Disjoint (positiveSubalgebra R).toSubmodule (cartanSubalgebra R).toSubmodule :=
  ((iSupIndep_rootSpace R).disjoint_biSup (x := 0) (by simp)).symm.mono
    (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R)
    (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)

/-- Over a field of characteristic zero, `n⁻` has trivial intersection with `𝔥 + n⁺`. -/
theorem disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule
      ((cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) := by
  have hdisj : Disjoint {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}
      (insert (0 : Module.Dual K H) {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0}) := by
    refine Set.disjoint_left.2 fun α hneg h0pos => ?_
    rcases h0pos with rfl | hpos
    · exact hneg.2 rfl
    · exact hpos.2 (R.isPointed_posRootCone _ hpos.1 hneg.1)
  have hsup : (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule ≤
      ⨆ α ∈ insert (0 : Module.Dual K H) {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0},
        rootSpace R α := by
    rw [iSup_insert]
    exact sup_le_sup (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)
      (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R)
  exact ((iSupIndep_rootSpace R).disjoint_biSup_biSup hdisj).mono
    (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R) hsup

/-- Over a field of characteristic zero, `n⁻ + n⁺` has trivial intersection with `𝔥` even without
generalized Cartan matrix hypotheses. -/
theorem disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra_of_charZero :
    Disjoint ((negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
      (cartanSubalgebra R).toSubmodule :=
  (disjoint_negativeSubalgebra_sup_positiveSubalgebra_rootSpace_zero R).mono_right
    (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)

private noncomputable def triangularLinearMap :
    (negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) →ₗ[K]
      PresentedLieAlgebra R :=
  ((negativeSubalgebra R).toSubmodule.subtype.comp (LinearMap.fst K _ _) +
      (cartanSubalgebra R).toSubmodule.subtype.comp
        ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _))) +
    (positiveSubalgebra R).toSubmodule.subtype.comp
      ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))

private theorem triangularLinearMap_bijective :
    Function.Bijective (triangularLinearMap R) := by
  refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun u => ?_⟩
  · rintro ⟨x, y, z⟩ h0
    change (x : PresentedLieAlgebra R) + y + z = 0 at h0
    have hx0 : (x : PresentedLieAlgebra R) = 0 := by
      have hyz : -(x : PresentedLieAlgebra R) = (y : PresentedLieAlgebra R) + z :=
        neg_eq_iff_add_eq_zero.2 (by simpa [add_assoc] using h0)
      exact neg_eq_zero.1 <| (Submodule.disjoint_def.1
        (disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra R)) _ (neg_mem x.2)
        (hyz ▸ add_mem (Submodule.mem_sup_left y.2) (Submodule.mem_sup_right z.2))
    have hyz0 : (y : PresentedLieAlgebra R) + z = 0 := by simpa [hx0] using h0
    have hy0 : (y : PresentedLieAlgebra R) = 0 :=
      neg_eq_zero.1 <| (Submodule.disjoint_def.1
        (disjoint_positiveSubalgebra_cartanSubalgebra R).symm)
        _ (neg_mem y.2) ((neg_eq_iff_add_eq_zero.2 hyz0) ▸ z.2)
    exact Prod.ext (Subtype.ext hx0)
      (Prod.ext (Subtype.ext hy0) (Subtype.ext (by simpa [hy0] using hyz0)))
  · have hu : u ∈ (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔
        (positiveSubalgebra R).toSubmodule :=
      negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R ▸ Submodule.mem_top
    obtain ⟨ab, hab, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hab
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

/-- **Direct-sum triangular decomposition.** Over a field of characteristic zero, addition defines
a linear isomorphism `n⁻ ⊕ 𝔥 ⊕ n⁺ ≃ₗ[K] PresentedLieAlgebra R`. -/
noncomputable def triangularEquiv :
    (negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) ≃ₗ[K]
      PresentedLieAlgebra R :=
  LinearEquiv.ofBijective (triangularLinearMap R) (triangularLinearMap_bijective R)

/-- `TauCeti.KacMoody.triangularEquiv` adds the three triangular components in `𝔤`. -/
@[simp]
theorem triangularEquiv_apply
    (p : negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) :
    triangularEquiv R p = (p.1 : PresentedLieAlgebra R) + p.2.1 + p.2.2 :=
  (rfl)

/-- The inverse of `TauCeti.KacMoody.triangularEquiv` embeds `n⁻` into the first summand. -/
@[simp]
theorem triangularEquiv_symm_coe_negative (x : negativeSubalgebra R) :
    (triangularEquiv R).symm x = (x, 0, 0) :=
  (triangularEquiv R).injective (by simp)

/-- The inverse of `TauCeti.KacMoody.triangularEquiv` embeds `𝔥` into the middle summand. -/
@[simp]
theorem triangularEquiv_symm_coe_cartan (y : cartanSubalgebra R) :
    (triangularEquiv R).symm y = (0, y, 0) :=
  (triangularEquiv R).injective (by simp)

/-- The inverse of `TauCeti.KacMoody.triangularEquiv` embeds `n⁺` into the last summand. -/
@[simp]
theorem triangularEquiv_symm_coe_positive (z : positiveSubalgebra R) :
    (triangularEquiv R).symm z = (0, 0, z) :=
  (triangularEquiv R).injective (by simp)

/-! ### Internal `Q`-grading and graded Lie algebra instances -/

/-- The root spaces of weights in `Q₊ ∪ (-Q₊)` span `PresentedLieAlgebra R`. -/
theorem biSup_rootSpace_posRootCone_or_neg_eq_top :
    (⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∨ -α ∈ R.posRootCone},
      rootSpace R α) = ⊤ := by
  rw [eq_top_iff, ← negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R,
    sup_le_iff, sup_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R).trans
      (biSup_mono fun _ h => Or.inr h.1)
  · exact (cartanSubalgebra_toSubmodule_le_rootSpace_zero R).trans <|
      le_biSup (rootSpace R)
        (show (0 : Module.Dual K H) ∈ {α | α ∈ R.posRootCone ∨ -α ∈ R.posRootCone} from
          Or.inl (zero_mem _))
  · exact (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R).trans
      (biSup_mono fun _ h => Or.inl h.1)

/-- The root spaces indexed by the root lattice `R.rootLattice` span `PresentedLieAlgebra R`. -/
theorem iSup_rootSpace_rootLattice_eq_top :
    (⨆ α : R.rootLattice, rootSpace R α) = ⊤ := by
  rw [eq_top_iff, ← biSup_rootSpace_posRootCone_or_neg_eq_top R]
  refine iSup₂_le fun α hα => ?_
  have hmem : α ∈ R.rootLattice := by
    rcases hα with hpos | hneg
    · exact R.posRootCone_le_rootLattice hpos
    · have hneg' : -α ∈ R.rootLattice := R.posRootCone_le_rootLattice hneg
      simpa using neg_mem hneg'
  exact le_iSup (fun β : R.rootLattice => rootSpace R β) ⟨α, hmem⟩

/-- The root spaces indexed by `Module.Dual K H` span `PresentedLieAlgebra R`. -/
theorem iSup_rootSpace_eq_top :
    (⨆ α : Module.Dual K H, rootSpace R α) = ⊤ := by
  rw [eq_top_iff, ← iSup_rootSpace_rootLattice_eq_top R]
  exact iSup_le fun α => le_iSup (rootSpace R) (α : Module.Dual K H)

/-- `PresentedLieAlgebra R` is the internal direct sum of its root spaces over `Module.Dual K H`. -/
theorem isInternal_rootSpace [DecidableEq (Module.Dual K H)] :
    DirectSum.IsInternal (rootSpace R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_rootSpace R) (iSup_rootSpace_eq_top R)

/-- `PresentedLieAlgebra R` is the internal direct sum of its root spaces over the root lattice
`R.rootLattice`. -/
theorem isInternal_rootSpace_rootLattice [DecidableEq R.rootLattice] :
    DirectSum.IsInternal (fun α : R.rootLattice => rootSpace R α) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_rootSpace_rootLattice R) (iSup_rootSpace_rootLattice_eq_top R)

noncomputable instance [DecidableEq (Module.Dual K H)] :
    DirectSum.Decomposition (rootSpace R) :=
  (isInternal_rootSpace R).chooseDecomposition

noncomputable instance [DecidableEq (Module.Dual K H)] :
    GradedLieAlgebra (rootSpace R) where

noncomputable instance [DecidableEq R.rootLattice] :
    DirectSum.Decomposition (fun α : R.rootLattice => rootSpace R α) :=
  (isInternal_rootSpace_rootLattice R).chooseDecomposition

noncomputable instance [DecidableEq R.rootLattice] :
    GradedLieAlgebra (fun α : R.rootLattice => rootSpace R α) where

/-- **No mixed-sign roots**: if neither `α` nor `-α` lies in the positive root cone `Q₊`, then
`rootSpace R α = ⊥`. -/
theorem rootSpace_eq_bot_of_notMem_posRootCone {α : Module.Dual K H}
    (hpos : α ∉ R.posRootCone) (hneg : -α ∉ R.posRootCone) :
    rootSpace R α = ⊥ := by
  have hd := (iSupIndep_rootSpace R).disjoint_biSup
    (x := α) (y := {β : Module.Dual K H | β ∈ R.posRootCone ∨ -β ∈ R.posRootCone})
    (by simp [hpos, hneg])
  rwa [biSup_rootSpace_posRootCone_or_neg_eq_top R, disjoint_top] at hd

/-- Any weight outside the root lattice `R.rootLattice` has zero root space. -/
theorem rootSpace_eq_bot_of_notMem_rootLattice {α : Module.Dual K H}
    (hα : α ∉ R.rootLattice) : rootSpace R α = ⊥ :=
  rootSpace_eq_bot_of_notMem_posRootCone R
    (fun h => hα (R.posRootCone_le_rootLattice h))
    (fun h => hα (by
      have h' : -α ∈ R.rootLattice := R.posRootCone_le_rootLattice h
      simpa using neg_mem h'))

/-- **Zero root space.** Over a field of characteristic zero, the zero root space of
`PresentedLieAlgebra R` is the Cartan subalgebra `𝔥`. -/
@[simp]
theorem rootSpace_zero_eq :
    rootSpace R 0 = (cartanSubalgebra R).toSubmodule := by
  refine le_antisymm (fun u hu => ?_) (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)
  have hu' : u ∈ (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔
      (positiveSubalgebra R).toSubmodule :=
    negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R ▸ Submodule.mem_top
  obtain ⟨ab, hab, z, hz, rfl⟩ := Submodule.mem_sup.1 hu'
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hab
  have hxz0 : x + z = 0 := by
    have hsub : x + y + z - y = x + z := by abel
    exact (Submodule.disjoint_def.1
      (disjoint_negativeSubalgebra_sup_positiveSubalgebra_rootSpace_zero R)) _
      (add_mem (Submodule.mem_sup_left hx) (Submodule.mem_sup_right hz))
      (hsub ▸ sub_mem hu (cartanSubalgebra_toSubmodule_le_rootSpace_zero R hy))
  rwa [show x + y + z = x + z + y by abel, hxz0, zero_add]

/-- Over a field of characteristic zero, `n⁺` is the direct sum of the root spaces of nonzero
elements of the positive root cone `Q₊`. -/
theorem positiveSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule =
      ⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  refine le_antisymm (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R) (fun u hu => ?_)
  have hu' : u ∈ (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔
      (positiveSubalgebra R).toSubmodule :=
    negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R ▸ Submodule.mem_top
  obtain ⟨ab, hab, z, hz, rfl⟩ := Submodule.mem_sup.1 hu'
  have hab_le : (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ≤
      ⨆ α ∈ insert (0 : Module.Dual K H) {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0},
        rootSpace R α := by
    rw [iSup_insert, sup_comm]
    exact sup_le_sup (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)
      (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R)
  have hdisj : Disjoint
      (insert (0 : Module.Dual K H) {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0})
      {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0} := by
    refine Set.disjoint_left.2 fun α h0neg hpos => ?_
    rcases h0neg with rfl | hneg
    · exact hpos.2 rfl
    · exact hpos.2 (R.isPointed_posRootCone _ hpos.1 hneg.1)
  have hab0 : ab = 0 :=
    (Submodule.disjoint_def.1 ((iSupIndep_rootSpace R).disjoint_biSup_biSup hdisj)) _ (hab_le hab)
      (by simpa using sub_mem hu (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R hz))
  rwa [hab0, zero_add]

/-- Over a field of characteristic zero, `n⁻` is the direct sum of the root spaces of weights
whose negation is a nonzero element of `Q₊`. -/
theorem negativeSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule =
      ⨆ α ∈ {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  rw [← map_positiveSubalgebra_chevalleyInvolution, LieSubalgebra.map_toSubmodule,
    positiveSubalgebra_toSubmodule_eq_biSup_rootSpace, Submodule.map_iSup]
  simp only [Submodule.map_iSup]
  refine le_antisymm (iSup₂_le fun β hβ => ?_) (iSup₂_le fun α hα => ?_)
  · change (rootSpace R β).map (chevalleyInvolution R).toLinearMap ≤ _
    rw [map_rootSpace_chevalleyInvolution]
    exact le_biSup (rootSpace R) (show -β ∈ {α | -α ∈ R.posRootCone ∧ α ≠ 0} from
      ⟨by simpa using hβ.1, neg_ne_zero.2 hβ.2⟩)
  · have hmem : -α ∈ {β : Module.Dual K H | β ∈ R.posRootCone ∧ β ≠ 0} :=
      ⟨hα.1, neg_ne_zero.2 hα.2⟩
    refine (le_biSup
      (fun β => (rootSpace R β).map (chevalleyInvolution R).toLinearMap) hmem).trans' ?_
    rw [map_rootSpace_chevalleyInvolution, neg_neg]

/-! ### Bracket-word spanning, simple root spaces, and finite-dimensionality -/

/-- **Positive root spaces are spanned by bracket words.** If `α ≠ 0` and `-α ∉ Q₊`, then `𝔤_α` is
spanned by the right-normed brackets of raising generators whose simple-root weights sum to `α`. -/
theorem rootSpace_eq_span_rightNormedBracket_positiveGenerator
    {α : Module.Dual K H} (h0 : α ≠ 0) (hneg : -α ∉ R.posRootCone) :
    rootSpace R α =
      Submodule.span K
        ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
          {p | ((p.1 :: p.2).map R.root).sum = α}) := by
  set Wα := Submodule.span K
    ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
      {p | ((p.1 :: p.2).map R.root).sum = α})
  have hWα : Wα ≤ rootSpace R α := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl, rfl⟩
    exact rightNormedBracket_positiveGenerator_mem_rootSpace R i w
  refine le_antisymm ?_ hWα
  by_cases hpos : α ∈ R.posRootCone
  · intro u hu
    have hu_pos : u ∈ (positiveSubalgebra R).toSubmodule := by
      rw [positiveSubalgebra_toSubmodule_eq_biSup_rootSpace]
      exact Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem ⟨hpos, h0⟩ hu)
    have hsplit : u ∈ Wα ⊔ Submodule.span K
        ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
          {p | ((p.1 :: p.2).map R.root).sum ≠ α}) := by
      rw [← Submodule.span_union, ← Set.image_union]
      rw [positiveSubalgebra_def, coe_lieSpan_range_eq_span_rightNormedBracket,
        ← Set.image_univ] at hu_pos
      convert hu_pos using 3
      ext p
      simp [em]
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hsplit
    have hu₂_other : u₂ ∈ ⨆ β ∈ {β : Module.Dual K H | β ≠ α}, rootSpace R β := by
      refine Submodule.span_le.2 ?_ hu₂
      rintro _ ⟨⟨i, w⟩, hne, rfl⟩
      exact Submodule.mem_iSup_of_mem ((i :: w).map R.root).sum
        (Submodule.mem_iSup_of_mem hne (rightNormedBracket_positiveGenerator_mem_rootSpace R i w))
    have hu₂0 : u₂ = 0 := by
      have hd := (iSupIndep_rootSpace R).disjoint_biSup
        (x := α) (y := {β : Module.Dual K H | β ≠ α}) (by simp)
      refine (Submodule.disjoint_def.1 hd) _ ?_ hu₂_other
      simpa using sub_mem hu (hWα hu₁)
    rwa [hu₂0, add_zero]
  · rw [rootSpace_eq_bot_of_notMem_posRootCone R hpos hneg]
    exact bot_le

/-- **Negative root spaces are spanned by bracket words.** If `α ≠ 0` and `α ∉ Q₊`, then `𝔤_α` is
spanned by the right-normed brackets of lowering generators whose negated simple-root weights sum
to `α`. -/
theorem rootSpace_eq_span_rightNormedBracket_negativeGenerator
    {α : Module.Dual K H} (h0 : α ≠ 0) (hpos : α ∉ R.posRootCone) :
    rootSpace R α =
      Submodule.span K
        ((fun p : I × List I => rightNormedBracket (negativeGenerator R) p.1 p.2) ''
          {p | -((p.1 :: p.2).map R.root).sum = α}) := by
  have heq : rootSpace R α = (rootSpace R (-α)).map (chevalleyInvolution R).toLinearMap := by
    rw [map_rootSpace_chevalleyInvolution, neg_neg]
  rw [heq, rootSpace_eq_span_rightNormedBracket_positiveGenerator R
    (neg_ne_zero.2 h0) (by simpa using hpos), Submodule.map_span, ← Set.image_comp]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨⟨i, w⟩, hw, rfl⟩
    change chevalleyInvolution R (rightNormedBracket (positiveGenerator R) i w) ∈ _
    rw [chevalleyInvolution_rightNormedBracket_positiveGenerator]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span
      ⟨(i, w), neg_eq_iff_eq_neg.2 hw, rfl⟩
  · rintro _ ⟨⟨i, w⟩, hw, rfl⟩
    dsimp only
    have hmem : chevalleyInvolution R (rightNormedBracket (positiveGenerator R) i w) ∈
        Submodule.span K
          (((chevalleyInvolution R).toLinearMap ∘
              fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
            {p | ((p.1 :: p.2).map R.root).sum = -α}) :=
      Submodule.subset_span ⟨(i, w), neg_eq_iff_eq_neg.1 hw, rfl⟩
    rw [chevalleyInvolution_rightNormedBracket_positiveGenerator] at hmem
    have hinv : (-1 : K) ^ (w.length + 1) • (-1 : K) ^ (w.length + 1) •
        rightNormedBracket (negativeGenerator R) i w =
        rightNormedBracket (negativeGenerator R) i w := by
      rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rw [← hinv]
    exact Submodule.smul_mem _ _ hmem

/-- **Simple root space.** Over a field of characteristic zero, the root space of the simple root
`αᵢ` is the line spanned by `eᵢ`. -/
theorem rootSpace_root_eq_span_singleton (i : I) :
    rootSpace R (R.root i) = K ∙ positiveGenerator R i := by
  have h0 : R.root i ≠ 0 := R.root_linearIndependent.ne_zero i
  have hneg : -R.root i ∉ R.posRootCone :=
    fun h => h0 (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) h)
  rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R h0 hneg]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, Prod.exists, Set.mem_singleton_iff]
  refine ⟨?_, fun hz => ⟨i, [], by simp, by simp [hz]⟩⟩
  rintro ⟨j, w, hw, rfl⟩
  have hrep : j :: w = List.replicate 1 i :=
    R.root_linearIndependent.eq_replicate_of_sum_map_eq_nsmul (by rwa [one_nsmul])
  rw [List.replicate_one, List.cons.injEq] at hrep
  rw [hrep.1, hrep.2, rightNormedBracket_nil]

/-- **Negative simple root space.** Over a field of characteristic zero, the root space of `-αᵢ` is
the line spanned by `fᵢ`. -/
theorem rootSpace_neg_root_eq_span_singleton (i : I) :
    rootSpace R (-R.root i) = K ∙ negativeGenerator R i := by
  have hchev : (chevalleyInvolution R).toLinearMap (positiveGenerator R i) =
      -negativeGenerator R i :=
    chevalleyInvolution_positiveGenerator R i
  rw [← map_rootSpace_chevalleyInvolution, rootSpace_root_eq_span_singleton, Submodule.map_span,
    Set.image_singleton, hchev]
  exact le_antisymm
    ((Submodule.span_singleton_le_iff_mem _ _).2
      (neg_mem (Submodule.mem_span_singleton_self (negativeGenerator R i))))
    ((Submodule.span_singleton_le_iff_mem _ _).2
      (by simpa using neg_mem (Submodule.mem_span_singleton_self (-negativeGenerator R i))))

/-- **Higher multiples of a simple root vanish.** Over a field of characteristic zero,
`rootSpace R (m • R.root i) = ⊥` for every `m ≥ 2`. -/
theorem rootSpace_nsmul_root_eq_bot (i : I) {m : ℕ} (hm : 2 ≤ m) :
    rootSpace R (m • R.root i) = ⊥ := by
  have h0 : m • R.root i ≠ 0 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    exact smul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (R.root_linearIndependent.ne_zero i)
  have hneg : -(m • R.root i) ∉ R.posRootCone :=
    fun h => h0 (R.isPointed_posRootCone _ (nsmul_mem (R.root_mem_posRootCone i) m) h)
  rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R h0 hneg, Submodule.span_eq_bot]
  rintro _ ⟨⟨j, w⟩, hw, rfl⟩
  have hrep : j :: w = List.replicate m i :=
    R.root_linearIndependent.eq_replicate_of_sum_map_eq_nsmul hw
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [List.replicate_succ, List.cons.injEq] at hrep
  dsimp only
  rw [hrep.1, hrep.2]
  exact rightNormedBracket_eq_zero_of_forall_mem_eq (positiveGenerator R) (by simp)
    fun l hl => List.eq_of_mem_replicate hl

/-- Over a field of characteristic zero, `rootSpace R (-(m • R.root i)) = ⊥` for every `m ≥ 2`. -/
theorem rootSpace_neg_nsmul_root_eq_bot (i : I) {m : ℕ} (hm : 2 ≤ m) :
    rootSpace R (-(m • R.root i)) = ⊥ := by
  rw [← map_rootSpace_chevalleyInvolution, rootSpace_nsmul_root_eq_bot R i hm, Submodule.map_bot]

private theorem fg_rootSpace_of_notMem_neg [Finite I] {α : Module.Dual K H}
    (hα : α ≠ 0) (hneg : -α ∉ R.posRootCone) :
    (rootSpace R α).FG := by
  by_cases hpos : α ∈ R.posRootCone
  · rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R hα hneg]
    refine Submodule.fg_span (Set.Finite.image _ ?_)
    refine (Set.Finite.prod Set.finite_univ
      (List.finite_length_eq I (R.height ⟨α, hpos⟩ - 1))).subset ?_
    rintro ⟨j, w⟩ (hw : ((j :: w).map R.root).sum = α)
    refine ⟨trivial, ?_⟩
    change w.length = R.height ⟨α, hpos⟩ - 1
    have hh := height_sum_map_root R (j :: w)
    have hsub : (⟨((j :: w).map R.root).sum, sum_map_root_mem_posRootCone R (j :: w)⟩ :
        R.posRootCone) = ⟨α, hpos⟩ := Subtype.ext hw
    rw [hsub, List.length_cons] at hh
    omega
  · rw [rootSpace_eq_bot_of_notMem_posRootCone R hpos hneg]
    exact Submodule.fg_bot

/-- **Finite-dimensionality of nonzero root spaces.** When `I` is finite and `K` has characteristic
zero, every nonzero root space `rootSpace R α` is finite-dimensional, even if `H` is
infinite-dimensional. -/
theorem finiteDimensional_rootSpace_of_ne_zero [Finite I] {α : Module.Dual K H}
    (hα : α ≠ 0) : FiniteDimensional K (rootSpace R α) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  by_cases hneg : -α ∈ R.posRootCone
  · have hpos : α ∉ R.posRootCone := fun hpos => hα (R.isPointed_posRootCone _ hpos hneg)
    have hfg : (rootSpace R (-α)).FG :=
      fg_rootSpace_of_notMem_neg R (neg_ne_zero.2 hα) (by simpa using hpos)
    have heq : rootSpace R α = (rootSpace R (-α)).map (chevalleyInvolution R).toLinearMap := by
      rw [map_rootSpace_chevalleyInvolution, neg_neg]
    rw [heq]
    exact hfg.map _
  · exact fg_rootSpace_of_notMem_neg R hα hneg

/-- When `I` is finite and `H` is finite-dimensional over a field of characteristic zero, every
root space `rootSpace R α` is finite-dimensional. -/
instance finiteDimensional_rootSpace [Finite I] [FiniteDimensional K H] (α : Module.Dual K H) :
    FiniteDimensional K (rootSpace R α) := by
  rcases eq_or_ne α 0 with rfl | hα
  · rw [← Submodule.fg_iff_finiteDimensional, rootSpace_zero_eq, cartanSubalgebra_toSubmodule,
      LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map (cartanElement R)
  · exact finiteDimensional_rootSpace_of_ne_zero R hα

/-! ### Generalized Cartan matrices in characteristic zero: simple multiplicities and center -/

section GeneralizedCartan

variable (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
  (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
include hdiag hoff hzero

/-- **Simple root multiplicity one.** For a generalized Cartan matrix over a field of
characteristic zero, `dim 𝔤_{αᵢ} = 1`. -/
@[simp]
theorem finrank_rootSpace_root (i : I) :
    Module.finrank K (rootSpace R (R.root i)) = 1 := by
  rw [rootSpace_root_eq_span_singleton,
    finrank_span_singleton (positiveGenerator_ne_zero R hdiag hoff hzero i)]

/-- **Negative simple root multiplicity one.** For a generalized Cartan matrix over a field of
characteristic zero, `dim 𝔤_{-αᵢ} = 1`. -/
@[simp]
theorem finrank_rootSpace_neg_root (i : I) :
    Module.finrank K (rootSpace R (-R.root i)) = 1 := by
  rw [rootSpace_neg_root_eq_span_singleton,
    finrank_span_singleton (negativeGenerator_ne_zero R hdiag hoff hzero i)]

/-- **Center of a Kac–Moody Lie algebra (Kac, Proposition 1.6).** For a generalized Cartan matrix
over a field of characteristic zero, the center of `PresentedLieAlgebra R` is the image of
`R.cartanCenter = {x ∈ H | ∀ i, αᵢ(x) = 0}` under `cartanElement R`. -/
theorem center_toSubmodule_eq_map_cartanCenter :
    (LieAlgebra.center K (PresentedLieAlgebra R)).toSubmodule =
      R.cartanCenter.map (cartanElement R) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · have hz0 : z ∈ rootSpace R 0 := by
      rw [mem_rootSpace_iff]
      intro x
      rw [LinearMap.zero_apply, zero_smul, ← lie_skew]
      simp [(LieModule.mem_maxTrivSubmodule K _ _ z).1 hz (cartanElement R x)]
    rw [rootSpace_zero_eq, cartanSubalgebra_toSubmodule] at hz0
    obtain ⟨x, rfl⟩ := hz0
    exact ⟨x, (cartanElement_mem_center_iff R hdiag hoff hzero).1 hz, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact cartanElement_mem_center_of_mem_cartanCenter R hx

/-- The canonical linear isomorphism `R.cartanCenter ≃ₗ[K] LieAlgebra.center K 𝔤(R)` induced by
`cartanElement R` for a generalized Cartan matrix over a field of characteristic zero. -/
noncomputable def cartanCenterEquiv :
    R.cartanCenter ≃ₗ[K] LieAlgebra.center K (PresentedLieAlgebra R) :=
  (Submodule.equivMapOfInjective (cartanElement R)
      (cartanElement_injective R hdiag hoff hzero) R.cartanCenter).trans
    (LinearEquiv.ofEq _ _ (center_toSubmodule_eq_map_cartanCenter R hdiag hoff hzero).symm)

/-- Coercing `TauCeti.KacMoody.cartanCenterEquiv` to the ambient Lie algebra gives
`TauCeti.KacMoody.cartanElement`. -/
@[simp]
theorem coe_cartanCenterEquiv_apply (x : R.cartanCenter) :
    (cartanCenterEquiv R hdiag hoff hzero x : PresentedLieAlgebra R) = cartanElement R x :=
  (rfl)

/-- The inverse of `TauCeti.KacMoody.cartanCenterEquiv` recovers `x` from a central
`cartanElement R x`. -/
@[simp]
theorem cartanCenterEquiv_symm_cartanElement {x : H}
    (hx : x ∈ R.cartanCenter)
    (hz : cartanElement R x ∈ LieAlgebra.center K (PresentedLieAlgebra R)) :
    (cartanCenterEquiv R hdiag hoff hzero).symm ⟨cartanElement R x, hz⟩ = ⟨x, hx⟩ := by
  apply (cartanCenterEquiv R hdiag hoff hzero).injective
  ext
  simp

/-- For a generalized Cartan matrix over a field of characteristic zero, the center of
`PresentedLieAlgebra R` is trivial if and only if `R.cartanCenter = ⊥`. -/
@[simp]
theorem center_eq_bot_iff :
    LieAlgebra.center K (PresentedLieAlgebra R) = ⊥ ↔ R.cartanCenter = ⊥ := by
  rw [← LieSubmodule.toSubmodule_eq_bot, center_toSubmodule_eq_map_cartanCenter R hdiag hoff hzero]
  refine ⟨fun h => (Submodule.eq_bot_iff _).2 fun x hx => ?_, fun h => by simp [h]⟩
  exact cartanElement_injective R hdiag hoff hzero <|
    ((Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩).trans (map_zero _).symm

end GeneralizedCartan

end CharZero

end KacMoody

end TauCeti
