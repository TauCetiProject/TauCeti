/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Graded
public import TauCeti.Algebra.Lie.KacMoody.Triangular
public import TauCeti.Algebra.Lie.Subalgebra.LieSpan
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Algebra.Lie.Graded.Supported
import TauCeti.Algebra.Lie.Weights.Eigenvector
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.LinearAlgebra.LinearIndependent.NonnegCombination
import TauCeti.LinearAlgebra.Submodule.Independent

/-!
# Root-space grading of Kac–Moody Lie algebras

Let `R : CartanRealization (A.map (Int.cast : ℤ → K)) H` be a realization of an integer matrix `A`
over a field `K`, and let `𝔤 = TauCeti.KacMoody.PresentedLieAlgebra R` be the Lie algebra it
presents. For every linear functional `α : Module.Dual K H`, the **root space**
`TauCeti.KacMoody.rootSpace R α` is the joint eigenspace
`{z ∈ 𝔤 | ∀ x : H, ⁅cartanElement R x, z⁆ = α x • z}` of the Cartan action.

Even when `A` is singular — for instance in affine type, where the null root `δ` vanishes on every
simple coroot — the simple roots `R.root i` are linearly independent in `Module.Dual K H`, so the
adjoint action of the full realization `H` separates all elements of the root lattice
`R.rootLattice`. Combining the spanning triangular decomposition `𝔤 = n⁻ + 𝔥 + n⁺` from
`TauCeti.Algebra.Lie.KacMoody.Triangular` with supremum-independence of joint eigenspaces yields,
over any field `K`:

* an **internal `Q`-grading** (`TauCeti.KacMoody.isInternal_rootSpace`,
  `TauCeti.KacMoody.isInternal_rootSpace_rootLattice`, and `GradedLieAlgebra` instances)
  `𝔤 = ⨁ α ∈ Q, 𝔤_α` with `𝔤_α = ⊥` unless `α ∈ Q₊` or `-α ∈ Q₊`
  (`TauCeti.KacMoody.rootSpace_eq_bot_of_notMem_posRootCone_of_neg_notMem`);
* **bracket-word spanning**: whenever `-α ∉ Q₊` (respectively `α ∉ Q₊`), `𝔤_α` is spanned by
  right-normed brackets of raising (respectively lowering) generators whose simple-root weights sum
  to `α` (respectively `-α`), via
  `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_positiveGenerator` and
  `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_negativeGenerator`.

Over a field of characteristic zero, the pointedness of the positive root cone `R.posRootCone` and
`LinearIndependent.finite_setOf_sum_map_eq` refine this grading and yield:

* **Triangular components via root spaces**: `𝔤_0 = 𝔥` (`TauCeti.KacMoody.rootSpace_zero_eq`),
  `n⁺ = ⨁_{α ∈ Q₊ \ {0}} 𝔤_α`, and `n⁻ = ⨁_{-α ∈ Q₊ \ {0}} 𝔤_α`.
* **Finite-dimensionality**: every nonzero weight `α ≠ 0` has finite-dimensional root space `𝔤_α`
  without any finiteness hypothesis on `I` or `H`
  (`TauCeti.KacMoody.finiteDimensional_rootSpace_of_ne_zero`).
* **Simple root multiplicities and `m • αᵢ` vanishing**: `𝔤_{αᵢ} = K ∙ eᵢ` and `𝔤_{-αᵢ} = K ∙ fᵢ`
  (one-dimensional whenever `cartanElement R` is injective, in particular for a generalized Cartan
  matrix, by `TauCeti.KacMoody.finrank_rootSpace_root`), while `𝔤_{m • αᵢ} = ⊥` and
  `𝔤_{-(m • αᵢ)} = ⊥` for `m ≥ 2`.
* **Center of a Kac–Moody Lie algebra** (`TauCeti.KacMoody.center_toSubmodule_eq_map_cartanCenter`
  and `TauCeti.KacMoody.cartanCenterEquiv`): in characteristic zero, whenever `cartanElement R` is
  injective (in particular for a generalized Cartan matrix), `LieAlgebra.center K 𝔤` is the
  isomorphic image of `R.cartanCenter = {x ∈ H | ∀ i, αᵢ(x) = 0}` under `cartanElement R`
  (Kac, Proposition 1.6).

The root-space grading and bracket-word spanning arguments adapt those for Serre's presentation in
`TauCeti.Algebra.Lie.Presentation.Serre.Triangular` and
`TauCeti.Algebra.Lie.Presentation.Serre.Word` to a `TauCeti.CartanRealization`.

## Main definitions

* `TauCeti.KacMoody.rootSpace`: the joint eigenspace `𝔤_α` for `α : Module.Dual K H`.
* `TauCeti.KacMoody.cartanCenterEquiv`: the linear equivalence
  `R.cartanCenter ≃ₗ[K] LieAlgebra.center K (PresentedLieAlgebra R)` whenever `cartanElement R` is
  injective over a field of characteristic zero (in particular for a generalized Cartan matrix).

## Main results

* `TauCeti.KacMoody.iSupIndep_rootSpace`, `TauCeti.KacMoody.lie_mem_rootSpace`,
  `TauCeti.KacMoody.map_chevalleyInvolution_rootSpace`.
* `TauCeti.KacMoody.isInternal_rootSpace`, `TauCeti.KacMoody.isInternal_rootSpace_rootLattice`,
  `TauCeti.KacMoody.rootSpace_eq_bot_of_notMem_posRootCone_of_neg_notMem`,
  `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_positiveGenerator`,
  `TauCeti.KacMoody.rootSpace_eq_span_rightNormedBracket_negativeGenerator`,
  `TauCeti.KacMoody.rootSpace_zero_eq`,
  `TauCeti.KacMoody.positiveSubalgebra_toSubmodule_eq_biSup_rootSpace`,
  `TauCeti.KacMoody.negativeSubalgebra_toSubmodule_eq_biSup_rootSpace`.
* `TauCeti.KacMoody.rootSpace_root_eq_span_singleton`,
  `TauCeti.KacMoody.rootSpace_nsmul_root_eq_bot`,
  `TauCeti.KacMoody.finrank_rootSpace_root`,
  `TauCeti.KacMoody.finiteDimensional_rootSpace_of_ne_zero`,
  `TauCeti.KacMoody.center_toSubmodule_eq_map_cartanCenter`,
  `TauCeti.KacMoody.cartanElement_cartanCenterEquiv_symm`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  Theorem 1.2, §1.3, and Proposition 1.6.
-/

public section

open LieAlgebra LieSubalgebra
open scoped Pointwise

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## Joint eigenspaces and internal `Q`-grading over an arbitrary field -/

/-- The **root space** `𝔤_α` of `TauCeti.KacMoody.PresentedLieAlgebra R` attached to a weight
`α : Module.Dual K H`: the joint `α`-eigenspace of the adjoint action of `cartanElement R x` for
`x : H`. -/
noncomputable def rootSpace (α : Module.Dual K H) : Submodule K (PresentedLieAlgebra R) :=
  ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x)

/-- The defining `iInf` of eigenspaces description of `TauCeti.KacMoody.rootSpace`. -/
theorem rootSpace_def (α : Module.Dual K H) :
    rootSpace R α = ⨅ x : H, (ad K (PresentedLieAlgebra R) (cartanElement R x)).eigenspace (α x) :=
  (rfl)

/-- An element `z` belongs to `rootSpace R α` if and only if `⁅cartanElement R x, z⁆ = α x • z`
for every `x : H`. -/
theorem mem_rootSpace_iff {α : Module.Dual K H} {z : PresentedLieAlgebra R} :
    z ∈ rootSpace R α ↔ ∀ x : H, ⁅cartanElement R x, z⁆ = α x • z := by simp [rootSpace]

/-- Every Cartan element `cartanElement R x` acts on `z ∈ rootSpace R α` by the scalar `α x`. -/
theorem lie_cartanElement_of_mem_rootSpace {α : Module.Dual K H} {z : PresentedLieAlgebra R}
    (hz : z ∈ rootSpace R α) (x : H) : ⁅cartanElement R x, z⁆ = α x • z :=
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
    (hy : y ∈ rootSpace R α) (hz : z ∈ rootSpace R β) : ⁅y, z⁆ ∈ rootSpace R (α + β) :=
  lie_mem_iInf_eigenspace_ad hy hz

instance : SetLike.GradedBracket (rootSpace R) (rootSpace R) where
  bracket_mem _ _ _ _ hy hz := lie_mem_rootSpace R hy hz

instance : SetLike.GradedBracket
    (fun α : R.rootLattice => rootSpace R α) (fun α : R.rootLattice => rootSpace R α) where
  bracket_mem _ _ _ _ hy hz := lie_mem_rootSpace R hy hz

/-- Every Cartan element `cartanElement R x` has root weight `0`. -/
@[simp]
theorem cartanElement_mem_rootSpace_zero (x : H) : cartanElement R x ∈ rootSpace R 0 :=
  (mem_rootSpace_iff R).2 fun _ => by simp

/-- The Cartan subalgebra lies in the zero root space. -/
theorem cartanSubalgebra_toSubmodule_le_rootSpace_zero :
    (cartanSubalgebra R).toSubmodule ≤ rootSpace R 0 := by
  rw [cartanSubalgebra_toSubmodule]; rintro _ ⟨x, rfl⟩; exact cartanElement_mem_rootSpace_zero R x

/-- The `i`-th raising generator `eᵢ` lies in the simple root space `𝔤_{αᵢ}`. -/
@[simp]
theorem positiveGenerator_mem_rootSpace (i : I) : positiveGenerator R i ∈ rootSpace R (R.root i) :=
  (mem_rootSpace_iff R).2 fun x => lie_cartanElement_positiveGenerator R x i

/-- The `i`-th lowering generator `fᵢ` lies in the negative simple root space `𝔤_{-αᵢ}`. -/
@[simp]
theorem negativeGenerator_mem_rootSpace (i : I) :
    negativeGenerator R i ∈ rootSpace R (-R.root i) :=
  (mem_rootSpace_iff R).2 fun x => by simp [lie_cartanElement_negativeGenerator]

private theorem map_chevalleyInvolution_rootSpace_le (α : Module.Dual K H) :
    (rootSpace R α).map (chevalleyInvolution R).toLinearMap ≤ rootSpace R (-α) := by
  rintro _ ⟨z, hz, rfl⟩
  refine (mem_rootSpace_iff R).2 fun x => ?_
  rw [LieHom.coe_toLinearMap, LieEquiv.coe_coe]
  have hx : cartanElement R x = -chevalleyInvolution R (cartanElement R x) := by simp
  conv_lhs => rw [hx]
  rw [neg_lie, ← LieEquiv.map_lie, lie_cartanElement_of_mem_rootSpace R hz x, map_smul,
    LinearMap.neg_apply, neg_smul]

/-- The Chevalley involution maps the root space `𝔤_α` onto `𝔤_{-α}`. -/
@[simp] theorem map_chevalleyInvolution_rootSpace (α : Module.Dual K H) :
    (rootSpace R α).map (chevalleyInvolution R).toLinearMap = rootSpace R (-α) := by
  refine le_antisymm (map_chevalleyInvolution_rootSpace_le R α) fun z hz =>
    ⟨chevalleyInvolution R z, ?_, ?_⟩
  · have hmem : (chevalleyInvolution R).toLinearMap z ∈
        (rootSpace R (-α)).map (chevalleyInvolution R).toLinearMap := ⟨z, hz, rfl⟩
    simpa [LieHom.coe_toLinearMap, LieEquiv.coe_coe] using
      map_chevalleyInvolution_rootSpace_le R (-α) hmem
  · rw [LieHom.coe_toLinearMap, LieEquiv.coe_coe, chevalleyInvolution_chevalleyInvolution]

private theorem map_chevalleyInvolution_biSup_rootSpace (p : Module.Dual K H → Prop) :
    (⨆ (α : Module.Dual K H) (_ : p α), rootSpace R α).map (chevalleyInvolution R).toLinearMap =
      ⨆ (α : Module.Dual K H) (_ : p (-α)), rootSpace R α := by
  simp only [Submodule.map_iSup, map_chevalleyInvolution_rootSpace]
  refine le_antisymm (iSup₂_le fun β hβ => ?_) (iSup₂_le fun α hα => ?_)
  · exact le_iSup₂_of_le (-β) (by simpa using hβ) le_rfl
  · exact (le_iSup₂_of_le (-α) hα le_rfl).trans' (by rw [neg_neg])

/-- The Chevalley involution sends a right-normed bracket of raising generators to the
corresponding signed right-normed bracket of lowering generators. -/
@[simp] theorem chevalleyInvolution_rightNormedBracket_positiveGenerator (i : I) (w : List I) :
    chevalleyInvolution R (rightNormedBracket (positiveGenerator R) i w) =
      (-1 : K) ^ (w.length + 1) • rightNormedBracket (negativeGenerator R) i w := by
  have hcomp :
      (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) ∘
          positiveGenerator R = -negativeGenerator R := by
    ext j; exact chevalleyInvolution_positiveGenerator R j
  rw [← LieEquiv.coe_toLieHom, LieHom.map_rightNormedBracket, hcomp, rightNormedBracket_neg,
    ← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The Chevalley involution sends a right-normed bracket of lowering generators to the
corresponding signed right-normed bracket of raising generators. -/
@[simp] theorem chevalleyInvolution_rightNormedBracket_negativeGenerator (i : I) (w : List I) :
    chevalleyInvolution R (rightNormedBracket (negativeGenerator R) i w) =
      (-1 : K) ^ (w.length + 1) • rightNormedBracket (positiveGenerator R) i w := by
  have h := congrArg (chevalleyInvolution R)
    (chevalleyInvolution_rightNormedBracket_positiveGenerator R i w)
  rw [chevalleyInvolution_chevalleyInvolution, map_smul] at h
  have hinv := congrArg (fun x => ((-1 : K) ^ (w.length + 1)) • x) h.symm
  simpa [smul_smul, ← mul_pow] using hinv

/-- A right-normed bracket of raising generators has weight equal to the sum of the simple roots
of its letters. -/
theorem rightNormedBracket_positiveGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (positiveGenerator R) i w ∈ rootSpace R ((i :: w).map R.root).sum :=
  rightNormedBracket_mem_of_bracket_mem (positiveGenerator R) (rootSpace R)
    (fun hy hz => lie_mem_rootSpace R hy hz) (positiveGenerator_mem_rootSpace R) i w

/-- A right-normed bracket of lowering generators has weight equal to the negation of the sum of
the simple roots of its letters. -/
theorem rightNormedBracket_negativeGenerator_mem_rootSpace (i : I) (w : List I) :
    rightNormedBracket (negativeGenerator R) i w ∈ rootSpace R (-((i :: w).map R.root).sum) := by
  have hmem : chevalleyInvolution R (rightNormedBracket (positiveGenerator R) i w) ∈
      rootSpace R (-((i :: w).map R.root).sum) := by
    rw [← map_chevalleyInvolution_rootSpace]
    exact ⟨_, rightNormedBracket_positiveGenerator_mem_rootSpace R i w, rfl⟩
  rw [chevalleyInvolution_rightNormedBracket_positiveGenerator] at hmem
  exact (Submodule.smul_mem_iff _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))).1 hmem

private theorem closure_range_root_le_posRootCone {α : Module.Dual K H}
    (hα : α ∈ AddSubsemigroup.closure (Set.range R.root)) : α ∈ R.posRootCone :=
  AddSubsemigroup.closure_induction (by rintro _ ⟨i, rfl⟩; exact R.root_mem_posRootCone i)
    (fun _ _ _ _ ha hb => add_mem ha hb) hα

private theorem positiveSubalgebra_le_supportedLieSubalgebra :
    positiveSubalgebra R ≤
      supportedLieSubalgebra (rootSpace R) (AddSubsemigroup.closure (Set.range R.root)) := by
  rw [positiveSubalgebra_def, lieSpan_le]
  rintro _ ⟨i, rfl⟩
  exact le_supportedLieSubalgebra (rootSpace R)
    (AddSubsemigroup.subset_closure (Set.mem_range_self i))
    (positiveGenerator_mem_rootSpace R i)

private theorem positiveSubalgebra_toSubmodule_le_biSup_posRootCone :
    (positiveSubalgebra R).toSubmodule ≤ ⨆ α ∈ R.posRootCone, rootSpace R α := by
  refine ((LieSubalgebra.toSubmodule_le_toSubmodule _ _).2
    (positiveSubalgebra_le_supportedLieSubalgebra R)).trans ?_
  rw [supportedLieSubalgebra_toSubmodule, iSup_subtype]
  exact biSup_mono fun _ h => closure_range_root_le_posRootCone R h

private theorem negativeSubalgebra_toSubmodule_le_biSup_neg_posRootCone :
    (negativeSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | -α ∈ R.posRootCone}, rootSpace R α := by
  rw [← map_chevalleyInvolution_positiveSubalgebra, LieSubalgebra.map_toSubmodule]
  refine (Submodule.map_mono (positiveSubalgebra_toSubmodule_le_biSup_posRootCone R)).trans ?_
  rw [map_chevalleyInvolution_biSup_rootSpace R (fun α => α ∈ R.posRootCone)]
  exact biSup_mono fun _ h => h

/-- The root spaces of weights in `Q₊ ∪ (-Q₊)` span `PresentedLieAlgebra R`. -/
theorem biSup_rootSpace_posRootCone_or_neg_eq_top :
    (⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∨ -α ∈ R.posRootCone},
      rootSpace R α) = ⊤ := by
  rw [eq_top_iff, ← negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top R,
    sup_le_iff, sup_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (negativeSubalgebra_toSubmodule_le_biSup_neg_posRootCone R).trans
      (biSup_mono fun _ h => Or.inr h)
  · exact (cartanSubalgebra_toSubmodule_le_rootSpace_zero R).trans <|
      le_iSup₂_of_le (0 : Module.Dual K H) (Or.inl (zero_mem _)) le_rfl
  · exact (positiveSubalgebra_toSubmodule_le_biSup_posRootCone R).trans
      (biSup_mono fun _ h => Or.inl h)

/-- The root spaces indexed by the root lattice `R.rootLattice` span `PresentedLieAlgebra R`. -/
theorem iSup_rootSpace_rootLattice_eq_top :
    (⨆ α : R.rootLattice, rootSpace R α) = ⊤ := by
  rw [eq_top_iff, ← biSup_rootSpace_posRootCone_or_neg_eq_top R]
  refine iSup₂_le fun α hα => ?_
  have hmem : α ∈ R.rootLattice := by
    rcases hα with hpos | hneg
    · exact R.posRootCone_le_rootLattice hpos
    · simpa using R.rootLattice.neg_mem (R.posRootCone_le_rootLattice hneg)
  exact le_iSup (fun β : R.rootLattice => rootSpace R β) ⟨α, hmem⟩

/-- The root spaces indexed by `Module.Dual K H` span `PresentedLieAlgebra R`. -/
theorem iSup_rootSpace_eq_top : (⨆ α : Module.Dual K H, rootSpace R α) = ⊤ := by
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

noncomputable instance [DecidableEq (Module.Dual K H)] : GradedLieAlgebra (rootSpace R) where

noncomputable instance [DecidableEq R.rootLattice] :
    DirectSum.Decomposition (fun α : R.rootLattice => rootSpace R α) :=
  (isInternal_rootSpace_rootLattice R).chooseDecomposition

noncomputable instance [DecidableEq R.rootLattice] :
    GradedLieAlgebra (fun α : R.rootLattice => rootSpace R α) where

/-- **No mixed-sign roots**: if neither `α` nor `-α` lies in the positive root cone `Q₊`, then
`rootSpace R α = ⊥`. -/
theorem rootSpace_eq_bot_of_notMem_posRootCone_of_neg_notMem {α : Module.Dual K H}
    (hpos : α ∉ R.posRootCone) (hneg : -α ∉ R.posRootCone) : rootSpace R α = ⊥ := by
  have hd := (iSupIndep_rootSpace R).disjoint_biSup
    (x := α) (y := {β : Module.Dual K H | β ∈ R.posRootCone ∨ -β ∈ R.posRootCone})
    (by simp [hpos, hneg])
  rwa [biSup_rootSpace_posRootCone_or_neg_eq_top R, disjoint_top] at hd

/-- Any weight outside the root lattice `R.rootLattice` has zero root space. -/
theorem rootSpace_eq_bot_of_notMem_rootLattice {α : Module.Dual K H}
    (hα : α ∉ R.rootLattice) : rootSpace R α = ⊥ :=
  rootSpace_eq_bot_of_notMem_posRootCone_of_neg_notMem R
    (fun h => hα (R.posRootCone_le_rootLattice h))
    (fun h => hα (by simpa using R.rootLattice.neg_mem (R.posRootCone_le_rootLattice h)))

/-! ### Bracket-word spanning over an arbitrary field -/

/-- **Positive root spaces are spanned by bracket words.** Over any field `K`, if `-α ∉ Q₊`, then
`𝔤_α` is spanned by the right-normed brackets of raising generators whose simple-root weights sum
to `α`. Note that `-α ∉ Q₊` automatically implies `α ≠ 0` because `0 ∈ Q₊`. -/
theorem rootSpace_eq_span_rightNormedBracket_positiveGenerator
    {α : Module.Dual K H} (hneg : -α ∉ R.posRootCone) :
    rootSpace R α =
      Submodule.span K
        ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
          {p | ((p.1 :: p.2).map R.root).sum = α}) := by
  have h0 : α ≠ 0 := fun h => hneg (by rw [h, neg_zero]; exact zero_mem _)
  set Wα := Submodule.span K
    ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
      {p | ((p.1 :: p.2).map R.root).sum = α})
  set Wne := Submodule.span K
    ((fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
      {p | ((p.1 :: p.2).map R.root).sum ≠ α})
  set Z := (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔ Wne
  have hWα : Wα ≤ rootSpace R α := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, rfl, rfl⟩
    exact rightNormedBracket_positiveGenerator_mem_rootSpace R i w
  have hWne : Wne ≤ ⨆ β ∈ {β : Module.Dual K H | β ≠ α}, rootSpace R β := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, w⟩, hne, rfl⟩
    exact Submodule.mem_iSup_of_mem ((i :: w).map R.root).sum
      (Submodule.mem_iSup_of_mem hne (rightNormedBracket_positiveGenerator_mem_rootSpace R i w))
  have hZ : Z ≤ ⨆ β ∈ {β : Module.Dual K H | β ≠ α}, rootSpace R β := by
    refine sup_le (sup_le ?_ ?_) hWne
    · refine (negativeSubalgebra_toSubmodule_le_biSup_neg_posRootCone R).trans
        (biSup_mono fun β hβ => ?_)
      rintro rfl
      exact hneg hβ
    · exact (cartanSubalgebra_toSubmodule_le_rootSpace_zero R).trans
        (le_iSup₂_of_le (0 : Module.Dual K H) h0.symm le_rfl)
  have hd : Disjoint (rootSpace R α) Z :=
    ((iSupIndep_rootSpace R).disjoint_biSup
      (x := α) (y := {β : Module.Dual K H | β ≠ α}) (by simp)).mono_right hZ
  have huniv : {p : I × List I | ((p.1 :: p.2).map R.root).sum = α} ∪
      {p | ((p.1 :: p.2).map R.root).sum ≠ α} = Set.univ := by
    ext p
    simp [em]
  have hpos_eq : (positiveSubalgebra R).toSubmodule = Wα ⊔ Wne := by
    rw [← Submodule.span_union, ← Set.image_union, huniv, Set.image_univ,
      positiveSubalgebra_def, coe_lieSpan_range_eq_span_rightNormedBracket]
  refine (eq_of_le_of_inf_le_of_le_sup (z := Z) hWα ?_ ?_).symm
  · rw [hd.eq_bot]
    exact bot_le
  · have htop : Wα ⊔ Z = ⊤ := by
      have hZ_eq : Wα ⊔ Z = (negativeSubalgebra R).toSubmodule ⊔
          (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule := by
        simp only [Z, hpos_eq, sup_assoc, sup_left_comm, sup_comm]
      rw [hZ_eq, negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top]
    rw [htop]
    exact le_top

/-- **Negative root spaces are spanned by bracket words.** Over any field `K`, if `α ∉ Q₊`, then
`𝔤_α` is spanned by the right-normed brackets of lowering generators whose negated simple-root
weights sum to `α`. Note that `α ∉ Q₊` automatically implies `α ≠ 0` because `0 ∈ Q₊`. -/
theorem rootSpace_eq_span_rightNormedBracket_negativeGenerator
    {α : Module.Dual K H} (hpos : α ∉ R.posRootCone) :
    rootSpace R α =
      Submodule.span K
        ((fun p : I × List I => rightNormedBracket (negativeGenerator R) p.1 p.2) ''
          {p | -((p.1 :: p.2).map R.root).sum = α}) := by
  have heq : rootSpace R α = (rootSpace R (-α)).map (chevalleyInvolution R).toLinearMap := by
    rw [map_chevalleyInvolution_rootSpace, neg_neg]
  rw [heq, rootSpace_eq_span_rightNormedBracket_positiveGenerator R (by simpa using hpos),
    Submodule.map_span, ← Set.image_comp]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨⟨i, w⟩, hw, rfl⟩
    rw [Function.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_coe,
      chevalleyInvolution_rightNormedBracket_positiveGenerator]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span
      ⟨(i, w), neg_eq_iff_eq_neg.2 hw, rfl⟩
  · rintro _ ⟨⟨i, w⟩, hw, rfl⟩
    have hmem :
        ((chevalleyInvolution R).toLinearMap ∘
            fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) (i, w) ∈
          Submodule.span K
            (((chevalleyInvolution R).toLinearMap ∘
                fun p : I × List I => rightNormedBracket (positiveGenerator R) p.1 p.2) ''
              {p | ((p.1 :: p.2).map R.root).sum = -α}) :=
      Submodule.subset_span ⟨(i, w), neg_eq_iff_eq_neg.1 hw, rfl⟩
    rw [Function.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_coe,
      chevalleyInvolution_rightNormedBracket_positiveGenerator] at hmem
    exact (Submodule.smul_mem_iff _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))).1 hmem

/-! ## Characteristic-zero cone refinement, simple root spaces, and center -/

section CharZero

variable [CharZero K]

private theorem positiveSubalgebra_toSubmodule_le_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  refine ((LieSubalgebra.toSubmodule_le_toSubmodule _ _).2
    (positiveSubalgebra_le_supportedLieSubalgebra R)).trans ?_
  rw [supportedLieSubalgebra_toSubmodule, iSup_subtype]
  refine biSup_mono fun α hα => ⟨closure_range_root_le_posRootCone R hα, fun h0 => ?_⟩
  exact (R.root_linearIndependent.restrict_scalars' ℤ).zero_notMem_closure_range (h0 ▸ hα)

private theorem negativeSubalgebra_toSubmodule_le_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule ≤
      ⨆ α ∈ {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  rw [← map_chevalleyInvolution_positiveSubalgebra, LieSubalgebra.map_toSubmodule]
  refine (Submodule.map_mono (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R)).trans ?_
  rw [map_chevalleyInvolution_biSup_rootSpace R
    (fun α => α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0})]
  exact biSup_mono fun _ h => ⟨h.1, neg_ne_zero.1 h.2⟩

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

/-- **Zero root space.** Over a field of characteristic zero, the zero root space of
`PresentedLieAlgebra R` is the Cartan subalgebra `𝔥`. -/
@[simp]
theorem rootSpace_zero_eq :
    rootSpace R 0 = (cartanSubalgebra R).toSubmodule := by
  refine (eq_of_le_of_inf_le_of_le_sup
    (z := (negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
    (cartanSubalgebra_toSubmodule_le_rootSpace_zero R) ?_ ?_).symm
  · rw [(disjoint_negativeSubalgebra_sup_positiveSubalgebra_rootSpace_zero R).symm.eq_bot]
    exact bot_le
  · rw [sup_left_comm, ← sup_assoc,
      negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top]
    exact le_top

/-- Over a field of characteristic zero, `n⁺` is the direct sum of the root spaces of nonzero
elements of the positive root cone `Q₊`. -/
theorem positiveSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (positiveSubalgebra R).toSubmodule =
      ⨆ α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  have hab_le : (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ≤
      ⨆ α ∈ insert (0 : Module.Dual K H) {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0},
        rootSpace R α := by
    rw [iSup_insert, sup_comm]
    exact sup_le_sup (cartanSubalgebra_toSubmodule_le_rootSpace_zero R)
      (negativeSubalgebra_toSubmodule_le_biSup_rootSpace R)
  have hdisj : Disjoint
      (insert (0 : Module.Dual K H) {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0})
      {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0} :=
    Set.disjoint_insert_left.2 ⟨by simp, disjoint_negCone_posCone R⟩
  have hd := ((iSupIndep_rootSpace R).disjoint_biSup_biSup hdisj).mono_left hab_le
  refine eq_of_le_of_inf_le_of_le_sup
    (z := (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule)
    (positiveSubalgebra_toSubmodule_le_biSup_rootSpace R) ?_ ?_
  · rw [hd.symm.eq_bot]
    exact bot_le
  · rw [sup_comm, negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top]
    exact le_top

/-- Over a field of characteristic zero, `n⁻` is the direct sum of the root spaces of weights
whose negation is a nonzero element of `Q₊`. -/
theorem negativeSubalgebra_toSubmodule_eq_biSup_rootSpace :
    (negativeSubalgebra R).toSubmodule =
      ⨆ α ∈ {α : Module.Dual K H | -α ∈ R.posRootCone ∧ α ≠ 0}, rootSpace R α := by
  rw [← map_chevalleyInvolution_positiveSubalgebra, LieSubalgebra.map_toSubmodule,
    positiveSubalgebra_toSubmodule_eq_biSup_rootSpace,
    map_chevalleyInvolution_biSup_rootSpace R
      (fun α => α ∈ {α : Module.Dual K H | α ∈ R.posRootCone ∧ α ≠ 0})]
  refine le_antisymm ?_ ?_
  · exact biSup_mono fun _ h => ⟨h.1, neg_ne_zero.1 h.2⟩
  · exact biSup_mono fun _ h => ⟨h.1, neg_ne_zero.2 h.2⟩

/-! ### Simple root spaces and finite-dimensionality -/

/-- **Simple root space.** Over a field of characteristic zero, the root space of the simple root
`αᵢ` is the `K`-span of `eᵢ`. -/
theorem rootSpace_root_eq_span_singleton (i : I) :
    rootSpace R (R.root i) = K ∙ positiveGenerator R i := by
  have hneg : -R.root i ∉ R.posRootCone := fun h =>
    R.root_linearIndependent.ne_zero i (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) h)
  rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R hneg,
    image_rightNormedBracket_sum_map_eq_self (positiveGenerator R) R.root_linearIndependent i]

/-- **Negative simple root space.** Over a field of characteristic zero, the root space of `-αᵢ` is
the `K`-span of `fᵢ`. -/
theorem rootSpace_neg_root_eq_span_singleton (i : I) :
    rootSpace R (-R.root i) = K ∙ negativeGenerator R i := by
  rw [← map_chevalleyInvolution_rootSpace, rootSpace_root_eq_span_singleton, Submodule.map_span,
    Set.image_singleton, LieHom.coe_toLinearMap, LieEquiv.coe_coe,
    chevalleyInvolution_positiveGenerator, ← Set.neg_singleton, Submodule.span_neg]

/-- **Higher multiples of a simple root vanish.** Over a field of characteristic zero,
`rootSpace R (m • R.root i) = ⊥` for every `m ≥ 2`. -/
theorem rootSpace_nsmul_root_eq_bot (i : I) {m : ℕ} (hm : 2 ≤ m) :
    rootSpace R (m • R.root i) = ⊥ := by
  have h0 : m • R.root i ≠ 0 := by
    rw [← Nat.cast_smul_eq_nsmul K]
    exact smul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (R.root_linearIndependent.ne_zero i)
  have hneg : -(m • R.root i) ∉ R.posRootCone :=
    fun h => h0 (R.isPointed_posRootCone _ (nsmul_mem (R.root_mem_posRootCone i) m) h)
  rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R hneg,
    span_rightNormedBracket_sum_map_eq_nsmul (positiveGenerator R) R.root_linearIndependent i hm]

/-- Over a field of characteristic zero, `rootSpace R (-(m • R.root i)) = ⊥` for every `m ≥ 2`. -/
theorem rootSpace_neg_nsmul_root_eq_bot (i : I) {m : ℕ} (hm : 2 ≤ m) :
    rootSpace R (-(m • R.root i)) = ⊥ := by
  rw [← map_chevalleyInvolution_rootSpace, rootSpace_nsmul_root_eq_bot R i hm, Submodule.map_bot]

private theorem fg_rootSpace_of_notMem_neg {α : Module.Dual K H}
    (hneg : -α ∉ R.posRootCone) : (rootSpace R α).FG := by
  rw [rootSpace_eq_span_rightNormedBracket_positiveGenerator R hneg]
  refine Submodule.fg_span (Set.Finite.image _ ?_)
  exact (R.root_linearIndependent.finite_setOf_sum_map_eq α).preimage
    (f := fun p : I × List I => p.1 :: p.2)
    fun ⟨_, _⟩ _ ⟨_, _⟩ _ h => by simpa using h

/-- **Finite-dimensionality of root spaces of nonzero weight.** Over a field of characteristic
zero, every root space `rootSpace R α` with `α ≠ 0` is finite-dimensional, without any finiteness
assumption on `I` or `H`. -/
theorem finiteDimensional_rootSpace_of_ne_zero {α : Module.Dual K H}
    (hα : α ≠ 0) : FiniteDimensional K (rootSpace R α) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  by_cases hneg : -α ∈ R.posRootCone
  · have hpos : α ∉ R.posRootCone := fun hpos => hα (R.isPointed_posRootCone _ hpos hneg)
    have hfg : (rootSpace R (-α)).FG :=
      fg_rootSpace_of_notMem_neg R (by simpa using hpos)
    have heq : rootSpace R α = (rootSpace R (-α)).map (chevalleyInvolution R).toLinearMap := by
      rw [map_chevalleyInvolution_rootSpace, neg_neg]
    rw [heq]
    exact hfg.map _
  · exact fg_rootSpace_of_notMem_neg R hneg

/-- When `H` is finite-dimensional over a field of characteristic zero, every root space
`rootSpace R α` is finite-dimensional. -/
instance finiteDimensional_rootSpace [FiniteDimensional K H] (α : Module.Dual K H) :
    FiniteDimensional K (rootSpace R α) := by
  rcases eq_or_ne α 0 with rfl | hα
  · rw [← Submodule.fg_iff_finiteDimensional, rootSpace_zero_eq, cartanSubalgebra_toSubmodule,
      LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map (cartanElement R)
  · exact finiteDimensional_rootSpace_of_ne_zero R hα

/-! ### Simple multiplicities and center when `cartanElement` is injective -/

section CartanInjective

variable {R} (hinj : Function.Injective (cartanElement R))
include hinj

/-- **Simple root multiplicity one.** Over a field of characteristic zero, whenever
`cartanElement R` is injective (in particular for a generalized Cartan matrix via
`TauCeti.KacMoody.cartanElement_injective`), `dim 𝔤_{αᵢ} = 1`. -/
theorem finrank_rootSpace_root (i : I) : Module.finrank K (rootSpace R (R.root i)) = 1 := by
  rw [rootSpace_root_eq_span_singleton,
    finrank_span_singleton (positiveGenerator_ne_zero_of_injective hinj i)]

/-- **Negative simple root multiplicity one.** Over a field of characteristic zero, whenever
`cartanElement R` is injective, `dim 𝔤_{-αᵢ} = 1`. -/
theorem finrank_rootSpace_neg_root (i : I) : Module.finrank K (rootSpace R (-R.root i)) = 1 := by
  rw [rootSpace_neg_root_eq_span_singleton,
    finrank_span_singleton (negativeGenerator_ne_zero_of_injective hinj i)]

/-- **Center of a Kac–Moody Lie algebra (Kac, Proposition 1.6).** Over a field of characteristic
zero, whenever `cartanElement R` is injective (in particular for a generalized Cartan matrix), the
center of `PresentedLieAlgebra R` is the image of `R.cartanCenter = {x ∈ H | ∀ i, αᵢ(x) = 0}` under
`cartanElement R`. -/
theorem center_toSubmodule_eq_map_cartanCenter :
    (LieAlgebra.center K (PresentedLieAlgebra R)).toSubmodule =
      R.cartanCenter.map (cartanElement R) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · have hz0 : z ∈ rootSpace R 0 := (mem_rootSpace_iff R).2 fun x => by
      rw [LinearMap.zero_apply, zero_smul, ← lie_skew]
      simp [(LieModule.mem_maxTrivSubmodule K _ _ z).1 hz (cartanElement R x)]
    rw [rootSpace_zero_eq, cartanSubalgebra_toSubmodule] at hz0
    obtain ⟨x, rfl⟩ := hz0
    exact ⟨x, (cartanElement_mem_center_iff hinj).1 hz, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact cartanElement_mem_center R hx

/-- The canonical linear isomorphism `R.cartanCenter ≃ₗ[K] LieAlgebra.center K 𝔤(R)` induced by
`cartanElement R` whenever `cartanElement R` is injective over a field of characteristic zero (in
particular for a generalized Cartan matrix). -/
noncomputable def cartanCenterEquiv :
    R.cartanCenter ≃ₗ[K] LieAlgebra.center K (PresentedLieAlgebra R) :=
  (Submodule.equivMapOfInjective (cartanElement R) hinj R.cartanCenter).trans
    (LinearEquiv.ofEq _ _ (center_toSubmodule_eq_map_cartanCenter hinj).symm)

/-- Coercing `TauCeti.KacMoody.cartanCenterEquiv` to the ambient Lie algebra gives
`TauCeti.KacMoody.cartanElement`. -/
@[simp] theorem coe_cartanCenterEquiv_apply (x : R.cartanCenter) :
    (cartanCenterEquiv hinj x : PresentedLieAlgebra R) = cartanElement R x := by
  rw [cartanCenterEquiv, LinearEquiv.trans_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans
    (Submodule.coe_equivMapOfInjective_apply (cartanElement R) _ R.cartanCenter x)

/-- Evaluating `TauCeti.KacMoody.cartanElement` on the inverse of
`TauCeti.KacMoody.cartanCenterEquiv` recovers the central Lie algebra element. -/
@[simp] theorem cartanElement_cartanCenterEquiv_symm
    (z : LieAlgebra.center K (PresentedLieAlgebra R)) :
    cartanElement R ((cartanCenterEquiv hinj).symm z) = z := by
  conv_rhs =>
    rw [← (cartanCenterEquiv hinj).apply_symm_apply z, coe_cartanCenterEquiv_apply]

/-- The inverse of `TauCeti.KacMoody.cartanCenterEquiv` recovers `x` from a central
`cartanElement R x`. -/
@[simp] theorem cartanCenterEquiv_symm_cartanElement {x : H}
    (hz : cartanElement R x ∈ LieAlgebra.center K (PresentedLieAlgebra R)) :
    (cartanCenterEquiv hinj).symm ⟨cartanElement R x, hz⟩ =
      ⟨x, (cartanElement_mem_center_iff hinj).1 hz⟩ := by
  apply (cartanCenterEquiv hinj).injective; ext; simp

/-- Over a field of characteristic zero, whenever `cartanElement R` is injective, the center of
`PresentedLieAlgebra R` is trivial if and only if `R.cartanCenter = ⊥`. -/
theorem center_eq_bot_iff :
    LieAlgebra.center K (PresentedLieAlgebra R) = ⊥ ↔ R.cartanCenter = ⊥ := by
  rw [← LieSubmodule.toSubmodule_eq_bot, center_toSubmodule_eq_map_cartanCenter hinj]
  refine ⟨fun h => (Submodule.eq_bot_iff _).2 fun x hx => ?_, fun h => by simp [h]⟩
  exact hinj <| ((Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩).trans (map_zero _).symm

end CartanInjective

end CharZero

end KacMoody

end TauCeti
