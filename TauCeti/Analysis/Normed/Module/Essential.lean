/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Operator.Restrict
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Algebra.Module.Span
import TauCeti.Topology.ApproximateUnit

/-!
# Bounded approximate identities on essential modules

Let `A` be a possibly nonunital normed algebra acting on a seminormed space `E` on the left through
a bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`, or on the right
through `R : A →L[𝕜] E →L[𝕜] E` with `R (a * b) x = R b (R a x)`. A left approximate identity of
`A` is a filter `l` on `A` with `e * a → a` along `l` for every `a`, and a right approximate
identity satisfies `a * e → a`; it is bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential submodule* of a bounded action `M : A →L[𝕜] E →L[𝕜] E` is the closed linear span
`ContinuousLinearMap.essentialSubmodule M = closure (span (M · ·))`; for a bimodule `(L, R)` the
two-sided essential submodule is the closed linear span
`ContinuousLinearMap.essentialBimoduleSubmodule L R = closure (span (A · E · A))`.
This file proves:

* invariance of `M.essentialSubmodule` under any commuting bounded action, symmetry of
  `essentialBimoduleSubmodule` under commuting actions, invariance under both `L` and `R`, and
  preservation under precomposition with surjective maps;
* that an eventually norm-bounded filter converging to the identity on generators `M a w`
  converges to the identity on `M.essentialSubmodule`, and that pointwise convergence along a proper
  filter implies membership in `M.essentialSubmodule` (and essentiality of a restricted action);
* that a bounded one-sided approximate identity converges to the identity pointwise on the
  corresponding essential submodule, that for a proper filter the essential submodule consists
  exactly of the points where it does, and that restricting an action to an invariant submodule
  inside its essential submodule produces an essential restricted action;
* that in the presence of a bounded left or right approximate identity,
  `essentialBimoduleSubmodule L R` equals `L.essentialSubmodule ⊓ R.essentialSubmodule`.

## Main definitions

* `ContinuousLinearMap.essentialSubmodule`: the closed linear span of `M · ·` for a bounded
  bilinear action `M`.
* `ContinuousLinearMap.essentialBimoduleSubmodule`: the closed linear span of `A · E · A` for a
  bounded bimodule `(L, R)`.

## Main results

* `ContinuousLinearMap.essentialSubmodule_le_iff` and
  `ContinuousLinearMap.essentialBimoduleSubmodule_le_iff`: universal properties of
  `essentialSubmodule` and `essentialBimoduleSubmodule`.
* `ContinuousLinearMap.apply_mem_essentialSubmodule` and
  `ContinuousLinearMap.apply_mem_essentialSubmodule_of_comm`: invariance of `M.essentialSubmodule`
  under `M` and under any commuting bounded bilinear action.
* `ContinuousLinearMap.apply_left_apply_right_mem_essentialBimoduleSubmodule`,
  `ContinuousLinearMap.apply_left_mem_essentialBimoduleSubmodule`,
  `ContinuousLinearMap.apply_right_mem_essentialBimoduleSubmodule`,
  `ContinuousLinearMap.apply_left_mem_essentialBimoduleSubmodule_of_mem_right`,
  `ContinuousLinearMap.apply_right_mem_essentialBimoduleSubmodule_of_mem_left`, and
  `ContinuousLinearMap.exists_continuousLinearMap_restrictAction_essentialBimoduleSubmodule`:
  generator membership, invariance, one-sided-to-two-sided entry, and embedding of the
  right-essential part of `L.essentialSubmodule` into `essentialBimoduleSubmodule L R`.
* `ContinuousLinearMap.tendsto_apply_of_mem_essentialSubmodule_of_tendsto_apply`,
  `ContinuousLinearMap.mem_essentialSubmodule_of_tendsto_apply`, and
  `ContinuousLinearMap.essentialSubmodule_restrictAction_eq_top_of_tendsto`: generator-to-closure
  convergence, limit-to-membership, and restriction essentiality without multiplication on `A`.
* `ContinuousLinearMap.tendsto_apply_of_mem_essentialSubmodule` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_essentialSubmodule`: convergence and characterization
  on the left essential submodule.
* `ContinuousLinearMap.tendsto_apply_of_mem_essentialSubmodule_right` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_essentialSubmodule_right`: convergence and
  characterization on the right essential submodule.
* `ContinuousLinearMap.essentialSubmodule_restrictAction_eq_top` and
  `ContinuousLinearMap.essentialSubmodule_restrictAction_eq_top_right`: restricted actions on
  invariant submodules of the essential part are essential.
* `ContinuousLinearMap.essentialBimoduleSubmodule_eq_inf_of_tendsto_mul_left` and
  `ContinuousLinearMap.essentialBimoduleSubmodule_eq_inf_of_tendsto_mul_right`: with a bounded
  right or left approximate identity,
  `essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓ R.essentialSubmodule`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.1.5.
-/

public section

open Filter Topology Submodule

namespace ContinuousLinearMap

section CompUnop

variable {𝕜 A E : Type*} [Semiring 𝕜]
  [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Precomposition of a continuous linear map `M : A →L[𝕜] E` with `MulOpposite.unop`. -/
def compUnop (M : A →L[𝕜] E) : Aᵐᵒᵖ →L[𝕜] E :=
  M.comp (MulOpposite.opContinuousLinearEquiv 𝕜 (M := A)).symm.toContinuousLinearMap

/-- Applying `M.compUnop` to `a : Aᵐᵒᵖ` evaluates `M` at `a.unop`. -/
@[simp]
theorem compUnop_apply (M : A →L[𝕜] E) (a : Aᵐᵒᵖ) : M.compUnop a = M a.unop := by
  unfold compUnop
  rfl

end CompUnop

section EssentialSubmodule

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The essential submodule of a bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E`, defined as the
closed linear span of `{M a x | a : A, x : E}`. -/
def essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) : Submodule 𝕜 E :=
  (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure

/-- Unfolding lemma for `ContinuousLinearMap.essentialSubmodule`. -/
theorem essentialSubmodule_eq_topologicalClosure_span (M : A →L[𝕜] E →L[𝕜] E) :
    M.essentialSubmodule = (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure := by
  unfold essentialSubmodule
  rfl

/-- The essential submodule of a bounded action is closed. -/
theorem isClosed_essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) :
    IsClosed (M.essentialSubmodule : Set E) :=
  isClosed_topologicalClosure _

/-- Every image `M a x` lies in `M.essentialSubmodule`. -/
@[simp]
theorem apply_mem_essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) (a : A) (x : E) :
    M a x ∈ M.essentialSubmodule :=
  le_topologicalClosure _ (subset_span ⟨(a, x), rfl⟩)

/-- `M.essentialSubmodule` is the least closed submodule containing every action value `M a x`. -/
theorem essentialSubmodule_le_iff {M : A →L[𝕜] E →L[𝕜] E} {p : Submodule 𝕜 E}
    (hp : IsClosed (p : Set E)) :
    M.essentialSubmodule ≤ p ↔ ∀ a x, M a x ∈ p :=
  ⟨fun h a x ↦ h (apply_mem_essentialSubmodule M a x), fun h ↦ by
    rw [essentialSubmodule_eq_topologicalClosure_span]
    exact topologicalClosure_minimal _ (span_le.2 (by rintro _ ⟨⟨a, x⟩, rfl⟩; exact h a x)) hp⟩

/-- If two bounded bilinear actions `M` and `N` commute (`M a (N b x) = N b (M a x)`), then `N b`
leaves `M.essentialSubmodule` invariant. -/
theorem apply_mem_essentialSubmodule_of_comm {M N : A →L[𝕜] E →L[𝕜] E}
    (hMN : ∀ a b x, M a (N b x) = N b (M a x)) (b : A) {x : E}
    (hx : x ∈ M.essentialSubmodule) :
    N b x ∈ M.essentialSubmodule :=
  (essentialSubmodule_le_iff (p := M.essentialSubmodule.comap (N b).toLinearMap)
    ((isClosed_essentialSubmodule M).preimage (N b).continuous)).2
    (fun a y ↦ by
      change N b (M a y) ∈ M.essentialSubmodule
      rw [← hMN]
      exact apply_mem_essentialSubmodule M a (N b y))
    hx

/-- The two-sided essential submodule of a bounded bimodule `(L, R)`, defined as the closed linear
span of `{L a (R b x) | a b : A, x : E}`. -/
def essentialBimoduleSubmodule (L R : A →L[𝕜] E →L[𝕜] E) : Submodule 𝕜 E :=
  (span 𝕜 (Set.range fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2))).topologicalClosure

/-- Unfolding lemma for `ContinuousLinearMap.essentialBimoduleSubmodule`. -/
theorem essentialBimoduleSubmodule_eq_topologicalClosure_span (L R : A →L[𝕜] E →L[𝕜] E) :
    essentialBimoduleSubmodule L R =
      (span 𝕜 (Set.range fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2))).topologicalClosure := by
  unfold essentialBimoduleSubmodule
  rfl

/-- The two-sided essential submodule of a bounded bimodule is closed. -/
theorem isClosed_essentialBimoduleSubmodule (L R : A →L[𝕜] E →L[𝕜] E) :
    IsClosed (essentialBimoduleSubmodule L R : Set E) :=
  isClosed_topologicalClosure _

/-- Every double action value `L a (R b x)` lies in `essentialBimoduleSubmodule L R`. -/
@[simp]
theorem apply_left_apply_right_mem_essentialBimoduleSubmodule (L R : A →L[𝕜] E →L[𝕜] E)
    (a b : A) (x : E) :
    L a (R b x) ∈ essentialBimoduleSubmodule L R :=
  le_topologicalClosure _ (subset_span ⟨(a, b, x), rfl⟩)

/-- `essentialBimoduleSubmodule L R` is the least closed submodule containing every double action
value `L a (R b x)`. -/
theorem essentialBimoduleSubmodule_le_iff {L R : A →L[𝕜] E →L[𝕜] E} {p : Submodule 𝕜 E}
    (hp : IsClosed (p : Set E)) :
    essentialBimoduleSubmodule L R ≤ p ↔ ∀ a b x, L a (R b x) ∈ p :=
  ⟨fun h a b x ↦ h (apply_left_apply_right_mem_essentialBimoduleSubmodule L R a b x), fun h ↦ by
    rw [essentialBimoduleSubmodule_eq_topologicalClosure_span]
    exact topologicalClosure_minimal _
      (span_le.2 (by rintro _ ⟨⟨a, b, x⟩, rfl⟩; exact h a b x)) hp⟩

/-- When two bounded actions commute, swapping them does not change the two-sided essential
submodule. -/
theorem essentialBimoduleSubmodule_comm {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    essentialBimoduleSubmodule L R = essentialBimoduleSubmodule R L := by
  refine le_antisymm ?_ ?_
  · exact (essentialBimoduleSubmodule_le_iff (isClosed_essentialBimoduleSubmodule R L)).2
      fun a b x ↦ by
        rw [hLR]
        exact apply_left_apply_right_mem_essentialBimoduleSubmodule R L b a x
  · exact (essentialBimoduleSubmodule_le_iff (isClosed_essentialBimoduleSubmodule L R)).2
      fun a b x ↦ by
        rw [← hLR]
        exact apply_left_apply_right_mem_essentialBimoduleSubmodule L R b a x

/-- Precomposing an action with a surjective bounded linear map preserves its essential
submodule. -/
theorem essentialSubmodule_comp_of_surjective {B : Type*} [SeminormedAddCommGroup B]
    [NormedSpace 𝕜 B] (M : A →L[𝕜] E →L[𝕜] E) {f : B →L[𝕜] A} (hf : Function.Surjective f) :
    (M.comp f).essentialSubmodule = M.essentialSubmodule := by
  have hset : Set.range (fun p : B × E ↦ (M.comp f) p.1 p.2) =
      Set.range fun p : A × E ↦ M p.1 p.2 :=
    (hf.prodMap Function.surjective_id).range_comp (fun p : A × E ↦ M p.1 p.2)
  simp only [essentialSubmodule_eq_topologicalClosure_span, hset]

/-- Precomposing two actions with a surjective bounded linear map preserves their two-sided
essential submodule. -/
theorem essentialBimoduleSubmodule_comp_of_surjective {B : Type*} [SeminormedAddCommGroup B]
    [NormedSpace 𝕜 B] (L R : A →L[𝕜] E →L[𝕜] E) {f : B →L[𝕜] A} (hf : Function.Surjective f) :
    essentialBimoduleSubmodule (L.comp f) (R.comp f) = essentialBimoduleSubmodule L R := by
  have hset : Set.range (fun p : B × B × E ↦ (L.comp f) p.1 ((R.comp f) p.2.1 p.2.2)) =
      Set.range fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2) :=
    (hf.prodMap (hf.prodMap Function.surjective_id)).range_comp
      (fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2))
  simp only [essentialBimoduleSubmodule_eq_topologicalClosure_span, hset]

/-- Precomposing an action with `MulOpposite.unop` preserves its essential submodule. -/
@[simp]
theorem essentialSubmodule_compUnop (M : A →L[𝕜] E →L[𝕜] E) :
    M.compUnop.essentialSubmodule = M.essentialSubmodule :=
  essentialSubmodule_comp_of_surjective M MulOpposite.unop_surjective

/-- Precomposing two actions with `MulOpposite.unop` preserves their two-sided essential
submodule. -/
@[simp]
theorem essentialBimoduleSubmodule_compUnop (L R : A →L[𝕜] E →L[𝕜] E) :
    essentialBimoduleSubmodule L.compUnop R.compUnop = essentialBimoduleSubmodule L R :=
  essentialBimoduleSubmodule_comp_of_surjective L R MulOpposite.unop_surjective

/-- The two-sided essential submodule is contained in the left essential submodule. -/
theorem essentialBimoduleSubmodule_le_left (L R : A →L[𝕜] E →L[𝕜] E) :
    essentialBimoduleSubmodule L R ≤ L.essentialSubmodule :=
  (essentialBimoduleSubmodule_le_iff (isClosed_essentialSubmodule L)).2 fun a b x ↦
    apply_mem_essentialSubmodule L a (R b x)

/-- The two-sided essential submodule is contained in the right essential submodule when the actions
commute. -/
theorem essentialBimoduleSubmodule_le_right {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    essentialBimoduleSubmodule L R ≤ R.essentialSubmodule :=
  (essentialBimoduleSubmodule_le_iff (isClosed_essentialSubmodule R)).2 fun a b x ↦ by
    rw [hLR]
    exact apply_mem_essentialSubmodule R b (L a x)

/-- The two-sided essential submodule is invariant under the left action `L`. -/
theorem apply_left_mem_essentialBimoduleSubmodule [Mul A] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (a : A) {x : E}
    (hx : x ∈ essentialBimoduleSubmodule L R) :
    L a x ∈ essentialBimoduleSubmodule L R :=
  (essentialBimoduleSubmodule_le_iff
      (p := (essentialBimoduleSubmodule L R).comap (L a).toLinearMap)
      ((isClosed_essentialBimoduleSubmodule L R).preimage (L a).continuous)).2
    (fun b c y ↦ by
      change L a (L b (R c y)) ∈ essentialBimoduleSubmodule L R
      rw [← hL]
      exact apply_left_apply_right_mem_essentialBimoduleSubmodule L R (a * b) c y)
    hx

/-- The two-sided essential submodule is invariant under the right action `R`. -/
theorem apply_right_mem_essentialBimoduleSubmodule [Mul A] {L R : A →L[𝕜] E →L[𝕜] E}
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (a : A) {x : E} (hx : x ∈ essentialBimoduleSubmodule L R) :
    R a x ∈ essentialBimoduleSubmodule L R :=
  (essentialBimoduleSubmodule_le_iff
      (p := (essentialBimoduleSubmodule L R).comap (R a).toLinearMap)
      ((isClosed_essentialBimoduleSubmodule L R).preimage (R a).continuous)).2
    (fun b c y ↦ by
      change R a (L b (R c y)) ∈ essentialBimoduleSubmodule L R
      rw [← hLR, ← hR]
      exact apply_left_apply_right_mem_essentialBimoduleSubmodule L R b (c * a) y)
    hx

/-- Applying the left action `L a` to an element of `R.essentialSubmodule` lands in the two-sided
essential submodule `essentialBimoduleSubmodule L R`. -/
theorem apply_left_mem_essentialBimoduleSubmodule_of_mem_right {L R : A →L[𝕜] E →L[𝕜] E}
    (a : A) {x : E} (hx : x ∈ R.essentialSubmodule) :
    L a x ∈ essentialBimoduleSubmodule L R :=
  (essentialSubmodule_le_iff
      (p := (essentialBimoduleSubmodule L R).comap (L a).toLinearMap)
      ((isClosed_essentialBimoduleSubmodule L R).preimage (L a).continuous)).2
    (fun b z ↦ apply_left_apply_right_mem_essentialBimoduleSubmodule L R a b z)
    hx

/-- If `L` and `R` commute, applying the right action `R b` to an element of `L.essentialSubmodule`
lands in the two-sided essential submodule `essentialBimoduleSubmodule L R`. -/
theorem apply_right_mem_essentialBimoduleSubmodule_of_mem_left {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (b : A) {y : E} (hy : y ∈ L.essentialSubmodule) :
    R b y ∈ essentialBimoduleSubmodule L R := by
  rw [essentialBimoduleSubmodule_comm hLR]
  exact apply_left_mem_essentialBimoduleSubmodule_of_mem_right b hy

/-- The right-essential submodule of `L.essentialSubmodule` embeds continuously into
`essentialBimoduleSubmodule L R` and intertwines both the left and right restricted actions. -/
theorem exists_continuousLinearMap_restrictAction_essentialBimoduleSubmodule
    [Mul A] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    ∃ ι : (R.restrictAction L.essentialSubmodule fun a _ hx ↦
          apply_mem_essentialSubmodule_of_comm hLR a hx).essentialSubmodule →L[𝕜]
        essentialBimoduleSubmodule L R,
      (∀ x, (ι x : E) = ((x : L.essentialSubmodule) : E)) ∧
      (∀ a x,
        ι ((R.restrictAction L.essentialSubmodule fun a _ hx ↦
            apply_mem_essentialSubmodule_of_comm hLR a hx).restrictAction _
            (fun a y _ ↦ apply_mem_essentialSubmodule _ a y) a x) =
          R.restrictAction (essentialBimoduleSubmodule L R)
            (fun a _ hx ↦ apply_right_mem_essentialBimoduleSubmodule hR hLR a hx) a (ι x)) ∧
      (∀ a x,
        ι ((L.restrictAction L.essentialSubmodule fun a x _ ↦
            apply_mem_essentialSubmodule L a x).restrictAction _
            (fun a _ hy ↦ apply_mem_essentialSubmodule_of_comm
              (fun b c y ↦ (restrictAction_apply_comm hLR L.essentialSubmodule
                (fun a x _ ↦ apply_mem_essentialSubmodule L a x)
                (fun a _ hx ↦ apply_mem_essentialSubmodule_of_comm hLR a hx)
                c b y).symm) a hy) a x) =
          L.restrictAction (essentialBimoduleSubmodule L R)
            (fun a _ hx ↦ apply_left_mem_essentialBimoduleSubmodule hL a hx) a (ι x)) := by
  let EL := L.essentialSubmodule
  have hLL_inv : ∀ a, ∀ x ∈ EL, L a x ∈ EL := fun a x _ ↦ apply_mem_essentialSubmodule L a x
  have hRL_inv : ∀ a, ∀ x ∈ EL, R a x ∈ EL :=
    fun a _ hx ↦ apply_mem_essentialSubmodule_of_comm hLR a hx
  let RL := R.restrictAction EL hRL_inv
  let ELR := RL.essentialSubmodule
  have hELR_mem (x : ELR) :
      (EL.subtypeL.comp ELR.subtypeL) x ∈ essentialBimoduleSubmodule L R :=
    (essentialSubmodule_le_iff (M := RL) (p := (essentialBimoduleSubmodule L R).comap EL.subtype)
      ((isClosed_essentialBimoduleSubmodule L R).preimage continuous_subtypeVal)).2
      (fun a y ↦ by
        simpa [RL, coe_restrictAction_apply] using
          apply_right_mem_essentialBimoduleSubmodule_of_mem_left hLR a y.property)
      x.property
  let ι : ELR →L[𝕜] essentialBimoduleSubmodule L R :=
    (EL.subtypeL.comp ELR.subtypeL).codRestrict (essentialBimoduleSubmodule L R) hELR_mem
  have hι_coe (x : ELR) : (ι x : E) = ((x : EL) : E) := by
    simp only [ι, coe_codRestrict_apply, comp_apply, Submodule.subtypeL_apply]
  refine ⟨ι, hι_coe, fun a x ↦ ?_, fun a x ↦ ?_⟩
  · exact restrictAction_intertwine EL.subtype hι_coe
      (fun y ↦ coe_restrictAction_apply R EL hRL_inv a y) x
  · exact restrictAction_intertwine EL.subtype hι_coe
      (fun y ↦ coe_restrictAction_apply L EL hLL_inv a y) x

/-- If an eventually norm-bounded filter `l` acts as the identity in the limit on every generator
`M a w`, then it converges pointwise to the identity on the entire essential submodule
`M.essentialSubmodule`. -/
theorem tendsto_apply_of_mem_essentialSubmodule_of_tendsto_apply (M : A →L[𝕜] E →L[𝕜] E)
    {l : Filter A} {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hgen : ∀ a w, Tendsto (fun e ↦ M e (M a w)) l (𝓝 (M a w))) {z : E}
    (hz : z ∈ M.essentialSubmodule) :
    Tendsto (fun e ↦ M e z) l (𝓝 z) := by
  have hd : Dense (span 𝕜 (Set.range fun p : A × E ↦
      (⟨M p.1 p.2, apply_mem_essentialSubmodule M p.1 p.2⟩ : M.essentialSubmodule)) :
      Set M.essentialSubmodule) :=
    TauCeti.dense_span_in_topologicalClosure (fun p : A × E ↦ M p.1 p.2)
  have hbound : ∀ᶠ e in l, ‖M e ∘L M.essentialSubmodule.subtypeL‖ ≤ ‖M‖ * C :=
    hC.mono fun e he ↦ (opNorm_comp_le (M e) M.essentialSubmodule.subtypeL).trans <|
      (mul_le_of_le_one_right (norm_nonneg _)
        M.essentialSubmodule.norm_subtypeL_le).trans <|
        (M.le_opNorm e).trans (mul_le_mul_of_nonneg_left he (norm_nonneg M))
  have htendsto : ∀ x ∈ (span 𝕜 (Set.range fun p : A × E ↦
        (⟨M p.1 p.2, apply_mem_essentialSubmodule M p.1 p.2⟩ : M.essentialSubmodule)) :
        Set M.essentialSubmodule),
      Tendsto (fun e ↦ (M e ∘L M.essentialSubmodule.subtypeL) x) l
        (𝓝 (M.essentialSubmodule.subtypeL x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨⟨a, w⟩, rfl⟩ := h
      exact hgen a w
    | zero => simpa using tendsto_const_nhds
    | add _ _ _ _ hu hv => simpa using hu.add hv
    | smul c _ _ hu => simpa using hu.const_smul c
  exact tendsto_apply_of_dense hd hbound htendsto ⟨z, hz⟩

/-- If `M e z → z` along a proper filter `l`, then `z` lies in `M.essentialSubmodule`. -/
theorem mem_essentialSubmodule_of_tendsto_apply (M : A →L[𝕜] E →L[𝕜] E)
    {l : Filter A} [l.NeBot] {z : E} (h : Tendsto (fun e ↦ M e z) l (𝓝 z)) :
    z ∈ M.essentialSubmodule :=
  (isClosed_essentialSubmodule M).mem_of_tendsto h <| .of_forall fun e ↦
    apply_mem_essentialSubmodule M e z

/-- If `M e x → x` along a proper filter `l` for every `x` in an `M`-invariant submodule `p`,
then the restricted action `M.restrictAction p hMp` is essential. -/
theorem essentialSubmodule_restrictAction_eq_top_of_tendsto (M : A →L[𝕜] E →L[𝕜] E)
    {l : Filter A} [l.NeBot] (p : Submodule 𝕜 E) (hMp : ∀ a x, x ∈ p → M a x ∈ p)
    (htendsto : ∀ x ∈ p, Tendsto (fun e ↦ M e x) l (𝓝 x)) :
    (M.restrictAction p hMp).essentialSubmodule = ⊤ :=
  eq_top_iff.2 fun x _ ↦ mem_essentialSubmodule_of_tendsto_apply (M.restrictAction p hMp) <|
    tendsto_subtype_rng.2 <| (htendsto x x.property).congr fun e ↦
      (coe_restrictAction_apply M p hMp e x).symm

end EssentialSubmodule

section ApproximateIdentity

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A bounded left approximate identity of `A` converges to the identity at every point of
`L.essentialSubmodule`. -/
theorem tendsto_apply_of_mem_essentialSubmodule (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ L.essentialSubmodule) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) :=
  tendsto_apply_of_mem_essentialSubmodule_of_tendsto_apply L hC
    (fun a w ↦ by simpa [Function.comp_def, hL] using ((L.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- For a proper bounded left approximate identity, `L.essentialSubmodule` consists exactly of the
points at which it converges to the identity. -/
theorem tendsto_apply_iff_mem_essentialSubmodule (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔ z ∈ L.essentialSubmodule :=
  ⟨mem_essentialSubmodule_of_tendsto_apply L, tendsto_apply_of_mem_essentialSubmodule L hL hC hl⟩

/-- A bounded right approximate identity of `A` converges to the identity at every point of
`R.essentialSubmodule`. -/
theorem tendsto_apply_of_mem_essentialSubmodule_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E}
    (hz : z ∈ R.essentialSubmodule) :
    Tendsto (fun e ↦ R e z) l (𝓝 z) :=
  tendsto_apply_of_mem_essentialSubmodule_of_tendsto_apply R hC
    (fun a w ↦ by simpa [Function.comp_def, hR] using ((R.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- For a proper bounded right approximate identity, `R.essentialSubmodule` consists exactly of the
points at which it converges to the identity. -/
theorem tendsto_apply_iff_mem_essentialSubmodule_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ R e z) l (𝓝 z) ↔ z ∈ R.essentialSubmodule :=
  ⟨mem_essentialSubmodule_of_tendsto_apply R,
    tendsto_apply_of_mem_essentialSubmodule_right R hR hC hl⟩

/-- Restricting a left action `L` to an `L`-invariant submodule `p ≤ L.essentialSubmodule` yields
an essential left action when `A` has a bounded left approximate identity. -/
theorem essentialSubmodule_restrictAction_eq_top (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a))
    (p : Submodule 𝕜 E) (hp : p ≤ L.essentialSubmodule)
    (hLp : ∀ a x, x ∈ p → L a x ∈ p) :
    (L.restrictAction p hLp).essentialSubmodule = ⊤ :=
  essentialSubmodule_restrictAction_eq_top_of_tendsto L p hLp fun _ hx ↦
    tendsto_apply_of_mem_essentialSubmodule L hL hC hl (hp hx)

/-- Restricting a right action `R` to an `R`-invariant submodule `p ≤ R.essentialSubmodule` yields
an essential right action when `A` has a bounded right approximate identity. -/
theorem essentialSubmodule_restrictAction_eq_top_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a))
    (p : Submodule 𝕜 E) (hp : p ≤ R.essentialSubmodule)
    (hRp : ∀ a x, x ∈ p → R a x ∈ p) :
    (R.restrictAction p hRp).essentialSubmodule = ⊤ :=
  essentialSubmodule_restrictAction_eq_top_of_tendsto R p hRp fun _ hx ↦
    tendsto_apply_of_mem_essentialSubmodule_right R hR hC hl (hp hx)

/-- In a bounded bimodule over a normed algebra with a bounded right approximate identity, the
two-sided essential submodule `essentialBimoduleSubmodule L R` equals the intersection
`L.essentialSubmodule ⊓ R.essentialSubmodule`. -/
theorem essentialBimoduleSubmodule_eq_inf_of_tendsto_mul_left
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓ R.essentialSubmodule := by
  refine le_antisymm
    (le_inf (essentialBimoduleSubmodule_le_left L R) (essentialBimoduleSubmodule_le_right hLR))
    fun x hx ↦ (isClosed_essentialBimoduleSubmodule L R).mem_of_tendsto
      (tendsto_apply_of_mem_essentialSubmodule_right R hR hC hl hx.2)
      (.of_forall fun e ↦ apply_right_mem_essentialBimoduleSubmodule_of_mem_left hLR e hx.1)

/-- In a bounded bimodule over a normed algebra with a bounded left approximate identity, the
two-sided essential submodule `essentialBimoduleSubmodule L R` equals the intersection
`L.essentialSubmodule ⊓ R.essentialSubmodule`. -/
theorem essentialBimoduleSubmodule_eq_inf_of_tendsto_mul_right
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓ R.essentialSubmodule := by
  let Lop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := L.compUnop
  let Rop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := R.compUnop
  have hLop : ∀ a b x, Lop (a * b) x = Lop b (Lop a x) := fun a b x ↦ by
    simp [Lop, hL]
  have hRLop : ∀ a b x, Rop a (Lop b x) = Lop b (Rop a x) := fun a b x ↦ by
    simp only [Rop, Lop, compUnop_apply]
    exact (hLR b.unop a.unop x).symm
  have h := essentialBimoduleSubmodule_eq_inf_of_tendsto_mul_left (l := l.map MulOpposite.op)
    hLop hRLop (Filter.eventually_map.2 hC) (TauCeti.tendsto_mul_left_map_op hl)
  rwa [essentialBimoduleSubmodule_compUnop, ← essentialBimoduleSubmodule_comm hLR,
    essentialSubmodule_compUnop, essentialSubmodule_compUnop, inf_comm] at h

end ApproximateIdentity

end ContinuousLinearMap
