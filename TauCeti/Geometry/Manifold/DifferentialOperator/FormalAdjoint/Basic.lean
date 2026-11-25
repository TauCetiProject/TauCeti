/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Inner
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Formal adjoints of operators between sections of Riemannian bundles

Let `V` and `W` be real vector bundles over a manifold `M` whose fibres carry inner products, and
let `μ` be a measure on `M`. A linear operator `Q : Γ(W) → Γ(V)` between smooth sections is a
*formal adjoint* of `P : Γ(V) → Γ(W)` with respect to `μ` (`LinearMap.IsFormalAdjoint`) when

`∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ`

for all smooth sections `s` and `t` one of which has compact support. This is the operator through
which `P` acts on distributional sections and on the `L²` sections of the two bundles; it depends
on the fibre metrics and on the density `μ`. For operators on real-valued functions the analogous
notion is the formal transpose `LinearMap.IsFormalTranspose`.

For a continuous Riemannian bundle and a locally finite measure that is positive on open sets of a
Hausdorff σ-compact manifold, formal adjoints are unique (`LinearMap.IsFormalAdjoint.unique`), by
the fundamental lemma for sections (`ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero`).
`LinearMap.formalAdjoint` picks the formal adjoint when there is one.

Formal adjoints of operators that do not enlarge supports reverse compositions; differential
operators between sections, in Grothendieck's sense (`TauCeti.differentialOperators`), are such
operators. Multiplication by a smooth function is its own formal adjoint, so the formal adjoint
of a commutator `[P, a]` is `-[Q, a]`. Hence a formal adjoint of a differential operator of order
at most `m` that does not enlarge supports is a differential operator of order at most `m`: its
`(m + 1)`-fold commutators are formal adjoints of zero, hence zero by uniqueness. No continuity of
the operators is assumed anywhere.

For operators of order zero, which are `C^∞(M)`-linear, formal adjunction is pointwise: if `Q` is a
formal adjoint of such a `P`, then `⟪P s x, t x⟫ = ⟪s x, Q t x⟫` at every point. Indeed
`∫ φ (⟪P s, t⟫ - ⟪s, Q t⟫) dμ` is the integration by parts identity for `φ s`, hence zero, for
every compactly supported smooth function `φ`.

## Main definitions

* `LinearMap.IsFormalAdjoint P Q μ`: `Q` is a formal adjoint of `P` with respect to `μ`.
* `LinearMap.formalAdjoint P μ`: the formal adjoint of `P`, if it has one, and `0` otherwise.

## Main results

* `LinearMap.IsFormalAdjoint.symm`, `.comp`, `.add`, `.sub`, `.smul`, `.neg`: the algebra of
  formal adjoints; compositions and sums need operators that do not enlarge supports.
* `LinearMap.isFormalAdjoint_of_forall_inner_eq`: a pointwise adjoint, such as the fibrewise
  adjoint of a bundle map, is a formal adjoint for every measure; in particular multiplication by
  a smooth function is its own formal adjoint (`LinearMap.isFormalAdjoint_lsmul`).
* `LinearMap.IsFormalAdjoint.unique`: uniqueness of formal adjoints.
* `LinearMap.IsFormalAdjoint.formalAdjoint_eq`,
  `LinearMap.IsFormalAdjoint.formalAdjoint_formalAdjoint`: the formal adjoint is characterized by
  integration by parts and is an involution.
* `LinearMap.IsFormalAdjoint.smulCommutator`: the formal adjoint of `[P, a]` is `-[Q, a]`.
* `LinearMap.IsFormalAdjoint.smulCommutator_pow`: the formal adjoint of the `j`-fold commutator
  `[⋯[P, a], …, a]` is the `j`-fold commutator `[⋯[Q, -a], …, -a]`.
* `LinearMap.IsFormalAdjoint.inner_apply_eq_of_mem_differentialOperators_zero`: a formal adjoint of
  an operator of order zero is a pointwise adjoint.
* `LinearMap.IsFormalAdjoint.mem_differentialOperators`: a formal adjoint of a differential
  operator of order at most `m` that does not enlarge supports is a differential operator of order
  at most `m`.

## References

* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (differential operators between vector bundles and their adjoints).
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti
open scoped ContDiff Manifold RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  {U : M → Type*} [TopologicalSpace (TotalSpace F'' U)]
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [FiberBundle F'' U] [VectorBundle ℝ F'' U]

namespace LinearMap

variable [MeasurableSpace M]

/-! ### Formal adjoints -/

/-- A linear operator `Q : Γ(W) → Γ(V)` is a *formal adjoint* of `P : Γ(V) → Γ(W)` with respect to
the measure `μ` if `∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ` for all smooth sections `s` and `t` one of
which has compact support. -/
def IsFormalAdjoint (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) (μ : Measure M) : Prop :=
  ∀ s t, IsCompact s.tsupport ∨ IsCompact t.tsupport →
    ∫ x, ⟪P s x, t x⟫ ∂μ = ∫ x, ⟪s x, Q t x⟫ ∂μ

open Classical in
/-- The formal adjoint of a linear operator `P : Γ(V) → Γ(W)` with respect to the measure `μ`: an
operator `Q` with `∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ` whenever `s` or `t` has compact support
(`LinearMap.IsFormalAdjoint`), if there is one, and `0` otherwise. It is unique under the
hypotheses of `LinearMap.IsFormalAdjoint.unique`. -/
def formalAdjoint (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (μ : Measure M) :
    Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
  if h : ∃ Q, P.IsFormalAdjoint Q μ then h.choose else 0

variable {P P₁ P₂ : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
  {Q Q₁ Q₂ : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯} {μ : Measure M}

/-- Unfolding `LinearMap.IsFormalAdjoint`: `Q` is a formal adjoint of `P` if and only if
`∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ` whenever `s` or `t` has compact support. -/
theorem isFormalAdjoint_iff : P.IsFormalAdjoint Q μ ↔
    ∀ s t, IsCompact s.tsupport ∨ IsCompact t.tsupport →
      ∫ x, ⟪P s x, t x⟫ ∂μ = ∫ x, ⟪s x, Q t x⟫ ∂μ :=
  Iff.rfl

/-- Integration by parts against a formal adjoint: if `Q` is a formal adjoint of `P`, then
`∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ` whenever `s` or `t` has compact support. -/
theorem IsFormalAdjoint.integral_inner_eq (h : P.IsFormalAdjoint Q μ)
    {s : Cₛ^∞⟮I; F, V⟯} {t : Cₛ^∞⟮I; F', W⟯} (hst : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    ∫ x, ⟪P s x, t x⟫ ∂μ = ∫ x, ⟪s x, Q t x⟫ ∂μ :=
  h s t hst

/-- An operator without a formal adjoint has formal adjoint `0` by convention. -/
theorem formalAdjoint_eq_zero_of_not_exists (h : ¬∃ Q, P.IsFormalAdjoint Q μ) :
    P.formalAdjoint μ = 0 := by
  simp [formalAdjoint, h]

/-- If `P` has a formal adjoint, then `LinearMap.formalAdjoint P μ` is one. -/
theorem IsFormalAdjoint.isFormalAdjoint_formalAdjoint (h : P.IsFormalAdjoint Q μ) :
    P.IsFormalAdjoint (P.formalAdjoint μ) μ := by
  have hex : ∃ Q, P.IsFormalAdjoint Q μ := ⟨Q, h⟩
  simp only [formalAdjoint, hex, ↓reduceDIte]
  exact hex.choose_spec

/-! ### The algebra of formal adjoints -/

/-- Formal adjunction is symmetric: if `Q` is a formal adjoint of `P`, then `P` is one of `Q`. -/
theorem IsFormalAdjoint.symm (h : P.IsFormalAdjoint Q μ) : Q.IsFormalAdjoint P μ := by
  intro t s hts
  simpa only [real_inner_comm] using (h s t hts.symm).symm

/-- `Q` is a formal adjoint of `P` exactly when `P` is a formal adjoint of `Q`. -/
theorem isFormalAdjoint_comm : P.IsFormalAdjoint Q μ ↔ Q.IsFormalAdjoint P μ :=
  ⟨.symm, .symm⟩

/-- A pointwise adjoint is a formal adjoint for every measure: if `⟪P s, t⟫ = ⟪s, Q t⟫` at every
point, for instance when `P` and `Q` are given by mutually adjoint bundle maps, then `Q` is a formal
adjoint of `P`. -/
theorem isFormalAdjoint_of_forall_inner_eq (h : ∀ s t x, ⟪P s x, t x⟫ = ⟪s x, Q t x⟫) :
    P.IsFormalAdjoint Q μ :=
  fun s t _ ↦ integral_congr_ae (.of_forall (h s t))

/-- The zero operator has the zero operator as formal adjoint, for every measure. -/
protected theorem IsFormalAdjoint.zero :
    (0 : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint 0 μ :=
  isFormalAdjoint_of_forall_inner_eq fun _ _ _ ↦ by simp

/-- The identity is its own formal adjoint, for every measure. -/
protected theorem IsFormalAdjoint.id :
    (LinearMap.id : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint LinearMap.id μ :=
  fun _ _ _ ↦ rfl

/-- Formal adjoints are compatible with scalar multiplication. -/
theorem IsFormalAdjoint.smul (h : P.IsFormalAdjoint Q μ) (c : ℝ) :
    (c • P).IsFormalAdjoint (c • Q) μ := by
  intro s t hst
  simp only [LinearMap.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  rw [integral_const_mul, integral_const_mul, h s t hst]

/-- Formal adjoints are compatible with negation. -/
theorem IsFormalAdjoint.neg (h : P.IsFormalAdjoint Q μ) : (-P).IsFormalAdjoint (-Q) μ := by
  intro s t hst
  simp only [LinearMap.neg_apply, ContMDiffSection.coe_neg, Pi.neg_apply, inner_neg_left,
    inner_neg_right, integral_neg, h s t hst]

omit [MeasurableSpace M] [∀ x, InnerProductSpace ℝ (U x)] [VectorBundle ℝ F'' U] in
/-- If `P` does not enlarge supports, then `P s` or `t` has compact support whenever `s` or `t`
does. -/
private theorem isCompact_tsupport_apply_or (hP : ∀ s, (P s).tsupport ⊆ s.tsupport)
    {s : Cₛ^∞⟮I; F, V⟯} {t : Cₛ^∞⟮I; F'', U⟯} (hst : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    IsCompact (P s).tsupport ∨ IsCompact t.tsupport :=
  hst.imp (·.of_isClosed_subset (P s).isClosed_tsupport (hP s)) _root_.id

omit [MeasurableSpace M] [∀ x, InnerProductSpace ℝ (U x)] [VectorBundle ℝ F'' U] in
/-- If `Q` does not enlarge supports, then `s` or `Q t` has compact support whenever `s` or `t`
does. -/
private theorem isCompact_tsupport_or_apply (hQ : ∀ t, (Q t).tsupport ⊆ t.tsupport)
    {s : Cₛ^∞⟮I; F'', U⟯} {t : Cₛ^∞⟮I; F', W⟯} (hst : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    IsCompact s.tsupport ∨ IsCompact (Q t).tsupport :=
  (isCompact_tsupport_apply_or hQ hst.symm).symm

/-- The formal adjoint of a composition is the composition of the formal adjoints in the reverse
order, provided the inner operator and the formal adjoint of the outer one do not enlarge
supports. -/
theorem IsFormalAdjoint.comp {R : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯}
    {S : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} (hR : R.IsFormalAdjoint S μ)
    (hP : P.IsFormalAdjoint Q μ) (hPs : ∀ s, (P s).tsupport ⊆ s.tsupport)
    (hSs : ∀ t, (S t).tsupport ⊆ t.tsupport) :
    (R ∘ₗ P).IsFormalAdjoint (Q ∘ₗ S) μ := by
  intro s t hst
  calc ∫ x, ⟪(R ∘ₗ P) s x, t x⟫ ∂μ = ∫ x, ⟪P s x, S t x⟫ ∂μ :=
        hR _ _ (isCompact_tsupport_apply_or hPs hst)
    _ = ∫ x, ⟪s x, (Q ∘ₗ S) t x⟫ ∂μ := hP _ _ (isCompact_tsupport_or_apply hSs hst)

section Integrable

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
  [IsContinuousRiemannianBundle F V] [IsContinuousRiemannianBundle F' W]

omit [IsContinuousRiemannianBundle F V] in
/-- If `P` does not enlarge supports, then `⟪P s, t⟫` is integrable whenever `s` or `t` has
compact support. -/
theorem integrable_inner_apply_left (hP : ∀ s, (P s).tsupport ⊆ s.tsupport)
    {s : Cₛ^∞⟮I; F, V⟯} {t : Cₛ^∞⟮I; F', W⟯} (hst : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    Integrable (fun x ↦ ⟪P s x, t x⟫) μ :=
  ContMDiffSection.integrable_inner (isCompact_tsupport_apply_or hP hst)

omit [IsContinuousRiemannianBundle F' W] in
/-- If `Q` does not enlarge supports, then `⟪s, Q t⟫` is integrable whenever `s` or `t` has
compact support. -/
theorem integrable_inner_apply_right (hQ : ∀ t, (Q t).tsupport ⊆ t.tsupport)
    {s : Cₛ^∞⟮I; F, V⟯} {t : Cₛ^∞⟮I; F', W⟯} (hst : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    Integrable (fun x ↦ ⟪s x, Q t x⟫) μ :=
  ContMDiffSection.integrable_inner (isCompact_tsupport_or_apply hQ hst)

/-- Formal adjoints of operators that do not enlarge supports add. -/
theorem IsFormalAdjoint.add (h₁ : P₁.IsFormalAdjoint Q₁ μ) (h₂ : P₂.IsFormalAdjoint Q₂ μ)
    (hP₁ : ∀ s, (P₁ s).tsupport ⊆ s.tsupport) (hP₂ : ∀ s, (P₂ s).tsupport ⊆ s.tsupport)
    (hQ₁ : ∀ t, (Q₁ t).tsupport ⊆ t.tsupport) (hQ₂ : ∀ t, (Q₂ t).tsupport ⊆ t.tsupport) :
    (P₁ + P₂).IsFormalAdjoint (Q₁ + Q₂) μ := by
  intro s t hst
  simp only [LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply, inner_add_left,
    inner_add_right]
  rw [integral_add (integrable_inner_apply_left hP₁ hst) (integrable_inner_apply_left hP₂ hst),
    integral_add (integrable_inner_apply_right hQ₁ hst) (integrable_inner_apply_right hQ₂ hst),
    h₁ s t hst, h₂ s t hst]

/-- Formal adjoints of operators that do not enlarge supports subtract. -/
theorem IsFormalAdjoint.sub (h₁ : P₁.IsFormalAdjoint Q₁ μ) (h₂ : P₂.IsFormalAdjoint Q₂ μ)
    (hP₁ : ∀ s, (P₁ s).tsupport ⊆ s.tsupport) (hP₂ : ∀ s, (P₂ s).tsupport ⊆ s.tsupport)
    (hQ₁ : ∀ t, (Q₁ t).tsupport ⊆ t.tsupport) (hQ₂ : ∀ t, (Q₂ t).tsupport ⊆ t.tsupport) :
    (P₁ - P₂).IsFormalAdjoint (Q₁ - Q₂) μ := by
  intro s t hst
  simp only [LinearMap.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply, inner_sub_left,
    inner_sub_right]
  rw [integral_sub (integrable_inner_apply_left hP₁ hst) (integrable_inner_apply_left hP₂ hst),
    integral_sub (integrable_inner_apply_right hQ₁ hst) (integrable_inner_apply_right hQ₂ hst),
    h₁ s t hst, h₂ s t hst]

end Integrable

/-! ### Multiplication by smooth functions -/

section Multiplication

/-- Multiplication by a smooth function is its own formal adjoint, for every measure. -/
theorem isFormalAdjoint_lsmul (a : C^∞⟮I, M; ℝ⟯) :
    (Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ a).IsFormalAdjoint (Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ a) μ :=
  isFormalAdjoint_of_forall_inner_eq fun s t x ↦ by
    simp [inner_smul_left, inner_smul_right]

end Multiplication

/-! ### Uniqueness -/

section Unique

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
  [IsContinuousRiemannianBundle F V]

/-- **Uniqueness of formal adjoints.** For bundles with continuous fibre metrics and a locally
finite measure that is positive on open sets of a Hausdorff σ-compact manifold, a linear operator
between smooth sections has at most one formal adjoint. -/
theorem IsFormalAdjoint.unique (h₁ : P.IsFormalAdjoint Q₁ μ) (h₂ : P.IsFormalAdjoint Q₂ μ) :
    Q₁ = Q₂ := by
  ext t : 1
  rw [← sub_eq_zero]
  refine ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero (μ := μ) fun s hs ↦ ?_
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, inner_sub_right]
  rw [integral_sub (ContMDiffSection.integrable_inner (.inl hs))
    (ContMDiffSection.integrable_inner (.inl hs)), ← h₁ s t (.inl hs), ← h₂ s t (.inl hs),
    sub_self]

/-- A formal adjoint of `P` is `LinearMap.formalAdjoint P μ`. -/
theorem IsFormalAdjoint.formalAdjoint_eq (h : P.IsFormalAdjoint Q μ) : P.formalAdjoint μ = Q :=
  h.isFormalAdjoint_formalAdjoint.unique h

/-- If `P` has a formal adjoint, then `LinearMap.formalAdjoint P μ` is characterized as the formal
adjoint of `P`. -/
theorem IsFormalAdjoint.formalAdjoint_eq_iff (h : P.IsFormalAdjoint Q μ) :
    P.formalAdjoint μ = Q₁ ↔ P.IsFormalAdjoint Q₁ μ := by
  rw [h.formalAdjoint_eq]
  exact ⟨fun h' ↦ h' ▸ h, h.unique⟩

/-- If `P` has a formal adjoint, then taking the formal adjoint twice gives back `P`. -/
theorem IsFormalAdjoint.formalAdjoint_formalAdjoint [IsContinuousRiemannianBundle F' W]
    (h : P.IsFormalAdjoint Q μ) :
    (P.formalAdjoint μ).formalAdjoint μ = P := by
  rw [h.formalAdjoint_eq, h.symm.formalAdjoint_eq]

/-- The formal adjoint of the zero operator is zero. -/
@[simp]
theorem formalAdjoint_zero :
    (0 : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).formalAdjoint μ = 0 :=
  IsFormalAdjoint.zero.formalAdjoint_eq

/-- Formal adjunction commutes with negation. -/
@[simp]
theorem formalAdjoint_neg : (-P).formalAdjoint μ = -P.formalAdjoint μ := by
  by_cases h : ∃ Q, P.IsFormalAdjoint Q μ
  · obtain ⟨Q, h⟩ := h
    rw [h.formalAdjoint_eq, h.neg.formalAdjoint_eq]
  · have h' : ¬∃ Q, (-P).IsFormalAdjoint Q μ := fun ⟨Q, hQ⟩ ↦ h ⟨-Q, by simpa using hQ.neg⟩
    rw [formalAdjoint_eq_zero_of_not_exists h, formalAdjoint_eq_zero_of_not_exists h', neg_zero]

/-- Formal adjunction commutes with scalar multiplication. -/
@[simp]
theorem formalAdjoint_smul (c : ℝ) : (c • P).formalAdjoint μ = c • P.formalAdjoint μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases h : ∃ Q, P.IsFormalAdjoint Q μ
  · obtain ⟨Q, h⟩ := h
    rw [h.formalAdjoint_eq, (h.smul c).formalAdjoint_eq]
  · have h' : ¬∃ Q, (c • P).IsFormalAdjoint Q μ := fun ⟨Q, hQ⟩ ↦
      h ⟨c⁻¹ • Q, by simpa [smul_smul, hc] using hQ.smul c⁻¹⟩
    rw [formalAdjoint_eq_zero_of_not_exists h, formalAdjoint_eq_zero_of_not_exists h', smul_zero]

/-- The identity is its own formal adjoint. -/
@[simp]
theorem formalAdjoint_id :
    (LinearMap.id : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).formalAdjoint μ = LinearMap.id :=
  IsFormalAdjoint.id.formalAdjoint_eq

/-- Multiplication by a smooth function is its own formal adjoint. -/
@[simp]
theorem formalAdjoint_lsmul (a : C^∞⟮I, M; ℝ⟯) :
    (Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ a).formalAdjoint μ = Algebra.lsmul ℝ ℝ Cₛ^∞⟮I; F, V⟯ a :=
  (isFormalAdjoint_lsmul a).formalAdjoint_eq

end Unique

/-! ### Differential operators -/

section DifferentialOperator

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ] [IsContinuousRiemannianBundle F V]
  [IsContinuousRiemannianBundle F' W]

/-- **The formal adjoint of a commutator.** If `Q` is a formal adjoint of `P` and neither enlarges
supports, then `-[Q, a]` is a formal adjoint of the commutator `[P, a]` with multiplication by
`a`: multiplication operators are their own formal adjoints and formal adjunction reverses
compositions. -/
theorem IsFormalAdjoint.smulCommutator (h : P.IsFormalAdjoint Q μ)
    (hPs : ∀ s, (P s).tsupport ⊆ s.tsupport) (hQs : ∀ t, (Q t).tsupport ⊆ t.tsupport)
    (a : C^∞⟮I, M; ℝ⟯) :
    (TauCeti.smulCommutator ℝ a P).IsFormalAdjoint (-TauCeti.smulCommutator ℝ a Q) μ := by
  -- Multiplication by `a` does not enlarge supports.
  have haV : ∀ s : Cₛ^∞⟮I; F, V⟯, (Algebra.lsmul ℝ ℝ _ a s).tsupport ⊆ s.tsupport :=
    ContMDiffSection.tsupport_smul_function_subset_right a
  have haW : ∀ t : Cₛ^∞⟮I; F', W⟯, (Algebra.lsmul ℝ ℝ _ a t).tsupport ⊆ t.tsupport :=
    ContMDiffSection.tsupport_smul_function_subset_right a
  have h' := (h.comp (isFormalAdjoint_lsmul a) haV hQs).sub
    ((isFormalAdjoint_lsmul a).comp h hPs haW)
    (fun s ↦ (hPs _).trans (haV s)) (fun s ↦ (haW _).trans (hPs s))
    (fun t ↦ (haV _).trans (hQs t)) (fun t ↦ (hQs _).trans (haW t))
  convert h' using 1 <;> ext <;> simp [sub_eq_neg_add]

/-- **The formal adjoint of an iterated commutator.** If `Q` is a formal adjoint of `P` and neither
enlarges supports, then the `j`-fold commutator `[⋯[Q, -a], …, -a]` is a formal adjoint of the
`j`-fold commutator `[⋯[P, a], …, a]`. -/
theorem IsFormalAdjoint.smulCommutator_pow (h : P.IsFormalAdjoint Q μ)
    (hPs : ∀ s, (P s).tsupport ⊆ s.tsupport) (hQs : ∀ t, (Q t).tsupport ⊆ t.tsupport)
    (a : C^∞⟮I, M; ℝ⟯) (j : ℕ) :
    ((TauCeti.smulCommutator ℝ a ^ j) P).IsFormalAdjoint
      ((TauCeti.smulCommutator ℝ (-a) ^ j) Q) μ := by
  induction j generalizing P Q with
  | zero => simpa using h
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, pow_succ, mul_apply_eq_comp]
    -- The formal adjoint `-[Q, a]` of `[P, a]` is the commutator `[Q, -a]`.
    have hneg : -TauCeti.smulCommutator ℝ a Q = TauCeti.smulCommutator ℝ (-a) Q := by
      ext t : 1
      simp only [LinearMap.neg_apply, smulCommutator_apply_apply, neg_smul, map_neg]
      abel
    exact ih (hneg ▸ h.smulCommutator hPs hQs a)
      (tsupport_smulCommutator_section_apply_subset hPs a)
      (tsupport_smulCommutator_section_apply_subset hQs (-a))

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **The order of a formal adjoint.** A formal adjoint of a differential operator of order at most
`m` that does not enlarge supports is a differential operator of order at most `m`. -/
theorem IsFormalAdjoint.mem_differentialOperators {m : ℕ} (h : P.IsFormalAdjoint Q μ)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (hQs : ∀ t, (Q t).tsupport ⊆ t.tsupport) :
    Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m := by
  have hPs := tsupport_differentialOperators_section_apply_subset hP
  induction m generalizing P Q with
  | zero =>
    -- The commutators `[P, a]` vanish, so the commutators `-[Q, a]`, their formal adjoints, are
    -- formal adjoints of zero.
    refine mem_differentialOperators_zero_iff_smulCommutator.2 fun a ↦ ?_
    have h' := h.smulCommutator hPs hQs a
    rw [smulCommutator_eq_zero_of_mem_differentialOperators_zero hP a] at h'
    exact neg_eq_zero.1 (h'.unique IsFormalAdjoint.zero)
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun a ↦ ?_
    simpa using neg_mem <| ih (h.smulCommutator hPs hQs a)
      (smulCommutator_mem_differentialOperators hP a)
      (fun t ↦ by
        simpa [neg_add_eq_sub] using tsupport_smulCommutator_section_apply_subset hQs (-a) t)
      (tsupport_differentialOperators_section_apply_subset
        (smulCommutator_mem_differentialOperators hP a))

/-- **Formal adjoints of operators of order zero are pointwise adjoints.** If `P` is a
differential operator of order zero, that is a `C^∞(M)`-linear map, and `Q` is a formal adjoint of
`P`, then `⟪P s x, t x⟫ = ⟪s x, Q t x⟫` for all smooth sections `s`, `t` and every point `x`. -/
theorem IsFormalAdjoint.inner_apply_eq_of_mem_differentialOperators_zero
    (h : P.IsFormalAdjoint Q μ)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0)
    (s : Cₛ^∞⟮I; F, V⟯) (t : Cₛ^∞⟮I; F', W⟯) (x : M) :
    ⟪P s x, t x⟫ = ⟪s x, Q t x⟫ := by
  have hcont : Continuous fun y ↦ ⟪P s y, t y⟫ - ⟪s y, Q t y⟫ :=
    (ContMDiffSection.continuous_inner _ _).sub (ContMDiffSection.continuous_inner _ _)
  -- The continuous function `⟪P s, t⟫ - ⟪s, Q t⟫` has zero integral against every test function
  -- `φ`: since `P (φ s) = φ P s`, this integral is the integration by parts identity for `φ s`.
  have hae : ∀ᵐ y ∂μ, ⟪P s y, t y⟫ - ⟪s y, Q t y⟫ = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let ψ : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have hPψ : P (ψ • s) = ψ • P s := mem_differentialOperators_zero_iff.1 hP ψ s
    have hs := ContMDiffSection.mem_compactlySupported.1 <|
      ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport ψ hφc s
    have hPs := ContMDiffSection.mem_compactlySupported.1 <|
      ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport ψ hφc (P s)
    rw [← hPψ] at hPs
    calc ∫ y, φ y • (⟪P s y, t y⟫ - ⟪s y, Q t y⟫) ∂μ
        = ∫ y, ⟪P (ψ • s) y, t y⟫ - ⟪(ψ • s) y, Q t y⟫ ∂μ := by
          refine integral_congr_ae (.of_forall fun y ↦ ?_)
          simp only [hPψ, ContMDiffSection.smul_apply, real_inner_smul_left, smul_eq_mul, mul_sub]
          simp only [ψ, ContMDiffMap.coeFn_mk]
      _ = 0 := by
          rw [integral_sub (ContMDiffSection.integrable_inner (.inl hPs))
            (ContMDiffSection.integrable_inner (.inl hs)), h _ _ (.inl hs), sub_self]
  exact sub_eq_zero.1 (congr_fun ((hcont.ae_eq_iff_eq μ continuous_const).1 hae) x)

end DifferentialOperator

end LinearMap
