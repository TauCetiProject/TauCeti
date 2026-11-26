/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invariant lines of matrix representations

A matrix representation `ρ : G →* GL(n, K)` over a field *has an invariant line* when some
one-dimensional subspace of `n → K` is invariant, in the sense of `Module.End.invtSubmodule`, under
every `ρ g`. For `n = 2` this is
reducibility of `ρ`; applied to the restriction of `ρ` to the kernel of `det ∘ ρ`, it is the
conclusion of reducibility criteria for residual two-dimensional Galois representations whose
determinant has nontrivial image, such as Caraiani–Newton, Lemma 5.6.5.

The predicate is characterized through a nonzero vector whose span is preserved, equivalently a
common eigenvector of all `ρ g`. It passes to every precomposition `ρ ∘ f`, in particular to the
restriction to a subgroup, so a line invariant under the whole group is invariant under the
determinant kernel; it is unchanged by conjugating `ρ` by an invertible matrix (a change of
basis). Two invertible values of `ρ` that anticommute, `ρ g * ρ h = -(ρ h * ρ g)`, rule out an
invariant line when `2 ≠ 0`, as for the quaternion matrices `i` and `j`.

## Main declarations

* `MonoidHom.HasInvariantLine`: some line of `n → K` is invariant under every `ρ g`.
* `MonoidHom.hasInvariantLine_iff`: the definition, with invariance unfolded to
  `∀ v ∈ W, ρ g *ᵥ v ∈ W`.
* `MonoidHom.hasInvariantLine_iff_exists_mulVec_mem_span`,
  `MonoidHom.hasInvariantLine_iff_exists_mulVec_eq_smul`: the line is spanned by a nonzero
  vector, a common eigenvector of all `ρ g`.
* `MonoidHom.HasInvariantLine.comp`: an invariant line of `ρ` is invariant under `ρ ∘ f`.
* `MonoidHom.hasInvariantLine_comp_ker_det_subtype_iff`: the restriction of `ρ` to the kernel of
  its determinant has an invariant line exactly when some line is invariant under every `ρ g` of
  determinant one.
* `MonoidHom.hasInvariantLine_comp_ker_det_subtype_iff_exists_mulVec_mem_span`: equivalently, some
  nonzero vector has its span preserved by every `ρ g` of determinant one.
* `MonoidHom.hasInvariantLine_conj_iff`: invariance under change of basis.
* `MonoidHom.hasInvariantLine_one`: the trivial representation has an invariant line.
* `MonoidHom.not_hasInvariantLine_of_mul_eq_neg_mul`: anticommuting values exclude an invariant
  line away from characteristic `2`.

## References

* A. Caraiani, J. Newton, *On the modularity of elliptic curves over imaginary quadratic fields*,
  Lemma 5.6.5, pp. 85–86.
-/

public section

open Matrix Module

namespace MonoidHom

section Monoid

variable {G : Type*} [Monoid G] {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
  (ρ : G →* GL n K)

/-- A matrix representation `ρ : G →* GL(n, K)` over a field *has an invariant line* if some
one-dimensional subspace of `n → K` is an invariant submodule of every `ρ g`. -/
def HasInvariantLine : Prop :=
  ∃ W : Submodule K (n → K), finrank K W = 1 ∧
    ∀ g, W ∈ End.invtSubmodule (toLin' (ρ g : Matrix n n K))

variable {ρ}

/-- `ρ` has an invariant line exactly when some one-dimensional subspace `W` of `n → K` is carried
into itself by every `ρ g`. -/
theorem hasInvariantLine_iff :
    ρ.HasInvariantLine ↔ ∃ W : Submodule K (n → K), finrank K W = 1 ∧
      ∀ g, ∀ v ∈ W, (ρ g : Matrix n n K) *ᵥ v ∈ W := by
  simp only [HasInvariantLine, End.mem_invtSubmodule_iff_forall_mem_of_mem, toLin'_apply]

/-- `ρ` has an invariant line exactly when some nonzero vector `v` has its span `K ∙ v` preserved
by every `ρ g`. -/
theorem hasInvariantLine_iff_exists_mulVec_mem_span :
    ρ.HasInvariantLine ↔ ∃ v ≠ 0, ∀ g, (ρ g : Matrix n n K) *ᵥ v ∈ K ∙ v := by
  rw [hasInvariantLine_iff]
  constructor
  · rintro ⟨W, hW, hρ⟩
    obtain ⟨⟨v, hvW⟩, hv, hspan⟩ := finrank_eq_one_iff'.1 hW
    refine ⟨v, fun h ↦ hv (Subtype.ext h), fun g ↦ Submodule.mem_span_singleton.2 ?_⟩
    obtain ⟨c, hc⟩ := hspan ⟨_, hρ g v hvW⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨v, hv, hρ⟩
    refine ⟨K ∙ v, finrank_span_singleton hv, fun g w hw ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [mulVec_smul]
    exact Submodule.smul_mem _ a (hρ g)

/-- `ρ` has an invariant line exactly when all `ρ g` have a common eigenvector. -/
theorem hasInvariantLine_iff_exists_mulVec_eq_smul :
    ρ.HasInvariantLine ↔ ∃ v ≠ 0, ∀ g, ∃ c : K, (ρ g : Matrix n n K) *ᵥ v = c • v := by
  simp only [hasInvariantLine_iff_exists_mulVec_mem_span, Submodule.mem_span_singleton, eq_comm]

/-- An invariant line of `ρ` is invariant under every precomposition `ρ ∘ f`; in particular a line
invariant under the whole group is invariant under each of its subgroups. -/
theorem HasInvariantLine.comp (h : ρ.HasInvariantLine) {H : Type*} [Monoid H] (f : H →* G) :
    (ρ.comp f).HasInvariantLine := by
  obtain ⟨W, hW, hρ⟩ := hasInvariantLine_iff.1 h
  exact hasInvariantLine_iff.2 ⟨W, hW, fun g ↦ hρ (f g)⟩

/-- The trivial representation has an invariant line, as soon as `n → K` is nonzero. -/
theorem hasInvariantLine_one [Nonempty n] : (1 : G →* GL n K).HasInvariantLine := by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine hasInvariantLine_iff_exists_mulVec_eq_smul.2
    ⟨Pi.single i 1, by simp, fun _ ↦ ⟨1, by rw [one_apply, Units.val_one, one_mulVec, one_smul]⟩⟩

/-- Two values of `ρ` that anticommute leave no line invariant, when `2 ≠ 0` in `K`: on a common
eigenvector their product would act by a scalar equal to its own negative, which is impossible
for invertible matrices. -/
theorem not_hasInvariantLine_of_mul_eq_neg_mul (h2 : (2 : K) ≠ 0) {g h : G}
    (hgh : (ρ g : Matrix n n K) * ρ h = -((ρ h : Matrix n n K) * ρ g)) :
    ¬ ρ.HasInvariantLine := by
  rintro hline
  obtain ⟨v, hv, hρ⟩ := hasInvariantLine_iff_exists_mulVec_eq_smul.1 hline
  obtain ⟨a, ha⟩ := hρ g
  obtain ⟨b, hb⟩ := hρ h
  -- Both products act on `v` by `a * b`, so `a * b • v = -(a * b • v)`.
  have hprod := congrArg (· *ᵥ v) hgh
  simp only [neg_mulVec, ← mulVec_mulVec, ha, hb, mulVec_smul, smul_smul] at hprod
  rw [mul_comm a b] at hprod
  have hab : ((2 : K) * (b * a)) • v = 0 := by
    rw [two_mul, add_smul, ← eq_neg_iff_add_eq_zero]
    exact hprod
  rcases mul_eq_zero.1 ((smul_eq_zero.1 hab).resolve_right hv) with h0 | h0
  · exact h2 h0
  -- A zero eigenvalue of an invertible matrix forces `v = 0`.
  have hzero : ∀ k : G, ∀ c : K, (ρ k : Matrix n n K) *ᵥ v = c • v → c ≠ 0 := by
    rintro k c hc rfl
    rw [zero_smul, ← mulVec_zero (ρ k : Matrix n n K)] at hc
    exact hv (mulVec_injective_of_isUnit (ρ k).isUnit hc)
  rcases mul_eq_zero.1 h0 with h0 | h0
  · exact hzero h b hb h0
  · exact hzero g a ha h0

end Monoid

section Group

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
  {ρ : G →* GL n K}

/-- The restriction of `ρ` to the kernel of its determinant has an invariant line exactly when some
line is carried into itself by every `ρ g` of determinant one. -/
theorem hasInvariantLine_comp_ker_det_subtype_iff :
    (ρ.comp (GeneralLinearGroup.det.comp ρ).ker.subtype).HasInvariantLine ↔
      ∃ W : Submodule K (n → K), finrank K W = 1 ∧
        ∀ g, GeneralLinearGroup.det (ρ g) = 1 → ∀ v ∈ W, (ρ g : Matrix n n K) *ᵥ v ∈ W := by
  rw [hasInvariantLine_iff]
  refine exists_congr fun W ↦ and_congr_right fun _ ↦ ⟨fun h g hg ↦ h ⟨g, hg⟩, ?_⟩
  rintro h ⟨g, hg⟩
  exact h g hg

/-- The restriction of `ρ` to the kernel of its determinant has an invariant line exactly when some
nonzero vector `v` has its span `K ∙ v` preserved by every `ρ g` of determinant one. -/
theorem hasInvariantLine_comp_ker_det_subtype_iff_exists_mulVec_mem_span :
    (ρ.comp (GeneralLinearGroup.det.comp ρ).ker.subtype).HasInvariantLine ↔
      ∃ v ≠ 0, ∀ g, GeneralLinearGroup.det (ρ g) = 1 → (ρ g : Matrix n n K) *ᵥ v ∈ K ∙ v := by
  rw [hasInvariantLine_iff_exists_mulVec_mem_span]
  refine exists_congr fun v ↦ and_congr_right fun _ ↦ ⟨fun h g hg ↦ h ⟨g, hg⟩, ?_⟩
  rintro h ⟨g, hg⟩
  exact h g hg

end Group

section Conj

variable {G : Type*} [Monoid G] {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
  {ρ : G →* GL n K}

/-- Conjugating `ρ` by an invertible matrix `P` carries an invariant line `W` to its image under
`P`: the linear map of `P * ρ g * P⁻¹` is the conjugate of that of `ρ g` by `P`. -/
theorem HasInvariantLine.conj (h : ρ.HasInvariantLine) (P : GL n K) :
    ((MulAut.conj P : GL n K →* GL n K).comp ρ).HasInvariantLine := by
  obtain ⟨W, hW, hρ⟩ := h
  let e : (n → K) ≃ₗ[K] n → K :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (GeneralLinearGroup.toLin P)
  refine ⟨W.map (e : (n → K) →ₗ[K] n → K), by rw [LinearEquiv.finrank_map_eq, hW], fun g ↦ ?_⟩
  have hconj : toLin' ((MulAut.conj P : GL n K →* GL n K).comp ρ g : Matrix n n K) =
      e.conj (toLin' (ρ g : Matrix n n K)) := by
    refine LinearMap.ext fun v ↦ ?_
    have he : e.symm v = ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ v :=
      e.symm_apply_eq.2 (by simp [e, mulVec_mulVec])
    simp [LinearEquiv.conj_apply, he, e, mulVec_mulVec, mul_assoc]
  rw [hconj, LinearEquiv.map_mem_invtSubmodule_conj_iff]
  exact hρ g

/-- Having an invariant line is unchanged by conjugating `ρ` by an invertible matrix, that is, by
a change of basis of `n → K`. -/
@[simp]
theorem hasInvariantLine_conj_iff (P : GL n K) :
    ((MulAut.conj P : GL n K →* GL n K).comp ρ).HasInvariantLine ↔ ρ.HasInvariantLine := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj P⟩
  have h' := h.conj P⁻¹
  have hρ : (MulAut.conj P⁻¹ : GL n K →* GL n K).comp
      ((MulAut.conj P : GL n K →* GL n K).comp ρ) = ρ := by
    ext g : 1
    simp [mul_assoc]
  rwa [hρ] at h'

end Conj

end MonoidHom
