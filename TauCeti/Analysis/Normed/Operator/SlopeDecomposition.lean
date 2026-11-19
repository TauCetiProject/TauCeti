/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.Slope
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Slope decompositions

A *slope decomposition* of a continuous `A`-linear operator `U` on a topological `A`-module `M` is
a pair of topological complements `M₁, M₂` stable under `U`, such that `M₁` is finite projective
and is annihilated by `Q(U)` for a monic `Q` of slope at most `r` with unit constant term, while
every such polynomial acts bijectively on `M₂`. The continuous projection onto `M₁` along `M₂`
then commutes with `U`. Polynomial annihilation cannot be replaced by a pointwise condition on
eigenvalues: over a nonreduced base, or on a nilpotent operator, only the polynomial detects the
action.

## Main definitions

* `ContinuousLinearMap.IsSlopeDecomposition K U r M₁ M₂`: `M = M₁ ⊕ M₂` is a slope `≤ r`
  decomposition for `U`.

## Main results

* `ContinuousLinearMap.IsSlopeDecomposition.exists_projection`: a slope decomposition has a
  continuous idempotent projector with image `M₁` and kernel `M₂`, commuting with `U`.

## References

* E. Urban, *Eigenvarieties for reductive groups*, Ann. of Math. 174 (2011), 1685–1784, §2.3.
-/

public section

open Polynomial

namespace ContinuousLinearMap

variable (K : Type*) [NormedField K] {A : Type*} [CommRing A] [Algebra K A]
  {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]

/-- A slope `≤ r` decomposition `M = M₁ ⊕ M₂` of a continuous operator `U`: the submodules are
topological complements stable under `U`, the first summand is finite projective and annihilated
by `Q(U)` for some monic `Q` of slope at most `r` with unit constant term, and every such
polynomial acts bijectively on the second summand. -/
structure IsSlopeDecomposition (U : M →L[A] M) (r : ℝ) (M₁ M₂ : Submodule A M) : Prop where
  /-- The summands are complements, with continuous projection onto `M₁` along `M₂`. -/
  isTopCompl : M₁.IsTopCompl M₂
  /-- The first summand is stable under `U`. -/
  mem_invtSubmodule_left : M₁ ∈ Module.End.invtSubmodule (U : M →ₗ[A] M)
  /-- The second summand is stable under `U`. -/
  mem_invtSubmodule_right : M₂ ∈ Module.End.invtSubmodule (U : M →ₗ[A] M)
  /-- The first summand is a finite `A`-module. -/
  finite : Module.Finite A M₁
  /-- The first summand is a projective `A`-module. -/
  projective : Module.Projective A M₁
  /-- A monic polynomial of slope at most `r`, with unit constant term, kills `M₁` at `U`. -/
  exists_annihilator : ∃ Q : A[X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧ Q.IsSlopeLE K r ∧
    M₁ ≤ LinearMap.ker (aeval (U : M →ₗ[A] M) Q)
  /-- Every monic polynomial of slope at most `r` with unit constant term is bijective on `M₂`
  at `U`. -/
  bijOn : ∀ P : A[X], P.Monic → IsUnit (P.coeff 0) → P.IsSlopeLE K r →
    Set.BijOn (aeval (U : M →ₗ[A] M) P) M₂ M₂

variable {K} {U : M →L[A] M} {r : ℝ} {M₁ M₂ : Submodule A M}

namespace IsSlopeDecomposition

/-- The cutoff of a slope decomposition is positive. -/
theorem pos (h : U.IsSlopeDecomposition K r M₁ M₂) : 0 < r :=
  let ⟨_, _, _, hQ, _⟩ := h.exists_annihilator
  hQ.pos

/-- The continuous projection onto the first summand along the second commutes with `U`. -/
theorem commute_projectionL (h : U.IsSlopeDecomposition K r M₁ M₂) :
    Commute (M₁.projectionL M₂ h.isTopCompl) U := by
  rw [ContinuousLinearMap.IsIdempotentElem.commute_iff
    (Submodule.isIdempotentElem_projectionL h.isTopCompl), Submodule.range_projectionL,
    Submodule.ker_projectionL]
  exact ⟨h.mem_invtSubmodule_left, h.mem_invtSubmodule_right⟩

/-- **The slope projector.** A slope decomposition has a continuous idempotent projector with
image `M₁` and kernel `M₂` that commutes with `U`. -/
theorem exists_projection (h : U.IsSlopeDecomposition K r M₁ M₂) :
    ∃ P : M →L[A] M, IsIdempotentElem P ∧ P.range = M₁ ∧ P.ker = M₂ ∧ Commute P U :=
  ⟨_, Submodule.isIdempotentElem_projectionL h.isTopCompl,
    Submodule.range_projectionL h.isTopCompl, Submodule.ker_projectionL h.isTopCompl,
    h.commute_projectionL⟩

end IsSlopeDecomposition

variable (K M)

/-- The zero operator has the slope decomposition `0 ⊕ M` at every positive cutoff. -/
theorem isSlopeDecomposition_zero_bot_top (hr : 0 < r) :
    (0 : M →L[A] M).IsSlopeDecomposition K r ⊥ ⊤ where
  isTopCompl := Submodule.isTopCompl_bot_top
  mem_invtSubmodule_left := (Module.End.mem_invtSubmodule _).2 bot_le
  mem_invtSubmodule_right := (Module.End.mem_invtSubmodule _).2 le_top
  finite := inferInstance
  projective := .of_free
  exists_annihilator := ⟨1, monic_one, by simp, isSlopeLE_one_iff.2 hr, bot_le⟩
  bijOn P _ hP _ := by
    rw [Submodule.top_coe, Set.bijOn_univ, ← Module.End.isUnit_iff,
      ContinuousLinearMap.toLinearMap_zero, ← coeff_zero_eq_aeval_zero']
    exact hP.map _

/-- On a finite projective module, the scalar operator `c` with `0 < r ≤ |c|` has the slope
decomposition `M ⊕ 0`. -/
theorem isSlopeDecomposition_algebraMap_smul_id_top_bot [ContinuousConstSMul A M]
    [Module.Finite A M] [Module.Projective A M] {c : K} (hr : 0 < r) (hrc : r ≤ ‖c‖) :
    (algebraMap K A c • ContinuousLinearMap.id A M).IsSlopeDecomposition K r ⊤ ⊥ where
  isTopCompl := Submodule.isTopCompl_top_bot
  mem_invtSubmodule_left := (Module.End.mem_invtSubmodule _).2 le_top
  mem_invtSubmodule_right := (Module.End.mem_invtSubmodule _).2 bot_le
  finite := .equiv Submodule.topEquiv.symm
  projective := .of_equiv Submodule.topEquiv.symm
  exists_annihilator := by
    have hc : c ≠ 0 := norm_pos_iff.1 (hr.trans_le hrc)
    refine ⟨X - C (algebraMap K A c), monic_X_sub_C _, ?_, isSlopeLE_X_sub_C_algebraMap hr hrc,
      fun m _ ↦ ?_⟩
    · simpa using (isUnit_iff_ne_zero.2 hc).map (algebraMap K A)
    · simp [Algebra.algebraMap_eq_smul_one]
  bijOn P _ _ _ := by
    rw [Submodule.bot_coe, Set.bijOn_singleton, map_zero]

end ContinuousLinearMap
