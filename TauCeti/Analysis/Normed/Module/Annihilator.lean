/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# Continuous annihilators and norm closure

For the continuous dual pairing `B = topDualPairing 𝕜 E`, Mathlib's
`S.orthogonalBilin B.flip` is the continuous annihilator of a subspace `S ≤ E`, and
`G.orthogonalBilin B` is the preannihilator of a subspace `G ≤ StrongDual 𝕜 E`.
Their order reversal, Galois connection and sum formulas are supplied by the general
`Submodule.orthogonalBilin` API.

This file proves that these subspaces are norm closed and that passing to norm closure does
not change an annihilator. Over the real or complex field, the preannihilator of the
annihilator is precisely the norm closure of the original subspace. Consequently continuous
annihilators distinguish norm closures, and a subspace is dense exactly when its annihilator
is zero. No completeness or closedness hypothesis is needed.

The analytic input is `exists_dual_vector''`, the norming-functional form of Hahn–Banach,
applied to the seminormed quotient. In particular, the results also apply to seminormed
spaces and nonclosed subspaces.

Apply the norm-closure identity as
`TauCeti.orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure S`
for `S : Submodule 𝕜 E`.

## References

* Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

namespace TauCeti

open Set Metric

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A preannihilator is norm closed in the original space. -/
theorem isClosed_orthogonalBilin_topDualPairing (G : Submodule 𝕜 (StrongDual 𝕜 E)) :
    IsClosed (G.orthogonalBilin (topDualPairing 𝕜 E) : Set E) := by
  have heq : (G.orthogonalBilin (topDualPairing 𝕜 E) : Set E) =
      ⋂ f ∈ G, {x | f x = 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter fun f _ => isClosed_eq f.continuous continuous_const

/-- A continuous annihilator is norm closed in the strong dual. -/
theorem isClosed_orthogonalBilin_topDualPairing_flip (S : Submodule 𝕜 E) :
    IsClosed (S.orthogonalBilin (topDualPairing 𝕜 E).flip : Set (StrongDual 𝕜 E)) := by
  have heq : (S.orthogonalBilin (topDualPairing 𝕜 E).flip : Set (StrongDual 𝕜 E)) =
      ⋂ x ∈ S, {f | f x = 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter fun x _ => isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous
    continuous_const

/-- Passing to norm closure does not change the continuous annihilator. -/
@[simp]
theorem orthogonalBilin_topologicalClosure_topDualPairing_flip (S : Submodule 𝕜 E) :
    S.topologicalClosure.orthogonalBilin (topDualPairing 𝕜 E).flip =
      S.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  apply le_antisymm (Submodule.orthogonalBilin_le S.le_topologicalClosure)
  intro f hf
  exact S.topologicalClosure_minimal hf f.isClosed_ker

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A functional of norm at most one annihilating a subspace can attain the distance to
that subspace at any prescribed vector, even when the subspace is not closed. -/
theorem exists_dual_eq_infDist (S : Submodule 𝕜 E) (x : E) :
    ∃ f : StrongDual 𝕜 E, (∀ y ∈ S, f y = 0) ∧ ‖f‖ ≤ 1 ∧
      f x = (infDist x (S : Set E) : 𝕜) := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 (Submodule.Quotient.mk x : E ⧸ S)
  refine ⟨g.comp S.mkQL, ?_, ?_, ?_⟩
  · intro y hy
    simp [(Submodule.Quotient.mk_eq_zero S).mpr hy]
  · refine (g.comp S.mkQL).opNorm_le_bound zero_le_one fun y => ?_
    calc
      ‖g (S.mkQL y)‖ ≤ ‖g‖ * ‖S.mkQL y‖ := g.le_opNorm _
      _ ≤ 1 * ‖y‖ := mul_le_mul hg (Submodule.Quotient.norm_mk_le S y)
        (norm_nonneg _) zero_le_one
  · -- The submodule quotient carries the norm of the quotient by its additive subgroup.
    have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ S)‖ = infDist x (S : Set E) :=
      QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_mkQL,
      Submodule.mkQ_apply, hnorm] using hgx

/-- **Norm double-annihilator theorem.** The preannihilator of the continuous annihilator
of a subspace is its norm closure. -/
@[simp]
theorem orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure
    (S : Submodule 𝕜 E) :
    (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin (topDualPairing 𝕜 E) =
      S.topologicalClosure := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, hf, _, hfx⟩ := exists_dual_eq_infDist S x
    have hzero : (infDist x (S : Set E) : 𝕜) = 0 := hfx.symm.trans (hx f hf)
    exact (mem_closure_iff_infDist_zero S.nonempty).mpr (by exact_mod_cast hzero)
  · refine S.topologicalClosure_minimal ?_ (isClosed_orthogonalBilin_topDualPairing _)
    intro x hx f hf
    exact hf x hx

/-- Continuous functionals characterize membership in a subspace's norm closure. -/
theorem mem_topologicalClosure_iff_forall_dual_eq_zero (S : Submodule 𝕜 E) (x : E) :
    x ∈ S.topologicalClosure ↔
      ∀ f : StrongDual 𝕜 E, (∀ y ∈ S, f y = 0) → f x = 0 := by
  rw [← orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure S]
  simp only [Submodule.mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply]

/-- Two subspaces have the same continuous annihilator exactly when their norm closures agree. -/
theorem orthogonalBilin_topDualPairing_flip_eq_iff_topologicalClosure_eq
    (S T : Submodule 𝕜 E) :
    S.orthogonalBilin (topDualPairing 𝕜 E).flip =
      T.orthogonalBilin (topDualPairing 𝕜 E).flip ↔
        S.topologicalClosure = T.topologicalClosure := by
  constructor
  · intro h
    rw [← orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure S,
      ← orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure T, h]
  · intro h
    rw [← orthogonalBilin_topologicalClosure_topDualPairing_flip S,
      ← orthogonalBilin_topologicalClosure_topDualPairing_flip T, h]

/-- A subspace is norm dense exactly when its continuous annihilator is zero. -/
theorem dense_iff_orthogonalBilin_topDualPairing_flip_eq_bot (S : Submodule 𝕜 E) :
    Dense (S : Set E) ↔ S.orthogonalBilin (topDualPairing 𝕜 E).flip = ⊥ := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  constructor
  · intro h
    ext f
    simp only [Submodule.mem_bot, Submodule.mem_orthogonalBilin, LinearMap.flip_apply,
      topDualPairing_apply]
    constructor
    · intro hf
      apply ContinuousLinearMap.ext
      intro x
      exact S.topologicalClosure_minimal hf f.isClosed_ker (h.symm ▸ Submodule.mem_top)
    · rintro rfl
      simp
  · intro h
    rw [← orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure S, h,
      Submodule.orthogonalBilin_bot]

end RCLike

end TauCeti
