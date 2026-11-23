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
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
is zero. No completeness or closedness hypothesis is needed. Dually, a finite-dimensional
subspace of the strong dual is the continuous annihilator of its preannihilator. As an
application, `ContinuousLinearMap.surjective_smul_add_apply_iff` decides when the map
`(τ, ξ) ↦ τ • w + H ξ` onto the dual of a finite-dimensional space is onto, for a symmetric `H`.

The analytic input is `exists_dual_vector''`, the norming-functional form of Hahn–Banach,
applied to the seminormed quotient. In particular, the results also apply to seminormed
spaces and nonclosed subspaces.

Apply the norm-closure identity as
`S.orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure`
for `S : Submodule 𝕜 E`.

## References

* Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

namespace Submodule

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
  simp only [mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply] at hf ⊢
  intro x hx
  have hker : S ≤ LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := fun y hy => by
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using hf y hy
  simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using
    S.topologicalClosure_minimal hker f.isClosed_ker hx

/-- A finite-dimensional subspace of the strong dual is the continuous annihilator of its
preannihilator: the continuous form of `Subspace.dualCoannihilator_dualAnnihilator_eq`. -/
@[simp]
theorem orthogonalBilin_orthogonalBilin_topDualPairing_flip_eq_of_finiteDimensional
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 G] :
    (G.orthogonalBilin (topDualPairing 𝕜 E)).orthogonalBilin (topDualPairing 𝕜 E).flip = G := by
  refine le_antisymm (fun ψ hψ ↦ ?_) le_orthogonalBilin_flip_orthogonalBilin
  let W : Submodule 𝕜 (Module.Dual 𝕜 E) := G.map (ContinuousLinearMap.coeLM 𝕜)
  have hW : (ψ : Module.Dual 𝕜 E) ∈ W.dualCoannihilator.dualAnnihilator := by
    simp only [mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply] at hψ
    simp only [mem_dualAnnihilator, mem_dualCoannihilator]
    intro e he
    exact hψ e fun g hg ↦ he g (mem_map_of_mem hg)
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq] at hW
  obtain ⟨g, hg, hgψ⟩ := hW
  rwa [← ContinuousLinearMap.coe_injective hgψ]

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
    simp only [mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply] at hx
    obtain ⟨f, hf, _, hfx⟩ := exists_dual_eq_infDist S x
    have hzero : (infDist x (S : Set E) : 𝕜) = 0 := hfx.symm.trans (hx f hf)
    exact (mem_closure_iff_infDist_zero S.nonempty).mpr (by exact_mod_cast hzero)
  · refine S.topologicalClosure_minimal ?_ (isClosed_orthogonalBilin_topDualPairing _)
    intro x hx
    simp only [mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply]
    intro f hf
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
    rw [← orthogonalBilin_topologicalClosure_topDualPairing_flip S, h]
    ext f
    simp only [Submodule.mem_bot, Submodule.mem_orthogonalBilin, LinearMap.flip_apply,
      topDualPairing_apply]
    constructor
    · intro hf
      apply ContinuousLinearMap.ext
      intro x
      simpa only [zero_apply] using hf x (Submodule.mem_top)
    · rintro rfl
      simp
  · intro h
    rw [← orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure S, h,
      Submodule.orthogonalBilin_bot]

end RCLike

end Submodule

/-! ### Maps onto the dual of a finite-dimensional space -/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- For a symmetric map `H : E → E*` and a functional `w` on a finite-dimensional space, the map
`(τ, ξ) ↦ τ • w + H ξ` from `𝕜 × E` to the dual of `E` is onto exactly when no nonzero vector lies
in the kernels of both `H` and `w`. By symmetry the vectors annihilating the range of this map are
those killed by both `H` and `w`, and a subspace of the dual with no nonzero annihilating vector is
the whole dual. For `H` the Hessian of a function and `w` the parameter derivative of the
differential, this is the transversality condition of a one-parameter family of functions. -/
theorem surjective_smul_add_apply_iff {H : E →L[𝕜] StrongDual 𝕜 E} (hH : ∀ u v, H u v = H v u)
    (w : StrongDual 𝕜 E) :
    Function.Surjective (fun p : 𝕜 × E ↦ p.1 • w + H p.2) ↔ ∀ v, H v = 0 → w v = 0 → v = 0 := by
  constructor
  · intro hs v hHv hwv
    by_contra hv
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual 𝕜 E, φ v ≠ 0 := by
      by_contra! h
      exact hv ((Module.forall_dual_apply_eq_zero_iff 𝕜 v).1 h)
    obtain ⟨p, hp⟩ := hs (LinearMap.toContinuousLinearMap φ)
    have h := congrArg (fun ψ : StrongDual 𝕜 E ↦ ψ v) hp
    simp only [add_apply, smul_apply, hwv, smul_zero, hH p.2 v, hHv, zero_apply, zero_add,
      LinearMap.coe_toContinuousLinearMap'] at h
    exact hφ h.symm
  · intro hker
    let L : 𝕜 × E →ₗ[𝕜] StrongDual 𝕜 E :=
      (LinearMap.fst 𝕜 𝕜 E).smulRight w + (H : E →ₗ[𝕜] StrongDual 𝕜 E) ∘ₗ LinearMap.snd 𝕜 𝕜 E
    have hL : ⇑L = fun p : 𝕜 × E ↦ p.1 • w + H p.2 := by
      ext p : 1
      simp [L]
    rw [← hL, ← LinearMap.range_eq_top]
    have hpre : (LinearMap.range L).orthogonalBilin (topDualPairing 𝕜 E) = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun v hv ↦ hker v ?_ ?_
      · ext u
        have := Submodule.mem_orthogonalBilin.1 hv (H u) ⟨((0 : 𝕜), u), by simp [L]⟩
        simpa [hH u v] using this
      · have := Submodule.mem_orthogonalBilin.1 hv w ⟨((1 : 𝕜), (0 : E)), by simp [L]⟩
        simpa using this
    rw [← Submodule.orthogonalBilin_orthogonalBilin_topDualPairing_flip_eq_of_finiteDimensional
      (LinearMap.range L), hpre, Submodule.orthogonalBilin_bot]

end ContinuousLinearMap
