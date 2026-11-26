/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.Analysis.Normed.Module.Annihilator
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic

/-!
# Weak-star double annihilators

The annihilator of a submodule of a topological module is weak-star closed; this needs only a
commutative topological semiring of scalars in which points are closed. Conversely, over `ℝ` or
`ℂ`, the annihilator of the preannihilator of a submodule of the continuous dual is its
weak-star closure. These statements use `Submodule.orthogonalBilin` for the canonical
`topDualPairing`; `StrongDual.toWeakDual` explicitly transports the continuous dual to the
weak-star topology. No completeness, separation, or local convexity of the original space is
needed.

For a seminormed space `E`, combining this with the norm double-annihilator theorem shows that
annihilators and preannihilators are mutually inverse, inclusion-reversing bijections between the
norm-closed subspaces of `E` and the weak-star closed subspaces of its dual
(`ClosedSubmodule.annihilatorOrderIso`).

## Main results

* `Submodule.isClosed_map_orthogonalBilin_topDualPairing_flip`: annihilators are weak-star
  closed.
* `Submodule.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure`: the annihilator of
  the preannihilator of a subspace of the dual is its weak-star closure.
* `ClosedSubmodule.annihilatorOrderIso`: closed subspaces of `E` and weak-star closed subspaces of
  its dual correspond, reversing inclusion.

The double-annihilator theorem is the standard duality result discussed in Megginson,
*An Introduction to Banach Space Theory*, §2.6. Its formal proof uses the weak representation
theorem `WeakDual.exists_forall_apply_eq_apply` and geometric Hahn--Banach separation in the
weak dual.
-/

public section

open Set

namespace Submodule

variable {𝕜 E : Type*}

section Closedness

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [T1Space 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The annihilator of a submodule, transported to the weak dual, is weak-star closed. -/
theorem isClosed_map_orthogonalBilin_topDualPairing_flip (F : Submodule 𝕜 E) :
    IsClosed ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) := by
  have heq : ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) =
      ⋂ x ∈ F, (fun f : WeakDual 𝕜 E ↦ f x) ⁻¹' {0} := by
    ext f
    refine (mem_map_equiv (e := StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)) _).trans ?_
    simp
  rw [heq]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage (WeakDual.eval_continuous x)

end Closedness

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The double annihilator of a submodule of the continuous dual, transported to the weak dual,
is its weak-star closure. The first orthogonal complement is the preannihilator in `E`; the
second is its annihilator in the continuous dual. -/
theorem map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) :
    ((G.orthogonalBilin (topDualPairing 𝕜 E)).orthogonalBilin
      (topDualPairing 𝕜 E).flip).map StrongDual.toWeakDual.toLinearMap =
      (G.map StrongDual.toWeakDual.toLinearMap).topologicalClosure := by
  -- The weak-dual synonym inherits these structures from the canonical dual pairing.
  let : AddCommGroup (WeakDual 𝕜 E) :=
    inferInstanceAs (AddCommGroup (WeakBilin (topDualPairing 𝕜 E)))
  let : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
    inferInstanceAs (IsTopologicalAddGroup (WeakBilin (topDualPairing 𝕜 E)))
  let H := G.map StrongDual.toWeakDual.toLinearMap
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    by_contra hn
    obtain ⟨l, u, hG, hf'⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (H.topologicalClosure.restrictScalars ℝ).convex H.isClosed_topologicalClosure hn
    obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply l
    have hG' : ∀ g ∈ G, RCLike.re (g x) < u := fun g hg ↦ by
      simpa only [hx, LinearEquiv.coe_coe, StrongDual.toWeakDual_apply] using
        hG _ (H.le_topologicalClosure (mem_map_of_mem hg))
    -- A real upper bound on a functional over a subspace forces the functional to vanish there.
    have hxG : x ∈ G.orthogonalBilin (topDualPairing 𝕜 E) := by
      refine mem_orthogonalBilin.mpr fun g hg ↦ ?_
      rw [topDualPairing_apply]
      by_contra hne
      have hlt := hG' _ (G.smul_mem (((u + 1 : ℝ) : 𝕜) / g x) hg)
      rw [smul_apply, smul_eq_mul, div_mul_cancel₀ _ hne, RCLike.ofReal_re] at hlt
      linarith
    have hfx : f x = 0 := by simpa using mem_orthogonalBilin.mp hf x hxG
    have hu := hG' 0 G.zero_mem
    rw [hx, LinearEquiv.coe_coe, StrongDual.toWeakDual_apply, hfx, map_zero] at hf'
    rw [zero_apply, map_zero] at hu
    exact (hu.trans hf').false
  · exact H.topologicalClosure_minimal
      (map_mono (G.le_orthogonalBilin_flip_orthogonalBilin (B := topDualPairing 𝕜 E)))
      (G.orthogonalBilin (topDualPairing 𝕜 E)).isClosed_map_orthogonalBilin_topDualPairing_flip

end Submodule

/-! ### Closed subspaces and weak-star closed subspaces of the dual -/

namespace ClosedSubmodule

open OrderDual

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The preannihilator of the annihilator of a closed subspace, the annihilator taken in the weak
dual, is the subspace itself. -/
theorem orthogonalBilin_comap_map_orthogonalBilin_flip (S : ClosedSubmodule 𝕜 E) :
    ((((S : Submodule 𝕜 E).orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap).comap StrongDual.toWeakDual.toLinearMap).orthogonalBilin
        (topDualPairing 𝕜 E) = S := by
  rw [Submodule.comap_map_eq_of_injective StrongDual.toWeakDual.injective,
    Submodule.orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure,
    S.isClosed.submodule_topologicalClosure_eq]

/-- The annihilator of the preannihilator of a weak-star closed subspace of the dual is the
subspace itself. -/
theorem map_orthogonalBilin_flip_orthogonalBilin_comap (G : ClosedSubmodule 𝕜 (WeakDual 𝕜 E)) :
    Submodule.map StrongDual.toWeakDual.toLinearMap
      ((((G : Submodule 𝕜 (WeakDual 𝕜 E)).comap
        StrongDual.toWeakDual.toLinearMap).orthogonalBilin (topDualPairing 𝕜 E)).orthogonalBilin
          (topDualPairing 𝕜 E).flip) = G := by
  rw [Submodule.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure,
    Submodule.map_comap_eq_of_surjective StrongDual.toWeakDual.surjective,
    G.isClosed.submodule_topologicalClosure_eq]

variable (𝕜 E) in
/-- **Annihilator duality.** Taking annihilators is an inclusion-reversing bijection between the
norm-closed subspaces of `E` and the weak-star closed subspaces of its dual; the inverse takes
preannihilators. This packages the two double-annihilator theorems
`Submodule.orthogonalBilin_orthogonalBilin_topDualPairing_eq_topologicalClosure` and
`Submodule.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure`. -/
noncomputable def annihilatorOrderIso :
    ClosedSubmodule 𝕜 E ≃o (ClosedSubmodule 𝕜 (WeakDual 𝕜 E))ᵒᵈ where
  toFun S := toDual ⟨((S : Submodule 𝕜 E).orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap,
      Submodule.isClosed_map_orthogonalBilin_topDualPairing_flip _⟩
  invFun G := ⟨((ofDual G).toSubmodule.comap
      StrongDual.toWeakDual.toLinearMap).orthogonalBilin (topDualPairing 𝕜 E),
      Submodule.isClosed_orthogonalBilin_topDualPairing _⟩
  left_inv S := toSubmodule_injective (orthogonalBilin_comap_map_orthogonalBilin_flip S)
  right_inv G := congrArg toDual
    (toSubmodule_injective (map_orthogonalBilin_flip_orthogonalBilin_comap (ofDual G)))
  map_rel_iff' {S T} := by
    -- The goal is stated for the bundled `Equiv.mk`; rewriting its coercion with
    -- `Equiv.coe_fn_mk` gives an ill-typed motive, so `change` only unfolds that coercion to
    -- expose the order-dual flip `toDual _ ≤ toDual _`, which `toDual_le_toDual` then rewrites.
    change toDual (⟨_, _⟩ : ClosedSubmodule 𝕜 (WeakDual 𝕜 E)) ≤ toDual ⟨_, _⟩ ↔ S ≤ T
    rw [OrderDual.toDual_le_toDual, ← toSubmodule_le_toSubmodule, ← toSubmodule_le_toSubmodule]
    refine ⟨fun h ↦ ?_, fun h ↦ Submodule.map_mono (Submodule.orthogonalBilin_le h)⟩
    rw [← orthogonalBilin_comap_map_orthogonalBilin_flip S,
      ← orthogonalBilin_comap_map_orthogonalBilin_flip T]
    exact Submodule.orthogonalBilin_le (Submodule.comap_mono h)

/-- The annihilator of a closed subspace, as a subspace of the weak dual. -/
@[simp]
theorem toSubmodule_annihilatorOrderIso_apply (S : ClosedSubmodule 𝕜 E) :
    (ofDual (annihilatorOrderIso 𝕜 E S)).toSubmodule =
      ((S : Submodule 𝕜 E).orthogonalBilin (topDualPairing 𝕜 E).flip).map
        StrongDual.toWeakDual.toLinearMap :=
  (rfl)

/-- The preannihilator of a weak-star closed subspace of the dual. -/
@[simp]
theorem toSubmodule_annihilatorOrderIso_symm_apply (G : (ClosedSubmodule 𝕜 (WeakDual 𝕜 E))ᵒᵈ) :
    ((annihilatorOrderIso 𝕜 E).symm G : Submodule 𝕜 E) =
      ((ofDual G).toSubmodule.comap
        StrongDual.toWeakDual.toLinearMap).orthogonalBilin (topDualPairing 𝕜 E) :=
  (rfl)

/-- A functional lies in the annihilator of a closed subspace exactly when it vanishes on it. -/
@[simp]
theorem mem_annihilatorOrderIso_iff {S : ClosedSubmodule 𝕜 E} {φ : WeakDual 𝕜 E} :
    φ ∈ ofDual (annihilatorOrderIso 𝕜 E S) ↔ ∀ x ∈ S, φ x = 0 := by
  rw [← mem_toSubmodule_iff, toSubmodule_annihilatorOrderIso_apply]
  refine (Submodule.mem_map_equiv (e := StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)) _).trans ?_
  simp

/-- A vector lies in the preannihilator of a weak-star closed subspace of the dual exactly when
every functional of the subspace vanishes on it. -/
@[simp]
theorem mem_annihilatorOrderIso_symm_iff {G : (ClosedSubmodule 𝕜 (WeakDual 𝕜 E))ᵒᵈ} {x : E} :
    x ∈ (annihilatorOrderIso 𝕜 E).symm G ↔ ∀ φ ∈ ofDual G, φ x = 0 := by
  rw [← mem_toSubmodule_iff, toSubmodule_annihilatorOrderIso_symm_apply]
  simp only [Submodule.mem_orthogonalBilin, Submodule.mem_comap, mem_toSubmodule_iff,
    topDualPairing_apply]
  refine ⟨fun h φ hφ ↦ ?_, fun h n hn ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := StrongDual.toWeakDual.surjective φ
    simpa only [LinearEquiv.coe_coe, StrongDual.toWeakDual_apply] using h n hφ
  · simpa only [LinearEquiv.coe_coe, StrongDual.toWeakDual_apply] using h _ hn

end ClosedSubmodule
