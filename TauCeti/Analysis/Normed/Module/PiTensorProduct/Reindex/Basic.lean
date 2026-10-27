/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Topology

/-!
# Symmetry of the projective tensor topology

Reindexing a finite tensor product preserves its projective seminorm when the factor seminorms
are reindexed along with the factors. Consequently, permutations and relabelings of the factors
give continuous linear equivalences for the projective topology. This is the symmetry map whose
extension to separated completions gives the completed tensor flip.

No topology on the individual factors, separation, or completeness is required for these
statements. The scalar field may be trivially normed. The construction uses Mathlib's algebraic
`PiTensorProduct.reindex`; seminorm preservation follows from the maximal property of
`PiTensorProduct.projectiveSeminormOf`, rather than a new tensor construction.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {ι κ 𝕜 : Type*} [Fintype ι] [Fintype κ] [NormedField 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]

namespace ProjectiveTensorProduct

variable {σ : ι → Type*} (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i))

/-- Relabel the factors of a projective tensor product, carrying each defining seminorm family
with its factor. Both directions are continuous for the projective topologies. -/
noncomputable def reindex (e : ι ≃ κ) :
    ProjectiveTensorProduct p ≃L[𝕜] ProjectiveTensorProduct (fun j => p (e.symm j)) := by
  let T := (toPiTensorProductLinearEquiv p).trans
    ((PiTensorProduct.reindex 𝕜 E e).trans
      (toPiTensorProductLinearEquiv (fun j => p (e.symm j))).symm)
  refine { T with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply WithSeminorms.continuous_of_isBounded (withSeminorms p)
      (withSeminorms (fun j => p (e.symm j)))
    intro t
    obtain ⟨s, rfl⟩ := (Equiv.piCongrLeft' (fun i => Finset (σ i)) e).surjective t
    refine ⟨{s}, 1, ?_⟩
    rw [Finset.sup_singleton]
    intro x
    simpa [T, seminormFamily_apply] using
      (projectiveSeminormOf_reindex (fun i => (s i).sup (p i)) e x.toPiTensorProduct).le
  · refine WithSeminorms.continuous_of_isBounded
      (withSeminorms (fun j => p (e.symm j))) (withSeminorms p) T.symm.toLinearMap ?_
    intro s
    refine ⟨{fun j => s (e.symm j)}, 1, ?_⟩
    rw [Finset.sup_singleton]
    intro x
    have h := projectiveSeminormOf_reindex (fun i => (s i).sup (p i)) e
      ((PiTensorProduct.reindex 𝕜 E e).symm x.toPiTensorProduct)
    simpa [T, seminormFamily_apply] using h.ge

/-- The topological reindexing has Mathlib's algebraic reindexing as its underlying map. -/
@[simp] theorem toPiTensorProduct_reindex (e : ι ≃ κ) (x : ProjectiveTensorProduct p) :
    (reindex p e x).toPiTensorProduct =
      PiTensorProduct.reindex 𝕜 E e x.toPiTensorProduct := by
  simp [reindex]

/-- Reindexing carries pure tensors to the correspondingly reindexed pure tensors. -/
@[simp] theorem reindex_tprod (e : ι ≃ κ) (x : ∀ i, E i) :
    reindex p e ⟨⨂ₜ[𝕜] i, x i⟩ =
      tprod (fun j => p (e.symm j)) (fun j => x (e.symm j)) := by
  apply ext
  simp

/-- The inverse reindexing recovers a pure tensor from its reindexed factors. -/
@[simp] theorem reindex_symm_tprod (e : ι ≃ κ) (x : ∀ i, E i) :
    (reindex p e).symm ⟨⨂ₜ[𝕜] j, x (e.symm j)⟩ = tprod p x := by
  apply (reindex p e).injective
  simpa only [tprod_apply, ContinuousLinearEquiv.apply_symm_apply] using
    (reindex_tprod p e x).symm

variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]
variable {τ : ι → Type*} (q : ∀ i, SeminormFamily 𝕜 (G i) (τ i))

/-- Relabeling tensor factors commutes with tensoring a family of linear maps. -/
theorem map_reindex (e : ι ≃ κ) (f : ∀ i, E i →ₗ[𝕜] G i)
    (x : ProjectiveTensorProduct p) :
    map (fun j => p (e.symm j)) (fun j => q (e.symm j)) (fun j => f (e.symm j))
      (reindex p e x) = reindex q e (map p q f x) := by
  apply ext
  simpa only [toPiTensorProduct_map, toPiTensorProduct_reindex] using
    PiTensorProduct.map_reindex f e x.toPiTensorProduct

end ProjectiveTensorProduct

end TauCeti
