/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Topological properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous, so its
two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for any morphism
class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well).
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.

Since `⋆`-homomorphisms between C⋆-algebras are contractive, any family of them is
equicontinuous. Pointwise convergence of such a family to a `⋆`-homomorphism, along any filter,
therefore passes from a set to the closure of the `⋆`-subalgebra it generates
(`NonUnitalStarAlgHom.tendsto_of_dense_adjoin`): it suffices to check it on generators.
-/

public section

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras (unital or not, and
in any morphism class) is closed. -/
instance isClosed_ker : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

open Filter Topology CStarAlgebra in
/-- Pointwise convergence of a family of `⋆`-homomorphisms between C⋆-algebras to a
`⋆`-homomorphism, along any filter, holds everywhere once it holds on a set whose generated
`⋆`-subalgebra is dense. -/
theorem tendsto_of_dense_adjoin {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₙₐ[ℂ] B}
    {g : A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (h : ∀ a ∈ s, Tendsto (fun i ↦ f i a) l (𝓝 (g a))) (a : A) :
    Tendsto (fun i ↦ f i a) l (𝓝 (g a)) := by
  -- The points of convergence form a `⋆`-subalgebra containing `s` ...
  let S : NonUnitalStarSubalgebra ℂ A :=
    { carrier := {a | Tendsto (fun i ↦ f i a) l (𝓝 (g a))}
      add_mem' := fun {a b} ha hb ↦ by simpa only [Set.mem_ofPred_eq, map_add] using ha.add hb
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using tendsto_const_nhds
      mul_mem' := fun {a b} ha hb ↦ by simpa only [Set.mem_ofPred_eq, map_mul] using ha.mul hb
      smul_mem' := fun c a ha ↦ by
        simpa only [Set.mem_ofPred_eq, map_smul] using ha.const_smul c
      star_mem' := fun {a} ha ↦ by simpa only [Set.mem_ofPred_eq, map_star] using ha.star }
  -- ... and, the family being uniformly contractive, a closed set.
  have hcl : IsClosed (S : Set A) := by
    have he : Equicontinuous fun i ↦ ⇑(f i) := by
      refine Metric.equicontinuous_of_continuity_modulus id tendsto_id _ fun a b i ↦ ?_
      simpa only [id_eq, dist_eq_norm, ← map_sub] using norm_apply_le (f i) (a - b)
    exact he.isClosed_setOfPred_tendsto (map_continuous g)
  have hle : closure (NonUnitalStarAlgebra.adjoin ℂ s : Set A) ⊆ S :=
    hcl.closure_subset_iff.mpr (NonUnitalStarAlgebra.adjoin_le h)
  exact hle (hs.closure_eq ▸ Set.mem_univ a)

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A star-algebra equivalence of C⋆-algebras as a continuous linear equivalence. Both directions
are continuous because star-algebra equivalences of C⋆-algebras are isometric. -/
def toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃L[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  continuous_toFun := (StarAlgEquiv.isometry e).continuous
  continuous_invFun := (StarAlgEquiv.isometry e.symm).continuous

@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

end StarAlgEquiv
