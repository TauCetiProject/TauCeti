/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal

/-!
# Topological properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous, so its
two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for any morphism
class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well).
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv`.

Since `⋆`-homomorphisms of C⋆-algebras are contractive, a sequence of them that is pointwise
Cauchy on a dense set converges pointwise to a `⋆`-homomorphism
(`NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq`), and pointwise convergence passes to
convergent arguments (`NonUnitalStarAlgHom.tendsto_apply_of_tendsto`). These are the limit
steps of approximate intertwining arguments.
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

namespace NonUnitalStarAlgHom

open Filter Topology

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A sequence of `⋆`-homomorphisms between C⋆-algebras that is pointwise Cauchy on a dense set
converges pointwise on the whole source, and the pointwise limit is a `⋆`-homomorphism. -/
theorem exists_tendsto_of_cauchySeq {f : ℕ → F} {S : Set A} (hS : Dense S)
    (hf : ∀ a ∈ S, CauchySeq fun n ↦ f n a) :
    ∃ θ : A →⋆ₙₐ[ℂ] B, ∀ a, Tendsto (fun n ↦ f n a) atTop (𝓝 (θ a)) := by
  have hc (x : A) : CauchySeq fun n ↦ f n x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨a, ha, hxa⟩ := hS.exists_dist_lt x (by positivity : 0 < ε / 3)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp (hf a ha) (ε / 3) (by positivity)
    have hle (n : ℕ) : dist (f n x) (f n a) ≤ dist x a := by
      simpa only [dist_eq_norm, ← map_sub] using norm_apply_le (f n) (x - a)
    refine ⟨N, fun n hn ↦ ?_⟩
    calc dist (f n x) (f N x)
        ≤ dist (f n x) (f n a) + dist (f n a) (f N a) + dist (f N a) (f N x) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (f N a)]
        gcongr
        · exact (hle n).trans_lt hxa
        · exact hN n hn
        · exact (hle N).trans_lt hxa
      _ = ε := by ring
  choose g hg using fun x ↦ cauchySeq_tendsto_of_complete (hc x)
  refine ⟨{
      toFun := g
      map_smul' := fun c x ↦ tendsto_nhds_unique (hg (c • x))
        (by simpa only [map_smul, MonoidHom.id_apply] using (hg x).const_smul c)
      map_zero' := tendsto_nhds_unique (hg 0) (by simpa only [map_zero] using tendsto_const_nhds)
      map_add' := fun x y ↦ tendsto_nhds_unique (hg (x + y))
        (by simpa only [map_add] using (hg x).add (hg y))
      map_mul' := fun x y ↦ tendsto_nhds_unique (hg (x * y))
        (by simpa only [map_mul] using (hg x).mul (hg y))
      map_star' := fun x ↦ tendsto_nhds_unique (hg (star x))
        (by simpa only [map_star] using (hg x).star) }, hg⟩

/-- Pointwise convergence of `⋆`-homomorphisms between C⋆-algebras passes to convergent
arguments: if `f i` tends to `g` pointwise and `x i` tends to `a`, then `f i (x i)` tends to
`g a`. -/
theorem tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → F} {g : A → B}
    (hf : ∀ a, Tendsto (fun i ↦ f i a) l (𝓝 (g a))) {x : ι → A} {a : A}
    (hx : Tendsto x l (𝓝 a)) : Tendsto (fun i ↦ f i (x i)) l (𝓝 (g a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa using hx.add (tendsto_iff_norm_sub_tendsto_zero.mp (hf a)))
  calc ‖f i (x i) - g a‖ ≤ ‖f i (x i) - f i a‖ + ‖f i a - g a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖x i - a‖ + ‖f i a - g a‖ := by
        gcongr
        simpa only [← map_sub] using norm_apply_le (f i) (x i - a)

end NonUnitalStarAlgHom
