/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Topological properties of C⋆-algebra homomorphisms and equivalences

A `⋆`-algebra homomorphism between complex C⋆-algebras is automatically continuous, so its
two-sided ideal kernel is closed (`NonUnitalStarAlgHom.isClosed_ker`, stated for any morphism
class, so it covers unital `⋆`-homomorphisms and `⋆`-equivalences as well).
A `⋆`-homomorphism between complex C⋆-algebras is contractive, so it bundles as a continuous
linear map `NonUnitalStarAlgHom.toContinuousLinearMap` of norm at most `1`.
A `⋆`-algebra equivalence of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it
bundles as a continuous linear equivalence `StarAlgEquiv.toContinuousLinearEquiv` and as a linear
isometric equivalence `StarAlgEquiv.toLinearIsometryEquiv`, whose restriction to self-adjoint
elements is the real-linear isometric equivalence `StarAlgEquiv.selfAdjointLinearIsometryEquiv`.

Since `⋆`-homomorphisms between C⋆-algebras are contractive, any family of them is
equicontinuous. Pointwise convergence of such a family to a `⋆`-homomorphism, along any filter,
therefore passes from a set to the closure of the `⋆`-subalgebra it generates
(`NonUnitalStarAlgHom.tendsto_of_dense_adjoin`): it suffices to check it on generators.

Contractivity (`NonUnitalStarAlgHom.dist_apply_le`) also shows that a sequence of them that is
pointwise Cauchy on a dense set converges pointwise to a `⋆`-homomorphism
(`NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq`), and that pointwise convergence passes to
convergent arguments (`NonUnitalStarAlgHom.tendsto_apply_of_tendsto`).
These are the limit steps of approximate intertwining arguments.
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

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A `⋆`-homomorphism between C⋆-algebras as a continuous linear map. It has norm at most `1`
because `⋆`-homomorphisms between C⋆-algebras are contractive. -/
def toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous (φ : A →ₗ[ℂ] B) 1 fun a => by
    simpa using NonUnitalStarAlgHom.norm_apply_le φ a

@[simp]
theorem coe_toContinuousLinearMap (φ : A →⋆ₙₐ[ℂ] B) : ⇑φ.toContinuousLinearMap = φ :=
  (rfl)

/-- A `⋆`-homomorphism between C⋆-algebras has norm at most `1` as a continuous linear map. -/
theorem norm_toContinuousLinearMap_le (φ : A →⋆ₙₐ[ℂ] B) : ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

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

/-- `StarAlgEquiv.toContinuousLinearEquiv` acts by the underlying star-algebra equivalence. -/
@[simp]
theorem coe_toContinuousLinearEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.toContinuousLinearEquiv`. -/
@[simp]
theorem toContinuousLinearEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toContinuousLinearEquiv.symm = e.symm.toContinuousLinearEquiv :=
  (rfl)

/-- A star-algebra equivalence of complex C⋆-algebras as a `ℂ`-linear isometric equivalence. -/
noncomputable def toLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) : A ≃ₗᵢ[ℂ] B where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := map_add e
  map_smul' := map_smul e
  norm_map' := StarAlgEquiv.norm_map e

/-- `StarAlgEquiv.toLinearIsometryEquiv` acts by the underlying star-algebra equivalence. -/
@[simp]
theorem coe_toLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑e.toLinearIsometryEquiv = e :=
  (rfl)

/-- Evaluating `StarAlgEquiv.toLinearIsometryEquiv` applies the star-algebra equivalence. -/
theorem toLinearIsometryEquiv_apply (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    e.toLinearIsometryEquiv a = e a :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.toLinearIsometryEquiv`. -/
@[simp]
theorem toLinearIsometryEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.toLinearIsometryEquiv.symm = e.symm.toLinearIsometryEquiv :=
  (rfl)

/-- Coercing `StarAlgEquiv.toLinearIsometryEquiv` to a continuous linear equivalence recovers
`StarAlgEquiv.toContinuousLinearEquiv`. -/
@[simp]
theorem toContinuousLinearEquiv_toLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) :
    e.toLinearIsometryEquiv.toContinuousLinearEquiv = e.toContinuousLinearEquiv :=
  (rfl)

/-- Restricting a star-algebra equivalence of complex C⋆-algebras to the self-adjoint elements gives
an `ℝ`-linear isometric equivalence `selfAdjoint A ≃ₗᵢ[ℝ] selfAdjoint B`. -/
noncomputable def selfAdjointLinearIsometryEquiv (e : A ≃⋆ₐ[ℂ] B) :
    selfAdjoint A ≃ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨e a.val, a.property.map e⟩
  invFun b := ⟨e.symm b.val, b.property.map e.symm⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)
  map_add' a₁ a₂ := Subtype.ext (map_add e a₁.val a₂.val)
  map_smul' r a := Subtype.ext <| by
    simp only [RingHom.id_apply, selfAdjoint.val_smul, ← Complex.coe_smul, map_smul]
  norm_map' a := StarAlgEquiv.norm_map e a.val

/-- The underlying element of `e.selfAdjointLinearIsometryEquiv a` is `e a`. -/
@[simp]
theorem coe_selfAdjointLinearIsometryEquiv_apply (e : A ≃⋆ₐ[ℂ] B) (a : selfAdjoint A) :
    (e.selfAdjointLinearIsometryEquiv a : B) = e a.val :=
  (rfl)

/-- Taking the inverse commutes with `StarAlgEquiv.selfAdjointLinearIsometryEquiv`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    e.selfAdjointLinearIsometryEquiv.symm = e.symm.selfAdjointLinearIsometryEquiv :=
  (rfl)

/-- On unital C⋆-algebras, `selfAdjointLinearIsometryEquiv` preserves `1`. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_one {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) : e.selfAdjointLinearIsometryEquiv 1 = 1 :=
  Subtype.ext (map_one e)

/-- On commutative C⋆-algebras, `selfAdjointLinearIsometryEquiv` preserves multiplication. -/
@[simp]
theorem selfAdjointLinearIsometryEquiv_mul {A B : Type*} [NonUnitalCommCStarAlgebra A]
    [NonUnitalCommCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) (a₁ a₂ : selfAdjoint A) :
    e.selfAdjointLinearIsometryEquiv (a₁ * a₂) =
      e.selfAdjointLinearIsometryEquiv a₁ * e.selfAdjointLinearIsometryEquiv a₂ :=
  Subtype.ext (map_mul e a₁.val a₂.val)

end StarAlgEquiv

namespace NonUnitalStarAlgHom

open Filter Topology

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A `⋆`-homomorphism between C⋆-algebras is `1`-Lipschitz: it does not increase distances. -/
theorem dist_apply_le (φ : F) (x y : A) : dist (φ x) (φ y) ≤ dist x y := by
  simpa only [dist_eq_norm, ← map_sub] using norm_apply_le φ (x - y)

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
    refine ⟨N, fun n hn ↦ ?_⟩
    calc dist (f n x) (f N x)
        ≤ dist (f n x) (f n a) + dist (f n a) (f N a) + dist (f N a) (f N x) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (f N a)]
        gcongr
        · exact (dist_apply_le (f n) x a).trans_lt hxa
        · exact hN n hn
        · exact (dist_apply_le (f N) x a).trans_lt hxa
      _ = ε := by ring
  choose g hg using fun x ↦ cauchySeq_tendsto_of_complete (hc x)
  have hlim := tendsto_pi_nhds.mpr hg
  have hlin : Tendsto (fun n x ↦ (f n : A →ₗ[ℂ] B) x) atTop (𝓝 g) := by
    simpa only [LinearMap.coe_ofClass] using hlim
  exact ⟨{ linearMapOfTendsto g (fun n ↦ (f n : A →ₗ[ℂ] B)) hlin, mulHomOfTendsto g f hlim with
      map_zero' := map_zero (linearMapOfTendsto g _ hlin)
      map_star' x := tendsto_nhds_unique (hg (star x)) (by simpa [map_star] using (hg x).star) },
    fun a ↦ by simpa using hg a⟩

/-- Pointwise convergence of `⋆`-homomorphisms between C⋆-algebras passes to convergent
arguments: if `f i` tends to `g` pointwise and `x i` tends to `a`, then `f i (x i)` tends to
`g a`. -/
theorem tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → F} {g : A → B}
    (hf : ∀ a, Tendsto (fun i ↦ f i a) l (𝓝 (g a))) {x : ι → A} {a : A}
    (hx : Tendsto x l (𝓝 a)) : Tendsto (fun i ↦ f i (x i)) l (𝓝 (g a)) := by
  rw [tendsto_iff_dist_tendsto_zero] at hx ⊢
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_)
    (by simpa using hx.add (tendsto_iff_dist_tendsto_zero.mp (hf a)))
  calc dist (f i (x i)) (g a) ≤ dist (f i (x i)) (f i a) + dist (f i a) (g a) :=
        dist_triangle _ _ _
    _ ≤ dist (x i) a + dist (f i a) (g a) := by
        gcongr
        exact dist_apply_le (f i) (x i) a

end NonUnitalStarAlgHom
