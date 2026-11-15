/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import TauCeti.Analysis.Normed.Operator.Basic
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
public import TauCeti.Topology.Algebra.Star.StarAlgHom

/-!
# Topological and point-norm properties of C⋆-algebra homomorphisms

Every `⋆`-algebra homomorphism between complex C⋆-algebras is contractive
(`NonUnitalStarAlgHom.norm_apply_le`), hence `1`-Lipschitz
(`NonUnitalStarAlgHom.lipschitzWith_one`), so its two-sided ideal kernel is closed
(`NonUnitalStarAlgHom.isClosed_ker`) and every family of `⋆`-homomorphisms between C⋆-algebras is
uniformly equicontinuous (`NonUnitalStarAlgHom.uniformEquicontinuous`). A `⋆`-algebra equivalence
of complex C⋆-algebras is isometric (`StarAlgEquiv.isometry`), so it bundles as a continuous linear
equivalence `StarAlgEquiv.toContinuousLinearEquiv`.

Equipped with the point-norm topology from `TauCeti.Topology.Algebra.Star.StarAlgHom`, evaluation
`(φ, a) ↦ φ a` and composition `(ψ, φ) ↦ ψ.comp φ` of `⋆`-homomorphisms between C⋆-algebras are
jointly continuous (`NonUnitalStarAlgHom.instContinuousEval`,
`NonUnitalStarAlgHom.continuous_comp`, and their `StarAlgHom` counterparts). Uniform
equicontinuity and completeness of `A →⋆ₙₐ[ℂ] B` imply that point-norm convergence and Cauchy
convergence can be checked on any dense subset or any generating set of a dense non-unital
`⋆`-subalgebra (`NonUnitalStarAlgHom.tendsto_of_tendsto_adjoin`,
`NonUnitalStarAlgHom.exists_tendsto_of_cauchy_map_adjoin`).
-/

public section

open Filter Topology

namespace NonUnitalStarAlgHom

section MorphismClass

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open scoped CStarAlgebra in
/-- The two-sided ideal kernel of any `⋆`-homomorphism between C⋆-algebras (unital or not, and
in any morphism class) is closed. -/
instance isClosed_ker (φ : F) : IsClosed (TwoSidedIdeal.ker φ : Set A) :=
  TwoSidedIdeal.isClosed_ker (map_continuous φ)

/-- Every `⋆`-homomorphism between complex C⋆-algebras is `1`-Lipschitz. -/
theorem lipschitzWith_one (φ : F) : LipschitzWith 1 φ :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using norm_apply_le φ (a - b)

/-- Any family of `⋆`-homomorphisms between complex C⋆-algebras is uniformly equicontinuous. -/
theorem uniformEquicontinuous {ι : Type*} (φ : ι → F) :
    UniformEquicontinuous fun i a ↦ φ i a :=
  Metric.uniformEquicontinuous_of_continuity_modulus id tendsto_id _ fun a b i ↦ by
    simpa only [id_eq, dist_eq_norm, ← map_sub] using norm_apply_le (φ i) (a - b)

/-- Any family of `⋆`-homomorphisms between complex C⋆-algebras is equicontinuous. -/
theorem equicontinuous {ι : Type*} (φ : ι → F) : Equicontinuous fun i a ↦ φ i a :=
  (uniformEquicontinuous φ).equicontinuous

end MorphismClass

section PointNorm

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Evaluation `(φ, a) ↦ φ a` on `A →⋆ₙₐ[ℂ] B` is jointly continuous for the point-norm topology
and the norm topologies on `A` and `B`. -/
instance instContinuousEval : ContinuousEval (A →⋆ₙₐ[ℂ] B) A B where
  continuous_eval :=
    AddMonoidHomClass.continuous_apply_of_bound (C := 1)
      (fun a ↦ (continuous_eval_const a).comp continuous_fst)
      (fun p a ↦ by simpa only [one_mul] using norm_apply_le p.1 a)
      continuous_snd

/-- Composition of `NonUnitalStarAlgHom`s between complex C⋆-algebras is jointly continuous in the
point-norm topology. -/
@[fun_prop]
theorem continuous_comp [NonUnitalCStarAlgebra C] :
    Continuous fun p : (B →⋆ₙₐ[ℂ] C) × (A →⋆ₙₐ[ℂ] B) ↦ p.1.comp p.2 :=
  continuous_iff.mpr fun a ↦
    continuous_eval.comp (continuous_fst.prodMk ((continuous_eval_const a).comp continuous_snd))

/-- Composition preserves point-norm convergence of `NonUnitalStarAlgHom`s between C⋆-algebras. -/
theorem tendsto_comp [NonUnitalCStarAlgebra C] {ι : Type*} {l : Filter ι}
    {ψ : ι → B →⋆ₙₐ[ℂ] C} {φ : ι → A →⋆ₙₐ[ℂ] B} {ψ₀ : B →⋆ₙₐ[ℂ] C} {φ₀ : A →⋆ₙₐ[ℂ] B}
    (hψ : Tendsto ψ l (𝓝 ψ₀)) (hφ : Tendsto φ l (𝓝 φ₀)) :
    Tendsto (fun i ↦ (ψ i).comp (φ i)) l (𝓝 (ψ₀.comp φ₀)) :=
  (continuous_comp.tendsto (ψ₀, φ₀)).comp (hψ.prodMk_nhds hφ)

/-- Pointwise convergence of `⋆`-homomorphisms on a dense subset extends to convergence in the
point-norm topology. -/
theorem tendsto_of_tendsto_of_dense {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₙₐ[ℂ] B}
    {φ : A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense s)
    (hf : ∀ a ∈ s, Tendsto (fun i ↦ f i a) l (𝓝 (φ a))) :
    Tendsto f l (𝓝 φ) := by
  open scoped CStarAlgebra in
  exact tendsto_iff_forall_tendsto.mpr <|
    hs.induction hf <| (equicontinuous f).isClosed_setOfPred_tendsto (map_continuous φ)

/-- Pointwise convergence of `⋆`-homomorphisms on a generating set of a dense non-unital
`⋆`-subalgebra extends to convergence in the point-norm topology. -/
theorem tendsto_of_tendsto_adjoin {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₙₐ[ℂ] B}
    {φ : A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (hf : ∀ a ∈ s, Tendsto (fun i ↦ f i a) l (𝓝 (φ a))) :
    Tendsto f l (𝓝 φ) := by
  refine tendsto_of_tendsto_of_dense hs fun a ha ↦ ?_
  induction ha using NonUnitalStarAlgebra.adjoin_induction with
  | mem x hx => exact hf x hx
  | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
  | zero => simp only [map_zero, tendsto_const_nhds]
  | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul hy
  | smul r x _ hx => simpa only [map_smul] using hx.const_smul r
  | star x _ hx => simpa only [map_star] using hx.star

/-- For any filter `l` and family `f : ι → A →⋆ₙₐ[ℂ] B`, the set of elements `a : A` along which
`i ↦ f i a` is Cauchy is closed in `A`. -/
theorem isClosed_setOf_cauchy_map {ι : Type*} (l : Filter ι) (f : ι → A →⋆ₙₐ[ℂ] B) :
    IsClosed {a : A | Cauchy (l.map fun i ↦ f i a)} := by
  rcases eq_or_neBot l with rfl | hl
  · have hemp : {a : A | Cauchy (Filter.map (fun i ↦ f i a) ⊥)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ h ↦ h.1.ne Filter.map_bot
    exact hemp ▸ isClosed_empty
  rw [← closure_subset_iff_isClosed]
  intro a ha
  simp only [Set.mem_ofPred_eq]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  obtain ⟨x, hx, hax⟩ := Metric.mem_closure_iff.mp ha (ε / 3) (by positivity)
  obtain ⟨t, htl, ht⟩ := (Metric.cauchy_iff.mp hx).2 (ε / 3) (by positivity)
  refine ⟨(fun i ↦ f i a) '' ((fun i ↦ f i x) ⁻¹' t),
    Filter.image_mem_map (Filter.mem_map.mp htl), ?_⟩
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  have hfi : dist (f i a) (f i x) ≤ dist a x := by
    simpa only [dist_eq_norm, ← map_sub] using norm_apply_le (f i) (a - x)
  have hfj : dist (f j x) (f j a) ≤ dist a x := by
    simpa only [dist_eq_norm, ← map_sub, norm_sub_rev x a] using norm_apply_le (f j) (x - a)
  have hij : dist (f i x) (f j x) < ε / 3 := ht (f i x) hi (f j x) hj
  linarith [dist_triangle4 (f i a) (f i x) (f j x) (f j a)]

/-- If `i ↦ f i a` is Cauchy along `l` on a dense subset of `A`, then `f` is Cauchy along `l` in
the point-norm uniformity. -/
theorem cauchy_map_of_cauchy_map_of_dense {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₙₐ[ℂ] B}
    {s : Set A} (hs : Dense s) (hf : ∀ a ∈ s, Cauchy (l.map fun i ↦ f i a)) :
    Cauchy (l.map f) := by
  rw [cauchy_iff_forall_cauchy]
  have hall := (isClosed_setOf_cauchy_map l f).closure_subset_iff.mpr hf
  intro a
  simpa only [Filter.map_map, Function.comp_def, Set.mem_ofPred_eq] using hall (hs a)

/-- If `i ↦ f i a` is Cauchy along a nontrivial filter `l` on a generating set of a dense
non-unital `⋆`-subalgebra of `A`, then `f` is Cauchy along `l` in the point-norm uniformity. -/
theorem cauchy_map_of_cauchy_map_adjoin {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (hf : ∀ a ∈ s, Cauchy (l.map fun i ↦ f i a)) :
    Cauchy (l.map f) := by
  refine cauchy_map_of_cauchy_map_of_dense hs fun a ha ↦ ?_
  rw [cauchy_map_iff_exists_tendsto]
  induction ha using NonUnitalStarAlgebra.adjoin_induction with
  | mem x hx => exact cauchy_map_iff_exists_tendsto.mp (hf x hx)
  | add x y _ _ hx hy =>
    obtain ⟨bx, hbx⟩ := hx
    obtain ⟨by', hby⟩ := hy
    exact ⟨bx + by', by simpa only [map_add] using hbx.add hby⟩
  | zero => exact ⟨0, by simp only [map_zero, tendsto_const_nhds]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨bx, hbx⟩ := hx
    obtain ⟨by', hby⟩ := hy
    exact ⟨bx * by', by simpa only [map_mul] using hbx.mul hby⟩
  | smul r x _ hx =>
    obtain ⟨bx, hbx⟩ := hx
    exact ⟨r • bx, by simpa only [map_smul] using hbx.const_smul r⟩
  | star x _ hx =>
    obtain ⟨bx, hbx⟩ := hx
    exact ⟨star bx, by simpa only [map_star] using hbx.star⟩

/-- A net of `⋆`-homomorphisms along a nontrivial filter that is pointwise Cauchy on a generating
set of a dense non-unital `⋆`-subalgebra converges in the point-norm topology to a
`⋆`-homomorphism. -/
theorem exists_tendsto_of_cauchy_map_adjoin {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (hf : ∀ a ∈ s, Cauchy (l.map fun i ↦ f i a)) :
    ∃ φ : A →⋆ₙₐ[ℂ] B, Tendsto f l (𝓝 φ) :=
  cauchy_map_iff_exists_tendsto.mp (cauchy_map_of_cauchy_map_adjoin hs hf)

/-- A sequence of `⋆`-homomorphisms that is pointwise Cauchy on a generating set of a dense
non-unital `⋆`-subalgebra converges in the point-norm topology to a `⋆`-homomorphism. -/
theorem exists_tendsto_of_cauchySeq_adjoin {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {f : ι → A →⋆ₙₐ[ℂ] B} {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (hf : ∀ a ∈ s, CauchySeq fun i ↦ f i a) :
    ∃ φ : A →⋆ₙₐ[ℂ] B, Tendsto f atTop (𝓝 φ) :=
  exists_tendsto_of_cauchy_map_adjoin hs hf

end PointNorm

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Evaluation `(φ, a) ↦ φ a` on `A →⋆ₐ[ℂ] B` is jointly continuous for the point-norm topology
and the norm topologies on `A` and `B`. -/
instance instContinuousEval : ContinuousEval (A →⋆ₐ[ℂ] B) A B where
  continuous_eval :=
    (continuous_eval : Continuous fun p : (A →⋆ₙₐ[ℂ] B) × A ↦ p.1 p.2).comp
      (continuous_toNonUnitalStarAlgHom.prodMap continuous_id)

/-- Composition of `StarAlgHom`s between complex C⋆-algebras is jointly continuous in the
point-norm topology. -/
@[fun_prop]
theorem continuous_comp [CStarAlgebra C] :
    Continuous fun p : (B →⋆ₐ[ℂ] C) × (A →⋆ₐ[ℂ] B) ↦ p.1.comp p.2 :=
  continuous_iff.mpr fun a ↦
    continuous_eval.comp (continuous_fst.prodMk ((continuous_eval_const a).comp continuous_snd))

/-- Composition preserves point-norm convergence of `StarAlgHom`s between C⋆-algebras. -/
theorem tendsto_comp [CStarAlgebra C] {ι : Type*} {l : Filter ι}
    {ψ : ι → B →⋆ₐ[ℂ] C} {φ : ι → A →⋆ₐ[ℂ] B} {ψ₀ : B →⋆ₐ[ℂ] C} {φ₀ : A →⋆ₐ[ℂ] B}
    (hψ : Tendsto ψ l (𝓝 ψ₀)) (hφ : Tendsto φ l (𝓝 φ₀)) :
    Tendsto (fun i ↦ (ψ i).comp (φ i)) l (𝓝 (ψ₀.comp φ₀)) :=
  (continuous_comp.tendsto (ψ₀, φ₀)).comp (hψ.prodMk_nhds hφ)

/-- Pointwise convergence of unital `⋆`-homomorphisms on a dense subset extends to convergence in
the point-norm topology. -/
theorem tendsto_of_tendsto_of_dense {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₐ[ℂ] B}
    {φ : A →⋆ₐ[ℂ] B} {s : Set A} (hs : Dense s)
    (hf : ∀ a ∈ s, Tendsto (fun i ↦ f i a) l (𝓝 (φ a))) :
    Tendsto f l (𝓝 φ) :=
  isInducing_toNonUnitalStarAlgHom.tendsto_nhds_iff.mpr
    (NonUnitalStarAlgHom.tendsto_of_tendsto_of_dense hs hf)

end StarAlgHom

namespace Unitary

variable {A : Type*} [CStarAlgebra A]

/-- Quantitative norm continuity of unitary conjugation on a unital C⋆-algebra: for unitaries
`u, v : unitary A` and `a : A`, `‖Ad(u) a - Ad(v) a‖ ≤ 2 * ‖a‖ * ‖(u : A) - (v : A)‖`. -/
theorem norm_conjStarAlgAut_sub_le (u v : unitary A) (a : A) :
    ‖(conjStarAlgAut ℂ A u) a - (conjStarAlgAut ℂ A v) a‖ ≤
      2 * ‖a‖ * ‖(u : A) - (v : A)‖ := by
  have hsplit : (conjStarAlgAut ℂ A u) a - (conjStarAlgAut ℂ A v) a =
      ((u : A) - (v : A)) * (a * star (u : A)) + ((v : A) * a) * star ((u : A) - (v : A)) := by
    simp only [conjStarAlgAut_apply, sub_mul, mul_sub, star_sub, mul_assoc]
    abel
  rw [hsplit]
  have h₁ : ‖((u : A) - (v : A)) * (a * star (u : A))‖ ≤ ‖a‖ * ‖(u : A) - (v : A)‖ := by
    calc
      ‖((u : A) - (v : A)) * (a * star (u : A))‖
        ≤ ‖(u : A) - (v : A)‖ * ‖a * star (u : A)‖ := norm_mul_le _ _
      _ = ‖(u : A) - (v : A)‖ * ‖a‖ := by
        congr 1
        simpa only [coe_star] using CStarRing.norm_mul_coe_unitary a (star u)
      _ = ‖a‖ * ‖(u : A) - (v : A)‖ := mul_comm _ _
  have h₂ : ‖((v : A) * a) * star ((u : A) - (v : A))‖ ≤ ‖a‖ * ‖(u : A) - (v : A)‖ := by
    calc
      ‖((v : A) * a) * star ((u : A) - (v : A))‖
        ≤ ‖(v : A) * a‖ * ‖star ((u : A) - (v : A))‖ := norm_mul_le _ _
      _ = ‖a‖ * ‖(u : A) - (v : A)‖ := by
        rw [CStarRing.norm_coe_unitary_mul, norm_star]
  calc
    ‖((u : A) - (v : A)) * (a * star (u : A)) + ((v : A) * a) * star ((u : A) - (v : A))‖
      ≤ ‖((u : A) - (v : A)) * (a * star (u : A))‖ +
          ‖((v : A) * a) * star ((u : A) - (v : A))‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖(u : A) - (v : A)‖ + ‖a‖ * ‖(u : A) - (v : A)‖ := add_le_add h₁ h₂
    _ = 2 * ‖a‖ * ‖(u : A) - (v : A)‖ := by ring

/-- Consecutive inner-automorphism error bound: for unitaries `u, v : unitary A` and `b : A`,
`‖Ad(v)(Ad(star u) b) - b‖ ≤ 2 * ‖b‖ * ‖(v : A) - (u : A)‖`. -/
theorem norm_conjStarAlgAut_star_sub_le (u v : unitary A) (b : A) :
    ‖(conjStarAlgAut ℂ A v) ((conjStarAlgAut ℂ A (star u)) b) - b‖ ≤
      2 * ‖b‖ * ‖(v : A) - (u : A)‖ := by
  have hb : (conjStarAlgAut ℂ A u) ((conjStarAlgAut ℂ A (star u)) b) = b := by
    simpa only [← conjStarAlgAut_symm] using (conjStarAlgAut ℂ A u).apply_symm_apply b
  have hdiff : (conjStarAlgAut ℂ A v) ((conjStarAlgAut ℂ A (star u)) b) - b =
      (conjStarAlgAut ℂ A v) ((conjStarAlgAut ℂ A (star u)) b) -
        (conjStarAlgAut ℂ A u) ((conjStarAlgAut ℂ A (star u)) b) := by
    rw [hb]
  rw [hdiff]
  simpa only [StarAlgEquiv.norm_map] using
    norm_conjStarAlgAut_sub_le v u ((conjStarAlgAut ℂ A (star u)) b)

end Unitary

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
