/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Completeness
public import TauCeti.Analysis.CStarAlgebra.Multiplier

/-!
# Nondegenerate representations and their extension to multipliers

A representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a possibly nonunital C⋆-algebra on a Hilbert
space is *nondegenerate* when the vectors `π a ξ` span a dense subspace of `H`. Equivalently, no
nonzero vector is annihilated by every `π a`, and `π e ξ → ξ` along an increasing approximate
unit.

A nondegenerate representation extends uniquely to a unital star-algebra homomorphism
`π' := π.multiplierExtension hπ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)` of the multiplier algebra. It is
characterized by `π' m * π a = π (m * a)`, and it is the strong limit of `π (m * e)` along an
increasing approximate unit `e`. This extension is how covariant pairs `(π, U)` with unitary
multipliers `U_s` are obtained from nondegenerate representations of crossed products.

## Main declarations

* `NonUnitalStarAlgHom.IsNondegenerate`: density of the span of the vectors `π a ξ`, unfolded by
  `isNondegenerate_iff_dense`.
* `NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero`: nondegeneracy means that no
  nonzero vector is killed by the whole representation.
* `NonUnitalStarAlgHom.isNondegenerate_iff_tendsto`: nondegeneracy means that the representation
  of an increasing approximate unit converges strongly to the identity.
* `NonUnitalStarAlgHom.multiplierExtension`: the extension to the multiplier algebra, with its
  characterizing identities `multiplierExtension_mul_eq_fst` and
  `mul_multiplierExtension_eq_snd`, the uniqueness statement
  `eq_multiplierExtension_of_apply_coe`, and the strong-limit formula
  `tendsto_multiplierExtension_apply`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1 and Proposition 2.39.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Corollary 2.51.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra InnerProductSpace

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A representation of a C⋆-algebra on a Hilbert space is *nondegenerate* when the vectors
`π a ξ` span a dense subspace. -/
def IsNondegenerate (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  Dense (Submodule.span ℂ (⋃ a, Set.range (π a)) : Set H)

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- Unfolding lemma: nondegeneracy is density of the span of the vectors `π a ξ`. -/
theorem isNondegenerate_iff_dense :
    π.IsNondegenerate ↔ Dense (Submodule.span ℂ (⋃ a, Set.range (π a)) : Set H) :=
  Iff.rfl

/-- Operators agreeing after composition with every operator of a nondegenerate representation
are equal. -/
theorem IsNondegenerate.ext (hπ : π.IsNondegenerate) {S T : H →L[ℂ] H}
    (h : ∀ a, S * π a = T * π a) : S = T := by
  refine ContinuousLinearMap.ext_on hπ fun x hx => ?_
  obtain ⟨a, ξ, rfl⟩ := Set.mem_iUnion.1 hx
  simpa using congr($(h a) ξ)

/-- A representation of a unital C⋆-algebra sending the identity to the identity operator is
nondegenerate. -/
theorem isNondegenerate_of_map_one {B : Type*} [CStarAlgebra B] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ 1 = 1) : ρ.IsNondegenerate := fun ξ =>
  subset_closure <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨1, ξ, by simp [hρ]⟩

section ApproximateUnit

variable [PartialOrder A] {l : Filter A}

/-- Along an increasing approximate unit, `π (m * e) η → π (m * a) ξ` when `η = π a ξ`. -/
private theorem tendsto_apply_apply (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (a : A)
    (ξ : H) : Tendsto (fun e => π (m.fst e) (π a ξ)) l (𝓝 (π (m.fst a) ξ)) := by
  have hcont : Continuous fun x : A => π (m.fst x) ξ := by fun_prop
  refine ((hcont.tendsto a).comp (hl.tendsto_mul_right a)).congr fun e => ?_
  simp [DoubleCentralizer.fst_mul]

/-- The operators `π (m * e)` for `e` in an increasing approximate unit are eventually bounded
by `‖m‖`. -/
private theorem eventually_norm_le (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) :
    ∀ᶠ e in l, ‖π (m.fst e)‖ ≤ ‖m‖ :=
  hl.eventually_norm.mono fun e he =>
    calc ‖π (m.fst e)‖ ≤ ‖m.fst e‖ := norm_apply_le π _
      _ ≤ ‖m.fst‖ * ‖e‖ := m.fst.le_opNorm e
      _ ≤ ‖m‖ := by simpa using mul_le_of_le_one_right (norm_nonneg m) he

/-- The vectors `π (m * e) η` converge along an increasing approximate unit whenever `η` lies in
the span of the vectors `π a ξ`. -/
private theorem exists_tendsto_of_mem_span (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A))
    {η : H} (hη : η ∈ Submodule.span ℂ (⋃ a, Set.range (π a))) :
    ∃ y, Tendsto (fun e => π (m.fst e) η) l (𝓝 y) := by
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ξ, rfl⟩ := Set.mem_iUnion.1 hx
    exact ⟨_, tendsto_apply_apply hl m a ξ⟩
  | zero => exact ⟨0, by simpa using tendsto_const_nhds⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simpa using hu.add hv⟩
  | smul c x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨c • u, by simpa using hu.const_smul c⟩

/-- For a nondegenerate representation, the vectors `π (m * e) ξ` form a Cauchy net along an
increasing approximate unit: approximate `ξ` by a vector of the span, on which the net converges,
and use the eventual bound `‖π (m * e)‖ ≤ ‖m‖`. -/
private theorem cauchy_map_apply (hπ : π.IsNondegenerate) (hl : l.IsIncreasingApproximateUnit)
    (m : 𝓜(ℂ, A)) (ξ : H) : Cauchy (map (fun e => π (m.fst e) ξ) l) := by
  have := hl.neBot
  set F : A → H → H := fun e ξ => π (m.fst e) ξ
  refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
  set δ := ε / (3 * (‖m‖ + 1))
  obtain ⟨η, hη, hξη⟩ := Metric.mem_closure_iff.1 (hπ ξ) δ (by positivity)
  obtain ⟨y, hy⟩ := exists_tendsto_of_mem_span hl m hη
  obtain ⟨t, ht, htε⟩ := Metric.cauchy_iff.1 hy.cauchy_map |>.2 (ε / 3) (by positivity)
  refine ⟨(F · ξ) '' ({e | ‖π (m.fst e)‖ ≤ ‖m‖} ∩ (F · η) ⁻¹' t),
    image_mem_map (inter_mem (eventually_norm_le hl m) ht), ?_⟩
  have hclose : ∀ e, ‖π (m.fst e)‖ ≤ ‖m‖ → dist (F e ξ) (F e η) < ε / 3 := fun e he => by
    have hmδ : ‖m‖ * δ < ε / 3 := by
      rw [show ‖m‖ * δ = ε / 3 * (‖m‖ / (‖m‖ + 1)) by simp only [δ]; field_simp]
      exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
    rw [dist_eq_norm, ← map_sub]
    refine (((π (m.fst e)).le_opNorm _).trans ?_).trans_lt hmδ
    exact mul_le_mul he (dist_eq_norm ξ η ▸ hξη.le) (norm_nonneg _) (norm_nonneg _)
  rintro _ ⟨e, ⟨he, het⟩, rfl⟩ _ ⟨e', ⟨he', het'⟩, rfl⟩
  calc dist (F e ξ) (F e' ξ) ≤ dist (F e ξ) (F e η) + dist (F e η) (F e' η) +
        dist (F e' η) (F e' ξ) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hclose e he
        · exact htε _ het _ het'
        · exact dist_comm (F e' η) _ ▸ hclose e' he'
    _ = ε := by ring

/-- For a nondegenerate representation, the vectors `π (m * e) ξ` converge along an increasing
approximate unit, and the limit is a bounded operator `T` with `T * π a = π (m * a)`. -/
private theorem exists_tendsto (hπ : π.IsNondegenerate) (hl : l.IsIncreasingApproximateUnit)
    (m : 𝓜(ℂ, A)) : ∃ T : H →L[ℂ] H, (∀ a, T * π a = π (m.fst a)) ∧
      ∀ ξ, Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (T ξ)) := by
  have := hl.neBot
  set f : H → H := fun ξ => limUnder l fun e => π (m.fst e) ξ
  have hf (ξ : H) : Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (f ξ)) :=
    tendsto_nhds_limUnder (cauchy_map_iff_exists_tendsto.1 (cauchy_map_apply hπ hl m ξ))
  -- The pointwise limit lies in the pointwise closure of a norm-bounded set of operators.
  have hmem : f ∈ closure (((↑) : (H →L[ℂ] H) → H → H) '' Metric.closedBall 0 ‖m‖) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.2 hf) <| (eventually_norm_le hl m).mono
      fun e he => ⟨π (m.fst e), mem_closedBall_zero_iff.2 he, rfl⟩
  set T := ContinuousLinearMap.ofMemClosureImageCoeBounded f
    (Metric.isBounded_closedBall (x := (0 : H →L[ℂ] H)) (r := ‖m‖)) hmem
  have hT : ⇑T = f := ContinuousLinearMap.ofMemClosureImageCoeBounded_apply _ _ _
  refine ⟨T, fun a => ContinuousLinearMap.ext fun ξ => ?_, fun ξ => hT ▸ hf ξ⟩
  rw [mul_apply_eq_comp, hT]
  exact tendsto_nhds_unique (hf (π a ξ)) (tendsto_apply_apply hl m a ξ)

end ApproximateUnit

/-- A nondegenerate representation admits, for each multiplier `m`, an operator `T` with
`T * π a = π (m * a)`. -/
private theorem exists_mul_eq (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) :
    ∃ T : H →L[ℂ] H, ∀ a, T * π a = π (m.fst a) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  obtain ⟨T, hT, -⟩ := exists_tendsto hπ (CStarAlgebra.increasingApproximateUnit A) m
  exact ⟨T, hT⟩

/-- The operator `π' m` determined by `π' m * π a = π (m * a)`. -/
private def extensionOp (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) : H →L[ℂ] H :=
  (exists_mul_eq hπ m).choose

private theorem extensionOp_mul (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    extensionOp hπ m * π a = π (m.fst a) :=
  (exists_mul_eq hπ m).choose_spec a

private theorem eq_extensionOp (hπ : π.IsNondegenerate) {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H}
    (hT : ∀ a, T * π a = π (m.fst a)) : T = extensionOp hπ m :=
  hπ.ext fun a => by rw [hT, extensionOp_mul]

private theorem mul_extensionOp (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    π a * extensionOp hπ m = π (m.snd a) :=
  hπ.ext fun b => by rw [mul_assoc, extensionOp_mul, ← map_mul, ← map_mul, m.central]

/-- The extension of a nondegenerate representation to the multiplier algebra: the unique
operator `π' m` with `π' m * π a = π (m * a)` for every `a`. -/
def multiplierExtension (hπ : π.IsNondegenerate) : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := extensionOp hπ
  map_one' := (eq_extensionOp hπ fun a => by simp).symm
  map_mul' m n := (eq_extensionOp hπ fun a => by
    rw [mul_assoc, extensionOp_mul, extensionOp_mul]
    simp).symm
  map_zero' := (eq_extensionOp hπ fun a => by simp).symm
  map_add' m n := (eq_extensionOp hπ fun a => by
    rw [add_mul, extensionOp_mul, extensionOp_mul]
    simp).symm
  commutes' r := (eq_extensionOp hπ fun a => by
    simp [Algebra.algebraMap_eq_smul_one]).symm
  map_star' m := (eq_extensionOp hπ fun a => by
    rw [DoubleCentralizer.star_fst, map_star, ← mul_extensionOp hπ, star_mul, ← map_star,
      star_star]).symm

variable (hπ : π.IsNondegenerate)

/-- The defining identity `π' m * π a = π (m * a)` of the multiplier extension. -/
@[simp]
theorem multiplierExtension_mul_eq_fst (m : 𝓜(ℂ, A)) (a : A) :
    π.multiplierExtension hπ m * π a = π (m.fst a) :=
  extensionOp_mul hπ m a

/-- The right-handed identity `π a * π' m = π (a * m)` of the multiplier extension. -/
@[simp]
theorem mul_multiplierExtension_eq_snd (m : 𝓜(ℂ, A)) (a : A) :
    π a * π.multiplierExtension hπ m = π (m.snd a) :=
  mul_extensionOp hπ m a

/-- The multiplier extension sends `π a ξ` to `π (m * a) ξ`. -/
@[simp]
theorem multiplierExtension_apply_apply (m : 𝓜(ℂ, A)) (a : A) (ξ : H) :
    π.multiplierExtension hπ m (π a ξ) = π (m.fst a) ξ :=
  congr($(multiplierExtension_mul_eq_fst hπ m a) ξ)

/-- An operator equals `π' m` exactly when it satisfies the defining identity. -/
theorem eq_multiplierExtension_iff {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H} :
    T = π.multiplierExtension hπ m ↔ ∀ a, T * π a = π (m.fst a) :=
  ⟨fun h a => h ▸ multiplierExtension_mul_eq_fst hπ m a, eq_extensionOp hπ⟩

/-- The multiplier extension restricts to `π` on `A`. -/
@[simp]
theorem multiplierExtension_coe (a : A) : π.multiplierExtension hπ (a : 𝓜(ℂ, A)) = π a :=
  ((eq_multiplierExtension_iff hπ).2 fun b => by simp).symm

/-- The multiplier extension is the only multiplicative map on `𝓜(ℂ, A)` extending `π`. -/
theorem eq_multiplierExtension_of_apply_coe {F : Type*} [FunLike F 𝓜(ℂ, A) (H →L[ℂ] H)]
    [MulHomClass F 𝓜(ℂ, A) (H →L[ℂ] H)] (ψ : F) (hψ : ∀ a : A, ψ a = π a) :
    ⇑ψ = π.multiplierExtension hπ := by
  funext m
  refine (eq_multiplierExtension_iff hπ).2 fun a => ?_
  rw [← hψ, ← map_mul, DoubleCentralizer.mul_coe_eq_coe_fst, hψ]

/-- Along an increasing approximate unit `e`, the operators `π (m * e)` converge strongly to the
multiplier extension `π' m`. -/
theorem tendsto_multiplierExtension_apply [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (ξ : H) :
    Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (π.multiplierExtension hπ m ξ)) := by
  obtain ⟨T, hT, hlim⟩ := exists_tendsto hπ hl m
  rw [← (eq_multiplierExtension_iff hπ).2 hT]
  exact hlim ξ

/-- Strict continuity of a norm-bounded family of multipliers gives strong continuity of its image
under the multiplier extension: if `x ↦ u x * a` is norm continuous for every `a` and
`‖u x‖ ≤ C`, then `x ↦ π' (u x) ξ` is continuous for every vector `ξ`. Only the left half of
strict continuity is needed. This applies to strictly continuous unitary multiplier groups. -/
theorem continuous_multiplierExtension_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C) (ξ : H) : Continuous fun x => π.multiplierExtension hπ (u x) ξ := by
  set Φ : H → X → H := fun η x => π.multiplierExtension hπ (u x) η
  -- Continuity holds on the span of the vectors `π a η`.
  have hspan : ∀ η ∈ Submodule.span ℂ (⋃ a, Set.range (π a)), Continuous (Φ η) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, η, rfl⟩ := Set.mem_iUnion.1 hx
      simp only [Φ, multiplierExtension_apply_apply]
      fun_prop
    | zero => simpa [Φ] using continuous_const
    | add x y _ _ hx hy =>
      simp only [Φ, map_add] at hx hy ⊢
      exact hx.add hy
    | smul c x _ hx =>
      simp only [Φ, map_smul] at hx ⊢
      exact hx.const_smul c
  -- The uniform bound makes `Φ ξ` a uniform limit of such continuous maps.
  refine continuous_of_uniform_approx_of_continuous fun U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨η, hη, hξη⟩ := Metric.mem_closure_iff.1 (hπ ξ) (ε / (|C| + 1)) (by positivity)
  refine ⟨Φ η, hspan η hη, fun x => hεU ?_⟩
  calc dist (Φ ξ x) (Φ η x) = ‖π.multiplierExtension hπ (u x) (ξ - η)‖ := by
        rw [dist_eq_norm, map_sub]
    _ ≤ ‖u x‖ * ‖ξ - η‖ :=
        ((π.multiplierExtension hπ (u x)).le_opNorm _).trans <|
          mul_le_mul_of_nonneg_right (norm_apply_le _ _) (norm_nonneg _)
    _ ≤ |C| * (ε / (|C| + 1)) := by
        rw [← dist_eq_norm]
        exact mul_le_mul ((hC x).trans (le_abs_self C)) hξη.le dist_nonneg (abs_nonneg C)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

/-- A representation is nondegenerate exactly when the representation of an increasing
approximate unit converges strongly to the identity. -/
theorem isNondegenerate_iff_tendsto [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    π.IsNondegenerate ↔ ∀ ξ, Tendsto (fun e => π e ξ) l (𝓝 ξ) := by
  refine ⟨fun hπ ξ => by simpa using tendsto_multiplierExtension_apply hπ hl 1 ξ,
    fun h ξ => ?_⟩
  have := hl.neBot
  exact mem_closure_of_tendsto (h ξ) <| .of_forall fun e =>
    Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, ξ, rfl⟩

/-- A representation is nondegenerate exactly when no nonzero vector is annihilated by every
operator of the representation. -/
theorem isNondegenerate_iff_forall_apply_eq_zero :
    π.IsNondegenerate ↔ ∀ ξ, (∀ a, π a ξ = 0) → ξ = 0 := by
  refine ⟨fun hπ ξ h => ?_, fun h => ?_⟩
  · let := CStarAlgebra.spectralOrder A
    have := CStarAlgebra.spectralOrderedRing A
    have hl := CStarAlgebra.increasingApproximateUnit A
    exact tendsto_nhds_unique ((isNondegenerate_iff_tendsto hl).1 hπ ξ) (by simp [h])
  · rw [IsNondegenerate, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    refine fun ξ hξ => h ξ fun a => ext_inner_left ℂ fun v => ?_
    rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ <|
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨star a, v, rfl⟩

end NonUnitalStarAlgHom
