/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Nondegenerate homomorphisms into multiplier algebras

A nonunital ⋆-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` between C⋆-algebras is *nondegenerate*
(`NonUnitalStarAlgHom.IsMultiplierNondegenerate`) when the elements `(φ a).fst b` span a dense
subspace of `B`. Equivalently, `(φ e).fst b → b` for every `b : B` along an increasing approximate
unit `e` of `A`.

Every nondegenerate homomorphism `φ` extends uniquely to a unital ⋆-homomorphism
`φ' := φ.extendToMultiplier hφ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)`, characterized by
`φ' m * φ a = φ (m.fst a)` for every `a : A`. On each `b : B`, `(φ' m).fst b` is the norm limit
of `(φ (m.fst e)).fst b` along an increasing approximate unit `e` of `A`, and norm-bounded strictly
continuous families in `𝓜(ℂ, A)` remain strictly continuous under `φ'`. Nondegenerate multiplier
homomorphisms compose with one another and with nondegenerate Hilbert-space representations.

## Main declarations

* `DoubleCentralizer.continuous_toProd`: continuity of the centralizer-pair projection on `𝓜(𝕜, A)`.
* `NonUnitalStarAlgHom.IsMultiplierNondegenerate`: density of the span of `(φ a).fst b` in `B`.
* `NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_tendsto_fst`: characterization along an
  increasing approximate unit.
* `NonUnitalStarAlgHom.extendToMultiplier`: the unique unital extension `𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)`,
  with `extendToMultiplier_mul_eq_fst`, `mul_extendToMultiplier_eq_snd`,
  `eq_extendToMultiplier_of_apply_coe`, and `continuous_extendToMultiplier_fst_apply`.
* `NonUnitalStarAlgHom.IsMultiplierNondegenerate.extendToMultiplier_comp` and
  `NonUnitalStarAlgHom.IsNondegenerate.multiplierExtension_comp`: stability under composition with
  nondegenerate multiplier and Hilbert-space homomorphisms.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.46.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.50.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra

namespace DoubleCentralizer

section Continuous

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Projection from a multiplier to its pair of left and right centralizers is norm continuous. -/
@[fun_prop]
theorem continuous_toProd :
    Continuous (DoubleCentralizer.toProd : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)) :=
  AddMonoidHomClass.continuous_of_bound toProdHom 1 fun m => by
    rw [one_mul, norm_def]

end Continuous

end DoubleCentralizer

namespace NonUnitalStarAlgHom

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- A ⋆-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is *nondegenerate* when the elements `(φ a).fst b`
span a dense subspace of `B`. -/
def IsMultiplierNondegenerate (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) : Prop :=
  Dense (Submodule.span ℂ (⋃ a, Set.range (φ a).fst) : Set B)

variable {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}

/-- Unfolding lemma: nondegeneracy is density of the span of `(φ a).fst b` in `B`. -/
theorem isMultiplierNondegenerate_iff_dense :
    φ.IsMultiplierNondegenerate ↔ Dense (Submodule.span ℂ (⋃ a, Set.range (φ a).fst) : Set B) :=
  Iff.rfl

/-- Bounded operators on `B` agreeing after every `(φ a).fst` are equal when `φ` is
nondegenerate. -/
theorem IsMultiplierNondegenerate.clm_ext (hφ : φ.IsMultiplierNondegenerate) {S T : B →L[ℂ] B}
    (h : ∀ a, S * (φ a).fst = T * (φ a).fst) : S = T := by
  refine ContinuousLinearMap.ext_on hφ fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := Set.mem_iUnion.1 hx
  simpa using congr($(h a) b)

/-- Multipliers of `B` agreeing on the left of every `φ a` are equal when `φ` is nondegenerate. -/
theorem IsMultiplierNondegenerate.ext (hφ : φ.IsMultiplierNondegenerate) {m n : 𝓜(ℂ, B)}
    (h : ∀ a, m * φ a = n * φ a) : m = n :=
  DoubleCentralizer.ext_fst fun b =>
    congr($(hφ.clm_ext fun a => congrArg (fun x : 𝓜(ℂ, B) => x.fst) (h a)) b)

/-- Multipliers of `B` agreeing on the right of every `φ a` are equal when `φ` is nondegenerate. -/
theorem IsMultiplierNondegenerate.ext_mul_left (hφ : φ.IsMultiplierNondegenerate) {m n : 𝓜(ℂ, B)}
    (h : ∀ a, φ a * m = φ a * n) : m = n :=
  star_injective <| hφ.ext fun a => by
    simpa [← map_star] using congrArg star (h (star a))

/-- A homomorphism from a unital C⋆-algebra sending `1` to `1` is nondegenerate. -/
theorem isMultiplierNondegenerate_of_map_one {D : Type*} [CStarAlgebra D]
    {ψ : D →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hψ : ψ 1 = 1) : ψ.IsMultiplierNondegenerate := fun b =>
  subset_closure <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨1, b, by simp [hψ]⟩

/-- The canonical inclusion `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` is nondegenerate. -/
theorem isMultiplierNondegenerate_coeHom :
    (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).IsMultiplierNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine fun b => mem_closure_of_tendsto (hl.tendsto_mul_right b) <| .of_forall fun e => ?_
  exact Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, b, by simp⟩

section ApproximateUnit

variable [PartialOrder A] {l : Filter A}

/-- Along an increasing approximate unit, `(φ (m.fst e)).fst ((φ a).fst b)` converges to
`(φ (m.fst a)).fst b`. -/
private theorem tendsto_fst_apply_apply (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A))
    (a : A) (b : B) :
    Tendsto (fun e => (φ (m.fst e)).fst ((φ a).fst b)) l (𝓝 ((φ (m.fst a)).fst b)) := by
  have hcont : Continuous fun x : A => (φ (m.fst x)).fst b := by fun_prop
  refine ((hcont.tendsto a).comp (hl.tendsto_mul_right a)).congr fun e => ?_
  simp only [Function.comp_apply, DoubleCentralizer.fst_mul]
  rw [← mul_apply_eq_comp, ← DoubleCentralizer.mul_fst, ← map_mul]

/-- Along an increasing approximate unit, `‖(φ (m.fst e)).fst‖` is eventually at most `‖m‖`. -/
private theorem eventually_norm_fst_le (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) :
    ∀ᶠ e in l, ‖(φ (m.fst e)).fst‖ ≤ ‖m‖ :=
  hl.eventually_norm.mono fun e he =>
    calc ‖(φ (m.fst e)).fst‖ = ‖φ (m.fst e)‖ := DoubleCentralizer.norm_fst _
      _ ≤ ‖m.fst e‖ := norm_apply_le φ _
      _ ≤ ‖m.fst‖ * ‖e‖ := m.fst.le_opNorm e
      _ ≤ ‖m‖ := by simpa using mul_le_of_le_one_right (norm_nonneg m) he

private theorem exists_tendsto_fst_of_mem_span (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A))
    {x : B} (hx : x ∈ Submodule.span ℂ (⋃ a, Set.range (φ a).fst)) :
    ∃ y, Tendsto (fun e => (φ (m.fst e)).fst x) l (𝓝 y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := Set.mem_iUnion.1 hx
    exact ⟨_, tendsto_fst_apply_apply hl m a b⟩
  | zero => exact ⟨0, by simpa using tendsto_const_nhds⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simpa using hu.add hv⟩
  | smul c x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨c • u, by simpa using hu.const_smul c⟩

/-- When `φ` is nondegenerate, `(φ (m.fst e)).fst b` is Cauchy along an increasing approximate
unit: approximate `b` in the dense span and use the eventual bound `‖(φ (m.fst e)).fst‖ ≤ ‖m‖`. -/
private theorem cauchy_map_fst_apply (hφ : φ.IsMultiplierNondegenerate)
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (b : B) :
    Cauchy (map (fun e => (φ (m.fst e)).fst b) l) := by
  have := hl.neBot
  set F : A → B → B := fun e b => (φ (m.fst e)).fst b
  refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
  set δ := ε / (3 * (‖m‖ + 1))
  obtain ⟨x, hx, hbx⟩ := Metric.mem_closure_iff.1 (hφ b) δ (by positivity)
  obtain ⟨y, hy⟩ := exists_tendsto_fst_of_mem_span hl m hx
  obtain ⟨t, ht, htε⟩ := Metric.cauchy_iff.1 hy.cauchy_map |>.2 (ε / 3) (by positivity)
  refine ⟨(F · b) '' ({e | ‖(φ (m.fst e)).fst‖ ≤ ‖m‖} ∩ (F · x) ⁻¹' t),
    image_mem_map (inter_mem (eventually_norm_fst_le hl m) ht), ?_⟩
  have hclose : ∀ e, ‖(φ (m.fst e)).fst‖ ≤ ‖m‖ → dist (F e b) (F e x) < ε / 3 := fun e he => by
    have hmδ : ‖m‖ * δ < ε / 3 := by
      simp only [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith
    rw [dist_eq_norm, ← map_sub]
    refine (((φ (m.fst e)).fst.le_opNorm _).trans ?_).trans_lt hmδ
    exact mul_le_mul he (dist_eq_norm b x ▸ hbx.le) (norm_nonneg _) (norm_nonneg _)
  rintro _ ⟨e, ⟨he, het⟩, rfl⟩ _ ⟨e', ⟨he', het'⟩, rfl⟩
  calc dist (F e b) (F e' b) ≤ dist (F e b) (F e x) + dist (F e x) (F e' x) +
        dist (F e' x) (F e' b) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hclose e he
        · exact htε _ het _ het'
        · exact dist_comm (F e' x) _ ▸ hclose e' he'
    _ = ε := by ring

private theorem exists_tendsto_fst (hφ : φ.IsMultiplierNondegenerate)
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) :
    ∃ T : B →L[ℂ] B, (∀ a, T * (φ a).fst = (φ (m.fst a)).fst) ∧
      ∀ b, Tendsto (fun e => (φ (m.fst e)).fst b) l (𝓝 (T b)) := by
  have := hl.neBot
  set f : B → B := fun b => limUnder l fun e => (φ (m.fst e)).fst b
  have hf (b : B) : Tendsto (fun e => (φ (m.fst e)).fst b) l (𝓝 (f b)) :=
    tendsto_nhds_limUnder (cauchy_map_iff_exists_tendsto.1 (cauchy_map_fst_apply hφ hl m b))
  have hmem : f ∈ closure (((↑) : (B →L[ℂ] B) → B → B) '' Metric.closedBall 0 ‖m‖) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.2 hf) <| (eventually_norm_fst_le hl m).mono
      fun e he => ⟨(φ (m.fst e)).fst, mem_closedBall_zero_iff.2 he, rfl⟩
  set T := ContinuousLinearMap.ofMemClosureImageCoeBounded f
    (Metric.isBounded_closedBall (x := (0 : B →L[ℂ] B)) (r := ‖m‖)) hmem
  have hT : ⇑T = f := ContinuousLinearMap.ofMemClosureImageCoeBounded_apply _ _ _
  refine ⟨T, fun a => ContinuousLinearMap.ext fun b => ?_, fun b => hT ▸ hf b⟩
  rw [mul_apply_eq_comp, hT]
  exact tendsto_nhds_unique (hf ((φ a).fst b)) (tendsto_fst_apply_apply hl m a b)

end ApproximateUnit

private theorem exists_clm_mul_eq (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) :
    ∃ T : B →L[ℂ] B, ∀ a, T * (φ a).fst = (φ (m.fst a)).fst := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  obtain ⟨T, hT, -⟩ := exists_tendsto_fst hφ (CStarAlgebra.increasingApproximateUnit A) m
  exact ⟨T, hT⟩

private def extensionCLM (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) : B →L[ℂ] B :=
  (exists_clm_mul_eq hφ m).choose

private theorem extensionCLM_mul (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    extensionCLM hφ m * (φ a).fst = (φ (m.fst a)).fst :=
  (exists_clm_mul_eq hφ m).choose_spec a

private theorem extensionCLM_apply_fst (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A))
    (a : A) (b : B) :
    extensionCLM hφ m ((φ a).fst b) = (φ (m.fst a)).fst b :=
  congr($(extensionCLM_mul hφ m a) b)

/-- The operators `extensionCLM hφ m` and `extensionCLM hφ (star m)` are adjoint for the pairing
`(x, y) ↦ star x * y` on `B`. -/
private theorem star_extensionCLM_mul (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A))
    (x y : B) :
    star (extensionCLM hφ (star m) x) * y = star x * extensionCLM hφ m y := by
  have hstar (q : A) (u w : B) : star ((φ q).fst u) * w = star u * (φ (star q)).fst w := by
    rw [← (φ (star q)).central, map_star φ, DoubleCentralizer.star_snd, star_star]
  have hgen (a c : A) (u v : B) :
      star (extensionCLM hφ (star m) ((φ a).fst u)) * (φ c).fst v =
        star ((φ a).fst u) * extensionCLM hφ m ((φ c).fst v) := by
    calc star (extensionCLM hφ (star m) ((φ a).fst u)) * (φ c).fst v
        = star u * (φ (star ((star m).fst a))).fst ((φ c).fst v) := by
          rw [extensionCLM_apply_fst, hstar]
      _ = star u * (φ (star ((star m).fst a) * c)).fst v := by
          rw [map_mul, DoubleCentralizer.mul_fst, mul_apply_eq_comp]
      _ = star u * (φ (star a * m.fst c)).fst v := by
          rw [DoubleCentralizer.star_fst, star_star, m.central]
      _ = star u * (φ (star a)).fst ((φ (m.fst c)).fst v) := by
          rw [map_mul, DoubleCentralizer.mul_fst, mul_apply_eq_comp]
      _ = star ((φ a).fst u) * extensionCLM hφ m ((φ c).fst v) := by
          rw [extensionCLM_apply_fst, hstar]
  have hy (a : A) (u : B) :
      star (extensionCLM hφ (star m) ((φ a).fst u)) * y =
        star ((φ a).fst u) * extensionCLM hφ m y := by
    have hy_span : ∀ z ∈ Submodule.span ℂ (⋃ c, Set.range (φ c).fst),
        star (extensionCLM hφ (star m) ((φ a).fst u)) * z =
          star ((φ a).fst u) * extensionCLM hφ m z := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, v, rfl⟩ := Set.mem_iUnion.1 hw
        exact hgen a c u v
      | zero => simp
      | add w₁ w₂ _ _ hw₁ hw₂ => simp [mul_add, hw₁, hw₂]
      | smul r w _ hw => simp [mul_smul_comm, hw]
    exact (isClosed_eq (by fun_prop) (by fun_prop)).closure_subset_iff.2 hy_span (hφ y)
  have hx_span : ∀ z ∈ Submodule.span ℂ (⋃ a, Set.range (φ a).fst),
      star (extensionCLM hφ (star m) z) * y = star z * extensionCLM hφ m y := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, u, rfl⟩ := Set.mem_iUnion.1 hw
      exact hy a u
    | zero => simp
    | add w₁ w₂ _ _ hw₁ hw₂ => simp [add_mul, hw₁, hw₂]
    | smul r w _ hw => simp [smul_mul_assoc, hw]
  exact (isClosed_eq (by fun_prop) (by fun_prop)).closure_subset_iff.2 hx_span (hφ x)

private def extensionMultiplier (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) : 𝓜(ℂ, B) :=
  DoubleCentralizer.ofAdjoint (extensionCLM hφ m) (extensionCLM hφ (star m))
    (star_extensionCLM_mul hφ m)

private theorem extensionMultiplier_mul (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    extensionMultiplier hφ m * φ a = φ (m.fst a) :=
  DoubleCentralizer.ext_fst fun b => by
    simpa [extensionMultiplier, mul_apply_eq_comp] using congr($(extensionCLM_mul hφ m a) b)

private theorem eq_extensionMultiplier (hφ : φ.IsMultiplierNondegenerate) {m : 𝓜(ℂ, A)}
    {n : 𝓜(ℂ, B)} (hn : ∀ a, n * φ a = φ (m.fst a)) : n = extensionMultiplier hφ m :=
  hφ.ext fun a => by rw [hn, extensionMultiplier_mul]

private theorem mul_extensionMultiplier (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    φ a * extensionMultiplier hφ m = φ (m.snd a) :=
  hφ.ext fun c => by
    rw [mul_assoc, extensionMultiplier_mul, ← map_mul, ← map_mul, m.central]

/-- The unital extension of a nondegenerate ⋆-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` to multiplier
algebras: the unique multiplier `φ' m` satisfying `φ' m * φ a = φ (m.fst a)` for every `a : A`. -/
def extendToMultiplier (hφ : φ.IsMultiplierNondegenerate) : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B) where
  toFun := extensionMultiplier hφ
  map_one' := (eq_extensionMultiplier hφ fun a => by simp).symm
  map_mul' m n := (eq_extensionMultiplier hφ fun a => by
    rw [mul_assoc, extensionMultiplier_mul, extensionMultiplier_mul]
    simp).symm
  map_zero' := (eq_extensionMultiplier hφ fun a => by simp).symm
  map_add' m n := (eq_extensionMultiplier hφ fun a => by
    rw [add_mul, extensionMultiplier_mul, extensionMultiplier_mul]
    simp).symm
  commutes' r := (eq_extensionMultiplier hφ fun a => by
    simp [Algebra.algebraMap_eq_smul_one]).symm
  map_star' m := (eq_extensionMultiplier hφ fun a => by
    rw [DoubleCentralizer.star_fst, map_star, ← mul_extensionMultiplier hφ, star_mul,
      ← map_star, star_star]).symm

variable (hφ : φ.IsMultiplierNondegenerate)

/-- The defining identity `φ' m * φ a = φ (m.fst a)` of the multiplier extension. -/
@[simp]
theorem extendToMultiplier_mul_eq_fst (m : 𝓜(ℂ, A)) (a : A) :
    φ.extendToMultiplier hφ m * φ a = φ (m.fst a) :=
  extensionMultiplier_mul hφ m a

/-- The right-handed identity `φ a * φ' m = φ (m.snd a)` of the multiplier extension. -/
@[simp]
theorem mul_extendToMultiplier_eq_snd (m : 𝓜(ℂ, A)) (a : A) :
    φ a * φ.extendToMultiplier hφ m = φ (m.snd a) :=
  mul_extensionMultiplier hφ m a

/-- On `(φ a).fst b`, the left centralizer of `φ' m` acts as `(φ (m.fst a)).fst b`. -/
@[simp]
theorem extendToMultiplier_fst_apply (m : 𝓜(ℂ, A)) (a : A) (b : B) :
    (φ.extendToMultiplier hφ m).fst ((φ a).fst b) = (φ (m.fst a)).fst b :=
  congr(($(extendToMultiplier_mul_eq_fst hφ m a)).fst b)

/-- On `(φ a).snd b`, the right centralizer of `φ' m` acts as `(φ (m.snd a)).snd b`. -/
@[simp]
theorem extendToMultiplier_snd_apply (m : 𝓜(ℂ, A)) (a : A) (b : B) :
    (φ.extendToMultiplier hφ m).snd ((φ a).snd b) = (φ (m.snd a)).snd b :=
  congr(($(mul_extendToMultiplier_eq_snd hφ m a)).snd b)

/-- A multiplier equals `φ' m` if and only if it satisfies `n * φ a = φ (m.fst a)` for all `a`. -/
theorem eq_extendToMultiplier_iff {m : 𝓜(ℂ, A)} {n : 𝓜(ℂ, B)} :
    n = φ.extendToMultiplier hφ m ↔ ∀ a, n * φ a = φ (m.fst a) :=
  ⟨fun h a => h ▸ extendToMultiplier_mul_eq_fst hφ m a, eq_extensionMultiplier hφ⟩

/-- The multiplier extension restricts to `φ` on `A`. -/
@[simp]
theorem extendToMultiplier_coe (a : A) : φ.extendToMultiplier hφ (a : 𝓜(ℂ, A)) = φ a :=
  ((eq_extendToMultiplier_iff hφ).2 fun c => by simp).symm

/-- `φ.extendToMultiplier hφ` is the unique multiplicative map on `𝓜(ℂ, A)` extending `φ`. -/
theorem eq_extendToMultiplier_of_apply_coe {F : Type*} [FunLike F 𝓜(ℂ, A) 𝓜(ℂ, B)]
    [MulHomClass F 𝓜(ℂ, A) 𝓜(ℂ, B)] (ψ : F) (hψ : ∀ a : A, ψ a = φ a) :
    ⇑ψ = φ.extendToMultiplier hφ := by
  funext m
  refine (eq_extendToMultiplier_iff hφ).2 fun a => ?_
  rw [← hψ, ← map_mul, DoubleCentralizer.mul_coe_eq_coe_fst, hψ]

/-- Extending the canonical inclusion `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` gives the identity on `𝓜(ℂ, A)`. -/
@[simp]
theorem extendToMultiplier_coeHom :
    (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).extendToMultiplier
      isMultiplierNondegenerate_coeHom = StarAlgHom.id ℂ 𝓜(ℂ, A) := by
  ext m : 1
  exact congrFun (eq_extendToMultiplier_of_apply_coe isMultiplierNondegenerate_coeHom
    (StarAlgHom.id ℂ 𝓜(ℂ, A)) fun _ => rfl).symm m

/-- Along an increasing approximate unit `e`, `(φ (m.fst e)).fst b` converges in norm to
`(φ.extendToMultiplier hφ m).fst b`. -/
theorem tendsto_extendToMultiplier_fst [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (b : B) :
    Tendsto (fun e => (φ (m.fst e)).fst b) l (𝓝 ((φ.extendToMultiplier hφ m).fst b)) := by
  obtain ⟨T, hT, hlim⟩ := exists_tendsto_fst hφ hl m
  have hTeq : T = (φ.extendToMultiplier hφ m).fst :=
    hφ.clm_ext fun a => (hT a).trans
      (congrArg (fun x : 𝓜(ℂ, B) => x.fst) (extendToMultiplier_mul_eq_fst hφ m a)).symm
  exact hTeq ▸ hlim b

/-- Norm-bounded left-strictly continuous families in `𝓜(ℂ, A)` map to left-strictly continuous
families in `𝓜(ℂ, B)` under `extendToMultiplier`. -/
theorem continuous_extendToMultiplier_fst_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {K : ℝ}
    (hK : ∀ x, ‖u x‖ ≤ K) (b : B) :
    Continuous fun x => (φ.extendToMultiplier hφ (u x)).fst b := by
  set Φ : B → X → B := fun y x => (φ.extendToMultiplier hφ (u x)).fst y
  have hspan : ∀ y ∈ Submodule.span ℂ (⋃ a, Set.range (φ a).fst), Continuous (Φ y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hz
      simp only [Φ, extendToMultiplier_fst_apply]
      fun_prop
    | zero => simpa [Φ] using continuous_const
    | add y z _ _ hy hz =>
      simp only [Φ, map_add] at hy hz ⊢
      exact hy.add hz
    | smul c y _ hy =>
      simp only [Φ, map_smul] at hy ⊢
      exact hy.const_smul c
  refine continuous_of_uniform_approx_of_continuous fun U hU => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨y, hy, hby⟩ := Metric.mem_closure_iff.1 (hφ b) (ε / (|K| + 1)) (by positivity)
  refine ⟨Φ y, hspan y hy, fun x => hεU ?_⟩
  calc dist (Φ b x) (Φ y x) = ‖(φ.extendToMultiplier hφ (u x)).fst (b - y)‖ := by
        rw [dist_eq_norm, map_sub]
    _ ≤ ‖u x‖ * ‖b - y‖ := by
        refine (((φ.extendToMultiplier hφ (u x)).fst.le_opNorm _).trans ?_)
        rw [DoubleCentralizer.norm_fst]
        exact mul_le_mul_of_nonneg_right
          (norm_apply_le (φ.extendToMultiplier hφ).toNonUnitalStarAlgHom _) (norm_nonneg _)
    _ ≤ |K| * (ε / (|K| + 1)) := by
        rw [← dist_eq_norm]
        exact mul_le_mul ((hK x).trans (le_abs_self K)) hby.le dist_nonneg (abs_nonneg K)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg K]

/-- A ⋆-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate if and only if `(φ e).fst b → b`
in norm for every `b : B` along an increasing approximate unit `e` of `A`. -/
theorem isMultiplierNondegenerate_iff_tendsto_fst [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    φ.IsMultiplierNondegenerate ↔ ∀ b, Tendsto (fun e => (φ e).fst b) l (𝓝 b) := by
  refine ⟨fun hφ b => by simpa using tendsto_extendToMultiplier_fst hφ hl 1 b, fun h b => ?_⟩
  have := hl.neBot
  exact mem_closure_of_tendsto (h b) <| .of_forall fun e =>
    Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, b, rfl⟩

section Composition

/-- Composing a nondegenerate multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` with the extension
of a nondegenerate multiplier homomorphism `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` produces a nondegenerate
multiplier homomorphism. -/
theorem IsMultiplierNondegenerate.extendToMultiplier_comp
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (hφ : φ.IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ).IsMultiplierNondegenerate := by
  rw [isMultiplierNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top]
  set S := Submodule.span ℂ
    (⋃ a, Set.range (((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ) a).fst)
  have hmem (b : B) (c : C) : (ψ b).fst c ∈ S.topologicalClosure := by
    have hspan : ∀ y ∈ Submodule.span ℂ (⋃ a, Set.range (φ a).fst), (ψ y).fst c ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, d, rfl⟩ := Set.mem_iUnion.1 hz
        refine Submodule.subset_span <| Set.mem_iUnion.2 ⟨a, (ψ d).fst c, ?_⟩
        simp
      | zero => simp
      | add y z _ _ hy hz => simpa [map_add] using S.add_mem hy hz
      | smul r y _ hy => simpa [map_smul] using S.smul_mem r hy
    have hclosed : IsClosed {y : B | (ψ y).fst c ∈ S.topologicalClosure} :=
      S.isClosed_topologicalClosure.preimage (by fun_prop)
    exact hclosed.closure_subset_iff.2
      (fun y hy => Submodule.le_topologicalClosure S (hspan y hy)) (hφ b)
  rw [eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top.1 hψ]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    S.isClosed_topologicalClosure
  rintro _ ⟨_, ⟨b, rfl⟩, c, rfl⟩
  exact hmem b c

/-- The multiplier extension of `(ψ.extendToMultiplier hψ) ∘ φ` is the composite of the two
multiplier extensions. -/
@[simp]
theorem extendToMultiplier_comp {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (hφ : φ.IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ).extendToMultiplier
      (hψ.extendToMultiplier_comp hφ) =
        (ψ.extendToMultiplier hψ).comp (φ.extendToMultiplier hφ) := by
  ext m : 1
  exact congrFun (eq_extendToMultiplier_of_apply_coe (hψ.extendToMultiplier_comp hφ)
    ((ψ.extendToMultiplier hψ).comp (φ.extendToMultiplier hφ)) fun a => by simp).symm m

/-- Composing a nondegenerate multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` with the extension
of a nondegenerate Hilbert-space representation `π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)` produces a
nondegenerate Hilbert-space representation of `A`. -/
theorem IsNondegenerate.multiplierExtension_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hφ : φ.IsMultiplierNondegenerate) :
    ((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ).IsNondegenerate := by
  rw [isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top]
  set S := Submodule.span ℂ
    (⋃ a, Set.range (((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ) a))
  have hmem (b : B) (ξ : H) : π b ξ ∈ S.topologicalClosure := by
    have hspan : ∀ y ∈ Submodule.span ℂ (⋃ a, Set.range (φ a).fst), π y ξ ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, d, rfl⟩ := Set.mem_iUnion.1 hz
        refine Submodule.subset_span <| Set.mem_iUnion.2 ⟨a, π d ξ, ?_⟩
        simp
      | zero => simp
      | add y z _ _ hy hz => simpa [map_add] using S.add_mem hy hz
      | smul r y _ hy => simpa [map_smul] using S.smul_mem r hy
    have hclosed : IsClosed {y : B | π y ξ ∈ S.topologicalClosure} :=
      S.isClosed_topologicalClosure.preimage (by fun_prop)
    exact hclosed.closure_subset_iff.2
      (fun y hy => Submodule.le_topologicalClosure S (hspan y hy)) (hφ b)
  rw [eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top.1
    (isNondegenerate_iff_dense.1 hπ)]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    S.isClosed_topologicalClosure
  rintro _ ⟨_, ⟨b, rfl⟩, ξ, rfl⟩
  exact hmem b ξ

/-- The Hilbert-space multiplier extension of `(π.multiplierExtension hπ) ∘ φ` factors through
`φ.extendToMultiplier hφ`. -/
@[simp]
theorem multiplierExtension_comp_extendToMultiplier {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hφ : φ.IsMultiplierNondegenerate) :
    ((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ).multiplierExtension
      (hπ.multiplierExtension_comp hφ) =
        (π.multiplierExtension hπ).comp (φ.extendToMultiplier hφ) := by
  ext m : 1
  exact congrFun (eq_multiplierExtension_of_apply_coe (hπ.multiplierExtension_comp hφ)
    ((π.multiplierExtension hπ).comp (φ.extendToMultiplier hφ)) fun a => by simp).symm m

end Composition

section DenseRange

variable {ι A : Type*} [NonUnitalCStarAlgebra A]

/-- Restricting a Hilbert-space representation of `A` to a dense subset `Set.range g` generates the
same closed essential subspace of `H`. -/
theorem topologicalClosure_span_range_comp_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {g : ι → A} (hg : DenseRange g)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (Submodule.span ℂ (⋃ i, Set.range (π (g i)))).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure := by
  set S := Submodule.span ℂ (⋃ i, Set.range (π (g i)))
  refine le_antisymm (Submodule.topologicalClosure_mono <| Submodule.span_mono <|
    Set.iUnion_subset fun i => Set.subset_iUnion (fun a => Set.range (π a)) (g i))
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) S.isClosed_topologicalClosure)
  rintro _ ⟨_, ⟨a, rfl⟩, ξ, rfl⟩
  have hclosed : IsClosed {x : A | π x ξ ∈ S.topologicalClosure} :=
    S.isClosed_topologicalClosure.preimage (by fun_prop)
  refine hclosed.closure_subset_iff.2 ?_ (hg a)
  rintro _ ⟨i, rfl⟩
  exact Submodule.le_topologicalClosure S (Submodule.subset_span (Set.mem_iUnion.2 ⟨i, ξ, rfl⟩))

/-- For any `g : ι → A` with dense range, a Hilbert-space representation
`π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate if and only if the vectors `π (g i) ξ` span a dense
subspace of `H`. -/
theorem isNondegenerate_iff_dense_span_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {g : ι → A} (hg : DenseRange g)
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} :
    π.IsNondegenerate ↔ Dense (Submodule.span ℂ (⋃ i, Set.range (π (g i))) : Set H) := by
  rw [isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top, topologicalClosure_span_range_comp_eq hg]

/-- Restricting a multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` to a dense subset `Set.range g`
generates the same closed essential subspace of `B`. -/
theorem topologicalClosure_span_fst_comp_eq {B : Type*} [NonUnitalCStarAlgebra B] {g : ι → A}
    (hg : DenseRange g) (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    (Submodule.span ℂ (⋃ i, Set.range (φ (g i)).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (φ a).fst)).topologicalClosure := by
  set S := Submodule.span ℂ (⋃ i, Set.range (φ (g i)).fst)
  refine le_antisymm (Submodule.topologicalClosure_mono <| Submodule.span_mono <|
    Set.iUnion_subset fun i => Set.subset_iUnion (fun a => Set.range (φ a).fst) (g i))
    (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) S.isClosed_topologicalClosure)
  rintro _ ⟨_, ⟨a, rfl⟩, b, rfl⟩
  have hcont : Continuous fun x : A => (φ x).fst b :=
    ((DoubleCentralizer.continuous_toProd.fst.comp (map_continuous φ))).clm_apply continuous_const
  have hclosed : IsClosed {x : A | (φ x).fst b ∈ S.topologicalClosure} :=
    S.isClosed_topologicalClosure.preimage hcont
  refine hclosed.closure_subset_iff.2 ?_ (hg a)
  rintro _ ⟨i, rfl⟩
  exact Submodule.le_topologicalClosure S (Submodule.subset_span (Set.mem_iUnion.2 ⟨i, b, rfl⟩))

/-- For any `g : ι → A` with dense range, a multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is
nondegenerate if and only if the elements `(φ (g i)).fst b` span a dense subspace of `B`. -/
theorem isMultiplierNondegenerate_iff_dense_span_comp {B : Type*} [NonUnitalCStarAlgebra B]
    {g : ι → A} (hg : DenseRange g) {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} :
    φ.IsMultiplierNondegenerate ↔
      Dense (Submodule.span ℂ (⋃ i, Set.range (φ (g i)).fst) : Set B) := by
  rw [isMultiplierNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top, topologicalClosure_span_fst_comp_eq hg]

end DenseRange

end NonUnitalStarAlgHom
