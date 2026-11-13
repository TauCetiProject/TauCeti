/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Algebra.Module.Span

/-!
# Nondegenerate homomorphisms into multiplier algebras

A `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` between C⋆-algebras is *nondegenerate*
(`NonUnitalStarAlgHom.IsMultiplierNondegenerate`) when `(φ a).fst b` — equivalently `(φ a).snd b`
(`isMultiplierNondegenerate_iff_dense_snd`) — has dense span in `B`, or `(φ e).fst b → b` /
`(φ e).snd b → b` along norm-bounded approximate units (`isMultiplierNondegenerate_iff_tendsto_fst`,
`isMultiplierNondegenerate_iff_tendsto_snd`). Every nondegenerate `φ` extends uniquely to
`φ' := φ.extendToMultiplier hφ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)` with `φ' m * φ a = φ (m.fst a)` and
`φ a * φ' m = φ (m.snd a)`, preserving strict continuity on norm-bounded families and composing
(`extendToMultiplier_comp`, `multiplierExtension_comp`).

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.39 and Proposition 2.46.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.50.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra

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

/-- Nondegeneracy of `φ` is equivalent to density of the span of `(φ a).snd b` in `B`. -/
theorem isMultiplierNondegenerate_iff_dense_snd :
    φ.IsMultiplierNondegenerate ↔ Dense (Submodule.span ℂ (⋃ a, Set.range (φ a).snd) : Set B) := by
  have hcl {L₁ L₂ : A → B → B} (hswap : ∀ a b, star (L₂ a b) = L₁ (star a) (star b))
      (hd : Dense (Submodule.span ℂ (⋃ a, Set.range (L₂ a)) : Set B)) :
      Dense (Submodule.span ℂ (⋃ a, Set.range (L₁ a)) : Set B) := fun b => by
    set S₁ := Submodule.span ℂ (⋃ a, Set.range (L₁ a))
    have hmem : (Submodule.span ℂ (⋃ a, Set.range (L₂ a)) : Set B) ⊆ star ⁻¹' closure S₁ :=
      fun z hz => subset_closure <| by
        induction hz using Submodule.span_induction with
        | mem _ hx =>
          obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hx
          exact Submodule.subset_span <| Set.mem_iUnion.2 ⟨star a, star y, (hswap a y).symm⟩
        | zero => simp
        | add _ _ _ _ hu hv => simpa only [SetLike.mem_coe, star_add] using S₁.add_mem hu hv
        | smul c _ _ hu => simpa only [SetLike.mem_coe, star_smul] using S₁.smul_mem (star c) hu
    simpa using (isClosed_closure.preimage continuous_star).closure_subset_iff.2 hmem (hd (star b))
  exact ⟨hcl fun _ _ => by simp [map_star], hcl fun _ _ => by simp [map_star]⟩

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
  star_injective <| hφ.ext fun a => by simpa [← map_star] using congrArg star (h (star a))

/-- A homomorphism from a unital C⋆-algebra sending `1` to `1` is nondegenerate. -/
theorem isMultiplierNondegenerate_of_map_one {D : Type*} [CStarAlgebra D]
    {ψ : D →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hψ : ψ 1 = 1) : ψ.IsMultiplierNondegenerate := fun b =>
  subset_closure <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨1, b, by simp [hψ]⟩

/-- The canonical inclusion `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` is nondegenerate. -/
@[simp]
theorem isMultiplierNondegenerate_coeHom :
    (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).IsMultiplierNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine fun b => mem_closure_of_tendsto (hl.tendsto_mul_right b) <| .of_forall fun e => ?_
  exact Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, b, by simp⟩

private theorem exists_tendsto_fst {l : Filter A} [l.NeBot] {C : ℝ}
    (hφ : φ.IsMultiplierNondegenerate) (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (m : 𝓜(ℂ, A)) :
    ∃ T : B →L[ℂ] B, (∀ a, T * (φ a).fst = (φ (m.fst a)).fst) ∧
      ∀ b, Tendsto (fun e => (φ (m.fst e)).fst b) l (𝓝 (T b)) :=
  m.exists_clm_tendsto_fst (K := 1) (L := fun a => (φ a).fst) hC hl (fun _ => by fun_prop)
    (fun a b => by rw [map_mul, DoubleCentralizer.mul_fst])
    (fun a => by simpa only [DoubleCentralizer.norm_fst, one_mul] using norm_apply_le φ a) hφ

private theorem exists_clm_mul_eq (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) :
    ∃ T : B →L[ℂ] B, ∀ a, T * (φ a).fst = (φ (m.fst a)).fst := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  exact ⟨_, (exists_tendsto_fst hφ hl.eventually_norm hl.tendsto_mul_right m).choose_spec.1⟩

private def extensionCLM (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) : B →L[ℂ] B :=
  (exists_clm_mul_eq hφ m).choose

private theorem extensionCLM_mul (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    extensionCLM hφ m * (φ a).fst = (φ (m.fst a)).fst :=
  (exists_clm_mul_eq hφ m).choose_spec a

private theorem star_extensionCLM_mul (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A))
    (x y : B) : star (extensionCLM hφ (star m) x) * y = star x * extensionCLM hφ m y := by
  have hstar (q : A) (u w : B) : star ((φ q).fst u) * w = star u * (φ (star q)).fst w := by
    rw [← (φ (star q)).central, map_star φ, DoubleCentralizer.star_snd, star_star]
  have happ (n : 𝓜(ℂ, A)) (q : A) (w : B) :
      extensionCLM hφ n ((φ q).fst w) = (φ (n.fst q)).fst w := congr($(extensionCLM_mul hφ n q) w)
  have hy (a : A) (u : B) : star (extensionCLM hφ (star m) ((φ a).fst u)) * y =
      star ((φ a).fst u) * extensionCLM hφ m y := by
    refine congr($(ContinuousLinearMap.ext_on hφ
      (f := ContinuousLinearMap.mul ℂ B (star (extensionCLM hφ (star m) ((φ a).fst u))))
      (g := (ContinuousLinearMap.mul ℂ B (star ((φ a).fst u))).comp (extensionCLM hφ m))
      fun _ hz => ?_) y)
    obtain ⟨c, v, rfl⟩ := Set.mem_iUnion.1 hz
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.comp_apply, happ, hstar]
    rw [← mul_apply_eq_comp, ← DoubleCentralizer.mul_fst, ← map_mul, DoubleCentralizer.star_fst,
      star_star, m.central, map_mul, DoubleCentralizer.mul_fst, mul_apply_eq_comp]
  refine star_injective ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', star_mul,
    star_star] using congr($(ContinuousLinearMap.ext_on hφ
    (f := (ContinuousLinearMap.mul ℂ B (star y)).comp (extensionCLM hφ (star m)))
    (g := ContinuousLinearMap.mul ℂ B (star (extensionCLM hφ m y))) fun _ hz => by
      obtain ⟨a, u, rfl⟩ := Set.mem_iUnion.1 hz
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', star_mul,
        star_star] using congrArg star (hy a u)) x)

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
  hφ.ext fun _ => by rw [mul_assoc, extensionMultiplier_mul, ← map_mul, ← map_mul, m.central]

/-- The unital extension of a nondegenerate ⋆-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` to multiplier
algebras: the unique multiplier `φ' m` satisfying `φ' m * φ a = φ (m.fst a)` for every `a : A`. -/
def extendToMultiplier (hφ : φ.IsMultiplierNondegenerate) : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B) where
  toFun := extensionMultiplier hφ
  map_one' := (eq_extensionMultiplier hφ fun _ => by simp).symm
  map_mul' _ _ := (eq_extensionMultiplier hφ fun _ => by
    simp [mul_assoc, extensionMultiplier_mul]).symm
  map_zero' := (eq_extensionMultiplier hφ fun _ => by simp).symm
  map_add' _ _ := (eq_extensionMultiplier hφ fun _ => by
    simp [add_mul, extensionMultiplier_mul]).symm
  commutes' _ := (eq_extensionMultiplier hφ fun _ => by simp [Algebra.algebraMap_eq_smul_one]).symm
  map_star' _ := (eq_extensionMultiplier hφ fun _ => by
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

/-- A multiplier equals `φ' m` if and only if it satisfies `φ a * n = φ (m.snd a)` for all `a`. -/
theorem eq_extendToMultiplier_iff_snd {m : 𝓜(ℂ, A)} {n : 𝓜(ℂ, B)} :
    n = φ.extendToMultiplier hφ m ↔ ∀ a, φ a * n = φ (m.snd a) :=
  ⟨fun h a => h ▸ mul_extendToMultiplier_eq_snd hφ m a,
    fun h => hφ.ext_mul_left fun a => (h a).trans (mul_extendToMultiplier_eq_snd hφ m a).symm⟩

/-- The multiplier extension restricts to `φ` on `A`. -/
@[simp]
theorem extendToMultiplier_coe (a : A) : φ.extendToMultiplier hφ (a : 𝓜(ℂ, A)) = φ a :=
  ((eq_extendToMultiplier_iff hφ).2 fun _ => by simp).symm

/-- `φ.extendToMultiplier hφ` is the unique multiplicative map on `𝓜(ℂ, A)` extending `φ`. -/
theorem eq_extendToMultiplier_of_apply_coe {F : Type*} [FunLike F 𝓜(ℂ, A) 𝓜(ℂ, B)]
    [MulHomClass F 𝓜(ℂ, A) 𝓜(ℂ, B)] (ψ : F) (hψ : ∀ a : A, ψ a = φ a) :
    ⇑ψ = φ.extendToMultiplier hφ := by
  funext m
  refine (eq_extendToMultiplier_iff hφ).2 fun a => ?_
  rw [← hψ, ← map_mul, DoubleCentralizer.mul_coe_eq_coe_fst, hψ]

/-- Extending the canonical inclusion `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` gives the identity on `𝓜(ℂ, A)`. -/
@[simp]
theorem extendToMultiplier_coeHom
    (h : (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).IsMultiplierNondegenerate) :
    (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).extendToMultiplier h =
      StarAlgHom.id ℂ 𝓜(ℂ, A) :=
  StarAlgHom.ext <| congrFun (eq_extendToMultiplier_of_apply_coe h
    (StarAlgHom.id ℂ 𝓜(ℂ, A)) fun _ => rfl).symm

/-- Along any eventually norm-bounded net `e` with `e * a → a` for all `a : A`,
`(φ (m.fst e)).fst b` converges in norm to `(φ.extendToMultiplier hφ m).fst b`. -/
theorem tendsto_extendToMultiplier_fst {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (m : 𝓜(ℂ, A)) (b : B) :
    Tendsto (fun e => (φ (m.fst e)).fst b) l (𝓝 ((φ.extendToMultiplier hφ m).fst b)) := by
  obtain ⟨T, hT, hlim⟩ := exists_tendsto_fst hφ hC hl m
  exact (hφ.clm_ext fun a => (hT a).trans
    (congrArg (fun x : 𝓜(ℂ, B) => x.fst) (extendToMultiplier_mul_eq_fst hφ m a)).symm) ▸ hlim b

/-- Along any eventually norm-bounded net `e` with `a * e → a` for all `a : A`,
`(φ (m.snd e)).snd b` converges in norm to `(φ.extendToMultiplier hφ m).snd b`. -/
theorem tendsto_extendToMultiplier_snd {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) (m : 𝓜(ℂ, A)) (b : B) :
    Tendsto (fun e => (φ (m.snd e)).snd b) l (𝓝 ((φ.extendToMultiplier hφ m).snd b)) := by
  have : (map star l).NeBot := map_neBot
  have hC' : ∀ᶠ e in map star l, ‖e‖ ≤ C :=
    eventually_map.2 (hC.mono fun e he => (norm_star e).trans_le he)
  have hl' (a : A) : Tendsto (· * a) (map star l) (𝓝 a) :=
    tendsto_map'_iff.2 <| by simpa [Function.comp_def, star_mul] using (hl (star a)).star
  simpa [Function.comp_def, map_star] using
    (tendsto_map'_iff.1 (tendsto_extendToMultiplier_fst hφ hC' hl' (star m) (star b))).star

/-- Norm-bounded left-strictly continuous families in `𝓜(ℂ, A)` map to left-strictly continuous
families in `𝓜(ℂ, B)` under `extendToMultiplier`. -/
theorem continuous_extendToMultiplier_fst_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {K : ℝ}
    (hK : ∀ x, ‖u x‖ ≤ K) (b : B) :
    Continuous fun x => (φ.extendToMultiplier hφ (u x)).fst b := by
  refine ContinuousLinearMap.continuous_apply_of_dense_span (C := K)
    (f := fun x => (φ.extendToMultiplier hφ (u x)).fst) hφ
    (fun x => (DoubleCentralizer.norm_fst _).trans_le <|
      (norm_apply_le (φ.extendToMultiplier hφ).toNonUnitalStarAlgHom _).trans (hK x))
    (fun _ hz => ?_) b
  obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hz
  simp only [extendToMultiplier_fst_apply]
  fun_prop

/-- Norm-bounded right-strictly continuous families remain right-strictly continuous under `φ'`. -/
theorem continuous_extendToMultiplier_snd_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).snd a) {K : ℝ}
    (hK : ∀ x, ‖u x‖ ≤ K) (b : B) :
    Continuous fun x => (φ.extendToMultiplier hφ (u x)).snd b := by
  have hu' (a : A) : Continuous fun x => (star (u x)).fst a :=
    (hu (star a)).star.congr fun x => (DoubleCentralizer.star_fst (u x) a).symm
  exact (continuous_extendToMultiplier_fst_apply hφ hu'
    (fun x => (norm_star _).trans_le (hK x)) (star b)).star.congr fun x => by simp [map_star]

/-- Along any eventually norm-bounded net `e` with `e * a → a` for all `a : A`, `φ` is
nondegenerate if and only if `(φ e).fst b → b` in norm for every `b : B`. -/
theorem isMultiplierNondegenerate_iff_tendsto_fst {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    φ.IsMultiplierNondegenerate ↔ ∀ b, Tendsto (fun e => (φ e).fst b) l (𝓝 b) :=
  ⟨fun hφ b => by simpa using tendsto_extendToMultiplier_fst hφ hC hl 1 b,
    fun h b => mem_closure_of_tendsto (h b) <| .of_forall fun e =>
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, b, rfl⟩⟩

/-- Along any eventually norm-bounded net `e` with `a * e → a` for all `a : A`, `φ` is
nondegenerate if and only if `(φ e).snd b → b` in norm for every `b : B`. -/
theorem isMultiplierNondegenerate_iff_tendsto_snd {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    φ.IsMultiplierNondegenerate ↔ ∀ b, Tendsto (fun e => (φ e).snd b) l (𝓝 b) :=
  ⟨fun hφ b => by simpa using tendsto_extendToMultiplier_snd hφ hC hl 1 b,
    fun h => isMultiplierNondegenerate_iff_dense_snd.2 fun b =>
      mem_closure_of_tendsto (h b) <| .of_forall fun e =>
        Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, b, rfl⟩⟩

private theorem dense_span_of_apply_eq {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (hφ : φ.IsMultiplierNondegenerate) {L : B → E →L[ℂ] E} {L' : A → E →L[ℂ] E}
    (hL_add : ∀ y z, L (y + z) = L y + L z) (hL_smul : ∀ (c : ℂ) y, L (c • y) = c • L y)
    (hL_cont : ∀ ξ, Continuous fun b => L b ξ)
    (hL_dense : Dense (Submodule.span ℂ (⋃ b, Set.range (L b)) : Set E))
    (hcomp : ∀ a d ξ, L' a (L d ξ) = L ((φ a).fst d) ξ) :
    Dense (Submodule.span ℂ (⋃ a, Set.range (L' a)) : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at hL_dense ⊢
  set S := Submodule.span ℂ (⋃ a, Set.range (L' a))
  rw [eq_top_iff, ← hL_dense]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    S.isClosed_topologicalClosure
  rintro _ ⟨_, ⟨b, rfl⟩, ξ, rfl⟩
  let f : B →ₗ[ℂ] E :=
    { toFun y := L y ξ, map_add' y z := by simp [hL_add], map_smul' c y := by simp [hL_smul] }
  refine (S.isClosed_topologicalClosure.preimage (hL_cont ξ)).closure_subset_iff.2
    (Submodule.span_le (p := S.topologicalClosure.comap f).2 ?_) (hφ b)
  rintro _ ⟨_, ⟨a, rfl⟩, d, rfl⟩
  exact Submodule.le_topologicalClosure S <| Submodule.subset_span <|
    Set.mem_iUnion.2 ⟨a, L d ξ, by simp [f, hcomp]⟩

/-- Composing a nondegenerate `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` with `ψ.extendToMultiplier hψ` for a
nondegenerate `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` produces a nondegenerate multiplier homomorphism. -/
theorem IsMultiplierNondegenerate.extendToMultiplier_comp
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (hφ : φ.IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ).IsMultiplierNondegenerate :=
  dense_span_of_apply_eq hφ (L := fun b => (ψ b).fst)
    (L' := fun a => (((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ) a).fst)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => by fun_prop) hψ fun _ _ _ => by simp

/-- The multiplier extension of `(ψ.extendToMultiplier hψ) ∘ φ` is the composite of the two
multiplier extensions. -/
@[simp]
theorem extendToMultiplier_comp {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    (hφ : φ.IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ).extendToMultiplier
      (hψ.extendToMultiplier_comp hφ) =
        (ψ.extendToMultiplier hψ).comp (φ.extendToMultiplier hφ) :=
  StarAlgHom.ext <| congrFun (eq_extendToMultiplier_of_apply_coe (hψ.extendToMultiplier_comp hφ)
    ((ψ.extendToMultiplier hψ).comp (φ.extendToMultiplier hφ)) fun _ => by simp).symm

/-- Composing a nondegenerate `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` with `π.multiplierExtension hπ` for a
nondegenerate representation `π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)` produces a nondegenerate representation. -/
theorem IsNondegenerate.multiplierExtension_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hφ : φ.IsMultiplierNondegenerate) :
    ((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ).IsNondegenerate :=
  isNondegenerate_iff_dense.2 <| dense_span_of_apply_eq hφ (L := ⇑π)
    (L' := ⇑((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ))
    (map_add π) (map_smul π) (fun _ => by fun_prop) (isNondegenerate_iff_dense.1 hπ)
    fun _ _ _ => by simp

/-- The Hilbert-space multiplier extension of `(π.multiplierExtension hπ) ∘ φ` factors through
`φ.extendToMultiplier hφ`. -/
@[simp]
theorem multiplierExtension_comp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hφ : φ.IsMultiplierNondegenerate) :
    ((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp φ).multiplierExtension
      (hπ.multiplierExtension_comp hφ) =
        (π.multiplierExtension hπ).comp (φ.extendToMultiplier hφ) :=
  StarAlgHom.ext <| congrFun (eq_multiplierExtension_of_apply_coe (hπ.multiplierExtension_comp hφ)
    ((π.multiplierExtension hπ).comp (φ.extendToMultiplier hφ)) fun _ => by simp).symm

/-- Restricting a multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` to a dense subset `Set.range g`
generates the same closed essential subspace of `B`. -/
theorem topologicalClosure_span_fst_comp_eq {ι : Type*} {g : ι → A}
    (hg : DenseRange g) (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    (Submodule.span ℂ (⋃ i, Set.range (φ (g i)).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (φ a).fst)).topologicalClosure :=
  hg.topologicalClosure_span_iUnion_range_comp_eq (R := ℂ) (L := fun a => ⇑(φ a).fst) fun _ =>
    by fun_prop

/-- For any `g : ι → A` with dense range, `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate if and only if
the elements `(φ (g i)).fst b` span a dense subspace of `B`. -/
theorem isMultiplierNondegenerate_iff_dense_span_comp {ι : Type*} {g : ι → A} (hg : DenseRange g) :
    φ.IsMultiplierNondegenerate ↔
      Dense (Submodule.span ℂ (⋃ i, Set.range (φ (g i)).fst) : Set B) := by
  simp_rw [isMultiplierNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    topologicalClosure_span_fst_comp_eq hg]

end NonUnitalStarAlgHom
