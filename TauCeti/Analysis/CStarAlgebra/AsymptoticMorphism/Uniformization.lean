/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AsymptoticMorphism.Basic
public import TauCeti.Analysis.Normed.Operator.BartleGraves
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Uniformization of asymptotic morphisms via Bartle–Graves continuous selections

Applying the Bartle–Graves continuous selection theorem to the surjective quotient map
`AsymptoticAlgebra.mkCLM B : (Set.Ici (1 : ℝ) →ᵇ B) →L[ℂ] AsymptoticAlgebra B` yields a continuous,
positively `ℝ`-homogeneous, linearly norm-bounded right inverse. Composing this selection with
`φ.toAsymptoticHom : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B` replaces any asymptotic morphism
`φ : AsymptoticMorphism A B` by an asymptotically equivalent `ψ` whose trajectory map
`ψ.toBounded : A → (Set.Ici (1 : ℝ) →ᵇ B)` is continuous, positively homogeneous, and uniformly
linearly bounded (`‖ψ t a‖ ≤ C * ‖a‖`). Whenever `Continuous φ.toBounded`, finite open covers of
compact input sets upgrade the pointwise asymptotic estimates of `Basic.lean` to compact-uniform
asymptotic contractivity and compact-uniform algebra defect bounds (Blackadar, §25.1–25.3).

## Main definitions and results

* `TauCeti.AsymptoticAlgebra.exists_continuous_nonlinearRightInverse_mkCLM`: the quotient map
  `(Set.Ici (1 : ℝ) →ᵇ B) →L[ℂ] AsymptoticAlgebra B` admits a continuous Bartle–Graves section.
* `TauCeti.AsymptoticMorphism.exists_equiv_continuous_toBounded`: replacement of `φ` by an
  asymptotically equivalent `ψ` with continuous `ψ.toBounded` and `‖ψ t a‖ ≤ C * ‖a‖`.
* `TauCeti.AsymptoticMorphism.eventually_compact_norm_lt_add`,
  `TauCeti.AsymptoticMorphism.eventually_compact_map_add_lt`,
  `TauCeti.AsymptoticMorphism.eventually_compact_map_smul_lt`,
  `TauCeti.AsymptoticMorphism.eventually_compact_map_mul_lt`, and
  `TauCeti.AsymptoticMorphism.eventually_compact_map_star_lt`: compact-uniform estimates.

## References

* Robert G. Bartle and Lawrence M. Graves, *Mappings between function spaces*, Trans. Amer. Math.
  Soc. **72** (1952), 400–413.
* Alain Connes and Nigel Higson, *Déformations, morphismes asymptotiques et K-théorie bivariante*,
  C. R. Acad. Sci. Paris Sér. I Math. **311** (1990), no. 2, 101–106.
* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**, Cambridge
  University Press, 1998, §25.1–25.3.
-/

public section

open Filter Metric Set Topology
open scoped BoundedContinuousFunction CStarAlgebra

namespace TauCeti

namespace AsymptoticAlgebra

variable (B : Type*) [NonUnitalCStarAlgebra B]

/-- The quotient map `mkCLM B : (Set.Ici (1 : ℝ) →ᵇ B) →L[ℂ] AsymptoticAlgebra B` admits a
continuous, positively `ℝ`-homogeneous, linearly norm-bounded right inverse by the Bartle–Graves
theorem. -/
theorem exists_continuous_nonlinearRightInverse_mkCLM :
    ∃ s : (mkCLM B).NonlinearRightInverse,
      0 < s.nnNorm ∧ Continuous s ∧ ∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ x, s (c • x) = c • s x := by
  obtain ⟨s, hpos, hcont, hhom⟩ :=
    (mkCLM B).exists_continuous_nonlinearRightInverse_of_surjective (mkCLM_surjective B)
  refine ⟨s, hpos, hcont, fun {c} hc x ↦ ?_⟩
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one,
    Complex.coe_smul] using hhom hc x

end AsymptoticAlgebra

namespace AsymptoticMorphism

section BartleGravesUniformization

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Every asymptotic morphism `φ : AsymptoticMorphism A B` is asymptotically equivalent to an
asymptotic morphism `ψ` whose bounded-trajectory map `ψ.toBounded : A → (Set.Ici (1 : ℝ) →ᵇ B)` is
continuous, positively `ℝ`-homogeneous, and satisfies a uniform linear norm bound
`‖ψ t a‖ ≤ C * ‖a‖` for all `t ≥ 1` and `a ∈ A` with `0 < C`. -/
theorem exists_equiv_continuous_toBounded (φ : AsymptoticMorphism A B) :
    ∃ ψ : AsymptoticMorphism A B, ψ.Equiv φ ∧ Continuous ψ.toBounded ∧
      (∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ t a, ψ t (c • a) = c • ψ t a) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ t a, ‖ψ t a‖ ≤ C * ‖a‖ := by
  obtain ⟨s, hs_pos, hs_cont, hs_hom⟩ :=
    AsymptoticAlgebra.exists_continuous_nonlinearRightInverse_mkCLM B
  let sec : A → (Ici (1 : ℝ) →ᵇ B) := fun a ↦ s (φ.toAsymptoticHom a)
  have hsec_mk (a : A) : AsymptoticAlgebra.mk (sec a) = φ.toAsymptoticHom a := by
    rw [← AsymptoticAlgebra.mkCLM_apply]; exact s.right_inv (φ.toAsymptoticHom a)
  let ψ : AsymptoticMorphism A B := ofAsymptoticHomSection sec hsec_mk
  refine ⟨ψ, equiv_iff_toAsymptoticHom_eq.mpr (toAsymptoticHom_ofAsymptoticHomSection sec hsec_mk),
    ?_, ?_, (s.nnNorm : ℝ), NNReal.coe_pos.mpr hs_pos, fun t a ↦ ?_⟩
  · rw [funext (toBounded_ofAsymptoticHomSection sec hsec_mk)]
    exact hs_cont.comp (map_continuous φ.toAsymptoticHom)
  · intro c hc t a
    have hsmul_hom : φ.toAsymptoticHom (c • a) = c • φ.toAsymptoticHom a := by
      rw [← Complex.coe_smul c a, map_smul, Complex.coe_smul]
    simp only [ψ, ofAsymptoticHomSection_apply, sec, hsmul_hom, hs_hom hc]; rfl
  · calc ‖ψ t a‖ = ‖sec a t‖ := by simp [ψ]
      _ ≤ ‖sec a‖ := (sec a).norm_coe_le_norm t
      _ ≤ (s.nnNorm : ℝ) * ‖φ.toAsymptoticHom a‖ := s.bound' (φ.toAsymptoticHom a)
      _ ≤ (s.nnNorm : ℝ) * ‖a‖ :=
        mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ.toAsymptoticHom a)
          (NNReal.coe_nonneg _)

end BartleGravesUniformization

section CompactUniformEstimates

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Compact-uniform asymptotic contractivity**: if `φ : AsymptoticMorphism A B` has continuous
`φ.toBounded : A → (Set.Ici (1 : ℝ) →ᵇ B)`, then for every compact set `K ⊆ A` and `ε > 0`,
eventually `‖φ t a‖ < ‖a‖ + ε` holds simultaneously for all `a ∈ K`. -/
theorem eventually_compact_norm_lt_add {φ : AsymptoticMorphism A B} (hφ : Continuous φ.toBounded)
    {K : Set A} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ∀ a ∈ K, ‖φ t a‖ < ‖a‖ + ε := by
  have h := BoundedContinuousFunction.eventually_forall_compact_norm_lt_add
    (F := φ.toBounded) (g := fun a ↦ ‖a‖) hK hφ.continuousOn continuous_norm.continuousOn
    (fun a _ {δ} hδ ↦ by simpa only [toBounded_apply] using φ.eventually_norm_lt_add a hδ) hε
  simpa only [toBounded_apply] using h

/-- **Compact-uniform addition defect**: if `Continuous φ.toBounded`, the addition defect of `φ`
tends to `0` uniformly on products `K₁ ×ˢ K₂` of compact subsets of `A`. -/
theorem eventually_compact_map_add_lt {φ : AsymptoticMorphism A B} (hφ : Continuous φ.toBounded)
    {K₁ K₂ : Set A} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ∀ a ∈ K₁, ∀ b ∈ K₂,
      ‖φ t (a + b) - (φ t a + φ t b)‖ < ε := by
  let F : A × A → (Ici (1 : ℝ) →ᵇ B) := fun p ↦
    φ.toBounded (p.1 + p.2) - (φ.toBounded p.1 + φ.toBounded p.2)
  have hF : Continuous F :=
    (hφ.comp (continuous_fst.add continuous_snd)).sub
      ((hφ.comp continuous_fst).add (hφ.comp continuous_snd))
  have h := BoundedContinuousFunction.eventually_forall_compact_norm_lt (hK₁.prod hK₂)
    hF.continuousOn
    (fun p _ ↦ (φ.map_add_tendsto p.1 p.2).congr fun t ↦ by simp [F, toBounded_apply]) hε
  filter_upwards [h] with t ht a ha b hb
  simpa [F, toBounded_apply] using ht (a, b) ⟨ha, hb⟩

/-- **Compact-uniform scalar multiplication defect**: if `Continuous φ.toBounded`, the `ℂ`-scalar
defect of `φ` tends to `0` uniformly on compact subsets `Λ ⊆ ℂ` and `K ⊆ A`. -/
theorem eventually_compact_map_smul_lt {φ : AsymptoticMorphism A B} (hφ : Continuous φ.toBounded)
    {Λ : Set ℂ} {K : Set A} (hΛ : IsCompact Λ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ∀ c ∈ Λ, ∀ a ∈ K,
      ‖φ t (c • a) - c • φ t a‖ < ε := by
  let F : ℂ × A → (Ici (1 : ℝ) →ᵇ B) := fun p ↦
    φ.toBounded (p.1 • p.2) - p.1 • φ.toBounded p.2
  have hF : Continuous F :=
    (hφ.comp (continuous_fst.smul continuous_snd)).sub
      (continuous_fst.smul (hφ.comp continuous_snd))
  have h := BoundedContinuousFunction.eventually_forall_compact_norm_lt (hΛ.prod hK)
    hF.continuousOn
    (fun p _ ↦ (φ.map_smul_tendsto p.1 p.2).congr fun t ↦ by simp [F, toBounded_apply]) hε
  filter_upwards [h] with t ht c hc a ha
  simpa [F, toBounded_apply] using ht (c, a) ⟨hc, ha⟩

/-- **Compact-uniform multiplication defect**: if `Continuous φ.toBounded`, the multiplication
defect of `φ` tends to `0` uniformly on products `K₁ ×ˢ K₂` of compact subsets of `A`. -/
theorem eventually_compact_map_mul_lt {φ : AsymptoticMorphism A B} (hφ : Continuous φ.toBounded)
    {K₁ K₂ : Set A} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ∀ a ∈ K₁, ∀ b ∈ K₂,
      ‖φ t (a * b) - φ t a * φ t b‖ < ε := by
  let F : A × A → (Ici (1 : ℝ) →ᵇ B) := fun p ↦
    φ.toBounded (p.1 * p.2) - φ.toBounded p.1 * φ.toBounded p.2
  have hF : Continuous F :=
    (hφ.comp (continuous_fst.mul continuous_snd)).sub
      ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd))
  have h := BoundedContinuousFunction.eventually_forall_compact_norm_lt (hK₁.prod hK₂)
    hF.continuousOn
    (fun p _ ↦ (φ.map_mul_tendsto p.1 p.2).congr fun t ↦ by simp [F, toBounded_apply]) hε
  filter_upwards [h] with t ht a ha b hb
  simpa [F, toBounded_apply] using ht (a, b) ⟨ha, hb⟩

/-- **Compact-uniform involution defect**: if `Continuous φ.toBounded`, the involution defect of
`φ` tends to `0` uniformly on compact subsets `K ⊆ A`. -/
theorem eventually_compact_map_star_lt {φ : AsymptoticMorphism A B} (hφ : Continuous φ.toBounded)
    {K : Set A} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Ici (1 : ℝ) in atTop, ∀ a ∈ K,
      ‖φ t (star a) - star (φ t a)‖ < ε := by
  let F : A → (Ici (1 : ℝ) →ᵇ B) := fun a ↦
    φ.toBounded (star a) - star (φ.toBounded a)
  have hF : Continuous F := (hφ.comp continuous_star).sub hφ.star
  have h := BoundedContinuousFunction.eventually_forall_compact_norm_lt hK hF.continuousOn
    (fun a _ ↦ (φ.map_star_tendsto a).congr fun t ↦ by simp [F, toBounded_apply]) hε
  filter_upwards [h] with t ht a ha
  simpa [F, toBounded_apply] using ht a ha

end CompactUniformEstimates

end AsymptoticMorphism

end TauCeti

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The constant asymptotic morphism attached to any `⋆`-homomorphism `f : A →⋆ₙₐ[ℂ] B` already has
continuous `toBounded : A → (Set.Ici (1 : ℝ) →ᵇ B)`. -/
theorem continuous_toBounded_toAsymptoticMorphism (f : A →⋆ₙₐ[ℂ] B) :
    Continuous f.toAsymptoticMorphism.toBounded := by
  let constHom : B →+ (Ici (1 : ℝ) →ᵇ B) :=
    { toFun := BoundedContinuousFunction.const (Ici (1 : ℝ))
      map_zero' := by ext; rfl
      map_add' := fun _ _ ↦ by ext; rfl }
  have hconst_cont : Continuous constHom :=
    AddMonoidHomClass.continuous_of_bound constHom 1 fun b ↦ by
      simpa only [constHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] using
        BoundedContinuousFunction.norm_const_le b
  have heq : f.toAsymptoticMorphism.toBounded = fun a ↦ constHom (f a) := by
    ext a t
    simp [constHom]
  rw [heq]
  exact hconst_cont.comp (map_continuous f)

end NonUnitalStarAlgHom
