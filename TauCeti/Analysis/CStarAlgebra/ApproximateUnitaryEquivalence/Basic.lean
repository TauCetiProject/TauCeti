/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.Hom

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set, equivalently when one lies in the point-norm closure of the unitary
conjugacy orbit of the other (`TauCeti.approximatelyUnitarilyEquivalent_iff_mem_closure`).
This file proves the equivalence-relation laws, joint closedness in the point-norm topology,
and compatibility with composition. Postcomposition is by a unital map, so implementing
unitaries remain unitaries. The relation preserves pointwise norms, injectivity, and (when
the source is unital) preservation of the identity element; in particular, mutually inverse
maps up to approximate unitary equivalence between unital C⋆-algebras are automatically unital.

The convention is that of Kirchberg–Phillips, *Embedding of exact C*-algebras in the
Cuntz algebra O₂*, Definition 0.5, extended to possibly nonunital source maps.
This is the target-unitary relation, not the multiplier- or unitization-unitary relation.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Approximate unitary equivalence, implemented by unitaries of the unital target itself.
The source and the two maps need not be unital. -/
def ApproximatelyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ u : unitary B, ∀ a ∈ F, ‖(u : B) * φ a * star (u : B) - ψ a‖ < ε

/-- Finite-set characterization of approximate unitary equivalence with target unitaries. -/
theorem approximatelyUnitarilyEquivalent_def (φ ψ : A →⋆ₙₐ[ℂ] B) :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε →
        ∃ u : unitary B, ∀ a ∈ F, ‖(u : B) * φ a * star (u : B) - ψ a‖ < ε :=
  Iff.rfl

namespace ApproximatelyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed unitary conjugacy gives approximate unitary equivalence. -/
theorem of_unitary (u : unitary B)
    (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  intro F ε hε
  exact ⟨u, fun a _ ↦ by simpa [h a] using hε⟩

/-- Approximate unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : ApproximatelyUnitarilyEquivalent φ φ :=
  of_unitary 1 (by simp)

/-- Approximate unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent ψ φ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨star u, fun a ha ↦ ?_⟩
  have heq : ‖(star u : B) * ψ a * (u : B) - φ a‖ =
      ‖(u : B) * φ a * star (u : B) - ψ a‖ := by
    let e := Unitary.conjStarAlgAut ℂ B u
    have hn := (StarAlgEquiv.isometry e.symm).dist_eq (ψ a) (e (φ a))
    rw [e.symm_apply_apply] at hn
    simpa only [e, dist_eq_norm, Unitary.conjStarAlgAut_symm_apply,
      Unitary.conjStarAlgAut_apply, norm_sub_rev] using hn
  simpa only [Unitary.coe_star, star_star] using heq.trans_lt (hu a ha)

/-- Approximate unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : ApproximatelyUnitarilyEquivalent φ ψ)
    (h₂ : ApproximatelyUnitarilyEquivalent ψ χ) : ApproximatelyUnitarilyEquivalent φ χ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h₁ F (ε / 2) (by positivity)
  obtain ⟨v, hv⟩ := h₂ F (ε / 2) (by positivity)
  refine ⟨v * u, fun a ha ↦ ?_⟩
  have heq : (v : B) * ((u : B) * φ a * star (u : B) - ψ a) * star (v : B) +
      ((v : B) * ψ a * star (v : B) - χ a) =
      ((v * u : unitary B) : B) * φ a * star ((v * u : unitary B) : B) - χ a := by
    simp [mul_sub, sub_mul, mul_assoc]
  rw [← heq]
  calc
    _ ≤ ‖(v : B) * ((u : B) * φ a * star (u : B) - ψ a) * star (v : B)‖ +
        ‖(v : B) * ψ a * star (v : B) - χ a‖ := norm_add_le _ _
    _ = ‖(u : B) * φ a * star (u : B) - ψ a‖ +
        ‖(v : B) * ψ a * star (v : B) - χ a‖ := by
      simpa only [Unitary.coe_star] using congrArg
        (fun x : ℝ ↦ x + ‖(v : B) * ψ a * star (v : B) - χ a‖)
        ((CStarRing.norm_mul_coe_unitary _ (star v)).trans
          (CStarRing.norm_coe_unitary_mul v _))
    _ < ε / 2 + ε / 2 := add_lt_add (hu a ha) (hv a ha)
    _ = ε := by ring

/-- The target-unitary relation is an equivalence relation. -/
theorem equivalence : Equivalence (ApproximatelyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition preserves approximate unitary equivalence, without a unitality condition. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : ApproximatelyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  classical
  intro F ε hε
  obtain ⟨u, hu⟩ := h (F.image ρ) ε hε
  exact ⟨u, fun a ha ↦ hu (ρ a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩

/-- Unital postcomposition preserves approximate unitary equivalence. -/
theorem postcomp [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨Unitary.map (StarMonoidHom.ofClass ρ) u, fun a ha ↦ ?_⟩
  -- The class-to-bundled star-monoid hom has no coercion simp lemma.
  have hρ (b : B) : (StarMonoidHom.ofClass ρ) b = ρ b := rfl
  simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    Unitary.coe_map, hρ, ← map_star, ← map_mul, ← map_sub] using
    (NonUnitalStarAlgHom.norm_apply_le ρ
      ((u : B) * φ a * star (u : B) - ψ a)).trans_lt (hu a ha)

/-- Approximately unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : ApproximatelyUnitarilyEquivalent φ ψ) (a : A) : ‖φ a‖ = ‖ψ a‖ := by
  have hle {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) :
      ‖φ a‖ ≤ ‖ψ a‖ := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨u, hu⟩ := h {a} ε hε
    have hn := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ B u) (φ a)
    have ht := norm_le_norm_add_norm_sub (ψ a) ((u : B) * φ a * star (u : B))
    rw [Unitary.conjStarAlgAut_apply] at hn
    rw [hn, norm_sub_rev] at ht
    linarith [hu a (Finset.mem_singleton_self a)]
  exact le_antisymm (hle h) (hle h.symm)

/-- Approximate unitary equivalence preserves injectivity. -/
theorem injective_iff (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  rw [injective_iff_map_eq_zero φ, injective_iff_map_eq_zero ψ]
  exact forall_congr' fun a ↦ by rw [← norm_eq_zero (a := φ a),
    ← norm_eq_zero (a := ψ a), h.norm_eq]

/-- Approximate unitary equivalence is a closed relation in the product point-norm topology on
`(A →⋆ₙₐ[ℂ] B) × (A →⋆ₙₐ[ℂ] B)`. -/
theorem isClosed_prod :
    IsClosed {p : (A →⋆ₙₐ[ℂ] B) × (A →⋆ₙₐ[ℂ] B) | ApproximatelyUnitarilyEquivalent p.1 p.2} := by
  rw [← closure_subset_iff_isClosed]
  rintro ⟨φ, ψ⟩ hp F ε hε
  have hmem : ({φ' : A →⋆ₙₐ[ℂ] B | ∀ a ∈ F, ‖φ' a - φ a‖ < ε / 3} ×ˢ
      {ψ' : A →⋆ₙₐ[ℂ] B | ∀ a ∈ F, ‖ψ' a - ψ a‖ < ε / 3}) ∈ 𝓝 (φ, ψ) := by
    refine prod_mem_nhds ?_ ?_
    · exact (φ.hasBasis_nhds.mem_iff).mpr ⟨⟨F, {x | dist x.1 x.2 < ε / 3}⟩,
        Metric.dist_mem_uniformity (by positivity),
        fun χ hχ a ha ↦ by simpa only [dist_eq_norm, Set.mem_ofPred_eq] using hχ a ha⟩
    · exact (ψ.hasBasis_nhds.mem_iff).mpr ⟨⟨F, {x | dist x.1 x.2 < ε / 3}⟩,
        Metric.dist_mem_uniformity (by positivity),
        fun χ hχ a ha ↦ by simpa only [dist_eq_norm, Set.mem_ofPred_eq] using hχ a ha⟩
  obtain ⟨⟨φ', ψ'⟩, ⟨hφ', hψ'⟩, hrel⟩ := mem_closure_iff_nhds.mp hp _ hmem
  obtain ⟨u, hu⟩ := hrel F (ε / 3) (by positivity)
  refine ⟨u, fun a ha ↦ ?_⟩
  let e := Unitary.conjStarAlgAut ℂ B u
  have he : ‖(u : B) * (φ a - φ' a) * star (u : B)‖ = ‖φ a - φ' a‖ := by
    simpa only [e, Unitary.conjStarAlgAut_apply] using StarAlgEquiv.norm_map e (φ a - φ' a)
  have hsplit : (u : B) * φ a * star (u : B) - ψ a =
      (u : B) * (φ a - φ' a) * star (u : B) + ((u : B) * φ' a * star (u : B) - ψ' a) +
        (ψ' a - ψ a) := by
    simp only [mul_sub, sub_mul]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖(u : B) * (φ a - φ' a) * star (u : B)‖ + ‖(u : B) * φ' a * star (u : B) - ψ' a‖ +
        ‖ψ' a - ψ a‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖φ' a - φ a‖ + ‖(u : B) * φ' a * star (u : B) - ψ' a‖ + ‖ψ' a - ψ a‖ := by
      rw [he, norm_sub_rev (φ a)]
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add (hφ' a ha) (hu a ha)) (hψ' a ha)
    _ = ε := by ring

/-- For fixed `φ`, the set of maps approximately unitarily equivalent to `φ` is closed in the
point-norm topology. -/
theorem isClosed_right (φ : A →⋆ₙₐ[ℂ] B) :
    IsClosed {ψ : A →⋆ₙₐ[ℂ] B | ApproximatelyUnitarilyEquivalent φ ψ} :=
  isClosed_prod.preimage (continuous_const.prodMk continuous_id)

/-- For fixed `ψ`, the set of maps approximately unitarily equivalent to `ψ` is closed in the
point-norm topology. -/
theorem isClosed_left (ψ : A →⋆ₙₐ[ℂ] B) :
    IsClosed {φ : A →⋆ₙₐ[ℂ] B | ApproximatelyUnitarilyEquivalent φ ψ} :=
  isClosed_prod.preimage (continuous_id.prodMk continuous_const)

/-- Approximate unitary equivalence passes to point-norm limits in both arguments along any
nontrivial filter. -/
theorem of_tendsto_hom {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → A →⋆ₙₐ[ℂ] B} (hf : Tendsto f l (𝓝 φ)) (hg : Tendsto g l (𝓝 ψ))
    (hfg : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent (f i) (g i)) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  isClosed_prod.mem_of_tendsto (hf.prodMk_nhds hg) hfg

/-- Approximate unitary equivalence passes to point-norm limits on the right. -/
theorem of_tendsto_right {ι : Type*} {l : Filter ι} [l.NeBot]
    {g : ι → A →⋆ₙₐ[ℂ] B} (hg : Tendsto g l (𝓝 ψ))
    (h : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent φ (g i)) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  of_tendsto_hom tendsto_const_nhds hg h

/-- Approximate unitary equivalence passes to point-norm limits on the left. -/
theorem of_tendsto_left {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → A →⋆ₙₐ[ℂ] B} (hf : Tendsto f l (𝓝 φ))
    (h : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent (f i) ψ) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  of_tendsto_hom hf tendsto_const_nhds h

section UnitalSource

variable {A : Type*} [CStarAlgebra A] {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Between unital C⋆-algebras, approximate unitary equivalence preserves unitality. -/
theorem map_one_eq_one_iff (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    φ 1 = 1 ↔ ψ 1 = 1 := by
  have aux {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) (hψ : ψ 1 = 1) :
      φ 1 = 1 := by
    obtain ⟨u, hu⟩ := h {1} (1 / 2) (by positivity)
    let e := Unitary.conjStarAlgAut ℂ B u
    have hproj : IsStarProjection (e (φ 1)) := ((IsStarProjection.one A).map φ).map e
    have hlt : ‖e (φ 1) - 1‖ < 1 := by
      have h1 := hu 1 (Finset.mem_singleton_self 1)
      simp only [e, hψ, Unitary.conjStarAlgAut_apply] at h1 ⊢
      linarith
    exact e.injective ((hproj.eq_one_of_norm_sub_one_lt_one hlt).trans (map_one e).symm)
  exact ⟨aux h.symm, aux h⟩

/-- If `ψ ∘ φ` and `φ ∘ ψ` are approximately unitarily equivalent to the respective identity maps
of unital C⋆-algebras `A` and `B`, then both `φ` and `ψ` are unital. -/
theorem map_one_of_comp_id {ψ : B →⋆ₙₐ[ℂ] A}
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (.id ℂ B)) :
    φ 1 = 1 ∧ ψ 1 = 1 := by
  have h1 : ψ (φ 1) = 1 := hψφ.map_one_eq_one_iff.mpr rfl
  have h2 : φ (ψ 1) = 1 := hφψ.map_one_eq_one_iff.mpr rfl
  refine ⟨?_, ?_⟩
  · calc φ 1 = φ 1 * 1 := (mul_one _).symm
      _ = φ 1 * φ (ψ 1) := by rw [h2]
      _ = φ (ψ 1) := by rw [← map_mul, one_mul]
      _ = 1 := h2
  · calc ψ 1 = ψ 1 * 1 := (mul_one _).symm
      _ = ψ 1 * ψ (φ 1) := by rw [h1]
      _ = ψ (φ 1) := by rw [← map_mul, one_mul]
      _ = 1 := h1

/-- If a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` is approximately unitarily equivalent to `φ` and
`φ ∘ ψ` is approximately unitarily equivalent to `id_B`, then `θ.symm` is approximately unitarily
equivalent to `ψ`. -/
theorem symm_of_comp_id {θ : A ≃⋆ₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hθφ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ)
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (.id ℂ B)) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  have h1 := ((hθφ.precomp ψ).trans hφψ).postcomp θ.symm.toStarAlgHom
  have hlhs : θ.symm.toStarAlgHom.toNonUnitalStarAlgHom.comp (θ.toNonUnitalStarAlgHom.comp ψ) =
      ψ := by
    ext b
    simp
  have hrhs : θ.symm.toStarAlgHom.toNonUnitalStarAlgHom.comp (.id ℂ B) =
      θ.symm.toNonUnitalStarAlgHom := by
    ext b
    simp
  rw [hlhs, hrhs] at h1
  exact h1.symm

end UnitalSource

end ApproximatelyUnitarilyEquivalent

/-- Two `⋆`-homomorphisms `φ, ψ : A →⋆ₙₐ[ℂ] B` into a unital C⋆-algebra are approximately unitarily
equivalent if and only if `ψ` lies in the point-norm closure of the unitary conjugacy orbit of
`φ`. -/
theorem approximatelyUnitarilyEquivalent_iff_mem_closure (φ ψ : A →⋆ₙₐ[ℂ] B) :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ψ ∈ closure (Set.range fun u : unitary B ↦
        (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) := by
  constructor
  · intro h
    rw [mem_closure_iff_nhds_basis ψ.hasBasis_nhds]
    rintro ⟨F, U⟩ hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    obtain ⟨u, hu⟩ := h F ε hε
    refine ⟨(Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ, ⟨u, rfl⟩, fun a ha ↦ ?_⟩
    apply hεU
    simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      Unitary.conjStarAlgAut_apply, dist_eq_norm] using hu a ha
  · refine fun h ↦ closure_minimal ?_ (ApproximatelyUnitarilyEquivalent.isClosed_right φ) h
    rintro _ ⟨u, rfl⟩
    exact .of_unitary u fun a ↦ rfl

end TauCeti
