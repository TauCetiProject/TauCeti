/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
import TauCeti.Analysis.Normed.Module.Multiplier
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Algebra.Module.Span

/-!
# Nondegenerate representations and their extension to multipliers

A representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a possibly nonunital C⋆-algebra on a Hilbert
space is *nondegenerate* when the vectors `π a ξ` span a dense subspace of `H`. Equivalently, no
nonzero vector is annihilated by every `π a`, and `π e ξ → ξ` along any eventually norm-bounded left
approximate unit `e`.

A nondegenerate representation extends uniquely to a unital star-algebra homomorphism
`π' := π.multiplierExtension hπ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)` of the multiplier algebra. It is
characterized by `π' m * π a = π (m * a)`, and it is the strong limit of `π (m * e)` along any
eventually norm-bounded left approximate unit `e`. Its underlying algebra homomorphism is
`ContinuousLinearMap.multiplierExtension`; the centralizer identities imply preservation of star.
This extension is how covariant pairs `(π, U)`
with unitary multipliers `U_s` are obtained from nondegenerate representations of crossed products.

## Main declarations

* `NonUnitalStarAlgHom.IsNondegenerate`: density of the span of the vectors `π a ξ`, unfolded by
  `isNondegenerate_iff_dense`.
* `NonUnitalStarAlgHom.IsNondegenerate.map_one`, `NonUnitalStarAlgHom.isNondegenerate_of_map_one`,
  `NonUnitalStarAlgHom.IsNondegenerate.toStarAlgHom`: a representation of a unital C⋆-algebra is
  nondegenerate exactly when it sends `1` to `1`, and therefore upgrades to a unital
  `⋆`-algebra homomorphism.
* `NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero`: nondegeneracy means that no
  nonzero vector is killed by the whole representation.
* `NonUnitalStarAlgHom.isNondegenerate_iff_tendsto`: nondegeneracy means that the representation
  of an eventually norm-bounded left approximate unit converges strongly to the identity.
* `NonUnitalStarAlgHom.topologicalClosure_span_range_comp_eq`,
  `NonUnitalStarAlgHom.isNondegenerate_iff_dense_span_comp`: nondegeneracy can be checked on any
  dense subset of `A`.
* `NonUnitalStarAlgHom.multiplierExtension`: the extension to the multiplier algebra, with its
  characterizing identities `multiplierExtension_mul_eq_fst` and
  `mul_multiplierExtension_eq_snd`, the uniqueness statement
  `eq_multiplierExtension_of_apply_coe`, and the strong-limit formula
  `tendsto_multiplierExtension_apply`.
* `NonUnitalStarAlgHom.isNondegenerate_of_subsingleton_space`,
  `NonUnitalStarAlgHom.not_isNondegenerate_of_subsingleton_domain`,
  `NonUnitalStarAlgHom.isNondegenerate_conjStarAlgEquiv_comp_iff`: degenerate-carrier edge cases
  and invariance of nondegeneracy under unitary equivalence.

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

/-- A nondegenerate representation of a unital C⋆-algebra sends the identity to the identity
operator. -/
theorem IsNondegenerate.map_one {B : Type*} [CStarAlgebra B] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) : ρ 1 = 1 :=
  hρ.ext fun b => by rw [← map_mul, one_mul, one_mul]

/-- Upgrade a nondegenerate representation of a unital C⋆-algebra to a unital `⋆`-algebra
homomorphism. -/
def IsNondegenerate.toStarAlgHom {B : Type*} [CStarAlgebra B] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) : B →⋆ₐ[ℂ] (H →L[ℂ] H) where
  __ := ρ
  map_one' := hρ.map_one
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, hρ.map_one]

/-- Coercing `hρ.toStarAlgHom` to a function recovers `ρ`. -/
@[simp]
theorem IsNondegenerate.coe_toStarAlgHom {B : Type*} [CStarAlgebra B]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    ⇑hρ.toStarAlgHom = ρ :=
  (rfl)

/-- Coercing `hρ.toStarAlgHom` to a non-unital `⋆`-algebra homomorphism recovers `ρ`. -/
@[simp]
theorem IsNondegenerate.toNonUnitalStarAlgHom_toStarAlgHom {B : Type*} [CStarAlgebra B]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    hρ.toStarAlgHom.toNonUnitalStarAlgHom = ρ :=
  (rfl)

/-- The Banach-module extension, before recording preservation of star. -/
private def extensionAlgHom (hπ : π.IsNondegenerate) : 𝓜(ℂ, A) →ₐ[ℂ] (H →L[ℂ] H) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  let ρ : A →L[ℂ] H →L[ℂ] H := (LinearMap.ofClass π).mkContinuous 1
    (fun a => by simpa only [LinearMap.coe_ofClass, one_mul] using norm_apply_le π a)
  exact ρ.multiplierExtension (map_mul π) hπ hl.eventually_norm hl.tendsto_mul_right

private theorem extensionAlgHom_mul (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    extensionAlgHom hπ m * π a = π (m.fst a) := by
  dsimp only [extensionAlgHom]
  exact ContinuousLinearMap.multiplierExtension_mul_eq_fst ..

private theorem eq_extensionAlgHom (hπ : π.IsNondegenerate) {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H}
    (hT : ∀ a, T * π a = π (m.fst a)) : T = extensionAlgHom hπ m := by
  dsimp only [extensionAlgHom]
  exact (ContinuousLinearMap.eq_multiplierExtension_iff ..).2 hT

private theorem mul_extensionAlgHom (hπ : π.IsNondegenerate) (m : 𝓜(ℂ, A)) (a : A) :
    π a * extensionAlgHom hπ m = π (m.snd a) :=
  hπ.ext fun b => by rw [mul_assoc, extensionAlgHom_mul, ← map_mul, ← map_mul, m.central]

/-- The extension of a nondegenerate representation to the multiplier algebra: the unique
operator `π' m` with `π' m * π a = π (m * a)` for every `a`. -/
def multiplierExtension (hπ : π.IsNondegenerate) : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toAlgHom := extensionAlgHom hπ
  map_star' m := (eq_extensionAlgHom hπ fun a => by
    rw [DoubleCentralizer.star_fst, map_star π, ← mul_extensionAlgHom hπ, star_mul,
      ← map_star π, star_star]
    rfl).symm

variable (hπ : π.IsNondegenerate)

/-- The defining identity `π' m * π a = π (m * a)` of the multiplier extension. -/
@[simp]
theorem multiplierExtension_mul_eq_fst (m : 𝓜(ℂ, A)) (a : A) :
    π.multiplierExtension hπ m * π a = π (m.fst a) :=
  extensionAlgHom_mul hπ m a

/-- The right-handed identity `π a * π' m = π (a * m)` of the multiplier extension. -/
@[simp]
theorem mul_multiplierExtension_eq_snd (m : 𝓜(ℂ, A)) (a : A) :
    π a * π.multiplierExtension hπ m = π (m.snd a) :=
  mul_extensionAlgHom hπ m a

/-- The multiplier extension sends `π a ξ` to `π (m * a) ξ`. -/
@[simp]
theorem multiplierExtension_apply_apply (m : 𝓜(ℂ, A)) (a : A) (ξ : H) :
    π.multiplierExtension hπ m (π a ξ) = π (m.fst a) ξ :=
  congr($(multiplierExtension_mul_eq_fst hπ m a) ξ)

/-- An operator equals `π' m` exactly when it satisfies the defining identity. -/
theorem eq_multiplierExtension_iff {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H} :
    T = π.multiplierExtension hπ m ↔ ∀ a, T * π a = π (m.fst a) :=
  ⟨fun h a => h ▸ multiplierExtension_mul_eq_fst hπ m a, eq_extensionAlgHom hπ⟩

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

/-- Along any eventually norm-bounded net `e` with `e * a → a` for all `a : A`, the operators
`π (m * e)` converge strongly to the multiplier extension `π' m`. -/
theorem tendsto_multiplierExtension_apply {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (m : 𝓜(ℂ, A)) (ξ : H) :
    Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (π.multiplierExtension hπ m ξ)) := by
  obtain ⟨T, hT, hlim⟩ := m.exists_clm_tendsto_fst (K := 1) (L := ⇑π) hC hl
    (fun _ => by fun_prop) (map_mul π)
    (fun a => by simpa only [one_mul] using norm_apply_le π a) hπ
  rw [← (eq_multiplierExtension_iff hπ).2 hT]
  exact hlim ξ

/-- Strict continuity of a norm-bounded family of multipliers gives strong continuity of its image
under the multiplier extension: if `x ↦ u x * a` is norm continuous for every `a` and
`‖u x‖ ≤ C`, then `x ↦ π' (u x) ξ` is continuous for every vector `ξ`. Only the left half of
strict continuity is needed. This applies to strictly continuous unitary multiplier groups. -/
theorem continuous_multiplierExtension_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C) (ξ : H) : Continuous fun x => π.multiplierExtension hπ (u x) ξ := by
  refine ContinuousLinearMap.continuous_apply_of_dense_span
    (f := fun x => π.multiplierExtension hπ (u x)) hπ
    (fun x => (norm_apply_le (π.multiplierExtension hπ).toNonUnitalStarAlgHom _).trans (hC x))
    (fun _ hx => ?_) ξ
  obtain ⟨a, η, rfl⟩ := Set.mem_iUnion.1 hx
  simp only [multiplierExtension_apply_apply]
  fun_prop

/-- Along any eventually norm-bounded net `e` with `e * a → a` for all `a : A`, a representation is
nondegenerate exactly when `π e` converges strongly to the identity. -/
theorem isNondegenerate_iff_tendsto {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    π.IsNondegenerate ↔ ∀ ξ, Tendsto (fun e => π e ξ) l (𝓝 ξ) :=
  ⟨fun hπ ξ => by simpa using tendsto_multiplierExtension_apply hπ hC hl 1 ξ,
    fun h ξ => mem_closure_of_tendsto (h ξ) <| .of_forall fun e =>
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, ξ, rfl⟩⟩

/-- A representation is nondegenerate exactly when no nonzero vector is annihilated by every
operator of the representation. -/
theorem isNondegenerate_iff_forall_apply_eq_zero :
    π.IsNondegenerate ↔ ∀ ξ, (∀ a, π a ξ = 0) → ξ = 0 := by
  refine ⟨fun hπ ξ h => ?_, fun h => ?_⟩
  · let := CStarAlgebra.spectralOrder A
    have := CStarAlgebra.spectralOrderedRing A
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    exact tendsto_nhds_unique
      ((isNondegenerate_iff_tendsto hl.eventually_norm hl.tendsto_mul_right).1 hπ ξ) (by simp [h])
  · rw [IsNondegenerate, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    refine fun ξ hξ => h ξ fun a => ext_inner_left ℂ fun v => ?_
    rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ <|
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨star a, v, rfl⟩

/-- Restricting a Hilbert-space representation of `A` to a dense subset `Set.range g` generates the
same closed essential subspace of `H`. -/
theorem topologicalClosure_span_range_comp_eq {ι : Type*} {g : ι → A} (hg : DenseRange g)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (Submodule.span ℂ (⋃ i, Set.range (π (g i)))).topologicalClosure =
      (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure :=
  hg.topologicalClosure_span_iUnion_range_comp_eq (R := ℂ) (L := fun a => ⇑(π a)) fun _ =>
    by fun_prop

/-- For any `g : ι → A` with dense range, `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate if and only
if the vectors `π (g i) ξ` span a dense subspace of `H`. -/
theorem isNondegenerate_iff_dense_span_comp {ι : Type*} {g : ι → A} (hg : DenseRange g) :
    π.IsNondegenerate ↔ Dense (Submodule.span ℂ (⋃ i, Set.range (π (g i))) : Set H) := by
  simp_rw [isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    topologicalClosure_span_range_comp_eq hg]

/-- Every representation on a zero Hilbert space is nondegenerate. -/
@[simp]
theorem isNondegenerate_of_subsingleton_space [Subsingleton H] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    π.IsNondegenerate :=
  isNondegenerate_iff_forall_apply_eq_zero.2 fun ξ _ => Subsingleton.elim ξ 0

/-- No representation of a zero C⋆-algebra on a nontrivial Hilbert space is nondegenerate. -/
@[simp]
theorem not_isNondegenerate_of_subsingleton_domain [Subsingleton A] [Nontrivial H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : ¬ π.IsNondegenerate := by
  intro hπ
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H)
  exact hξ <| (isNondegenerate_iff_forall_apply_eq_zero.1 hπ) ξ fun a => by
    rw [Subsingleton.elim a 0, map_zero, _root_.zero_apply]

/-- Conjugating a representation by a linear isometric equivalence preserves nondegeneracy. -/
@[simp]
theorem isNondegenerate_conjStarAlgEquiv_comp_iff {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] K) :
    (U.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp π).IsNondegenerate ↔ π.IsNondegenerate := by
  simp only [isNondegenerate_iff_forall_apply_eq_zero, comp_apply,
    StarAlgEquiv.toNonUnitalStarAlgHom_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    map_eq_zero_iff U U.injective]
  refine ⟨fun h ξ hξ => U.injective ?_, fun h η hη => U.symm.injective ?_⟩
  · simpa only [map_zero] using h (U ξ) fun a => by simpa only [U.symm_apply_apply] using hξ a
  · simpa only [map_zero] using h (U.symm η) hη

/-- Precomposing a representation with a star homomorphism of dense range preserves and reflects
nondegeneracy. -/
theorem isNondegenerate_comp_iff {B : Type*} [NonUnitalCStarAlgebra B] {φ : B →⋆ₙₐ[ℂ] A}
    (hφ : DenseRange φ) : (π.comp φ).IsNondegenerate ↔ π.IsNondegenerate := by
  rw [isNondegenerate_iff_dense_span_comp hφ, isNondegenerate_iff_dense]
  simp only [comp_apply]

end NonUnitalStarAlgHom
