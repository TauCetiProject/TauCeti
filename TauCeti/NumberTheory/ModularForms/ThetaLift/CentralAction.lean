/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RepresentationTheory.Continuous.Unitary.Reducing

/-!
# Central actions and denominators on a line

A finite unitary group action has an orthogonal projection onto its invariant vectors, given by
averaging. An equivariant kernel family has an invariant sum. Operators commuting with the action
have a stable common kernel and stable orthogonal complement.

For a clearing endomorphism of a line, scalarity identifies its determinant with its action. This
turns the denominator pairing hypothesis into a bound on a product of two line projections.
Pairing against the unnormalized orbit sum `∑ g : G, T g x` of translates recovers the projection
pairing scaled by `|G|`, introducing the reciprocal norm `‖place (|G|)‖⁻¹`; at a complex p-adic
place this equals `p ^ padicValNat p |G|`.

The pairing hypotheses below are the precise integrality inputs. Coordinate integrality and
orthogonality to false lifts belong to the applications that establish those hypotheses.

## Main results

* `TauCeti.ThetaLift.averageMap_inner_left` and `TauCeti.ThetaLift.starProjection_averageMap`.
* `TauCeti.ThetaLift.inner_starProjection_line` and
  `TauCeti.ThetaLift.det_smul_id_of_span_singleton`.
* `TauCeti.ThetaLift.norm_inner_starProjection_span_singleton_le_exp`, the direct denominator
  bound.
* `TauCeti.ThetaLift.norm_inner_starProjection_centralAverage_le_exp`, the orbit-sum bound with
  reciprocal cardinality factor `‖place (Fintype.card G : ℂ)‖⁻¹`.
* `TauCeti.ThetaLift.norm_inner_starProjection_centralAverage_le_exp_padic`, its explicit p-adic
  form `Real.exp β * (p : ℝ) ^ padicValNat p (Fintype.card G)`.

## References

The statements and argument follow [ShortProof](https://github.com/lsernau/grh-lean),
`lsernau/grh-lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207`, file
`grh/src/New/OneLift/HeckeValues/CentralAction.lean`. The abstract formulation here makes the
integral-pairing and invariance hypotheses explicit. The proofs are independent.
-/

public noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace TauCeti.ThetaLift

variable {G E : Type*} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A unitary group action has its inverse as its inner-product adjoint. -/
theorem inner_apply_eq_inner_inv_apply (T : G →* E →ₗᵢ[ℂ] E) (z : G) (x y : E) :
    ⟪x, T z y⟫_ℂ = ⟪T z⁻¹ x, y⟫_ℂ := by
  have hzx : T z (T z⁻¹ x) = x := by
    calc
      T z (T z⁻¹ x) = (T z * T z⁻¹) x := rfl
      _ = T (z * z⁻¹) x := by rw [map_mul]
      _ = x := by simp
  calc
    ⟪x, T z y⟫_ℂ = ⟪T z (T z⁻¹ x), T z y⟫_ℂ := by rw [hzx]
    _ = ⟪T z⁻¹ x, y⟫_ℂ := (T z).inner_map_map _ _

/-- The sum of an equivariant kernel family is fixed by every action operator. -/
theorem apply_kernelSum [Fintype G] (T : G →* E →ₗᵢ[ℂ] E) (K : G → E)
    (hK : ∀ z g, T z⁻¹ (K g) = K (g * z)) (z : G) :
    T z (∑ g, K g) = ∑ g, K g := by
  classical
  have hK' (g : G) : T z (K g) = K (g * z⁻¹) := by simpa using hK z⁻¹ g
  calc
    T z (∑ g, K g) = ∑ g, T z (K g) := by simp
    _ = ∑ g, K (g * z⁻¹) := by simp [hK']
    _ = ∑ g, K g := Equiv.sum_comp (Equiv.mulRight z⁻¹) K

/-- Averaging preserves the pairing with an invariant vector. -/
theorem averageMap_inner_left [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {π : ContRepresentation ℂ G E} (hπ : π.IsUnitary) {φ : E} (hφ : φ ∈ π.invariants)
    (x : E) : ⟪π.toRepresentation.averageMap x, φ⟫_ℂ = ⟪x, φ⟫_ℂ := by
  have := hπ.hasOrthogonalProjection_invariants
  rw [← hπ.starProjection_invariants_apply, π.invariants.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hφ]

/-- The common kernel of an indexed family of endomorphisms. -/
def falseLiftCommonKernel {𝕜 F ι : Type*} [Semiring 𝕜] [AddCommMonoid F] [Module 𝕜 F]
    (A : ι → Module.End 𝕜 F) : Submodule 𝕜 F :=
  ⨅ i, LinearMap.ker (A i)

@[simp]
theorem mem_falseLiftCommonKernel {𝕜 F ι : Type*} [Semiring 𝕜] [AddCommMonoid F] [Module 𝕜 F]
    {A : ι → Module.End 𝕜 F} {x : F} :
    x ∈ falseLiftCommonKernel A ↔ ∀ i, A i x = 0 := by
  simp [falseLiftCommonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- A linear map commuting with a family preserves its common kernel. -/
theorem map_falseLiftCommonKernel_le {𝕜 F ι : Type*} [Semiring 𝕜] [AddCommMonoid F] [Module 𝕜 F]
    (A : ι → Module.End 𝕜 F) (U : Module.End 𝕜 F)
    (hcomm : ∀ i x, U (A i x) = A i (U x)) :
    (falseLiftCommonKernel A).map U ≤ falseLiftCommonKernel A := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ∀ i, A i x = 0 := mem_falseLiftCommonKernel.mp hx
  rw [mem_falseLiftCommonKernel]
  intro i
  rw [← hcomm i x, hx' i, map_zero]

/-- An action operator preserves the common kernel of operators commuting with it. -/
theorem representation_apply_mem_falseLiftCommonKernel {ι : Type*}
    (T : G →* E →ₗᵢ[ℂ] E) (A : ι → Module.End ℂ E) (z : G)
    (hcomm : ∀ i x, T z (A i x) = A i (T z x)) {x : E}
    (hx : x ∈ falseLiftCommonKernel A) : T z x ∈ falseLiftCommonKernel A :=
  map_falseLiftCommonKernel_le A (T z).toLinearMap hcomm ⟨x, hx, rfl⟩

/-- A unitary action preserves the orthogonal complement of a commuting family's common kernel. -/
theorem representation_apply_mem_orthogonal_falseLiftCommonKernel {ι : Type*}
    (T : G →* E →ₗᵢ[ℂ] E) (A : ι → Module.End ℂ E) (z : G)
    (hcomm : ∀ i x, T z⁻¹ (A i x) = A i (T z⁻¹ x)) {x : E}
    (hx : x ∈ (falseLiftCommonKernel A)ᗮ) : T z x ∈ (falseLiftCommonKernel A)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro w hw
  rw [inner_apply_eq_inner_inv_apply]
  exact hx (T z⁻¹ w) (representation_apply_mem_falseLiftCommonKernel T A z⁻¹ hcomm hw)

/-- The pairing of two orthogonal projections onto the line spanned by a vector. -/
theorem inner_starProjection_line (φ x y : E) :
    ⟪(Submodule.span ℂ {φ}).starProjection x,
      (Submodule.span ℂ {φ}).starProjection y⟫_ℂ =
        ⟪x, φ⟫_ℂ * ⟪φ, y⟫_ℂ / ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hφ : φ = 0
  · subst φ
    simp
  have hproj (w : E) : (ℂ ∙ φ).starProjection w =
      (⟪φ, w⟫_ℂ / ((‖φ‖ ^ 2 : ℝ) : ℂ)) • φ := Submodule.starProjection_singleton ℂ w
  rw [hproj, hproj]
  simp only [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
    map_div₀, Complex.conj_ofReal, inner_conj_symm]
  have hnorm : ((‖φ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hφ)
  field_simp
  rw [Complex.ofReal_pow]
  ac_rfl

/-- An endomorphism of the line spanned by a vector acts by its determinant. -/
theorem det_smul_id_of_span_singleton {𝕜 F : Type*} [Field 𝕜] [AddCommGroup F] [Module 𝕜 F]
    (φ : F) (Λ : Module.End 𝕜 (Submodule.span 𝕜 {φ})) :
    Λ = LinearMap.det Λ • LinearMap.id := by
  by_cases hφ : φ = 0
  · subst φ
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    simp only [Submodule.span_zero_singleton, Submodule.mem_bot] at hx
    subst x
    have hz : (⟨0, hx⟩ : 𝕜 ∙ (0 : F)) = 0 := by ext; rfl
    rw [hz]
    simp
  exact LinearMap.ext (LinearMap.apply_eq_det_smul_of_finrank_eq_one
    (finrank_span_singleton hφ) Λ)

/-- A determinant lower bound and a unit product estimate give an exponential upper bound. -/
theorem norm_le_exp_of_exp_neg_le_norm {k : Type*} [NormedField k]
    (place : ℂ →+* k) (β : ℝ) (d a : ℂ)
    (hd : Real.exp (-β) ≤ ‖place d‖) (hda : ‖place (d * a)‖ ≤ 1) :
    ‖place a‖ ≤ Real.exp β := by
  rw [map_mul, norm_mul] at hda
  have hle : (Real.exp β)⁻¹ * ‖place a‖ ≤ 1 := by
    calc
      (Real.exp β)⁻¹ * ‖place a‖ ≤ ‖place d‖ * ‖place a‖ :=
        mul_le_mul_of_nonneg_right (by simpa [Real.exp_neg] using hd) (norm_nonneg _)
      _ ≤ 1 := hda
  rwa [inv_mul_le_iff₀ (Real.exp_pos β), mul_one] at hle

/-- Direct denominator bound on a projecting subspace, given scalarity of the clearing map. -/
theorem norm_inner_starProjection_le_exp (Z : Submodule ℂ E) [Z.HasOrthogonalProjection]
    {k : Type*} [NormedField k] (place : ℂ →+* k) (Λ : Module.End ℂ Z) (β : ℝ)
    (x y : E) (hdet : Real.exp (-β) ≤ ‖place (LinearMap.det Λ)‖)
    (hscalar : ((Λ (Z.orthogonalProjectionOnto y) : Z) : E) =
      LinearMap.det Λ • Z.starProjection y)
    (hpair : ‖place (inner ℂ x ((Λ (Z.orthogonalProjectionOnto y) : Z) : E))‖ ≤ 1) :
    ‖place (inner ℂ (Z.starProjection x) (Z.starProjection y))‖ ≤ Real.exp β := by
  apply norm_le_exp_of_exp_neg_le_norm place β (LinearMap.det Λ)
    (inner ℂ (Z.starProjection x) (Z.starProjection y)) hdet
  have hbridge : LinearMap.det Λ * inner ℂ (Z.starProjection x) (Z.starProjection y) =
      inner ℂ x ((Λ (Z.orthogonalProjectionOnto y) : Z) : E) := by
    rw [hscalar, inner_smul_right, Z.inner_starProjection_left_eq_right,
      Z.starProjection_eq_self_iff.mpr (Z.starProjection_apply_mem y)]
  rwa [hbridge]

/-- The direct denominator bound for the line of a vector. -/
theorem norm_inner_starProjection_span_singleton_le_exp {k : Type*} [NormedField k]
    (place : ℂ →+* k) (φ : E) (Λ : Module.End ℂ (ℂ ∙ φ))
    (β : ℝ) (x y : E) (hdet : Real.exp (-β) ≤ ‖place (LinearMap.det Λ)‖)
    (hpair : ‖place (inner ℂ x
      ((Λ ((ℂ ∙ φ).orthogonalProjectionOnto y) : ℂ ∙ φ) : E))‖ ≤ 1) :
    ‖place (inner ℂ ((ℂ ∙ φ).starProjection x) ((ℂ ∙ φ).starProjection y))‖ ≤
      Real.exp β := by
  by_cases hφ : φ = 0
  · subst φ
    simpa using Real.exp_nonneg β
  apply norm_inner_starProjection_le_exp (ℂ ∙ φ) place Λ β x y hdet _ hpair
  have h := LinearMap.congr_fun (det_smul_id_of_span_singleton φ Λ)
    ((ℂ ∙ φ).orthogonalProjectionOnto y)
  exact congrArg Subtype.val h

/-- Projecting to a line spanned by an invariant vector absorbs the average. -/
theorem starProjection_averageMap [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {π : ContRepresentation ℂ G E} (hπ : π.IsUnitary) {φ : E} (hφ : φ ∈ π.invariants)
    (y : E) :
    (ℂ ∙ φ).starProjection (π.toRepresentation.averageMap y) = (ℂ ∙ φ).starProjection y := by
  have hinner : ⟪φ, π.toRepresentation.averageMap y⟫_ℂ = ⟪φ, y⟫_ℂ := by
    rw [← inner_conj_symm, averageMap_inner_left hπ hφ, inner_conj_symm]
  rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton, hinner]

/-- Pairing the unnormalized `G`-orbit sum of `x` with an element of an invariant line scales the
projection pairing by `Fintype.card G`. -/
theorem inner_sum_orbit_starProjection [Fintype G] (T : G →* E →ₗᵢ[ℂ] E)
    {φ : E} (hφ : ∀ z, T z φ = φ) (x y : E) :
    ⟪∑ g : G, T g x, (ℂ ∙ φ).starProjection y⟫_ℂ =
      (Fintype.card G : ℂ) * ⟪(ℂ ∙ φ).starProjection x, (ℂ ∙ φ).starProjection y⟫_ℂ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hcard
  let π : ContRepresentation ℂ G E := .ofMonoidHom
    { toFun := fun g ↦ (T g).toContinuousLinearMap
      map_one' := by rw [T.map_one]; rfl
      map_mul' := fun g h ↦ by rw [T.map_mul]; rfl }
  have hπ : π.IsUnitary :=
    (ContRepresentation.isUnitary_iff_isometry π).2 fun g ↦ (T g).isometry
  have hφ' : φ ∈ π.invariants := fun g ↦ hφ g
  have horbit : ∑ g : G, T g x = (Fintype.card G : ℂ) • π.toRepresentation.averageMap x := by
    rw [Representation.averageMap_apply, invOf_eq_inv, smul_inv_smul₀ hcard]
    rfl
  rw [horbit, inner_smul_left, map_natCast,
    ← (ℂ ∙ φ).inner_starProjection_left_eq_right, starProjection_averageMap hπ hφ' x,
    (ℂ ∙ φ).inner_starProjection_left_eq_right, (ℂ ∙ φ).inner_starProjection_left_eq_right,
    (ℂ ∙ φ).starProjection_eq_self_iff.mpr ((ℂ ∙ φ).starProjection_apply_mem y)]

/-- The central-action denominator bound on an invariant line: a single integral pairing against
the `G`-orbit sum `∑ g, T g x` bounds `‖place ⟪pr x, pr y⟫‖` by
`Real.exp β * ‖place (Fintype.card G : ℂ)‖⁻¹`. -/
theorem norm_inner_starProjection_centralAverage_le_exp [Fintype G]
    {k : Type*} [NormedField k] [CharZero k] (place : ℂ →+* k)
    (T : G →* E →ₗᵢ[ℂ] E) (φ : E) (hφ : ∀ z, T z φ = φ)
    (Λ : Module.End ℂ (ℂ ∙ φ)) (β : ℝ) (x y : E)
    (hdet : Real.exp (-β) ≤ ‖place (LinearMap.det Λ)‖)
    (hpair : ‖place (inner ℂ (∑ g : G, T g x)
      ((Λ ((ℂ ∙ φ).orthogonalProjectionOnto y) : ℂ ∙ φ) : E))‖ ≤ 1) :
    ‖place (inner ℂ ((ℂ ∙ φ).starProjection x) ((ℂ ∙ φ).starProjection y))‖ ≤
      Real.exp β * ‖place (Fintype.card G : ℂ)‖⁻¹ := by
  have hdirect :
      ‖place (inner ℂ ((ℂ ∙ φ).starProjection (∑ g : G, T g x))
        ((ℂ ∙ φ).starProjection y))‖ ≤ Real.exp β :=
    norm_inner_starProjection_span_singleton_le_exp place φ Λ β (∑ g : G, T g x) y hdet hpair
  have hscale :
      inner ℂ ((ℂ ∙ φ).starProjection (∑ g : G, T g x)) ((ℂ ∙ φ).starProjection y) =
        (Fintype.card G : ℂ) *
          inner ℂ ((ℂ ∙ φ).starProjection x) ((ℂ ∙ φ).starProjection y) := by
    rw [(ℂ ∙ φ).inner_starProjection_left_eq_right,
      (ℂ ∙ φ).starProjection_eq_self_iff.mpr ((ℂ ∙ φ).starProjection_apply_mem y),
      inner_sum_orbit_starProjection T hφ x y]
  rw [hscale, map_mul, norm_mul] at hdirect
  have hcard_pos : 0 < ‖place (Fintype.card G : ℂ)‖ := by
    rw [norm_pos_iff, map_natCast]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_comm (Real.exp β)]
  exact (le_inv_mul_iff₀ hcard_pos).mpr hdirect

/-- The norm of a nonzero natural number in a complex p-adic field. -/
theorem norm_padicComplex_natCast {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    ‖(n : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have hnorm := PadicComplex.norm_extends' p (n : ℚ_[p])
  simp only [map_natCast, PadicComplex.coe_natCast] at hnorm
  rw [hnorm, Padic.norm_natCast_eq_zpow hn]

/-- The reciprocal norm of a nonzero natural number in a complex p-adic field. -/
theorem norm_padicComplex_natCast_inv {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    ‖(n : ℂ_[p])‖⁻¹ = (p : ℝ) ^ padicValNat p n := by
  rw [norm_padicComplex_natCast hn, ← zpow_natCast, ← inv_zpow]
  simp

/-- The central-action denominator bound with the explicit p-adic cardinality factor. -/
theorem norm_inner_starProjection_centralAverage_le_exp_padic [Fintype G]
    {p : ℕ} [Fact p.Prime] (place : ℂ →+* ℂ_[p]) (T : G →* E →ₗᵢ[ℂ] E)
    (φ : E) (hφ : ∀ z, T z φ = φ)
    (Λ : Module.End ℂ (ℂ ∙ φ)) (β : ℝ) (x y : E)
    (hdet : Real.exp (-β) ≤ ‖place (LinearMap.det Λ)‖)
    (hpair : ‖place (inner ℂ (∑ g : G, T g x)
      ((Λ ((ℂ ∙ φ).orthogonalProjectionOnto y) : ℂ ∙ φ) : E))‖ ≤ 1) :
    ‖place (inner ℂ ((ℂ ∙ φ).starProjection x) ((ℂ ∙ φ).starProjection y))‖ ≤
      Real.exp β * (p : ℝ) ^ padicValNat p (Fintype.card G) := by
  simpa only [map_natCast, norm_padicComplex_natCast_inv (p := p) Fintype.card_ne_zero] using
    norm_inner_starProjection_centralAverage_le_exp place T φ hφ Λ β x y hdet hpair

end TauCeti.ThetaLift
