/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Representation.GNS
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Intertwiner
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.PeakFunction

/-!
# Multiplier-valued covariant homomorphisms and their integrated forms

A *covariant multiplier homomorphism* of a C⋆-dynamical system `(A, G, α)` into a possibly
nonunital C⋆-algebra `B` consists of `π : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` and `u : G →* unitary 𝓜(ℂ, B)` with
norm-continuous left orbits `r ↦ u_r b` and covariance `u_r π(a) = π(α_r(a)) u_r`. On a
topological group, strict right continuity `r ↦ b u_r` follows by taking adjoints.

Composing `(π, u)` with the multiplier extension of a nondegenerate Hilbert-space representation of
`B` yields a `CovariantRepresentation`, and composing with the multiplier extension of a
nondegenerate `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` pushes `(π, u)` forward to `C`.

For a measure `μ` finite on compact sets, every `f : C_c(G, A)` integrates strictly to a multiplier
`CovariantMultiplierHom.integratedMultiplier` acting by `b ↦ ∫ r, (π(f r) u_r).fst b ∂μ` and
`b ↦ ∫ r, (π(f r) u_r).snd b ∂μ`. Every nondegenerate representation of `B` sends this multiplier
to the vector-valued integrated operator of the induced covariant representation, so
`DoubleCentralizer.eq_iff_forall_multiplierExtension_eq` transfers multiplicativity under twisted
convolution, preservation of the twisted involution, functoriality, and uniqueness of nondegenerate
covariant multiplier homomorphisms (`eq_of_integratedMultiplier_eq`) from the Hilbert-space theory.
Peak-function approximation shows that the integrated multipliers generate the same closed essential
subspace of `B` as `π` (`topologicalClosure_span_integratedMultiplier`,
`dense_span_integratedMultiplier_iff`).

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.39, Proposition 2.40, and
  Section 2.6 (Theorem 2.61).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

section Basic

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- A covariant homomorphism from a C⋆-dynamical system `(A, G, α)` into the multiplier algebra of
a possibly nonunital C⋆-algebra `B`. Coefficient nondegeneracy is not built into the structure so
that integrated forms and nondegeneracy equivalences apply uniformly. -/
structure CovariantMultiplierHom (α : CStarAction G A) (B : Type*)
    [NonUnitalCStarAlgebra B] where
  /-- The coefficient ⋆-homomorphism into `𝓜(ℂ, B)`. -/
  coefficient : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)
  /-- The group homomorphism into the unitary group of `𝓜(ℂ, B)`. -/
  group : G →* unitary 𝓜(ℂ, B)
  /-- Strict left continuity of the group homomorphism: `r ↦ u_r b` is norm continuous. -/
  continuous_group_fst (b : B) : Continuous fun r => (group r : 𝓜(ℂ, B)).fst b
  /-- Covariance of the coefficient and group multiplier maps. -/
  covariance (r : G) (a : A) :
    (group r : 𝓜(ℂ, B)) * coefficient a = coefficient (α r a) * group r

namespace CovariantMultiplierHom

variable {α : CStarAction G A}

/-- The coefficient and group homomorphisms determine a covariant multiplier homomorphism. -/
@[ext]
theorem ext {M N : CovariantMultiplierHom α B}
    (hπ : M.coefficient = N.coefficient) (hu : M.group = N.group) : M = N := by
  rcases M, N, hπ, hu with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl⟩
  rfl

/-- Covariance as an equality in `𝓜(ℂ, B)`. -/
@[simp]
theorem group_mul_coefficient (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    (M.group r : 𝓜(ℂ, B)) * M.coefficient a = M.coefficient (α r a) * M.group r :=
  M.covariance r a

/-- Moving a group multiplier to the left of a coefficient twists by the inverse group element. -/
theorem coefficient_mul_group (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    M.coefficient a * (M.group r : 𝓜(ℂ, B)) = (M.group r : 𝓜(ℂ, B)) * M.coefficient (α r⁻¹ a) := by
  simp

/-- Conjugation by `M.group r` implements the action `α r` on coefficients. -/
theorem coefficient_action (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    M.coefficient (α r a) = (M.group r : 𝓜(ℂ, B)) * M.coefficient a * (M.group r⁻¹ : 𝓜(ℂ, B)) := by
  rw [M.group_mul_coefficient, mul_assoc, ← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one,
    OneMemClass.coe_one, mul_one]

/-- Every unitary multiplier in the image of `M.group` has norm at most `1`, without assuming `B`
nontrivial. -/
theorem norm_group_le_one (M : CovariantMultiplierHom α B) (r : G) :
    ‖(M.group r : 𝓜(ℂ, B))‖ ≤ 1 := by
  by_cases h : Nontrivial 𝓜(ℂ, B)
  · exact (CStarRing.norm_coe_unitary (M.group r)).le
  · have := not_nontrivial_iff_subsingleton.1 h
    simp [Subsingleton.elim (M.group r : 𝓜(ℂ, B)) 0]

/-- On a topological group, `M.group` is strictly continuous on the right:
`r ↦ (M.group r : 𝓜(ℂ, B)).snd b` is norm continuous for every `b : B`. -/
theorem continuous_group_snd [IsTopologicalGroup G] (M : CovariantMultiplierHom α B) (b : B) :
    Continuous fun r => (M.group r : 𝓜(ℂ, B)).snd b := by
  -- Deduce right strict continuity from left strict continuity via adjoints and group inversion.
  have heq (r : G) :
      (M.group r : 𝓜(ℂ, B)).snd b = star ((M.group r⁻¹ : 𝓜(ℂ, B)).fst (star b)) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, DoubleCentralizer.star_fst, star_star,
      star_star]
  simp_rw [heq]
  exact ((M.continuous_group_fst (star b)).comp continuous_inv).star

/-- Compose a covariant multiplier homomorphism into `𝓜(ℂ, B)` with the multiplier extension of a
nondegenerate Hilbert-space representation of `B` to obtain a `CovariantRepresentation`. -/
def toCovariantRepresentation (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) : CovariantRepresentation α H where
  coefficient := (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp M.coefficient
  group := .ofMonoidHom
    (((ρ.multiplierExtension hρ : 𝓜(ℂ, B) →* (H →L[ℂ] H)).comp
      (Submonoid.subtype (unitary 𝓜(ℂ, B)))).comp M.group)
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r =>
    Unitary.map_mem (ρ.multiplierExtension hρ) (M.group r).prop
  continuous_orbit v :=
    ρ.continuous_multiplierExtension_apply hρ M.continuous_group_fst M.norm_group_le_one v
  covariance r a v := by
    have hcov := congr($(congrArg (ρ.multiplierExtension hρ) (M.covariance r a)) v)
    rwa [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp] at hcov

@[simp]
theorem toCovariantRepresentation_coefficient (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (M.toCovariantRepresentation hρ).coefficient =
      (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp M.coefficient := (rfl)

@[simp]
theorem toCovariantRepresentation_group_apply (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) (r : G) :
    (M.toCovariantRepresentation hρ).group r = ρ.multiplierExtension hρ (M.group r) := (rfl)

/-- Push a covariant multiplier homomorphism into `𝓜(ℂ, B)` forward along a nondegenerate
multiplier homomorphism `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)`. -/
def map (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) : CovariantMultiplierHom α C where
  coefficient := (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp M.coefficient
  group := (Unitary.map (StarMonoidHom.ofClass (ψ.extendToMultiplier hψ))).toMonoidHom.comp M.group
  continuous_group_fst c :=
    ψ.continuous_extendToMultiplier_fst_apply hψ M.continuous_group_fst M.norm_group_le_one c
  covariance r a := by
    have hcov := congrArg (ψ.extendToMultiplier hψ) (M.covariance r a)
    rwa [map_mul, map_mul] at hcov

@[simp]
theorem map_coefficient (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) :
    (M.map hψ).coefficient =
      (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp M.coefficient := (rfl)

@[simp]
theorem coe_map_group (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (r : G) :
    ((M.map hψ).group r : 𝓜(ℂ, C)) = ψ.extendToMultiplier hψ (M.group r) := (rfl)

/-- Pushing forward along the canonical inclusion `B →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` recovers `M`. -/
@[simp]
theorem map_coeHom (M : CovariantMultiplierHom α B)
    (h : (DoubleCentralizer.coeHom (𝕜 := ℂ) : B →⋆ₙₐ[ℂ] 𝓜(ℂ, B)).IsMultiplierNondegenerate) :
    M.map h = M :=
  ext (NonUnitalStarAlgHom.ext fun _ => by simp) (MonoidHom.ext fun _ => Subtype.ext <| by simp)

/-- Successive pushforwards agree with pushforward along the composite multiplier homomorphism. -/
@[simp]
theorem map_map {D : Type*} [NonUnitalCStarAlgebra D] (M : CovariantMultiplierHom α B)
    {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hψ : ψ.IsMultiplierNondegenerate)
    {θ : C →⋆ₙₐ[ℂ] 𝓜(ℂ, D)} (hθ : θ.IsMultiplierNondegenerate) :
    (M.map hψ).map hθ = M.map (hθ.extendToMultiplier_comp hψ) :=
  ext
    (NonUnitalStarAlgHom.ext fun a => DFunLike.congr_fun
      (NonUnitalStarAlgHom.extendToMultiplier_comp hθ hψ).symm (M.coefficient a))
    (MonoidHom.ext fun r => Subtype.ext <| DFunLike.congr_fun
      (NonUnitalStarAlgHom.extendToMultiplier_comp hθ hψ).symm (M.group r : 𝓜(ℂ, B)))

/-- Pushing forward along `ψ` and then applying a nondegenerate representation `π` of `C` agrees
with applying the composite nondegenerate representation `(π.multiplierExtension hπ) ∘ ψ`. -/
@[simp]
theorem toCovariantRepresentation_map (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) :
    (M.map hψ).toCovariantRepresentation hπ =
      M.toCovariantRepresentation (hπ.multiplierExtension_comp hψ) :=
  CovariantRepresentation.ext
    (NonUnitalStarAlgHom.ext fun a => DFunLike.congr_fun
      (NonUnitalStarAlgHom.multiplierExtension_comp hπ hψ).symm
      (M.coefficient a))
    (DFunLike.ext _ _ fun r => DFunLike.congr_fun
      (NonUnitalStarAlgHom.multiplierExtension_comp hπ hψ).symm
      (M.group r : 𝓜(ℂ, B)))

/-- Pull back a covariant multiplier homomorphism along an equivariant coefficient map. -/
def comap {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) : CovariantMultiplierHom α' B where
  coefficient := M.coefficient.comp φ.toNonUnitalStarAlgHom
  group := M.group
  continuous_group_fst := M.continuous_group_fst
  covariance r a := by
    simpa only [NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom, φ.map_action]
      using M.covariance r (φ a)

@[simp]
theorem comap_coefficient {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) :
    (M.comap φ).coefficient = M.coefficient.comp φ.toNonUnitalStarAlgHom := (rfl)

@[simp]
theorem comap_group {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) : (M.comap φ).group = M.group := (rfl)

/-- Pullback along the identity equivariant homomorphism recovers `M`. -/
@[simp]
theorem comap_id (M : CovariantMultiplierHom α B) : M.comap (Hom.id α) = M :=
  ext (NonUnitalStarAlgHom.ext fun _ => by simp) rfl

/-- Successive pullbacks agree with pullback along the composite equivariant homomorphism. -/
@[simp]
theorem comap_comp {A' A'' : Type*} [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra A'']
    {α' : CStarAction G A'} {α'' : CStarAction G A''}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) (θ : Hom α'' α') :
    (M.comap φ).comap θ = M.comap (φ.comp θ) :=
  ext (NonUnitalStarAlgHom.ext fun _ => by simp) rfl

/-- Pushforward along a nondegenerate multiplier homomorphism commutes with pullback along an
equivariant coefficient homomorphism. -/
theorem map_comap {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) :
    (M.comap φ).map hψ = (M.map hψ).comap φ :=
  ext rfl rfl

@[simp]
theorem toCovariantRepresentation_comap {A' : Type*} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (M : CovariantMultiplierHom α B) (φ : Hom α' α) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (M.comap φ).toCovariantRepresentation hρ = (M.toCovariantRepresentation hρ).comap φ :=
  CovariantRepresentation.ext (by ext; simp) (DFunLike.ext _ _ fun _ => by simp)

end CovariantMultiplierHom

end Basic

/-! ### Strict Bochner integration of covariant multiplier homomorphisms -/

namespace CovariantMultiplierHom

section Integrated

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} (M : CovariantMultiplierHom α B)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The left centralizer integrand `r ↦ (π(f r) u_r).fst b` is norm continuous in `B`. -/
@[fun_prop]
theorem continuous_integrand_fst (f : C_c(G, A)) (b : B) :
    Continuous fun r => (M.coefficient (f r) * M.group r).fst b := by
  simp only [DoubleCentralizer.mul_fst, mul_apply_eq_comp]
  exact ((DoubleCentralizer.continuous_toProd.fst.comp
    ((map_continuous M.coefficient).comp f.continuous))).clm_apply (M.continuous_group_fst b)

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The right centralizer integrand `r ↦ (M.coefficient (f r) * M.group r).snd b` is norm
continuous in `B`. -/
@[fun_prop]
theorem continuous_integrand_snd (f : C_c(G, A)) (b : B) :
    Continuous fun r => (M.coefficient (f r) * M.group r).snd b := by
  -- Rewrite using covariance so that the norm-continuous coefficient map acts on the outside.
  simp_rw [M.coefficient_mul_group, DoubleCentralizer.mul_snd, mul_apply_eq_comp]
  exact ((DoubleCentralizer.continuous_toProd.snd.comp ((map_continuous M.coefficient).comp
    (α.continuous_apply continuous_inv f.continuous)))).clm_apply (M.continuous_group_snd b)

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The left centralizer integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand_fst (f : C_c(G, A)) (b : B) :
    HasCompactSupport fun r => (M.coefficient (f r) * M.group r).fst b :=
  f.hasCompactSupport.mono fun _ hg hzero => hg (by simp [hzero])

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The right centralizer integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand_snd (f : C_c(G, A)) (b : B) :
    HasCompactSupport fun r => (M.coefficient (f r) * M.group r).snd b :=
  f.hasCompactSupport.mono fun _ hg hzero => hg (by simp [hzero])

omit [IsTopologicalGroup G] in
/-- The left centralizer integrand is Bochner integrable. -/
theorem integrable_integrand_fst (f : C_c(G, A)) (b : B) :
    Integrable (fun r => (M.coefficient (f r) * M.group r).fst b) μ :=
  (M.continuous_integrand_fst f b).integrable_of_hasCompactSupport
    (M.hasCompactSupport_integrand_fst f b)

/-- The right centralizer integrand is Bochner integrable. -/
theorem integrable_integrand_snd (f : C_c(G, A)) (b : B) :
    Integrable (fun r => (M.coefficient (f r) * M.group r).snd b) μ :=
  (M.continuous_integrand_snd f b).integrable_of_hasCompactSupport
    (M.hasCompactSupport_integrand_snd f b)

omit [IsTopologicalGroup G] in
private theorem norm_integral_fst_le (f : C_c(G, A)) (b : B) :
    ‖∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ‖ ≤ (∫ r, ‖f r‖ ∂μ) * ‖b‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun r => ?_)
  refine (((M.coefficient (f r) * M.group r).fst).le_opNorm b).trans ?_
  rw [DoubleCentralizer.norm_fst, CStarRing.norm_mul_coe_unitary]
  exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg b)

omit [IsTopologicalGroup G] in
private theorem norm_integral_snd_le (f : C_c(G, A)) (b : B) :
    ‖∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ‖ ≤ (∫ r, ‖f r‖ ∂μ) * ‖b‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun r => ?_)
  refine (((M.coefficient (f r) * M.group r).snd).le_opNorm b).trans ?_
  rw [DoubleCentralizer.norm_snd, CStarRing.norm_mul_coe_unitary]
  exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg b)

omit [IsTopologicalGroup G] in
private def integratedFst (f : C_c(G, A)) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun b := ∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ
      map_add' b c := by
        simpa only [map_add] using
          integral_add (M.integrable_integrand_fst μ f b) (M.integrable_integrand_fst μ f c)
      map_smul' z b := by simpa only [map_smul, RingHom.id_apply] using integral_smul z _ }
    (∫ r, ‖f r‖ ∂μ) (M.norm_integral_fst_le μ f)

private def integratedSnd (f : C_c(G, A)) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun b := ∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ
      map_add' b c := by
        simpa only [map_add] using
          integral_add (M.integrable_integrand_snd μ f b) (M.integrable_integrand_snd μ f c)
      map_smul' z b := by simpa only [map_smul, RingHom.id_apply] using integral_smul z _ }
    (∫ r, ‖f r‖ ∂μ) (M.norm_integral_snd_le μ f)

/-- The strict Bochner integrated form of a covariant multiplier homomorphism on `C_c(G, A)`. -/
def integratedMultiplier : C_c(G, A) →ₗ[ℂ] 𝓜(ℂ, B) where
  toFun f :=
    { toProd := (M.integratedFst μ f, M.integratedSnd μ f)
      central x y := by
        dsimp only [integratedFst, integratedSnd, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
          AddHom.coe_mk]
        have hl := (ContinuousLinearMap.mul ℂ B x).integral_comp_comm
          (M.integrable_integrand_fst μ f y)
        have hr := ((ContinuousLinearMap.mul ℂ B).flip y).integral_comp_comm
          (M.integrable_integrand_snd μ f x)
        simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
        rw [← hl, ← hr]
        exact integral_congr_ae <| .of_forall fun r =>
          (M.coefficient (f r) * M.group r).central x y }
  map_add' f g := DoubleCentralizer.ext_fst fun b => by
    simpa [integratedFst, add_mul] using
      integral_add (M.integrable_integrand_fst μ f b) (M.integrable_integrand_fst μ g b)
  map_smul' z f := DoubleCentralizer.ext_fst fun b => by
    simpa [integratedFst, smul_mul_assoc] using
      integral_smul z fun r => (M.coefficient (f r) * M.group r).fst b

/-- Left action of the integrated multiplier as a Bochner integral in `B`. -/
@[simp]
theorem integratedMultiplier_fst_apply (f : C_c(G, A)) (b : B) :
    (M.integratedMultiplier μ f).fst b = ∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ := (rfl)

/-- Right action of the integrated multiplier as a Bochner integral in `B`. -/
@[simp]
theorem integratedMultiplier_snd_apply (f : C_c(G, A)) (b : B) :
    (M.integratedMultiplier μ f).snd b = ∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ := (rfl)

/-- The integrated multiplier is bounded in norm by the L¹ norm of `f`. -/
theorem norm_integratedMultiplier_le (f : C_c(G, A)) :
    ‖M.integratedMultiplier μ f‖ ≤ ∫ r, ‖f r‖ ∂μ :=
  (DoubleCentralizer.norm_fst _).symm.trans_le <|
    LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _)
      (M.norm_integral_fst_le μ f)

/-- Applying the multiplier extension of any nondegenerate Hilbert-space representation of `B` to
`M.integratedMultiplier μ f` yields the vector-integrated operator of the corresponding
`CovariantRepresentation`. -/
@[simp]
theorem multiplierExtension_integratedMultiplier {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (f : C_c(G, A)) :
    ρ.multiplierExtension hρ (M.integratedMultiplier μ f) =
      (M.toCovariantRepresentation hρ).integratedOperator μ f := by
  symm
  refine (ρ.eq_multiplierExtension_iff hρ).2 fun b => ContinuousLinearMap.ext fun v => ?_
  have hev := AddMonoidHom.integral_comp_comm (AddMonoidHom.mk' (fun x => ρ x v) fun _ _ => by simp)
    ((ContinuousLinearMap.apply ℂ H v).continuous.comp (map_continuous ρ))
    (M.integrable_integrand_fst μ f b)
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [mul_apply_eq_comp, CovariantRepresentation.integratedOperator_apply,
    integratedMultiplier_fst_apply, ← hev]
  exact integral_congr_ae <| .of_forall fun r => by
    simp [DoubleCentralizer.mul_fst, mul_apply_eq_comp]

/-- Pushing `M` forward along a nondegenerate `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` commutes with strict
Bochner integration. -/
@[simp]
theorem extendToMultiplier_integratedMultiplier {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (f : C_c(G, A)) :
    ψ.extendToMultiplier hψ (M.integratedMultiplier μ f) = (M.map hψ).integratedMultiplier μ f := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ π hπ => ?_
  rw [← StarAlgHom.comp_apply, ← NonUnitalStarAlgHom.multiplierExtension_comp,
    M.multiplierExtension_integratedMultiplier, (M.map hψ).multiplierExtension_integratedMultiplier,
    M.toCovariantRepresentation_map]

/-- Pullback of a covariant multiplier homomorphism along an equivariant coefficient map commutes
with strict Bochner integration. -/
@[simp]
theorem integratedMultiplier_comap [LocallyCompactSpace G] {A' : Type*}
    [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'} (φ : Hom α' α)
    (f : ConvolutionAlgebra α' μ) :
    (M.comap φ).integratedMultiplier μ f.ofConv =
      M.integratedMultiplier μ (φ.convolutionMap μ f).ofConv :=
  DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ ρ hρ => by
    simpa using (M.toCovariantRepresentation hρ).integratedOperator_comap φ μ f

/-- Left multiplication of `f` by `a : A` becomes left multiplication by `M.coefficient a`. -/
@[simp]
theorem integratedMultiplier_smul (a : A) (f : C_c(G, A)) :
    M.integratedMultiplier μ (a • f) = M.coefficient a * M.integratedMultiplier μ f :=
  DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ _ _ => by simp

section LeftInvariant

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Strict Bochner integration is multiplicative for twisted convolution with respect to a
left-invariant measure. -/
@[simp]
theorem integratedMultiplier_convolution (f g : C_c(G, A)) :
    M.integratedMultiplier μ (α.convolution μ f g) =
      M.integratedMultiplier μ f * M.integratedMultiplier μ g :=
  DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ _ _ => by simp

/-- Twisted left translation on `C_c(G, A)` becomes left multiplication by `M.group r`. -/
@[simp]
theorem integratedMultiplier_translate (r : G) (f : C_c(G, A)) :
    M.integratedMultiplier μ (α.translate r f) =
      (M.group r : 𝓜(ℂ, B)) * M.integratedMultiplier μ f :=
  DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ _ _ => by simp

end LeftInvariant

section PeakApproximation

variable [LocallyCompactSpace G] [R1Space G] [μ.IsOpenPosMeasure]

/-- Peak-function approximation at any group element `r₀ : G`: every vector
`(M.coefficient a * M.group r₀).fst b` in `B` can be approximated in norm within `ε > 0` by
`(M.integratedMultiplier μ f).fst b` for some `f : C_c(G, A)`. -/
theorem exists_norm_integratedMultiplier_fst_sub_le (r₀ : G) (a : A) (b : B) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : C_c(G, A),
      ‖(M.integratedMultiplier μ f).fst b - (M.coefficient a * M.group r₀).fst b‖ ≤ ε := by
  set ψ : G → B := fun r => (M.coefficient a * M.group r).fst b
  have hψ : Continuous ψ := (M.coefficient a).fst.continuous.comp (M.continuous_group_fst b)
  have hU : {r : G | ‖ψ r - ψ r₀‖ ≤ ε} ∈ 𝓝 r₀ :=
    (continuous_norm.comp (hψ.sub continuous_const)).continuousAt.preimage_mem_nhds
      (ge_mem_nhds (by simpa [ψ] using hε))
  obtain ⟨φ, hφ0, hφU, hφ1⟩ := exists_nonneg_tsupport_subset_integral_eq_one μ hU
  let f : C_c(G, A) := φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)
  have hf_int : (M.integratedMultiplier μ f).fst b = ∫ r, φ r • ψ r ∂μ := by
    rw [integratedMultiplier_fst_apply]
    refine integral_congr_ae (.of_forall fun r => ?_)
    have hfr : f r = (φ r : ℂ) • a := by simp [f, CompactlySupportedContinuousMap.compLeft_apply]
    dsimp only
    rw [hfr, map_smul]
    simp [ψ]
  exact ⟨f, hf_int ▸ φ.norm_integral_smul_sub_le hφ0 hφ1 hψ fun r hr => hφU hr⟩

/-- The integrated multipliers on `C_c(G, A)` generate the exact same closed essential subspace of
`B` as `M.coefficient`. -/
theorem topologicalClosure_span_integratedMultiplier :
    (Submodule.span ℂ
      (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (M.coefficient a).fst)).topologicalClosure := by
  set S₁ := Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst)
  set S₂ := Submodule.span ℂ (⋃ a : A, Set.range (M.coefficient a).fst)
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      S₂.isClosed_topologicalClosure
    rintro _ ⟨_, ⟨f, rfl⟩, b, rfl⟩
    set W := S₂.topologicalClosure
    have : CompleteSpace W := S₂.isClosed_topologicalClosure.completeSpace_coe
    have hmem (r : G) : (M.coefficient (f r) * M.group r).fst b ∈ W :=
      Submodule.le_topologicalClosure S₂ <| Submodule.subset_span <|
        Set.mem_iUnion.2 ⟨f r, (M.group r : 𝓜(ℂ, B)).fst b, rfl⟩
    let F : G → W := Set.codRestrict (fun r => (M.coefficient (f r) * M.group r).fst b) W hmem
    have hF_int : Integrable F μ := ((M.continuous_integrand_fst f b).codRestrict
      hmem).integrable_of_hasCompactSupport <| (M.hasCompactSupport_integrand_fst f b).mono
        fun _ hr h0 => hr (Subtype.ext (h0.trans Submodule.coe_zero.symm))
    rw [integratedMultiplier_fst_apply]
    exact (W.subtypeL.integral_comp_comm hF_int).symm ▸ (∫ r, F r ∂μ).prop
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      S₁.isClosed_topologicalClosure
    rintro _ ⟨_, ⟨a, rfl⟩, b, rfl⟩
    rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨f, hf⟩ := M.exists_norm_integratedMultiplier_fst_sub_le μ 1 a b (half_pos hε)
    rw [map_one, OneMemClass.coe_one, mul_one] at hf
    refine ⟨(M.integratedMultiplier μ f).fst b,
      Submodule.subset_span (Set.mem_iUnion.2 ⟨f, b, rfl⟩), ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact hf.trans_lt (half_lt_self hε)

/-- Multiplier nondegeneracy is preserved and reflected by the strict integrated form on
`C_c(G, A)`. -/
theorem dense_span_integratedMultiplier_iff :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst) : Set B) ↔
      M.coefficient.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top,
    M.topologicalClosure_span_integratedMultiplier μ]

end PeakApproximation

end Integrated

section Uniqueness

variable {G A B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {M N : CovariantMultiplierHom α B}
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]

/-- Nondegenerate covariant multiplier homomorphisms are uniquely determined by their strict
integrated forms on `C_c(G, A)`. -/
theorem eq_of_integratedMultiplier_eq (hM : M.coefficient.IsMultiplierNondegenerate)
    (h : ∀ f : C_c(G, A), M.integratedMultiplier μ f = N.integratedMultiplier μ f) :
    M = N := by
  have hrep {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate) :
      M.toCovariantRepresentation hρ = N.toCovariantRepresentation hρ :=
    CovariantRepresentation.ext_integratedOperator μ (hρ.multiplierExtension_comp hM) fun f => by
      rw [← M.multiplierExtension_integratedMultiplier μ hρ,
        ← N.multiplierExtension_integratedMultiplier μ hρ, h f]
  exact ext
    (NonUnitalStarAlgHom.ext fun a => DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2
      fun _ _ _ _ ρ hρ => congrArg (fun P => P.coefficient a) (hrep ρ hρ))
    (MonoidHom.ext fun r => Subtype.ext <| DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2
      fun _ _ _ _ ρ hρ => congrArg (fun P => P.group r) (hrep ρ hρ))

end Uniqueness

section Haar

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} (M : CovariantMultiplierHom α B)
  (μ : Measure G) [μ.IsHaarMeasure]

/-- With respect to a left Haar measure, strict Bochner integration sends the twisted involution on
`C_c(G, A)` to the adjoint in `𝓜(ℂ, B)`. -/
@[simp]
theorem integratedMultiplier_twistedInvolution (f : C_c(G, A)) :
    M.integratedMultiplier μ (α.twistedInvolution f) = star (M.integratedMultiplier μ f) :=
  DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun _ _ _ _ _ _ => by simp [map_star]

/-- The strict integrated form of a covariant multiplier homomorphism as a ⋆-homomorphism out of
the twisted convolution algebra `ConvolutionAlgebra α μ`. -/
def integratedStarAlgHom : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B) where
  toFun f := M.integratedMultiplier μ f.ofConv
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_smul' _ _ := by simp
  map_star' _ := by simp

@[simp]
theorem integratedStarAlgHom_apply (f : ConvolutionAlgebra α μ) :
    M.integratedStarAlgHom μ f = M.integratedMultiplier μ f.ofConv := (rfl)

/-- The integrated ⋆-homomorphism is contractive for the L¹ norm on `ConvolutionAlgebra α μ`. -/
theorem norm_integratedStarAlgHom_le_norm (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [ConvolutionAlgebra.norm_eq_integral_norm] using M.norm_integratedMultiplier_le μ f.ofConv

theorem multiplierExtension_integratedStarAlgHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (f : ConvolutionAlgebra α μ) :
    ρ.multiplierExtension hρ (M.integratedStarAlgHom μ f) =
      (M.toCovariantRepresentation hρ).integratedStarAlgHom μ f := by simp

theorem extendToMultiplier_integratedStarAlgHom {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (f : ConvolutionAlgebra α μ) :
    ψ.extendToMultiplier hψ (M.integratedStarAlgHom μ f) =
      (M.map hψ).integratedStarAlgHom μ f := by simp

/-- Pullback of a covariant multiplier homomorphism along an equivariant coefficient map composes
`integratedStarAlgHom` with the induced convolution homomorphism. -/
@[simp]
theorem integratedStarAlgHom_comap {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (φ : Hom α' α) :
    (M.comap φ).integratedStarAlgHom μ = (M.integratedStarAlgHom μ).comp (φ.convolutionMap μ) :=
  NonUnitalStarAlgHom.ext fun _ => by simp

/-- Nondegenerate covariant multiplier homomorphisms are uniquely determined by their integrated
⋆-homomorphisms on `ConvolutionAlgebra α μ`. -/
theorem eq_of_integratedStarAlgHom_eq {N : CovariantMultiplierHom α B}
    (hM : M.coefficient.IsMultiplierNondegenerate)
    (h : M.integratedStarAlgHom μ = N.integratedStarAlgHom μ) : M = N :=
  eq_of_integratedMultiplier_eq μ hM fun f => by
    simpa using congr($h (ConvolutionAlgebra.toConv f))

end Haar

end CovariantMultiplierHom

end TauCeti.CStarAction
