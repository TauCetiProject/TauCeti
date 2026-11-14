/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.Unitary
public import TauCeti.Analysis.Fourier.Pontryagin.Density
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Spectral measure of a unitary representation of a discrete abelian group

Let `π` be a unitary representation of a discrete abelian group `G` on a complex Hilbert space
`H`, written additively as `π : ContRepresentation ℂ (Multiplicative G) H`, and let
`PontryaginDual G` be the Pontryagin dual of `G`, a compact abelian group. This file constructs
the projection-valued measure `P` on `PontryaginDual G` with

`π g = ∫ χ(g) dP(χ)`,

the spectral theorem of Stone, Naimark, Ambrose and Godement for discrete abelian groups. For
`G = ℤⁿ` the dual is the torus `𝕋ⁿ`, and `P` decomposes a representation of `ℤⁿ` over the
characters of `ℤⁿ`.

The operators `π g` are commuting unitaries, so they generate a commutative unital C⋆-algebra
`A`. Restricting a character of `A` to the operators `π g` gives a continuous character of `G`;
composing with the inverse Gelfand transform of `A`, this yields a unital star homomorphism
`C(PontryaginDual G, ℂ) → (H →L[ℂ] H)`, the spectral calculus of `π`, sending the evaluation
character `χ ↦ χ g` to `π g`. Its projection-valued measure
`TauCeti.ProjValMeasure.ofRepresentation` is the spectral measure. The evaluation characters span
a dense subspace of `C(PontryaginDual G, ℂ)` (`PontryaginDual.dense_span_evalBoundedContinuous`),
so both objects are determined by the values `π g`.

The trivial character carries the invariant vectors: the spectral projection of `{1}` is the
projection onto the `π`-invariant vectors. Hence `π` has no nonzero invariant vector exactly
when `P({1}) = 0`.

The spectral measure is natural in the group and in the Hilbert space. Restricting `π` along a
homomorphism `f` pushes `P` forward along the dual homomorphism `χ ↦ χ ∘ f`, and a unitary
intertwining two representations intertwines their spectral projections. Combining the two, a
unitary `U` with `U π(g) = π'(f g) U` satisfies `U P(B) = P'({χ | χ ∘ f ∈ B}) U`. For a unitary
representation `ρ` of a semidirect product `G ⋊[φ] K` this says that `ρ k` moves the spectral
measure of `ρ` restricted to `G` by the map `χ ↦ χ ∘ φ k` on the characters of `G`, and likewise
for the diagonal measures `B ↦ ‖P(B) ξ‖²`. For `ℤ² ⋊ SL₂(ℤ)` this is the equivariance of the
spectral measure on the torus `𝕋²` under the dual action of `SL₂(ℤ)`, the starting point of the
spectral proof of relative property (T) of `(ℤ² ⋊ SL₂(ℤ), ℤ²)`.

## Main declarations

* `ContRepresentation.spectralStarAlgHom`: the spectral calculus of `π`, and its
  characterization `ContRepresentation.eq_spectralStarAlgHom_iff`.
* `ContRepresentation.spectralPVM`: the spectral measure of `π`.
* `ContRepresentation.integral_spectralPVM_evalBoundedContinuous`: `∫ χ(g) dP(χ) = π g`.
* `ContRepresentation.integral_diag_spectralPVM`: the diagonal measure of `ξ` has
  Fourier–Stieltjes transform `g ↦ ⟪ξ, π g ξ⟫`.
* `ContRepresentation.eq_spectralPVM_iff`: uniqueness among projection-valued measures with
  regular diagonal measures.
* `ContRepresentation.forall_commute_spectralPVM_proj_iff`: the operators commuting with the
  spectral measure are those commuting with `π`.
* `ContRepresentation.range_spectralPVM_proj_singleton_one`: `P({1})` projects onto the
  `π`-invariant vectors.
* `ContRepresentation.spectralPVM_restrict`: restriction along a homomorphism pushes the spectral
  measure forward along the dual homomorphism.
* `ContRepresentation.apply_spectralPVM_proj_of_intertwines_restrict`,
  `ContRepresentation.map_diag_spectralPVM_of_intertwines_restrict`: equivariance of the spectral
  projections and diagonal measures under a unitary intertwiner.
* `ContRepresentation.apply_inr_spectralPVM_restrict_inl_proj`,
  `ContRepresentation.map_diag_spectralPVM_restrict_inl_apply_inr`: equivariance of the spectral
  measure of the normal abelian factor of a semidirect product.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §4.4.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Appendix D.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

noncomputable section

open MeasureTheory TauCeti WeakDual
open scoped InnerProductSpace CStarAlgebra

namespace ContRepresentation

variable {G : Type*} [AddCommGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : ContRepresentation ℂ (Multiplicative G) H}

namespace SpectralPVM

/-- The operator `π g`, as a unitary. -/
private def unitaryOp (hπ : π.IsUnitary) (g : Multiplicative G) : unitary (H →L[ℂ] H) :=
  ⟨π g, hπ.mem_unitary g⟩

private theorem coe_unitaryOp (hπ : π.IsUnitary) (g : Multiplicative G) :
    (unitaryOp hπ g : H →L[ℂ] H) = π g :=
  rfl

/-- The closed star algebra generated by the unitaries `π g`. -/
private def algebra (hπ : π.IsUnitary) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range fun g => (unitaryOp hπ g : H →L[ℂ] H))).topologicalClosure

private theorem star_apply (hπ : π.IsUnitary) (g : Multiplicative G) : star (π g) = π g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, hπ.adjoint_eq_inv]

omit [CompleteSpace H] in
private theorem commute_apply (g h : Multiplicative G) : Commute (π g) (π h) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

private instance (hπ : π.IsUnitary) : IsMulCommutative (algebra hπ) := by
  have : IsMulCommutative
      (StarAlgebra.adjoin ℂ (Set.range fun g => (unitaryOp hπ g : H →L[ℂ] H))) := by
    refine StarAlgebra.isMulCommutative_adjoin ℂ ?_ ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact ⟨by simp only [coe_unitaryOp, star_apply hπ]; exact commute_apply _ _⟩
    · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ _
      simp only [coe_unitaryOp]
      exact commute_apply g h
    · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ _
      simp only [coe_unitaryOp, star_apply hπ]
      exact commute_apply g h⁻¹
  unfold algebra
  infer_instance

private instance (hπ : π.IsUnitary) : IsClosed (algebra hπ : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

open scoped IsMulCommutative in
private instance (hπ : π.IsUnitary) : CommCStarAlgebra (algebra hπ) where

private theorem apply_mem_algebra (hπ : π.IsUnitary) (g : Multiplicative G) :
    π g ∈ algebra hπ :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨g, coe_unitaryOp hπ g⟩)

/-- An operator of `π`, as an element of the generated algebra. -/
private def op (hπ : π.IsUnitary) (g : Multiplicative G) : algebra hπ :=
  ⟨π g, apply_mem_algebra hπ g⟩

private theorem star_op (hπ : π.IsUnitary) (g : Multiplicative G) :
    star (op hπ g) = op hπ g⁻¹ :=
  Subtype.ext (star_apply hπ g)

private theorem op_mul (hπ : π.IsUnitary) (g h : Multiplicative G) :
    op hπ (g * h) = op hπ g * op hπ h :=
  Subtype.ext (map_mul π g h)

private theorem op_one (hπ : π.IsUnitary) : op hπ 1 = 1 :=
  Subtype.ext (map_one π)

/-- A character of the generated algebra takes values of modulus one on the operators of `π`. -/
private theorem apply_op_mem_sphere (hπ : π.IsUnitary) (ω : characterSpace ℂ (algebra hπ))
    (g : Multiplicative G) : ω (op hπ g) ∈ Submonoid.unitSphere ℂ := by
  have h : star (ω (op hπ g)) * ω (op hπ g) = 1 := by
    rw [← map_star, ← map_mul, star_op, ← op_mul, inv_mul_cancel, op_one, map_one]
  rw [Complex.star_def, Complex.conj_mul'] at h
  refine mem_sphere_zero_iff_norm.2 ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_)
  exact_mod_cast h

/-- The value of a character of the generated algebra on an operator of `π`, as a point of the
circle. -/
private def circleValue (hπ : π.IsUnitary) (ω : characterSpace ℂ (algebra hπ))
    (g : Multiplicative G) : Circle :=
  ⟨ω (op hπ g), apply_op_mem_sphere hπ ω g⟩

private theorem coe_circleValue (hπ : π.IsUnitary) (ω : characterSpace ℂ (algebra hπ))
    (g : Multiplicative G) : (circleValue hπ ω g : ℂ) = ω (op hπ g) :=
  rfl

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The group character obtained by restricting a character of the generated algebra to the
operators of `π`. -/
private def toDual (hπ : π.IsUnitary) (ω : characterSpace ℂ (algebra hπ)) :
    PontryaginDual (Multiplicative G) where
  toFun := circleValue hπ ω
  map_one' := Circle.ext (by rw [coe_circleValue, op_one, map_one, Circle.coe_one])
  map_mul' g h := Circle.ext (by
    rw [Circle.coe_mul, coe_circleValue, coe_circleValue, coe_circleValue, op_mul, map_mul])
  continuous_toFun := continuous_of_discreteTopology

private theorem coe_toDual_apply (hπ : π.IsUnitary) (ω : characterSpace ℂ (algebra hπ))
    (g : Multiplicative G) : (toDual hπ ω g : ℂ) = ω (op hπ g) :=
  rfl

private theorem continuous_toDual (hπ : π.IsUnitary) : Continuous (toDual hπ) := by
  refine ContinuousMonoidHom.continuous_of_continuous_uncurry _
    (continuous_prod_of_discrete_right.2 fun g => ?_)
  exact ((eval_continuous (op hπ g)).comp continuous_subtype_val).subtype_mk
    (apply_op_mem_sphere hπ · g)

end SpectralPVM

open SpectralPVM
open PontryaginDual (evalBoundedContinuous starAlgHom_ext
  mem_of_isClosed_of_forall_evalBoundedContinuous_mem)

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The **spectral calculus** of a unitary representation `π` of a discrete abelian group `G`: the
unital star homomorphism from the continuous functions on the compact Pontryagin dual of `G` to the
bounded operators, sending the evaluation character `χ ↦ χ g` to `π g`
(`spectralStarAlgHom_evalBoundedContinuous`). It is the only such star homomorphism
(`eq_spectralStarAlgHom_iff`). -/
def spectralStarAlgHom (hπ : π.IsUnitary) :
    C(PontryaginDual (Multiplicative G), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  ((algebra hπ).subtype.comp (gelfandStarTransform (algebra hπ)).symm.toStarAlgHom).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨toDual hπ, continuous_toDual hπ⟩)

/-- The spectral calculus sends the evaluation character at `g` to `π g`. -/
@[simp]
theorem spectralStarAlgHom_evalBoundedContinuous (hπ : π.IsUnitary) (g : G) :
    π.spectralStarAlgHom hπ (evalBoundedContinuous g).toContinuousMap = π (.ofAdd g) := by
  have h : gelfandStarTransform (algebra hπ) (op hπ (.ofAdd g)) =
      (evalBoundedContinuous g).toContinuousMap.comp ⟨toDual hπ, continuous_toDual hπ⟩ :=
    ContinuousMap.ext fun ω => by simp [coe_toDual_apply]
  simp [spectralStarAlgHom, ← h, op]

/-- **Uniqueness of the spectral calculus.** A unital star homomorphism from the continuous
functions on the Pontryagin dual is the spectral calculus of `π` iff it sends each evaluation
character at `g` to `π g`. -/
theorem eq_spectralStarAlgHom_iff (hπ : π.IsUnitary)
    (φ : C(PontryaginDual (Multiplicative G), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    φ = π.spectralStarAlgHom hπ ↔
      ∀ g : G, φ (evalBoundedContinuous g).toContinuousMap = π (.ofAdd g) := by
  refine ⟨fun h g => by rw [h, spectralStarAlgHom_evalBoundedContinuous], fun h => ?_⟩
  exact starAlgHom_ext fun g => by rw [h, spectralStarAlgHom_evalBoundedContinuous]

/-- An operator commuting with every `π g` commutes with the whole spectral calculus of `π`. -/
theorem commute_spectralStarAlgHom (hπ : π.IsUnitary) {A : H →L[ℂ] H}
    (hA : ∀ g, Commute A (π g)) (f : C(PontryaginDual (Multiplicative G), ℂ)) :
    Commute A (π.spectralStarAlgHom hπ f) := by
  let M : Submodule ℂ C(PontryaginDual (Multiplicative G), ℂ) :=
    { carrier := {f | Commute A (π.spectralStarAlgHom hπ f)}
      add_mem' := fun ha hb => by simpa only [Set.mem_ofPred_eq, map_add] using ha.add_right hb
      zero_mem' := by simp
      smul_mem' := fun c _ hf => by simpa only [Set.mem_ofPred_eq, map_smul] using hf.smul_right c }
  have hcont := map_continuous (π.spectralStarAlgHom hπ)
  refine mem_of_isClosed_of_forall_evalBoundedContinuous_mem (M := M)
    (isClosed_eq (continuous_const.mul hcont) (hcont.mul continuous_const)) (fun g => ?_) f
  simpa [M] using hA (.ofAdd g)

section Measure

variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- The **spectral measure** of a unitary representation `π` of a discrete abelian group `G`: the
projection-valued measure on the compact Pontryagin dual of `G` of the spectral calculus of `π`.
Integrating the evaluation character `χ ↦ χ g` against it gives `π g`
(`integral_spectralPVM_evalBoundedContinuous`), and it is the only projection-valued measure
with regular diagonal measures doing so (`eq_spectralPVM_iff`). -/
def spectralPVM (hπ : π.IsUnitary) :
    ProjValMeasure (PontryaginDual (Multiplicative G)) H :=
  ProjValMeasure.ofRepresentation (π.spectralStarAlgHom hπ)

/-- The diagonal measures of the spectral measure are regular. -/
instance regular_diag_spectralPVM (hπ : π.IsUnitary) (ξ : H) :
    ((π.spectralPVM hπ).diag ξ).Regular :=
  ProjValMeasure.regular_diag_ofRepresentation _ ξ

/-- Integrating a continuous function against the spectral measure gives its spectral
calculus. -/
@[simp]
theorem integral_spectralPVM_ofContinuousMap (hπ : π.IsUnitary)
    (f : C(PontryaginDual (Multiplicative G), ℂ)) :
    (π.spectralPVM hπ).integral (BoundedBorelFunction.ofContinuousMap f) =
      π.spectralStarAlgHom hπ f :=
  ProjValMeasure.integral_ofRepresentation_ofContinuousMap _ f

/-- **Recovery of the representation.** Integrating the evaluation character at `g` against the
spectral measure gives `π g`. -/
theorem integral_spectralPVM_evalBoundedContinuous (hπ : π.IsUnitary) (g : G) :
    (π.spectralPVM hπ).integral
        (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g).toContinuousMap) =
      π (.ofAdd g) := by
  simp

/-- The diagonal measure of `ξ` has Fourier–Stieltjes transform the matrix coefficient
`g ↦ ⟪ξ, π g ξ⟫`. -/
theorem integral_diag_spectralPVM (hπ : π.IsUnitary) (ξ : H) (g : G) :
    ∫ χ, (χ (.ofAdd g) : ℂ) ∂(π.spectralPVM hπ).diag ξ = ⟪ξ, π (.ofAdd g) ξ⟫_ℂ := by
  simpa using (π.spectralPVM hπ).integral_diag_eq_inner_integral
    (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g).toContinuousMap) ξ

/-- **Uniqueness of the spectral measure.** A projection-valued measure on the Pontryagin dual
with regular diagonal measures is the spectral measure of `π` iff integrating each evaluation
character at `g` against it gives `π g`. -/
theorem eq_spectralPVM_iff (hπ : π.IsUnitary)
    (P : ProjValMeasure (PontryaginDual (Multiplicative G)) H)
    (hP : ∀ ξ, (P.diag ξ).Regular) :
    P = π.spectralPVM hπ ↔ ∀ g : G,
      P.integral (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g).toContinuousMap) =
        π (.ofAdd g) := by
  rw [spectralPVM, ProjValMeasure.eq_ofRepresentation_iff _ P hP]
  refine ⟨fun h g => by rw [h, spectralStarAlgHom_evalBoundedContinuous], fun h f => ?_⟩
  let Ψ : C(PontryaginDual (Multiplicative G), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    P.integral.comp BoundedBorelFunction.ofContinuousMap
  exact congr($((π.eq_spectralStarAlgHom_iff hπ Ψ).2 h) f)

/-- **Commutant of the spectral measure.** An operator commutes with every spectral projection of
`π` iff it commutes with every `π g`. -/
theorem forall_commute_spectralPVM_proj_iff (hπ : π.IsUnitary) (A : H →L[ℂ] H) :
    (∀ B hB, Commute A ((π.spectralPVM hπ).proj B hB)) ↔ ∀ g, Commute A (π g) := by
  rw [spectralPVM, ProjValMeasure.forall_commute_proj_ofRepresentation_iff]
  refine ⟨fun h g => ?_, fun h => π.commute_spectralStarAlgHom hπ h⟩
  simpa using h (evalBoundedContinuous g.toAdd).toContinuousMap

/-- Each `π g` fixes the range of the spectral projection of the trivial character. -/
theorem apply_spectralPVM_proj_singleton_one (hπ : π.IsUnitary) (g : Multiplicative G)
    (ξ : H) :
    π g ((π.spectralPVM hπ).proj {1} (measurableSet_singleton 1) ξ) =
      (π.spectralPVM hπ).proj {1} (measurableSet_singleton 1) ξ := by
  set P := π.spectralPVM hπ
  have hmul : BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g.toAdd).toContinuousMap *
      BoundedBorelFunction.indicator {1} (measurableSet_singleton 1) 1 =
      BoundedBorelFunction.indicator {1} (measurableSet_singleton 1) 1 := by
    ext χ
    by_cases hχ : χ = 1 <;> simp [hχ]
  have hg : P.integral
      (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g.toAdd).toContinuousMap) =
        π g :=
    integral_spectralPVM_evalBoundedContinuous hπ g.toAdd
  calc π g (P.proj {1} (measurableSet_singleton 1) ξ)
      = (P.integral
          (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g.toAdd).toContinuousMap) *
          P.integral (BoundedBorelFunction.indicator {1} (measurableSet_singleton 1) 1)) ξ := by
        rw [mul_apply_eq_comp, hg, P.integral_indicator]
    _ = P.proj {1} (measurableSet_singleton 1) ξ := by
        rw [← map_mul, hmul, P.integral_indicator]

/-- The diagonal measure of a `π`-invariant vector is carried by the trivial character. -/
private theorem diag_spectralPVM_compl_singleton_one (hπ : π.IsUnitary) {ξ : H}
    (hξ : ξ ∈ π.invariants) : (π.spectralPVM hπ).diag ξ {1}ᶜ = 0 := by
  set μ := (π.spectralPVM hπ).diag ξ
  -- Each evaluation character is `1` almost everywhere, since `π g ξ - ξ = 0`.
  have hae (g : G) : μ {χ | (χ (.ofAdd g) : ℂ) ≠ 1} = 0 := by
    have h0 : (π.spectralPVM hπ).integral
        (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g).toContinuousMap - 1) ξ =
          0 := by
      rw [map_sub, map_one, integral_spectralPVM_evalBoundedContinuous, sub_apply, hξ,
        one_apply_eq_self, sub_self]
    simpa [sub_eq_zero] using
      ae_iff.1 (((π.spectralPVM hπ).integral_apply_eq_zero_iff _ ξ).1 h0)
  -- By regularity, a nonnull open set contains a nonnull compact set, which is covered by
  -- finitely many of these null sets.
  by_contra hne
  obtain ⟨K, hKU, hK, hμK⟩ :=
    isOpen_compl_singleton.exists_lt_isCompact (μ := μ) (pos_iff_ne_zero.2 hne)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : G => {χ : PontryaginDual (Multiplicative G) | (χ (.ofAdd g) : ℂ) ≠ 1})
    (fun g => isOpen_ne_fun (TauCeti.PontryaginDual.continuous_coe_eval_const _) continuous_const)
    (fun χ hχ => by
      obtain ⟨g, hg⟩ : ∃ g : Multiplicative G, χ g ≠ 1 := by
        by_contra! h
        exact hKU hχ (PontryaginDual.ext h)
      exact Set.mem_iUnion.2 ⟨g.toAdd, fun h => hg (Circle.ext h)⟩)
  exact hμK.ne' (measure_mono_null ht ((measure_biUnion_null_iff t.countable_toSet).2
    fun g _ => hae g))

/-- **Invariant vectors.** A vector is fixed by the spectral projection of the trivial character
iff it is `π`-invariant. -/
theorem spectralPVM_proj_singleton_one_apply_eq_self_iff (hπ : π.IsUnitary) (ξ : H) :
    (π.spectralPVM hπ).proj {1} (measurableSet_singleton 1) ξ = ξ ↔ ξ ∈ π.invariants := by
  refine ⟨fun h g => by rw [← h]; exact apply_spectralPVM_proj_singleton_one hπ g ξ,
    fun hξ => ?_⟩
  have h0 : (π.spectralPVM hπ).proj {1}ᶜ (measurableSet_singleton 1).compl ξ = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, ProjValMeasure.norm_sq_proj_apply,
      diag_spectralPVM_compl_singleton_one hπ hξ, ENNReal.toReal_zero]
  rw [ProjValMeasure.proj_compl, sub_apply, ContinuousLinearMap.id_apply,
    sub_eq_zero] at h0
  exact h0.symm

/-- **Invariant vectors.** The spectral projection of the trivial character is the projection onto
the `π`-invariant vectors. -/
theorem range_spectralPVM_proj_singleton_one (hπ : π.IsUnitary) :
    LinearMap.range ((π.spectralPVM hπ).proj {1} (measurableSet_singleton 1) : H →ₗ[ℂ] H) =
      π.invariants := by
  ext ξ
  refine ⟨?_, fun hξ => ⟨ξ, (π.spectralPVM_proj_singleton_one_apply_eq_self_iff hπ ξ).2 hξ⟩⟩
  rintro ⟨η, rfl⟩ g
  exact apply_spectralPVM_proj_singleton_one hπ g η

/-- The trivial character carries no spectral mass iff `π` has no nonzero invariant vector. -/
theorem spectralPVM_proj_singleton_one_eq_zero_iff (hπ : π.IsUnitary) :
    (π.spectralPVM hπ).proj {1} (measurableSet_singleton 1) = 0 ↔ π.invariants = ⊥ := by
  rw [← range_spectralPVM_proj_singleton_one hπ, LinearMap.range_eq_bot,
    ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj]

end Measure

section Equivariance

/-! ### Naturality and equivariance -/

variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]
  {G' : Type*} [AddCommGroup G'] [TopologicalSpace G'] [DiscreteTopology G']
  [MeasurableSpace (PontryaginDual (Multiplicative G'))]
  [BorelSpace (PontryaginDual (Multiplicative G'))]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Naturality of the spectral measure.** Restricting `π` along a homomorphism `f` pushes its
spectral measure forward along the dual homomorphism `χ ↦ χ ∘ f`. -/
@[simp]
theorem spectralPVM_restrict (hπ : π.IsUnitary) (f : Multiplicative G' →ₜ* Multiplicative G) :
    (π.restrict (f : Multiplicative G' →* Multiplicative G)).spectralPVM (hπ.restrict _) =
      (π.spectralPVM hπ).map (PontryaginDual.map f)
        (map_continuous (PontryaginDual.map f)).measurable := by
  symm
  refine ((π.restrict _).eq_spectralPVM_iff (hπ.restrict _) _ fun ξ => ?_).2 fun g => ?_
  · -- The pushforward of a finite regular measure along a continuous map is regular.
    rw [ProjValMeasure.map_diag]
    have := Measure.InnerRegularCompactLTTop.map_of_continuous (μ := (π.spectralPVM hπ).diag ξ)
      (map_continuous (PontryaginDual.map f))
    infer_instance
  · have h : BoundedBorelFunction.compStarAlgHom' (PontryaginDual.map f)
        (map_continuous (PontryaginDual.map f)).measurable
          (BoundedBorelFunction.ofContinuousMap (evalBoundedContinuous g).toContinuousMap) =
        BoundedBorelFunction.ofContinuousMap
          (evalBoundedContinuous (f (.ofAdd g)).toAdd).toContinuousMap := by
      ext χ
      simp
    rw [ProjValMeasure.integral_map, h, integral_spectralPVM_evalBoundedContinuous,
      restrict_apply, ofAdd_toAdd, MonoidHom.coe_ofClass]

/-- **Unitary transport of the spectral measure.** A unitary `U` intertwining `π` with `π'`
intertwines their spectral projections: `U ∘ P_π(B) = P_π'(B) ∘ U`. -/
theorem apply_spectralPVM_proj_of_intertwines {π' : ContRepresentation ℂ (Multiplicative G) H'}
    (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ξ, U (π g ξ) = π' g (U ξ)) {B : Set (PontryaginDual (Multiplicative G))}
    (hB : MeasurableSet B) (ξ : H) :
    U ((π.spectralPVM hπ).proj B hB ξ) = (π'.spectralPVM hπ').proj B hB (U ξ) := by
  have h : π'.spectralStarAlgHom hπ' =
      U.conjStarAlgEquiv.toStarAlgHom.comp (π.spectralStarAlgHom hπ) := by
    refine ((π'.eq_spectralStarAlgHom_iff hπ' _).2 fun g => ?_).symm
    ext η
    simp [hU]
  unfold spectralPVM
  rw [h, StarAlgHom.ofRepresentation_proj_conj, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    U.symm_apply_apply]

/-- **Equivariance of the spectral measure.** If a unitary `U` intertwines `π` with the
restriction of `π'` along a homomorphism `f`, then `U ∘ P_π(B) = P_π'(f̂⁻¹(B)) ∘ U`, where
`f̂ : χ ↦ χ ∘ f` is the dual homomorphism. -/
theorem apply_spectralPVM_proj_of_intertwines_restrict
    {π' : ContRepresentation ℂ (Multiplicative G') H'} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    (U : H ≃ₗᵢ[ℂ] H') (f : Multiplicative G →ₜ* Multiplicative G')
    (hU : ∀ g ξ, U (π g ξ) = π' (f g) (U ξ)) {B : Set (PontryaginDual (Multiplicative G))}
    (hB : MeasurableSet B) (ξ : H) :
    U ((π.spectralPVM hπ).proj B hB ξ) =
      (π'.spectralPVM hπ').proj (PontryaginDual.map f ⁻¹' B)
        ((map_continuous (PontryaginDual.map f)).measurable hB) (U ξ) := by
  rw [apply_spectralPVM_proj_of_intertwines hπ (hπ'.restrict _) U hU hB,
    spectralPVM_restrict, ProjValMeasure.map_proj]

/-- **Equivariance of the diagonal spectral measures.** If a unitary `U` intertwines `π` with the
restriction of `π'` along a homomorphism `f`, then pushing the diagonal measure of `U ξ` forward
along the dual homomorphism `f̂ : χ ↦ χ ∘ f` gives the diagonal measure of `ξ`. -/
theorem map_diag_spectralPVM_of_intertwines_restrict
    {π' : ContRepresentation ℂ (Multiplicative G') H'} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    (U : H ≃ₗᵢ[ℂ] H') (f : Multiplicative G →ₜ* Multiplicative G')
    (hU : ∀ g ξ, U (π g ξ) = π' (f g) (U ξ)) (ξ : H) :
    Measure.map (PontryaginDual.map f) ((π'.spectralPVM hπ').diag (U ξ)) =
      (π.spectralPVM hπ).diag ξ := by
  have hf := (map_continuous (PontryaginDual.map f)).measurable
  ext B hB
  rw [Measure.map_apply hf hB,
    ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
    ← ProjValMeasure.norm_sq_proj_apply _ _ (hf hB), ← ProjValMeasure.norm_sq_proj_apply _ _ hB,
    ← apply_spectralPVM_proj_of_intertwines_restrict hπ hπ' U f hU hB, U.norm_map]

section SemidirectProduct

open SemidirectProduct (inl inr)

variable {K : Type*} [Group K] {φ : K →* MulAut (Multiplicative G)}
  {ρ : ContRepresentation ℂ (Multiplicative G ⋊[φ] K) H}

/-- **Equivariance of the spectral measure in a semidirect product.** For a unitary
representation `ρ` of `G ⋊[φ] K` with `G` discrete abelian, the operator `ρ k` carries the spectral
projection of a set `B` of characters of `G`, for the restriction of `ρ` to `G`, to the spectral
projection of `{χ | χ ∘ φ k ∈ B}`. -/
theorem apply_inr_spectralPVM_restrict_inl_proj (hρ : ρ.IsUnitary) (k : K)
    {B : Set (PontryaginDual (Multiplicative G))} (hB : MeasurableSet B) (ξ : H) :
    ρ (inr k) (((ρ.restrict inl).spectralPVM (hρ.restrict _)).proj B hB ξ) =
      ((ρ.restrict inl).spectralPVM (hρ.restrict _)).proj
        (PontryaginDual.map ⟨(φ k).toMonoidHom, continuous_of_discreteTopology⟩ ⁻¹' B)
        ((map_continuous (PontryaginDual.map _)).measurable hB) (ρ (inr k) ξ) := by
  rw [← hρ.coe_toLinearIsometryEquiv (inr k)]
  exact apply_spectralPVM_proj_of_intertwines_restrict (hρ.restrict _) (hρ.restrict _)
    (hρ.toLinearIsometryEquiv (inr k)) _
    (fun g η => by rw [IsUnitary.coe_toLinearIsometryEquiv]; exact ρ.apply_inr_apply_inl k g η) hB ξ

/-- **Equivariance of the diagonal spectral measures in a semidirect product.** For a unitary
representation `ρ` of `G ⋊[φ] K` with `G` discrete abelian, pushing the diagonal spectral measure
of `ρ k ξ`, for the restriction of `ρ` to `G`, forward along `χ ↦ χ ∘ φ k` gives the diagonal
spectral measure of `ξ`. -/
theorem map_diag_spectralPVM_restrict_inl_apply_inr (hρ : ρ.IsUnitary) (k : K) (ξ : H) :
    Measure.map (PontryaginDual.map ⟨(φ k).toMonoidHom, continuous_of_discreteTopology⟩)
        (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ρ (inr k) ξ)) =
      ((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ := by
  rw [← hρ.coe_toLinearIsometryEquiv (inr k)]
  exact map_diag_spectralPVM_of_intertwines_restrict (hρ.restrict _) (hρ.restrict _)
    (hρ.toLinearIsometryEquiv (inr k)) _
    (fun g η => by rw [IsUnitary.coe_toLinearIsometryEquiv]; exact ρ.apply_inr_apply_inl k g η) ξ

end SemidirectProduct

end Equivariance

end ContRepresentation
