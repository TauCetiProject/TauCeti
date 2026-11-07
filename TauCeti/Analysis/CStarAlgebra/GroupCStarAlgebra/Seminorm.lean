/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
public import TauCeti.RepresentationTheory.Continuous.Integrated.CompactlySupported
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star

/-!
# Group convolution algebras, integrated unitary representations and the full group C⋆-seminorm

For a locally compact group `G : Type u` and a measure `μ`, `GroupConvolutionAlgebra G μ` is the
convolution ⋆-algebra `CStarAction.ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ`
on `C_c(G, ℂ)` with convolution `(f * g) s = ∫ r, f r * g (r⁻¹ * s) ∂μ`, the modular-weighted
involution `f⋆ s = c(s) • conj (f s⁻¹)` (`c = Measure.modularCharacter`), the `L¹(μ)` norm, and
isometric left translation `CStarAction.ConvolutionAlgebra.translateLIE`.

Integrating a strongly continuous unitary representation `U : ContRepresentation ℂ G H` against a
left Haar measure `μ` yields an `L¹`-contractive nonunital ⋆-homomorphism
`ContRepresentation.IsUnitary.integratedStarAlgHom` on `GroupConvolutionAlgebra G μ`. Taking
`‖f‖ᵤ = sup ‖U(f)‖` over `H : Type u` defines the definite C⋆-seminorm
`GroupConvolutionAlgebra.fullSeminorm G μ` for every left Haar measure `μ`, and rescaling by
`Measure.haarScalarFactor` identifies `GroupConvolutionAlgebra` and its universal C⋆-seminorm across
choices of left Haar measure.

## Main definitions

* `TauCeti.GroupConvolutionAlgebra`: abbreviation for
  `CStarAction.ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ`.
* `ContRepresentation.IsUnitary.integratedStarAlgHom`: the integrated nonunital ⋆-homomorphism on
  `GroupConvolutionAlgebra G μ`.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm`: the universal group C⋆-seminorm `‖·‖ᵤ`.
* `TauCeti.GroupConvolutionAlgebra.haarMeasureEquiv`: Haar-measure rescaling ⋆-isomorphism on
  `GroupConvolutionAlgebra`.

## Main statements

* `ContRepresentation.IsUnitary.integratedOperator_mul` and
  `ContRepresentation.IsUnitary.integratedOperator_star`: multiplicativity and ⋆-compatibility.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm_star_mul_self` and
  `TauCeti.GroupConvolutionAlgebra.fullSeminorm_eq_zero_iff`: the C⋆-identity and definiteness.
* `TauCeti.GroupConvolutionAlgebra.fullSeminorm_haarMeasureEquiv`: preservation of `fullSeminorm`
  under change of left Haar measure.

## References

* Kenneth R. Davidson, *C*-Algebras by Example*, Chapter VII.
* Jacques Dixmier, *C*-Algebras*, §13.9.
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.5, §3.2 and §7.1.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Function
open scoped CompactlySupported Pointwise InnerProductSpace ENNReal NNReal

namespace TauCeti

/-- The group convolution ⋆-algebra on `C_c(G, ℂ)` with respect to a measure `μ`, realized as the
convolution algebra `CStarAction.ConvolutionAlgebra` of the trivial action of `G` on `ℂ`. -/
abbrev GroupConvolutionAlgebra (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) :=
  CStarAction.ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ

end TauCeti

/-! ### Integrated ⋆-homomorphisms on the group convolution algebra -/

namespace ContRepresentation.IsUnitary

open TauCeti

section Convolution

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a left-invariant measure, the integrated form turns scalar convolution into composition. -/
@[simp] theorem integratedOperator_convolution {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (f g : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ ((CStarAction.trivial (G := G) (A := ℂ)).convolution μ f g) =
      hU.integratedOperator hcont μ f * hU.integratedOperator hcont μ g := by
  rw [← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_convolution,
    hU.integratedOperator_toTrivialCovariant, hU.integratedOperator_toTrivialCovariant]

/-- Left translation of `f : C_c(G, ℂ)` corresponds to left multiplication of `U(f)` by `U r`. -/
@[simp] theorem integratedOperator_translate {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (r : G) (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ ((CStarAction.trivial (G := G) (A := ℂ)).translate r f) =
      U r * hU.integratedOperator hcont μ f := by
  rw [← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_translate,
    toTrivialCovariant_group, hU.integratedOperator_toTrivialCovariant]

/-- For a left-invariant measure, the integrated form turns convolution into composition. -/
theorem integratedOperator_mul {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (f g : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (f * g).ofConv =
      hU.integratedOperator hcont μ f.ofConv * hU.integratedOperator hcont μ g.ofConv := by
  simp

/-- Left translation of `f` corresponds to left multiplication of `U(f)` by `U r`. -/
theorem integratedOperator_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (CStarAction.ConvolutionAlgebra.translateLIE r f).ofConv =
      U r * hU.integratedOperator hcont μ f.ofConv := by
  simp

end Convolution

section Star

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Against a left Haar measure, the integrated form intertwines the modular-weighted involution on
`C_c(G, ℂ)` with the Hilbert-space adjoint. -/
@[simp] theorem integratedOperator_twistedInvolution {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : C_c(G, ℂ)) :
    hU.integratedOperator hcont μ ((CStarAction.trivial (G := G) (A := ℂ)).twistedInvolution f) =
      star (hU.integratedOperator hcont μ f) := by
  rw [← hU.integratedOperator_toTrivialCovariant hcont μ,
    CStarAction.CovariantRepresentation.integratedOperator_twistedInvolution,
    hU.integratedOperator_toTrivialCovariant]

/-- Against a left Haar measure, the integrated form intertwines the modular-weighted involution
with the Hilbert-space adjoint. -/
theorem integratedOperator_star {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedOperator hcont μ (star f).ofConv =
      star (hU.integratedOperator hcont μ f.ofConv) := by
  simp

/-- The integrated form of a strongly continuous unitary representation as a nonunital complex
⋆-algebra homomorphism out of `GroupConvolutionAlgebra G μ`. -/
def integratedStarAlgHom {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure] :
    GroupConvolutionAlgebra G μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := hU.integratedOperator hcont μ f.ofConv
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' := hU.integratedOperator_mul hcont μ
  map_smul' _ _ := by simp
  map_star' := hU.integratedOperator_star hcont μ

@[simp] theorem integratedStarAlgHom_apply {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ f = hU.integratedOperator hcont μ f.ofConv := (rfl)

/-- Every integrated unitary representation is `L¹`-contractive. -/
theorem norm_integratedStarAlgHom_le_norm {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) : ‖hU.integratedStarAlgHom hcont μ f‖ ≤ ‖f‖ := by
  simpa only [integratedStarAlgHom_apply,
    CStarAction.ConvolutionAlgebra.norm_eq_integral_norm] using
    hU.norm_integratedOperator_le hcont μ f.ofConv

theorem integratedStarAlgHom_translateLIE {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont μ (CStarAction.ConvolutionAlgebra.translateLIE r f) =
      U r * hU.integratedStarAlgHom hcont μ f :=
  hU.integratedOperator_translateLIE hcont μ r f

end Star

section CommGroup

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Over a commutative group, the integrated ⋆-homomorphism has commuting values. -/
theorem integratedStarAlgHom_commute {U : ContRepresentation ℂ G H} (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (μ : Measure G) [μ.IsHaarMeasure]
    (f g : GroupConvolutionAlgebra G μ) :
    Commute (hU.integratedStarAlgHom hcont μ f) (hU.integratedStarAlgHom hcont μ g) :=
  hU.integratedOperator_commute hcont μ f.ofConv g.ofConv

end CommGroup
end ContRepresentation.IsUnitary

/-! ### The universal group C⋆-seminorm -/

namespace TauCeti.GroupConvolutionAlgebra

universe u

section FullSeminorm

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

variable (G μ) in
private def integratedSeminorms : Set (Seminorm ℂ (GroupConvolutionAlgebra G μ)) :=
  {p | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v),
      p = (normSeminorm ℂ (H →L[ℂ] H)).comp
        (hU.integratedStarAlgHom hcont μ : GroupConvolutionAlgebra G μ →ₗ[ℂ] (H →L[ℂ] H))}

private theorem bddAbove_integratedSeminorms : BddAbove (integratedSeminorms G μ) :=
  ⟨normSeminorm ℂ _, fun _ ⟨_, _, _, _, _, hU, hcont, hp⟩ f =>
    hp ▸ hU.norm_integratedStarAlgHom_le_norm hcont μ f⟩

variable (G μ) in
/-- The universal (or full) group C⋆-seminorm `‖f‖ᵤ = sup ‖U(f)‖` on `GroupConvolutionAlgebra G μ`,
ranging over strongly continuous unitary representations of `G` on Hilbert spaces in `Type u`. -/
def fullSeminorm : Seminorm ℂ (GroupConvolutionAlgebra G μ) := sSup (integratedSeminorms G μ)

/-- Pointwise formula for `fullSeminorm` as the supremum of integrated operator norms. -/
theorem fullSeminorm_apply (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ f =
      sSup {r | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v), ‖hU.integratedStarAlgHom hcont μ f‖ = r} := by
  rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms, iSup]
  congr 1; ext r; simp [integratedSeminorms]

/-- Every integrated unitary representation on `H : Type u` is bounded by `fullSeminorm`. -/
theorem norm_integratedStarAlgHom_le_fullSeminorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ContRepresentation ℂ G H}
    (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (f : GroupConvolutionAlgebra G μ) :
    ‖hU.integratedStarAlgHom hcont μ f‖ ≤ fullSeminorm G μ f :=
  le_csSup bddAbove_integratedSeminorms
    ⟨H, inferInstance, inferInstance, inferInstance, U, hU, hcont, rfl⟩ f

/-- `fullSeminorm G μ f` is the least nonnegative upper bound for all integrated operator norms. -/
theorem fullSeminorm_le_iff {f : GroupConvolutionAlgebra G μ} {c : ℝ} (hc : 0 ≤ c) :
    fullSeminorm G μ f ≤ c ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
        (hcont : ∀ v, Continuous fun g => U g v), ‖hU.integratedStarAlgHom hcont μ f‖ ≤ c :=
  ⟨fun h _ _ _ _ _ hU hcont => (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f).trans h,
    fun h => by
      rw [fullSeminorm, Seminorm.sSup_apply bddAbove_integratedSeminorms]
      exact Real.iSup_le (fun ⟨_, H, _, _, _, U, hU, hcont, hp⟩ => hp ▸ h H U hU hcont) hc⟩

/-- The full group C⋆-seminorm is dominated by the `L¹(μ)` norm. -/
theorem fullSeminorm_le_norm (f : GroupConvolutionAlgebra G μ) : fullSeminorm G μ f ≤ ‖f‖ :=
  (fullSeminorm_le_iff (norm_nonneg f)).2 fun _ _ _ _ _ hU hcont =>
    hU.norm_integratedStarAlgHom_le_norm hcont μ f

/-- The full group C⋆-seminorm is submultiplicative for convolution. -/
theorem fullSeminorm_mul_le (f g : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (f * g) ≤ fullSeminorm G μ f * fullSeminorm G μ g :=
  (fullSeminorm_le_iff (mul_nonneg (apply_nonneg _ f) (apply_nonneg _ g))).2
    fun _ _ _ _ _ hU hcont => by
      rw [map_mul]
      exact (norm_mul_le _ _).trans <|
        mul_le_mul (norm_integratedStarAlgHom_le_fullSeminorm hU hcont f)
          (norm_integratedStarAlgHom_le_fullSeminorm hU hcont g) (norm_nonneg _) (apply_nonneg _ f)

/-- The full group C⋆-seminorm is invariant under the modular-weighted involution. -/
@[simp] theorem fullSeminorm_star (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f) = fullSeminorm G μ f := by
  have key (g : GroupConvolutionAlgebra G μ) : fullSeminorm G μ (star g) ≤ fullSeminorm G μ g :=
    (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun _ _ _ _ _ hU hcont => by
      rw [map_star, _root_.norm_star]; exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (key f) (by simpa using key (star f))

/-- The full group C⋆-seminorm satisfies the C⋆-identity `‖f⋆ * f‖ᵤ = ‖f‖ᵤ²`. -/
theorem fullSeminorm_star_mul_self (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (star f * f) = fullSeminorm G μ f * fullSeminorm G μ f := by
  refine le_antisymm ((fullSeminorm_mul_le _ _).trans_eq (by rw [fullSeminorm_star])) ?_
  have hsqrt : fullSeminorm G μ f ≤ √(fullSeminorm G μ (star f * f)) :=
    (fullSeminorm_le_iff (Real.sqrt_nonneg _)).2 fun _ _ _ _ _ hU hcont =>
      Real.le_sqrt_of_sq_le <| by
        rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
        exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont _
  exact (mul_le_mul hsqrt hsqrt (apply_nonneg _ f) (Real.sqrt_nonneg _)).trans_eq
    (Real.mul_self_sqrt (apply_nonneg _ _))

/-- The full group C⋆-seminorm is definite for every left Haar measure `μ` (without regularity
assumptions on `μ`, via comparison with `Measure.haar` and the left regular representation). -/
@[simp] theorem fullSeminorm_eq_zero_iff {f : GroupConvolutionAlgebra G μ} :
    fullSeminorm G μ f = 0 ↔ f = 0 := by
  refine ⟨fun hf => CStarAction.ConvolutionAlgebra.ext ?_, fun hf => hf ▸ map_zero _⟩
  have hU := (Measure.haar : Measure G).isUnitary_leftRegular (𝕜 := ℂ) (E := ℂ)
  have hcont := (Measure.haar : Measure G).continuous_leftRegular_apply
    (𝕜 := ℂ) (E := ℂ) 2 ENNReal.ofNat_ne_top
  have hzero : hU.integratedOperator hcont μ f.ofConv = 0 := by
    rw [← hU.integratedStarAlgHom_apply, ← norm_le_zero_iff, ← hf]
    exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont f
  rw [hU.integratedOperator_eq_haarScalarFactor_smul hcont μ Measure.haar] at hzero
  have hhaar := (smul_eq_zero.1 hzero).resolve_left <|
    NNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ Measure.haar).ne'
  exact (Measure.haar : Measure G).injective_integratedOperator_leftRegular
    (by simpa only [CStarAction.ConvolutionAlgebra.ofConv_zero, map_zero] using hhaar)

/-- Left translation preserves the full group C⋆-seminorm. -/
@[simp] theorem fullSeminorm_translateLIE (r : G) (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G μ (CStarAction.ConvolutionAlgebra.translateLIE r f) = fullSeminorm G μ f := by
  have h (t : G) (g : GroupConvolutionAlgebra G μ) :
      fullSeminorm G μ (CStarAction.ConvolutionAlgebra.translateLIE t g) ≤ fullSeminorm G μ g :=
    (fullSeminorm_le_iff (apply_nonneg _ _)).2 fun _ _ _ _ _ hU hcont => by
      rw [hU.integratedStarAlgHom_translateLIE, CStarRing.norm_mem_unitary_mul _ (hU.mem_unitary t)]
      exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (h r f) (by simpa using h r⁻¹ (CStarAction.ConvolutionAlgebra.translateLIE r f))

end FullSeminorm

/-! ### Independence of the choice of Haar measure on the group convolution algebra -/

section HaarMeasureEquiv

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

omit [LocallyCompactSpace G] in
private theorem smul_haarScalarFactor_smul (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] (f : C_c(G, ℂ)) :
    ((Measure.haarScalarFactor ν κ : ℝ) : ℂ) • (((Measure.haarScalarFactor μ ν : ℝ) : ℂ) • f) =
      ((Measure.haarScalarFactor μ κ : ℝ) : ℂ) • f := by
  ext s; simp [smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul,
    mul_comm (Measure.haarScalarFactor ν κ), ← Measure.haarScalarFactor_eq_mul μ ν κ]

variable (G) in
/-- Rescaling by `Measure.haarScalarFactor μ ν` identifies `GroupConvolutionAlgebra G μ` with
`GroupConvolutionAlgebra G ν` as a complex ⋆-algebra for any two left Haar measures `μ` and `ν`. -/
def haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    GroupConvolutionAlgebra G μ ≃⋆ₐ[ℂ] GroupConvolutionAlgebra G ν where
  toFun f := .toConv (((Measure.haarScalarFactor μ ν : ℝ) : ℂ) • f.ofConv)
  invFun f := .toConv (((Measure.haarScalarFactor ν μ : ℝ) : ℂ) • f.ofConv)
  left_inv f := CStarAction.ConvolutionAlgebra.ext <|
    (smul_haarScalarFactor_smul μ ν μ f.ofConv).trans (by simp)
  right_inv f := CStarAction.ConvolutionAlgebra.ext <|
    (smul_haarScalarFactor_smul ν μ ν f.ofConv).trans (by simp)
  map_add' f g := CStarAction.ConvolutionAlgebra.ext <| by simp [smul_add]
  map_smul' z f := CStarAction.ConvolutionAlgebra.ext <|
    CompactlySupportedContinuousMap.ext fun _ => by simp [smul_eq_mul]; ring
  map_mul' f g := CStarAction.ConvolutionAlgebra.ext <|
      CompactlySupportedContinuousMap.ext fun s => by
    simp only [CStarAction.ConvolutionAlgebra.ofConv_mul, CStarAction.convolution_apply,
      CStarAction.trivial_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ ν (by fun_prop)
      (f.ofConv.hasCompactSupport.mono fun _ hr hz => hr (by simp [hz])), Complex.real_smul]
    simp_rw [mul_mul_mul_comm ((Measure.haarScalarFactor μ ν : ℝ) : ℂ)]
    rw [integral_const_mul]; ring
  map_star' f := CStarAction.ConvolutionAlgebra.ext <|
      CompactlySupportedContinuousMap.ext fun s => by
    simp [CStarAction.twistedInvolution_apply, smul_eq_mul, Complex.real_smul]; ring

@[simp] theorem ofConv_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    (haarMeasureEquiv G μ ν f).ofConv = ((Measure.haarScalarFactor μ ν : ℝ) : ℂ) • f.ofConv := (rfl)
theorem ofConv_haarMeasureEquiv_apply (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) (s : G) :
    (haarMeasureEquiv G μ ν f).ofConv s =
      ((Measure.haarScalarFactor μ ν : ℝ) : ℂ) * f.ofConv s := (rfl)
@[simp] theorem haarMeasureEquiv_symm (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).symm = haarMeasureEquiv G ν μ := (rfl)
@[simp] theorem haarMeasureEquiv_refl (μ : Measure G) [μ.IsHaarMeasure] :
    haarMeasureEquiv G μ μ = StarAlgEquiv.refl ℂ (GroupConvolutionAlgebra G μ) := by
  ext f : 1; apply CStarAction.ConvolutionAlgebra.ext; ext s; simp
@[simp] theorem haarMeasureEquiv_apply_haarMeasureEquiv (μ ν κ : Measure G) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] [κ.IsHaarMeasure] (f : GroupConvolutionAlgebra G μ) :
    haarMeasureEquiv G ν κ (haarMeasureEquiv G μ ν f) = haarMeasureEquiv G μ κ f :=
  CStarAction.ConvolutionAlgebra.ext (smul_haarScalarFactor_smul μ ν κ f.ofConv)
theorem haarMeasureEquiv_trans (μ ν κ : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    [κ.IsHaarMeasure] :
    (haarMeasureEquiv G μ ν).trans (haarMeasureEquiv G ν κ) = haarMeasureEquiv G μ κ :=
  StarAlgEquiv.ext (haarMeasureEquiv_apply_haarMeasureEquiv μ ν κ)

/-- Rescaling by `Measure.haarScalarFactor μ ν` is an `L¹` isometry. -/
@[simp] theorem norm_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) : ‖haarMeasureEquiv G μ ν f‖ = ‖f‖ := by
  rw [CStarAction.ConvolutionAlgebra.norm_eq_integral_norm,
    CStarAction.ConvolutionAlgebra.norm_eq_integral_norm,
    TauCeti.integral_isMulLeftInvariant_eq_haarScalarFactor_smul μ ν
      (f := fun s => ‖f.ofConv s‖) (by fun_prop) f.ofConv.hasCompactSupport.norm,
    smul_eq_mul, ← integral_const_mul]
  congr 1 with s; simp [abs_of_nonneg (NNReal.coe_nonneg _)]

@[simp] theorem translateLIE_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (r : G) (f : GroupConvolutionAlgebra G μ) :
    CStarAction.ConvolutionAlgebra.translateLIE r (haarMeasureEquiv G μ ν f) =
      haarMeasureEquiv G μ ν (CStarAction.ConvolutionAlgebra.translateLIE r f) :=
  CStarAction.ConvolutionAlgebra.ext <| CompactlySupportedContinuousMap.ext fun _ => by simp

/-- Rescaling by `haarMeasureEquiv` intertwines `integratedStarAlgHom` across Haar measures. -/
theorem _root_.ContRepresentation.IsUnitary.integratedStarAlgHom_haarMeasureEquiv {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : ContRepresentation ℂ G H} (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] (f : GroupConvolutionAlgebra G μ) :
    hU.integratedStarAlgHom hcont ν (haarMeasureEquiv G μ ν f) =
      hU.integratedStarAlgHom hcont μ f := by
  rw [hU.integratedStarAlgHom_apply, ofConv_haarMeasureEquiv, map_smul, Complex.coe_smul,
    hU.integratedStarAlgHom_apply, hU.integratedOperator_eq_haarScalarFactor_smul hcont μ ν]

/-- `haarMeasureEquiv` preserves the universal group C⋆-seminorm. -/
@[simp] theorem fullSeminorm_haarMeasureEquiv (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (f : GroupConvolutionAlgebra G μ) :
    fullSeminorm G ν (haarMeasureEquiv G μ ν f) = fullSeminorm G μ f := by
  have h {α β : Measure G} [α.IsHaarMeasure] [β.IsHaarMeasure] (g : GroupConvolutionAlgebra G α) :
      fullSeminorm G β (haarMeasureEquiv G α β g) ≤ fullSeminorm G α g :=
    (fullSeminorm_le_iff (apply_nonneg _ g)).2 fun H _ _ _ U hU hcont => by
      rw [hU.integratedStarAlgHom_haarMeasureEquiv hcont α β]
      exact norm_integratedStarAlgHom_le_fullSeminorm hU hcont g
  exact le_antisymm (h f) (by simpa using h (α := ν) (β := μ) (haarMeasureEquiv G μ ν f))

end HaarMeasureEquiv
end TauCeti.GroupConvolutionAlgebra

end
