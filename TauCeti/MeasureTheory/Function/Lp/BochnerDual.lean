/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
public import TauCeti.MeasureTheory.Function.Lp.Linfty.Sigma
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Norming

/-!
# The integral pairing between Bochner spaces

For Hölder conjugate exponents `1 ≤ p, q ≤ ∞` and a normed space `X` over `𝕜 = ℝ` or `ℂ`, the
integral pairing `⟨f, g⟩ = ∫ g s (f s) dμ` of `f ∈ Lᵖ(μ; X)` with `g ∈ L^q(μ; X⋆)` gives the
canonical contraction

`TauCeti.bochnerDualMap 𝕜 X μ p q : L^q(μ; X⋆) →L[𝕜] (Lᵖ(μ; X))⋆`.

It is Mathlib's bilinear `Lp` pairing `ContinuousLinearMap.lpPairing` of the evaluation map
`X⋆ × X → 𝕜`, with the arguments ordered so that `L^q(μ; X⋆)` acts on `Lᵖ(μ; X)`. The pairing is
bilinear, also over `ℂ`.

The main results compute norms through this pairing.

* `TauCeti.norm_bochnerDualMap_of_ne_top` and `TauCeti.norm_bochnerDualMap`: the map is an
  isometry when `q < ∞`, on an arbitrary measure space, and for all conjugate exponents on a
  σ-finite measure space. In particular its range is closed.
* `TauCeti.norm_bochnerDualMap_linftySigma`: at `p = 1`, `q = ∞`, the map is isometric on an
  arbitrary measure space when restricted to the support-restricted space `TauCeti.linftySigma`.
* `TauCeti.norm_le_of_dual_pairing_bound_of_ne_top` and `TauCeti.norm_le_of_dual_pairing_bound`:
  conversely, the functions in `L^q(μ; X⋆)` norm `Lᵖ(μ; X)`, when `p < ∞` on an arbitrary measure
  space and for all conjugate exponents on a σ-finite measure space.
* `TauCeti.bochnerDualMap_apply_compLp`: naturality of the pairing for bounded linear maps of the
  target and their adjoints.

## Implementation notes

The norm computations reduce to the scalar norming theorems for `Lᵖ(μ)` against simple test
functions, such as `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`. The strongly
measurable almost norming vectors of
`MeasureTheory.AEStronglyMeasurable.exists_stronglyMeasurable_norming` turn `g` into the scalar
function `s ↦ g s (x s)`, whose `L^q` norm is almost that of `g` and is normed by the scalar
test functions `φ` through the vector test functions `φ • x`. The norming statements choose
almost norming functionals of `f` in the same way, through the embedding into the bidual.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Proposition 1.3.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {𝕜 S X : Type*} [RCLike 𝕜] [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [q.HolderConjugate p]

variable (𝕜 X μ p q) in
/-- The integral pairing `g ↦ (f ↦ ∫ g s (f s) dμ)` from `L^q(μ; X⋆)` to the continuous dual of
`Lᵖ(μ; X)`, for Hölder conjugate exponents `p` and `q`. This abbreviation of Mathlib's bilinear
pairing `ContinuousLinearMap.lpPairing` of the evaluation map only fixes the order of the
arguments. -/
noncomputable abbrev bochnerDualMap : Lp (StrongDual 𝕜 X) q μ →L[𝕜] StrongDual 𝕜 (Lp X p μ) :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ q p

/-- The integral formula for the pairing of `g ∈ L^q(μ; X⋆)` with `f ∈ Lᵖ(μ; X)`. -/
@[simp]
theorem bochnerDualMap_apply (g : Lp (StrongDual 𝕜 X) q μ) (f : Lp X p μ) :
    bochnerDualMap 𝕜 X μ p q g f = ∫ s, g s (f s) ∂μ := by
  simp [ContinuousLinearMap.lpPairing_eq_integral]

/-- The integral pairing is a contraction: Hölder's inequality. -/
theorem norm_bochnerDualMap_le (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ ≤ ‖g‖ :=
  ((bochnerDualMap 𝕜 X μ p q).le_opNorm g).trans <| mul_le_of_le_one_left (norm_nonneg g) <|
    (ContinuousLinearMap.norm_lpPairing_le _).trans ContinuousLinearMap.norm_id_le

/-- **Naturality of the integral pairing.** For a bounded linear map `T : X →L[𝕜] Y`, pairing
`g ∈ L^q(μ; Y⋆)` with `T ∘ f` is pairing the pullback `s ↦ g s ∘L T` with `f ∈ Lᵖ(μ; X)`. -/
theorem bochnerDualMap_apply_compLp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (g : Lp (StrongDual 𝕜 Y) q μ) (f : Lp X p μ) :
    bochnerDualMap 𝕜 Y μ p q g (T.compLp f) =
      bochnerDualMap 𝕜 X μ p q (((ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip T).compLp g) f := by
  simp only [bochnerDualMap_apply]
  refine integral_congr_ae ?_
  filter_upwards [T.coeFn_compLp f, ((ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip T).coeFn_compLp g]
    with s hf hg
  simp [hf, hg]

/-- The scalar norming principle for `h ∈ L^r(μ)` against simple test functions in the conjugate
`L^{r'}(μ)`, in the form supplied by
`MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le` and its variants. -/
private def ScalarNorming (μ : Measure S) (r r' : ℝ≥0∞) (h : S → 𝕜) : Prop :=
  ∀ C : ℝ≥0∞, (∀ φ : SimpleFunc S 𝕜, MemLp φ r' μ → ‖∫ s, h s * φ s ∂μ‖ₑ ≤ C * eLpNorm φ r' μ) →
    eLpNorm h r μ ≤ C

/-- A scalar function `φ ∈ Lʳ(μ)` times a strongly measurable field `x` of vectors of norm at
most one lies in `Lʳ(μ; E)`, with norm at most that of `φ`. These are the test functions of the
norming arguments below. -/
private theorem memLp_smul_and_eLpNorm_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {x : S → E} (hx : StronglyMeasurable x) (hx1 : ∀ s, ‖x s‖ ≤ 1) {r : ℝ≥0∞}
    {φ : S → 𝕜} (hφ : MemLp φ r μ) :
    MemLp (fun s ↦ φ s • x s) r μ ∧ eLpNorm (fun s ↦ φ s • x s) r μ ≤ eLpNorm φ r μ := by
  have hle : ∀ s, ‖φ s • x s‖ ≤ ‖φ s‖ := fun s ↦ by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx1 s)
  have hm : AEStronglyMeasurable (fun s ↦ φ s • x s) μ :=
    hφ.aestronglyMeasurable.smul hx.aestronglyMeasurable
  exact ⟨hφ.of_le hm (ae_of_all _ hle), eLpNorm_mono hm hle⟩

/-- The core of the isometry theorems for `bochnerDualMap`: if the scalar norming principle for
`L^q(μ)` holds for scalar functions dominated by `‖g‖`, then the norm of `g ∈ L^q(μ; X⋆)` is at
most that of the functional `f ↦ ∫ g s (f s) dμ`. -/
private theorem eLpNorm_le_enorm_bochnerDualMap (g : Lp (StrongDual 𝕜 X) q μ)
    (hnorm : ∀ h : S → 𝕜, MemLp h q μ → (∀ᵐ s ∂μ, ‖h s‖ ≤ ‖g s‖) → ScalarNorming μ q p h) :
    eLpNorm g q μ ≤ ‖bochnerDualMap 𝕜 X μ p q g‖ₑ := by
  set Λ := bochnerDualMap 𝕜 X μ p q g
  -- Test `g` against strongly measurable fields `x` of vectors of norm at most one.
  refine (Lp.aestronglyMeasurable g).eLpNorm_le_of_forall_eLpNorm_apply_le fun x hx hx1 ↦ ?_
  have hle : ∀ s, ‖g s (x s)‖ ≤ ‖g s‖ := fun s ↦
    ((g s).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hx1 s))
  have hh : MemLp (fun s ↦ g s (x s)) q μ :=
    (Lp.memLp g).of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      (Lp.aestronglyMeasurable g) hx.aestronglyMeasurable) (ae_of_all _ hle)
  refine hnorm _ hh (ae_of_all _ hle) _ fun φ hφ ↦ ?_
  -- The scalar test function `φ` pairs with `s ↦ g s (x s)` as `φ • x` pairs with `g`.
  obtain ⟨hf, hfφ⟩ := memLp_smul_and_eLpNorm_smul_le hx hx1 hφ
  calc ‖∫ s, g s (x s) * φ s ∂μ‖ₑ = ‖Λ (hf.toLp fun s ↦ φ s • x s)‖ₑ := by
        rw [bochnerDualMap_apply]
        congr 1
        refine integral_congr_ae (hf.coeFn_toLp.mono fun s hs ↦ ?_)
        simp [hs, mul_comm]
    _ ≤ ‖Λ‖ₑ * ‖hf.toLp fun s ↦ φ s • x s‖ₑ := Λ.le_opENorm _
    _ ≤ ‖Λ‖ₑ * eLpNorm φ p μ := by rw [Lp.eNorm_toLp hf]; gcongr

/-- The core of `norm_le_of_dual_pairing_bound_of_ne_top` and `norm_le_of_dual_pairing_bound`:
given the scalar norming principle for `Lᵖ(μ)`, the norm of `f ∈ Lᵖ(μ; X)` is bounded by any bound
of its pairings with `L^q(μ; X⋆)`. -/
private theorem eLpNorm_le_of_enorm_bochnerDualMap_le (f : Lp X p μ)
    (hnorm : ∀ h : S → 𝕜, MemLp h p μ → ScalarNorming μ p q h) {C : ℝ≥0∞}
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ₑ ≤ C * ‖g‖ₑ) :
    eLpNorm f p μ ≤ C := by
  -- Test the image `ι ∘ f` of `f` in the bidual against strongly measurable fields `x` of
  -- functionals of norm at most one.
  set ι := NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)
  have hιf : AEStronglyMeasurable (fun s ↦ ι (f s)) μ :=
    ι.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  refine (eLpNorm_mono (Lp.aestronglyMeasurable f) fun s ↦ (ι.norm_map (f s)).ge).trans <|
    hιf.eLpNorm_le_of_forall_eLpNorm_apply_le fun x hx hx1 ↦ ?_
  have hh : MemLp (fun s ↦ x s (f s)) p μ :=
    (Lp.memLp f).of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hx.aestronglyMeasurable (Lp.aestronglyMeasurable f)) (ae_of_all _ fun s ↦
        ((x s).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hx1 s)))
  refine hnorm _ hh _ fun φ hφ ↦ ?_
  -- The scalar test function `φ` pairs with `s ↦ x s (f s)` as `φ • x` pairs with `f`.
  obtain ⟨hg, hgφ⟩ := memLp_smul_and_eLpNorm_smul_le hx hx1 hφ
  calc ‖∫ s, x s (f s) * φ s ∂μ‖ₑ
      = ‖bochnerDualMap 𝕜 X μ p q (hg.toLp fun s ↦ φ s • x s) f‖ₑ := by
        rw [bochnerDualMap_apply]
        congr 1
        refine integral_congr_ae (hg.coeFn_toLp.mono fun s hs ↦ ?_)
        simp [hs, mul_comm]
    _ ≤ C * ‖hg.toLp fun s ↦ φ s • x s‖ₑ := hbound _
    _ ≤ C * eLpNorm φ q μ := by rw [Lp.eNorm_toLp hg]; gcongr

/-- **The Bochner integral pairing is an isometry for `q < ∞`.** On an arbitrary measure space, for
Hölder conjugate exponents `p` and `q` with `q < ∞`, the functional `f ↦ ∫ g s (f s) dμ` on
`Lᵖ(μ; X)` has norm `‖g‖_q` for every `g ∈ L^q(μ; X⋆)`. -/
theorem norm_bochnerDualMap_of_ne_top (hq : q ≠ ∞) (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ := by
  refine le_antisymm (norm_bochnerDualMap_le g) ?_
  rw [Lp.norm_def, ← toReal_eNorm (bochnerDualMap 𝕜 X μ p q g)]
  exact ENNReal.toReal_mono eNorm_ne_top
    (eLpNorm_le_enorm_bochnerDualMap g fun _ hh _ _ htest ↦
      hh.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top hq htest)

/-- **The Bochner integral pairing is an isometry.** On a σ-finite measure space, for all Hölder
conjugate exponents `p` and `q`, the functional `f ↦ ∫ g s (f s) dμ` on `Lᵖ(μ; X)` has norm
`‖g‖_q` for every `g ∈ L^q(μ; X⋆)`. -/
theorem norm_bochnerDualMap [SigmaFinite μ] (g : Lp (StrongDual 𝕜 X) q μ) :
    ‖bochnerDualMap 𝕜 X μ p q g‖ = ‖g‖ := by
  refine le_antisymm (norm_bochnerDualMap_le g) ?_
  rw [Lp.norm_def, ← toReal_eNorm (bochnerDualMap 𝕜 X μ p q g)]
  exact ENNReal.toReal_mono eNorm_ne_top
    (eLpNorm_le_enorm_bochnerDualMap g fun _ hh _ _ htest ↦
      hh.eLpNorm_le_of_forall_enorm_integral_mul_le htest)

/-- **`L^q(μ; X⋆)` norms `Lᵖ(μ; X)` for `p < ∞`.** On an arbitrary measure space, for Hölder
conjugate exponents `p` and `q` with `p < ∞`, if `‖∫ g s (f s) dμ‖ ≤ C ‖g‖_q` for every
`g ∈ L^q(μ; X⋆)`, then `‖f‖_p ≤ C`. -/
theorem norm_le_of_dual_pairing_bound_of_ne_top (hp : p ≠ ∞) (f : Lp X p μ) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hC
    (eLpNorm_le_of_enorm_bochnerDualMap_le f
      (fun (_ : S → 𝕜) hh _ htest ↦
        hh.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top (q' := q) hp htest) fun g ↦ ?_)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (hbound g)

/-- **`L^q(μ; X⋆)` norms `Lᵖ(μ; X)`.** On a σ-finite measure space, for all Hölder conjugate
exponents `p` and `q`, if `‖∫ g s (f s) dμ‖ ≤ C ‖g‖_q` for every `g ∈ L^q(μ; X⋆)`, then
`‖f‖_p ≤ C`. -/
theorem norm_le_of_dual_pairing_bound [SigmaFinite μ] (f : Lp X p μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : Lp (StrongDual 𝕜 X) q μ, ‖bochnerDualMap 𝕜 X μ p q g f‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hC
    (eLpNorm_le_of_enorm_bochnerDualMap_le f
      (fun (_ : S → 𝕜) hh _ htest ↦ hh.eLpNorm_le_of_forall_enorm_integral_mul_le (q' := q) htest)
      fun g ↦ ?_)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (hbound g)

/-- On an arbitrary measure space, the integral pairing is an isometry for `q < ∞`. -/
theorem isometry_bochnerDualMap_of_ne_top (hq : q ≠ ∞) :
    Isometry (bochnerDualMap 𝕜 X μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_bochnerDualMap_of_ne_top hq)

/-- On a σ-finite measure space, the integral pairing is an isometry. -/
theorem isometry_bochnerDualMap [SigmaFinite μ] : Isometry (bochnerDualMap 𝕜 X μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ norm_bochnerDualMap

/-- On an arbitrary measure space, the integral pairing has closed range for `q < ∞`. -/
theorem isClosed_range_bochnerDualMap_of_ne_top (hq : q ≠ ∞) :
    IsClosed (Set.range (bochnerDualMap 𝕜 X μ p q)) :=
  (isometry_bochnerDualMap_of_ne_top hq).isClosedEmbedding.isClosed_range

/-- On a σ-finite measure space, the integral pairing has closed range. -/
theorem isClosed_range_bochnerDualMap [SigmaFinite μ] :
    IsClosed (Set.range (bochnerDualMap 𝕜 X μ p q)) :=
  isometry_bochnerDualMap.isClosedEmbedding.isClosed_range

/-- **The integral pairing on the support-restricted infinity space.** On an arbitrary measure
space, the functional `f ↦ ∫ g s (f s) dμ` on `L¹(μ; X)` has norm `‖g‖_∞` for every `g` in the
support-restricted space `L∞_σ(μ; X⋆) = TauCeti.linftySigma 𝕜 X⋆ μ`. For the whole native space
`L∞(μ; X⋆)` this fails on a set of infinite measure without subsets of finite positive measure,
on which every integrable function vanishes. -/
theorem norm_bochnerDualMap_linftySigma (g : linftySigma 𝕜 (StrongDual 𝕜 X) μ) :
    ‖bochnerDualMap 𝕜 X μ 1 ∞ (g : Lp (StrongDual 𝕜 X) ∞ μ)‖ = ‖g‖ := by
  refine le_antisymm (norm_bochnerDualMap_le _) ?_
  -- `g` vanishes almost everywhere off a measurable set on which `μ` is σ-finite.
  obtain ⟨t, ht, hvan, hσ⟩ := (mem_linftySigma_iff.1 g.property).exists_set_sigmaFinite
  rw [← Submodule.norm_coe, Lp.norm_def,
    ← toReal_eNorm (bochnerDualMap 𝕜 X μ 1 ∞ (g : Lp (StrongDual 𝕜 X) ∞ μ))]
  refine ENNReal.toReal_mono eNorm_ne_top (eLpNorm_le_enorm_bochnerDualMap _
    fun h hh hle _ htest ↦
      hh.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le_of_restrict_compl ht
        ?_ htest)
  filter_upwards [ae_restrict_of_ae hle, hvan] with s h1 h2
  simpa [h2] using h1

end TauCeti
