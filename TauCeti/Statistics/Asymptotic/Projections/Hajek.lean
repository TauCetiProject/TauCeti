/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.Lp.Pi
import TauCeti.MeasureTheory.Integral.Pi

/-!
# The Hájek projection

Let `T` be a real statistic of independent coordinates `Xᵢ` with laws `P i`, indexed by a finite
type `ι`. Its Hájek projection is
`T̂ = ∑ᵢ E(T | Xᵢ) - (|ι| - 1) E T`,
where the conditional expectation `E(T | Xᵢ = a)` is written as the integral of
`y ↦ T (Function.update y i a)` under the product law, that is with the coordinates other than
`i` integrated out.

For square-integrable `T`, the residual `T - T̂` is orthogonal in `L²` to every sum `∑ᵢ gᵢ(Xᵢ)`
of square-integrable functions of one coordinate each. For nonempty `ι` these sums contain the
constants and `T̂` is one of them, so `T̂` is the `L²` projection of `T` onto the closed space of
such sums. For empty `ι` that space is `{0}` while the formula gives `T̂ = E T`, so the
projection statement needs a nonempty index type; the orthogonality holds in all cases.

## Main results

* `TauCeti.hajekProjection`: the Hájek projection.
* `TauCeti.hajekProjection_eq_integral_add_sum`: `T̂ = E T + ∑ᵢ (E(T | Xᵢ) - E T)`.
* `TauCeti.hajekProjection_const`, `TauCeti.hajekProjection_const_mul`: the projection of a
  constant, and homogeneity in the statistic.
* `TauCeti.hajekProjection_add`, `TauCeti.hajekProjection_sub`, `TauCeti.hajekProjection_sub_const`:
  additivity on integrable statistics, almost everywhere (the partial integrals at a point are
  integrals of sections, which are integrable only almost everywhere).
* `TauCeti.integral_hajekProjection`: `E T̂ = E T` for integrable `T`.
* `TauCeti.hajekProjection_sum_comp_eval`: a sum of integrable functions of one coordinate each
  is its own Hájek projection.
* `TauCeti.integral_hajekProjection_mul_comp_eval`: `T` and `T̂` have the same inner product with
  every square-integrable function of one coordinate.
* `TauCeti.integral_sub_hajekProjection_mul_eq_zero`: the residual `T - T̂` is orthogonal to
  every sum of square-integrable functions of one coordinate each.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 11.10.
-/

public section

open MeasureTheory ProbabilityTheory Function

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- The **Hájek projection** of a statistic `T` of independent coordinates with laws `P i`:
`T̂ x = ∑ᵢ E(T | Xᵢ = xᵢ) - (|ι| - 1) E T`, where `E(T | Xᵢ = a)` is the integral of
`y ↦ T (Function.update y i a)` under `Measure.pi P`. -/
noncomputable def hajekProjection (P : ∀ i, Measure (α i)) (T : (∀ i, α i) → ℝ)
    (x : ∀ i, α i) : ℝ :=
  ∑ i, ∫ y, T (update y i (x i)) ∂(Measure.pi P) -
    (Fintype.card ι - 1 : ℝ) * ∫ y, T y ∂(Measure.pi P)

/-- The defining formula of `hajekProjection`. -/
theorem hajekProjection_def (P : ∀ i, Measure (α i)) (T : (∀ i, α i) → ℝ) (x : ∀ i, α i) :
    hajekProjection P T x = ∑ i, ∫ y, T (update y i (x i)) ∂(Measure.pi P) -
      (Fintype.card ι - 1 : ℝ) * ∫ y, T y ∂(Measure.pi P) :=
  (rfl)

/-- The centred form of the Hájek projection: `T̂ = E T + ∑ᵢ (E(T | Xᵢ) - E T)`. -/
theorem hajekProjection_eq_integral_add_sum (P : ∀ i, Measure (α i)) (T : (∀ i, α i) → ℝ)
    (x : ∀ i, α i) :
    hajekProjection P T x = ∫ y, T y ∂(Measure.pi P) +
      ∑ i, (∫ y, T (update y i (x i)) ∂(Measure.pi P) - ∫ y, T y ∂(Measure.pi P)) := by
  rw [hajekProjection_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- For an empty index type the Hájek projection is the constant `E T`. -/
@[simp]
theorem hajekProjection_of_isEmpty [IsEmpty ι] (P : ∀ i, Measure (α i)) (T : (∀ i, α i) → ℝ)
    (x : ∀ i, α i) : hajekProjection P T x = ∫ y, T y ∂(Measure.pi P) := by
  simp [hajekProjection_eq_integral_add_sum]

/-- The Hájek projection of a constant `c` is the constant `∫ c d(Measure.pi P)`; under
probability laws this is `c`. -/
@[simp]
theorem hajekProjection_const (P : ∀ i, Measure (α i)) (c : ℝ) (x : ∀ i, α i) :
    hajekProjection P (fun _ ↦ c) x = (Measure.pi P).real Set.univ * c := by
  simp only [hajekProjection_def, integral_const, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- The Hájek projection commutes with multiplication by a constant. -/
@[simp]
theorem hajekProjection_const_mul (P : ∀ i, Measure (α i)) (c : ℝ) (T : (∀ i, α i) → ℝ)
    (x : ∀ i, α i) : hajekProjection P (fun y ↦ c * T y) x = c * hajekProjection P T x := by
  simp only [hajekProjection_def, integral_const_mul, ← Finset.mul_sum]
  ring

/-- The Hájek projection is additive, almost everywhere, on integrable statistics. -/
theorem hajekProjection_add (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T S : (∀ i, α i) → ℝ} (hT : Integrable T (Measure.pi P)) (hS : Integrable S (Measure.pi P)) :
    hajekProjection P (T + S) =ᵐ[Measure.pi P] hajekProjection P T + hajekProjection P S := by
  filter_upwards [ae_forall_integrable_comp_update_eval P hT,
    ae_forall_integrable_comp_update_eval P hS] with x hxT hxS
  simp only [hajekProjection_def, Pi.add_apply, integral_add hT hS, integral_add (hxT _) (hxS _),
    Finset.sum_add_distrib]
  ring

/-- The Hájek projection is subtractive, almost everywhere, on integrable statistics. -/
theorem hajekProjection_sub (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T S : (∀ i, α i) → ℝ} (hT : Integrable T (Measure.pi P)) (hS : Integrable S (Measure.pi P)) :
    hajekProjection P (T - S) =ᵐ[Measure.pi P] hajekProjection P T - hajekProjection P S := by
  filter_upwards [ae_forall_integrable_comp_update_eval P hT,
    ae_forall_integrable_comp_update_eval P hS] with x hxT hxS
  simp only [hajekProjection_def, Pi.sub_apply, integral_sub hT hS, integral_sub (hxT _) (hxS _),
    Finset.sum_sub_distrib]
  ring

/-- Centring an integrable statistic by a constant `c` centres its Hájek projection by `c`, almost
everywhere: the Hájek projection of `Uₙ - θ` is that of `Uₙ`, minus `θ`. -/
theorem hajekProjection_sub_const (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T : (∀ i, α i) → ℝ} (hT : Integrable T (Measure.pi P)) (c : ℝ) :
    hajekProjection P (fun y ↦ T y - c) =ᵐ[Measure.pi P] fun x ↦ hajekProjection P T x - c := by
  filter_upwards [hajekProjection_sub P hT (integrable_const c)] with x hx
  rw [Pi.sub_apply, hajekProjection_const, probReal_univ, one_mul] at hx
  exact hx

/-- **The mean of the Hájek projection.** For an integrable statistic `T` of independent
coordinates, `E T̂ = E T`. -/
theorem integral_hajekProjection (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T : (∀ i, α i) → ℝ} (hT : Integrable T (Measure.pi P)) :
    ∫ x, hajekProjection P T x ∂(Measure.pi P) = ∫ x, T x ∂(Measure.pi P) := by
  have hc (i : ι) : Integrable (fun x : ∀ i, α i ↦ ∫ y, T (update y i (x i)) ∂(Measure.pi P))
      (Measure.pi P) :=
    (measurePreserving_eval P i).integrable_comp_of_integrable (integrable_integral_update P i hT)
  -- Each conditional expectation `E(T | Xᵢ)` has mean `E T`.
  have hmean (i : ι) : ∫ x, ∫ y, T (update y i (x i)) ∂(Measure.pi P) ∂(Measure.pi P) =
      ∫ x, T x ∂(Measure.pi P) := by
    rw [integral_comp_eval (integrable_integral_update P i hT).aestronglyMeasurable,
      integral_integral_update P i hT]
  rw [funext (hajekProjection_def P T), integral_sub (integrable_finsetSum _ fun i _ ↦ hc i)
    (integrable_const _), integral_finsetSum _ fun i _ ↦ hc i]
  simp only [hmean, integral_const, probReal_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, smul_eq_mul]
  ring

/-- A sum of integrable functions of one coordinate each is its own Hájek projection. -/
theorem hajekProjection_sum_comp_eval (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] {f : ∀ i, α i → ℝ} (hf : ∀ i, Integrable (f i) (P i))
    (x : ∀ i, α i) :
    hajekProjection P (fun y ↦ ∑ i, f i (y i)) x = ∑ i, f i (x i) := by
  have hev : ∀ j, Integrable (fun y : ∀ i, α i ↦ f j (y j)) (Measure.pi P) := fun j ↦
    (measurePreserving_eval P j).integrable_comp_of_integrable (hf j)
  have hint : ∀ i j, Integrable (fun y : ∀ i, α i ↦ f j (update y i (x i) j)) (Measure.pi P) := by
    intro i j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simpa [update_of_ne hji] using hev j
  -- Integrating out every coordinate but `i` leaves `f i (x i)` and the means of the others.
  have hterm : ∀ i j, ∫ y, f j (update y i (x i) j) ∂(Measure.pi P) =
      ∫ a, f j a ∂(P j) + if j = i then f j (x j) - ∫ a, f j a ∂(P j) else 0 := by
    intro i j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji, integral_comp_eval (hf j).aestronglyMeasurable]
  simp_rw [hajekProjection_eq_integral_add_sum, integral_finsetSum _ fun j _ ↦ hint _ j,
    integral_finsetSum _ fun j _ ↦ hev j, hterm, Finset.sum_add_distrib,
    integral_comp_eval (hf _).aestronglyMeasurable]
  simp [Finset.sum_sub_distrib]

/-- The Hájek projection of a square-integrable statistic of independent coordinates is
square-integrable. -/
theorem memLp_hajekProjection (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    {T : (∀ i, α i) → ℝ} (hT : MemLp T 2 (Measure.pi P)) :
    MemLp (hajekProjection P T) 2 (Measure.pi P) := by
  have hc : ∀ j, MemLp (fun x : ∀ i, α i ↦ ∫ y, T (update y j (x j)) ∂(Measure.pi P) -
      ∫ y, T y ∂(Measure.pi P)) 2 (Measure.pi P) := fun j ↦
    ((memLp_integral_update P hT j).sub (memLp_const _)).comp_measurePreserving
      (measurePreserving_eval P j)
  have h := (memLp_const (∫ y, T y ∂(Measure.pi P))).add (memLp_finsetSum' Finset.univ
    fun j _ ↦ hc j)
  convert h using 1
  ext x
  simp [hajekProjection_eq_integral_add_sum]

/-- `T` and its Hájek projection have the same inner product with every square-integrable
function of one coordinate: `E(T̂ g(Xᵢ)) = E(T g(Xᵢ))`. -/
theorem integral_hajekProjection_mul_comp_eval (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] {T : (∀ i, α i) → ℝ} (hT : MemLp T 2 (Measure.pi P))
    (i : ι) {g : α i → ℝ} (hg : MemLp g 2 (P i)) :
    ∫ x, hajekProjection P T x * g (x i) ∂(Measure.pi P) =
      ∫ x, T x * g (x i) ∂(Measure.pi P) := by
  set μ := Measure.pi P
  set m := ∫ y, T y ∂μ
  -- The centred conditional expectations `d j a = E(T | Xⱼ = a) - E T`.
  set d : ∀ j, α j → ℝ := fun j a ↦ ∫ y, T (update y j a) ∂μ - m with hd
  have hcL : ∀ j, MemLp (fun a ↦ ∫ y, T (update y j a) ∂μ) 2 (P j) :=
    memLp_integral_update P hT
  have hdL : ∀ j, MemLp (d j) 2 (P j) := fun j ↦ (hcL j).sub (memLp_const m)
  have hgx : MemLp (fun x : ∀ i, α i ↦ g (x i)) 2 μ :=
    hg.comp_measurePreserving (measurePreserving_eval P i)
  have hdx : ∀ j, MemLp (fun x : ∀ i, α i ↦ d j (x j)) 2 μ := fun j ↦
    (hdL j).comp_measurePreserving (measurePreserving_eval P j)
  have hTg : Integrable (fun x ↦ T x * g (x i)) μ := hT.integrable_mul hgx
  have hdg : ∀ j, Integrable (fun x ↦ d j (x j) * g (x i)) μ := fun j ↦
    (hdx j).integrable_mul hgx
  -- Each conditional expectation has mean `E T`, so the `d j` are centred.
  have hdmean : ∀ j, ∫ a, d j a ∂(P j) = 0 := fun j ↦ by
    rw [hd, integral_sub ((hcL j).integrable one_le_two) (integrable_const m),
      integral_integral_update P j (hT.integrable one_le_two)]
    simp [m, μ]
  -- Only the term `j = i` of `∑ⱼ d j (xⱼ)` correlates with `g (xᵢ)`.
  have hsum : ∫ x, ∑ j, d j (x j) * g (x i) ∂μ =
      ∫ x, T x * g (x i) ∂μ - m * ∫ a, g a ∂(P i) := by
    rw [integral_finsetSum _ fun j _ ↦ hdg j, Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
    · have hcg : Integrable (fun a ↦ (∫ y, T (update y i a) ∂μ) * g a) (P i) :=
        (hcL i).integrable_mul hg
      rw [integral_comp_eval (f := fun a ↦ d i a * g a)
          ((hdL i).aestronglyMeasurable.mul hg.aestronglyMeasurable),
        integral_mul_comp_eval_eq P i hTg, ← integral_const_mul,
        ← integral_sub hcg ((hg.integrable one_le_two).const_mul m)]
      simp [hd, sub_mul]
    · rw [integral_comp_eval_mul_comp_eval P hji (hdL j).aestronglyMeasurable
        hg.aestronglyMeasurable, hdmean, zero_mul]
  calc ∫ x, hajekProjection P T x * g (x i) ∂μ
      = ∫ x, (m * g (x i) + ∑ j, d j (x j) * g (x i)) ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [hajekProjection_eq_integral_add_sum, add_mul, Finset.sum_mul]
    _ = ∫ x, T x * g (x i) ∂μ := by
        rw [integral_add ((hgx.integrable one_le_two).const_mul m)
            (integrable_finsetSum _ fun j _ ↦ hdg j),
          integral_const_mul, hsum, integral_comp_eval hg.aestronglyMeasurable]
        ring

/-- **Orthogonality of the Hájek projection** (van der Vaart, Lemma 11.10). For a
square-integrable statistic `T` of independent coordinates, the residual `T - T̂` is orthogonal
in `L²` to every sum `∑ᵢ gᵢ(Xᵢ)` of square-integrable functions of one coordinate each. For a
nonempty index type these sums contain the constants and `T̂` is one of them, so `T̂` is the `L²`
projection of `T` onto their closed span. -/
theorem integral_sub_hajekProjection_mul_eq_zero (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] (T : (∀ i, α i) → ℝ) (hT : MemLp T 2 (Measure.pi P))
    (g : ∀ i, α i → ℝ) (hg : ∀ i, MemLp (g i) 2 (P i)) :
    ∫ x, (T x - hajekProjection P T x) * ∑ i, g i (x i) ∂(Measure.pi P) = 0 := by
  have hgx : ∀ i, MemLp (fun x : ∀ i, α i ↦ g i (x i)) 2 (Measure.pi P) := fun i ↦
    (hg i).comp_measurePreserving (measurePreserving_eval P i)
  have hres : ∀ i, Integrable (fun x ↦ (T x - hajekProjection P T x) * g i (x i))
      (Measure.pi P) := fun i ↦ (hT.sub (memLp_hajekProjection P hT)).integrable_mul (hgx i)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ hres i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hTg : Integrable (fun x ↦ T x * g i (x i)) (Measure.pi P) := hT.integrable_mul (hgx i)
  have hHg : Integrable (fun x ↦ hajekProjection P T x * g i (x i)) (Measure.pi P) :=
    (memLp_hajekProjection P hT).integrable_mul (hgx i)
  simp_rw [sub_mul]
  rw [integral_sub hTg hHg, integral_hajekProjection_mul_comp_eval P hT i (hg i), sub_self]

end TauCeti
