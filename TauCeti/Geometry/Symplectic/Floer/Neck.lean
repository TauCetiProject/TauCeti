/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Inserting a cylindrical neck into Hamiltonian perturbation data

Gluing and compactness arguments for inhomogeneous Floer equations deform a domain by stretching
it along a long cylindrical neck. In coordinates `z = (s, t)`, inserting a neck of length `L` at
the line `s = c` replaces a perturbation datum `K` by `K ∘ (σ × id)`, where the *neck-collapsing
map* `σ` is the identity for `s ≤ c`, is constant equal to `c` on `[c, c + L]`, and is the
translation `s ↦ s - L` for `s ≥ c + L`. If `K` is independent of `s` near the line `s = c`, the
stretched datum is again smooth, and it agrees near every point with a translate of `K`.

The energy identity turns curvature bounds into energy bounds, but a pointwise curvature bound
multiplied by the length of an arbitrarily long neck gives no uniform estimate. The point of this
file is that, when `K` is cylindrical near the neck (`K = H_t dt` there), the curvature of the
stretched datum vanishes along the whole neck, so its integrated curvature is controlled by that
of `K` itself, uniformly in the neck length.

The results hold for perturbation data on the product of the domain with a manifold `M` carrying
a two-form, such as a closed symplectic manifold, and the energy estimate uses the energy identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` for a nondegenerate two-form.
The curvature statements for a symplectic vector space are the special case of the constant form
`TauCeti.SymplecticForm.constSmooth`; the energy estimate there is stated separately, through the
vector-space identity `TauCeti.SymplecticForm.integral_floerEnergyDensity`.

## Main definitions

* `TauCeti.Floer.neckCollapse c L`: the neck-collapsing map `σ : ℝ → ℝ`.
* `TauCeti.Floer.neckStretch c L K`: the datum `K ∘ (σ × id)` with a neck of length `L` inserted
  at `s = c`.

## Main results

* `TauCeti.Floer.contMDiff_neckStretch_family`: inserting a neck whose length depends smoothly on
  a parameter, at a line where the datum is independent of `s`, gives a datum that is smooth
  jointly in the parameter, the domain point and the point of the manifold;
  `TauCeti.Floer.contMDiff_uncurry_neckStretch` is the case of a fixed length, and
  `TauCeti.Floer.contDiff_neckStretch_family` and `TauCeti.Floer.contDiff_uncurry_neckStretch`
  are the vector-space cases.
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_neckStretch`: the curvature of the stretched datum
  is the curvature of the original datum pulled back along `σ × id`.
* `TauCeti.SmoothTwoForm.integral_abs_hamiltonianCurvature_neckStretch_le`: for a datum that is
  cylindrical near the neck, the integrated curvature over the stretched rectangle is bounded by
  the integral of any pointwise curvature bound over the original rectangle, uniformly in `L`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_neckStretch_sub_le`:
  consequently the Floer energy over the stretched rectangle differs from its topological part
  (symplectic area plus boundary term) by at most that same constant, for every neck length;
  `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_neckStretch_sub_le` is the same estimate
  for a symplectic vector space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Sections 8 and 9, on perturbation
  data on surfaces with strip-like ends and their compatibility with gluing along long necks.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti

namespace Floer

section NeckCollapse

variable {c L s : ℝ}

/-- The *neck-collapsing map* `σ : ℝ → ℝ` for a neck of length `L` at `c`: it is the identity on
`(-∞, c]`, collapses `[c, c + L]` to `c`, and is the translation `s ↦ s - L` on `[c + L, ∞)`
(for `0 ≤ L`). -/
def neckCollapse (c L s : ℝ) : ℝ :=
  min s c + max (s - (c + L)) 0

theorem neckCollapse_def (c L s : ℝ) : neckCollapse c L s = min s c + max (s - (c + L)) 0 :=
  (rfl)

@[simp]
theorem neckCollapse_of_le (hL : 0 ≤ L) (hs : s ≤ c) : neckCollapse c L s = s := by
  rw [neckCollapse_def, min_eq_left hs, max_eq_right (by linarith), add_zero]

@[simp]
theorem neckCollapse_of_mem_Icc (hs : s ∈ Icc c (c + L)) : neckCollapse c L s = c := by
  rw [neckCollapse_def, min_eq_right hs.1, max_eq_right (by linarith [hs.2]), add_zero]

@[simp]
theorem neckCollapse_of_ge (hL : 0 ≤ L) (hs : c + L ≤ s) : neckCollapse c L s = s - L := by
  rw [neckCollapse_def, min_eq_right (by linarith), max_eq_left (by linarith)]
  ring

/-- A neck of length zero collapses nothing. -/
@[simp]
theorem neckCollapse_zero (c s : ℝ) : neckCollapse c 0 s = s := by
  rcases le_total s c with hs | hs
  · exact neckCollapse_of_le le_rfl hs
  · rw [neckCollapse_of_ge le_rfl (by simpa using hs), sub_zero]

theorem continuous_neckCollapse (c L : ℝ) : Continuous (neckCollapse c L) := by
  unfold neckCollapse
  fun_prop

end NeckCollapse

section NeckStretch

variable {X : Type*} {c L : ℝ}

/-- The datum `K ∘ (σ × id)` obtained from `K` by inserting a neck of length `L` at the line
`s = c`, where `σ = neckCollapse c L`. -/
def neckStretch (c L : ℝ) (K : ℝ × ℝ → X) (z : ℝ × ℝ) : X :=
  K (neckCollapse c L z.1, z.2)

@[simp]
theorem neckStretch_apply (K : ℝ × ℝ → X) (z : ℝ × ℝ) :
    neckStretch c L K z = K (neckCollapse c L z.1, z.2) :=
  (rfl)

/-- Inserting a neck of length zero does not change the datum. -/
@[simp]
theorem neckStretch_zero (c : ℝ) (K : ℝ × ℝ → X) : neckStretch c 0 K = K := by
  funext z
  simp

/-- If `K` is independent of `s` near the line `s = c`, then near every point `z` the stretched
datum agrees with the translate of `K` that moves `z` to `(σ z.1, z.2)`. -/
theorem neckStretch_eventuallyEq (hL : 0 ≤ L) {K : ℝ × ℝ → X}
    (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t)) (z : ℝ × ℝ) :
    neckStretch c L K =ᶠ[𝓝 z] fun w ↦ K (w + (neckCollapse c L z.1 - z.1, 0)) := by
  obtain ⟨s, t⟩ := z
  rcases lt_or_ge s c with hs | hs
  · -- Before the neck, `σ` is the identity near `s`.
    have hev : ∀ᶠ w : ℝ × ℝ in 𝓝 (s, t), w.1 < c :=
      (continuous_fst.tendsto (s, t)).eventually (Iio_mem_nhds hs)
    filter_upwards [hev] with w hw
    simp [neckCollapse_of_le hL hw.le, neckCollapse_of_le hL hs.le, Prod.mk_zero_zero]
  rcases lt_or_ge (c + L) s with hs' | hs'
  · -- After the neck, `σ` is the translation by `-L` near `s`.
    have hev : ∀ᶠ w : ℝ × ℝ in 𝓝 (s, t), c + L < w.1 :=
      (continuous_fst.tendsto (s, t)).eventually (Ioi_mem_nhds hs')
    filter_upwards [hev] with w hw
    simp only [neckStretch_apply, neckCollapse_of_ge hL hw.le, neckCollapse_of_ge hL hs'.le]
    congr 1
    ext <;> simp [sub_eq_add_neg]
  · -- On the neck, both sides are evaluations of `K` near the line `s = c`.
    have hσ : neckCollapse c L s = c := neckCollapse_of_mem_Icc ⟨hs, hs'⟩
    have h₁ : Tendsto (fun w : ℝ × ℝ ↦ neckCollapse c L w.1) (𝓝 (s, t)) (𝓝 c) := by
      have h := ((continuous_neckCollapse c L).tendsto s).comp (continuous_fst.tendsto (s, t))
      rwa [hσ] at h
    have h₂ : Tendsto (fun w : ℝ × ℝ ↦ w.1 + (c - s)) (𝓝 (s, t)) (𝓝 c) :=
      (by fun_prop : Continuous fun w : ℝ × ℝ ↦ w.1 + (c - s)).tendsto' (s, t) c (by simp)
    filter_upwards [h₁.eventually hK, h₂.eventually hK] with w hw₁ hw₂
    have hw : w + (c - s, 0) = (w.1 + (c - s), w.2) := by ext <;> simp
    rw [neckStretch_apply, hw₁, hσ, hw, hw₂]

/-- **Smoothness in the neck length.** Inserting a neck whose length `ℓ p ≥ 0` depends smoothly
on a parameter `p`, at a line near which a smooth datum on the product of the domain with a
manifold `M` is independent of `s`, gives a datum that is smooth jointly in the parameter, the
domain point and the point of `M`. -/
theorem contMDiff_neckStretch_family {P E H M F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : WithTop ℕ∞} {ℓ : P → ℝ} (hℓ : ContDiff ℝ n ℓ) (hℓ₀ : ∀ p, 0 ≤ ℓ p)
    {K : ℝ × ℝ → M → F} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, F) n (uncurry K)) :
    ContMDiff (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, F) n
      fun q : P × (ℝ × ℝ) × M ↦ neckStretch c (ℓ q.1) K q.2.1 q.2.2 := by
  rintro ⟨p, ⟨s, t⟩, x⟩
  -- Near every point the stretched datum is a translate of `K` in `s`, by a smooth amount.
  have htrans (δ : P → ℝ) (hδ : ContDiff ℝ n δ) :
      ContMDiff (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, F) n
        fun q : P × (ℝ × ℝ) × M ↦ K (q.2.1.1 - δ q.1, q.2.1.2) q.2.2 := by
    have hg : ContDiff ℝ n fun q : P × (ℝ × ℝ) ↦ (q.2.1 - δ q.1, q.2.2) := by fun_prop
    have hdom : ContMDiff (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ × ℝ) n
        fun q : P × (ℝ × ℝ) × M ↦ (q.2.1.1 - δ q.1, q.2.1.2) :=
      (contMDiff_prod_modelWithCornersSelf_iff.2 hg.contMDiff).comp
        (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))
    exact hKd.comp (hdom.prodMk (contMDiff_snd.comp contMDiff_snd))
  have hs : Continuous fun q : P × (ℝ × ℝ) × M ↦ q.2.1.1 := by fun_prop
  have hσ : Continuous fun q : P × (ℝ × ℝ) × M ↦ neckCollapse c (ℓ q.1) q.2.1.1 := by
    have := hℓ.continuous
    unfold neckCollapse
    fun_prop
  rcases lt_or_ge s c with hsc | hsc
  · -- Before the neck, the datum is `K` itself.
    refine (htrans (fun _ ↦ 0) contDiff_const _).congr_of_eventuallyEq ?_
    filter_upwards [(hs.tendsto _).eventually (Iio_mem_nhds hsc)] with q hq
    simp [neckCollapse_of_le (hℓ₀ q.1) (le_of_lt hq)]
  rcases lt_or_ge (c + ℓ p) s with hsc' | hsc'
  · -- After the neck, the datum is the translate of `K` by `-ℓ`.
    refine (htrans ℓ hℓ _).congr_of_eventuallyEq ?_
    have hev : ∀ᶠ q : P × (ℝ × ℝ) × M in 𝓝 (p, (s, t), x), c + ℓ q.1 < q.2.1.1 :=
      ((continuous_const.add (hℓ.continuous.comp continuous_fst)).tendsto _).eventually_lt
        (hs.tendsto _) hsc'
    filter_upwards [hev] with q hq
    simp [neckCollapse_of_ge (hℓ₀ q.1) hq.le]
  · -- On the neck, both the datum and the translate of `K` by `c - s` are evaluations of `K`
    -- near the line `s = c`.
    refine (htrans (fun _ ↦ s - c) contDiff_const _).congr_of_eventuallyEq ?_
    have h₁ : Tendsto (fun q : P × (ℝ × ℝ) × M ↦ neckCollapse c (ℓ q.1) q.2.1.1)
        (𝓝 (p, (s, t), x)) (𝓝 c) := by
      have h := hσ.tendsto (p, (s, t), x)
      rwa [neckCollapse_of_mem_Icc ⟨hsc, hsc'⟩] at h
    have h₂ : Tendsto (fun q : P × (ℝ × ℝ) × M ↦ q.2.1.1 - (s - c)) (𝓝 (p, (s, t), x)) (𝓝 c) :=
      (hs.sub continuous_const).tendsto' _ c (by simp)
    filter_upwards [h₁.eventually hK, h₂.eventually hK] with q hq₁ hq₂
    rw [neckStretch_apply, hq₁ q.2.1.2, hq₂ q.2.1.2]

/-- **Smoothness in the neck length, for a vector space.** Inserting a neck whose length
`ℓ p ≥ 0` depends smoothly on a parameter `p`, at a line near which a smooth datum is independent
of `s`, gives a datum that is smooth jointly in the parameter, the domain point and the target
point. This is the vector-space case of `TauCeti.Floer.contMDiff_neckStretch_family`. -/
theorem contDiff_neckStretch_family {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {ℓ : P → ℝ} (hℓ : ContDiff ℝ n ℓ) (hℓ₀ : ∀ p, 0 ≤ ℓ p)
    {K : ℝ × ℝ → E → F} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContDiff ℝ n (uncurry K)) :
    ContDiff ℝ n fun q : P × (ℝ × ℝ) × E ↦ neckStretch c (ℓ q.1) K q.2.1 q.2.2 := by
  -- Identify the self-model of `P × (ℝ × ℝ) × E` with the product of the self-models.
  rw [← contMDiff_iff_contDiff, ← contMDiff_prod_modelWithCornersSelf_iff,
    modelWithCornersSelf_prod (E := ℝ × ℝ) (F := E), ← chartedSpaceSelf_prod]
  exact contMDiff_neckStretch_family hℓ hℓ₀ hK
    (contMDiff_prod_modelWithCornersSelf_iff.2 hKd.contMDiff)

/-- Inserting a neck at a line near which a smooth datum on the product of the domain with a
manifold is independent of `s` gives a smooth datum. -/
theorem contMDiff_uncurry_neckStretch {E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} (hL : 0 ≤ L)
    {K : ℝ × ℝ → M → F} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, F) n (uncurry K)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, F) n (uncurry (neckStretch c L K)) :=
  (contMDiff_neckStretch_family (P := ℝ) contDiff_const (fun _ ↦ hL) hK hKd).comp
    ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_id)

/-- Inserting a neck at a line near which a smooth datum is independent of `s` gives a smooth
datum. -/
theorem contDiff_uncurry_neckStretch {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} (hL : 0 ≤ L)
    {K : ℝ × ℝ → E → F} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContDiff ℝ n (uncurry K)) : ContDiff ℝ n (uncurry (neckStretch c L K)) :=
  (contDiff_neckStretch_family (P := ℝ) contDiff_const (fun _ ↦ hL) hK hKd).comp
    ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)

/-- A datum vanishing near the line `s = c` is independent of `s` there. -/
private theorem eventually_forall_eq_of_eventually_forall_eq_zero {Y : Type*} [Zero Y]
    {K : ℝ × ℝ → Y} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = 0) :
    ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t) := by
  filter_upwards [hK] with s hs t
  rw [hs t, hK.self_of_nhds t]

end NeckStretch

end Floer

namespace SmoothTwoForm

open Floer

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {c L : ℝ}

/-- **Curvature of a stretched datum.** If the perturbation data on the product of the domain with
a manifold are independent of `s` near the line `s = c`, the curvature of the datum with a neck of
length `L` inserted at `s = c` is the curvature of the original datum at `(σ s, t)`, where
`σ = neckCollapse c L`. -/
theorem hamiltonianCurvature_neckStretch (ω : SmoothTwoForm I M) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t))
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z x =
      ω.hamiltonianCurvature Ks Kt (neckCollapse c L z.1, z.2) x := by
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (neckStretch_eventuallyEq hL hKs z)
    (neckStretch_eventuallyEq hL hKt z), hamiltonianCurvature_comp_add_right]
  congr 2
  ext <;> simp

/-- **Uniform curvature bound for neck-stretching.** Let `K` be perturbation data on the product
of the domain with a manifold, cylindrical near the line `s = c`, that is `K_s = 0` and `K_t`
independent of `s` there, and let `B` bound the curvature of `K` pointwise over the rectangle
`[a₁, b₁] × [a₂, b₂]` containing that line. Then for every neck length `L ≥ 0` and every map `u`,
the integrated curvature of the stretched datum along `u` over the stretched rectangle
`[a₁, b₁ + L] × [a₂, b₂]` is at most `∫ B` over the original rectangle. -/
theorem integral_abs_hamiltonianCurvature_neckStretch_le (ω : SmoothTwoForm I M) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (u : ℝ × ℝ → M) {B : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hB : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ B z)
    (hBi : IntegrableOn B (Icc a b)) :
    ∫ z in Icc a (b.1 + L, b.2),
        |ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z)| ≤
      ∫ z in Icc a b, B z := by
  set f : ℝ × ℝ → ℝ :=
    fun z ↦ |ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z)|
  have hf (z : ℝ × ℝ) : f z = |ω.hamiltonianCurvature Ks Kt (neckCollapse c L z.1, z.2) (u z)| :=
    by simp only [f, ω.hamiltonianCurvature_neckStretch hL
      (eventually_forall_eq_of_eventually_forall_eq_zero hKs) hKt]
  by_cases hfi : IntegrableOn f (Icc a (b.1 + L, b.2))
  swap
  · rw [integral_undef hfi]
    exact setIntegral_nonneg measurableSet_Icc fun z hz ↦ (abs_nonneg _).trans (hB z hz (u z))
  -- Split the stretched rectangle into the part before the neck, the neck, and the part after it.
  set I := Icc a.2 b.2
  have hdisj {x y z : ℝ} : Disjoint (Ico x y ×ˢ I) (Icc y z ×ˢ I) :=
    disjoint_prod.2 <| Or.inl <| disjoint_left.2 fun _ h h' ↦ (h.2.trans_le h'.1).false
  have hmeas {x y : ℝ} : MeasurableSet (Icc x y ×ˢ I) := measurableSet_Icc.prod measurableSet_Icc
  have hsplit {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
      Icc x z ×ˢ I = Ico x y ×ˢ I ∪ Icc y z ×ˢ I := by
    rw [← union_prod, Ico_union_Icc_eq_Icc hxy hyz]
  have hcL : c ≤ c + L := le_add_of_nonneg_right hL
  have hcLb : c + L ≤ b.1 + L := by linarith
  rw [Icc_prod_eq] at hfi ⊢
  rw [Icc_prod_eq] at hBi hB ⊢
  dsimp only at hfi ⊢
  rw [hsplit hac (hcb.trans (le_add_of_nonneg_right hL))] at hfi ⊢
  rw [hsplit hac hcb] at hBi hB ⊢
  rw [setIntegral_union hdisj hmeas (hfi.mono_set subset_union_left)
    (hfi.mono_set subset_union_right), setIntegral_union hdisj hmeas
    (hBi.mono_set subset_union_left) (hBi.mono_set subset_union_right)]
  have hfi₂ := hfi.mono_set (subset_union_right (s := Ico a.1 c ×ˢ I))
  rw [hsplit hcL hcLb] at hfi₂
  rw [hsplit hcL hcLb, setIntegral_union hdisj hmeas (hfi₂.mono_set subset_union_left)
    (hfi₂.mono_set subset_union_right)]
  -- Before the neck, the stretched datum is the original one.
  have h₁ : ∫ z in Ico a.1 c ×ˢ I, f z ≤ ∫ z in Ico a.1 c ×ˢ I, B z := by
    refine setIntegral_mono_on (hfi.mono_set subset_union_left) (hBi.mono_set subset_union_left)
      (measurableSet_Ico.prod measurableSet_Icc) fun z hz ↦ ?_
    rw [hf, neckCollapse_of_le hL hz.1.2.le]
    exact hB z (Or.inl hz) (u z)
  -- Along the neck, the curvature vanishes.
  have h₂ : ∫ z in Ico c (c + L) ×ˢ I, f z = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ by
      rw [hf, neckCollapse_of_mem_Icc ⟨hz.1.1, hz.1.2.le⟩,
        ω.hamiltonianCurvature_eq_zero_of_cylindrical hKs hKt, abs_zero]
  -- After the neck, the stretched datum is the translate of the original one by `-L`.
  have h₃ : ∫ z in Icc (c + L) (b.1 + L) ×ˢ I, f z ≤ ∫ z in Icc c b.1 ×ˢ I, B z := by
    refine setIntegral_Icc_prod_le_of_comp_add_le measurableSet_Icc
      (hfi₂.mono_set subset_union_right) (hBi.mono_set subset_union_right) fun z hz ↦ ?_
    rw [hf, Prod.fst_add, neckCollapse_of_ge hL (by linarith [hz.1.1]),
      add_sub_cancel_right, Prod.snd_add, add_zero]
    exact hB z (Or.inr hz) _
  linarith

/-- **Uniform energy estimate for neck-stretching, for a manifold target.** Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold, and let `K` be `C¹` perturbation data,
cylindrical near the line `s = c`, whose curvature is bounded by `B` over the rectangle
`[a₁, b₁] × [a₂, b₂]` containing that line. For a map `u` that is `C¹` near the stretched
rectangle `[a₁, b₁ + L] × [a₂, b₂]`, with integrable energy density and curvature for the stretched
datum there, the Floer energy of `u` for the stretched datum differs from its symplectic area plus
the boundary integral of the pulled-back stretched one-form by at most `∫ B` over the original
rectangle, for every neck length `L ≥ 0`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_neckStretch_sub_le
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (hKsd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks))
    (hKtd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt)) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) {B : ℝ × ℝ → ℝ}
    {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1) (hab : a.2 ≤ b.2)
    (habU : Icc a (b.1 + L, b.2) ⊆ U)
    (hE : IntegrableOn (ω.floerEnergyDensity (neckStretch c L Ks) (neckStretch c L Kt) u)
      (Icc a (b.1 + L, b.2)))
    (hR : IntegrableOn
      (fun z ↦ ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z))
      (Icc a (b.1 + L, b.2)))
    (hB : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ B z)
    (hBi : IntegrableOn B (Icc a b)) :
    |(∫ z in Icc a (b.1 + L, b.2),
        ω.floerEnergyDensity (neckStretch c L Ks) (neckStretch c L Kt) u z) -
      ((∫ z in Icc a (b.1 + L, b.2), (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ s in a.1..b.1 + L, neckStretch c L Ks (s, a.2) (u (s, a.2))) +
          (∫ t in a.2..b.2, neckStretch c L Kt (b.1 + L, t) (u (b.1 + L, t))) -
          (∫ s in a.1..b.1 + L, neckStretch c L Ks (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, neckStretch c L Kt (a.1, t) (u (a.1, t))))| ≤
      ∫ z in Icc a b, B z := by
  have hab' : a ≤ (b.1 + L, b.2) := ⟨by linarith, hab⟩
  rw [hω.integral_floerEnergyDensity hU hu
    (contMDiff_uncurry_neckStretch hL (eventually_forall_eq_of_eventually_forall_eq_zero hKs)
      hKsd).contMDiffOn
    (contMDiff_uncurry_neckStretch hL hKt hKtd).contMDiffOn hab' habU hE hR,
    sub_sub_cancel_left, abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_neckStretch_le hL hKs hKt u hac hcb hB hBi)

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {c L : ℝ}

/-- **Curvature of a stretched datum.** If the perturbation data are independent of `s` near the
line `s = c`, the curvature of the datum with a neck of length `L` inserted at `s = c` is the
curvature of the original datum at `(σ s, t)`, where `σ = neckCollapse c L`. This is the
vector-space case of `TauCeti.SmoothTwoForm.hamiltonianCurvature_neckStretch`. -/
theorem hamiltonianCurvature_neckStretch (ω : SymplecticForm V) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t))
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z x =
      ω.hamiltonianCurvature Ks Kt (neckCollapse c L z.1, z.2) x := by
  simpa using ω.constSmooth.hamiltonianCurvature_neckStretch hL hKs hKt z x

/-- **Uniform curvature bound for neck-stretching.** Let `K` be cylindrical near the line `s = c`,
that is `K_s = 0` and `K_t` independent of `s` there, and let `M` bound the curvature of `K`
pointwise over the rectangle `[a₁, b₁] × [a₂, b₂]` containing that line. Then for every neck length
`L ≥ 0` and every map `u`, the integrated curvature of the stretched datum along `u` over the
stretched rectangle `[a₁, b₁ + L] × [a₂, b₂]` is at most `∫ M` over the original rectangle. This is
the vector-space case of `TauCeti.SmoothTwoForm.integral_abs_hamiltonianCurvature_neckStretch_le`.
-/
theorem integral_abs_hamiltonianCurvature_neckStretch_le (ω : SymplecticForm V) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (u : ℝ × ℝ → V) {M : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hM : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ M z)
    (hMi : IntegrableOn M (Icc a b)) :
    ∫ z in Icc a (b.1 + L, b.2),
        |ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z)| ≤
      ∫ z in Icc a b, M z := by
  simpa using ω.constSmooth.integral_abs_hamiltonianCurvature_neckStretch_le hL hKs hKt u hac hcb
    (by simpa using hM) hMi

/-- **Uniform energy estimate for neck-stretching.** Under the hypotheses of
`integral_abs_hamiltonianCurvature_neckStretch_le`, for `C¹` perturbation data and a map `u` that
is `C¹` near the stretched rectangle, the Floer energy of `u` for the stretched datum differs from
its symplectic area plus the boundary integral of the pulled-back stretched one-form by at most
`∫ M` over the original rectangle, for every neck length `L ≥ 0`. -/
theorem abs_integral_floerEnergyDensity_neckStretch_sub_le (ω : SymplecticForm V) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (hKsd : ContDiff ℝ 1 (uncurry Ks)) (hKtd : ContDiff ℝ 1 (uncurry Kt)) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u U) {M : ℝ × ℝ → ℝ} {a b : ℝ × ℝ}
    (hac : a.1 ≤ c) (hcb : c ≤ b.1) (hab : a.2 ≤ b.2) (habU : Icc a (b.1 + L, b.2) ⊆ U)
    (hM : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ M z)
    (hMi : IntegrableOn M (Icc a b)) :
    |(∫ z in Icc a (b.1 + L, b.2),
        ω.floerEnergyDensity (neckStretch c L Ks) (neckStretch c L Kt) u z) -
      ((∫ z in Icc a (b.1 + L, b.2),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ s in a.1..b.1 + L, neckStretch c L Ks (s, a.2) (u (s, a.2))) +
          (∫ t in a.2..b.2, neckStretch c L Kt (b.1 + L, t) (u (b.1 + L, t))) -
          (∫ s in a.1..b.1 + L, neckStretch c L Ks (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, neckStretch c L Kt (a.1, t) (u (a.1, t))))| ≤
      ∫ z in Icc a b, M z := by
  have hab' : a ≤ (b.1 + L, b.2) := ⟨by linarith, hab⟩
  rw [ω.integral_floerEnergyDensity hU hu (contDiff_uncurry_neckStretch hL
    (eventually_forall_eq_of_eventually_forall_eq_zero hKs) hKsd).contDiffOn
    (contDiff_uncurry_neckStretch hL hKt hKtd).contDiffOn hab' habU]
  dsimp only
  rw [sub_sub_cancel_left, abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_neckStretch_le hL hKs hKt u hac hcb hM hMi)

end SymplecticForm

end TauCeti
