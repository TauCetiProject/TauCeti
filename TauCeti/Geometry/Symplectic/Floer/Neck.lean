/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Inserting a cylindrical neck into Hamiltonian perturbation data

Gluing and compactness arguments for inhomogeneous Floer equations deform a domain by stretching
it along a long cylindrical neck. In coordinates `z = (s, t)`, inserting a neck of length `L` at
the line `s = c` replaces a perturbation datum `K` by `K ∘ (σ × id)`, where the *neck-collapsing
map* `σ` is the identity for `s ≤ c`, is constant equal to `c` on `[c, c + L]`, and is the
translation `s ↦ s - L` for `s ≥ c + L`. If `K` is independent of `s` near the line `s = c`, the
stretched datum is again smooth, and it agrees near every point with a translate of `K`.

The energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` turns curvature bounds
into energy bounds, but a pointwise curvature bound multiplied by the length of an arbitrarily
long neck gives no uniform estimate. The point of this file is that, when `K` is cylindrical near
the neck (`K = H_t dt` there), the curvature of the stretched datum vanishes along the whole neck,
so its integrated curvature is controlled by that of `K` itself, uniformly in the neck length.

## Main definitions

* `TauCeti.Floer.neckCollapse c L`: the neck-collapsing map `σ : ℝ → ℝ`.
* `TauCeti.Floer.neckStretch c L K`: the datum `K ∘ (σ × id)` with a neck of length `L` inserted
  at `s = c`.

## Main results

* `TauCeti.Floer.contDiff_uncurry_neckStretch`: inserting a neck at a line where the datum is
  independent of `s` preserves smoothness.
* `TauCeti.SymplecticForm.hamiltonianCurvature_neckStretch`: the curvature of the stretched datum
  is the curvature of the original datum pulled back along `σ × id`.
* `TauCeti.SymplecticForm.integral_abs_hamiltonianCurvature_neckStretch_le`: for a datum that is
  cylindrical near the neck, the integrated curvature over the stretched rectangle is bounded by
  the integral of any pointwise curvature bound over the original rectangle, uniformly in `L`.
* `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_neckStretch_sub_le`: consequently the
  Floer energy over the stretched rectangle differs from its topological part (symplectic area
  plus boundary term) by at most that same constant, for every neck length.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Sections 8 and 9, on perturbation
  data on surfaces with strip-like ends and their compatibility with gluing along long necks.
-/

public section

open Filter Function MeasureTheory Set Topology

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

/-- Inserting a neck at a line near which a smooth datum is independent of `s` gives a smooth
datum. -/
theorem contDiff_uncurry_neckStretch {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} (hL : 0 ≤ L)
    {K : ℝ × ℝ → E → F} (hK : ∀ᶠ s in 𝓝 c, ∀ t, K (s, t) = K (c, t))
    (hKd : ContDiff ℝ n (uncurry K)) : ContDiff ℝ n (uncurry (neckStretch c L K)) := by
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  set v : ℝ × ℝ := (neckCollapse c L p.1.1 - p.1.1, 0)
  have hev : uncurry (neckStretch c L K) =ᶠ[𝓝 p] fun q ↦ uncurry K (q.1 + v, q.2) := by
    filter_upwards [(continuous_fst.tendsto p).eventually (neckStretch_eventuallyEq hL hK p.1)]
      with q hq
    simp only [uncurry_def]
    exact congrFun hq q.2
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hshift : ContDiff ℝ n fun q : (ℝ × ℝ) × E ↦ (q.1 + v, q.2) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  exact (hKd.comp hshift).contDiffAt

end NeckStretch

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {c L : ℝ}

/-- **Curvature of a stretched datum.** If the perturbation data are independent of `s` near the
line `s = c`, the curvature of the datum with a neck of length `L` inserted at `s = c` is the
curvature of the original datum at `(σ s, t)`, where `σ = neckCollapse c L`. -/
theorem hamiltonianCurvature_neckStretch (ω : SymplecticForm V) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t))
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z x =
      ω.hamiltonianCurvature Ks Kt (neckCollapse c L z.1, z.2) x := by
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (neckStretch_eventuallyEq hL hKs z)
    (neckStretch_eventuallyEq hL hKt z), hamiltonianCurvature_comp_add_right]
  congr 2
  ext <;> simp

/-- **Uniform curvature bound for neck-stretching.** Let `K` be cylindrical near the line `s = c`,
that is `K_s = 0` and `K_t` independent of `s` there, and let `M` bound the curvature of `K`
pointwise over the rectangle `[a₁, b₁] × [a₂, b₂]` containing that line. Then for every neck length
`L ≥ 0` and every map `u`, the integrated curvature of the stretched datum along `u` over the
stretched rectangle `[a₁, b₁ + L] × [a₂, b₂]` is at most `∫ M` over the original rectangle. -/
theorem integral_abs_hamiltonianCurvature_neckStretch_le (ω : SymplecticForm V) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0) (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (u : ℝ × ℝ → V) {M : ℝ × ℝ → ℝ} {a b : ℝ × ℝ} (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hM : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ M z)
    (hMi : IntegrableOn M (Icc a b)) :
    ∫ z in Icc a (b.1 + L, b.2),
        |ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z)| ≤
      ∫ z in Icc a b, M z := by
  set f : ℝ × ℝ → ℝ :=
    fun z ↦ |ω.hamiltonianCurvature (neckStretch c L Ks) (neckStretch c L Kt) z (u z)|
  have hKs' : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t) := by
    filter_upwards [hKs] with s hs t
    rw [hs t, hKs.self_of_nhds t]
  have hf (z : ℝ × ℝ) : f z = |ω.hamiltonianCurvature Ks Kt (neckCollapse c L z.1, z.2) (u z)| :=
    by simp only [f, ω.hamiltonianCurvature_neckStretch hL hKs' hKt]
  by_cases hfi : IntegrableOn f (Icc a (b.1 + L, b.2))
  swap
  · rw [integral_undef hfi]
    exact setIntegral_nonneg measurableSet_Icc fun z hz ↦ (abs_nonneg _).trans (hM z hz (u z))
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
  rw [Icc_prod_eq] at hMi hM ⊢
  dsimp only at hfi ⊢
  rw [hsplit hac (hcb.trans (le_add_of_nonneg_right hL))] at hfi ⊢
  rw [hsplit hac hcb] at hMi hM ⊢
  rw [setIntegral_union hdisj hmeas (hfi.mono_set subset_union_left)
    (hfi.mono_set subset_union_right), setIntegral_union hdisj hmeas
    (hMi.mono_set subset_union_left) (hMi.mono_set subset_union_right)]
  have hfi₂ := hfi.mono_set (subset_union_right (s := Ico a.1 c ×ˢ I))
  rw [hsplit hcL hcLb] at hfi₂
  rw [hsplit hcL hcLb, setIntegral_union hdisj hmeas (hfi₂.mono_set subset_union_left)
    (hfi₂.mono_set subset_union_right)]
  -- Before the neck, the stretched datum is the original one.
  have h₁ : ∫ z in Ico a.1 c ×ˢ I, f z ≤ ∫ z in Ico a.1 c ×ˢ I, M z := by
    refine setIntegral_mono_on (hfi.mono_set subset_union_left) (hMi.mono_set subset_union_left)
      (measurableSet_Ico.prod measurableSet_Icc) fun z hz ↦ ?_
    rw [hf, neckCollapse_of_le hL hz.1.2.le]
    exact hM z (Or.inl hz) (u z)
  -- Along the neck, the curvature vanishes.
  have h₂ : ∫ z in Ico c (c + L) ×ˢ I, f z = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ by
      rw [hf, neckCollapse_of_mem_Icc ⟨hz.1.1, hz.1.2.le⟩,
        ω.hamiltonianCurvature_eq_zero_of_cylindrical hKs hKt, abs_zero]
  -- After the neck, the stretched datum is the translate of the original one by `-L`.
  set e : ℝ × ℝ → ℝ × ℝ := (· + (-L, 0))
  have he : MeasurePreserving e := by
    -- Translation invariance of `volume` on `ℝ × ℝ` is found on the product measure.
    have : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
      rw [Measure.volume_eq_prod]
      infer_instance
    exact measurePreserving_add_right volume (-L, 0)
  have hemb : MeasurableEmbedding e := measurableEmbedding_addRight (-L, 0)
  have hpre : e ⁻¹' (Icc c b.1 ×ˢ I) = Icc (c + L) (b.1 + L) ×ˢ I := by
    ext z
    simp only [e, mem_preimage, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add, add_zero]
    constructor <;> rintro ⟨⟨h, h'⟩, h''⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h''⟩
  have h₃ : ∫ z in Icc (c + L) (b.1 + L) ×ˢ I, f z ≤ ∫ z in Icc c b.1 ×ˢ I, M z := by
    rw [← he.setIntegral_preimage_emb hemb M, hpre]
    have hMe : IntegrableOn (M ∘ e) (Icc (c + L) (b.1 + L) ×ˢ I) := by
      rw [← hpre, he.integrableOn_comp_preimage hemb]
      exact hMi.mono_set subset_union_right
    refine setIntegral_mono_on (hfi₂.mono_set subset_union_right) hMe hmeas fun z hz ↦ ?_
    have hez : (neckCollapse c L z.1, z.2) = e z := by
      ext <;> simp [e, neckCollapse_of_ge hL hz.1.1, sub_eq_add_neg]
    have hz' : z ∈ e ⁻¹' (Icc c b.1 ×ˢ I) := hpre ▸ hz
    rw [hf, hez]
    exact hM (e z) (Or.inr hz') (u z)
  linarith

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
  have hKs' : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = Ks (c, t) := by
    filter_upwards [hKs] with s hs t
    rw [hs t, hKs.self_of_nhds t]
  have hab' : a ≤ (b.1 + L, b.2) := ⟨by linarith, hab⟩
  rw [ω.integral_floerEnergyDensity hU hu (contDiff_uncurry_neckStretch hL hKs' hKsd).contDiffOn
    (contDiff_uncurry_neckStretch hL hKt hKtd).contDiffOn hab' habU]
  dsimp only
  rw [sub_sub_cancel_left, abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_neckStretch_le hL hKs hKt u hac hcb hM hMi)

end SymplecticForm

end TauCeti
