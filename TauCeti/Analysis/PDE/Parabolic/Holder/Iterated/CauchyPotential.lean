/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyPotential
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
import TauCeti.Analysis.InnerProductSpace.Laplacian.Iterate

/-!
# The Cauchy heat potential in the parabolic Hölder spaces of every order

For an initial datum `g ∈ C_b^{k,α}(E)`, `α ≤ 1`, and a slab `E × [a, b]` with `0 ≤ a < b`, the
Cauchy heat potential `u(t, x) = ∫ K_1(y) g(x - √t • y) dy` (`TauCeti.heatCauchyPotential`)
belongs to the bounded parabolic Hölder space `C_{par,b}^{k+α}(E × [a, b])` of order `k`
(`TauCeti.ParabolicCkHolderSpace`), and `g ↦ u` is a bounded linear map
`TauCeti.ParabolicCkHolderSpace.heatCauchyPotentialL` whose operator norm is bounded independently
of the slab. At order two it is the potential `TauCeti.heatCauchyPotentialL` into
`C_b^{2+α,1+α/2}`. This is the initial-data part of the solution operator of the Cauchy problem
`∂ₜu - Δu = f`, `u(·, 0) = g` at every order of differentiability: the order-`k` Schauder theory
of parabolic equations starts its method of continuity from the heat equation.

Each field of `u` is the Cauchy potential of a derivative of the datum: since the potential
commutes with spatial derivatives and solves the heat equation `∂ₜu = Δu`, the field
`D_t^r D_x^m u` is the Cauchy potential of `D^m Δ^r g`
(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatCauchyPotentialL`). The three conditions on the
fields then come from estimates on the potential.

* For `2 r + m ≤ k` the datum `D^m Δ^r g` is bounded by `(dim E)^r ‖g‖`
  (`TauCeti.norm_iteratedFDeriv_iterate_laplacian_le`), and so is its potential, by the maximum
  principle.
* For `2 r + m = k` the datum is `α`-Hölder
  (`TauCeti.norm_iteratedFDeriv_iterate_laplacian_sub_le`), so the field is parabolically
  `α`-Hölder (`TauCeti.holderWith_slabHeatCauchyPotential`).
* For `2 r + m = k - 1` the datum has an `α`-Hölder derivative, so the time slices of the field
  are `(1 + α)/2`-Hölder
  (`TauCeti.norm_heatCauchyPotential_sub_heatCauchyPotential_le_of_holderWith_fderiv`).

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.heatCauchyPotentialL`: the Cauchy potential as a continuous
  linear map `C_b^{k,α}(E) → C_{par,b}^{k+α}(E × [a, b])`.
* `TauCeti.ParabolicCkHolderSpace.heatCauchyPotentialL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatCauchyPotentialL`: the values and the fields.
* `TauCeti.ParabolicCkHolderSpace.timeDerivL_heatCauchyPotentialL_eq_laplacian` and
  `TauCeti.ParabolicCkHolderSpace.spatialTrace_heatCauchyPotentialL_left`: the potential solves
  the heat equation `∂ₜu = Δu` and attains its datum at `t = 0`.
* `TauCeti.ParabolicCkHolderSpace.norm_heatCauchyPotentialL_le`: the operator-norm bound
  `(k + 1)² (1 + dim E)^k (4 + M_α + M_{1+α})`, with the moments `M_γ` of
  `TauCeti.heatKernelMoment`.
* `TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace_heatCauchyPotentialL`: agreement
  with the order-two potential.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Hölder spaces of higher order).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

namespace ParabolicCkHolderSpace

/-! ### The data of the fields -/

/-- The datum `D^m Δ^r g` whose Cauchy potential is the field `D_t^r D_x^m u`. -/
private abbrev datum (g : CkHolderSpace k α E F) (r m : ℕ) : E → E [×m]→L[ℝ] F :=
  iteratedFDeriv ℝ m (Δ^[r] (g : E → F))

private theorem contDiff_iterate (g : CkHolderSpace k α E F) {r : ℕ} (h : 2 * r ≤ k) :
    ContDiff ℝ (k - 2 * r : ℕ) (Δ^[r] (g : E → F)) :=
  g.contDiff.iterate_laplacian (by exact_mod_cast (by omega : k - 2 * r + 2 * r ≤ k))

private theorem continuous_datum (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m ≤ k) :
    Continuous (datum g r m) :=
  (contDiff_iterate g (r := r) (by omega)).continuous_iteratedFDeriv (by norm_cast; omega)

private theorem norm_datum_le (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m ≤ k) (x : E) :
    ‖datum g r m x‖ ≤ Module.finrank ℝ E ^ r * ‖g‖ :=
  (norm_iteratedFDeriv_iterate_laplacian_le g.contDiff (by omega) x).trans
    (mul_le_mul_of_nonneg_left (g.norm_iteratedFDeriv_apply_le (by omega) x) (by positivity))

private theorem holderWith_datum (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m = k) :
    HolderWith (Module.finrank ℝ E ^ r * nnHolderNorm α (iteratedFDeriv ℝ k g)) α
      (datum g r m) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [dist_eq_norm]
  refine (norm_iteratedFDeriv_iterate_laplacian_sub_le g.contDiff (by omega) x y).trans ?_
  have hH := g.memHolder_iteratedFDeriv.holderWith.dist_le x y
  rw [dist_eq_norm] at hH
  rw [show m + 2 * r = k by omega]
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hH (by positivity)

/-- The derivative of the datum `D^m Δ^r g` is `D^(m+1) Δ^r g`, curried on the left. -/
private theorem hasFDerivAt_datum (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m + 1 ≤ k)
    (y : E) : HasFDerivAt (datum g r m)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F (datum g r (m + 1) y))
      y := by
  have hd := ((contDiff_iterate g (r := r) (by omega)).differentiable_iteratedFDeriv
    (m := m) (by norm_cast; omega) y).hasFDerivAt
  have he : datum g r (m + 1) y = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E)
      F).symm (fderiv ℝ (datum g r m) y) := by
    simp only [datum, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
  rwa [he, LinearIsometryEquiv.apply_symm_apply]

/-! ### The fields -/

variable [MeasurableSpace E] [BorelSpace E]

/-- The fields `D_t^r D_x^m u` of the potential: the slab Cauchy potentials of `D^m Δ^r g` for
`2 r + m ≤ k`, and zero otherwise. -/
private def field (g : CkHolderSpace k α E F) (r m : ℕ) : slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F) :=
  if h : 2 * r + m ≤ k then
    slabHeatCauchyPotential (datum g r m) (continuous_datum g h) (norm_datum_le g h)
  else 0

private theorem field_apply (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m ≤ k)
    (p : slab (E := E) a b) :
    field g r m p = heatCauchyPotential (datum g r m) (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space := by
  rw [field, dite_eq_left h, slabHeatCauchyPotential_apply]

private theorem field_slabMk (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m ≤ k) (x : E)
    (t : Icc a b) : field g r m (slabMk x t) = heatCauchyPotential (datum g r m) t x := by
  rw [field_apply g h, space_slabMk, time_slabMk]

private theorem norm_field_le (g : CkHolderSpace k α E F) (r m : ℕ) :
    ‖field (a := a) (b := b) g r m‖ ≤ Module.finrank ℝ E ^ r * ‖g‖ := by
  by_cases h : 2 * r + m ≤ k
  · rw [field, dite_eq_left h]
    exact norm_slabHeatCauchyPotential_le _ _
  · rw [field, dite_eq_right h]
    exact (norm_zero (E := slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F))).trans_le (by positivity)

private theorem hasFDerivAt_field (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m + 1 ≤ k)
    (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ field g r m (slabMk y t)) (field g r (m + 1) (slabMk x t)).curryLeft
      x := by
  set e :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).toContinuousLinearEquiv
  simp only [field_slabMk g (by omega : 2 * r + m ≤ k),
    field_slabMk g (by omega : 2 * r + (m + 1) ≤ k)]
  have hd := hasFDerivAt_heatCauchyPotential (g := datum g r m) (g' := e ∘ datum g r (m + 1))
    (M := Module.finrank ℝ E ^ r * ‖g‖) (fun y ↦ hasFDerivAt_datum g h y)
    (e.continuous.comp (continuous_datum g (by omega : 2 * r + (m + 1) ≤ k))) (fun y ↦
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).norm_map
        (datum g r (m + 1) y)).trans_le (norm_datum_le g (by omega) y)) t x
  rw [heatCauchyPotential_comp_continuousLinearEquiv] at hd
  convert hd using 1
  ext v w
  simp [e, continuousMultilinearCurryLeftEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]

private theorem hasDerivWithinAt_field (hab : a < b) (ha : 0 ≤ a) (g : CkHolderSpace k α E F)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (field g r m) x)
      (field g (r + 1) m (slabMk x t)) (Icc a b) t := by
  rw [field_slabMk g (by omega : 2 * (r + 1) + m ≤ k)]
  have hφ : ContDiff ℝ (m + 2 : ℕ) (Δ^[r] (g : E → F)) :=
    (contDiff_iterate g (r := r) (by omega)).of_le (by norm_cast; omega)
  have hΔ : Δ (datum g r m) = datum g (r + 1) m := by
    rw [datum, datum, hφ.laplacian_iteratedFDeriv, Function.iterate_succ_apply']
  have hc2 : ContDiff ℝ 2 (datum g r m) :=
    (contDiff_iterate g (r := r) (by omega)).iteratedFDeriv_right (by norm_cast; omega)
  have h₁ : ∀ y, ‖fderiv ℝ (datum g r m) y‖ ≤ Module.finrank ℝ E ^ r * ‖g‖ := fun y ↦ by
    rw [(hasFDerivAt_datum g (by omega) y).fderiv, LinearIsometryEquiv.norm_map]
    exact norm_datum_le g (by omega) y
  -- The bound on the second derivative is stated through the lemma, whose statement carries the
  -- norm on bilinear maps into multilinear maps that instance search does not reach directly.
  have hd := hasDerivWithinAt_heatCauchyPotential (M₂ := Module.finrank ℝ E ^ r * ‖g‖) hc2
    (norm_datum_le g (by omega)) h₁ (fun y ↦ by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, datum,
        norm_iteratedFDeriv_iteratedFDeriv]
      exact norm_datum_le g (m := 1 + 1 + m) (by omega) y)
    (ha.trans t.property.1) x
  rw [hΔ] at hd
  refine (hd.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 ha))).congr_of_mem
    (fun s hs ↦ ?_) t.property
  simp [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le hs,
    field_slabMk g (by omega : 2 * r + m ≤ k)]

private theorem holderWith_field_slabMk (hα : α ≤ 1) (g : CkHolderSpace k α E F) {r m : ℕ}
    (h : 2 * r + m + 1 = k) (x : E) :
    HolderWith (Module.finrank ℝ E ^ r * nnHolderNorm α (iteratedFDeriv ℝ k g) *
      heatKernelMoment E (1 + α)) ((1 + α) / 2) fun t : Icc a b ↦ field g r m (slabMk x t) := by
  set e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F)
  have hH : HolderWith (Module.finrank ℝ E ^ r * nnHolderNorm α (iteratedFDeriv ℝ k g)) α
      (e ∘ datum g r (m + 1)) := e.isometry.comp_holderWith (holderWith_datum g (by omega))
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun t _ s _ ↦ ?_
  rw [dist_eq_norm, field_slabMk g (by omega), field_slabMk g (by omega), Subtype.dist_eq,
    Real.dist_eq]
  refine (norm_heatCauchyPotential_sub_heatCauchyPotential_le_of_holderWith_fderiv
    (fun y ↦ hasFDerivAt_datum g (by omega) y) hH hα (norm_datum_le g (by omega)) t s x).trans_eq ?_
  push_cast
  ring_nf

private theorem holderWith_field (g : CkHolderSpace k α E F) {r m : ℕ} (h : 2 * r + m = k) :
    HolderWith (Module.finrank ℝ E ^ r * nnHolderNorm α (iteratedFDeriv ℝ k g) *
      (1 + heatKernelMoment E α)) α (field (a := a) (b := b) g r m) := by
  rw [field, dite_eq_left h.le]
  exact holderWith_slabHeatCauchyPotential _ _ (holderWith_datum g h)

/-! ### The potential -/

/-- The Cauchy potential of a `C_b^{k,α}` datum as an element of `C_{par,b}^{k+α}`. -/
private def potential (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a) (g : CkHolderSpace k α E F) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (field g) (fun _ _ h t x ↦ hasFDerivAt_field g h t x)
    (fun _ _ h x t ↦ hasDerivWithinAt_field hab ha g h x t)
    (fun _ _ h ↦ ⟨_, fun x ↦ holderWith_field_slabMk hα g h x⟩)
    (fun _ _ h ↦ (holderWith_field g h).memHolder)

private theorem mixedDerivL_potential (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)
    (g : CkHolderSpace k α E F) (r m : ℕ) :
    mixedDerivL r m (potential hα hab ha g) = field g r m := by
  by_cases h : 2 * r + m ≤ k
  · exact mixedDerivL_mk _ _ _ _ h
  · rw [mixedDerivL_of_lt (by omega), zero_apply, field, dite_eq_right h]

private theorem potential_apply (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)
    (g : CkHolderSpace k α E F) (p : slab (E := E) a b) :
    potential hα hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [potential, mk_apply, field_apply g (by omega), datum, Function.iterate_zero, id,
    iteratedFDeriv_zero_eq_comp]
  have := heatCauchyPotential_comp_continuousLinearEquiv
    (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv (g : E → F)
    (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at this
  rw [this]
  simp

/-- The contribution of the field of index `(r, m)` to the norm of the potential: its supremum
norm, the norm of its time slices and its Hölder norm. -/
private theorem norm_fields_potential_le (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)
    (g : CkHolderSpace k α E F) {r m : ℕ} (hp : 2 * r + m ≤ k) :
    ‖mixedDerivL r m (potential hα hab ha g)‖ + (‖timeSliceL r m (potential hα hab ha g)‖ +
      ‖mixedDerivHolderL r m (potential hα hab ha g)‖) ≤ (1 + Module.finrank ℝ E) ^ k *
        (4 + heatKernelMoment E α + heatKernelMoment E (1 + α)) * ‖g‖ := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set B : ℝ := (1 + d) ^ k * ‖g‖
  have hd : 0 ≤ d := Nat.cast_nonneg _
  -- The power `d ^ r`, `2 r ≤ k`, is at most `(1 + d) ^ k`.
  have hg : d ^ r * ‖g‖ ≤ B := mul_le_mul_of_nonneg_right
    ((pow_le_pow_left₀ hd (by linarith) r).trans (pow_le_pow_right₀ (by linarith) (by omega)))
    (norm_nonneg g)
  have hK : d ^ r * (nnHolderNorm α (iteratedFDeriv ℝ k g) : ℝ) ≤ B :=
    (mul_le_mul_of_nonneg_left g.nnHolderNorm_iteratedFDeriv_le (by positivity)).trans hg
  have hB0 : 0 ≤ B := by positivity
  set f := potential hα hab ha g
  have hfield : ‖mixedDerivL r m f‖ ≤ B := by
    rw [mixedDerivL_potential]
    exact (norm_field_le g r m).trans hg
  have hslice : ‖timeSliceL r m f‖ ≤ B + B * heatKernelMoment E (1 + α) := by
    by_cases h : 2 * r + m + 1 = k
    · refine (norm_timeSliceL_le_of_holderWith f h (C := Module.finrank ℝ E ^ r *
        nnHolderNorm α (iteratedFDeriv ℝ k g) * heatKernelMoment E (1 + α)) fun x ↦ ?_).trans ?_
      · rw [mixedDerivL_potential]
        exact holderWith_field_slabMk hα g h x
      · push_cast
        gcongr
    · rw [timeSliceL_of_ne h, zero_apply, norm_zero]
      positivity
  have hhold : ‖mixedDerivHolderL r m f‖ ≤ B + B * (1 + heatKernelMoment E α) := by
    by_cases h : 2 * r + m = k
    · have hcoe : ⇑(mixedDerivHolderL r m f) = ⇑(field g r m) :=
        funext fun p ↦ by rw [mixedDerivHolderL_apply f h, mixedDerivL_potential]
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith hB0 (fun p ↦ ?_)
        (hcoe ▸ holderWith_field g h)).trans ?_
      · rw [hcoe, ← mixedDerivL_potential hα hab ha]
        exact ((mixedDerivL r m f).norm_coe_le_norm p).trans hfield
      · push_cast
        gcongr
    · rw [mixedDerivHolderL_of_ne h, zero_apply, norm_zero]
      positivity
  linarith

private theorem norm_potential_le (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)
    (g : CkHolderSpace k α E F) :
    ‖potential hα hab ha g‖ ≤ (k + 1) ^ 2 * (1 + Module.finrank ℝ E) ^ k *
      (4 + heatKernelMoment E α + heatKernelMoment E (1 + α)) * ‖g‖ := by
  set C : ℝ := (1 + Module.finrank ℝ E) ^ k *
    (4 + heatKernelMoment E α + heatKernelMoment E (1 + α)) * ‖g‖
  rw [norm_eq]
  calc ∑ p ∈ parabolicDerivPairs k, (‖mixedDerivL p.1 p.2 (potential hα hab ha g)‖ +
        (‖timeSliceL p.1 p.2 (potential hα hab ha g)‖ +
          ‖mixedDerivHolderL p.1 p.2 (potential hα hab ha g)‖))
      ≤ ∑ _p ∈ parabolicDerivPairs k, C := Finset.sum_le_sum fun p hp ↦
        norm_fields_potential_le hα hab ha g (mem_parabolicDerivPairs.1 hp)
    _ = (parabolicDerivPairs k).card * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k + 1) ^ 2 * C := by
        gcongr
        exact_mod_cast card_parabolicDerivPairs_le k
    _ = _ := by ring

variable (hα : α ≤ 1) (hab : a < b) (ha : 0 ≤ a)

/-- **The Cauchy heat potential in `C_{par,b}^{k+α}`.** For `α ≤ 1` and `0 ≤ a < b`, the Cauchy
heat potential `u(t, x) = ∫ K_1(y) g(x - √t • y) dy` of a datum `g ∈ C_b^{k,α}(E)`, restricted to
the slab `E × [a, b]`, as a continuous linear map into the bounded parabolic Hölder space of order
`k`. Its field `D_t^r D_x^m u` is the Cauchy potential of `D^m Δ^r g`
(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_heatCauchyPotentialL`), and its operator norm is
bounded independently of the slab (`TauCeti.ParabolicCkHolderSpace.norm_heatCauchyPotentialL_le`).
-/
def heatCauchyPotentialL : CkHolderSpace k α E F →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := potential hα hab ha
      map_add' g₁ g₂ := ext fun p ↦ by
        simp only [potential_apply, coe_add, CkHolderSpace.coe_add, Pi.add_apply]
        exact heatCauchyPotential_add g₁.contDiff.continuous
          g₁.norm_apply_le_iteratedFDeriv_zero g₂.contDiff.continuous
          g₂.norm_apply_le_iteratedFDeriv_zero _ _
      map_smul' c g := ext fun p ↦ by
        simp only [potential_apply, coe_smul, CkHolderSpace.coe_smul, Pi.smul_apply,
          RingHom.id_apply]
        exact heatCauchyPotential_smul c _ _ _ }
    _ (norm_potential_le hα hab ha)

private theorem heatCauchyPotentialL_eq_potential (g : CkHolderSpace k α E F) :
    heatCauchyPotentialL hα hab ha g = potential hα hab ha g :=
  (rfl)

variable {hα hab ha}

/-- The value of the potential at a point of the slab. -/
@[simp]
theorem heatCauchyPotentialL_apply (g : CkHolderSpace k α E F) (p : slab (E := E) a b) :
    heatCauchyPotentialL hα hab ha g p =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, potential_apply]

/-- **The fields of the potential.** For `2 r + m ≤ k`, the field `D_t^r D_x^m u` of the Cauchy
potential `u` of `g` is the Cauchy potential of `D^m Δ^r g`. In particular the time derivatives
are given by the heat equation `∂ₜu = Δu`, up to the initial time when `a = 0`. -/
@[simp]
theorem mixedDerivL_heatCauchyPotentialL (g : CkHolderSpace k α E F) {r m : ℕ}
    (h : 2 * r + m ≤ k) (p : slab (E := E) a b) :
    mixedDerivL r m (heatCauchyPotentialL hα hab ha g) p =
      heatCauchyPotential (iteratedFDeriv ℝ m (Δ^[r] (g : E → F)))
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatCauchyPotentialL_eq_potential, mixedDerivL_potential, field_apply g h]

variable (k α E F hα hab ha) in
/-- The operator norm of the Cauchy potential into `C_{par,b}^{k+α}` is at most
`(k + 1)² (1 + dim E)^k (4 + M_α + M_{1+α})`, where `M_γ = ∫ ‖y‖^γ K_1(y) dy` is
`TauCeti.heatKernelMoment`. In particular it is independent of the slab. -/
theorem norm_heatCauchyPotentialL_le :
    ‖heatCauchyPotentialL (k := k) (α := α) (E := E) (F := F) hα hab ha‖ ≤
      (k + 1) ^ 2 * (1 + Module.finrank ℝ E) ^ k *
        (4 + heatKernelMoment E α + heatKernelMoment E (1 + α)) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g ↦ by
    rw [heatCauchyPotentialL_eq_potential]
    exact norm_potential_le hα hab ha g

/-- At order two the potential is the Cauchy potential `TauCeti.heatCauchyPotentialL` into
`C_b^{2+α,1+α/2}`, under the identification `equivParabolicC2HolderSpace`. -/
theorem equivParabolicC2HolderSpace_heatCauchyPotentialL (g : CkHolderSpace 2 α E F) :
    equivParabolicC2HolderSpace (heatCauchyPotentialL hα hab ha g) =
      TauCeti.heatCauchyPotentialL hab ha g :=
  ParabolicC2HolderSpace.ext fun p ↦ by simp

/-- **The heat equation.** For a datum of order `k + 2`, the time derivative of the Cauchy potential
is the spatial Laplacian of its time slice, at every point of the closed slab. -/
theorem timeDerivL_heatCauchyPotentialL_eq_laplacian (g : CkHolderSpace (k + 2) α E F)
    (p : slab (E := E) a b) :
    timeDerivL k α E F hab (heatCauchyPotentialL hα hab ha g) p =
      Δ (fun y ↦ heatCauchyPotentialL hα hab ha g (slabMk y (slabTime p)))
        (p : ParabolicSpaceTime E).space := by
  have hL := heatCauchyPotential_comp_continuousLinearEquiv
    (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv
    (iteratedFDeriv ℝ 0 (Δ^[1] (g : E → F))) (p : ParabolicSpaceTime E).time
    (p : ParabolicSpaceTime E).space
  have hcomp : ((continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv ∘
      iteratedFDeriv ℝ 0 (Δ^[1] (g : E → F))) = Δ (g : E → F) := by
    funext y
    simp
  have hslice : (fun y ↦ heatCauchyPotentialL hα hab ha g (slabMk y (slabTime p))) =
      heatCauchyPotential g (p : ParabolicSpaceTime E).time := by
    funext y
    simp
  -- The field `D_t^1 D_x^0` is the potential of the `0`-th curried field of `Δ^[1] g`; read through
  -- the curry equivalence it is the potential of `Δ g` (`hcomp`), because the potential commutes
  -- with continuous linear equivalences (`hL`). That is the Laplacian of the potential of `g`.
  rw [timeDerivL_apply, mixedDerivL_heatCauchyPotentialL g (by omega), hslice,
    laplacian_heatCauchyPotential (g.contDiff.of_le (by norm_cast; omega))
      g.norm_fderiv_le_iteratedFDeriv_one g.norm_fderiv_fderiv_le_iteratedFDeriv_two, ← hcomp, hL]
  simp

/-- **Attainment of the initial datum.** On the slab `E × [0, b]`, the initial trace of the Cauchy
potential of `g` is `g`. -/
theorem spatialTrace_heatCauchyPotentialL_left [CompleteSpace F] (hb : 0 < b)
    (g : CkHolderSpace k α E F) :
    (heatCauchyPotentialL hα hb le_rfl g).spatialTrace ⟨0, left_mem_Icc.2 hb.le⟩ = g := by
  ext x
  simp [heatCauchyPotential_zero]

end ParabolicCkHolderSpace

end TauCeti
