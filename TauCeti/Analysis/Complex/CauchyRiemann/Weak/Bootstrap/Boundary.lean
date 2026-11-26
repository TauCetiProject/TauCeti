/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.HigherOrder
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap.HalfPlane
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Data.ENNReal.Holder

/-!
# Elliptic bootstrapping at a totally real boundary

Let `Ω ⊆ ℂ` be open, write `z = s + i t` and `H = Ω ∩ {0 ≤ t}`, and let `V` be a
finite-dimensional real inner product space with an isometric involution `R`, whose fixed space
`Fix R` plays the role of the totally real boundary subspace (for `V = ℂⁿ`, coordinatewise
conjugation and `Fix R = ℝⁿ`). Let `u` be a weak solution on `H` of the nonlinear Cauchy–Riemann
equation

`∂ₛu + J(z, u) ∂ₜu = η(z, u)`

in the sense of `TauCeti.IsWeakCauchyRiemannOn p H J η u`, for finite `p > 2`, with
`J(z, u z)² = -1`, the boundary condition `u(s) ∈ Fix R` for real `s ∈ Ω`, and `J(s, u s)`
anticommuting with `R` for real `s ∈ Ω` (for `R` the conjugation, this holds when `J(s, x) = i`
for real `x`). If `J` and `η` are of class `C^ℓ` up to the axis near the graph of `u`, this file
proves that `u ∈ W^{ℓ+1,p}_loc(H)`: the solution is as regular up to the boundary as in the
interior. This is the planar boundary case of McDuff–Salamon, Theorem B.4.1, in the adapted
coordinates of a totally real boundary condition.

The proof is McDuff–Salamon's induction. If `u ∈ W^{m,p}_loc(H)` with `1 ≤ m ≤ ℓ`, then:

* `u` solves the linear equation `∂ₛξ + A ∂ₜξ = η(z, u z)` up to the boundary with the frozen
  coefficient `A(z) = J(z, u z)` (`TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn`);
  its boundary hypothesis `⟪Fix R, A(s) u(s)⟫ = 0` holds because `A(s)` anticommutes with `R` and
  `u(s)` is fixed by `R` (`LinearIsometry.inner_apply_eq_zero_of_anticomm`);
* `A` and `η(z, u z)` are in `W^{m,p}_loc(H)` by the half-disc composition theorem
  `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`;
* the reflection of `A` across the axis is a Sobolev coefficient on the doubled domain, because
  `A(s)` anticommutes with `R` on the axis (`TauCeti.isSobolevCRCoefficients_crReflection`);
* so the linear regularity up to the boundary, `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_succ`,
  gives `u ∈ W^{m+1,p}_loc(H)`.

The reflection argument needs a domain invariant under conjugation. The general statement follows
by localizing (`TauCeti.inter_setOf_im_nonneg_induction`): near the axis to discs centred on the
axis, and away from it to the interior theorem `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`.

## Main results

* `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane`: a weak solution with a totally real
  boundary condition is in `W^{ℓ+1,p}_loc` up to the boundary for `C^ℓ` data.
* `TauCeti.forall_memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane`: for smooth data it is in
  `W^{k,p}_loc` up to the boundary for every `k`, also for `p = ∞`.
* `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_prod`: the same bootstrap in the adapted
  coordinates `F × F` of a totally real submanifold, for a finite-dimensional normed space `F`,
  with boundary values on the zero section `F × {0}` and the standard structure
  `(v, w) ↦ (-w, v)` there.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {W : Set (ℂ × V)} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
  {R : V ≃ₗᵢ[ℝ] V} {p : ℝ≥0∞}

/-- The boundary bootstrap on a domain invariant under conjugation, where the solution can be
reflected across the axis. -/
private theorem memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_of_mapsTo
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hp : 2 < p) (hp' : p ≠ ⊤) {ℓ : ℕ}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J z (u z) * J z (u z) = -1)
    (hR : Function.Involutive R) (huR : ∀ s : ℝ, (s : ℂ) ∈ Ω → R (u s) = u s)
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v, R (J s (u s) v) = -J s (u s) (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) u := by
  lift p to ℝ≥0 using hp'
  have hp2 : 2 < p := by exact_mod_cast hp
  -- The boundary subspace is the fixed space of `R`.
  let Λ : Submodule ℝ V := LinearMap.eqLocus (R : V →ₗ[ℝ] V) LinearMap.id
  have hΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (u s) (u s)⟫_ℝ = 0 :=
    fun s hs _ hv => R.toLinearIsometry.inner_apply_eq_zero_of_anticomm (hJR s hs) hv (huR s hs)
  suffices ∀ m ≤ ℓ, MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (m + 1) u from this ℓ le_rfl
  intro m hm
  induction m with
  | zero => exact h.memWkpLoc_one
  | succ m ih =>
    have hu := ih (by omega)
    have hmℓ : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hm
    have hJ1 := hJ.of_le (show (1 : WithTop ℕ∞) ≤ ℓ by exact_mod_cast (by omega : 1 ≤ ℓ))
    -- Freeze the coefficients along the graph of `u`.
    obtain ⟨DA, hDA, hDAp, hsol⟩ := exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn
      hp ENNReal.coe_ne_top hW hJ1 huW hΛ h
    rw [← Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hDA
    have hAc : ContinuousOn (fun z => J z (u z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
      hJ1.continuousOn.comp (continuousOn_id.prodMk h.continuousOn) fun z hz => ⟨huW z hz, hz.2⟩
    -- The reflected frozen coefficients are Sobolev coefficients on the doubled domain.
    have hc := isSobolevCRCoefficients_crReflection (R := R.toContinuousLinearEquiv)
      (S := 0) hΩ (by exact_mod_cast (show (1 : ℝ≥0) ≤ p from one_le_two.trans hp2.le)) hDA hAc
      hJR hDAp memLpLoc_zero
    exact hsol.memWkpLoc_succ hR hΩ (fun _ hv => hv) hc hp2 hJ2
      (ENNReal.inv_add_inv_lt_one_of_two_lt hp) le_rfl
      (hu.contDiffOn_comp_graph_succ_halfPlane hp2 h.continuousOn hW (hJ.of_le hmℓ) huW)
      (memWkpLoc_const 0)
      (hu.contDiffOn_comp_graph_succ_halfPlane hp2 h.continuousOn hW (hη.of_le hmℓ) huW)

/-- **Elliptic bootstrapping at a totally real boundary** (McDuff–Salamon, Theorem B.4.1, the
planar boundary case). Let `2 < p < ∞` and `ℓ : ℕ`, and let `R` be an isometric involution of `V`.
Let `J` and `η` be of class `C^ℓ` jointly in `(z, x)` on `W ∩ {0 ≤ z.im}`, for an open set `W`
containing the graph of `u` over `H = Ω ∩ {0 ≤ t}`, with `J(z, u z)² = -1` for almost every
`z ∈ H`. Suppose that `u(s)` is fixed by `R` and that `J(s, u s)` anticommutes with `R` for real
`s ∈ Ω`. A weak solution `u` on `H` of
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` then lies in `W^{ℓ+1,p}_loc(H)`. -/
theorem memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (hp : 2 < p) (hp' : p ≠ ⊤) {ℓ : ℕ}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J z (u z) * J z (u z) = -1)
    (hR : Function.Involutive R) (huR : ∀ s : ℝ, (s : ℂ) ∈ Ω → R (u s) = u s)
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v, R (J s (u s) v) = -J s (u s) (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) u := by
  refine inter_setOf_im_nonneg_induction (fun U => MemWkpLoc p U (ℓ + 1) u)
    memWkpLoc_iff_locally.2 ?_ fun x r _ hrΩ => ?_
  · -- Away from the axis, this is interior regularity.
    have hU := Opens.coe_upperHalf_subset Ω
    have hWU : W ∩ {x | 0 < x.1.im} ⊆ W ∩ {x | 0 ≤ x.1.im} :=
      inter_subset_inter_right _ fun x (hx : 0 < x.1.im) => hx.le
    refine memWkpLoc_of_isWeakCauchyRiemannOn hp hp'
      (hW.inter (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)))
      (hJ.mono hWU) (hη.mono hWU) (fun z hz => ⟨huW z (hU hz), (Opens.mem_upperHalf.1 hz).2⟩)
      (ae_restrict_of_ae_restrict_of_subset hU hJ2) (h.mono hU)
  · -- Near the axis, restrict to a disc centred on the axis, which is invariant under conjugation.
    let B : Opens ℂ := ⟨Metric.ball (x : ℂ) r, Metric.isOpen_ball⟩
    have hB : (B : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
      inter_subset_inter_left _ hrΩ
    have hBc : MapsTo (starRingEnd ℂ) B B := fun _ hz => conj_mem_ball_of_im_eq_zero (by simp) hz
    exact memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_of_mapsTo hBc hp hp' hW hJ hη
      (fun z hz => huW z (hB hz)) (ae_restrict_of_ae_restrict_of_subset hB hJ2) hR
      (fun s hs => huR s (hrΩ hs)) (fun s hs => hJR s (hrΩ hs)) (h.mono hB)

/-- **Smoothness up to a totally real boundary** (McDuff–Salamon, Remark B.4.3, the planar
boundary case). Under the hypotheses of `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane`
with `J` and `η` smooth and `p > 2`, possibly `p = ∞`, a weak solution `u` on `H = Ω ∩ {0 ≤ t}`
lies in `W^{k,p}_loc(H)` for every `k`. For `p = ∞` the solution is first bootstrapped at the
finite exponent `3`, and `W^{k+1,3}` up to the axis embeds in `W^{k,∞}` up to the axis
(`TauCeti.MemWkpLoc.memWkpLoc_top_inter_setOf_im_nonneg`). -/
theorem forall_memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (hp : 2 < p)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ∞ (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ∞ (fun x : ℂ × V => η x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J z (u z) * J z (u z) = -1)
    (hR : Function.Involutive R) (huR : ∀ s : ℝ, (s : ℂ) ∈ Ω → R (u s) = u s)
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v, R (J s (u s) v) = -J s (u s) (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) (k : ℕ) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u := by
  have hfin {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤) (hqp : q ≤ p) (m : ℕ) :
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (m + 1) u :=
    memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (ℓ := m) hq hq' hW
      (hJ.of_le (by exact_mod_cast le_top)) (hη.of_le (by exact_mod_cast le_top)) huW hJ2 hR huR
      hJR (h.mono_exponent hqp)
  rcases eq_or_ne p ⊤ with rfl | hp'
  · -- Pass to the finite exponent `3` and embed up to the axis.
    exact (hfin (q := 3) (by norm_num) (by norm_num) le_top k).memWkpLoc_top_inter_setOf_im_nonneg
      (by norm_num)
  · exact (hfin hp hp' le_rfl k).of_succ

/-! ### Adapted coordinates -/

section Adapted

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {W' : Set (ℂ × (F × F))} {J' : ℂ → F × F → (F × F) →L[ℝ] (F × F)} {η' : ℂ → F × F → F × F}
  {w : ℂ → F × F}

/-- **Elliptic bootstrapping at a totally real boundary, in adapted coordinates.** Let
`2 < p < ∞` and `ℓ : ℕ`, and let `F` be a finite-dimensional real normed space. On `F × F` the
zero section `F × {0}` plays the role of `ℝⁿ ⊆ ℂⁿ` and `(v, w) ↦ (-w, v)` that of multiplication
by `i`. Let `J'` and `η'` be of class `C^ℓ` jointly in `(z, x)` on `W' ∩ {0 ≤ z.im}`, for an open
set `W'` containing the graph of `w` over `H = Ω ∩ {0 ≤ t}`, with `J'(z, w z)² = -1` for almost
every `z ∈ H`. Suppose that, for real `s ∈ Ω`, `w(s)` lies on the zero section and `J'(s, w s)` is
the standard structure. A weak solution `w` on `H` of `∂ₛw + J'(z, w) ∂ₜw = η'(z, w)` then lies in
`W^{ℓ+1,p}_loc(H)`. These are the coordinates of the adapted charts of a totally real submanifold
(`TauCeti.IsAdaptedChart`). -/
theorem memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_prod (hp : 2 < p) (hp' : p ≠ ⊤) {ℓ : ℕ}
    (hW : IsOpen W')
    (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × (F × F) => J' x.1 x.2) (W' ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × (F × F) => η' x.1 x.2) (W' ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, w z) ∈ W')
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J' z (w z) * J' z (w z) = -1)
    (hw : ∀ s : ℝ, (s : ℂ) ∈ Ω → (w s).2 = 0)
    (hJs : ∀ s : ℝ, (s : ℂ) ∈ Ω →
      J' s (w s) = (-ContinuousLinearMap.snd ℝ F F).prod (ContinuousLinearMap.fst ℝ F F))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J' η' w) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) w := by
  -- Read `F × F` in the Euclidean model `G × G` with the `L²` product norm. There
  -- `R (a, b) = (a, -b)` is an isometric involution that fixes the zero section and anticommutes
  -- with the standard structure, so the boundary bootstrap for `R` applies.
  let G := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))
  let T : (F × F) ≃L[ℝ] WithLp 2 (G × G) :=
    ((toEuclidean (E := F)).prodCongr (toEuclidean (E := F))).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ G G).symm
  let R : WithLp 2 (G × G) ≃ₗᵢ[ℝ] WithLp 2 (G × G) :=
    LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ G)
      (LinearIsometryEquiv.neg ℝ)
  have hT : ContDiff ℝ ⊤ (Prod.map id T.symm : ℂ × WithLp 2 (G × G) → ℂ × (F × F)) :=
    contDiff_id.prodMap T.symm.contDiff
  -- `Prod.map id T.symm` fixes the first coordinate.
  have hmaps : MapsTo (Prod.map id T.symm) (Prod.map id T.symm ⁻¹' W' ∩ {x | 0 ≤ x.1.im})
      (W' ∩ {x | 0 ≤ x.1.im}) := fun x hx => ⟨mem_preimage.1 hx.1, by simpa using hx.2⟩
  have hconj := T.conjContinuousAlgEquiv.toContinuousLinearEquiv.contDiff (n := ℓ)
  have key := memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (W := Prod.map id T.symm ⁻¹' W')
    (J := fun z y => (T : F × F →L[ℝ] WithLp 2 (G × G)) ∘L J' z (T.symm y) ∘L
      (T.symm : WithLp 2 (G × G) →L[ℝ] F × F))
    (η := fun z y => T (η' z (T.symm y))) (R := R) (u := fun z => T (w z)) hp hp'
    (hW.preimage hT.continuous)
    ((hconj.comp_contDiffOn (hJ.comp (hT.of_le le_top).contDiffOn hmaps)).congr fun x _ => ?_)
    (T.contDiff.comp_contDiffOn (hη.comp (hT.of_le le_top).contDiffOn hmaps))
    (fun z hz => by simpa using huW z hz) ?_
    (fun x => (WithLp.ext_iff 2).2 (Prod.ext (by simp [R]) (by simp [R]))) (fun s hs => ?_)
    (fun s hs v => ?_) (h.continuousLinearEquiv_comp T)
  · simpa using key.clm_comp (T.symm : WithLp 2 (G × G) →L[ℝ] F × F)
  · ext v
    simp
  · filter_upwards [hJ2] with z hz
    simp only [ContinuousLinearEquiv.symm_apply_apply,
      ← ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ← map_mul, hz, map_neg, map_one]
  · exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [R, T]) (by simp [R, T, hw s hs]))
  · exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [R, T, hJs s hs]) (by simp [R, T, hJs s hs]))

end Adapted

/-! ### Checks -/

/-- The identity on a half-disc solves the homogeneous equation for `J = i`, with real boundary
values fixed by conjugation and `i` anticommuting with conjugation, so the boundary bootstrap
applies to it at every order. -/
example (ℓ : ℕ) : MemWkpLoc 3 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) (id : ℂ → ℂ) :=
  memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (W := univ) (R := conjLIE) (by norm_num)
    (by norm_num) isOpen_univ contDiffOn_const contDiffOn_const (fun _ _ => mem_univ _)
    (.of_forall fun _ => by ext; simp [← mul_assoc]) (fun z => by simp) (fun s _ => by simp)
    (fun _ _ v => by simp) (isWeakCauchyRiemannOn_id.mono inter_subset_left)

end TauCeti
