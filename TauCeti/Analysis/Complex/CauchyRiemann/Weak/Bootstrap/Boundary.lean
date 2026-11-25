/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.HigherOrder
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap.HalfPlane
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc
import TauCeti.Analysis.Sobolev.Local.Locality
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
`J(z, u z)² = -1`, the boundary condition `u(s) ∈ Fix R` for real `s ∈ Ω`, and `J(s, x)`
anticommuting with `R` for real `s ∈ Ω` and `x ∈ Fix R` (for `R` the conjugation, this holds for
`J(s, x) = i`). If `J` and `η` are of class `C^ℓ` up to the axis near the graph of `u`, this file
proves that `u ∈ W^{ℓ+1,p}_loc(H)`: the solution is as regular up to the boundary as in the
interior. This is the planar boundary case of McDuff–Salamon, Theorem B.4.1, in the adapted
coordinates of a totally real boundary condition.

The proof is McDuff–Salamon's induction. If `u ∈ W^{m,p}_loc(H)` with `1 ≤ m ≤ ℓ`, then:

* `u` solves the linear equation `∂ₛξ + A ∂ₜξ = η(z, u z)` up to the boundary with the frozen
  coefficient `A(z) = J(z, u z)`
  (`TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn_of_mem`);
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
  `W^{k,p}_loc` up to the boundary for every `k`.

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

omit [FiniteDimensional ℝ V] in
/-- An operator anticommuting with an isometric involution `R` maps the fixed space of `R` into its
orthogonal complement: `⟪v, T w⟫ = ⟪R v, R T w⟫ = -⟪v, T w⟫` for `v, w` fixed by `R`. -/
private theorem inner_apply_eq_zero_of_anticomm {T : V →L[ℝ] V} (hT : ∀ v, R (T v) = -T (R v))
    {v w : V} (hv : R v = v) (hw : R w = w) : ⟪v, T w⟫_ℝ = 0 := by
  have h := R.inner_map_map v (T w)
  rw [hv, hT, hw, inner_neg_right] at h
  linarith

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
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ x, R x = x → ∀ v, R (J s x v) = -J s x (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) u := by
  lift p to ℝ≥0 using hp'
  have hp2 : 2 < p := by exact_mod_cast hp
  -- The boundary subspace is the fixed space of `R`.
  let Λ : Submodule ℝ V := LinearMap.eqLocus (R : V →ₗ[ℝ] V) LinearMap.id
  have hJΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ x ∈ Λ, ∀ v ∈ Λ, ∀ w ∈ Λ, ⟪v, J s x w⟫_ℝ = 0 :=
    fun s hs x hx _ hv _ hw => inner_apply_eq_zero_of_anticomm (hJR s hs x hx) hv hw
  suffices ∀ m ≤ ℓ, MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (m + 1) u from this ℓ le_rfl
  intro m hm
  induction m with
  | zero => exact h.memWkpLoc_one
  | succ m ih =>
    have hu := ih (by omega)
    have hmℓ : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hm
    have hJ1 := hJ.of_le (show (1 : WithTop ℕ∞) ≤ ℓ by exact_mod_cast (by omega : 1 ≤ ℓ))
    -- Freeze the coefficients along the graph of `u`.
    obtain ⟨DA, hDA, hDAp, hsol⟩ := exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn_of_mem
      (Λ := Λ) hp ENNReal.coe_ne_top hW hJ1 huW huR hJΛ (h.mono_exponent le_rfl)
    rw [← Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hDA
    have hAc : ContinuousOn (fun z => J z (u z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
      hJ1.continuousOn.comp (continuousOn_id.prodMk h.continuousOn) fun z hz => ⟨huW z hz, hz.2⟩
    -- The reflected frozen coefficients are Sobolev coefficients on the doubled domain.
    have hc := isSobolevCRCoefficients_crReflection (R := R.toContinuousLinearEquiv)
      (S := 0) hΩ (by exact_mod_cast (show (1 : ℝ≥0) ≤ p from one_le_two.trans hp2.le)) hDA hAc
      (fun s hs v => hJR s hs _ (huR s hs) v) hDAp memLpLoc_zero
    exact hsol.memWkpLoc_succ hR hΩ (fun _ hv => hv) hc hp2 hJ2
      (ENNReal.inv_add_inv_lt_one_of_two_lt hp) le_rfl
      (hu.contDiffOn_comp_graph_succ_halfPlane hp2 h.continuousOn hW (hJ.of_le hmℓ) huW)
      (memWkpLoc_const 0)
      (hu.contDiffOn_comp_graph_succ_halfPlane hp2 h.continuousOn hW (hη.of_le hmℓ) huW)

/-- **Elliptic bootstrapping at a totally real boundary** (McDuff–Salamon, Theorem B.4.1, the
planar boundary case). Let `2 < p < ∞` and `ℓ : ℕ`, and let `R` be an isometric involution of `V`.
Let `J` and `η` be of class `C^ℓ` jointly in `(z, x)` on `W ∩ {0 ≤ z.im}`, for an open set `W`
containing the graph of `u` over `H = Ω ∩ {0 ≤ t}`, with `J(z, u z)² = -1` for almost every
`z ∈ H`. Suppose that `u(s)` is fixed by `R` and that `J(s, x)` anticommutes with `R` for real
`s ∈ Ω` and every `x` fixed by `R`. A weak solution `u` on `H` of
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` then lies in `W^{ℓ+1,p}_loc(H)`. -/
theorem memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (hp : 2 < p) (hp' : p ≠ ⊤) {ℓ : ℕ}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J z (u z) * J z (u z) = -1)
    (hR : Function.Involutive R) (huR : ∀ s : ℝ, (s : ℂ) ∈ Ω → R (u s) = u s)
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ x, R x = x → ∀ v, R (J s x v) = -J s x (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) u := by
  refine inter_setOf_im_nonneg_induction (fun U => MemWkpLoc p U (ℓ + 1) u)
    memWkpLoc_iff_locally.2 ?_ fun x r _ hrΩ => ?_
  · -- Away from the axis, this is interior regularity.
    have hU : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
      fun z hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
    have hWU : W ∩ {x | 0 < x.1.im} ⊆ W ∩ {x | 0 ≤ x.1.im} :=
      inter_subset_inter_right _ fun x (hx : 0 < x.1.im) => hx.le
    refine memWkpLoc_of_isWeakCauchyRiemannOn hp hp'
      (hW.inter (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)))
      (hJ.mono hWU) (hη.mono hWU) (fun z hz => ⟨huW z (hU hz), (Opens.mem_upperHalf.1 hz).2⟩)
      (ae_restrict_of_ae_restrict_of_subset hU hJ2) ?_
    simpa [← Opens.coe_upperHalf, Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] using
      (h.mono hU)
  · -- Near the axis, restrict to a disc centred on the axis, which is invariant under conjugation.
    let B : Opens ℂ := ⟨Metric.ball (x : ℂ) r, Metric.isOpen_ball⟩
    have hB : (B : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
      inter_subset_inter_left _ hrΩ
    have hBc : MapsTo (starRingEnd ℂ) B B := fun z hz => by
      simpa [B, Metric.mem_ball, ← Complex.dist_conj_conj z] using hz
    exact memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_of_mapsTo hBc hp hp' hW hJ hη
      (fun z hz => huW z (hB hz)) (ae_restrict_of_ae_restrict_of_subset hB hJ2) hR
      (fun s hs => huR s (hrΩ hs)) (fun s hs => hJR s (hrΩ hs)) (h.mono hB)

/-- **Smoothness up to a totally real boundary** (McDuff–Salamon, Remark B.4.3, the planar
boundary case). Under the hypotheses of `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane`
with `J` and `η` smooth, a weak solution `u` on `H = Ω ∩ {0 ≤ t}` lies in `W^{k,p}_loc(H)` for
every `k`. -/
theorem forall_memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (hp : 2 < p) (hp' : p ≠ ⊤)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ∞ (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (hη : ContDiffOn ℝ ∞ (fun x : ℂ × V => η x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      J z (u z) * J z (u z) = -1)
    (hR : Function.Involutive R) (huR : ∀ s : ℝ, (s : ℂ) ∈ Ω → R (u s) = u s)
    (hJR : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ x, R x = x → ∀ v, R (J s x v) = -J s x (R v))
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) (k : ℕ) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u :=
  (memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (ℓ := k) hp hp' hW
    (hJ.of_le (by exact_mod_cast le_top)) (hη.of_le (by exact_mod_cast le_top)) huW hJ2 hR huR
    hJR h).of_succ

/-! ### Checks -/

/-- The identity on a half-disc solves the homogeneous equation for `J = i`, with real boundary
values fixed by conjugation and `i` anticommuting with conjugation, so the boundary bootstrap
applies to it at every order. -/
example (ℓ : ℕ) : MemWkpLoc 3 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (ℓ + 1) (id : ℂ → ℂ) :=
  memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane (W := univ) (R := conjLIE) (by norm_num)
    (by norm_num) isOpen_univ contDiffOn_const contDiffOn_const (fun _ _ => mem_univ _)
    (.of_forall fun _ => by ext; simp [← mul_assoc]) (fun z => by simp) (fun s _ => by simp)
    (fun _ _ _ _ v => by simp) (isWeakCauchyRiemannOn_id.mono inter_subset_left)

end TauCeti
