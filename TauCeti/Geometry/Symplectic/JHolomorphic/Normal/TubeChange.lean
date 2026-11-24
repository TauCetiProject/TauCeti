/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.Analysis.Calculus.FDeriv.NormalSegment
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Calculus.IteratedFDeriv.SliceLimit

/-!
# Changing the tube around a curve: normal dilations of maps

Near an embedded curve `C`, Taubes reads fields in normal coordinates `(z, W) ∈ E × N` given by a
tubular map `F` with `F(z, 0) = z`, and dilates the normal directions:
`Φ_a(z, W) = F(z, a W)`. A second tube `F'` with the same zero section gives the coordinate change
`g = F'⁻¹ ∘ F`, a map defined near the zero section `E × {0}` that preserves it. In the dilated
coordinates the change is the conjugate of `g` by the normal dilation `δ_a(z, W) = (z, a W)`:

`(δ_a⁻¹ ∘ g ∘ δ_a)(z, W) = (g₁(z, a W), a⁻¹ g₂(z, a W))`

(`TauCeti.normalDilationMap g a`). As `a → 0` it converges, with its derivatives and uniformly on
compact sets, to the **normal linearization** of `g` along the zero section,

`g_N(z, W) = (g₁(z, 0), ∂_W g₂(z, 0) W)`

(`TauCeti.normalLinearizationMap g`), which is linear on each normal fibre. Two tubes are
**first-jet identical** along `C` when `g(z, 0) = (z, 0)` and `dg(z, 0) = id`; then `g_N` is the
identity, so the dilated coordinate changes converge to the identity. This is how statements
proved in one fixed tube (the foliation by pseudoholomorphic normal disks) transfer to any other
tube with the same first jet: in both the dilated coordinates agree up to an error that vanishes
as `a → 0`, while undilated the two normal coordinates of a point differ by `O(|ξ|²)`. In
particular the largest normal distance from `C` of a set of points shrinking to `C`, such as the
zero set of a Seiberg–Witten section, is asymptotically the same in both tubes.

## Main definitions

* `TauCeti.normalDilationMap g a`: the conjugate `δ_a⁻¹ ∘ g ∘ δ_a` of a map `g` of `E × N`, written
  so that it is defined for every `a`.
* `TauCeti.normalLinearizationMap g`: the normal linearization of `g` along `E × {0}`.

## Main results

* `TauCeti.normalDilationMap_normalDilationMap`, `TauCeti.normalDilationMap_comp`: the dilations
  form an action of the multiplicative monoid, and conjugation respects composition for `a ≠ 0`.
* `TauCeti.tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen`: if `g` is `C^(i+1)`
  on an open set `Ω` and maps the zero section into itself, the `i`-th derivatives of the
  dilations converge to those of `g_N`, uniformly on compact sets over the zero section in `Ω`.
* `TauCeti.tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen_of_firstJet_eq_id`: for
  a first-jet identical change of tube they converge to the identity in `Cⁱ`; with `i = 1`, this is
  rescaled `C¹` convergence to the identity.
* `IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sq`: a change of tube that is `C²` and first-jet
  identical over a compact set of base points satisfies `‖g(z, ξ) - (z, ξ)‖ ≤ C ‖ξ‖²` there.
* `IsCompact.exists_pos_forall_abs_norm_snd_sub_norm_le_mul`,
  `IsCompact.tendsto_sSup_norm_snd_div_sSup_norm_snd`: the normal distances `‖ξ‖` and `‖g₂(z, ξ)‖`
  of a point in the two tubes have ratio tending to one, uniformly; hence the largest normal
  distances of sets shrinking to the zero section have ratio tending to one.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *GR = SW: counting curves and connections*,
  J. Differential Geom. 52 (1999), 453–609.
-/

public section

noncomputable section

open Filter Metric Set Topology

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-! ### Normal dilations and normal linearizations of maps -/

/-- **The normal dilation of a map** `g` of `E × N`: the map
`(z, W) ↦ (g₁(z, a W), a⁻¹ g₂(z, a W))`. For `a ≠ 0` it is the conjugate `δ_a⁻¹ ∘ g ∘ δ_a` of
`g` by the normal dilation `δ_a(z, W) = (z, a W)`. -/
def normalDilationMap (g : E × N → E × N) (a : ℝ) (p : E × N) : E × N :=
  ((g (p.1, a • p.2)).1, a⁻¹ • (g (p.1, a • p.2)).2)

@[simp]
theorem normalDilationMap_apply (g : E × N → E × N) (a : ℝ) (p : E × N) :
    normalDilationMap g a p = ((g (p.1, a • p.2)).1, a⁻¹ • (g (p.1, a • p.2)).2) :=
  (rfl)

@[simp]
theorem normalDilationMap_one (g : E × N → E × N) : normalDilationMap g 1 = g := by
  funext p
  simp

/-- Normal dilations of maps compose: dilating by `a` and then by `b` is dilating by `a b`. -/
@[simp]
theorem normalDilationMap_normalDilationMap (g : E × N → E × N) (a b : ℝ) :
    normalDilationMap (normalDilationMap g a) b = normalDilationMap g (a * b) := by
  funext p
  simp only [normalDilationMap_apply, smul_smul, mul_inv_rev]

/-- For `a ≠ 0` the normal dilation is a conjugation, so it respects composition. -/
theorem normalDilationMap_comp (g h : E × N → E × N) {a : ℝ} (ha : a ≠ 0) :
    normalDilationMap (g ∘ h) a = normalDilationMap g a ∘ normalDilationMap h a := by
  funext p
  simp only [normalDilationMap_apply, Function.comp_apply, smul_inv_smul₀ ha]

@[simp]
theorem normalDilationMap_id {a : ℝ} (ha : a ≠ 0) :
    normalDilationMap (id : E × N → E × N) a = id := by
  funext p
  simp only [normalDilationMap_apply, id_eq, inv_smul_smul₀ ha]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The normal linearization of a map along the zero section**:
`g_N(z, W) = (g₁(z, 0), ∂_W g₂(z, 0) W)`. It is the limit of the normal dilations of `g` when `g`
is `C¹` near the zero section and maps it into itself
(`TauCeti.tendstoUniformlyOn_normalDilationMap_of_isOpen`, which takes `N` complete). -/
def normalLinearizationMap (g : E × N → E × N) (p : E × N) : E × N :=
  ((g (p.1, 0)).1, (fderiv ℝ g (p.1, 0) (0, p.2)).2)

@[simp]
theorem normalLinearizationMap_apply (g : E × N → E × N) (p : E × N) :
    normalLinearizationMap g p = ((g (p.1, 0)).1, (fderiv ℝ g (p.1, 0) (0, p.2)).2) :=
  (rfl)

/-- The normal linearization is invariant under every nonzero normal dilation. -/
@[simp]
theorem normalDilationMap_normalLinearizationMap (g : E × N → E × N) {a : ℝ} (ha : a ≠ 0) :
    normalDilationMap (normalLinearizationMap g) a = normalLinearizationMap g := by
  funext p
  have hp : ((0 : E), a • p.2) = a • ((0 : E), p.2) := by simp
  simp only [normalDilationMap_apply, normalLinearizationMap_apply]
  rw [hp, map_smul, Prod.smul_snd, inv_smul_smul₀ ha]

/-- If `g` fixes `(z, 0)` and its derivative there fixes the normal directions `(0, ξ)`, its normal
linearization fixes every point `(z, W)` of the normal fibre over `z`. -/
theorem normalLinearizationMap_eq_self {g : E × N → E × N} {p : E × N}
    (h₀ : g (p.1, 0) = (p.1, 0)) (h₁ : ∀ ξ, fderiv ℝ g (p.1, 0) (0, ξ) = (0, ξ)) :
    normalLinearizationMap g p = p := by
  simp [h₀, h₁]

/-! ### Convergence of the normal dilations -/

/-- The normal dilation of `g` at `(a, p)`, written with Hadamard's lemma so that it is defined
and smooth in `(a, p)` jointly, including `a = 0`: the quotient `a⁻¹ g₂(z, a W)` is replaced by
the average `∫₀¹ ∂_W g₂(z, t a W) W dt` of the normal derivative. -/
private def hadamardMap (g : E × N → E × N) (q : ℝ × (E × N)) : E × N :=
  ((g (q.2.1, q.1 • q.2.2)).1,
    ∫ t in (0 : ℝ)..1, (fderiv ℝ g (q.2.1, t • q.1 • q.2.2) (0, q.2.2)).2)

/-- On `normalSegmentDomain Ω`, the normal component of the average normal derivative of `g` is the
average normal derivative of the normal component `g₂` of `g`. -/
private theorem integral_fderiv_snd_eq {g : E × N → E × N} {Ω : Set (E × N)} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 1 g Ω) {q : ℝ × (E × N)} (hq : q ∈ normalSegmentDomain Ω) :
    ∫ t in (0 : ℝ)..1, (fderiv ℝ g (q.2.1, t • q.1 • q.2.2) (0, q.2.2)).2 =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x ↦ (g x).2) (q.2.1, t • q.1 • q.2.2) (0, q.2.2) := by
  simpa only [ContinuousLinearMap.coe_snd'] using
    integral_clm_fderiv_eq_integral_fderiv_of_mem_normalSegmentDomain
      (ContinuousLinearMap.snd ℝ E N) hΩ (hg.differentiableOn one_ne_zero) hq

/-- The Hadamard form of the normal dilation is `Cⁿ` in `(a, z, W)` where the normal segments lie
in an open set on which `g` is `C^(n+1)`. -/
private theorem contDiffOn_hadamardMap {g : E × N → E × N} {Ω : Set (E × N)} (hΩ : IsOpen Ω)
    {n : ℕ∞} (hg : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) g Ω) :
    ContDiffOn ℝ n (hadamardMap g) (normalSegmentDomain Ω) :=
  (hg.of_le le_self_add).comp_normalSegmentDomain.fst.prodMk
    ((contDiffOn_integral_fderiv_normalSegmentDomain hΩ hg.snd).congr fun _ hq ↦
      integral_fderiv_snd_eq hΩ (hg.of_le le_add_self) hq)

variable [CompleteSpace N]

/-- At `a = 0` the Hadamard form of the normal dilation is the normal linearization. -/
private theorem hadamardMap_zero (g : E × N → E × N) (p : E × N) :
    hadamardMap g (0, p) = normalLinearizationMap g p := by
  simp [hadamardMap]

/-- Away from `a = 0` the Hadamard form is the normal dilation, provided `g` is `C¹` on an open
set containing the segment from `(p.1, 0)` to `(p.1, a • p.2)` and maps `(p.1, 0)` to the zero
section. -/
private theorem hadamardMap_of_ne_zero {g : E × N → E × N} {Ω : Set (E × N)} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 1 g Ω) {a : ℝ} {p : E × N} (hg₀ : (g (p.1, 0)).2 = 0) (ha : a ≠ 0)
    (hq : (a, p) ∈ normalSegmentDomain Ω) :
    hadamardMap g (a, p) = normalDilationMap g a p := by
  have h := inv_smul_sub_eq_integral_fderiv_of_mem_normalSegmentDomain
    (f := fun x ↦ (g x).2) hΩ hg.snd ha hq
  rw [hg₀, sub_zero, ← integral_fderiv_snd_eq hΩ hg hq] at h
  rw [hadamardMap, normalDilationMap_apply, h]

variable {g : E × N → E × N}

/-- **The normal dilations of a map converge to its normal linearization in `Cⁱ`.** Let `g` be
`Cⁿ` on an open set `Ω`, with `i + 1 ≤ n`, and let `g` map the zero section into itself where it
meets `Ω`. Then the `i`-th derivatives of `δ_a⁻¹ ∘ g ∘ δ_a` converge to those of `g_N` uniformly
on every compact set `K` with `(z, 0) ∈ Ω` for `(z, W) ∈ K`, as `a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen {Ω K : Set (E × N)}
    {n : WithTop ℕ∞} {i : ℕ} (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ n g Ω)
    (hg₀ : ∀ z, (z, 0) ∈ Ω → (g (z, 0)).2 = 0) (hi : (i + 1 : WithTop ℕ∞) ≤ n)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i (normalDilationMap g a))
      (iteratedFDeriv ℝ i (normalLinearizationMap g)) (𝓝[≠] 0) K := by
  have hg1 : ContDiffOn ℝ 1 g Ω := hg.of_le (le_trans (by exact_mod_cast Nat.le_add_left 1 i) hi)
  have h := ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_slice
    (contDiffOn_hadamardMap (n := i) hΩ (hg.of_le (by exact_mod_cast hi)))
    (isOpen_normalSegmentDomain hΩ) hK (fun p hp ↦ zero_mem_normalSegmentDomain (hKΩ p hp))
    nhdsWithin_le_nhds (g := normalDilationMap g)
    (eventually_nhdsWithin_of_forall (s := {0}ᶜ) fun a ha y hy ↦ (hadamardMap_of_ne_zero hΩ hg1
      (hg₀ y.1 (mk_zero_mem_of_mem_normalSegmentDomain hy)) ha hy).symm)
  rwa [funext (hadamardMap_zero g)] at h

/-- **The normal dilations of a map converge to its normal linearization.** If `g` is `C¹` on an
open set `Ω` and maps the zero section into itself where it meets `Ω`, then
`δ_a⁻¹ ∘ g ∘ δ_a → g_N` uniformly on every compact set `K` with `(z, 0) ∈ Ω` for `(z, W) ∈ K`, as
`a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_normalDilationMap_of_isOpen {Ω K : Set (E × N)} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 1 g Ω) (hg₀ : ∀ z, (z, 0) ∈ Ω → (g (z, 0)).2 = 0)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    TendstoUniformlyOn (normalDilationMap g) (normalLinearizationMap g) (𝓝[≠] 0) K := by
  have h := (continuousMultilinearCurryFin0 ℝ (E × N) (E × N)).isometry
    |>.uniformContinuous.comp_tendstoUniformlyOn
      (tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen (i := 0) hΩ hg hg₀
        (by simp) hK hKΩ)
  simp only [Function.comp_def, continuousMultilinearCurryFin0_apply,
    iteratedFDeriv_zero_apply] at h
  exact h

/-- **First-jet identical tubes: rescaled `Cⁱ` convergence to the identity.** Let `g` be `Cⁿ` on
an open set `Ω`, with `i + 1 ≤ n`, and let `g(z, 0) = (z, 0)` and `dg(z, 0) (0, ξ) = (0, ξ)` where
`(z, 0)` lies in `Ω`; since `g` fixes the zero section near these points, this says that `g` has
the first jet of the identity there. Then the `i`-th derivatives of `δ_a⁻¹ ∘ g ∘ δ_a` converge to
those of the identity uniformly on every compact set `K` with `(z, 0) ∈ Ω` for `(z, W) ∈ K`, as
`a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen_of_firstJet_eq_id
    {Ω K : Set (E × N)} {n : WithTop ℕ∞} {i : ℕ} (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ n g Ω)
    (hg₀ : ∀ z, (z, 0) ∈ Ω → g (z, 0) = (z, 0))
    (hg₁ : ∀ z, (z, 0) ∈ Ω → ∀ ξ, fderiv ℝ g (z, 0) (0, ξ) = (0, ξ))
    (hi : (i + 1 : WithTop ℕ∞) ≤ n) (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i (normalDilationMap g a))
      (iteratedFDeriv ℝ i id) (𝓝[≠] 0) K := by
  refine (tendstoUniformlyOn_iteratedFDeriv_normalDilationMap_of_isOpen hΩ hg
    (fun z hz ↦ by simp [hg₀ z hz]) hi hK hKΩ).congr_right fun p hp ↦ ?_
  -- Near `p`, the base points stay over `Ω`, where `g_N` is the identity.
  refine (EventuallyEq.iteratedFDeriv ℝ ?_ i).eq_of_nhds
  filter_upwards [(by fun_prop : Continuous fun q : E × N ↦ (q.1, (0 : N))).continuousAt
    |>.preimage_mem_nhds (hΩ.mem_nhds (hKΩ p hp))] with q hq
  exact normalLinearizationMap_eq_self (hg₀ q.1 hq) (hg₁ q.1 hq)

end TauCeti

/-! ### First-jet identical tubes differ quadratically -/

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
  [NormedSpace ℝ N] {g : E × N → E × N}

/-- **First-jet identical tubes differ quadratically.** Let `K` be a compact set of base points
such that `g` is `C²` at `(z, 0)` with `g(z, 0) = (z, 0)` and `dg(z, 0) (0, ξ) = (0, ξ)` for
`z ∈ K`. Then there are `r > 0` and `C` such that `‖g(z, ξ) - (z, ξ)‖ ≤ C ‖ξ‖²` for `z ∈ K`
and `‖ξ‖ ≤ r`. -/
theorem IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sq {K : Set E} (hK : IsCompact K)
    (hg : ∀ z ∈ K, ContDiffAt ℝ 2 g (z, 0)) (hg₀ : ∀ z ∈ K, g (z, 0) = (z, 0))
    (hg₁ : ∀ z ∈ K, ∀ ξ, fderiv ℝ g (z, 0) (0, ξ) = (0, ξ)) :
    ∃ r > 0, ∃ C, ∀ z ∈ K, ∀ ξ : N, ‖ξ‖ ≤ r → ‖g (z, ξ) - (z, ξ)‖ ≤ C * ‖ξ‖ ^ 2 := by
  -- The normal slices `ξ ↦ g(z, ξ)` have a uniformly quadratic Taylor remainder at `ξ = 0`.
  obtain ⟨r, hr, C, hC⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul
    (F := fun z ξ ↦ g (z, ξ)) (x := fun _ ↦ (0 : N))
    (fun z hz ↦ by simpa only [Function.uncurry_def, Prod.mk.eta] using hg z hz) continuousOn_const
  refine ⟨r, hr, C, fun z hz ξ hξ ↦ ?_⟩
  -- The slice at `z` has derivative `ξ ↦ (0, ξ)` at `0`.
  have hd : fderiv ℝ (fun ξ ↦ g (z, ξ)) 0 ξ = (0, ξ) := by
    have h : HasFDerivAt (fun ξ ↦ g (z, ξ))
        (fderiv ℝ g (z, 0) ∘L ContinuousLinearMap.inr ℝ E N) 0 :=
      ((hg z hz).differentiableAt (by norm_num)).hasFDerivAt.comp (0 : N)
        (hasFDerivAt_prodMk_right z 0)
    rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hg₁ z hz]
  -- Since `g(z, 0) = (z, 0)`, the first-order remainder is `g(z, ξ) - (z, ξ)`.
  have hsub : g (z, ξ) - g (z, 0) - (0, ξ) = g (z, ξ) - (z, ξ) := by
    rw [hg₀ z hz, sub_sub, Prod.mk_add_mk, add_zero, zero_add]
  have hT : ‖g (z, ξ) - g (z, 0) - fderiv ℝ (fun ξ ↦ g (z, ξ)) 0 ξ‖ ≤
      C * max ‖ξ‖ 0 * ‖ξ‖ := by
    simpa only [zero_add, sub_zero, norm_zero] using hC z hz ξ 0 hξ (by simpa using hr.le)
  rwa [hd, hsub, max_eq_left (norm_nonneg ξ), mul_assoc, ← sq] at hT

/-- **Normal distances in first-jet identical tubes are asymptotic.** Under the hypotheses of
`IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sq`, for every `ε > 0` there is `δ > 0` such that
for `z ∈ K` and `‖ξ‖ < δ` the normal coordinate of `g(z, ξ)` has norm within `ε ‖ξ‖` of `‖ξ‖`. -/
theorem IsCompact.exists_pos_forall_abs_norm_snd_sub_norm_le_mul {K : Set E} (hK : IsCompact K)
    (hg : ∀ z ∈ K, ContDiffAt ℝ 2 g (z, 0)) (hg₀ : ∀ z ∈ K, g (z, 0) = (z, 0))
    (hg₁ : ∀ z ∈ K, ∀ ξ, fderiv ℝ g (z, 0) (0, ξ) = (0, ξ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ ξ : N, ‖ξ‖ < δ → |‖(g (z, ξ)).2‖ - ‖ξ‖| ≤ ε * ‖ξ‖ := by
  obtain ⟨r, hr, C, hC⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sq hg hg₀ hg₁
  refine ⟨min r (ε / (|C| + 1)), by positivity, fun z hz ξ hξ ↦ ?_⟩
  have hξε : (|C| + 1) * ‖ξ‖ ≤ ε :=
    ((lt_div_iff₀' (by positivity)).1 (hξ.trans_le (min_le_right _ _))).le
  calc |‖(g (z, ξ)).2‖ - ‖ξ‖| ≤ ‖(g (z, ξ) - (z, ξ)).2‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖g (z, ξ) - (z, ξ)‖ := norm_snd_le _
    _ ≤ C * ‖ξ‖ ^ 2 := hC z hz ξ (hξ.le.trans (min_le_left _ _))
    _ ≤ ((|C| + 1) * ‖ξ‖) * ‖ξ‖ := by
        rw [sq, ← mul_assoc]
        gcongr
        linarith [le_abs_self C]
    _ ≤ ε * ‖ξ‖ := by gcongr

/-- **The largest normal distances in first-jet identical tubes have ratio tending to one.** Under
the hypotheses of `IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sq`, let `S i` be sets of points
over `K` whose largest normal distance `a i = sup_{(z, ξ) ∈ S i} ‖ξ‖` is eventually positive and
tends to zero. Then the largest normal distance of `g (S i)` divided by `a i` tends to one. -/
theorem IsCompact.tendsto_sSup_norm_snd_div_sSup_norm_snd {K : Set E} (hK : IsCompact K)
    (hg : ∀ z ∈ K, ContDiffAt ℝ 2 g (z, 0)) (hg₀ : ∀ z ∈ K, g (z, 0) = (z, 0))
    (hg₁ : ∀ z ∈ K, ∀ ξ, fderiv ℝ g (z, 0) (0, ξ) = (0, ξ)) {ι : Type*} {l : Filter ι}
    {S : ι → Set (E × N)} (hSK : ∀ i, ∀ p ∈ S i, p.1 ∈ K)
    (hS : Tendsto (fun i ↦ sSup ((fun p ↦ ‖p.2‖) '' S i)) l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < sSup ((fun p ↦ ‖p.2‖) '' S i)) :
    Tendsto (fun i ↦ sSup ((fun p ↦ ‖(g p).2‖) '' S i) / sSup ((fun p ↦ ‖p.2‖) '' S i)) l
      (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ :=
    hK.exists_pos_forall_abs_norm_snd_sub_norm_le_mul hg hg₀ hg₁ (half_pos hε)
  filter_upwards [hpos, hS.eventually (gt_mem_nhds hδ)] with i hi hiδ
  set a := sSup ((fun p ↦ ‖p.2‖) '' S i)
  set b := sSup ((fun p ↦ ‖(g p).2‖) '' S i)
  -- A positive supremum of reals is that of a nonempty set bounded above.
  have hbdd : BddAbove ((fun p ↦ ‖p.2‖) '' S i) := by
    by_contra h
    exact hi.ne' (Real.sSup_of_not_bddAbove h)
  have hne : (S i).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hi.ne' (by simp [a, h])
  have hle : ∀ p ∈ S i, ‖p.2‖ ≤ a := fun p hp ↦ le_csSup hbdd (mem_image_of_mem _ hp)
  have hpt : ∀ p ∈ S i, |‖(g p).2‖ - ‖p.2‖| ≤ ε / 2 * a := fun p hp ↦
    (hgδ p.1 (hSK i p hp) p.2 ((hle p hp).trans_lt hiδ)).trans
      (mul_le_mul_of_nonneg_left (hle p hp) (by positivity))
  -- Each normal distance in one tube is within `ε a / 2` of that in the other.
  have hup : ∀ p ∈ S i, ‖(g p).2‖ ≤ a + ε / 2 * a := fun p hp ↦ by
    linarith [(abs_le.1 (hpt p hp)).2, hle p hp]
  have hbdd' : BddAbove ((fun p ↦ ‖(g p).2‖) '' S i) := ⟨_, forall_mem_image.2 hup⟩
  have hb : b ≤ a + ε / 2 * a := csSup_le (hne.image _) (forall_mem_image.2 hup)
  have ha : a ≤ b + ε / 2 * a := csSup_le (hne.image _) fun _ ⟨p, hp, hap⟩ ↦ by
    rw [← hap]
    linarith [(abs_le.1 (hpt p hp)).1, le_csSup hbdd' (mem_image_of_mem _ hp)]
  rw [Real.dist_eq, div_sub_one hi.ne', abs_div, abs_of_pos hi, div_lt_iff₀ hi, abs_lt]
  constructor <;> nlinarith
