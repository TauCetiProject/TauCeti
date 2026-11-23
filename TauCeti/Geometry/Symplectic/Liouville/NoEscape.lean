/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Manifold.MaximumPrinciple
import TauCeti.Analysis.Complex.HorizontalStrip

/-!
# No escape for `J`-holomorphic strips in a Liouville completion

Let `M` be a completion of the Liouville domain `W ⊆ M` for the symplectic form `ω = dα`, and let
`r = TauCeti.liouvilleRadialCoordinate Z W` be the radial coordinate of its cylindrical end
`M \ W`, smooth there by `TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleRadialCoordinate`.
An almost complex structure `J` is of contact type on the part `{r > R}` of the end when
`dr ∘ J = -α` there.

This file proves that holomorphic strips cannot escape into the cylindrical end. Let `J_w` be a
family of almost complex structures depending on the point `w` of the strip, as for continuation
strips and parametrized families of strips. If every `J_w` is of contact type and tamed by `ω` on
`{r > R}`, for some `R ≥ 1`, then a strip `ℝ × [0, 1] → M` which solves `∂ₜu = J_w(u) ∂ₛu` where
it enters `{r > R}`, and whose two boundary lines and two ends `|ℜ z| ≥ T` lie in `{r ≤ R}`, lies
entirely in `{r ≤ R}`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends`).
This is the a priori bound on the images of Floer strips between exact Lagrangians contained in
`{r ≤ R}`, needed before compactness for holomorphic curves can be applied. It is the maximum
principle `TauCeti.Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends` for the
radial coordinate and the Liouville primitive, whose exterior derivative is `ω`.

The equation is only required at the points which `u` maps into `{r > R}`. So the bound applies to
Floer strips `∂ₜu = J_w(u) ∂ₛu + X_w(u)` whose Hamiltonian vector fields `X_w` vanish on
`{r > R}`, for instance continuation strips between Hamiltonians which are constant outside a
compact subset of `{r ≤ R}`, with the same `R` for every member of a family of such strips.

The boundary lines of a Floer strip need not stay in `{r ≤ R}`: they lie on two exact Lagrangians,
which are only required to be cylindrical at infinity. A set `L` is cylindrical on `{r > R}` when
every Liouville trajectory through a point of `L` in `{r > R}` stays in `L` as long as it stays in
`{r > R}`, so that `L ∩ {r > R}` is the cone over a subset of a level of `r`. The Liouville field
`Z` is then tangent to `L`, and if `L` is isotropic, in the sense that `ω` vanishes on pairs of
vectors of its tangent cones, the Liouville primitive vanishes on these tangent cones,
`α(v) = ω(Z, v) = 0` (`TauCeti.IsLiouvilleCompletion.apply_eq_zero_of_mem_mtangentConeAt`). Along
a boundary line mapped into such a Lagrangian the Cauchy--Riemann equation then gives the Neumann
condition `∂ₜ(r ∘ u) = -α(∂ₛu) = 0` of
`TauCeti.Pseudoholomorphic.comp_le_of_mapsTo_of_comp_le_strip_ends`. The ends of a Floer strip
converge to Hamiltonian chords, and if these chords lie in `{r ≤ R}`, then for every `R' > R` the
ends `|ℜ z| ≥ T` of the strip lie in `{r < R'}` once `T` is large
(`TauCeti.exists_forall_mem_of_tendsto_strip_ends`). So a strip between two exact Lagrangians
cylindrical on `{r > R}`, whose ends converge to chords in `{r ≤ R}`, lies in the compact set
`{r ≤ R}`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_mapsTo_of_tendsto_strip_ends`).

## Main results

* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends`:
  a `J`-holomorphic strip with boundary lines and ends in `{r ≤ R}` lies in `{r ≤ R}`.
* `TauCeti.IsLiouvilleDomain.apply_eq_zero_of_eventually_flowOf_mem`: the Liouville primitive
  vanishes on the tangent cone of an isotropic set containing the Liouville trajectories through a
  point for small times.
* `TauCeti.IsLiouvilleCompletion.apply_eq_zero_of_mem_mtangentConeAt`: the Liouville primitive
  vanishes on the tangent cones of an isotropic set cylindrical on `{r > R}`.
* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_of_mapsTo_of_tendsto_strip_ends`:
  a `J`-holomorphic strip with boundary lines on isotropic sets cylindrical on `{r > R}`, and
  ends converging to chords in `{r ≤ R}`, lies in `{r ≤ R}`.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2.
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (completions and almost complex structures of contact type).
-/

public section

open Set Complex Filter
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {J : ℂ → SmoothAlmostComplexStructure I M} {u : ℂ → M} {z : ℂ}

/-- **No escape for strips in a Liouville completion.** Let `r` be the radial coordinate of a
completion of the Liouville domain `W`, let `R ≥ 1`, and let `J_w` be a family of almost complex
structures depending on the point `w` of the strip. Suppose that on `{r > R}` every `J_w` is of
contact type, `dr ∘ J_w = -α`, and is tamed by `ω`, that is `ω(v, J_w v) ≥ 0`. Let `r ∘ u` be
continuous on the closed strip `ℝ × [0, 1]`, and let `u` be `C²` and solve
`∂ₜu = J_w(u) ∂ₛu` at the points `w` of the open strip `ℝ × (0, 1)` which it maps into
`{r > R}`. If `u` maps both boundary lines `ℑ z = 0` and `ℑ z = 1` into `{r ≤ R}`, and also the
two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u` maps the whole strip into `{r ≤ R}`. -/
theorem liouvilleRadialCoordinate_le_of_le_strip_boundary_of_le_ends
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val) {R T : ℝ}
    (hR : 1 ≤ R)
    (hJ : ∀ w x, R < liouvilleRadialCoordinate Z W x → ∀ v,
      mvfderiv I (liouvilleRadialCoordinate Z W) x (J w x v) = -α.val x ![v])
    (htame : ∀ w x, R < liouvilleRadialCoordinate Z W x → ∀ v, 0 ≤ ω.eval₂ x v (J w x v))
    (hf : ContinuousOn (liouvilleRadialCoordinate Z W ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < liouvilleRadialCoordinate Z W (u z) →
      ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < liouvilleRadialCoordinate Z W (u z) →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J z (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (h₀ : ∀ z : ℂ, z.im = 0 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (h₁ : ∀ z : ℂ, z.im = 1 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → liouvilleRadialCoordinate Z W (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : liouvilleRadialCoordinate Z W (u z) ≤ R := by
  -- On `{r > R}` the point lies outside `W`, where `r` is smooth.
  have hρ (x : M) (hx : R < liouvilleRadialCoordinate Z W x) :
      ContMDiffAt I 𝓘(ℝ) 2 (liouvilleRadialCoordinate Z W) x :=
    (h.contMDiffAt_liouvilleRadialCoordinate hZ
      ((h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hR.trans_lt hx))).of_le (by simp)
  refine Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends hf hu hCR hρ
    (fun x _ ↦ ((isSmoothForm_def _ _).1 α.isSmoothForm x).mdifferentiableAt (by simp)) hJ
    (fun w x hx v ↦ ?_) h₀ h₁ hends hz₀ hz₁
  rw [h.mextDeriv_eq]
  simpa only [SmoothBundleForm.eval₂_apply] using htame w x hx v

/-! ### Lagrangians cylindrical at infinity -/

end IsLiouvilleCompletion

namespace IsLiouvilleDomain

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {L : Set M} {x : M} {v : TangentSpace I x}

/-- **The Liouville primitive vanishes on isotropic sets swept out by the Liouville flow.** Let
`L` be a set containing the Liouville trajectory through `x` for all small times, and suppose that
`ω` vanishes on pairs of vectors of the tangent cone of `L` at `x`, as it does on the tangent
spaces of a Lagrangian. Then the Liouville primitive `α` vanishes on that tangent cone: the
Liouville field `Z` is tangent to `L`, so `α(v) = ω(Z, v) = 0`. -/
theorem apply_eq_zero_of_eventually_flowOf_mem (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hL : ∀ᶠ t in 𝓝 0, flowOf Z t x ∈ L)
    (hiso : ∀ v ∈ mtangentConeAt I L x, ∀ w ∈ mtangentConeAt I L x, ω.eval₂ x v w = 0)
    (hv : v ∈ mtangentConeAt I L x) : α.val x ![v] = 0 := by
  -- The trajectory starts at `x`, so its velocity there is `Z x`.
  have hZx : Z x ∈ mtangentConeAt I L x := by
    have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
    have hcone := (isMIntegralCurveAt_flowOf hZs (mem_flowDomain_zero hZs x)).mem_mtangentConeAt hL
    generalize hy : flowOf Z 0 x = y at hcone
    rw [flowOf_zero] at hy
    exact hy ▸ hcone
  rw [← hZ, RoughForm.interior_apply]
  simpa using hiso _ hZx _ hv

end IsLiouvilleDomain

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {J : ℂ → SmoothAlmostComplexStructure I M} {u : ℂ → M} {z : ℂ}
  {L : Set M} {x : M} {v : TangentSpace I x}

/-- **The Liouville primitive vanishes on Lagrangians cylindrical at infinity.** Let `r` be the
radial coordinate of a completion of the Liouville domain `W`, and let `L` be cylindrical on the
region `{r > R}`: every Liouville trajectory through a point of `L` in `{r > R}` stays in `L` as
long as it stays in `{r > R}`, so that `L ∩ {r > R}` is the cone over a subset of a level of `r`.
If `ω` vanishes on pairs of vectors of the tangent cone of `L` at a point `x` with `r x > R`, then
the Liouville primitive `α` vanishes on that tangent cone. This is the condition `α|TL = 0` on the
cylindrical end of an exact Lagrangian. -/
theorem apply_eq_zero_of_mem_mtangentConeAt (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) {R : ℝ}
    (hL : ∀ t, R < liouvilleRadialCoordinate Z W (flowOf Z t x) → flowOf Z t x ∈ L)
    (hx : R < liouvilleRadialCoordinate Z W x)
    (hiso : ∀ v ∈ mtangentConeAt I L x, ∀ w ∈ mtangentConeAt I L x, ω.eval₂ x v w = 0)
    (hv : v ∈ mtangentConeAt I L x) : α.val x ![v] = 0 := by
  -- For small times the trajectory through `x` stays in `{r > R}`, hence in `L`.
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  have hcont : ContinuousAt (fun t ↦ liouvilleRadialCoordinate Z W (flowOf Z t x)) 0 :=
    (h.continuous_liouvilleRadialCoordinate hZ).continuousAt.comp
      (mdifferentiableAt_flowOf hZs (mem_flowDomain_zero hZs x)).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), R < liouvilleRadialCoordinate Z W (flowOf Z t x) :=
    hcont.eventually (lt_mem_nhds (by simpa only [flowOf_zero] using hx))
  exact h.toIsLiouvilleDomain.apply_eq_zero_of_eventually_flowOf_mem hZ
    (hev.mono fun t ht ↦ hL t ht) hiso hv

/-- **No escape for strips between exact Lagrangians cylindrical at infinity.** Let `r` be the
radial coordinate of a completion of the Liouville domain `W`, let `R ≥ 1`, and let `J_w` be a
family of almost complex structures depending on the point `w` of the strip which, on `{r > R}`,
are of contact type, `dr ∘ J_w = -α`, and tamed by `ω`. Let `L₀` and `L₁` be cylindrical on
`{r > R}`, every Liouville trajectory through a point of `Lᵢ` in `{r > R}` staying in `Lᵢ` as long
as it stays in `{r > R}`, and isotropic there in the sense that `ω` vanishes on pairs of vectors of
their tangent cones, as for exact Lagrangians cylindrical at infinity.

Let `u` map the boundary line `ℑ z = 0` into `L₀` and the line `ℑ z = 1` into `L₁`, with `r ∘ u`
continuous on the closed strip `ℝ × [0, 1]`. Suppose that at the points of the open strip which it
maps into `{r > R}`, `u` is `C²` and solves `∂ₜu = J_w(u) ∂ₛu`, and that at the points of the
boundary lines which it maps into `{r > R}`, it has a derivative `Du z` within the closed strip
satisfying the Cauchy--Riemann equation `Du z I = J z (u z) (Du z 1)`. Finally suppose that as
`s → -∞` and `s → +∞` the maps `t ↦ u (s + i t)` converge, jointly in `s` and `t ∈ [0, 1]`, to
chords `p` and `q` lying in `{r ≤ R}`. Then `u` maps the whole strip into `{r ≤ R}`.

The equation is only required at the points which `u` maps into `{r > R}`, so this applies to Floer
strips whose Hamiltonian vector fields vanish there. -/
theorem liouvilleRadialCoordinate_le_of_mapsTo_of_tendsto_strip_ends
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val) {R : ℝ}
    (hR : 1 ≤ R) {L₀ L₁ : Set M} {p q : ℝ → M} {Du : (z : ℂ) → ℂ →L[ℝ] TangentSpace I (u z)}
    (hJ : ∀ w x, R < liouvilleRadialCoordinate Z W x → ∀ v,
      mvfderiv I (liouvilleRadialCoordinate Z W) x (J w x v) = -α.val x ![v])
    (htame : ∀ w x, R < liouvilleRadialCoordinate Z W x → ∀ v, 0 ≤ ω.eval₂ x v (J w x v))
    (hcyl₀ : ∀ x ∈ L₀, R < liouvilleRadialCoordinate Z W x → ∀ t,
      R < liouvilleRadialCoordinate Z W (flowOf Z t x) → flowOf Z t x ∈ L₀)
    (hcyl₁ : ∀ x ∈ L₁, R < liouvilleRadialCoordinate Z W x → ∀ t,
      R < liouvilleRadialCoordinate Z W (flowOf Z t x) → flowOf Z t x ∈ L₁)
    (hiso₀ : ∀ x ∈ L₀, R < liouvilleRadialCoordinate Z W x →
      ∀ v ∈ mtangentConeAt I L₀ x, ∀ w ∈ mtangentConeAt I L₀ x, ω.eval₂ x v w = 0)
    (hiso₁ : ∀ x ∈ L₁, R < liouvilleRadialCoordinate Z W x →
      ∀ v ∈ mtangentConeAt I L₁ x, ∀ w ∈ mtangentConeAt I L₁ x, ω.eval₂ x v w = 0)
    (hf : ContinuousOn (liouvilleRadialCoordinate Z W ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < liouvilleRadialCoordinate Z W (u z) →
      ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < liouvilleRadialCoordinate Z W (u z) →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J z (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hDu : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < liouvilleRadialCoordinate Z W (u z) →
      HasMFDerivWithinAt 𝓘(ℝ, ℂ) I u (univ ×ℂ Icc 0 1) z (Du z))
    (hCRbdry : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < liouvilleRadialCoordinate Z W (u z) →
      Du z (Complex.I : ℂ) = J z (u z) (Du z 1))
    (hL₀ : MapsTo u {z : ℂ | z.im = 0} L₀) (hL₁ : MapsTo u {z : ℂ | z.im = 1} L₁)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, liouvilleRadialCoordinate Z W (p t) ≤ R)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, liouvilleRadialCoordinate Z W (q t) ≤ R)
    (hup : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun s : ℝ × ℝ ↦ u (s.1 + s.2 * Complex.I))
      (atBot ×ˢ 𝓝[Icc 0 1] t) (𝓝 (p t)))
    (huq : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun s : ℝ × ℝ ↦ u (s.1 + s.2 * Complex.I))
      (atTop ×ˢ 𝓝[Icc 0 1] t) (𝓝 (q t)))
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : liouvilleRadialCoordinate Z W (u z) ≤ R := by
  -- The ends only approach `{r ≤ R}`, so prove the bound `r ≤ R'` for every `R' > R`: on long
  -- enough ends the strip lies in the open set `{r < R'}`.
  refine le_of_forall_gt_imp_ge_of_dense fun R' hR' ↦ ?_
  obtain ⟨T, hT⟩ := exists_forall_mem_of_tendsto_strip_ends
    (U := {x | liouvilleRadialCoordinate Z W x < R'})
    (isOpen_lt (h.continuous_liouvilleRadialCoordinate hZ) continuous_const)
    (fun t ht ↦ (hp t ht).trans_lt hR') (fun t ht ↦ (hq t ht).trans_lt hR') hup huq
  -- On `{r > R'}` the point lies outside `W`, where `r` is smooth.
  have hρ (x : M) (hx : R' < liouvilleRadialCoordinate Z W x) :
      ContMDiffAt I 𝓘(ℝ) 2 (liouvilleRadialCoordinate Z W) x :=
    (h.contMDiffAt_liouvilleRadialCoordinate hZ
      ((h.one_lt_liouvilleRadialCoordinate_iff hZ).1 ((hR.trans_lt hR').trans hx))).of_le
        (by simp)
  refine Pseudoholomorphic.comp_le_of_mapsTo_of_comp_le_strip_ends hf
    (fun z h₀ h₁ hRz ↦ hu z h₀ h₁ (hR'.trans hRz)) (fun z h₀ h₁ hRz ↦ hCR z h₀ h₁ (hR'.trans hRz))
    hρ (fun x _ ↦ ((isSmoothForm_def _ _).1 α.isSmoothForm x).mdifferentiableAt (by simp))
    (fun w x hx ↦ hJ w x (hR'.trans hx)) (fun w x hx v ↦ ?_)
    (fun z hz hRz ↦ hDu z hz (hR'.trans hRz)) (fun z hz hRz ↦ hCRbdry z hz (hR'.trans hRz)) hL₀ hL₁
    (fun x hx hRx v hv ↦ h.apply_eq_zero_of_mem_mtangentConeAt hZ (hcyl₀ x hx (hR'.trans hRx))
      (hR'.trans hRx) (hiso₀ x hx (hR'.trans hRx)) hv)
    (fun x hx hRx v hv ↦ h.apply_eq_zero_of_mem_mtangentConeAt hZ (hcyl₁ x hx (hR'.trans hRx))
      (hR'.trans hRx) (hiso₁ x hx (hR'.trans hRx)) hv)
    (fun z hz h₀ h₁ ↦ (hT z hz h₀ h₁).le) hz₀ hz₁
  rw [h.mextDeriv_eq]
  simpa only [SmoothBundleForm.eval₂_apply] using htame w x (hR'.trans hx) v

end IsLiouvilleCompletion

end TauCeti
