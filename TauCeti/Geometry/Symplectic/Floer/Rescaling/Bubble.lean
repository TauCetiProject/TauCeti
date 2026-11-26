/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Basic
import TauCeti.Geometry.Symplectic.Floer.Compactness.Limit
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The bubble at a bubbling point of Floer solutions

Let `uₙ` be smooth solutions of the Floer equation `(du - X_K)^{0,1} = 0` on an open set `U` of the
domain `ℝ × ℝ`, for a `C²` perturbation `K = K_s ds + K_t dt` and a `C¹` domain-dependent almost
complex structure `J(z, x)` on a finite-dimensional symplectic vector space `(V, ω)`, with values
in a compact set `K`. Suppose their derivatives blow up along points `zₙ → z₀ ∈ U`. Rescaling at
the points chosen by Hofer's lemma
(`TauCeti.SymplecticForm.exists_rescale_isComplexLinearMap_perturbedFDeriv`) gives centres
`cₙ → z₀` and scales `εₙ → 0` for which the maps `vₙ(w) = uₙ(cₙ + εₙ w)` solve the rescaled Floer
equation on squares of radii tending to infinity, with derivative of norm one at the origin and
of norm at most two on the squares.

This file extracts the bubble from the rescaled maps
(`TauCeti.SymplecticForm.exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv`). Along a
subsequence, the `vₙ` converge locally uniformly on the whole plane to a `C¹` map
`v : ℝ × ℝ → K`, and so do their derivatives. The limit is

* holomorphic for the structure `J(z₀, ·)` frozen at the bubbling point;
* nonconstant, since `‖dv(0)‖ = 1`, with `‖dv‖ ≤ 2` everywhere;
* of symplectic area `∫ ω(∂ₛv, ∂ₜv)` at most the energy that concentrates at `z₀`: for every
  `δ > 0`, at most the lower limit of the Floer energies of the `uₙ` over the disc of radius `δ`
  about `z₀`.

This is a nonconstant `J(z₀, ·)`-holomorphic plane at the interior bubbling point, whose area is
bounded by the energy concentrating there; its identification with a sphere of the stable limit
needs the removal of singularities below. The locally uniform convergence of the maps is
Arzelà–Ascoli on exhausting discs
(`TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall`), and the
convergence of the derivatives is the interior estimate for the Floer equation, applied to the
rescaled equations as one family over the parameters `(cₙ, εₙ)`
(`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric`). The
limit is only shown to be `C¹`; its smoothness, the removal of its singularity at infinity, which
makes it a sphere, and the lower bound on its energy by the minimal energy of nonconstant spheres
need elliptic regularity of the limit.

## References

* H. Hofer, *Pseudoholomorphic curves in symplectizations with applications to the Weinstein
  conjecture in dimension three*, Invent. Math. 114 (1993), 515–563, for the choice of the
  rescaling points.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.2
  (rescaling where the derivatives blow up), Section 4.6 (bubbling) and Section 8.1 (bubbles of
  inhomogeneous equations are holomorphic for the frozen structure).
-/

public section

open Complex Filter Function Metric Set Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
  {z₀ : ℝ × ℝ}

variable [FiniteDimensional ℝ V]

/-! ### Convergence of the derivatives -/

/-- The derivatives of rescaled Floer solutions converge on an open set `B` of `ℝ × ℝ`. Let `uₙ`
be smooth on an open `U ∋ z₀`, and let the rescaled maps `vₙ(w) = uₙ(cₙ + εₙ w)`, with `cₙ → z₀`
and `εₙ → 0`, solve the rescaled Floer equation on `B` with derivatives of norm at most `M` there,
and converge pointwise there to `v`. Then `v` is `C¹` on `B` and `dvₙ → dv` locally uniformly on
`B`. The rescaled equations form one family of data `J(c + ε w, x)` and `ε X_K(c + ε w, x)` over
the parameter `(c, ε)`, jointly `C¹` in the parameter and the point `(w, x)`. -/
private theorem tendstoLocallyUniformlyOn_fderiv_rescale (ω : SymplecticForm V) (hU : IsOpen U)
    (hz₀ : z₀ ∈ U) (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hJ : ContDiffOn ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (u n) U) {c : ℕ → ℝ × ℝ} {ε : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 z₀)) (hε : Tendsto ε atTop (𝓝 0)) {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    {M : ℝ} {v : ℝ × ℝ → V} (hmem : ∀ n, ∀ w ∈ B, c n + ε n • w ∈ U)
    (hbd : ∀ n, ∀ w ∈ B, ‖fderiv ℝ (fun w ↦ u n (c n + ε n • w)) w‖ ≤ M)
    (hsol : ∀ n, ∀ w ∈ B, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (c n + ε n • w) (u n (c n + ε n • w)))
      (ω.perturbedFDeriv (fun w x ↦ ε n * Ks (c n + ε n • w) x)
        (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w :
        ℝ × ℝ →ₗ[ℝ] V))
    (hlim : ∀ w ∈ B, Tendsto (fun n ↦ u n (c n + ε n • w)) atTop (𝓝 (v w))) :
    ContDiffOn ℝ 1 v B ∧ TendstoLocallyUniformlyOn
      (fun n ↦ fderiv ℝ (fun w ↦ u n (c n + ε n • w))) (fderiv ℝ v) atTop B := by
  -- The Hamiltonian one-form of `K` is `C¹`, as a constant family over `Unit`.
  have hlift {H : ℝ × ℝ → V → ℝ} (hH : ContDiffOn ℝ 2 (uncurry H) (U ×ˢ univ)) :
      ContDiffOn ℝ (1 + 1) (fun q : Unit × ((ℝ × ℝ) × V) ↦ H q.2.1 q.2.2)
        (univ ×ˢ (U ×ˢ univ)) := by
    rw [one_add_one_eq_two]
    exact hH.comp contDiffOn_snd fun _ hq ↦ hq.2
  have hX : ContDiffOn ℝ 1 (fun q : (ℝ × ℝ) × V ↦ ω.hamiltonianOneForm Ks Kt q.1 q.2)
      (U ×ˢ univ) :=
    (ω.contDiffOn_hamiltonianOneForm (P := Unit) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt)
      (isOpen_univ.prod (hU.prod isOpen_univ)) (hlift hKs) (hlift hKt)).comp
      ((contDiff_const (c := ())).prodMk contDiff_id).contDiffOn fun q hq ↦ ⟨mem_univ _, hq⟩
  -- The data at the parameter `(c, ε)` and the point `(w, x)`.
  set g : (((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) × V → (ℝ × ℝ) × V :=
    fun q ↦ (q.1.1.1 + q.1.1.2 • q.1.2, q.2)
  have hg : ContDiff ℝ 1 g := by fun_prop
  obtain ⟨hvc, hconv, -⟩ := tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric
    (J := fun q ↦ (J (g q).1 (g q).2).toLinearMap.toContinuousLinearMap)
    (X := fun q ↦ q.1.1.2 • ω.hamiltonianOneForm Ks Kt (g q).1 (g q).2)
    ((hU.prod isOpen_univ).preimage hg.continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage _ _))
    (contDiff_fst.fst.snd.contDiffOn.smul (hX.comp hg.contDiffOn (mapsTo_preimage _ _))) hB
    (p := fun n ↦ (c n, ε n)) (p₀ := (z₀, 0)) (u := fun n w ↦ u n (c n + ε n • w)) (v := v)
    (hc.prodMk_nhds hε) (fun w _ ↦ ⟨by simpa [g] using hz₀, mem_univ _⟩)
    (fun n ↦ (hu n).comp (contDiff_const.add (contDiff_id.const_smul (ε n))).contDiffOn
      fun w hw ↦ hmem n w hw)
    (fun n w _ ζ ↦ by simp [g])
    (fun n w hw ↦ by
      have h := (ω.isComplexLinearMap_perturbedFDeriv_iff_fderiv_stdComplexLineImag_sub
        (J := fun w x ↦ J (c n + ε n • w) x)).1 (hsol n w hw)
      rw [hamiltonianOneForm_rescale] at h
      simpa [g] using h)
    (fun C _ hCB ↦ ⟨M, fun n w hw ↦ hbd n w (hCB hw)⟩) hlim
  exact ⟨hvc, hconv⟩

/-- The rescaled Floer solutions `vₙ(w) = uₙ(cₙ + εₙ w)` of a sequence of smooth solutions `uₙ`
on `U ∋ z₀`, with `cₙ → z₀` and `εₙ → 0`, that eventually solve the rescaled equation with
derivatives of norm at most `2` on squares of radii `Rₙ → ∞`, and that converge pointwise to `g`:
then `g` is `C¹` and `J(z₀, ·)`-holomorphic, and `dvₙ → dg` locally uniformly on the plane. -/
private theorem contDiff_and_tendstoLocallyUniformly_fderiv_rescale (ω : SymplecticForm V)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hJ : ContDiffOn ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (u n) U)
    (hsol : ∀ n, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u n y))
      (ω.perturbedFDeriv Ks Kt (u n) y : ℝ × ℝ →ₗ[ℝ] V))
    {c : ℕ → ℝ × ℝ} {ε R : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 z₀)) (hε : Tendsto ε atTop (𝓝 0))
    (hR : Tendsto R atTop atTop)
    (hev : ∀ᶠ n in atTop, ∀ w, ‖w‖ ≤ R n → c n + ε n • w ∈ U ∧
      ‖fderiv ℝ (fun w ↦ u n (c n + ε n • w)) w‖ ≤ 2 ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (c n + ε n • w) (u n (c n + ε n • w)))
        (ω.perturbedFDeriv (fun w x ↦ ε n * Ks (c n + ε n • w) x)
          (fun w x ↦ ε n * Kt (c n + ε n • w) x) (fun w ↦ u n (c n + ε n • w)) w :
          ℝ × ℝ →ₗ[ℝ] V))
    {g : ℝ × ℝ → V} (hlim : ∀ w, Tendsto (fun n ↦ u n (c n + ε n • w)) atTop (𝓝 (g w))) :
    ContDiff ℝ 1 g ∧ TendstoLocallyUniformly (fun n ↦ fderiv ℝ (fun w ↦ u n (c n + ε n • w)))
      (fderiv ℝ g) atTop ∧
      ∀ w, IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ) (J z₀) g w := by
  have hcont (w : ℝ × ℝ) : (z₀, g w) ∈ U ×ˢ (univ : Set V) := ⟨hz₀, mem_univ _⟩
  have hX (H : ℝ × ℝ → V → ℝ) (hH : ContDiffOn ℝ 2 (uncurry H) (U ×ˢ univ)) (w : ℝ × ℝ) :=
    (ω.continuousOn_uncurry_hamiltonianVectorField (hH.of_le (by norm_num))).continuousAt
      ((hU.prod isOpen_univ).mem_nhds (hcont w))
  -- On the open square of radius `m`, from an index `k` on.
  have hball (m : ℕ) : ContDiffOn ℝ 1 g (ball 0 m) ∧ TendstoLocallyUniformlyOn
      (fun n ↦ fderiv ℝ (fun w ↦ u n (c n + ε n • w))) (fderiv ℝ g) atTop (ball 0 m) ∧
      ∀ w ∈ ball (0 : ℝ × ℝ) m,
        IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ) (J z₀) g w := by
    obtain ⟨k, hk⟩ := (hev.and (hR.eventually_ge_atTop m)).exists_forall_of_atTop
    have hkR (n : ℕ) (w : ℝ × ℝ) (hw : w ∈ ball (0 : ℝ × ℝ) m) :=
      (hk (n + k) (Nat.le_add_left k n)).1 w
        ((mem_ball_zero_iff.1 hw).le.trans (hk _ (Nat.le_add_left k n)).2)
    have hk' := tendsto_add_atTop_nat k
    obtain ⟨h1, h2⟩ := tendstoLocallyUniformlyOn_fderiv_rescale ω hU hz₀ hKs hKt hJ
      (u := fun n ↦ u (n + k)) (fun n ↦ hu _) (hc.comp hk') (hε.comp hk') isOpen_ball
      (fun n w hw ↦ (hkR n w hw).1) (fun n w hw ↦ (hkR n w hw).2.1)
      (fun n w hw ↦ (hkR n w hw).2.2) fun w _ ↦ (hlim w).comp hk'
    refine ⟨h1, fun s hs x hx ↦ ?_, ω.isJHolomorphicAt_of_tendstoLocallyUniformlyOn_rescale
      isOpen_ball (hc.comp hk') (hε.comp hk') (fun w _ ↦ (hlim w).comp hk') h2
      (fun w _ ↦ hJ.continuousOn.continuousAt ((hU.prod isOpen_univ).mem_nhds (hcont w)))
      (fun w _ ↦ hX Ks hKs w) (fun w _ ↦ hX Kt hKt w) (fun n w hw ↦ ?_)
      (Eventually.of_forall fun n w hw ↦ hsol _ _ (hkR n w hw).1)⟩
    · -- Undo the shift by `k`.
      obtain ⟨t, ht, hevt⟩ := h2 s hs x hx
      obtain ⟨N, hN⟩ := eventually_atTop.1 hevt
      refine ⟨t, ht, eventually_atTop.2 ⟨N + k, fun n hn ↦ ?_⟩⟩
      have hnk : n - k + k = n := by omega
      simpa only [Function.comp_apply, hnk] using hN (n - k) (by omega)
    · have hmem := (hkR n w hw).1
      exact ((hu _).differentiableOn (by simp) _ hmem).differentiableAt (hU.mem_nhds hmem)
  -- The open squares of integer radii exhaust the plane.
  refine ⟨contDiff_iff_contDiffAt.2 fun w ↦ ?_, ?_, fun w ↦ ?_⟩
  · obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    exact (hball m).1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hm))
  · rw [← tendstoLocallyUniformlyOn_univ, ← iUnion_ball_nat (0 : ℝ × ℝ)]
    exact tendstoLocallyUniformlyOn_iUnion (fun m ↦ isOpen_ball) fun m ↦ (hball m).2.1
  · obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    exact (hball m).2.2 w (mem_ball_zero_iff.2 hm)

/-! ### The bubble -/

/-- **The bubble at a bubbling point of Floer solutions.** Let `K = K_s ds + K_t dt` be `C²` and
`J(z, x)` be `C¹` on `U × V` for an open set `U ⊆ ℝ × ℝ`, and let `uₙ` be smooth solutions of the
Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on `U` with values in a compact set `K`. If
the derivatives blow up along points `zₙ → z₀ ∈ U`, then there are a subsequence `φ`, centres
`cₙ → z₀`, scales `εₙ > 0` with `εₙ → 0`, and a `C¹` map `v : ℝ × ℝ → K` such that

* the rescaled maps `w ↦ u_{φ n}(cₙ + εₙ w)` and their derivatives converge to `v` and its
  derivative, locally uniformly on `ℝ × ℝ`;
* `v` is holomorphic for the structure `J(z₀, ·)` frozen at `z₀`;
* `‖dv(0)‖ = 1`, so `v` is not constant, and `‖dv‖ ≤ 2` everywhere;
* for every `δ > 0`, the symplectic area `∫ ω(∂ₛv, ∂ₜv)` of `v` is at most the lower limit of the
  Floer energies of the `u_{φ n}` over the disc of radius `δ` about `z₀`. -/
theorem exists_tendstoLocallyUniformly_rescale_of_tendsto_norm_fderiv (ω : SymplecticForm V)
    {K : Set V} {u : ℕ → ℝ × ℝ → V} {z : ℕ → ℝ × ℝ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hK : IsCompact K) (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hJ : ContDiffOn ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (hu : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (u n) U) (huK : ∀ n, MapsTo (u n) U K)
    (hsol : ∀ n, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u n y))
      (ω.perturbedFDeriv Ks Kt (u n) y : ℝ × ℝ →ₗ[ℝ] V))
    (hz : Tendsto z atTop (𝓝 z₀)) (hblow : Tendsto (fun n ↦ ‖fderiv ℝ (u n) (z n)‖) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (c : ℕ → ℝ × ℝ) (ε : ℕ → ℝ) (v : ℝ × ℝ → V), StrictMono φ ∧
      (∀ n, 0 < ε n) ∧ Tendsto c atTop (𝓝 z₀) ∧ Tendsto ε atTop (𝓝 0) ∧
      TendstoLocallyUniformly (fun n w ↦ u (φ n) (c n + ε n • w)) v atTop ∧
      TendstoLocallyUniformly (fun n ↦ fderiv ℝ (fun w ↦ u (φ n) (c n + ε n • w)))
        (fderiv ℝ v) atTop ∧
      ContDiff ℝ 1 v ∧ (∀ w, v w ∈ K) ∧
      (∀ w, IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ) (J z₀) v w) ∧
      ‖fderiv ℝ v 0‖ = 1 ∧ (∀ w, ‖fderiv ℝ v w‖ ≤ 2) ∧
      ∀ δ > 0, ∫⁻ w, ENNReal.ofReal
          (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) ≤
        liminf (fun n ↦ ∫⁻ y in ball z₀ δ,
          ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u (φ n)) y)) atTop := by
  -- Rescale at the points chosen by Hofer's lemma.
  obtain ⟨c, ε, R, hε, hc, hε0, hR, -, hev⟩ := ω.exists_rescale_isComplexLinearMap_perturbedFDeriv
    (J := J) hU hz₀ (fun n ↦ (hu n).of_le (by simp)) (Eventually.of_forall hsol) hz hblow
  set ru : ℕ → ℝ × ℝ → V := fun n w ↦ u n (c n + ε n • w)
  obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
  -- From the index `N` on, the rescaled maps are `2`-Lipschitz on the discs of radius `R n`, with
  -- values in `K` there, so a subsequence converges locally uniformly by Arzelà–Ascoli.
  have hlip (n : ℕ) : LipschitzOnWith 2 (ru (n + N)) (closedBall 0 (R (n + N))) := by
    have h := hN (n + N) (Nat.le_add_left N n)
    refine (convex_closedBall _ _).lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ) (fun w hw ↦ ?_)
      fun w hw ↦ ?_
    · have hmem := (h.2 w (mem_closedBall_zero_iff.1 hw)).1
      exact (((hu _).differentiableOn (by simp) _ hmem).differentiableAt
        (hU.mem_nhds hmem)).comp w
          ((differentiableAt_id.const_smul (ε (n + N))).const_add (c (n + N)))
    · rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact_mod_cast (h.2 w (mem_closedBall_zero_iff.1 hw)).2.1
  obtain ⟨ψ, hψ, g, htr⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall hK
    ((tendsto_add_atTop_iff_nat N).2 hR) hlip
    fun n w hw ↦ huK _ ((hN _ (Nat.le_add_left N n)).2 w (mem_closedBall_zero_iff.1 hw)).1
  set φ : ℕ → ℕ := fun n ↦ ψ n + N
  have hφ : StrictMono φ := fun m n hmn ↦ Nat.add_lt_add_right (hψ hmn) N
  have hφN (n : ℕ) : N ≤ φ n := Nat.le_add_left N (ψ n)
  have htr' : TendstoLocallyUniformly (fun n ↦ ru (φ n)) g atTop := htr
  have hRφ : Tendsto (fun n ↦ R (φ n)) atTop atTop := hR.comp hφ.tendsto_atTop
  have hptw (w : ℝ × ℝ) : Tendsto (fun n ↦ ru (φ n) w) atTop (𝓝 (g w)) :=
    htr'.tendsto_at w
  -- The derivatives converge too, and the limit is a `J(z₀, ·)`-holomorphic plane.
  obtain ⟨hgc, hderiv, hhol⟩ := contDiff_and_tendstoLocallyUniformly_fderiv_rescale ω hU hz₀ hKs
    hKt hJ (fun n ↦ hu _) (fun n ↦ hsol _) (hc.comp hφ.tendsto_atTop)
    (hε0.comp hφ.tendsto_atTop) hRφ (Eventually.of_forall fun n ↦ (hN _ (hφN n)).2) hptw
  have hnorm (w : ℝ × ℝ) := (continuous_norm.tendsto _).comp
    (hderiv.tendsto_at w)
  refine ⟨φ, c ∘ φ, ε ∘ φ, g, hφ, fun n ↦ hε _, hc.comp hφ.tendsto_atTop,
    hε0.comp hφ.tendsto_atTop, htr', hderiv, hgc, fun w ↦ hK.isClosed.mem_of_tendsto (hptw w)
      ((hRφ.eventually_ge_atTop ‖w‖).mono fun n hn ↦ huK _ ((hN _ (hφN n)).2 w hn).1), hhol,
    tendsto_nhds_unique (hnorm 0) (tendsto_const_nhds.congr fun n ↦ ((hN _ (hφN n)).1).symm),
    fun w ↦ le_of_tendsto (hnorm w)
      ((hRφ.eventually_ge_atTop ‖w‖).mono fun n hn ↦ ((hN _ (hφN n)).2 w hn).2.1),
    fun δ hδ ↦ ω.lintegral_symplecticForm_le_liminf_of_tendsto_rescale hU hz₀
      (fun n ↦ (hu _).of_le (by simp)) (hKs.of_le (by norm_num)) (hKt.of_le (by norm_num))
      (hc.comp hφ.tendsto_atTop) (hε0.comp hφ.tendsto_atTop) hptw
      (fun w ↦ hderiv.tendsto_at w) hδ⟩

end TauCeti.SymplecticForm
