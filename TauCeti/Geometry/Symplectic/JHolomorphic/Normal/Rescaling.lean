/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Normal rescaling of an almost complex structure along a pseudoholomorphic curve

Near an embedded pseudoholomorphic curve `C` in an almost complex manifold, choose coordinates
`(z, W) ∈ E × N` in which `C` is the zero section `E × {0}`, for instance through a tubular
map `F` of the normal bundle with `F(z, 0) = z`. The almost complex structure becomes a field
`J : E × N → (E × N →L[ℝ] E × N)`, and `C` is `J`-holomorphic exactly when `J(z, 0)` preserves the
tangent spaces `E × {0}` of the zero section, that is, the normal component of `J(z, 0) (v, 0)`
vanishes. Taubes studies Seiberg–Witten solutions concentrating along `C` in the coordinates
`Φ_a(z, W) = F(z, a W)`, which magnify the normal directions by `a⁻¹` as `a → 0`. In the local
coordinates this is the normal dilation `δ_a(z, W) = (z, a W)`, and the structure read in the
dilated coordinates is the pullback

`(δ_a^* J)(z, W) = S_a⁻¹ ∘ J(z, a W) ∘ S_a`,  `S_a (v, n) = (v, a n)`

(`TauCeti.normalDilation J a`; for `a ≠ 0` it is `OpenPartialHomeomorph.pullbackEnd` along the
dilation, `TauCeti.normalDilation_eq_pullbackEnd`, and the dilations compose,
`TauCeti.normalDilation_normalDilation`). Writing `J` in blocks along `E × N`, the dilation
multiplies the block `N → E` by `a` and divides the block `E → N` by `a`. The latter vanishes on
the zero section, so its quotient by `a` converges to its normal derivative, and the limit is the
**normal linearization** of `J` along the zero section (`TauCeti.normalLinearization J`):

`J_N(z, W) (v, n) = (J_EE(z, 0) v,  ∂_W J_NE(z, 0)[W] v + J_NN(z, 0) n)`.

The term `∂_W J_NE(z, 0)[W]`, linear in `W`, is retained in the limit: it is the zeroth-order
coefficient of the real-linear equation cut out by the `J_N`-holomorphic graphs (last item below),
the normal Cauchy–Riemann equation of the zero section in these coordinates. This file proves:

* **convergence in `Cᵏ`**: if `J` is `C^(k+1)` and the zero section is `J`-holomorphic, then for
  every `i ≤ k` the `i`-th derivatives of `δ_a^* J` converge to those of `J_N` uniformly on every
  compact set as `a → 0`, `a ≠ 0` (`TauCeti.tendstoUniformlyOn_iteratedFDeriv_normalDilation`;
  `TauCeti.tendstoUniformlyOn_normalDilation` for the fields themselves when `J` is `C¹`). The
  proof writes `δ_a^* J` through Hadamard's lemma as a field depending smoothly on `(a, z, W)`
  jointly, including `a = 0`, where its value is `J_N`. These statements, and the fact that `J_N`
  squares to `-1` below, take `E` and `N` complete, so that this average is a Bochner integral;
* `J_N` is again an almost complex structure when `J` is one
  (`TauCeti.normalLinearization_apply_normalLinearization_apply`), it is `C^k` when `J` is
  `C^(k+1)` (`TauCeti.contDiff_normalLinearization`), and it is invariant under every normal
  dilation (`TauCeti.normalDilation_normalLinearization`);
* the vertical directions `{0} × N` are `J_N`-invariant and the projection to `E` intertwines
  `J_N(z, W)` with the structure `j(z) = J_EE(z, 0)` of the curve
  (`TauCeti.normalLinearization_apply`);
* a linear map `(v ↦ (v, D v))`, such as the derivative at `z` of the graph of a section `s` with
  `s(z) = W` and `D = ds(z)`, is complex linear from `j(z)` to `J_N(z, W)` exactly when
  `D ∘ j(z) = ∂_W J_NE(z, 0)[W] + J_NN(z, 0) ∘ D`
  (`TauCeti.normalLinearization_comp_prod_eq_iff`). So the `J_N`-holomorphic graphs are the
  solutions of a real-linear first-order equation in `s`, with the zeroth-order coefficient
  `W ↦ ∂_W J_NE(z, 0)[W]`.

The coordinates are those of a fixed tubular chart: the global choice of `F` (Taubes uses a
foliation by `J`-holomorphic normal disks) is a separate construction.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
  [NormedSpace ℝ N]

/-- **The normal dilation of an endomorphism field.** For a field `J` on `E × N` and `a : ℝ`, the
field `(z, W) ↦ S_a⁻¹ ∘ J(z, a W) ∘ S_a`, where `S_a (v, n) = (v, a n)`. For `a ≠ 0` it is the
pullback of `J` along the normal dilation `(z, W) ↦ (z, a W)`. -/
def normalDilation (J : E × N → E × N →L[ℝ] E × N) (a : ℝ) (p : E × N) : E × N →L[ℝ] E × N :=
  (ContinuousLinearMap.id ℝ E).prodMap (a⁻¹ • ContinuousLinearMap.id ℝ N) ∘L J (p.1, a • p.2) ∘L
    (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N)

@[simp]
theorem normalDilation_apply (J : E × N → E × N →L[ℝ] E × N) (a : ℝ) (p v : E × N) :
    normalDilation J a p v =
      ((J (p.1, a • p.2) (v.1, a • v.2)).1, a⁻¹ • (J (p.1, a • p.2) (v.1, a • v.2)).2) := by
  simp [normalDilation, Prod.map]

@[simp]
theorem normalDilation_one (J : E × N → E × N →L[ℝ] E × N) : normalDilation J 1 = J := by
  funext p
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp

/-- Normal dilations compose: dilating by `a` and then by `b` is dilating by `a b`. -/
@[simp]
theorem normalDilation_normalDilation (J : E × N → E × N →L[ℝ] E × N) (a b : ℝ) :
    normalDilation (normalDilation J a) b = normalDilation J (a * b) := by
  funext p
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [smul_smul, mul_comm]

/-- For `a ≠ 0` the normal dilation of `J` is its pullback (`OpenPartialHomeomorph.pullbackEnd`)
along the linear automorphism `(z, W) ↦ (z, a W)` of `E × N`. -/
theorem normalDilation_eq_pullbackEnd (J : E × N → E × N →L[ℝ] E × N) {a : ℝ} (ha : a ≠ 0) :
    normalDilation J a = OpenPartialHomeomorph.pullbackEnd
      (Homeomorph.toOpenPartialHomeomorph (ContinuousLinearEquiv.toHomeomorph
        ((ContinuousLinearEquiv.refl ℝ E).prodCongr
          (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha) : N ≃L[ℝ] N)))) J := by
  have hs (x : N) :
      (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha) : N ≃L[ℝ] N).symm x = a⁻¹ • x := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    simp [smul_smul, ha]
  funext p
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [OpenPartialHomeomorph.pullbackEnd_apply, ContinuousLinearEquiv.fderiv, Prod.map, hs]

/-- **The normal linearization of an endomorphism field along the zero section**:
`J_N(z, W) (v, n) = (J_EE(z, 0) v, ∂_W J_NE(z, 0)[W] v + J_NN(z, 0) n)`, where `J_EE`, `J_NE`
and `J_NN` are the blocks of `J` along `E × N`. It is the limit of the normal dilations of `J` when
the zero section is `J`-holomorphic (`TauCeti.tendstoUniformlyOn_normalDilation`). -/
def normalLinearization (J : E × N → E × N →L[ℝ] E × N) (p : E × N) : E × N →L[ℝ] E × N :=
  ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L J (p.1, 0) ∘L
      ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
    ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
      (fderiv ℝ J (p.1, 0) (0, p.2) ∘L ContinuousLinearMap.inl ℝ E N ∘L
          ContinuousLinearMap.fst ℝ E N +
        J (p.1, 0) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)

@[simp]
theorem normalLinearization_apply (J : E × N → E × N →L[ℝ] E × N) (p v : E × N) :
    normalLinearization J p v =
      ((J (p.1, 0) (v.1, 0)).1,
        (fderiv ℝ J (p.1, 0) (0, p.2) (v.1, 0)).2 + (J (p.1, 0) (0, v.2)).2) := by
  simp [normalLinearization]

/-! ### Algebraic properties -/

/-- For `a ≠ 0` the normal dilation of an almost complex structure squares to `-1`. -/
theorem normalDilation_apply_normalDilation_apply {J : E × N → E × N →L[ℝ] E × N}
    (hJ : ∀ p v, J p (J p v) = -v) {a : ℝ} (ha : a ≠ 0) (p v : E × N) :
    normalDilation J a p (normalDilation J a p v) = -v := by
  have hw (w : E × N) : (w.1, a • a⁻¹ • w.2) = w := by
    rw [smul_inv_smul₀ ha]
  simp only [normalDilation_apply, hw, hJ, Prod.fst_neg, Prod.snd_neg, smul_neg,
    inv_smul_smul₀ ha]
  rfl

/-- **The normal linearization is invariant under normal dilations**: its block `E → N` is
linear in the normal coordinate and its other blocks do not depend on it. -/
theorem normalDilation_normalLinearization (J : E × N → E × N →L[ℝ] E × N) {b : ℝ}
    (hb : b ≠ 0) : normalDilation (normalLinearization J) b = normalLinearization J := by
  funext p
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hdir : ((0 : E), b • p.2) = b • ((0 : E), p.2) := by simp
  have hv : ((0 : E), b • v.2) = b • ((0 : E), v.2) := by simp
  simp only [normalDilation_apply, normalLinearization_apply, hdir, hv, map_smul]
  simp [inv_smul_smul₀ hb]

/-- **Holomorphic graphs of the normal linearization.** Let `j = J_EE(z, 0)` be the structure of
the zero section at `z`. A linear map `v ↦ (v, D v)`, such as the derivative at `z` of the graph of
a section `s` with `s(z) = W` and `D = ds(z)`, is complex linear from `j` to `J_N(z, W)` exactly
when `D` solves the real-linear equation `D ∘ j = ∂_W J_NE(z, 0)[W] + J_NN(z, 0) ∘ D`. -/
theorem normalLinearization_comp_prod_eq_iff (J : E × N → E × N →L[ℝ] E × N) (z : E) (W : N)
    (D : E →L[ℝ] N) :
    normalLinearization J (z, W) ∘L (ContinuousLinearMap.id ℝ E).prod D =
        (ContinuousLinearMap.id ℝ E).prod D ∘L
          (ContinuousLinearMap.fst ℝ E N ∘L J (z, 0) ∘L ContinuousLinearMap.inl ℝ E N) ↔
      D ∘L (ContinuousLinearMap.fst ℝ E N ∘L J (z, 0) ∘L ContinuousLinearMap.inl ℝ E N) =
        ContinuousLinearMap.snd ℝ E N ∘L fderiv ℝ J (z, 0) (0, W) ∘L
            ContinuousLinearMap.inl ℝ E N +
          ContinuousLinearMap.snd ℝ E N ∘L J (z, 0) ∘L ContinuousLinearMap.inr ℝ E N ∘L D := by
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, normalLinearization_apply,
    Prod.ext_iff, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    true_and]
  exact forall_congr' fun _ ↦ eq_comm

/-- The normal linearization of a `C^(n+1)` field is `C^n`. -/
theorem contDiff_normalLinearization {J : E × N → E × N →L[ℝ] E × N} {n : WithTop ℕ∞}
    (hJ : ContDiff ℝ (n + 1) J) : ContDiff ℝ n (normalLinearization J) := by
  have hJn : ContDiff ℝ n J := hJ.of_le le_self_add
  have hJ' : ContDiff ℝ n (fderiv ℝ J) := hJ.fderiv_right le_rfl
  have hz : ContDiff ℝ n fun p : E × N ↦ ((p.1, 0) : E × N) :=
    contDiff_fst.prodMk (contDiff_const (c := (0 : N)))
  have hJ₀ : ContDiff ℝ n fun p : E × N ↦ J (p.1, 0) := hJn.comp hz
  have hD : ContDiff ℝ n fun p : E × N ↦ fderiv ℝ J (p.1, 0) (0, p.2) :=
    (hJ'.comp hz).clm_apply ((contDiff_const (c := (0 : E))).prodMk contDiff_snd)
  -- Every block is a fixed linear map composed with one of the smooth fields above.
  have hcomp : ∀ {F : E × N → E × N →L[ℝ] E × N}, ContDiff ℝ n F →
      ∀ (A B : E × N →L[ℝ] E × N), ContDiff ℝ n fun p ↦ A ∘L F p ∘L B :=
    fun hF A B ↦ contDiff_const.clm_comp (hF.clm_comp contDiff_const)
  have h := (hcomp hJ₀ (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)
      (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)).add
    ((hcomp hD (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)
      (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)).add
    (hcomp hJ₀ (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)
      (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)))
  convert h using 1
  funext p
  simp only [normalLinearization, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_add]

/-! ### The normal dilation through Hadamard's lemma -/

variable [CompleteSpace E] [CompleteSpace N]

/-- The normal dilation of `J` at `(a, p)`, written with Hadamard's lemma so that it is defined
and smooth in `(a, p)` jointly, including `a = 0`: the block `E → N` of `J(z, a W)` divided by
`a` is replaced by the average `∫₀¹ ∂_W J(z, t a W)[W] dt` of the normal derivative. -/
private def hadamardField (J : E × N → E × N →L[ℝ] E × N) (q : ℝ × (E × N)) :
    E × N →L[ℝ] E × N :=
  ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L J (q.2.1, q.1 • q.2.2) ∘L
      ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
    q.1 • (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L
      J (q.2.1, q.1 • q.2.2) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N) +
    ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
      (∫ t in (0 : ℝ)..1, fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2)) ∘L
        ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
    ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
      J (q.2.1, q.1 • q.2.2) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N

omit [CompleteSpace E] [CompleteSpace N] in
private theorem hadamardField_apply (J : E × N → E × N →L[ℝ] E × N) (q : ℝ × (E × N))
    (v : E × N) :
    hadamardField J q v =
      ((J (q.2.1, q.1 • q.2.2) (v.1, 0)).1 + q.1 • (J (q.2.1, q.1 • q.2.2) (0, v.2)).1,
        ((∫ t in (0 : ℝ)..1, fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2)) (v.1, 0)).2 +
          (J (q.2.1, q.1 • q.2.2) (0, v.2)).2) := by
  simp only [hadamardField, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.smul_mk, smul_zero,
    Prod.mk_add_mk, add_zero, zero_add]

/-- At `a = 0` the Hadamard form of the normal dilation is the normal linearization. -/
private theorem hadamardField_zero (J : E × N → E × N →L[ℝ] E × N) (p : E × N) :
    hadamardField J (0, p) = normalLinearization J p := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [hadamardField_apply, normalLinearization_apply]
  simp only [zero_smul, smul_zero, add_zero, intervalIntegral.integral_const, sub_zero, one_smul]

/-- **Hadamard's lemma along the normal dilation**: `J(z, a W) - J(z, 0)` is `a` times the
average of the normal derivative of `J` along the segment from `(z, 0)` to `(z, a W)`. -/
private theorem sub_eq_smul_integral_fderiv {J : E × N → E × N →L[ℝ] E × N}
    (hJ : ContDiff ℝ 1 J) (a : ℝ) (p : E × N) :
    J (p.1, a • p.2) - J (p.1, 0) =
      a • ∫ t in (0 : ℝ)..1, fderiv ℝ J (p.1, t • a • p.2) (0, p.2) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ ↦ J (p.1, t • a • p.2))
      (a • fderiv ℝ J (p.1, t • a • p.2) (0, p.2)) t := by
    intro t _
    have hpath : HasDerivAt (fun t : ℝ ↦ (p.1, t • a • p.2)) (0, a • p.2) t := by
      simpa using HasDerivAt.prodMk (hasDerivAt_const t p.1)
        ((hasDerivAt_id t).smul_const (a • p.2))
    have hdir : ((0 : E), a • p.2) = a • ((0 : E), p.2) := by simp
    have key := ((hJ.differentiable one_ne_zero) (p.1, t • a • p.2)).hasFDerivAt.comp_hasDerivAt
      t hpath
    rw [hdir, map_smul] at key
    exact key
  have hint : IntervalIntegrable (fun t : ℝ ↦ a • fderiv ℝ J (p.1, t • a • p.2) (0, p.2))
      MeasureTheory.volume 0 1 := by
    have hseg : Continuous fun t : ℝ ↦ (p.1, t • a • p.2) :=
      continuous_const.prodMk (continuous_id.smul continuous_const)
    refine Continuous.intervalIntegrable ?_ 0 1
    exact (continuous_const : Continuous fun _ : ℝ ↦ a).smul
      (((hJ.continuous_fderiv one_ne_zero).comp hseg).clm_apply continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_smul] at h
  rw [h]
  simp

/-- Away from `a = 0` the Hadamard form is the normal dilation, provided the zero section is
`J`-holomorphic. -/
private theorem hadamardField_of_ne_zero {J : E × N → E × N →L[ℝ] E × N} (hJ : ContDiff ℝ 1 J)
    (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0) {a : ℝ} (ha : a ≠ 0) (p : E × N) :
    hadamardField J (a, p) = normalDilation J a p := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  -- The block `E → N` of `J(z, a W)` is `a` times the average of the normal derivative.
  have hNE : a⁻¹ • (J (p.1, a • p.2) (v.1, 0)).2 =
      ((∫ t in (0 : ℝ)..1, fderiv ℝ J (p.1, t • a • p.2) (0, p.2)) (v.1, 0)).2 := by
    have h := congrArg (fun L : E × N →L[ℝ] E × N ↦ (L (v.1, 0)).2)
      (sub_eq_smul_integral_fderiv hJ a p)
    simp only [sub_apply, Prod.snd_sub, hJ₀, sub_zero, smul_apply, Prod.smul_snd] at h
    rw [h, inv_smul_smul₀ ha]
  have hv : (v.1, a • v.2) = (v.1, 0) + a • ((0 : E), v.2) := by simp
  rw [hadamardField_apply, normalDilation_apply, hv, map_add, map_smul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_add, inv_smul_smul₀ ha, hNE]

omit [CompleteSpace E] [CompleteSpace N] in
/-- The Hadamard form of the normal dilation is `C^n` in `(a, z, W)` when `J` is `C^(n+1)`. -/
private theorem contDiff_hadamardField {J : E × N → E × N →L[ℝ] E × N} {n : ℕ∞}
    (hJ : ContDiff ℝ ((n : WithTop ℕ∞) + 1) J) : ContDiff ℝ n (hadamardField J) := by
  have hJn : ContDiff ℝ n J := hJ.of_le le_self_add
  have hJ' : ContDiff ℝ n (fderiv ℝ J) := hJ.fderiv_right le_rfl
  have hpt : ContDiff ℝ n fun q : ℝ × (E × N) ↦ ((q.2.1, q.1 • q.2.2) : E × N) :=
    contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd)
  have hJa : ContDiff ℝ n fun q : ℝ × (E × N) ↦ J (q.2.1, q.1 • q.2.2) := hJn.comp hpt
  have hI : ContDiff ℝ n fun q : ℝ × (E × N) ↦
      ∫ t in (0 : ℝ)..1, fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2) := by
    have hpt' : ContDiff ℝ n fun y : (ℝ × (E × N)) × ℝ ↦
        ((y.1.2.1, y.2 • y.1.1 • y.1.2.2) : E × N) :=
      contDiff_fst.snd.fst.prodMk (contDiff_snd.smul (contDiff_fst.fst.smul contDiff_fst.snd.snd))
    have hf : ContDiff ℝ n fun y : (ℝ × (E × N)) × ℝ ↦
        fderiv ℝ J (y.1.2.1, y.2 • y.1.1 • y.1.2.2) (0, y.1.2.2) :=
      (hJ'.comp hpt').clm_apply (contDiff_const.prodMk contDiff_fst.snd.snd)
    exact hf.parametric_intervalIntegral (μ := MeasureTheory.volume) (a := 0) (b := 1)
  -- Every term is a fixed linear map composed with one of the smooth fields above.
  have hcomp : ∀ {F : ℝ × (E × N) → E × N →L[ℝ] E × N}, ContDiff ℝ n F →
      ∀ (A B : E × N →L[ℝ] E × N), ContDiff ℝ n fun q ↦ A ∘L F q ∘L B :=
    fun hF A B ↦ contDiff_const.clm_comp (hF.clm_comp contDiff_const)
  have h := (((hcomp hJa (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)
    (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)).add
    (contDiff_fst.smul (hcomp hJa (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N)
      (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)))).add
    (hcomp hI (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)
      (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N))).add
    (hcomp hJa (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)
      (ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N))
  convert h using 1
  funext q
  simp only [hadamardField, ContinuousLinearMap.comp_assoc, Pi.smul_apply']

/-! ### Convergence of the normal dilations -/

variable {J : E × N → E × N →L[ℝ] E × N}

/-- **The normal dilations of `J` converge to its normal linearization.** If `J` is `C¹` and the
zero section `E × {0}` is `J`-holomorphic, then `δ_a^* J → J_N` uniformly on every compact set as
`a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_normalDilation (hJ : ContDiff ℝ 1 J)
    (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0) {K : Set (E × N)} (hK : IsCompact K) :
    TendstoUniformlyOn (normalDilation J) (normalLinearization J) (𝓝[≠] 0) K := by
  have hc : Continuous (hadamardField J) :=
    (contDiff_hadamardField (n := 0) (by simpa using hJ)).continuous
  have h := Continuous.tendstoUniformlyOn_of_tendsto (Φ := fun a p ↦ hadamardField J (a, p))
    hc hK (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[≠] (0 : ℝ)) (𝓝 0))
  simp only [id, hadamardField_zero] at h
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with a ha p _
  exact hadamardField_of_ne_zero hJ hJ₀ ha p

/-- **The normal dilations of `J` converge to its normal linearization in `Cᵏ`.** If `J` is
`C^(k+1)` and the zero section `E × {0}` is `J`-holomorphic, then for every `i ≤ k` the `i`-th
derivatives of `δ_a^* J` converge to those of `J_N` uniformly on every compact set as `a → 0`,
`a ≠ 0`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_normalDilation {k i : ℕ} (hJ : ContDiff ℝ (k + 1) J)
    (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0) (hi : i ≤ k) {K : Set (E × N)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i (normalDilation J a))
      (iteratedFDeriv ℝ i (normalLinearization J)) (𝓝[≠] 0) K := by
  have hG : ContDiff ℝ k (hadamardField J) := contDiff_hadamardField (n := k) (by exact_mod_cast hJ)
  have hJ1 : ContDiff ℝ 1 J := hJ.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  have hik : (i : WithTop ℕ∞) ≤ k := by exact_mod_cast hi
  -- The derivatives in `p` of `p ↦ G(a, p)` are those of `G` restricted to the `p`-directions.
  have hpartial (a : ℝ) : iteratedFDeriv ℝ i (fun p ↦ hadamardField J (a, p)) =
      fun p ↦ (iteratedFDeriv ℝ i (hadamardField J) (a, p)).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (E × N) := by
    have hfun : (fun p ↦ hadamardField J (a, p)) =
        (fun q ↦ hadamardField J ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ ℝ (E × N) := by
      ext1 p; simp
    funext p
    have hshift : ContDiff ℝ k fun q ↦ hadamardField J ((a, 0) + q) :=
      hG.comp (contDiff_const.add contDiff_id)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift _ hik,
      iteratedFDeriv_comp_add_left']
    simp
  have hc : Continuous fun q : ℝ × (E × N) ↦
      (iteratedFDeriv ℝ i (hadamardField J) q).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (E × N) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      (hG.continuous_iteratedFDeriv hik)
  have h := Continuous.tendstoUniformlyOn_of_tendsto
    (Φ := fun a p ↦ (iteratedFDeriv ℝ i (hadamardField J) (a, p)).compContinuousLinearMap
      fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (E × N))
    hc hK (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[≠] (0 : ℝ)) (𝓝 0))
  have hlim : (fun p ↦ (iteratedFDeriv ℝ i (hadamardField J) ((0 : ℝ), p)).compContinuousLinearMap
      fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (E × N)) =
        iteratedFDeriv ℝ i (normalLinearization J) := by
    rw [← hpartial]
    simp only [hadamardField_zero]
  simp only [id, hlim] at h
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with a ha p _
  have hfield : (fun p ↦ hadamardField J (a, p)) = normalDilation J a :=
    funext (hadamardField_of_ne_zero hJ1 hJ₀ ha)
  simp only [← hfield, hpartial]

/-- **The normal linearization of an almost complex structure is an almost complex structure**,
when the zero section is `J`-holomorphic and `J` is `C¹`. -/
theorem normalLinearization_apply_normalLinearization_apply (hJ : ContDiff ℝ 1 J)
    (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0) (hJ₂ : ∀ p v, J p (J p v) = -v) (p v : E × N) :
    normalLinearization J p (normalLinearization J p v) = -v := by
  -- `a ↦ G(a, p) (G(a, p) v)` is continuous and equals `-v` for `a ≠ 0`.
  have hG : Continuous fun a : ℝ ↦ hadamardField J (a, p) :=
    (contDiff_hadamardField (J := J) (n := 0) (by simpa using hJ)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hc : Continuous fun a : ℝ ↦ hadamardField J (a, p) (hadamardField J (a, p) v) :=
    hG.clm_apply (hG.clm_apply continuous_const)
  have hlim : Tendsto (fun a : ℝ ↦ hadamardField J (a, p) (hadamardField J (a, p) v)) (𝓝[≠] 0)
      (𝓝 (hadamardField J (0, p) (hadamardField J (0, p) v))) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hconst : (fun a : ℝ ↦ hadamardField J (a, p) (hadamardField J (a, p) v)) =ᶠ[𝓝[≠] 0]
      fun _ ↦ -v := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [hadamardField_of_ne_zero hJ hJ₀ ha]
    exact normalDilation_apply_normalDilation_apply hJ₂ ha p v
  have := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  simpa only [hadamardField_zero] using this

end TauCeti
