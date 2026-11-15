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
public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
import Mathlib.Analysis.Calculus.TaylorIntegral
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Normal rescaling of an almost complex structure along a pseudoholomorphic curve

Near an embedded pseudoholomorphic curve `C` in an almost complex manifold, choose coordinates
`(z, W) ∈ E × N` in which `C` is the zero section `E × {0}`, for instance through a tubular
map `F` of the normal bundle with `F(z, 0) = z`. The almost complex structure becomes a field
`J : E × N → (E × N →L[ℝ] E × N)`, and `C` is `J`-holomorphic exactly when `J(z, 0)` preserves the
tangent spaces `E × {0}` of the zero section, that is, the normal component of `J(z, 0) (v, 0)`
vanishes. Taubes studies pseudoholomorphic curves and Seiberg–Witten solutions near `C` in the
coordinates `Φ_a(z, W) = F(z, a W)`, which magnify the normal directions by `a⁻¹` as `a → 0`. In
the local coordinates this is the normal dilation `δ_a(z, W) = (z, a W)`, and the structure read
in the dilated coordinates is the pullback

`(δ_a^* J)(z, W) = S_a⁻¹ ∘ J(z, a W) ∘ S_a`,  `S_a (v, n) = (v, a n)`

(`TauCeti.normalDilation J a`; for `a ≠ 0` it is `OpenPartialHomeomorph.pullbackEnd` along the
dilation, `TauCeti.normalDilation_eq_pullbackEnd`, and the dilations compose,
`TauCeti.normalDilation_normalDilation`). Writing `J` in blocks along `E × N`, the dilation
multiplies the block `N → E` by `a` and divides the block `E → N` by `a`. The latter vanishes on
the zero section, so its quotient by `a` converges to its normal derivative, and the limit is the
**normal linearization** of `J` along the zero section (`TauCeti.normalLinearization J`):

`J_N(z, W) (v, n) = (J_EE(z, 0) v,  ∂_W J_NE(z, 0)[W] v + J_NN(z, 0) n)`.

Read off from this coordinate formula (`TauCeti.normalLinearization_apply`), the vertical
directions `{0} × N` are `J_N`-invariant and the projection to `E` intertwines `J_N(z, W)` with
the structure `j(z) = J_EE(z, 0)` of the curve. The term `∂_W J_NE(z, 0)[W]`, linear in `W`, is
retained in the limit: it is the zeroth-order coefficient of the real-linear equation cut out by
the `J_N`-holomorphic graphs (last item below), the normal Cauchy–Riemann equation of the zero
section in these coordinates.

The coordinate field is only required to be defined, differentiable and almost complex on an open
set `Ω ⊆ E × N` around the relevant points of the zero section, as for the pullback of `J` by a
tubular map defined on a disk bundle. This file proves:

* **convergence in `Cᵏ`**: if `J` is `C^(k+1)` on an open `Ω` and the zero section is
  `J`-holomorphic where it meets `Ω`, then for every `i ≤ k` the `i`-th derivatives of `δ_a^* J`
  converge to those of `J_N` uniformly on every compact set `K` with `(z, 0) ∈ Ω` for
  `(z, W) ∈ K`, as `a → 0`, `a ≠ 0`
  (`TauCeti.tendstoUniformlyOn_iteratedFDeriv_normalDilation_of_isOpen`;
  `TauCeti.tendstoUniformlyOn_normalDilation_of_isOpen` for the fields themselves when `J` is
  `C¹`, and `TauCeti.tendstoUniformlyOn_iteratedFDeriv_normalDilation`,
  `TauCeti.tendstoUniformlyOn_normalDilation` for globally defined fields). The proof writes
  `δ_a^* J` through Hadamard's lemma as a field depending smoothly on `(a, z, W)` jointly,
  including `a = 0`, where its value is `J_N`. These statements take `N` complete, so that the
  average in Hadamard's lemma is a Bochner integral;
* `J_N(z, W)` squares to `-1` when `J` is differentiable at `(z, 0)`, squares to `-1` near
  `(z, 0)`, and `J(z, 0)` preserves `E × {0}`
  (`TauCeti.normalLinearization_apply_normalLinearization_apply`); `J_N` is `Cᵐ` near `(z, W)`
  when `J` is `C^(m+1)` near `(z, 0)` (`TauCeti.contDiffAt_normalLinearization`); and it is
  invariant under every nonzero normal dilation (`TauCeti.normalDilation_normalLinearization`);
* a linear map `(v ↦ (v, D v))`, such as the derivative at `z` of the graph of a section `s` with
  `s(z) = W` and `D = ds(z)`, is complex linear from `j(z)` to `J_N(z, W)` exactly when
  `D ∘ j(z) = ∂_W J_NE(z, 0)[W] + J_NN(z, 0) ∘ D`
  (`TauCeti.normalLinearization_comp_prod_eq_iff`). So the `J_N`-holomorphic graphs are the
  solutions of a real-linear first-order equation in `s`, with the zeroth-order coefficient
  `W ↦ ∂_W J_NE(z, 0)[W]`. In terms of `TauCeti.cauchyRiemannOperator`, the Cauchy–Riemann defect
  of the graph of `s` for `J_N` is the normal component of the linearization
  `TauCeti.cauchyRiemannLinearization` of the Cauchy–Riemann operator of `J` at the zero section
  in the direction `(0, s)` (`TauCeti.cauchyRiemannOperator_normalLinearization`).

The coordinates are those of a fixed tubular chart: the global choice of `F` (Taubes uses a
foliation by `J`-holomorphic normal disks) is a separate construction.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
* C. H. Taubes, *GR = SW: counting curves and connections*,
  J. Differential Geom. 52 (1999), 453–609.
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

theorem normalDilation_def (J : E × N → E × N →L[ℝ] E × N) (a : ℝ) (p : E × N) :
    normalDilation J a p =
      (ContinuousLinearMap.id ℝ E).prodMap (a⁻¹ • ContinuousLinearMap.id ℝ N) ∘L
        J (p.1, a • p.2) ∘L (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ N) :=
  (rfl)

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
`J` is `C¹` near the zero section and the zero section is `J`-holomorphic
(`TauCeti.tendstoUniformlyOn_normalDilation_of_isOpen`, which takes `N` complete). -/
def normalLinearization (J : E × N → E × N →L[ℝ] E × N) (p : E × N) : E × N →L[ℝ] E × N :=
  ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L J (p.1, 0) ∘L
      ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
    ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
      (fderiv ℝ J (p.1, 0) (0, p.2) ∘L ContinuousLinearMap.inl ℝ E N ∘L
          ContinuousLinearMap.fst ℝ E N +
        J (p.1, 0) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N)

theorem normalLinearization_def (J : E × N → E × N →L[ℝ] E × N) (p : E × N) :
    normalLinearization J p =
      ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L J (p.1, 0) ∘L
          ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
        ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
          (fderiv ℝ J (p.1, 0) (0, p.2) ∘L ContinuousLinearMap.inl ℝ E N ∘L
              ContinuousLinearMap.fst ℝ E N +
            J (p.1, 0) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N) :=
  (rfl)

@[simp]
theorem normalLinearization_apply (J : E × N → E × N →L[ℝ] E × N) (p v : E × N) :
    normalLinearization J p v =
      ((J (p.1, 0) (v.1, 0)).1,
        (fderiv ℝ J (p.1, 0) (0, p.2) (v.1, 0)).2 + (J (p.1, 0) (0, v.2)).2) := by
  simp [normalLinearization]

/-! ### Algebraic properties -/

/-- For `a ≠ 0` the normal dilation of `J` squares to `-1` at `p` when `J` squares to `-1` at the
dilated point `(p.1, a • p.2)`. -/
theorem normalDilation_apply_normalDilation_apply {J : E × N → E × N →L[ℝ] E × N} {a : ℝ}
    (ha : a ≠ 0) {p : E × N} (hJ : ∀ w, J (p.1, a • p.2) (J (p.1, a • p.2) w) = -w)
    (v : E × N) : normalDilation J a p (normalDilation J a p v) = -v := by
  have hw (w : E × N) : (w.1, a • a⁻¹ • w.2) = w := by
    rw [smul_inv_smul₀ ha]
  simp only [normalDilation_apply, hw, hJ, Prod.fst_neg, Prod.snd_neg, smul_neg,
    inv_smul_smul₀ ha]
  rfl

/-- **The normal linearization is invariant under nonzero normal dilations**: its block `E → N`
is linear in the normal coordinate and its other blocks do not depend on it. -/
@[simp]
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

/-- **The Cauchy–Riemann defect of a graph for the normal linearization.** For a section `s`
differentiable at `z`, the Cauchy–Riemann defect at `z` of its graph `w ↦ (w, s w)` for `J_N`, with
source structure `j = J_EE(z, 0)`, is the normal component of the linearization at the zero
section `w ↦ (w, 0)` of the Cauchy–Riemann operator of `J` in the direction `w ↦ (0, s w)`. -/
theorem cauchyRiemannOperator_normalLinearization (J : E × N → E × N →L[ℝ] E × N) {s : E → N}
    {z : E} (hs : DifferentiableAt ℝ s z) :
    cauchyRiemannOperator (ContinuousLinearMap.fst ℝ E N ∘L J (z, 0) ∘L
        ContinuousLinearMap.inl ℝ E N) (normalLinearization J) (fun w ↦ (w, s w)) z =
      ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
        cauchyRiemannLinearization (ContinuousLinearMap.fst ℝ E N ∘L J (z, 0) ∘L
          ContinuousLinearMap.inl ℝ E N) J (fun w ↦ (w, 0)) (fun w ↦ (0, s w)) z := by
  have hgraph : fderiv ℝ (fun w ↦ (w, s w)) z = (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ s z) :=
    ((hasFDerivAt_id (𝕜 := ℝ) z).prodMk hs.hasFDerivAt).fderiv
  have hzero : fderiv ℝ (fun w : E ↦ (w, (0 : N))) z = ContinuousLinearMap.inl ℝ E N :=
    ((hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_const (0 : N) z)).fderiv
  have hdir : fderiv ℝ (fun w ↦ ((0 : E), s w)) z = (0 : E →L[ℝ] E).prod (fderiv ℝ s z) :=
    ((hasFDerivAt_const (0 : E) z).prodMk hs.hasFDerivAt).fderiv
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [cauchyRiemannOperator_apply, cauchyRiemannLinearization_apply, hgraph, hzero, hdir,
    normalLinearization_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_sub]
    abel

/-- **The normal linearization of an almost complex structure is an almost complex structure.**
At `p`, it suffices that `J` is differentiable at `(p.1, 0)`, squares to `-1` near `(p.1, 0)`, and
`J(p.1, 0)` preserves `E × {0}`: the identity `J' J + J J' = 0` obtained by differentiating
`J² = -1` in the direction `(0, p.2)` makes the block `E → N` of `J_N(p)` anticommute with the
diagonal blocks. -/
theorem normalLinearization_apply_normalLinearization_apply {J : E × N → E × N →L[ℝ] E × N}
    {p : E × N} (hJ : DifferentiableAt ℝ J (p.1, 0)) (hJ₀ : ∀ w, (J (p.1, 0) (w, 0)).2 = 0)
    (hJ₂ : ∀ᶠ q in 𝓝 (p.1, 0), ∀ w, J q (J q w) = -w) (v : E × N) :
    normalLinearization J p (normalLinearization J p v) = -v := by
  rw [normalLinearization_apply, normalLinearization_apply]
  set x : E × N := (p.1, 0)
  set J' := fderiv ℝ J x ((0 : E), p.2)
  -- Differentiating `q ↦ J q (J q w) = -w` at `x`.
  have hderiv (w : E × N) : J' (J x w) + J x (J' w) = 0 := by
    have hf := hJ.hasFDerivAt.clm_apply (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
    have h0 : HasFDerivAt (fun q ↦ J q (J q w)) (0 : E × N →L[ℝ] E × N) x :=
      (hasFDerivAt_const (-w) x).congr_of_eventuallyEq (hJ₂.mono fun q hq ↦ hq w)
    have h := congrArg (fun L : E × N →L[ℝ] E × N ↦ L ((0 : E), p.2)) (hf.unique h0)
    simpa [J', add_comm] using h
  have hJx := hJ₂.self_of_nhds
  have hA : J x (v.1, 0) = ((J x (v.1, 0)).1, 0) := Prod.ext rfl (hJ₀ v.1)
  -- The normal component of `J x u` only depends on the normal component of `u`.
  have hsplit (u : E × N) : (J x u).2 = (J x (0, u.2)).2 := by
    have hu : u = (u.1, 0) + (0, u.2) := by simp
    conv_lhs => rw [hu, map_add, Prod.snd_add, hJ₀, zero_add]
  refine Prod.ext ?_ ?_
  · rw [← hA, hJx]
    simp
  · have hadd : J x (0, (J' (v.1, 0)).2 + (J x (0, v.2)).2) =
        J x (0, (J' (v.1, 0)).2) + J x (0, (J x (0, v.2)).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero]
    have h := congrArg Prod.snd (hderiv (v.1, 0))
    rw [Prod.snd_add, hsplit (J' (v.1, 0))] at h
    rw [hadd, Prod.snd_add, ← hsplit (J x (0, v.2)), ← hA, ← add_assoc, h]
    simp [hJx]

/-! ### Regularity -/

/-- The normal dilation of `J` by `a` is `Cⁿ` at `p` when `J` is `Cⁿ` at `(p.1, a • p.2)`. -/
theorem contDiffAt_normalDilation {J : E × N → E × N →L[ℝ] E × N} {n : WithTop ℕ∞} {a : ℝ}
    {p : E × N} (hJ : ContDiffAt ℝ n J (p.1, a • p.2)) :
    ContDiffAt ℝ n (normalDilation J a) p := by
  have hg : ContDiffAt ℝ n (fun q : E × N ↦ J (q.1, a • q.2)) p :=
    hJ.comp p (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul a))
  exact contDiffAt_const.clm_comp (hg.clm_comp contDiffAt_const)

/-- The normal dilation of `J` by `a` is `Cⁿ` on the preimage of a set where `J` is `Cⁿ`. -/
theorem contDiffOn_normalDilation {J : E × N → E × N →L[ℝ] E × N} {n : WithTop ℕ∞} {a : ℝ}
    {s : Set (E × N)} (hJ : ContDiffOn ℝ n J s) :
    ContDiffOn ℝ n (normalDilation J a) {p | (p.1, a • p.2) ∈ s} := by
  have hg : ContDiffOn ℝ n (fun q : E × N ↦ J (q.1, a • q.2)) {p | (p.1, a • p.2) ∈ s} :=
    hJ.comp (contDiff_fst.prodMk (contDiff_snd.const_smul a)).contDiffOn fun _ hp ↦ hp
  exact contDiffOn_const.clm_comp (hg.clm_comp contDiffOn_const)

/-- The normal dilations of a `Cⁿ` field are `Cⁿ`. -/
theorem contDiff_normalDilation {J : E × N → E × N →L[ℝ] E × N} {n : WithTop ℕ∞}
    (hJ : ContDiff ℝ n J) (a : ℝ) : ContDiff ℝ n (normalDilation J a) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_normalDilation hJ.contDiffAt

/-- The normal linearization of `J` is `Cᵐ` at `p` when `J` is `Cⁿ` at `(p.1, 0)` and
`m + 1 ≤ n`. -/
theorem contDiffAt_normalLinearization {J : E × N → E × N →L[ℝ] E × N} {m n : WithTop ℕ∞}
    {p : E × N} (hJ : ContDiffAt ℝ n J (p.1, 0)) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (normalLinearization J) p := by
  have hz : ContDiffAt ℝ m (fun q : E × N ↦ ((q.1, 0) : E × N)) p :=
    contDiffAt_fst.prodMk contDiffAt_const
  have hJ₀ : ContDiffAt ℝ m (fun q : E × N ↦ J (q.1, 0)) p :=
    (hJ.of_le (le_self_add.trans hmn)).comp p hz
  have hD : ContDiffAt ℝ m (fun q : E × N ↦ fderiv ℝ J (q.1, 0) ((0 : E), q.2)) p :=
    ((hJ.fderiv_right hmn).comp p hz).clm_apply (contDiffAt_const.prodMk contDiffAt_snd)
  unfold normalLinearization
  exact (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hJ₀.clm_comp contDiffAt_const))).add
    (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp
      ((hD.clm_comp contDiffAt_const).add (hJ₀.clm_comp contDiffAt_const))))

/-- The normal linearization of `J` is `Cᵐ` wherever the zero-section point lies in an open set
on which `J` is `Cⁿ`, for `m + 1 ≤ n`. -/
theorem contDiffOn_normalLinearization {J : E × N → E × N →L[ℝ] E × N} {m n : WithTop ℕ∞}
    {Ω : Set (E × N)} (hΩ : IsOpen Ω) (hJ : ContDiffOn ℝ n J Ω) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (normalLinearization J) {p | (p.1, 0) ∈ Ω} := fun _ hp ↦
  (contDiffAt_normalLinearization (hJ.contDiffAt (hΩ.mem_nhds hp)) hmn).contDiffWithinAt

/-- The normal linearization of a `Cⁿ` field is `Cᵐ` for `m + 1 ≤ n`. -/
theorem contDiff_normalLinearization {J : E × N → E × N →L[ℝ] E × N} {m n : WithTop ℕ∞}
    (hJ : ContDiff ℝ n J) (hmn : m + 1 ≤ n) : ContDiff ℝ m (normalLinearization J) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_normalLinearization hJ.contDiffAt hmn

/-! ### The normal dilation through Hadamard's lemma -/

/-- The parameters `(a, z, W)` for which the segment from `(z, 0)` to `(z, a W)` lies in `Ω`, so
that Hadamard's lemma applies to a field defined on `Ω`. -/
private def hadamardDomain (Ω : Set (E × N)) : Set (ℝ × (E × N)) :=
  {q | ∀ t ∈ Icc (0 : ℝ) 1, (q.2.1, t • q.1 • q.2.2) ∈ Ω}

omit [NormedSpace ℝ E] in
private theorem isOpen_hadamardDomain {Ω : Set (E × N)} (hΩ : IsOpen Ω) :
    IsOpen (hadamardDomain Ω) := by
  refine isOpen_iff_mem_nhds.2 fun q hq ↦ ?_
  have hc : Continuous fun y : (ℝ × (E × N)) × ℝ ↦ ((y.1.2.1, y.2 • y.1.1 • y.1.2.2) : E × N) :=
    by fun_prop
  exact isCompact_Icc.eventually_forall_of_forall_eventually (P := fun (q : ℝ × (E × N)) (t : ℝ) ↦
    (q.2.1, t • q.1 • q.2.2) ∈ Ω) fun t ht ↦ hc.continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds (hq t ht))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem zero_mem_hadamardDomain {Ω : Set (E × N)} {p : E × N} (hp : (p.1, 0) ∈ Ω) :
    ((0 : ℝ), p) ∈ hadamardDomain Ω := fun t _ ↦ by simpa using hp

/-- The normal dilation of `J` at `(a, p)`, written with Hadamard's lemma so that it is defined
and smooth in `(a, p)` jointly, including `a = 0`: the block `E → N` of `J(z, a W)` divided by
`a` is replaced by the average `∫₀¹ ∂_W J_NE(z, t a W)[W] dt` of the normal derivative. -/
private def hadamardField (J : E × N → E × N →L[ℝ] E × N) (q : ℝ × (E × N)) :
    E × N →L[ℝ] E × N :=
  ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L J (q.2.1, q.1 • q.2.2) ∘L
      ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N +
    q.1 • (ContinuousLinearMap.inl ℝ E N ∘L ContinuousLinearMap.fst ℝ E N ∘L
      J (q.2.1, q.1 • q.2.2) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N) +
    ContinuousLinearMap.inr ℝ E N ∘L
      (∫ t in (0 : ℝ)..1, ContinuousLinearMap.snd ℝ E N ∘L
        fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2) ∘L ContinuousLinearMap.inl ℝ E N) ∘L
        ContinuousLinearMap.fst ℝ E N +
    ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N ∘L
      J (q.2.1, q.1 • q.2.2) ∘L ContinuousLinearMap.inr ℝ E N ∘L ContinuousLinearMap.snd ℝ E N

private theorem hadamardField_apply (J : E × N → E × N →L[ℝ] E × N) (q : ℝ × (E × N))
    (v : E × N) :
    hadamardField J q v =
      ((J (q.2.1, q.1 • q.2.2) (v.1, 0)).1 + q.1 • (J (q.2.1, q.1 • q.2.2) (0, v.2)).1,
        (∫ t in (0 : ℝ)..1, ContinuousLinearMap.snd ℝ E N ∘L
            fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2) ∘L ContinuousLinearMap.inl ℝ E N) v.1 +
          (J (q.2.1, q.1 • q.2.2) (0, v.2)).2) := by
  simp only [hadamardField, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.smul_mk, smul_zero,
    Prod.mk_add_mk, add_zero, zero_add]

/-- The Hadamard form of the normal dilation is `Cⁿ` in `(a, z, W)` where the segments lie in an
open set on which `J` is `C^(n+1)`. -/
private theorem contDiffOn_hadamardField {J : E × N → E × N →L[ℝ] E × N} {Ω : Set (E × N)}
    (hΩ : IsOpen Ω) {n : ℕ∞} (hJ : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) J Ω) :
    ContDiffOn ℝ n (hadamardField J) (hadamardDomain Ω) := by
  have hJn : ContDiffOn ℝ n J Ω := hJ.of_le le_self_add
  have hJ' : ContDiffOn ℝ n (fderiv ℝ J) Ω := hJ.fderiv_of_isOpen hΩ le_rfl
  have hJa : ContDiffOn ℝ n (fun q : ℝ × (E × N) ↦ J (q.2.1, q.1 • q.2.2)) (hadamardDomain Ω) :=
    hJn.comp (by fun_prop : ContDiff ℝ n fun q : ℝ × (E × N) ↦
      ((q.2.1, q.1 • q.2.2) : E × N)).contDiffOn fun q hq ↦ by
        simpa using hq 1 (right_mem_Icc.2 zero_le_one)
  have hI : ContDiffOn ℝ n (fun q : ℝ × (E × N) ↦ ∫ t in (0 : ℝ)..1,
      ContinuousLinearMap.snd ℝ E N ∘L fderiv ℝ J (q.2.1, t • q.1 • q.2.2) (0, q.2.2) ∘L
        ContinuousLinearMap.inl ℝ E N) (hadamardDomain Ω) := by
    refine ContDiffOn.parametric_intervalIntegral (isOpen_hadamardDomain hΩ) ?_
    have hpt : ContDiffOn ℝ n (fun y : (ℝ × (E × N)) × ℝ ↦
        fderiv ℝ J (y.1.2.1, y.2 • y.1.1 • y.1.2.2)) (hadamardDomain Ω ×ˢ uIcc 0 1) :=
      hJ'.comp (by fun_prop : ContDiff ℝ n fun y : (ℝ × (E × N)) × ℝ ↦
        ((y.1.2.1, y.2 • y.1.1 • y.1.2.2) : E × N)).contDiffOn fun y hy ↦ by
        rw [uIcc_of_le zero_le_one] at hy
        exact hy.1 y.2 hy.2
    exact contDiffOn_const.clm_comp ((hpt.clm_apply (by fun_prop)).clm_comp contDiffOn_const)
  unfold hadamardField
  -- Every term is a fixed linear map composed with one of the smooth fields above.
  exact (((contDiffOn_const.clm_comp
      (contDiffOn_const.clm_comp (hJa.clm_comp contDiffOn_const))).add
    (contDiffOn_fst.smul (contDiffOn_const.clm_comp (contDiffOn_const.clm_comp
      (hJa.clm_comp contDiffOn_const))))).add
    (contDiffOn_const.clm_comp (hI.clm_comp contDiffOn_const))).add
    (contDiffOn_const.clm_comp (contDiffOn_const.clm_comp (hJa.clm_comp contDiffOn_const)))

variable [CompleteSpace N]

/-- At `a = 0` the Hadamard form of the normal dilation is the normal linearization. -/
private theorem hadamardField_zero (J : E × N → E × N →L[ℝ] E × N) (p : E × N) :
    hadamardField J (0, p) = normalLinearization J p := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [hadamardField_apply, normalLinearization_apply]
  simp

/-- Away from `a = 0` the Hadamard form is the normal dilation, provided `J` is `C¹` on an open
set containing the segment from `(p.1, 0)` to `(p.1, a • p.2)` and `J(p.1, 0)` preserves
`E × {0}`. -/
private theorem hadamardField_of_ne_zero {J : E × N → E × N →L[ℝ] E × N} {Ω : Set (E × N)}
    (hΩ : IsOpen Ω) (hJ : ContDiffOn ℝ 1 J Ω) {a : ℝ} {p : E × N}
    (hJ₀ : ∀ v, (J (p.1, 0) (v, 0)).2 = 0) (ha : a ≠ 0) (hq : (a, p) ∈ hadamardDomain Ω) :
    hadamardField J (a, p) = normalDilation J a p := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hseg (t : ℝ) : (p.1, (0 : N)) + t • ((0 : E), a • p.2) = (p.1, t • a • p.2) := by simp
  have hJt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 1 J (p.1, t • a • p.2) :=
    hJ.contDiffAt (hΩ.mem_nhds (hq t ht))
  -- The block `E → N` of `J(z, a W)` is `a` times the average of the normal derivative.
  have hNE : a⁻¹ • (J (p.1, a • p.2) (v.1, 0)).2 =
      (∫ t in (0 : ℝ)..1, ContinuousLinearMap.snd ℝ E N ∘L
        fderiv ℝ J (p.1, t • a • p.2) (0, p.2) ∘L ContinuousLinearMap.inl ℝ E N) v.1 := by
    let f : E × N → N := fun q ↦ (J q (v.1, 0)).2
    have hf (q : E × N) (hq : ContDiffAt ℝ 1 J q) (y : E × N) :
        fderiv ℝ f q y = (fderiv ℝ J q y (v.1, 0)).2 := by
      have h := ((hq.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
        (hasFDerivAt_const (v.1, 0) q)).snd.fderiv
      simp [f, h]
    have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (f := f) (x := (p.1, 0))
      (y := ((0 : E), a • p.2)) fun t ht ↦ by
        rw [hseg]
        exact contDiffAt_snd.comp _ ((hJt t ht).clm_apply contDiffAt_const)
    have hcont : ContinuousOn (fun t : ℝ ↦ ContinuousLinearMap.snd ℝ E N ∘L
        fderiv ℝ J (p.1, t • a • p.2) (0, p.2) ∘L ContinuousLinearMap.inl ℝ E N) (uIcc 0 1) := by
      refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [uIcc_of_le zero_le_one] at ht
      have hd := ((hJt t ht).fderiv_right (m := 0) (by norm_num)).continuousAt
      have hγ : ContinuousAt (fun t : ℝ ↦ ((p.1, t • a • p.2) : E × N)) t := by fun_prop
      exact continuousAt_const.clm_comp
        (((hd.comp_of_eq hγ rfl).clm_apply continuousAt_const).clm_comp continuousAt_const)
    rw [ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable)]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, pow_zero, iteratedFDeriv_zero_apply,
      Prod.mk_add_mk, add_zero, f, hJ₀] at hT
    have hone (x : E × N) (m : Fin (0 + 1) → E × N) :
        iteratedFDeriv ℝ (0 + 1) f x m = fderiv ℝ f x (m 0) :=
      iteratedFDeriv_one_apply m
    rw [hT, intervalIntegral.integral_congr (g := fun t ↦ a • (fderiv ℝ J (p.1, t • a • p.2)
      (0, p.2) (v.1, 0)).2), intervalIntegral.integral_smul, inv_smul_smul₀ ha]
    · simp
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hdir : ((0 : E), a • p.2) = a • ((0 : E), p.2) := by simp
    dsimp only
    rw [hone, hseg, hf _ (hJt t ht), hdir, map_smul, smul_apply, Prod.smul_snd]
  have hv : (v.1, a • v.2) = (v.1, 0) + a • ((0 : E), v.2) := by simp
  rw [hadamardField_apply, normalDilation_apply, hv, map_add, map_smul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_add, inv_smul_smul₀ ha, hNE]

/-! ### Convergence of the normal dilations -/

variable {J : E × N → E × N →L[ℝ] E × N}

/-- **The normal dilations of `J` converge to its normal linearization in `Cᵏ`.** Let `J` be
`Cⁿ` on an open set `Ω`, with `i + 1 ≤ n`, and let the zero section be `J`-holomorphic where it
meets `Ω`. Then the `i`-th derivatives of `δ_a^* J` converge to those of `J_N` uniformly on every
compact set `K` with `(z, 0) ∈ Ω` for `(z, W) ∈ K`, as `a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_normalDilation_of_isOpen {Ω K : Set (E × N)}
    {n : WithTop ℕ∞} {i : ℕ} (hΩ : IsOpen Ω) (hJ : ContDiffOn ℝ n J Ω)
    (hJ₀ : ∀ z, (z, 0) ∈ Ω → ∀ v, (J (z, 0) (v, 0)).2 = 0) (hi : (i + 1 : WithTop ℕ∞) ≤ n)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i (normalDilation J a))
      (iteratedFDeriv ℝ i (normalLinearization J)) (𝓝[≠] 0) K := by
  have hD := isOpen_hadamardDomain hΩ
  have hG : ContDiffOn ℝ i (hadamardField J) (hadamardDomain Ω) :=
    contDiffOn_hadamardField hΩ (hJ.of_le (by exact_mod_cast hi))
  have hJ1 : ContDiffOn ℝ 1 J Ω := hJ.of_le (le_trans (by exact_mod_cast Nat.le_add_left 1 i) hi)
  -- The derivatives in `p` of `p ↦ G(a, p)` are jointly continuous near `{0} × K`.
  have hΦ : ∀ p ∈ K, ContinuousAt (Function.uncurry fun a p ↦
      iteratedFDeriv ℝ i (fun y ↦ hadamardField J (a, y)) p) (0, p) := by
    intro p hp
    have hmem := zero_mem_hadamardDomain (hKΩ p hp)
    have hc : ContinuousAt (fun z : ℝ × (E × N) ↦
        (iteratedFDeriv ℝ i (hadamardField J) z).compContinuousLinearMap
          fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (E × N)) (0, p) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.continuousAt.comp
        ((hG.contDiffAt (hD.mem_nhds hmem)).continuousAt_iteratedFDeriv le_rfl)
    refine hc.congr ?_
    filter_upwards [hD.mem_nhds hmem] with z hz
    exact ((hG.contDiffAt (hD.mem_nhds hz)).iteratedFDeriv_prod_right i le_rfl).symm
  have h := hK.tendstoUniformlyOn_of_continuousAt hΦ
  have h0 : (fun y ↦ hadamardField J ((0 : ℝ), y)) = normalLinearization J :=
    funext (hadamardField_zero J)
  simp only [h0] at h
  have h' : TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i fun y ↦ hadamardField J (a, y))
      (iteratedFDeriv ℝ i (normalLinearization J)) (𝓝[≠] 0) K :=
    fun u hu ↦ nhdsWithin_le_nhds (h u hu)
  refine h'.congr ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
    (hK.eventually_forall_of_forall_eventually (P := fun a p ↦ (a, p) ∈ hadamardDomain Ω)
      fun p hp ↦ hD.mem_nhds (zero_mem_hadamardDomain (hKΩ p hp)))] with a ha haK p hp
  refine (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ i).eq_of_nhds
  have hy : ∀ᶠ y in 𝓝 p, (a, y) ∈ hadamardDomain Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hD.mem_nhds (haK p hp))
  filter_upwards [hy] with y hy
  have hy0 : (y.1, 0) ∈ Ω := by
    simpa using hy 0 (left_mem_Icc.2 zero_le_one)
  exact hadamardField_of_ne_zero hΩ hJ1 (hJ₀ y.1 hy0) ha hy

/-- **The normal dilations of `J` converge to its normal linearization.** If `J` is `C¹` on an
open set `Ω` and the zero section is `J`-holomorphic where it meets `Ω`, then `δ_a^* J → J_N`
uniformly on every compact set `K` with `(z, 0) ∈ Ω` for `(z, W) ∈ K`, as `a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_normalDilation_of_isOpen {Ω K : Set (E × N)} (hΩ : IsOpen Ω)
    (hJ : ContDiffOn ℝ 1 J Ω) (hJ₀ : ∀ z, (z, 0) ∈ Ω → ∀ v, (J (z, 0) (v, 0)).2 = 0)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    TendstoUniformlyOn (normalDilation J) (normalLinearization J) (𝓝[≠] 0) K := by
  have h := (continuousMultilinearCurryFin0 ℝ (E × N) (E × N →L[ℝ] E × N)).isometry
    |>.uniformContinuous.comp_tendstoUniformlyOn
      (tendstoUniformlyOn_iteratedFDeriv_normalDilation_of_isOpen (i := 0) hΩ hJ hJ₀ (by simp)
        hK hKΩ)
  simpa [Function.comp_def] using h

/-- **The normal dilations of `J` converge to its normal linearization in `Cᵏ`.** If `J` is `Cⁿ`
with `i + 1 ≤ n` and the zero section `E × {0}` is `J`-holomorphic, then the `i`-th derivatives of
`δ_a^* J` converge to those of `J_N` uniformly on every compact set as `a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_normalDilation {n : WithTop ℕ∞} {i : ℕ}
    (hJ : ContDiff ℝ n J) (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0)
    (hi : (i + 1 : WithTop ℕ∞) ≤ n) {K : Set (E × N)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a ↦ iteratedFDeriv ℝ i (normalDilation J a))
      (iteratedFDeriv ℝ i (normalLinearization J)) (𝓝[≠] 0) K :=
  tendstoUniformlyOn_iteratedFDeriv_normalDilation_of_isOpen isOpen_univ hJ.contDiffOn
    (fun z _ ↦ hJ₀ z) hi hK fun _ _ ↦ mem_univ _

/-- **The normal dilations of `J` converge to its normal linearization.** If `J` is `C¹` and the
zero section `E × {0}` is `J`-holomorphic, then `δ_a^* J → J_N` uniformly on every compact set as
`a → 0`, `a ≠ 0`. -/
theorem tendstoUniformlyOn_normalDilation (hJ : ContDiff ℝ 1 J)
    (hJ₀ : ∀ z v, (J (z, 0) (v, 0)).2 = 0) {K : Set (E × N)} (hK : IsCompact K) :
    TendstoUniformlyOn (normalDilation J) (normalLinearization J) (𝓝[≠] 0) K :=
  tendstoUniformlyOn_normalDilation_of_isOpen isOpen_univ hJ.contDiffOn (fun z _ ↦ hJ₀ z) hK
    fun _ _ ↦ mem_univ _

end TauCeti
