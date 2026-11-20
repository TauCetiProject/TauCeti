/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Trivialization
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Symplectic.Manifold.FixedPoint
import TauCeti.Geometry.Symplectic.Manifold.Suspension.AlmostComplex

/-!
# Nondegeneracy of the orbit tori of a surface map up to a period cutoff

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a surface preserving a two-form `σ`, and let
`K_((s, t), y)` be a *vertical family* of almost complex structures on the tangent spaces of `M`
satisfying the seam identity

`dφ⁻¹ ∘ K_((s, t), y) = K_((s, t + 1), φ⁻¹ y) ∘ dφ⁻¹`,

the data from which a block almost complex structure on the symplectic suspension
`(ℝ / ℤ)_s × Y_φ` descends (`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).
A periodic point `x` of period `d` gives the orbit torus `S¹ × γ_x`. Along it, for a family not
depending on `s` (such as `TauCeti.SmoothMappingTorus.seamFamily`), the normal operator in vertical
directions is `D v = ∂s v + K(t) ∂t v` with `K(t) = K_((s₀, t), x)`
(`TauCeti.orbitTorusVerticalOperator`, `TauCeti.hasDerivAt_cauchyRiemannOperator_vertical`), and
the normal sections twisted by a real sign character are the maps `v : ℝ × ℝ → T_x M` with
`v (s + k, t) = ε₁ v (s, t)` and `P ^ n v (s + a, t + n d) = ε₂ v (s, t)`, on the finite cover with
deck group spanned by `(k, 0)` and `(a, n d)`. Here `P = dφ^d_x` is the linearized return map.
The loop `t ↦ K_((s₀, t), x)` of endomorphisms of `T_x M`, which is the model space `E` by
definition, is `TauCeti.verticalFamilyAt K s₀ x`.

This file supplies the hypotheses of the kernel criteria of
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Trivialization` from these geometric data:

* at a periodic point of period `d` the seam identity becomes the seam identity of the return map,
  `P ∘ K(t + d) = K(t) ∘ P`
  (`TauCeti.SmoothMappingTorus.apply_apply_add_eq_apply_apply_of_hasMFDerivAt_iterate`);
* the return map preserves `σ`, because every iterate of `φ` does
  (`TauCeti.SmoothTwoForm.isIsometry_fixedPointDerivative`).

When the vertical family is smooth, as for
`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`, the loop
`TauCeti.verticalFamilyAt K s₀ x` is smooth by `TauCeti.contDiff_verticalFamilyAt`, which
discharges the `C²` hypothesis below.

The main theorem combines these with the dynamics of the return map. If `φ` is nondegenerate up to
period `2 N` (no return map of a periodic orbit of period at most `2 N` has the eigenvalue `1`),
then `det (1 - P ^ (2 n)) ≠ 0` for every periodic point of period `d` and every `n` with
`d n ≤ N`, since the return map of the `2 n`-fold cover is `P ^ (2 n)`
(`TauCeti.IsNondegenerateUpToPeriod.det_smul_one_sub_pow_ne_zero`). Hence all four twisted
vertical operators on every cover of the orbit torus whose period along the orbit is at most `N`
have no nonzero `C²` kernel element
(`TauCeti.forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_of_isNondegenerateUpToPeriod`).
The eigenvalue `-1` of `P ^ n`, which governs the sign character twisted along the orbit, is
excluded by nondegeneracy of the `2 n`-fold cover; so nondegeneracy up to period `N` alone does not
control the twisted operators on the covers of period `N`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158.
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301--354.
-/

public section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]

/-- The vertical family `K` read at the circle coordinate `s` and the point `x`: the loop
`t ↦ K_((s, t), x)` of endomorphisms of `T_x M`, which is the model space `E` by definition. -/
noncomputable def verticalFamilyAt
    (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)) (s : ℝ) (x : M) (t : ℝ) :
    E →L[ℝ] E :=
  show E →L[ℝ] E from (K ((s, t), x)).toLinearMap.toContinuousLinearMap

/-- The loop `TauCeti.verticalFamilyAt K s x` at time `t` acts as `K_((s, t), x)`. -/
@[simp]
theorem verticalFamilyAt_apply
    (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)) (s : ℝ) (x : M) (t : ℝ)
    (v : E) : verticalFamilyAt K s x t v = K ((s, t), x) v :=
  (rfl)

/-- **The vertical family at a point is as smooth as the family.** If the vertical family `K` is a
`C^n` section of the endomorphism bundle of `T M` along `(ℝ × ℝ) × M → M`, then the loop
`TauCeti.verticalFamilyAt K s x` is `C^n`. -/
theorem contDiff_verticalFamilyAt [IsManifold I 1 M] {n : WithTop ℕ∞}
    {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : (ℝ × ℝ) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap))
    (s : ℝ) (x : M) : ContDiff ℝ n (verticalFamilyAt K s x) :=
  contMDiff_iff_contDiff.1 (contMDiff_apply_prodMk_const_of_contMDiff_hom_bundle _ hK
    (contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)) x)

variable [IsManifold I ∞ M] {φ : M ≃ₘ⟮I, I⟯ M}
  {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}

/-- **The orbit tori of a surface map are nondegenerate through half the period cutoff.** Let
`φ` be a diffeomorphism of a surface preserving a two-form `σ`, and let `K` be a vertical family
satisfying the seam identity. Let `x` be a periodic point of period `d > 0`, with return map
`P = dφ^d_x`, and suppose that along the orbit, at the circle coordinate `s₀`, the structures
`K(t) = K_((s₀, t), x)` depend `C²` on `t` and that `σ_x` tames `K(0)`. If `φ`
is nondegenerate up to period `2 N`, then for `n > 0` with `d n ≤ N`, `k > 0` and `a ∈ ℤ`, the
vertical operator `∂s + K(t) ∂t`, twisted by any signs `ε₁` along `(k, 0)` and `ε₂` along
`(a, n d)` through `P`, has no nonzero `C²` kernel element. -/
theorem forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_of_isNondegenerateUpToPeriod
    (hE : Module.finrank ℝ E = 2) {σ : SmoothTwoForm I M}
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    {x : M} (s₀ : ℝ)
    (hK2 : ContDiff ℝ 2 (verticalFamilyAt K s₀ x))
    (htame : ∀ v : TangentSpace I x, v ≠ 0 → 0 < σ.eval₂ x v (K ((s₀, 0), x) v))
    {N d n k : ℕ} (hφ : IsNondegenerateUpToPeriod I φ (2 * N)) (hx : IsPeriodicPt φ d x)
    (hd : 0 < d) (hn : 0 < n) (hdn : d * n ≤ N) (hk : 0 < k) {P : E →L[ℝ] E}
    (hP : HasMFDerivAt I I (⇑φ)^[d] x P) (a : ℤ) :
    ∀ ε₁ ε₂ : ℝ, ε₁ ^ 2 = 1 → ε₂ ^ 2 = 1 → ∀ v : ℝ × ℝ → E, ContDiff ℝ 2 v →
      (∀ s t, v (s + k, t) = ε₁ • v (s, t)) →
      (∀ s t, (P ^ n) (v (s + a, t + n * d)) = ε₂ • v (s, t)) →
      (∀ z, orbitTorusVerticalOperator (verticalFamilyAt K s₀ x) v z = 0) →
      v = 0 := by
  -- The form `σ` at `x`, as a continuous bilinear map on `T_x M`, which is `E` by definition.
  let σx : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (show LinearMap.BilinForm ℝ E from σ.bilinFormAt x))
  have hσx (v w : E) : σx v w = σ.eval₂ x v w := by
    simp only [σx, LinearMap.coe_toContinuousLinearMap']
    exact SmoothForm.bilinFormAt_apply σ x v w
  have hσanti (v w : E) : σx v w = -σx w v := by
    rw [hσx, hσx]
    exact SmoothBundleForm.eval₂_swap σ x v w
  have hKsq (t : ℝ) (w : E) :
      verticalFamilyAt K s₀ x t (verticalFamilyAt K s₀ x t w) = -w := by
    rw [verticalFamilyAt_apply, verticalFamilyAt_apply]
    exact (K ((s₀, t), x)).apply_apply w
  -- On a surface every almost complex structure preserves the alternating form `σ_x`.
  have hσJ (J : AlmostComplexStructure E) (v w : E) : σx (J v) (J w) = σx v w :=
    J.bilin_apply_apply_eq_of_finrank_le_two hE.le (B := ContinuousLinearMap.toLinearMap₁₂ σx)
      (fun u ↦ by simpa using CharZero.eq_neg_self_iff.1 (hσanti u u)) v w
  have hσK (t : ℝ) (v w : E) :
      σx (verticalFamilyAt K s₀ x t v) (verticalFamilyAt K s₀ x t w) = σx v w := by
    rw [verticalFamilyAt_apply, verticalFamilyAt_apply]
    exact hσJ (K ((s₀, t), x)) v w
  have hσtame (v : E) (hv : v ≠ 0) : 0 < σx v (verticalFamilyAt K s₀ x 0 v) := by
    rw [verticalFamilyAt_apply]
    exact (htame v hv).trans_eq (hσx _ _).symm
  -- The return map preserves `σ` at `x`, since every iterate of `φ` preserves `σ`.
  have hPσ (v w : E) : σx (P v) (P w) = σx v w := by
    have h := (SmoothTwoForm.isIsometry_fixedPointDerivative (φ.contMDiff.iterate d)
      (SmoothForm.mpullback_iterate_eq_self φ.contMDiff hσ d) ⟨x, hx.isFixedPt.eq⟩).apply v w
    rw [hP.fixedPointDerivative_eq] at h
    rw [hσx, hσx, ← SmoothForm.bilinFormAt_apply σ x v w,
      ← SmoothForm.bilinFormAt_apply σ x (P v) (P w)]
    exact h
  have hPK (t : ℝ) :
      P ∘L verticalFamilyAt K s₀ x (t + d) = verticalFamilyAt K s₀ x t ∘L P := by
    ext v
    simpa only [ContinuousLinearMap.comp_apply, verticalFamilyAt_apply] using
      SmoothMappingTorus.apply_apply_add_eq_apply_apply_of_hasMFDerivAt_iterate ht hx hP s₀ t v
  -- The return map `P ^ (2 n)` of the `2 n`-fold cover, of period `2 d n ≤ 2 N`, fixes no vector.
  have hdet := hφ.det_smul_one_sub_pow_ne_zero (m := 2 * n) (j := 1) hd (by omega) one_pos
    (by nlinarith) hx hP (one_pow 1)
  rw [one_smul] at hdet
  intro ε₁ ε₂ hε₁ hε₂ v hv hv₁ hv₂ hDv
  refine (forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two hE hK2
    hKsq hσanti hσK hσtame hPσ hPK one_pos
    (Nat.cast_pos.2 hd) hk hn a).2 hdet ε₁ ε₂ hε₁ hε₂ v hv (by simpa using hv₁)
    (by simpa using hv₂) hDv

end TauCeti
