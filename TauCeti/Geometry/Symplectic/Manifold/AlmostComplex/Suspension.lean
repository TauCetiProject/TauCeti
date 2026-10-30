/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Suspension
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# Block almost complex structures on a symplectic suspension

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold and
`X_φ = (ℝ / ℤ)_s × Y_φ` the product of a circle with its smooth mapping torus
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))`. The map

`q : (ℝ × ℝ) × M → X_φ`, `((s, t), x) ↦ ([s], [t, x])`

(`TauCeti.SmoothMappingTorus.suspensionMk φ`) is a surjective smooth local diffeomorphism. Its
fibers are the orbits of the deck transformations `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)`
for integers `j` and `k`.

On the cover, a jointly smooth family `K_((s,t),x)` of almost complex structures on `T_x M` gives
the block structure `J_cover (a ∂_s + b ∂_t + v) = -b ∂_s + a ∂_t + K v`
(`TauCeti.SmoothAlmostComplexStructure.prodFamily`). It is invariant under the deck
transformations when `K` is periodic in `s` and satisfies the seam equation
`dφ⁻¹ ∘ K_((s,t),x) = K_((s,t+1),φ⁻¹ x) ∘ dφ⁻¹`. In that case `J_cover` descends to a smooth almost
complex structure `J` on `X_φ` (`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`)
with `J ∂_s = T` and `J T = -∂_s`, where `T = ∂_t` is the suspension vector field, and with `J = K`
on the vertical tangent spaces. The family `K` need not be invariant under `φ`: the seam equation
only relates its values at heights `t` and `t + 1`.

The form `Ω = ds ∧ dt + σ_v` of the suspension pulls back along `q` to `ds ∧ dt + σ`
(`TauCeti.SmoothMappingTorus.mpullback_suspensionMk_suspensionForm`). Hence `J` is compatible with
`Ω` when every `K_p` is compatible with `σ`, and `Ω` tames `J` when `σ` tames every `K_p`.

## Main definitions

* `TauCeti.SmoothMappingTorus.suspensionMk φ`: the covering map `((s, t), x) ↦ ([s], [t, x])`.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure φ K hK hper hseam`: the descent of
  the block structure of a periodic family `K` satisfying the seam equation.

## Main results

* `TauCeti.SmoothMappingTorus.isLocalDiffeomorph_suspensionMk`,
  `TauCeti.SmoothMappingTorus.suspensionMk_eq_suspensionMk_iff`: `q` is a local diffeomorphism,
  whose fibers are the deck orbits.
* `TauCeti.SmoothMappingTorus.mfderiv_suspensionMk_apply`: the differential of `q`.
* `TauCeti.SmoothMappingTorus.mpullback_suspensionMk_suspensionForm`: `q^* Ω = ds ∧ dt + σ`.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure_apply_mfderiv`: `J` sends
  `a ∂_s + b ∂_t + v` to `-b ∂_s + a ∂_t + K v`.
* `TauCeti.SmoothMappingTorus.eq_suspensionAlmostComplexStructure_iff`: `J` is the only almost
  complex structure on `X_φ` covered by the block structure.
* `TauCeti.SmoothMappingTorus.tames_suspensionForm_suspensionAlmostComplexStructure`,
  `TauCeti.SmoothMappingTorus.compatible_suspensionForm_suspensionAlmostComplexStructure`:
  tameness and compatibility with `Ω`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (block almost complex structures on `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (compatible almost complex structures).
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The covering map -/

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- The covering map `((s, t), x) ↦ ([s], [t, x])` of `(ℝ / ℤ) × Y_φ` by `(ℝ × ℝ) × M`. -/
def suspensionMk (p : (ℝ × ℝ) × M) : UnitAddCircle × SmoothMappingTorus φ :=
  ((p.1.1 : UnitAddCircle), mk φ p.1.2 p.2)

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
@[simp]
theorem suspensionMk_apply (s t : ℝ) (x : M) :
    suspensionMk φ ((s, t), x) = ((s : UnitAddCircle), mk φ t x) :=
  (rfl)

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
theorem suspensionMk_surjective : Surjective (suspensionMk φ) := by
  rintro ⟨θ, y⟩
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  exact ⟨((s, t), x), rfl⟩

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- Two points of `(ℝ × ℝ) × M` have the same image under `q` exactly when they differ by a
deck transformation `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)`. -/
theorem suspensionMk_eq_suspensionMk_iff {p p' : (ℝ × ℝ) × M} :
    suspensionMk φ p = suspensionMk φ p' ↔
      ∃ j k : ℤ, p' = (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) := by
  obtain ⟨⟨s, t⟩, x⟩ := p
  obtain ⟨⟨s', t'⟩, x'⟩ := p'
  have hs : ((s : UnitAddCircle) = s') ↔ ∃ j : ℤ, s' = s + j := by
    rw [eq_comm, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, mul_one]
    exact exists_congr fun j ↦ by constructor <;> intro h <;> linarith
  have ht : mk φ t x = mk φ t' x' ↔ ∃ k : ℤ, t' = t + k ∧ x' = (φ ^ (-k)) x := by
    rw [eq_comm, mk_eq_mk_iff]
  simp only [suspensionMk_apply, Prod.mk.injEq, hs, ht, Prod.mk_add_mk]
  constructor
  · rintro ⟨⟨j, hj⟩, k, hk, hx⟩
    exact ⟨j, k, ⟨hj, hk⟩, hx⟩
  · rintro ⟨j, k, ⟨hj, hk⟩, hx⟩
    exact ⟨⟨j, hj⟩, k, hk, hx⟩

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- The deck transformations `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)` preserve `q`. -/
theorem suspensionMk_deck (j k : ℤ) (p : (ℝ × ℝ) × M) :
    suspensionMk φ (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) = suspensionMk φ p :=
  ((suspensionMk_eq_suspensionMk_iff φ).2 ⟨j, k, rfl⟩).symm

theorem isLocalDiffeomorph_suspensionMk :
    IsLocalDiffeomorph (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ (suspensionMk φ) := by
  -- Reassociating `(ℝ × ℝ) × M` as `ℝ × (ℝ × M)` is a diffeomorphism.
  have hfst : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ∞ (fun p : (ℝ × ℝ) × M ↦ p.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_fst
  have hsnd : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ∞ (fun p : (ℝ × ℝ) × M ↦ p.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_fst
  let e : ((ℝ × ℝ) × M) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ).prod I, 𝓘(ℝ).prod (𝓘(ℝ).prod I)⟯ ℝ × (ℝ × M) :=
    { toEquiv := Equiv.prodAssoc ℝ ℝ M
      contMDiff_toFun := hfst.prodMk (hsnd.prodMk contMDiff_snd)
      contMDiff_invFun := (contMDiff_fst.prodMk_space (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd) }
  have hq : suspensionMk φ = Prod.map ((↑) : ℝ → UnitAddCircle) (uncurry (mk φ)) ∘ e := (rfl)
  rw [hq]
  exact fun p ↦ IsLocalDiffeomorphAt.comp (hf := e.isLocalDiffeomorph p)
    (hg := ((AddCircle.isLocalDiffeomorph_coe 1 ∞).prodMap (isLocalDiffeomorph_uncurry_mk φ)) (e p))

/-- The differential of `q` sends `a ∂_s + b ∂_t + v` at `((s, t), x)` to `a ∂_s` plus the image
of `(b, v)` under the differential of `(t, x) ↦ [t, x]`. -/
theorem mfderiv_suspensionMk_apply (s t : ℝ) (x : M) (u : ℝ × ℝ) (v : TangentSpace I x) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) ((s, t), x)
        ((Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v)) =
      (Manifold.tangentSpaceProdEquiv (suspensionMk φ ((s, t), x))).symm
        (u.1, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (u.2, v))) := by
  have h₀ : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (fun p : (ℝ × ℝ) × M ↦ p.1.1) ((s, t), x)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) F)) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasMFDerivAt.comp ((s, t), x) (hasMFDerivAt_fst _)
  have h₁ := (AddCircle.hasMFDerivAt_coe (1 : ℝ) s).comp ((s, t), x) h₀
  have h₂ : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod I) (fun p : (ℝ × ℝ) × M ↦ (p.1.2, p.2))
      ((s, t), x) (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) F)).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) F)) :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasMFDerivAt.comp ((s, t), x) (hasMFDerivAt_fst _)).prodMk
      (hasMFDerivAt_snd _)
  have h₃ := (((contMDiff_uncurry_mk φ (t, x)).mdifferentiableAt (by simp)).hasMFDerivAt).comp
    ((s, t), x) h₂
  have h : HasMFDerivAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ)
      ((s, t), x) _ := h₁.prodMk h₃
  rw [h.mfderiv, Manifold.tangentSpaceProdEquiv_symm_apply,
    Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  -- The derivative of `q` acts on `(u, v)` componentwise.
  rfl

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The form `Ω = ds ∧ dt + σ_v` of the suspension pulls back along `q` to the form `ds ∧ dt + σ`
of `(ℝ × ℝ) × M`. -/
theorem mpullback_suspensionMk_suspensionForm :
    SmoothForm.mpullback (suspensionMk φ) (isLocalDiffeomorph_suspensionMk φ).contMDiff
        (suspensionForm φ σ hσ) =
      (stdSymplecticForm (V := ℝ)).constSmooth.prod σ := by
  refine SmoothBundleForm.ext_eval₂ fun ⟨⟨s, t⟩, x⟩ V W ↦ ?_
  -- Write `V` and `W` through their components.
  obtain ⟨u, v, rfl⟩ : ∃ (u : ℝ × ℝ) (v : TangentSpace I x),
      (Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v) = V :=
    ⟨_, _, ContinuousLinearEquiv.symm_apply_apply _ V⟩
  obtain ⟨u', v', rfl⟩ : ∃ (u : ℝ × ℝ) (v : TangentSpace I x),
      (Manifold.tangentSpaceProdEquiv ((s, t), x)).symm (u, v) = W :=
    ⟨_, _, ContinuousLinearEquiv.symm_apply_apply _ W⟩
  rw [SmoothForm.eval₂_mpullback, mfderiv_suspensionMk_apply, mfderiv_suspensionMk_apply,
    suspensionMk_apply, eval₂_suspensionForm_mk, SmoothTwoForm.eval₂_prod,
    SymplecticForm.fromTangentSpace_constSmooth_apply, stdSymplecticForm_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply, Real.inner_apply]
  -- `NormedSpace.fromTangentSpace` is the identity of `ℝ × ℝ`.
  change u.1 * u'.2 - u'.1 * u.2 + _ = u.1 * u'.2 - u.2 * u'.1 + _
  ring

/-! ### The descended block structure -/

variable [FiniteDimensional ℝ F]
  (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
    (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))
  (hper : ∀ (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2), K (p.1 + (1, 0), p.2) w = K p w)
  (hseam : ∀ (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2),
    mfderiv I I φ.symm p.2 (K p w) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 w))

omit [FiniteDimensional ℝ F] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- A family of almost complex structures takes the same value at equal points. -/
private theorem apply_congr_point {p p' : (ℝ × ℝ) × M} (h : p = p') (w : F) :
    K p w = K p' w := by
  subst h
  rfl

omit [FiniteDimensional ℝ F] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
include hper hseam in
/-- A periodic family satisfying the seam equation satisfies the seam equation for every deck
transformation `((s, t), x) ↦ ((s + j, t + k), φ ^ (-k) x)`. -/
private theorem mfderiv_zpow_apply (j k : ℤ) (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2) :
    mfderiv I I (φ ^ (-k)) p.2 (K p w) =
      K (p.1 + ((j : ℝ), (k : ℝ)), (φ ^ (-k)) p.2) (mfderiv I I (φ ^ (-k)) p.2 w) := by
  -- Periodicity in `s` for all integer translations.
  have hperZ (j : ℤ) (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2) :
      K (p.1 + ((j : ℝ), 0), p.2) w = K p w := by
    induction j using Int.induction_on generalizing p with
    | zero => exact apply_congr_point K (by simp [Prod.mk_zero_zero]) w
    | succ i ih =>
      rw [← ih p w, ← hper (p.1 + (((i : ℤ) : ℝ), 0), p.2) w]
      exact apply_congr_point K (by ext <;> simp; ring) w
    | pred i ih =>
      rw [← ih p w, ← hper (p.1 + (((-i - 1 : ℤ) : ℝ), 0), p.2) w]
      exact apply_congr_point K (by ext <;> simp; ring) w
  -- The inverse seam equation `dφ ∘ K_((s,t),x) = K_((s,t-1),φ x) ∘ dφ`.
  have hseam' (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2) :
      mfderiv I I φ p.2 (K p w) = K (p.1 - (0, 1), φ p.2) (mfderiv I I φ p.2 w) := by
    have hinv (y : M) (u : TangentSpace I y) :
        mfderiv I I φ.symm (φ y) (mfderiv I I φ y u) = u := by
      rw [← mfderiv_comp_apply y (φ.symm.mdifferentiable (by simp) (φ y))
        (φ.mdifferentiable (by simp) y), show ⇑φ.symm ∘ ⇑φ = id from funext φ.symm_apply_apply,
        mfderiv_id, ContinuousLinearMap.id_apply]
    refine (φ.symm.isInvertible_mfderiv (x := φ p.2) (by simp)).injective ?_
    rw [hinv, hseam (p.1 - (0, 1), φ p.2), hinv]
    exact apply_congr_point K (by simp) w
  -- The seam equation for the powers `φ ^ (-k)`.
  have hseamZ (k : ℤ) (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2) :
      mfderiv I I (φ ^ (-k)) p.2 (K p w) =
        K (p.1 + (0, (k : ℝ)), (φ ^ (-k)) p.2) (mfderiv I I (φ ^ (-k)) p.2 w) := by
    induction k using Int.induction_on generalizing p with
    | zero =>
      rw [show φ ^ (-(0 : ℤ)) = 1 by simp, Diffeomorph.coe_one, mfderiv_id]
      exact apply_congr_point K (by simp [Prod.mk_zero_zero]) w
    | succ i ih =>
      have hcoe : ⇑(φ ^ (-((i : ℤ) + 1))) = φ.symm ∘ ⇑(φ ^ (-(i : ℤ))) := by
        rw [show φ ^ (-((i : ℤ) + 1)) = φ⁻¹ * φ ^ (-(i : ℤ)) by group, Diffeomorph.coe_mul,
          Diffeomorph.coe_inv]
      have hd := (φ ^ (-(i : ℤ))).mdifferentiable (by simp) p.2
      rw [hcoe, mfderiv_comp_apply p.2 (φ.symm.mdifferentiable (by simp) _) hd, ih p w,
        mfderiv_comp_apply p.2 (φ.symm.mdifferentiable (by simp) _) hd,
        hseam (p.1 + (0, ((i : ℤ) : ℝ)), (φ ^ (-(i : ℤ))) p.2)]
      exact apply_congr_point K (by ext <;> simp; ring) _
    | pred i ih =>
      have hcoe : ⇑(φ ^ (-(-(i : ℤ) - 1))) = φ ∘ ⇑(φ ^ (-(-(i : ℤ)))) := by
        rw [show φ ^ (-(-(i : ℤ) - 1)) = φ * φ ^ (-(-(i : ℤ))) by group, Diffeomorph.coe_mul]
      have hd := (φ ^ (-(-(i : ℤ)))).mdifferentiable (by simp) p.2
      rw [hcoe, mfderiv_comp_apply p.2 (φ.mdifferentiable (by simp) _) hd, ih p w,
        mfderiv_comp_apply p.2 (φ.mdifferentiable (by simp) _) hd,
        hseam' (p.1 + (0, ((-(i : ℤ) : ℤ) : ℝ)), (φ ^ (-(-(i : ℤ)))) p.2)]
      exact apply_congr_point K (by ext <;> simp; ring) _
  rw [hseamZ k p w, ← hperZ j]
  exact apply_congr_point K (by ext <;> simp [add_comm]) _

include hper hseam in
/-- The block structure of a periodic family satisfying the seam equation is consistent with `q`:
its deck transformations intertwine it. -/
private theorem mfderiv_suspensionMk_prodFamily_consistent :
    ∀ (p p' : (ℝ × ℝ) × M), suspensionMk φ p = suspensionMk φ p' →
      ∀ (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) (w : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p'),
        mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p v =
            mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p' w →
          mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p
              (SmoothAlmostComplexStructure.prodFamily
                (AlmostComplexStructure.product ℝ).constSmooth K hK p v) =
            mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p'
              (SmoothAlmostComplexStructure.prodFamily
                (AlmostComplexStructure.product ℝ).constSmooth K hK p' w) := by
  refine SmoothAlmostComplexStructure.mfderiv_apply_eq_of_deck
    ((isLocalDiffeomorph_suspensionMk φ).mdifferentiable (by simp)) (fun p p' hpp' ↦ ?_)
    (fun p ↦ ((isLocalDiffeomorph_suspensionMk φ).isInvertible_mfderiv (by simp) p).injective)
  obtain ⟨j, k, rfl⟩ := (suspensionMk_eq_suspensionMk_iff φ).1 hpp'
  refine ⟨Prod.map (fun a ↦ a + ((j : ℝ), (k : ℝ))) ⇑(φ ^ (-k)), rfl,
    funext fun p ↦ suspensionMk_deck φ j k p, ?_, ?_⟩
  · exact ((differentiableAt_id.add_const _).mdifferentiableAt).prodMap
      ((φ ^ (-k)).mdifferentiable (by simp) p.2)
  · exact (SmoothAlmostComplexStructure.mfderiv_translation_prodFamily_iff K hK _ _ p).2
      (mfderiv_zpow_apply φ K hper hseam j k p)

/-- The smooth almost complex structure on `X_φ = (ℝ / ℤ) × Y_φ` induced by a jointly smooth
family `K_((s,t),x)` of almost complex structures on `T_x M` that is periodic in `s` and satisfies
the seam equation `dφ⁻¹ ∘ K_((s,t),x) = K_((s,t+1),φ⁻¹ x) ∘ dφ⁻¹`. It is the descent of the block
structure `a ∂_s + b ∂_t + v ↦ -b ∂_s + a ∂_t + K v` along `q`
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure_apply_mfderiv`). -/
def suspensionAlmostComplexStructure :
    SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
      (UnitAddCircle × SmoothMappingTorus φ) :=
  SmoothAlmostComplexStructure.descend
    (SmoothAlmostComplexStructure.prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK)
    (isLocalDiffeomorph_suspensionMk φ) (suspensionMk_surjective φ)
    (mfderiv_suspensionMk_prodFamily_consistent φ K hK hper hseam)

/-- The induced almost complex structure sends `a ∂_s + b ∂_t + v` at `([s], [t, x])` to
`-b ∂_s + a ∂_t + K_((s,t),x) v`. In particular `J ∂_s = T` and `J T = -∂_s` for the suspension
vector field `T = ∂_t`. -/
theorem suspensionAlmostComplexStructure_apply_mfderiv (s t : ℝ) (x : M) (a b : ℝ)
    (v : TangentSpace I x) :
    suspensionAlmostComplexStructure φ K hK hper hseam (suspensionMk φ ((s, t), x))
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
      (Manifold.tangentSpaceProdEquiv _).symm
        (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K ((s, t), x) v))) := by
  have h := SmoothAlmostComplexStructure.descend_apply_mfderiv
    (hq := isLocalDiffeomorph_suspensionMk φ) (hsurj := suspensionMk_surjective φ)
    (hJ := mfderiv_suspensionMk_prodFamily_consistent φ K hK hper hseam) ((s, t), x)
    ((Manifold.tangentSpaceProdEquiv ((s, t), x)).symm ((a, b), v))
  rw [mfderiv_suspensionMk_apply, SmoothAlmostComplexStructure.prodFamily_apply,
    ContinuousLinearEquiv.apply_symm_apply] at h
  -- The horizontal block is the standard structure `(a, b) ↦ (-b, a)` of `ℝ × ℝ`.
  rw [AlmostComplexStructure.constSmooth_apply, AlmostComplexStructure.product_apply,
    mfderiv_suspensionMk_apply] at h
  exact h

/-- The induced almost complex structure is the only almost complex structure `J'` on `X_φ` with
`J' (q p) (dq_p v) = dq_p (J_cover p v)` for the block structure `J_cover` on the cover. -/
theorem eq_suspensionAlmostComplexStructure_iff
    {J' : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
      (UnitAddCircle × SmoothMappingTorus φ)} :
    J' = suspensionAlmostComplexStructure φ K hK hper hseam ↔
      ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p),
        J' (suspensionMk φ p)
            (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p v) =
          mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionMk φ) p
            (SmoothAlmostComplexStructure.prodFamily
              (AlmostComplexStructure.product ℝ).constSmooth K hK p v) :=
  SmoothAlmostComplexStructure.eq_descend_iff

/-- If `σ` tames every vertical structure `K_p`, then `Ω = ds ∧ dt + σ_v` tames the induced
almost complex structure. -/
theorem tames_suspensionForm_suspensionAlmostComplexStructure
    (htame : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ σ p.2 v (K p v)) :
    (suspensionForm φ σ hσ).Tames (suspensionAlmostComplexStructure φ K hK hper hseam) := by
  rw [suspensionAlmostComplexStructure, SmoothAlmostComplexStructure.tames_descend_iff,
    mpullback_suspensionMk_suspensionForm]
  exact SmoothAlmostComplexStructure.tames_prodFamily _ K hK
    (SymplecticForm.compatible_constSmooth_iff.2 stdSymplecticForm_compatible_product).tames htame

/-- If every vertical structure `K_p` is compatible with a nondegenerate `σ`, then the induced
almost complex structure is compatible with `Ω = ds ∧ dt + σ_v`. -/
theorem compatible_suspensionForm_suspensionAlmostComplexStructure (hσn : σ.IsNondegenerate)
    (hcompat : ∀ p : (ℝ × ℝ) × M, (hσn.symplecticFormAt p.2).Compatible (K p)) :
    (suspensionForm φ σ hσ).Compatible (suspensionAlmostComplexStructure φ K hK hper hseam) := by
  rw [suspensionAlmostComplexStructure, SmoothAlmostComplexStructure.compatible_descend_iff,
    mpullback_suspensionMk_suspensionForm]
  exact SmoothAlmostComplexStructure.compatible_prodFamily _ K hK
    (SymplecticForm.compatible_constSmooth_iff.2 stdSymplecticForm_compatible_product) hσn hcompat

end TauCeti.SmoothMappingTorus
