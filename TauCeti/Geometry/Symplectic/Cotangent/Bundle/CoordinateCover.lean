/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle

/-!
# The cotangent bundle in the coordinates of a map to `ℝ^ι`

Let `B` be a manifold and let `κ : B → ℝ^ι` be smooth. Each `c ∈ ℝ^ι` and `x ∈ B` give the
covector `∑ j, c_j dκ_j` at `x`. This file studies the corresponding map

`Ψ : ℝ^ι × B → T*B`, `Ψ(c, x) = ∑ j, c_j dκ_j` at `x`

(`TauCeti.CotangentBundle.coordinateCover`), which reads covectors in the coordinates `c` dual to
the functions `κ_j`.

* The covector `Ψ(c, x)` evaluates a tangent vector `u` at `x` as `c ⬝ᵥ dκ u`
  (`TauCeti.CotangentBundle.coordinateCover_snd_apply`), and where `dκ_x` is bijective every
  covector at `x` is `Ψ(c, x)` for some `c` (`TauCeti.CotangentBundle.exists_coordinateCover_eq`).
* `Ψ` is smooth, and it pulls the canonical symplectic form `ω = -dλ` back to `∑ j, dκ_j ∧ dc_j`
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_coordinateCover`).
* Where `dκ_x` is bijective, `Ψ` is a local diffeomorphism at `(c, x)`
  (`TauCeti.CotangentBundle.isLocalDiffeomorphAt_coordinateCover`).

So local coordinates `κ` on `B` give the coordinates `(c, κ)` on `T*B` in which
`ω = ∑ j, dκ_j ∧ dc_j`, the canonical coordinates of the cotangent bundle.

## Implementation notes

The pullback of `ω` is computed by comparing Liouville forms with the action–angle covering map
`TauCeti.CotangentBundle.actionAngleCover` of the cotangent bundle of a torus: `Ψ` pulls the
Liouville form back to `∑ j, c_j dκ_j`
(`TauCeti.CotangentBundle.mpullback_liouvilleForm_coordinateCover_apply`), as does
`(c, x) ↦ ∑ j, c_j dθ_j` at the angles `θ = κ x`, whose canonical form is known in these coordinates
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.2 (coordinates on the cotangent bundle).
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set Module
open scoped ContDiff Manifold

namespace TauCeti

namespace CotangentBundle

variable {F H' B : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  (J : ModelWithCorners ℝ F H') [TopologicalSpace B] [ChartedSpace H' B]
  {ι : Type*} [Fintype ι]

/-- The covector `∑ j, c_j dκ_j` at `x`, as a function of `(c, x)`: the cover of `T*B` by the
coordinates dual to the functions `κ_j`. -/
def coordinateCover (κ : B → ι → ℝ) (q : (ι → ℝ) × B) : CotangentBundle J B :=
  TotalSpace.mk' (F →L[ℝ] ℝ) q.2 (∑ j, q.1 j • mvfderiv J (κ · j) q.2)

/-- The covector `∑ j, c_j dκ_j` at `x` lies over `x`. -/
@[simp]
theorem proj_coordinateCover (κ : B → ι → ℝ) (q : (ι → ℝ) × B) :
    (coordinateCover J κ q).proj = q.2 :=
  (rfl)

variable {J} {κ : B → ι → ℝ}

/-- The covector of the cover at `(c, x)` is `∑ j, c_j dκ_j` at `x`. -/
theorem coordinateCover_snd (q : (ι → ℝ) × B) :
    (coordinateCover J κ q).snd = ∑ j, q.1 j • mvfderiv J (κ · j) q.2 :=
  (rfl)

/-- The covector `∑ j, c_j dκ_j` evaluates a tangent vector `u` as `c ⬝ᵥ dκ u`. -/
theorem coordinateCover_snd_apply {q : (ι → ℝ) × B}
    (hκ : MDifferentiableAt J 𝓘(ℝ, ι → ℝ) κ q.2) (u : TangentSpace J q.2) :
    (coordinateCover J κ q).snd u = q.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u := by
  have hd (j : ι) : mvfderiv J (κ · j) q.2 u = mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u j := by
    rw [mvfderiv_apply hκ j, ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply]
    -- The `j`-th coordinate projection, read on the tangent space `ι → ℝ` of `ℝ^ι`.
    rfl
  -- Read `u` as a tangent vector at `q.2`, so that `sum_apply` applies to the covectors on
  -- `TangentSpace J q.2`; each summand `(c • φ) u = c * φ u` then holds by definition.
  refine (sum_apply Finset.univ (fun j ↦ q.1 j • mvfderiv J (κ · j) q.2) u).trans ?_
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (q.1 j * ·) (hd j)

/-- Where `dκ_x` is bijective, every covector at `x` is `∑ j, c_j dκ_j` for some `c`. -/
theorem exists_coordinateCover_eq {x : B} (hκ : MDifferentiableAt J 𝓘(ℝ, ι → ℝ) κ x)
    (hx : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ x)) (α : TangentSpace J x →L[ℝ] ℝ) :
    ∃ c, coordinateCover J κ (c, x) = TotalSpace.mk' (F →L[ℝ] ℝ) x α := by
  classical
  let D : TangentSpace J x ≃ₗ[ℝ] (ι → ℝ) :=
    LinearEquiv.ofBijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ x).toLinearMap hx
  refine ⟨fun j ↦ α (D.symm (Pi.single j 1)), congrArg (TotalSpace.mk' (F →L[ℝ] ℝ) x) ?_⟩
  ext u
  -- `∑ j, α (D⁻¹ eⱼ) (D u)ⱼ = α (D⁻¹ (D u)) = α u`.
  refine (coordinateCover_snd_apply (q := (_, x)) hκ u).trans ?_
  have hu : u = ∑ j, (D u) j • D.symm (Pi.single j 1) := by
    conv_lhs => rw [← D.symm_apply_apply u, pi_eq_sum_univ' (D u)]
    rw [map_sum]
    simp only [map_smul]
  conv_rhs => rw [hu]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

variable [IsManifold J ∞ B]

/-- The cover `(c, x) ↦ ∑ j, c_j dκ_j` is smooth. -/
theorem contMDiff_coordinateCover (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ (coordinateCover J κ) :=
  ContMDiff.sum_sectionAlong Finset.univ _ contMDiff_snd fun j _ ↦
    ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) j).contMDiff.comp contMDiff_fst).smul_totalSpace
      ((ContMDiff.contMDiff_totalSpaceMk_mvfderiv (n := ∞)
        ((contMDiff_pi_module_iff.1 hκ j).of_le (by simp))).comp contMDiff_snd)

/-- **The cover pulls the Liouville form back to `∑ j, c_j dκ_j`**: on a tangent vector `v` at
`(c, x)` the pullback takes the value `c ⬝ᵥ dκ v.2`. -/
theorem mpullback_liouvilleForm_coordinateCover_apply (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ)
    (q : (ι → ℝ) × B) (v : Fin 1 → TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
    mpullback (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ)
        (liouvilleForm J B).val q v =
      q.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 (v 0).2 := by
  rw [mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.snd) (fun _ ↦ rfl)
    ((contMDiff_coordinateCover hκ q).mdifferentiableAt (by simp)), mfderiv_snd]
  -- `ContinuousLinearMap.snd` applied to the tangent vector `v 0` of the product model is
  -- `(v 0).2`.
  exact coordinateCover_snd_apply ((hκ q.2).mdifferentiableAt (by simp)) (v 0).2

variable (κ) in
/-- The angles and actions `(κ x, c)` of `(c, x)`. -/
private def anglesActions (q : (ι → ℝ) × B) : (ι → ℝ) × (ι → ℝ) := (κ q.2, q.1)

omit [IsManifold J ∞ B] in
/-- The map `(c, x) ↦ (κ x, c)` is smooth. -/
private theorem contMDiff_anglesActions (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ) :
    ContMDiff (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞ (anglesActions κ) :=
  (hκ.comp contMDiff_snd).prodMk_space contMDiff_fst

omit [IsManifold J ∞ B] in
/-- The map `(c, x) ↦ (κ x, c)` has derivative `(w, u) ↦ (dκ u, w)`. -/
private theorem hasMFDerivAt_anglesActions (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ)
    (q : (ι → ℝ) × B) :
    HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q
      (((mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) F)).prod
        (ContinuousLinearMap.fst ℝ (ι → ℝ) F)) := by
  have h₁ := ((hκ q.2).mdifferentiableAt (by simp)).hasMFDerivAt.comp q
    (hasMFDerivAt_snd (I := 𝓘(ℝ, ι → ℝ)) (I' := J) q)
  have h₂ := hasMFDerivAt_fst (I := 𝓘(ℝ, ι → ℝ)) (I' := J) q
  -- The model of `(ι → ℝ) × (ι → ℝ)` is that of a normed space, so the derivatives pair up.
  exact ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩

/-- **The canonical form in the coordinates of `κ`.** The cover `(c, x) ↦ ∑ j, c_j dκ_j` pulls the
canonical symplectic form `ω = -dλ` of `T*B` back to `∑ j, dκ_j ∧ dc_j`, which takes the value
`w' ⬝ᵥ dκ u - w ⬝ᵥ dκ u'` on `(w, u), (w', u')`. -/
theorem eval₂_symplecticForm_mfderiv_coordinateCover (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ)
    (q : (ι → ℝ) × B) (v v' : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
    SmoothBundleForm.eval₂ (symplecticForm J B) (coordinateCover J κ q)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ) q v)
        (mfderiv (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (coordinateCover J κ) q v') =
      v'.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 - v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v'.2 := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hΞ := contMDiff_anglesActions hκ
  have hT := contMDiff_actionAngleCover (ι := ι) 1
  -- Both maps pull the Liouville forms back to `∑ j, c_j dκ_j`.
  have hlv : SmoothForm.mpullback (coordinateCover J κ) (contMDiff_coordinateCover hκ)
        (liouvilleForm J B) =
      SmoothForm.mpullback (actionAngleCover 1 ∘ anglesActions κ) (hT.comp hΞ)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle (1 : ℝ))) := by
    refine SmoothBundleForm.ext fun x w ↦ ?_
    obtain ⟨u, rfl⟩ : ∃ u, w = ![u] := ⟨w 0, by ext i; fin_cases i; rfl⟩
    rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_coordinateCover_apply hκ,
      ← SmoothForm.mpullback_mpullback _ _ hΞ hT, SmoothForm.mpullback_apply_one,
      SmoothForm.coe_mpullback, mpullback_liouvilleForm_actionAngleCover_apply,
      (hasMFDerivAt_anglesActions hκ x).mfderiv]
    -- Both sides are `∑ j, c_j (dκ u)_j`: the derivative `(w, u) ↦ (dκ u, w)` of `anglesActions`
    -- has second component `w`, and `(dκ u)_j` is its `j`-th first component, by definition of
    -- `ContinuousLinearMap.prod`, `fst` and `snd`.
    rfl
  -- `ω = -dλ`, and `d` commutes with both pullbacks.
  have hB := SmoothForm.mextDeriv_mpullback_apply_two (coordinateCover J κ)
    (contMDiff_coordinateCover hκ) (liouvilleForm J B) q v v'
  have hTq := SmoothForm.mextDeriv_mpullback_apply_two _ (hT.comp hΞ)
    (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle (1 : ℝ))) q v v'
  rw [hlv, hTq] at hB
  have hG (w : TangentSpace (𝓘(ℝ, ι → ℝ).prod J) q) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod J) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (actionAngleCover 1 ∘ anglesActions κ) q w =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (actionAngleCover 1) (anglesActions κ q)
          (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q w) :=
    mfderiv_comp_apply q ((hT _).mdifferentiableAt (by simp))
      ((hΞ q).mdifferentiableAt (by simp)) w
  have hω := eval₂_symplecticForm_mfderiv_actionAngleCover (ι := ι) 1 (anglesActions κ q)
    (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q v)
    (mfderiv (𝓘(ℝ, ι → ℝ).prod J) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (anglesActions κ) q v')
  rw [← hG, ← hG, SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDeriv,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply] at hω
  rw [SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDeriv, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, ← hB]
  -- `hω` is the value of `-dλ` after the second map; read it with `(w, u) ↦ (dκ u, w)`.
  refine (congrArg Neg.neg ?_).trans (hω.trans ?_)
  · -- The base points `(f ∘ g) q` and `f (g q)` agree by definition.
    rfl
  rw [(hasMFDerivAt_anglesActions hκ q).mfderiv]
  simp only [dotProduct, ← Finset.sum_sub_distrib]
  -- The derivative `(w, u) ↦ (dκ u, w)` has these coordinates by definition.
  exact Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· - ·) (mul_comm _ _) (mul_comm _ _)

/-- If `w' ⬝ᵥ D u - w ⬝ᵥ D u'` vanishes for all `(w', u')`, for a bijective map `D` with `D 0 = 0`,
then `w = 0` and `u = 0`. -/
private theorem eq_zero_of_forall_dotProduct_sub_eq_zero {V : Type*} [Zero V]
    {D : V → ι → ℝ} (hD : Bijective D) (hD₀ : D 0 = 0) {w : ι → ℝ} {u : V}
    (H : ∀ w' u', w' ⬝ᵥ D u - w ⬝ᵥ D u' = 0) : w = 0 ∧ u = 0 := by
  classical
  -- Pairing with `(eᵢ, 0)` gives `(D u)ᵢ = 0`, so `u = 0`.
  have hu : u = 0 := hD.1 <| hD₀.symm ▸ funext fun i ↦ by
    simpa [hD₀] using H (Pi.single i 1) 0
  -- Pairing with `(0, D⁻¹ eᵢ)` then gives `wᵢ = 0`.
  refine ⟨funext fun i ↦ ?_, hu⟩
  obtain ⟨u', hu'⟩ := hD.2 (Pi.single i 1)
  simpa [hu, hu', hD₀] using H 0 u'

/-- **The cover is a local diffeomorphism** at every point `(c, x)` where `dκ_x` is bijective, when
`ι` has `dim B` elements: its pullback of the canonical form is nondegenerate there. -/
theorem isLocalDiffeomorphAt_coordinateCover [FiniteDimensional ℝ F] [BoundarylessManifold J B]
    (hκ : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ κ) {q : (ι → ℝ) × B}
    (hq : Bijective (mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2)) (hι : Fintype.card ι = finrank ℝ F) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (coordinateCover J κ) q := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_coordinateCover hκ).contMDiffOn
    isOpen_univ (mem_univ q) BoundarylessManifold.isInteriorPoint (by simp) ?_
    (by simp [Module.finrank_prod, hι, ContinuousLinearMap.dual_finrank_eq])
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- A vector killed by the derivative pairs to zero with everything under the pulled-back form.
  have H (w' : ι → ℝ) (u' : TangentSpace J q.2) :
      w' ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 v.2 - v.1 ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) κ q.2 u' = 0 := by
    have := eval₂_symplecticForm_mfderiv_coordinateCover hκ q v (w', u')
    rw [hv, SmoothBundleForm.eval₂_zero_left] at this
    exact this.symm
  obtain ⟨h₁, h₂⟩ := eq_zero_of_forall_dotProduct_sub_eq_zero hq (map_zero _) H
  exact Prod.ext h₁ h₂

end CotangentBundle

end TauCeti
