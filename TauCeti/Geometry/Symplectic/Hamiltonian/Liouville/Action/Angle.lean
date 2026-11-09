/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Basic

/-!
# The angle map and its pullback of the symplectic form

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`).

## Moving a section by the flow action

For a section `s` of `F`, so that `F ∘ s = id`, moving `s` by a map `h : (ι → ℝ) → (ι → ℝ)`
changes `s^* σ` by the exact form `∑ᵢ dhᵢ ∧ dcᵢ`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_section`); the moved map
`h • s` is again a section. Choosing `h` with `∑ᵢ dhᵢ ∧ dcᵢ = -s^* σ` therefore turns `s` into an
isotropic section, `s^* σ = 0`, which is Lagrangian when `M` has dimension `2 |ι|`.

## The angle map

Let `λ⁽ⁱ⁾` be a family of periods along `s`, `λ⁽ⁱ⁾(c) • s(c) = s(c)`, and let `A` be action
variables for it, `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`). The
**angle map** (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`) is

`Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`.

It maps `(θ, c)` into the level `F⁻¹(c)`, and it is `2π`-periodic in each angle `θᵢ`. When the
`λ⁽ⁱ⁾(c)` are a basis of the period lattice of `s(c)`, two angles have the same image exactly when
they differ by `2π ℤ^ι`, so `θ ↦ Ψ(θ, c)` descends to an injective map from the torus
`(ℝ / 2πℤ)^ι`. Since the period one-forms `∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` are closed, the pullback of `σ` along
`Ψ` is

`Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ + s^* σ`

(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap`), and for an isotropic section `s`
it is `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ`. This pullback identity is not yet the Liouville–Arnold normal form
`σ = ∑ᵢ dθᵢ ∧ dIᵢ`: that reading needs `(θ, c) ↦ Ψ(θ, c)` to be a local diffeomorphism, so that
`(θ, A)` are coordinates, and this is not proved here.

## Main definitions

* `TauCeti.SmoothTwoForm.IsSymplectic.angleMap`: the angle map `(θ, c) ↦ Ψ(θ, c)`.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `apply_angleMap`, `contMDiffOn_angleMap`: the angle map takes values in the levels of `F`, and it
  is smooth.
* `angleMap_add_two_pi_mul_intCast`, `angleMap_eq_angleMap_iff`: the angle map is `2π`-periodic in
  the angles, and injective modulo `2π ℤ^ι` for a basis of periods.
* `eval₂_mfderiv_angleMap`: `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ + s^* σ`.
* `eval₂_mfderiv_angleMap_of_eval₂_eq_zero`: `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ` for an isotropic section.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (Lagrangian sections and the symplectic form in action-angle coordinates).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Set Filter Module Topology Function Real
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))

include hσ hF hcomm hc

/-! ### The angle map -/

/-- The **angle map** of a map `s : (ι → ℝ) → M` and a family of vectors `λ⁽ⁱ⁾(c)`, `i : ι`,
depending on `c : ι → ℝ`:

`(θ, c) ↦ (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`.

When `s` is a section of `F` and the `λ⁽ⁱ⁾` are periods along it, this map is `2π`-periodic in
each angle `θᵢ` (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_add_two_pi_mul_intCast`), and it pulls
`σ` back to `∑ᵢ dθᵢ ∧ dAᵢ + s^* σ` for action variables `A`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap`). -/
noncomputable def angleMap (s : (ι → ℝ) → M) (p : ι → (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) × (ι → ℝ)) :
    M :=
  (hσ.hamiltonianFlowAction hF hcomm hc (∑ i, ((2 * π)⁻¹ * q.1 i) • p i q.2)).toMul (s q.2)

variable {s : (ι → ℝ) → M} {p : ι → (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

theorem angleMap_apply (q : (ι → ℝ) × (ι → ℝ)) :
    hσ.angleMap hF hcomm hc s p q =
      (hσ.hamiltonianFlowAction hF hcomm hc (∑ i, ((2 * π)⁻¹ * q.1 i) • p i q.2)).toMul (s q.2) :=
  (rfl)

/-- The angle map takes values in the levels of `F`: `F (Ψ(θ, c)) = F (s c)`. In particular, for a
section `s` of `F` near `c`, the angle map sends `(θ, c)` into the level `F⁻¹(c)`. -/
theorem apply_angleMap (q : (ι → ℝ) × (ι → ℝ)) :
    F (hσ.angleMap hF hcomm hc s p q) = F (s q.2) :=
  hσ.apply_hamiltonianFlowAction hF hcomm hc _ _

/-- **The angle map is `2π`-periodic in the angles.** If the `λ⁽ⁱ⁾(c)` are periods of `s c`, then
shifting the angles by `2π m`, `m ∈ ℤ^ι`, does not change the image. -/
theorem angleMap_add_two_pi_mul_intCast
    (hp : ∀ i, p i c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c)) (θ : ι → ℝ)
    (m : ι → ℤ) :
    hσ.angleMap hF hcomm hc s p (θ + fun i ↦ 2 * π * m i, c) =
      hσ.angleMap hF hcomm hc s p (θ, c) := by
  have hsum : ∑ i, ((2 * π)⁻¹ * (θ + fun i ↦ 2 * π * m i) i) • p i c =
      ∑ i, ((2 * π)⁻¹ * θ i) • p i c + ∑ i, m i • p i c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Pi.add_apply, mul_add, add_smul, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul, Int.cast_smul_eq_zsmul]
  have hmem : ∑ i, m i • p i c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) :=
    AddSubgroup.sum_mem _ fun i _ ↦ AddSubgroup.zsmul_mem _ (hp i) _
  rw [angleMap_apply, angleMap_apply, hsum, hσ.hamiltonianFlowAction_add_apply hF hcomm hc,
    (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hmem]

/-- **The angle map is injective modulo `2π ℤ^ι`.** If the `λ⁽ⁱ⁾(c)` are linearly independent and
generate the period lattice of `s c`, then two angles have the same image under the angle map
exactly when they differ by `2π m` for some `m ∈ ℤ^ι`. Thus `θ ↦ Ψ(θ, c)` descends to an injective
map from the torus `(ℝ / 2πℤ)^ι`. -/
theorem angleMap_eq_angleMap_iff (hli : LinearIndependent ℝ fun i ↦ p i c)
    (hcl : hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
      AddSubgroup.closure (range fun i ↦ p i c)) {θ θ' : ι → ℝ} :
    hσ.angleMap hF hcomm hc s p (θ, c) = hσ.angleMap hF hcomm hc s p (θ', c) ↔
      ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  have hdiff : -∑ i, ((2 * π)⁻¹ * θ i) • p i c + ∑ i, ((2 * π)⁻¹ * θ' i) • p i c =
      ∑ i, ((2 * π)⁻¹ * (θ' i - θ i)) • p i c := by
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    simp only [mul_sub, sub_smul]
  rw [angleMap_apply, angleMap_apply, hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc, hcl,
    ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun, hdiff]
  have h2π : (2 * π) ≠ 0 := by positivity
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, funext fun i ↦ ?_⟩
    have key := Fintype.linearIndependent_iff.1 hli (fun i ↦ (m i : ℝ) - (2 * π)⁻¹ * (θ' i - θ i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, hm, sub_self]) i
    rw [sub_eq_zero] at key
    rw [Pi.add_apply, key]
    field_simp
    ring
  · rintro ⟨m, rfl⟩
    refine ⟨m, Finset.sum_congr rfl fun i _ ↦ ?_⟩
    rw [Pi.add_apply, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul,
      Int.cast_smul_eq_zsmul]

/-- **The angle map is smooth.** If `s` and the `λ⁽ⁱ⁾` are smooth on `t`, the angle map is smooth
on `(ι → ℝ) × t`. -/
theorem contMDiffOn_angleMap {t : Set (ι → ℝ)} (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t)
    (hp : ∀ i, ContDiffOn ℝ ∞ (p i) t) :
    ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ (hσ.angleMap hF hcomm hc s p) (univ ×ˢ t) := by
  have ht : MapsTo Prod.snd (univ ×ˢ t : Set ((ι → ℝ) × (ι → ℝ))) t := fun q hq ↦ (mem_prod.1 hq).2
  have hu : ContDiffOn ℝ ∞
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ ∑ i, ((2 * π)⁻¹ * q.1 i) • p i q.2) (univ ×ˢ t) :=
    ContDiffOn.sum fun i _ ↦
      (by fun_prop : ContDiff ℝ ∞ fun q : (ι → ℝ) × (ι → ℝ) ↦ (2 * π)⁻¹ * q.1 i).contDiffOn.fun_smul
        ((hp i).comp contDiffOn_snd ht)
  have hsn : ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ (s ∘ Prod.snd) (univ ×ˢ t) :=
    hs.comp contDiffOn_snd.contMDiffOn ht
  rw [show hσ.angleMap hF hcomm hc s p = _ from funext (hσ.angleMap_apply hF hcomm hc)]
  exact (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp_contMDiffOn
    (hu.contMDiffOn.prodMk hsn)

/-- **The pullback of `σ` along the angle map.** Let `s` be a section of `F` near `c`,
differentiable at `c`, let the `λ⁽ⁱ⁾`, differentiable at `c`, be periods along it near `c`, and
let `A` be action variables for them at `c`, `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`. Then at `(θ, c)` the
angle map pulls `σ` back to

`Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ + s^* σ`.

The terms coming from the variation of the periods with `c` cancel because the period one-forms
`∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` are closed
(`TauCeti.SmoothTwoForm.IsSymplectic.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer`). -/
theorem eval₂_mfderiv_angleMap {A : (ι → ℝ) → ι → ℝ}
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hp : ∀ i, DifferentiableAt ℝ (p i) c)
    (hps : ∀ i, ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (θ a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ (hσ.angleMap hF hcomm hc s p (θ, c))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b) +
        SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') := by
  set u : (ι → ℝ) × (ι → ℝ) → ι → ℝ := fun q ↦ ∑ i, ((2 * π)⁻¹ * q.1 i) • p i q.2
  -- The derivative of the vector `u (θ, c) = ∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)` by which `s c` is moved.
  have hu : HasFDerivAt u (∑ i, (((2 * π)⁻¹ * θ i) •
      (fderiv ℝ (p i) c).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) +
        ((2 * π)⁻¹ • ((proj i : (ι → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)))).smulRight (p i c))) (θ, c) :=
    HasFDerivAt.fun_sum fun i _ ↦
      ((((proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).hasFDerivAt).const_mul _).smul
        ((hp i).hasFDerivAt.comp (θ, c) hasFDerivAt_snd)
  have hdu (a b : ι → ℝ) : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, ι → ℝ) u (θ, c) (a, b) =
      ∑ i, ((2 * π)⁻¹ * θ i) • fderiv ℝ (p i) c b + ∑ i, ((2 * π)⁻¹ * a i) • p i c := by
    have h : fderiv ℝ u (θ, c) (a, b) =
        ∑ i, ((2 * π)⁻¹ * θ i) • fderiv ℝ (p i) c b + ∑ i, ((2 * π)⁻¹ * a i) • p i c := by
      rw [hu.fderiv, ← Finset.sum_add_distrib]
      simp [smul_eq_mul, mul_assoc]
    exact (congrArg (fun L ↦ L (a, b)) hu.differentiableAt.hasFDerivAt.hasMFDerivAt.mfderiv).trans h
  -- The moved map is `s ∘ Prod.snd`, and `F ∘ s ∘ Prod.snd = Prod.snd` near `(θ, c)`.
  have hsd : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (fun q ↦ s q.2) (θ, c) :=
    hs.comp (θ, c) differentiableAt_snd.mdifferentiableAt
  have hds (a b : ι → ℝ) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (fun q ↦ s q.2) (θ, c) (a, b) =
        mfderiv 𝓘(ℝ, ι → ℝ) I s c b := by
    have h := hs.hasMFDerivAt.comp (θ, c) (hasFDerivAt_snd :
      HasFDerivAt (Prod.snd : (ι → ℝ) × (ι → ℝ) → ι → ℝ) (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))
        (θ, c)).hasMFDerivAt
    exact congrArg (fun L ↦ L (a, b)) h.mfderiv
  have hdFs (a b : ι → ℝ) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, ι → ℝ) (F ∘ fun q ↦ s q.2) (θ, c) (a, b) = b := by
    have hev : (F ∘ fun q : (ι → ℝ) × (ι → ℝ) ↦ s q.2) =ᶠ[𝓝 (θ, c)] Prod.snd :=
      (continuous_snd.tendsto (θ, c)).eventually hFs
    exact congrArg (fun L ↦ L (a, b)) ((hasFDerivAt_snd :
      HasFDerivAt (Prod.snd : (ι → ℝ) × (ι → ℝ) → ι → ℝ) (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))
        (θ, c)).congr_of_eventuallyEq hev).hasMFDerivAt.mfderiv
  -- The period one-forms are closed.
  have hsym (i : ι) : fderiv ℝ (p i) c b ⬝ᵥ b' = fderiv ℝ (p i) c b' ⬝ᵥ b :=
    hσ.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer hF hcomm hc hs hFs (hp i) (hps i)
      b b'
  have hdA (i : ι) (w : ι → ℝ) : fderiv ℝ (fun c ↦ A c i) c w = (2 * π)⁻¹ * (p i c ⬝ᵥ w) := by
    rw [(hA i).fderiv]
    simp [dotProduct, Finset.mul_sum, mul_comm]
  rw [show hσ.angleMap hF hcomm hc s p = fun q ↦
    (hσ.hamiltonianFlowAction hF hcomm hc (u q)).toMul (s q.2) from
      funext (hσ.angleMap_apply hF hcomm hc)]
  refine (hσ.eval₂_mfderiv_hamiltonianFlowAction_comp hF hcomm hc
    (hu.differentiableAt.mdifferentiableAt) hsd (a, b) (a', b')).trans ?_
  rw [hdu, hdu, hds, hds, hdFs, hdFs]
  simp only [add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul, hsym, hdA]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The angle map of an isotropic section.** If, in addition to the hypotheses of
`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap`, the section `s` is isotropic at `c`,
`s^* σ = 0`, then the angle map pulls `σ` back to `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ` at `(θ, c)`. Once `Ψ`
is known to be a local diffeomorphism, so that `(θ, A)` are coordinates, this gives the
Liouville–Arnold normal form `σ = ∑ᵢ dθᵢ ∧ dIᵢ` in the angles `θᵢ` and the actions `Iᵢ = Aᵢ`. -/
theorem eval₂_mfderiv_angleMap_of_eval₂_eq_zero {A : (ι → ℝ) → ι → ℝ}
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hL : ∀ b b', SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hp : ∀ i, DifferentiableAt ℝ (p i) c)
    (hps : ∀ i, ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (θ a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ (hσ.angleMap hF hcomm hc s p (θ, c))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b) := by
  rw [hσ.eval₂_mfderiv_angleMap hF hcomm hc hs hFs hp hps hA]
  exact add_eq_left.2 (hL b b')

end IsSymplectic

end SmoothTwoForm

end TauCeti
