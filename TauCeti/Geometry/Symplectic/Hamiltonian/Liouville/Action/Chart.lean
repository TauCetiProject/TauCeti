/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Angle

/-!
# Action-angle charts near a regular Liouville torus

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions with complete
Hamiltonian vector fields, generating the Hamiltonian flow action `v • y` of `ι → ℝ` on `M`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`). For a section `s` of `F` and periods
`λ⁽ⁱ⁾(c)` of `s c`, the angle map (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`) is

`Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`.

This file proves that `Ψ` is a chart of `M` in which the Liouville–Arnold normal form holds.

* **The flows are translations of the angles.** Moving `Ψ(θ, c)` by `∑ᵢ wᵢ λ⁽ⁱ⁾(c)` adds `2π w`
  to the angles (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction_apply_angleMap`). In
  terms of action variables `A`, with `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`, moving by `v` adds `u` to the
  angles whenever `∑ᵢ uᵢ dAᵢ = v ⬝ᵥ dc`
  (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction_apply_angleMap_of_fderiv`). For a
  Hamiltonian `H = h ∘ F` the vector `v` is the gradient of `h`, and this is the statement
  `X_H = ∑ᵢ (∂K / ∂Iᵢ) ∂_{θᵢ}` for `H = K(I)` in the actions `I = A`.
* **The angle map is a local diffeomorphism.** If the section `s` is isotropic, `s^* σ = 0`, then
  `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ`
  (`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap_of_eval₂_eq_zero`).
  When the periods `λ⁽ⁱ⁾(c)` are linearly independent this form is nondegenerate, so the
  differential of `Ψ` is injective
  (`TauCeti.SmoothTwoForm.IsSymplectic.injective_mfderiv_angleMap`), hence invertible since both
  sides have dimension `2 |ι|`, and `Ψ` is a local diffeomorphism at every `(θ, c)`
  (`TauCeti.SmoothTwoForm.IsSymplectic.isLocalDiffeomorphAt_angleMap`).
* **The angle map is injective modulo `2πℤ^ι`.** Since `F (Ψ(θ, c)) = c`, two points `(θ, c)` and
  `(θ', c')` have the same image exactly when `c = c'` and `θ' - θ ∈ 2πℤ^ι`, as soon as the
  `λ⁽ⁱ⁾(c)` form a basis of the period lattice of `s c`
  (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_eq_angleMap_iff_of_section`).

Near a compact connected component of a level consisting of regular points, with an isotropic
section through it, all these hypotheses hold on a neighbourhood `U` of the level value
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_angleMap_of_isCompact`). Then
`Ψ` is a local diffeomorphism on `ℝ^ι × U` whose fibres are exactly the orbits of `2πℤ^ι` acting on
the angles, and it pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ` for action variables `A` that are a local
diffeomorphism at the level value. These are the properties saying that `(θ mod 2π, A)` are
action-angle coordinates near the torus, in which `σ = ∑ᵢ dθᵢ ∧ dIᵢ` with `I = A`; the map induced
on the torus `(ℝ / 2πℤ)^ι` itself is not constructed in this file.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `hamiltonianFlowAction_apply_angleMap`, `hamiltonianFlowAction_apply_angleMap_of_fderiv`: the
  Hamiltonian flows act on the angles by translations.
* `injective_mfderiv_angleMap`, `isLocalDiffeomorphAt_angleMap`: for an isotropic section and
  independent periods, the angle map is a local diffeomorphism.
* `angleMap_eq_angleMap_iff_of_section`: the angle map is injective modulo `2πℤ^ι`.
* `exists_isLocalDiffeomorphAt_angleMap_of_isCompact`: action-angle charts near a compact regular
  component of a level.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action-angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (action-angle coordinates from a Lagrangian section).
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

variable {s : (ι → ℝ) → M} {p : ι → (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

/-! ### The Hamiltonian flows in angle coordinates -/

/-- **The Hamiltonian flows translate the angles.** Moving `Ψ(θ, c)` by the combination
`∑ᵢ wᵢ λ⁽ⁱ⁾(c)` of the vectors `λ⁽ⁱ⁾(c)` adds `2π w` to the angles. -/
theorem hamiltonianFlowAction_apply_angleMap (θ w : ι → ℝ) :
    (hσ.hamiltonianFlowAction hF hcomm hc (∑ i, w i • p i c)).toMul
        (hσ.angleMap hF hcomm hc s p (θ, c)) =
      hσ.angleMap hF hcomm hc s p (θ + (2 * π) • w, c) := by
  have hsum : ∑ i, w i • p i c + ∑ i, ((2 * π)⁻¹ * θ i) • p i c =
      ∑ i, ((2 * π)⁻¹ * (θ + (2 * π) • w) i) • p i c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← add_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul, add_comm]
  rw [angleMap_apply, angleMap_apply, ← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, hsum]

/-- **The Hamiltonian flows in action-angle coordinates.** Let `A` be action variables at `c`,
`dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`. If `∑ᵢ uᵢ dAᵢ = v ⬝ᵥ dc` at `c`, then moving `Ψ(θ, c)` by `v`
adds `u` to the angles.

For a Hamiltonian `H = h ∘ F`, whose Hamiltonian vector field is `∑ⱼ (∂ⱼ h) X_{Fⱼ}`, the vector `v`
is the gradient of `h` at `c`. Writing `h = K ∘ A`, the condition says that `uᵢ = ∂K / ∂Iᵢ`, so
this is the integrated form of `X_H = ∑ᵢ (∂K / ∂Iᵢ) ∂_{θᵢ}`. -/
theorem hamiltonianFlowAction_apply_angleMap_of_fderiv {A : (ι → ℝ) → ι → ℝ}
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    {u v : ι → ℝ} (huv : ∀ w, ∑ i, u i * fderiv ℝ (fun c ↦ A c i) c w = v ⬝ᵥ w) (θ : ι → ℝ) :
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (hσ.angleMap hF hcomm hc s p (θ, c)) =
      hσ.angleMap hF hcomm hc s p (θ + u, c) := by
  classical
  -- The condition on `u` says that `v = ∑ᵢ (uᵢ / 2π) λ⁽ⁱ⁾(c)`.
  have hd (i : ι) (w : ι → ℝ) : fderiv ℝ (fun c ↦ A c i) c w = (2 * π)⁻¹ * (p i c ⬝ᵥ w) := by
    rw [(hA i).fderiv]
    simp [dotProduct, Finset.mul_sum, mul_comm]
  have hv : ∑ i, ((2 * π)⁻¹ * u i) • p i c = v := by
    refine funext fun k ↦ ?_
    have h := huv (Pi.single k 1)
    simp only [hd, dotProduct_single, mul_one] at h
    rw [Finset.sum_apply, ← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hθ : θ + u = θ + (2 * π) • fun i ↦ (2 * π)⁻¹ * u i := by
    refine funext fun i ↦ ?_
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  rw [hθ, ← hσ.hamiltonianFlowAction_apply_angleMap hF hcomm hc, hv]

/-! ### The angle map is a local diffeomorphism -/

/-- **The differential of the angle map is injective.** Let `s` be a section of `F` near `c`,
differentiable and isotropic at `c`, and let the `λ⁽ⁱ⁾`, differentiable at `c`, be periods along
it near `c`. If the vectors `λ⁽ⁱ⁾(c)` are linearly independent, then the differential of the angle
map at `(θ, c)` is injective: it pulls `σ` back to the nondegenerate form `∑ᵢ dθᵢ ∧ dAᵢ`. -/
theorem injective_mfderiv_angleMap (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c)
    (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hL : ∀ b b', SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hp : ∀ i, DifferentiableAt ℝ (p i) c)
    (hps : ∀ i, ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hli : LinearIndependent ℝ fun i ↦ p i c) (θ : ι → ℝ) :
    Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c)) := by
  classical
  -- Linear action variables at `c`, `Aᵢ(c') = (2π)⁻¹ ⟨λ⁽ⁱ⁾(c), c'⟩`.
  set α : ι → (ι → ℝ) →L[ℝ] ℝ := fun i ↦ (2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)
  have hdA (i : ι) (w : ι → ℝ) : fderiv ℝ (fun c' ↦ α i c') c w = (2 * π)⁻¹ * (p i c ⬝ᵥ w) := by
    rw [(α i).hasFDerivAt.fderiv]
    simp [α, dotProduct, Finset.mul_sum, mul_comm]
  have hω := hσ.eval₂_mfderiv_angleMap_of_eval₂_eq_zero hF hcomm hc (A := fun c' i ↦ α i c') hs
    hFs hL hp hps (fun i ↦ (α i).hasFDerivAt) θ
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hab
  -- Pairing `(a, b)` with every `(a', b')` gives `∑ᵢ aᵢ ⟨λ⁽ⁱ⁾(c), b'⟩ = ∑ᵢ a'ᵢ ⟨λ⁽ⁱ⁾(c), b⟩`.
  have h0 (a' b' : ι → ℝ) :
      ∑ i, (a i * ((2 * π)⁻¹ * (p i c ⬝ᵥ b')) - a' i * ((2 * π)⁻¹ * (p i c ⬝ᵥ b))) = 0 := by
    have h := hω a a' b b'
    simp only [hdA] at h
    rw [← h, hab]
    simpa using SmoothBundleForm.eval₂_smul_left σ _ (0 : ℝ) 0
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a', b'))
  have h2π : (2 * π)⁻¹ ≠ 0 := by positivity
  -- With `a' = 0`, the vector `∑ᵢ aᵢ λ⁽ⁱ⁾(c)` is orthogonal to everything, so `a = 0`.
  have ha : a = 0 := by
    have hu (b' : ι → ℝ) : (∑ i, a i • p i c) ⬝ᵥ b' = 0 := by
      have h := h0 0 b'
      simp only [Pi.zero_apply, zero_mul, sub_zero] at h
      rw [sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul]
      refine (mul_eq_zero.1 ?_).resolve_left h2π
      rw [Finset.mul_sum, ← h]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    exact funext (Fintype.linearIndependent_iff.1 hli a (dotProduct_self_eq_zero.1 (hu _)))
  -- With `b' = 0`, `b` is orthogonal to every `λ⁽ⁱ⁾(c)`, so `b = 0` since these form a basis.
  have hb : b = 0 := by
    have hk (k : ι) : p k c ⬝ᵥ b = 0 := by
      have h := h0 (Pi.single k 1) 0
      simp only [dotProduct_zero, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero,
        Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] at h
      exact (mul_eq_zero.1 h).resolve_left h2π
    have hM := Matrix.mulVec_injective_iff_isUnit.2
      (Matrix.linearIndependent_row_iff_isUnit.1 hli)
    exact hM (funext fun k ↦ by simpa [Matrix.mulVec] using hk k)
  rw [ha, hb]
  rfl

/-- **The angle map is a local diffeomorphism.** On a manifold of dimension `2 · |ι|`, let `s` be a
smooth section of `F` over an open set `t`, isotropic at `c ∈ t`, and let the `λ⁽ⁱ⁾`, smooth on
`t`, be periods along `s` near `c` that are linearly independent at `c`. Then the angle map is a
smooth local diffeomorphism at `(θ, c)` for every `θ`. -/
theorem isLocalDiffeomorphAt_angleMap (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {t : Set (ι → ℝ)} (ht : IsOpen t) (hct : c ∈ t) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t)
    (hFs : ∀ c ∈ t, F (s c) = c)
    (hL : ∀ b b', SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hp : ∀ i, ContDiffOn ℝ ∞ (p i) t)
    (hps : ∀ i, ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hli : LinearIndependent ℝ fun i ↦ p i c) (θ : ι → ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ (hσ.angleMap hF hcomm hc s p) (θ, c) := by
  have htc := ht.mem_nhds hct
  let L : (ι → ℝ) × (ι → ℝ) →L[ℝ] E :=
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c)
  have hinj : Injective L := hσ.injective_mfderiv_angleMap hF hcomm hc
    ((hs.contMDiffAt htc).mdifferentiableAt (by simp)) (eventually_of_mem htc hFs) hL
    (fun i ↦ ((hp i).contDiffAt htc).differentiableAt (by simp)) hps hli θ
  have hfin : finrank ℝ ((ι → ℝ) × (ι → ℝ)) = finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, ← hdim, two_mul]
  exact isLocalDiffeomorphAt_of_mfderiv_eq (hσ.contMDiffOn_angleMap hF hcomm hc hs hp)
    (isOpen_univ.prod ht) ⟨mem_univ _, hct⟩ BoundarylessManifold.isInteriorPoint (by simp)
    (e := (LinearMap.linearEquivOfInjective L.toLinearMap hinj hfin).toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun w ↦ LinearMap.linearEquivOfInjective_apply hinj hfin w)

/-- **The angle map is injective modulo `2πℤ^ι`.** Let `s c` and `s c'` lie in the levels `c` and
`c'` of `F`, and let the `λ⁽ⁱ⁾(c)` be linearly independent and generate the period lattice of
`s c`. Then `Ψ(θ, c) = Ψ(θ', c')` exactly when `c' = c` and `θ' - θ ∈ 2πℤ^ι`. -/
theorem angleMap_eq_angleMap_iff_of_section {c' : ι → ℝ} (hFc : F (s c) = c)
    (hFc' : F (s c') = c') (hli : LinearIndependent ℝ fun i ↦ p i c)
    (hcl : hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
      AddSubgroup.closure (range fun i ↦ p i c)) {θ θ' : ι → ℝ} :
    hσ.angleMap hF hcomm hc s p (θ, c) = hσ.angleMap hF hcomm hc s p (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  constructor
  · intro h
    obtain rfl : c' = c := by
      have hF' := congrArg F h
      rwa [hσ.apply_angleMap hF hcomm hc, hσ.apply_angleMap hF hcomm hc, hFc, hFc', eq_comm]
        at hF'
    exact ⟨rfl, (hσ.angleMap_eq_angleMap_iff hF hcomm hc hli hcl).1 h⟩
  · rintro ⟨rfl, h⟩
    exact (hσ.angleMap_eq_angleMap_iff hF hcomm hc hli hcl).2 h

/-! ### Action-angle charts near a compact regular component -/

/-- **Action-angle charts near a Liouville torus.** On a manifold of dimension `2 · |ι|`, let the
connected component of `x` in its level `F⁻¹(F x)` be compact and consist of regular points of
`F`, and let `s` be a smooth isotropic section of `F` through `x`, defined on an open set `t`.
Then there are periods `λ⁽ⁱ⁾`, action variables `A`, a local diffeomorphism at `F x`, and an open
neighbourhood `U ⊆ t` of `F x` such that for all `c, c' ∈ U`:

* the differential of `Aᵢ` at `c` is `(2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ(c) dcⱼ`;
* the angle map `Ψ` is a local diffeomorphism at `(θ, c)` for every `θ`;
* it pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ` at `(θ, c)`;
* `Ψ(θ, c) = Ψ(θ', c')` exactly when `c' = c` and `θ' - θ ∈ 2πℤ^ι`.

So `Ψ` is a local diffeomorphism on `ℝ^ι × U` that identifies points exactly when their angles
differ by `2πℤ^ι`, and `σ = ∑ᵢ dθᵢ ∧ dIᵢ` in the angles `θ` and the actions `I = A`. -/
theorem exists_isLocalDiffeomorphAt_angleMap_of_isCompact
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M} {t : Set (ι → ℝ)}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (ht : IsOpen t) (hxt : F x ∈ t)
    (hsx : s (F x) = x) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c)
    (hL : ∀ c ∈ t, ∀ b b', SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0) :
    ∃ (p : ι → (ι → ℝ) → ι → ℝ) (A : (ι → ℝ) → ι → ℝ) (U : Set (ι → ℝ)),
      IsOpen U ∧ F x ∈ U ∧ U ⊆ t ∧ IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A (F x) ∧
      ∀ c ∈ U,
        (∀ i, HasFDerivAt (fun c ↦ A c i)
          ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c) ∧
        (∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞
          (hσ.angleMap hF hcomm hc s p) (θ, c)) ∧
        (∀ θ a a' b b', SmoothBundleForm.eval₂ σ (hσ.angleMap hF hcomm hc s p (θ, c))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a, b))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a', b')) =
          ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b)) ∧
        ∀ c' ∈ U, ∀ θ θ', hσ.angleMap hF hcomm hc s p (θ, c) =
            hσ.angleMap hF hcomm hc s p (θ', c') ↔
          c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  obtain ⟨p, A, hA, hp⟩ := hσ.exists_isLocalDiffeomorphAt_action_of_isCompact hF hcomm hc hdim
    hreg hK ht hxt hsx hs hFs
  obtain ⟨U, hUp, hU, hxU⟩ := eventually_nhds_iff.1 (hp.and (ht.mem_nhds hxt))
  have hUt : U ⊆ t := fun c hcU ↦ (hUp c hcU).2
  -- Every `λ⁽ⁱ⁾(c)` with `c ∈ U` is a period of `s c`.
  have hps (i : ι) {c : ι → ℝ} (hcU : c ∈ U) :
      ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c') :=
    eventually_of_mem (hU.mem_nhds hcU) fun c' hc' ↦
      (hUp c' hc').1.2.2.1 ▸ AddSubgroup.subset_closure (mem_range_self i)
  refine ⟨p, A, U, hU, hxU, hUt, hA, fun c hcU ↦ ⟨(hUp c hcU).1.2.2.2.1, fun θ ↦ ?_, fun θ ↦ ?_,
    fun c' hc' θ θ' ↦ ?_⟩⟩
  · exact hσ.isLocalDiffeomorphAt_angleMap hF hcomm hc hdim hU hcU (hs.mono hUt)
      (fun c hc' ↦ hFs c (hUt hc')) (hL c (hUt hcU))
      (fun i c' hc' ↦ ((hUp c' hc').1.1 i).contDiffWithinAt) (fun i ↦ hps i hcU)
      (hUp c hcU).1.2.1 θ
  · have htc := ht.mem_nhds (hUt hcU)
    exact hσ.eval₂_mfderiv_angleMap_of_eval₂_eq_zero hF hcomm hc
      ((hs.contMDiffAt htc).mdifferentiableAt (by simp)) (eventually_of_mem htc hFs)
      (hL c (hUt hcU)) (fun i ↦ ((hUp c hcU).1.1 i).differentiableAt (by simp))
      (fun i ↦ hps i hcU) (hUp c hcU).1.2.2.2.1 θ
  · exact hσ.angleMap_eq_angleMap_iff_of_section hF hcomm hc (hFs c (hUt hcU))
      (hFs c' (hUt hc')) (hUp c hcU).1.2.1 (hUp c hcU).1.2.2.1

end IsSymplectic

end SmoothTwoForm

end TauCeti
