/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Angle
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.IsotropicSection
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Neighborhood

/-!
# Local action-angle coordinates near a regular Liouville torus

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions with complete
Hamiltonian vector fields, generating the Hamiltonian flow action `v • y` of `ι → ℝ` on `M`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`). For a section `s` of `F` and periods
`λ⁽ⁱ⁾(c)` of `s c`, the angle map (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`) is

`Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`.

This file proves that `Ψ` is a local diffeomorphism, injective modulo `2πℤ^ι` across nearby
levels, in which the Liouville–Arnold normal form holds.

If the section `s` is isotropic, `s^* σ = 0`, then `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap_of_eval₂_eq_zero`). When the periods
`λ⁽ⁱ⁾(c)` are linearly independent this form is nondegenerate, so the differential of `Ψ` is
injective (`TauCeti.SmoothTwoForm.IsSymplectic.injective_mfderiv_angleMap`), hence invertible since
both sides have dimension `2 |ι|`, and `Ψ` is a local diffeomorphism at every `(θ, c)`
(`TauCeti.SmoothTwoForm.IsSymplectic.isLocalDiffeomorphAt_angleMap`). Since `F (Ψ(θ, c)) = c`, two
points `(θ, c)` and `(θ', c')` have the same image exactly when `c = c'` and `θ' - θ ∈ 2πℤ^ι`, as
soon as the `λ⁽ⁱ⁾(c)` form a basis of the period lattice of `s c`
(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_eq_angleMap_iff_of_section`). The Hamiltonian flows
translate the angles, which in action variables `I = A` is the statement
`X_H = ∑ᵢ (∂K / ∂Iᵢ) ∂_{θᵢ}` for `H = K(I)`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction_apply_angleMap_of_fderiv`).

Near a compact connected component of a level consisting of regular points, with an isotropic
section through it, all these hypotheses hold on a neighbourhood `U` of the level value
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_angleMap_of_isCompact`). Then
`Ψ` is a local diffeomorphism on `ℝ^ι × U` whose fibres are exactly the orbits of `2πℤ^ι` acting on
the angles, and it pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ` for action variables `A` that are a local
diffeomorphism at the level value. These are the properties saying that `(θ mod 2π, A)` are
action-angle coordinates near the torus, in which `σ = ∑ᵢ dθᵢ ∧ dIᵢ` with `I = A`; the map induced
on the torus `(ℝ / 2πℤ)^ι` itself is not constructed in this file. At the level value the angles
sweep out the whole component, since a basis of periods spans `ι → ℝ`
(`TauCeti.SmoothTwoForm.IsSymplectic.range_angleMap`).

No completeness of the Hamiltonian vector fields is needed for these coordinates. They are complete
on an open neighbourhood `W` of a compact component of a level
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_opens_isCompleteVectorField_hamiltonianVectorField`),
so the angle map built on `W`, followed by the inclusion `W → M`, gives action-angle coordinates
near the component for any smooth family of Poisson-commuting functions
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`).

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `injective_mfderiv_angleMap`, `isLocalDiffeomorphAt_angleMap`: for an isotropic section and
  independent periods, the angle map is a local diffeomorphism.
* `exists_isLocalDiffeomorphAt_angleMap_of_isCompact`: local action-angle coordinates near a
  compact regular component of a level, given by the angle map of complete commuting flows.
* `exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`: local action-angle coordinates
  near a compact regular component of a level, with no completeness hypothesis.

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
  have hdA (i : ι) (w : ι → ℝ) : fderiv ℝ (fun c' ↦ α i c') c w = (2 * π)⁻¹ * (p i c ⬝ᵥ w) :=
    fderiv_apply_eq_of_hasFDerivAt_action (α i).hasFDerivAt w
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
    -- `σ` is linear in its first argument, so it vanishes on the zero vector `0 = 0 • 0`.
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
  have hinj := hσ.injective_mfderiv_angleMap hF hcomm hc
    ((hs.contMDiffAt htc).mdifferentiableAt (by simp)) (eventually_of_mem htc hFs) hL
    (fun i ↦ ((hp i).contDiffAt htc).differentiableAt (by simp)) hps hli θ
  have hfin : finrank ℝ ((ι → ℝ) × (ι → ℝ)) = finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, ← hdim, two_mul]
  exact isLocalDiffeomorphAt_of_injective_mfderiv (hσ.contMDiffOn_angleMap hF hcomm hc hs hp)
    (isOpen_univ.prod ht) ⟨mem_univ _, hct⟩ BoundarylessManifold.isInteriorPoint (by simp) hinj
    hfin

/-! ### Local action-angle coordinates near a compact regular component -/

/-- **Local action-angle coordinates near a Liouville torus.** On a manifold of dimension
`2 · |ι|`, let the connected component of `x` in its level `F⁻¹(F x)` be compact and consist of
regular points of `F`, and let `s` be a smooth isotropic section of `F` through `x`, defined on an
open set `t`.
Then there are periods `λ⁽ⁱ⁾`, action variables `A`, a local diffeomorphism at `F x`, and an open
neighbourhood `U ⊆ t` of `F x` such that the angles `θ ↦ Ψ(θ, F x)` sweep out the component of `x`,
and for all `c, c' ∈ U`:

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
      range (fun θ ↦ hσ.angleMap hF hcomm hc s p (θ, F x)) =
        connectedComponentIn (F ⁻¹' {F x}) x ∧
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
    eventually_of_mem (hU.mem_nhds hcU) fun c' hc' ↦ by
      obtain ⟨⟨-, -, hcl, -⟩, -⟩ := hUp c' hc'
      exact hcl ▸ AddSubgroup.subset_closure (mem_range_self i)
  refine ⟨p, A, U, hU, hxU, hUt, hA, ?_, fun c hcU ↦ ?_⟩
  · obtain ⟨⟨-, hli, -⟩, -⟩ := hUp (F x) hxU
    rw [hσ.range_angleMap hF hcomm hc hli, hsx]
    exact hσ.range_hamiltonianFlowAction_apply hF hcomm hc hdim hreg
  obtain ⟨⟨hpd, hli, hcl, hAd, -⟩, hct⟩ := hUp c hcU
  have htc := ht.mem_nhds hct
  refine ⟨hAd, fun θ ↦ ?_, fun θ ↦ ?_, fun c' hc' θ θ' ↦ ?_⟩
  · exact hσ.isLocalDiffeomorphAt_angleMap hF hcomm hc hdim hU hcU (hs.mono hUt)
      (fun c hc' ↦ hFs c (hUt hc')) (hL c hct)
      (fun i c' hc' ↦ by
        obtain ⟨⟨hpd', -⟩, -⟩ := hUp c' hc'
        exact (hpd' i).contDiffWithinAt) (fun i ↦ hps i hcU) hli θ
  · exact hσ.eval₂_mfderiv_angleMap_of_eval₂_eq_zero hF hcomm hc
      ((hs.contMDiffAt htc).mdifferentiableAt (by simp)) (eventually_of_mem htc hFs)
      (hL c hct) (fun i ↦ (hpd i).differentiableAt (by simp)) (fun i ↦ hps i hcU) hAd θ
  · exact hσ.angleMap_eq_angleMap_iff_of_section hF hcomm hc (hFs c hct) (hFs c' (hUt hc')) hli
      hcl

end IsSymplectic

/-! ### Action-angle coordinates without completeness -/

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ}

/-- **Local action-angle coordinates near a compact regular component of a level.** On a
symplectic manifold of dimension `2 · |ι|`, let `F` be a smooth family of pairwise
Poisson-commuting functions, and let the connected component `L` of `x` in its level `F⁻¹(F x)` be
compact and consist of regular points of `F`. The Hamiltonian vector fields of the `F_i` need not
be complete. Then there are a map `Ψ : ℝ^ι × ℝ^ι → M`, action variables `A`, a local
diffeomorphism at `F x`, and an open neighbourhood `U` of `F x` such that the angles
`θ ↦ Ψ(θ, F x)` sweep out `L`, and for all `c, c' ∈ U` and all angles `θ`:

* `F (Ψ(θ, c)) = c`;
* `Ψ` is a local diffeomorphism at `(θ, c)`;
* `Ψ` pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ` at `(θ, c)`;
* `Ψ(θ, c) = Ψ(θ', c')` exactly when `c' = c` and `θ' - θ ∈ 2πℤ^ι`.

So `(θ mod 2π, A)` are action-angle coordinates on a neighbourhood of `L`, in which
`σ = ∑ᵢ dθᵢ ∧ dIᵢ` with `I = A`. -/
theorem exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ (Ψ : (ι → ℝ) × (ι → ℝ) → M) (A : (ι → ℝ) → ι → ℝ) (U : Set (ι → ℝ)),
      IsOpen U ∧ F x ∈ U ∧ IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A (F x) ∧
      range (fun θ ↦ Ψ (θ, F x)) = connectedComponentIn (F ⁻¹' {F x}) x ∧
      ∀ c ∈ U,
        (∀ θ, F (Ψ (θ, c)) = c) ∧
        (∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, c)) ∧
        (∀ θ a a' b b', SmoothBundleForm.eval₂ σ (Ψ (θ, c))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a, b))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a', b')) =
          ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b)) ∧
        ∀ c' ∈ U, ∀ θ θ', Ψ (θ, c) = Ψ (θ', c') ↔
          c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  -- The Hamiltonian flows are complete on an open neighbourhood `W` of the component, which is
  -- also the component of `x` in its level in `W`; the chart is built on `W`.
  obtain ⟨W, hxW, himage, hKW, hregW, hcommW, hcW⟩ :=
    hσ.isNondegenerate.exists_opens_isCompact_connectedComponentIn_isCompleteVectorField
      (hF.of_le (by simp)) hcomm hreg hK
  set y : W := ⟨x, hxW⟩
  set σW : SmoothTwoForm I W := SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtype_val σ
  have hσW : σW.IsSymplectic := hσ.mpullback_subtype_val W
  have hFW : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ fun z : W ↦ F z := hF.comp contMDiff_subtype_val
  obtain ⟨t, ht, hyt, s, hsy, hs, hFs, hL⟩ :=
    hσW.exists_contMDiffOn_section_eval₂_mfderiv_eq_zero hFW hcommW hcW
      (hregW y (mem_connectedComponentIn rfl))
  obtain ⟨p, A, U, hU, hyU, hUt, hA, hrange, hUc⟩ :=
    hσW.exists_isLocalDiffeomorphAt_angleMap_of_isCompact hFW hcommW hcW hdim hregW hKW ht hyt
      hsy hs hFs hL
  -- Transport the chart on `W` along the inclusion `W → M`.
  refine ⟨Subtype.val ∘ hσW.angleMap hFW hcommW hcW s p, A, U, hU, hyU, hA, ?_,
    fun c hcU ↦ ?_⟩
  · rw [← himage]
    exact (range_comp Subtype.val _).trans (congrArg _ hrange)
  obtain ⟨-, hloc, hpull, hinj⟩ := hUc c hcU
  refine ⟨fun θ ↦ ?_, fun θ ↦ (hloc θ).comp (hg := isLocalDiffeomorph_subtype_val _),
    fun θ a a' b b' ↦ ?_, fun c' hc' θ θ' ↦ ?_⟩
  · exact (hσW.apply_angleMap hFW hcommW hcW (θ, c)).trans (hFs c (hUt hcU))
  · -- the inclusion pulls `σ` back to `σW`, and the chain rule splits the differential
    rw [mfderiv_comp (θ, c) (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
      ((hloc θ).mdifferentiableAt (by simp))]
    exact (SmoothForm.eval₂_mpullback _ contMDiff_subtype_val σ _ _ _).symm.trans
      (hpull θ a a' b b')
  · rw [Function.comp_apply, Function.comp_apply, Subtype.val_injective.eq_iff]
    exact hinj c' hc' θ θ'

end IsSymplectic

end SmoothTwoForm

end TauCeti
