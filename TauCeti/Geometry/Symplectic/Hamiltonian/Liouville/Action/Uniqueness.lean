/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Angle
public import TauCeti.Analysis.Calculus.FDeriv.Matrix
public import TauCeti.LinearAlgebra.Matrix.TransposeLattice

/-!
# Uniqueness of action variables up to integral affine changes

Let `Λ c ⊆ ℝ^ι` be a family of lattices depending on `c` in an open set `D ⊆ ℝ^ι`. A map
`A : ℝ^ι → ℝ^ι` is a system of **action variables** for it on `D` when `Λ c = 2π (DA_c)ᵀ ℤ^ι` for
every `c ∈ D`, the transpose lattice of `2π DA_c` (`ContinuousLinearMap.transposeLattice`): a
vector `v` lies in `Λ c` exactly when the one-form `v ⬝ᵥ dc` is `2π ∑ᵢ nᵢ dAᵢ` for some integers
`nᵢ`. The action variables of a Liouville integrable system near a compact
regular level component have this property for the period lattices along a section
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`).

This file proves that action variables are unique up to integral affine changes. If `A` and `A'`
are `C¹` action variables for the same lattices on an open preconnected set `D`, and the derivative
of `A` is injective, then

`A' = M A + b` on `D`, for some `M ∈ GL(ι, ℤ)` and `b : ι → ℝ`

(`TauCeti.exists_eq_mulVec_add_of_forall_eq_transposeLattice`). At each point the rows of `DA`
and `DA'` are two bases of the same lattice, so `DA' = M_c DA` with `M_c ∈ GL(ι, ℤ)`
(`ContinuousLinearMap.exists_generalLinearGroup_mulVec_eq_of_transposeLattice_eq`). The matrix
`M_c = DA'(c) DA(c)⁻¹` depends continuously on `c` and has integer entries, so it is constant on
the preconnected set `D`, and then `A' - M A` has zero derivative
(`TauCeti.exists_eq_mulVec_add_of_forall_exists_fderiv_eq`). Conversely, every integral affine
change of action variables is again a system of action variables
(`TauCeti.forall_eq_transposeLattice_of_eq_mulVec_add`).

For a Liouville integrable system, let `λ⁽ⁱ⁾` and `λ'⁽ⁱ⁾` be two families of periods along one
section `s`, with action variables `A` and `A'` describing the period lattices, and with angle maps
`Ψ` and `Ψ'` (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`). Then a single `P ∈ GL(ι, ℤ)` relates
all three: `A' = P A + b`, `λ'⁽ⁱ⁾ = ∑ₖ Pᵢₖ λ⁽ᵏ⁾` and `Ψ'(θ, c) = Ψ(θ P, c)`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_eq_mulVec_add_and_angleMap_eq`). In action-angle
coordinates `(θ, I)` this is the change `(θ, I) ↦ (P⁻ᵀ θ, P I + b)`, which is the integral affine
change `TauCeti.CotangentBundle.integralAffineDiffeomorph` of the model `T*Tⁿ` with matrix `P⁻ᵀ`;
that change preserves the symplectic form `∑ᵢ dθᵢ ∧ dIᵢ`.

Global action coordinates need more than exact period forms. On the strip
`B = (1, 2) × (0, 3π)`, the lattices `2π (Da)ᵀ ℤ²` of the polar map `a(r, φ) = (r cos φ, r sin φ)`
admit no injective action variables (`TauCeti.not_injOn_of_forall_transposeLattice_eq_polar`):
every choice is `M a + b`, and `a(r, φ) = a(r, φ + 2π)`.

## Main results

* `TauCeti.exists_eq_mulVec_add_of_forall_eq_transposeLattice`: action variables are unique up to
  integral affine changes.
* `TauCeti.forall_eq_transposeLattice_of_eq_mulVec_add`: integral affine changes of action
  variables are action variables.
* `TauCeti.SmoothTwoForm.IsSymplectic.angleMap_sum_smul`: changing the basis of periods by a matrix
  `P` changes the angles by `θ ↦ θ P`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_eq_mulVec_add_and_angleMap_eq`: along a fixed section,
  action-angle data of a Liouville integrable system are unique up to integral affine changes.
* `TauCeti.not_injOn_of_forall_transposeLattice_eq_polar`: the polar lattices on
  `(1, 2) × (0, 3π)` have no injective action variables.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Sections 1–2 (the integral affine structure of the action variables, and the
  obstructions to global action-angle coordinates).
-/

public section

open Set Filter Module Topology Function Real Matrix
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Set (ι → ℝ)} {A A' : (ι → ℝ) → ι → ℝ}

/-! ### Action variables of a family of lattices -/

variable {Λ : (ι → ℝ) → AddSubgroup (ι → ℝ)}

/-- **Action variables are unique up to integral affine changes.** Let `Λ c` be a family of
lattices over an open preconnected set `D`, and let `A` and `A'` be two `C¹` maps on `D` that are
action variables for it: for every `c ∈ D`, `Λ c = 2π (DA_c)ᵀ ℤ^ι`, that is, a vector `v` lies in
`Λ c` exactly when the one-form `v ⬝ᵥ dc` is `2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`, and likewise
for `A'`. If the derivative of `A` is injective on `D`, then `A' = M A + b` on `D` for some
`M ∈ GL(ι, ℤ)` and `b : ι → ℝ`. -/
theorem exists_eq_mulVec_add_of_forall_eq_transposeLattice (hDo : IsOpen D)
    (hD : IsPreconnected D) (hA : ContDiffOn ℝ 1 A D) (hA' : ContDiffOn ℝ 1 A' D)
    (hinj : ∀ c ∈ D, Injective (fderiv ℝ A c))
    (hΛ : ∀ c ∈ D, Λ c = ((2 * π) • fderiv ℝ A c).transposeLattice)
    (hΛ' : ∀ c ∈ D, Λ c = ((2 * π) • fderiv ℝ A' c).transposeLattice) :
    ∃ (M : GL ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = (M : Matrix ι ι ℤ).map (↑) *ᵥ A c + b := by
  have hdA {c} (hc : c ∈ D) : DifferentiableAt ℝ A c :=
    (hA.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  -- At each point the two derivatives, scaled by `2π`, are bases of the same lattice.
  have hpt {c} (hc : c ∈ D) : ∃ M : GL ι ℤ, ∀ w,
      fderiv ℝ A' c w = (M : Matrix ι ι ℤ).map (↑) *ᵥ fderiv ℝ A c w := by
    obtain ⟨M, hM⟩ := ContinuousLinearMap.exists_generalLinearGroup_mulVec_eq_of_transposeLattice_eq
      ((smul_right_injective _ h2π).comp (hinj c hc)) ((hΛ c hc).symm.trans (hΛ' c hc))
    exact ⟨M, fun w ↦ smul_right_injective _ h2π (by simpa [mulVec_smul] using hM w)⟩
  rcases D.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · exact ⟨1, 0, by simp⟩
  obtain ⟨M, b, hMb⟩ := exists_eq_mulVec_add_of_forall_exists_fderiv_eq hDo hD hA hA' hinj
    fun c hc ↦ (hpt hc).elim fun M hM ↦ ⟨M, hM⟩
  -- The constant matrix `M` is the invertible matrix relating the derivatives at `c₀`.
  obtain ⟨M₀, hM₀⟩ := hpt hc₀
  have hd := (hdA hc₀).hasFDerivAt.of_eventuallyEq_mulVec_add
    (eventually_of_mem (hDo.mem_nhds hc₀) hMb)
  have hsurj : Surjective (fderiv ℝ A c₀) :=
    LinearMap.injective_iff_surjective (f := (fderiv ℝ A c₀ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).1
      (hinj c₀ hc₀)
  have hMM₀ : M = M₀ := by
    refine Matrix.map_injective (Int.cast_injective (α := ℝ))
      (Matrix.toLin'.injective (LinearMap.ext fun u ↦ ?_))
    obtain ⟨w, rfl⟩ := hsurj u
    simp [← hM₀, hd.fderiv]
  exact ⟨M₀, b, hMM₀ ▸ hMb⟩

/-- **Integral affine changes of action variables are action variables.** If `A` are action
variables for a family of lattices `Λ c` over an open set `D`, that is, `Λ c = 2π (DA_c)ᵀ ℤ^ι` for
every `c ∈ D`, then so are `A' = M A + b` for every `M ∈ GL(ι, ℤ)` and `b : ι → ℝ`. -/
theorem forall_eq_transposeLattice_of_eq_mulVec_add (hDo : IsOpen D)
    (hA : DifferentiableOn ℝ A D)
    (hΛ : ∀ c ∈ D, Λ c = ((2 * π) • fderiv ℝ A c).transposeLattice)
    (M : GL ι ℤ) (b : ι → ℝ) (hA' : ∀ c ∈ D, A' c = (M : Matrix ι ι ℤ).map (↑) *ᵥ A c + b) :
    ∀ c ∈ D, Λ c = ((2 * π) • fderiv ℝ A' c).transposeLattice := by
  intro c hc
  have hdA := (hA c hc).differentiableAt (hDo.mem_nhds hc)
  -- Near `c`, `A' = M A + b`, so `DA' = M DA`.
  have hA'c := hdA.hasFDerivAt.of_eventuallyEq_mulVec_add (eventually_of_mem (hDo.mem_nhds hc) hA')
  rw [hΛ c hc, hA'c.fderiv, ← ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.transposeLattice_toLin'_comp]

/-! ### Polar coordinates: action variables need not be injective -/

/-- The polar map `a(r, φ) = (r cos φ, r sin φ)` is smooth. -/
private theorem contDiff_polar :
    ContDiff ℝ 1 fun c : Fin 2 → ℝ ↦ ![c 0 * cos (c 1), c 0 * sin (c 1)] := by
  refine contDiff_pi.2 fun i ↦ ?_
  fin_cases i
  · simpa using (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) 0).mul
      (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) 1).cos
  · simpa using (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) 0).mul
      (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) 1).sin

/-- The polar map `a(r, φ) = (r cos φ, r sin φ)` has injective derivative wherever `r ≠ 0`. -/
private theorem injective_fderiv_polar {c : Fin 2 → ℝ} (hc : c 0 ≠ 0) :
    Injective (fderiv ℝ (fun c : Fin 2 → ℝ ↦ ![c 0 * cos (c 1), c 0 * sin (c 1)]) c) := by
  have hd := (contDiff_polar.differentiable one_ne_zero) c
  have h0 : HasFDerivAt (fun c : Fin 2 → ℝ ↦ c 0 * cos (c 1))
      (c 0 • (-sin (c 1) • proj (1 : Fin 2)) + cos (c 1) • proj (0 : Fin 2)) c :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) c).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) c).cos
  have h1 : HasFDerivAt (fun c : Fin 2 → ℝ ↦ c 0 * sin (c 1))
      (c 0 • (cos (c 1) • proj (1 : Fin 2)) + sin (c 1) • proj (0 : Fin 2)) c :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) c).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) c).sin
  rw [injective_iff_map_eq_zero]
  intro w hw
  have e0 := congrArg (· w) (fderiv_apply hd 0)
  have e1 := congrArg (· w) (fderiv_apply hd 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h0.fderiv,
    h1.fderiv, ContinuousLinearMap.comp_apply, hw, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.zero_apply]
    at e0 e1
  have hw0 : w 0 = 0 := by
    linear_combination cos (c 1) * e0 + sin (c 1) * e1 - w 0 * sin_sq_add_cos_sq (c 1)
  have hw1 : c 0 * w 1 = 0 := by
    linear_combination -sin (c 1) * e0 + cos (c 1) * e1 - c 0 * w 1 * sin_sq_add_cos_sq (c 1)
  ext i
  fin_cases i
  · exact hw0
  · exact (mul_eq_zero.1 hw1).resolve_left hc

/-- **No injective action variables for the polar lattices.** On the strip
`B = (1, 2) × (0, 3π)` of the `(r, φ)`-plane, consider the lattices `2π (Da)ᵀ ℤ²` of the polar map
`a(r, φ) = (r cos φ, r sin φ)`, spanned by the exact one-forms `2π da₁` and `2π da₂`. Every `C¹`
map `A` on `B` with the same lattices, that is, every choice of action variables for them, fails to
be injective on `B`: by uniqueness of action variables `A = M a + b` for some `M ∈ GL(2, ℤ)`, and
`a` takes the same value at `(r, φ)` and `(r, φ + 2π)`. So no action variables map `B` injectively
into `ℝ²`. -/
theorem not_injOn_of_forall_transposeLattice_eq_polar {A : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hA : ContDiffOn ℝ 1 A {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)})
    (hΛ : ∀ c ∈ {c : Fin 2 → ℝ | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)},
      ((2 * π) • fderiv ℝ (fun c : Fin 2 → ℝ ↦ ![c 0 * cos (c 1), c 0 * sin (c 1)]) c
        ).transposeLattice = ((2 * π) • fderiv ℝ A c).transposeLattice) :
    ¬ InjOn A {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)} := by
  set B : Set (Fin 2 → ℝ) := {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)}
  have hBo : IsOpen B :=
    (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))
  have hBc : Convex ℝ B :=
    ((convex_Ioo 1 2).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0)).inter
      ((convex_Ioo 0 (3 * π)).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1))
  obtain ⟨M, b, hMb⟩ := exists_eq_mulVec_add_of_forall_eq_transposeLattice hBo
    hBc.isPreconnected contDiff_polar.contDiffOn hA
    (fun c hc ↦ injective_fderiv_polar (by linarith [hc.1.1])) (fun _ _ ↦ rfl) hΛ
  -- The points `(3/2, 1)` and `(3/2, 1 + 2π)` of `B` have the same polar image.
  have h1 : (![3 / 2, 1] : Fin 2 → ℝ) ∈ B := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith [two_le_pi]
  have h2 : (![3 / 2, 1 + 2 * π] : Fin 2 → ℝ) ∈ B := by
    refine ⟨by norm_num, ?_, ?_⟩ <;> simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      linarith [two_le_pi]
  intro hinj
  have heq := hinj h1 h2 (by rw [hMb _ h1, hMb _ h2]; simp [cos_add_two_pi, sin_add_two_pi])
  have h := congrFun heq 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  linarith [pi_pos]

/-! ### Action-angle data of a Liouville integrable system -/

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {s : (ι → ℝ) → M} {p p' : ι → (ι → ℝ) → ι → ℝ}

include hσ hF hcomm hc

omit [DecidableEq ι] in
/-- **Changing the basis of periods reparametrizes the angles.** If the periods are replaced by
the combinations `λ'⁽ⁱ⁾ = ∑ₖ Pᵢₖ λ⁽ᵏ⁾`, the angle map `Ψ'` of the new periods is the angle map `Ψ`
of the old ones precomposed with the linear change of angles `θ ↦ θ P`:
`Ψ'(θ, c) = Ψ(θ P, c)`. -/
theorem angleMap_sum_smul (P : Matrix ι ι ℝ) (θ c : ι → ℝ) :
    hσ.angleMap hF hcomm hc s (fun i c ↦ ∑ k, P i k • p k c) (θ, c) =
      hσ.angleMap hF hcomm hc s p (θ ᵥ* P, c) := by
  have hsum : ∑ i, ((2 * π)⁻¹ * θ i) • ∑ k, P i k • p k c =
      ∑ k, ((2 * π)⁻¹ * (θ ᵥ* P) k) • p k c := by
    simp only [Finset.smul_sum, smul_smul, vecMul, dotProduct, Finset.mul_sum, Finset.sum_smul,
      mul_assoc]
    exact Finset.sum_comm
  rw [angleMap_apply, angleMap_apply, hsum]

/-- **Along a fixed section, action-angle data are unique up to integral affine changes.** Let `s`
be a section of `F` over an open preconnected set `D`. Let `λ⁽ⁱ⁾` and `λ'⁽ⁱ⁾` be two continuous
families of vectors on `D`, the `λ⁽ⁱ⁾(c)` linearly independent, with action variables `A` and `A'`:
`dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` and `dA'ᵢ = (2π)⁻¹ ∑ⱼ λ'⁽ⁱ⁾ⱼ dcⱼ`. Suppose both describe the period
lattice: for every `c ∈ D`, the periods of `s c` form the transpose lattice `2π (DA_c)ᵀ ℤ^ι`, so
`v` is a period of `s c` exactly when `v ⬝ᵥ dc = 2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`, and likewise
for `A'`. Then there are `P ∈ GL(ι, ℤ)` and `b : ι → ℝ` such
that on `D`

* the actions change by the integral affine map `A' = P A + b`;
* the periods change by `λ'⁽ⁱ⁾ = ∑ₖ Pᵢₖ λ⁽ᵏ⁾`;
* the angle maps change by the linear change of angles `θ ↦ θ P`: `Ψ'(θ, c) = Ψ(θ P, c)`. -/
theorem exists_eq_mulVec_add_and_angleMap_eq (hDo : IsOpen D) (hD : IsPreconnected D)
    (hp : ∀ i, ContinuousOn (p i) D) (hp' : ∀ i, ContinuousOn (p' i) D)
    (hli : ∀ c ∈ D, LinearIndependent ℝ fun i ↦ p i c)
    (hA : ∀ c ∈ D, ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (hA' : ∀ c ∈ D, ∀ i, HasFDerivAt (fun c ↦ A' c i)
      ((2 * π)⁻¹ • ∑ j, p' i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (hΛ : ∀ c ∈ D, hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
      ((2 * π) • fderiv ℝ A c).transposeLattice)
    (hΛ' : ∀ c ∈ D, hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
      ((2 * π) • fderiv ℝ A' c).transposeLattice) :
    ∃ (P : GL ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = (P : Matrix ι ι ℤ).map (↑) *ᵥ A c + b ∧
      (∀ i, p' i c = ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) • p k c) ∧
      ∀ θ, hσ.angleMap hF hcomm hc s p' (θ, c) =
        hσ.angleMap hF hcomm hc s p (θ ᵥ* (P : Matrix ι ι ℤ).map (↑), c) := by
  obtain ⟨P, b, hPb⟩ := exists_eq_mulVec_add_of_forall_eq_transposeLattice hDo hD
    ((contDiffOn_action_of_hasFDerivAt (n := 0) hDo (fun i ↦ contDiffOn_zero.2 (hp i)) hA).of_le
      (by simp))
    ((contDiffOn_action_of_hasFDerivAt (n := 0) hDo (fun i ↦ contDiffOn_zero.2 (hp' i))
      hA').of_le (by simp))
    (fun c hcD ↦ injective_fderiv_action_of_hasFDerivAt (hli c hcD) (hA c hcD)) hΛ hΛ'
  refine ⟨P, b, fun c hcD ↦ ⟨hPb c hcD, ?_⟩⟩
  -- Differentiating `A'ᵢ = ∑ₖ Pᵢₖ Aₖ + bᵢ` and comparing with `dA'ᵢ` gives the periods.
  have hper (i : ι) : p' i c = ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) • p k c := by
    have hd := (hasFDerivAt_pi.2 (hA' c hcD)).unique
      ((hasFDerivAt_pi.2 (hA c hcD)).of_eventuallyEq_mulVec_add
        (eventually_of_mem (hDo.mem_nhds hcD) hPb))
    funext j
    have h : (2 * π)⁻¹ * p' i c j = (2 * π)⁻¹ * ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) * p k c j := by
      simpa [Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_left_comm] using
        congrFun (congrArg (· (Pi.single j 1)) hd) i
    simpa using mul_left_cancel₀ (by positivity) h
  refine ⟨hper, fun θ ↦ ?_⟩
  rw [← hσ.angleMap_sum_smul hF hcomm hc, angleMap_apply, angleMap_apply]
  simp only [hper, Matrix.map_apply]

end IsSymplectic

end SmoothTwoForm

end TauCeti
