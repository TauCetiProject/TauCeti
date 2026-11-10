/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Angle
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Uniqueness of action variables up to integral affine changes

Let `Λ c ⊆ ℝ^ι` be a family of lattices depending on `c` in an open set `D ⊆ ℝ^ι`. A map
`A : ℝ^ι → ℝ^ι` is a system of **action variables** for it on `D` when `Λ c = 2π (DA_c)ᵀ ℤ^ι` for
every `c ∈ D`: a vector `v` lies in `Λ c` exactly when the one-form `v ⬝ᵥ dc` is `2π ∑ᵢ nᵢ dAᵢ`
for some integers `nᵢ`. The action variables of a Liouville integrable system near a compact
regular level component have this property for the period lattices along a section
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`).

This file proves that action variables are unique up to integral affine changes. If `A` and `A'`
are `C¹` action variables for the same lattices on an open preconnected set `D`, and the derivative
of `A` is injective, then

`A' = M A + b` on `D`, for some `M ∈ GL(ι, ℤ)` and `b : ι → ℝ`

(`TauCeti.exists_eq_mulVec_add_of_forall_mem_iff`). At each point the rows of `DA` and `DA'` are
two bases of the same lattice, so `DA' = M_c DA` with `M_c ∈ GL(ι, ℤ)`
(`TauCeti.exists_generalLinearGroup_mulVec_eq_of_forall_exists_iff`). The matrix
`M_c = DA'(c) DA(c)⁻¹` depends continuously on `c` and has integer entries, so it is constant on
the preconnected set `D`, and then `A' - M A` has zero derivative
(`TauCeti.exists_eq_mulVec_add_of_forall_exists_fderiv_eq`). Conversely, every integral affine
change of action variables is again a system of action variables
(`TauCeti.forall_mem_iff_of_eq_mulVec_add`).

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
admit no injective action variables (`TauCeti.not_injOn_of_forall_exists_iff_polar`): every choice
is `M a + b`, and `a(r, φ) = a(r, φ + 2π)`.

## Main results

* `TauCeti.exists_generalLinearGroup_mulVec_eq_of_forall_exists_iff`: two linear maps defining the
  same lattice differ by an element of `GL(ι, ℤ)`.
* `TauCeti.exists_eq_mulVec_add_of_forall_mem_iff`: action variables are unique up to integral
  affine changes.
* `TauCeti.forall_mem_iff_of_eq_mulVec_add`: integral affine changes of action variables are
  action variables.
* `TauCeti.SmoothTwoForm.IsSymplectic.angleMap_sum_smul`: changing the basis of periods by a matrix
  `P` changes the angles by `θ ↦ θ P`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_eq_mulVec_add_and_angleMap_eq`: action-angle data of a
  Liouville integrable system are unique up to integral affine changes.
* `TauCeti.not_injOn_of_forall_exists_iff_polar`: the polar lattices on `(1, 2) × (0, 3π)` have no
  injective action variables.

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Changes of basis of the lattice `2π Lᵀ ℤ^ι` -/

omit [DecidableEq ι] in
/-- If every vector of the lattice `2π L₁ᵀ ℤ^ι` lies in `2π L₂ᵀ ℤ^ι`, then `L₁ = N L₂` for an
integer matrix `N`. Here the lattice `2π Lᵀ ℤ^ι` of a linear map `L` is the set of vectors `v` whose
one-form `v ⬝ᵥ ·` is `2π ∑ᵢ nᵢ Lᵢ` for integers `nᵢ`. -/
theorem exists_map_intCast_mulVec_eq_of_forall_exists_imp
    (L₁ L₂ : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (h : ∀ v : ι → ℝ, (∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * L₁ w i) →
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * L₂ w i) :
    ∃ N : Matrix ι ι ℤ, ∀ w, L₁ w = N.map (↑) *ᵥ L₂ w := by
  classical
  -- The `i`-th row of the matrix of `L₁`, scaled by `2π`, is the lattice vector with `n = eᵢ`.
  have hrow (i : ι) : ∃ n : ι → ℤ, ∀ w,
      (2 * π) • LinearMap.toMatrix' (L₁ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) i ⬝ᵥ w =
        2 * π * ∑ k, n k * L₂ w k := by
    refine h _ ⟨Pi.single i 1, fun w ↦ ?_⟩
    have hw : LinearMap.toMatrix' (L₁ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) i ⬝ᵥ w = L₁ w i :=
      congrFun (LinearMap.toMatrix'_mulVec (L₁ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) w) i
    simp [smul_dotProduct, hw, Pi.single_apply]
  choose n hn using hrow
  refine ⟨Matrix.of n, fun w ↦ funext fun i ↦ ?_⟩
  have hw : LinearMap.toMatrix' (L₁ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) i ⬝ᵥ w = L₁ w i :=
    congrFun (LinearMap.toMatrix'_mulVec (L₁ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) w) i
  have h := hn i w
  rw [smul_dotProduct, hw, smul_eq_mul] at h
  rw [mul_left_cancel₀ (by positivity) h]
  simp [mulVec, dotProduct]

/-- **Two bases of one lattice differ by an element of `GL(ι, ℤ)`.** If the injective linear map
`L` and the linear map `L'` define the same lattice `2π Lᵀ ℤ^ι = 2π L'ᵀ ℤ^ι`, that is, the
one-form `v ⬝ᵥ ·` is an integral combination of the components of `2π L` exactly when it is an
integral combination of the components of `2π L'`, then `L' = M L` for an invertible integer matrix
`M`. -/
theorem exists_generalLinearGroup_mulVec_eq_of_forall_exists_iff
    (L L' : (ι → ℝ) →L[ℝ] (ι → ℝ)) (hL : Injective L)
    (h : ∀ v : ι → ℝ, (∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * L w i) ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * L' w i) :
    ∃ M : GL ι ℤ, ∀ w, L' w = (M : Matrix ι ι ℤ).map (↑) *ᵥ L w := by
  obtain ⟨M, hM⟩ := exists_map_intCast_mulVec_eq_of_forall_exists_imp L' L fun v ↦ (h v).2
  obtain ⟨N, hN⟩ := exists_map_intCast_mulVec_eq_of_forall_exists_imp L L' fun v ↦ (h v).1
  -- `L = N M L` and `L` is onto, so `N M = 1`.
  have hsurj : Surjective L :=
    LinearMap.injective_iff_surjective (f := (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).1 hL
  have hcast : (N * M).map ((↑) : ℤ → ℝ) = (1 : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) := by
    rw [Matrix.map_one _ Int.cast_zero Int.cast_one]
    refine Matrix.toLin'.injective (LinearMap.ext fun u ↦ ?_)
    obtain ⟨w, rfl⟩ := hsurj u
    have hmap : (N * M).map ((↑) : ℤ → ℝ) = N.map (↑) * M.map (↑) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    simp only [Matrix.toLin'_apply, hmap, ← mulVec_mulVec, ← hM, ← hN, one_mulVec]
  have hNM : N * M = 1 := Matrix.map_injective Int.cast_injective hcast
  exact ⟨⟨M, N, mul_eq_one_comm.1 hNM, hNM⟩, hM⟩

/-! ### Maps whose derivatives differ by integer matrices -/

variable {D : Set (ι → ℝ)} {A A' : (ι → ℝ) → ι → ℝ}

/-- **Derivatives related by integer matrices force an integral affine relation.** Let `A` and `A'`
be `C¹` maps on an open preconnected set `D`, with the derivative of `A` injective on `D`. If at
each point `c ∈ D` the derivative of `A'` is `M_c` times that of `A` for some `M_c ∈ GL(ι, ℤ)`,
then `M_c` does not depend on `c`, and `A' = M A + b` on `D` for some constant `b`. -/
theorem exists_eq_mulVec_add_of_forall_exists_fderiv_eq (hDo : IsOpen D) (hD : IsPreconnected D)
    (hA : ContDiffOn ℝ 1 A D) (hA' : ContDiffOn ℝ 1 A' D)
    (hinj : ∀ c ∈ D, Injective (fderiv ℝ A c))
    (hpt : ∀ c ∈ D, ∃ M : GL ι ℤ, ∀ w,
      fderiv ℝ A' c w = (M : Matrix ι ι ℤ).map (↑) *ᵥ fderiv ℝ A c w) :
    ∃ (M : GL ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = (M : Matrix ι ι ℤ).map (↑) *ᵥ A c + b := by
  rcases D.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · exact ⟨1, 0, by simp⟩
  choose! M hM using hpt
  -- The matrix `M c` is the value at `c` of the map `R c = DA'(c) DA(c)⁻¹`, continuous on `D`.
  set R : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    fun c ↦ fderiv ℝ A' c * Ring.inverse (fderiv ℝ A c)
  have hsurj {c} (hc : c ∈ D) : Surjective (fderiv ℝ A c) :=
    LinearMap.injective_iff_surjective (f := (fderiv ℝ A c : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).1
      (hinj c hc)
  have hunit {c} (hc : c ∈ D) : IsUnit (fderiv ℝ A c) :=
    ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hinj c hc, hsurj hc⟩
  have hR : ContinuousOn R D := fun c hc ↦ by
    have hinv := NormedRing.inverse_continuousAt (hunit hc).unit
    rw [IsUnit.unit_spec] at hinv
    exact ((hA'.continuousOn_fderiv_of_isOpen hDo le_rfl) c hc).mul
      (hinv.comp_continuousWithinAt ((hA.continuousOn_fderiv_of_isOpen hDo le_rfl) c hc))
  have hRM {c} (hc : c ∈ D) (w : ι → ℝ) : R c w = (M c : Matrix ι ι ℤ).map (↑) *ᵥ w := by
    obtain ⟨u, rfl⟩ := hsurj hc w
    rw [← hM c hc, ← mul_apply_eq_comp, mul_assoc,
      Ring.inverse_mul_cancel _ (hunit hc), mul_one]
  -- The entries of `M c` are continuous and integral, hence constant on `D`.
  have hconst {c} (hc : c ∈ D) : M c = M c₀ := by
    refine Units.ext (Matrix.ext fun i k ↦
      hD.constant (f := fun c ↦ (M c : Matrix ι ι ℤ) i k) ?_ hc hc₀)
    have hentry : EqOn (fun c ↦ ((M c : Matrix ι ι ℤ) i k : ℝ)) (fun c ↦ R c (Pi.single k 1) i)
        D := fun c hc ↦ by simp [hRM hc, mulVec_single]
    refine Int.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.2 ?_
    exact ((continuous_apply i).comp_continuousOn (hR.clm_apply continuousOn_const)).congr hentry
  -- So `A' - M A` has zero derivative on `D`.
  set N : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' ((M c₀ : Matrix ι ι ℤ).map (↑)))
  have hN (w : ι → ℝ) : N w = (M c₀ : Matrix ι ι ℤ).map (↑) *ᵥ w := Matrix.toLin'_apply _ _
  have hdA {c} (hc : c ∈ D) : DifferentiableAt ℝ A c :=
    (hA.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have hdA' {c} (hc : c ∈ D) : DifferentiableAt ℝ A' c :=
    (hA'.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have hg : EqOn (fderiv ℝ fun c ↦ A' c - N (A c)) 0 D := fun c hc ↦ by
    have h : HasFDerivAt (fun c ↦ A' c - N (A c)) (fderiv ℝ A' c - N.comp (fderiv ℝ A c)) c :=
      (hdA' hc).hasFDerivAt.sub (N.hasFDerivAt.comp c (hdA hc).hasFDerivAt)
    rw [h.fderiv]
    ext1 w
    simp [hN, hM c hc, hconst hc]
  have hgd : DifferentiableOn ℝ (fun c ↦ A' c - N (A c)) D := fun c hc ↦
    ((hdA' hc).sub (N.differentiableAt.comp c (hdA hc))).differentiableWithinAt
  refine ⟨M c₀, A' c₀ - N (A c₀), fun c hc ↦ ?_⟩
  rw [← hN, ← hDo.is_const_of_fderiv_eq_zero hD hgd hg hc hc₀]
  abel

/-! ### Action variables of a family of lattices -/

variable {Λ : (ι → ℝ) → Set (ι → ℝ)}

/-- **Action variables are unique up to integral affine changes.** Let `Λ c` be a family of
lattices over an open preconnected set `D`, and let `A` and `A'` be two `C¹` maps on `D` that are
action variables for it: for every `c ∈ D`, a vector `v` lies in `Λ c` exactly when the one-form
`v ⬝ᵥ dc` is `2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`, and likewise for `A'`. If the derivative of
`A` is injective on `D`, then `A' = M A + b` on `D` for some `M ∈ GL(ι, ℤ)` and `b : ι → ℝ`. -/
theorem exists_eq_mulVec_add_of_forall_mem_iff (hDo : IsOpen D) (hD : IsPreconnected D)
    (hA : ContDiffOn ℝ 1 A D) (hA' : ContDiffOn ℝ 1 A' D)
    (hinj : ∀ c ∈ D, Injective (fderiv ℝ A c))
    (hΛ : ∀ c ∈ D, ∀ v, v ∈ Λ c ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A c i) c w)
    (hΛ' : ∀ c ∈ D, ∀ v, v ∈ Λ c ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A' c i) c w) :
    ∃ (M : GL ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = (M : Matrix ι ι ℤ).map (↑) *ᵥ A c + b := by
  refine exists_eq_mulVec_add_of_forall_exists_fderiv_eq hDo hD hA hA' hinj fun c hc ↦ ?_
  -- At each point the two derivatives are bases of the same lattice.
  have hdA := (hA.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have hdA' := (hA'.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  refine exists_generalLinearGroup_mulVec_eq_of_forall_exists_iff _ _ (hinj c hc) fun v ↦ ?_
  simpa [fderiv_apply hdA, fderiv_apply hdA'] using (hΛ c hc v).symm.trans (hΛ' c hc v)

/-- **Integral affine changes of action variables are action variables.** If `A` are action
variables for a family of lattices `Λ c` over an open set `D`, that is, `v ∈ Λ c` exactly when the
one-form `v ⬝ᵥ dc` is `2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`, then so are `A' = M A + b` for every
`M ∈ GL(ι, ℤ)` and `b : ι → ℝ`. -/
theorem forall_mem_iff_of_eq_mulVec_add (hDo : IsOpen D) (hA : DifferentiableOn ℝ A D)
    (hΛ : ∀ c ∈ D, ∀ v, v ∈ Λ c ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A c i) c w)
    (M : GL ι ℤ) (b : ι → ℝ) (hA' : ∀ c ∈ D, A' c = (M : Matrix ι ι ℤ).map (↑) *ᵥ A c + b) :
    ∀ c ∈ D, ∀ v, v ∈ Λ c ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A' c i) c w := by
  intro c hc v
  have hdA := (hA c hc).differentiableAt (hDo.mem_nhds hc)
  set N : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' ((M : Matrix ι ι ℤ).map (↑)))
  have hN (w : ι → ℝ) : N w = (M : Matrix ι ι ℤ).map (↑) *ᵥ w := Matrix.toLin'_apply _ _
  -- Near `c`, `A' = N ∘ A + b`, so `dA'ᵢ = ∑ₖ Mᵢₖ dAₖ`.
  have hA'c : HasFDerivAt A' (N.comp (fderiv ℝ A c)) c := by
    refine ((N.hasFDerivAt.comp c hdA.hasFDerivAt).add_const b).congr_of_eventuallyEq ?_
    filter_upwards [hDo.mem_nhds hc] with c' hc'
    simp [hA' c' hc', hN]
  -- Hence `∑ᵢ nᵢ dA'ᵢ = ∑ₖ (n M)ₖ dAₖ`.
  have hsum (n : ι → ℤ) (w : ι → ℝ) :
      ∑ i, (n i : ℝ) * fderiv ℝ (fun c ↦ A' c i) c w =
        ∑ k, ((n ᵥ* (M : Matrix ι ι ℤ)) k : ℝ) * fderiv ℝ (fun c ↦ A c k) c w := by
    simp only [fderiv_apply hA'c.differentiableAt, fderiv_apply hdA, hA'c.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hN, mulVec, vecMul,
      dotProduct, Finset.mul_sum, Finset.sum_mul, Int.cast_sum, Int.cast_mul, Matrix.map_apply,
      mul_assoc]
    exact Finset.sum_comm
  rw [hΛ c hc v]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n ᵥ* ((M⁻¹ : GL ι ℤ) : Matrix ι ι ℤ), fun w ↦ ?_⟩
    rw [hsum, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one, hn]
  · rintro ⟨n, hn⟩
    exact ⟨n ᵥ* (M : Matrix ι ι ℤ), fun w ↦ by rw [hn, hsum]⟩

omit [DecidableEq ι] in
/-- Action variables whose derivatives are given by continuous periods are `C¹`. -/
private theorem contDiffOn_of_hasFDerivAt (hDo : IsOpen D)
    {p : ι → (ι → ℝ) → ι → ℝ} (hp : ∀ i, ContinuousOn (p i) D)
    (hA : ∀ c ∈ D, ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c) :
    ContDiffOn ℝ 1 A D := by
  refine contDiffOn_pi.2 fun i ↦ ?_
  rw [← zero_add 1, contDiffOn_succ_iff_fderiv_of_isOpen hDo]
  refine ⟨fun c hc ↦ (hA c hc i).differentiableAt.differentiableWithinAt, by simp,
    contDiffOn_zero.2 ?_⟩
  refine ContinuousOn.congr ?_ fun c hc ↦ (hA c hc i).fderiv
  exact (continuousOn_const (c := (2 * π)⁻¹)).smul (continuousOn_finsetSum _ fun j _ ↦
    ((continuous_apply j).comp_continuousOn (hp i)).smul
      (continuousOn_const (c := (proj j : (ι → ℝ) →L[ℝ] ℝ))))

omit [DecidableEq ι] in
/-- Action variables whose derivatives are given by linearly independent periods have injective
derivative. -/
private theorem injective_fderiv_of_hasFDerivAt {p : ι → (ι → ℝ) → ι → ℝ} {c : ι → ℝ}
    (hli : LinearIndependent ℝ fun i ↦ p i c)
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c) :
    Injective (fderiv ℝ A c) := by
  classical
  have hL (w : ι → ℝ) : fderiv ℝ A c w = (2 * π)⁻¹ • (Matrix.of fun i j ↦ p i c j) *ᵥ w := by
    rw [(hasFDerivAt_pi.2 hA).fderiv]
    ext i
    simp [mulVec, dotProduct, Finset.mul_sum]
  have hP := Matrix.mulVec_injective_iff_isUnit.2 (Matrix.linearIndependent_row_iff_isUnit.1 hli)
  intro w w' h
  rw [hL, hL] at h
  exact hP (smul_right_injective _ (by positivity) h)

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
theorem not_injOn_of_forall_exists_iff_polar {A : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hA : ContDiffOn ℝ 1 A {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)})
    (hΛ : ∀ c ∈ {c : Fin 2 → ℝ | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)}, ∀ v,
      (∃ n : Fin 2 → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ
        (fun c ↦ ![c 0 * cos (c 1), c 0 * sin (c 1)] i) c w) ↔
      ∃ n : Fin 2 → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A c i) c w) :
    ¬ InjOn A {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)} := by
  set B : Set (Fin 2 → ℝ) := {c | c 0 ∈ Ioo 1 2 ∧ c 1 ∈ Ioo 0 (3 * π)}
  have hBo : IsOpen B :=
    (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))
  have hBc : Convex ℝ B :=
    ((convex_Ioo 1 2).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0)).inter
      ((convex_Ioo 0 (3 * π)).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1))
  obtain ⟨M, b, hMb⟩ := exists_eq_mulVec_add_of_forall_mem_iff hBo hBc.isPreconnected
    contDiff_polar.contDiffOn hA (fun c hc ↦ injective_fderiv_polar (by linarith [hc.1.1]))
    (Λ := fun c ↦ {v | ∃ n : Fin 2 → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ
        (fun c ↦ ![c 0 * cos (c 1), c 0 * sin (c 1)] i) c w})
    (fun _ _ _ ↦ Iff.rfl) hΛ
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

/-- **Action-angle data are unique up to integral affine changes.** Let `s` be a section of `F`
over an open preconnected set `D`. Let `λ⁽ⁱ⁾` and `λ'⁽ⁱ⁾` be two continuous families of vectors on
`D`, the `λ⁽ⁱ⁾(c)` linearly independent, with action variables `A` and `A'`:
`dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` and `dA'ᵢ = (2π)⁻¹ ∑ⱼ λ'⁽ⁱ⁾ⱼ dcⱼ`. Suppose both describe the period
lattice: for every `c ∈ D`, `v` is a period of `s c` exactly when `v ⬝ᵥ dc = 2π ∑ᵢ nᵢ dAᵢ` for
some integers `nᵢ`, and likewise for `A'`. Then there are `P ∈ GL(ι, ℤ)` and `b : ι → ℝ` such
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
    (hΛ : ∀ c ∈ D, ∀ v, v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A c i) c w)
    (hΛ' : ∀ c ∈ D, ∀ v, v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) ↔
      ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A' c i) c w) :
    ∃ (P : GL ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = (P : Matrix ι ι ℤ).map (↑) *ᵥ A c + b ∧
      (∀ i, p' i c = ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) • p k c) ∧
      ∀ θ, hσ.angleMap hF hcomm hc s p' (θ, c) =
        hσ.angleMap hF hcomm hc s p (θ ᵥ* (P : Matrix ι ι ℤ).map (↑), c) := by
  obtain ⟨P, b, hPb⟩ := exists_eq_mulVec_add_of_forall_mem_iff hDo hD
    (contDiffOn_of_hasFDerivAt hDo hp hA)
    (contDiffOn_of_hasFDerivAt hDo hp' hA')
    (fun c hcD ↦ injective_fderiv_of_hasFDerivAt (hli c hcD) (hA c hcD)) hΛ hΛ'
  refine ⟨P, b, fun c hcD ↦ ⟨hPb c hcD, ?_⟩⟩
  -- Differentiating `A'ᵢ = ∑ₖ Pᵢₖ Aₖ + bᵢ` and comparing with `dA'ᵢ` gives the periods.
  have hper (i : ι) : p' i c = ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) • p k c := by
    have hcomp : HasFDerivAt (fun c ↦ A' c i) (∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) •
        ((2 * π)⁻¹ • ∑ j, p k c j • (proj j : (ι → ℝ) →L[ℝ] ℝ))) c := by
      refine ((HasFDerivAt.fun_sum fun k _ ↦ (hA c hcD k).const_smul
        ((P : Matrix ι ι ℤ) i k : ℝ)).add_const (b i)).congr_of_eventuallyEq ?_
      filter_upwards [hDo.mem_nhds hcD] with c' hc'
      simp [hPb c' hc', mulVec, dotProduct]
    funext j
    have h := congrArg (· (Pi.single j 1)) ((hA' c hcD i).unique hcomp)
    simp only [FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
      Finset.sum_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_left_cancel₀ (by positivity : (2 * π)⁻¹ ≠ 0) (h.trans ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  refine ⟨hper, fun θ ↦ ?_⟩
  rw [← hσ.angleMap_sum_smul hF hcomm hc, angleMap_apply, angleMap_apply]
  simp only [hper, Matrix.map_apply]

end IsSymplectic

end SmoothTwoForm

end TauCeti
