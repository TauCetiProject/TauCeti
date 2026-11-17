/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Bivector
import TauCeti.LinearAlgebra.Multilinear.CurvatureDimThree

/-!
# Irreducible decomposition of algebraic curvature tensors and bivector operators

Every algebraic curvature tensor `r` on a finite-dimensional real inner product space `V` of
dimension `n` decomposes into three orthogonal `O(V)`-equivariant components:

`r = scalarPart r + tracelessRicciPart r + weyl r`,

where:

* `scalarPart r = (Scal(r) / (n (n - 1))) • constantCurvature V` carries the scalar contraction;
* `tracelessRicciPart r = (n - 2)⁻¹ • (Ric₀(r) ⊙ g)` carries the traceless Ricci contraction
  `Ric₀(r) = Ric(r) - (Scal(r) / n) g`;
* `weyl r = r - tracelessRicciPart r - scalarPart r` is completely trace-free (`Ric(weyl r) = 0`)
  in every dimension, agrees with `r - schouten r ⊙ g` whenever `n ≠ 2`, and vanishes identically
  in dimensions `n ≤ 3`.

On all of `FourTensor V`, the three linear maps `scalarPart`, `tracelessRicciPart`, and `weyl` are
idempotent and mutually annihilating (`P ∘ Q = 0` for distinct `P, Q`) in every dimension, and the
bivector curvature operator decomposes in the Böhm–Wilking form

`curvatureOperator r = (Scal(r) / (n (n - 1))) • (id ∧ id) + (2 / (n - 2)) • (Ric₀End(r) ∧ id) + W`,

where `W = curvatureOperator (weyl r)`. Restricted to algebraic curvature tensors, the three
projections preserve `algebraicCurvatureSubmodule V`, and the three summands of
`curvatureOperator r` are symmetric and pairwise orthogonal with respect to the Hilbert–Schmidt
trace pairing `(A, B) ↦ tr(A ∘ B)`.

## Main definitions

* `TauCeti.FourTensor.tracelessRicci`: the traceless Ricci bilinear form
  `Ric(r) - (Scal(r) / n) g`.
* `TauCeti.FourTensor.ricciEnd` and `TauCeti.FourTensor.tracelessRicciEnd`: the Riesz endomorphisms
  of `ricci` and `tracelessRicci` on `V`.
* `TauCeti.FourTensor.schouten`: the algebraic Schouten bilinear form
  `(n - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (n - 1))) g)`.
* `TauCeti.FourTensor.scalarPart`, `TauCeti.FourTensor.tracelessRicciPart`, and
  `TauCeti.FourTensor.weyl`: the three `O(V)`-equivariant projections on `FourTensor V`.

## Main results

* `TauCeti.FourTensor.eq_zero_of_finrank_le_one` and
  `TauCeti.FourTensor.eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two`: low-dimensional
  normal forms.
* `TauCeti.FourTensor.weyl_add_tracelessRicciPart_add_scalarPart` and the nine idempotence and
  mutual-annihilation lemmas (`scalarPart_scalarPart`, `tracelessRicciPart_scalarPart`, etc.).
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_weyl` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_weyl`: the Weyl component of an algebraic
  curvature tensor is trace-free in every dimension.
* `TauCeti.FourTensor.curvatureOperator_eq_add`: the Böhm–Wilking bivector operator decomposition
  on `FourTensor V`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.trace_curvatureOperator_weyl_comp_scalarPart`,
  `TauCeti.FourTensor.IsAlgebraicCurvature.trace_curvatureOperator_weyl_comp_tracelessRicciPart`,
  and `TauCeti.FourTensor.trace_curvatureOperator_tracelessRicciPart_comp_scalarPart`: pairwise
  Hilbert–Schmidt orthogonality of the three summands for algebraic curvature tensors.
* `TauCeti.FourTensor.IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureOperator_eq_of_finrank_eq_three`: vanishing of
  the Weyl tensor in dimensions `≤ 3` and the resulting three-dimensional curvature formula.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Theorem 1.114.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. (2) 167 (2008), 1079–1097, Section 1.
-/

public section

open LinearMap (BilinForm)
open exteriorPower
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a space of dimension at most `1`, every four-tensor antisymmetric in its first pair of
arguments vanishes. -/
theorem eq_zero_of_finrank_le_one (hV : Module.finrank ℝ V ≤ 1) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w]) : r = 0 := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, zero_apply]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with h0 | h1
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    have hdiag : r ![m 0, m 0, m 2, m 3] = 0 :=
      CharZero.eq_neg_self_iff.mp (h₁ (m 0) (m 0) (m 2) (m 3))
    simpa [Subsingleton.elim (m 1) (m 0)] using hdiag
  · let b := (Module.finBasis ℝ V).reindex (finCongr h1)
    have hexp (x : V) : x = b.repr x 0 • b 0 := by
      conv_lhs => rw [← b.sum_repr x]
      simp
    rw [hexp (m 0), hexp (m 1), apply_smul_first, apply_smul_second]
    have hdiag : r ![b 0, b 0, m 2, m 3] = 0 :=
      CharZero.eq_neg_self_iff.mp (h₁ (b 0) (b 0) (m 2) (m 3))
    rw [hdiag, mul_zero, mul_zero]

/-- On a space of dimension at most `1`, every algebraic curvature tensor vanishes. -/
theorem IsAlgebraicCurvature.eq_zero_of_finrank_le_one (hV : Module.finrank ℝ V ≤ 1)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) : r = 0 :=
  FourTensor.eq_zero_of_finrank_le_one hV hr.antisymm_first

/-- On a space of dimension at most `1`, `algebraicCurvatureSubmodule V` is a subsingleton. -/
theorem subsingleton_algebraicCurvatureSubmodule_of_finrank_le_one
    (hV : Module.finrank ℝ V ≤ 1) : Subsingleton (algebraicCurvatureSubmodule V) :=
  ⟨fun r q ↦ Subtype.ext <|
    ((mem_algebraicCurvatureSubmodule.mp r.2).eq_zero_of_finrank_le_one hV).trans
      ((mem_algebraicCurvatureSubmodule.mp q.2).eq_zero_of_finrank_le_one hV).symm⟩

/-- On a space of dimension at most `1`, every Kulkarni–Nomizu four-tensor vanishes. -/
theorem kulkarniNomizu_eq_zero_of_finrank_le_one (hV : Module.finrank ℝ V ≤ 1)
    (h k : BilinForm ℝ V) : kulkarniNomizu h k = 0 :=
  eq_zero_of_finrank_le_one hV fun u v z w ↦ by
    simp only [kulkarniNomizu_apply_eq]
    exact LinearMap.BilinForm.kulkarniNomizu_antisymm_first h k u v w z

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Low-dimensional normal forms -/

/-- On a space of dimension at most `1`, the constant-curvature tensor vanishes. -/
theorem constantCurvature_eq_zero_of_finrank_le_one (hV : Module.finrank ℝ V ≤ 1) :
    constantCurvature V = 0 :=
  eq_zero_of_finrank_le_one hV isAlgebraicCurvature_constantCurvature.antisymm_first

/-- In dimension at least `2`, the constant-curvature tensor is nonzero. -/
theorem constantCurvature_ne_zero_of_two_le_finrank (hV : 2 ≤ Module.finrank ℝ V) :
    constantCurvature V ≠ 0 := by
  intro h
  have hs := congrArg scalar h
  rw [scalar_constantCurvature, map_zero] at hs
  have hV' : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hV
  nlinarith

/-- In dimension `2`, every pair-antisymmetric four-tensor is `(scalar r / 2) • constantCurvature V`
because `⋀[ℝ]^2 V` is one-dimensional. -/
theorem eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two
    (hV : Module.finrank ℝ V = 2) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    r = (scalar r / 2) • constantCurvature V := by
  have hfin : Module.finrank ℝ (⋀[ℝ]^2 V) = 1 := by
    rw [exteriorPower.finrank_eq, hV]
    decide
  let b := (Module.finBasis ℝ (⋀[ℝ]^2 V)).reindex (finCongr hfin)
  have hend (T : Module.End ℝ (⋀[ℝ]^2 V)) :
      T = LinearMap.trace ℝ (⋀[ℝ]^2 V) T • LinearMap.id := by
    refine b.ext fun i ↦ ?_
    rw [Subsingleton.elim i 0, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
    simp only [Fin.sum_univ_one, Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    conv_lhs => rw [← b.sum_repr (T (b 0))]
    simp
  have hT := congrArg ofBivectorEnd (hend (curvatureOperator r))
  rw [ofBivectorEnd_curvatureOperator_of_antisymm h₁ h₂, map_smul,
    ← curvatureOperator_constantCurvature,
    isAlgebraicCurvature_constantCurvature.ofBivectorEnd_curvatureOperator] at hT
  have htr : LinearMap.trace ℝ (⋀[ℝ]^2 V) (curvatureOperator r) = scalar r / 2 := by
    linarith [scalar_eq_two_mul_trace_curvatureOperator h₁ h₂]
  rwa [htr] at hT

/-- In dimension `2`, every algebraic curvature tensor is `(scalar r / 2) • constantCurvature V`. -/
theorem IsAlgebraicCurvature.eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two
    (hV : Module.finrank ℝ V = 2) {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    r = (scalar r / 2) • constantCurvature V :=
  FourTensor.eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two hV
    hr.antisymm_first hr.antisymm_last

/-! ### Traceless Ricci, Riesz operators, and algebraic Schouten tensor -/

/-- The traceless Ricci contraction `Ric₀(r) = Ric(r) - (Scal(r) / dim V) g` of a four-tensor. -/
def tracelessRicci : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ricci + (-(Module.finrank ℝ V : ℝ)⁻¹ • scalar).smulRight (innerₗ V)

/-- Evaluation of `tracelessRicci` as a linear combination of `ricci` and `innerₗ V`. -/
theorem tracelessRicci_apply (r : FourTensor V) :
    tracelessRicci r = ricci r - (scalar r / (Module.finrank ℝ V : ℝ)) • innerₗ V := by
  ext u v
  simp only [tracelessRicci, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, div_eq_inv_mul]
  ring

/-- Pointwise evaluation of `tracelessRicci`. -/
theorem tracelessRicci_apply_apply (r : FourTensor V) (u v : V) :
    tracelessRicci r u v = ricci r u v - scalar r / (Module.finrank ℝ V : ℝ) * ⟪u, v⟫ := by
  simp [tracelessRicci_apply]

private theorem bilinFormTrace_sub (h k : BilinForm ℝ V) :
    bilinFormTrace (h - k) = bilinFormTrace h - bilinFormTrace k := by
  simp only [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ V), LinearMap.sub_apply,
    Finset.sum_sub_distrib]

/-- The metric trace of `tracelessRicci r` vanishes in every dimension. -/
@[simp]
theorem bilinFormTrace_tracelessRicci (r : FourTensor V) :
    bilinFormTrace (tracelessRicci r) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with h0 | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    have htr : tracelessRicci r = 0 := by
      ext u v
      rw [Subsingleton.elim u 0]
      simp
    rw [htr, map_zero]
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [tracelessRicci_apply, bilinFormTrace_sub, map_smul, bilinFormTrace_inner, ← scalar_apply,
      smul_eq_mul, div_mul_cancel₀ _ hn', sub_self]

/-- For an algebraic curvature tensor, `tracelessRicci r` is a symmetric bilinear form. -/
theorem IsAlgebraicCurvature.isSymm_tracelessRicci {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicci r).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  rw [tracelessRicci_apply_apply, tracelessRicci_apply_apply, hr.isSymm_ricci.eq u v,
    real_inner_comm u v]

/-- The traceless Ricci tensor of the constant-curvature tensor vanishes in every dimension. -/
@[simp]
theorem tracelessRicci_constantCurvature : tracelessRicci (constantCurvature V) = 0 := by
  rcases eq_or_ne (Module.finrank ℝ V) 0 with h0 | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext u v
    rw [Subsingleton.elim u 0]
    simp
  · have hn' : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    ext u v
    rw [tracelessRicci_apply_apply, ricci_constantCurvature, scalar_constantCurvature,
      mul_div_cancel_left₀ _ hn']
    simp

/-- `tracelessRicci` is equivariant under linear isometric equivalences. -/
theorem tracelessRicci_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) (u v : W) :
    tracelessRicci (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap)
        u v =
      tracelessRicci r (e u) (e v) := by
  rw [tracelessRicci_apply_apply, tracelessRicci_apply_apply,
    ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    e.inner_map_map]

/-- Riesz identification of a bilinear form `h : BilinForm ℝ V` with the endomorphism `A` satisfying
`⟪A u, v⟫ = h u v`. -/
private def rieszEnd : BilinForm ℝ V →ₗ[ℝ] Module.End ℝ V where
  toFun h := (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv.toLinearMap ∘ₗ
    h.toContinuousBilinearMap.toLinearMap
  map_add' h k := LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' c h := LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

private theorem inner_rieszEnd_left (h : BilinForm ℝ V) (u v : V) :
    ⟪rieszEnd h u, v⟫ = h u v := by
  simp [rieszEnd, InnerProductSpace.toDual_symm_apply]

private theorem trace_rieszEnd (h : BilinForm ℝ V) :
    LinearMap.trace ℝ V (rieszEnd h) = bilinFormTrace h := by
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b, bilinFormTrace_eq_sum h b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_rieszEnd_left]

/-- The Ricci endomorphism `RicEnd(r) : Module.End ℝ V` characterized by
`⟪ricciEnd r u, v⟫ = ricci r u v`. -/
def ricciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  rieszEnd ∘ₗ ricci

/-- `ricciEnd r` represents `ricci r` with respect to the inner product. -/
@[simp]
theorem inner_ricciEnd_left (r : FourTensor V) (u v : V) :
    ⟪ricciEnd r u, v⟫ = ricci r u v :=
  inner_rieszEnd_left (ricci r) u v

/-- The trace of `ricciEnd r` is `scalar r`. -/
@[simp]
theorem trace_ricciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (ricciEnd r) = scalar r := by
  rw [ricciEnd, LinearMap.comp_apply, trace_rieszEnd, ← scalar_apply]

/-- For an algebraic curvature tensor, `ricciEnd r` is a symmetric endomorphism of `V`. -/
theorem IsAlgebraicCurvature.isSymmetric_ricciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (ricciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_ricciEnd_left, real_inner_comm (ricciEnd r v) u, inner_ricciEnd_left,
    hr.isSymm_ricci.eq u v]

/-- The traceless Ricci endomorphism `Ric₀End(r) : Module.End ℝ V` characterized by
`⟪tracelessRicciEnd r u, v⟫ = tracelessRicci r u v`. -/
def tracelessRicciEnd : FourTensor V →ₗ[ℝ] Module.End ℝ V :=
  rieszEnd ∘ₗ tracelessRicci

/-- `tracelessRicciEnd r` represents `tracelessRicci r` with respect to the inner product. -/
@[simp]
theorem inner_tracelessRicciEnd_left (r : FourTensor V) (u v : V) :
    ⟪tracelessRicciEnd r u, v⟫ = tracelessRicci r u v :=
  inner_rieszEnd_left (tracelessRicci r) u v

/-- The trace of `tracelessRicciEnd r` vanishes in every dimension. -/
@[simp]
theorem trace_tracelessRicciEnd (r : FourTensor V) :
    LinearMap.trace ℝ V (tracelessRicciEnd r) = 0 := by
  rw [tracelessRicciEnd, LinearMap.comp_apply, trace_rieszEnd, bilinFormTrace_tracelessRicci]

/-- For an algebraic curvature tensor, `tracelessRicciEnd r` is a symmetric endomorphism of `V`. -/
theorem IsAlgebraicCurvature.isSymmetric_tracelessRicciEnd {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) : (tracelessRicciEnd r).IsSymmetric := fun u v ↦ by
  rw [inner_tracelessRicciEnd_left, real_inner_comm (tracelessRicciEnd r v) u,
    inner_tracelessRicciEnd_left, hr.isSymm_tracelessRicci.eq u v]

/-- Pulling back `r` along a linear isometric equivalence `e : W ≃ₗᵢ[ℝ] V` conjugates
`tracelessRicciEnd r` by `e`. -/
theorem tracelessRicciEnd_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    tracelessRicciEnd
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      e.symm.toLinearEquiv.conj (tracelessRicciEnd r) := by
  ext u
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [inner_tracelessRicciEnd_left, tracelessRicci_compContinuousLinearMap_linearIsometryEquiv]
  change tracelessRicci r (e u) (e v) = ⟪e.symm (tracelessRicciEnd r (e u)), v⟫
  rw [← e.inner_map_map, e.apply_symm_apply, inner_tracelessRicciEnd_left]

/-- The algebraic Schouten bilinear form
`P(r) = (dim V - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (dim V - 1))) g)`. -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
    (ricci + (-(2 * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar).smulRight (innerₗ V))

/-- Evaluation of the algebraic Schouten form. -/
theorem schouten_apply (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
      (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) := by
  ext u v
  simp only [schouten, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, innerₗ_apply_apply, smul_eq_mul, div_eq_inv_mul]
  ring

/-- Pointwise evaluation of the algebraic Schouten form. -/
theorem schouten_apply_apply (r : FourTensor V) (u v : V) :
    schouten r u v = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
      (ricci r u v - scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) * ⟪u, v⟫) := by
  simp [schouten_apply]

/-- For an algebraic curvature tensor, `schouten r` is symmetric. -/
theorem IsAlgebraicCurvature.isSymm_schouten {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    (schouten r).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  rw [schouten_apply_apply, schouten_apply_apply, hr.isSymm_ricci.eq u v, real_inner_comm u v]

/-! ### Scalar, traceless-Ricci, and Weyl components -/

/-- The scalar curvature component `(Scal(r) / (n (n - 1))) • constantCurvature V` of a
four-tensor. -/
def scalarPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  (((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar).smulRight
    (constantCurvature V)

/-- Evaluation of `scalarPart`. -/
theorem scalarPart_apply (r : FourTensor V) :
    scalarPart r =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
        constantCurvature V := by
  simp [scalarPart, div_eq_inv_mul]

/-- The traceless-Ricci curvature component `(n - 2)⁻¹ • (tracelessRicci r ⊙ g)` of a
four-tensor. -/
def tracelessRicciPart : FourTensor V →ₗ[ℝ] FourTensor V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • (kulkarniNomizu.flip (innerₗ V) ∘ₗ tracelessRicci)

/-- Evaluation of `tracelessRicciPart`. -/
theorem tracelessRicciPart_apply (r : FourTensor V) :
    tracelessRicciPart r =
      ((Module.finrank ℝ V : ℝ) - 2)⁻¹ • kulkarniNomizu (tracelessRicci r) (innerₗ V) :=
  (rfl)

/-- The Weyl curvature component `r - tracelessRicciPart r - scalarPart r` of a four-tensor. -/
def weyl : FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.id - tracelessRicciPart - scalarPart

/-- Evaluation of `weyl`. -/
theorem weyl_apply (r : FourTensor V) :
    weyl r = r - tracelessRicciPart r - scalarPart r :=
  (rfl)

/-- Every four-tensor is the sum of its Weyl, traceless-Ricci, and scalar parts. -/
@[simp]
theorem weyl_add_tracelessRicciPart_add_scalarPart (r : FourTensor V) :
    weyl r + tracelessRicciPart r + scalarPart r = r := by
  ext m
  simp only [weyl_apply, add_apply, sub_apply]
  ring

/-- Irreducible curvature decomposition `r = scalarPart r + tracelessRicciPart r + weyl r`. -/
theorem eq_scalarPart_add_tracelessRicciPart_add_weyl (r : FourTensor V) :
    r = scalarPart r + tracelessRicciPart r + weyl r := by
  ext m
  simp only [weyl_apply, add_apply, sub_apply]
  ring

/-- Away from dimension `2`, the non-Weyl part `tracelessRicciPart r + scalarPart r` is the
Kulkarni–Nomizu product of `schouten r` with the inner product. -/
theorem tracelessRicciPart_add_scalarPart_eq_kulkarniNomizu_schouten
    (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicciPart r + scalarPart r = kulkarniNomizu (schouten r) (innerₗ V) := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h1
  · rw [tracelessRicciPart_apply, scalarPart_apply,
      kulkarniNomizu_eq_zero_of_finrank_le_one h1,
      constantCurvature_eq_zero_of_finrank_le_one h1,
      kulkarniNomizu_eq_zero_of_finrank_le_one h1, smul_zero, smul_zero, add_zero]
  · have h3 : 3 ≤ Module.finrank ℝ V := by omega
    have h3' : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast h3
    have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := by linarith
    have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := by linarith
    ext m
    have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
    rw [hm, add_apply, tracelessRicciPart_apply, scalarPart_apply, smul_apply, smul_apply,
      constantCurvature_apply, kulkarniNomizu_apply, kulkarniNomizu_apply]
    simp only [tracelessRicci_apply_apply, schouten_apply_apply, innerₗ_apply_apply, smul_eq_mul]
    field_simp
    ring

/-- Away from dimension `2`, `weyl r = r - kulkarniNomizu (schouten r) (innerₗ V)`. -/
theorem weyl_eq_sub_kulkarniNomizu_schouten (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    weyl r = r - kulkarniNomizu (schouten r) (innerₗ V) := by
  rw [weyl_apply, sub_sub, tracelessRicciPart_add_scalarPart_eq_kulkarniNomizu_schouten hn]

/-- `scalarPart r` is always an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_scalarPart (r : FourTensor V) :
    IsAlgebraicCurvature (scalarPart r) :=
  mem_algebraicCurvatureSubmodule.mp <|
    Submodule.smul_mem (algebraicCurvatureSubmodule V) _
      (mem_algebraicCurvatureSubmodule.mpr isAlgebraicCurvature_constantCurvature)

/-- If `r` is an algebraic curvature tensor, so is `tracelessRicciPart r`. -/
theorem IsAlgebraicCurvature.tracelessRicciPart {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.tracelessRicciPart r) :=
  mem_algebraicCurvatureSubmodule.mp <|
    Submodule.smul_mem (algebraicCurvatureSubmodule V) _
      (mem_algebraicCurvatureSubmodule.mpr
        (isAlgebraicCurvature_kulkarniNomizu hr.isSymm_tracelessRicci
          ⟨fun u v ↦ real_inner_comm v u⟩))

/-- If `r` is an algebraic curvature tensor, so is `weyl r`. -/
theorem IsAlgebraicCurvature.weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    IsAlgebraicCurvature (FourTensor.weyl r) :=
  mem_algebraicCurvatureSubmodule.mp <|
    Submodule.sub_mem (algebraicCurvatureSubmodule V)
      (Submodule.sub_mem (algebraicCurvatureSubmodule V)
        (mem_algebraicCurvatureSubmodule.mpr hr)
        (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart))
      (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r))

/-! ### `O(V)`-equivariance of the three projections -/

/-- `scalarPart` commutes with pullback along a linear isometric equivalence. -/
theorem scalarPart_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    scalarPart (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (scalarPart r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  rw [scalarPart_apply, scalarPart_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq,
    ← ContinuousMultilinearMap.compContinuousLinearMap_apply,
    constantCurvature_compContinuousLinearMap_linearIsometry]

/-- `tracelessRicciPart` commutes with pullback along a linear isometric equivalence. -/
theorem tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    tracelessRicciPart
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (tracelessRicciPart r).compContinuousLinearMap
        fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, tracelessRicciPart_apply, tracelessRicciPart_apply, smul_apply,
    compContinuousLinearMap_apply_vec, smul_apply, kulkarniNomizu_apply, kulkarniNomizu_apply,
    e.toLinearEquiv.finrank_eq]
  simp only [tracelessRicci_compContinuousLinearMap_linearIsometryEquiv, innerₗ_apply_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    e.inner_map_map]

/-- `weyl` commutes with pullback along a linear isometric equivalence. -/
theorem weyl_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    weyl (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (weyl r).compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap := by
  rw [weyl_apply, weyl_apply,
    tracelessRicciPart_compContinuousLinearMap_linearIsometryEquiv,
    scalarPart_compContinuousLinearMap_linearIsometryEquiv]
  ext m
  simp only [sub_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-! ### Contractions, idempotence, and mutual annihilation -/

/-- In dimension at least `2`, `scalar (scalarPart r) = scalar r`. -/
theorem scalar_scalarPart (hV : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    scalar (scalarPart r) = scalar r := by
  have hV' : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hV
  have hprod : (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 := by nlinarith
  rw [scalarPart_apply, map_smul, scalar_constantCurvature, smul_eq_mul,
    div_mul_cancel₀ _ hprod]

/-- In dimension at least `2`, `ricci (scalarPart r) = (scalar r / dim V) • innerₗ V`. -/
theorem ricci_scalarPart (hV : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ricci (scalarPart r) = (scalar r / (Module.finrank ℝ V : ℝ)) • innerₗ V := by
  have hV' : (2 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hV
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
  rw [scalarPart_apply, map_smul, ricci_constantCurvature, smul_smul]
  congr 1
  field_simp

/-- The traceless Ricci contraction of `scalarPart r` vanishes in every dimension. -/
@[simp]
theorem tracelessRicci_scalarPart (r : FourTensor V) :
    tracelessRicci (scalarPart r) = 0 := by
  rw [scalarPart_apply, map_smul, tracelessRicci_constantCurvature, smul_zero]

/-- The scalar contraction of `tracelessRicciPart r` vanishes in every dimension. -/
@[simp]
theorem scalar_tracelessRicciPart (r : FourTensor V) :
    scalar (tracelessRicciPart r) = 0 := by
  rw [tracelessRicciPart_apply, map_smul, scalar_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, mul_zero, smul_zero]

/-- Away from dimension `2`, `ricci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem ricci_tracelessRicciPart (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    ricci (tracelessRicciPart r) = tracelessRicci r := by
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [tracelessRicciPart_apply, map_smul, ricci_kulkarniNomizu_innerₗ,
    bilinFormTrace_tracelessRicci, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hn2, one_smul]

/-- Away from dimension `2`, `tracelessRicci (tracelessRicciPart r) = tracelessRicci r`. -/
theorem tracelessRicci_tracelessRicciPart (hn : Module.finrank ℝ V ≠ 2) (r : FourTensor V) :
    tracelessRicci (tracelessRicciPart r) = tracelessRicci r := by
  ext u v
  rw [tracelessRicci_apply_apply, ricci_tracelessRicciPart hn, scalar_tracelessRicciPart]
  simp

/-- `scalarPart` is idempotent in every dimension. -/
@[simp]
theorem scalarPart_scalarPart (r : FourTensor V) :
    scalarPart (scalarPart r) = scalarPart r := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h1
  · rw [scalarPart_apply (scalarPart r), scalarPart_apply r,
      constantCurvature_eq_zero_of_finrank_le_one h1, smul_zero, smul_zero]
  · rw [scalarPart_apply (scalarPart r), scalar_scalarPart h1, ← scalarPart_apply]

/-- `tracelessRicciPart` annihilates `scalarPart` in every dimension. -/
@[simp]
theorem tracelessRicciPart_scalarPart (r : FourTensor V) :
    tracelessRicciPart (scalarPart r) = 0 := by
  rw [tracelessRicciPart_apply, tracelessRicci_scalarPart, map_zero, LinearMap.zero_apply,
    smul_zero]

/-- `scalarPart` annihilates `tracelessRicciPart` in every dimension. -/
@[simp]
theorem scalarPart_tracelessRicciPart (r : FourTensor V) :
    scalarPart (tracelessRicciPart r) = 0 := by
  rw [scalarPart_apply, scalar_tracelessRicciPart, zero_div, zero_smul]

/-- `tracelessRicciPart` is idempotent in every dimension. -/
@[simp]
theorem tracelessRicciPart_tracelessRicciPart (r : FourTensor V) :
    tracelessRicciPart (tracelessRicciPart r) = tracelessRicciPart r := by
  rcases eq_or_ne (Module.finrank ℝ V) 2 with h2 | hn
  · simp [tracelessRicciPart_apply, h2]
  · rw [tracelessRicciPart_apply (tracelessRicciPart r), tracelessRicci_tracelessRicciPart hn,
      ← tracelessRicciPart_apply]

/-- `weyl` annihilates `scalarPart` in every dimension. -/
@[simp]
theorem weyl_scalarPart (r : FourTensor V) : weyl (scalarPart r) = 0 := by
  rw [weyl_apply, tracelessRicciPart_scalarPart, scalarPart_scalarPart, sub_zero, sub_self]

/-- `weyl` annihilates `tracelessRicciPart` in every dimension. -/
@[simp]
theorem weyl_tracelessRicciPart (r : FourTensor V) : weyl (tracelessRicciPart r) = 0 := by
  rw [weyl_apply, tracelessRicciPart_tracelessRicciPart, scalarPart_tracelessRicciPart, sub_self,
    sub_zero]

/-- `scalarPart` annihilates `weyl` in every dimension. -/
@[simp]
theorem scalarPart_weyl (r : FourTensor V) : scalarPart (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, scalarPart_tracelessRicciPart, scalarPart_scalarPart, sub_zero,
    sub_self]

/-- `tracelessRicciPart` annihilates `weyl` in every dimension. -/
@[simp]
theorem tracelessRicciPart_weyl (r : FourTensor V) : tracelessRicciPart (weyl r) = 0 := by
  rw [weyl_apply, map_sub, map_sub, tracelessRicciPart_tracelessRicciPart,
    tracelessRicciPart_scalarPart, sub_self, sub_zero]

/-- `weyl` is idempotent in every dimension. -/
@[simp]
theorem weyl_weyl (r : FourTensor V) : weyl (weyl r) = weyl r := by
  rw [weyl_apply (weyl r), tracelessRicciPart_weyl, scalarPart_weyl, sub_zero, sub_zero]

/-- For an algebraic curvature tensor, the Weyl component has vanishing Ricci contraction in every
dimension. -/
theorem IsAlgebraicCurvature.ricci_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.weyl r) = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h1
  · rw [hr.weyl.eq_zero_of_finrank_le_one h1, map_zero]
  · rcases eq_or_ne (Module.finrank ℝ V) 2 with h2 | hn
    · have htr0 : FourTensor.tracelessRicciPart r = 0 := by simp [tracelessRicciPart_apply, h2]
      have hw : FourTensor.weyl r = 0 := by
        rw [weyl_apply, htr0, sub_zero, scalarPart_apply, h2]
        norm_num
        exact sub_eq_zero.mpr (hr.eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two h2)
      rw [hw, map_zero]
    · have hw : FourTensor.weyl r =
          r + (-1 : ℝ) • FourTensor.tracelessRicciPart r + (-1 : ℝ) • scalarPart r := by
        ext m
        simp only [weyl_apply, add_apply, sub_apply, smul_apply, smul_eq_mul]
        ring
      rw [hw, map_add, map_add, map_smul, map_smul, ricci_tracelessRicciPart hn,
        ricci_scalarPart h1]
      ext u v
      simp only [LinearMap.add_apply, LinearMap.smul_apply, tracelessRicci_apply_apply,
        innerₗ_apply_apply, LinearMap.zero_apply, smul_eq_mul]
      ring

/-- For an algebraic curvature tensor, the Weyl component has vanishing scalar contraction in every
dimension. -/
theorem IsAlgebraicCurvature.scalar_weyl {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.weyl r) = 0 := by
  rw [scalar_apply, hr.ricci_weyl, map_zero]

/-! ### Bivector operator decomposition and Hilbert–Schmidt orthogonality -/

/-- The bivector operator of `scalarPart r` is
`(Scal(r) / (n (n - 1))) • (id ∧ id)`. -/
theorem curvatureOperator_scalarPart (r : FourTensor V) :
    curvatureOperator (scalarPart r) =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
        wedgeEnd (LinearMap.id : Module.End ℝ V) LinearMap.id := by
  rw [scalarPart_apply, map_smul, curvatureOperator_constantCurvature, wedgeEnd_id_id]

/-- The bivector operator of `tracelessRicciPart r` is
`(2 / (n - 2)) • (tracelessRicciEnd r ∧ id)`. -/
theorem curvatureOperator_tracelessRicciPart (r : FourTensor V) :
    curvatureOperator (tracelessRicciPart r) =
      (2 / ((Module.finrank ℝ V : ℝ) - 2)) •
        wedgeEnd (tracelessRicciEnd r) LinearMap.id := by
  rw [tracelessRicciPart_apply, map_smul,
    curvatureOperator_kulkarniNomizu_of_inner (A := tracelessRicciEnd r) (B := LinearMap.id)
      (fun u v ↦ (inner_tracelessRicciEnd_left r u v).symm)
      (fun u v ↦ by simp [innerₗ_apply_apply]),
    smul_smul, inv_mul_eq_div]

/-- **Böhm–Wilking bivector operator decomposition**: for every four-tensor `r`,
`curvatureOperator r` splits into scalar (`id ∧ id`), traceless-Ricci (`Ric₀End ∧ id`), and Weyl
operators on `⋀[ℝ]^2 V`. -/
theorem curvatureOperator_eq_add (r : FourTensor V) :
    curvatureOperator r =
      (scalar r / ((Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1))) •
          wedgeEnd (LinearMap.id : Module.End ℝ V) LinearMap.id +
        (2 / ((Module.finrank ℝ V : ℝ) - 2)) •
          wedgeEnd (tracelessRicciEnd r) LinearMap.id +
        curvatureOperator (weyl r) := by
  conv_lhs => rw [eq_scalarPart_add_tracelessRicciPart_add_weyl r]
  rw [map_add, map_add, curvatureOperator_scalarPart, curvatureOperator_tracelessRicciPart]

/-- The Weyl bivector operator of an algebraic curvature tensor is Hilbert–Schmidt orthogonal to
`A ∧ id` for every endomorphism `A : Module.End ℝ V`. -/
theorem IsAlgebraicCurvature.trace_curvatureOperator_weyl_comp_wedgeEnd_id {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (A : Module.End ℝ V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureOperator (FourTensor.weyl r) ∘ₗ wedgeEnd A LinearMap.id) = 0 := by
  have h := two_mul_trace_curvatureOperator_comp_wedgeEnd_id (stdOrthonormalBasis ℝ V)
    hr.weyl.antisymm_first hr.weyl.antisymm_last A
  rw [hr.ricci_weyl] at h
  simp only [LinearMap.zero_apply, Finset.sum_const_zero] at h
  linarith

/-- The Weyl bivector operator of an algebraic curvature tensor is Hilbert–Schmidt orthogonal to
every scalar curvature operator. -/
theorem IsAlgebraicCurvature.trace_curvatureOperator_weyl_comp_scalarPart {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (q : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureOperator (FourTensor.weyl r) ∘ₗ curvatureOperator (scalarPart q)) = 0 := by
  rw [curvatureOperator_scalarPart, LinearMap.comp_smul, map_smul,
    hr.trace_curvatureOperator_weyl_comp_wedgeEnd_id, smul_zero]

/-- The Weyl bivector operator of an algebraic curvature tensor is Hilbert–Schmidt orthogonal to
every traceless-Ricci curvature operator. -/
theorem IsAlgebraicCurvature.trace_curvatureOperator_weyl_comp_tracelessRicciPart
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (q : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureOperator (FourTensor.weyl r) ∘ₗ
          curvatureOperator (FourTensor.tracelessRicciPart q)) = 0 := by
  rw [curvatureOperator_tracelessRicciPart, LinearMap.comp_smul, map_smul,
    hr.trace_curvatureOperator_weyl_comp_wedgeEnd_id, smul_zero]

/-- Every traceless-Ricci bivector operator is Hilbert–Schmidt orthogonal to every scalar curvature
operator. -/
theorem trace_curvatureOperator_tracelessRicciPart_comp_scalarPart (r q : FourTensor V) :
    LinearMap.trace ℝ (⋀[ℝ]^2 V)
        (curvatureOperator (tracelessRicciPart r) ∘ₗ curvatureOperator (scalarPart q)) = 0 := by
  rw [curvatureOperator_tracelessRicciPart, curvatureOperator_scalarPart, LinearMap.smul_comp,
    LinearMap.comp_smul, wedgeEnd_id_id, LinearMap.comp_id, map_smul, map_smul,
    trace_wedgeEnd_id_right, trace_tracelessRicciEnd, mul_zero, smul_zero, smul_zero]

/-! ### Vanishing of the Weyl component in dimensions at most `3` -/

/-- **In dimension at most `3`, the Weyl component of every algebraic curvature tensor vanishes.**
-/
theorem IsAlgebraicCurvature.weyl_eq_zero_of_finrank_le_three
    (hV : Module.finrank ℝ V ≤ 3) {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    FourTensor.weyl r = 0 := by
  rcases le_or_gt (Module.finrank ℝ V) 1 with h1 | h1
  · exact hr.weyl.eq_zero_of_finrank_le_one h1
  · rcases eq_or_ne (Module.finrank ℝ V) 2 with h2 | hn2
    · rw [hr.weyl.eq_scalar_div_two_smul_constantCurvature_of_finrank_eq_two h2,
        hr.scalar_weyl, zero_div, zero_smul]
    · have h3 : Module.finrank ℝ V = 3 := by omega
      let T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
        LinearMap.mk₂ ℝ
          (fun u v ↦ LinearMap.mk₂ ℝ (fun w z ↦ FourTensor.weyl r ![u, v, z, w])
            (fun w₁ w₂ z ↦ apply_add_fourth ..)
            (fun c w z ↦ by simp [apply_smul_fourth])
            (fun w z₁ z₂ ↦ apply_add_third ..)
            (fun c w z ↦ by simp [apply_smul_third]))
          (fun u₁ u₂ v ↦ by ext w z; simp [apply_add_first])
          (fun c u v ↦ by ext w z; simp [apply_smul_first])
          (fun u v₁ v₂ ↦ by ext w z; simp [apply_add_second])
          (fun c u v ↦ by ext w z; simp [apply_smul_second])
      have hT : T = 0 :=
        LinearMap.eq_zero_of_sum_basis_eq_zero_of_card_eq_three
          ((two_ne_zero (α := ℝ)).isUnit.isSMulRegular ℝ)
          (stdOrthonormalBasis ℝ V).toBasis (by simpa using h3)
          (fun u v w z ↦ hr.weyl.antisymm_first u v z w)
          (fun u v w z ↦ hr.weyl.antisymm_last u v z w)
          (fun y z ↦ by
            simp only [T, LinearMap.mk₂_apply, OrthonormalBasis.coe_toBasis,
              ← ricci_apply_orthonormalBasis (stdOrthonormalBasis ℝ V), hr.ricci_weyl,
              LinearMap.zero_apply])
      ext m
      have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
      have hm' := LinearMap.congr_fun (LinearMap.congr_fun
        (LinearMap.congr_fun (LinearMap.congr_fun hT (m 0)) (m 1)) (m 3)) (m 2)
      rw [hm, zero_apply]
      simpa only [T, LinearMap.mk₂_apply, LinearMap.zero_apply] using hm'

/-- In dimension at most `3`, every algebraic curvature tensor equals the sum of its scalar and
traceless-Ricci parts. -/
theorem IsAlgebraicCurvature.eq_scalarPart_add_tracelessRicciPart_of_finrank_le_three
    (hV : Module.finrank ℝ V ≤ 3) {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    r = scalarPart r + FourTensor.tracelessRicciPart r := by
  conv_lhs => rw [eq_scalarPart_add_tracelessRicciPart_add_weyl r]
  rw [hr.weyl_eq_zero_of_finrank_le_three hV, add_zero]

/-- In dimension `3`, every algebraic curvature tensor is the Kulkarni–Nomizu product of its
Schouten tensor with the inner product. -/
theorem IsAlgebraicCurvature.eq_kulkarniNomizu_schouten_of_finrank_eq_three
    (hV : Module.finrank ℝ V = 3) {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    r = kulkarniNomizu (schouten r) (innerₗ V) := by
  have h := hr.weyl_eq_zero_of_finrank_le_three hV.le
  rw [weyl_eq_sub_kulkarniNomizu_schouten (by omega) r] at h
  exact sub_eq_zero.mp h

/-- **Three-dimensional bivector curvature operator formula**: in dimension `3`, every algebraic
curvature tensor has bivector operator
`(Scal(r) / 6) • (id ∧ id) + 2 • (tracelessRicciEnd r ∧ id)`. -/
theorem IsAlgebraicCurvature.curvatureOperator_eq_of_finrank_eq_three
    (hV : Module.finrank ℝ V = 3) {r : FourTensor V} (hr : IsAlgebraicCurvature r) :
    curvatureOperator r =
      (scalar r / 6) • wedgeEnd (LinearMap.id : Module.End ℝ V) LinearMap.id +
        (2 : ℝ) • wedgeEnd (tracelessRicciEnd r) LinearMap.id := by
  rw [curvatureOperator_eq_add, hr.weyl_eq_zero_of_finrank_le_three hV.le, map_zero, add_zero, hV]
  norm_num

end InnerProductSpace

end TauCeti.FourTensor
