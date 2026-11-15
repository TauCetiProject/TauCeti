/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.LinearAlgebra.CliffordAlgebra.Classification
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Four
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Euclidean actions of negative-definite Clifford algebras and orthogonal hyperplane frames

Given a representation of a negative-definite real Clifford algebra `Cliff(0, q)` on a
finite-dimensional real vector space `W`, averaging any positive-definite quadratic form over the
finite signed monomial group equips `W` with an inner product for which every Clifford vector acts
skew-adjointly (`AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`). Transporting that
inner product along an orthonormal basis transfers the Clifford action to any real inner product
space `E` of the same dimension as a family of skew-symmetric continuous linear operators squaring
to `-1` and pairwise anticommuting.

Evaluated at any unit vector `x ∈ E`, `q` such operators produce `q` orthonormal vectors in the
orthogonal complement `(ℝ ∙ x)ᗮ`; when `finrank ℝ E = q + 1`, they form an explicit orthonormal
basis of `(ℝ ∙ x)ᗮ`. Combined with the real Clifford algebra models `Cliff(0, 1) ≃ₐ[ℝ] ℂ`,
`Cliff(0, 3) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`, and `Cliff(0, 7) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)`, this yields skew-adjoint
Clifford operator families on real inner product spaces of dimensions `2`, `4`, and `8`, the linear
algebra behind the smooth tangent frames on `S¹`, `S³`, and `S⁷`.

## Main definitions and results

* `AlgHom.map_cliffordAlgebraι_mul_self`, `AlgHom.map_cliffordAlgebraι_anticommute_of_isOrtho`:
  the Clifford relations transported along an algebra homomorphism, over any commutative ring.
* `TauCeti.mem_orthogonal_span_singleton_of_skew`,
  `TauCeti.orthonormal_apply_of_skew_anticommute`: skew-symmetric anticommuting operators squaring
  to `-1` send each unit vector `x` to an orthonormal family in `(ℝ ∙ x)ᗮ`.
* `TauCeti.orthonormalBasisOrthogonalOfSkewFamily`: when `finrank ℝ E = card ι + 1`, this family
  is an `OrthonormalBasis ι ℝ (ℝ ∙ x)ᗮ`.
* `TauCeti.exists_skewAdjoint_cliffordAction_of_finrank_eq`: any finite-dimensional real module
  over a Clifford algebra with a finite orthogonal `-1`-basis transfers to a skew-adjoint
  continuous-linear Clifford action on any real inner product space of equal dimension.
* `TauCeti.exists_skewAdjoint_anticommuting_clm`: for `n ∈ {1, 3, 7}`, every `(n + 1)`-dimensional
  real inner product space admits `n` skew-symmetric anticommuting continuous linear endomorphisms
  squaring to `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1 (orthogonal multiplications and tangent frames on
  `S¹`, `S³`, and `S⁷`).
-/

public section

open CliffordAlgebra Module
open scoped InnerProductSpace Quaternion

namespace AlgHom

section CliffordRelations

variable {K M A W : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [Ring A] [Algebra K A] [AddCommGroup W] [Module K W] {Q : QuadraticForm K M}

/-- Under any algebra homomorphism out of `CliffordAlgebra Q`, the image of a vector `v` squares to
the scalar `Q v`. -/
theorem map_cliffordAlgebraι_mul_self (ρ : CliffordAlgebra Q →ₐ[K] A) (v : M) :
    ρ (ι Q v) * ρ (ι Q v) = algebraMap K A (Q v) := by
  rw [← map_mul, ι_sq_scalar, AlgHom.commutes]

/-- In a `CliffordAlgebra Q`-module, applying a vector `v` twice scales by `Q v`. -/
theorem map_cliffordAlgebraι_apply_self (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    (v : M) (w : W) :
    ρ (ι Q v) (ρ (ι Q v) w) = Q v • w := by
  rw [← mul_apply_eq_comp, ρ.map_cliffordAlgebraι_mul_self, Module.algebraMap_end_apply]

/-- A vector with `Q v = -1` maps to a square root of `-1` under any algebra homomorphism out of
`CliffordAlgebra Q`. -/
theorem map_cliffordAlgebraι_mul_self_of_eq_neg_one (ρ : CliffordAlgebra Q →ₐ[K] A)
    {v : M} (hv : Q v = -1) :
    ρ (ι Q v) * ρ (ι Q v) = -1 := by
  rw [ρ.map_cliffordAlgebraι_mul_self, hv, map_neg, map_one]

/-- In a `CliffordAlgebra Q`-module, applying a vector with `Q v = -1` twice negates every
element. -/
theorem map_cliffordAlgebraι_apply_self_of_eq_neg_one
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W) {v : M} (hv : Q v = -1) (w : W) :
    ρ (ι Q v) (ρ (ι Q v) w) = -w := by
  rw [ρ.map_cliffordAlgebraι_apply_self, hv, neg_one_smul]

/-- Under any algebra homomorphism out of `CliffordAlgebra Q`, the anticommutator of two vectors is
the scalar `polar Q u v`. -/
theorem map_cliffordAlgebraι_mul_add_swap (ρ : CliffordAlgebra Q →ₐ[K] A) (u v : M) :
    ρ (ι Q u) * ρ (ι Q v) + ρ (ι Q v) * ρ (ι Q u) = algebraMap K A (QuadraticMap.polar Q u v) := by
  calc
    ρ (ι Q u) * ρ (ι Q v) + ρ (ι Q v) * ρ (ι Q u) = ρ (ι Q u * ι Q v + ι Q v * ι Q u) := by
      simp [map_add, map_mul]
    _ = algebraMap K A (QuadraticMap.polar Q u v) := by
      rw [ι_mul_ι_add_swap, AlgHom.commutes]

/-- Orthogonal vectors anticommute under any algebra homomorphism out of `CliffordAlgebra Q`. -/
theorem map_cliffordAlgebraι_anticommute_of_isOrtho (ρ : CliffordAlgebra Q →ₐ[K] A)
    {u v : M} (huv : Q.IsOrtho u v) :
    ρ (ι Q u) * ρ (ι Q v) + ρ (ι Q v) * ρ (ι Q u) = 0 := by
  have hpol : QuadraticMap.polar Q u v = 0 := by
    rw [QuadraticMap.polar, huv]
    abel
  rw [ρ.map_cliffordAlgebraι_mul_add_swap, hpol, map_zero]

/-- Orthogonal vectors act as anticommuting endomorphisms on any `CliffordAlgebra Q`-module. -/
theorem map_cliffordAlgebraι_apply_anticommute_of_isOrtho
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W) {u v : M} (huv : Q.IsOrtho u v) (w : W) :
    ρ (ι Q u) (ρ (ι Q v) w) + ρ (ι Q v) (ρ (ι Q u) w) = 0 := by
  have h := congrArg (fun T : Module.End K W ↦ T w)
    (ρ.map_cliffordAlgebraι_anticommute_of_isOrtho huv)
  simpa only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.zero_apply] using h

end CliffordRelations

end AlgHom

namespace TauCeti

section SkewOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A skew-symmetric map on a real inner product space sends every vector to an orthogonal vector:
`⟪f x, x⟫ = 0`. -/
theorem inner_apply_self_eq_zero_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    ⟪f x, x⟫_ℝ = 0 := by
  have h₁ := hf x x
  have h₂ := real_inner_comm x (f x)
  linarith

/-- A skew-symmetric map on a real inner product space satisfies `⟪x, f x⟫ = 0`. -/
theorem inner_self_apply_eq_zero_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    ⟪x, f x⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_apply_self_eq_zero_of_skew hf]

/-- For a skew-symmetric map `f` on a real inner product space, `f x` lies in `(ℝ ∙ x)ᗮ`. -/
theorem mem_orthogonal_span_singleton_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    f x ∈ (ℝ ∙ x)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_self_apply_eq_zero_of_skew hf x)

/-- A skew-symmetric map satisfying `f (f y) = -y` preserves the inner product. -/
theorem inner_apply_apply_of_skew_of_sq_neg_id {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hsq : ∀ x, f (f x) = -x) (x y : E) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [hf, hsq, inner_neg_right, neg_neg]

/-- A skew-symmetric map satisfying `f (f x) = -x` preserves norms. -/
theorem norm_apply_of_skew_of_sq_neg_id {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hsq : ∀ x, f (f x) = -x) (x : E) :
    ‖f x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    inner_apply_apply_of_skew_of_sq_neg_id hf hsq]

/-- Two anticommuting skew-symmetric maps on a real inner product space take orthogonal values at
every vector `x`. -/
theorem inner_apply_apply_eq_zero_of_skew_anticommute {f g : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hg : ∀ x y, ⟪g x, y⟫_ℝ = -⟪x, g y⟫_ℝ)
    (hanti : ∀ x, f (g x) + g (f x) = 0) (x : E) :
    ⟪f x, g x⟫_ℝ = 0 := by
  have h₁ := hf x (g x)
  have h₂ := hg (f x) x
  have h₃ := real_inner_comm (g (f x)) x
  have hsum : ⟪x, f (g x)⟫_ℝ + ⟪x, g (f x)⟫_ℝ = 0 := by
    rw [← inner_add_right, hanti x, inner_zero_right]
  linarith

/-- Evaluating a family of pairwise anticommuting skew-symmetric maps squaring to `-1` at a unit
vector produces an orthonormal family in `E`. -/
theorem orthonormal_apply_of_skew_anticommute {ι : Type*} {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ (fun i ↦ A i x) :=
  ⟨fun i ↦ (norm_apply_of_skew_of_sq_neg_id (hskew i) (hsq i) x).trans hx,
    fun {i j} hij ↦ inner_apply_apply_eq_zero_of_skew_anticommute (hskew i) (hskew j)
      (hanti i j hij) x⟩

/-- Evaluating a family of pairwise anticommuting skew-symmetric maps squaring to `-1` at a unit
vector `x` produces an orthonormal family in `(ℝ ∙ x)ᗮ`. -/
theorem orthonormal_orthogonal_of_skew_anticommute {ι : Type*} {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ
      (fun i ↦ (⟨A i x, mem_orthogonal_span_singleton_of_skew (hskew i) x⟩ : (ℝ ∙ x)ᗮ)) := by
  have horth := orthonormal_apply_of_skew_anticommute hskew hsq hanti hx
  exact ⟨fun i ↦ horth.1 i, fun {i j} hij ↦ horth.2 hij⟩

/-- When `finrank ℝ E = card ι + 1`, a family of `card ι` pairwise anticommuting skew-symmetric
maps squaring to `-1` evaluates at each unit vector `x` to an orthonormal basis of `(ℝ ∙ x)ᗮ`. -/
noncomputable def orthonormalBasisOrthogonalOfSkewFamily {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : Module.finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) :
    OrthonormalBasis ι ℝ (ℝ ∙ x)ᗮ := by
  have : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [hrank]; exact Nat.succ_pos _)
  let : Fact (Module.finrank ℝ E = Fintype.card ι + 1) := ⟨hrank⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  have hcard : Fintype.card ι = Module.finrank ℝ (ℝ ∙ x)ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) hx0).symm
  let v : ι → (ℝ ∙ x)ᗮ := fun i ↦ ⟨A i x, mem_orthogonal_span_singleton_of_skew (hskew i) x⟩
  have hv : Orthonormal ℝ v := orthonormal_orthogonal_of_skew_anticommute hskew hsq hanti hx
  exact (basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent hcard).toOrthonormalBasis
    (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)

/-- Each vector of `TauCeti.orthonormalBasisOrthogonalOfSkewFamily` coerces in `E` to `A i x`. -/
@[simp]
theorem coe_orthonormalBasisOrthogonalOfSkewFamily_apply {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : Module.finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (i : ι) :
    ((orthonormalBasisOrthogonalOfSkewFamily hskew hsq hanti hrank hx i : (ℝ ∙ x)ᗮ) : E) =
      A i x := by
  simp [orthonormalBasisOrthogonalOfSkewFamily]

/-- Coordinates in `TauCeti.orthonormalBasisOrthogonalOfSkewFamily` are inner products against
`A i x` in the ambient space `E`. -/
@[simp]
theorem orthonormalBasisOrthogonalOfSkewFamily_repr_apply {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : Module.finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (v : (ℝ ∙ x)ᗮ) (i : ι) :
    (orthonormalBasisOrthogonalOfSkewFamily hskew hsq hanti hrank hx).repr v i =
      ⟪A i x, (v : E)⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply, Submodule.coe_inner,
    coe_orthonormalBasisOrthogonalOfSkewFamily_apply]

end SkewOperators

section EuclideanCliffordModules

/-- Any finite-dimensional real module `W` over `CliffordAlgebra Q`, where `Q` has a finite
orthogonal basis squaring to `-1`, transfers to a skew-adjoint continuous-linear Clifford action on
any finite-dimensional real inner product space `E` of the same dimension. -/
theorem exists_skewAdjoint_cliffordAction_of_finrank_eq
    {M W E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W)
    {I : Type*} [Finite I] (b : Module.Basis I ℝ M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ σ : CliffordAlgebra Q →ₐ[ℝ] (E →L[ℝ] E),
      ∀ (v : M) (x y : E), ⟪σ (ι Q v) x, y⟫_ℝ = -⟪x, σ (ι Q v) y⟫_ℝ := by
  let w := Module.finBasis ℝ W
  let Q₀ : QuadraticForm ℝ W :=
    (QuadraticMap.weightedSumSquares ℝ (1 : Fin (Module.finrank ℝ W) → ℝ)).comp
      w.equivFun.toLinearMap
  have hQ₀ : Q₀.PosDef :=
    ((QuadraticMap.posDef_weightedSumSquares_iff _).mpr fun _ ↦ zero_lt_one).comp
      w.equivFun.toLinearMap w.equivFun.injective
  obtain ⟨B, hBpos, hBsymm, hBskew⟩ :=
    ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι b hb hQ hQ₀
  -- Equip `W` with the averaged positive-definite symmetric form, then transport to `E`.
  let core : InnerProductSpace.Core ℝ W :=
    { inner x y := B x y
      conj_inner_symm x y := by simpa using hBsymm.eq y x
      re_inner_nonneg x := by simpa using hBpos.nonneg x
      add_left x y z := by simp
      smul_left x y r := by simp
      definite x hx := hBpos.anisotropic x (by simpa using hx) }
  let := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  have hinner (x y : W) : inner ℝ x y = B x y := (rfl)
  let U : W ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ W).repr.trans
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim.symm)).repr.symm
  let toCLM : Module.End ℝ E →ₐ[ℝ] (E →L[ℝ] E) :=
    { toFun := LinearMap.toContinuousLinearMap
      map_zero' := ContinuousLinearMap.ext fun _ ↦ rfl
      map_add' _ _ := ContinuousLinearMap.ext fun _ ↦ rfl
      map_one' := ContinuousLinearMap.ext fun _ ↦ rfl
      map_mul' _ _ := ContinuousLinearMap.ext fun _ ↦ rfl
      commutes' _ := ContinuousLinearMap.ext fun _ ↦ rfl }
  let conjU : Module.End ℝ W ≃ₐ[ℝ] Module.End ℝ E := U.toLinearEquiv.conjAlgEquiv ℝ
  refine ⟨toCLM.comp (conjU.toAlgHom.comp ρ), fun v x y ↦ ?_⟩
  have hskewv : B (ρ (ι Q v) (U.symm x)) (U.symm y) = -B (U.symm x) (ρ (ι Q v) (U.symm y)) := by
    simpa only [Pi.neg_apply, map_neg] using hBskew v (U.symm x) (U.symm y)
  have happly (z : E) :
      (toCLM.comp (conjU.toAlgHom.comp ρ)) (ι Q v) z = U (ρ (ι Q v) (U.symm z)) := (rfl)
  rw [happly, happly]
  calc
    ⟪U (ρ (ι Q v) (U.symm x)), y⟫_ℝ = ⟪U (ρ (ι Q v) (U.symm x)), U (U.symm y)⟫_ℝ := by
      rw [U.apply_symm_apply]
    _ = B (ρ (ι Q v) (U.symm x)) (U.symm y) := by rw [U.inner_map_map, hinner]
    _ = -B (U.symm x) (ρ (ι Q v) (U.symm y)) := hskewv
    _ = -⟪U (U.symm x), U (ρ (ι Q v) (U.symm y))⟫_ℝ := by rw [U.inner_map_map, hinner]
    _ = -⟪x, U (ρ (ι Q v) (U.symm y))⟫_ℝ := by rw [U.apply_symm_apply]

/-- A finite-dimensional real module `W` over `Cliff(0, q)` induces `q` skew-symmetric
anticommuting continuous linear endomorphisms squaring to `-1` on any real inner product space `E`
of the same finite dimension. -/
theorem exists_skewAdjoint_anticommuting_clm_of_cliffordModule {q : ℕ}
    {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra (realCliffordForm 0 q) →ₐ[ℝ] Module.End ℝ W)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ A : Fin q → (E →L[ℝ] E),
      (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) ∧
      (∀ i x, A i (A i x) = -x) ∧
      (∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) := by
  let b : Module.Basis (Fin (0 + q)) ℝ (Fin (0 + q) → ℝ) := Pi.basisFun ℝ (Fin (0 + q))
  have hb : ∀ i j, i ≠ j → (realCliffordForm 0 q).IsOrtho (b i) (b j) := fun i j hij ↦ by
    simpa [b] using isOrtho_realCliffordForm_single hij 1 1
  have hQ : ∀ i, realCliffordForm 0 q (b i) = -1 := fun i ↦ by
    simp [b]
  obtain ⟨σ, hσ⟩ := exists_skewAdjoint_cliffordAction_of_finrank_eq ρ b hb hQ hdim
  let e : Fin q → Fin (0 + q) := Fin.cast (Nat.zero_add q).symm
  refine ⟨fun i ↦ σ (ι (realCliffordForm 0 q) (b (e i))), fun i ↦ hσ _, fun i x ↦ ?_,
    fun i j hij x ↦ ?_⟩
  · have hsq := congrArg (fun T : E →L[ℝ] E ↦ T x)
      (σ.map_cliffordAlgebraι_mul_self_of_eq_neg_one (hQ (e i)))
    simpa only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] using hsq
  · have heij : e i ≠ e j := fun h ↦ hij ((Fin.cast_injective _) h)
    have hanti := congrArg (fun T : E →L[ℝ] E ↦ T x)
      (σ.map_cliffordAlgebraι_anticommute_of_isOrtho (hb (e i) (e j) heij))
    simpa only [add_apply, mul_apply_eq_comp, zero_apply] using hanti

private noncomputable def cliffordModuleZeroOne :
    CliffordAlgebra (realCliffordForm 0 1) →ₐ[ℝ] Module.End ℝ ℂ :=
  (Algebra.lmul ℝ ℂ).comp realCliffordZeroOneEquivComplex.toAlgHom

private noncomputable def cliffordModuleZeroThree :
    CliffordAlgebra (realCliffordForm 0 3) →ₐ[ℝ] Module.End ℝ ℍ[ℝ] :=
  (Algebra.lmul ℝ ℍ[ℝ]).comp
    ((AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ]).comp realCliffordZeroThreeEquivQuaternionProd.toAlgHom)

private theorem nonempty_cliffordModule_zero_seven :
    Nonempty (CliffordAlgebra (realCliffordForm 0 7) →ₐ[ℝ] Module.End ℝ (Fin 8 → ℝ)) := by
  obtain ⟨e⟩ := realClifford_classification_of_residue_eq_seven 0 7
    (by rw [realCliffordResidue_def])
  exact ⟨(Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin 8)).toAlgHom.comp
    ((AlgHom.fst ℝ (Matrix (Fin 8) (Fin 8) ℝ) (Matrix (Fin 8) (Fin 8) ℝ)).comp e.toAlgHom)⟩

/-- For `n ∈ {1, 3, 7}`, every `(n + 1)`-dimensional real inner product space `E` admits `n`
pairwise anticommuting skew-symmetric continuous linear endomorphisms squaring to `-1`. These arise
from the real Clifford algebras `Cliff(0, 1) ≃ₐ[ℝ] ℂ`, `Cliff(0, 3) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`, and
`Cliff(0, 7) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)`. -/
theorem exists_skewAdjoint_anticommuting_clm {n : ℕ}
    (hn : n = 1 ∨ n = 3 ∨ n = 7)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : Module.finrank ℝ E = n + 1) :
    ∃ A : Fin n → (E →L[ℝ] E),
      (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) ∧
      (∀ i x, A i (A i x) = -x) ∧
      (∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) := by
  have : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [hE]; exact Nat.succ_pos n)
  rcases hn with rfl | rfl | rfl
  · exact exists_skewAdjoint_anticommuting_clm_of_cliffordModule cliffordModuleZeroOne
      (Complex.finrank_real_complex.trans hE.symm)
  · exact exists_skewAdjoint_anticommuting_clm_of_cliffordModule cliffordModuleZeroThree
      (Quaternion.finrank_eq_four.trans hE.symm)
  · obtain ⟨ρ⟩ := nonempty_cliffordModule_zero_seven
    exact exists_skewAdjoint_anticommuting_clm_of_cliffordModule ρ
      ((by rw [Module.finrank_fin_fun] : Module.finrank ℝ (Fin 8 → ℝ) = 8).trans hE.symm)

end EuclideanCliffordModules

end TauCeti
