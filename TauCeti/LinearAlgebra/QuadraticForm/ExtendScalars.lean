/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.MvPolynomial
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import TauCeti.Data.Matrix.DotProduct

/-!
# Coordinate scalar extension of quadratic forms

For a commutative ring `K`, a commutative `K`-algebra `L` and a quadratic form `Q` on `ι → K`
with `ι` finite, `QuadraticForm.extendScalars L Q` is the quadratic form on `ι → L` given by the
coordinate polynomial of `Q` with its coefficients mapped into `L`:
`x ↦ ∑ᵢ Q(eᵢ) xᵢ² + ∑_{i<j} b_Q(eᵢ, eⱼ) xᵢ xⱼ`, where `b_Q` is the polar form
(Elman--Karpenko--Merkurjev, §7, before Lemma 7.15).

Mathlib's `QuadraticForm.baseChange` needs `2` to be invertible, because it is built from the
associated symmetric bilinear form. The coordinate extension needs no such hypothesis, so it is
the scalar extension used for quadratic forms in characteristic two. A form on an arbitrary space
with a finite basis `b` is extended through its coordinate form `Q.basisRepr b`; the result does
not depend on the basis up to isometry.

The construction extends the Gram matrix of any bilinear form `B` with `B x x = Q x`. The
extension is characterized by its values on vectors with coordinates in `K`
(`QuadraticForm.extendScalars_apply_algebraMap_comp`), because an `L`-quadratic map on `ι → L` is
determined by those values (`QuadraticMap.ext_algebraMap_comp`); every other property below is
derived from this characterization. Anisotropy is not preserved in general: the norm form
`x² + x y + y²` of `𝔽₄ / 𝔽₂` is anisotropic over `𝔽₂` and isotropic over `𝔽₄`.

## Main definitions

* `QuadraticForm.extendScalars L Q`: the coordinate scalar extension of `Q` to `L`.
* `QuadraticMap.IsometryEquiv.extendScalars`: the isometry of extensions induced by an isometry.

## Main results

* `QuadraticMap.ext_algebraMap_comp`: a quadratic map on `ι → L` is determined by its values on
  vectors with coordinates in `K`.
* `QuadraticForm.extendScalars_toQuadraticMap`: the extension of `x ↦ B x x` is read off the Gram
  matrix of `B` mapped into `L`, for every bilinear form `B`.
* `QuadraticForm.extendScalars_apply`, `QuadraticForm.toMvPolynomial_extendScalars`: the
  coordinate formula for the extension; its coordinate polynomial is that of `Q` with the
  coefficients mapped into `L`.
* `QuadraticForm.extendScalars_apply_algebraMap_comp`, `QuadraticForm.extendScalars_smul_apply`:
  the extension agrees with `Q` on `K`-points and scales by `c²` along scalars.
* `QuadraticForm.toMatrix'_polarBilin_extendScalars`: the Gram matrix of the polar form of the
  extension is the image of the Gram matrix of the polar form of `Q`.
* `QuadraticForm.extendScalars_self`, `QuadraticForm.extendScalars_extendScalars`: extension to
  `K` is the identity, and extensions along a tower `K → L → M` compose.
* `QuadraticForm.extendScalars_prod`: the extension of an orthogonal sum is the orthogonal sum of
  the extensions.
* `QuadraticForm.extendScalars_binaryQuadraticForm`: the extension of `[a, b]` is `[a, b]`; in
  particular the hyperbolic plane `x y` extends to the hyperbolic plane.
* `QuadraticForm.extendScalars_weightedSumSquares`: the extension of a diagonal form is
  diagonal.
* `QuadraticMap.Equivalent.extendScalars`: isometric forms have isometric extensions.
* `QuadraticForm.nondegenerate_polarBilin_extendScalars_iff`: along an injective map of domains,
  in particular over fields, extension preserves and reflects nonsingularity.
* `QuadraticForm.equivalent_extendScalars_basisRepr`: independence of the chosen basis.
* `QuadraticForm.not_anisotropic_extendScalars`: isotropy persists under extension.
* `QuadraticForm.isometryEquivBaseChangeExtendScalars`: with `2` invertible, the extension is
  isometric to Mathlib's `QuadraticForm.baseChange`.

## References

* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  §7.
-/

public section

noncomputable section

open scoped TensorProduct

open LinearMap (BilinForm)

open QuadraticMap

/-- The identification `L ⊗[K] (ι → K) ≃ (ι → L)` sends `1 ⊗ v` to `v` read in `ι → L`. -/
private theorem piScalarRight_one_tmul {K L ι : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] (v : ι → K) :
    TensorProduct.piScalarRight K L L ι (1 ⊗ₜ v) = algebraMap K L ∘ v := by
  ext i
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.algebraMap_eq_smul_one]

namespace QuadraticMap

variable {K L N ι : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable [AddCommGroup N] [Module L N] [Finite ι]

/-- A quadratic map on `ι → L` is determined by its values on vectors with coordinates in
`K`. -/
theorem ext_algebraMap_comp ⦃Q₁ Q₂ : QuadraticMap L (ι → L) N⦄
    (h : ∀ v : ι → K, Q₁ (algebraMap K L ∘ v) = Q₂ (algebraMap K L ∘ v)) : Q₁ = Q₂ := by
  classical
  have := Fintype.ofFinite ι
  -- `baseChange_ext` needs `N` as a `K`-module; restrict its scalars along `K → L`.
  let : Module K N := Module.compHom N (algebraMap K L)
  have : IsScalarTower K L N := IsScalarTower.of_compHom K L N
  have hcomp : Q₁.comp (TensorProduct.piScalarRight K L L ι).toLinearMap =
      Q₂.comp (TensorProduct.piScalarRight K L L ι).toLinearMap :=
    baseChange_ext fun v ↦ by
      rw [comp_apply, comp_apply, LinearEquiv.coe_toLinearMap, piScalarRight_one_tmul]
      exact h v
  ext x
  simpa using DFunLike.congr_fun hcomp ((TensorProduct.piScalarRight K L L ι).symm x)

end QuadraticMap

namespace QuadraticForm

section CommRing

variable {K : Type*} (L : Type*) [CommRing K] [CommRing L] [Algebra K L]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The coordinate scalar extension of a quadratic form `Q` on `ι → K` to a commutative
`K`-algebra `L`: the quadratic form on `ι → L` whose coordinate polynomial is that of `Q` with
coefficients mapped into `L`, `x ↦ ∑ᵢ Q(eᵢ) xᵢ² + ∑_{i<j} b_Q(eᵢ, eⱼ) xᵢ xⱼ`
(`QuadraticForm.extendScalars_apply`).

It is built from the Gram matrix of a bilinear form `B` with `B x x = Q x`; the result does not
depend on the choice of `B` (`QuadraticForm.extendScalars_toQuadraticMap`). Unlike
`QuadraticForm.baseChange`, it does not need `2` to be invertible. -/
def extendScalars (Q : QuadraticForm K (ι → K)) : QuadraticForm L (ι → L) :=
  (Matrix.toBilin' ((BilinForm.toMatrix'
    (LinearMap.BilinMap.toQuadraticMap_surjective Q).choose).map (algebraMap K L))).toQuadraticMap

/-- The extension agrees with `Q` on vectors with coordinates in `K`. This characterizes the
extension, by `QuadraticMap.ext_algebraMap_comp`. -/
@[simp]
theorem extendScalars_apply_algebraMap_comp (Q : QuadraticForm K (ι → K)) (v : ι → K) :
    extendScalars L Q (algebraMap K L ∘ v) = algebraMap K L (Q v) := by
  rw [extendScalars, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply',
    ← RingHom.map_dotProduct_mulVec, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix',
    ← LinearMap.BilinMap.toQuadraticMap_apply,
    (LinearMap.BilinMap.toQuadraticMap_surjective Q).choose_spec]

/-- A quadratic form on `ι → L` which agrees with `Q` on vectors with coordinates in `K` is the
extension of `Q`. -/
theorem eq_extendScalars_iff {Q : QuadraticForm K (ι → K)} {Q' : QuadraticForm L (ι → L)} :
    Q' = extendScalars L Q ↔ ∀ v : ι → K, Q' (algebraMap K L ∘ v) = algebraMap K L (Q v) :=
  ⟨fun h v ↦ by rw [h, extendScalars_apply_algebraMap_comp],
    fun h ↦ QuadraticMap.ext_algebraMap_comp fun v ↦ by
      rw [h, extendScalars_apply_algebraMap_comp]⟩

/-- The extension scales by `c²` along the scalar multiples of a vector with coordinates in `K`:
`(extendScalars L Q)(c ⊗ v) = c² Q(v)`. -/
theorem extendScalars_smul_apply (Q : QuadraticForm K (ι → K)) (c : L) (v : ι → K) :
    extendScalars L Q (c • (algebraMap K L ∘ v)) = c ^ 2 * algebraMap K L (Q v) := by
  rw [QuadraticMap.map_smul, extendScalars_apply_algebraMap_comp, smul_eq_mul, pow_two]

/-- The extension of `B x x` is computed by extending the Gram matrix of `B`, for every bilinear
form `B`: the definition of `QuadraticForm.extendScalars` does not depend on the chosen bilinear
form. -/
theorem extendScalars_toQuadraticMap (B : BilinForm K (ι → K)) :
    extendScalars L B.toQuadraticMap =
      (Matrix.toBilin' ((BilinForm.toMatrix' B).map (algebraMap K L))).toQuadraticMap := by
  refine ((eq_extendScalars_iff L).2 fun v ↦ ?_).symm
  rw [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply',
    ← RingHom.map_dotProduct_mulVec, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix',
    LinearMap.BilinMap.toQuadraticMap_apply]

/-- The coordinate formula for the extension:
`x ↦ ∑ᵢ Q(eᵢ) xᵢ² + ∑_{i<j} b_Q(eᵢ, eⱼ) xᵢ xⱼ`, with the coefficients mapped into `L`. -/
theorem extendScalars_apply [LinearOrder ι] (Q : QuadraticForm K (ι → K)) (x : ι → L) :
    extendScalars L Q x =
      ∑ i, algebraMap K L (Q (Pi.single i 1)) * x i ^ 2 +
        ∑ i, ∑ j with i < j,
          algebraMap K L (polar Q (Pi.single i 1) (Pi.single j 1)) * x i * x j := by
  conv_lhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q (Pi.basisFun K ι)]
  rw [extendScalars_toQuadraticMap, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply]
  simp only [Matrix.map_apply, BilinForm.toMatrix'_apply]
  simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsplit (j : ι) : x i * algebraMap K L
      (Q.toBilin (Pi.basisFun K ι) (Pi.single i 1) (Pi.single j 1)) * x j =
      (if i = j then algebraMap K L (Q (Pi.single i 1)) * x i ^ 2 else 0) +
        if i < j then algebraMap K L (polar Q (Pi.single i 1) (Pi.single j 1)) * x i * x j
        else 0 := by
    rw [← Pi.basisFun_apply K ι i, ← Pi.basisFun_apply K ι j, QuadraticMap.toBilin_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [h, h.ne, ite_false, ite_true, zero_add]
      ring
    · simp only [ite_true, lt_irrefl, ite_false, add_zero]
      ring
    · simp [h.ne', h.not_gt]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype ι] in
variable (K) in
/-- A standard basis vector of `ι → L` has its coordinates in `K`. -/
private theorem single_one_eq_algebraMap_comp (k : ι) :
    (Pi.single k 1 : ι → L) = algebraMap K L ∘ Pi.single k 1 := by
  ext l
  by_cases h : l = k <;> simp [h]

/-- The polar form of the extension agrees with the polar form of `Q` on vectors with
coordinates in `K`. -/
@[simp]
theorem polar_extendScalars_algebraMap_comp (Q : QuadraticForm K (ι → K)) (v w : ι → K) :
    polar (extendScalars L Q) (algebraMap K L ∘ v) (algebraMap K L ∘ w) =
      algebraMap K L (polar Q v w) := by
  have hadd : algebraMap K L ∘ v + algebraMap K L ∘ w = algebraMap K L ∘ (v + w) := by
    ext i
    simp
  simp only [polar, hadd, extendScalars_apply_algebraMap_comp, map_sub]

/-- The Gram matrix of the polar form of the extension is the image of the Gram matrix of the
polar form of `Q`. -/
theorem toMatrix'_polarBilin_extendScalars (Q : QuadraticForm K (ι → K)) :
    BilinForm.toMatrix' (polarBilin (extendScalars L Q)) =
      (BilinForm.toMatrix' (polarBilin Q)).map (algebraMap K L) := by
  ext i j
  rw [Matrix.map_apply, BilinForm.toMatrix'_apply, BilinForm.toMatrix'_apply,
    polarBilin_apply_apply, polarBilin_apply_apply, single_one_eq_algebraMap_comp K L i,
    single_one_eq_algebraMap_comp K L j, polar_extendScalars_algebraMap_comp]

/-- The coordinate polynomial of the extension is the coordinate polynomial of `Q` with its
coefficients mapped into `L`. -/
theorem toMvPolynomial_extendScalars (Q : QuadraticForm K (ι → K)) :
    (extendScalars L Q).toMvPolynomial = MvPolynomial.map (algebraMap K L) Q.toMvPolynomial := by
  rw [toMvPolynomial_def, toMvPolynomial_def, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [single_one_eq_algebraMap_comp K L i, extendScalars_apply_algebraMap_comp]
    simp
  · refine Finset.sum_congr rfl fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      simp only [Sym2.lift_mk]
      rw [single_one_eq_algebraMap_comp K L i,
        single_one_eq_algebraMap_comp K L j, polar_extendScalars_algebraMap_comp]
      simp

/-- Extending scalars from `K` to itself does nothing. -/
@[simp]
theorem extendScalars_self (Q : QuadraticForm K (ι → K)) : extendScalars K Q = Q :=
  ((eq_extendScalars_iff K).2 fun v ↦ by simp).symm

/-- Extending scalars along a tower `K → L → M` in two steps is extending them in one step. -/
theorem extendScalars_extendScalars (M : Type*) [CommRing M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (Q : QuadraticForm K (ι → K)) :
    extendScalars M (extendScalars L Q) = extendScalars M Q := by
  refine (eq_extendScalars_iff M).2 fun v ↦ ?_
  have hcomp : algebraMap K M ∘ v = algebraMap L M ∘ (algebraMap K L ∘ v) := by
    ext i
    simp [← IsScalarTower.algebraMap_apply]
  rw [hcomp, extendScalars_apply_algebraMap_comp, extendScalars_apply_algebraMap_comp,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem extendScalars_zero : extendScalars L (0 : QuadraticForm K (ι → K)) = 0 :=
  ((eq_extendScalars_iff L).2 fun v ↦ by simp).symm

@[simp]
theorem extendScalars_add (Q₁ Q₂ : QuadraticForm K (ι → K)) :
    extendScalars L (Q₁ + Q₂) = extendScalars L Q₁ + extendScalars L Q₂ :=
  ((eq_extendScalars_iff L).2 fun v ↦ by simp).symm

@[simp]
theorem extendScalars_smul (c : K) (Q : QuadraticForm K (ι → K)) :
    extendScalars L (c • Q) = algebraMap K L c • extendScalars L Q :=
  ((eq_extendScalars_iff L).2 fun v ↦ by simp [Algebra.smul_def]).symm

/-- The extension of a diagonal form is the diagonal form with the coefficients mapped into
`L`. -/
@[simp]
theorem extendScalars_weightedSumSquares (w : ι → K) :
    extendScalars L (weightedSumSquares K w) = weightedSumSquares L (algebraMap K L ∘ w) :=
  ((eq_extendScalars_iff L).2 fun v ↦ by simp [weightedSumSquares_apply]).symm

/-- The extension of the binary form `[a, b] = a x² + x y + b y²` is `[a, b]` with the
coefficients mapped into `L`; the mixed term `x y` survives. In particular the hyperbolic plane
`x y = [0, 0]` extends to the hyperbolic plane. -/
@[simp]
theorem extendScalars_binaryQuadraticForm (a b : K) :
    extendScalars L (TauCeti.binaryQuadraticForm K a b) =
      TauCeti.binaryQuadraticForm L (algebraMap K L a) (algebraMap K L b) :=
  ((eq_extendScalars_iff L).2 fun v ↦ by simp [TauCeti.binaryQuadraticForm_apply]).symm

/-- The extension of an orthogonal sum `Q₁ ⊥ Q₂`, written in the coordinates `ι ⊕ κ`, is the
orthogonal sum of the extensions. -/
theorem extendScalars_prod (Q₁ : QuadraticForm K (ι → K)) (Q₂ : QuadraticForm K (κ → K)) :
    extendScalars L
        ((Q₁.prod Q₂).comp (LinearEquiv.sumArrowLequivProdArrow ι κ K K).toLinearMap) =
      ((extendScalars L Q₁).prod (extendScalars L Q₂)).comp
        (LinearEquiv.sumArrowLequivProdArrow ι κ L L).toLinearMap := by
  refine ((eq_extendScalars_iff L).2 fun v ↦ ?_).symm
  simp [LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow, Function.comp_assoc]

/-- An isometry `Q₁ ≅ Q₂` of quadratic forms on coordinate spaces induces an isometry of their
extensions to `L`. The underlying linear equivalence is the base change of the given one,
transported to coordinates; it carries `algebraMap K L ∘ v` to `algebraMap K L ∘ e v`. -/
def _root_.QuadraticMap.IsometryEquiv.extendScalars {Q₁ : QuadraticForm K (ι → K)}
    {Q₂ : QuadraticForm K (κ → K)} (e : Q₁.IsometryEquiv Q₂) :
    (QuadraticForm.extendScalars L Q₁).IsometryEquiv (QuadraticForm.extendScalars L Q₂) where
  toLinearEquiv := (TensorProduct.piScalarRight K L L ι).symm ≪≫ₗ
    LinearEquiv.baseChange K L _ _ e.toLinearEquiv ≪≫ₗ TensorProduct.piScalarRight K L L κ
  map_app' x := by
    have h : (QuadraticForm.extendScalars L Q₂).comp
        ((TensorProduct.piScalarRight K L L ι).symm ≪≫ₗ
          LinearEquiv.baseChange K L _ _ e.toLinearEquiv ≪≫ₗ
            TensorProduct.piScalarRight K L L κ).toLinearMap =
          QuadraticForm.extendScalars L Q₁ := by
      refine (eq_extendScalars_iff L).2 fun v ↦ ?_
      rw [QuadraticMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
        LinearEquiv.trans_apply, ← piScalarRight_one_tmul, LinearEquiv.symm_apply_apply,
        LinearEquiv.baseChange_tmul, piScalarRight_one_tmul, extendScalars_apply_algebraMap_comp,
        QuadraticMap.IsometryEquiv.coe_toLinearEquiv, e.map_app]
    exact DFunLike.congr_fun h x

/-- The induced isometry of extensions carries a vector with coordinates in `K` to the image of
that vector. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.extendScalars_apply_algebraMap_comp
    {Q₁ : QuadraticForm K (ι → K)} {Q₂ : QuadraticForm K (κ → K)} (e : Q₁.IsometryEquiv Q₂)
    (v : ι → K) : e.extendScalars L (algebraMap K L ∘ v) = algebraMap K L ∘ e v := by
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  simp only [QuadraticMap.IsometryEquiv.extendScalars, LinearEquiv.trans_apply]
  rw [← piScalarRight_one_tmul, LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    piScalarRight_one_tmul, QuadraticMap.IsometryEquiv.coe_toLinearEquiv]

/-- Isometric forms have isometric extensions. -/
theorem _root_.QuadraticMap.Equivalent.extendScalars {Q₁ : QuadraticForm K (ι → K)}
    {Q₂ : QuadraticForm K (κ → K)} (h : Q₁.Equivalent Q₂) :
    (QuadraticForm.extendScalars L Q₁).Equivalent (QuadraticForm.extendScalars L Q₂) :=
  let ⟨e⟩ := h
  ⟨e.extendScalars L⟩

/-- The extension of a form on a space with a finite basis, computed in the coordinates of a
basis, does not depend on the basis up to isometry. -/
theorem equivalent_extendScalars_basisRepr {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) :
    (extendScalars L (Q.basisRepr b)).Equivalent (extendScalars L (Q.basisRepr b')) :=
  ⟨((Q.isometryEquivBasisRepr b).symm.trans (Q.isometryEquivBasisRepr b')).extendScalars L⟩

/-- If `Q` is isotropic over `K`, then its extension is isotropic over any faithful
`K`-algebra. -/
theorem not_anisotropic_extendScalars [FaithfulSMul K L] {Q : QuadraticForm K (ι → K)}
    (hQ : ¬ Q.Anisotropic) : ¬ (extendScalars L Q).Anisotropic := by
  intro h
  refine hQ fun v hv ↦ ?_
  have hinj := FaithfulSMul.algebraMap_injective K L
  have : algebraMap K L ∘ v = 0 := h _ (by rw [extendScalars_apply_algebraMap_comp, hv, map_zero])
  ext i
  exact hinj (by simpa using congr_fun this i)

/-- With `2` invertible, the coordinate extension is isometric to Mathlib's
`QuadraticForm.baseChange`, through the identification `L ⊗[K] (ι → K) ≃ (ι → L)`. -/
def isometryEquivBaseChangeExtendScalars [Invertible (2 : K)] (Q : QuadraticForm K (ι → K)) :
    (Q.baseChange L).IsometryEquiv (extendScalars L Q) where
  toLinearEquiv := TensorProduct.piScalarRight K L L ι
  map_app' x := by
    have h : (extendScalars L Q).comp (TensorProduct.piScalarRight K L L ι).toLinearMap =
        Q.baseChange L :=
      baseChange_ext fun v ↦ by
        rw [QuadraticMap.comp_apply, LinearEquiv.coe_toLinearMap, piScalarRight_one_tmul,
          extendScalars_apply_algebraMap_comp, baseChange_tmul, mul_one,
          Algebra.algebraMap_eq_smul_one]
    exact DFunLike.congr_fun h x

@[simp]
theorem isometryEquivBaseChangeExtendScalars_tmul [Invertible (2 : K)]
    (Q : QuadraticForm K (ι → K)) (c : L) (v : ι → K) :
    isometryEquivBaseChangeExtendScalars L Q (c ⊗ₜ v) = c • (algebraMap K L ∘ v) := by
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  simp only [isometryEquivBaseChangeExtendScalars]
  ext i
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, mul_comm]

end CommRing

section IsDomain

variable {K : Type*} (L : Type*) [CommRing K] [IsDomain K] [CommRing L] [IsDomain L]
variable [Algebra K L] [FaithfulSMul K L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extension from a domain to a domain along an injective algebra map preserves and reflects
nonsingularity: the polar form of the extension is nondegenerate exactly when the polar form of
`Q` is. This covers every extension of fields. -/
theorem nondegenerate_polarBilin_extendScalars_iff {Q : QuadraticForm K (ι → K)} :
    (polarBilin (extendScalars L Q)).Nondegenerate ↔ (polarBilin Q).Nondegenerate := by
  refine BilinForm.nondegenerate_toMatrix'_iff.symm.trans
    (Iff.trans ?_ BilinForm.nondegenerate_toMatrix'_iff)
  rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.nondegenerate_iff_det_ne_zero,
    toMatrix'_polarBilin_extendScalars, ← (algebraMap K L).mapMatrix_apply,
    ← RingHom.map_det, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)]

end IsDomain

end QuadraticForm
