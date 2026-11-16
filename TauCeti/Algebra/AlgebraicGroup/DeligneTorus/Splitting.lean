/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.RingTheory.TensorProduct.Complex
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
import TauCeti.Algebra.AlgebraicGroup.Torus.Splitting

/-!
# Complex splitting and non-splitness of the Deligne torus

For every commutative complex algebra `R` equipped with a compatible real algebra structure
(`[Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]`), the `ℝ`-algebra isomorphism
`ℂ ⊗[ℝ] R ≃ₐ[ℝ] R × R` (`TauCeti.complexTensorProductEquiv`) identifies the `R`-points of the
Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` with `Rˣ × Rˣ` (`TauCeti.DeligneTorus.splittingMulEquiv`), sending
a pure tensor `z ⊗ r` to `(z • r, conj z • r)`. Specialising to `R = ℂ` gives Milne's splitting
`S(ℂ) ≃* ℂˣ × ℂˣ` (`TauCeti.DeligneTorus.complexSplitting`), under which:

* the inclusion `S(ℝ) → S(ℂ)` sends `z ∈ ℂˣ` to `(z, conj z)`
  (`TauCeti.DeligneTorus.complexSplitting_real`), so the real point `I` goes to `(I, -I)`
  (`TauCeti.DeligneTorus.complexSplitting_I`), whereas the scalar point `1 ⊗ I` goes to `(I, I)`
  (`TauCeti.DeligneTorus.complexSplitting_scalar`);
* complex conjugation on `S(ℂ)` sends `(z₁, z₂)` to `(conj z₂, conj z₁)`
  (`TauCeti.DeligneTorus.conj_swap`), cutting out `S(ℝ)` as its fixed locus
  (`TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`);
* the diagonal `d` sends `r` to `(r, r)`, the weight `w` sends `r` to `(r⁻¹, r⁻¹)`, and the
  product of the two components is the norm `Nm` (`TauCeti.DeligneTorus.splittingMulEquiv_diagonal`,
  `TauCeti.DeligneTorus.splittingMulEquiv_weight`,
  `TauCeti.DeligneTorus.fst_mul_snd_splittingMulEquiv`).

By the Yoneda lemma for commutative Hopf algebras (`TauCeti.CommHopfAlgCat.homOfPointsMap`), the
natural splitting of `R`-points lifts to the bialgebra isomorphism
`ℂ ⊗[ℝ] S ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` (`TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`) and
exhibits `S` as a rank-two algebraic torus over `ℝ`
(`TauCeti.DeligneTorus.torusCommHopfAlgProperty_S`). Over `ℝ` itself, however, `S` is not split
(`TauCeti.DeligneTorus.not_split`): `S(ℝ) ≃* ℂˣ` has infinitely many elements of finite order
(`TauCeti.DeligneTorus.infinite_isOfFinOrder_realPoints`), including `I` of order four, whereas in
any product `σ → ℝˣ` every element `g` satisfying `g ^ 4 = 1` already satisfies `g ^ 2 = 1`
(`TauCeti.DeligneTorus.isEmpty_realPoints_mulEquiv_pi`).

## Main definitions

* `TauCeti.DeligneTorus.splittingMulEquiv`: `S(R) ≃* Rˣ × Rˣ` for a commutative complex algebra `R`
  over `ℝ`.
* `TauCeti.DeligneTorus.complexSplitting`: `S(ℂ) ≃* ℂˣ × ℂˣ`.
* `TauCeti.DeligneTorus.baseChangeComplex`: the base change of `S` from `ℝ` to `ℂ` as a
  finite-type commutative Hopf `ℂ`-algebra, with point identification
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv`.
* `TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`: the coordinate bialgebra splitting
  `baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]`.
* `TauCeti.DeligneTorus.baseChangeSplitTorusIso`: the isomorphism identifying `baseChangeComplex`
  with the rank-two split torus, with point compatibility
  `TauCeti.DeligneTorus.pointsMulEquiv_mapDomain_baseChangeSplitTorusIso`.

## Main results

* `TauCeti.DeligneTorus.complexSplitting_apply`, `TauCeti.DeligneTorus.complexSplitting_tmul`:
  explicit component formulas `a ⊗ b ↦ (a * b, conj a * b)`.
* `TauCeti.DeligneTorus.complexSplitting_real`, `TauCeti.DeligneTorus.complexSplitting_I`,
  `TauCeti.DeligneTorus.complexSplitting_scalar`: real points versus complex scalar points.
* `TauCeti.DeligneTorus.conj_swap`, `TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`: Galois
  conjugation on `S(ℂ)` and characterization of `S(ℝ)` inside `S(ℂ)`.
* `TauCeti.DeligneTorus.splittingMulEquiv_diagonal`,
  `TauCeti.DeligneTorus.splittingMulEquiv_weight`,
  `TauCeti.DeligneTorus.fst_mul_snd_splittingMulEquiv`,
  `TauCeti.DeligneTorus.complexSplitting_mul_real`: compatibility with `diagonal`, `weight`, and
  `norm`.
* `TauCeti.DeligneTorus.torusCommHopfAlgProperty_S` and `TauCeti.DeligneTorus.not_split`: `S` is a
  non-split algebraic torus over `ℝ`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open CategoryTheory WithConv TauCeti.Algebra
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.DeligneTorus

section PointsSplitting

-- Prefer the real module from `[Algebra ℝ R]` so `ℂ ⊗[ℝ] R` matches `pointsMulEquiv R`.
attribute [local instance high] Algebra.toModule

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **Splitting of the points of the Deligne torus over a complex algebra.** For a commutative
`ℂ`-algebra `R` with compatible `ℝ`-algebra structure, `S(R) ≃* Rˣ × Rˣ` via
`z ⊗ r ↦ (z • r, conj z • r)`. -/
noncomputable def splittingMulEquiv : WithConv (S →ₐ[ℝ] R) ≃* Rˣ × Rˣ :=
  (pointsMulEquiv R).trans
    ((Units.mapEquiv (complexTensorProductEquiv R).toMulEquiv).trans MulEquiv.prodUnits)

/-- **Milne's complex splitting** `S(ℂ) ≃* ℂˣ × ℂˣ` of the Deligne torus on complex points. -/
noncomputable abbrev complexSplitting : WithConv (S →ₐ[ℝ] ℂ) ≃* ℂˣ × ℂˣ :=
  splittingMulEquiv ℂ

variable {R}

theorem coe_fst_splittingMulEquiv (f : WithConv (S →ₐ[ℝ] R)) :
    ((splittingMulEquiv R f).1 : R) = (complexTensorProductEquiv R (pointsMulEquiv R f)).1 :=
  (rfl)

theorem coe_snd_splittingMulEquiv (f : WithConv (S →ₐ[ℝ] R)) :
    ((splittingMulEquiv R f).2 : R) = (complexTensorProductEquiv R (pointsMulEquiv R f)).2 :=
  (rfl)

/-- The pair of complex numbers underlying `complexSplitting f` is the image of the unit
`pointsMulEquiv ℂ f` of `ℂ ⊗[ℝ] ℂ` under `complexTensorProductEquiv ℂ`. -/
theorem complexSplitting_apply (f : WithConv (S →ₐ[ℝ] ℂ)) :
    (((complexSplitting f).1 : ℂ), ((complexSplitting f).2 : ℂ)) =
      complexTensorProductEquiv ℂ (pointsMulEquiv ℂ f) :=
  Prod.ext rfl rfl

/-- On a unit `u` of `ℂ ⊗[ℝ] ℂ` whose underlying element is a pure tensor `a ⊗ b`, the two
components of `complexSplitting` are `a * b` and `conj a * b`. -/
theorem complexSplitting_tmul {u : (ℂ ⊗[ℝ] ℂ)ˣ} {a b : ℂ} (hu : (u : ℂ ⊗[ℝ] ℂ) = a ⊗ₜ[ℝ] b) :
    ((complexSplitting ((pointsMulEquiv ℂ).symm u)).1 : ℂ) = a * b ∧
      ((complexSplitting ((pointsMulEquiv ℂ).symm u)).2 : ℂ) = starRingEnd ℂ a * b := by
  rw [coe_fst_splittingMulEquiv, coe_snd_splittingMulEquiv, MulEquiv.apply_symm_apply, hu]
  simp

theorem coe_pointsMulEquiv_splittingMulEquiv_symm (p : Rˣ × Rˣ) :
    (pointsMulEquiv R ((splittingMulEquiv R).symm p) : ℂ ⊗[ℝ] R) =
      (complexTensorProductEquiv R).symm (p.1, p.2) := by
  apply (complexTensorProductEquiv R).injective
  rw [AlgEquiv.apply_symm_apply]
  exact Prod.ext
    ((coe_fst_splittingMulEquiv ((splittingMulEquiv R).symm p)).symm.trans
      (by rw [MulEquiv.apply_symm_apply]))
    ((coe_snd_splittingMulEquiv ((splittingMulEquiv R).symm p)).symm.trans
      (by rw [MulEquiv.apply_symm_apply]))

/-- **Naturality of `splittingMulEquiv` along `ℂ`-algebra homomorphisms.** -/
theorem splittingMulEquiv_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (f : WithConv (S →ₐ[ℝ] R)) :
    splittingMulEquiv R' (AlgHom.mapValue (h.restrictScalars ℝ) f) =
      (Units.map (h : R →* R') (splittingMulEquiv R f).1,
        Units.map (h : R →* R') (splittingMulEquiv R f).2) := by
  have hmap := complexTensorProductEquiv_map_of_algHom h (pointsMulEquiv R f)
  have hl : Algebra.TensorProduct.lTensor (S := ℂ) ℂ (h.restrictScalars ℝ)
      (pointsMulEquiv R f) =
      Algebra.TensorProduct.map (AlgHom.id ℝ ℂ) (h.restrictScalars ℝ) (pointsMulEquiv R f) :=
    rfl
  ext
  · dsimp only
    rw [coe_fst_splittingMulEquiv, pointsMulEquiv_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
      hl, Units.coe_map, MonoidHom.coe_ofClass, coe_fst_splittingMulEquiv]
    exact congrArg Prod.fst hmap
  · dsimp only
    rw [coe_snd_splittingMulEquiv, pointsMulEquiv_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
      hl, Units.coe_map, MonoidHom.coe_ofClass, coe_snd_splittingMulEquiv]
    exact congrArg Prod.snd hmap

/-- Inverse naturality of `splittingMulEquiv` along `ℂ`-algebra homomorphisms. -/
theorem mapValue_splittingMulEquiv_symm {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (p : Rˣ × Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) ((splittingMulEquiv R).symm p) =
      (splittingMulEquiv R').symm (Units.map (h : R →* R') p.1, Units.map (h : R →* R') p.2) := by
  apply (splittingMulEquiv R').injective
  rw [splittingMulEquiv_mapValue, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- **Base-changing a real point to `R`** sends `z ∈ S(ℝ) ≃ ℂˣ` to `(z, conj z)` embedded into
`Rˣ × Rˣ`. -/
theorem splittingMulEquiv_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    splittingMulEquiv R (AlgHom.mapValue (Algebra.ofId ℝ R) f) =
      (Units.map (algebraMap ℂ R : ℂ →* R) (realPointsMulEquiv f),
        Units.map ((algebraMap ℂ R).comp (starRingEnd ℂ) : ℂ →* R) (realPointsMulEquiv f)) := by
  obtain ⟨z, rfl⟩ := realPointsMulEquiv.symm.surjective f
  ext
  · dsimp only
    rw [coe_fst_splittingMulEquiv, pointsMulEquiv_mapValue,
      pointsMulEquiv_realPointsMulEquiv_symm, MulEquiv.apply_symm_apply]
    simp
  · dsimp only
    rw [coe_snd_splittingMulEquiv, pointsMulEquiv_mapValue,
      pointsMulEquiv_realPointsMulEquiv_symm, MulEquiv.apply_symm_apply]
    simp

/-- **On real points, `S(ℝ) → S(ℂ)` is `z ↦ (z, conj z)`.** -/
theorem complexSplitting_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    complexSplitting (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      (realPointsMulEquiv f, Units.map (starRingEnd ℂ : ℂ →* ℂ) (realPointsMulEquiv f)) := by
  simpa using splittingMulEquiv_real (R := ℂ) f

/-- **Pinning the factor order**: the real point `I ∈ ℂˣ` maps to `(I, -I)` in `S(ℂ) ≃* ℂˣ × ℂˣ`. -/
theorem complexSplitting_I :
    complexSplitting (AlgHom.mapValue (Algebra.ofId ℝ ℂ)
        (realPointsMulEquiv.symm (Units.mk0 Complex.I Complex.I_ne_zero))) =
      (Units.mk0 Complex.I Complex.I_ne_zero, -Units.mk0 Complex.I Complex.I_ne_zero) := by
  rw [complexSplitting_real, MulEquiv.apply_symm_apply]
  ext <;> simp

/-- **Scalar `I` versus real `I`**: the `ℂ`-point corresponding to `1 ⊗ I` in `(ℂ ⊗[ℝ] ℂ)ˣ` maps to
`(I, I)`, whereas the real point `I` (corresponding to `I ⊗ 1`) maps to `(I, -I)`. -/
theorem complexSplitting_scalar :
    complexSplitting ((pointsMulEquiv ℂ).symm
        (Units.map (Algebra.TensorProduct.includeRight : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ).toMonoidHom
          (Units.mk0 Complex.I Complex.I_ne_zero))) =
      (Units.mk0 Complex.I Complex.I_ne_zero, Units.mk0 Complex.I Complex.I_ne_zero) := by
  ext <;> simp [coe_fst_splittingMulEquiv, coe_snd_splittingMulEquiv]

/-- **Complex conjugation on `S(ℂ)`** sends `(z₁, z₂)` to `(conj z₂, conj z₁)`. -/
theorem conj_swap (f : WithConv (S →ₐ[ℝ] ℂ)) :
    complexSplitting (AlgHom.mapValue Complex.conjAe.toAlgHom f) =
      (Units.map (starRingEnd ℂ : ℂ →* ℂ) (complexSplitting f).2,
        Units.map (starRingEnd ℂ : ℂ →* ℂ) (complexSplitting f).1) := by
  have hconj := complexTensorProductEquiv_map_of_conj Complex.conjAe.toAlgHom
    (fun z ↦ by simp [Complex.conjAe_coe]) (pointsMulEquiv ℂ f)
  have hl : Algebra.TensorProduct.lTensor (S := ℂ) ℂ Complex.conjAe.toAlgHom
      (pointsMulEquiv ℂ f) =
      Algebra.TensorProduct.map (AlgHom.id ℝ ℂ) Complex.conjAe.toAlgHom (pointsMulEquiv ℂ f) :=
    rfl
  ext
  · dsimp only
    rw [coe_fst_splittingMulEquiv, pointsMulEquiv_mapValue, Units.coe_map,
      MonoidHom.coe_ofClass, hl, Units.coe_map, MonoidHom.coe_ofClass, coe_snd_splittingMulEquiv]
    simpa [Complex.conjAe_coe] using congrArg Prod.fst hconj
  · dsimp only
    rw [coe_snd_splittingMulEquiv, pointsMulEquiv_mapValue, Units.coe_map,
      MonoidHom.coe_ofClass, hl, Units.coe_map, MonoidHom.coe_ofClass, coe_fst_splittingMulEquiv]
    simpa [Complex.conjAe_coe] using congrArg Prod.snd hconj

/-- **Characterization of real points inside `S(ℂ)`**: a complex point lies in the image of `S(ℝ)`
if and only if its two components under `complexSplitting` are `(z, conj z)`. -/
theorem mem_mrange_mapValue_ofId_iff (f : WithConv (S →ₐ[ℝ] ℂ)) :
    f ∈ MonoidHom.mrange (AlgHom.mapValue (Algebra.ofId ℝ ℂ)) ↔
      Units.map (starRingEnd ℂ : ℂ →* ℂ) (complexSplitting f).1 = (complexSplitting f).2 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [complexSplitting_real]
  · intro hf
    refine ⟨realPointsMulEquiv.symm (complexSplitting f).1, ?_⟩
    apply complexSplitting.injective
    rw [complexSplitting_real, MulEquiv.apply_symm_apply]
    exact Prod.ext rfl hf

/-- Over a complex algebra `R`, the diagonal `d(r)` splits as `(r, r)`. -/
@[simp]
theorem splittingMulEquiv_diagonal (r : Rˣ) :
    splittingMulEquiv R (diagonal R r) = (r, r) := by
  ext <;> simp [coe_fst_splittingMulEquiv, coe_snd_splittingMulEquiv]

/-- Over a complex algebra `R`, the weight `w(r)` splits as `(r⁻¹, r⁻¹)`. -/
@[simp]
theorem splittingMulEquiv_weight (r : Rˣ) :
    splittingMulEquiv R (weight R r) = (r⁻¹, r⁻¹) := by
  rw [weight_eq_inv_diagonal, map_inv (splittingMulEquiv R), splittingMulEquiv_diagonal,
    Prod.inv_mk]

/-- Over `ℂ`, the weight is `w(r) = (r⁻¹, r⁻¹)`. -/
theorem complexSplitting_weight (r : ℂˣ) :
    complexSplitting (weight ℂ r) = (r⁻¹, r⁻¹) :=
  splittingMulEquiv_weight r

/-- **The product of the two splitting components is the norm** over any commutative complex algebra
`R`. -/
theorem fst_mul_snd_splittingMulEquiv (f : WithConv (S →ₐ[ℝ] R)) :
    (splittingMulEquiv R f).1 * (splittingMulEquiv R f).2 = norm R f := by
  have hcomm : Algebra.TensorProduct.comm ℝ R ℂ
      (Algebra.TensorProduct.comm ℝ ℂ R (pointsMulEquiv R f)) = pointsMulEquiv R f :=
    (Algebra.TensorProduct.comm ℝ ℂ R).symm_apply_apply _
  ext
  rw [Units.val_mul, coe_fst_splittingMulEquiv, coe_snd_splittingMulEquiv, norm_apply,
    NormTorus.coe_norm, norm_tensorProduct_complex, tensorProductComplexAlgEquiv_apply, hcomm]

/-- On a real point mapped to `S(ℂ)`, the product of the two splitting components is `|z|²`. -/
theorem complexSplitting_mul_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (((complexSplitting (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f)).1 *
        (complexSplitting (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f)).2 : ℂˣ) : ℂ) =
      Complex.normSq (realPointsMulEquiv f) := by
  rw [fst_mul_snd_splittingMulEquiv, norm_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
    Algebra.ofId_apply, coe_norm_real]
  rfl

end PointsSplitting

/-! ### Coordinate bialgebra splitting over `ℂ` -/

section SchemeSplitting

/-- **The base change of the Deligne torus `S` from `ℝ` to `ℂ`**, as a finite-type commutative Hopf
`ℂ`-algebra. -/
noncomputable def baseChangeComplex : FiniteTypeCommHopfAlgCat.{0, 0} ℂ :=
  FiniteTypeCommHopfAlgCat.baseChange (K := ℂ) (FiniteTypeCommHopfAlgCat.of ℝ S)

/-- **Points of the base-changed Deligne torus `S_ℂ`** over a commutative `ℂ`-algebra `R` with
compatible `ℝ`-algebra structure identify with the `R`-points of `S`. -/
noncomputable def baseChangeComplexPointsMulEquiv (R : Type*) [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃* WithConv (S →ₐ[ℝ] R) :=
  (AlgHom.baseChangePointsMulEquiv (k := ℝ) (K := ℂ)
    (A := FiniteTypeCommHopfAlgCat.of ℝ S) (R := R)).symm

private lemma baseChangeComplexPointsMulEquiv_mapValue {R R' : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) =
      AlgHom.mapValue (H := S) (φ.restrictScalars ℝ) (baseChangeComplexPointsMulEquiv R g) :=
  AlgHom.baseChangePointsMulEquiv_symm_mapValue
    (k := ℝ) (K := ℂ) (A := FiniteTypeCommHopfAlgCat.of ℝ S) φ g

/-- On a commutative `ℂ`-algebra `R`, `ℂ`-points of `baseChangeComplex` correspond naturally to
`ℂ`-points of `ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` through `splittingMulEquiv R`. -/
private noncomputable def baseChangeProductPointsMulEquiv (R : Type*) [CommRing R] [Algebra ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃* WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R) :=
  (baseChangeComplexPointsMulEquiv R).trans <|
    (splittingMulEquiv R).trans <|
      (MulEquiv.prodCongr MultiplicativeGroup.pointsMulEquiv.symm
        MultiplicativeGroup.pointsMulEquiv.symm).trans AffineGroup.Product.pointsMulEquiv.symm

private lemma mapValue_baseChangeProductPointsMulEquiv {R R' : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing R'] [Algebra ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) φ (baseChangeProductPointsMulEquiv R g) =
      baseChangeProductPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) := by
  simp only [baseChangeProductPointsMulEquiv, MulEquiv.trans_apply]
  rw [AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply,
    baseChangeComplexPointsMulEquiv_mapValue, splittingMulEquiv_mapValue]
  congr 1
  exact Prod.ext (MultiplicativeGroup.mapValue_pointsMulEquiv_symm_apply _ _)
    (MultiplicativeGroup.mapValue_pointsMulEquiv_symm_apply _ _)

/-- The natural isomorphism of group-valued points functors between `baseChangeComplex` and
`ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]`. -/
private noncomputable def baseChangeProductPointsNatIso :
    HopfAlgebra.pointsFunctor (R := ℂ) (H := baseChangeComplex) ≅
      HopfAlgebra.pointsFunctor (R := ℂ) (H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) :=
  NatIso.ofComponents (fun A ↦ MulEquiv.toGrpIso (baseChangeProductPointsMulEquiv A)) fun φ ↦ by
    ext g
    exact (mapValue_baseChangeProductPointsMulEquiv φ.hom g).symm

/-- The categorical isomorphism `baseChangeComplex ≅ ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` in `CommHopfAlgCat ℂ`
recovered by Yoneda from `baseChangeProductPointsNatIso`. -/
private noncomputable def baseChangeComplexCommHopfIso :
    _root_.CommHopfAlgCat.of ℂ baseChangeComplex ≅
      _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) where
  hom := CommHopfAlgCat.homOfPointsMap baseChangeProductPointsNatIso.inv
  inv := CommHopfAlgCat.homOfPointsMap baseChangeProductPointsNatIso.hom
  hom_inv_id := by
    rw [← CommHopfAlgCat.homOfPointsMap_comp, baseChangeProductPointsNatIso.hom_inv_id,
      CommHopfAlgCat.homOfPointsMap_id]
  inv_hom_id := by
    rw [← CommHopfAlgCat.homOfPointsMap_comp, baseChangeProductPointsNatIso.inv_hom_id,
      CommHopfAlgCat.homOfPointsMap_id]

/-- **Scheme-level complex splitting of the Deligne torus**:
`baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` as commutative Hopf `ℂ`-algebras. -/
noncomputable def baseChangeComplexBialgEquiv :
    baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹] :=
  _root_.CommHopfAlgCat.ofIso baseChangeComplexCommHopfIso

/-- **Compatibility of `baseChangeComplexBialgEquiv` with `splittingMulEquiv` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
theorem mapDomain_baseChangeComplexBialgEquiv {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra ℂ R]
    [IsScalarTower ℝ ℂ R]
    (p : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) × WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    BialgHom.mapDomain baseChangeComplexBialgEquiv.toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p) =
      (baseChangeComplexPointsMulEquiv R).symm
        ((splittingMulEquiv R).symm
          (MultiplicativeGroup.pointsMulEquiv p.1, MultiplicativeGroup.pointsMulEquiv p.2)) := by
  let H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]
  let f : WithConv (H →ₐ[ℂ] R) := AffineGroup.Product.pointsMulEquiv.symm p
  let idH : WithConv (H →ₐ[ℂ] H) := toConv (AlgHom.id ℂ H)
  have hid : BialgHom.mapDomain baseChangeComplexBialgEquiv.toBialgHom idH =
      (baseChangeProductPointsMulEquiv H).symm idH := by
    have hnat_iso := CommHopfAlgCat.mapPointsFunctor_homOfPointsMap
      (H := _root_.CommHopfAlgCat.of ℂ H) (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
      baseChangeProductPointsNatIso.inv
    have hmap := congrArg (fun α ↦ α.app (CommAlgCat.of ℂ H) idH) hnat_iso
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] at hmap
    rw [baseChangeComplexBialgEquiv, BialgEquiv.toBialgHom_eq_coe, CommHopfAlgCat.coe_ofIso]
    exact hmap.trans (by
      simp only [baseChangeProductPointsNatIso, NatIso.ofComponents_inv_app]
      rfl)
  have hfp : AlgHom.mapValue (H := H) f.ofConv idH = f := by
    simp only [AlgHom.mapValue_apply, idH, AlgHom.comp_id, toConv_ofConv]
  have hnat := DFunLike.congr_fun
    (BialgHom.mapValue_mapDomain baseChangeComplexBialgEquiv.toBialgHom f.ofConv).symm idH
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hfp, hid] at hnat
  apply (baseChangeComplexPointsMulEquiv R).injective
  rw [← hnat, MulEquiv.apply_symm_apply, baseChangeComplexPointsMulEquiv_mapValue]
  have hsymm : baseChangeComplexPointsMulEquiv H ((baseChangeProductPointsMulEquiv H).symm idH) =
      (splittingMulEquiv H).symm
        (MultiplicativeGroup.pointsMulEquiv (AffineGroup.Product.pointsMulEquiv idH).1,
          MultiplicativeGroup.pointsMulEquiv (AffineGroup.Product.pointsMulEquiv idH).2) := by
    simp only [baseChangeProductPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
    exact (baseChangeComplexPointsMulEquiv H).apply_symm_apply _
  rw [hsymm, mapValue_splittingMulEquiv_symm,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue,
    ← AffineGroup.Product.pointsMulEquiv_mapValue_fst,
    ← AffineGroup.Product.pointsMulEquiv_mapValue_snd,
    hfp]
  simp only [f, MulEquiv.apply_symm_apply]

end SchemeSplitting

/-! ### Algebraic torus property and non-splitness over `ℝ` -/

section TorusAndNotSplit

private noncomputable def baseChangeSplitTorusPointsMulEquiv (R : Type*) [CommRing R]
    [Algebra ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃*
      WithConv (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) →ₐ[ℂ] R) :=
  (baseChangeComplexPointsMulEquiv R).trans <|
    (splittingMulEquiv R).trans <|
      MulEquiv.prodUnits.symm.trans <|
        (Units.mapEquiv (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ R)).symm.toMulEquiv).trans <|
          MulEquiv.piUnits.trans <|
            (MulEquiv.arrowCongr Equiv.ulift.symm (MulEquiv.refl Rˣ)).trans
              (SplitTorus.pointsMulEquiv (R := ℂ) (A := R) (σ := ULift.{0} (Fin 2))).symm

private lemma mapValue_baseChangeSplitTorusPointsMulEquiv {R R' : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing R'] [Algebra ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ))) φ
        (baseChangeSplitTorusPointsMulEquiv R g) =
      baseChangeSplitTorusPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) := by
  dsimp only [baseChangeSplitTorusPointsMulEquiv, MulEquiv.trans_apply]
  rw [SplitTorus.mapValue_pointsMulEquiv_symm_apply,
    baseChangeComplexPointsMulEquiv_mapValue, splittingMulEquiv_mapValue]
  congr 1
  funext ⟨i⟩
  ext
  fin_cases i <;> rfl

private noncomputable def baseChangeSplitTorusPointsNatIso :
    HopfAlgebra.pointsFunctor (R := ℂ) (H := baseChangeComplex) ≅
      HopfAlgebra.pointsFunctor (R := ℂ)
        (H := MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ))) :=
  NatIso.ofComponents (fun A ↦ MulEquiv.toGrpIso (baseChangeSplitTorusPointsMulEquiv A)) fun φ ↦ by
    ext g
    exact (mapValue_baseChangeSplitTorusPointsMulEquiv φ.hom g).symm

/-- **Isomorphism between the base change of `S` to `ℂ` and the rank-two split torus.** -/
noncomputable def baseChangeSplitTorusIso :
    DiagonalizableGroup.coordinateRing ℂ (SplitTorus.characterGroup (ULift.{0} (Fin 2))) ≅
      baseChangeComplex :=
  ObjectProperty.isoMk _
    { hom := CommHopfAlgCat.homOfPointsMap baseChangeSplitTorusPointsNatIso.hom
      inv := CommHopfAlgCat.homOfPointsMap baseChangeSplitTorusPointsNatIso.inv
      hom_inv_id := by
        rw [← CommHopfAlgCat.homOfPointsMap_comp, baseChangeSplitTorusPointsNatIso.inv_hom_id,
          CommHopfAlgCat.homOfPointsMap_id]
      inv_hom_id := by
        rw [← CommHopfAlgCat.homOfPointsMap_comp, baseChangeSplitTorusPointsNatIso.hom_inv_id,
          CommHopfAlgCat.homOfPointsMap_id] }

/-- **Compatibility of `baseChangeSplitTorusIso` with `splittingMulEquiv` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure: the two split-torus coordinates
of a base-changed point `g` are the two components of `splittingMulEquiv R`. -/
theorem pointsMulEquiv_mapDomain_baseChangeSplitTorusIso {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    (SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨0⟩,
      SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨1⟩) =
      splittingMulEquiv R (baseChangeComplexPointsMulEquiv R g) := by
  let idB : WithConv (baseChangeComplex →ₐ[ℂ] baseChangeComplex) :=
    toConv (AlgHom.id ℂ baseChangeComplex)
  have hid : BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom idB =
      baseChangeSplitTorusPointsMulEquiv baseChangeComplex idB := by
    have hnat_iso := CommHopfAlgCat.mapPointsFunctor_homOfPointsMap
      (H := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
      (K := (DiagonalizableGroup.coordinateRing ℂ
        (SplitTorus.characterGroup (ULift.{0} (Fin 2)))).obj)
      baseChangeSplitTorusPointsNatIso.hom
    have hmap := congrArg (fun α ↦ α.app (CommAlgCat.of ℂ baseChangeComplex) idB) hnat_iso
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] at hmap
    exact hmap.trans (by
      simp only [baseChangeSplitTorusPointsNatIso, NatIso.ofComponents_hom_app]
      rfl)
  have hg : AlgHom.mapValue (H := baseChangeComplex) g.ofConv idB = g := by
    simp only [AlgHom.mapValue_apply, idB, AlgHom.comp_id, toConv_ofConv]
  have hnat := DFunLike.congr_fun
    (BialgHom.mapValue_mapDomain baseChangeSplitTorusIso.hom.hom.hom g.ofConv).symm idB
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg, hid] at hnat
  have hcomp : ∀ i : ULift.{0} (Fin 2),
      SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) i =
        Units.map g.ofConv.toMonoidHom
          (SplitTorus.pointsMulEquiv (baseChangeSplitTorusPointsMulEquiv baseChangeComplex idB)
            i) := fun i ↦ by
    rw [← hnat, SplitTorus.pointsMulEquiv_mapValue]
  have hsplit : splittingMulEquiv R (baseChangeComplexPointsMulEquiv R g) =
      (Units.map (g.ofConv : baseChangeComplex →* R)
          (splittingMulEquiv baseChangeComplex
            (baseChangeComplexPointsMulEquiv baseChangeComplex idB)).1,
        Units.map (g.ofConv : baseChangeComplex →* R)
          (splittingMulEquiv baseChangeComplex
            (baseChangeComplexPointsMulEquiv baseChangeComplex idB)).2) := by
    rw [← splittingMulEquiv_mapValue g.ofConv, ← baseChangeComplexPointsMulEquiv_mapValue, hg]
  rw [hcomp ⟨0⟩, hcomp ⟨1⟩, hsplit]
  ext <;> simp [baseChangeSplitTorusPointsMulEquiv, MulEquiv.prodUnits]

/-- After base change from `ℝ` to `ℂ`, the Deligne torus is a split torus. -/
theorem splitTorusCommHopfAlgProperty_baseChange_complex :
    splitTorusCommHopfAlgProperty ℂ baseChangeComplex :=
  (splitTorusCommHopfAlgProperty_iff ℂ _).mpr ⟨2, ⟨baseChangeSplitTorusIso⟩⟩

/-- **The Deligne torus is an algebraic torus over `ℝ`** (split of rank two over `ℂ`). -/
theorem torusCommHopfAlgProperty_S :
    torusCommHopfAlgProperty ℝ (FiniteTypeCommHopfAlgCat.of ℝ S) :=
  torusCommHopfAlgProperty.of_baseChange ℝ ℂ (FiniteTypeCommHopfAlgCat.of ℝ S)
    splitTorusCommHopfAlgProperty_baseChange_complex

/-- **The real points `S(ℝ) ≃* ℂˣ` contain infinitely many elements of finite order**, witnessed by
the primitive `(k + 1)`-th roots of unity `exp (2πI / (k + 1))`. -/
theorem infinite_isOfFinOrder_realPoints :
    Infinite {f : WithConv (S →ₐ[ℝ] ℝ) // IsOfFinOrder f} := by
  let u (k : ℕ) : ℂˣ :=
    ((Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k)).isUnit
      (Nat.succ_ne_zero k)).unit
  have hprim (k : ℕ) : IsPrimitiveRoot (u k) (k + 1) :=
    (Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k)).isUnit_unit
      (Nat.succ_ne_zero k)
  let instM : Monoid (WithConv (S →ₐ[ℝ] ℝ)) := inferInstance
  let φ := @MulEquiv.toMonoidHom ℂˣ (WithConv (S →ₐ[ℝ] ℝ)) inferInstance instM.toMulOneClass
    realPointsMulEquiv.symm
  refine Infinite.of_injective
    (fun k : ℕ ↦ ⟨φ (u k),
      @MonoidHom.isOfFinOrder ℂˣ (WithConv (S →ₐ[ℝ] ℝ)) inferInstance instM φ (u k)
        ((hprim k).isOfFinOrder (Nat.succ_ne_zero k))⟩)
    fun k l hkl ↦ ?_
  have hu : u k = u l :=
    realPointsMulEquiv.symm.injective (congrArg Subtype.val hkl)
  exact Nat.succ.inj <| (hprim k).eq_orderOf.trans <| (congrArg orderOf hu).trans
    (hprim l).eq_orderOf.symm

/-- For every index type `σ`, `S(ℝ)` is not multiplicatively isomorphic to `σ → ℝˣ`: the real point
`I ∈ ℂˣ` has order four (`I ^ 4 = 1`, `I ^ 2 ≠ 1`), whereas every element `g : σ → ℝˣ` satisfying
`g ^ 4 = 1` already satisfies `g ^ 2 = 1`. -/
theorem isEmpty_realPoints_mulEquiv_pi (σ : Type*) :
    IsEmpty (WithConv (S →ₐ[ℝ] ℝ) ≃* (σ → ℝˣ)) := by
  refine ⟨fun e ↦ ?_⟩
  let uI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  let ψ : ℂˣ ≃* (σ → ℝˣ) := realPointsMulEquiv.symm.trans e
  have huI4 : uI ^ 4 = 1 := Units.ext Complex.I_pow_four
  have hg4 : ψ uI ^ 4 = 1 := by rw [← map_pow, huI4, map_one]
  have hg2 : ψ uI ^ 2 = 1 := funext fun i ↦ Units.ext <| by
    have hi4 : ((ψ uI i : ℝˣ) : ℝ) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Pi.pow_apply, hg4, Pi.one_apply, Units.val_one]
    rcases (pow_eq_one_iff_of_ne_zero (by positivity : 4 ≠ 0)).mp hi4 with h1 | ⟨hm1, -⟩
    · simp [h1]
    · norm_num [hm1]
  have huI2 : uI ^ 2 = 1 := ψ.injective (by rw [map_pow, map_one, hg2])
  have hval := congrArg Units.val huI2
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, sq, Complex.I_mul_I, Units.val_one] at hval
  norm_num at hval

/-- **Non-example: the Deligne torus is not split over `ℝ`**, because `S(ℝ) ≃* ℂˣ` is not
multiplicatively isomorphic to `(ℝˣ)ⁿ` (`isEmpty_realPoints_mulEquiv_pi`). -/
theorem not_split : ¬ splitTorusCommHopfAlgProperty ℝ (FiniteTypeCommHopfAlgCat.of ℝ S) := by
  intro h
  obtain ⟨n, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff ℝ _).mp h
  let e : MonoidAlgebra ℝ (Multiplicative (ULift.{0} (Fin n) →₀ ℤ)) ≃ₐc[ℝ] S :=
    _root_.CommHopfAlgCat.ofIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{0, 0} ℝ) (_root_.CommHopfAlgCat.{0} ℝ)).mapIso i)
  exact (isEmpty_realPoints_mulEquiv_pi (ULift.{0} (Fin n))).false
    ((BialgEquiv.mapDomainMulEquiv (A := ℝ) e).trans SplitTorus.pointsMulEquiv)

end TorusAndNotSplit

end TauCeti.DeligneTorus
