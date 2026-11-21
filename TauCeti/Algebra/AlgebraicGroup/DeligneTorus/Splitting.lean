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
# The splitting of the Deligne torus over `ℂ`

Over `ℂ` the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` splits: `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`. On points, for a complex
algebra `R` with a compatible real algebra structure, the points `S(R) = (ℂ ⊗[ℝ] R)ˣ` are
identified with `Rˣ × Rˣ` (`TauCeti.DeligneTorus.complexSplitting R`) through the splitting
`ℂ ⊗[ℝ] R ≃ R × R`, `a ⊗ x ↦ (a • x, conj a • x)` (`TauCeti.complexTensorProductEquivProd`). With
this normalization:

* a real point `z ∈ S(ℝ) = ℂˣ` goes to `(z, conj z)` in `S(ℂ)`
  (`TauCeti.DeligneTorus.complexSplitting_real`), so the real point `i` goes to `(i, -i)`, which
  fixes the order of the two factors, whereas the scalar point `1 ⊗ i` goes to `(i, i)`
  (`TauCeti.DeligneTorus.complexSplitting_scalar`);
* complex conjugation of `S(ℂ)` acts by `(z₁, z₂) ↦ (conj z₂, conj z₁)`
  (`TauCeti.DeligneTorus.complexSplitting_conj`), cutting out `S(ℝ)` as its fixed locus
  (`TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`);
* the diagonal `d(r)` and the weight `w(r)` are `(r, r)` and `(r⁻¹, r⁻¹)`
  (`TauCeti.DeligneTorus.complexSplitting_diagonal`,
  `TauCeti.DeligneTorus.complexSplitting_weight`), and the product of the two components is the
  norm `Nm` (`TauCeti.DeligneTorus.fst_mul_snd_complexSplitting`).

The cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ` is `z ↦ (z, 1)` (`TauCeti.DeligneTorus.mu`). It is not
defined over `ℝ`: `μ(-1) = (-1, 1)` is not of the form `(z, conj z)`
(`TauCeti.DeligneTorus.mu_neg_one_notMem_range_mapValue`). The characters of `S` are
`z₁ ^ p * z₂ ^ q` for `(p, q) ∈ ℤ²` (`TauCeti.DeligneTorus.characterGroup`), and complex
conjugation exchanges `(p, q)` and `(q, p)`. These are the conventions in which a real Hodge
structure of type `(p, q)` is a representation of `S` on which `z ∈ S(ℝ)` acts on the
`(p, q)`-summand by `z^{-p} conj(z)^{-q}`, and through which a cocharacter `μ` of a Shimura datum
is defined.

By the Yoneda lemma for commutative Hopf algebras (`TauCeti.CommHopfAlgCat.homOfPointsMap`), the
natural splitting of `R`-points lifts to the bialgebra isomorphism
`ℂ ⊗[ℝ] S ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` (`TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`) and
exhibits `S` as a rank-two algebraic torus over `ℝ`
(`TauCeti.DeligneTorus.torusCommHopfAlgProperty_S`). Over `ℝ` itself, however, `S` is not split
(`TauCeti.DeligneTorus.not_splitTorusCommHopfAlgProperty_S`): `S(ℝ) ≃* ℂˣ` contains the order-four
element `I`, whereas in any product `σ → ℝˣ` every element `g` satisfying `g ^ 4 = 1` already
satisfies `g ^ 2 = 1` (`TauCeti.DeligneTorus.isEmpty_realPoints_mulEquiv_pi`).

## Main definitions

* `TauCeti.DeligneTorus.complexSplitting R`: `S(R) ≃* Rˣ × Rˣ` for a complex algebra `R`.
* `TauCeti.DeligneTorus.mu R`: the cocharacter `μ : z ↦ (z, 1)` on points over a complex algebra.
* `TauCeti.DeligneTorus.characterGroup R`: the characters `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`, as a
  homomorphism from `ℤ²` (written multiplicatively) to the characters of `S(R)`.
* `TauCeti.DeligneTorus.baseChangeComplex`: the base change of `S` from `ℝ` to `ℂ` as a
  finite-type commutative Hopf `ℂ`-algebra, with point identification
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv`.
* `TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`: the coordinate bialgebra splitting
  `baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]`.
* `TauCeti.DeligneTorus.baseChangeSplitTorusIso`: the isomorphism identifying `baseChangeComplex`
  with the rank-two split torus, with point compatibility
  `TauCeti.DeligneTorus.pointsMulEquiv_mapDomain_baseChangeSplitTorusIso`.

## Main results

* `TauCeti.DeligneTorus.complexSplitting_mapValue`, `TauCeti.DeligneTorus.mapValue_mu`,
  `TauCeti.DeligneTorus.characterGroup_mapValue`,
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapValue`: naturality in `R`.
* `TauCeti.DeligneTorus.complexSplitting_real`, `TauCeti.DeligneTorus.complexSplitting_scalar`,
  `TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`: real points versus complex scalar points,
  and characterization of `S(ℝ)` inside `S(ℂ)`.
* `TauCeti.DeligneTorus.complexSplitting_conj`: complex conjugation on `S(ℂ)` is
  `(z₁, z₂) ↦ (conj z₂, conj z₁)`.
* `TauCeti.DeligneTorus.complexSplitting_diagonal`, `TauCeti.DeligneTorus.complexSplitting_weight`,
  `TauCeti.DeligneTorus.fst_mul_snd_complexSplitting`,
  `TauCeti.DeligneTorus.complexSplitting_mul_real`: compatibility with `diagonal`, `weight`, and
  `norm`.
* `TauCeti.DeligneTorus.mu_neg_one_notMem_range_mapValue`: `μ` is not defined over `ℝ`.
* `TauCeti.DeligneTorus.weight_eq_mu_mul_conj`: over `ℂ`, `w(r) = μ(r⁻¹) · μ'(r⁻¹)`, where `μ'` is
  the complex conjugate of `μ`.
* `TauCeti.DeligneTorus.characterGroup_injective`: distinct pairs `(p, q)` give distinct
  characters of `S(ℂ)`.
* `TauCeti.DeligneTorus.characterGroup_conj`: conjugation exchanges the characters `(p, q)` and
  `(q, p)`.
* `TauCeti.DeligneTorus.characterGroup_mu`, `TauCeti.DeligneTorus.characterGroup_weight`,
  `TauCeti.DeligneTorus.characterGroup_norm`: the character `(p, q)` is `z ↦ z ^ p` on `μ(z)` and
  `r ↦ r ^ (-(p + q))` on the weight, and `(1, 1)` is the norm on real points.
* `TauCeti.DeligneTorus.infinite_isOfFinOrder_realPoints`: `S(ℝ)` has infinitely many elements of
  finite order.
* `TauCeti.DeligneTorus.torusCommHopfAlgProperty_S` and
  `TauCeti.DeligneTorus.not_splitTorusCommHopfAlgProperty_S`: `S` is a non-split algebraic torus
  over `ℝ`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open CategoryTheory WithConv TauCeti.Algebra
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The splitting `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` on points -/

section Splitting

-- Prefer the real module from `[Algebra ℝ R]` so `ℂ ⊗[ℝ] R` matches `pointsMulEquiv R`.
attribute [local instance high] Algebra.toModule

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **The splitting of the Deligne torus over `ℂ`.** For a complex algebra `R`, the points
`S(R) = (ℂ ⊗[ℝ] R)ˣ` are identified with `Rˣ × Rˣ` through `a ⊗ x ↦ (a • x, conj a • x)`. -/
noncomputable def complexSplitting : WithConv (S →ₐ[ℝ] R) ≃* Rˣ × Rˣ :=
  (pointsMulEquiv R).trans
    ((Units.mapEquiv (complexTensorProductEquivProd R).toMulEquiv).trans MulEquiv.prodUnits)

variable {R}

/-- The first component of the splitting is the first component of `ℂ ⊗[ℝ] R ≃ R × R`, which
sends `a ⊗ x` to `a • x`. -/
@[simp]
theorem coe_complexSplitting_fst (f : WithConv (S →ₐ[ℝ] R)) :
    ((complexSplitting R f).1 : R) = (complexTensorProductEquivProd R (pointsMulEquiv R f)).1 :=
  (rfl)

/-- The second component of the splitting is the second component of `ℂ ⊗[ℝ] R ≃ R × R`, which
sends `a ⊗ x` to `conj a • x`. -/
@[simp]
theorem coe_complexSplitting_snd (f : WithConv (S →ₐ[ℝ] R)) :
    ((complexSplitting R f).2 : R) = (complexTensorProductEquivProd R (pointsMulEquiv R f)).2 :=
  (rfl)

/-- The pair of complex numbers underlying `complexSplitting ℂ f` is the image of the unit
`pointsMulEquiv ℂ f` of `ℂ ⊗[ℝ] ℂ` under `complexTensorProductEquivProd ℂ`. -/
theorem complexSplitting_apply (f : WithConv (S →ₐ[ℝ] ℂ)) :
    (((complexSplitting ℂ f).1 : ℂ), ((complexSplitting ℂ f).2 : ℂ)) =
      complexTensorProductEquivProd ℂ (pointsMulEquiv ℂ f) :=
  Prod.ext rfl rfl

/-- On a unit `u` of `ℂ ⊗[ℝ] ℂ` whose underlying element is a pure tensor `a ⊗ b`, the two
components of `complexSplitting ℂ` are `a * b` and `conj a * b`. -/
theorem complexSplitting_tmul {u : (ℂ ⊗[ℝ] ℂ)ˣ} {a b : ℂ} (hu : (u : ℂ ⊗[ℝ] ℂ) = a ⊗ₜ[ℝ] b) :
    ((complexSplitting ℂ ((pointsMulEquiv ℂ).symm u)).1 : ℂ) = a * b ∧
      ((complexSplitting ℂ ((pointsMulEquiv ℂ).symm u)).2 : ℂ) = starRingEnd ℂ a * b := by
  rw [coe_complexSplitting_fst, coe_complexSplitting_snd, MulEquiv.apply_symm_apply, hu]
  simp [smul_eq_mul]

/-- The element of `ℂ ⊗[ℝ] R` underlying `(complexSplitting R).symm p`. -/
theorem coe_pointsMulEquiv_complexSplitting_symm (p : Rˣ × Rˣ) :
    ↑(pointsMulEquiv R ((complexSplitting R).symm p)) =
      (complexTensorProductEquivProd R).symm ((p.1 : R), (p.2 : R)) := by
  apply (complexTensorProductEquivProd R).injective
  rw [AlgEquiv.apply_symm_apply]
  exact Prod.ext
    ((coe_complexSplitting_fst ((complexSplitting R).symm p)).symm.trans
      (by rw [MulEquiv.apply_symm_apply]))
    ((coe_complexSplitting_snd ((complexSplitting R).symm p)).symm.trans
      (by rw [MulEquiv.apply_symm_apply]))

/-- **Naturality of the splitting in `R`**: post-composing a point with a complex algebra map
`h : R → R'` applies `h` to both components. -/
theorem complexSplitting_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (f : WithConv (S →ₐ[ℝ] R)) :
    complexSplitting R' (AlgHom.mapValue (h.restrictScalars ℝ) f) =
      (Units.map (h : R →* R') (complexSplitting R f).1,
        Units.map (h : R →* R') (complexSplitting R f).2) := by
  ext <;> simp only [coe_complexSplitting_fst, coe_complexSplitting_snd, pointsMulEquiv_mapValue,
    Units.coe_map, MonoidHom.coe_ofClass, complexTensorProductEquivProd_lTensor]

/-- Inverse naturality of `complexSplitting` along `ℂ`-algebra homomorphisms. -/
theorem mapValue_complexSplitting_symm {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (p : Rˣ × Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) ((complexSplitting R).symm p) =
      (complexSplitting R').symm (Units.map (h : R →* R') p.1, Units.map (h : R →* R') p.2) := by
  apply (complexSplitting R').injective
  rw [complexSplitting_mapValue, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- **The diagonal over a complex algebra** is `d(r) = (r, r)`. -/
@[simp]
theorem complexSplitting_diagonal (r : Rˣ) : complexSplitting R (diagonal R r) = (r, r) := by
  ext <;> simp

/-- **The weight over a complex algebra** is `w(r) = (r⁻¹, r⁻¹)`. -/
@[simp]
theorem complexSplitting_weight (r : Rˣ) : complexSplitting R (weight R r) = (r⁻¹, r⁻¹) := by
  rw [weight_eq_inv_diagonal, map_inv (complexSplitting R), complexSplitting_diagonal, Prod.inv_mk]

/-- **The product of the two splitting components is the norm** over any commutative complex algebra
`R`. -/
theorem fst_mul_snd_complexSplitting (f : WithConv (S →ₐ[ℝ] R)) :
    (complexSplitting R f).1 * (complexSplitting R f).2 = norm R f := by
  have hcomm : Algebra.TensorProduct.comm ℝ R ℂ
      (Algebra.TensorProduct.comm ℝ ℂ R (pointsMulEquiv R f)) = pointsMulEquiv R f :=
    (Algebra.TensorProduct.comm ℝ ℂ R).symm_apply_apply _
  ext
  rw [Units.val_mul, coe_complexSplitting_fst, coe_complexSplitting_snd, norm_apply,
    NormTorus.coe_norm, norm_tensorProduct_complex, tensorProductComplexAlgEquiv_apply, hcomm]

end Splitting

/-- **Real points in the splitting**: the image in `S(ℂ)` of the real point `z ∈ S(ℝ) = ℂˣ` is
`(z, conj z)`. -/
theorem complexSplitting_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      (realPointsMulEquiv f, star (realPointsMulEquiv f)) := by
  obtain ⟨z, rfl⟩ := realPointsMulEquiv.symm.surjective f
  ext <;> simp only [coe_complexSplitting_fst, coe_complexSplitting_snd, pointsMulEquiv_mapValue,
    pointsMulEquiv_realPointsMulEquiv_symm, Units.coe_map, MonoidHom.coe_ofClass] <;>
    simp

/-- **Complex conjugation on `S(ℂ)`** acts by `(z₁, z₂) ↦ (conj z₂, conj z₁)`. -/
theorem complexSplitting_conj (f : WithConv (S →ₐ[ℝ] ℂ)) :
    complexSplitting ℂ (AlgHom.mapValue Complex.conjAe.toAlgHom f) =
      (star (complexSplitting ℂ f).2, star (complexSplitting ℂ f).1) := by
  ext <;> simp only [coe_complexSplitting_fst, coe_complexSplitting_snd, pointsMulEquiv_mapValue,
    Units.coe_map, MonoidHom.coe_ofClass, complexTensorProductEquivProd_lTensor_conjAe,
    Units.coe_star, Complex.star_def]

/-- **Characterization of real points inside `S(ℂ)`**: a complex point lies in the image of `S(ℝ)`
if and only if its two components under `complexSplitting ℂ` are `(z, conj z)`. -/
theorem mem_mrange_mapValue_ofId_iff (f : WithConv (S →ₐ[ℝ] ℂ)) :
    f ∈ MonoidHom.mrange (AlgHom.mapValue (Algebra.ofId ℝ ℂ)) ↔
      star (complexSplitting ℂ f).1 = (complexSplitting ℂ f).2 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [complexSplitting_real]
  · intro hf
    refine ⟨realPointsMulEquiv.symm (complexSplitting ℂ f).1, ?_⟩
    apply (complexSplitting ℂ).injective
    rw [complexSplitting_real, MulEquiv.apply_symm_apply]
    exact Prod.ext rfl hf

/-- On a real point mapped to `S(ℂ)`, the product of the two splitting components is `|z|²`. -/
theorem complexSplitting_mul_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (((complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f)).1 *
        (complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f)).2 : ℂˣ) : ℂ) =
      Complex.normSq (realPointsMulEquiv f) := by
  rw [fst_mul_snd_complexSplitting, norm_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
    Algebra.ofId_apply, coe_norm_real, Complex.coe_algebraMap]

/-- The real point `i` goes to `(i, -i)` in `S(ℂ) ≃ ℂˣ × ℂˣ`, which pins the order of the two
factors. -/
example : complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ)
      (realPointsMulEquiv.symm (Units.mk0 _ Complex.I_ne_zero))) =
    (Units.mk0 _ Complex.I_ne_zero, Units.mk0 (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero)) := by
  rw [complexSplitting_real, MulEquiv.apply_symm_apply]
  ext <;> simp

/-- **Scalar `I` versus real `I`**: the `ℂ`-point corresponding to `1 ⊗ I` in `(ℂ ⊗[ℝ] ℂ)ˣ` maps to
`(I, I)`, whereas the real point `I` (corresponding to `I ⊗ 1`) maps to `(I, -I)`. -/
theorem complexSplitting_scalar :
    complexSplitting ℂ ((pointsMulEquiv ℂ).symm
        (Units.map (Algebra.TensorProduct.includeRight : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ).toMonoidHom
          (Units.mk0 Complex.I Complex.I_ne_zero))) =
      (Units.mk0 Complex.I Complex.I_ne_zero, Units.mk0 Complex.I Complex.I_ne_zero) := by
  ext <;> simp [coe_complexSplitting_fst, coe_complexSplitting_snd]

/-- The `ℂ`-point with value `1 ⊗ i`, the diagonal `d(i)`, goes to `(i, i)`; compare the real point
`i`, with value `i ⊗ 1`, which goes to `(i, -i)`. -/
example : complexSplitting ℂ (diagonal ℂ (Units.mk0 _ Complex.I_ne_zero)) =
    (Units.mk0 _ Complex.I_ne_zero, Units.mk0 _ Complex.I_ne_zero) :=
  complexSplitting_diagonal _

/-! ### The cocharacter `μ` -/

section Mu

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **The cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ`** on points over a complex algebra, `z ↦ (z, 1)` in the
splitting `S(R) ≃ Rˣ × Rˣ`. -/
noncomputable def mu : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (complexSplitting R).symm.toMonoidHom.comp (MonoidHom.inl Rˣ Rˣ)

variable {R}

@[simp]
theorem complexSplitting_mu (z : Rˣ) : complexSplitting R (mu R z) = (z, 1) := by
  simp [mu]

/-- **Naturality of `μ` in `R`**: post-composing `μ(z)` with a complex algebra map `h : R → R'` is
`μ(h z)`. -/
theorem mapValue_mu {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (z : Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) (mu R z) = mu R' (Units.map (h : R →* R') z) := by
  apply (complexSplitting R').injective
  rw [complexSplitting_mapValue, complexSplitting_mu, complexSplitting_mu, map_one]

end Mu

/-- **`μ` is not defined over `ℝ`**: `μ(-1) = (-1, 1)` is not of the form `(z, conj z)`, so it is
not the image of a real point. -/
theorem mu_neg_one_notMem_range_mapValue :
    mu ℂ (-1) ∉ Set.range (AlgHom.mapValue (Algebra.ofId ℝ ℂ) (H := S)) := by
  rintro ⟨f, hf⟩
  have h := congrArg (complexSplitting ℂ) hf
  rw [complexSplitting_real, complexSplitting_mu, Prod.mk.injEq] at h
  have h2 := congrArg (fun u : ℂˣ ↦ (u : ℂ)) h.2
  norm_num [h.1] at h2

/-- **The weight is `μ` times its conjugate**: over `ℂ`, `w(r) = μ(r⁻¹) · μ'(r⁻¹)`, where
`μ'(z) = conj (μ (conj z)) = (1, z)` is the complex conjugate of `μ`. -/
theorem weight_eq_mu_mul_conj (r : ℂˣ) :
    weight ℂ r = mu ℂ r⁻¹ * AlgHom.mapValue Complex.conjAe.toAlgHom (mu ℂ (star r⁻¹)) := by
  apply (complexSplitting ℂ).injective
  rw [map_mul, complexSplitting_weight, complexSplitting_mu, complexSplitting_conj,
    complexSplitting_mu]
  simp

/-! ### Characters -/

section Character

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **The characters of the Deligne torus** on points over a complex algebra: the pair `(p, q)`
gives the character `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` of `S(R) ≃ Rˣ × Rˣ`. Over `ℂ` distinct pairs give
distinct characters (`characterGroup_injective`), so this embeds `ℤ²` as a group of characters of
`S(ℂ)`. -/
noncomputable def characterGroup : Multiplicative (ℤ × ℤ) →* (WithConv (S →ₐ[ℝ] R) →* Rˣ) where
  toFun pq :=
    { toFun f := (complexSplitting R f).1 ^ pq.toAdd.1 * (complexSplitting R f).2 ^ pq.toAdd.2
      map_one' := by simp
      map_mul' f g := by
        simp only [map_mul, Prod.fst_mul, Prod.snd_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }
  map_one' := MonoidHom.ext fun f ↦ by simp
  map_mul' pq pq' := MonoidHom.ext fun f ↦ by
    simp only [MonoidHom.mul_apply, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_mul, Prod.fst_add,
      Prod.snd_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

variable {R}

@[simp]
theorem characterGroup_apply (p q : ℤ) (f : WithConv (S →ₐ[ℝ] R)) :
    characterGroup R (.ofAdd (p, q)) f =
      (complexSplitting R f).1 ^ p * (complexSplitting R f).2 ^ q :=
  (rfl)

/-- The character of a sum of pairs is the product of the characters. -/
theorem characterGroup_add_apply (a b : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] R)) :
    characterGroup R (.ofAdd (a + b)) f =
      characterGroup R (.ofAdd a) f * characterGroup R (.ofAdd b) f := by
  rw [ofAdd_add, map_mul, MonoidHom.mul_apply]

/-- The character of the negative of a pair is the inverse of the character. -/
theorem characterGroup_neg_apply (a : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] R)) :
    characterGroup R (.ofAdd (-a)) f = (characterGroup R (.ofAdd a) f)⁻¹ := by
  rw [ofAdd_neg, map_inv, MonoidHom.inv_apply]

/-- The character `(p, q)` takes the value `z ^ p` on `μ(z)`; in particular `(1, 0)` takes the
value `z` and `(0, 1)` the value `1`. -/
theorem characterGroup_mu (p q : ℤ) (z : Rˣ) :
    characterGroup R (.ofAdd (p, q)) (mu R z) = z ^ p := by
  simp

/-- The character `(p, q)` takes the value `r ^ (p + q)` on the diagonal `d(r)`. -/
theorem characterGroup_diagonal (p q : ℤ) (r : Rˣ) :
    characterGroup R (.ofAdd (p, q)) (diagonal R r) = r ^ (p + q) := by
  simp [zpow_add]

/-- The character `(p, q)` takes the value `r ^ (-(p + q))` on the weight `w(r)`. -/
theorem characterGroup_weight (p q : ℤ) (r : Rˣ) :
    characterGroup R (.ofAdd (p, q)) (weight R r) = r ^ (-(p + q)) := by
  simp [zpow_neg, zpow_add, mul_comm]

/-- **Naturality of the characters in `R`**: the character `(p, q)` of a point post-composed with a
complex algebra map `h : R → R'` is `h` applied to the character `(p, q)` of the point. -/
theorem characterGroup_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (pq : Multiplicative (ℤ × ℤ))
    (f : WithConv (S →ₐ[ℝ] R)) :
    characterGroup R' pq (AlgHom.mapValue (h.restrictScalars ℝ) f) =
      Units.map (h : R →* R') (characterGroup R pq f) := by
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ pq' : ℤ × ℤ, Multiplicative.ofAdd pq' = pq := ⟨pq.toAdd, rfl⟩
  rw [characterGroup_apply, characterGroup_apply, complexSplitting_mapValue]
  simp

end Character

/-- **Complex conjugation exchanges the characters `(p, q)` and `(q, p)`**: the character `(p, q)`
of the conjugate of a point is the conjugate of the character `(q, p)` of the point. -/
theorem characterGroup_conj (p q : ℤ) (f : WithConv (S →ₐ[ℝ] ℂ)) :
    characterGroup ℂ (.ofAdd (p, q)) (AlgHom.mapValue Complex.conjAe.toAlgHom f) =
      star (characterGroup ℂ (.ofAdd (q, p)) f) := by
  rw [characterGroup_apply, characterGroup_apply, complexSplitting_conj]
  simp [mul_comm]

/-- **The character `(1, 1)` is the norm on real points**: on the image of a real point `z` it is
`z * conj z = |z|²`, the norm `Nm(z)`. -/
theorem characterGroup_norm (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (characterGroup ℂ (.ofAdd (1, 1)) (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) : ℂ) =
      (norm ℝ f : ℝ) := by
  rw [characterGroup_apply, complexSplitting_real, coe_norm_real]
  simp [Complex.mul_conj]

/-- **Distinct pairs give distinct characters of `S(ℂ)`**: `(p, q) ↦ ((z₁, z₂) ↦ z₁ ^ p * z₂ ^ q)`
is injective, so the characters `characterGroup ℂ` form a copy of `ℤ²`. -/
theorem characterGroup_injective : Function.Injective (characterGroup ℂ) := by
  rw [injective_iff_map_eq_one]
  intro pq h
  -- evaluate at the points `(2, 1)` and `(1, 2)` of `S(ℂ) ≃ ℂˣ × ℂˣ`
  have key (n : ℤ) (hn : Units.mk0 (2 : ℂ) two_ne_zero ^ n = 1) : n = 0 := by
    have := congrArg (fun u : ℂˣ ↦ ‖(u : ℂ)‖) hn
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Complex.norm_two,
      Units.val_one, norm_one] at this
    exact (zpow_eq_one_iff_right₀ zero_le_two (by norm_num)).mp this
  have h₁ := DFunLike.congr_fun h ((complexSplitting ℂ).symm (Units.mk0 2 two_ne_zero, 1))
  have h₂ := DFunLike.congr_fun h ((complexSplitting ℂ).symm (1, Units.mk0 2 two_ne_zero))
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ pq' : ℤ × ℤ, Multiplicative.ofAdd pq' = pq := ⟨pq.toAdd, rfl⟩
  simp only [characterGroup_apply, MulEquiv.apply_symm_apply, one_zpow, mul_one, one_mul,
    MonoidHom.one_apply] at h₁ h₂
  simp [key p h₁, key q h₂]

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

/-- **Naturality of `baseChangeComplexPointsMulEquiv` along `ℂ`-algebra homomorphisms.** -/
theorem baseChangeComplexPointsMulEquiv_mapValue {R R' : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) =
      AlgHom.mapValue (H := S) (φ.restrictScalars ℝ) (baseChangeComplexPointsMulEquiv R g) :=
  AlgHom.baseChangePointsMulEquiv_symm_mapValue
    (k := ℝ) (K := ℂ) (A := FiniteTypeCommHopfAlgCat.of ℝ S) φ g

/-- On a commutative `ℂ`-algebra `R`, `ℂ`-points of `baseChangeComplex` correspond naturally to
`ℂ`-points of `ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` through `complexSplitting R`. -/
private noncomputable def baseChangeProductPointsMulEquiv (R : Type*) [CommRing R] [Algebra ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃* WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R) :=
  (baseChangeComplexPointsMulEquiv R).trans <|
    (complexSplitting R).trans <|
      (MulEquiv.prodCongr MultiplicativeGroup.pointsMulEquiv.symm
        MultiplicativeGroup.pointsMulEquiv.symm).trans AffineGroup.Product.pointsMulEquiv.symm

private lemma mapValue_baseChangeProductPointsMulEquiv {R R' : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing R'] [Algebra ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) φ (baseChangeProductPointsMulEquiv R g) =
      baseChangeProductPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) := by
  simp only [baseChangeProductPointsMulEquiv, MulEquiv.trans_apply]
  rw [AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply,
    baseChangeComplexPointsMulEquiv_mapValue, complexSplitting_mapValue]
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

/-- **Scheme-level complex splitting of the Deligne torus**:
`baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` as commutative Hopf `ℂ`-algebras. -/
noncomputable def baseChangeComplexBialgEquiv :
    baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹] :=
  _root_.CommHopfAlgCat.ofIso
    (CommHopfAlgCat.isoOfPointsIso
      (H := _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]))
      (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
      baseChangeProductPointsNatIso.symm)

/-- **Compatibility of `baseChangeComplexBialgEquiv` with `complexSplitting` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
theorem mapDomain_baseChangeComplexBialgEquiv {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra ℂ R]
    [IsScalarTower ℝ ℂ R]
    (p : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) × WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    BialgHom.mapDomain baseChangeComplexBialgEquiv.toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p) =
      (baseChangeComplexPointsMulEquiv R).symm
        ((complexSplitting R).symm
          (MultiplicativeGroup.pointsMulEquiv p.1, MultiplicativeGroup.pointsMulEquiv p.2)) := by
  let H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]
  let f : WithConv (H →ₐ[ℂ] R) := AffineGroup.Product.pointsMulEquiv.symm p
  let idH : WithConv (H →ₐ[ℂ] H) := toConv (AlgHom.id ℂ H)
  have hdom := CommHopfAlgCat.mapDomain_homOfPointsMap
    (H := _root_.CommHopfAlgCat.of ℂ H)
    (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
    baseChangeProductPointsNatIso.inv f
  have hid : baseChangeProductPointsNatIso.inv.app (CommAlgCat.of ℂ H) idH =
      (baseChangeComplexPointsMulEquiv H).symm
        ((complexSplitting H).symm
          (MultiplicativeGroup.pointsMulEquiv (AffineGroup.Product.pointsMulEquiv idH).1,
            MultiplicativeGroup.pointsMulEquiv (AffineGroup.Product.pointsMulEquiv idH).2)) := by
    simp only [baseChangeProductPointsNatIso, NatIso.ofComponents_inv_app]
    rfl
  rw [baseChangeComplexBialgEquiv, BialgEquiv.toBialgHom_eq_coe, CommHopfAlgCat.coe_ofIso,
    CommHopfAlgCat.isoOfPointsIso_hom, Iso.symm_hom, hdom, hid]
  apply (baseChangeComplexPointsMulEquiv R).injective
  rw [MulEquiv.apply_symm_apply, baseChangeComplexPointsMulEquiv_mapValue,
    MulEquiv.apply_symm_apply, mapValue_complexSplitting_symm,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue,
    ← MultiplicativeGroup.pointsMulEquiv_mapValue,
    ← AffineGroup.Product.pointsMulEquiv_mapValue_fst,
    ← AffineGroup.Product.pointsMulEquiv_mapValue_snd]
  have hf : AlgHom.mapValue f.ofConv idH = f := by
    rw [AlgHom.mapValue_apply]
    exact (congrArg toConv (AlgHom.ext fun _ ↦ rfl)).trans (toConv_ofConv f)
  rw [hf]
  simp only [f, MulEquiv.apply_symm_apply]

end SchemeSplitting

/-! ### Algebraic torus property and non-splitness over `ℝ` -/

section TorusAndNotSplit

private noncomputable def baseChangeSplitTorusPointsMulEquiv (R : Type*) [CommRing R]
    [Algebra ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃*
      WithConv (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) →ₐ[ℂ] R) :=
  (baseChangeComplexPointsMulEquiv R).trans <|
    (complexSplitting R).trans <|
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
    baseChangeComplexPointsMulEquiv_mapValue, complexSplitting_mapValue]
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
  ObjectProperty.isoMk _ (CommHopfAlgCat.isoOfPointsIso baseChangeSplitTorusPointsNatIso)

/-- **Compatibility of `baseChangeSplitTorusIso` with `complexSplitting` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure: the two split-torus coordinates
of a base-changed point `g` are the two components of `complexSplitting R`. -/
theorem pointsMulEquiv_mapDomain_baseChangeSplitTorusIso {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    (SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨0⟩,
      SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨1⟩) =
      complexSplitting R (baseChangeComplexPointsMulEquiv R g) := by
  let idB : WithConv (baseChangeComplex →ₐ[ℂ] baseChangeComplex) :=
    toConv (AlgHom.id ℂ baseChangeComplex)
  have hdom := CommHopfAlgCat.mapDomain_homOfPointsMap
    (H := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
    (K := _root_.CommHopfAlgCat.of ℂ
      (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ))))
    baseChangeSplitTorusPointsNatIso.hom g
  have hid : baseChangeSplitTorusPointsNatIso.hom.app
      (CommAlgCat.of ℂ baseChangeComplex) idB =
      baseChangeSplitTorusPointsMulEquiv baseChangeComplex idB := by
    simp [baseChangeSplitTorusPointsNatIso]
    rfl
  rw [baseChangeSplitTorusIso, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    CommHopfAlgCat.isoOfPointsIso_hom, hdom, hid,
    SplitTorus.pointsMulEquiv_mapValue, SplitTorus.pointsMulEquiv_mapValue]
  have hsplit : complexSplitting R (baseChangeComplexPointsMulEquiv R g) =
      (Units.map (g.ofConv : baseChangeComplex →* R)
          (complexSplitting baseChangeComplex
            (baseChangeComplexPointsMulEquiv baseChangeComplex idB)).1,
        Units.map (g.ofConv : baseChangeComplex →* R)
          (complexSplitting baseChangeComplex
            (baseChangeComplexPointsMulEquiv baseChangeComplex idB)).2) := by
    rw [← complexSplitting_mapValue g.ofConv, ← baseChangeComplexPointsMulEquiv_mapValue]
    simp [idB, AlgHom.mapValue_apply]
  rw [hsplit]
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
  refine Infinite.of_injective
    (fun k : ℕ ↦ ⟨realPointsMulEquiv.symm (u k),
      isOfFinOrder_iff_pow_eq_one.2
        ⟨k + 1, Nat.succ_pos k, by rw [← map_pow, (hprim k).pow_eq_one, map_one]⟩⟩)
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
theorem not_splitTorusCommHopfAlgProperty_S :
    ¬ splitTorusCommHopfAlgProperty ℝ (FiniteTypeCommHopfAlgCat.of ℝ S) := by
  intro h
  obtain ⟨n, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff ℝ _).mp h
  let e : MonoidAlgebra ℝ (Multiplicative (ULift.{0} (Fin n) →₀ ℤ)) ≃ₐc[ℝ] S :=
    _root_.CommHopfAlgCat.ofIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{0, 0} ℝ) (_root_.CommHopfAlgCat.{0} ℝ)).mapIso i)
  exact (isEmpty_realPoints_mulEquiv_pi (ULift.{0} (Fin n))).false
    ((BialgEquiv.mapDomainMulEquiv (A := ℝ) e).trans SplitTorus.pointsMulEquiv)

end TorusAndNotSplit

end TauCeti.DeligneTorus
