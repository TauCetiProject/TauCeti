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
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
import TauCeti.Algebra.AlgebraicGroup.Torus.Splitting
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product
import TauCeti.Data.Finsupp.Fin

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
  (`TauCeti.DeligneTorus.complexSplitting_scalar_I`);
* complex conjugation of `S(ℂ)` acts by `(z₁, z₂) ↦ (conj z₂, conj z₁)`
  (`TauCeti.DeligneTorus.complexSplitting_conj`), cutting out `S(ℝ)` as its fixed locus
  (`TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`);
* the diagonal `d(r)` and the weight `w(r)` are `(r, r)` and `(r⁻¹, r⁻¹)`
  (`TauCeti.DeligneTorus.complexSplitting_diagonal`,
  `TauCeti.DeligneTorus.complexSplitting_weight`), and the product of the two components is the
  norm `Nm` (`TauCeti.DeligneTorus.fst_mul_snd_complexSplitting`).

The cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ` is `z ↦ (z, 1)` (`TauCeti.DeligneTorus.mu`). It is not
defined over `ℝ`: `μ(-1) = (-1, 1)` is not of the form `(z, conj z)`
(`TauCeti.DeligneTorus.mu_neg_one_notMem_range_mapValue`). The algebraic characters of `S_ℂ` are
classified by the pairs `(p, q) ∈ ℤ²`; on points over any complex algebra `R` they evaluate to the
homomorphisms `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` (`TauCeti.DeligneTorus.characterGroup R`), and complex
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
* `TauCeti.DeligneTorus.characterGroup R`: evaluation of the algebraic characters `(p, q) ∈ ℤ²` of
  `S_ℂ` on `R`-points, sending `(p, q)` to `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` on `S(R)`.
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
  `TauCeti.DeligneTorus.characterGroup_mapValue`: naturality in `R`.
* `TauCeti.DeligneTorus.complexSplitting_real`, `TauCeti.DeligneTorus.complexSplitting_scalar_I`,
  `TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`: real points versus complex scalar points,
  and characterization of `S(ℝ)` inside `S(ℂ)`.
* `TauCeti.DeligneTorus.complexSplitting_conj`: complex conjugation on `S(ℂ)` is
  `(z₁, z₂) ↦ (conj z₂, conj z₁)`.
* `TauCeti.DeligneTorus.complexSplitting_diagonal`, `TauCeti.DeligneTorus.complexSplitting_weight`,
  `TauCeti.DeligneTorus.fst_mul_snd_complexSplitting`: compatibility with `diagonal`, `weight`, and
  `norm`.
* `TauCeti.DeligneTorus.mu_neg_one_notMem_range_mapValue`: `μ` is not defined over `ℝ`.
* `TauCeti.DeligneTorus.characterGroup_injective`: distinct pairs `(p, q)` give distinct
  characters of `S(ℂ)`.
* `TauCeti.DeligneTorus.characterGroup_conj`: conjugation exchanges the characters `(p, q)` and
  `(q, p)`.
* `TauCeti.DeligneTorus.characterGroup_mu`, `TauCeti.DeligneTorus.characterGroup_weight`: the
  character `(p, q)` is `z ↦ z ^ p` on `μ(z)` and `r ↦ r ^ (-(p + q))` on the weight.
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

/-- The pair of values in `R` underlying `complexSplitting R f` is the image of the unit
`pointsMulEquiv R f` of `ℂ ⊗[ℝ] R` under `complexTensorProductEquivProd R`. -/
theorem coe_complexSplitting_apply (f : WithConv (S →ₐ[ℝ] R)) :
    (((complexSplitting R f).1 : R), ((complexSplitting R f).2 : R)) =
      complexTensorProductEquivProd R (pointsMulEquiv R f) :=
  Prod.ext (coe_complexSplitting_fst f) (coe_complexSplitting_snd f)

/-- On a unit `u` of `ℂ ⊗[ℝ] R` whose underlying element is a pure tensor `a ⊗ b`, the two
components of `complexSplitting R ((pointsMulEquiv R).symm u)` are `a • b` and `conj a • b`. -/
theorem coe_complexSplitting_components_of_val_eq_tmul {u : (ℂ ⊗[ℝ] R)ˣ} {a : ℂ} {b : R}
    (hu : (u : ℂ ⊗[ℝ] R) = a ⊗ₜ[ℝ] b) :
    ((complexSplitting R ((pointsMulEquiv R).symm u)).1 : R) = a • b ∧
      ((complexSplitting R ((pointsMulEquiv R).symm u)).2 : R) = starRingEnd ℂ a • b := by
  have h := coe_complexSplitting_apply ((pointsMulEquiv R).symm u)
  rw [MulEquiv.apply_symm_apply, hu, complexTensorProductEquivProd_tmul] at h
  exact Prod.mk.inj h

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

/-- The real point `i` goes to `(i, -i)` in `S(ℂ) ≃ ℂˣ × ℂˣ`, which pins the order of the two
factors. -/
example : complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ)
      (realPointsMulEquiv.symm (Units.mk0 _ Complex.I_ne_zero))) =
    (Units.mk0 _ Complex.I_ne_zero, Units.mk0 (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero)) := by
  rw [complexSplitting_real, MulEquiv.apply_symm_apply]
  ext <;> simp

/-- **Scalar `I` versus real `I`**: the `ℂ`-point corresponding to `1 ⊗ I` in `(ℂ ⊗[ℝ] ℂ)ˣ` maps to
`(I, I)`, whereas the real point `I` (corresponding to `I ⊗ 1`) maps to `(I, -I)`. -/
theorem complexSplitting_scalar_I :
    complexSplitting ℂ ((pointsMulEquiv ℂ).symm
        (Units.map (Algebra.TensorProduct.includeRight : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ).toMonoidHom
          (Units.mk0 Complex.I Complex.I_ne_zero))) =
      (Units.mk0 Complex.I Complex.I_ne_zero, Units.mk0 Complex.I Complex.I_ne_zero) := by
  rw [← pointsMulEquiv_diagonal, MulEquiv.symm_apply_apply, complexSplitting_diagonal]

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

/-! ### Characters -/

section Character

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **Evaluation of the algebraic characters of `S_ℂ` on `R`-points:** over a complex algebra `R`,
the pair `(p, q)` evaluates on `S(R) ≃ Rˣ × Rˣ` to the homomorphism `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`.
Over `ℂ`, distinct pairs give distinct homomorphisms (`characterGroup_injective`), embedding `ℤ²`
into `S(ℂ) →* ℂˣ`. -/
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
noncomputable abbrev baseChangeComplex : FiniteTypeCommHopfAlgCat.{0, 0} ℂ :=
  FiniteTypeCommHopfAlgCat.baseChange (K := ℂ) (FiniteTypeCommHopfAlgCat.of ℝ S)

/-- **Points of the base-changed Deligne torus `S_ℂ`** over a commutative `ℂ`-algebra `R` with
compatible `ℝ`-algebra structure identify with the `R`-points of `S`. -/
noncomputable abbrev baseChangeComplexPointsMulEquiv (R : Type*) [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃* WithConv (S →ₐ[ℝ] R) :=
  (AlgHom.baseChangePointsMulEquiv (k := ℝ) (K := ℂ)
    (A := FiniteTypeCommHopfAlgCat.of ℝ S) (R := R)).symm

/-- On a commutative `ℂ`-algebra `R`, `R`-points of `baseChangeComplex` (over `ℂ`) correspond
naturally to `R`-points of `ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` (over `ℂ`) through `complexSplitting R`. -/
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
  have hbc :
      baseChangeComplexPointsMulEquiv R' (AlgHom.mapValue (H := baseChangeComplex) φ g) =
        AlgHom.mapValue (H := S) (φ.restrictScalars ℝ) (baseChangeComplexPointsMulEquiv R g) :=
    AlgHom.baseChangePointsMulEquiv_symm_mapValue
      (k := ℝ) (K := ℂ) (A := FiniteTypeCommHopfAlgCat.of ℝ S) φ g
  simp only [baseChangeProductPointsMulEquiv, MulEquiv.trans_apply]
  rw [AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply, hbc, complexSplitting_mapValue]
  congr 1
  exact Prod.ext (MultiplicativeGroup.mapValue_pointsMulEquiv_symm_apply _ _)
    (MultiplicativeGroup.mapValue_pointsMulEquiv_symm_apply _ _)

private lemma mapValue_baseChangeProductPointsMulEquiv_symm {R R' : Type*} [CommRing R]
    [Algebra ℂ R] [CommRing R'] [Algebra ℂ R'] (φ : R →ₐ[ℂ] R')
    (f : WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := baseChangeComplex) φ
        ((baseChangeProductPointsMulEquiv R).symm f) =
      (baseChangeProductPointsMulEquiv R').symm
        (AlgHom.mapValue (H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) φ f) := by
  apply (baseChangeProductPointsMulEquiv R').injective
  rw [← mapValue_baseChangeProductPointsMulEquiv, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

private lemma baseChangeProductPointsMulEquiv_symm_eq {R : Type*} [CommRing R] [Algebra ℂ R] :
    ∀ (instR : Algebra ℝ R) (hT : @IsScalarTower ℝ ℂ R _ _ instR.toSMul)
      (p : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) × WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)),
    (baseChangeProductPointsMulEquiv R).symm (AffineGroup.Product.pointsMulEquiv.symm p) =
      (@baseChangeComplexPointsMulEquiv R _ instR _ hT).symm
        ((@complexSplitting R _ instR _ hT).symm
          (MultiplicativeGroup.pointsMulEquiv p.1, MultiplicativeGroup.pointsMulEquiv p.2)) := by
  let inst0 : Algebra ℝ R := inferInstance
  let ht0 : IsScalarTower ℝ ℂ R := inferInstance
  intro instR hT p
  have h1 : ∀ r : ℝ, @algebraMap ℝ R _ _ instR r = algebraMap ℂ R (algebraMap ℝ ℂ r) :=
    @IsScalarTower.algebraMap_apply ℝ ℂ R _ _ _ _ _ instR hT
  have h2 : ∀ r : ℝ, @algebraMap ℝ R _ _ inst0 r = algebraMap ℂ R (algebraMap ℝ ℂ r) :=
    @IsScalarTower.algebraMap_apply ℝ ℂ R _ _ _ _ _ inst0 ht0
  obtain rfl : instR = inst0 := Algebra.algebra_ext _ _ fun r ↦
    (h1 r).trans (h2 r).symm
  obtain rfl : hT = ht0 := Subsingleton.elim _ _
  simp only [baseChangeProductPointsMulEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  rfl

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
    ((CommHopfAlgCat.pointsFunctor (R := ℂ)).preimageIso
      (X := Opposite.op (_root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹])))
      (Y := Opposite.op (_root_.CommHopfAlgCat.of ℂ baseChangeComplex))
      baseChangeProductPointsNatIso.symm).unop

/-- **Compatibility of `baseChangeComplexBialgEquiv` with `complexSplitting` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
@[simp↓]
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
  have hhom : baseChangeComplexBialgEquiv.toBialgHom =
      (CommHopfAlgCat.homOfPointsMap
        (H := _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]))
        (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
        baseChangeProductPointsNatIso.inv).hom := by
    rw [baseChangeComplexBialgEquiv, BialgEquiv.toBialgHom_eq_coe, CommHopfAlgCat.coe_ofIso]
    congr 1
    apply Quiver.Hom.op_inj
    apply (CommHopfAlgCat.pointsFunctor (R := ℂ) :
      (_root_.CommHopfAlgCat ℂ)ᵒᵖ ⥤ CommAlgCat ℂ ⥤ GrpCat).map_injective
    rw [Iso.unop_hom, Quiver.Hom.op_unop]
    have hlhs :
        (CommHopfAlgCat.pointsFunctor (R := ℂ) :
          (_root_.CommHopfAlgCat ℂ)ᵒᵖ ⥤ CommAlgCat ℂ ⥤ GrpCat).map
            ((CommHopfAlgCat.pointsFunctor (R := ℂ)).preimageIso
              (X := Opposite.op (_root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹])))
              (Y := Opposite.op (_root_.CommHopfAlgCat.of ℂ baseChangeComplex))
              baseChangeProductPointsNatIso.symm).hom =
          baseChangeProductPointsNatIso.inv :=
      Functor.map_preimage
        (CommHopfAlgCat.pointsFunctor (R := ℂ) :
          (_root_.CommHopfAlgCat ℂ)ᵒᵖ ⥤ CommAlgCat ℂ ⥤ GrpCat)
        _
    rw [hlhs, CommHopfAlgCat.pointsFunctor_map, Quiver.Hom.unop_op,
      CommHopfAlgCat.mapPointsFunctor_homOfPointsMap]
  have hdom := CommHopfAlgCat.mapDomain_homOfPointsMap_of_natural
    (H := _root_.CommHopfAlgCat.of ℂ H)
    (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
    baseChangeProductPointsNatIso.inv
    ((baseChangeProductPointsMulEquiv H).symm idH)
    (baseChangeProductPointsMulEquiv R).symm
    (by simp only [baseChangeProductPointsNatIso, NatIso.ofComponents_inv_app]; rfl)
    (fun g ↦ by
      rw [mapValue_baseChangeProductPointsMulEquiv_symm]
      congr 1
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro x
      simp only [idH, AlgHom.mapValue_apply]
      rfl)
    f
  rw [hhom, hdom]
  exact baseChangeProductPointsMulEquiv_symm_eq _ _ p

end SchemeSplitting

/-! ### Algebraic torus property and non-splitness over `ℝ` -/

section TorusAndNotSplit

private noncomputable def finTwoFinsuppMulEquiv :
    Multiplicative (ULift.{0} (Fin 2) →₀ ℤ) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  let eAdd : (ULift.{0} (Fin 2) →₀ ℤ) ≃+ ℤ × ℤ :=
    (Finsupp.domCongr (M := ℤ) Equiv.ulift).trans (Finsupp.finTwoAddEquiv ℤ)
  { toFun x := (Multiplicative.ofAdd (eAdd x.toAdd).1, Multiplicative.ofAdd (eAdd x.toAdd).2)
    invFun p := Multiplicative.ofAdd (eAdd.symm (p.1.toAdd, p.2.toAdd))
    left_inv x := by simp [toAdd_ofAdd]
    right_inv p := by simp [eAdd.apply_symm_apply]
    map_mul' x y := by simp [map_add, ofAdd_add] }

private lemma finTwoFinsuppMulEquiv_single_zero :
    finTwoFinsuppMulEquiv (Multiplicative.ofAdd (Finsupp.single ⟨0⟩ 1)) =
      (Multiplicative.ofAdd (1 : ℤ), 1) := by
  simp [finTwoFinsuppMulEquiv, Equiv.ulift, ofAdd_zero]

private lemma finTwoFinsuppMulEquiv_single_one :
    finTwoFinsuppMulEquiv (Multiplicative.ofAdd (Finsupp.single ⟨1⟩ 1)) =
      (1, Multiplicative.ofAdd (1 : ℤ)) := by
  simp [finTwoFinsuppMulEquiv, Equiv.ulift, ofAdd_zero]

private noncomputable def splitTorusTensorBialgEquiv :
    MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) ≃ₐc[ℂ]
      ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹] :=
  let eL := (AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ).symm
  let eTensor :
      MonoidAlgebra ℂ (Multiplicative ℤ) ⊗[ℂ] MonoidAlgebra ℂ (Multiplicative ℤ) ≃ₐc[ℂ]
        ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹] :=
    BialgEquiv.ofBialgHom
      (_root_.Bialgebra.TensorProduct.map eL.toBialgHom eL.toBialgHom)
      (_root_.Bialgebra.TensorProduct.map eL.symm.toBialgHom eL.symm.toBialgHom)
      (Bialgebra.TensorProduct.map_comp_map_eq_id eL.comp_symm eL.comp_symm)
      (Bialgebra.TensorProduct.map_comp_map_eq_id eL.symm_comp eL.symm_comp)
  (MonoidAlgebra.domCongrBialgEquiv ℂ ℂ finTwoFinsuppMulEquiv).trans
    ((MonoidAlgebra.prodTensorBialgEquiv ℂ).trans eTensor)

private lemma splitTorusTensorBialgEquiv_single_zero :
    splitTorusTensorBialgEquiv
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single ⟨0⟩ (1 : ℤ))) (1 : ℂ)) =
      LaurentPolynomial.T 1 ⊗ₜ[ℂ] (1 : ℂ[T;T⁻¹]) := by
  let eL := (AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ).symm
  change (_root_.Bialgebra.TensorProduct.map eL.toBialgHom eL.toBialgHom)
      ((MonoidAlgebra.prodTensorBialgEquiv ℂ)
        ((MonoidAlgebra.domCongr ℂ ℂ finTwoFinsuppMulEquiv)
          (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single ⟨0⟩ (1 : ℤ))) (1 : ℂ)))) =
    _
  rw [MonoidAlgebra.domCongr_single, finTwoFinsuppMulEquiv_single_zero,
    MonoidAlgebra.prodTensorBialgEquiv_single, _root_.Bialgebra.TensorProduct.map_tmul]
  simp only [eL, BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
    AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single, toAdd_ofAdd, toAdd_one]
  exact congrArg₂ (· ⊗ₜ[ℂ] ·) rfl LaurentPolynomial.T_zero

private lemma splitTorusTensorBialgEquiv_single_one :
    splitTorusTensorBialgEquiv
        (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single ⟨1⟩ (1 : ℤ))) (1 : ℂ)) =
      (1 : ℂ[T;T⁻¹]) ⊗ₜ[ℂ] LaurentPolynomial.T 1 := by
  let eL := (AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ).symm
  change (_root_.Bialgebra.TensorProduct.map eL.toBialgHom eL.toBialgHom)
      ((MonoidAlgebra.prodTensorBialgEquiv ℂ)
        ((MonoidAlgebra.domCongr ℂ ℂ finTwoFinsuppMulEquiv)
          (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single ⟨1⟩ (1 : ℤ))) (1 : ℂ)))) =
    _
  rw [MonoidAlgebra.domCongr_single, finTwoFinsuppMulEquiv_single_one,
    MonoidAlgebra.prodTensorBialgEquiv_single, _root_.Bialgebra.TensorProduct.map_tmul]
  simp only [eL, BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
    AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single, toAdd_ofAdd, toAdd_one]
  exact congrArg₂ (· ⊗ₜ[ℂ] ·) LaurentPolynomial.T_zero rfl

/-- Coordinate bialgebra isomorphism identifying the rank-two split torus with `baseChangeComplex`.
-/
noncomputable def baseChangeSplitTorusBialgEquiv :
    MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) ≃ₐc[ℂ] baseChangeComplex :=
  splitTorusTensorBialgEquiv.trans baseChangeComplexBialgEquiv.symm

/-- **Isomorphism between the base change of `S` to `ℂ` and the rank-two split torus.** -/
noncomputable def baseChangeSplitTorusIso :
    DiagonalizableGroup.coordinateRing ℂ (SplitTorus.characterGroup (ULift.{0} (Fin 2))) ≅
      baseChangeComplex :=
  ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk baseChangeSplitTorusBialgEquiv)

/-- The forward bialgebra morphism underlying `baseChangeSplitTorusIso` is
`baseChangeSplitTorusBialgEquiv`. -/
theorem baseChangeSplitTorusIso_hom_hom_hom :
    baseChangeSplitTorusIso.hom.hom.hom = baseChangeSplitTorusBialgEquiv.toBialgHom :=
  (rfl)

/-- **Compatibility of `baseChangeSplitTorusIso` with `complexSplitting` on points** over every
commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure: the two split-torus coordinates
of a base-changed point `g` are the two components of `complexSplitting R`. -/
theorem pointsMulEquiv_mapDomain_baseChangeSplitTorusIso {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    (SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨0⟩,
      SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨1⟩) =
      complexSplitting R (baseChangeComplexPointsMulEquiv R g) := by
  let c := complexSplitting R (baseChangeComplexPointsMulEquiv R g)
  let p : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) × WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) :=
    (MultiplicativeGroup.pointsMulEquiv.symm c.1, MultiplicativeGroup.pointsMulEquiv.symm c.2)
  have hg : BialgHom.mapDomain (baseChangeComplexBialgEquiv : _ →ₐc[ℂ] _)
      (AffineGroup.Product.pointsMulEquiv.symm p) = g := by
    rw [← BialgEquiv.toBialgHom_eq_coe, mapDomain_baseChangeComplexBialgEquiv]
    simp only [p, c, MulEquiv.apply_symm_apply, Prod.mk.eta, MulEquiv.symm_apply_apply]
  have hcancel : BialgHom.mapDomain (baseChangeComplexBialgEquiv.symm : _ →ₐc[ℂ] _) g =
      AffineGroup.Product.pointsMulEquiv.symm p := by
    rw [← hg, ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
      BialgEquiv.comp_symm, BialgHom.mapDomain_id, MonoidHom.id_apply]
  have hcomp : BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g =
      BialgHom.mapDomain splitTorusTensorBialgEquiv.toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p) := by
    rw [baseChangeSplitTorusIso_hom_hom_hom, baseChangeSplitTorusBialgEquiv,
      BialgEquiv.toBialgHom_eq_coe, BialgEquiv.trans_toBialgHom, BialgHom.mapDomain_comp,
      MonoidHom.comp_apply, hcancel, BialgEquiv.toBialgHom_eq_coe]
  rw [hcomp]
  apply Prod.ext <;> apply Units.ext
  · simp only [SplitTorus.pointsMulEquiv_apply_coe, BialgHom.mapDomain_apply,
      AlgHom.comp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, splitTorusTensorBialgEquiv_single_zero,
      AffineGroup.Product.pointsMulEquiv_symm_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one, p, MultiplicativeGroup.pointsMulEquiv_symm_apply,
      laurentEval_T, zpow_one, c]
  · simp only [SplitTorus.pointsMulEquiv_apply_coe, BialgHom.mapDomain_apply,
      AlgHom.comp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, splitTorusTensorBialgEquiv_single_one,
      AffineGroup.Product.pointsMulEquiv_symm_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, one_mul, p, MultiplicativeGroup.pointsMulEquiv_symm_apply,
      laurentEval_T, zpow_one, c]

@[simp↓]
theorem pointsMulEquiv_mapDomain_baseChangeSplitTorusIso_zero {R : Type*} [CommRing R]
    [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨0⟩ =
      (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).1 :=
  congrArg Prod.fst (pointsMulEquiv_mapDomain_baseChangeSplitTorusIso g)

@[simp↓]
theorem pointsMulEquiv_mapDomain_baseChangeSplitTorusIso_one {R : Type*} [CommRing R]
    [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g) ⟨1⟩ =
      (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).2 :=
  congrArg Prod.snd (pointsMulEquiv_mapDomain_baseChangeSplitTorusIso g)

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
