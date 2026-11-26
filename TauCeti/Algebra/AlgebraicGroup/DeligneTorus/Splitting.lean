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
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.CoordinateIso
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
import TauCeti.Algebra.AlgebraicGroup.Torus.Splitting
import TauCeti.RingTheory.NormTrace.Prod

/-!
# The splitting of the Deligne torus over `ℂ`

Over `ℂ` the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` splits: `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`. Throughout the point-level
sections below, `R` denotes a commutative `ℂ`-algebra equipped with a compatible `ℝ`-algebra
structure (`[Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]`). Over such an algebra `R`, the
points `S(R) = (ℂ ⊗[ℝ] R)ˣ` are identified with `Rˣ × Rˣ`
(`TauCeti.DeligneTorus.complexSplitting R`) through the splitting `ℂ ⊗[ℝ] R ≃ R × R`,
`a ⊗ x ↦ (a • x, conj a • x)` (`TauCeti.complexTensorProductEquivProd`). With this normalization:

* a real point `z ∈ S(ℝ) = ℂˣ` goes to `(z, conj z)` in `S(ℂ)`
  (`TauCeti.DeligneTorus.complexSplitting_real`), so the real point `i` goes to `(i, -i)`, which
  fixes the order of the two factors, whereas the scalar point `1 ⊗ i` goes to `(i, i)`;
* complex conjugation of `S(ℂ)` acts by `(z₁, z₂) ↦ (conj z₂, conj z₁)`
  (`TauCeti.DeligneTorus.complexSplitting_conj`), cutting out `S(ℝ)` as its fixed locus
  (`TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`);
* the diagonal `d(r)` and the weight `w(r)` are `(r, r)` and `(r⁻¹, r⁻¹)`
  (`TauCeti.DeligneTorus.complexSplitting_diagonal`,
  `TauCeti.DeligneTorus.complexSplitting_weight`), and the product of the two components is the
  norm `Nm` (`TauCeti.DeligneTorus.fst_mul_snd_complexSplitting`).

The cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ` is `z ↦ (z, 1)` (`TauCeti.DeligneTorus.mu`). It is not
defined over `ℝ`: `μ(-1) = (-1, 1)` is not of the form `(z, conj z)`
(`TauCeti.DeligneTorus.mu_neg_one_notMem_range_mapValue`). Over any `R` as above, integer pairs
`(p, q) ∈ ℤ²` evaluate on points to the homomorphisms `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`
(`TauCeti.DeligneTorus.characterGroup R`), distinct pairs yield distinct characters of `S(ℂ)`
(`TauCeti.DeligneTorus.characterGroup_injective`), and complex conjugation exchanges `(p, q)` and
`(q, p)`; the algebraic character-lattice isomorphism `X*(S_ℂ) ≃+ ℤ × ℤ` is established in
`TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Characters`. These are the conventions in which a
real Hodge structure of type `(p, q)` is a representation of `S` on which `z ∈ S(ℝ)` acts on the
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

* `TauCeti.DeligneTorus.complexSplitting R`: `S(R) ≃* Rˣ × Rˣ` for `R` as above.
* `TauCeti.DeligneTorus.mu R`: the cocharacter `μ : z ↦ (z, 1)` on `R`-points.
* `TauCeti.DeligneTorus.characterGroup R`: evaluation of integer pairs `(p, q) ∈ ℤ²` on
  `R`-points, sending `(p, q)` to `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` on `S(R)`.
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
* `TauCeti.DeligneTorus.complexSplitting_real`,
  `TauCeti.DeligneTorus.mem_mrange_mapValue_ofId_iff`: real points and characterization of `S(ℝ)`
  inside `S(ℂ)`.
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
* `TauCeti.DeligneTorus.coe_norm_eq_mul`, `TauCeti.DeligneTorus.norm_eq_characterGroup`,
  `TauCeti.DeligneTorus.norm_zpow_eq_characterGroup`: over a complex algebra the norm of a point
  with coordinates `(z₁, z₂)` is `z₁ * z₂`, the character `(1, 1)`, and its `m`-th power is
  `(m, m)`.
* `TauCeti.DeligneTorus.mapDomain_baseChangeComplexBialgEquiv` and
  `TauCeti.DeligneTorus.mapDomain_baseChangeComplexBialgEquiv_symm`: point compatibility in both
  directions for `baseChangeComplexBialgEquiv`.
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

/-- **Naturality of the splitting in `R`**: post-composing a point with a complex algebra map
`h : R → R'` applies `h` to both components. -/
theorem complexSplitting_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (f : WithConv (S →ₐ[ℝ] R)) :
    complexSplitting R' (AlgHom.mapValue (h.restrictScalars ℝ) f) =
      (Units.map (h : R →* R') (complexSplitting R f).1,
        Units.map (h : R →* R') (complexSplitting R f).2) := by
  ext <;> simp only [coe_complexSplitting_fst, coe_complexSplitting_snd, pointsMulEquiv_mapValue,
    Units.coe_map, MonoidHom.coe_ofClass, complexTensorProductEquivProd_lTensor]

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
    NormTorus.coe_norm, norm_tensorProduct_complex, tensorProductComplexEquivProd_apply, hcomm]

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
example :
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

/-- **The norm over a complex algebra**: a point of `S` with coordinates `(z₁, z₂)` in
`S(R) ≃ Rˣ × Rˣ` has norm `z₁ * z₂`. -/
theorem coe_norm_eq_mul (f : WithConv (S →ₐ[ℝ] R)) :
    (norm R f : R) = (complexSplitting R f).1 * (complexSplitting R f).2 := by
  -- `R ⊗[ℝ] ℂ ≃ₐ[R] R × R`, `x ⊗ a ↦ (a • x, conj a • x)`; the type is not written out, since
  -- with `Algebra ℂ R` in scope the notation `R ⊗[ℝ] ℂ` would pick the real structure of `ℂ`
  let e := AlgEquiv.ofRingEquiv (R := R)
    (f := ((Algebra.TensorProduct.comm ℝ ℂ R).symm.trans
      (complexTensorProductEquivProd R)).toRingEquiv)
    fun r ↦ by simp [Algebra.TensorProduct.algebraMap_apply]
  have he : ∀ x, e (Algebra.TensorProduct.comm ℝ ℂ R x) = complexTensorProductEquivProd R x :=
    fun x ↦ congrArg (complexTensorProductEquivProd R)
      ((Algebra.TensorProduct.comm ℝ ℂ R).symm_apply_apply x)
  rw [norm_apply, NormTorus.coe_norm, ← Algebra.norm_eq_of_algEquiv e, Algebra.norm_prod]
  simp [he, coe_complexSplitting_fst, coe_complexSplitting_snd]

/-- **The norm is the character `(1, 1)`** of `S(R) ≃ Rˣ × Rˣ`, `(z₁, z₂) ↦ z₁ * z₂`. -/
theorem norm_eq_characterGroup (f : WithConv (S →ₐ[ℝ] R)) :
    norm R f = characterGroup R (.ofAdd (1, 1)) f :=
  Units.ext <| by rw [coe_norm_eq_mul, characterGroup_apply, zpow_one, zpow_one, Units.val_mul]

/-- The `m`-th power of the norm is the character `(m, m)`. -/
theorem norm_zpow_eq_characterGroup (f : WithConv (S →ₐ[ℝ] R)) (m : ℤ) :
    norm R f ^ m = characterGroup R (.ofAdd (m, m)) f := by
  rw [norm_eq_characterGroup, characterGroup_apply, characterGroup_apply, zpow_one, zpow_one,
    mul_zpow]

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

/-- The underlying `ℝ`-algebra map of `baseChangeComplexPointsMulEquiv R g` restricts `g` along
`a ↦ 1 ⊗ a`. -/
@[simp]
theorem ofConv_baseChangeComplexPointsMulEquiv {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    (baseChangeComplexPointsMulEquiv R g).ofConv = (AlgHom.liftEquiv ℝ ℂ S R).symm g.ofConv :=
  AlgHom.baseChangePointsMulEquiv_symm_ofConv g

/-- The underlying `ℂ`-algebra map of `(baseChangeComplexPointsMulEquiv R).symm f` is the
`ℂ`-linear lift of `f` to `ℂ ⊗[ℝ] S`. -/
@[simp]
theorem ofConv_baseChangeComplexPointsMulEquiv_symm {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (f : WithConv (S →ₐ[ℝ] R)) :
    ((baseChangeComplexPointsMulEquiv R).symm f).ofConv = AlgHom.liftEquiv ℝ ℂ S R f.ofConv :=
  AlgHom.baseChangePointsMulEquiv_apply_ofConv f

/-- On a commutative `ℂ`-algebra `R`, `R`-points of `baseChangeComplex` (over `ℂ`) correspond
naturally to `R`-points of `ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]` (over `ℂ`) through `complexSplitting R`. -/
private noncomputable def baseChangeProductPointsMulEquiv (R : Type*) [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] :
    WithConv (baseChangeComplex →ₐ[ℂ] R) ≃* WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R) :=
  (baseChangeComplexPointsMulEquiv R).trans <|
    (complexSplitting R).trans <|
      (MulEquiv.prodCongr MultiplicativeGroup.pointsMulEquiv.symm
        MultiplicativeGroup.pointsMulEquiv.symm).trans AffineGroup.Product.pointsMulEquiv.symm

private lemma mapValue_baseChangeProductPointsMulEquiv {R R' : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (φ : R →ₐ[ℂ] R') (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
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
    [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R] [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (φ : R →ₐ[ℂ] R')
    (f : WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := baseChangeComplex) φ
        ((baseChangeProductPointsMulEquiv R).symm f) =
      (baseChangeProductPointsMulEquiv R').symm
        (AlgHom.mapValue (H := ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) φ f) := by
  apply (baseChangeProductPointsMulEquiv R').injective
  rw [← mapValue_baseChangeProductPointsMulEquiv, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

private lemma baseChangeProductPointsMulEquiv_symm_eq {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R]
    (p : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R) × WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    (baseChangeProductPointsMulEquiv R).symm (AffineGroup.Product.pointsMulEquiv.symm p) =
      (baseChangeComplexPointsMulEquiv R).symm
        ((complexSplitting R).symm
          (MultiplicativeGroup.pointsMulEquiv p.1, MultiplicativeGroup.pointsMulEquiv p.2)) := by
  simp only [baseChangeProductPointsMulEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  -- `(MulEquiv.prodCongr f g).symm` acts componentwise on products.
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
    { hom := CommHopfAlgCat.homOfPointsMap
        (H := _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]))
        (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
        baseChangeProductPointsNatIso.inv
      inv := CommHopfAlgCat.homOfPointsMap
        (H := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
        (K := _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]))
        baseChangeProductPointsNatIso.hom
      hom_inv_id := by
        rw [← CommHopfAlgCat.homOfPointsMap_comp, Iso.hom_inv_id, CommHopfAlgCat.homOfPointsMap_id]
      inv_hom_id := by
        rw [← CommHopfAlgCat.homOfPointsMap_comp, Iso.inv_hom_id,
          CommHopfAlgCat.homOfPointsMap_id] }

private lemma baseChangeComplexBialgEquiv_toBialgHom :
    baseChangeComplexBialgEquiv.toBialgHom =
      (CommHopfAlgCat.homOfPointsMap
        (H := _root_.CommHopfAlgCat.of ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]))
        (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
        baseChangeProductPointsNatIso.inv).hom := by
  rw [baseChangeComplexBialgEquiv, BialgEquiv.toBialgHom_eq_coe, CommHopfAlgCat.coe_ofIso]

private lemma mapValue_baseChangeProductPointsMulEquiv_symm_id {R : Type*} [CommRing R]
    [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]
    (g : WithConv ((ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]) →ₐ[ℂ] R)) :
    AlgHom.mapValue (H := baseChangeComplex) g.ofConv
        ((baseChangeProductPointsMulEquiv (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹])).symm
          (toConv (AlgHom.id ℂ (ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹])))) =
      (baseChangeProductPointsMulEquiv R).symm g := by
  rw [mapValue_baseChangeProductPointsMulEquiv_symm]
  congr 1
  apply WithConv.ofConv_injective
  simp [AlgHom.mapValue_apply]

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
  have hid :
      baseChangeProductPointsNatIso.inv.app (CommAlgCat.of ℂ H) (toConv (AlgHom.id ℂ H)) =
        (baseChangeProductPointsMulEquiv H).symm (toConv (AlgHom.id ℂ H)) := by
    rw [baseChangeProductPointsNatIso, NatIso.ofComponents_inv_app _ _]
    dsimp only [MulEquiv.toGrpIso]
    rw [ConcreteCategory.hom_ofHom, MulEquiv.coe_toMonoidHom]
    -- `CommAlgCat.of ℂ H` and `H` share the same `ℂ`-algebra and inferred `ℝ`-algebra instances.
    rfl
  rw [baseChangeComplexBialgEquiv_toBialgHom,
    CommHopfAlgCat.mapDomain_homOfPointsMap (R := ℂ)
      (H := _root_.CommHopfAlgCat.of ℂ H)
      (K := _root_.CommHopfAlgCat.of ℂ baseChangeComplex)
      baseChangeProductPointsNatIso.inv,
    hid, mapValue_baseChangeProductPointsMulEquiv_symm_id]
  exact baseChangeProductPointsMulEquiv_symm_eq p

/-- **Compatibility of `baseChangeComplexBialgEquiv.symm` with `complexSplitting` on points** over
every commutative `ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
@[simp↓]
theorem mapDomain_baseChangeComplexBialgEquiv_symm {R : Type*} [CommRing R] [Algebra ℝ R]
    [Algebra ℂ R] [IsScalarTower ℝ ℂ R] (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    BialgHom.mapDomain baseChangeComplexBialgEquiv.symm.toBialgHom g =
      AffineGroup.Product.pointsMulEquiv.symm
        ((MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := R)).symm
            (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).1,
          (MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := R)).symm
            (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).2) := by
  have hg :
      BialgEquiv.mapDomainMulEquiv (A := R) baseChangeComplexBialgEquiv
        (AffineGroup.Product.pointsMulEquiv.symm
          ((MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := R)).symm
              (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).1,
            (MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := R)).symm
              (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).2)) = g := by
    rw [BialgEquiv.mapDomainMulEquiv_apply, ← BialgEquiv.toBialgHom_eq_coe,
      mapDomain_baseChangeComplexBialgEquiv]
    simp
  rw [BialgEquiv.toBialgHom_eq_coe, ← BialgEquiv.mapDomainMulEquiv_symm_apply,
    MulEquiv.symm_apply_eq]
  exact hg.symm

end SchemeSplitting

/-! ### Algebraic torus property and non-splitness over `ℝ` -/

section TorusAndNotSplit

/-- Coordinate bialgebra isomorphism identifying the rank-two split torus with `baseChangeComplex`.
-/
noncomputable def baseChangeSplitTorusBialgEquiv :
    MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) ≃ₐc[ℂ] baseChangeComplex :=
  (SplitTorus.rankTwoTensorBialgEquiv.{0} ℂ).trans baseChangeComplexBialgEquiv.symm

/-- The forward bialgebra morphism of `baseChangeSplitTorusBialgEquiv` factors through
`SplitTorus.rankTwoTensorBialgEquiv` and `baseChangeComplexBialgEquiv.symm`. -/
theorem baseChangeSplitTorusBialgEquiv_toBialgHom :
    baseChangeSplitTorusBialgEquiv.toBialgHom =
      baseChangeComplexBialgEquiv.symm.toBialgHom.comp
        (SplitTorus.rankTwoTensorBialgEquiv.{0} ℂ).toBialgHom := by
  rw [baseChangeSplitTorusBialgEquiv, BialgEquiv.toBialgHom_eq_coe, BialgEquiv.trans_toBialgHom]
  simp only [BialgEquiv.toBialgHom_eq_coe]

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
  rw [baseChangeSplitTorusIso_hom_hom_hom, baseChangeSplitTorusBialgEquiv_toBialgHom,
    BialgHom.mapDomain_comp, MonoidHom.comp_apply, mapDomain_baseChangeComplexBialgEquiv_symm,
    SplitTorus.pointsMulEquiv_mapDomain_rankTwoTensorBialgEquiv]
  simp

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
  let f : ℂˣ →* WithConv (S →ₐ[ℝ] ℝ) := realPointsMulEquiv.symm.toMonoidHom
  refine Infinite.of_injective
    (fun k : ℕ ↦ ⟨f (u k),
      (Function.Injective.isOfFinOrder_iff (f := f) realPointsMulEquiv.symm.injective).2
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
  let uI : ℂˣ := (Complex.isPrimitiveRoot_I.isUnit (by norm_num)).unit
  let ψ : ℂˣ ≃* (σ → ℝˣ) := realPointsMulEquiv.symm.trans e
  have hprim : IsPrimitiveRoot (ψ uI) 4 :=
    (Complex.isPrimitiveRoot_I.isUnit_unit (by norm_num)).map_of_injective ψ.injective
  have h2 : ψ uI ^ 2 = 1 := funext fun i ↦ Units.ext <| by
    have hi4 : ((ψ uI i : ℝˣ) : ℝ) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Pi.pow_apply, hprim.pow_eq_one, Pi.one_apply, Units.val_one]
    rcases (pow_eq_one_iff_of_ne_zero (by positivity : 4 ≠ 0)).mp hi4 with h1 | ⟨hm1, -⟩
    · simp [h1]
    · simp [hm1]
  exact absurd (hprim.dvd_of_pow_eq_one 2 h2) (by norm_num)

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
