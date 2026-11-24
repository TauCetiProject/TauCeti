/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic
public import TauCeti.RingTheory.TensorProduct.Complex
import TauCeti.RingTheory.NormTrace.Prod

/-!
# The splitting of the Deligne torus over `ℂ`

Over `ℂ` the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` splits: `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`. On points, for a complex
algebra `R` the points `S(R) = (ℂ ⊗[ℝ] R)ˣ` are identified with `Rˣ × Rˣ` through the splitting
`ℂ ⊗[ℝ] R ≃ R × R`, `a ⊗ x ↦ (a • x, conj a • x)` (`TauCeti.complexTensorProductEquivProd`). With
this normalization:

* a real point `z ∈ S(ℝ) = ℂˣ` goes to `(z, conj z)` in `S(ℂ)`, so the real point `i` goes to
  `(i, -i)`, which fixes the order of the two factors;
* complex conjugation of `S(ℂ)` acts by `(z₁, z₂) ↦ (conj z₂, conj z₁)`;
* the diagonal `d(r)` and the weight `w(r)` are `(r, r)` and `(r⁻¹, r⁻¹)`.

The cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ` is `z ↦ (z, 1)`. It is not defined over `ℝ`: `μ(-1) = (-1, 1)`
is not of the form `(z, conj z)`. The characters of `S` are `z₁ ^ p * z₂ ^ q` for `(p, q) ∈ ℤ²`,
and complex conjugation exchanges `(p, q)` and `(q, p)`. These are the conventions in which a real
Hodge structure of type `(p, q)` is a representation of `S` on which `z ∈ S(ℝ)` acts on the
`(p, q)`-summand by `z^{-p} conj(z)^{-q}`, and through which a cocharacter `μ` of a Shimura datum
is defined.

## Main definitions

* `TauCeti.DeligneTorus.complexSplitting R`: `S(R) ≃* Rˣ × Rˣ` for a complex algebra `R`.
* `TauCeti.DeligneTorus.mu R`: the cocharacter `μ : z ↦ (z, 1)` on points over a complex algebra.
* `TauCeti.DeligneTorus.characterGroup R`: the characters `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`, as a
  homomorphism from `ℤ²` (written multiplicatively) to the characters of `S(R)`.

## Main results

* `TauCeti.DeligneTorus.complexSplitting_mapValue`, `TauCeti.DeligneTorus.mapValue_mu`,
  `TauCeti.DeligneTorus.characterGroup_mapValue`: the splitting, `μ` and the characters are natural
  in `R`.
* `TauCeti.DeligneTorus.complexSplitting_real`: the image of a real point `z` is `(z, conj z)`.
* `TauCeti.DeligneTorus.complexSplitting_conj`: complex conjugation on `S(ℂ)` is
  `(z₁, z₂) ↦ (conj z₂, conj z₁)`.
* `TauCeti.DeligneTorus.complexSplitting_diagonal`, `TauCeti.DeligneTorus.complexSplitting_weight`:
  `d(r) = (r, r)` and `w(r) = (r⁻¹, r⁻¹)`.
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
* `TauCeti.DeligneTorus.coe_norm_eq_mul`, `TauCeti.DeligneTorus.norm_eq_characterGroup`: over a
  complex algebra the norm of a point with coordinates `(z₁, z₂)` is `z₁ * z₂`, the character
  `(1, 1)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The splitting `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` -/

section Splitting

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

/-- The real point `i` goes to `(i, -i)` in `S(ℂ) ≃ ℂˣ × ℂˣ`, which pins the order of the two
factors. -/
example : complexSplitting ℂ (AlgHom.mapValue (Algebra.ofId ℝ ℂ)
      (realPointsMulEquiv.symm (Units.mk0 _ Complex.I_ne_zero))) =
    (Units.mk0 _ Complex.I_ne_zero, Units.mk0 (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero)) := by
  rw [complexSplitting_real, MulEquiv.apply_symm_apply]
  ext <;> simp

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

end TauCeti.DeligneTorus
