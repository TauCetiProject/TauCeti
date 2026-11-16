/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic
public import TauCeti.RingTheory.TensorProduct.Complex

/-!
# The complex points of the Deligne torus

Over `ℂ` the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` splits: its complex points are the units of
`ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ` (`TauCeti.complexTensorEquivProd`, `a ⊗ b ↦ (a * b, conj a * b)`), so
`S(ℂ) ≃* ℂˣ × ℂˣ` (`TauCeti.DeligneTorus.complexSplitting`). In this splitting, following Milne's
conventions for Hodge structures:

* a real point `z ∈ S(ℝ) = ℂˣ` becomes `(z, conj z)`, so `i ↦ (i, -i)`, and the product of the two
  components is the norm `z * conj z = |z|²`;
* the diagonal and the weight over `ℂ` are `r ↦ (r, r)` and `r ↦ (r⁻¹, r⁻¹)`; in particular the
  complex point `1 ⊗ i` becomes `(i, i)`;
* complex conjugation of the coefficients acts on `S(ℂ)` by `(z₁, z₂) ↦ (conj z₂, conj z₁)`;
* the cocharacter `μ : 𝔾ₘ → S` over `ℂ` is `z ↦ (z, 1)`; it is not defined over `ℝ`, and the
  weight is `w(r) = μ(r⁻¹) * μ̄(r⁻¹)` where `μ̄ : z ↦ (1, z)` is the conjugate of `μ`;
* the characters of `S(ℂ)` are `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` for `(p, q) ∈ ℤ × ℤ`, these are
  pairwise distinct, conjugation exchanges `(p, q)` and `(q, p)`, the character `(1, 1)` is the norm
  on real points and the character `(p, q)` is `r ↦ r ^ (-(p + q))` on the weight.

Finally, `S` is not split: `S(ℝ) = ℂˣ` contains the element `i` of order `4`, while every
element `x` of `ℝˣ × ℝˣ` with `x ^ 4 = 1` satisfies `x ^ 2 = 1`.

## Main definitions

* `TauCeti.DeligneTorus.complexSplitting`: `S(ℂ) ≃* ℂˣ × ℂˣ`.
* `TauCeti.DeligneTorus.mu`: the cocharacter `μ : z ↦ (z, 1)` on complex points.
* `TauCeti.DeligneTorus.characterGroup`: the characters `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` of `S(ℂ)`,
  as a homomorphism from `ℤ × ℤ`.

## Main results

* `TauCeti.DeligneTorus.complexSplitting_mapValue_ofId`: `S(ℝ) → S(ℂ)` is `z ↦ (z, conj z)`.
* `TauCeti.DeligneTorus.complexSplitting_mapValue_conjAe`: conjugation acts on `S(ℂ)` by
  `(z₁, z₂) ↦ (conj z₂, conj z₁)`.
* `TauCeti.DeligneTorus.weight_eq_mu_mul_mapValue_conjAe_mu`: `w(r) = μ(r⁻¹) * μ̄(r⁻¹)`.
* `TauCeti.DeligneTorus.mu_not_mem_mrange_mapValue_ofId`: `μ` is not defined over `ℝ`.
* `TauCeti.DeligneTorus.characterGroup_injective`,
  `TauCeti.DeligneTorus.characterGroup_mapValue_conjAe`: the characters are pairwise distinct, and
  conjugation exchanges `(p, q)` and `(q, p)`.
* `TauCeti.DeligneTorus.isEmpty_realPoints_mulEquiv_units_prod`: `S(ℝ)` is not isomorphic to
  `ℝˣ × ℝˣ`, so `S` is not split.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open AlgHom
open scoped ComplexConjugate TensorProduct

namespace TauCeti.DeligneTorus

/-- **The splitting of the Deligne torus over `ℂ`**: `S(ℂ) ≃* ℂˣ × ℂˣ`, through the units of
`ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ`, `a ⊗ b ↦ (a * b, conj a * b)`. -/
noncomputable def complexSplitting : WithConv (S →ₐ[ℝ] ℂ) ≃* ℂˣ × ℂˣ :=
  (pointsMulEquiv ℂ).trans
    ((Units.mapEquiv complexTensorEquivProd.toMulEquiv).trans MulEquiv.prodUnits)

/-- The first component of the splitting of a complex point is the first component of its unit
in `ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ`. -/
@[simp]
theorem coe_complexSplitting_fst (x : WithConv (S →ₐ[ℝ] ℂ)) :
    ((complexSplitting x).1 : ℂ) = (complexTensorEquivProd (pointsMulEquiv ℂ x : ℂ ⊗[ℝ] ℂ)).1 :=
  (rfl)

/-- The second component of the splitting of a complex point is the second component of its unit
in `ℂ ⊗[ℝ] ℂ ≃ ℂ × ℂ`. -/
@[simp]
theorem coe_complexSplitting_snd (x : WithConv (S →ₐ[ℝ] ℂ)) :
    ((complexSplitting x).2 : ℂ) = (complexTensorEquivProd (pointsMulEquiv ℂ x : ℂ ⊗[ℝ] ℂ)).2 :=
  (rfl)

/-- **Real points in the splitting**: the map `S(ℝ) → S(ℂ)` is `z ↦ (z, conj z)`. -/
theorem complexSplitting_mapValue_ofId (f : WithConv (S →ₐ[ℝ] ℝ)) :
    complexSplitting (mapValue (Algebra.ofId ℝ ℂ) f) =
      (realPointsMulEquiv f, star (realPointsMulEquiv f)) := by
  obtain ⟨z, rfl⟩ := realPointsMulEquiv.symm.surjective f
  -- the real point `z` is the unit `z ⊗ 1` of `ℂ ⊗[ℝ] ℝ`, which stays `z ⊗ 1` in `ℂ ⊗[ℝ] ℂ`
  have h : (pointsMulEquiv ℂ (mapValue (Algebra.ofId ℝ ℂ) (realPointsMulEquiv.symm z)) :
      ℂ ⊗[ℝ] ℂ) = (z : ℂ) ⊗ₜ 1 := by
    rw [pointsMulEquiv_mapValue, pointsMulEquiv_realPointsMulEquiv_symm]
    simp
  rw [MulEquiv.apply_symm_apply]
  ext
  · rw [coe_complexSplitting_fst, h]
    simp
  · rw [coe_complexSplitting_snd, h]
    simp

/-- The real point `i ∈ S(ℝ) = ℂˣ` becomes `(i, -i)` in `S(ℂ) ≃ ℂˣ × ℂˣ`; this pins the order of
the two factors. -/
theorem complexSplitting_I :
    complexSplitting (mapValue (Algebra.ofId ℝ ℂ)
        (realPointsMulEquiv.symm (Units.mk0 Complex.I Complex.I_ne_zero))) =
      (Units.mk0 Complex.I Complex.I_ne_zero,
        Units.mk0 (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero)) := by
  rw [complexSplitting_mapValue_ofId, MulEquiv.apply_symm_apply]
  ext <;> simp

/-- On a real point `z`, the product of the two components of the splitting is the norm
`z * conj z = |z|²`. -/
theorem complexSplitting_fst_mul_snd_mapValue_ofId (f : WithConv (S →ₐ[ℝ] ℝ)) :
    ((complexSplitting (mapValue (Algebra.ofId ℝ ℂ) f)).1 *
        (complexSplitting (mapValue (Algebra.ofId ℝ ℂ) f)).2 : ℂ) = (norm ℝ f : ℝ) := by
  rw [complexSplitting_mapValue_ofId, coe_norm_real]
  simp [Complex.mul_conj]

/-- **The diagonal over `ℂ`** is `r ↦ (r, r)`. -/
@[simp]
theorem complexSplitting_diagonal (r : ℂˣ) : complexSplitting (diagonal ℂ r) = (r, r) := by
  ext <;> simp

/-- **The weight over `ℂ`** is `r ↦ (r⁻¹, r⁻¹)`. -/
@[simp]
theorem complexSplitting_weight (r : ℂˣ) : complexSplitting (weight ℂ r) = (r⁻¹, r⁻¹) := by
  rw [weight_eq_inv_diagonal, map_inv complexSplitting, complexSplitting_diagonal, Prod.inv_mk]

/-- **Complex conjugation on `S(ℂ)`.** Applying complex conjugation to the values of a complex point
acts on `S(ℂ) ≃ ℂˣ × ℂˣ` by `(z₁, z₂) ↦ (conj z₂, conj z₁)`. -/
theorem complexSplitting_mapValue_conjAe (x : WithConv (S →ₐ[ℝ] ℂ)) :
    complexSplitting (mapValue Complex.conjAe.toAlgHom x) =
      (star (complexSplitting x).2, star (complexSplitting x).1) := by
  ext
  · rw [coe_complexSplitting_fst, pointsMulEquiv_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
      complexTensorEquivProd_map_conjAe, Units.coe_star, coe_complexSplitting_snd,
      Complex.star_def]
  · rw [coe_complexSplitting_snd, pointsMulEquiv_mapValue, Units.coe_map, MonoidHom.coe_ofClass,
      complexTensorEquivProd_map_conjAe, Units.coe_star, coe_complexSplitting_fst,
      Complex.star_def]

/-! ### The cocharacter `μ` -/

/-- **The cocharacter `μ : 𝔾ₘ → S` over `ℂ`**, on complex points `z ↦ (z, 1)`. -/
noncomputable def mu : ℂˣ →* WithConv (S →ₐ[ℝ] ℂ) :=
  complexSplitting.symm.toMonoidHom.comp (MonoidHom.inl ℂˣ ℂˣ)

/-- `μ(z) = (z, 1)` in `S(ℂ) ≃ ℂˣ × ℂˣ`. -/
@[simp]
theorem complexSplitting_mu (z : ℂˣ) : complexSplitting (mu z) = (z, 1) := by
  simp [mu]

/-- The conjugate `μ̄` of `μ`, that is `z ↦ conj (μ (conj z))`, is `z ↦ (1, z)`. -/
theorem complexSplitting_mapValue_conjAe_mu (z : ℂˣ) :
    complexSplitting (mapValue Complex.conjAe.toAlgHom (mu (star z))) = (1, z) := by
  rw [complexSplitting_mapValue_conjAe, complexSplitting_mu, star_one, star_star]

/-- **The weight is `μ` times its conjugate**: `w(r) = μ(r⁻¹) * μ̄(r⁻¹)` over `ℂ`. -/
theorem weight_eq_mu_mul_mapValue_conjAe_mu (r : ℂˣ) :
    weight ℂ r = mu r⁻¹ * mapValue Complex.conjAe.toAlgHom (mu (star r⁻¹)) := by
  apply complexSplitting.injective
  rw [map_mul complexSplitting, complexSplitting_mapValue_conjAe_mu, complexSplitting_mu,
    complexSplitting_weight, Prod.mk_mul_mk, mul_one, one_mul]

/-- **`μ` is not defined over `ℝ`**: `μ(-1) = (-1, 1)` is not of the form `(z, conj z)`, so it is
not the image of a real point. -/
theorem mu_not_mem_mrange_mapValue_ofId :
    mu (-1) ∉ MonoidHom.mrange (mapValue (H := S) (Algebra.ofId ℝ ℂ)) := by
  rintro ⟨f, hf⟩
  have h := congrArg complexSplitting hf
  rw [complexSplitting_mapValue_ofId, complexSplitting_mu, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [h₁, Units.ext_iff, Units.coe_star] at h₂
  norm_num at h₂

/-! ### Characters -/

/-- **The characters of `S` over `ℂ`**: `(p, q) ∈ ℤ × ℤ` gives the character
`(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` of `S(ℂ) ≃ ℂˣ × ℂˣ` (`TauCeti.DeligneTorus.characterGroup_apply`). -/
noncomputable def characterGroup :
    Multiplicative (ℤ × ℤ) →* (WithConv (S →ₐ[ℝ] ℂ) →* ℂˣ) where
  toFun pq := (((zpowGroupHom pq.toAdd.1).comp (MonoidHom.fst ℂˣ ℂˣ)) *
    ((zpowGroupHom pq.toAdd.2).comp (MonoidHom.snd ℂˣ ℂˣ))).comp complexSplitting.toMonoidHom
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, MonoidHom.comp_apply,
      MonoidHom.mul_apply, zpowGroupHom_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, Units.val_mul]
    ring

/-- The character `(p, q)` sends a complex point with components `(z₁, z₂)` to `z₁ ^ p * z₂ ^ q`. -/
@[simp]
theorem characterGroup_apply (p q : ℤ) (x : WithConv (S →ₐ[ℝ] ℂ)) :
    characterGroup (.ofAdd (p, q)) x = (complexSplitting x).1 ^ p * (complexSplitting x).2 ^ q :=
  (rfl)

/-- **The characters are pairwise distinct**: `(p, q)` is recovered from the character, by
evaluating it on the points `(2, 1)` and `(1, 2)` of `S(ℂ) ≃ ℂˣ × ℂˣ`. -/
theorem characterGroup_injective : Function.Injective characterGroup := by
  rw [injective_iff_map_eq_one]
  intro pq h
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ a, Multiplicative.ofAdd a = pq := ⟨pq.toAdd, rfl⟩
  -- `2 ^ n = 1` in `ℂˣ` forces `n = 0`, by taking absolute values
  have key (n : ℤ) (hn : Units.mk0 (2 : ℂ) two_ne_zero ^ n = 1) : n = 0 := by
    rw [Units.ext_iff, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one] at hn
    have := congrArg (‖·‖) hn
    simp only [norm_zpow, Complex.norm_ofNat, norm_one] at this
    exact (zpow_eq_one_iff_right₀ zero_le_two (by norm_num)).1 this
  have hp := DFunLike.congr_fun h (complexSplitting.symm (Units.mk0 2 two_ne_zero, 1))
  have hq := DFunLike.congr_fun h (complexSplitting.symm (1, Units.mk0 2 two_ne_zero))
  simp only [characterGroup_apply, MulEquiv.apply_symm_apply, one_zpow, mul_one, one_mul,
    MonoidHom.one_apply] at hp hq
  rw [key p hp, key q hq, Prod.mk_zero_zero, ofAdd_zero]

/-- **Conjugation exchanges the characters `(p, q)` and `(q, p)`**: the character `(p, q)` of the
conjugate of a complex point `x` is the conjugate of the character `(q, p)` of `x`. -/
theorem characterGroup_mapValue_conjAe (p q : ℤ) (x : WithConv (S →ₐ[ℝ] ℂ)) :
    characterGroup (.ofAdd (p, q)) (mapValue Complex.conjAe.toAlgHom x) =
      star (characterGroup (.ofAdd (q, p)) x) := by
  rw [characterGroup_apply, characterGroup_apply, complexSplitting_mapValue_conjAe, star_mul,
    star_zpow, star_zpow]

/-- The character `(p, q)` takes the value `z ^ p` on `μ(z)`; in particular `(1, 0)` takes the
value `z` and `(0, 1)` the value `1`. -/
theorem characterGroup_mu (p q : ℤ) (z : ℂˣ) : characterGroup (.ofAdd (p, q)) (mu z) = z ^ p := by
  simp

/-- On real points the character `(1, 1)` is the norm. -/
theorem characterGroup_mapValue_ofId (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (characterGroup (.ofAdd (1, 1)) (mapValue (Algebra.ofId ℝ ℂ) f) : ℂ) = (norm ℝ f : ℝ) := by
  rw [characterGroup_apply, zpow_one, zpow_one, Units.val_mul,
    complexSplitting_fst_mul_snd_mapValue_ofId]

/-- The character `(p, q)` takes the value `r ^ (-(p + q))` on the weight `w(r)`. -/
theorem characterGroup_weight (p q : ℤ) (r : ℂˣ) :
    characterGroup (.ofAdd (p, q)) (weight ℂ r) = r ^ (-(p + q)) := by
  rw [characterGroup_apply, complexSplitting_weight, inv_zpow', inv_zpow', ← zpow_add, neg_add]

/-! ### The Deligne torus is not split -/

/-- **The Deligne torus is not split**: its real points `ℂˣ` are not isomorphic to `ℝˣ × ℝˣ`.
Indeed `i ∈ ℂˣ` satisfies `i ^ 4 = 1` but `i ^ 2 ≠ 1`, while every `x ∈ ℝˣ × ℝˣ` with `x ^ 4 = 1`
satisfies `x ^ 2 = 1`. -/
theorem isEmpty_realPoints_mulEquiv_units_prod :
    IsEmpty (WithConv (S →ₐ[ℝ] ℝ) ≃* ℝˣ × ℝˣ) := by
  refine ⟨fun e => ?_⟩
  let ψ : ℂˣ ≃* ℝˣ × ℝˣ := realPointsMulEquiv.symm.trans e
  have key (u : ℝˣ) (hu : u ^ 4 = 1) : u ^ 2 = 1 := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at hu ⊢
    exact (pow_eq_one_iff_of_nonneg (sq_nonneg (u : ℝ)) two_ne_zero).1 (by rw [← pow_mul]; exact hu)
  let i : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have h4 : ψ i ^ 4 = 1 := by
    rw [← map_pow, show i ^ 4 = 1 from Units.ext (by simp [i]), map_one]
  have h2 : ψ (i ^ 2) = 1 := by
    rw [map_pow]
    exact Prod.ext (key _ (congrArg Prod.fst h4)) (key _ (congrArg Prod.snd h4))
  have : ((i ^ 2 : ℂˣ) : ℂ) = 1 := by rw [ψ.map_eq_one_iff.1 h2, Units.val_one]
  norm_num [i] at this

end TauCeti.DeligneTorus
