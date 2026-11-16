/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike
import Mathlib.Algebra.Ring.Fin

/-!
# Hodge cocharacter and character group of the Deligne torus

Through the complex splitting `S(R) ≃* Rˣ × Rˣ` (`TauCeti.DeligneTorus.splittingMulEquiv`), the
Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` carries Milne's Hodge cocharacter `μ : 𝔾_{m,ℂ} → S_ℂ`,
`z ↦ (z, 1)`, its complex conjugate `muConj : 𝔾_{m,ℂ} → S_ℂ`, `z ↦ (1, z)`, and the character
lattice `X*(S) ≃ ℤ × ℤ` sending `(p, q)` to the character `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`:

* at the coordinate Hopf algebra level over `ℂ`, `μ` and `muConj` are the bialgebra homomorphisms
  `TauCeti.DeligneTorus.muBialgHom` and `TauCeti.DeligneTorus.muConjBialgHom` obtained by composing
  `TauCeti.DeligneTorus.baseChangeComplexBialgEquiv` with the left and right tensor projections,
  inducing `TauCeti.DeligneTorus.muOver` and `TauCeti.DeligneTorus.muConjOver` on `R`-points
  (`TauCeti.DeligneTorus.mapDomain_muBialgHom`, `TauCeti.DeligneTorus.mapDomain_muConjBialgHom`);
* over `ℂ`, `w(r) = μ(r⁻¹) * muConj(r⁻¹)` (`TauCeti.DeligneTorus.weight_eq_mu_mul_conj`), while `μ`
  does not descend to `ℝ`: `μ(-1)` splits as `(-1, 1)`, which is not of the form `(z, conj z)`
  (`TauCeti.DeligneTorus.mu_neg_one_not_mem_mrange`, `TauCeti.DeligneTorus.mu_not_real`);
* the characters `(p, q) ∈ ℤ × ℤ` act on `R`-points via `TauCeti.DeligneTorus.characterOver`
  (`TauCeti.DeligneTorus.characterGroup` over `ℂ`), complex conjugation exchanges `(p, q)` and
  `(q, p)` (`TauCeti.DeligneTorus.characterGroup_conj`), the character basis `(1, 0), (0, 1)` is
  dual to the cocharacter basis `μ, muConj`, respectively
  (`TauCeti.DeligneTorus.characterOver_muOver`, `TauCeti.DeligneTorus.characterOver_muConjOver`),
  `(1, 1)` is the norm (`TauCeti.DeligneTorus.characterOver_one_one`,
  `TauCeti.DeligneTorus.characterGroup_norm`), and `(p, q)` evaluates to `r ^ (-(p + q))` on `w(r)`
  (`TauCeti.DeligneTorus.characterGroup_weight`);
* the additive group of group-like elements of `baseChangeComplex` is isomorphic to `ℤ × ℤ`
  (`TauCeti.DeligneTorus.additiveGroupLikeComplexAddEquiv`), with the group-like element
  corresponding to `(p, q)` evaluating on base-changed points to `characterOver R (p, q)`
  (`TauCeti.DeligneTorus.ofConv_additiveGroupLikeComplexAddEquiv_symm`).

## Main definitions

* `TauCeti.DeligneTorus.muOver`, `TauCeti.DeligneTorus.mu`: the Hodge cocharacter `z ↦ (z, 1)` on
  points over a commutative complex algebra `R` (specialised to `R = ℂ` for `mu`).
* `TauCeti.DeligneTorus.muConjOver`, `TauCeti.DeligneTorus.muConj`: the conjugate cocharacter
  `z ↦ (1, z)`.
* `TauCeti.DeligneTorus.muBialgHom`, `TauCeti.DeligneTorus.muConjBialgHom`: the coordinate
  bialgebra homomorphisms `baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹]` representing `μ` and `muConj`.
* `TauCeti.DeligneTorus.characterOver`, `TauCeti.DeligneTorus.characterGroup`: the character
  `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q` indexed by `pq : ℤ × ℤ`.
* `TauCeti.DeligneTorus.additiveGroupLikeComplexAddEquiv`: the character-lattice isomorphism
  `Additive (GroupLike ℂ baseChangeComplex) ≃+ ℤ × ℤ`.

## Main results

* `TauCeti.DeligneTorus.mapDomain_muBialgHom`, `TauCeti.DeligneTorus.mapDomain_muConjBialgHom`:
  point-level compatibility for `muBialgHom` and `muConjBialgHom`.
* `TauCeti.DeligneTorus.mapValue_conj_mu`: complex conjugation transports `μ` to `muConj`.
* `TauCeti.DeligneTorus.weight_eq_mu_mul_conj`: `w(r) = μ(r⁻¹) * muConj(r⁻¹)`.
* `TauCeti.DeligneTorus.mu_neg_one_not_mem_mrange`, `TauCeti.DeligneTorus.mu_not_real`: `μ` is not
  defined over `ℝ`.
* `TauCeti.DeligneTorus.characterGroup_conj`, `TauCeti.DeligneTorus.characterOver_muOver`,
  `TauCeti.DeligneTorus.characterOver_muConjOver`, `TauCeti.DeligneTorus.characterGroup_norm`,
  `TauCeti.DeligneTorus.characterGroup_weight`, `TauCeti.DeligneTorus.characterGroup_injective`,
  `TauCeti.DeligneTorus.ofConv_additiveGroupLikeComplexAddEquiv_symm`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The Hodge cocharacter `μ` and its conjugate `muConj` -/

section Cocharacters

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **Milne's Hodge cocharacter** `μ : Rˣ →* S(R)` over a commutative complex algebra `R`, sending
`z` to `(z, 1)` under `splittingMulEquiv R`. -/
noncomputable def muOver : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (splittingMulEquiv R).symm.toMonoidHom.comp (MonoidHom.inl Rˣ Rˣ)

/-- **Milne's Hodge cocharacter on complex points**, `μ : ℂˣ →* S(ℂ)`, `z ↦ (z, 1)`. -/
noncomputable abbrev mu : ℂˣ →* WithConv (S →ₐ[ℝ] ℂ) :=
  muOver ℂ

/-- **The conjugate cocharacter** `muConjOver R : Rˣ →* S(R)` over a commutative complex algebra
`R`, sending `z` to `(1, z)` under `splittingMulEquiv R`. -/
noncomputable def muConjOver : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (splittingMulEquiv R).symm.toMonoidHom.comp (MonoidHom.inr Rˣ Rˣ)

/-- **The conjugate cocharacter on complex points**, `muConj : ℂˣ →* S(ℂ)`, `z ↦ (1, z)`. -/
noncomputable abbrev muConj : ℂˣ →* WithConv (S →ₐ[ℝ] ℂ) :=
  muConjOver ℂ

variable {R}

/-- Under `splittingMulEquiv R`, `muOver R z` has components `(z, 1)`. -/
@[simp]
theorem splittingMulEquiv_muOver (z : Rˣ) :
    splittingMulEquiv R (muOver R z) = (z, 1) :=
  (splittingMulEquiv R).apply_symm_apply (z, 1)

/-- Under `splittingMulEquiv R`, `muConjOver R z` has components `(1, z)`. -/
@[simp]
theorem splittingMulEquiv_muConjOver (z : Rˣ) :
    splittingMulEquiv R (muConjOver R z) = (1, z) :=
  (splittingMulEquiv R).apply_symm_apply (1, z)

/-- Under `complexSplitting`, `mu z` has components `(z, 1)`. -/
theorem complexSplitting_mu (z : ℂˣ) :
    complexSplitting (mu z) = (z, 1) :=
  splittingMulEquiv_muOver z

/-- Under `complexSplitting`, `muConj z` has components `(1, z)`. -/
theorem complexSplitting_muConj (z : ℂˣ) :
    complexSplitting (muConj z) = (1, z) :=
  splittingMulEquiv_muConjOver z

/-- Naturality of `muOver` along `ℂ`-algebra homomorphisms. -/
theorem mapValue_muOver {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (z : Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) (muOver R z) =
      muOver R' (Units.map (h : R →* R') z) := by
  apply (splittingMulEquiv R').injective
  rw [splittingMulEquiv_mapValue, splittingMulEquiv_muOver, splittingMulEquiv_muOver, map_one]

/-- Naturality of `muConjOver` along `ℂ`-algebra homomorphisms. -/
theorem mapValue_muConjOver {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (z : Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) (muConjOver R z) =
      muConjOver R' (Units.map (h : R →* R') z) := by
  apply (splittingMulEquiv R').injective
  rw [splittingMulEquiv_mapValue, splittingMulEquiv_muConjOver, splittingMulEquiv_muConjOver,
    map_one]

/-- **Complex conjugation transports `μ` to `muConj`**: conjugating `μ(z)` in `S(ℂ)` gives
`muConj (conj z)`. -/
theorem mapValue_conj_mu (z : ℂˣ) :
    AlgHom.mapValue Complex.conjAe.toAlgHom (mu z) =
      muConj (Units.map (starRingEnd ℂ : ℂ →* ℂ) z) := by
  apply complexSplitting.injective
  rw [conj_swap, complexSplitting_mu, complexSplitting_muConj, map_one]

/-- Composing `μ` with complex conjugation on both source and target yields `muConj`. -/
theorem mapValue_conj_mu_conj (z : ℂˣ) :
    AlgHom.mapValue Complex.conjAe.toAlgHom (mu (Units.map (starRingEnd ℂ : ℂ →* ℂ) z)) =
      muConj z := by
  rw [mapValue_conj_mu]
  congr 1
  exact Units.ext (Complex.conj_conj (z : ℂ))

/-- `Nm ∘ μ = id` on `Rˣ`. -/
@[simp]
theorem norm_muOver (z : Rˣ) : norm R (muOver R z) = z := by
  rw [← fst_mul_snd_splittingMulEquiv, splittingMulEquiv_muOver, mul_one]

/-- `Nm ∘ muConj = id` on `Rˣ`. -/
@[simp]
theorem norm_muConjOver (z : Rˣ) : norm R (muConjOver R z) = z := by
  rw [← fst_mul_snd_splittingMulEquiv, splittingMulEquiv_muConjOver, one_mul]

/-- Over a complex algebra `R`, the diagonal factors as `d(r) = μ(r) * muConj(r)`. -/
theorem diagonal_eq_muOver_mul_muConjOver (r : Rˣ) :
    diagonal R r = muOver R r * muConjOver R r := by
  apply (splittingMulEquiv R).injective
  rw [splittingMulEquiv_diagonal, map_mul, splittingMulEquiv_muOver, splittingMulEquiv_muConjOver,
    Prod.mk_mul_mk, mul_one, one_mul]

/-- Over a complex algebra `R`, the weight factors as `w(r) = μ(r⁻¹) * muConj(r⁻¹)`. -/
theorem weight_eq_muOver_mul_muConjOver (r : Rˣ) :
    weight R r = muOver R r⁻¹ * muConjOver R r⁻¹ := by
  apply (splittingMulEquiv R).injective
  rw [splittingMulEquiv_weight, map_mul, splittingMulEquiv_muOver, splittingMulEquiv_muConjOver,
    Prod.mk_mul_mk, mul_one, one_mul]

/-- **Over `ℂ`, `w(r) = μ(r⁻¹) * muConj(r⁻¹)`.** -/
theorem weight_eq_mu_mul_conj (r : ℂˣ) :
    weight ℂ r = mu r⁻¹ * muConj r⁻¹ :=
  weight_eq_muOver_mul_muConjOver r

/-- **Scheme-level Hodge cocharacter** `μ : 𝔾_{m,ℂ} → S_ℂ`, as the coordinate bialgebra
homomorphism `baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹]` projecting onto the left factor of
`baseChangeComplexBialgEquiv`. -/
noncomputable def muBialgHom : baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹] :=
  (Bialgebra.TensorProduct.projectLeft (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])).comp
    baseChangeComplexBialgEquiv.toBialgHom

/-- **Scheme-level conjugate cocharacter** `muConj : 𝔾_{m,ℂ} → S_ℂ`, as the coordinate bialgebra
homomorphism `baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹]` projecting onto the right factor of
`baseChangeComplexBialgEquiv`. -/
noncomputable def muConjBialgHom : baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹] :=
  (Bialgebra.TensorProduct.projectRight (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])).comp
    baseChangeComplexBialgEquiv.toBialgHom

/-- **Compatibility of `muBialgHom` with `muOver` on points** over every commutative `ℂ`-algebra `R`
with compatible `ℝ`-algebra structure. -/
theorem mapDomain_muBialgHom (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muBialgHom g) =
      muOver R (MultiplicativeGroup.pointsMulEquiv g) := by
  have hproj : BialgHom.mapDomain
      (Bialgebra.TensorProduct.projectLeft (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm (g, 1) := by
    rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectLeft]
  rw [muBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, hproj,
    mapDomain_baseChangeComplexBialgEquiv, MulEquiv.apply_symm_apply, map_one]
  rfl

/-- **Compatibility of `muConjBialgHom` with `muConjOver` on points** over every commutative
`ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
theorem mapDomain_muConjBialgHom (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muConjBialgHom g) =
      muConjOver R (MultiplicativeGroup.pointsMulEquiv g) := by
  have hproj : BialgHom.mapDomain
      (Bialgebra.TensorProduct.projectRight (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm ((1 : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)), g) := by
    rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectRight]
  rw [muConjBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, hproj,
    mapDomain_baseChangeComplexBialgEquiv, MulEquiv.apply_symm_apply, map_one]
  rfl

/-- **`μ(-1)` is not a real point of `S`**: under `complexSplitting` it equals `(-1, 1)`, which is
not of the form `(z, conj z)`. -/
theorem mu_neg_one_not_mem_mrange :
    mu (-1) ∉ MonoidHom.mrange (AlgHom.mapValue (Algebra.ofId ℝ ℂ)) := by
  rw [mem_mrange_mapValue_ofId_iff, complexSplitting_mu]
  intro h
  have hval := congrArg Units.val h
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_neg, Units.val_one, map_neg,
    map_one] at hval
  norm_num at hval

/-- **Non-example: the Hodge cocharacter `μ` is not defined over `ℝ`**: there is no real
homomorphism `ℝˣ →* S(ℝ)` whose complexification agrees with `μ` on real scalars. -/
theorem mu_not_real :
    ¬ ∃ c : ℝˣ →* WithConv (S →ₐ[ℝ] ℝ),
      ∀ r : ℝˣ, AlgHom.mapValue (Algebra.ofId ℝ ℂ) (c r) =
        mu (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) r) := by
  rintro ⟨c, hc⟩
  apply mu_neg_one_not_mem_mrange
  refine ⟨c (-1), ?_⟩
  rw [hc (-1)]
  congr 1
  ext
  simp

/-- Coordinate-Hopf-algebra form of `mu_not_real`: no bialgebra homomorphism `S →ₐc[ℝ] ℝ[T;T⁻¹]`
induces `μ` on real-scalar points. -/
theorem not_exists_bialgHom_mapDomain_eq_mu :
    ¬ ∃ φ : S →ₐc[ℝ] ℝ[T;T⁻¹],
      ∀ r : ℝˣ,
        AlgHom.mapValue (Algebra.ofId ℝ ℂ)
            (BialgHom.mapDomain φ (MultiplicativeGroup.pointsMulEquiv.symm r)) =
          mu (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) r) := by
  rintro ⟨φ, hφ⟩
  exact mu_not_real ⟨(BialgHom.mapDomain φ).comp
    (MultiplicativeGroup.pointsMulEquiv (R := ℝ) (A := ℝ)).symm.toMonoidHom, hφ⟩

end Cocharacters

/-! ### The character group `X*(S) ≃ ℤ × ℤ` -/

section Characters

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **Character `(p, q)` of the Deligne torus** over a commutative complex algebra `R`, sending a
point with splitting `(z₁, z₂) ∈ Rˣ × Rˣ` to `z₁ ^ p * z₂ ^ q`. -/
noncomputable def characterOver (pq : ℤ × ℤ) : WithConv (S →ₐ[ℝ] R) →* Rˣ :=
  ((zpowGroupHom pq.1).coprod (zpowGroupHom pq.2)).comp (splittingMulEquiv R).toMonoidHom

/-- **Milne's character group parametrization** of the Deligne torus on complex points, sending
`pq = (p, q) : ℤ × ℤ` to the character `S(ℂ) →* ℂˣ`, `(z₁, z₂) ↦ z₁ ^ p * z₂ ^ q`. -/
noncomputable abbrev characterGroup (pq : ℤ × ℤ) : WithConv (S →ₐ[ℝ] ℂ) →* ℂˣ :=
  characterOver ℂ pq

variable {R}

/-- Explicit formula for `characterOver R pq` in terms of `splittingMulEquiv R`. -/
theorem characterOver_apply (pq : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] R)) :
    characterOver R pq f =
      (splittingMulEquiv R f).1 ^ pq.1 * (splittingMulEquiv R f).2 ^ pq.2 :=
  (rfl)

/-- Explicit formula for `characterGroup pq` in terms of `complexSplitting`. -/
theorem characterGroup_apply (pq : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] ℂ)) :
    characterGroup pq f =
      (complexSplitting f).1 ^ pq.1 * (complexSplitting f).2 ^ pq.2 :=
  (rfl)

/-- Naturality of `characterOver` along `ℂ`-algebra homomorphisms. -/
theorem characterOver_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (pq : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] R)) :
    characterOver R' pq (AlgHom.mapValue (h.restrictScalars ℝ) f) =
      Units.map (h : R →* R') (characterOver R pq f) := by
  rw [characterOver_apply, splittingMulEquiv_mapValue, characterOver_apply, map_mul, map_zpow,
    map_zpow]

/-- The zero pair `(0, 0)` gives the trivial character `1`. -/
@[simp]
theorem characterOver_zero : characterOver R (0, 0) = 1 := by
  ext f
  simp [characterOver_apply]

/-- Addition of exponent pairs in `ℤ × ℤ` corresponds to pointwise multiplication of characters. -/
theorem characterOver_add (pq rs : ℤ × ℤ) :
    characterOver R (pq + rs) = characterOver R pq * characterOver R rs := by
  ext f
  simp only [characterOver_apply, Prod.fst_add, Prod.snd_add, zpow_add, MonoidHom.mul_apply,
    mul_mul_mul_comm]

/-- Negation in `ℤ × ℤ` corresponds to pointwise inversion of characters. -/
theorem characterOver_neg (pq : ℤ × ℤ) :
    characterOver R (-pq) = (characterOver R pq)⁻¹ := by
  ext f
  simp only [characterOver_apply, Prod.fst_neg, Prod.snd_neg, zpow_neg, MonoidHom.inv_apply,
    mul_inv_rev, mul_comm]

/-- **Complex conjugation exchanges the characters `(p, q)` and `(q, p)`** on `S(ℂ)`: pointwise
form `(conj ∘ χ_{p,q} ∘ conj)(f) = χ_{q,p}(f)`. -/
theorem characterGroup_conj_apply (pq : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] ℂ)) :
    Units.map (starRingEnd ℂ : ℂ →* ℂ)
        (characterGroup pq (AlgHom.mapValue Complex.conjAe.toAlgHom f)) =
      characterGroup pq.swap f := by
  have hinv : ∀ u : ℂˣ,
      Units.map (starRingEnd ℂ : ℂ →* ℂ) (Units.map (starRingEnd ℂ : ℂ →* ℂ) u) = u :=
    fun u ↦ Units.ext (Complex.conj_conj (u : ℂ))
  rw [characterGroup_apply, conj_swap]
  dsimp only [Prod.swap]
  rw [map_mul, map_zpow, map_zpow, hinv, hinv, mul_comm, characterGroup_apply]

/-- **Galois action on `X*(S)`**: conjugating `characterGroup pq` by complex conjugation on both
`S(ℂ)` and `ℂˣ` produces `characterGroup pq.swap`. -/
theorem characterGroup_conj (pq : ℤ × ℤ) :
    (Units.map (starRingEnd ℂ : ℂ →* ℂ)).comp
        ((characterGroup pq).comp (AlgHom.mapValue Complex.conjAe.toAlgHom)) =
      characterGroup pq.swap :=
  MonoidHom.ext (characterGroup_conj_apply pq)

/-- Pairing `characterOver R pq` with `muOver R` extracts the first exponent `pq.1`. -/
@[simp]
theorem characterOver_muOver (pq : ℤ × ℤ) (z : Rˣ) :
    characterOver R pq (muOver R z) = z ^ pq.1 := by
  rw [characterOver_apply, splittingMulEquiv_muOver, one_zpow, mul_one]

/-- Pairing `characterOver R pq` with `muConjOver R` extracts the second exponent `pq.2`. -/
@[simp]
theorem characterOver_muConjOver (pq : ℤ × ℤ) (z : Rˣ) :
    characterOver R pq (muConjOver R z) = z ^ pq.2 := by
  rw [characterOver_apply, splittingMulEquiv_muConjOver, one_zpow, one_mul]

/-- **Distinct pairs in `ℤ × ℤ` define distinct characters on `S(ℂ)`.** -/
theorem characterGroup_injective : Function.Injective characterGroup := by
  intro pq rs h
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  have hinj : Function.Injective (fun n : ℤ ↦ u ^ n) := by
    intro m n hmn
    have hval := congrArg Units.val hmn
    simp only [Units.val_zpow_eq_zpow_val, u, Units.val_mk0] at hval
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_zpow, ← Complex.ofReal_zpow] at hval
    exact (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective
      (Complex.ofReal_injective hval)
  have h1 : u ^ pq.1 = u ^ rs.1 := by
    simpa only [characterOver_muOver] using DFunLike.congr_fun h (mu u)
  have h2 : u ^ pq.2 = u ^ rs.2 := by
    simpa only [characterOver_muConjOver] using DFunLike.congr_fun h (muConj u)
  exact Prod.ext (hinj h1) (hinj h2)

/-- **The character `(1, 1)` is the norm** over every commutative complex algebra `R`. -/
@[simp]
theorem characterOver_one_one : characterOver R (1, 1) = norm R := by
  ext f
  rw [characterOver_apply, zpow_one, zpow_one, fst_mul_snd_splittingMulEquiv]

/-- **On real points, the character `(1, 1)` equals the norm `Nm : S(ℝ) →* ℝˣ` embedded into
`ℂˣ`.** -/
theorem characterGroup_norm (f : WithConv (S →ₐ[ℝ] ℝ)) :
    characterGroup (1, 1) (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) (norm ℝ f) := by
  rw [characterGroup, characterOver_one_one, norm_mapValue]
  rfl

/-- Evaluating `characterOver R pq` on `diagonal R r` gives `r ^ (pq.1 + pq.2)`. -/
@[simp]
theorem characterOver_diagonal (pq : ℤ × ℤ) (r : Rˣ) :
    characterOver R pq (diagonal R r) = r ^ (pq.1 + pq.2) := by
  rw [characterOver_apply, splittingMulEquiv_diagonal, zpow_add]

/-- Evaluating `characterOver R pq` on `weight R r` gives `r ^ (-(pq.1 + pq.2))`. -/
@[simp]
theorem characterOver_weight (pq : ℤ × ℤ) (r : Rˣ) :
    characterOver R pq (weight R r) = r ^ (-(pq.1 + pq.2)) := by
  rw [characterOver_apply, splittingMulEquiv_weight, inv_zpow', inv_zpow', ← zpow_add, ← neg_add]

/-- **The character `(p, q)` takes value `r ^ (-(p + q))` on `w(r)`.** -/
theorem characterGroup_weight (pq : ℤ × ℤ) (r : ℂˣ) :
    characterGroup pq (weight ℂ r) = r ^ (-(pq.1 + pq.2)) :=
  characterOver_weight pq r

/-! ### Identification of the algebraic character lattice over `ℂ` with `ℤ × ℤ` -/

/-- **Algebraic character lattice of `S_ℂ`**: the additive group of group-like elements of
`baseChangeComplex` is isomorphic to `ℤ × ℤ`. -/
noncomputable def additiveGroupLikeComplexAddEquiv :
    Additive (_root_.GroupLike ℂ baseChangeComplex) ≃+ ℤ × ℤ :=
  let eBialg : MonoidAlgebra ℂ (SplitTorus.characterGroup (ULift.{0} (Fin 2))) ≃ₐc[ℂ]
      baseChangeComplex :=
    _root_.CommHopfAlgCat.ofIso
      ((finiteTypeCommHopfAlgProperty ℂ).ι.mapIso baseChangeSplitTorusIso)
  (MulEquiv.toAdditive
    (eBialg.mapGroupLike.symm.trans
      (TauCeti.MonoidAlgebra.groupLikeEquiv (R := ℂ)
        (H := SplitTorus.characterGroup (ULift.{0} (Fin 2)))))).trans
    ((AddEquiv.additiveMultiplicative (ULift.{0} (Fin 2) →₀ ℤ)).trans
      ((Finsupp.domCongr Equiv.ulift).trans
        (Finsupp.addEquivFunOnFinite.trans (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ ℤ)).toAddEquiv)))

/-- **Evaluation of the algebraic character lattice on base-changed points**: evaluating a
base-changed `R`-point `g` of `S_ℂ` at the group-like element corresponding to `pq : ℤ × ℤ` under
`additiveGroupLikeComplexAddEquiv.symm` equals `characterOver R pq`. -/
theorem ofConv_additiveGroupLikeComplexAddEquiv_symm (pq : ℤ × ℤ)
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      (characterOver R pq (baseChangeComplexPointsMulEquiv R g) : R) := by
  let eFinsupp : (ULift.{0} (Fin 2) →₀ ℤ) ≃+ ℤ × ℤ :=
    (Finsupp.domCongr Equiv.ulift).trans
      (Finsupp.addEquivFunOnFinite.trans (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ ℤ)).toAddEquiv)
  let m : ULift.{0} (Fin 2) →₀ ℤ := eFinsupp.symm pq
  have hm0 : m ⟨0⟩ = pq.1 := congrArg Prod.fst (eFinsupp.apply_symm_apply pq)
  have hm1 : m ⟨1⟩ = pq.2 := congrArg Prod.snd (eFinsupp.apply_symm_apply pq)
  have hval : ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      baseChangeSplitTorusIso.hom.hom.hom
        (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1) := by
    simp only [additiveGroupLikeComplexAddEquiv, AddEquiv.symm_trans_apply,
      MulEquiv.toAdditive_apply_symm_apply, toMul_ofMul, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, BialgEquiv.val_mapGroupLike,
      TauCeti.MonoidAlgebra.val_groupLikeEquiv_symm, m, eFinsupp]
    rw [← BialgEquiv.coe_toBialgHom, CommHopfAlgCat.coe_ofIso, Functor.mapIso_hom,
      ObjectProperty.ι_map, AddEquiv.additiveMultiplicative_symm_apply, toMul_ofMul]
    rfl
  let p : WithConv (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) →ₐ[ℂ] R) :=
    BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g
  have hp := pointsMulEquiv_mapDomain_baseChangeSplitTorusIso g
  have hp0 : SplitTorus.pointsMulEquiv p ⟨0⟩ =
      (splittingMulEquiv R (baseChangeComplexPointsMulEquiv R g)).1 := congrArg Prod.fst hp
  have hp1 : SplitTorus.pointsMulEquiv p ⟨1⟩ =
      (splittingMulEquiv R (baseChangeComplexPointsMulEquiv R g)).2 := congrArg Prod.snd hp
  have hchar : g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      ((freeAbelianCharEquiv.symm (SplitTorus.pointsMulEquiv p) (Multiplicative.ofAdd m) :
        Rˣ) : R) := by
    have hmap : g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
        p.ofConv (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1) := by
      rw [hval]
      exact (BialgHom.mapDomain_apply_apply (A := R) baseChangeSplitTorusIso.hom.hom.hom g _).symm
    rw [hmap, ← DiagonalizableGroup.charOfPoint_apply_coe (f := p.ofConv),
      ← DiagonalizableGroup.pointsMulEquiv_apply,
      ← MulEquiv.symm_apply_apply freeAbelianCharEquiv (DiagonalizableGroup.pointsMulEquiv p),
      ← SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv]
  rw [hchar, freeAbelianCharEquiv_symm_apply_ofAdd,
    Finsupp.prod_fintype _ _ (fun _ ↦ zpow_zero _),
    Fintype.prod_equiv Equiv.ulift
      (fun i : ULift.{0} (Fin 2) ↦ SplitTorus.pointsMulEquiv p i ^ m i)
      (fun i : Fin 2 ↦ SplitTorus.pointsMulEquiv p ⟨i⟩ ^ m ⟨i⟩)
      (fun _ ↦ rfl),
    Fin.prod_univ_two, hp0, hp1, hm0, hm1, characterOver_apply]

end Characters

end TauCeti.DeligneTorus
