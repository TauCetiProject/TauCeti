/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike
import TauCeti.Data.Finsupp.Fin
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Hodge cocharacters and algebraic character lattice of the Deligne torus

Building on the complex splitting `S(R) ≃* Rˣ × Rˣ` (`TauCeti.DeligneTorus.complexSplitting`) and
the scheme-level splitting `baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]`
(`TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`), this file develops Milne's Hodge cocharacter
`μ : 𝔾_{m,ℂ} → S_ℂ`, `z ↦ (z, 1)`, its complex conjugate `muConj : 𝔾_{m,ℂ} → S_ℂ`,
`z ↦ (1, z)`, and the algebraic character lattice `X*(S_ℂ) ≃+ ℤ × ℤ`. Throughout the point-level
sections below, `R` denotes a commutative `ℂ`-algebra equipped with a compatible `ℝ`-algebra
structure (`[Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]`).

* At the coordinate Hopf algebra level over `ℂ`, `μ` and `muConj` are the bialgebra homomorphisms
  `TauCeti.DeligneTorus.muBialgHom` and `TauCeti.DeligneTorus.muConjBialgHom` obtained by composing
  `TauCeti.DeligneTorus.baseChangeComplexBialgEquiv` with the left and right tensor projections,
  inducing `TauCeti.DeligneTorus.mu` and `TauCeti.DeligneTorus.muConj` on `R`-points
  (`TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom`,
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom`).
* Over every such algebra `R`, `d(r) = μ(r) * muConj(r)` and `w(r) = μ(r⁻¹) * muConj(r⁻¹)`
  (`TauCeti.DeligneTorus.diagonal_eq_mu_mul_muConj`,
  `TauCeti.DeligneTorus.weight_eq_mu_inv_mul_muConj_inv`), while `μ` does not descend to `ℝ`
  (`TauCeti.DeligneTorus.not_exists_realPoints_lift_mu`,
  `TauCeti.DeligneTorus.not_exists_bialgHom_inducing_mu_on_realPoints`).
* Pairing `characterGroup R` with `muConj R` extracts the second exponent
  (`TauCeti.DeligneTorus.characterGroup_muConj`), and over every such algebra `R` the character
  `(1, 1)` equals `norm R` (`TauCeti.DeligneTorus.characterGroup_one_one`).
* The additive group of group-like elements of `baseChangeComplex` is isomorphic to `ℤ × ℤ`
  (`TauCeti.DeligneTorus.characterLatticeEquiv`), with the group-like element
  corresponding to `(p, q)` evaluating on a base-changed `R`-point `g` to the value of
  `characterGroup R (.ofAdd (p, q))` at the corresponding point of `S(R)`, coerced from `Rˣ` to
  `R` (`TauCeti.DeligneTorus.ofConv_characterLatticeEquiv_symm`), and complex conjugation swapping
  the two coordinates (`TauCeti.DeligneTorus.characterLatticeEquiv_conjAe_smul`).

## Main definitions

* `TauCeti.DeligneTorus.muConj R`: the conjugate cocharacter `z ↦ (1, z)` on `R`-points for `R` as
  above.
* `TauCeti.DeligneTorus.muBialgHom`, `TauCeti.DeligneTorus.muConjBialgHom`: the coordinate
  bialgebra homomorphisms `baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹]` representing `μ` and `muConj`.
* `TauCeti.DeligneTorus.characterLatticeEquiv`: the character-lattice isomorphism
  `Additive (GroupLike ℂ baseChangeComplex) ≃+ ℤ × ℤ`.

## Main results

* `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom`,
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom`: point-level
  compatibility for `muBialgHom` and `muConjBialgHom`.
* `TauCeti.DeligneTorus.mapValue_conj_mu`, `TauCeti.DeligneTorus.mapValue_conj_mu_conj`: complex
  conjugation transports `μ` to `muConj`.
* `TauCeti.DeligneTorus.diagonal_eq_mu_mul_muConj`,
  `TauCeti.DeligneTorus.weight_eq_mu_inv_mul_muConj_inv`: factorization of `d` and `w` via `μ` and
  `muConj`.
* `TauCeti.DeligneTorus.not_exists_realPoints_lift_mu`,
  `TauCeti.DeligneTorus.not_exists_bialgHom_inducing_mu_on_realPoints`: `μ` does not lift to `ℝ`
  on real points.
* `TauCeti.DeligneTorus.characterGroup_muConj`, `TauCeti.DeligneTorus.characterGroup_one_one`,
  `TauCeti.DeligneTorus.ofConv_characterLatticeEquiv_symm`,
  `TauCeti.DeligneTorus.characterLatticeEquiv_conjAe_smul`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.DeligneTorus

/-! ### The conjugate cocharacter `muConj` and coordinate bialgebra maps -/

section Cocharacters

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- **The conjugate cocharacter** `muConj R : Rˣ →* S(R)` over a commutative complex algebra `R`,
sending `z` to `(1, z)` under `complexSplitting R`. -/
noncomputable def muConj : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (complexSplitting R).symm.toMonoidHom.comp (MonoidHom.inr Rˣ Rˣ)

variable {R}

/-- Under `complexSplitting R`, `muConj R z` has components `(1, z)`. -/
@[simp]
theorem complexSplitting_muConj (z : Rˣ) :
    complexSplitting R (muConj R z) = (1, z) :=
  (complexSplitting R).apply_symm_apply (1, z)

/-- Naturality of `muConj` along `ℂ`-algebra homomorphisms. -/
theorem mapValue_muConj {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℂ R']
    [IsScalarTower ℝ ℂ R'] (h : R →ₐ[ℂ] R') (z : Rˣ) :
    AlgHom.mapValue (h.restrictScalars ℝ) (muConj R z) =
      muConj R' (Units.map (h : R →* R') z) := by
  apply (complexSplitting R').injective
  rw [complexSplitting_mapValue, complexSplitting_muConj, complexSplitting_muConj, map_one]

/-- **Complex conjugation transports `μ` to `muConj`**: conjugating `μ(z)` in `S(ℂ)` gives
`muConj ℂ (conj z)`. -/
theorem mapValue_conj_mu (z : ℂˣ) :
    AlgHom.mapValue Complex.conjAe.toAlgHom (mu ℂ z) = muConj ℂ (star z) := by
  apply (complexSplitting ℂ).injective
  rw [complexSplitting_conj, complexSplitting_mu, complexSplitting_muConj]
  simp

/-- Composing `μ` with complex conjugation on both source and target yields `muConj`. -/
theorem mapValue_conj_mu_conj (z : ℂˣ) :
    AlgHom.mapValue Complex.conjAe.toAlgHom (mu ℂ (star z)) = muConj ℂ z := by
  rw [mapValue_conj_mu, star_star]

/-- `Nm ∘ μ = id` on `Rˣ`. -/
@[simp]
theorem norm_mu (z : Rˣ) : norm R (mu R z) = z := by
  rw [← fst_mul_snd_complexSplitting, complexSplitting_mu, mul_one]

/-- `Nm ∘ muConj = id` on `Rˣ`. -/
@[simp]
theorem norm_muConj (z : Rˣ) : norm R (muConj R z) = z := by
  rw [← fst_mul_snd_complexSplitting, complexSplitting_muConj, one_mul]

/-- Over a complex algebra `R`, the diagonal factors as `d(r) = μ(r) * muConj(r)`. -/
theorem diagonal_eq_mu_mul_muConj (r : Rˣ) :
    diagonal R r = mu R r * muConj R r := by
  apply (complexSplitting R).injective
  rw [complexSplitting_diagonal, map_mul, complexSplitting_mu, complexSplitting_muConj,
    Prod.mk_mul_mk, mul_one, one_mul]

/-- Over a complex algebra `R`, the weight factors as `w(r) = μ(r⁻¹) * muConj(r⁻¹)`. -/
theorem weight_eq_mu_inv_mul_muConj_inv (r : Rˣ) :
    weight R r = mu R r⁻¹ * muConj R r⁻¹ := by
  rw [weight_eq_inv_diagonal, ← map_inv (diagonal R), diagonal_eq_mu_mul_muConj]

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

omit [Algebra ℝ R] [IsScalarTower ℝ ℂ R] in
private lemma mapDomain_projectLeft (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    BialgHom.mapDomain
        (Bialgebra.TensorProduct.projectLeft (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm (g, 1) := by
  rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectLeft]

omit [Algebra ℝ R] [IsScalarTower ℝ ℂ R] in
private lemma mapDomain_projectRight (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    BialgHom.mapDomain
        (Bialgebra.TensorProduct.projectRight (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm ((1 : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)), g) := by
  rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectRight]

/-- **Compatibility of `muBialgHom` with `mu` on points** over every commutative `ℂ`-algebra `R`
with compatible `ℝ`-algebra structure. -/
@[simp↓]
theorem baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom
    (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muBialgHom g) =
      mu R (MultiplicativeGroup.pointsMulEquiv g) := by
  rw [muBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, mapDomain_projectLeft,
    mapDomain_baseChangeComplexBialgEquiv]
  apply (complexSplitting R).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, complexSplitting_mu, map_one]

/-- **Compatibility of `muConjBialgHom` with `muConj` on points** over every commutative
`ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
@[simp↓]
theorem baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom
    (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muConjBialgHom g) =
      muConj R (MultiplicativeGroup.pointsMulEquiv g) := by
  rw [muConjBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, mapDomain_projectRight,
    mapDomain_baseChangeComplexBialgEquiv]
  apply (complexSplitting R).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, complexSplitting_muConj, map_one]

/-- **Non-example: `μ` does not lift to real points**: no homomorphism `ℝˣ →* S(ℝ)` agrees with
`μ` on real units after mapping its values from `S(ℝ)` into `S(ℂ)`. -/
theorem not_exists_realPoints_lift_mu :
    ¬ ∃ c : ℝˣ →* WithConv (S →ₐ[ℝ] ℝ),
      ∀ r : ℝˣ, AlgHom.mapValue (Algebra.ofId ℝ ℂ) (c r) =
        mu ℂ (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) r) := by
  rintro ⟨c, hc⟩
  apply mu_neg_one_notMem_range_mapValue
  refine ⟨c (-1), ?_⟩
  rw [hc (-1)]
  congr 1
  ext
  simp

/-- **Non-example: `μ` is not defined over `ℝ`**: no coordinate bialgebra homomorphism
`S →ₐc[ℝ] ℝ[T;T⁻¹]` induces `μ` on real-scalar points. -/
theorem not_exists_bialgHom_inducing_mu_on_realPoints :
    ¬ ∃ φ : S →ₐc[ℝ] ℝ[T;T⁻¹],
      ∀ r : ℝˣ,
        AlgHom.mapValue (Algebra.ofId ℝ ℂ)
            (BialgHom.mapDomain φ (MultiplicativeGroup.pointsMulEquiv.symm r)) =
          mu ℂ (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) r) := by
  rintro ⟨φ, hφ⟩
  exact not_exists_realPoints_lift_mu ⟨(BialgHom.mapDomain φ).comp
    (MultiplicativeGroup.pointsMulEquiv (R := ℝ) (A := ℝ)).symm.toMonoidHom, hφ⟩

end Cocharacters

/-! ### Additional character properties and algebraic character lattice over `ℂ` -/

section Characters

variable (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- Pairing `characterGroup R (.ofAdd (p, q))` with `muConj R` extracts the second exponent `q`. -/
theorem characterGroup_muConj (p q : ℤ) (z : Rˣ) :
    characterGroup R (.ofAdd (p, q)) (muConj R z) = z ^ q := by
  rw [characterGroup_apply, complexSplitting_muConj, one_zpow, one_mul]

/-- **The character `(1, 1)` is the norm** over every commutative complex algebra `R`. -/
@[simp]
theorem characterGroup_one_one : characterGroup R (.ofAdd (1, 1)) = norm R := by
  ext f
  rw [characterGroup_apply, zpow_one, zpow_one, fst_mul_snd_complexSplitting]

/-- **On real points, the character `(1, 1)` equals the norm `Nm : S(ℝ) →* ℝˣ` embedded into
`ℂˣ`.** -/
theorem characterGroup_norm_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    characterGroup ℂ (.ofAdd (1, 1)) (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) (norm ℝ f) := by
  rw [characterGroup_one_one, norm_mapValue]
  exact Units.ext (by simp)

/-! ### Identification of the algebraic character lattice over `ℂ` with `ℤ × ℤ` -/

/-- **Algebraic character lattice of `S_ℂ`**: the additive group of group-like elements of
`baseChangeComplex` is isomorphic to `ℤ × ℤ`. -/
noncomputable def characterLatticeEquiv :
    Additive (_root_.GroupLike ℂ baseChangeComplex) ≃+ ℤ × ℤ :=
  (MulEquiv.toAdditive
    (baseChangeSplitTorusBialgEquiv.mapGroupLike.symm.trans
      (TauCeti.MonoidAlgebra.groupLikeEquiv (R := ℂ)
        (H := SplitTorus.characterGroup (ULift.{0} (Fin 2)))))).trans
    ((AddEquiv.additiveMultiplicative (ULift.{0} (Fin 2) →₀ ℤ)).trans
      (Finsupp.uliftFinTwoAddEquiv ℤ))

private lemma val_toMul_characterLatticeEquiv_symm (pq : ℤ × ℤ) :
    ((characterLatticeEquiv.symm pq).toMul : baseChangeComplex) =
      baseChangeSplitTorusBialgEquiv.toBialgHom
        (_root_.MonoidAlgebra.single
          (Multiplicative.ofAdd ((Finsupp.uliftFinTwoAddEquiv ℤ).symm pq)) 1) := by
  simp only [characterLatticeEquiv, AddEquiv.symm_trans_apply,
    MulEquiv.toAdditive_apply_symm_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom, BialgEquiv.val_mapGroupLike,
    TauCeti.MonoidAlgebra.val_groupLikeEquiv_symm, toMul_ofMul]
  rw [AddEquiv.additiveMultiplicative_symm_apply, toMul_ofMul]

/-- **Evaluation of the algebraic character lattice on base-changed points**: evaluating a
base-changed `R`-point `g` of `S_ℂ` at the group-like element corresponding to `pq : ℤ × ℤ` under
`characterLatticeEquiv.symm` equals the value of `characterGroup R (.ofAdd pq)` at the
corresponding point `baseChangeComplexPointsMulEquiv R g : S(R)`, coerced from `Rˣ` to `R`. -/
@[simp]
theorem ofConv_characterLatticeEquiv_symm (pq : ℤ × ℤ)
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    g.ofConv ((characterLatticeEquiv.symm pq).toMul : baseChangeComplex) =
      (characterGroup R (.ofAdd pq) (baseChangeComplexPointsMulEquiv R g) : R) := by
  rcases pq with ⟨p, q⟩
  rw [val_toMul_characterLatticeEquiv_symm,
    ← BialgHom.mapDomain_apply_apply (A := R) baseChangeSplitTorusBialgEquiv.toBialgHom g,
    baseChangeSplitTorusBialgEquiv_toBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    mapDomain_baseChangeComplexBialgEquiv_symm]
  simp

private lemma ofConv_conjAe_smul (g : WithConv (baseChangeComplex →ₐ[ℂ] ℂ))
    (z : ℂ ⊗[ℝ] S) :
    g.ofConv (Complex.conjAe • z) =
      star (((baseChangeComplexPointsMulEquiv ℂ).symm
        (AlgHom.mapValue Complex.conjAe.toAlgHom
          (baseChangeComplexPointsMulEquiv ℂ g))).ofConv z) := by
  simp [g.ofConv.apply_scalarAut_smul Complex.conjAe z]

private lemma characterGroup_swap_conj (pq : ℤ × ℤ) (f : WithConv (S →ₐ[ℝ] ℂ)) :
    characterGroup ℂ (.ofAdd pq.swap) f =
      star (characterGroup ℂ (.ofAdd pq) (AlgHom.mapValue Complex.conjAe.toAlgHom f)) := by
  rw [characterGroup_apply, characterGroup_apply, complexSplitting_conj]
  simp [mul_comm]

/-- **Galois equivariance of the algebraic character lattice**: the action of complex conjugation
`Complex.conjAe` on `Additive (GroupLike ℂ baseChangeComplex)` corresponds under
`characterLatticeEquiv` to swapping the two coordinates `(p, q) ↦ (q, p)`. -/
@[simp]
theorem characterLatticeEquiv_conjAe_smul
    (x : Additive (_root_.GroupLike ℂ baseChangeComplex)) :
    characterLatticeEquiv (Complex.conjAe • x) = (characterLatticeEquiv x).swap := by
  apply Multiplicative.ofAdd.injective
  apply characterGroup_injective
  refine MonoidHom.ext fun f ↦ Units.ext ?_
  let g : WithConv (baseChangeComplex →ₐ[ℂ] ℂ) := (baseChangeComplexPointsMulEquiv ℂ).symm f
  have hf : baseChangeComplexPointsMulEquiv ℂ g = f :=
    (baseChangeComplexPointsMulEquiv ℂ).apply_symm_apply f
  rw [← hf, ← ofConv_characterLatticeEquiv_symm, AddEquiv.symm_apply_apply,
    Additive.toMul_smul, TauCeti.ScalarAut.val_smul, ofConv_conjAe_smul, hf,
    characterGroup_swap_conj, Units.coe_star]
  congr 1
  have h1 := ofConv_characterLatticeEquiv_symm (R := ℂ) (characterLatticeEquiv x)
    ((baseChangeComplexPointsMulEquiv ℂ).symm (AlgHom.mapValue Complex.conjAe.toAlgHom f))
  rwa [AddEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at h1

end Characters

end TauCeti.DeligneTorus
