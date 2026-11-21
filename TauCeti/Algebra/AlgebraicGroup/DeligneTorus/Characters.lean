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
# Hodge cocharacters and algebraic character lattice of the Deligne torus

Building on the complex splitting `S(R) ≃* Rˣ × Rˣ` (`TauCeti.DeligneTorus.complexSplitting`) and
the scheme-level splitting `baseChangeComplex ≃ₐc[ℂ] ℂ[T;T⁻¹] ⊗[ℂ] ℂ[T;T⁻¹]`
(`TauCeti.DeligneTorus.baseChangeComplexBialgEquiv`), this file develops Milne's Hodge cocharacter
`μ : 𝔾_{m,ℂ} → S_ℂ`, `z ↦ (z, 1)`, its complex conjugate `muConj : 𝔾_{m,ℂ} → S_ℂ`,
`z ↦ (1, z)`, and the algebraic character lattice `X*(S_ℂ) ≃+ ℤ × ℤ`:

* at the coordinate Hopf algebra level over `ℂ`, `μ` and `muConj` are the bialgebra homomorphisms
  `TauCeti.DeligneTorus.muBialgHom` and `TauCeti.DeligneTorus.muConjBialgHom` obtained by composing
  `TauCeti.DeligneTorus.baseChangeComplexBialgEquiv` with the left and right tensor projections,
  inducing `TauCeti.DeligneTorus.mu` and `TauCeti.DeligneTorus.muConj` on `R`-points
  (`TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom`,
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom`);
* over every complex algebra `R`, `d(r) = μ(r) * muConj(r)` and `w(r) = μ(r⁻¹) * muConj(r⁻¹)`
  (`TauCeti.DeligneTorus.diagonal_eq_mu_mul_muConj`,
  `TauCeti.DeligneTorus.weight_eq_mu_mul_muConj`), while `μ` does not descend to `ℝ`
  (`TauCeti.DeligneTorus.mu_not_real`, `TauCeti.DeligneTorus.not_exists_bialgHom_mapDomain_eq_mu`);
* pairing `characterGroup` with `muConj` extracts the second exponent
  (`TauCeti.DeligneTorus.characterGroup_muConj`), and `(1, 1)` equals `norm`
  (`TauCeti.DeligneTorus.characterGroup_one_one`);
* the additive group of group-like elements of `baseChangeComplex` is isomorphic to `ℤ × ℤ`
  (`TauCeti.DeligneTorus.additiveGroupLikeComplexAddEquiv`), with the group-like element
  corresponding to `(p, q)` evaluating on base-changed points to `characterGroup R (.ofAdd (p, q))`
  (`TauCeti.DeligneTorus.ofConv_additiveGroupLikeComplexAddEquiv_symm`).

## Main definitions

* `TauCeti.DeligneTorus.muConj R`: the conjugate cocharacter `z ↦ (1, z)` on points over a
  commutative complex algebra `R`.
* `TauCeti.DeligneTorus.muBialgHom`, `TauCeti.DeligneTorus.muConjBialgHom`: the coordinate
  bialgebra homomorphisms `baseChangeComplex →ₐc[ℂ] ℂ[T;T⁻¹]` representing `μ` and `muConj`.
* `TauCeti.DeligneTorus.additiveGroupLikeComplexAddEquiv`: the character-lattice isomorphism
  `Additive (GroupLike ℂ baseChangeComplex) ≃+ ℤ × ℤ`.

## Main results

* `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom`,
  `TauCeti.DeligneTorus.baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom`: point-level
  compatibility for `muBialgHom` and `muConjBialgHom`.
* `TauCeti.DeligneTorus.mapValue_conj_mu`, `TauCeti.DeligneTorus.mapValue_conj_mu_conj`: complex
  conjugation transports `μ` to `muConj`.
* `TauCeti.DeligneTorus.diagonal_eq_mu_mul_muConj`,
  `TauCeti.DeligneTorus.weight_eq_mu_mul_muConj`: factorization of `d` and `w` via `μ` and
  `muConj`.
* `TauCeti.DeligneTorus.mu_not_real`, `TauCeti.DeligneTorus.not_exists_bialgHom_mapDomain_eq_mu`:
  `μ` is not defined over `ℝ`.
* `TauCeti.DeligneTorus.characterGroup_muConj`, `TauCeti.DeligneTorus.characterGroup_one_one`,
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
theorem weight_eq_mu_mul_muConj (r : Rˣ) :
    weight R r = mu R r⁻¹ * muConj R r⁻¹ := by
  apply (complexSplitting R).injective
  rw [complexSplitting_weight, map_mul, complexSplitting_mu, complexSplitting_muConj,
    Prod.mk_mul_mk, mul_one, one_mul]

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

/-- **Compatibility of `muBialgHom` with `mu` on points** over every commutative `ℂ`-algebra `R`
with compatible `ℝ`-algebra structure. -/
theorem baseChangeComplexPointsMulEquiv_mapDomain_muBialgHom
    (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muBialgHom g) =
      mu R (MultiplicativeGroup.pointsMulEquiv g) := by
  have hproj : BialgHom.mapDomain
      (Bialgebra.TensorProduct.projectLeft (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm (g, 1) := by
    rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectLeft]
  rw [muBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, hproj,
    mapDomain_baseChangeComplexBialgEquiv]
  apply (complexSplitting R).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, complexSplitting_mu, map_one]

/-- **Compatibility of `muConjBialgHom` with `muConj` on points** over every commutative
`ℂ`-algebra `R` with compatible `ℝ`-algebra structure. -/
theorem baseChangeComplexPointsMulEquiv_mapDomain_muConjBialgHom
    (g : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)) :
    baseChangeComplexPointsMulEquiv R (BialgHom.mapDomain muConjBialgHom g) =
      muConj R (MultiplicativeGroup.pointsMulEquiv g) := by
  have hproj : BialgHom.mapDomain
      (Bialgebra.TensorProduct.projectRight (R := ℂ) (H₁ := ℂ[T;T⁻¹]) (H₂ := ℂ[T;T⁻¹])) g =
      AffineGroup.Product.pointsMulEquiv.symm ((1 : WithConv (ℂ[T;T⁻¹] →ₐ[ℂ] R)), g) := by
    rw [BialgHom.mapDomain_apply, AffineGroup.Product.mapDomain_projectRight]
  rw [muConjBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply, hproj,
    mapDomain_baseChangeComplexBialgEquiv]
  apply (complexSplitting R).injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, complexSplitting_muConj, map_one]

/-- **Non-example: the Hodge cocharacter `μ` is not defined over `ℝ`**: there is no real
homomorphism `ℝˣ →* S(ℝ)` whose complexification agrees with `μ` on real scalars. -/
theorem mu_not_real :
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

/-- Coordinate-Hopf-algebra form of `mu_not_real`: no bialgebra homomorphism `S →ₐc[ℝ] ℝ[T;T⁻¹]`
induces `μ` on real-scalar points. -/
theorem not_exists_bialgHom_mapDomain_eq_mu :
    ¬ ∃ φ : S →ₐc[ℝ] ℝ[T;T⁻¹],
      ∀ r : ℝˣ,
        AlgHom.mapValue (Algebra.ofId ℝ ℂ)
            (BialgHom.mapDomain φ (MultiplicativeGroup.pointsMulEquiv.symm r)) =
          mu ℂ (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) r) := by
  rintro ⟨φ, hφ⟩
  exact mu_not_real ⟨(BialgHom.mapDomain φ).comp
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

/-- **Galois action on `X*(S)`**: conjugating `characterGroup ℂ (.ofAdd pq)` by complex
conjugation on both `S(ℂ)` and `ℂˣ` produces `characterGroup ℂ (.ofAdd pq.swap)`. -/
theorem characterGroup_conj_monoidHom (pq : ℤ × ℤ) :
    (Units.map (starRingEnd ℂ : ℂ →* ℂ)).comp
        ((characterGroup ℂ (.ofAdd pq)).comp (AlgHom.mapValue Complex.conjAe.toAlgHom)) =
      characterGroup ℂ (.ofAdd pq.swap) := by
  refine MonoidHom.ext fun f ↦ Units.ext ?_
  simp only [MonoidHom.comp_apply]
  rw [characterGroup_conj]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.coe_star, Complex.star_def,
    starRingEnd_self_apply, Prod.swap]

/-- **On real points, the character `(1, 1)` equals the norm `Nm : S(ℝ) →* ℝˣ` embedded into
`ℂˣ`.** -/
theorem characterGroup_norm_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    characterGroup ℂ (.ofAdd (1, 1)) (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) =
      Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) (norm ℝ f) := by
  ext
  simpa using characterGroup_norm f

/-! ### Identification of the algebraic character lattice over `ℂ` with `ℤ × ℤ` -/

private noncomputable def finsuppULiftFinTwoAddEquiv : (ULift.{0} (Fin 2) →₀ ℤ) ≃+ ℤ × ℤ :=
  (Finsupp.domCongr Equiv.ulift).trans
    (Finsupp.addEquivFunOnFinite.trans (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ ℤ)).toAddEquiv)

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
      finsuppULiftFinTwoAddEquiv)

private lemma val_toMul_additiveGroupLikeComplexAddEquiv_symm (pq : ℤ × ℤ) :
    ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      baseChangeSplitTorusIso.hom.hom.hom
        (_root_.MonoidAlgebra.single (Multiplicative.ofAdd (finsuppULiftFinTwoAddEquiv.symm pq))
          1) := by
  simp only [additiveGroupLikeComplexAddEquiv, AddEquiv.symm_trans_apply,
    MulEquiv.toAdditive_apply_symm_apply, toMul_ofMul, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, BialgEquiv.val_mapGroupLike,
    TauCeti.MonoidAlgebra.val_groupLikeEquiv_symm]
  rw [← BialgEquiv.coe_toBialgHom, CommHopfAlgCat.coe_ofIso, Functor.mapIso_hom,
    ObjectProperty.ι_map]
  exact congrArg (fun φ : _ →ₐc[ℂ] baseChangeComplex ↦
      φ (_root_.MonoidAlgebra.single (Multiplicative.ofAdd (finsuppULiftFinTwoAddEquiv.symm pq)) 1))
    rfl

omit [Algebra ℝ R] [IsScalarTower ℝ ℂ R] in
private lemma ofConv_additiveGroupLikeComplexAddEquiv_symm_eq_freeAbelianCharEquiv (pq : ℤ × ℤ)
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      ((freeAbelianCharEquiv.symm
          (SplitTorus.pointsMulEquiv (BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g))
          (Multiplicative.ofAdd (finsuppULiftFinTwoAddEquiv.symm pq)) : Rˣ) : R) := by
  let p : WithConv (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) →ₐ[ℂ] R) :=
    BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g
  have hmap : g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      p.ofConv (_root_.MonoidAlgebra.single
        (Multiplicative.ofAdd (finsuppULiftFinTwoAddEquiv.symm pq)) 1) := by
    rw [val_toMul_additiveGroupLikeComplexAddEquiv_symm]
    exact (BialgHom.mapDomain_apply_apply (A := R) baseChangeSplitTorusIso.hom.hom.hom g _).symm
  rw [hmap]
  change p.ofConv _ = ((freeAbelianCharEquiv.symm (SplitTorus.pointsMulEquiv p) _ : Rˣ) : R)
  rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, MulEquiv.symm_apply_apply,
    DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe]

/-- **Evaluation of the algebraic character lattice on base-changed points**: evaluating a
base-changed `R`-point `g` of `S_ℂ` at the group-like element corresponding to `pq : ℤ × ℤ` under
`additiveGroupLikeComplexAddEquiv.symm` equals `characterGroup R (.ofAdd pq)`. -/
theorem ofConv_additiveGroupLikeComplexAddEquiv_symm (pq : ℤ × ℤ)
    (g : WithConv (baseChangeComplex →ₐ[ℂ] R)) :
    g.ofConv ((additiveGroupLikeComplexAddEquiv.symm pq).toMul : baseChangeComplex) =
      (characterGroup R (.ofAdd pq) (baseChangeComplexPointsMulEquiv R g) : R) := by
  -- Transport `g` along `baseChangeSplitTorusIso` to a point of the rank-two split torus,
  -- then evaluate `freeAbelianCharEquiv.symm` as the product over `Fin 2` of the two coordinates.
  let m : ULift.{0} (Fin 2) →₀ ℤ := finsuppULiftFinTwoAddEquiv.symm pq
  have hm0 : m ⟨0⟩ = pq.1 := congrArg Prod.fst (finsuppULiftFinTwoAddEquiv.apply_symm_apply pq)
  have hm1 : m ⟨1⟩ = pq.2 := congrArg Prod.snd (finsuppULiftFinTwoAddEquiv.apply_symm_apply pq)
  let p : WithConv (MonoidAlgebra ℂ (Multiplicative (ULift.{0} (Fin 2) →₀ ℤ)) →ₐ[ℂ] R) :=
    BialgHom.mapDomain baseChangeSplitTorusIso.hom.hom.hom g
  have hp := pointsMulEquiv_mapDomain_baseChangeSplitTorusIso g
  have hp0 : SplitTorus.pointsMulEquiv p ⟨0⟩ =
      (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).1 := congrArg Prod.fst hp
  have hp1 : SplitTorus.pointsMulEquiv p ⟨1⟩ =
      (complexSplitting R (baseChangeComplexPointsMulEquiv R g)).2 := congrArg Prod.snd hp
  rw [ofConv_additiveGroupLikeComplexAddEquiv_symm_eq_freeAbelianCharEquiv]
  change ((freeAbelianCharEquiv.symm (SplitTorus.pointsMulEquiv p)
      (Multiplicative.ofAdd m) : Rˣ) : R) = _
  rw [freeAbelianCharEquiv_symm_apply_ofAdd,
    Finsupp.prod_fintype _ _ (fun _ ↦ zpow_zero _),
    Fintype.prod_equiv Equiv.ulift
      (fun i : ULift.{0} (Fin 2) ↦ SplitTorus.pointsMulEquiv p i ^ m i)
      (fun i : Fin 2 ↦ SplitTorus.pointsMulEquiv p ⟨i⟩ ^ m ⟨i⟩)
      (fun _ ↦ rfl),
    Fin.prod_univ_two, hp0, hp1, hm0, hm1, characterGroup_apply]

end Characters

end TauCeti.DeligneTorus
