/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Adic completions along algebra homomorphisms

Mathlib's `AdicCompletion.map` is functorial in the module for a fixed ring and ideal. This file
makes the completion of a ring functorial in the pair `(S, I)`: an `R`-algebra homomorphism
`f : S →ₐ[R] S'` with `I ≤ f⁻¹ I'` induces an `R`-algebra homomorphism of completions
`AdicCompletion I S →ₐ[R] AdicCompletion I' S'`, and an `R`-algebra isomorphism carrying `I`
onto `I'` induces an isomorphism of completions. This is what is needed to compare the
completions of isomorphic local rings, for instance of two models of the localization of a ring
at a prime.

## Main definitions and results

* `AdicCompletion.factor_evalₐ`: the projections `evalₐ I n` are compatible with the transition
  maps `S ⧸ I ^ n → S ⧸ I ^ m`.
* `AdicCompletion.mapₐ`: the map of completions induced by an algebra homomorphism, with
  `AdicCompletion.evalₐ_mapₐ` and `AdicCompletion.mapₐ_of`, and the functoriality laws
  `AdicCompletion.mapₐ_id` and `AdicCompletion.mapₐ_comp`.
* `AdicCompletion.congrₐ`: the isomorphism of completions induced by an algebra isomorphism,
  with `AdicCompletion.toAlgHom_congrₐ` (it is `mapₐ` of the underlying homomorphism),
  `AdicCompletion.evalₐ_congrₐ`, `AdicCompletion.congrₐ_of`, and the laws
  `AdicCompletion.congrₐ_refl`, `AdicCompletion.congrₐ_symm` and `AdicCompletion.congrₐ_trans`.
-/

public section

namespace AdicCompletion

variable {R S S' S'' : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing S'']
  [Algebra R S] [Algebra R S'] [Algebra R S''] {I : Ideal S} {I' : Ideal S'} {I'' : Ideal S''}

/-- The projections of the adic completion to `S ⧸ I ^ n` are compatible with the transition maps
`S ⧸ I ^ n → S ⧸ I ^ m` for `m ≤ n`. -/
@[simp]
theorem factor_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨c, rfl⟩ := mk_surjective I S x
  simp [AdicCompletion.Ideal.mk_eq_mk I hle]

private theorem mapₐ_aux (f : S →ₐ[R] S') (hf : I ≤ I'.comap f) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
        ((Ideal.quotientMapₐ (I' ^ n) f
          ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n))).comp
          ((evalₐ I n).restrictScalars R)) =
      (Ideal.quotientMapₐ (I' ^ m) f
          ((Ideal.pow_right_mono hf m).trans (Ideal.le_comap_pow _ m))).comp
        ((evalₐ I m).restrictScalars R) := by
  ext x
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, ← factor_evalₐ hle x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  simp [← hy]

/-- An `R`-algebra homomorphism `f : S →ₐ[R] S'` with `I ≤ f⁻¹ I'` induces an `R`-algebra
homomorphism `AdicCompletion I S →ₐ[R] AdicCompletion I' S'`, reducing modulo `I' ^ n` to the map
`S ⧸ I ^ n → S' ⧸ I' ^ n` induced by `f`. -/
noncomputable def mapₐ (f : S →ₐ[R] S') (hf : I ≤ I'.comap f) :
    AdicCompletion I S →ₐ[R] AdicCompletion I' S' :=
  liftAlgHom I' (fun n ↦ (Ideal.quotientMapₐ (I' ^ n) f
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n))).comp
      ((evalₐ I n).restrictScalars R)) (mapₐ_aux f hf)

/-- Modulo `I' ^ n`, the map of completions `mapₐ f hf` is the map `S ⧸ I ^ n → S' ⧸ I' ^ n`
induced by `f`. -/
@[simp]
theorem evalₐ_mapₐ (f : S →ₐ[R] S') (hf : I ≤ I'.comap f) (n : ℕ) (x : AdicCompletion I S) :
    evalₐ I' n (mapₐ f hf x) = Ideal.quotientMap (I' ^ n) f.toRingHom
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)) (evalₐ I n x) :=
  evalₐ_liftAlgHom _ _ (mapₐ_aux f hf) _ _

/-- The map of completions extends `f` along the canonical maps `S → AdicCompletion I S` and
`S' → AdicCompletion I' S'`. -/
@[simp]
theorem mapₐ_of (f : S →ₐ[R] S') (hf : I ≤ I'.comap f) (x : S) :
    mapₐ f hf (of I S x) = of I' S' (f x) :=
  ext_evalₐ fun n ↦ by simp

/-- The identity of `S` induces the identity of `AdicCompletion I S`. -/
@[simp]
theorem mapₐ_id (hf : I ≤ I.comap (AlgHom.id R S)) :
    mapₐ (AlgHom.id R S) hf = AlgHom.id R (AdicCompletion I S) :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    simp [← hy]

/-- The map of completions induced by a composite is the composite of the induced maps. -/
theorem mapₐ_comp (g : S' →ₐ[R] S'') (hg : I' ≤ I''.comap g) (f : S →ₐ[R] S')
    (hf : I ≤ I'.comap f) :
    (mapₐ g hg).comp (mapₐ f hf) = mapₐ (g.comp f) (hf.trans (Ideal.comap_mono hg)) :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    simp [← hy]

/-- Pointwise form of `AdicCompletion.mapₐ_comp`. -/
@[simp]
theorem mapₐ_mapₐ (g : S' →ₐ[R] S'') (hg : I' ≤ I''.comap g) (f : S →ₐ[R] S')
    (hf : I ≤ I'.comap f) (x : AdicCompletion I S) :
    mapₐ g hg (mapₐ f hf x) = mapₐ (g.comp f) (hf.trans (Ideal.comap_mono hg)) x :=
  DFunLike.congr_fun (mapₐ_comp g hg f hf) x

/-- An `R`-algebra isomorphism `e : S ≃ₐ[R] S'` carrying `I` onto `I'` induces an `R`-algebra
isomorphism `AdicCompletion I S ≃ₐ[R] AdicCompletion I' S'`. -/
noncomputable def congrₐ (e : S ≃ₐ[R] S') (he : I.map e = I') :
    AdicCompletion I S ≃ₐ[R] AdicCompletion I' S' :=
  AlgEquiv.ofAlgHom (mapₐ (e : S →ₐ[R] S') (he ▸ Ideal.le_comap_map))
    (mapₐ (e.symm : S' →ₐ[R] S) (he ▸ (Ideal.comap_symm (e : S ≃+* S')).ge))
    (AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I' n x)
      simp [← hy])
    (AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      simp [← hy])

/-- As an algebra homomorphism, `congrₐ e he` is the map of completions induced by `e`. -/
@[simp]
theorem toAlgHom_congrₐ (e : S ≃ₐ[R] S') (he : I.map e = I') :
    (congrₐ e he : AdicCompletion I S →ₐ[R] AdicCompletion I' S') =
      mapₐ (e : S →ₐ[R] S') (he ▸ Ideal.le_comap_map) :=
  AlgHom.ext fun _ ↦ rfl

/-- The identity isomorphism of `S` induces the identity isomorphism of `AdicCompletion I S`. -/
@[simp]
theorem congrₐ_refl (he : I.map (AlgEquiv.refl : S ≃ₐ[R] S) = I) :
    congrₐ AlgEquiv.refl he = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective (mapₐ_id fun _ h ↦ h)

/-- The inverse of `congrₐ e he` is the isomorphism of completions induced by `e.symm`. -/
@[simp]
theorem congrₐ_symm (e : S ≃ₐ[R] S') (he : I.map e = I') :
    (congrₐ e he).symm = congrₐ e.symm (he ▸ Ideal.map_of_equiv (e : S ≃+* S')) :=
  AlgEquiv.ext fun _ ↦ rfl

/-- The isomorphism of completions induced by a composite is the composite of the induced
isomorphisms. -/
@[simp]
theorem congrₐ_trans (e : S ≃ₐ[R] S') (he : I.map e = I') (e' : S' ≃ₐ[R] S'')
    (he' : I'.map e' = I'') :
    (congrₐ e he).trans (congrₐ e' he') =
      congrₐ (e.trans e') (by
        subst he he'; exact (Ideal.map_map (e : S →+* S') (e' : S' →+* S'')).symm) :=
  AlgEquiv.coe_toAlgHom_injective
    (mapₐ_comp (e' : S' →ₐ[R] S'') (he' ▸ Ideal.le_comap_map) (e : S →ₐ[R] S')
      (he ▸ Ideal.le_comap_map))

/-- Pointwise form of `AdicCompletion.congrₐ_trans`. -/
@[simp]
theorem congrₐ_congrₐ (e : S ≃ₐ[R] S') (he : I.map e = I') (e' : S' ≃ₐ[R] S'')
    (he' : I'.map e' = I'') (x : AdicCompletion I S) :
    congrₐ e' he' (congrₐ e he x) =
      congrₐ (e.trans e') (by
        subst he he'; exact (Ideal.map_map (e : S →+* S') (e' : S' →+* S'')).symm) x :=
  DFunLike.congr_fun (congrₐ_trans e he e' he') x

/-- The isomorphism of completions extends `e` along the canonical maps into the completions. -/
@[simp]
theorem congrₐ_of (e : S ≃ₐ[R] S') (he : I.map e = I') (x : S) :
    congrₐ e he (of I S x) = of I' S' (e x) :=
  mapₐ_of (e : S →ₐ[R] S') (he ▸ Ideal.le_comap_map) x

/-- Modulo `I' ^ n`, the isomorphism of completions `congrₐ e he` is the map
`S ⧸ I ^ n → S' ⧸ I' ^ n` induced by `e`. -/
@[simp]
theorem evalₐ_congrₐ (e : S ≃ₐ[R] S') (he : I.map e = I') (n : ℕ) (x : AdicCompletion I S) :
    evalₐ I' n (congrₐ e he x) = Ideal.quotientMap (I' ^ n) (e : S →+* S')
      ((Ideal.pow_right_mono (he ▸ Ideal.le_comap_map) n).trans (Ideal.le_comap_pow _ n))
      (evalₐ I n x) :=
  evalₐ_mapₐ (e : S →ₐ[R] S') (he ▸ Ideal.le_comap_map) n x

/-- Modulo `I ^ n`, the inverse of `congrₐ e he` is the map `S' ⧸ I' ^ n → S ⧸ I ^ n` induced
by `e.symm`. -/
theorem evalₐ_congrₐ_symm (e : S ≃ₐ[R] S') (he : I.map e = I') (n : ℕ)
    (x : AdicCompletion I' S') :
    evalₐ I n ((congrₐ e he).symm x) = Ideal.quotientMap (I ^ n) (e.symm : S' →+* S)
      ((Ideal.pow_right_mono (he ▸ (Ideal.comap_symm (e : S ≃+* S')).ge) n).trans
        (Ideal.le_comap_pow _ n))
      (evalₐ I' n x) :=
  evalₐ_mapₐ (e.symm : S' →ₐ[R] S) (he ▸ (Ideal.comap_symm (e : S ≃+* S')).ge) n x

/-- The inverse of `congrₐ e he` extends `e.symm` along the canonical maps into the
completions. -/
theorem congrₐ_symm_of (e : S ≃ₐ[R] S') (he : I.map e = I') (x : S') :
    (congrₐ e he).symm (of I' S' x) = of I S (e.symm x) :=
  mapₐ_of (e.symm : S' →ₐ[R] S) (he ▸ (Ideal.comap_symm (e : S ≃+* S')).ge) x

end AdicCompletion
