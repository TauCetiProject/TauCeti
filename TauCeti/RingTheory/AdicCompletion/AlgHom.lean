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
* `AdicCompletion.mapₐ_injective` and `AdicCompletion.mapₐ_bijective`: the map of completions is
  injective, resp. bijective, when all the maps `S ⧸ I ^ n → S' ⧸ I' ^ n` are. For instance a
  ring whose quotients by the powers of `I` agree with those of an `I'`-adically complete ring
  `S'` has completion `S'`.
* `AdicCompletion.congrₐ`: the isomorphism of completions induced by an algebra isomorphism,
  with `AdicCompletion.toAlgHom_congrₐ` (it is `mapₐ` of the underlying homomorphism),
  `AdicCompletion.evalₐ_congrₐ`, `AdicCompletion.congrₐ_of`, and the laws
  `AdicCompletion.congrₐ_refl`, `AdicCompletion.congrₐ_symm` and `AdicCompletion.congrₐ_trans`.
* `AdicCompletion.mapOfPowLe` and `AdicCompletion.equivOfExistsPowLe`: canonical `R`-algebra
  maps and isomorphisms `AdicCompletion I R ≃ₐ[R] AdicCompletion J R` when powers of `I` and `J`
  are mutually cofinal, without requiring finite generation.
-/

public section

namespace AdicCompletion

section

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

/-- The map of completions is injective if every map `S ⧸ I ^ n → S' ⧸ I' ^ n` induced by `f` is
injective. -/
theorem mapₐ_injective (f : S →ₐ[R] S') (hf : I ≤ I'.comap f)
    (h : ∀ n, Function.Injective (Ideal.quotientMap (I' ^ n) f.toRingHom
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)))) :
    Function.Injective (mapₐ f hf) := fun x y hxy ↦
  ext_evalₐ fun n ↦ h n (by simpa using congrArg (evalₐ I' n) hxy)

/-- **Completions agree when all the quotients do.** The map of completions is bijective if every
map `S ⧸ I ^ n → S' ⧸ I' ^ n` induced by `f` is bijective. -/
theorem mapₐ_bijective (f : S →ₐ[R] S') (hf : I ≤ I'.comap f)
    (h : ∀ n, Function.Bijective (Ideal.quotientMap (I' ^ n) f.toRingHom
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)))) :
    Function.Bijective (mapₐ f hf) := by
  refine ⟨mapₐ_injective f hf fun n ↦ (h n).1, fun y ↦ ?_⟩
  -- The inverses of the maps of quotients are compatible, so they lift to the completion.
  let e (n : ℕ) := RingEquiv.ofBijective _ (h n)
  let g (n : ℕ) : AdicCompletion I' S' →+* S ⧸ I ^ n :=
    (e n).symm.toRingHom.comp (evalₐ I' n).toRingHom
  have hg {m n : ℕ} (hle : m ≤ n) : (Ideal.Quotient.factorPow I hle).comp (g n) = g m := by
    ext z
    apply (e m).injective
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective ((e n).symm (evalₐ I' n z))
    have hz : evalₐ I' n z = Ideal.Quotient.mk (I' ^ n) (f s) := by
      rw [← (e n).apply_symm_apply (evalₐ I' n z), ← hs]
      simp [e]
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [← hs, ← factor_evalₐ hle z, hz]
    simp [e]
  refine ⟨liftRingHom I g hg y, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_mapₐ, evalₐ_liftRingHom]
  exact (e n).apply_symm_apply _

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

end

section CofinalIdeals

variable {R : Type*} [CommRing R] {I J K : Ideal R}

private theorem mapOfPowLe_aux {a : ℕ} (h : I ^ a ≤ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp
        ((Ideal.Quotient.factorₐ R ((pow_mul I a n).symm ▸ Ideal.pow_right_mono h n)).comp
          (evalₐ I (a * n))) =
      (Ideal.Quotient.factorₐ R ((pow_mul I a m).symm ▸ Ideal.pow_right_mono h m)).comp
        (evalₐ I (a * m)) := by
  ext x
  simp only [AlgHom.comp_apply, ← factor_evalₐ (Nat.mul_le_mul_left a hle) x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I (a * n) x)
  simp [← hy]

/-- If `I ^ a ≤ J`, the canonical `R`-algebra homomorphism
`AdicCompletion I R →ₐ[R] AdicCompletion J R` induced by `R ⧸ I ^ (a * n) → R ⧸ J ^ n`. -/
noncomputable def mapOfPowLe {a : ℕ} (h : I ^ a ≤ J) :
    AdicCompletion I R →ₐ[R] AdicCompletion J R :=
  liftAlgHom J (fun n ↦ (Ideal.Quotient.factorₐ R
      ((pow_mul I a n).symm ▸ Ideal.pow_right_mono h n)).comp (evalₐ I (a * n)))
    (mapOfPowLe_aux h)

/-- Modulo `J ^ n`, `mapOfPowLe h` factors through `evalₐ I (a * n)`. -/
@[simp]
theorem evalₐ_mapOfPowLe {a : ℕ} (h : I ^ a ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (mapOfPowLe h x) =
      Ideal.Quotient.factor ((pow_mul I a n).symm ▸ Ideal.pow_right_mono h n)
        (evalₐ I (a * n) x) :=
  evalₐ_liftAlgHom _ _ (mapOfPowLe_aux h) _ _

/-- `mapOfPowLe` sends `of I R x` to `of J R x`. -/
@[simp]
theorem mapOfPowLe_of {a : ℕ} (h : I ^ a ≤ J) (x : R) :
    mapOfPowLe h (of I R x) = of J R x :=
  (mapOfPowLe h).commutes x

/-- The map `mapOfPowLe` is independent of the exponent `a` satisfying `I ^ a ≤ J`. -/
theorem mapOfPowLe_eq {a b : ℕ} (ha : I ^ a ≤ J) (hb : I ^ b ≤ J) :
    mapOfPowLe ha = mapOfPowLe hb :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    simp only [evalₐ_mapOfPowLe]
    have ha' := factor_evalₐ (Nat.mul_le_mul_right n (le_max_left a b)) x
    have hb' := factor_evalₐ (Nat.mul_le_mul_right n (le_max_right a b)) x
    rw [← ha', ← hb']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I (max a b * n) x)
    simp [← hy]

/-- Any `mapOfPowLe` from an ideal to itself is the identity. -/
@[simp]
theorem mapOfPowLe_self {a : ℕ} (h : I ^ a ≤ I) :
    mapOfPowLe h = AlgHom.id R (AdicCompletion I R) := by
  rw [mapOfPowLe_eq h (pow_one I).le]
  exact AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    simp only [evalₐ_mapOfPowLe, AlgHom.id_apply]
    rw [← factor_evalₐ (one_mul n).le x]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    simp [← hz]

/-- `mapOfPowLe` is functorial in compositions of power inclusions. -/
theorem mapOfPowLe_comp {a b : ℕ} (hIJ : I ^ a ≤ J) (hJK : J ^ b ≤ K) :
    (mapOfPowLe hJK).comp (mapOfPowLe hIJ) =
      mapOfPowLe (show I ^ (a * b) ≤ K by
        rw [pow_mul]
        exact (Ideal.pow_right_mono hIJ b).trans hJK) :=
  AlgHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    simp only [AlgHom.comp_apply, evalₐ_mapOfPowLe]
    rw [← factor_evalₐ (mul_assoc a b n).ge x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I (a * b * n) x)
    simp [← hy]

/-- If powers of `I` and `J` are mutually cofinal (`∃ a, I ^ a ≤ J` and `∃ b, J ^ b ≤ I`), the
`I`-adic and `J`-adic completions of `R` are canonically isomorphic as `R`-algebras. -/
noncomputable def equivOfExistsPowLe (hIJ : ∃ a, I ^ a ≤ J) (hJI : ∃ b, J ^ b ≤ I) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J R :=
  AlgEquiv.ofAlgHom (mapOfPowLe hIJ.choose_spec) (mapOfPowLe hJI.choose_spec)
    ((mapOfPowLe_comp hJI.choose_spec hIJ.choose_spec).trans (mapOfPowLe_self _))
    ((mapOfPowLe_comp hIJ.choose_spec hJI.choose_spec).trans (mapOfPowLe_self _))

/-- `equivOfExistsPowLe` sends `of I R x` to `of J R x`. -/
@[simp]
theorem equivOfExistsPowLe_of (hIJ : ∃ a, I ^ a ≤ J) (hJI : ∃ b, J ^ b ≤ I) (x : R) :
    equivOfExistsPowLe hIJ hJI (of I R x) = of J R x :=
  (equivOfExistsPowLe hIJ hJI).commutes x

/-- `equivOfExistsPowLe` from an ideal to itself is the identity isomorphism. -/
@[simp]
theorem equivOfExistsPowLe_self (h : ∃ a, I ^ a ≤ I) :
    equivOfExistsPowLe h h = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective (mapOfPowLe_self h.choose_spec)

/-- The inverse of `equivOfExistsPowLe hIJ hJI` is `equivOfExistsPowLe hJI hIJ`. -/
@[simp]
theorem equivOfExistsPowLe_symm (hIJ : ∃ a, I ^ a ≤ J) (hJI : ∃ b, J ^ b ≤ I) :
    (equivOfExistsPowLe hIJ hJI).symm = equivOfExistsPowLe hJI hIJ :=
  AlgEquiv.ext fun _ ↦ rfl

/-- Composition of `equivOfExistsPowLe` is `equivOfExistsPowLe` for the composed inclusions. -/
@[simp]
theorem equivOfExistsPowLe_trans (hIJ : ∃ a, I ^ a ≤ J) (hJI : ∃ b, J ^ b ≤ I)
    (hJK : ∃ c, J ^ c ≤ K) (hKJ : ∃ d, K ^ d ≤ J) :
    (equivOfExistsPowLe hIJ hJI).trans (equivOfExistsPowLe hJK hKJ) =
      equivOfExistsPowLe
        (let ⟨a, ha⟩ := hIJ; let ⟨c, hc⟩ := hJK
          ⟨a * c, by rw [pow_mul]; exact (Ideal.pow_right_mono ha c).trans hc⟩)
        (let ⟨d, hd⟩ := hKJ; let ⟨b, hb⟩ := hJI
          ⟨d * b, by rw [pow_mul]; exact (Ideal.pow_right_mono hd b).trans hb⟩) := by
  refine AlgEquiv.coe_toAlgHom_injective ?_
  have hIK : ∃ e, I ^ e ≤ K := by
    obtain ⟨a, ha⟩ := hIJ
    obtain ⟨c, hc⟩ := hJK
    exact ⟨a * c, by rw [pow_mul]; exact (Ideal.pow_right_mono ha c).trans hc⟩
  change (mapOfPowLe hJK.choose_spec).comp (mapOfPowLe hIJ.choose_spec) =
    mapOfPowLe hIK.choose_spec
  exact (mapOfPowLe_comp hIJ.choose_spec hJK.choose_spec).trans (mapOfPowLe_eq _ hIK.choose_spec)

end CofinalIdeals

end AdicCompletion
