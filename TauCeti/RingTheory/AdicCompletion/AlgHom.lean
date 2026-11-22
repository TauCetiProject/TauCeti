/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.LocalRing.AlgHom

/-!
# Adic completions along algebra homomorphisms

Mathlib's `AdicCompletion.map` is functorial in the module for a fixed ring and ideal. This file
makes the completion of a ring functorial in the pair `(S, I)`: an `R`-algebra homomorphism
`f : S →ₐ[R] S'` with `I ≤ f⁻¹ I'` induces an `R`-algebra homomorphism of completions
`AdicCompletion I S →ₐ[R] AdicCompletion I' S'`, and an `R`-algebra isomorphism carrying `I`
onto `I'` induces an isomorphism of completions. This is what is needed to compare the
completions of isomorphic local rings, for instance of two models of the localization of a ring
at a prime.

We also record an elementary adic uniqueness principle for `k`-algebra homomorphisms into an
adically separated commutative ring (`IsHausdorff J S`): if `G` generates a left ideal modulo which
every element of `R` is represented by a scalar in `k`, then two `k`-algebra homomorphisms
`R →ₐ[k] S` that agree on `G` and send `G` into `J` are congruent modulo every power `J ^ n`, hence
equal (`AlgHom.sub_mem_pow_of_eqOn`, `AlgHom.ext_of_isHausdorff`), without assuming `R` is
commutative. Specializing to local `k`-algebras `R` and `S` with `algebraMap k (ResidueField R)`
surjective yields uniqueness from agreement on any generating set of `maximalIdeal R`
(`AlgHom.ext_of_span_eq_maximalIdeal`), even when `R` is not finitely generated as a `k`-algebra
(as for rings of analytic germs or formal power series).

## Main definitions and results

* `AdicCompletion.factor_evalₐ`: the projections `evalₐ I n` are compatible with the transition
  maps `S ⧸ I ^ n → S ⧸ I ^ m`; in terms of representatives, `AdicCompletion.evalₐ_eq_mk_of_le`.
* `AdicCompletion.mapₐ`: the map of completions induced by an algebra homomorphism, with
  `AdicCompletion.evalₐ_mapₐ`, `AdicCompletion.mapₐ_of`, `AdicCompletion.mapₐ_congr`, and the
  functoriality laws `AdicCompletion.mapₐ_id` and `AdicCompletion.mapₐ_comp`.
* `AdicCompletion.mapₐ_injective` and `AdicCompletion.mapₐ_bijective`: the map of completions is
  injective, resp. bijective, when all the maps `S ⧸ I ^ n → S' ⧸ I' ^ n` are. For instance a
  ring whose quotients by the powers of `I` agree with those of an `I'`-adically complete ring
  `S'` has completion `S'`.
* `AdicCompletion.congrₐ`: the isomorphism of completions induced by an algebra isomorphism,
  with `AdicCompletion.toAlgHom_congrₐ` (it is `mapₐ` of the underlying homomorphism),
  `AdicCompletion.evalₐ_congrₐ`, `AdicCompletion.congrₐ_of`, and the laws
  `AdicCompletion.congrₐ_refl`, `AdicCompletion.congrₐ_symm` and `AdicCompletion.congrₐ_trans`.
* `AlgHom.sub_mem_pow_of_eqOn`, `AlgHom.ext_of_isHausdorff`: adic congruences to every order and
  uniqueness of `k`-algebra homomorphisms into an adically separated commutative ring from
  agreement on a set `G` generating an ideal modulo which every element is represented by a scalar.
* `AlgHom.ext_of_span_eq_maximalIdeal`: specialization to commutative local `k`-algebras, giving
  uniqueness from agreement on generators of the maximal ideal.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2 (for `I`-adic congruences and uniqueness of
  homomorphisms into adically separated targets) and §3 (for the local-ring specialization and
  maximal-ideal generators).
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

/-- If the projection of `x` to `S ⧸ I ^ n` is the class of `a`, then so is its projection to
`S ⧸ I ^ m` for every `m ≤ n`. -/
theorem evalₐ_eq_mk_of_le {m n : ℕ} (hle : m ≤ n) {x : AdicCompletion I S} {a : S}
    (h : evalₐ I n x = Ideal.Quotient.mk _ a) : evalₐ I m x = Ideal.Quotient.mk _ a := by
  rw [← factor_evalₐ hle x, h, Ideal.Quotient.factor_mk]

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

omit [CommRing R] [Algebra R S] [Algebra R S'] in
/-- Pointwise-equal algebra homomorphisms (possibly over distinct base rings `R₁` and `R₂`) induce
the same map on adic completions. -/
theorem mapₐ_congr {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Algebra R₁ S] [Algebra R₁ S']
    [Algebra R₂ S] [Algebra R₂ S'] {f₁ : S →ₐ[R₁] S'} {f₂ : S →ₐ[R₂] S'}
    {hf₁ : I ≤ I'.comap f₁} {hf₂ : I ≤ I'.comap f₂} (h : ∀ s, f₁ s = f₂ s)
    (x : AdicCompletion I S) :
    mapₐ f₁ hf₁ x = mapₐ f₂ hf₂ x :=
  ext_evalₐ fun n ↦ by
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    simp [← hs, h s]

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

end AdicCompletion

namespace AlgHom

/-- **Adic congruences from generators modulo which every element is a scalar.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and
`φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into an ideal `J` of `S`. Then `φ r - ψ r ∈ J ^ n`
for every `n : ℕ` and `r : R`. -/
theorem sub_mem_pow_of_eqOn {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} {J : Ideal S}
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    ∀ (n : ℕ) (r : R), φ r - ψ r ∈ J ^ n
  | 0, _ => by simp
  | n + 1, r => by
    have hψJ : Ideal.span G ≤ J.comap ψ.toRingHom :=
      Ideal.span_le.2 fun g hg ↦ Ideal.mem_comap.2 (hG hg ▸ hGJ g hg)
    obtain ⟨c, hc⟩ := haug r
    have hrc : φ r - ψ r = φ (r - algebraMap k R c) - ψ (r - algebraMap k R c) := by simp
    rw [hrc]
    refine Submodule.span_induction (p := fun x _ ↦ φ x - ψ x ∈ J ^ (n + 1))
      (fun g hg ↦ by simp [hG hg]) (by simp)
      (fun x y _ _ hx hy ↦ by simpa only [map_add, sub_add_sub_comm] using add_mem hx hy)
      (fun a x hx ihx ↦ ?_) hc
    have hsplit : φ (a • x) - ψ (a • x) = φ a * (φ x - ψ x) + (φ a - ψ a) * ψ x := by
      simp only [smul_eq_mul, map_mul, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ (φ a) ihx)
      (pow_succ J n ▸ Ideal.mul_mem_mul (sub_mem_pow_of_eqOn haug hGJ hG n a) (hψJ hx))

/-- **Uniqueness of `k`-algebra homomorphisms into an adically separated ring.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and `S` is
`IsHausdorff J S` for an ideal `J` of `S`. If `φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into
`J`, then `φ = ψ`. -/
theorem ext_of_isHausdorff {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} (J : Ideal S) [IsHausdorff J S]
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    φ = ψ :=
  AlgHom.coe_fn_injective <| IsHausdorff.funext' J fun n r ↦
    Ideal.Quotient.eq.2 (sub_mem_pow_of_eqOn haug hGJ hG n r)

/-- **Uniqueness of `k`-algebra homomorphisms of local rings from maximal-ideal generators.** Let
`R` and `S` be commutative local `k`-algebras such that `algebraMap k (ResidueField R)` is
surjective and `S` is separated (`IsHausdorff`) with respect to its maximal ideal. If `G` generates
`maximalIdeal R` and `φ, ψ : R →ₐ[k] S` agree on `G` with `φ` local (no locality assumption on `ψ`
is needed), then `φ = ψ`. -/
theorem ext_of_span_eq_maximalIdeal {k R S : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra k R] [Algebra k S]
    [IsHausdorff (IsLocalRing.maximalIdeal S) S] {φ ψ : R →ₐ[k] S} [IsLocalHom φ]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)))
    {G : Set R} (hG_span : Ideal.span G = IsLocalRing.maximalIdeal R)
    (hG : Set.EqOn φ ψ G) :
    φ = ψ := by
  have : IsLocalHom φ.toRingHom := ⟨IsLocalHom.map_nonunit (f := φ)⟩
  refine ext_of_isHausdorff (IsLocalRing.maximalIdeal S) (fun r ↦ ?_) (fun g hg ↦ ?_) hG
  · obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R r)
    refine ⟨c, hG_span.symm ▸ (IsLocalRing.residue_eq_zero_iff _).1 ?_⟩
    rw [map_sub, TauCeti.residue_algebraMap, hc, sub_self]
  · exact map_nonunit φ.toRingHom g (hG_span ▸ Ideal.subset_span hg)

end AlgHom
