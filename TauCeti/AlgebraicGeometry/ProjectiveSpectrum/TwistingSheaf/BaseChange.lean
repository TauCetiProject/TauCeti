/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Functor
public import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Base change of the sections of twisting sheaves over standard opens

Let `f : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism over a coefficient extension `R → S` which is a
base change in every degree: each component `𝒜ⱼ → ℬⱼ` exhibits `ℬⱼ` as `S ⊗[R] 𝒜ⱼ`. For `a`
homogeneous of positive degree, this file proves that pulling back sections of the twisting sheaf
`𝒪(n)` along `Proj.map f`,

`Γ(D₊(a), 𝒪_{Proj 𝒜}(n)) → Γ(D₊(f a), 𝒪_{Proj ℬ}(n))`,

is a base change along the map of functions `Γ(D₊(a), 𝒪) → Γ(D₊(f a), 𝒪)`
(`AlgebraicGeometry.Proj.twistingSheaf.isBaseChange_comap_basicOpen`), for every `n ∈ ℤ`. For
`n = 0` this is the base change of homogeneous localizations
`HomogeneousLocalization.Away.baseChangeEquiv`; the argument here works with the description of
the sections over `D₊(a)` as fractions `r / aᵏ` (`exists_eq_const_basicOpen`) and of their
vanishing (`const_eq_zero_iff`). It is the affine input for comparing `(Proj.map f)^* 𝒪(n)` with
`𝒪(n)`, and hence for the compatibility of the relative `Proj` with base change on twisting
sheaves.

The proof puts an element of `Γ(D₊(f a), 𝒪) ⊗ Γ(D₊(a), 𝒪(n))` over a common denominator `aᵏ`,
with numerator in `S ⊗[R] 𝒜ⱼ`. Injectivity then reduces to the injectivity of `S ⊗[R] 𝒜ⱼ → ℬⱼ`.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.isBaseChange_comap_basicOpen`: on standard opens, pulling
  back sections of `𝒪(n)` along a degreewise base change is a base change.

## References

* [Stacks, Lemma 27.11.6 (01N2)](https://stacks.math.columbia.edu/tag/01N2)

Adapted from the
[relative Proj base-change formalization](https://github.com/roed-math/TauCeti-w2-fresh/tree/8bf602f6c2bed52e7e390df1ba2c2de30f8a6dfb)
by `roed-math`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace HomogeneousLocalization
open scoped TensorProduct

namespace AlgebraicGeometry.Proj.twistingSheaf

universe u

section

variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ} {a : A} {d : ℕ}

/-- The section `r / aᵏ` of `𝒪(n)` over `D₊(a)`, for `r` homogeneous of degree `k d + n`. -/
private abbrev fracPow (ha : a ∈ 𝒜 d) (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : A)
    (hr : r ∈ 𝒜 j) : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) :=
  const h r (a ^ k) hr (by simpa [mul_comm] using SetLike.pow_mem_graded k ha) (basicOpen 𝒜 a)
    fun x hx hak ↦ hx (x.isPrime.mem_of_pow_mem k hak)

/-- The fractions `r / aᵏ`, `r ∈ 𝒜 j`, as an additive map. -/
private def fracPowHom (ha : a ∈ 𝒜 d) (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) :
    𝒜 j →+ Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) where
  toFun r := fracPow ha k j h r r.property
  map_zero' := const_zero ..
  map_add' _ _ := (const_add ..).symm

/-- The function `y / aˡ` on `D₊(a)` multiplies the section `x / aᵏ` of `𝒪(n)` to
`(y x) / aˡ⁺ᵏ`. -/
private theorem awayToSection_mk_smul_fracPow (ha : a ∈ 𝒜 d) (l k j : ℕ)
    (h : (j : ℤ) = (k * d : ℕ) + n) (h' : ((l * d + j : ℕ) : ℤ) = ((l + k) * d : ℕ) + n)
    (y x : A) (hy : y ∈ 𝒜 (l * d)) (hx : x ∈ 𝒜 j) :
    awayToSection 𝒜 a (Away.mk 𝒜 ha l y hy) • fracPow ha k j h x hx =
      fracPow ha (l + k) (l * d + j) h' (y * x) (SetLike.mul_mem_graded hy hx) := by
  refine ext fun z ↦ (mul_sectionsLinearEquivTwistingSheafZero_apply _ _ z).symm.trans ?_
  -- Under `Γ(D₊(a), 𝒪) ≃ Γ(D₊(a), 𝒪(0))`, the function `y / aˡ` is the fraction `y / aˡ`.
  rw [show sectionsLinearEquivTwistingSheafZero 𝒜 _ (awayToSection 𝒜 a (Away.mk 𝒜 ha l y hy)) =
    fracPow (n := 0) ha l (l * d) (by simp) y hy from ext fun _ ↦ rfl]
  erw [mul_const, const_apply, const_apply]
  exact congrArg _ (Subtype.ext (pow_add ..).symm)

end

-- Both projective spectra lie in `Scheme.{u}`; the coefficient rings have arbitrary universes.
variable {R S : Type*} {A B : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  (φ : ∀ j, 𝒜 j →ₗ[R] ℬ j) (hφ : ∀ j x, (φ j x : B) = f x)
  {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)

variable (ℬ) in
/-- The image of `s : S` as a function on `D₊(b)`. -/
private abbrev coeff (b : B) : S →+* Γ(Proj ℬ, basicOpen ℬ b) :=
  (awayToSection ℬ b).hom.comp (algebraMap S (Away ℬ b))

variable [Algebra Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))]
  (halg : ∀ c, algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a)) c =
    (map f hf).appLE _ _ (map_preimage_basicOpen f hf a).ge c)

include halg hφ in
/-- The scalar `r : R` acts on `D₊(f a)` through either coefficient ring. -/
private theorem coeff_smul (r : R) (s : S) :
    coeff ℬ (f a) (r • s) =
      algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) _ (awayToSection 𝒜 a (Away.mk 𝒜 ha 0 (algebraMap R A r)
        (by simpa using SetLike.algebraMap_mem_graded 𝒜 r))) * coeff ℬ (f a) s := by
  have hfR (r : R) : f (algebraMap R A r) = algebraMap R B r := by
    have h1 : (1 : A) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    have e : (⟨algebraMap R A r, SetLike.algebraMap_mem_graded 𝒜 r⟩ : 𝒜 0) = r • ⟨1, h1⟩ :=
      Subtype.ext (Algebra.algebraMap_eq_smul_one r)
    rw [← hφ 0 ⟨_, SetLike.algebraMap_mem_graded 𝒜 r⟩, e, map_smul,
      Submodule.coe_smul_of_tower, hφ, map_one, Algebra.algebraMap_eq_smul_one]
  rw [halg, ← CommRingCat.comp_apply, awayToSection_comp_appLE _ _ ha, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, Away.map_mk, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
  refine congrArg _ (HomogeneousLocalization.val_injective _ ?_)
  rw [HomogeneousLocalization.val_mul, Away.val_mk, hfR]
  simp only [HomogeneousLocalization.val_algebraMap,
    IsScalarTower.algebraMap_apply S B (Localization _), ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
  simp only [pow_zero, Submonoid.coe_one, mul_one, one_mul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

include halg hφ in
/-- Scalars of `R` move across the tensor product of the fractions `s ⊗ r / aᵏ`. -/
private theorem coeff_smul_tmul (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : R) (s : S)
    (x : 𝒜 j) :
    coeff ℬ (f a) (r • s) ⊗ₜ[Γ(Proj 𝒜, basicOpen 𝒜 a)] fracPowHom ha k j h x =
      coeff ℬ (f a) s ⊗ₜ fracPowHom ha k j h (r • x) := by
  rw [coeff_smul f hf φ hφ ha halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
  congr 1
  -- Unpack the private additive map to compare the fraction representatives.
  change _ • fracPow ha k j h x x.property = fracPow ha k j h _ (r • x).property
  exact (awayToSection_mk_smul_fracPow ha 0 k j h (by simpa using h) _ _ _ x.property).trans
    (const_ext (by simp [Algebra.smul_def]))

/-- The elements `∑ s ⊗ r / aᵏ` of `Γ(D₊(f a), 𝒪) ⊗ Γ(D₊(a), 𝒪(n))`, for `∑ s ⊗ r ∈ S ⊗[R] 𝒜ⱼ`. -/
private def theta (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) :
    S ⊗[R] 𝒜 j →+ Γ(Proj ℬ, basicOpen ℬ (f a)) ⊗[Γ(Proj 𝒜, basicOpen 𝒜 a)]
      Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) :=
  TensorProduct.liftAddHom
    { toFun s :=
        (TensorProduct.mk _ _ _ (coeff ℬ (f a) s)).toAddMonoidHom.comp (fracPowHom ha k j h)
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
    fun r s x ↦ coeff_smul_tmul f hf φ hφ ha n halg k j h r s x

private theorem theta_tmul (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (s : S) (x : 𝒜 j) :
    theta f hf φ hφ ha n halg k j h (s ⊗ₜ x) = coeff ℬ (f a) s ⊗ₜ fracPowHom ha k j h x :=
  TensorProduct.liftAddHom_tmul ..

/-- Multiplication by `aᴺ`, from `𝒜ⱼ` to `𝒜_J`, `J = N d + j`. -/
private def mulPow (N j J : ℕ) (hJ : N * d + j = J) : 𝒜 j →ₗ[R] 𝒜 J :=
  (LinearEquiv.ofEq _ _ (congrArg 𝒜 hJ)).toLinearMap ∘ₗ DirectSum.gMulLHom R (fun i ↦ 𝒜 i)
    ⟨a ^ N, by simpa [mul_comm] using SetLike.pow_mem_graded N ha⟩

/-- Raising the denominator `aᵏ` to `aᵏ⁺ᴺ` does not change the elements `∑ s ⊗ r / aᵏ`. -/
private theorem theta_mulPow (k j N J K : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n)
    (hJ : N * d + j = J) (hK : k + N = K) (h' : (J : ℤ) = (K * d : ℕ) + n) (t : S ⊗[R] 𝒜 j) :
    theta f hf φ hφ ha n halg K J h' ((mulPow ha N j J hJ).baseChange S t) =
      theta f hf φ hφ ha n halg k j h t := by
  subst hK
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]
  | tmul s x =>
    rw [LinearMap.baseChange_tmul, theta_tmul, theta_tmul]
    congr 1
    -- Unpack the private additive and linear maps to compare their fraction representatives.
    change fracPow ha (k + N) J h' (a ^ N * x) (mulPow ha N j J hJ x).property =
      fracPow ha k j h x x.property
    exact const_ext (by ring)

omit [GradedAlgebra ℬ] [Algebra Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))] in
include hφ in
/-- The numerators of `mulPow` are multiplied by `(f a)ᴺ` in `B`. -/
private theorem coe_liftBaseChange_mulPow (N j J : ℕ) (hJ : N * d + j = J)
    (t : S ⊗[R] 𝒜 j) :
    (((φ J).liftBaseChange S ((mulPow ha N j J hJ).baseChange S t) : ℬ J) : B) =
      f a ^ N * (((φ j).liftBaseChange S t : ℬ j) : B) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, Submodule.coe_add, ht, ht', mul_add]
  | tmul s x =>
    simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, Submodule.coe_smul, hφ,
      mul_smul_comm]
    -- The graded product `gMulLHom` computes the product `aᴺ x` of representatives in `A`.
    rw [show ((mulPow ha N j J hJ x : 𝒜 J) : A) = a ^ N * x from rfl, map_mul, map_pow]

omit [Algebra Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))] in
include hφ in
/-- The function `(∑ s • f y) / (f a)ˡ` on `D₊(f a)` is `∑ s • (y / aˡ)`. -/
private theorem awayToSection_mk_liftBaseChange (l : ℕ) (s : S) (y : 𝒜 (l * d)) :
    awayToSection ℬ (f a) (Away.mk ℬ (Graded.map_mem f ha) l _
        ((φ (l * d)).liftBaseChange S (s ⊗ₜ y)).property) =
      coeff ℬ (f a) s * (map f hf).appLE _ _ (map_preimage_basicOpen f hf a).ge
        (awayToSection 𝒜 a (Away.mk 𝒜 ha l y y.property)) := by
  rw [← CommRingCat.comp_apply, awayToSection_comp_appLE _ _ ha, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, Away.map_mk, RingHom.comp_apply, ← map_mul]
  refine congrArg _ (HomogeneousLocalization.val_injective _ ?_)
  simp only [← Algebra.smul_def, HomogeneousLocalization.val_smul, Away.val_mk,
    Localization.smul_mk, LinearMap.liftBaseChange_tmul, Submodule.coe_smul, hφ]

include halg in
/-- A product `(∑ s • f y) / (f a)ˡ ⊗ x / aᵏ` is `∑ s ⊗ y x / aˡ⁺ᵏ`. -/
private theorem awayToSection_mk_tmul_eq_theta (l k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n)
    (hJ : ((l * d + j : ℕ) : ℤ) = ((l + k) * d : ℕ) + n) (x : A) (hx : x ∈ 𝒜 j)
    (u : S ⊗[R] 𝒜 (l * d)) :
    awayToSection ℬ (f a) (Away.mk ℬ (Graded.map_mem f ha) l _
        ((φ (l * d)).liftBaseChange S u).property) ⊗ₜ[Γ(Proj 𝒜, basicOpen 𝒜 a)]
        fracPow ha k j h x hx =
      theta f hf φ hφ ha n halg (l + k) (l * d + j) hJ
        (((DirectSum.gMulLHom R (fun i ↦ 𝒜 i)).flip ⟨x, hx⟩).baseChange S u) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' =>
    have e : Away.mk ℬ (Graded.map_mem f ha) l _ ((φ (l * d)).liftBaseChange S (u + u')).property =
        Away.mk ℬ (Graded.map_mem f ha) l _ ((φ (l * d)).liftBaseChange S u).property +
        Away.mk ℬ (Graded.map_mem f ha) l _ ((φ (l * d)).liftBaseChange S u').property := by
      have := map_add (Away.mkLinearMap (Graded.map_mem f ha) l)
        ((φ (l * d)).liftBaseChange S u) ((φ (l * d)).liftBaseChange S u')
      simp only [Away.mkLinearMap_apply] at this
      simpa only [map_add] using this
    rw [e, map_add, TensorProduct.add_tmul, hu, hu', map_add, map_add]
  | tmul s y =>
    rw [awayToSection_mk_liftBaseChange f hf φ hφ ha l s y, LinearMap.baseChange_tmul,
      theta_tmul, mul_comm, ← halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
    congr 1
    exact awayToSection_mk_smul_fracPow ha l k j h hJ y x y.property hx

include hd in
/-- Every element of `Γ(D₊(f a), 𝒪) ⊗ Γ(D₊(a), 𝒪(n))` is of the form `∑ s ⊗ r / aᵏ`. -/
private theorem exists_eq_theta
    (hsurj : ∀ j, Function.Surjective ((φ j).liftBaseChange S))
    (z : Γ(Proj ℬ, basicOpen ℬ (f a)) ⊗[Γ(Proj 𝒜, basicOpen 𝒜 a)]
      Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a)) :
    ∃ (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (t : S ⊗[R] 𝒜 j),
      z = theta f hf φ hφ ha n halg k j h t := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    obtain ⟨k, j, h, t, rfl⟩ := hz
    obtain ⟨k', j', h', t', rfl⟩ := hz'
    have hJ : k * d + j' = k' * d + j := by zify; push_cast at h h'; linarith
    have hJK : ((k' * d + j : ℕ) : ℤ) = ((k + k') * d : ℕ) + n := by push_cast at h ⊢; linarith
    refine ⟨k + k', k' * d + j, hJK, (mulPow ha k' j _ rfl).baseChange S t +
      (mulPow ha k j' _ hJ).baseChange S t', ?_⟩
    rw [map_add, theta_mulPow f hf φ hφ ha n halg k j k' _ _ h rfl rfl hJK,
      theta_mulPow f hf φ hφ ha n halg k' j' k _ _ h' hJ (Nat.add_comm _ _) hJK]
  | tmul c m =>
    obtain ⟨k, j, h, x, hx, rfl⟩ := exists_eq_const_basicOpen ha hd m
    obtain ⟨c, rfl⟩ := (basicOpenIsoAway ℬ (f a) (Graded.map_mem f ha)
      hd).commRingCatIsoToRingEquiv.surjective c
    obtain ⟨l, y, hy, rfl⟩ := Away.mk_surjective ℬ (Graded.map_mem f ha) c
    obtain ⟨u, hu⟩ := hsurj (l * d) ⟨y, hy⟩
    obtain rfl : ((φ (l * d)).liftBaseChange S u : B) = y := congrArg Subtype.val hu
    have hJ : ((l * d + j : ℕ) : ℤ) = ((l + k) * d : ℕ) + n := by push_cast at h ⊢; linarith
    refine ⟨l + k, l * d + j, hJ,
      ((DirectSum.gMulLHom R (fun i ↦ 𝒜 i)).flip ⟨x, hx⟩).baseChange S u, ?_⟩
    exact awayToSection_mk_tmul_eq_theta f hf φ hφ ha n halg l k j h hJ x hx u

variable [Module Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(twistingSheaf ℬ n, basicOpen ℬ (f a))]
  [IsScalarTower Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))
    Γ(twistingSheaf ℬ n, basicOpen ℬ (f a))]
  (ψ : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) →ₗ[Γ(Proj 𝒜, basicOpen 𝒜 a)]
    Γ(twistingSheaf ℬ n, basicOpen ℬ (f a)))
  (hψ : ∀ s, ψ s = comap f hf (fun _ hy ↦ (map_preimage_basicOpen f hf a).ge hy) s)

include hψ in
/-- The base change of `ψ` sends `∑ s ⊗ r / aᵏ` to the fraction `(∑ s • f r) / (f a)ᵏ`. -/
private theorem liftBaseChange_theta (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n)
    (t : S ⊗[R] 𝒜 j) :
    ψ.liftBaseChange _ (theta f hf φ hφ ha n halg k j h t) =
      fracPow (Graded.map_mem f ha) k j h _ ((φ j).liftBaseChange S t).property := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]; exact const_add ..
  | tmul s x =>
    rw [theta_tmul, LinearMap.liftBaseChange_tmul, hψ]
    refine (congrArg (coeff ℬ (f a) s • ·) (comap_const f hf _ h _ _ x.property
      (by simpa [mul_comm] using SetLike.pow_mem_graded k ha)
      fun y (hy : y ∈ basicOpen 𝒜 a) hak ↦ hy (y.isPrime.mem_of_pow_mem k hak))).trans ?_
    -- The coefficient `s` is the function `s / (f a)⁰` on `D₊(f a)`.
    have hs : algebraMap S B s ∈ ℬ (0 * d) := by simpa using SetLike.algebraMap_mem_graded ℬ s
    have e : algebraMap S (Away ℬ (f a)) s = Away.mk ℬ (Graded.map_mem f ha) 0 _ hs :=
      HomogeneousLocalization.val_injective _ (by
        rw [HomogeneousLocalization.val_algebraMap, Away.val_mk,
          IsScalarTower.algebraMap_apply S B, ← Localization.mk_one_eq_algebraMap]
        exact congrArg _ (Subtype.ext (pow_zero _).symm))
    rw [RingHom.comp_apply, e]
    refine (congrArg (_ • ·) (const_ext (by rw [map_pow]) : _ = fracPow (Graded.map_mem f ha) k j h
      (f x) (Graded.map_mem f x.property))).trans <|
        (awayToSection_mk_smul_fracPow _ 0 k j h (by simpa using h) ..).trans ?_
    exact const_ext (by simp [hφ, Algebra.smul_def])

include hφ ha halg hψ hd in
/-- **Pulling back sections of `𝒪(n)` over a standard open is a base change.** Let `f : 𝒜 →+*ᵍ ℬ`
be a graded ring homomorphism over `R → S` which exhibits each `ℬⱼ` as the base change
`S ⊗[R] 𝒜ⱼ` (through the components `φ j` of `f`), and let `a ∈ 𝒜_d`, `d > 0`. Then the pullback
of sections `Γ(D₊(a), 𝒪_{Proj 𝒜}(n)) → Γ(D₊(f a), 𝒪_{Proj ℬ}(n))` along `Proj.map f`, given as
`ψ`, exhibits its target as the base change along `Γ(D₊(a), 𝒪) → Γ(D₊(f a), 𝒪)`. -/
theorem isBaseChange_comap_basicOpen (hbc : ∀ j, IsBaseChange S (φ j)) :
    IsBaseChange Γ(Proj ℬ, basicOpen ℬ (f a)) ψ := by
  rw [IsBaseChange.iff_liftBaseChange_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun m' ↦ ?_⟩
  · obtain ⟨k, j, h, t, rfl⟩ := exists_eq_theta f hf φ hφ ha hd n halg
      (fun j ↦ (hbc j).liftBaseChange_bijective.2) z
    rw [liftBaseChange_theta f hf φ hφ ha n halg ψ hψ] at hz
    obtain ⟨N, hN⟩ := (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hd
      (Graded.map_mem f ha)) ..).1 hz
    have ht : (mulPow ha N j _ rfl).baseChange S t = 0 := by
      refine (hbc _).liftBaseChange_injective (Subtype.ext ?_)
      rw [coe_liftBaseChange_mulPow f φ hφ ha, map_zero, Submodule.coe_zero]
      simpa only [map_pow] using hN
    have hJ : ((N * d + j : ℕ) : ℤ) = ((k + N) * d : ℕ) + n := by push_cast at h ⊢; linarith
    rw [← theta_mulPow f hf φ hφ ha n halg k j N _ _ h rfl rfl hJ, ht, map_zero]
  · obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen (Graded.map_mem f ha) hd m'
    obtain ⟨t, ht⟩ := (hbc j).liftBaseChange_bijective.2 ⟨r, hr⟩
    refine ⟨theta f hf φ hφ ha n halg k j h t, ?_⟩
    rw [liftBaseChange_theta f hf φ hφ ha n halg ψ hψ]
    exact const_ext (by rw [ht])

end AlgebraicGeometry.Proj.twistingSheaf
