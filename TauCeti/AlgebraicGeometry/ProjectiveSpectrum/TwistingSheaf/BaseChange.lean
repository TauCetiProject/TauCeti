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
* The proof is adapted from the [relative Proj base-change formalization](https://github.com/roed-math/TauCeti-w2-fresh/blob/8bf602f6c2bed52e7e390df1ba2c2de30f8a6dfb/TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/BaseChange.lean).
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Proj.twistingSheaf

universe u

section

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ} {a : A} {d : ℕ}

/-- The section `r / aᵏ` of `𝒪(n)` over `D₊(a)`, for `r` homogeneous of degree `k d + n`. -/
private abbrev fracPow (ha : a ∈ 𝒜 d) (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : A)
    (hr : r ∈ 𝒜 j) : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) :=
  const h r (a ^ k) hr (by simpa [mul_comm] using SetLike.pow_mem_graded k ha) (basicOpen 𝒜 a)
    fun x hx hak ↦ hx (x.isPrime.mem_of_pow_mem k hak)

/-- The fractions `r / aᵏ`, `r ∈ 𝒜 j`, as an additive map. -/
private def fracPowHom (ha : a ∈ 𝒜 d) (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) :
    𝒜 j →+ Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) where
  toFun r := fracPow ha k j h r r.2
  map_zero' := const_zero ..
  map_add' _ _ := (const_add ..).symm

end

variable {R S A B : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  (φ : ∀ j, 𝒜 j →ₗ[R] ℬ j) (hφ : ∀ j x, (φ j x : B) = f x)
  {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)

/-- The image of `s : S` as a function on `D₊(f a)`. -/
private abbrev coeff (V : (Proj ℬ).Opens) : S →+ Γ(Proj ℬ, V) :=
  (sectionsLinearEquivTwistingSheafZero ℬ V).symm.toAddMonoidHom.comp
    ((toTwistingSheaf ℬ (j := 0) (by simp) V).comp (algebraMap S (ℬ 0)).toAddMonoidHom)

private theorem val_coeff_apply (V : (Proj ℬ).Opens) (s : S) (y : V) :
    ((coeff V s).1 y).val = Localization.mk (algebraMap S B s) 1 :=
  (sectionsLinearEquivTwistingSheafZero_symm_apply_val ..).trans
    (congrArg (Localization.mk · 1) (SetLike.GradeZero.coe_algebraMap ℬ s))

/-- The function `r / aˡ` on `D₊(a)`, for `r` homogeneous of degree `l d`. -/
private abbrev frac0 (l : ℕ) (r : A) (hr : r ∈ 𝒜 (l * d)) : Γ(Proj 𝒜, basicOpen 𝒜 a) :=
  (sectionsLinearEquivTwistingSheafZero 𝒜 _).symm (fracPow (n := 0) ha l (l * d) (by simp) r hr)

private theorem val_frac0_apply (l : ℕ) (r : A) (hr : r ∈ 𝒜 (l * d)) (y : basicOpen 𝒜 a) :
    ((frac0 ha l r hr).1 y).val =
      Localization.mk r ⟨a ^ l, fun h ↦ y.2 (y.1.isPrime.mem_of_pow_mem l h)⟩ :=
  sectionsLinearEquivTwistingSheafZero_symm_apply_val ..

omit [GradedAlgebra ℬ] in
include hφ in
private theorem map_algebraMap (r : R) : f (algebraMap R A r) = algebraMap R B r := by
  have h1 : (1 : A) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
  have e : (⟨algebraMap R A r, SetLike.algebraMap_mem_graded 𝒜 r⟩ : 𝒜 0) = r • ⟨1, h1⟩ :=
    Subtype.ext (Algebra.algebraMap_eq_smul_one r)
  rw [← hφ 0 ⟨_, SetLike.algebraMap_mem_graded 𝒜 r⟩, e, map_smul, Submodule.coe_smul_of_tower,
    hφ, map_one, Algebra.algebraMap_eq_smul_one]

/-- The two functions on `D₊(f a)` agree as soon as their values agree in the localizations. -/
private theorem sections_ext {V : (Proj ℬ).Opens} {c c' : Γ(Proj ℬ, V)}
    (h : ∀ y : V, (c.1 y).val = (c'.1 y).val) : c = c' :=
  (sectionsLinearEquivTwistingSheafZero ℬ V).injective (ext h)

variable [Algebra Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))]
  (halg : ∀ c, algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a)) c =
    (map f hf).appLE _ _ (map_preimage_basicOpen f hf a).ge c)

include halg hφ in
/-- The scalar `r : R` acts on `D₊(f a)` through either coefficient ring. -/
private theorem coeff_smul (r : R) (s : S) :
    coeff (basicOpen ℬ (f a)) (r • s) =
      algebraMap Γ(Proj 𝒜, basicOpen 𝒜 a) _
        (frac0 ha 0 (algebraMap R A r) (by simpa using SetLike.algebraMap_mem_graded 𝒜 r)) *
      coeff _ s := by
  refine sections_ext fun y ↦ ?_
  rw [halg]
  -- Expose pointwise multiplication of structure-sheaf sections to use `val_mul`.
  change _ = (((map f hf).appLE _ _ _ _).1 y * (coeff _ s).1 y).val
  refine (val_coeff_apply _ _ y).trans (Eq.trans ?_ (HomogeneousLocalization.val_mul _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (val_map_appLE_apply f hf
    (fun _ hy ↦ (map_preimage_basicOpen f hf a).ge hy) _ y).symm (val_coeff_apply _ _ y).symm)
  have key := val_frac0_apply ha 0 (algebraMap R A r)
    (by simpa using SetLike.algebraMap_mem_graded 𝒜 r)
    ⟨ProjectiveSpectrum.comap f hf y.1, (map_preimage_basicOpen f hf a).ge y.2⟩
  erw [key, ProjectiveSpectrum.TwistingSheaf.localizationsMap_mk]
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [map_algebraMap f φ hφ, pow_zero, map_one, one_mul, mul_one, Submonoid.coe_one,
    Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

include halg hφ in
/-- Scalars of `R` move across the tensor product of the fractions `s ⊗ r / aᵏ`. -/
private theorem coeff_smul_tmul (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : R) (s : S)
    (x : 𝒜 j) :
    coeff (basicOpen ℬ (f a)) (r • s) ⊗ₜ[Γ(Proj 𝒜, basicOpen 𝒜 a)] fracPowHom ha k j h x =
      coeff (basicOpen ℬ (f a)) s ⊗ₜ fracPowHom ha k j h (r • x) := by
  rw [coeff_smul f hf φ hφ ha halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
  congr 1
  refine ext fun y ↦ ?_
  refine (smul_apply _ _ y).trans ?_
  erw [val_frac0_apply]
  -- The remaining values are the constant fractions defining `fracPowHom`.
  change Localization.mk _ _ * Localization.mk (x : A) _ = Localization.mk ((r • x : 𝒜 j) : A) _
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [Algebra.smul_def, mul_comm]⟩

/-- The elements `∑ s ⊗ r / aᵏ` of `Γ(D₊(f a), 𝒪) ⊗ Γ(D₊(a), 𝒪(n))`, for `∑ s ⊗ r ∈ S ⊗[R] 𝒜ⱼ`. -/
private def theta (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) :
    S ⊗[R] 𝒜 j →+ Γ(Proj ℬ, basicOpen ℬ (f a)) ⊗[Γ(Proj 𝒜, basicOpen 𝒜 a)]
      Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 a) :=
  TensorProduct.liftAddHom
    { toFun s := (TensorProduct.mk _ _ _ (coeff _ s)).toAddMonoidHom.comp (fracPowHom ha k j h)
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
    fun r s x ↦ coeff_smul_tmul f hf φ hφ ha n halg k j h r s x

private theorem theta_tmul (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (s : S) (x : 𝒜 j) :
    theta f hf φ hφ ha n halg k j h (s ⊗ₜ x) = coeff _ s ⊗ₜ fracPowHom ha k j h x :=
  TensorProduct.liftAddHom_tmul ..

/-- Multiplication by `aᴺ`, from `𝒜ⱼ` to `𝒜_J`, `J = N d + j`. -/
private def mulPow (N j J : ℕ) (hJ : N * d + j = J) : 𝒜 j →ₗ[R] 𝒜 J :=
  ((LinearMap.mulLeft R (a ^ N)).domRestrict (𝒜 j)).codRestrict (𝒜 J) fun x ↦
    hJ ▸ SetLike.mul_mem_graded
      (by simpa [mul_comm] using SetLike.pow_mem_graded N ha) x.2

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
    -- Unfold only the additive map on fractions, keeping the section constructions opaque.
    change fracPow ha (k + N) J h' (a ^ N * x) (mulPow ha N j J hJ x).2 = fracPow ha k j h x x.2
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
    simp [mulPow, hφ]

omit [Algebra Γ(Proj 𝒜, basicOpen 𝒜 a) Γ(Proj ℬ, basicOpen ℬ (f a))] in
include hφ in
/-- The fraction `(∑ s • f y) / (f a)ˡ` of degree zero is `∑ s • (y / aˡ)`. -/
private theorem symm_fracPow_liftBaseChange (l : ℕ) (s : S) (y : 𝒜 (l * d)) :
    (sectionsLinearEquivTwistingSheafZero ℬ (basicOpen ℬ (f a))).symm
        (fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
          ((φ (l * d)).liftBaseChange S (s ⊗ₜ y)).2) =
      coeff _ s * (map f hf).appLE _ _ (map_preimage_basicOpen f hf a).ge (frac0 ha l y y.2) := by
  refine sections_ext fun z ↦ ?_
  refine (sectionsLinearEquivTwistingSheafZero_symm_apply_val ..).trans ?_
  -- Expose pointwise multiplication of structure-sheaf sections to use `val_mul`.
  change _ = ((coeff _ s).1 z * ((map f hf).appLE _ _ _ _).1 z).val
  refine Eq.trans ?_ (HomogeneousLocalization.val_mul _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) (val_coeff_apply _ _ z).symm (val_map_appLE_apply f hf
    (fun _ hy ↦ (map_preimage_basicOpen f hf a).ge hy) _ z).symm)
  have key := val_frac0_apply ha l y y.2
    ⟨ProjectiveSpectrum.comap f hf z.1, (map_preimage_basicOpen f hf a).ge z.2⟩
  erw [key, ProjectiveSpectrum.TwistingSheaf.localizationsMap_mk]
  rw [Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
  simp only [LinearMap.liftBaseChange_tmul, Submodule.coe_smul, hφ, Algebra.smul_def,
    map_pow, Submonoid.coe_mul, Submonoid.coe_one]
  ring

/-- Multiplication by `x ∈ 𝒜ⱼ`, from `𝒜ᵢ` to `𝒜ᵢ₊ⱼ`. -/
private def mulRight (i j : ℕ) (x : 𝒜 j) : 𝒜 i →ₗ[R] 𝒜 (i + j) :=
  ((LinearMap.mulRight R (x : A)).domRestrict (𝒜 i)).codRestrict (𝒜 (i + j)) fun y ↦
    SetLike.mul_mem_graded y.2 x.2

include halg in
/-- A product `(∑ s • f y / (f a)ˡ) ⊗ x / aᵏ` is `∑ s ⊗ y x / aˡ⁺ᵏ`. -/
private theorem symm_fracPow_tmul_eq_theta (l k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n)
    (hJ : ((l * d + j : ℕ) : ℤ) = ((l + k) * d : ℕ) + n) (x : A) (hx : x ∈ 𝒜 j)
    (u : S ⊗[R] 𝒜 (l * d)) :
    (sectionsLinearEquivTwistingSheafZero ℬ (basicOpen ℬ (f a))).symm
        (fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
          ((φ (l * d)).liftBaseChange S u).2) ⊗ₜ[Γ(Proj 𝒜, basicOpen 𝒜 a)]
        fracPow ha k j h x hx =
      theta f hf φ hφ ha n halg (l + k) (l * d + j) hJ
        ((mulRight (l * d) j ⟨x, hx⟩).baseChange S u) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' =>
    have e : fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
        ((φ (l * d)).liftBaseChange S (u + u')).2 =
        fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
          ((φ (l * d)).liftBaseChange S u).2 +
        fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
          ((φ (l * d)).liftBaseChange S u').2 :=
      (const_ext (by simp only [map_add, Submodule.coe_add])).trans (const_add ..).symm
    rw [e, map_add, TensorProduct.add_tmul, hu, hu', map_add, map_add]
  | tmul s y =>
    rw [symm_fracPow_liftBaseChange f hf φ hφ ha l s y, LinearMap.baseChange_tmul, theta_tmul,
      mul_comm, ← halg, ← Algebra.smul_def, TensorProduct.smul_tmul]
    congr 1
    refine ext fun z ↦ (smul_apply _ _ z).trans ?_
    erw [val_frac0_apply]
    -- Evaluate the constant sections after the scalar action to compare fractions.
    change Localization.mk _ _ * Localization.mk x _ = Localization.mk (y * x : A) _
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [pow_add]⟩

include hd in
/-- Every element of `Γ(D₊(f a), 𝒪) ⊗ Γ(D₊(a), 𝒪(n))` is of the form `∑ s ⊗ r / aᵏ`. -/
private theorem exists_eq_theta (hbc : ∀ j, IsBaseChange S (φ j))
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
    obtain ⟨l, j₀, h₀, y, hy, hc⟩ := exists_eq_const_basicOpen (n := 0) (Graded.map_mem f ha) hd
      (sectionsLinearEquivTwistingSheafZero ℬ _ c)
    obtain rfl : j₀ = l * d := by omega
    obtain ⟨u, hu⟩ := (hbc (l * d)).liftBaseChange_bijective.2 ⟨y, hy⟩
    have hc' : c = (sectionsLinearEquivTwistingSheafZero ℬ _).symm
        (fracPow (n := 0) (Graded.map_mem f ha) l (l * d) (by simp) _
          ((φ (l * d)).liftBaseChange S u).2) := by
      rw [← (sectionsLinearEquivTwistingSheafZero ℬ _).symm_apply_apply c, hc]
      exact congrArg _ (const_ext (by rw [hu]))
    have hJ : ((l * d + j : ℕ) : ℤ) = ((l + k) * d : ℕ) + n := by push_cast at h ⊢; linarith
    refine ⟨l + k, l * d + j, hJ, (mulRight (l * d) j ⟨x, hx⟩).baseChange S u, ?_⟩
    rw [hc']
    exact symm_fracPow_tmul_eq_theta f hf φ hφ ha n halg l k j h hJ x hx u

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
      fracPow (Graded.map_mem f ha) k j h _ ((φ j).liftBaseChange S t).2 := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]; exact const_add ..
  | tmul s x =>
    rw [theta_tmul, LinearMap.liftBaseChange_tmul, hψ]
    refine ext fun y ↦ (smul_apply _ _ y).trans ?_
    erw [val_coeff_apply, comap_apply, ProjectiveSpectrum.TwistingSheaf.localizationsMap_mk]
    rw [Localization.mk_mul]
    refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, ?_⟩)
    simp only [LinearMap.liftBaseChange_tmul, Submodule.coe_smul, hφ, Algebra.smul_def,
      map_pow, Submonoid.coe_mul, Submonoid.coe_one]
    ring

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
  · obtain ⟨k, j, h, t, rfl⟩ := exists_eq_theta f hf φ hφ ha hd n halg hbc z
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
