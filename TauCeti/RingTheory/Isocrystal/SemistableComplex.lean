/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# The semistable complex of a Frobenius–monodromy datum

Let `K` be a field, `p : K`, `r : ℤ`, let `D` and `E` be `K`-vector spaces, and let
`φ N : D →ₗ[K] D` and `ι : D →ₗ[K] E` be linear maps satisfying the Frobenius–monodromy relation
`N ∘ φ = p • φ ∘ N`. The *semistable complex* of this datum in weight `r` is the three-term complex
```
D ⟶ D × E × D ⟶ D,
x ↦ ((1 - φ / p ^ r) x, ι x, N x),
(a, b, c) ↦ N a - (1 - φ / p ^ (r - 1)) c.
```
It is the total fibre of the commutative square with top `(1 - φ / p ^ r, ι) : D → D × E`, sides
`N : D → D` and `(N, 0) : D × E → D`, and bottom `1 - φ / p ^ (r - 1) : D → D`; the square commutes
because `N` intertwines `1 - φ / p ^ r` with `1 - φ / p ^ (r - 1)`.

Nekovář and Nizioł identify the rational syntomic cohomology in weight `r` of a semistable
arithmetic pair over a `p`-adic field with the total fibre of this square, where `D` is rational
Hyodo–Kato cohomology with its Frobenius `φ` and monodromy `N`, `E` is the quotient `RΓ_dR / F^r` of
de Rham cohomology by the `r`-th Hodge step, and `ι` is the Hyodo–Kato map attached to a
uniformizer. When `D` and `E` are single vector spaces rather than complexes, that total fibre is
the three-term complex above. In this application `φ` is only semilinear over `K₀ = W(k)[1/p]`;
here `K` is any field over which `φ`, `N` and `ι` are all linear, such as `ℚ`.

The monodromy operator comes with two normalizations. Hyodo–Kato's operator `N_c` changes
uniformizers by `exp(log(u) N_c)`, while the normalized convention uses `N_b = -N_c / e`, where `e`
is the ramification index. Replacing `N` by `c • N` for a scalar `c` changes the semistable complex
along the chain map `(id, id × id × c, c)`, which is an isomorphism when `c ≠ 0`; the conversion
between the two conventions is the case `c = -1 / e`. This chain map fixes the Frobenius and de
Rham components.

## Main definitions

* `TauCeti.semistableComplexD₀`, `TauCeti.semistableComplexD₁`: the two differentials.
* `TauCeti.semistableComplex`: the complex `D ⟶ D × E × D ⟶ D` as a short complex of `K`-modules.
* `TauCeti.semistableComplexMap`: the morphism of semistable complexes induced by linear maps
  compatible with `φ`, `ι` and `N`.
* `TauCeti.semistableComplexRescale`: the chain map `(id, id × id × c, c)` from the complex of `N`
  to that of `c • N`, and `TauCeti.semistableComplexRescaleIso`, which upgrades it to an
  isomorphism when `c ≠ 0`.

## Main results

* `LinearMap.comp_one_sub_smul_eq_of_comp_eq_smul_comp`: the relation `N φ = p φ N` gives
  `N (1 - a φ) = (1 - a p φ) N` for every scalar `a`.
* `LinearMap.smul_comp_eq_smul_comp_of_comp_eq`: the relation `N φ = p φ N` is preserved by
  rescaling `N`.
* `TauCeti.semistableComplexD₁_comp_semistableComplexD₀`: the differentials compose to zero
  when `p ≠ 0` and `N φ = p φ N`, for every `r : ℤ`.
* `TauCeti.semistableComplexD₀_smul`, `TauCeti.semistableComplexD₁_smul_comp`: the two squares of
  the rescaling chain map. They hold for every scalar `c`, including `c = 0`, and need no relation
  between `φ` and `N`.

## References

* J. Nekovář and W. Nizioł, *Syntomic cohomology and p-adic regulators for varieties over p-adic
  fields*, Algebra & Number Theory 10 (2016), §3.2 and Proposition 3.8.
* O. Hyodo and K. Kato, *Semi-stable reduction and crystalline cohomology with logarithmic poles*,
  Astérisque 223 (1994), Theorem 5.1.
-/

public section

open CategoryTheory

universe u v

namespace LinearMap

variable {K D : Type*} [CommSemiring K]

/-- The Frobenius–monodromy relation `N φ = p φ N` makes `N` intertwine `1 - a φ` with
`1 - a p φ`, for every scalar `a`. -/
theorem comp_one_sub_smul_eq_of_comp_eq_smul_comp [AddCommGroup D] [Module K D] {p : K}
    {φ N : D →ₗ[K] D} (h : N ∘ₗ φ = p • (φ ∘ₗ N)) (a : K) :
    N ∘ₗ (1 - a • φ) = (1 - (a * p) • φ) ∘ₗ N := by
  ext x
  simpa [mul_smul] using congrArg (a • ·) (LinearMap.congr_fun h x)

/-- The Frobenius–monodromy relation `N φ = p φ N` is preserved by rescaling the monodromy. -/
theorem smul_comp_eq_smul_comp_of_comp_eq [AddCommMonoid D] [Module K D] {p : K}
    {φ N : D →ₗ[K] D} (h : N ∘ₗ φ = p • (φ ∘ₗ N)) (c : K) :
    (c • N) ∘ₗ φ = p • (φ ∘ₗ (c • N)) := by
  rw [LinearMap.smul_comp, h, LinearMap.comp_smul, smul_comm]

end LinearMap

namespace TauCeti

section Linear

variable {K D E : Type*} [Field K] [AddCommGroup D] [Module K D] [AddCommGroup E] [Module K E]

variable (p : K) (r : ℤ) (φ : D →ₗ[K] D) (ι : D →ₗ[K] E) (N : D →ₗ[K] D)

/-- The first differential `x ↦ ((1 - φ / p ^ r) x, ι x, N x)` of the semistable complex. -/
def semistableComplexD₀ : D →ₗ[K] D × E × D :=
  (1 - p ^ (-r) • φ).prod (ι.prod N)

/-- The second differential `(a, b, c) ↦ N a - (1 - φ / p ^ (r - 1)) c` of the semistable
complex. -/
def semistableComplexD₁ : D × E × D →ₗ[K] D :=
  N ∘ₗ LinearMap.fst K D (E × D) -
    (1 - p ^ (1 - r) • φ) ∘ₗ LinearMap.snd K E D ∘ₗ LinearMap.snd K D (E × D)

@[simp]
lemma semistableComplexD₀_apply (x : D) :
    semistableComplexD₀ p r φ ι N x = (x - p ^ (-r) • φ x, ι x, N x) := (rfl)

@[simp]
lemma semistableComplexD₁_apply (x : D × E × D) :
    semistableComplexD₁ p r φ N x = N x.1 - (x.2.2 - p ^ (1 - r) • φ x.2.2) := (rfl)

/-- The two differentials of the semistable complex compose to zero, for every weight `r : ℤ`. -/
theorem semistableComplexD₁_comp_semistableComplexD₀ (hp : p ≠ 0)
    (h : N ∘ₗ φ = p • (φ ∘ₗ N)) :
    semistableComplexD₁ p r φ N ∘ₗ semistableComplexD₀ p r φ ι N = 0 := by
  have hpow : p ^ (-r) * p = p ^ (1 - r) := by
    rw [← zpow_add_one₀ hp, neg_add_eq_sub]
  ext x
  have hx :=
    LinearMap.congr_fun (LinearMap.comp_one_sub_smul_eq_of_comp_eq_smul_comp h (p ^ (-r))) x
  simp only [hpow, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    one_apply_eq_self] at hx
  simp only [LinearMap.comp_apply, semistableComplexD₀_apply, semistableComplexD₁_apply,
    LinearMap.zero_apply, hx, sub_self]

/-- Rescaling the monodromy by `c` multiplies the third component of the first differential by `c`.
This holds for every scalar `c`, including `c = 0`. -/
theorem semistableComplexD₀_smul (c : K) :
    semistableComplexD₀ p r φ ι (c • N) =
      (LinearMap.id.prodMap (LinearMap.id.prodMap (c • LinearMap.id))) ∘ₗ
        semistableComplexD₀ p r φ ι N := by
  ext x <;> simp

/-- Rescaling the monodromy by `c`, and the third component of the middle term by `c`, multiplies
the second differential by `c`. This holds for every scalar `c`, including `c = 0`. -/
theorem semistableComplexD₁_smul_comp (c : K) :
    semistableComplexD₁ p r φ (c • N) ∘ₗ
        (LinearMap.id.prodMap (LinearMap.id.prodMap (c • LinearMap.id))) =
      c • semistableComplexD₁ p r φ (E := E) N := by
  ext x <;> simp [smul_sub, smul_comm c]

variable {D' E' : Type*} [AddCommGroup D'] [Module K D'] [AddCommGroup E'] [Module K E']
  {φ ι N} {φ' : D' →ₗ[K] D'} {ι' : D' →ₗ[K] E'} {N' : D' →ₗ[K] D'}

/-- Linear maps compatible with `φ`, `ι` and `N` commute with the first differentials. -/
theorem prodMap_comp_semistableComplexD₀ {f : D →ₗ[K] D'} {g : E →ₗ[K] E'}
    (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hι : g ∘ₗ ι = ι' ∘ₗ f) (hN : f ∘ₗ N = N' ∘ₗ f) :
    f.prodMap (g.prodMap f) ∘ₗ semistableComplexD₀ p r φ ι N =
      semistableComplexD₀ p r φ' ι' N' ∘ₗ f := by
  have hφ' (x : D) : f (φ x) = φ' (f x) := LinearMap.congr_fun hφ x
  have hι' (x : D) : g (ι x) = ι' (f x) := LinearMap.congr_fun hι x
  have hN' (x : D) : f (N x) = N' (f x) := LinearMap.congr_fun hN x
  ext x <;> simp [hφ', hι', hN']

/-- Linear maps compatible with `φ` and `N` commute with the second differentials. -/
theorem comp_semistableComplexD₁ {f : D →ₗ[K] D'} (g : E →ₗ[K] E')
    (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hN : f ∘ₗ N = N' ∘ₗ f) :
    f ∘ₗ semistableComplexD₁ p r φ N =
      semistableComplexD₁ p r φ' N' ∘ₗ f.prodMap (g.prodMap f) := by
  have hφ' (x : D) : f (φ x) = φ' (f x) := LinearMap.congr_fun hφ x
  have hN' (x : D) : f (N x) = N' (f x) := LinearMap.congr_fun hN x
  ext x <;> simp [hφ', hN']

end Linear

section ShortComplex

variable {K : Type u} {D E : Type v} [Field K] [AddCommGroup D] [Module K D] [AddCommGroup E]
  [Module K E] (p : K) (r : ℤ) (φ : D →ₗ[K] D) (ι : D →ₗ[K] E) (N : D →ₗ[K] D)

/-- The semistable complex `D ⟶ D × E × D ⟶ D` of a Frobenius–monodromy datum in weight `r`, with
differentials `semistableComplexD₀` and `semistableComplexD₁`. -/
@[expose, implicit_reducible, simps]
noncomputable def semistableComplex (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) :
    ShortComplex (ModuleCat.{v} K) where
  X₁ := ModuleCat.of K D
  X₂ := ModuleCat.of K (D × E × D)
  X₃ := ModuleCat.of K D
  f := ModuleCat.ofHom (semistableComplexD₀ p r φ ι N)
  g := ModuleCat.ofHom (semistableComplexD₁ p r φ N)
  zero := ModuleCat.hom_ext (semistableComplexD₁_comp_semistableComplexD₀ p r φ ι N hp h)

variable {p r φ ι N}

/-- The chain map `(id, id × id × c, c)` from the semistable complex of `N` to that of `c • N`. It
is the identity on the Frobenius and de Rham components, and is defined for every scalar `c`. -/
@[expose, simps]
noncomputable def semistableComplexRescale (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) (c : K) :
    semistableComplex p r φ ι N hp h ⟶
      semistableComplex p r φ ι (c • N) hp (LinearMap.smul_comp_eq_smul_comp_of_comp_eq h c) where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom (LinearMap.id.prodMap (LinearMap.id.prodMap (c • LinearMap.id)))
  τ₃ := ModuleCat.ofHom (c • LinearMap.id)
  comm₁₂ := by
    simp only [semistableComplex_f, Category.id_comp, ← ModuleCat.ofHom_comp]
    rw [semistableComplexD₀_smul]
  comm₂₃ := by
    simp only [semistableComplex_g, ← ModuleCat.ofHom_comp]
    rw [semistableComplexD₁_smul_comp, LinearMap.smul_comp, LinearMap.id_comp]

/-- For `c ≠ 0`, rescaling the monodromy by `c` gives an isomorphism of semistable complexes,
with hom `semistableComplexRescale`. -/
noncomputable def semistableComplexRescaleIso (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) {c : K}
    (hc : c ≠ 0) :
    semistableComplex p r φ ι N hp h ≅
      semistableComplex p r φ ι (c • N) hp (LinearMap.smul_comp_eq_smul_comp_of_comp_eq h c) :=
  ShortComplex.isoMk (Iso.refl _)
    ((LinearEquiv.refl K D).prodCongr
      ((LinearEquiv.refl K E).prodCongr (LinearEquiv.smulOfNeZero K D c hc))).toModuleIso
    (LinearEquiv.smulOfNeZero K D c hc).toModuleIso
    (semistableComplexRescale hp h c).comm₁₂ (semistableComplexRescale hp h c).comm₂₃

@[simp]
lemma semistableComplexRescaleIso_hom (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) {c : K}
    (hc : c ≠ 0) :
    (semistableComplexRescaleIso (r := r) (ι := ι) hp h hc).hom =
      semistableComplexRescale hp h c := by
  ext x : 3 <;> simp [semistableComplexRescaleIso, ShortComplex.isoMk]

@[simp]
lemma semistableComplexRescaleIso_inv_τ₁ (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) {c : K}
    (hc : c ≠ 0) : (semistableComplexRescaleIso (r := r) (ι := ι) hp h hc).inv.τ₁ = 𝟙 _ :=
  -- The first component of `semistableComplexRescaleIso` is `Iso.refl _`, and the first objects
  -- of both complexes are by definition `ModuleCat.of K D`.
  (rfl)

@[simp]
lemma semistableComplexRescaleIso_inv_τ₂ (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) {c : K}
    (hc : c ≠ 0) :
    (semistableComplexRescaleIso (r := r) (ι := ι) hp h hc).inv.τ₂ =
      ModuleCat.ofHom (LinearMap.id.prodMap (LinearMap.id.prodMap (c⁻¹ • LinearMap.id))) := by
  ext x : 2
  simp [semistableComplexRescaleIso, ShortComplex.isoMk, Units.smul_def]

@[simp]
lemma semistableComplexRescaleIso_inv_τ₃ (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) {c : K}
    (hc : c ≠ 0) :
    (semistableComplexRescaleIso (r := r) (ι := ι) hp h hc).inv.τ₃ =
      ModuleCat.ofHom (c⁻¹ • LinearMap.id) := by
  ext x : 2
  simp [semistableComplexRescaleIso, ShortComplex.isoMk, Units.smul_def]

variable {D' E' D'' E'' : Type v} [AddCommGroup D'] [Module K D'] [AddCommGroup E'] [Module K E']
  [AddCommGroup D''] [Module K D''] [AddCommGroup E''] [Module K E'']
  {φ' : D' →ₗ[K] D'} {ι' : D' →ₗ[K] E'} {N' : D' →ₗ[K] D'}
  {φ'' : D'' →ₗ[K] D''} {ι'' : D'' →ₗ[K] E''} {N'' : D'' →ₗ[K] D''}

/-- Linear maps `f : D → D'` and `g : E → E'` compatible with `φ`, `ι` and `N` induce the morphism
`(f, f × g × f, f)` of semistable complexes. -/
@[expose, simps]
noncomputable def semistableComplexMap (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N))
    (h' : N' ∘ₗ φ' = p • (φ' ∘ₗ N')) (f : D →ₗ[K] D') (g : E →ₗ[K] E')
    (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hι : g ∘ₗ ι = ι' ∘ₗ f) (hN : f ∘ₗ N = N' ∘ₗ f) :
    semistableComplex p r φ ι N hp h ⟶ semistableComplex p r φ' ι' N' hp h' where
  τ₁ := ModuleCat.ofHom f
  τ₂ := ModuleCat.ofHom (f.prodMap (g.prodMap f))
  τ₃ := ModuleCat.ofHom f
  comm₁₂ := by
    simp only [semistableComplex_f, ← ModuleCat.ofHom_comp]
    rw [prodMap_comp_semistableComplexD₀ p r hφ hι hN]
  comm₂₃ := by
    simp only [semistableComplex_g, ← ModuleCat.ofHom_comp]
    rw [comp_semistableComplexD₁ p r g hφ hN]

@[simp]
theorem semistableComplexMap_id (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N)) :
    semistableComplexMap (r := r) (ι := ι) hp h h LinearMap.id LinearMap.id
      (by simp) (by simp) (by simp) = 𝟙 _ := by
  -- `simp` leaves `𝟙 (ModuleCat.of K D) = 𝟙 (semistableComplex _ _ _ _ _ hp h).X₁`, which holds
  -- because the objects of `semistableComplex` are by definition the coordinate modules.
  ext : 1 <;> simp <;> rfl

@[reassoc (attr := simp)]
theorem semistableComplexMap_comp (hp : p ≠ 0) (h : N ∘ₗ φ = p • (φ ∘ₗ N))
    (h' : N' ∘ₗ φ' = p • (φ' ∘ₗ N')) (h'' : N'' ∘ₗ φ'' = p • (φ'' ∘ₗ N''))
    {f : D →ₗ[K] D'} {g : E →ₗ[K] E'} {f' : D' →ₗ[K] D''} {g' : E' →ₗ[K] E''}
    (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hι : g ∘ₗ ι = ι' ∘ₗ f) (hN : f ∘ₗ N = N' ∘ₗ f)
    (hφ' : f' ∘ₗ φ' = φ'' ∘ₗ f') (hι' : g' ∘ₗ ι' = ι'' ∘ₗ f') (hN' : f' ∘ₗ N' = N'' ∘ₗ f') :
    semistableComplexMap (r := r) hp h h' f g hφ hι hN ≫
        semistableComplexMap hp h' h'' f' g' hφ' hι' hN' =
      semistableComplexMap hp h h'' (f' ∘ₗ f) (g' ∘ₗ g)
        (by rw [LinearMap.comp_assoc, hφ, ← LinearMap.comp_assoc, hφ', LinearMap.comp_assoc])
        (by rw [LinearMap.comp_assoc, hι, ← LinearMap.comp_assoc, hι', LinearMap.comp_assoc])
        (by rw [LinearMap.comp_assoc, hN, ← LinearMap.comp_assoc, hN', LinearMap.comp_assoc]) := by
  ext x : 3 <;> simp

/-- Rescaling the monodromy is natural in the Frobenius–monodromy datum. -/
@[reassoc]
theorem semistableComplexMap_comp_semistableComplexRescale (hp : p ≠ 0)
    (h : N ∘ₗ φ = p • (φ ∘ₗ N)) (h' : N' ∘ₗ φ' = p • (φ' ∘ₗ N')) {f : D →ₗ[K] D'}
    {g : E →ₗ[K] E'} (hφ : f ∘ₗ φ = φ' ∘ₗ f) (hι : g ∘ₗ ι = ι' ∘ₗ f) (hN : f ∘ₗ N = N' ∘ₗ f)
    (c : K) :
    semistableComplexMap (r := r) hp h h' f g hφ hι hN ≫ semistableComplexRescale hp h' c =
      semistableComplexRescale hp h c ≫
        semistableComplexMap hp (LinearMap.smul_comp_eq_smul_comp_of_comp_eq h c)
          (LinearMap.smul_comp_eq_smul_comp_of_comp_eq h' c) f g hφ hι
          (by rw [LinearMap.comp_smul, hN, LinearMap.smul_comp]) := by
  ext x : 3 <;> simp

end ShortComplex

end TauCeti
