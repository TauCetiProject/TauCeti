/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Cusp
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap
public import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
public import TauCeti.NumberTheory.ModularForms.QExpansion.FunctionField
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action

/-!
# The level-one modular function field is `ℚ(j)` over the rationals

Let `X(1)` be the compactified level-one modular curve, the compactified quotient of the upper
half-plane by `PSL(2, ℤ)`. The modular invariant `j` is a meromorphic function on `X(1)`
(`TauCeti.ModularGroup.jMeromorphicFunction`), and since `j : X(1) → ℙ¹(ℂ)` is a biholomorphism
(`TauCeti.ModularGroup.jBiholomorph`), pulling back the rational functions of the coordinate of the
Riemann sphere identifies the field of meromorphic functions on `X(1)` with `ℂ(j)`
(`TauCeti.ModularGroup.jRatFuncEquiv`). In particular `j` is transcendental over `ℂ`.

This file descends this description to the arithmetic function field. For a subfield `K` of `ℂ`,
`Subgroup.CompactifiedQuotient.coeffSubfield cuspDatumInfty K` consists of the meromorphic
functions whose Laurent expansion in `q = exp (2 π i τ)` has all its coefficients in `K`. The
expansion of `j` is `q⁻¹ + 744 + 196884 q + ⋯` with integer coefficients, so `K(j)` lies in this
subfield. Conversely, write a function `F` with coefficients in `K` as `P(j) / Q(j)` with
`P, Q ∈ ℂ[X]`. The identity `F Q(j) = P(j)` of Laurent series has all the expansions of `F` and
of the powers of `j` in `K⸨q⸩`, so applying a `K`-linear functional `ℂ → K` to all coefficients
turns it into a relation `F Q'(j) = P'(j)` with `P', Q' ∈ K[X]` and `Q' ≠ 0`
(`HahnSeries.exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom`). Hence

  `coeffSubfield cuspDatumInfty K = K(j)`

(`TauCeti.ModularGroup.coeffSubfield_cuspDatumInfty_eq_closure`). For `K = ℚ`, the prime subfield
`⊥` of `ℂ`, this is the identity `F₁ = ℚ(j)` for the field of level-one modular functions with
rational Fourier coefficients (`TauCeti.ModularGroup.coeffSubfield_cuspDatumInfty_bot`).

Finally, for a finite-index subgroup `H` of `SL(2, ℤ)`, a meromorphic function `F` on the
compactified quotient `X_H` is pulled back from `X(1)` exactly when its value at the orbit of `τ`
depends only on the `SL(2, ℤ)`-orbit of `τ`
(`TauCeti.ModularGroup.exists_compactifiedQuotientComap_eq_iff`). Composing the map `X_H → X(1)`
with `j` gives a finite holomorphic map `β : X_H → ℙ¹(ℂ)` whose fibres over the finite points are
these orbits, so `F` is constant along all but one fibre of `β`, and is therefore the pullback of
its trace along `β` divided by `deg β`
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_comap_eq_of_eventually_subsingleton_image`).

## Main definitions

* `TauCeti.ModularGroup.jMeromorphicFunction`: the modular invariant `j` as a meromorphic function
  on the compactified level-one modular curve.
* `TauCeti.ModularGroup.jRatFuncEquiv`: the isomorphism `ℂ(X) ≃ₐ[ℂ] M(X(1))`, `X ↦ j`.

## Main results

* `TauCeti.ModularGroup.transcendental_jMeromorphicFunction`: `j` is transcendental over `ℂ`.
* `TauCeti.ModularGroup.laurentQExpansion_jMeromorphicFunction`: the Laurent expansion of `j` at
  the cusp is the classical `q`-expansion of `j`.
* `TauCeti.ModularGroup.mem_coeffSubfield_cuspDatumInfty_iff`: a meromorphic function has
  coefficients in `K` exactly when it is `P(j) / Q(j)` with `P, Q ∈ K[X]`, `Q ≠ 0`.
* `TauCeti.ModularGroup.coeffSubfield_cuspDatumInfty_eq_closure`: the functions with coefficients
  in `K` form the field `K(j)`.
* `TauCeti.ModularGroup.coeffSubfield_cuspDatumInfty_bot`: `F₁ = ℚ(j)`.
* `TauCeti.ModularGroup.exists_compactifiedQuotientComap_eq_iff`: the meromorphic functions on
  `X_H` pulled back from `X(1)` are those invariant under `SL(2, ℤ)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.4, 6.1.
* Serge Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 6, §3.
-/

public noncomputable section

open Function MulAction OnePoint Polynomial UpperHalfPlane TauCeti.RiemannSurface
open _root_.Subgroup.CompactifiedQuotient
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open MeromorphicFunction

/-- The modular invariant takes the two different values `∞` and `1728` on `X(1)`. -/
private theorem exists_jSphere_ne :
    ∃ x₁ x₂ : psl2zToPSL2R.range.CompactifiedQuotient, jSphere x₁ ≠ jSphere x₂ :=
  ⟨ofCusp cuspOrbitInfty, ofQuotient (Quotient.mk _ I), by simp⟩

/-- The inverse of `jBiholomorph` takes different values at `0` and `∞`. -/
private theorem exists_jBiholomorph_symm_ne :
    ∃ y₁ y₂ : OnePoint ℂ, jBiholomorph.symm y₁ ≠ jBiholomorph.symm y₂ :=
  ⟨∞, ((0 : ℂ) : OnePoint ℂ), jBiholomorph.symm.injective.ne (by simp)⟩

/-- **The modular invariant as a meromorphic function** on the compactified level-one modular
curve: the pullback of the coordinate of the Riemann sphere along `jSphere`. It has the value
`j τ` at the orbit of `τ` and a simple pole at the cusp. -/
def jMeromorphicFunction : MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient :=
  comap jSphere mdifferentiable_jSphere exists_jSphere_ne coordinate

/-- As a map to the Riemann sphere, `jMeromorphicFunction` is `jSphere`. -/
@[simp]
theorem coe_jMeromorphicFunction : ⇑jMeromorphicFunction = jSphere := by
  ext x
  simp [jMeromorphicFunction, coordinate_apply]

/-- The finite part of `jMeromorphicFunction` at the orbit of `τ` is `j τ`. -/
@[simp]
theorem finitePart_jMeromorphicFunction_ofQuotient_mk (τ : ℍ) :
    jMeromorphicFunction.finitePart (ofQuotient (Quotient.mk _ τ)) = ModularForm.j τ :=
  finitePart_of_eq_coe (by simp)

/-- Pulling back along `jSphere` is a bijection from the meromorphic functions on the Riemann sphere
onto those on `X(1)`, with inverse the pullback along the inverse of `jBiholomorph`. -/
private theorem bijective_comapₐ_jSphere :
    Bijective (comapₐ jSphere mdifferentiable_jSphere exists_jSphere_ne) := by
  refine ⟨comapₐ_injective _ _ _, fun F ↦ ⟨comap jBiholomorph.symm
    (jBiholomorph.symm.mdifferentiable (by simp)) exists_jBiholomorph_symm_ne F, ext fun x ↦ ?_⟩⟩
  simp [← coe_jBiholomorph]

/-- **The function field of `X(1)` is `ℂ(j)`.** Every meromorphic function on the compactified
level-one modular curve is a unique rational function of `j`: evaluation at `j` is an isomorphism
of `ℂ`-algebras from the rational functions over `ℂ`. -/
def jRatFuncEquiv :
    RatFunc ℂ ≃ₐ[ℂ] MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient :=
  ratFuncEquiv.trans <| AlgEquiv.ofBijective _ bijective_comapₐ_jSphere

/-- On polynomials, `jRatFuncEquiv` is evaluation at `j`. -/
@[simp]
theorem jRatFuncEquiv_algebraMap (p : ℂ[X]) :
    jRatFuncEquiv (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval jMeromorphicFunction p := by
  simp [jRatFuncEquiv, ← aeval_algHom_apply, jMeromorphicFunction]

/-- The isomorphism `jRatFuncEquiv` sends the variable `X` to `j`. -/
@[simp]
theorem jRatFuncEquiv_X : jRatFuncEquiv RatFunc.X = jMeromorphicFunction := by
  simpa using jRatFuncEquiv_algebraMap Polynomial.X

/-- Every meromorphic function on `X(1)` is `P(j) / Q(j)` for polynomials `P, Q` over `ℂ`. -/
theorem jRatFuncEquiv_apply (r : RatFunc ℂ) :
    jRatFuncEquiv r = aeval jMeromorphicFunction r.num / aeval jMeromorphicFunction r.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [map_div₀, jRatFuncEquiv_algebraMap, jRatFuncEquiv_algebraMap]

/-- **`j` is transcendental over `ℂ`.** -/
theorem transcendental_jMeromorphicFunction : Transcendental ℂ jMeromorphicFunction := by
  rintro ⟨p, hp, h⟩
  rw [← jRatFuncEquiv_algebraMap, map_eq_zero_iff _ jRatFuncEquiv.injective] at h
  exact hp ((IsFractionRing.injective ℂ[X] (RatFunc ℂ)).eq_iff' (map_zero _) |>.mp h)

/-- A nonzero polynomial over `ℂ` does not vanish at `j`. -/
theorem aeval_jMeromorphicFunction_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    aeval jMeromorphicFunction p ≠ 0 :=
  fun h ↦ transcendental_jMeromorphicFunction ⟨p, hp, h⟩

/-- **The `q`-expansion of `j` at the cusp.** The Laurent expansion of `jMeromorphicFunction` at
the normalized level-one cusp datum is the classical `q`-expansion `q⁻¹ + 744 + 196884 q + ⋯` of
`j`. -/
@[simp]
theorem laurentQExpansion_jMeromorphicFunction :
    laurentQExpansion cuspDatumInfty jMeromorphicFunction =
      TauCeti.UpperHalfPlane.laurentQExpansion 1 ModularForm.j := by
  simp [laurentQExpansion_apply]

/-- The modular invariant has its coefficients in every subfield of `ℂ`: they are integers. -/
@[simp]
theorem jMeromorphicFunction_mem_coeffSubfield (K : Subfield ℂ) :
    jMeromorphicFunction ∈ coeffSubfield cuspDatumInfty K := by
  refine (mem_coeffSubfield _).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := ModularForm.exists_laurentQExpansion_j_coeff_eq_intCast n
  rw [laurentQExpansion_jMeromorphicFunction, hm]
  exact intCast_mem K m

/-- A polynomial over `K` evaluated at `j` lies in the subfield generated by `j` and the constants
in `K`. -/
private theorem aeval_map_mem_closure {K : Subfield ℂ} (p : K[X]) :
    aeval jMeromorphicFunction (p.map K.subtype) ∈
      Subfield.closure (insert jMeromorphicFunction (algebraMap ℂ _ '' K)) := by
  rw [aeval_eq_sum_range]
  refine Subfield.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  refine Subfield.mul_mem _ (Subfield.subset_closure (Set.mem_insert_of_mem _ ?_))
    (Subfield.pow_mem _ (Subfield.subset_closure (Set.mem_insert _ _)) _)
  exact ⟨_, by simp, rfl⟩

/-- `K(j)` is contained in the meromorphic functions with coefficients in `K`. -/
private theorem closure_le_coeffSubfield (K : Subfield ℂ) :
    Subfield.closure (insert jMeromorphicFunction (algebraMap ℂ _ '' K)) ≤
      coeffSubfield cuspDatumInfty K := by
  rw [Subfield.closure_le, Set.insert_subset_iff]
  refine ⟨jMeromorphicFunction_mem_coeffSubfield K, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  exact (algebraMap_mem_coeffSubfield _).mpr hc

/-- The Laurent expansion at the cusp of a polynomial over `K` in `j` is the image of the polynomial
evaluated at a series `ℓ` over `K` expanding `j`. -/
private theorem laurentQExpansion_aeval_map {K : Subfield ℂ} {ℓ : LaurentSeries K}
    (hℓ : HahnSeries.mapRingHom K.subtype ℓ =
      laurentQExpansion cuspDatumInfty jMeromorphicFunction) (r : K[X]) :
    laurentQExpansion cuspDatumInfty (aeval jMeromorphicFunction (r.map K.subtype)) =
      HahnSeries.mapRingHom K.subtype (r.eval₂ HahnSeries.C ℓ) := by
  rw [laurentQExpansion_aeval, ← hℓ, eval₂_map, hom_eval₂]
  congr 1
  ext c : 1
  simpa [HahnSeries.mapRingHom_apply] using (HahnSeries.map_C (Γ := ℤ) c K.subtype).symm

/-- **Descent of the rational expression in `j`.** A meromorphic function with coefficients in
`K` satisfies `F Q(j) = P(j)` for polynomials `P, Q` over `K` with `Q ≠ 0`. -/
private theorem exists_mul_aeval_eq_aeval_of_mem_coeffSubfield {K : Subfield ℂ}
    {F : MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient}
    (hF : F ∈ coeffSubfield cuspDatumInfty K) :
    ∃ p q : K[X], q ≠ 0 ∧ F * aeval jMeromorphicFunction (q.map K.subtype) =
      aeval jMeromorphicFunction (p.map K.subtype) := by
  obtain ⟨φ, hφ⟩ := (mem_coeffSubfield_iff_exists_mapRingHom_eq _).mp hF
  obtain ⟨ℓ, hℓ⟩ :=
    (mem_coeffSubfield_iff_exists_mapRingHom_eq _).mp (jMeromorphicFunction_mem_coeffSubfield K)
  -- `F Q(j) = P(j)` over `ℂ`, with `P / Q` the rational function of `F`
  have hFr : F * aeval jMeromorphicFunction (jRatFuncEquiv.symm F).denom =
      aeval jMeromorphicFunction (jRatFuncEquiv.symm F).num := by
    have h := jRatFuncEquiv_apply (jRatFuncEquiv.symm F)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (congrArg (· * _) h).trans
      (div_mul_cancel₀ _ (aeval_jMeromorphicFunction_ne_zero (RatFunc.denom_ne_zero _)))
  -- expand at the cusp, where the series of `F` and of `j` have coefficients in `K`
  have hL : HahnSeries.mapRingHom (algebraMap K ℂ) φ * (jRatFuncEquiv.symm F).denom.eval₂
      HahnSeries.C (HahnSeries.mapRingHom (algebraMap K ℂ) ℓ) = (jRatFuncEquiv.symm F).num.eval₂
      HahnSeries.C (HahnSeries.mapRingHom (algebraMap K ℂ) ℓ) := by
    have hK : algebraMap K ℂ = K.subtype := RingHom.ext (Algebra.algebraMap_ofSubsemiring_apply K)
    simpa [hK, hφ, hℓ, laurentQExpansion_aeval] using
      congrArg (laurentQExpansion cuspDatumInfty) hFr
  obtain ⟨p, q, hq, hpq⟩ :=
    HahnSeries.exists_mul_eval₂_C_eq_eval₂_C_of_mapRingHom (RatFunc.denom_ne_zero _) hL
  -- map the relation over `K` back to the expansions over `ℂ`
  refine ⟨p, q, hq, laurentQExpansion_injective cuspDatumInfty ?_⟩
  simp only [map_mul, ← hφ, laurentQExpansion_aeval_map hℓ, ← hpq]

/-- **The functions with coefficients in `K` are the rational functions of `j` over `K`.** A
meromorphic function on `X(1)` has all the Laurent coefficients of its expansion at the cusp in a
subfield `K` of `ℂ` exactly when it is `P(j) / Q(j)` for polynomials `P, Q` over `K` with
`Q ≠ 0`. -/
theorem mem_coeffSubfield_cuspDatumInfty_iff {K : Subfield ℂ}
    {F : MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient} :
    F ∈ coeffSubfield cuspDatumInfty K ↔ ∃ p q : K[X], q ≠ 0 ∧
      F = aeval jMeromorphicFunction (p.map K.subtype) /
        aeval jMeromorphicFunction (q.map K.subtype) := by
  refine ⟨fun hF ↦ ?_, ?_⟩
  · obtain ⟨p, q, hq, h⟩ := exists_mul_aeval_eq_aeval_of_mem_coeffSubfield hF
    refine ⟨p, q, hq, ?_⟩
    rw [← h, mul_div_cancel_right₀ _ (aeval_jMeromorphicFunction_ne_zero
      ((Polynomial.map_ne_zero_iff K.subtype_injective).mpr hq))]
  · rintro ⟨p, q, -, rfl⟩
    exact closure_le_coeffSubfield K
      (Subfield.div_mem _ (aeval_map_mem_closure p) (aeval_map_mem_closure q))

/-- **The functions with coefficients in `K` form the field `K(j)`.** For a subfield `K` of `ℂ`,
the meromorphic functions on `X(1)` whose Laurent expansion at the cusp has all its coefficients
in `K` form the subfield generated by `j` and the constants in `K`. -/
theorem coeffSubfield_cuspDatumInfty_eq_closure (K : Subfield ℂ) :
    coeffSubfield cuspDatumInfty K =
      Subfield.closure (insert jMeromorphicFunction (algebraMap ℂ _ '' K)) := by
  refine le_antisymm (fun F hF ↦ ?_) (closure_le_coeffSubfield K)
  obtain ⟨p, q, -, rfl⟩ := mem_coeffSubfield_cuspDatumInfty_iff.mp hF
  exact Subfield.div_mem _ (aeval_map_mem_closure p) (aeval_map_mem_closure q)

/-- **`F₁ = ℚ(j)`.** The meromorphic functions on the compactified level-one modular curve whose
Laurent expansion at the cusp has rational coefficients, that is coefficients in the prime
subfield `⊥` of `ℂ`, form the subfield generated by `j`. -/
theorem coeffSubfield_cuspDatumInfty_bot :
    coeffSubfield cuspDatumInfty ⊥ = Subfield.closure {jMeromorphicFunction} := by
  rw [coeffSubfield_cuspDatumInfty_eq_closure]
  refine le_antisymm (Subfield.closure_le.mpr ?_) (Subfield.closure_mono (by simp))
  rw [Set.insert_subset_iff]
  refine ⟨Subfield.subset_closure rfl, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  have h : algebraMap ℂ (MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient) c ∈
      (⊥ : Subfield ℂ).map (algebraMap ℂ _) := ⟨c, hc, rfl⟩
  rw [Subfield.map_bot] at h
  exact (bot_le : ⊥ ≤ Subfield.closure {jMeromorphicFunction}) h

/-! ### Functions pulled back from `X(1)` -/

/-- **The functions pulled back from `X(1)`.** For a finite-index subgroup `H` of `SL(2, ℤ)`, a
meromorphic function `F` on the compactified quotient `X_H` is the pullback along `X_H → X(1)` of
a meromorphic function on `X(1)` exactly when its value at the orbit of `τ` depends only on the
`SL(2, ℤ)`-orbit of `τ`. -/
theorem exists_compactifiedQuotientComap_eq_iff (H : _root_.Subgroup SL(2, ℤ)) [H.FiniteIndex]
    {F : MeromorphicFunction (H.map sl2zToPSL2R).CompactifiedQuotient} :
    (∃ G : MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient,
        _root_.Subgroup.compactifiedQuotientComap H.map_sl2zToPSL2R_le_range_psl2zToPSL2R G = F) ↔
      ∀ (γ : SL(2, ℤ)) (τ : ℍ),
        F (ofQuotient (Quotient.mk _ (γ • τ))) = F (ofQuotient (Quotient.mk _ τ)) := by
  set h := H.map_sl2zToPSL2R_le_range_psl2zToPSL2R
  refine ⟨?_, fun hF ↦ ?_⟩
  · rintro ⟨G, rfl⟩ γ τ
    simp only [_root_.Subgroup.compactifiedQuotientComap_apply,
      _root_.Subgroup.compactifiedQuotientMap_ofQuotient]
    refine congrArg (G ∘ ofQuotient) (Quotient.sound (orbitRel_apply.2 ?_))
    exact ⟨⟨sl2zToPSL2R γ, γ, psl2zToPSL2R_mk γ⟩, UpperHalfPlane.sl2zToPSL2R_smul γ τ⟩
  have := (_root_.Subgroup.isCofinite_map_sl2zToPSL2R H).compactSpace_compactifiedQuotient
  set β := jFiniteHolomorphicMap.comp (Fuchsian.compactifiedQuotientFiniteHolomorphicMap h)
  -- Over a finite point of the sphere, the fibre of `β` consists of the orbits of the
  -- `SL(2, ℤ)`-translates of one point of the upper half-plane, where `F` takes one value.
  have hfib : ∀ᶠ y in Filter.cofinite, (F '' (β ⁻¹' {y})).Subsingleton := by
    refine (Set.finite_singleton (∞ : OnePoint ℂ)).eventually_cofinite_notMem.mono ?_
    rintro y hy _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx' hy
    cases x with
    | ofCusp C => simp [β, ← hx] at hy
    | ofQuotient p =>
    cases x' with
    | ofCusp C => simp [β, ← hx'] at hy
    | ofQuotient p' =>
    induction p using Quotient.inductionOn with | h τ =>
    induction p' using Quotient.inductionOn with | h τ' =>
    have he := hx.trans hx'.symm
    simp only [β, FiniteHolomorphicMap.coe_comp, Function.comp_apply,
      Fuchsian.coe_compactifiedQuotientFiniteHolomorphicMap, coe_jFiniteHolomorphicMap,
      _root_.Subgroup.compactifiedQuotientMap_ofQuotient, jSphere_ofQuotient,
      OnePoint.coe_eq_coe] at he
    obtain ⟨γ, hγ⟩ := (j_eq_j_iff (z := τ') (w := τ)).1
      (by rw [← jQuotient_mk, ← jQuotient_mk]; exact he.symm)
    rw [← hγ, hF]
  obtain ⟨g, hg⟩ := MeromorphicFunction.exists_comap_eq_of_eventually_subsingleton_image β F hfib
  refine ⟨comap _ jFiniteHolomorphicMap.holomorphic jFiniteHolomorphicMap.nonconstant g,
    ext fun x ↦ ?_⟩
  rw [← hg, _root_.Subgroup.compactifiedQuotientComap_apply, comap_apply, comap_apply]
  simp [β]

end TauCeti.ModularGroup
