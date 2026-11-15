/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.CategoryTheory.Exact.Injective
public import TauCeti.Algebra.Homology.HomotopyCategory.EventuallyNullHomotopic

/-!
# Complexes acyclic in nonnegative degrees

A **tail** of a cochain complex `I` for an exact structure `E` is a family of conflations
`Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹`, `k ≥ 0`, factoring the differentials `dᵏ = pᵏ ≫ iᵏ⁺¹`: the complex is acyclic in
nonnegative degrees, and `Z⁰` is the object it resolves. An injective resolution of an object
`M`, with `Z⁰ = M`, is the basic example.

A map of complexes `φ : I ⟶ J` with tails restricts to maps of cycles `Zᵏ ⟶ Z'ᵏ`
(`TauCeti.ExactStructure.TailData.cyclesMap`). When the terms of `I` are projective:

* if the map of cycles in degree `k + 1` lifts along the deflation `Jᵏ ↠ Z'ᵏ⁺¹`, then the map in
  degree `k` factors through the projective object `Iᵏ`: correct `φᵏ` by the lift. In particular,
  if the map in degree `k + 1` factors through a projective object, so does the map in degree `k`;
* if `φ` is eventually null-homotopic, the homotopy lifts the map of cycles in a high degree along
  a deflation of `J`, so the map of cycles in degree `0` factors through a projective object.
  No condition on the terms of `J` is needed.

Conversely, maps of cycles lift to maps of complexes when `I` vanishes in negative degrees. A
family of maps `Iᵏ ⟶ Jᵏ` commuting with the differentials in high degrees extends downwards to a map
of complexes when the terms of `I` are projective, by lifting along the deflations of `J`; this
needs no tail of `I`. A map of cycles `Zⁿ ⟶ Z'ⁿ` extends upwards when the terms of `J` are
injective, by extending across the inflations of `I`.

The inflation `Z⁰ ↣ I⁰` is a map `TauCeti.ExactStructure.TailData.ι` from `Z⁰` placed in degree
`0` to `I`. When `I` vanishes in negative degrees its mapping cone is acyclic, so `I` resolves
`Z⁰`.

These lemmas give the faithfulness and fullness steps of the Keller–Vossieck theorem for a
Frobenius exact category, applied to injective resolutions, whose terms are then also projective.

## Main definitions

* `TauCeti.ExactStructure.TailData`: a tail of a complex.
* `TauCeti.ExactStructure.TailData.cyclesMap`: the maps of cycles induced by a map of complexes.
* `TauCeti.ExactStructure.TailData.ι`: the map from `Z⁰` placed in degree `0`.

## Main results

* `TauCeti.ExactStructure.TailData.factorsThrough_cyclesMap_of_comp_p` and
  `TauCeti.ExactStructure.TailData.factorsThrough_cyclesMap_of_succ`: the downward step.
* `TauCeti.ExactStructure.TailData.factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic`:
  an eventually null-homotopic map out of a complex of projectives restricts in degree `0` to a map
  factoring through a projective object.
* `TauCeti.ExactStructure.TailData.exists_hom_eq_of_eventually`: if `I` vanishes in negative
  degrees and has projective terms, maps commuting with the differentials in high degrees extend
  downwards to a map of complexes.
* `TauCeti.ExactStructure.TailData.exists_hom_cyclesMap_eq`: if `I` vanishes in negative degrees,
  every map of cycles is the map of cycles of a map of complexes, for projective source terms and
  injective target terms.
* `TauCeti.ExactStructure.TailData.acyclic_mappingCone_ι`: `I` resolves `Z⁰`.
* `TauCeti.ExactStructure.TailData.exists_iso_Z`: a map to `I` from a complex vanishing above
  degree `k + 1`, invertible in degree `k` and monic in degree `k + 1`, identifies its top term
  with the cycles `Zᵏ⁺¹`.

## Implementation notes

`TailData` is `TauCeti.ExactStructure.AcyclicData` restricted to nonnegative degrees, and the
lifting steps parallel those for `TauCeti.ExactStructure.CompleteResolution`. The acyclicity of the
mapping cone of `TailData.ι` follows the pushout construction of
`TauCeti/CategoryTheory/Exact/HomologicalComplex/Injective/Resolution.lean`, through
`TauCeti.ExactStructure.acyclic_mappingCone_of_isPushout`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Definition 10.1 (acyclic complexes) and Section 12
  (resolutions and the lifting of maps along them).
* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- A **tail** of a cochain complex `I`: conflations `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹` for `k ≥ 0` factoring the
differentials, `dᵏ = pᵏ ≫ iᵏ⁺¹`. -/
structure TailData (I : CochainComplex C ℤ) where
  /-- The objects of cycles. -/
  Z : ℕ → C
  /-- The inflations of the cycles into the complex. -/
  i (k : ℕ) : Z k ⟶ I.X k
  /-- The deflations onto the next cycles. -/
  p (k : ℕ) : I.X k ⟶ Z (k + 1)
  zero (k : ℕ) : i k ≫ p k = 0
  conflation (k : ℕ) : E.Conflation (ShortComplex.mk (i k) (p k) (zero k))
  fac (k : ℕ) : p k ≫ i (k + 1) = I.d k (k + 1)

namespace TailData

variable {E} {I J : CochainComplex C ℤ} (tI : E.TailData I) (tJ : E.TailData J)

attribute [reassoc (attr := simp)] zero

instance (k : ℕ) : Mono (tI.i k) := (E.isInflation_f (tI.conflation k)).mono

instance (k : ℕ) : Epi (tI.p k) := (E.isDeflation_g (tI.conflation k)).epi

/-- The morphism into the cycles `Zᵏ` induced by a morphism into `Iᵏ` killed by `Iᵏ ↠ Zᵏ⁺¹`. -/
noncomputable def liftZ {T : C} (k : ℕ) (f : T ⟶ I.X k) (hf : f ≫ tI.p k = 0) : T ⟶ tI.Z k :=
  (E.isKernelCokernelPair _ (tI.conflation k)).lift f hf

@[reassoc (attr := simp)]
theorem liftZ_i {T : C} (k : ℕ) (f : T ⟶ I.X k) (hf : f ≫ tI.p k = 0) :
    tI.liftZ k f hf ≫ tI.i k = f :=
  (E.isKernelCokernelPair _ (tI.conflation k)).lift_f f hf

/-- The morphism out of the cycles `Zᵏ⁺¹` induced by a morphism out of `Iᵏ` killing
`Zᵏ ↣ Iᵏ`. -/
noncomputable def descZ {T : C} (k : ℕ) (f : I.X k ⟶ T) (hf : tI.i k ≫ f = 0) :
    tI.Z (k + 1) ⟶ T :=
  (E.isKernelCokernelPair _ (tI.conflation k)).desc f hf

@[reassoc (attr := simp)]
theorem p_descZ {T : C} (k : ℕ) (f : I.X k ⟶ T) (hf : tI.i k ≫ f = 0) :
    tI.p k ≫ tI.descZ k f hf = f :=
  (E.isKernelCokernelPair _ (tI.conflation k)).g_desc f hf

@[reassoc (attr := simp)]
theorem i_d (k : ℕ) : tI.i k ≫ I.d k (k + 1) = 0 := by
  rw [← tI.fac, tI.zero_assoc, zero_comp]

@[reassoc (attr := simp)]
theorem d_p (k : ℕ) : I.d k (k + 1) ≫ tI.p (k + 1) = 0 := by
  rw [← tI.fac, Category.assoc, tI.zero, comp_zero]

/-- The conflation `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹` as an injective presentation of `Zᵏ`, when `Iᵏ` is
injective. -/
@[expose, simps]
def injectivePresentation (k : ℕ) (hI : E.isInjective (I.X k)) :
    E.InjectivePresentation (tI.Z k) where
  I := I.X k
  K := tI.Z (k + 1)
  i := tI.i k
  p := tI.p k
  zero := tI.zero k
  conflation := tI.conflation k
  isInjective := hI

/-- The conflation `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹` as a projective presentation of `Zᵏ⁺¹`, when `Iᵏ` is
projective. -/
@[expose, simps]
def projectivePresentation (k : ℕ) (hI : E.isProjective (I.X k)) :
    E.ProjectivePresentation (tI.Z (k + 1)) where
  K := tI.Z k
  P := I.X k
  i := tI.i k
  p := tI.p k
  zero := tI.zero k
  conflation := tI.conflation k
  isProjective := hI

variable (φ : I ⟶ J)

/-- The map of cycles in degree `k` induced by a map of complexes: the restriction of `φᵏ` to
`Zᵏ ↣ Iᵏ`, which lands in `Z'ᵏ`. -/
noncomputable def cyclesMap (k : ℕ) : tI.Z k ⟶ tJ.Z k :=
  tJ.liftZ k (tI.i k ≫ φ.f k) (by
    rw [← cancel_mono (tJ.i (k + 1)), Category.assoc, Category.assoc, tJ.fac, zero_comp,
      φ.comm, tI.i_d_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem cyclesMap_i (k : ℕ) : tI.cyclesMap tJ φ k ≫ tJ.i k = tI.i k ≫ φ.f k :=
  tJ.liftZ_i _ _ _

/-- The map of cycles in degree `k + 1` is induced by `φᵏ` along the deflations. -/
@[reassoc]
theorem p_cyclesMap (k : ℕ) : tI.p k ≫ tI.cyclesMap tJ φ (k + 1) = φ.f k ≫ tJ.p k := by
  rw [← cancel_mono (tJ.i (k + 1)), Category.assoc, cyclesMap_i, ← Category.assoc, tI.fac,
    Category.assoc, tJ.fac, φ.comm]
  rfl

@[simp]
theorem cyclesMap_id (k : ℕ) : tI.cyclesMap tI (𝟙 I) k = 𝟙 _ := by
  rw [← cancel_mono (tI.i k), cyclesMap_i, HomologicalComplex.id_f, Category.comp_id,
    Category.id_comp]

/-- Maps of cycles are functorial. (Not a simp lemma: the middle tail `tJ` is not determined by
the left-hand side.) -/
theorem cyclesMap_comp {K : CochainComplex C ℤ} (tK : E.TailData K) (ψ : J ⟶ K) (k : ℕ) :
    tI.cyclesMap tK (φ ≫ ψ) k = tI.cyclesMap tJ φ k ≫ tJ.cyclesMap tK ψ k := by
  rw [← cancel_mono (tK.i k), cyclesMap_i, Category.assoc, cyclesMap_i, cyclesMap_i_assoc,
    HomologicalComplex.comp_f]

@[simp]
theorem cyclesMap_zero (k : ℕ) : tI.cyclesMap tJ 0 k = 0 := by
  rw [← cancel_mono (tJ.i k), cyclesMap_i, HomologicalComplex.zero_f, comp_zero, zero_comp]

@[simp]
theorem cyclesMap_add (ψ : I ⟶ J) (k : ℕ) :
    tI.cyclesMap tJ (φ + ψ) k = tI.cyclesMap tJ φ k + tI.cyclesMap tJ ψ k := by
  rw [← cancel_mono (tJ.i k), cyclesMap_i, HomologicalComplex.add_f_apply, Preadditive.comp_add,
    Preadditive.add_comp, cyclesMap_i, cyclesMap_i]

@[simp]
theorem cyclesMap_neg (k : ℕ) : tI.cyclesMap tJ (-φ) k = -tI.cyclesMap tJ φ k := by
  rw [← cancel_mono (tJ.i k), cyclesMap_i, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
    Preadditive.neg_comp, cyclesMap_i]

@[simp]
theorem cyclesMap_sub (ψ : I ⟶ J) (k : ℕ) :
    tI.cyclesMap tJ (φ - ψ) k = tI.cyclesMap tJ φ k - tI.cyclesMap tJ ψ k := by
  rw [sub_eq_add_neg, cyclesMap_add, cyclesMap_neg, ← sub_eq_add_neg]

/-- **The downward step**: if `Iᵏ` is projective and the map of cycles in degree `k + 1` lifts
along the deflation `Jᵏ ↠ Z'ᵏ⁺¹`, then the map of cycles in degree `k` factors through `Iᵏ`. -/
theorem factorsThrough_cyclesMap_of_comp_p (k : ℕ) (hI : E.isProjective (I.X k))
    (u : tI.Z (k + 1) ⟶ J.X k) (hu : u ≫ tJ.p k = tI.cyclesMap tJ φ (k + 1)) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ k) := by
  -- The correction of `φᵏ` by the lift vanishes after `Jᵏ ↠ Z'ᵏ⁺¹`, so lands in the cycles.
  have hg : (φ.f k - tI.p k ≫ u) ≫ tJ.p k = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hu, p_cyclesMap, sub_self]
  refine (ObjectProperty.factorsThrough_iff _ _).2
    ⟨I.X k, hI, tI.i k, tJ.liftZ k _ hg, ?_⟩
  rw [← cancel_mono (tJ.i k), cyclesMap_i, Category.assoc, liftZ_i, Preadditive.comp_sub,
    tI.zero_assoc, zero_comp, sub_zero]

/-- **The downward step**, projective form: if `Iᵏ` is projective and the map of cycles in degree
`k + 1` factors through a projective object, so does the map of cycles in degree `k`. -/
theorem factorsThrough_cyclesMap_of_succ (k : ℕ) (hI : E.isProjective (I.X k))
    (h : E.isProjective.FactorsThrough (tI.cyclesMap tJ φ (k + 1))) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ k) := by
  obtain ⟨P, hP, u, v, huv⟩ := (ObjectProperty.factorsThrough_iff _ _).1 h
  -- Lift `v` along the deflation `Jᵏ ↠ Z'ᵏ⁺¹`, out of the projective `P`.
  exact tI.factorsThrough_cyclesMap_of_comp_p tJ φ k hI
    (u ≫ hP.factorThru (E.isDeflation_g (tJ.conflation k)) v)
    (by rw [Category.assoc, hP.factorThru_comp, huv])

/-- If the terms of `I` are projective and the map of cycles in some degree `n` factors through a
projective object, so does the map of cycles in degree `0`. -/
theorem factorsThrough_cyclesMap_zero_of_factorsThrough (hI : ∀ k : ℕ, E.isProjective (I.X k))
    (n : ℕ) (h : E.isProjective.FactorsThrough (tI.cyclesMap tJ φ n)) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ 0) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (tI.factorsThrough_cyclesMap_of_succ tJ φ n (hI n) h)

/-- **Eventually null-homotopic maps vanish stably on cycles**: if `φ` is eventually
null-homotopic and the terms of `I` are projective, the map of cycles in degree `0` factors
through a projective object. -/
theorem factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic
    (hI : ∀ k : ℕ, E.isProjective (I.X k)) (hφ : CochainComplex.IsEventuallyNullHomotopic φ) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ 0) := by
  obtain ⟨n, z, hz⟩ := (CochainComplex.isEventuallyNullHomotopic_iff φ).1 hφ
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n ≤ j := ⟨n.toNat, Int.self_le_toNat n⟩
  -- In degree `j + 1`, the homotopy equation restricted to the cycles lifts the map of cycles
  -- along `Jʲ ↠ Z'ʲ⁺¹`; then apply the downward steps.
  refine tI.factorsThrough_cyclesMap_zero_of_factorsThrough tJ φ hI j
    (tI.factorsThrough_cyclesMap_of_comp_p tJ φ j (hI j)
      (tI.i (j + 1) ≫ z.v ((j + 1 : ℕ) : ℤ) j (by push_cast; lia)) ?_)
  symm
  rw [← cancel_mono (tJ.i (j + 1)), cyclesMap_i, Category.assoc, Category.assoc, tJ.fac,
    hz _ (by push_cast; lia), δ_v (-1) 0 (by lia) z _ _ (add_zero _) j
      (((j + 1 : ℕ) : ℤ) + 1) (by push_cast; lia) rfl, Int.negOnePow_zero, one_smul,
    Preadditive.comp_add, tI.i_d_assoc, zero_comp, add_zero]
  rfl

section Extension

variable {tI tJ}

/-- **The downward extension step**: if `Iᵐ` is projective, a map `eᵐ⁺¹ : Iᵐ⁺¹ ⟶ Jᵐ⁺¹` such that
`d ≫ eᵐ⁺¹` lands in the cycles `Z'ᵐ⁺¹` extends to a map `eᵐ : Iᵐ ⟶ Jᵐ` with
`eᵐ ≫ d = d ≫ eᵐ⁺¹`. -/
theorem exists_comp_d_eq (m : ℕ) (hI : E.isProjective (I.X m))
    (e : I.X (m + 1 : ℕ) ⟶ J.X (m + 1 : ℕ))
    (he : I.d m ((m + 1 : ℕ) : ℤ) ≫ e ≫ tJ.p (m + 1) = 0) :
    ∃ e' : I.X m ⟶ J.X m, e' ≫ J.d m (m + 1) = I.d m (m + 1) ≫ e := by
  -- Lift the induced map `Iᵐ ⟶ Z'ᵐ⁺¹` along `Jᵐ ↠ Z'ᵐ⁺¹`.
  let x := tJ.liftZ (m + 1) (I.d m ((m + 1 : ℕ) : ℤ) ≫ e) (by rw [Category.assoc, he])
  let e' := hI.factorThru (E.isDeflation_g (tJ.conflation m)) x
  have he' : e' ≫ tJ.p m = x := hI.factorThru_comp _ _
  exact ⟨e', by rw [← tJ.fac, reassoc_of% he', tJ.liftZ_i]; rfl⟩

variable (tJ)

include tJ in
/-- **Eventual maps extend downwards**: if the terms of `I` are projective and `I` vanishes in
negative degrees, a family of maps `eᵏ : Iᵏ ⟶ Jᵏ` commuting with the differentials in degrees
`≥ m` agrees in degrees `≥ m` with a map of complexes. -/
theorem exists_hom_eq_of_eventually [I.IsStrictlyGE 0]
    (hI : ∀ k : ℕ, E.isProjective (I.X k)) (m : ℕ) (e : ∀ k : ℤ, I.X k ⟶ J.X k)
    (he : ∀ k : ℤ, (m : ℤ) ≤ k → e k ≫ J.d k (k + 1) = I.d k (k + 1) ≫ e (k + 1)) :
    ∃ Φ : I ⟶ J, ∀ k : ℤ, (m : ℤ) ≤ k → Φ.f k = e k := by
  induction m generalizing e with
  | zero =>
    refine ⟨{ f k := if 0 ≤ k then e k else 0, comm' := ?_ }, fun k hk ↦ by
      simp [show (0 : ℤ) ≤ k by lia]⟩
    rintro k _ rfl
    by_cases hk : 0 ≤ k
    · simp only [hk, ite_true, show 0 ≤ k + 1 by lia]
      exact he k (by simpa using hk)
    · exact (I.isZero_of_isStrictlyGE 0 k (by lia)).eq_of_src _ _
  | succ m ih =>
    -- `d ≫ eᵐ⁺¹` lands in the cycles, since `d ≫ eᵐ⁺¹ ≫ d = d ≫ d ≫ eᵐ⁺² = 0`.
    have hc : I.d m ((m + 1 : ℕ) : ℤ) ≫ e (m + 1 : ℕ) ≫ tJ.p (m + 1) = 0 := by
      rw [← cancel_mono (tJ.i (m + 1 + 1)), Category.assoc, Category.assoc, tJ.fac, zero_comp,
        he ((m + 1 : ℕ) : ℤ) le_rfl, I.d_comp_d_assoc, zero_comp]
    obtain ⟨e', h₁⟩ := exists_comp_d_eq m (hI m) (e (m + 1 : ℕ)) hc
    obtain ⟨Φ, hΦ⟩ := ih (Function.update e (m : ℤ) e') (fun k hk ↦ by
      rcases (show k = m ∨ (m + 1 : ℕ) ≤ k by lia) with rfl | hk'
      · rw [Function.update_self, Function.update_of_ne (by lia)]
        exact h₁
      · rw [Function.update_of_ne (by lia), Function.update_of_ne (by lia)]
        exact he k hk')
    refine ⟨Φ, fun k hk ↦ ?_⟩
    rw [hΦ k (by lia), Function.update_of_ne (by lia)]

variable {tJ}

/-- **The upward extension step**: if `Jᵐ⁺¹` is injective, a map `eᵐ : Iᵐ ⟶ Jᵐ` sending the cycles
into the cycles extends to a map `eᵐ⁺¹ : Iᵐ⁺¹ ⟶ Jᵐ⁺¹` sending the cycles into the cycles, with
`d ≫ eᵐ⁺¹ = eᵐ ≫ d`. -/
theorem exists_d_comp_eq (m : ℕ) (hJ : E.isInjective (J.X (m + 1 : ℕ))) (e : I.X m ⟶ J.X m)
    (he : tI.i m ≫ e ≫ tJ.p m = 0) :
    ∃ e' : I.X (m + 1 : ℕ) ⟶ J.X (m + 1 : ℕ), I.d m (m + 1) ≫ e' = e ≫ J.d m (m + 1) ∧
      tI.i (m + 1) ≫ e' ≫ tJ.p (m + 1) = 0 := by
  -- Extend the induced map `Zᵐ⁺¹ ⟶ Z'ᵐ⁺¹ ↣ Jᵐ⁺¹` across `Zᵐ⁺¹ ↣ Iᵐ⁺¹`.
  let y := tI.descZ m (e ≫ tJ.p m) he
  let e' := hJ.factorThru (E.isInflation_f (tI.conflation (m + 1))) (y ≫ tJ.i (m + 1))
  have he' : tI.i (m + 1) ≫ e' = y ≫ tJ.i (m + 1) := hJ.comp_factorThru _ _
  refine ⟨e', ?_, by rw [reassoc_of% he', tJ.zero, comp_zero]⟩
  rw [← tI.fac, Category.assoc, he', tI.p_descZ_assoc, Category.assoc, tJ.fac]

/-- The upward extensions `Iⁿ⁺ᵏ ⟶ Jⁿ⁺ᵏ` of a map of cycles `x : Zⁿ ⟶ Z'ⁿ`. -/
private noncomputable def upSeq (hJ : ∀ k : ℕ, E.isInjective (J.X k)) (n : ℕ)
    (x : tI.Z n ⟶ tJ.Z n) : ∀ k : ℕ,
    { e : I.X (n + k : ℕ) ⟶ J.X (n + k : ℕ) // tI.i (n + k) ≫ e ≫ tJ.p (n + k) = 0 }
  | 0 => ⟨(hJ n).factorThru (E.isInflation_f (tI.conflation n)) (x ≫ tJ.i n), by
      dsimp only [Nat.add_zero]
      rw [(hJ n).comp_factorThru_assoc, Category.assoc, tJ.zero, comp_zero]⟩
  | k + 1 => ⟨(exists_d_comp_eq (n + k) (hJ _) (upSeq hJ n x k).1 (upSeq hJ n x k).2).choose,
      (exists_d_comp_eq (n + k) (hJ _) (upSeq hJ n x k).1 (upSeq hJ n x k).2).choose_spec.2⟩

/-- The upward extensions as a family indexed by `ℤ`, zero below `n`. -/
private noncomputable def upFamily (hJ : ∀ k : ℕ, E.isInjective (J.X k)) (n : ℕ)
    (x : tI.Z n ⟶ tJ.Z n) (j : ℤ) : I.X j ⟶ J.X j :=
  if h : (n : ℤ) ≤ j then
    (I.XIsoOfEq (show ((n + (j - n).toNat : ℕ) : ℤ) = j by lia)).inv ≫
      (upSeq hJ n x (j - n).toNat).1 ≫ (J.XIsoOfEq (by lia)).hom
  else 0

private theorem upFamily_natCast (hJ : ∀ k : ℕ, E.isInjective (J.X k)) (n : ℕ)
    (x : tI.Z n ⟶ tJ.Z n) (k : ℕ) : upFamily hJ n x (n + k : ℕ) = (upSeq hJ n x k).1 := by
  have key : ∀ (a : ℕ) (ha : a = k),
      (I.XIsoOfEq (show ((n + a : ℕ) : ℤ) = (n + k : ℕ) by subst ha; rfl)).inv ≫
        (upSeq hJ n x a).1 ≫ (J.XIsoOfEq (show ((n + a : ℕ) : ℤ) = (n + k : ℕ) by
          subst ha; rfl)).hom = (upSeq hJ n x k).1 := by
    rintro a rfl
    simp
  rw [upFamily, dite_eq_left (by lia)]
  exact key _ (by lia)

variable (tI tJ) in
/-- **Maps of cycles lift to maps of complexes**: if the terms of `I` are projective, those of `J`
are injective, and `I` vanishes in negative degrees, every map of cycles `x : Zⁿ ⟶ Z'ⁿ` is the
map of cycles of a map of complexes. -/
theorem exists_hom_cyclesMap_eq [I.IsStrictlyGE 0]
    (hI : ∀ k : ℕ, E.isProjective (I.X k)) (hJ : ∀ k : ℕ, E.isInjective (J.X k)) (n : ℕ)
    (x : tI.Z n ⟶ tJ.Z n) : ∃ Φ : I ⟶ J, tI.cyclesMap tJ Φ n = x := by
  -- Extend `x` upwards by injectivity of the terms of `J`, then downwards by projectivity of the
  -- terms of `I`.
  obtain ⟨Φ, hΦ⟩ := exists_hom_eq_of_eventually tJ hI n (upFamily hJ n x) (fun j hj ↦ by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = ((n + k : ℕ) : ℤ) := ⟨(j - n).toNat, by lia⟩
    rw [show (((n + k : ℕ) : ℤ) + 1) = ((n + (k + 1) : ℕ) : ℤ) by lia, upFamily_natCast,
      upFamily_natCast]
    exact ((exists_d_comp_eq (n + k) (hJ _) _ (upSeq hJ n x k).2).choose_spec.1).symm)
  refine ⟨Φ, (cancel_mono (tJ.i n)).1 ?_⟩
  -- `n + 0` reduces to `n`, so this is the case `k = 0` of `upFamily_natCast`.
  have h0 : upFamily hJ n x n = (upSeq hJ n x 0).1 := upFamily_natCast hJ n x 0
  rw [cyclesMap_i, hΦ n le_rfl, h0]
  exact (hJ n).comp_factorThru _ _

end Extension

section Resolution

open ZeroObject

/-- The map from the cycles `Z⁰`, placed in degree `0`, to `I`: the inflation `Z⁰ ↣ I⁰`. -/
noncomputable def ι : (HomologicalComplex.single C (.up ℤ) 0).obj (tI.Z 0) ⟶ I :=
  HomologicalComplex.mkHomFromSingle (tI.i 0) (by
    rintro _ rfl
    exact tI.i_d 0)

/-- In degree `0`, the map `ι` is the inflation `Z⁰ ↣ I⁰`. -/
@[simp]
theorem ι_f_zero :
    tI.ι.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tI.Z 0)).hom ≫ tI.i 0 :=
  HomologicalComplex.mkHomFromSingle_f _ _

@[simp]
theorem ι_f_of_ne {n : ℤ} (hn : n ≠ 0) : tI.ι.f n = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ 0 _ n hn).eq_of_src _ _

/-- A map of complexes `Φ` extends its map of cycles in degree `0`, along `ι`. -/
@[reassoc]
theorem single_map_comp_ι (Φ : I ⟶ J) :
    (HomologicalComplex.single C (.up ℤ) 0).map (tI.cyclesMap tJ Φ 0) ≫ tJ.ι = tI.ι ≫ Φ := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_f_zero, ι_f_zero,
    HomologicalComplex.single_map_f_self, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    cyclesMap_i]
  exact (Category.assoc _ _ _).symm

/-- If `ι ≫ Φ` is homotopic to `f ≫ ι` for a morphism of cycles `f : Z⁰ ⟶ Z'⁰`, and `J` vanishes
in negative degrees, then `f` is the map of cycles of `Φ` in degree `0`. -/
theorem cyclesMap_zero_eq_of_homotopy [J.IsStrictlyGE 0] (Φ : I ⟶ J) (f : tI.Z 0 ⟶ tJ.Z 0)
    (h : Homotopy (tI.ι ≫ Φ) ((HomologicalComplex.single C (.up ℤ) 0).map f ≫ tJ.ι)) :
    tI.cyclesMap tJ Φ 0 = f := by
  -- Homotopic maps out of an object in degree `0` agree in degree `0`.
  have h0 := CochainComplex.f_eq_of_homotopy_of_single (neg_add_cancel 1)
    (J.isZero_of_isStrictlyGE 0 (-1) (by lia)) h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_f_zero, ι_f_zero,
    HomologicalComplex.single_map_f_self, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, cancel_epi] at h0
  rw [← cancel_mono (tJ.i 0), cyclesMap_i]
  exact h0

/-- The cycles of the mapping cone of `ι`: those of `I` in nonnegative degrees, the terms of `I`
in negative degrees. -/
private noncomputable def coneB : ℤ → C
  | Int.ofNat k => tI.Z k
  | Int.negSucc k => I.X (Int.negSucc k)

private noncomputable def coneJ : ∀ m, coneB tI m ⟶ I.X m
  | Int.ofNat k => tI.i k
  | Int.negSucc _ => 𝟙 _

private noncomputable def coneU : ∀ m, I.X m ⟶ coneB tI (m + 1)
  | Int.ofNat k => tI.p k
  | Int.negSucc _ => 0

private noncomputable def coneV :
    ∀ m, ((HomologicalComplex.single C (.up ℤ) 0).obj (tI.Z 0)).X m ⟶ coneB tI m
  | Int.ofNat 0 => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tI.Z 0)).hom
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

/-- **`I` resolves `Z⁰`**: if `I` vanishes in negative degrees, the mapping cone of `ι` is
acyclic. -/
theorem acyclic_mappingCone_ι [I.IsStrictlyGE 0] :
    E.acyclic (CochainComplex.mappingCone tI.ι) := by
  have hS (m : ℤ) (hm : m ≠ 0) :
      IsZero (((HomologicalComplex.single C (.up ℤ) 0).obj (tI.Z 0)).X m) :=
    HomologicalComplex.isZero_single_obj_X _ 0 _ m hm
  refine E.acyclic_mappingCone_of_isPushout _ (coneB tI) (coneJ tI) (fun _ ↦ 0) (coneU tI)
    (coneV tI) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_)
  · match m with
    | Int.ofNat k => exact E.isInflation_f (tI.conflation k)
    | Int.negSucc _ => exact E.isInflation_id _
  · match m with
    | Int.ofNat k =>
      exact (E.isKernelCokernelPair _ (tI.conflation k)).isPushout_of_isZero (hS _ (by lia))
    | Int.negSucc 0 =>
      have : IsIso (coneJ tI (Int.negSucc 0)) := inferInstanceAs (IsIso (𝟙 _))
      have : IsIso (coneV tI (Int.negSucc 0 + 1)) :=
        inferInstanceAs (IsIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tI.Z 0)).hom)
      exact IsPushout.of_horiz_isIso ⟨(I.isZero_of_isStrictlyGE 0 _ (by lia)).eq_of_src _ _⟩
    | Int.negSucc (k + 1) =>
      have : IsIso (coneJ tI (Int.negSucc (k + 1))) := inferInstanceAs (IsIso (𝟙 _))
      have : IsIso (coneV tI (Int.negSucc (k + 1) + 1)) :=
        isIso_of_source_target_iso_zero _ (hS _ (by lia)).isoZero
          (I.isZero_of_isStrictlyGE 0 (Int.negSucc k) (by lia)).isoZero
      exact IsPushout.of_horiz_isIso ⟨(I.isZero_of_isStrictlyGE 0 _ (by lia)).eq_of_src _ _⟩
  · match m with
    | Int.ofNat k => exact tI.fac k
    | Int.negSucc _ => exact (I.isZero_of_isStrictlyGE 0 _ (by lia)).eq_of_src _ _
  · match m with
    | Int.ofNat 0 => exact (tI.ι_f_zero).symm
    | Int.ofNat (k + 1) => exact (hS _ (by lia)).eq_of_src _ _
    | Int.negSucc _ => exact (hS _ (by lia)).eq_of_src _ _
  · simp
  · simp

end Resolution

/-- **The top term of a truncation is an object of cycles.** Let `j : T ⟶ I` map a complex
vanishing above degree `k + 1` to `I`, invertible in degree `k` and monic in degree `k + 1`, with
`Tᵏ ⟶ Tᵏ⁺¹` an epimorphism.
Then `j` identifies the top term `Tᵏ⁺¹` with the cycles `Zᵏ⁺¹`. -/
theorem exists_iso_Z {T : CochainComplex C ℤ} (k : ℕ) [T.IsStrictlyLE ((k + 1 : ℕ) : ℤ)]
    (j : T ⟶ I) [IsIso (j.f k)] [Mono (j.f ((k + 1 : ℕ) : ℤ))]
    [Epi (T.d k ((k + 1 : ℕ) : ℤ))] :
    ∃ θ : T.X ((k + 1 : ℕ) : ℤ) ≅ tI.Z (k + 1), θ.hom ≫ tI.i (k + 1) = j.f ((k + 1 : ℕ) : ℤ) := by
  -- `jᵏ⁺¹` lands in the cycles, giving `θ`; the inverse `ψ` is induced by `(jᵏ)⁻¹ ≫ d`.
  have hjp : j.f ((k + 1 : ℕ) : ℤ) ≫ tI.p (k + 1) = 0 := by
    rw [← cancel_mono (tI.i (k + 1 + 1)), Category.assoc, tI.fac, zero_comp, j.comm,
      (T.isZero_of_isStrictlyLE ((k + 1 : ℕ) : ℤ) _ (by lia)).eq_of_tgt (T.d _ _) 0, zero_comp]
  let θ : T.X ((k + 1 : ℕ) : ℤ) ⟶ tI.Z (k + 1) := tI.liftZ (k + 1) _ hjp
  have hθ : θ ≫ tI.i (k + 1) = j.f ((k + 1 : ℕ) : ℤ) := tI.liftZ_i _ _ _
  have hd : T.d k ((k + 1 : ℕ) : ℤ) ≫ θ = j.f k ≫ tI.p k := by
    rw [← cancel_mono (tI.i (k + 1)), Category.assoc, hθ, Category.assoc, tI.fac]
    exact (j.comm _ _).symm
  let ψ : tI.Z (k + 1) ⟶ T.X ((k + 1 : ℕ) : ℤ) :=
    tI.descZ k (inv (j.f k) ≫ T.d k ((k + 1 : ℕ) : ℤ)) (by
      rw [← cancel_mono (j.f ((k + 1 : ℕ) : ℤ)), Category.assoc, Category.assoc, zero_comp,
        ← j.comm, IsIso.inv_hom_id_assoc]
      exact tI.i_d k)
  have hψ : tI.p k ≫ ψ = inv (j.f k) ≫ T.d k ((k + 1 : ℕ) : ℤ) := tI.p_descZ _ _ _
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    rw [← cancel_epi (T.d k ((k + 1 : ℕ) : ℤ)), reassoc_of% hd, hψ, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    rw [← cancel_epi (tI.p k), reassoc_of% hψ, hd, IsIso.inv_hom_id_assoc, Category.comp_id]
  exact ⟨⟨θ, ψ, hθψ, hψθ⟩, hθ⟩

end TailData

end TauCeti.ExactStructure
