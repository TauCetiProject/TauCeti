/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import TauCeti.CategoryTheory.ObjectProperty.FactorsThrough
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

* if the map of cycles in degree `k + 1` factors through a projective object, so does the map in
  degree `k`: lift along the deflation `Jᵏ ↠ Z'ᵏ⁺¹` and correct `φᵏ`;
* if `φ` is eventually null-homotopic, the map of cycles in a high degree factors through a term
  of `J`, so in the projective case the map of cycles in degree `0` factors through a projective
  object.

Conversely, maps of cycles lift to maps of complexes. A family of maps `Iᵏ ⟶ Jᵏ` commuting with
the differentials in high degrees extends downwards to a map of complexes when the terms of `I` are
projective, by lifting along the deflations of `J`; and a map of cycles `Zⁿ ⟶ Z'ⁿ` extends upwards
when the terms of `J` are injective, by extending across the inflations of `I`.

For a Frobenius exact category this computes the morphisms of the stable category from maps of
injective resolutions modulo eventual null-homotopy, the stabilization in the Keller–Vossieck
theorem.

## Main definitions

* `TauCeti.ExactStructure.TailData`: a tail of a complex.
* `TauCeti.ExactStructure.TailData.cyclesMap`: the maps of cycles induced by a map of complexes.

## Main results

* `TauCeti.ExactStructure.TailData.factorsThrough_cyclesMap_of_succ`: the downward step.
* `TauCeti.ExactStructure.TailData.factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic`:
  an eventually null-homotopic map of complexes of projectives restricts in degree `0` to a map
  factoring through a projective object.
* `TauCeti.ExactStructure.TailData.exists_hom_eq_of_eventually`: maps commuting with the
  differentials in high degrees extend downwards to a map of complexes.
* `TauCeti.ExactStructure.TailData.exists_hom_cyclesMap_eq`: every map of cycles is the map of
  cycles of a map of complexes, for projective source terms and injective target terms.

## References

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

/-- **The downward step**: if `Iᵏ` is projective and the map of cycles in degree `k + 1`
factors through a projective object, so does the map of cycles in degree `k`. -/
theorem factorsThrough_cyclesMap_of_succ (k : ℕ) (hI : E.isProjective (I.X k))
    (h : E.isProjective.FactorsThrough (tI.cyclesMap tJ φ (k + 1))) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ k) := by
  obtain ⟨P, hP, u, v, huv⟩ := (ObjectProperty.factorsThrough_iff _ _).1 h
  -- Lift `v` along the deflation `Jᵏ ↠ Z'ᵏ⁺¹`, out of the projective `P`.
  let w := hP.factorThru (E.isDeflation_g (tJ.conflation k)) v
  have hw : w ≫ tJ.p k = v := hP.factorThru_comp _ _
  -- The correction of `φᵏ` vanishes after `Jᵏ ↠ Z'ᵏ⁺¹`, so lands in the cycles.
  have hg : (φ.f k - tI.p k ≫ u ≫ w) ≫ tJ.p k = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw, ← huv, ← p_cyclesMap,
      sub_self]
  refine (ObjectProperty.factorsThrough_iff _ _).2
    ⟨I.X k, hI, tI.i k, tJ.liftZ k _ hg, ?_⟩
  rw [← cancel_mono (tJ.i k), cyclesMap_i, Category.assoc, liftZ_i, Preadditive.comp_sub,
    tI.zero_assoc, zero_comp, sub_zero]

/-- If the terms of `I` are projective and the map of cycles in some degree `n` factors through a
projective object, so does the map of cycles in degree `0`. -/
theorem factorsThrough_cyclesMap_zero_of_factorsThrough (hI : ∀ k : ℕ, E.isProjective (I.X k))
    (n : ℕ) (h : E.isProjective.FactorsThrough (tI.cyclesMap tJ φ n)) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ 0) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (tI.factorsThrough_cyclesMap_of_succ tJ φ n (hI n) h)

/-- **Eventually null-homotopic maps vanish stably on cycles**: if `φ` is eventually
null-homotopic and the terms of `I` and `J` are projective, the map of cycles in degree `0`
factors through a projective object. -/
theorem factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic
    (hI : ∀ k : ℕ, E.isProjective (I.X k)) (hJ : ∀ k : ℕ, E.isProjective (J.X k))
    (hφ : CochainComplex.IsEventuallyNullHomotopic φ) :
    E.isProjective.FactorsThrough (tI.cyclesMap tJ φ 0) := by
  obtain ⟨n, z, hz⟩ := (CochainComplex.isEventuallyNullHomotopic_iff φ).1 hφ
  obtain ⟨j, hj⟩ : ∃ j : ℕ, n ≤ j := ⟨n.toNat, Int.self_le_toNat n⟩
  -- In degree `j + 1`, the homotopy equation restricted to the cycles factors through `Jʲ`; then
  -- apply the downward step.
  refine tI.factorsThrough_cyclesMap_zero_of_factorsThrough tJ φ hI (j + 1)
    ((ObjectProperty.factorsThrough_iff _ _).2 ⟨J.X j, hJ j,
      tI.i (j + 1) ≫ z.v ((j + 1 : ℕ) : ℤ) j (by push_cast; lia), tJ.p j, ?_⟩)
  rw [← cancel_mono (tJ.i (j + 1)), cyclesMap_i, Category.assoc, Category.assoc, tJ.fac,
    hz _ (by push_cast; lia), δ_v (-1) 0 (by lia) z _ _ (add_zero _) j
      (((j + 1 : ℕ) : ℤ) + 1) (by push_cast; lia) rfl, Int.negOnePow_zero, one_smul,
    Preadditive.comp_add, tI.i_d_assoc, zero_comp, add_zero]
  rfl

section Extension

variable {tI tJ}

/-- **The downward extension step**: if `Iᵐ` is projective, a map `eᵐ⁺¹ : Iᵐ⁺¹ ⟶ Jᵐ⁺¹` sending the
cycles into the cycles extends to a map `eᵐ : Iᵐ ⟶ Jᵐ` sending the cycles into the cycles, with
`eᵐ ≫ d = d ≫ eᵐ⁺¹`. -/
theorem exists_comp_d_eq (m : ℕ) (hI : E.isProjective (I.X m))
    (e : I.X (m + 1 : ℕ) ⟶ J.X (m + 1 : ℕ))
    (he : tI.i (m + 1) ≫ e ≫ tJ.p (m + 1) = 0) :
    ∃ e' : I.X m ⟶ J.X m, e' ≫ J.d m (m + 1) = I.d m (m + 1) ≫ e ∧
      tI.i m ≫ e' ≫ tJ.p m = 0 := by
  -- Lift the induced map `Iᵐ ↠ Zᵐ⁺¹ ⟶ Z'ᵐ⁺¹` along `Jᵐ ↠ Z'ᵐ⁺¹`.
  let x := tJ.liftZ (m + 1) (tI.i (m + 1) ≫ e) (by rw [Category.assoc, he])
  let e' := hI.factorThru (E.isDeflation_g (tJ.conflation m)) (tI.p m ≫ x)
  have he' : e' ≫ tJ.p m = tI.p m ≫ x := hI.factorThru_comp _ _
  refine ⟨e', ?_, by rw [he', tI.zero_assoc, zero_comp]⟩
  rw [← tJ.fac, reassoc_of% he', tJ.liftZ_i, ← Category.assoc, tI.fac]

variable (tI tJ)

include tI tJ in
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
    have hc : tI.i (m + 1) ≫ e (m + 1 : ℕ) ≫ tJ.p (m + 1) = 0 := by
      rw [← cancel_mono (tJ.i (m + 1 + 1)), Category.assoc, Category.assoc, tJ.fac, zero_comp]
      have := he ((m + 1 : ℕ) : ℤ) le_rfl
      rw [this, ← Category.assoc, tI.i_d, zero_comp]
    obtain ⟨e', h₁, -⟩ := exists_comp_d_eq m (hI m) (e (m + 1 : ℕ)) hc
    obtain ⟨Φ, hΦ⟩ := ih (Function.update e (m : ℤ) e') (fun k hk ↦ by
      rcases (show k = m ∨ (m + 1 : ℕ) ≤ k by lia) with rfl | hk'
      · rw [Function.update_self, Function.update_of_ne (by lia)]
        exact h₁
      · rw [Function.update_of_ne (by lia), Function.update_of_ne (by lia)]
        exact he k hk')
    refine ⟨Φ, fun k hk ↦ ?_⟩
    rw [hΦ k (by lia), Function.update_of_ne (by lia)]

variable {tI tJ}

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
      change tI.i n ≫ (hJ n).factorThru (E.isInflation_f (tI.conflation n)) (x ≫ tJ.i n) ≫
        tJ.p n = 0
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
  obtain ⟨Φ, hΦ⟩ := exists_hom_eq_of_eventually tI tJ hI n (upFamily hJ n x) (fun j hj ↦ by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = ((n + k : ℕ) : ℤ) := ⟨(j - n).toNat, by lia⟩
    change upFamily hJ n x ((n + k : ℕ) : ℤ) ≫ J.d ((n + k : ℕ) : ℤ) ((n + (k + 1) : ℕ) : ℤ) =
      I.d ((n + k : ℕ) : ℤ) ((n + (k + 1) : ℕ) : ℤ) ≫ upFamily hJ n x ((n + (k + 1) : ℕ) : ℤ)
    rw [upFamily_natCast, upFamily_natCast]
    exact ((exists_d_comp_eq (n + k) (hJ _) _ (upSeq hJ n x k).2).choose_spec.1).symm)
  refine ⟨Φ, (cancel_mono (tJ.i n)).1 ?_⟩
  rw [cyclesMap_i, hΦ n le_rfl]
  change tI.i n ≫ upFamily hJ n x ((n + 0 : ℕ) : ℤ) = _
  rw [upFamily_natCast]
  exact (hJ n).comp_factorThru _ _

end Extension

end TailData

end TauCeti.ExactStructure
