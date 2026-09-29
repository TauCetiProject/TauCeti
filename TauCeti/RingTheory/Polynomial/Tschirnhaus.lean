/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Tschirnhaus transforms

Let `f` and `T` be polynomials over a commutative ring `R`. The *Tschirnhaus transform* of `f`
by `T` is the polynomial whose roots are the values `T(α)` at the roots `α` of `f`, counted with
multiplicity. It is defined on the coefficient side, as the resultant in `X` of `f(X)` and
`Y - T(X)`,
```
tschirnhausPolynomial f T = Res_X (f(X), Y - T(X)),
```
so it is a polynomial expression in the coefficients of `f` and `T`. For monic `f` it therefore
commutes with every base change `R →+* S`: the transform of an integral polynomial over `ℚ` is
the image of its transform over `ℤ`, and the transform modulo `p` is its reduction.

`T` is *admissible* for `f` over a field `K` when it separates the roots of `f`, that is, when
`a ↦ T(a)` is injective on the roots of `f` in its splitting field. Admissibility does not depend
on the field in which the roots are taken, and for monic `f` the transform is separable exactly
when `f` is separable and `T` is admissible. Admissible transforms are the classical remedy for
a resolvent whose specialization at `f` is not separable: the resolvent is recomputed at the
transform, whose roots are in bijection with those of `f`.

## Main definitions

* `Polynomial.tschirnhausPolynomial f T`: the Tschirnhaus transform of `f` by `T`.
* `Polynomial.TschirnhausAdmissible f T`: `T` separates the roots of `f`.

## Main results

* `Polynomial.map_tschirnhausPolynomial`: for monic `f`, the transform commutes with base change.
* `Polynomial.tschirnhausPolynomial_eq_prod_roots`: over a domain in which monic `f` splits, the
  transform is `∏ (X - T(α))` over the roots `α` of `f`.
* `Polynomial.monic_tschirnhausPolynomial`, `Polynomial.natDegree_tschirnhausPolynomial`: the
  transform of a monic polynomial is monic of the same degree, over any commutative ring.
* `Polynomial.aroots_tschirnhausPolynomial`, `Polynomial.rootSet_tschirnhausPolynomial`: the roots
  of the transform are the values of `T` at the roots of `f`.
* `Polynomial.separable_tschirnhausPolynomial_iff`: the transform is separable if and only if `f`
  is separable and `T` is admissible.
* `Polynomial.TschirnhausAdmissible.bijOn_rootSet`: an admissible `T` maps the roots of `f`
  bijectively onto the roots of the transform.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §6.3, where
  Tschirnhausen transformations are used to make a resolvent squarefree.
-/

public section

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The **Tschirnhaus transform** of `f` by `T`: the resultant in `X` of `f(X)` and `Y - T(X)`,
as a polynomial in `Y`. When `f` is monic and splits, its roots are the values `T(α)` at the
roots `α` of `f`, counted with multiplicity (`Polynomial.tschirnhausPolynomial_eq_prod_roots`). -/
def tschirnhausPolynomial (f T : R[X]) : R[X] :=
  resultant (f.map C) (C X - T.map C : R[X][X])

theorem tschirnhausPolynomial_def (f T : R[X]) :
    tschirnhausPolynomial f T = resultant (f.map C) (C X - T.map C : R[X][X]) :=
  (rfl)

private theorem natDegree_C_X_sub_map_C_le (T : R[X]) :
    (C X - T.map C : R[X][X]).natDegree ≤ T.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_map_le)

/-- For monic `f`, the resultant defining the Tschirnhaus transform may be computed with any
valid bound `n` on the degree of `T`. -/
theorem tschirnhausPolynomial_eq_resultant {f : R[X]} (hf : f.Monic) (T : R[X]) {n : ℕ}
    (hn : T.natDegree ≤ n) :
    tschirnhausPolynomial f T = resultant (f.map C) (C X - T.map C) f.natDegree n := by
  rw [← natDegree_map_eq_of_injective C_injective f,
    (hf.map C).resultant_of_le ((natDegree_C_X_sub_map_C_le T).trans hn), tschirnhausPolynomial]

/-- **Base change.** For monic `f`, the Tschirnhaus transform commutes with every ring
morphism. No hypothesis on `T` is needed, although its degree may drop. -/
theorem map_tschirnhausPolynomial {f : R[X]} (hf : f.Monic) (T : R[X]) (φ : R →+* S) :
    (tschirnhausPolynomial f T).map φ = tschirnhausPolynomial (f.map φ) (T.map φ) := by
  nontriviality S
  rw [tschirnhausPolynomial_eq_resultant hf T le_rfl,
    tschirnhausPolynomial_eq_resultant (hf.map φ) (T.map φ) natDegree_map_le, hf.natDegree_map,
    ← coe_mapRingHom, ← resultant_map_map]
  have hC : (mapRingHom φ).comp C = C.comp φ := RingHom.ext fun a ↦ by simp
  congr 1 <;> simp [Polynomial.map_map, hC]

/-- **The root-product formula.** Over a domain in which the monic polynomial `f` splits, the
Tschirnhaus transform of `f` by `T` is `∏ (X - T(α))`, the product over the roots `α` of `f`
counted with multiplicity. -/
theorem tschirnhausPolynomial_eq_prod_roots [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) (T : R[X]) :
    tschirnhausPolynomial f T = ((f.roots.map T.eval).map fun b ↦ X - C b).prod := by
  rw [tschirnhausPolynomial_eq_resultant hf T le_rfl,
    ← natDegree_map_eq_of_injective C_injective f,
    resultant_eq_prod_eval _ _ _ (natDegree_C_X_sub_map_C_le T) (hs.map C),
    (hf.map C).leadingCoeff, one_pow, one_mul, hs.roots_map_of_injective C_injective,
    Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ ↦ ?_
  simp [eval_map]

/-- Over a domain in which the monic polynomial `f` splits, the roots of the Tschirnhaus
transform are the values of `T` at the roots of `f`, counted with multiplicity. -/
theorem roots_tschirnhausPolynomial [IsDomain R] {f : R[X]} (hf : f.Monic) (hs : f.Splits)
    (T : R[X]) : (tschirnhausPolynomial f T).roots = f.roots.map T.eval := by
  rw [tschirnhausPolynomial_eq_prod_roots hf hs, roots_multiset_prod_X_sub_C]

/-- The Tschirnhaus transform splits in every domain in which the monic polynomial `f` splits. -/
theorem splits_tschirnhausPolynomial [IsDomain R] {f : R[X]} (hf : f.Monic) (hs : f.Splits)
    (T : R[X]) : (tschirnhausPolynomial f T).Splits := by
  rw [tschirnhausPolynomial_eq_prod_roots hf hs]
  refine Splits.multisetProd fun g hg ↦ ?_
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hg
  exact Splits.X_sub_C b

private theorem monic_and_natDegree_tschirnhausPolynomial {f : R[X]} (hf : f.Monic) (T : R[X]) :
    (tschirnhausPolynomial f T).Monic ∧ (tschirnhausPolynomial f T).natDegree = f.natDegree := by
  induction f using induction_of_Splits_of_injective_of_surjective with
  | Splits K f hs =>
    rw [tschirnhausPolynomial_eq_prod_roots hf hs, natDegree_multiset_prod_X_sub_C_eq_card,
      Multiset.card_map, hs.natDegree_eq_card_roots]
    exact ⟨monic_multiset_prod_of_monic _ _ fun b _ ↦ monic_X_sub_C b, rfl⟩
  | injective R S φ hφ f IH =>
    obtain ⟨hmonic, hdeg⟩ := IH (hf.map φ) (T.map φ)
    rw [← map_tschirnhausPolynomial hf, natDegree_map_eq_of_injective hφ,
      natDegree_map_eq_of_injective hφ] at hdeg
    rw [← map_tschirnhausPolynomial hf] at hmonic
    exact ⟨monic_of_injective hφ hmonic, hdeg⟩
  | surjective R S φ hφ f IH =>
    obtain ⟨q, rfl, -, hq⟩ :=
      lifts_and_natDegree_eq_and_monic ((mem_lifts f).2 (map_surjective φ hφ f)) hf
    obtain ⟨T, rfl⟩ := map_surjective φ hφ T
    obtain ⟨hmonic, hdeg⟩ := IH q hq T
    rw [← map_tschirnhausPolynomial hq]
    rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨monic_of_subsingleton _, by simp [natDegree_of_subsingleton]⟩
    · exact ⟨hmonic.map φ, by rw [hmonic.natDegree_map, hq.natDegree_map, hdeg]⟩

/-- The Tschirnhaus transform of a monic polynomial is monic, over any commutative ring. -/
theorem monic_tschirnhausPolynomial {f : R[X]} (hf : f.Monic) (T : R[X]) :
    (tschirnhausPolynomial f T).Monic :=
  (monic_and_natDegree_tschirnhausPolynomial hf T).1

/-- The Tschirnhaus transform of a monic polynomial has the same degree, whatever the degree of
`T`, over any commutative ring. -/
@[simp]
theorem natDegree_tschirnhausPolynomial {f : R[X]} (hf : f.Monic) (T : R[X]) :
    (tschirnhausPolynomial f T).natDegree = f.natDegree :=
  (monic_and_natDegree_tschirnhausPolynomial hf T).2

/-- The Tschirnhaus transform by `X` is the identity on monic polynomials. -/
@[simp]
theorem tschirnhausPolynomial_X {f : R[X]} (hf : f.Monic) : tschirnhausPolynomial f X = f := by
  rw [tschirnhausPolynomial_eq_resultant hf X natDegree_X_le, Polynomial.map_X,
    resultant_C_sub_X_right _ _ _ natDegree_map_le, eval_map, eval₂_C_X]

/-- The Tschirnhaus transform by a constant `c` collapses every root to `c`. -/
@[simp]
theorem tschirnhausPolynomial_C {f : R[X]} (hf : f.Monic) (c : R) :
    tschirnhausPolynomial f (C c) = (X - C c) ^ f.natDegree := by
  rw [tschirnhausPolynomial_eq_resultant hf (C c) (natDegree_C c).le, Polynomial.map_C, ← C_sub,
    resultant_C_zero_right]

section Algebra

variable {K L : Type*} [CommRing K] [CommRing L] [IsDomain L] [Algebra K L]

/-- If the monic polynomial `f` splits in the domain `L`, then the roots in `L` of the
Tschirnhaus transform are the values of `T` at the roots of `f` in `L`, counted with
multiplicity. -/
theorem aroots_tschirnhausPolynomial {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).aroots L = (f.aroots L).map fun a ↦ aeval a T := by
  rw [aroots_def, map_tschirnhausPolynomial hf, roots_tschirnhausPolynomial (hf.map _) hs,
    aroots_def]
  exact Multiset.map_congr rfl fun a _ ↦ eval_map_algebraMap T a

/-- If the monic polynomial `f` splits in the domain `L`, then the roots in `L` of the
Tschirnhaus transform are the images under `T` of the roots of `f` in `L`. -/
theorem rootSet_tschirnhausPolynomial {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).rootSet L = (fun a ↦ aeval a T) '' f.rootSet L := by
  classical
  ext b
  simp [rootSet_def, aroots_tschirnhausPolynomial hf hs]

end Algebra

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `T` is **admissible** for `f`, or *separates the roots* of `f`, when `a ↦ T(a)` is injective
on the roots of `f` in its splitting field. By `Polynomial.tschirnhausAdmissible_iff_injOn`, the
splitting field may be replaced by any field in which `f` splits. -/
def TschirnhausAdmissible (f T : K[X]) : Prop :=
  Set.InjOn (fun a ↦ aeval a T) (f.rootSet f.SplittingField)

/-- Admissibility may be tested in any field in which `f` splits. -/
theorem tschirnhausAdmissible_iff_injOn {f T : K[X]} (hs : (f.map (algebraMap K L)).Splits) :
    TschirnhausAdmissible f T ↔ Set.InjOn (fun a ↦ aeval a T) (f.rootSet L) := by
  let φ : f.SplittingField →ₐ[K] L := SplittingField.lift f hs
  have hφ : Function.Injective φ := φ.toRingHom.injective
  rw [TschirnhausAdmissible, ← (SplittingField.splits f).image_rootSet φ]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [aeval_algHom_apply] at hab
    rw [h ha hb (hφ hab)]
  · refine fun h a ha b hb hab ↦ hφ (h (Set.mem_image_of_mem φ ha) (Set.mem_image_of_mem φ hb) ?_)
    simp only [aeval_algHom_apply, hab]

/-- The Tschirnhaus transform by `X` is admissible. -/
@[simp]
theorem tschirnhausAdmissible_X (f : K[X]) : TschirnhausAdmissible f X := by
  simp [TschirnhausAdmissible]

/-- If the monic polynomial `f` splits in `L`, then its Tschirnhaus transform by `T` is separable
if and only if `f` is separable and `T` is injective on the roots of `f` in `L`. -/
theorem separable_tschirnhausPolynomial_iff_of_splits {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).Separable ↔
      f.Separable ∧ Set.InjOn (fun a ↦ aeval a T) (f.rootSet L) := by
  classical
  have hmem : ∀ a, a ∈ f.rootSet L ↔ a ∈ f.aroots L := fun a ↦ by
    rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset]
  have hsT : ((tschirnhausPolynomial f T).map (algebraMap K L)).Splits := by
    rw [map_tschirnhausPolynomial hf]
    exact splits_tschirnhausPolynomial (hf.map _) hs _
  rw [← nodup_aroots_iff_of_splits (monic_tschirnhausPolynomial hf T).ne_zero hsT,
    ← nodup_aroots_iff_of_splits hf.ne_zero hs, aroots_tschirnhausPolynomial hf hs]
  constructor
  · intro h
    have hnodup := Multiset.Nodup.of_map _ h
    refine ⟨hnodup, fun a ha b hb hab ↦ ?_⟩
    exact (Multiset.nodup_map_iff_inj_on hnodup).1 h a ((hmem a).1 ha) b ((hmem b).1 hb) hab
  · rintro ⟨hnodup, hinj⟩
    exact (Multiset.nodup_map_iff_inj_on hnodup).2
      fun a ha b hb hab ↦ hinj ((hmem a).2 ha) ((hmem b).2 hb) hab

/-- **Separability of the Tschirnhaus transform.** For monic `f`, the Tschirnhaus transform by
`T` is separable if and only if `f` is separable and `T` is admissible for `f`. -/
theorem separable_tschirnhausPolynomial_iff {f : K[X]} (hf : f.Monic) (T : K[X]) :
    (tschirnhausPolynomial f T).Separable ↔ f.Separable ∧ TschirnhausAdmissible f T :=
  separable_tschirnhausPolynomial_iff_of_splits hf (SplittingField.splits f) T

/-- **The root sets correspond.** If `T` is admissible for the monic polynomial `f`, which
splits in `L`, then `a ↦ T(a)` maps the roots of `f` in `L` bijectively onto the roots of the
Tschirnhaus transform in `L`. -/
theorem TschirnhausAdmissible.bijOn_rootSet {f T : K[X]} (hT : TschirnhausAdmissible f T)
    (hf : f.Monic) (hs : (f.map (algebraMap K L)).Splits) :
    Set.BijOn (fun a ↦ aeval a T) (f.rootSet L) ((tschirnhausPolynomial f T).rootSet L) := by
  rw [rootSet_tschirnhausPolynomial hf hs]
  exact ((tschirnhausAdmissible_iff_injOn hs).1 hT).bijOn_image

end Field

end Polynomial
