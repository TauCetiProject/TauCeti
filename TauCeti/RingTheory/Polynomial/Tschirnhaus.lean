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
For monic `f`, it commutes with every base change `R →+* S`: the transform of a monic integral
polynomial over `ℚ` is the image of its transform over `ℤ`, and the transform modulo `p` is its
reduction. For arbitrary `f`, degree-dropping specialization need not preserve this resultant.

`T` is *admissible* for `f` over a field `K` when it separates the roots of `f`, that is, when
`a ↦ T(a)` is injective on the roots of `f` in its splitting field. Admissibility does not depend
on the field in which the roots are taken. For nonzero `f` over a field, the transform is
separable exactly when `f` is separable and `T` is admissible. Admissible transforms are the
classical remedy for a resolvent whose specialization at `f` is not separable: the resolvent is
recomputed at the transform, whose roots are in bijection with those of `f`.

## Main definitions

* `Polynomial.tschirnhausPolynomial f T`: the Tschirnhaus transform of `f` by `T`.
* `Polynomial.TschirnhausAdmissible f T`: `T` separates the roots of `f`.

## Main results

* `Polynomial.map_tschirnhausPolynomial`: for monic `f`, the transform commutes with base change.
* `Polynomial.map_tschirnhausPolynomial_of_injective`: the same holds for any `f` under an
  injective base change.
* `Polynomial.tschirnhausPolynomial_eq_prod_roots`: over a domain in which monic `f` splits, the
  transform is `∏ (X - T(α))` over the roots `α` of `f`.
* `Polynomial.tschirnhausPolynomial_eq_C_mul_prod_roots`: the corresponding formula for
  any splitting polynomial over a domain, including its leading coefficient factor.
* `Polynomial.ne_zero_tschirnhausPolynomial_field`: the transform of any nonzero field
  polynomial is nonzero.
* `Polynomial.monic_tschirnhausPolynomial`, `Polynomial.natDegree_tschirnhausPolynomial`: the
  transform of a monic polynomial is monic of the same degree, over any commutative ring.
* `Polynomial.aroots_tschirnhausPolynomial`, `Polynomial.rootSet_tschirnhausPolynomial`: the roots
  of the transform are the values of `T` at the roots of `f`.
  The `_field` variants cover arbitrary field polynomials in splitting domains, including `f = 0`.
* `Polynomial.isRoot_tschirnhausPolynomial`: over a domain, `T(α)` is a root of the transform
  whenever `α` is a root of the nonzero polynomial `f`.
* `Polynomial.Monic.tschirnhausRootMap`, `Polynomial.tschirnhausRootMap`: the resulting map
  `α ↦ T(α)` from the roots of `f` to the roots of its transform, for monic `f` over a domain and
  for any field polynomial in a domain; it is surjective whenever `f` splits.
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
@[simp]
theorem map_tschirnhausPolynomial {f : R[X]} (hf : f.Monic) (T : R[X]) (φ : R →+* S) :
    (tschirnhausPolynomial f T).map φ = tschirnhausPolynomial (f.map φ) (T.map φ) := by
  nontriviality S
  rw [tschirnhausPolynomial_eq_resultant hf T le_rfl,
    tschirnhausPolynomial_eq_resultant (hf.map φ) (T.map φ) natDegree_map_le, hf.natDegree_map]
  simp only [← coe_mapRingHom]
  rw [← resultant_map_map]
  have hC : (mapRingHom φ).comp C = C.comp φ := RingHom.ext fun a ↦ by simp
  congr 1 <;> simp [Polynomial.map_map, hC]

/-- The Tschirnhaus transform commutes with an injective base change, without requiring `f` to
be monic. -/
@[simp]
theorem map_tschirnhausPolynomial_of_injective (f T : R[X]) (φ : R →+* S)
    (hφ : Function.Injective φ) :
    (tschirnhausPolynomial f T).map φ = tschirnhausPolynomial (f.map φ) (T.map φ) := by
  have hφ' : Function.Injective (mapRingHom φ) := map_injective φ hφ
  rw [tschirnhausPolynomial, tschirnhausPolynomial]
  conv_lhs => rw [← coe_mapRingHom φ]
  rw [← resultant_map_map]
  have hC : (mapRingHom φ).comp C = C.comp φ := RingHom.ext fun a ↦ by simp
  have hfmap : (f.map C).map (mapRingHom φ) = (f.map φ).map C := by
    simp [Polynomial.map_map, hC]
  have hgmap : (C X - T.map C : R[X][X]).map (mapRingHom φ) =
      C X - (T.map φ).map C := by simp [Polynomial.map_map, hC]
  rw [hfmap, hgmap]
  congr 1
  · simp [natDegree_map_eq_of_injective C_injective,
      natDegree_map_eq_of_injective hφ]
  · rw [← hgmap, natDegree_map_eq_of_injective hφ']

/-- **The root-product formula.** Over a domain in which `f` splits, its Tschirnhaus transform is
its leading coefficient raised to the degree in `X` of `Y - T(X)`, times the product of
`X - T(α)` over the roots `α` of `f`, counted with multiplicity. -/
theorem tschirnhausPolynomial_eq_C_mul_prod_roots [IsDomain R] {f : R[X]}
    (hs : f.Splits) (T : R[X]) :
    tschirnhausPolynomial f T =
      C (f.leadingCoeff ^ (C X - T.map C : R[X][X]).natDegree) *
        ((f.roots.map T.eval).map fun b ↦ X - C b).prod := by
  let g : R[X][X] := C X - T.map C
  rw [tschirnhausPolynomial, resultant_eq_prod_eval _ _ _ le_rfl (hs.map C),
    leadingCoeff_map_of_injective C_injective, ← C_pow,
    hs.roots_map_of_injective C_injective, Multiset.map_map]
  have heval (a : R) : eval (C a) g = X - C (T.eval a) := by simp [g, eval_map]
  simp only [Function.comp_def, heval, Multiset.map_map, g]

/-- **The monic root-product formula.** Over a domain in which the monic polynomial `f` splits,
the Tschirnhaus transform of `f` by `T` is `∏ (X - T(α))`. -/
theorem tschirnhausPolynomial_eq_prod_roots [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) (T : R[X]) :
    tschirnhausPolynomial f T = ((f.roots.map T.eval).map fun b ↦ X - C b).prod := by
  rw [tschirnhausPolynomial_eq_C_mul_prod_roots hs, hf.leadingCoeff, one_pow, C_1, one_mul]

/-- For a polynomial over a domain that splits, the roots of its Tschirnhaus transform are the
values of `T` at its roots, counted with multiplicity. Both sides are empty when `f = 0`. -/
@[simp]
theorem roots_tschirnhausPolynomial [IsDomain R] {f : R[X]} (hs : f.Splits) (T : R[X]) :
    (tschirnhausPolynomial f T).roots = f.roots.map T.eval := by
  rcases eq_or_ne f 0 with rfl | hf
  · rcases eq_or_ne (C X - T.map C : R[X][X]).natDegree 0 with h | h <;>
      simp [tschirnhausPolynomial_def, h]
  rw [tschirnhausPolynomial_eq_C_mul_prod_roots hs T,
    roots_C_mul _ (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf)),
    roots_multiset_prod_X_sub_C]

/-- For a nonzero polynomial over a domain, the value of `T` at any root of `f` is a root of the
Tschirnhaus transform; no splitting hypothesis is needed. -/
theorem isRoot_tschirnhausPolynomial [IsDomain R] {f : R[X]} (hf : f ≠ 0) {a : R}
    (ha : f.IsRoot a) (T : R[X]) : (tschirnhausPolynomial f T).IsRoot (T.eval a) := by
  let ψ := algebraMap R (FractionRing R)
  let M := (f.map ψ).SplittingField
  let φ : R →+* M := (algebraMap (FractionRing R) M).comp ψ
  have hφ : Function.Injective φ :=
    (algebraMap (FractionRing R) M).injective.comp (IsFractionRing.injective R _)
  have hf' : f.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hf
  have hs : (f.map φ).Splits := by
    rw [← Polynomial.map_map]
    exact SplittingField.splits _
  have hmem : φ (T.eval a) ∈ (tschirnhausPolynomial (f.map φ) (T.map φ)).roots := by
    rw [roots_tschirnhausPolynomial hs]
    refine Multiset.mem_map.2 ⟨φ a, ?_, by rw [eval_map_apply]⟩
    rw [mem_roots hf', IsRoot, eval_map_apply, ha.eq_zero, map_zero]
  rw [← map_tschirnhausPolynomial_of_injective f T φ hφ] at hmem
  rw [IsRoot, ← hφ.eq_iff, map_zero, ← eval_map_apply]
  exact (mem_roots'.1 hmem).2

/-- The Tschirnhaus transform splits in every domain in which `f` splits. -/
theorem splits_tschirnhausPolynomial [IsDomain R] {f : R[X]} (hs : f.Splits)
    (T : R[X]) : (tschirnhausPolynomial f T).Splits := by
  rw [tschirnhausPolynomial_eq_C_mul_prod_roots hs T]
  refine Splits.C_mul (.multisetProd fun g hg ↦ ?_) _
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

/-- The Tschirnhaus transform by `X` is the identity. -/
@[simp]
theorem tschirnhausPolynomial_X (f : R[X]) : tschirnhausPolynomial f X = f := by
  nontriviality R
  have hdeg : (C X - X : R[X][X]).natDegree = 1 := by
    -- Reverse the subtraction to use `natDegree_X_sub_C`; negation preserves the degree.
    rw [show (C X - X : R[X][X]) = -(X - C X) by ring, natDegree_neg,
      natDegree_X_sub_C]
  -- Rewrite the mapped right input explicitly, since its default degree bound depends on it.
  rw [tschirnhausPolynomial, Polynomial.map_X]
  rw [hdeg, resultant_C_sub_X_right _ _ _ le_rfl]
  simp [eval_map]

/-- The Tschirnhaus transform by a constant `c` collapses every root to `c`. -/
@[simp]
theorem tschirnhausPolynomial_C (f : R[X]) (c : R) :
    tschirnhausPolynomial f (C c) = (X - C c) ^ f.natDegree := by
  -- The second polynomial is constant in the outer variable, so `resultant_C_zero_right`
  -- applies with its outer degree explicitly rewritten to zero.
  rw [tschirnhausPolynomial, Polynomial.map_C, ← C_sub]
  simp only [natDegree_C]
  rw [resultant_C_zero_right]
  simp [natDegree_map_eq_of_injective C_injective]

section Algebra

variable {K L : Type*} [CommRing K] [CommRing L] [IsDomain L] [Algebra K L]

/-- If the monic polynomial `f` splits in the domain `L`, then the roots in `L` of the
Tschirnhaus transform are the values of `T` at the roots of `f` in `L`, counted with
multiplicity. -/
@[simp]
theorem aroots_tschirnhausPolynomial {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).aroots L = (f.aroots L).map fun a ↦ aeval a T := by
  rw [aroots_def, map_tschirnhausPolynomial hf,
    roots_tschirnhausPolynomial hs,
    aroots_def]
  exact Multiset.map_congr rfl fun a _ ↦ eval_map_algebraMap T a

/-- If the monic polynomial `f` splits in the domain `L`, then the roots in `L` of the
Tschirnhaus transform are the images under `T` of the roots of `f` in `L`. -/
@[simp]
theorem rootSet_tschirnhausPolynomial {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).rootSet L = (fun a ↦ aeval a T) '' f.rootSet L := by
  classical
  ext b
  simp [rootSet_def, aroots_tschirnhausPolynomial hf hs]

/-- The map from the roots of a monic polynomial `f` to the roots of its Tschirnhaus transform,
sending `α` to `T(α)`, in a domain `L`. -/
noncomputable def Monic.tschirnhausRootMap {f : K[X]} (hf : f.Monic) (T : K[X]) :
    f.rootSet L → (tschirnhausPolynomial f T).rootSet L :=
  Set.MapsTo.restrict (fun a ↦ aeval a T) _ _ <| by
    intro a ha
    rw [mem_rootSet', ← eval_map_algebraMap] at ha ⊢
    dsimp only
    rw [map_tschirnhausPolynomial hf, ← eval_map_algebraMap]
    exact ⟨(monic_tschirnhausPolynomial (hf.map _) _).ne_zero,
      isRoot_tschirnhausPolynomial ha.1 ha.2 _⟩

@[simp]
theorem Monic.coe_tschirnhausRootMap {f : K[X]} (hf : f.Monic) (T : K[X]) (x : f.rootSet L) :
    (hf.tschirnhausRootMap T x : L) = aeval (x : L) T :=
  Set.MapsTo.val_restrict_apply _ _

/-- Every root of the Tschirnhaus transform of a monic polynomial is the image of a root of the
original polynomial. -/
theorem Monic.tschirnhausRootMap_surjective {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    Function.Surjective (hf.tschirnhausRootMap (L := L) T) := by
  refine (Set.MapsTo.restrict_surjective_iff _).2 ?_
  rw [rootSet_tschirnhausPolynomial hf hs]
  exact Set.surjOn_image _ _

/-- If a monic polynomial splits after a base change, then its Tschirnhaus transform splits
after the same base change. -/
theorem splits_map_tschirnhausPolynomial {f : K[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    ((tschirnhausPolynomial f T).map (algebraMap K L)).Splits := by
  rw [map_tschirnhausPolynomial hf]
  exact splits_tschirnhausPolynomial hs _

end Algebra

section Field

variable {K : Type*} [Field K]

/-- Over a field, the Tschirnhaus transform of a nonzero polynomial is nonzero. -/
theorem ne_zero_tschirnhausPolynomial_field {f : K[X]} (hf : f ≠ 0)
    (T : K[X]) : tschirnhausPolynomial f T ≠ 0 := by
  intro h
  have hm := congrArg (fun p : K[X] ↦ p.map (algebraMap K f.SplittingField)) h
  rw [map_tschirnhausPolynomial_of_injective f T _
    (algebraMap K f.SplittingField).injective,
    tschirnhausPolynomial_eq_C_mul_prod_roots (SplittingField.splits f)
      (T.map (algebraMap K f.SplittingField))] at hm
  rw [Polynomial.map_zero] at hm
  exact mul_ne_zero
    (C_ne_zero.mpr (pow_ne_zero _ (leadingCoeff_ne_zero.mpr (map_ne_zero hf))))
    (monic_multisetProd_X_sub_C _).ne_zero hm

section Domain

variable {L : Type*} [CommRing L] [IsDomain L] [Algebra K L]

/-- In any domain in which a field polynomial splits, the roots of its transform are the values
of `T` at its roots, counted with multiplicity. Both sides are empty when `f = 0`. -/
@[simp]
theorem aroots_tschirnhausPolynomial_field {f : K[X]}
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).aroots L = (f.aroots L).map fun a ↦ aeval a T := by
  rw [aroots_def, map_tschirnhausPolynomial_of_injective f T _ (algebraMap K L).injective,
    roots_tschirnhausPolynomial hs, aroots_def]
  exact Multiset.map_congr rfl fun a _ ↦ eval_map_algebraMap T a

/-- The root set of the transform of a field polynomial is the image of the root set under `T`,
in any domain in which `f` splits. Both sides are empty when `f = 0`. -/
@[simp]
theorem rootSet_tschirnhausPolynomial_field {f : K[X]}
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).rootSet L = (fun a ↦ aeval a T) '' f.rootSet L := by
  classical
  ext b
  simp [rootSet_def, aroots_tschirnhausPolynomial_field hs]

/-- If a polynomial over a field splits after a base change to a domain, then its Tschirnhaus
transform splits after the same base change. -/
theorem splits_map_tschirnhausPolynomial_field {f : K[X]}
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    ((tschirnhausPolynomial f T).map (algebraMap K L)).Splits := by
  rw [map_tschirnhausPolynomial_of_injective f T _ (algebraMap K L).injective]
  exact splits_tschirnhausPolynomial hs _

/-- The map from the roots of a field polynomial to the roots of its Tschirnhaus transform in a
domain, sending `α` to `T(α)`. -/
noncomputable def tschirnhausRootMap (f T : K[X]) :
    f.rootSet L → (tschirnhausPolynomial f T).rootSet L :=
  Set.MapsTo.restrict (fun a ↦ aeval a T) _ _ <| by
    intro a ha
    rw [mem_rootSet', ← eval_map_algebraMap] at ha ⊢
    dsimp only
    have hf : f ≠ 0 := fun hf ↦ ha.1 (by simp [hf])
    refine ⟨map_ne_zero (ne_zero_tschirnhausPolynomial_field hf T), ?_⟩
    rw [map_tschirnhausPolynomial_of_injective f T _ (algebraMap K L).injective,
      ← eval_map_algebraMap]
    exact isRoot_tschirnhausPolynomial ha.1 ha.2 _

@[simp]
theorem coe_tschirnhausRootMap (f T : K[X]) (x : f.rootSet L) :
    (tschirnhausRootMap f T x : L) = aeval (x : L) T :=
  Set.MapsTo.val_restrict_apply _ _

/-- Every root in a splitting domain of the Tschirnhaus transform of a field polynomial is the
image of a root of the original polynomial. For `f = 0` the transform is `0` or `1`, so both root
sets are empty. -/
theorem tschirnhausRootMap_surjective {f : K[X]}
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    Function.Surjective (tschirnhausRootMap (L := L) f T) := by
  refine (Set.MapsTo.restrict_surjective_iff _).2 ?_
  rw [rootSet_tschirnhausPolynomial_field hs]
  exact Set.surjOn_image _ _

end Domain

variable {L : Type*} [Field L] [Algebra K L]

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

/-- If the nonzero polynomial `f` splits in `L`, then its Tschirnhaus transform by `T` is separable
if and only if `f` is separable and `T` is injective on the roots of `f` in `L`. -/
theorem separable_tschirnhausPolynomial_iff_of_splits {f : K[X]} (hf : f ≠ 0)
    (hs : (f.map (algebraMap K L)).Splits) (T : K[X]) :
    (tschirnhausPolynomial f T).Separable ↔
      f.Separable ∧ Set.InjOn (fun a ↦ aeval a T) (f.rootSet L) := by
  classical
  have hmem : ∀ a, a ∈ f.rootSet L ↔ a ∈ f.aroots L := fun a ↦ by
    rw [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset]
  have hsT : ((tschirnhausPolynomial f T).map (algebraMap K L)).Splits := by
    exact splits_map_tschirnhausPolynomial_field hs _
  have hfT : tschirnhausPolynomial f T ≠ 0 := ne_zero_tschirnhausPolynomial_field hf T
  rw [← nodup_aroots_iff_of_splits hfT hsT,
    ← nodup_aroots_iff_of_splits hf hs, aroots_tschirnhausPolynomial_field hs]
  constructor
  · intro h
    refine ⟨Multiset.Nodup.of_map _ h, fun a ha b hb hab ↦ ?_⟩
    exact Multiset.inj_on_of_nodup_map h a ((hmem a).1 ha) b ((hmem b).1 hb) hab
  · rintro ⟨hnodup, hinj⟩
    exact hnodup.map_on fun a ha b hb hab ↦ hinj ((hmem a).2 ha) ((hmem b).2 hb) hab

/-- **Separability of the Tschirnhaus transform.** For nonzero `f`, the Tschirnhaus transform by
`T` is separable if and only if `f` is separable and `T` is admissible for `f`. -/
theorem separable_tschirnhausPolynomial_iff {f : K[X]} (hf : f ≠ 0) (T : K[X]) :
    (tschirnhausPolynomial f T).Separable ↔ f.Separable ∧ TschirnhausAdmissible f T :=
  separable_tschirnhausPolynomial_iff_of_splits hf (SplittingField.splits f) T

/-- **The root sets correspond.** If `T` is admissible for a polynomial `f` that splits in `L`,
then `a ↦ T(a)` maps the roots of `f` in `L` bijectively onto the roots of the Tschirnhaus
transform in `L`. Both root sets are empty when `f = 0`. -/
theorem TschirnhausAdmissible.bijOn_rootSet {f T : K[X]} (hT : TschirnhausAdmissible f T)
    (hs : (f.map (algebraMap K L)).Splits) :
    Set.BijOn (fun a ↦ aeval a T) (f.rootSet L) ((tschirnhausPolynomial f T).rootSet L) := by
  rw [rootSet_tschirnhausPolynomial_field hs]
  exact ((tschirnhausAdmissible_iff_injOn hs).1 hT).bijOn_image

/-- The canonical equivalence from the roots of `f` to the roots of an admissible Tschirnhaus
transform, sending `α` to `T(α)`. -/
noncomputable def TschirnhausAdmissible.rootSetEquiv {f T : K[X]}
    (hT : TschirnhausAdmissible f T)
    (hs : (f.map (algebraMap K L)).Splits) :
    f.rootSet L ≃ (tschirnhausPolynomial f T).rootSet L :=
  Equiv.ofBijective _ (hT.bijOn_rootSet hs).bijective

@[simp]
theorem TschirnhausAdmissible.coe_rootSetEquiv_apply {f T : K[X]}
    (hT : TschirnhausAdmissible f T)
    (hs : (f.map (algebraMap K L)).Splits) (x : f.rootSet L) :
    (hT.rootSetEquiv hs x : L) = aeval (x : L) T := by
  rw [TschirnhausAdmissible.rootSetEquiv, Equiv.coe_ofBijective,
    (hT.bijOn_rootSet hs).mapsTo.val_restrict_apply]

/-- Applying `T` to the inverse image under the canonical root equivalence recovers the root. -/
@[simp]
theorem TschirnhausAdmissible.aeval_coe_rootSetEquiv_symm_apply {f T : K[X]}
    (hT : TschirnhausAdmissible f T)
    (hs : (f.map (algebraMap K L)).Splits)
    (y : (tschirnhausPolynomial f T).rootSet L) :
    aeval ((hT.rootSetEquiv hs).symm y : L) T = (y : L) := by
  rw [← hT.coe_rootSetEquiv_apply hs]
  exact congrArg Subtype.val ((hT.rootSetEquiv hs).apply_symm_apply y)

end Field

end Polynomial
