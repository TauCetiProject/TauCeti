/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat ring homomorphisms

A commutative square whose horizontal maps are isomorphisms transports flatness after
localizing the targets at corresponding submonoids
(`RingHom.flat_localization_comp_iff_of_ringEquiv`). Applied at corresponding primes, this lets
symmetry arguments reduce flatness of a morphism to flatness at one point.

The file also states the equational criterion for flatness for a ring homomorphism
`g : A →+* B`, without an `Algebra A B` instance
(`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq_zero`), together with its two-sided equality form
`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq`. This form applies to endomorphisms such
as Frobenius, where `B = A` already carries its own `A`-module structure. It is deduced from
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`.

## References

* [Stacks: Equational criterion for flatness](https://stacks.math.columbia.edu/tag/00HK)
-/

public section

namespace RingHom

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- A commutative square `eS ∘ f = g ∘ eR` whose horizontal maps are ring isomorphisms
transports flatness after localizing the targets at corresponding submonoids: if `M.map eS = M'`,
`T` is a localization of `S` at `M` and `T'` is a localization of `S'` at `M'`, then `S → T` after
`f` is flat exactly when `S' → T'` after `g` is. -/
theorem flat_localization_comp_iff_of_ringEquiv {T T' : Type*} [CommRing T] [CommRing T']
    [Algebra S T] [Algebra S' T'] (f : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) {M : Submonoid S} {M' : Submonoid S'}
    [IsLocalization M T] [IsLocalization M' T'] (hM : M.map eS = M') :
    ((algebraMap S T).comp f).Flat ↔ ((algebraMap S' T').comp g).Flat := by
  let e := IsLocalization.ringEquivOfRingEquiv T T' eS hM
  have he : e.toRingHom.comp ((algebraMap S T).comp f) =
      ((algebraMap S' T').comp g).comp eR.toRingHom := by
    ext x
    exact (IsLocalization.ringEquivOfRingEquiv_eq hM (f x)).trans
      (congrArg (algebraMap S' T') (RingHom.congr_fun h x))
  rw [← Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective, he,
    Flat.comp_iff_of_bijective_right eR.bijective]

/-- **Equational criterion for flatness** of a ring homomorphism: if `g : A →+* B` is flat, every
relation `∑ⱼ g (fⱼ) xⱼ = 0` in `B` is trivial, that is, `xⱼ = ∑ᵢ g (aⱼᵢ) yᵢ` for some `aⱼᵢ ∈ A` and
`yᵢ ∈ B` with `∑ⱼ fⱼ aⱼᵢ = 0` for every `i`. -/
@[stacks 00HK]
theorem Flat.exists_eq_sum_mul_of_sum_mul_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    {g : A →+* B} (hg : g.Flat) {ι : Type*} [Fintype ι] {f : ι → A} {x : ι → B}
    (h : ∑ j, g (f j) * x j = 0) :
    ∃ (k : ℕ) (a : ι → Fin k → A) (y : Fin k → B),
      (∀ j, x j = ∑ i, g (a j i) * y i) ∧ ∀ i, ∑ j, f j * a j i = 0 := by
  algebraize [g]
  obtain ⟨k, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A)
    (M := B) (f := f) (x := x) (by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h)
  exact ⟨k, a, y, fun j ↦ by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hxy j, ha⟩

private theorem sum_subtype_mul_eq_sum_mul {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (u : s → R) (v : ι → R) (w : ι → R)
    (huv : ∀ (i : ι) (hi : i ∈ s), u ⟨i, hi⟩ = v i) :
    ∑ i : s, w i.val * u i = ∑ i ∈ s, v i * w i := by
  rw [← Finset.sum_coe_sort s fun i ↦ v i * w i]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, huv i.val i.property]

/-- If `g : A →+* B` is flat and `∑ i ∈ s, b i * g (x i) = ∑ j ∈ t, b' j * g (x' j)` in `B`,
then `b` and `b'` factor through a common finite family `c : Fin k → B` via coefficients in `A`
satisfying the matching `A`-linear relations on `x` and `x'`. -/
@[stacks 00HK]
theorem Flat.exists_eq_sum_mul_of_sum_mul_eq {A B : Type*} [CommRing A] [CommRing B]
    {g : A →+* B} (hg : g.Flat) {ι κ : Type*} {s : Finset ι} {t : Finset κ}
    {b : ι → B} {b' : κ → B} {x : ι → A} {x' : κ → A}
    (hsum : ∑ i ∈ s, b i * g (x i) = ∑ j ∈ t, b' j * g (x' j)) :
    ∃ (k : ℕ) (aL : ι → Fin k → A) (aR : κ → Fin k → A) (c : Fin k → B),
      (∀ i ∈ s, b i = ∑ l : Fin k, g (aL i l) * c l) ∧
      (∀ j ∈ t, b' j = ∑ l : Fin k, g (aR j l) * c l) ∧
      (∀ l : Fin k, ∑ i ∈ s, aL i l * x i = ∑ j ∈ t, aR j l * x' j) := by
  classical
  let f : (s : Type _) ⊕ (t : Type _) → A := Sum.elim (fun i ↦ x i.val) (fun j ↦ -x' j.val)
  let v : (s : Type _) ⊕ (t : Type _) → B := Sum.elim (fun i ↦ b i.val) (fun j ↦ b' j.val)
  have hrel : ∑ u : (s : Type _) ⊕ (t : Type _), g (f u) * v u = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [f, v, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul, Finset.sum_neg_distrib]
    rw [sum_subtype_mul_eq_sum_mul s (fun i ↦ b i.val) b (fun i ↦ g (x i)) fun _ _ ↦ rfl,
      sum_subtype_mul_eq_sum_mul t (fun j ↦ b' j.val) b' (fun j ↦ g (x' j)) fun _ _ ↦ rfl,
      hsum, add_neg_cancel]
  obtain ⟨k, a, c, hvc, hga⟩ := hg.exists_eq_sum_mul_of_sum_mul_eq_zero hrel
  let aL (i : ι) (l : Fin k) : A := if hi : i ∈ s then a (Sum.inl ⟨i, hi⟩) l else 0
  let aR (j : κ) (l : Fin k) : A := if hj : j ∈ t then a (Sum.inr ⟨j, hj⟩) l else 0
  refine ⟨k, aL, aR, c, fun i hi ↦ ?_, fun j hj ↦ ?_, fun l ↦ ?_⟩
  · simpa [v, aL, hi] using hvc (Sum.inl ⟨i, hi⟩)
  · simpa [v, aR, hj] using hvc (Sum.inr ⟨j, hj⟩)
  · have hl := hga l
    rw [Fintype.sum_sum_type] at hl
    simp only [f, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at hl
    rwa [sum_subtype_mul_eq_sum_mul s (fun i ↦ a (Sum.inl i) l) (aL · l) x
        (fun _ hi ↦ by simp [aL, hi]),
      sum_subtype_mul_eq_sum_mul t (fun j ↦ a (Sum.inr j) l) (aR · l) x'
        (fun _ hj ↦ by simp [aR, hj]),
      ← sub_eq_add_neg, sub_eq_zero] at hl

end RingHom
