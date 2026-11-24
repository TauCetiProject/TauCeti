/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.BaseChange
public import TauCeti.NumberTheory.HilbertSymbol.Archimedean
public import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Ramification of a quaternion algebra over a number field

Let `F` be a number field and `a, b ∈ Fˣ`. The quaternion algebra `B = ℍ[F,a,b]` is
**ramified** at a place `v` of `F` when its completion `B_v = ℍ[F_v,a,b]` is not isomorphic to
the matrix algebra `M₂(F_v)`, equivalently when it is a division algebra. By the splitting
criterion this happens exactly when the Hilbert symbol `(a, b)_v` of the images of `a` and `b`
in `F_v` is `-1`, and this file takes that symbol as the definition:

* `TauCeti.QuaternionAlgebra.IsRamifiedAt a b v` for a finite place `v`, read in the completion
  `v.adicCompletion F`;
* `TauCeti.QuaternionAlgebra.IsRamifiedAtReal a b w` for a real place `w`, read in `ℝ`, where it
  says that `a` and `b` are both negative at `w`;
* `TauCeti.QuaternionAlgebra.IsRamifiedAtPrime a b p` over `ℚ`, read in `ℚ_p`, which agrees with
  `IsRamifiedAt` at the finite place of `ℚ` above `p`.

Complex places are never ramified, because every quaternion algebra over `ℂ` is split, so these
predicates cover all the places at which `B` can ramify.

The predicates are compared with the local splitting and division statements, and they depend
only on `B` up to isomorphism: they are unchanged when `a` or `b` is multiplied by a square, when
`a` and `b` are exchanged, or when `(a, b)` is replaced by the parameters of any isomorphic
symbol algebra.

The finite ramification places form a finite set
`TauCeti.QuaternionAlgebra.ramifiedFinitePlaces a b`, contained in the set of places at which
`2`, `a` or `b` is not a unit. With the real ramification places
`TauCeti.QuaternionAlgebra.ramifiedRealPlaces a b`, Hilbert's product formula shows that the total
number of ramified places is even.

## Main definitions

* `TauCeti.QuaternionAlgebra.IsRamifiedAt`, `TauCeti.QuaternionAlgebra.IsRamifiedAtReal`,
  `TauCeti.QuaternionAlgebra.IsRamifiedAtPrime`: ramification at a finite place, at a real place,
  and at a rational prime.
* `TauCeti.QuaternionAlgebra.ramifiedFinitePlaces`, `TauCeti.QuaternionAlgebra.ramifiedRealPlaces`:
  the finite sets of finite and of real ramified places.

## Main results

* `TauCeti.QuaternionAlgebra.isRamifiedAt_iff_isEmpty_algEquiv_matrix`,
  `TauCeti.QuaternionAlgebra.isRamifiedAt_iff_forall_isUnit`: ramification at a finite place is
  the failure of `B_v` to split, and is `B_v` being a division algebra; the real analogues are
  `isRamifiedAtReal_iff_isEmpty_algEquiv_matrix` and `isRamifiedAtReal_iff_forall_isUnit`.
* `TauCeti.QuaternionAlgebra.isRamifiedAtReal_iff`: `B` is ramified at a real place exactly when
  `a` and `b` are both negative there.
* `TauCeti.QuaternionAlgebra.isRamifiedAt_iff_of_nonempty_algEquiv`: isomorphic symbol algebras
  have the same ramified places.
* `TauCeti.QuaternionAlgebra.not_isRamifiedAt_of_valuation_eq_one`: `B` is unramified at a finite
  place at which `2`, `a` and `b` are units.
* `TauCeti.QuaternionAlgebra.even_card_ramifiedFinitePlaces_add_card_ramifiedRealPlaces`: the
  number of ramified places is even.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021),
  Chapter 14.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §2.
-/

public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped Quaternion

namespace TauCeti.QuaternionAlgebra

variable {F : Type*} [Field F]

/-! ### Real places -/

section Real

variable (a b : Fˣ)

/-- The quaternion algebra `ℍ[F,a,b]` is **ramified at the real place `w`** when the real Hilbert
symbol of the images of `a` and `b` under `w` is `-1`, that is, when `ℍ[ℝ,a,b]` is not split. -/
def IsRamifiedAtReal (w : {w : InfinitePlace F // w.IsReal}) : Prop :=
  hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1

variable {a b}

/-- Unfolds `IsRamifiedAtReal` to the real Hilbert symbol. -/
theorem isRamifiedAtReal_def {w : {w : InfinitePlace F // w.IsReal}} :
    IsRamifiedAtReal a b w ↔ hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 :=
  Iff.rfl

/-- `ℍ[F,a,b]` is unramified at a real place exactly when the real Hilbert symbol is `1`. -/
theorem not_isRamifiedAtReal_iff {w : {w : InfinitePlace F // w.IsReal}} :
    ¬IsRamifiedAtReal a b w ↔ hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 := by
  rw [isRamifiedAtReal_def, ← Int.units_ne_iff_eq_neg, not_not]

/-- `ℍ[F,a,b]` is ramified at a real place `w` exactly when `a` and `b` are both negative at
`w`. -/
theorem isRamifiedAtReal_iff {w : {w : InfinitePlace F // w.IsReal}} :
    IsRamifiedAtReal a b w ↔
      embedding_of_isReal w.property (a : F) < 0 ∧ embedding_of_isReal w.property (b : F) < 0 := by
  rw [isRamifiedAtReal_def, hilbertSymbol_real_eq_neg_one_iff, unitAtRealPlace_apply,
    unitAtRealPlace_apply]

/-- `ℍ[F,a,b]` is ramified at a real place `w` exactly when `ℍ[ℝ,a,b]`, its completion at `w`,
is not isomorphic to `M₂(ℝ)`. -/
theorem isRamifiedAtReal_iff_isEmpty_algEquiv_matrix {w : {w : InfinitePlace F // w.IsReal}} :
    IsRamifiedAtReal a b w ↔
      IsEmpty (ℍ[ℝ,embedding_of_isReal w.property (a : F),embedding_of_isReal w.property (b : F)]
        ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [← not_nonempty_iff, ← unitAtRealPlace_apply, ← unitAtRealPlace_apply,
    ← hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix, ← not_isRamifiedAtReal_iff, not_not]

/-- `ℍ[F,a,b]` is ramified at a real place `w` exactly when `ℍ[ℝ,a,b]`, its completion at `w`,
is a division algebra. -/
theorem isRamifiedAtReal_iff_forall_isUnit {w : {w : InfinitePlace F // w.IsReal}} :
    IsRamifiedAtReal a b w ↔
      ∀ x : ℍ[ℝ,embedding_of_isReal w.property (a : F),embedding_of_isReal w.property (b : F)],
        x ≠ 0 → IsUnit x := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [← unitAtRealPlace_apply, ← unitAtRealPlace_apply,
    ← hilbertSymbol_eq_neg_one_iff_forall_isUnit,
    isRamifiedAtReal_def]

/-- Isomorphic symbol algebras over `F` are ramified at the same real places. -/
theorem isRamifiedAtReal_iff_of_nonempty_algEquiv {c d : Fˣ}
    (h : Nonempty (ℍ[F,(a : F),(b : F)] ≃ₐ[F] ℍ[F,(c : F),(d : F)]))
    (w : {w : InfinitePlace F // w.IsReal}) :
    IsRamifiedAtReal a b w ↔ IsRamifiedAtReal c d w := by
  let : Algebra F ℝ := (embedding_of_isReal w.property).toAlgebra
  have h' := nonempty_algEquiv_baseChangeTwoParams (S := ℝ) h
  rw [RingHom.algebraMap_toAlgebra, ← unitAtRealPlace_apply, ← unitAtRealPlace_apply,
    ← unitAtRealPlace_apply, ← unitAtRealPlace_apply] at h'
  rw [isRamifiedAtReal_def, isRamifiedAtReal_def, hilbertSymbol_eq_of_nonempty_algEquiv h']

/-- Exchanging the two parameters does not change the real ramification. -/
theorem isRamifiedAtReal_comm (w : {w : InfinitePlace F // w.IsReal}) :
    IsRamifiedAtReal a b w ↔ IsRamifiedAtReal b a w :=
  isRamifiedAtReal_iff_of_nonempty_algEquiv ⟨_root_.QuaternionAlgebra.swapEquiv _ _⟩ w

/-- The real ramification depends only on the square classes of the parameters. -/
theorem isRamifiedAtReal_congr_sq {a' b' : Fˣ} (ha : IsSquare (a * a')) (hb : IsSquare (b * b'))
    (w : {w : InfinitePlace F // w.IsReal}) :
    IsRamifiedAtReal a b w ↔ IsRamifiedAtReal a' b' w := by
  rw [isRamifiedAtReal_def, isRamifiedAtReal_def, hilbertSymbol_congr_sq _ _ _ _
    (by simpa only [map_mul] using ha.map (unitAtRealPlace w))
    (by simpa only [map_mul] using hb.map (unitAtRealPlace w))]

end Real

/-! ### Finite places -/

section Finite

variable [NumberField F] (a b : Fˣ)

/-- The quaternion algebra `ℍ[F,a,b]` is **ramified at the finite place `v`** when the Hilbert
symbol of the images of `a` and `b` in the completion `F_v` is `-1`, that is, when `ℍ[F_v,a,b]`
is not split. -/
def IsRamifiedAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = -1

variable {a b}

/-- Unfolds `IsRamifiedAt` to the Hilbert symbol over the completion. -/
theorem isRamifiedAt_def {v : HeightOneSpectrum (𝓞 F)} :
    IsRamifiedAt a b v ↔ hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = -1 :=
  Iff.rfl

/-- `ℍ[F,a,b]` is unramified at a finite place exactly when the local Hilbert symbol is `1`. -/
theorem not_isRamifiedAt_iff {v : HeightOneSpectrum (𝓞 F)} :
    ¬IsRamifiedAt a b v ↔ hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 := by
  rw [isRamifiedAt_def, ← Int.units_ne_iff_eq_neg, not_not]

/-- `ℍ[F,a,b]` is ramified at a finite place `v` exactly when `ℍ[F_v,a,b]`, its completion at
`v`, is not isomorphic to `M₂(F_v)`. -/
theorem isRamifiedAt_iff_isEmpty_algEquiv_matrix {v : HeightOneSpectrum (𝓞 F)} :
    IsRamifiedAt a b v ↔
      IsEmpty (ℍ[v.adicCompletion F,algebraMap F _ (a : F),algebraMap F _ (b : F)]
        ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  let : Invertible (2 : v.adicCompletion F) := invertibleOfNonzero two_ne_zero
  rw [← not_nonempty_iff, ← v.unitAtFinitePlace_apply, ← v.unitAtFinitePlace_apply,
    ← hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix, ← not_isRamifiedAt_iff, not_not]

/-- `ℍ[F,a,b]` is ramified at a finite place `v` exactly when `ℍ[F_v,a,b]`, its completion at
`v`, is a division algebra. -/
theorem isRamifiedAt_iff_forall_isUnit {v : HeightOneSpectrum (𝓞 F)} :
    IsRamifiedAt a b v ↔
      ∀ x : ℍ[v.adicCompletion F,algebraMap F _ (a : F),algebraMap F _ (b : F)],
        x ≠ 0 → IsUnit x := by
  let : Invertible (2 : v.adicCompletion F) := invertibleOfNonzero two_ne_zero
  rw [← v.unitAtFinitePlace_apply, ← v.unitAtFinitePlace_apply,
    ← hilbertSymbol_eq_neg_one_iff_forall_isUnit, isRamifiedAt_def]

/-- `ℍ[F,a,b]` is ramified at a finite place `v` exactly when the norm form of `ℍ[F_v,a,b]` is
anisotropic. -/
theorem isRamifiedAt_iff_anisotropic_normForm {v : HeightOneSpectrum (𝓞 F)} :
    IsRamifiedAt a b v ↔
      (_root_.QuaternionAlgebra.normForm (algebraMap F (v.adicCompletion F) (a : F)) 0
        (algebraMap F _ (b : F))).Anisotropic := by
  rw [_root_.QuaternionAlgebra.anisotropic_normForm_iff, isRamifiedAt_iff_forall_isUnit]

/-- Isomorphic symbol algebras over `F` are ramified at the same finite places. -/
theorem isRamifiedAt_iff_of_nonempty_algEquiv {c d : Fˣ}
    (h : Nonempty (ℍ[F,(a : F),(b : F)] ≃ₐ[F] ℍ[F,(c : F),(d : F)]))
    (v : HeightOneSpectrum (𝓞 F)) :
    IsRamifiedAt a b v ↔ IsRamifiedAt c d v := by
  have h' := nonempty_algEquiv_baseChangeTwoParams (S := v.adicCompletion F) h
  rw [← v.unitAtFinitePlace_apply a, ← v.unitAtFinitePlace_apply b, ← v.unitAtFinitePlace_apply c,
    ← v.unitAtFinitePlace_apply d] at h'
  rw [isRamifiedAt_def, isRamifiedAt_def, hilbertSymbol_eq_of_nonempty_algEquiv h']

/-- Exchanging the two parameters does not change the ramification at a finite place. -/
theorem isRamifiedAt_comm (v : HeightOneSpectrum (𝓞 F)) :
    IsRamifiedAt a b v ↔ IsRamifiedAt b a v :=
  isRamifiedAt_iff_of_nonempty_algEquiv ⟨_root_.QuaternionAlgebra.swapEquiv _ _⟩ v

/-- The ramification at a finite place depends only on the square classes of the parameters. -/
theorem isRamifiedAt_congr_sq {a' b' : Fˣ} (ha : IsSquare (a * a')) (hb : IsSquare (b * b'))
    (v : HeightOneSpectrum (𝓞 F)) :
    IsRamifiedAt a b v ↔ IsRamifiedAt a' b' v := by
  rw [isRamifiedAt_def, isRamifiedAt_def, hilbertSymbol_congr_sq _ _ _ _
    (by simpa only [map_mul] using ha.map v.unitAtFinitePlace)
    (by simpa only [map_mul] using hb.map v.unitAtFinitePlace)]

/-- `ℍ[F,a,b]` is unramified at a finite place at which `2`, `a` and `b` are units. -/
theorem not_isRamifiedAt_of_valuation_eq_one {v : HeightOneSpectrum (𝓞 F)}
    (h2 : v.valuation F 2 = 1) (ha : v.valuation F a = 1) (hb : v.valuation F b = 1) :
    ¬IsRamifiedAt a b v :=
  not_isRamifiedAt_iff.mpr (hilbertSymbol_unitAtFinitePlace_eq_one h2 ha hb)

variable (a b)

/-- The finite places at which `ℍ[F,a,b]` is ramified are exactly the places at which the
localized Hilbert symbol of `a` and `b` is not `1`: the multiplicative support of that symbol. -/
theorem setOf_isRamifiedAt_eq_mulSupport :
    {v | IsRamifiedAt a b v} =
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  ext v
  rw [Set.mem_ofPred_eq, Function.mem_mulSupport, Int.units_ne_iff_eq_neg, isRamifiedAt_def]

/-- A quaternion algebra over a number field is ramified at only finitely many finite places. -/
theorem finite_setOf_isRamifiedAt : {v | IsRamifiedAt a b v}.Finite := by
  rw [setOf_isRamifiedAt_eq_mulSupport]
  exact hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace a b

/-- The finite set of finite places at which `ℍ[F,a,b]` is ramified. -/
def ramifiedFinitePlaces : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_setOf_isRamifiedAt a b).toFinset

variable {a b}

@[simp]
theorem mem_ramifiedFinitePlaces {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ ramifiedFinitePlaces a b ↔ IsRamifiedAt a b v := by
  rw [ramifiedFinitePlaces, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

end Finite

/-! ### The parity of the number of ramified places -/

section Parity

variable (a b : Fˣ)

open Classical in
/-- The finite set of real places at which `ℍ[F,a,b]` is ramified. -/
def ramifiedRealPlaces [NumberField F] : Finset {w : InfinitePlace F // w.IsReal} :=
  {w | IsRamifiedAtReal a b w}

variable {a b}

@[simp]
theorem mem_ramifiedRealPlaces [NumberField F] {w : {w : InfinitePlace F // w.IsReal}} :
    w ∈ ramifiedRealPlaces a b ↔ IsRamifiedAtReal a b w := by
  classical
  rw [ramifiedRealPlaces, Finset.mem_filter, and_iff_right (Finset.mem_univ w)]

variable [NumberField F] (a b)

/-- **The number of ramified places is even.** A quaternion algebra over a number field is
ramified at an even number of places, counting the finite and the real ones; this is Hilbert's
product formula `∏_v (a, b)_v = 1`. -/
theorem even_card_ramifiedFinitePlaces_add_card_ramifiedRealPlaces :
    Even ((ramifiedFinitePlaces a b).card + (ramifiedRealPlaces a b).card) := by
  classical
  have hfin : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b)) =
        (-1) ^ (ramifiedFinitePlaces a b).card := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ramifiedFinitePlaces a b) fun v hv ↦ by
        rw [← setOf_isRamifiedAt_eq_mulSupport] at hv
        exact mem_ramifiedFinitePlaces.mpr hv,
      ← Finset.prod_const]
    exact Finset.prod_congr rfl fun v hv ↦ mem_ramifiedFinitePlaces.mp hv
  have hreal : (∏ w : {w : InfinitePlace F // w.IsReal},
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b)) =
        (-1) ^ (ramifiedRealPlaces a b).card := by
    rw [← Finset.prod_subset (Finset.subset_univ (ramifiedRealPlaces a b)) fun w _ hw ↦
        not_isRamifiedAtReal_iff.mp (mt mem_ramifiedRealPlaces.mpr hw),
      ← Finset.prod_const]
    exact Finset.prod_congr rfl fun w hw ↦ mem_ramifiedRealPlaces.mp hw
  have h := hilbertSymbol_productFormula a b
  rwa [hfin, hreal, ← pow_add, neg_one_pow_eq_one_iff_even (by decide)] at h

end Parity

/-! ### Rational primes -/

section Rat

variable (a b : ℚˣ)

/-- The quaternion algebra `ℍ[ℚ,a,b]` is **ramified at the prime `p`** when the Hilbert symbol of
`a` and `b` over `ℚ_p` is `-1`, that is, when `ℍ[ℚ_p,a,b]` is not split. -/
def IsRamifiedAtPrime (p : ℕ) [Fact p.Prime] : Prop :=
  hilbertSymbol (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom a)
    (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom b) = -1

variable {a b}

/-- Unfolds `IsRamifiedAtPrime` to the Hilbert symbol over `ℚ_p`. -/
theorem isRamifiedAtPrime_def {p : ℕ} [Fact p.Prime] :
    IsRamifiedAtPrime a b p ↔
      hilbertSymbol (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom a)
        (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom b) = -1 :=
  Iff.rfl

/-- Ramification of `ℍ[ℚ,a,b]` at a prime `p` is ramification at the finite place of `ℚ`
above `p`. -/
theorem isRamifiedAtPrime_iff_isRamifiedAt (p : ℕ) [hp : Fact p.Prime] :
    IsRamifiedAtPrime a b p ↔
      IsRamifiedAt a b ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) := by
  rw [isRamifiedAtPrime_def, isRamifiedAt_def, hilbertSymbol_unitAtFinitePlace_rat ⟨p, hp.out⟩]

end Rat

end TauCeti.QuaternionAlgebra
