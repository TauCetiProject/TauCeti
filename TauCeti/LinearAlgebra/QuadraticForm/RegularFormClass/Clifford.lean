/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import TauCeti.Algebra.BrauerGroup.Splitting
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# The Clifford invariant of a regular quadratic form

Over a field `K` in which two is invertible, a regular quadratic form `q` of rank `n` on a
finite-dimensional space determines a central simple `K`-algebra: its Clifford algebra `C(q)` when
`n` is even, and its even Clifford algebra `C₀(q)` when `n` is odd. The **Clifford invariant**
(or Witt invariant) `c(q)` is the Brauer class of that algebra (Lam V.3.12).

The invariant is defined on `TauCeti.RegularFormClass`, through the Clifford algebra of a diagonal
presentation. It does not depend on the presentation, because an isometry of quadratic forms
induces an isomorphism of Clifford algebras and of their even subalgebras. Its value on the class
of an arbitrary regular form is the Brauer class of any central simple algebra isomorphic to the
Clifford algebra, or the even Clifford algebra, of that form
(`TauCeti.RegularFormClass.cliffordInvariant_formClass_of_even` and
`TauCeti.RegularFormClass.cliffordInvariant_formClass_of_odd`).

Every Clifford invariant is `2`-torsion, because the reversion of a Clifford algebra identifies it
with its opposite algebra, and in odd rank the even Clifford algebra is itself a Clifford algebra in
one lower rank. In ranks at most two the Clifford and Hasse invariants agree: the Clifford algebra
of `⟨a, b⟩` is the quaternion algebra `ℍ[K, a, b]`, while in ranks `0` and `1` the algebra is `K`.

## Main definitions

* `TauCeti.RegularFormClass.cliffordInvariant`: the Clifford invariant of an isometry class of
  regular quadratic forms.

## Main results

* `TauCeti.RegularFormClass.cliffordInvariant_mk_of_even`,
  `TauCeti.RegularFormClass.cliffordInvariant_mk_of_odd`: its value on a diagonal presentation.
* `TauCeti.RegularFormClass.cliffordInvariant_formClass_of_even`,
  `TauCeti.RegularFormClass.cliffordInvariant_formClass_of_odd`: its value on the class of a
  regular form on any finite-dimensional space.
* `TauCeti.BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra`: a central simple algebra
  isomorphic to a Clifford algebra has a self-inverse Brauer class.
* `TauCeti.RegularFormClass.cliffordInvariant_sq`: the invariant is `2`-torsion.
* `TauCeti.RegularFormClass.cliffordInvariant_eq_one_of_rank_le_one`: it is trivial in ranks `0`
  and `1`.
* `TauCeti.RegularFormClass.cliffordInvariant_mk_binary`: `c⟨a, b⟩ = [(a, b)]`.
* `TauCeti.RegularFormClass.cliffordInvariant_eq_hasseInvariant_of_rank_le_two`: in ranks at most
  two the Clifford invariant is the Hasse invariant; in particular the hyperbolic plane has trivial
  invariant (`TauCeti.RegularFormClass.cliffordInvariant_hyperbolicClass`).

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, Theorems 2.4 and 2.5 and Definition 3.12.
-/

public section

open Module QuadraticMap
open scoped Quaternion

namespace TauCeti

universe u v

/-- **A central simple algebra isomorphic to a Clifford algebra has a self-inverse Brauer class**:
the reversion identifies a Clifford algebra with its opposite algebra. No hypothesis on the form
is needed beyond the central simplicity carried by `A`. -/
theorem BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra {K : Type u} [Field K]
    {W : Type*} [AddCommGroup W] [Module K W] {P : QuadraticForm K W} (A : CSA.{u, u} K)
    (e : CliffordAlgebra P ≃ₐ[K] A) : (BrauerGroup.mk A)⁻¹ = BrauerGroup.mk A :=
  BrauerGroup.inv_mk_eq_mk_of_algEquiv_op
    (e.symm.trans (CliffordAlgebra.reverseOpEquiv.trans (AlgEquiv.op e)))

namespace RegularFormClass

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The central simple algebra of a presentation -/

/-- The Clifford algebra of an even-rank diagonal presentation, as a central simple algebra. -/
private noncomputable abbrev cliffordCSA (p : RegularFormPresentation K) (h : Even p.1) : CSA K :=
  haveI := CliffordAlgebra.isCentral_of_even_finrank (nondegenerate_presentedForm p)
    (by simpa using h)
  haveI := CliffordAlgebra.isSimpleRing_of_even_finrank (nondegenerate_presentedForm p)
    (by simpa using h)
  CSA.of K (CliffordAlgebra (presentedForm p))

/-- The even Clifford algebra of an odd-rank diagonal presentation, as a central simple
algebra. -/
private noncomputable abbrev evenCliffordCSA (p : RegularFormPresentation K) (h : ¬Even p.1) :
    CSA K :=
  haveI := CliffordAlgebra.isCentral_even_of_odd_finrank (nondegenerate_presentedForm p)
    (by simpa [Nat.not_even_iff_odd] using h)
  haveI := CliffordAlgebra.isSimpleRing_even_of_odd_finrank (nondegenerate_presentedForm p)
    (by simpa [Nat.not_even_iff_odd] using h)
  CSA.of K (CliffordAlgebra.even (presentedForm p))

/-- The Brauer class of the central simple algebra that the parity of the rank selects. -/
private noncomputable def presentationCliffordClass (p : RegularFormPresentation K) :
    BrauerGroup K :=
  if h : Even p.1 then BrauerGroup.mk (cliffordCSA p h) else BrauerGroup.mk (evenCliffordCSA p h)

/-- Isometric presentations select isomorphic algebras. -/
private theorem presentationCliffordClass_eq_of_equiv {p q : RegularFormPresentation K}
    (hpq : p ≈ q) : presentationCliffordClass p = presentationCliffordClass q := by
  obtain ⟨e⟩ := hpq
  have hn : p.1 = q.1 := fst_eq_of_presentedForm_equivalent ⟨e⟩
  by_cases h : Even p.1
  · rw [presentationCliffordClass, presentationCliffordClass, dite_eq_left h,
      dite_eq_left (hn ▸ h)]
    exact BrauerGroup.mk_eq_mk_of_algEquiv (CliffordAlgebra.equivOfIsometry e)
  · rw [presentationCliffordClass, presentationCliffordClass, dite_eq_right h,
      dite_eq_right (hn ▸ h)]
    exact BrauerGroup.mk_eq_mk_of_algEquiv (CliffordAlgebra.evenEquivOfIsometry e)

/-! ### The Clifford invariant -/

/-- **The Clifford invariant of an isometry class of regular quadratic forms**: for a diagonal
presentation `q` of rank `n`, the Brauer class of the Clifford algebra `C(q)` when `n` is even and
of the even Clifford algebra `C₀(q)` when `n` is odd (Lam V.3.12). It does not depend on the
presentation. -/
noncomputable def cliffordInvariant : RegularFormClass K → BrauerGroup K :=
  Quotient.lift presentationCliffordClass fun _ _ => presentationCliffordClass_eq_of_equiv

/-- On a presentation of even rank, the Clifford invariant is the Brauer class of any central
simple algebra isomorphic to the Clifford algebra of the presented form. -/
theorem cliffordInvariant_mk_of_even (p : RegularFormPresentation K) (h : Even p.1)
    (A : CSA.{u, u} K) (e : CliffordAlgebra (presentedForm p) ≃ₐ[K] A) :
    cliffordInvariant (Quotient.mk (regularFormSetoid K) p) = BrauerGroup.mk A := by
  rw [cliffordInvariant, Quotient.lift_mk, presentationCliffordClass, dite_eq_left h]
  exact BrauerGroup.mk_eq_mk_of_algEquiv e

/-- On a presentation of odd rank, the Clifford invariant is the Brauer class of any central
simple algebra isomorphic to the even Clifford algebra of the presented form. -/
theorem cliffordInvariant_mk_of_odd (p : RegularFormPresentation K) (h : Odd p.1)
    (A : CSA.{u, u} K) (e : CliffordAlgebra.even (presentedForm p) ≃ₐ[K] A) :
    cliffordInvariant (Quotient.mk (regularFormSetoid K) p) = BrauerGroup.mk A := by
  rw [cliffordInvariant, Quotient.lift_mk, presentationCliffordClass,
    dite_eq_right (Nat.not_even_iff_odd.mpr h)]
  exact BrauerGroup.mk_eq_mk_of_algEquiv e

section formClass

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The Clifford invariant of a regular form of even dimension** is the Brauer class of any
central simple algebra isomorphic to its Clifford algebra. -/
theorem cliffordInvariant_formClass_of_even (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (h : Even (finrank K V)) (A : CSA.{u, u} K) (e : CliffordAlgebra Q ≃ₐ[K] A) :
    cliffordInvariant (formClass Q hQ) = BrauerGroup.mk A := by
  obtain ⟨p, ⟨f⟩⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p ⟨f⟩]
  have hp : finrank K V = p.1 := by simpa using f.toLinearEquiv.finrank_eq
  exact cliffordInvariant_mk_of_even p (hp ▸ h) A
    ((CliffordAlgebra.equivOfIsometry f.symm).trans e)

/-- **The Clifford invariant of a regular form of odd dimension** is the Brauer class of any
central simple algebra isomorphic to its even Clifford algebra. -/
theorem cliffordInvariant_formClass_of_odd (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (h : Odd (finrank K V)) (A : CSA.{u, u} K) (e : CliffordAlgebra.even Q ≃ₐ[K] A) :
    cliffordInvariant (formClass Q hQ) = BrauerGroup.mk A := by
  obtain ⟨p, ⟨f⟩⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p ⟨f⟩]
  have hp : finrank K V = p.1 := by simpa using f.toLinearEquiv.finrank_eq
  exact cliffordInvariant_mk_of_odd p (hp ▸ h) A
    ((CliffordAlgebra.evenEquivOfIsometry f.symm).trans e)

end formClass

/-! ### Two-torsion -/

/-- **The Clifford invariant is `2`-torsion.** -/
theorem cliffordInvariant_sq (x : RegularFormClass K) : cliffordInvariant x ^ 2 = 1 := by
  suffices h : (cliffordInvariant x)⁻¹ = cliffordInvariant x by
    rw [_root_.sq, ← inv_mul_cancel (cliffordInvariant x), h]
  induction x using Quotient.inductionOn with
  | h p =>
    by_cases hp : Even p.1
    · rw [cliffordInvariant_mk_of_even p hp (cliffordCSA p hp) AlgEquiv.refl]
      exact BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra _ AlgEquiv.refl
    · have hodd := Nat.not_even_iff_odd.mp hp
      rw [cliffordInvariant_mk_of_odd p hodd (evenCliffordCSA p hp) AlgEquiv.refl]
      -- In odd rank the even Clifford algebra is itself a Clifford algebra.
      obtain ⟨n, P, -, -, ⟨e⟩⟩ := CliffordAlgebra.exists_nonempty_algEquiv_even_of_odd_finrank
        (nondegenerate_presentedForm p) (by simpa using hodd)
      exact BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra (evenCliffordCSA p hp) e.symm

/-! ### Low rank -/

/-- The Clifford invariant is trivial in ranks `0` and `1`, where the selected algebra is `K`. -/
theorem cliffordInvariant_eq_one_of_rank_le_one {x : RegularFormClass K} (hx : x.rank ≤ 1) :
    cliffordInvariant x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    have hn : n ≤ 1 := by simpa using hx
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rw [cliffordInvariant_mk_of_even _ Even.zero (cliffordCSA _ Even.zero) AlgEquiv.refl]
      exact BrauerGroup.mk_eq_one_of_finrank_eq_one _ (by simp [CliffordAlgebra.finrank_eq_two_pow])
    · have h1 : ¬Even 1 := Nat.not_even_one
      rw [cliffordInvariant_mk_of_odd _ odd_one (evenCliffordCSA _ h1) AlgEquiv.refl]
      exact BrauerGroup.mk_eq_one_of_finrank_eq_one _ (by simp [CliffordAlgebra.finrank_even])

/-- The zero class has trivial Clifford invariant. -/
@[simp]
theorem cliffordInvariant_zero : cliffordInvariant (0 : RegularFormClass K) = 1 :=
  cliffordInvariant_eq_one_of_rank_le_one (by simp)

/-- The unit class `⟨1⟩` has trivial Clifford invariant. -/
@[simp]
theorem cliffordInvariant_one : cliffordInvariant (1 : RegularFormClass K) = 1 :=
  cliffordInvariant_eq_one_of_rank_le_one rank_one.le

/-- **The Clifford invariant of a binary form `⟨a, b⟩` is the quaternion symbol `[(a, b)]`**: the
Clifford algebra of `⟨a, b⟩` is the quaternion algebra `ℍ[K, a, b]`. -/
@[simp]
theorem cliffordInvariant_mk_binary (a b : Kˣ) :
    cliffordInvariant (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      BrauerGroup.quaternionClass a b := by
  let f : (presentedForm (⟨2, ![a, b]⟩ : RegularFormPresentation K)).IsometryEquiv
      (CliffordAlgebraQuaternion.Q (a : K) b) :=
    ⟨LinearEquiv.finTwoArrow K K, fun v => by
      simp [presentedForm_two, weightedSumSquares_apply, CliffordAlgebraQuaternion.Q_apply]⟩
  rw [BrauerGroup.quaternionClass_def]
  exact cliffordInvariant_mk_of_even _ even_two _
    ((CliffordAlgebra.equivOfIsometry f).trans CliffordAlgebraQuaternion.equiv)

/-- **In ranks at most two the Clifford invariant is the Hasse invariant.** This is the low-rank
case of Lam V.3.20, whose correction terms vanish for `n ≤ 2`. -/
theorem cliffordInvariant_eq_hasseInvariant_of_rank_le_two {x : RegularFormClass K}
    (hx : x.rank ≤ 2) : cliffordInvariant x = hasseInvariant x := by
  rcases Nat.lt_or_ge x.rank 2 with h | h
  · rw [cliffordInvariant_eq_one_of_rank_le_one (by omega),
      hasseInvariant_eq_one_of_rank_le_one (by omega)]
  · induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨n, w⟩ := p
      obtain rfl : n = 2 := le_antisymm (by simpa using hx) (by simpa using h)
      have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
      rw [hw, cliffordInvariant_mk_binary, hasseInvariant_mk_binary]

/-- The hyperbolic plane has trivial Clifford invariant: its Clifford algebra `ℍ[K, 1, -1]` is
split. -/
@[simp]
theorem cliffordInvariant_hyperbolicClass : cliffordInvariant (hyperbolicClass K) = 1 := by
  rw [hyperbolicClass_def, cliffordInvariant_mk_binary, BrauerGroup.quaternionClass_one_left]

end RegularFormClass

end TauCeti
