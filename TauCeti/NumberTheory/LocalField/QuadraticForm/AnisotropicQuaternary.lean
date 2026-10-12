/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.BrauerClass
public import TauCeti.NumberTheory.HilbertSymbol.Pfister
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Classification
import Mathlib.NumberTheory.Padics.LocalField
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation
import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo

/-!
# The anisotropic quaternary form and the quaternion division algebra over a local field

Let `K` be a nonarchimedean local field in which `2` is invertible. By the quaternary isotropy
criterion, a regular form of rank four over `K` is anisotropic exactly when its discriminant is
trivial and its local Hasse invariant is `-(-1, -1)_K`. These invariants do not depend on the form,
so by the local classification there is exactly one anisotropic regular quaternary form over `K` up
to isometry. It is the norm form `<<a, b>> = <1, -a, -b, ab>` of every quaternion division algebra
`ℍ[K,a,b]`, that is of every `ℍ[K,a,b]` with `(a, b)_K = -1`.

Two quaternion division algebras over `K` therefore have isometric norm forms. Witt cancellation of
the common summand `<1>` leaves isometric pure norm forms `<-a, -b, ab>` and `<-c, -d, cd>`, whose
Hasse invariants `[(a, b)] · [(-1, -1)]` and `[(c, d)] · [(-1, -1)]` agree. So `ℍ[K,a,b]` and
`ℍ[K,c,d]` have the same Brauer class and are isomorphic. Since the split quaternion algebras are
all isomorphic to `M₂(K)`, the Hilbert symbol `(a, b)_K` is a complete invariant of `ℍ[K,a,b]`, and
there are exactly two quaternion algebras over `K` up to isomorphism; both occur, because the
Hilbert symbol takes both values (`TauCeti.uncurry_hilbertSymbol_surjective`).

Over `ℚ_2`, where `(-1, -1) = -1`, the anisotropic quaternary form is the sum of four squares
`<1, 1, 1, 1>`, the norm form of Hamilton's quaternions.

## Main results

* `TauCeti.RegularFormClass.eq_of_rank_eq_four_of_anisotropic`: two anisotropic regular-form classes
  of rank four over `K` are equal.
* `TauCeti.RegularFormClass.anisotropic_iff_eq_pfisterFormClass_two`: if `(a, b)_K = -1`, a class of
  rank four is anisotropic exactly when it is the class of `<<a, b>>`.
* `QuadraticForm.equivalent_of_finrank_eq_four_of_anisotropic`: two anisotropic quadratic forms on
  spaces of dimension four over `K` are isometric.
* `TauCeti.QuaternionAlgebra.nonempty_algEquiv_iff_hilbertSymbol_eq`: two quaternion algebras over
  `K` are isomorphic exactly when their Hilbert symbols agree.
* `TauCeti.QuaternionAlgebra.nonempty_algEquiv_of_hilbertSymbol_eq_neg_one`: any two quaternion
  division algebras over `K` are isomorphic.
* `TauCeti.BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq`: two quaternion symbols over `K`
  have the same Brauer class exactly when their Hilbert symbols agree.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:17–63:18.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.3, Theorem 7 and its corollary.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VI, §2.
-/

public section

open scoped Quaternion

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

/-- **The anisotropic quaternary form is unique** (O'Meara 63:17, Serre IV Thm 7 cor.). Two
anisotropic regular-form classes of rank four over `K` are equal: both have trivial discriminant and
local Hasse invariant `-(-1, -1)_K`. -/
theorem eq_of_rank_eq_four_of_anisotropic {x y : RegularFormClass K} (hx : x.rank = 4)
    (hy : y.rank = 4) (hxa : x.Anisotropic) (hya : y.Anisotropic) : x = y := by
  have hinv {z : RegularFormClass K} (hz : z.rank = 4) (hza : z.Anisotropic) :
      discr z = 0 ∧ localHasse z = -hilbertSymbol (-1 : Kˣ) (-1) := by
    have h := mt (not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four hz).mpr
      (not_not.mpr hza)
    rw [not_or, not_not] at h
    exact ⟨h.1, Int.units_ne_iff_eq_neg.mp h.2⟩
  obtain ⟨hdx, hsx⟩ := hinv hx hxa
  obtain ⟨hdy, hsy⟩ := hinv hy hya
  exact eq_of_discr_eq_of_localHasse_eq (hx.trans hy.symm) (hdx.trans hdy.symm)
    (hsx.trans hsy.symm)

/-- **The anisotropic quaternary form is a norm form.** If `(a, b)_K = -1`, that is if `ℍ[K,a,b]` is
a division algebra, then a regular-form class of rank four over `K` is anisotropic exactly when it
is the class of the norm form `<<a, b>> = <1, -a, -b, ab>` of `ℍ[K,a,b]`. -/
theorem anisotropic_iff_eq_pfisterFormClass_two {x : RegularFormClass K} (hx : x.rank = 4)
    {a b : Kˣ} (hab : hilbertSymbol a b = -1) :
    x.Anisotropic ↔ x = pfisterFormClass ![a, b] := by
  have hp := (anisotropic_pfisterFormClass_two_iff_hilbertSymbol_eq_neg_one a b).mpr hab
  exact ⟨fun hxa => eq_of_rank_eq_four_of_anisotropic hx (by simp) hxa hp, fun h => h ▸ hp⟩

/-- **The norm forms of two quaternion division algebras are isometric.** If `(a, b)_K = -1` and
`(c, d)_K = -1`, then `<<a, b>> = <<c, d>>`. -/
theorem pfisterFormClass_two_eq_of_hilbertSymbol_eq_neg_one {a b c d : Kˣ}
    (hab : hilbertSymbol a b = -1) (hcd : hilbertSymbol c d = -1) :
    pfisterFormClass ![a, b] = pfisterFormClass ![c, d] :=
  (anisotropic_iff_eq_pfisterFormClass_two (by simp) hcd).mp
    ((anisotropic_pfisterFormClass_two_iff_hilbertSymbol_eq_neg_one a b).mpr hab)

end RegularFormClass

namespace BrauerGroup

/-- Two quaternion symbols over `K` with Hilbert symbol `-1` have the same Brauer class. -/
private theorem quaternionClass_eq_of_hilbertSymbol_eq_neg_one {a b c d : Kˣ}
    (hab : hilbertSymbol a b = -1) (hcd : hilbertSymbol c d = -1) :
    quaternionClass a b = quaternionClass c d := by
  -- Witt cancellation of `<1>` from the isometric norm forms leaves isometric pure norm forms
  -- `<-a, -b, ab>` and `<-c, -d, cd>`, whose Hasse invariants are `[(a, b)] · [(-1, -1)]` and
  -- `[(c, d)] · [(-1, -1)]`.
  -- `<<a, b>>` is `<1>` plus the pure norm form `<-a, -b, ab>`.
  have hsplit (a b : Kˣ) : pfisterFormClass ![a, b] =
      Quotient.mk (regularFormSetoid K) ⟨1, fun _ => 1⟩ +
        Quotient.mk (regularFormSetoid K) ⟨3, ![-a, -b, a * b]⟩ := by
    rw [pfisterFormClass_two, RegularFormClass.mk_succ_eq_mk_rankOne_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  have h := RegularFormClass.pfisterFormClass_two_eq_of_hilbertSymbol_eq_neg_one hab hcd
  rw [hsplit, hsplit] at h
  have hs := congrArg RegularFormClass.hasseInvariant (add_left_cancel h)
  rwa [RegularFormClass.hasseInvariant_mk_neg_neg_mul,
    RegularFormClass.hasseInvariant_mk_neg_neg_mul, mul_left_inj] at hs

/-- **The Brauer class of a quaternion algebra over a local field is its Hilbert symbol**: two
quaternion symbols over `K` have the same Brauer class exactly when their Hilbert symbols agree. -/
theorem quaternionClass_eq_iff_hilbertSymbol_eq (a b c d : Kˣ) :
    quaternionClass a b = quaternionClass c d ↔ hilbertSymbol a b = hilbertSymbol c d := by
  refine ⟨fun h => hilbertSymbol_eq_of_nonempty_algEquiv ((quaternionClass_eq_iff a b c d).mp h),
    fun h => ?_⟩
  have hsplit (a b : Kˣ) : quaternionClass a b = 1 ↔ hilbertSymbol a b = 1 :=
    (quaternionClass_eq_one_iff a b).trans
      (hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix a b).symm
  rcases Int.units_eq_one_or (hilbertSymbol a b) with hab | hab
  · rw [(hsplit a b).mpr hab, (hsplit c d).mpr (h ▸ hab)]
  · exact quaternionClass_eq_of_hilbertSymbol_eq_neg_one hab (h ▸ hab)

end BrauerGroup

namespace QuaternionAlgebra

/-- **Quaternion algebras over a local field are classified by the Hilbert symbol**: `ℍ[K,a,b]` and
`ℍ[K,c,d]` are isomorphic exactly when `(a, b)_K = (c, d)_K`. Since the symbol takes both values
(`TauCeti.uncurry_hilbertSymbol_surjective`), there are exactly two quaternion algebras over `K` up
to isomorphism: `M₂(K)` and the quaternion division algebra. -/
theorem nonempty_algEquiv_iff_hilbertSymbol_eq (a b c d : Kˣ) :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] ℍ[K,(c : K),(d : K)]) ↔
      hilbertSymbol a b = hilbertSymbol c d :=
  (BrauerGroup.quaternionClass_eq_iff a b c d).symm.trans
    (BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq a b c d)

/-- **The quaternion division algebra over a local field is unique**: if `(a, b)_K = -1` and
`(c, d)_K = -1`, then `ℍ[K,a,b]` and `ℍ[K,c,d]` are isomorphic. -/
theorem nonempty_algEquiv_of_hilbertSymbol_eq_neg_one {a b c d : Kˣ}
    (hab : hilbertSymbol a b = -1) (hcd : hilbertSymbol c d = -1) :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] ℍ[K,(c : K),(d : K)]) :=
  (nonempty_algEquiv_iff_hilbertSymbol_eq a b c d).mpr (hab.trans hcd.symm)

end QuaternionAlgebra

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **The anisotropic quaternary form is unique** (O'Meara 63:17, Serre IV Thm 7 cor.). Two
anisotropic quadratic forms on spaces of dimension four over `K` are isometric. -/
theorem equivalent_of_finrank_eq_four_of_anisotropic {Q : QuadraticForm K V}
    {R : QuadraticForm K W} (hV : Module.finrank K V = 4) (hW : Module.finrank K W = 4)
    (hQ : Q.Anisotropic) (hR : R.Anisotropic) : Q.Equivalent R := by
  rw [← formClass_eq_iff Q hQ.nondegenerate R hR.nondegenerate]
  exact RegularFormClass.eq_of_rank_eq_four_of_anisotropic (by rwa [rank_formClass])
    (by rwa [rank_formClass]) ((anisotropic_formClass Q _).mpr hQ)
    ((anisotropic_formClass R _).mpr hR)

end QuadraticForm

/-- **Worked example.** Since `(-1, -1)_{ℚ_2} = -1`, a regular-form class of rank four over `ℚ_2` is
anisotropic exactly when it is the class of the sum of four squares `<1, 1, 1, 1> = <<-1, -1>>`, the
norm form of Hamilton's quaternions. -/
example {x : TauCeti.RegularFormClass ℚ_[2]} (hx : x.rank = 4) :
    x.Anisotropic ↔ x = Quotient.mk (TauCeti.regularFormSetoid ℚ_[2]) ⟨4, fun _ => 1⟩ := by
  have hw : (![1, -(-1), -(-1), -1 * -1] : Fin 4 → ℚ_[2]ˣ) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp
  rw [TauCeti.RegularFormClass.anisotropic_iff_eq_pfisterFormClass_two hx
    TauCeti.hilbertSymbol_neg_one_neg_one_padicTwo, TauCeti.pfisterFormClass_two, hw]
