/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Real
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Realization
public import TauCeti.NumberTheory.QuadraticForm.Global.Invariants
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.NumberTheory.HilbertSymbol.Archimedean

/-!
# Local forms attached to an admissible system of invariants

Let `I` be a system of local invariants of rank `n` over a number field `K`: a global
discriminant `d`, a Hasse sign `s_v` at each finite place and a positive index `p_w` at each real
place. A family of regular quadratic forms `U_v` over the completions `K_v` and `R_w` over `ℝ`,
all on the coordinate space of dimension `n`, *realizes `I` locally* when `U_v` has discriminant
the image of `d` in `K_v` and local Hasse invariant `s_v`, and `R_w` has positive index `p_w`.

The main theorem is that an admissible system is realized locally. At a finite place this is the
local realization theorem `TauCeti.RegularFormClass.exists_of_realization`: the two exceptions
it carries, rank one with `s_v = -1` and rank two with `d_v = [-1]` and `s_v = -1`, are exactly the
small-rank conditions of admissibility. At a real place the form is a sum of `p_w` squares minus
`n - p_w` squares, and its discriminant `(-1)^(n - p_w)` is the image of `d` by the real
discriminant condition of admissibility. As for the local predicates of
`TauCeti.NumberTheory.QuadraticForm.Global.Predicates`, no complex clause is included: a complex
place carries only the rank, and every regular form on `Fin n → ℂ` is isometric to the sum of `n`
squares (`QuadraticForm.equivalent_weightedSumSquares_one_iff_finrank_eq`), so a complex-place
form would carry no information beyond `n`.

The predicate `IsLocalRealization` only records the local invariants; the global constraints are
inherited from the system when that system is admissible. A family realizing an admissible system
has all its local discriminants images of the one global class `d`, its finite Hasse invariants
trivial at almost every place, and the product of its finite Hasse invariants with the real Hasse
signs `(-1)^(q(q-1)/2)`, `q` the negative index, equal to one. These are exactly the hypotheses of
O'Meara's existence theorem 72:1 for a global form with prescribed localizations: applied to a
family realizing an admissible system, that theorem produces a global form isometric to `U_v` at
every finite place and to `R_w` at every real place, hence a global form with invariants `I`.

The construction is not canonical: the local realization theorem is an existence statement, and
so is the theorem here.

Conversely, the hypotheses of 72:1 make a family of local forms a realization of an admissible
system. A family `U_v`, `R_w` of rank `n ≥ 1` whose discriminants are the images of one global
class `d`, whose finite Hasse invariants are trivial at almost every place and whose Hasse product
is one realizes the system of rank `n`, discriminant `d`, the Hasse invariants of the `U_v` and the
positive indices of the `R_w`, and that system is admissible. The small-rank conditions of
admissibility hold automatically for any family of regular local forms.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsLocalRealization`: a family of
  local forms realizes the system `I`.
* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.ofLocalForms`: the system of invariants
  of a family of local forms, with a chosen global discriminant.

## Main results

* `GlobalFormInvariants.IsAdmissible.exists_regularFormClass_atFinitePlace`,
  `GlobalFormInvariants.IsAdmissible.exists_quadraticForm_atFinitePlace`: at each finite place, an
  admissible system is realized by a regular form over the completion.
* `GlobalFormInvariants.IsAdmissible.exists_quadraticForm_atRealPlace`: at each real place, by a
  regular real form of the prescribed signature.
* `GlobalFormInvariants.IsAdmissible.exists_isLocalRealization`: an admissible system is realized
  locally.
* `GlobalFormInvariants.IsLocalRealization.discr_real`,
  `GlobalFormInvariants.IsLocalRealization.hasFiniteMulSupport_localHasse`,
  `GlobalFormInvariants.IsLocalRealization.finprod_localHasse_mul_prod_eq_one`: for a family
  realizing an admissible system, the real discriminants are images of the global discriminant,
  the finite Hasse invariants have finite support, and the Hasse product is one.
* `GlobalFormInvariants.IsLocalRealization.isAdmissible_iff`: conversely, a system realized by a
  family of local forms is admissible exactly when its rank is positive, the real discriminants
  are images of the global discriminant, and the finite Hasse invariants of the family have finite
  support and Hasse product one.
* `GlobalFormInvariants.isLocalRealization_ofLocalForms`,
  `GlobalFormInvariants.isAdmissible_ofLocalForms`: a family of regular local forms of positive
  rank with discriminants coming from one global class, almost everywhere trivial Hasse invariants
  and Hasse product one realizes an admissible system, its own system `ofLocalForms`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:23 for the local
  realization and 72:1 for existence with prescribed local invariants.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §2.3, Proposition 6, and
  §3.3, Theorem 9.
-/

public section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

namespace GlobalFormInvariants

variable (I : GlobalFormInvariants K)

/-- **A family of local forms realizing a system of invariants.** Regular quadratic forms `U v`
over the completion `K_v` at every finite place `v` and `R w` over `ℝ` at every real place `w`,
all on the coordinate space of dimension `I.rank`, realize `I` when `U v` has discriminant the
image of the global discriminant of `I` and local Hasse invariant `I.finiteHasse v`, and `R w`
has positive index `I.realPositiveIndex w`. -/
structure IsLocalRealization
    (U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K))
    (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)) :
    Prop where
  /-- The form at a finite place is regular. -/
  nondegenerate_finite (v : HeightOneSpectrum (𝓞 K)) : (U v).Nondegenerate
  /-- The discriminant at a finite place is the image of the global discriminant. -/
  discr_finite (v : HeightOneSpectrum (𝓞 K)) :
    RegularFormClass.discr (formClass (U v) (nondegenerate_finite v)) = I.discrAtFinitePlace v
  /-- The local Hasse invariant at a finite place is the prescribed Hasse sign. -/
  localHasse_finite (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    RegularFormClass.localHasse (formClass (U v) (nondegenerate_finite v)) = I.finiteHasse v
  /-- The form at a real place is regular. -/
  nondegenerate_real (w : {w : InfinitePlace K // w.IsReal}) : (R w).Nondegenerate
  /-- The positive index at a real place is the prescribed one. -/
  sigPos_real (w : {w : InfinitePlace K // w.IsReal}) : sigPos (R w) = I.realPositiveIndex w

namespace IsLocalRealization

variable {I}
variable {U : ∀ v : HeightOneSpectrum (𝓞 K),
    _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
  {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
  (hL : I.IsLocalRealization U R)

include hL

/-- The negative index at a real place is the negative index `n - p_w` of the system. -/
theorem sigNeg_real (w : {w : InfinitePlace K // w.IsReal}) :
    sigNeg (R w) = I.realNegativeIndex w := by
  have h := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate (R w) (hL.nondegenerate_real w)
  rw [Module.finrank_fin_fun, hL.sigPos_real] at h
  rw [realNegativeIndex_def]
  omega

/-- The discriminant at a real place of a family realizing an admissible system is the image of
the global discriminant under the real embedding. -/
theorem discr_real (hI : I.IsAdmissible) (w : {w : InfinitePlace K // w.IsReal}) :
    RegularFormClass.discr (formClass (R w) (hL.nondegenerate_real w)) = I.discrAtRealPlace w := by
  rw [QuadraticForm.discr_formClass_eq_sigNeg_nsmul, hL.sigNeg_real, hI.discrAtRealPlace_eq]

/-- The real Hasse sign `(-1)^(q(q-1)/2)` of the form at a real place, `q` its negative index, is
the real Hasse sign of the system. -/
theorem neg_one_pow_choose_sigNeg_eq_realHasse (w : {w : InfinitePlace K // w.IsReal}) :
    (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = I.realHasse w := by
  rw [hL.sigNeg_real, realHasse_def]

/-- For a diagonalization `R w ≃ ⟨a₁, …, aₙ⟩` of the form at a real place, the product
`∏_{i<j} (aᵢ, aⱼ)_ℝ` of the real Hilbert symbols is the real Hasse sign of the system. -/
theorem prod_hilbertSymbol_eq_realHasse (w : {w : InfinitePlace K // w.IsReal}) {ι : Type*}
    [Fintype ι] [LinearOrder ι] {a : ι → ℝˣ}
    (h : (R w).Equivalent (weightedSumSquares ℝ fun i ↦ (a i : ℝ))) :
    ∏ ij ∈ univ.filter (fun ij : ι × ι ↦ ij.1 < ij.2), hilbertSymbol (a ij.1) (a ij.2) =
      I.realHasse w := by
  rw [prod_hilbertSymbol_real_of_equiv_weightedSumSquares h,
    hL.neg_one_pow_choose_sigNeg_eq_realHasse]

/-- The finite Hasse invariants of a family realizing an admissible system are trivial at all but
finitely many finite places. -/
theorem hasFiniteMulSupport_localHasse (hI : I.IsAdmissible) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v)) := by
  simpa only [funext hL.localHasse_finite] using hI.hasFiniteMulSupport_finiteHasse

open scoped Classical in
/-- **The Hasse product of a locally realizing family is one.** For a family realizing an
admissible system, the product over all finite places of the local Hasse invariants, times the
product over the real places of the real Hasse signs `(-1)^(q(q-1)/2)`, is `1`. -/
theorem finprod_localHasse_mul_prod_eq_one (hI : I.IsAdmissible) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v))) *
      ∏ w, (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = 1 := by
  simp only [hL.localHasse_finite, hL.neg_one_pow_choose_sigNeg_eq_realHasse]
  rw [← hasseProduct_def]
  exact hI.hasseProduct_eq_one

open scoped Classical in
/-- The Hasse product of a locally realizing family may be computed over any finite set of
finite places outside which the finite Hasse invariants are trivial. -/
theorem prod_localHasse_mul_prod_eq_one (hI : I.IsAdmissible)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v))) ⊆ S) :
    (∏ v ∈ S,
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v))) *
      ∏ w, (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset _ hS]
  exact hL.finprod_localHasse_mul_prod_eq_one hI

open scoped Classical in
/-- **Admissibility of a locally realized system.** A system of invariants realized by a family of
regular local forms is admissible exactly when its rank is positive, the discriminant of the form
at every real place is the image of the global discriminant, the local Hasse invariants of the
forms at the finite places are trivial at almost every place, and their product with the real
Hasse signs `(-1)^(q(q-1)/2)`, `q` the negative index, is one.

The two small-rank conditions of admissibility need no hypothesis: in rank one, and in rank two
with discriminant `[-1]`, every regular form over a nonarchimedean local field has trivial local
Hasse invariant. -/
theorem isAdmissible_iff :
    I.IsAdmissible ↔ 1 ≤ I.rank ∧
      (∀ w, RegularFormClass.discr (formClass (R w) (hL.nondegenerate_real w)) =
        I.discrAtRealPlace w) ∧
      (Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
        letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
        RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v))) ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
        RegularFormClass.localHasse (formClass (U v) (hL.nondegenerate_finite v))) *
        ∏ w, (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = 1 := by
  refine ⟨fun hI ↦ ⟨hI.one_le_rank, hL.discr_real hI, hL.hasFiniteMulSupport_localHasse hI,
    hL.finprod_localHasse_mul_prod_eq_one hI⟩, fun ⟨hn, hd, hs, hp⟩ ↦ ?_⟩
  have hrank (v : HeightOneSpectrum (𝓞 K)) :
      (formClass (U v) (hL.nondegenerate_finite v)).rank = I.rank := by
    simp
  refine
    { one_le_rank := hn
      realPositiveIndex_le_rank := fun w ↦ ?_
      discrAtRealPlace_eq := fun w ↦ ?_
      hasFiniteMulSupport_finiteHasse := by simpa only [hL.localHasse_finite] using hs
      finiteHasse_eq_one_of_rank_eq_one := fun h1 v ↦ ?_
      finiteHasse_eq_one_of_rank_eq_two := fun h2 v hdv ↦ ?_
      hasseProduct_eq_one := ?_ }
  · have h := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate (R w) (hL.nondegenerate_real w)
    rw [Module.finrank_fin_fun, hL.sigPos_real] at h
    omega
  · rw [← hd w, QuadraticForm.discr_formClass_eq_sigNeg_nsmul, hL.sigNeg_real]
  · let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    rw [← hL.localHasse_finite]
    exact RegularFormClass.localHasse_eq_one_of_rank_le_one ((hrank v).trans h1).le
  · let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    rw [← hL.localHasse_finite]
    exact RegularFormClass.localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one
      ((hrank v).trans h2) ((hL.discr_finite v).trans hdv)
  · simpa only [hL.localHasse_finite, hL.neg_one_pow_choose_sigNeg_eq_realHasse,
      ← hasseProduct_def] using hp

end IsLocalRealization

section LocalForms

variable {n : ℕ} (d : SquareClassGroup K)
  (U : ∀ v : HeightOneSpectrum (𝓞 K),
    _root_.QuadraticForm (v.adicCompletion K) (Fin n → v.adicCompletion K))
  (hU : ∀ v, (U v).Nondegenerate)
  (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin n → ℝ))

/-- **The system of invariants of a family of local forms.** For a global square class `d` and
regular forms `U v` over the completions `K_v` and `R w` over `ℝ`, all on the coordinate space of
dimension `n`, this is the system of rank `n` and global discriminant `d` whose Hasse sign at a
finite place `v` is the local Hasse invariant of `U v` and whose positive index at a real place
`w` is that of `R w`.

The body is exposed so that the rank of `ofLocalForms d U hU R` reduces to `n`: the forms `U v`
and `R w` live on `Fin n`, and `IsLocalRealization` asks for forms on the coordinate space of the
rank of the system. -/
@[expose]
noncomputable def ofLocalForms : GlobalFormInvariants K where
  rank := n
  discr := d
  finiteHasse v :=
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    RegularFormClass.localHasse (formClass (U v) (hU v))
  realPositiveIndex w := sigPos (R w)

/-- The rank of the system of a family of local forms is the dimension `n`. -/
@[simp]
theorem ofLocalForms_rank : (ofLocalForms d U hU R).rank = n :=
  (rfl)

/-- The global discriminant of the system of a family of local forms is the chosen class `d`. -/
@[simp]
theorem ofLocalForms_discr : (ofLocalForms d U hU R).discr = d :=
  (rfl)

/-- The Hasse sign at a finite place `v` of the system of a family of local forms is the local
Hasse invariant of `U v`. -/
@[simp]
theorem ofLocalForms_finiteHasse (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    (ofLocalForms d U hU R).finiteHasse v =
      RegularFormClass.localHasse (formClass (U v) (hU v)) :=
  (rfl)

/-- The positive index at a real place `w` of the system of a family of local forms is the
positive index of `R w`. -/
@[simp]
theorem ofLocalForms_realPositiveIndex (w : {w : InfinitePlace K // w.IsReal}) :
    (ofLocalForms d U hU R).realPositiveIndex w = sigPos (R w) :=
  (rfl)

variable {d U R}

/-- A family of regular local forms whose discriminants at the finite places are the images of a
global square class `d` realizes the system of invariants it defines with `d`. -/
theorem isLocalRealization_ofLocalForms
    (hUd : ∀ v, RegularFormClass.discr (formClass (U v) (hU v)) =
      (algebraMap K (v.adicCompletion K)).squareClassMap d)
    (hR : ∀ w, (R w).Nondegenerate) :
    (ofLocalForms d U hU R).IsLocalRealization U R where
  nondegenerate_finite := hU
  discr_finite v := (hUd v).trans (by rw [discrAtFinitePlace_def, ofLocalForms_discr])
  localHasse_finite v := (ofLocalForms_finiteHasse d U hU R v).symm
  nondegenerate_real := hR
  sigPos_real w := (ofLocalForms_realPositiveIndex d U hU R w).symm

open scoped Classical in
/-- **The local data of a global form with prescribed localizations is admissible.** Let `U v` and
`R w` be regular forms of rank `n ≥ 1` over the finite completions and over `ℝ` at the real places
of `K`, whose discriminants are the images of one global square class `d`, whose local Hasse
invariants are trivial at almost every finite place, and whose Hasse product, with the real Hasse
signs `(-1)^(q(q-1)/2)` for the negative indices `q`, is one. Then the system of invariants of the
family is admissible.

These are the hypotheses of O'Meara's existence theorem 72:1 for a global form with prescribed
localizations. Since the family realizes its own system (`isLocalRealization_ofLocalForms`), such a
family is a local realization of an admissible system. -/
theorem isAdmissible_ofLocalForms (hn : 1 ≤ n)
    (hUd : ∀ v, RegularFormClass.discr (formClass (U v) (hU v)) =
      (algebraMap K (v.adicCompletion K)).squareClassMap d)
    (hR : ∀ w, (R w).Nondegenerate)
    (hRd : ∀ w, RegularFormClass.discr (formClass (R w) (hR w)) =
      (embedding_of_isReal w.2).squareClassMap d)
    (hs : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hU v)))
    (hp : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
      RegularFormClass.localHasse (formClass (U v) (hU v))) *
        ∏ w, (-1 : ℤˣ) ^ (sigNeg (R w)).choose 2 = 1) :
    (ofLocalForms d U hU R).IsAdmissible :=
  ((isLocalRealization_ofLocalForms hU hUd hR).isAdmissible_iff).mpr
    ⟨hn, fun w ↦ (hRd w).trans (by rw [discrAtRealPlace_def, ofLocalForms_discr]), hs, hp⟩

end LocalForms

namespace IsAdmissible

variable {I} (hI : I.IsAdmissible)
include hI

/-- **Local realization at a finite place.** An admissible system is realized at every finite
place `v` by an isometry class of regular forms over `K_v` of the prescribed rank, with
discriminant the image of the global discriminant and the prescribed local Hasse invariant. -/
theorem exists_regularFormClass_atFinitePlace (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    ∃ x : RegularFormClass (v.adicCompletion K), x.rank = I.rank ∧
      RegularFormClass.discr x = I.discrAtFinitePlace v ∧
      RegularFormClass.localHasse x = I.finiteHasse v :=
  RegularFormClass.exists_of_realization hI.one_le_rank _ _
    (fun hn ↦ hI.finiteHasse_eq_one_of_rank_eq_one hn v)
    fun hn hd ↦ hI.finiteHasse_eq_one_of_rank_eq_two hn v hd

/-- **Local realization at a finite place, by a form on the coordinate space.** An admissible
system is realized at every finite place `v` by a regular quadratic form on `K_v ^ n`, `n` the
rank of the system, with discriminant the image of the global discriminant and the prescribed
local Hasse invariant. -/
theorem exists_quadraticForm_atFinitePlace (v : HeightOneSpectrum (𝓞 K)) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    ∃ (Q : _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K))
      (hQ : Q.Nondegenerate),
      RegularFormClass.discr (formClass Q hQ) = I.discrAtFinitePlace v ∧
      RegularFormClass.localHasse (formClass Q hQ) = I.finiteHasse v := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨x, hx, hxd, hxs⟩ := hI.exists_regularFormClass_atFinitePlace v
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, a⟩ := p
    rw [RegularFormClass.rank_mk] at hx
    subst hx
    exact ⟨presentedForm ⟨I.rank, a⟩,
      nondegenerate_presentedForm (⟨I.rank, a⟩ : RegularFormPresentation (v.adicCompletion K)),
      by rwa [formClass_presentedForm], by rwa [formClass_presentedForm]⟩

/-- **Local realization at a real place.** An admissible system is realized at every real place
`w` by a regular quadratic form on `ℝ ^ n`, `n` the rank of the system, with positive index
`p_w`, negative index `n - p_w`, and discriminant the image of the global discriminant under the
real embedding of `w`. -/
theorem exists_quadraticForm_atRealPlace (w : {w : InfinitePlace K // w.IsReal}) :
    ∃ (Q : _root_.QuadraticForm ℝ (Fin I.rank → ℝ)) (hQ : Q.Nondegenerate),
      sigPos Q = I.realPositiveIndex w ∧ sigNeg Q = I.realNegativeIndex w ∧
      RegularFormClass.discr (formClass Q hQ) = I.discrAtRealPlace w := by
  obtain ⟨Q, hQ, hp, hq⟩ :=
    QuadraticForm.exists_nondegenerate_and_sigPos_eq_and_sigNeg_eq (hI.realPositiveIndex_le_rank w)
  rw [← realNegativeIndex_def] at hq
  exact ⟨Q, hQ, hp, hq, by
    rw [QuadraticForm.discr_formClass_eq_sigNeg_nsmul, hq, hI.discrAtRealPlace_eq]⟩

/-- **Local realization of an admissible system.** An admissible system of invariants is realized
by a family of regular quadratic forms over the finite and real completions, on the coordinate
space of its rank. -/
theorem exists_isLocalRealization :
    ∃ (U : ∀ v : HeightOneSpectrum (𝓞 K),
        _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K))
      (R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)),
      I.IsLocalRealization U R := by
  choose U hU hUd hUs using hI.exists_quadraticForm_atFinitePlace
  choose R hR hRp _ _ using hI.exists_quadraticForm_atRealPlace
  exact ⟨U, R, hU, hUd, hUs, hR, hRp⟩

end IsAdmissible

end GlobalFormInvariants

end TauCeti.NumberField.QuadraticForm
