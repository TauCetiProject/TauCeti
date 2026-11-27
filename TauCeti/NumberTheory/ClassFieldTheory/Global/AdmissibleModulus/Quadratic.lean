/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.ConductorDiscriminant
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Rat
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.NumberField.Discriminant.Relative
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt2.Ramification
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants

/-!
# The conductor of a quadratic field

Let `E/ℚ` be a finite abelian extension. The real place of `ℚ` lies in the conductor of `E/ℚ`
exactly when `E` is not totally real (`mem_infinitePart_abelianConductor_rat_iff`), since the
places of `E` ramified over the real place are its complex places. When `[E : ℚ] = p` is prime,
the conductor–discriminant formula `𝔡_{E/ℚ} = 𝔣^{p - 1}` reads `f^{p - 1} = |d_E|` on absolute
norms, where `f` is the absolute norm of the finite part of the conductor and `d_E` is the
discriminant (`absNorm_finitePart_abelianConductor_pow`).

For a quadratic field `E` this determines the conductor completely: its finite part is generated
by `|d_E|` (`finitePart_abelianConductor_of_isQuadraticExtension`), and its infinite part contains
the real place exactly when `d_E < 0` (`mem_infinitePart_abelianConductor_iff_discr_neg`). So the
conductor of `E/ℚ` is `(|d_E|)` for a real quadratic field
(`abelianConductor_eq_ratFiniteModulus_of_discr_pos`) and `(|d_E|)·∞` for an imaginary one
(`abelianConductor_eq_ratModulus_of_discr_neg`).

For instance, the three quadratic subfields `ℚ(i)`, `ℚ(√2)` and `ℚ(√-2)` of `ℚ(ζ₈)` have
discriminants `-4`, `8` and `-8`, hence conductors `(4)·∞`, `(8)` (`abelianConductor_sqrt_two`)
and `(8)·∞` (`abelianConductor_sqrt_neg_two`), while `ℚ(√5) ⊆ ℚ(ζ₅)` has conductor `(5)`
(`abelianConductor_sqrt_five`). Their exponents at `2`, together with the exponent `0` of the
trivial character, add up to `0 + 2 + 3 + 3 = 8`, the exponent of `2` in the discriminant `2⁸` of
`ℚ(ζ₈)`, and their maximum `3` is the exponent of `2` in the conductor `(8)·∞` of `ℚ(ζ₈)`. The
real place drops out of the conductor of `ℚ(√2)` and `ℚ(√5)` although it lies in that of the
cyclotomic field containing them.

## Main results

* `TauCeti.ClassFieldTheory.mem_infinitePart_abelianConductor_rat_iff`: the real place of `ℚ` lies
  in the conductor of an abelian extension `E/ℚ` exactly when `E` is not totally real.
* `TauCeti.ClassFieldTheory.absNorm_finitePart_abelianConductor_pow`: for `E/ℚ` abelian of prime
  degree `p`, `f^{p - 1} = |d_E|`.
* `TauCeti.ClassFieldTheory.finitePart_abelianConductor_of_isQuadraticExtension`: the finite part
  of the conductor of a quadratic field is `(|d_E|)`.
* `TauCeti.ClassFieldTheory.mem_infinitePart_abelianConductor_iff_discr_neg`: the conductor of a
  quadratic field contains the real place exactly when its discriminant is negative.
* `TauCeti.ClassFieldTheory.abelianConductor_eq_ratFiniteModulus_of_discr_pos` and
  `TauCeti.ClassFieldTheory.abelianConductor_eq_ratModulus_of_discr_neg`: the conductor of a real
  quadratic field is `(d_E)`, and that of an imaginary quadratic field is `(|d_E|)·∞`.
* `TauCeti.ClassFieldTheory.abelianConductor_sqrt_two`,
  `TauCeti.ClassFieldTheory.abelianConductor_sqrt_neg_two` and
  `TauCeti.ClassFieldTheory.abelianConductor_sqrt_five`: the conductors `(8)`, `(8)·∞` and `(5)` of
  `ℚ(√2)`, `ℚ(√-2)` and `ℚ(√5)`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Examples 3.11 and 3.29 and Remark 3.28.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6, and Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace
  TauCeti.GlobalNumberFields Polynomial

/-! ### Abelian extensions of `ℚ` -/

section Abelian

variable (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E]

/-- **The real place of `ℚ` lies in the conductor exactly when the field is not totally real.**
For a finite abelian extension `E/ℚ`, every infinite place of `E` lies over the real place of `ℚ`,
and it is ramified there exactly when it is complex. -/
theorem mem_infinitePart_abelianConductor_rat_iff (w : {w : InfinitePlace ℚ // w.IsReal}) :
    w ∈ (abelianConductor ℚ E).infinitePart ↔ ¬ IsTotallyReal E := by
  rw [mem_infinitePart_abelianConductor_iff,
    ← isUnramifiedAtInfinitePlaces_iff_isTotallyReal (k := ℚ)]
  exact not_congr ⟨fun h ↦ ⟨fun v ↦ h v (Subsingleton.elim _ _)⟩, fun h v _ ↦ h.isUnramified v⟩

/-- **The conductor–discriminant formula over `ℚ` in prime degree.** For an abelian extension
`E/ℚ` of prime degree `p`, the absolute norm `f` of the finite part of the conductor satisfies
`f^{p - 1} = |d_E|`, where `d_E` is the discriminant of `E`. -/
theorem absNorm_finitePart_abelianConductor_pow (hp : (Module.finrank ℚ E).Prime) :
    Ideal.absNorm (abelianConductor ℚ E).finitePart ^ (Module.finrank ℚ E - 1) =
      (discr E).natAbs := by
  rw [← map_pow, ← relDiscr_eq_finitePart_abelianConductor_pow ℚ E hp,
    TauCeti.NumberField.absNorm_relDiscr_ringOfIntegers_rat]

end Abelian

/-! ### Quadratic fields -/

section Quadratic

variable (E : Type) [Field E] [NumberField E] [Algebra.IsQuadraticExtension ℚ E]

/-- **The finite part of the conductor of a quadratic field** `E` is generated by the absolute
value of its discriminant `d_E`. -/
theorem finitePart_abelianConductor_of_isQuadraticExtension :
    (abelianConductor ℚ E).finitePart = Ideal.span {((discr E).natAbs : 𝓞 ℚ)} := by
  have := IsAbelianGalois.of_isCyclic ℚ E
  have h := absNorm_finitePart_abelianConductor_pow E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two, pow_one] at h
  rw [← h Nat.prime_two, Rat.RingOfIntegers.ideal_span_absNorm_eq_self]

/-- **The conductor of a quadratic field contains the real place exactly when the field is
imaginary**, that is, when its discriminant is negative. -/
theorem mem_infinitePart_abelianConductor_iff_discr_neg (w : {w : InfinitePlace ℚ // w.IsReal}) :
    w ∈ (abelianConductor ℚ E).infinitePart ↔ discr E < 0 := by
  have := IsAbelianGalois.of_isCyclic ℚ E
  have h2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ E
  rw [mem_infinitePart_abelianConductor_rat_iff]
  refine ⟨fun h ↦ (discr_ne_zero E).lt_or_gt.resolve_right fun hd ↦
    h (IsTotallyReal.of_zero_lt_discr hd (by omega)), fun hd h ↦ ?_⟩
  have := nrComplexPlaces_eq_one_of_discr_lt_zero hd (by omega)
  rw [IsTotallyReal.nrComplexPlaces_eq_zero] at this
  exact zero_ne_one this

/-- **The conductor of a real quadratic field** `E` is the modulus `(d_E)`, without the real place.
-/
theorem abelianConductor_eq_ratFiniteModulus_of_discr_pos (hd : 0 < discr E) :
    abelianConductor ℚ E = ratFiniteModulus (discr E).natAbs (by omega) := by
  refine Modulus.ext ?_ ?_
  · rw [finitePart_abelianConductor_of_isQuadraticExtension, ratFiniteModulus_finitePart]
  · ext w
    simpa [mem_infinitePart_abelianConductor_iff_discr_neg] using hd.le

/-- **The conductor of an imaginary quadratic field** `E` is the modulus `(|d_E|)·∞`. -/
theorem abelianConductor_eq_ratModulus_of_discr_neg (hd : discr E < 0) :
    abelianConductor ℚ E = ratModulus (discr E).natAbs (by omega) := by
  refine Modulus.ext ?_ ?_
  · rw [finitePart_abelianConductor_of_isQuadraticExtension, ratModulus_finitePart]
  · ext w
    rw [mem_infinitePart_abelianConductor_iff_discr_neg, ratModulus_infinitePart,
      Finset.mem_singleton]
    exact iff_of_true hd (Subtype.ext (Subsingleton.elim _ _))

end Quadratic

/-! ### Examples -/

section Examples

variable {K : Type} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The conductor of `ℚ(√2)` is `(8)`**: the discriminant of `ℚ(√2)` is `8`. -/
theorem abelianConductor_sqrt_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    abelianConductor ℚ K = ratFiniteModulus 8 (by norm_num) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨TauCeti.NumberField.Sqrt2.finrank_eq_two hmin hgen⟩
  have hd := TauCeti.NumberField.Sqrt2.discr_eq_eight hmin hgen
  rw [abelianConductor_eq_ratFiniteModulus_of_discr_pos K (by omega)]
  simp [hd]

/-- **The conductor of `ℚ(√-2)` is `(8)·∞`**: the discriminant of `ℚ(√-2)` is `-8`. -/
theorem abelianConductor_sqrt_neg_two (hmin : minpoly ℤ θ = X ^ 2 + 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    abelianConductor ℚ K = ratModulus 8 (by norm_num) := by
  have hmin' : minpoly ℤ θ = X ^ 2 - C (-2) := by
    rw [hmin, map_neg, map_ofNat, sub_neg_eq_add]
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin' hgen⟩
  have hd : discr K = -8 :=
    (discr_eq_four_mul_of_mod_four_ne_one hmin' hgen Int.prime_two.squarefree.neg
      (by decide)).trans (by norm_num)
  rw [abelianConductor_eq_ratModulus_of_discr_neg K (by omega)]
  simp [hd]

/-- **The conductor of `ℚ(√5)` is `(5)`**, for `ℚ(√5)` presented by the golden ratio: the
discriminant of `ℚ(√5)` is `5`. -/
theorem abelianConductor_sqrt_five (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    abelianConductor ℚ K = ratFiniteModulus 5 (by norm_num) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨TauCeti.NumberField.Sqrt5.finrank_eq_two hmin hgen⟩
  have hd := TauCeti.NumberField.Sqrt5.discr_eq_five hmin hgen
  rw [abelianConductor_eq_ratFiniteModulus_of_discr_pos K (by omega)]
  simp [hd]

end Examples

end TauCeti.ClassFieldTheory
