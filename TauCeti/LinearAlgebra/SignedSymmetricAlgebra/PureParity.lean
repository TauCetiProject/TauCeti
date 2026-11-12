/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Purely even and purely odd specializations of the signed symmetric algebra

When the generating graded module `V` of `TauCeti.SignedSym G` is concentrated in a single parity,
the Koszul commutation sign is uniform across all generators and `SignedSym G` specializes to an
ordinary symmetric or exterior algebra on `V`:

* When all odd-degree pieces of `V` vanish, `SignedSym G` is isomorphic as an `R`-algebra to
  `SymmetricAlgebra R V` over any commutative ring (`TauCeti.SignedSym.symmetricEquiv`), with no
  invertibility of `2` required, identifying `lengthPiece G n` with homogeneous polynomials of
  degree `n`.
* When all even-degree pieces of `V` vanish, `SignedSym G` maps canonically onto
  `ExteriorAlgebra R V` over any commutative ring (`TauCeti.SignedSym.toExterior`), carrying
  `lengthPiece G n` onto `⋀[R]^n V` (`map_lengthPiece_toExterior`). When `Invertible (2 : R)`
  holds, this upgrades to an algebra isomorphism `TauCeti.SignedSym.exteriorEquiv`, yielding module
  finiteness when `V` is a finite `R`-module (`finite_of_even_piece_eq_bot`), and when `V` is a
  finite free `R`-module, the rank formula `2 ^ finrank R V` over a nontrivial ring
  (`finrank_eq_two_pow_of_even_piece_eq_bot`) and vanishing of `lengthPiece G d` above
  `finrank R V` (`lengthPiece_eq_bot_of_even_piece_eq_bot_of_finrank_lt`).

When `V` is concentrated in a single nonzero degree `d`, input-degree pieces `signedSymPiece G`
coincide with word-length pieces at nonnegative multiples `n * d` (`n : ℕ`) and vanish outside
them; for `d = 1`, `toExterior` maps `signedSymPiece G p` onto
`TauCeti.ExteriorAlgebra.integerGrading R V p` over any commutative ring
(`map_signedSymPiece_toExterior_of_piece_eq_bot`), and when `Invertible (2 : R)` holds,
`exteriorEquiv` identifies them isomorphically and, for a finite free `R`-module `V`,
`signedSymPiece G p` vanishes for `finrank R V < p`
(`signedSymPiece_eq_bot_of_piece_eq_bot_of_finrank_lt`).

For mixed-parity gradings, see `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.SymmetricExterior`.
The construction follows J. Pardon, *Contact homology and virtual fundamental cycles*,
equation (1.1).

## Main definitions

* `TauCeti.SignedSym.symmetricEquiv`: `SignedSym G ≃ₐ[R] SymmetricAlgebra R V` when odd pieces
  vanish, over any commutative ring.
* `TauCeti.SignedSym.toExterior`, `TauCeti.SignedSym.exteriorEquiv`: comparison and (when `2` is
  invertible) equivalence with `ExteriorAlgebra R V` when even pieces vanish.

## Main results

* `TauCeti.SignedSym.map_lengthPiece_symmetricEquiv` and
  `TauCeti.SignedSym.map_lengthPiece_toExterior`: word-length compatibility with homogeneous
  polynomials and exterior powers over any commutative ring.
* `TauCeti.SignedSym.map_signedSymPiece_toExterior_of_piece_eq_bot`: degree-`1` input-degree
  compatibility with `TauCeti.ExteriorAlgebra.integerGrading R V`.
* `TauCeti.SignedSym.lengthPiece_eq_bot_of_even_piece_eq_bot_of_finrank_lt`,
  `TauCeti.SignedSym.signedSymPiece_eq_bot_of_piece_eq_bot_of_finrank_lt`,
  `TauCeti.SignedSym.finite_of_even_piece_eq_bot`, and
  `TauCeti.SignedSym.finrank_eq_two_pow_of_even_piece_eq_bot`: top-degree vanishing and rank (for
  finite free `V`, over nontrivial `R` for the rank formula) and module finiteness (for finite `V`)
  in the purely odd case when `2` is invertible.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V)

section PurelyEven

/-- **Purely even comparison.** When all odd-degree pieces of `V` vanish, `SignedSym G` is
isomorphic as an `R`-algebra to `SymmetricAlgebra R V` over any commutative ring, with no
invertibility of `2` required. -/
def symmetricEquiv (hG : ∀ p, Odd p → G.piece p = ⊥) :
    SignedSym G ≃ₐ[R] SymmetricAlgebra R V :=
  AlgEquiv.ofAlgHom
    (lift G (SymmetricAlgebra.ι R V) fun p q x y hx _ => by
      by_cases hp : Odd p
      · rw [hG p hp, Submodule.mem_bot] at hx
        simp [hx]
      · rw [Int.negOnePow_even _ ((Int.not_odd_iff_even.mp hp).mul_right q), Units.val_one,
          one_smul, mul_comm])
    (SymmetricAlgebra.liftOfCommute
      ⟨generator G, fun x y =>
        commute_of_mem_parityGrading_zero G
          (generator_mem_parityGrading G (mem_parityGrading_zero_of_odd_eq_bot hG x))
          (generator G y)⟩)
    (by ext x; simp)
    (by ext x; simp)

/-- `symmetricEquiv` sends each generator of `SignedSym G` to the canonical generator of
`SymmetricAlgebra R V`. -/
@[simp]
theorem symmetricEquiv_generator (hG : ∀ p, Odd p → G.piece p = ⊥) (x : V) :
    symmetricEquiv G hG (generator G x) = SymmetricAlgebra.ι R V x := by
  simp [symmetricEquiv]

/-- The inverse of `symmetricEquiv` sends each symmetric-algebra generator to the generator of
`SignedSym G`. -/
@[simp]
theorem symmetricEquiv_symm_ι (hG : ∀ p, Odd p → G.piece p = ⊥) (x : V) :
    (symmetricEquiv G hG).symm (SymmetricAlgebra.ι R V x) = generator G x := by
  simp [symmetricEquiv]

/-- `symmetricEquiv` identifies word-length pieces with the homogeneous polynomial submodules of
`SymmetricAlgebra R V`. -/
theorem map_lengthPiece_symmetricEquiv (hG : ∀ p, Odd p → G.piece p = ⊥) (n : ℕ) :
    (lengthPiece G n).map (symmetricEquiv G hG).toLinearMap =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n := by
  rw [lengthPiece_def, TauCeti.SymmetricAlgebra.homogeneousSubmodule]
  refine (Submodule.map_pow _ (symmetricEquiv G hG).toAlgHom n).trans ?_
  rw [← LinearMap.range_comp]
  congr 2
  ext x
  simp

/-- Membership in the degree-`n` homogeneous submodule of `SymmetricAlgebra R V` corresponds to
word length `n` in `SignedSym G`. -/
@[simp]
theorem symmetricEquiv_mem_homogeneousSubmodule_iff (hG : ∀ p, Odd p → G.piece p = ⊥)
    {n : ℕ} {a : SignedSym G} :
    symmetricEquiv G hG a ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n ↔
      a ∈ lengthPiece G n := by
  simp [← map_lengthPiece_symmetricEquiv G hG n]

/-- The inverse of `symmetricEquiv` lands in `lengthPiece G n` precisely on the degree-`n`
homogeneous submodule of `SymmetricAlgebra R V`. -/
@[simp]
theorem symmetricEquiv_symm_mem_lengthPiece_iff (hG : ∀ p, Odd p → G.piece p = ⊥)
    {n : ℕ} {s : SymmetricAlgebra R V} :
    (symmetricEquiv G hG).symm s ∈ lengthPiece G n ↔
      s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n := by
  rw [← symmetricEquiv_mem_homogeneousSubmodule_iff G hG, AlgEquiv.apply_symm_apply]

end PurelyEven

section PurelyOdd

/-- When all even-degree pieces of `V` vanish, `SignedSym G` maps canonically to
`ExteriorAlgebra R V` over any commutative ring, with no invertibility of `2` required. -/
def toExterior (hG : ∀ p, Even p → G.piece p = ⊥) :
    SignedSym G →ₐ[R] ExteriorAlgebra R V :=
  lift G (ExteriorAlgebra.ι R) fun p q x y hx hy => by
    by_cases hp : Even p
    · rw [hG p hp, Submodule.mem_bot] at hx
      simp [hx]
    · by_cases hq : Even q
      · rw [hG q hq, Submodule.mem_bot] at hy
        simp [hy]
      · have hp' : Odd p := Int.not_even_iff_odd.mp hp
        have hq' : Odd q := Int.not_even_iff_odd.mp hq
        rw [Int.negOnePow_odd _ (hp'.mul hq'), Units.val_neg, Units.val_one, neg_smul, one_smul]
        exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- `toExterior` sends each generator of `SignedSym G` to the canonical exterior generator. -/
@[simp]
theorem toExterior_generator (hG : ∀ p, Even p → G.piece p = ⊥) (x : V) :
    toExterior G hG (generator G x) = ExteriorAlgebra.ι R x := by
  simp [toExterior]

/-- **Purely odd comparison.** When `2` is invertible and all even-degree pieces of `V` vanish,
`SignedSym G` is isomorphic as an `R`-algebra to `ExteriorAlgebra R V`. -/
def exteriorEquiv [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥) :
    SignedSym G ≃ₐ[R] ExteriorAlgebra R V :=
  AlgEquiv.ofAlgHom (toExterior G hG)
    (ExteriorAlgebra.lift R ⟨generator G, fun x => by
      rw [← pow_two]
      exact generator_sq_eq_zero_of_mem_parityGrading_one G
        (mem_parityGrading_one_of_even_eq_bot hG x)⟩)
    (by ext x; simp)
    (by ext x; simp)

/-- The forward direction of `exteriorEquiv` is `toExterior`. -/
@[simp]
theorem exteriorEquiv_apply [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥)
    (a : SignedSym G) :
    exteriorEquiv G hG a = toExterior G hG a := by
  simp [exteriorEquiv]

/-- The underlying linear map of `exteriorEquiv` is that of `toExterior`. -/
@[simp]
theorem exteriorEquiv_toLinearMap [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥) :
    (exteriorEquiv G hG).toLinearMap = (toExterior G hG).toLinearMap :=
  AlgEquiv.toLinearMap_ofAlgHom _ _ _ _

/-- The inverse of `exteriorEquiv` sends each exterior generator to the generator of
`SignedSym G`. -/
@[simp]
theorem exteriorEquiv_symm_ι [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥) (x : V) :
    (exteriorEquiv G hG).symm (ExteriorAlgebra.ι R x) = generator G x := by
  simp [exteriorEquiv]

/-- Over any commutative ring, `toExterior` maps `lengthPiece G n` onto the `n`-th exterior
power. -/
theorem map_lengthPiece_toExterior (hG : ∀ p, Even p → G.piece p = ⊥) (n : ℕ) :
    (lengthPiece G n).map (toExterior G hG).toLinearMap = ⋀[R]^n V := by
  rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    ← LinearMap.range_comp]
  congr 2
  ext x
  simp

/-- Over any commutative ring, `toExterior` maps words of length `n` into the `n`-th exterior
power. -/
theorem toExterior_mem_exteriorPower (hG : ∀ p, Even p → G.piece p = ⊥) {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) :
    toExterior G hG a ∈ ⋀[R]^n V := by
  rw [← map_lengthPiece_toExterior G hG n, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- When `2` is invertible, membership of `toExterior G hG a` in the `n`-th exterior power
corresponds to word length `n` in `SignedSym G`. -/
@[simp]
theorem toExterior_mem_exteriorPower_iff [Invertible (2 : R)]
    (hG : ∀ p, Even p → G.piece p = ⊥) {n : ℕ} {a : SignedSym G} :
    toExterior G hG a ∈ ⋀[R]^n V ↔ a ∈ lengthPiece G n := by
  rw [← exteriorEquiv_apply G hG a, ← map_lengthPiece_toExterior G hG n,
    ← exteriorEquiv_toLinearMap G hG, ← AlgEquiv.toLinearEquiv_toLinearMap,
    Submodule.mem_map_equiv, ← AlgEquiv.toLinearEquiv_apply, LinearEquiv.symm_apply_apply]

/-- When `2` is invertible, the inverse of `exteriorEquiv` lands in `lengthPiece G n` precisely
on the `n`-th exterior power. -/
@[simp]
theorem exteriorEquiv_symm_mem_lengthPiece_iff [Invertible (2 : R)]
    (hG : ∀ p, Even p → G.piece p = ⊥) {n : ℕ} {e : ExteriorAlgebra R V} :
    (exteriorEquiv G hG).symm e ∈ lengthPiece G n ↔ e ∈ ⋀[R]^n V := by
  rw [← toExterior_mem_exteriorPower_iff G hG, ← exteriorEquiv_apply G hG,
    AlgEquiv.apply_symm_apply]

/-- When `V` is concentrated in degree `1`, `toExterior` maps the input-degree piece
`signedSymPiece G p` onto `TauCeti.ExteriorAlgebra.integerGrading R V p` for every integer `p`,
over any commutative ring. -/
theorem map_signedSymPiece_toExterior_of_piece_eq_bot (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) (p : ℤ)
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    (signedSymPiece G p).map (toExterior G hG').toLinearMap =
      TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [signedSymPiece_eq_bot_of_piece_eq_bot_of_forall_mul_ne G hG (fun n => by omega),
      Submodule.map_bot, TauCeti.ExteriorAlgebra.integerGrading_of_neg hp]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have hn : signedSymPiece G (n : ℤ) = lengthPiece G n := by
      simpa only [mul_one] using signedSymPiece_eq_lengthPiece_of_piece_eq_bot G one_ne_zero hG n
    rw [hn, TauCeti.ExteriorAlgebra.integerGrading_natCast, map_lengthPiece_toExterior]

/-- When `V` is concentrated in degree `1`, `toExterior` maps elements of input degree `p` into
`TauCeti.ExteriorAlgebra.integerGrading R V p`, over any commutative ring. -/
theorem toExterior_mem_integerGrading_of_piece_eq_bot (hG : ∀ q, q ≠ 1 → G.piece q = ⊥)
    {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    toExterior G hG' a ∈ TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rw [← map_signedSymPiece_toExterior_of_piece_eq_bot G hG p hG', ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- When `V` is concentrated in degree `1` and `2` is invertible, membership of `toExterior` in
`TauCeti.ExteriorAlgebra.integerGrading R V p` characterizes `signedSymPiece G p`. -/
theorem toExterior_mem_integerGrading_iff_of_piece_eq_bot [Invertible (2 : R)]
    (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ} {a : SignedSym G}
    (hG' : ∀ q, Even q → G.piece q = ⊥ :=
      fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) :
    toExterior G hG' a ∈ TauCeti.ExteriorAlgebra.integerGrading R V p ↔
      a ∈ signedSymPiece G p := by
  rw [← exteriorEquiv_apply G hG' a, ← map_signedSymPiece_toExterior_of_piece_eq_bot G hG p hG',
    ← exteriorEquiv_toLinearMap G hG', ← AlgEquiv.toLinearEquiv_toLinearMap,
    Submodule.mem_map_equiv, ← AlgEquiv.toLinearEquiv_apply, LinearEquiv.symm_apply_apply]

/-- When `2` is invertible and all even-degree pieces of a finite free `R`-module `V` vanish,
every word-length piece of `SignedSym G` above `finrank R V` vanishes. -/
theorem lengthPiece_eq_bot_of_even_piece_eq_bot_of_finrank_lt [Invertible (2 : R)]
    [Module.Free R V] [Module.Finite R V] (hG : ∀ p, Even p → G.piece p = ⊥) {d : ℕ}
    (hd : Module.finrank R V < d) :
    lengthPiece G d = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hmem : exteriorEquiv G hG a ∈ ⋀[R]^d V := by
    rw [exteriorEquiv_apply]
    exact toExterior_mem_exteriorPower G hG ha
  have hzero : exteriorEquiv G hG a = 0 :=
    congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt d hd ⟨_, hmem⟩)
  exact (exteriorEquiv G hG).injective (hzero.trans (map_zero _).symm)

/-- When `V` is a finite free `R`-module concentrated in degree `1` and `2` is invertible, every
input-degree piece of `SignedSym G` above `finrank R V` vanishes. -/
theorem signedSymPiece_eq_bot_of_piece_eq_bot_of_finrank_lt [Invertible (2 : R)] [Module.Free R V]
    [Module.Finite R V] (hG : ∀ q, q ≠ 1 → G.piece q = ⊥) {p : ℤ}
    (hp : (Module.finrank R V : ℤ) < p) :
    signedSymPiece G p = ⊥ := by
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt ((Nat.cast_nonneg _).trans_lt hp))
  have hd : signedSymPiece G (d : ℤ) = lengthPiece G d := by
    simpa only [mul_one] using signedSymPiece_eq_lengthPiece_of_piece_eq_bot G one_ne_zero hG d
  rw [hd]
  exact lengthPiece_eq_bot_of_even_piece_eq_bot_of_finrank_lt G
    (fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))) (Nat.cast_lt.mp hp)

/-- When `2` is invertible and all even-degree pieces of a finite `R`-module `V` vanish,
`SignedSym G` is a finite `R`-module. -/
theorem finite_of_even_piece_eq_bot [Invertible (2 : R)] [Module.Finite R V]
    (hG : ∀ p, Even p → G.piece p = ⊥) :
    Module.Finite R (SignedSym G) :=
  Module.Finite.equiv (exteriorEquiv G hG).symm.toLinearEquiv

/-- When `2` is invertible and all even-degree pieces of a finite free `R`-module `V` vanish,
`SignedSym G` has rank `2 ^ finrank R V`. -/
theorem finrank_eq_two_pow_of_even_piece_eq_bot [Nontrivial R] [Invertible (2 : R)]
    [Module.Free R V] [Module.Finite R V] (hG : ∀ p, Even p → G.piece p = ⊥) :
    Module.finrank R (SignedSym G) = 2 ^ Module.finrank R V := by
  rw [(exteriorEquiv G hG).toLinearEquiv.finrank_eq,
    TauCeti.ExteriorAlgebra.finrank_eq_two_pow]

end PurelyOdd

end TauCeti.SignedSym
