/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Comparison of the signed symmetric algebra with symmetric and exterior algebras

For an internally integer-graded `R`-module `V` with grading `G`, splitting `V` into its even and
odd parity summands `TauCeti.parityGrading G.piece 0` and `TauCeti.parityGrading G.piece 1`
compares `TauCeti.SignedSym G` with the tensor product of the symmetric algebra on the even part
and the exterior algebra on the odd part:
`SignedSym G ≃ₐ[R]`
`SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R] ExteriorAlgebra R (parityGrading G.piece 1)`.
Because `SymmetricAlgebra R (parityGrading G.piece 0)` has purely even parity, the Koszul sign
between the two tensor factors is `+1`, so their super tensor product is Mathlib's ordinary
`Algebra.TensorProduct`.

We separate the maps that hold over an arbitrary commutative ring from those that require
`2` to be invertible:

* Over any commutative ring `R`, even-parity generators are central in `SignedSym G`, giving the
  inclusion `fromSymmetricEven`, the factor projections `toSymmetricEven` and `toExteriorOdd`
  (hence injectivity of `fromSymmetricEven`), the comparison map `toSymTensorExterior`, and the
  purely even equivalence `symmetricEquiv` when all odd-degree pieces vanish.
* When `Invertible (2 : R)` holds (in particular over `ℚ`), odd-parity generators in `SignedSym G`
  square to zero, giving `fromExteriorOdd`, `fromSymTensorExterior`, the algebra equivalence
  `symTensorExteriorEquiv`, module freeness of `SignedSym G` when its parity pieces (or all
  graded pieces) are free, and the purely odd equivalence `exteriorEquiv`.

The comparison respects parity, word length (`TauCeti.SignedSym.lengthPiece`), and functoriality
along degree-preserving linear maps (`TauCeti.SignedSym.map`). When `V` is concentrated in a
single nonzero degree `d`, the input-degree pieces `signedSymPiece G (n * d)` coincide with the
word-length pieces `lengthPiece G n` and vanish outside multiples of `d`; for `d = 1` this
identifies `signedSymPiece G` with `TauCeti.ExteriorAlgebra.integerGrading R V`.

The construction realizes the polynomial-exterior description of the free supercommutative
algebra in J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1).

## Main definitions

* `TauCeti.SignedSym.fromSymmetricEven`, `TauCeti.SignedSym.toSymmetricEven`: inclusion and
  projection for `SymmetricAlgebra R (parityGrading G.piece 0)`, over any commutative ring.
* `TauCeti.SignedSym.toExteriorOdd`, `TauCeti.SignedSym.fromExteriorOdd`: projection and
  (for `Invertible (2 : R)`) inclusion for `ExteriorAlgebra R (parityGrading G.piece 1)`.
* `TauCeti.SignedSym.toSymTensorExterior`, `TauCeti.SignedSym.fromSymTensorExterior`,
  `TauCeti.SignedSym.symTensorExteriorEquiv`: the tensor comparison maps and algebra equivalence.
* `TauCeti.SignedSym.symmetricEquiv`: `SignedSym G ≃ₐ[R] SymmetricAlgebra R V` when odd pieces
  vanish, over any commutative ring.
* `TauCeti.SignedSym.toExterior`, `TauCeti.SignedSym.exteriorEquiv`: comparison and equivalence
  with `ExteriorAlgebra R V` when even pieces vanish.

## Main results

* `TauCeti.SignedSym.fromSymmetricEven_injective` and `TauCeti.SignedSym.fromExteriorOdd_injective`:
  the factor inclusions embed into `SignedSym G`.
* `TauCeti.SignedSym.map_lengthPiece_symTensorExteriorEquiv` and
  `TauCeti.SignedSym.map_parityGrading_symTensorExteriorEquiv`: compatibility of
  `symTensorExteriorEquiv` with word length and parity.
* `TauCeti.SignedSym.instModuleFree` and `TauCeti.SignedSym.free_of_free_piece`: freeness of
  `SignedSym G` as an `R`-module when `2` is invertible.
* `TauCeti.SignedSym.signedSymPiece_eq_lengthPiece_of_piece_eq_bot`,
  `TauCeti.SignedSym.map_signedSymPiece_exteriorEquiv`, and
  `TauCeti.SignedSym.signedSymPiece_eq_bot_of_finrank_lt`: graded comparison when `V` is
  concentrated in a single degree.
-/

public section

open DirectSum
open scoped TensorProduct

namespace TauCeti.SignedSym

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V)

/-! ### Parity projections on the generating module -/

private noncomputable def parityComponent (k : ZMod 2) : V →ₗ[R] parityGrading G.piece k :=
  (DirectSum.component R (ZMod 2) (fun i => parityGrading G.piece i) k).comp
    (DirectSum.decomposeLinearEquiv (parityGrading G.piece)).toLinearMap

private theorem parityComponent_apply (k : ZMod 2) (x : V) :
    parityComponent G k x = DirectSum.decompose (parityGrading G.piece) x k :=
  (rfl)

private theorem decompose_parityGrading_of_mem_same {k : ZMod 2} {x : V}
    (hx : x ∈ parityGrading G.piece k) :
    DirectSum.decompose (parityGrading G.piece) x k = ⟨x, hx⟩ :=
  Subtype.ext (DirectSum.decompose_of_mem_same (parityGrading G.piece) hx)

private theorem decompose_parityGrading_of_mem_ne {j k : ZMod 2} {x : V}
    (hx : x ∈ parityGrading G.piece j) (hjk : j ≠ k) :
    DirectSum.decompose (parityGrading G.piece) x k = 0 :=
  Subtype.ext (DirectSum.decompose_of_mem_ne (parityGrading G.piece) hx hjk)

private theorem symAlgHom_ext {M A : Type*} [AddCommMonoid M] [Module R M]
    [Semiring A] [Algebra R A] {F H : SymmetricAlgebra R M →ₐ[R] A}
    (h : ∀ m, F (SymmetricAlgebra.ι R M m) = H (SymmetricAlgebra.ι R M m)) : F = H :=
  AlgHom.toRingHom_injective <| SymmetricAlgebra.ringHom_ext (by ext; simp) h

/-! ### Even and odd factor inclusions and projections -/

/-- The canonical algebra map from the symmetric algebra on the even part of `V` into
`SignedSym G`. Even-parity generators are central in `SignedSym G`, so no invertibility of `2`
is required. -/
def fromSymmetricEven :
    SymmetricAlgebra R (parityGrading G.piece 0) →ₐ[R] SignedSym G :=
  (Subalgebra.center R (SignedSym G)).val.comp <|
    SymmetricAlgebra.lift
      { toFun := fun x =>
          ⟨generator G x.1, generator_mem_center_of_mem_parityGrading_zero G x.2⟩
        map_add' := fun x y => Subtype.ext (map_add (generator G) x.1 y.1)
        map_smul' := fun r x => Subtype.ext (map_smul (generator G) r x.1) }

/-- `fromSymmetricEven` sends a symmetric-algebra generator to the corresponding generator of
`SignedSym G`. -/
@[simp]
theorem fromSymmetricEven_ι (x : parityGrading G.piece 0) :
    fromSymmetricEven G (SymmetricAlgebra.ι R (parityGrading G.piece 0) x) = generator G x := by
  simp [fromSymmetricEven]

/-- Every element in the image of `fromSymmetricEven` lies in the center of `SignedSym G`. -/
theorem fromSymmetricEven_mem_center (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ Subalgebra.center R (SignedSym G) :=
  Subtype.prop _

/-- Every element in the image of `fromSymmetricEven` commutes with all of `SignedSym G`. -/
theorem commute_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (a : SignedSym G) : Commute (fromSymmetricEven G s) a :=
  (Subalgebra.mem_center_iff.mp (fromSymmetricEven_mem_center G s) a).symm

/-- Every element in the image of `fromSymmetricEven` has even parity. -/
theorem fromSymmetricEven_mem_parityGrading_zero
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ parityGrading (signedSymPiece G) 0 := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (SetLike.one_mem_graded (parityGrading (signedSymPiece G)))
  | ι x =>
    rw [fromSymmetricEven_ι]
    exact generator_mem_parityGrading G x.2
  | mul a b ha hb =>
    have hmul := SetLike.mul_mem_graded ha hb
    rw [zero_add] at hmul
    rwa [map_mul]
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

/-- `fromSymmetricEven` carries homogeneous polynomials of degree `n` into word length `n`. -/
theorem fromSymmetricEven_mem_lengthPiece {n : ℕ}
    {s : SymmetricAlgebra R (parityGrading G.piece 0)}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n) :
    fromSymmetricEven G s ∈ lengthPiece G n := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, lengthPiece_zero]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  | add a b k _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | mem_mul m hm k b _ hb =>
    obtain ⟨x, rfl⟩ := hm
    simpa only [map_mul, fromSymmetricEven_ι, Nat.add_comm 1 k] using
      SetLike.mul_mem_graded (generator_mem_lengthPiece G x.1) hb

/-- The algebra projection from `SignedSym G` onto the symmetric algebra of the even part of `V`,
sending odd-parity generators to zero. No invertibility of `2` is needed. -/
noncomputable def toSymmetricEven :
    SignedSym G →ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) :=
  lift G ((SymmetricAlgebra.ι R (parityGrading G.piece 0)).comp (parityComponent G 0)) <| by
    intro p q x y hx hy
    simp only [LinearMap.comp_apply, parityComponent_apply]
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    have hy' : y ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hy
    by_cases hp : (p : ZMod 2) = 0
    · by_cases hq : (q : ZMod 2) = 0
      · have hsign : (p * q).negOnePow = 1 := by
          rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul, hp, hq, mul_zero, uzpow_zero]
        rw [hsign, Units.val_one, one_smul, mul_comm]
      · rw [decompose_parityGrading_of_mem_ne G hy' hq, map_zero, mul_zero, zero_mul, smul_zero]
    · rw [decompose_parityGrading_of_mem_ne G hx' hp, map_zero, zero_mul, mul_zero, smul_zero]

/-- On generators, `toSymmetricEven` projects onto the even parity component. -/
@[simp]
theorem toSymmetricEven_generator (x : V) :
    toSymmetricEven G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0)
        (DirectSum.decompose (parityGrading G.piece) x 0) :=
  lift_generator G _ _ x

/-- On an even-parity generator, `toSymmetricEven` is the canonical symmetric-algebra generator. -/
theorem toSymmetricEven_generator_of_mem_zero {x : V} (hx : x ∈ parityGrading G.piece 0) :
    toSymmetricEven G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ := by
  rw [toSymmetricEven_generator, decompose_parityGrading_of_mem_same G hx]

/-- `toSymmetricEven` annihilates odd-parity generators. -/
theorem toSymmetricEven_generator_of_mem_one {x : V} (hx : x ∈ parityGrading G.piece 1) :
    toSymmetricEven G (generator G x) = 0 := by
  rw [toSymmetricEven_generator, decompose_parityGrading_of_mem_ne G hx (by decide), map_zero]

/-- `toSymmetricEven` is a left inverse to `fromSymmetricEven` as an algebra homomorphism. -/
@[simp]
theorem toSymmetricEven_comp_fromSymmetricEven :
    (toSymmetricEven G).comp (fromSymmetricEven G) =
      AlgHom.id R (SymmetricAlgebra R (parityGrading G.piece 0)) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [toSymmetricEven_generator_of_mem_zero G x.2]

/-- Applying `toSymmetricEven` after `fromSymmetricEven` recovers the original element. -/
@[simp]
theorem toSymmetricEven_fromSymmetricEven
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymmetricEven G (fromSymmetricEven G s) = s :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromSymmetricEven G) s

/-- The symmetric algebra on the even part embeds injectively into `SignedSym G`, over any
commutative ring. -/
theorem fromSymmetricEven_injective : Function.Injective (fromSymmetricEven G) :=
  Function.LeftInverse.injective (toSymmetricEven_fromSymmetricEven G)

/-- The algebra projection from `SignedSym G` onto the exterior algebra of the odd part of `V`,
sending even-parity generators to zero. Anticommutativity of distinct exterior generators holds
over any commutative ring, so no invertibility of `2` is needed. -/
noncomputable def toExteriorOdd :
    SignedSym G →ₐ[R] ExteriorAlgebra R (parityGrading G.piece 1) :=
  lift G ((ExteriorAlgebra.ι R (M := parityGrading G.piece 1)).comp (parityComponent G 1)) <| by
    intro p q x y hx hy
    simp only [LinearMap.comp_apply, parityComponent_apply]
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    have hy' : y ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hy
    by_cases hp : (p : ZMod 2) = 1
    · by_cases hq : (q : ZMod 2) = 1
      · have hsign : (p * q).negOnePow = -1 := by
          rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul, hp, hq, mul_one, uzpow_one]
        rw [hsign, Units.val_neg, Units.val_one, neg_smul, one_smul]
        exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      · rw [decompose_parityGrading_of_mem_ne G hy' hq, map_zero, mul_zero, zero_mul, smul_zero]
    · rw [decompose_parityGrading_of_mem_ne G hx' hp, map_zero, zero_mul, mul_zero, smul_zero]

/-- On generators, `toExteriorOdd` projects onto the odd parity component. -/
@[simp]
theorem toExteriorOdd_generator (x : V) :
    toExteriorOdd G (generator G x) =
      ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) :=
  lift_generator G _ _ x

/-- `toExteriorOdd` annihilates even-parity generators. -/
theorem toExteriorOdd_generator_of_mem_zero {x : V} (hx : x ∈ parityGrading G.piece 0) :
    toExteriorOdd G (generator G x) = 0 := by
  rw [toExteriorOdd_generator, decompose_parityGrading_of_mem_ne G hx (by decide), map_zero]

/-- On an odd-parity generator, `toExteriorOdd` is the canonical exterior-algebra generator. -/
theorem toExteriorOdd_generator_of_mem_one {x : V} (hx : x ∈ parityGrading G.piece 1) :
    toExteriorOdd G (generator G x) = ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  rw [toExteriorOdd_generator, decompose_parityGrading_of_mem_same G hx]

/-- When `2` is invertible, odd-parity generators in `SignedSym G` square to zero, inducing the
canonical algebra map from the exterior algebra on the odd part of `V`. -/
def fromExteriorOdd [Invertible (2 : R)] :
    ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R] SignedSym G :=
  ExteriorAlgebra.lift R
    ⟨(generator G).comp (parityGrading G.piece 1).subtype, fun x => by
      simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← pow_two] using
        generator_sq_eq_zero_of_mem_parityGrading_one G x.2⟩

/-- `fromExteriorOdd` sends an exterior-algebra generator to the corresponding generator of
`SignedSym G`. -/
@[simp]
theorem fromExteriorOdd_ι [Invertible (2 : R)] (x : parityGrading G.piece 1) :
    fromExteriorOdd G (ExteriorAlgebra.ι R x) = generator G x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ x

/-- `toExteriorOdd` is a left inverse to `fromExteriorOdd` as an algebra homomorphism. -/
@[simp]
theorem toExteriorOdd_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toExteriorOdd G).comp (fromExteriorOdd G) =
      AlgHom.id R (ExteriorAlgebra R (parityGrading G.piece 1)) := by
  ext x
  simp [toExteriorOdd_generator_of_mem_one G x.2]

/-- Applying `toExteriorOdd` after `fromExteriorOdd` recovers the original exterior element. -/
@[simp]
theorem toExteriorOdd_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toExteriorOdd G (fromExteriorOdd G e) = e :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromExteriorOdd G) e

/-- When `2` is invertible, the exterior algebra on the odd part embeds injectively into
`SignedSym G`. -/
theorem fromExteriorOdd_injective [Invertible (2 : R)] :
    Function.Injective (fromExteriorOdd G) :=
  Function.LeftInverse.injective (toExteriorOdd_fromExteriorOdd G)

/-- `fromExteriorOdd` carries `n`-th exterior powers into word length `n`. -/
theorem fromExteriorOdd_mem_lengthPiece [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ ⋀[R]^n (parityGrading G.piece 1)) :
    fromExteriorOdd G e ∈ lengthPiece G n := by
  rw [_root_.ExteriorAlgebra.exteriorPower] at he
  induction he using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, lengthPiece_zero]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  | add a b k _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | mem_mul m hm k b _ hb =>
    obtain ⟨x, rfl⟩ := hm
    simpa only [map_mul, fromExteriorOdd_ι, Nat.add_comm 1 k] using
      SetLike.mul_mem_graded (generator_mem_lengthPiece G x.1) hb

/-- `fromExteriorOdd` preserves parity with respect to the integer grading of the exterior
algebra. -/
theorem fromExteriorOdd_mem_parityGrading [Invertible (2 : R)] {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) :
    fromExteriorOdd G e ∈ parityGrading (signedSymPiece G) k := by
  refine coarsenGrading_induction he (fun p hp a ha => ?_) (by simp) fun x y hx hy => by
    rw [map_add]; exact add_mem hx hy
  rcases lt_or_ge p 0 with hpneg | hpnonneg
  · rw [TauCeti.ExteriorAlgebra.integerGrading_of_neg hpneg, Submodule.mem_bot] at ha
    simp [ha]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpnonneg
  rw [TauCeti.ExteriorAlgebra.integerGrading_natCast,
    _root_.ExteriorAlgebra.exteriorPower] at ha
  rw [← hp]
  have hn : ∀ {m : ℕ} {b : ExteriorAlgebra R (parityGrading G.piece 1)},
      b ∈ LinearMap.range (ExteriorAlgebra.ι R) ^ m →
        fromExteriorOdd G b ∈ parityGrading (signedSymPiece G) (m : ZMod 2) := by
    intro m b hb
    induction hb using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Nat.cast_zero]
      exact Submodule.smul_mem _ r (SetLike.one_mem_graded (parityGrading (signedSymPiece G)))
    | add x y l _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mem_mul u hu l y _ hy =>
      obtain ⟨x, rfl⟩ := hu
      rw [map_mul, fromExteriorOdd_ι, Nat.cast_succ, add_comm _ (1 : ZMod 2)]
      exact SetLike.mul_mem_graded (generator_mem_parityGrading G x.2) hy
  exact hn ha

/-! ### The tensor product comparison and algebra equivalence -/

private noncomputable def symTensorExteriorGenerator :
    V →ₗ[R]
      SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1) :=
  Algebra.TensorProduct.includeLeft.toLinearMap.comp
      ((SymmetricAlgebra.ι R (parityGrading G.piece 0)).comp (parityComponent G 0)) +
    Algebra.TensorProduct.includeRight.toLinearMap.comp
      ((ExteriorAlgebra.ι R (M := parityGrading G.piece 1)).comp (parityComponent G 1))

private theorem symTensorExteriorGenerator_of_mem_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) :
    symTensorExteriorGenerator G x =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 := by
  simp only [symTensorExteriorGenerator, LinearMap.add_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, parityComponent_apply]
  rw [decompose_parityGrading_of_mem_same G hx,
    decompose_parityGrading_of_mem_ne G hx (by decide), map_zero, TensorProduct.tmul_zero,
    add_zero]

private theorem symTensorExteriorGenerator_of_mem_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    symTensorExteriorGenerator G x = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  simp only [symTensorExteriorGenerator, LinearMap.add_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, parityComponent_apply]
  rw [decompose_parityGrading_of_mem_ne G hx (by decide),
    decompose_parityGrading_of_mem_same G hx, map_zero, TensorProduct.zero_tmul, zero_add]

/-- The comparison algebra homomorphism from `SignedSym G` to
`SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R] ExteriorAlgebra R (parityGrading G.piece 1)`,
sending each generator `x = x₀ + x₁` to `ι x₀ ⊗ₜ 1 + 1 ⊗ₜ ι x₁`. This requires no invertibility
of `2`. -/
noncomputable def toSymTensorExterior :
    SignedSym G →ₐ[R]
      SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1) :=
  lift G (symTensorExteriorGenerator G) <| by
    intro p q x y hx hy
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    have hy' : y ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hy
    rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul]
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) (p : ZMod 2) with hp | hp <;>
      rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) (q : ZMod 2) with hq | hq
    · rw [hp] at hx'; rw [hq] at hy'
      rw [hp, hq, mul_zero, uzpow_zero, Units.val_one, one_smul,
        symTensorExteriorGenerator_of_mem_zero G hx',
        symTensorExteriorGenerator_of_mem_zero G hy',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    · rw [hp] at hx'; rw [hq] at hy'
      rw [hp, hq, zero_mul, uzpow_zero, Units.val_one, one_smul,
        symTensorExteriorGenerator_of_mem_zero G hx',
        symTensorExteriorGenerator_of_mem_one G hy',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul, one_mul, mul_one]
    · rw [hp] at hx'; rw [hq] at hy'
      rw [hp, hq, mul_zero, uzpow_zero, Units.val_one, one_smul,
        symTensorExteriorGenerator_of_mem_one G hx',
        symTensorExteriorGenerator_of_mem_zero G hy',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, mul_one, one_mul]
    · rw [hp] at hx'; rw [hq] at hy'
      rw [hp, hq, mul_one, uzpow_one, Units.val_neg, Units.val_one, neg_smul, one_smul,
        symTensorExteriorGenerator_of_mem_one G hx',
        symTensorExteriorGenerator_of_mem_one G hy',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), TensorProduct.tmul_neg]

/-- `toSymTensorExterior` splits a generator into its even symmetric and odd exterior parts. -/
@[simp]
theorem toSymTensorExterior_generator (x : V) :
    toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0)
          (DirectSum.decompose (parityGrading G.piece) x 0) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) :=
  lift_generator G _ _ x

/-- On an even-parity generator, `toSymTensorExterior` lands in the left tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_zero {x : V} (hx : x ∈ parityGrading G.piece 0) :
    toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_zero G hx)

/-- On an odd-parity generator, `toSymTensorExterior` lands in the right tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_one {x : V} (hx : x ∈ parityGrading G.piece 1) :
    toSymTensorExterior G (generator G x) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_one G hx)

/-- `toSymTensorExterior` embeds `fromSymmetricEven` as the left tensor inclusion `s ↦ s ⊗ₜ 1`,
over any commutative ring. -/
@[simp]
theorem toSymTensorExterior_comp_fromSymmetricEven :
    (toSymTensorExterior G).comp (fromSymmetricEven G) = Algebra.TensorProduct.includeLeft :=
  symAlgHom_ext fun x => by simp [toSymTensorExterior_generator_of_mem_zero G x.2]

/-- Pointwise form of `toSymTensorExterior_comp_fromSymmetricEven`. -/
@[simp]
theorem toSymTensorExterior_fromSymmetricEven
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymTensorExterior G (fromSymmetricEven G s) = s ⊗ₜ[R] 1 :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymmetricEven G) s

/-- When `2` is invertible, `toSymTensorExterior` embeds `fromExteriorOdd` as the right tensor
inclusion `e ↦ 1 ⊗ₜ e`. -/
@[simp]
theorem toSymTensorExterior_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromExteriorOdd G) = Algebra.TensorProduct.includeRight := by
  ext x
  simp [toSymTensorExterior_generator_of_mem_one G x.2]

/-- Pointwise form of `toSymTensorExterior_comp_fromExteriorOdd`. -/
@[simp]
theorem toSymTensorExterior_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymTensorExterior G (fromExteriorOdd G e) = 1 ⊗ₜ[R] e :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromExteriorOdd G) e

/-- When `2` is invertible, multiplying `fromSymmetricEven` and `fromExteriorOdd` defines the
algebra homomorphism from `Sym(V_even) ⊗ Λ(V_odd)` into `SignedSym G`. -/
def fromSymTensorExterior [Invertible (2 : R)] :
    SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R]
      SignedSym G :=
  Algebra.TensorProduct.lift (fromSymmetricEven G) (fromExteriorOdd G) fun s e =>
    commute_fromSymmetricEven G s (fromExteriorOdd G e)

/-- On a pure tensor, `fromSymTensorExterior` multiplies the images of the two factors. -/
@[simp]
theorem fromSymTensorExterior_tmul [Invertible (2 : R)]
    (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    fromSymTensorExterior G (s ⊗ₜ[R] e) = fromSymmetricEven G s * fromExteriorOdd G e :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Composing `fromSymTensorExterior` with the left tensor inclusion recovers
`fromSymmetricEven`. -/
@[simp]
theorem fromSymTensorExterior_comp_includeLeft [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeLeft = fromSymmetricEven G :=
  symAlgHom_ext fun x => by simp

/-- Composing `fromSymTensorExterior` with the right tensor inclusion recovers
`fromExteriorOdd`. -/
@[simp]
theorem fromSymTensorExterior_comp_includeRight [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeRight = fromExteriorOdd G := by
  ext x
  simp

/-- `toSymTensorExterior` followed by `fromSymTensorExterior` is the identity on `SignedSym G`. -/
@[simp]
theorem fromSymTensorExterior_comp_toSymTensorExterior [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp (toSymTensorExterior G) = AlgHom.id R (SignedSym G) := by
  ext x
  simp only [AlgHom.comp_apply, AlgHom.id_apply, toSymTensorExterior_generator, map_add,
    fromSymTensorExterior_tmul, map_one, mul_one, one_mul, fromSymmetricEven_ι, fromExteriorOdd_ι]
  rw [← map_add, decompose_parityGrading_zero_add_one]

/-- Pointwise form of `fromSymTensorExterior_comp_toSymTensorExterior`. -/
@[simp]
theorem fromSymTensorExterior_toSymTensorExterior [Invertible (2 : R)] (a : SignedSym G) :
    fromSymTensorExterior G (toSymTensorExterior G a) = a :=
  AlgHom.congr_fun (fromSymTensorExterior_comp_toSymTensorExterior G) a

/-- `fromSymTensorExterior` followed by `toSymTensorExterior` is the identity on the tensor
product. -/
@[simp]
theorem toSymTensorExterior_comp_fromSymTensorExterior [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromSymTensorExterior G) =
      AlgHom.id R
        (SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
          ExteriorAlgebra R (parityGrading G.piece 1)) := by
  apply Algebra.TensorProduct.ext
  · exact symAlgHom_ext fun x => by simp [toSymTensorExterior_generator_of_mem_zero G x.2]
  · ext x
    simp [toSymTensorExterior_generator_of_mem_one G x.2]

/-- Pointwise form of `toSymTensorExterior_comp_fromSymTensorExterior`. -/
@[simp]
theorem toSymTensorExterior_fromSymTensorExterior [Invertible (2 : R)]
    (z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymTensorExterior G (fromSymTensorExterior G z) = z :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymTensorExterior G) z

/-- **Comparison with symmetric and exterior algebras.** When `2` is invertible in `R` (in
particular over `ℚ`), the signed symmetric algebra on `G` is canonically isomorphic as an
`R`-algebra to `Sym(V_even) ⊗ Λ(V_odd)`. -/
noncomputable def symTensorExteriorEquiv [Invertible (2 : R)] :
    SignedSym G ≃ₐ[R]
      SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1) :=
  AlgEquiv.ofAlgHom (toSymTensorExterior G) (fromSymTensorExterior G)
    (toSymTensorExterior_comp_fromSymTensorExterior G)
    (fromSymTensorExterior_comp_toSymTensorExterior G)

/-- The forward direction of `symTensorExteriorEquiv` is `toSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_apply [Invertible (2 : R)] (a : SignedSym G) :
    symTensorExteriorEquiv G a = toSymTensorExterior G a :=
  (rfl)

/-- The inverse of `symTensorExteriorEquiv` is `fromSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_symm_apply [Invertible (2 : R)]
    (z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)) :
    (symTensorExteriorEquiv G).symm z = fromSymTensorExterior G z :=
  (rfl)

/-! ### Module freeness -/

/-- When `2` is invertible and both parity summands of `V` are free `R`-modules, `SignedSym G` is
a free `R`-module. -/
instance instModuleFree [Invertible (2 : R)]
    [Module.Free R (parityGrading G.piece 0)] [Module.Free R (parityGrading G.piece 1)] :
    Module.Free R (SignedSym G) :=
  Module.Free.of_equiv (symTensorExteriorEquiv G).symm.toLinearEquiv

/-- When `2` is invertible and every homogeneous piece `G.piece p` is a free `R`-module,
`SignedSym G` is a free `R`-module. -/
theorem free_of_free_piece [Invertible (2 : R)] [∀ p, Module.Free R (G.piece p)] :
    Module.Free R (SignedSym G) := by
  have : Module.Free R (parityGrading G.piece 0) :=
    Module.Free.of_equiv (coarsenGradingEquiv G.piece (Int.castAddHom (ZMod 2)) 0)
  have : Module.Free R (parityGrading G.piece 1) :=
    Module.Free.of_equiv (coarsenGradingEquiv G.piece (Int.castAddHom (ZMod 2)) 1)
  exact inferInstance

/-! ### Word-length and parity compatibility -/

/-- Over any commutative ring, `toSymTensorExterior` maps words of length `n` into the sum of the
bidegree `(i, j)` symmetric-exterior tensor pieces with `i + j = n`. -/
theorem toSymTensorExterior_mem_iSup_homogeneous_exteriorPower {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) :
    toSymTensorExterior G a ∈
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂
          (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
            (ExteriorAlgebra R (parityGrading G.piece 1)))
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  let B (i j : ℕ) :=
    Submodule.map₂
      (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
        (ExteriorAlgebra R (parityGrading G.piece 1)))
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
      (⋀[R]^j (parityGrading G.piece 1))
  let S (m : ℕ) := ⨆ (i : ℕ) (j : ℕ) (_ : i + j = m), B i j
  have mem_S {i j m : ℕ} (hij : i + j = m) {z} (hz : z ∈ B i j) : z ∈ S m :=
    Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hij hz))
  refine length_induction G (P := fun m a => toSymTensorExterior G a ∈ S m)
    (fun r => ?_) (fun _ _ _ ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun m x a ih => ?_) ha
  · rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    exact mem_S (i := 0) (j := 0) rfl <| Submodule.apply_mem_map₂ _
      (by rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule, pow_zero]
          exact Submodule.mem_one.mpr ⟨r, rfl⟩)
      (SetLike.one_mem_graded fun j => ⋀[R]^j (parityGrading G.piece 1))
  · rw [map_mul, toSymTensorExterior_generator, add_mul]
    set x₀ := DirectSum.decompose (parityGrading G.piece) x 0
    set x₁ := DirectSum.decompose (parityGrading G.piece) x 1
    have hleft : S m ≤ (S (m + 1)).comap
        (LinearMap.mulLeft R (SymmetricAlgebra.ι R _ x₀ ⊗ₜ[R] (1 : ExteriorAlgebra R _))) :=
      iSup₂_le fun i j => iSup_le fun hij => Submodule.map₂_le.mpr fun s hs e he => by
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        refine mem_S (i := i + 1) (j := j) (by omega) (Submodule.apply_mem_map₂ _ ?_ he)
        simpa only [Nat.add_comm 1 i] using SetLike.mul_mem_graded
          (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ x₀) hs
    have hright : S m ≤ (S (m + 1)).comap
        (LinearMap.mulLeft R ((1 : SymmetricAlgebra R _) ⊗ₜ[R] ExteriorAlgebra.ι R x₁)) :=
      iSup₂_le fun i j => iSup_le fun hij => Submodule.map₂_le.mpr fun s hs e he => by
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        exact mem_S (i := i) (j := j + 1) (by omega)
          (Submodule.apply_mem_map₂ _ hs (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower x₁ he))
    exact add_mem (hleft ih) (hright ih)

/-- Under `symTensorExteriorEquiv`, the word-length-`n` submodule corresponds to the sum of the
tensor products of symmetric degree `i` and exterior degree `j` with `i + j = n`. -/
theorem map_lengthPiece_symTensorExteriorEquiv [Invertible (2 : R)] (n : ℕ) :
    (lengthPiece G n).map (symTensorExteriorEquiv G).toLinearMap =
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂
          (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
            (ExteriorAlgebra R (parityGrading G.piece 1)))
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact toSymTensorExterior_mem_iSup_homogeneous_exteriorPower G ha
  · refine iSup₂_le fun i j => iSup_le fun hij => Submodule.map₂_le.mpr fun s hs e he => ?_
    refine ⟨fromSymTensorExterior G (s ⊗ₜ[R] e), ?_, ?_⟩
    · rw [fromSymTensorExterior_tmul, ← hij]
      exact SetLike.mul_mem_graded
        (fromSymmetricEven_mem_lengthPiece G hs) (fromExteriorOdd_mem_lengthPiece G he)
    · exact toSymTensorExterior_fromSymTensorExterior G (s ⊗ₜ[R] e)

private theorem toSymTensorExterior_mem_parity_of_mem_signedSymPiece {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) :
    toSymTensorExterior G a ∈
      Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) (p : ZMod 2)) := by
  let P (j : ZMod 2) :=
    Submodule.map₂
      (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
        (ExteriorAlgebra R (parityGrading G.piece 1)))
      ⊤ (parityGrading
        (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) j)
  refine homogeneous_induction G (P := fun p b => toSymTensorExterior G b ∈ P (p : ZMod 2))
    ?_ ?_ ?_ (fun _ => by simp)
    (fun _ x y hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun _ r x hx => by rw [map_smul]; exact Submodule.smul_mem _ r hx) ha
  · rw [map_one, Int.cast_zero]
    exact Submodule.apply_mem_map₂ _ Submodule.mem_top
      (SetLike.one_mem_graded (parityGrading
        (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1))))
  · intro q x hx
    have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
    rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq
    · rw [hq] at hx' ⊢
      rw [toSymTensorExterior_generator_of_mem_zero G hx']
      exact Submodule.apply_mem_map₂ _ Submodule.mem_top
        (SetLike.one_mem_graded (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1))))
    · rw [hq] at hx' ⊢
      rw [toSymTensorExterior_generator_of_mem_one G hx']
      exact Submodule.apply_mem_map₂ _ Submodule.mem_top <|
        mem_parityGrading_of_mem
          (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (R := R)
            (⟨x, hx'⟩ : parityGrading G.piece 1))
  · intro q r u v hu hv
    rw [map_mul, Int.cast_add]
    have hmul : P (q : ZMod 2) ≤ (P ((q : ZMod 2) + (r : ZMod 2))).comap
        (LinearMap.mulRight R (toSymTensorExterior G v)) :=
      Submodule.map₂_le.mpr fun s₁ _ e₁ he₁ => by
        simp only [Submodule.mem_comap, LinearMap.mulRight_apply, TensorProduct.mk_apply]
        have hmulR : P (r : ZMod 2) ≤
            (P ((q : ZMod 2) + (r : ZMod 2))).comap (LinearMap.mulLeft R (s₁ ⊗ₜ[R] e₁)) :=
          Submodule.map₂_le.mpr fun s₂ _ e₂ he₂ => by
            simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
              Algebra.TensorProduct.tmul_mul_tmul]
            exact Submodule.apply_mem_map₂ _ Submodule.mem_top (SetLike.mul_mem_graded he₁ he₂)
        exact hmulR hv
    exact hmul hu

/-- Over any commutative ring, `toSymTensorExterior` sends elements of parity `k` into the
submodule of tensors whose exterior factor has parity `k`. -/
theorem toSymTensorExterior_mem_parityGrading {k : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) k) :
    toSymTensorExterior G a ∈
      Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  refine coarsenGrading_induction ha (fun p hp b hb => ?_) (by simp) fun x y hx hy => by
    rw [map_add]; exact add_mem hx hy
  rw [← hp]
  exact toSymTensorExterior_mem_parity_of_mem_signedSymPiece G hb

/-- Under `symTensorExteriorEquiv`, the parity-`k` piece of `SignedSym G` corresponds to the
tensors whose exterior factor has parity `k`. -/
theorem map_parityGrading_symTensorExteriorEquiv [Invertible (2 : R)] (k : ZMod 2) :
    (parityGrading (signedSymPiece G) k).map (symTensorExteriorEquiv G).toLinearMap =
      Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact toSymTensorExterior_mem_parityGrading G ha
  · refine Submodule.map₂_le.mpr fun s _ e he => ?_
    refine ⟨fromSymTensorExterior G (s ⊗ₜ[R] e), ?_, ?_⟩
    · rw [fromSymTensorExterior_tmul, ← zero_add k]
      exact SetLike.mul_mem_graded
        (fromSymmetricEven_mem_parityGrading_zero G s) (fromExteriorOdd_mem_parityGrading G he)
    · exact toSymTensorExterior_fromSymTensorExterior G (s ⊗ₜ[R] e)

/-! ### Functoriality along degree-preserving maps -/

section Functoriality

variable {W : Type w} [AddCommGroup W] [Module R W] (H : InternalGrading R W)

/-- `fromSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymmetricEven (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromSymmetricEven G) =
      (fromSymmetricEven H).comp (SymmetricAlgebra.map R (hf.restrictParity 0)) :=
  symAlgHom_ext fun x => by simp

/-- `fromExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromExteriorOdd [Invertible (2 : R)] (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromExteriorOdd G) =
      (fromExteriorOdd H).comp (ExteriorAlgebra.map (hf.restrictParity 1)) := by
  ext x
  simp

/-- `toSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem toSymmetricEven_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toSymmetricEven H).comp (map G H f hf) =
      (SymmetricAlgebra.map R (hf.restrictParity 0)).comp (toSymmetricEven G) := by
  ext x
  simp

/-- `toExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem toExteriorOdd_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toExteriorOdd H).comp (map G H f hf) =
      (ExteriorAlgebra.map (hf.restrictParity 1)).comp (toExteriorOdd G) := by
  ext x
  simp

/-- `toSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem toSymTensorExterior_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toSymTensorExterior H).comp (map G H f hf) =
      (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.restrictParity 0))
        (ExteriorAlgebra.map (hf.restrictParity 1))).comp (toSymTensorExterior G) := by
  ext x
  simp

/-- `fromSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymTensorExterior [Invertible (2 : R)] (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromSymTensorExterior G) =
      (fromSymTensorExterior H).comp
        (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.restrictParity 0))
          (ExteriorAlgebra.map (hf.restrictParity 1))) := by
  apply Algebra.TensorProduct.ext
  · rw [AlgHom.comp_assoc, fromSymTensorExterior_comp_includeLeft, map_comp_fromSymmetricEven]
    exact symAlgHom_ext fun x => by simp
  · calc
      ((map G H f hf).comp (fromSymTensorExterior G)).comp Algebra.TensorProduct.includeRight =
          (map G H f hf).comp (fromExteriorOdd G) := by
        rw [AlgHom.comp_assoc, fromSymTensorExterior_comp_includeRight]
      _ = (fromExteriorOdd H).comp (ExteriorAlgebra.map (hf.restrictParity 1)) :=
        map_comp_fromExteriorOdd G H f hf
      _ = ((fromSymTensorExterior H).comp
            (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.restrictParity 0))
              (ExteriorAlgebra.map (hf.restrictParity 1)))).comp
            Algebra.TensorProduct.includeRight := by
        ext x
        simp

end Functoriality

/-! ### Concentration in a single degree -/

section SingleDegree

/-- When all homogeneous pieces of `V` outside degree `d` vanish, every element of `V` has
degree `d`. -/
theorem mem_piece_of_piece_eq_bot {d : ℤ} (hG : ∀ p, p ≠ d → G.piece p = ⊥) (x : V) :
    x ∈ G.piece d := by
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => exact zero_mem _
  | @homogeneous p y =>
    rcases y with ⟨y, hy⟩
    simp only
    by_cases hp : p = d
    · exact hp ▸ hy
    · rw [hG p hp, Submodule.mem_bot] at hy
      rw [hy]
      exact zero_mem _
  | add x y hx hy => exact add_mem hx hy

/-- When `V` is concentrated in degree `d`, words of length `n` have input degree `n * d`. -/
theorem lengthPiece_le_signedSymPiece_of_piece_eq_bot {d : ℤ}
    (hG : ∀ p, p ≠ d → G.piece p = ⊥) (n : ℕ) :
    lengthPiece G n ≤ signedSymPiece G (n * d) := by
  intro a ha
  refine length_induction G (P := fun m b => b ∈ signedSymPiece G (m * d))
    (fun r => ?_) (fun _ _ _ hx hy => add_mem hx hy) (fun m x b hb => ?_) ha
  · rw [Nat.cast_zero, zero_mul, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (SetLike.one_mem_graded (signedSymPiece G))
  · have hdeg : (m + 1 : ℕ) * d = d + m * d := by push_cast; ring
    rw [hdeg]
    exact SetLike.mul_mem_graded (generator_mem_signedSymPiece G (mem_piece_of_piece_eq_bot G hG x))
      hb

/-- When `V` is concentrated in degree `d`, input degrees not of the form `n * d` (`n : ℕ`)
vanish in `SignedSym G`. -/
theorem signedSymPiece_eq_bot_of_forall_mul_ne {d p : ℤ}
    (hG : ∀ q, q ≠ d → G.piece q = ⊥) (hp : ∀ n : ℕ, (n : ℤ) * d ≠ p) :
    signedSymPiece G p = ⊥ := by
  rw [signedSymPiece_eq_span, Submodule.span_eq_bot]
  rintro _ ⟨n, deg, x, hx, rfl, rfl⟩
  by_cases hdeg : ∀ i, deg i = d
  · refine (hp n ?_).elim
    simp [hdeg]
  · obtain ⟨i, hi⟩ := not_forall.mp hdeg
    have hxi : x i = 0 := by
      have := hx i
      rwa [hG (deg i) hi, Submodule.mem_bot] at this
    exact List.prod_eq_zero (List.mem_ofFn.mpr ⟨i, by simp [hxi]⟩)

/-- When `V` is concentrated in a nonzero degree `d`, the input-degree piece `n * d` coincides
with the word-length piece `lengthPiece G n`. -/
theorem signedSymPiece_eq_lengthPiece_of_piece_eq_bot {d : ℤ} (hd : d ≠ 0)
    (hG : ∀ q, q ≠ d → G.piece q = ⊥) (n : ℕ) :
    signedSymPiece G (n * d) = lengthPiece G n := by
  refine le_antisymm ?_ (lengthPiece_le_signedSymPiece_of_piece_eq_bot G hG n)
  rw [signedSymPiece_eq_span, Submodule.span_le]
  rintro _ ⟨m, deg, x, hx, hsum, rfl⟩
  by_cases hdeg : ∀ i, deg i = d
  · have hmn : m = n := by
      apply Int.ofNat.inj
      refine mul_right_cancel₀ hd ?_
      simpa [hdeg] using hsum
    subst hmn
    exact word_mem_lengthPiece G x
  · obtain ⟨i, hi⟩ := not_forall.mp hdeg
    have hxi : x i = 0 := by
      have := hx i
      rwa [hG (deg i) hi, Submodule.mem_bot] at this
    rw [List.prod_eq_zero (List.mem_ofFn.mpr ⟨i, by simp [hxi]⟩)]
    exact zero_mem _

end SingleDegree

/-! ### Purely even and purely odd specializations -/

section PurelyEven

/-- When all odd-degree pieces of `V` vanish, every element of `V` has even parity. -/
theorem mem_parityGrading_zero_of_odd_piece_eq_bot
    (hG : ∀ p, Odd p → G.piece p = ⊥) (x : V) :
    x ∈ parityGrading G.piece 0 := by
  have hodd : parityGrading G.piece 1 = ⊥ := by
    rw [parityGrading_one]
    exact iSup_eq_bot.mpr fun k => hG (2 * k + 1) ⟨k, rfl⟩
  have h1 : (DirectSum.decompose (parityGrading G.piece) x 1 : V) = 0 := by
    obtain ⟨v, hv⟩ := DirectSum.decompose (parityGrading G.piece) x 1
    rwa [hodd, Submodule.mem_bot] at hv
  have hsum := decompose_parityGrading_zero_add_one G.piece x
  rw [h1, add_zero] at hsum
  rw [← hsum]
  exact (DirectSum.decompose (parityGrading G.piece) x 0).2

/-- When all odd-degree pieces of `V` vanish, `SignedSym G` is commutative over any commutative
ring. -/
theorem mul_comm_of_odd_piece_eq_bot (hG : ∀ p, Odd p → G.piece p = ⊥)
    (a b : SignedSym G) : a * b = b * a := by
  induction a using SignedSym.induction with
  | algebraMap r => exact Algebra.commutes r b
  | generator x =>
    exact (commute_of_mem_parityGrading_zero G
      (generator_mem_parityGrading G (mem_parityGrading_zero_of_odd_piece_eq_bot G hG x)) b).eq
  | mul u v hu hv => rw [mul_assoc, hv, ← mul_assoc, hu, mul_assoc]
  | add u v hu hv => rw [add_mul, mul_add, hu, hv]

/-- **Purely even comparison.** When all odd-degree pieces of `V` vanish, `SignedSym G` is
isomorphic as an `R`-algebra to `SymmetricAlgebra R V` over any commutative ring, with no
invertibility of `2` required. -/
def symmetricEquiv (hG : ∀ p, Odd p → G.piece p = ⊥) :
    SignedSym G ≃ₐ[R] SymmetricAlgebra R V :=
  AlgEquiv.ofAlgHom
    (lift G (SymmetricAlgebra.ι R V) fun p q x y hx hy => by
      by_cases hp : Odd p
      · rw [hG p hp, Submodule.mem_bot] at hx
        simp [hx]
      · by_cases hq : Odd q
        · rw [hG q hq, Submodule.mem_bot] at hy
          simp [hy]
        · obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.mp hp
          have hsign : ((k + k) * q).negOnePow = 1 := by
            rw [← two_mul, mul_assoc, Int.negOnePow_two_mul]
          rw [hsign, Units.val_one, one_smul, mul_comm])
    ((Subalgebra.center R (SignedSym G)).val.comp <|
      SymmetricAlgebra.lift
        { toFun := fun x => ⟨generator G x, generator_mem_center_of_mem_parityGrading_zero G
            (mem_parityGrading_zero_of_odd_piece_eq_bot G hG x)⟩
          map_add' := fun x y => Subtype.ext (map_add (generator G) x y)
          map_smul' := fun r x => Subtype.ext (map_smul (generator G) r x) })
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      simp)
    (by
      ext x
      simp)

/-- `symmetricEquiv` sends each generator of `SignedSym G` to the canonical generator of
`SymmetricAlgebra R V`. -/
@[simp]
theorem symmetricEquiv_generator (hG : ∀ p, Odd p → G.piece p = ⊥) (x : V) :
    symmetricEquiv G hG (generator G x) = SymmetricAlgebra.ι R V x :=
  lift_generator G _ _ x

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
  exact symmetricEquiv_generator G hG x

/-- Membership in the degree-`n` homogeneous submodule of `SymmetricAlgebra R V` corresponds to
word length `n` in `SignedSym G`. -/
@[simp]
theorem symmetricEquiv_mem_homogeneousSubmodule_iff (hG : ∀ p, Odd p → G.piece p = ⊥)
    {n : ℕ} {a : SignedSym G} :
    symmetricEquiv G hG a ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R V n ↔
      a ∈ lengthPiece G n := by
  rw [← map_lengthPiece_symmetricEquiv G hG n]
  exact ⟨fun ⟨b, hb, hab⟩ => (symmetricEquiv G hG).injective hab ▸ hb,
    fun ha => ⟨a, ha, rfl⟩⟩

end PurelyEven

section PurelyOdd

/-- When all even-degree pieces of `V` vanish, every element of `V` has odd parity. -/
theorem mem_parityGrading_one_of_even_piece_eq_bot
    (hG : ∀ p, Even p → G.piece p = ⊥) (x : V) :
    x ∈ parityGrading G.piece 1 := by
  have heven : parityGrading G.piece 0 = ⊥ := by
    rw [parityGrading_zero]
    exact iSup_eq_bot.mpr fun k => hG (2 * k) ⟨k, two_mul k⟩
  have h0 : (DirectSum.decompose (parityGrading G.piece) x 0 : V) = 0 := by
    obtain ⟨v, hv⟩ := DirectSum.decompose (parityGrading G.piece) x 0
    rwa [heven, Submodule.mem_bot] at hv
  have hsum := decompose_parityGrading_zero_add_one G.piece x
  rw [h0, zero_add] at hsum
  rw [← hsum]
  exact (DirectSum.decompose (parityGrading G.piece) x 1).2

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
    toExterior G hG (generator G x) = ExteriorAlgebra.ι R x :=
  lift_generator G _ _ x

/-- **Purely odd comparison.** When `2` is invertible and all even-degree pieces of `V` vanish,
`SignedSym G` is isomorphic as an `R`-algebra to `ExteriorAlgebra R V`. -/
def exteriorEquiv [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥) :
    SignedSym G ≃ₐ[R] ExteriorAlgebra R V :=
  AlgEquiv.ofAlgHom (toExterior G hG)
    (ExteriorAlgebra.lift R ⟨generator G, fun x => by
      rw [← pow_two]
      exact generator_sq_eq_zero_of_mem_parityGrading_one G
        (mem_parityGrading_one_of_even_piece_eq_bot G hG x)⟩)
    (by ext x; simp)
    (by ext x; simp)

/-- The forward direction of `exteriorEquiv` is `toExterior`. -/
@[simp]
theorem exteriorEquiv_apply [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥)
    (a : SignedSym G) :
    exteriorEquiv G hG a = toExterior G hG a :=
  (rfl)

/-- The inverse of `exteriorEquiv` sends each exterior generator to the generator of
`SignedSym G`. -/
@[simp]
theorem exteriorEquiv_symm_ι [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥) (x : V) :
    (exteriorEquiv G hG).symm (ExteriorAlgebra.ι R x) = generator G x := by
  simp [exteriorEquiv]

/-- Over any commutative ring, `toExterior` maps words of length `n` into the `n`-th exterior
power. -/
theorem toExterior_mem_exteriorPower (hG : ∀ p, Even p → G.piece p = ⊥) {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) :
    toExterior G hG a ∈ ⋀[R]^n V := by
  have hmap : (lengthPiece G n).map (toExterior G hG).toLinearMap = ⋀[R]^n V := by
    rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
      ← LinearMap.range_comp]
    congr 2
    ext x
    exact toExterior_generator G hG x
  exact hmap ▸ ⟨a, ha, rfl⟩

/-- `exteriorEquiv` identifies word-length pieces with exterior powers. -/
theorem map_lengthPiece_exteriorEquiv [Invertible (2 : R)] (hG : ∀ p, Even p → G.piece p = ⊥)
    (n : ℕ) :
    (lengthPiece G n).map (exteriorEquiv G hG).toLinearMap = ⋀[R]^n V := by
  rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower]
  refine (Submodule.map_pow _ (exteriorEquiv G hG).toAlgHom n).trans ?_
  rw [← LinearMap.range_comp]
  congr 2
  ext x
  exact toExterior_generator G hG x

/-- When `2` is invertible, membership of `toExterior G hG a` in the `n`-th exterior power
corresponds to word length `n` in `SignedSym G`. -/
@[simp]
theorem toExterior_mem_exteriorPower_iff [Invertible (2 : R)]
    (hG : ∀ p, Even p → G.piece p = ⊥) {n : ℕ} {a : SignedSym G} :
    toExterior G hG a ∈ ⋀[R]^n V ↔ a ∈ lengthPiece G n := by
  rw [← exteriorEquiv_apply G hG a, ← map_lengthPiece_exteriorEquiv G hG n]
  exact ⟨fun ⟨b, hb, hab⟩ => (exteriorEquiv G hG).injective hab ▸ hb,
    fun ha => ⟨a, ha, rfl⟩⟩

/-- When `V` is concentrated in degree `1` and `2` is invertible, `exteriorEquiv` identifies the
input-degree pieces `signedSymPiece G p` with `TauCeti.ExteriorAlgebra.integerGrading R V p` for
every integer `p`. -/
theorem map_signedSymPiece_exteriorEquiv [Invertible (2 : R)]
    (hG : ∀ p, p ≠ 1 → G.piece p = ⊥) (p : ℤ) :
    (signedSymPiece G p).map
        (exteriorEquiv G fun q hq =>
          hG q (by rintro rfl; exact absurd hq (by decide))).toLinearMap =
      TauCeti.ExteriorAlgebra.integerGrading R V p := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [signedSymPiece_eq_bot_of_forall_mul_ne G hG (fun n => by omega), Submodule.map_bot,
      TauCeti.ExteriorAlgebra.integerGrading_of_neg hp]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have hn : signedSymPiece G (n : ℤ) = lengthPiece G n := by
      simpa only [mul_one] using signedSymPiece_eq_lengthPiece_of_piece_eq_bot G one_ne_zero hG n
    rw [hn, TauCeti.ExteriorAlgebra.integerGrading_natCast, map_lengthPiece_exteriorEquiv]

/-- When `V` is a finite free `R`-module concentrated in degree `1` and `2` is invertible, every
input-degree piece of `SignedSym G` above `finrank R V` vanishes. -/
theorem signedSymPiece_eq_bot_of_finrank_lt [Invertible (2 : R)]
    [Module.Free R V] [Module.Finite R V] (hG : ∀ p, p ≠ 1 → G.piece p = ⊥) {d : ℕ}
    (hd : Module.finrank R V < d) :
    signedSymPiece G d = ⊥ := by
  let e := exteriorEquiv G fun q hq => hG q (by rintro rfl; exact absurd hq (by decide))
  rw [eq_bot_iff]
  intro a ha
  have hmem : e a ∈ ⋀[R]^d V := by
    rw [← TauCeti.ExteriorAlgebra.integerGrading_natCast,
      ← map_signedSymPiece_exteriorEquiv G hG d]
    exact ⟨a, ha, rfl⟩
  have hzero : e a = 0 :=
    congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt d hd ⟨e a, hmem⟩)
  exact e.injective (hzero.trans (map_zero e).symm)

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
