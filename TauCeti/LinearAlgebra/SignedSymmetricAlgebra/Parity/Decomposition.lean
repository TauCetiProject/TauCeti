/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Algebra.Operations
import TauCeti.Algebra.DirectSum.Component
import TauCeti.Data.ZMod.IntUnitsPower
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Parity decomposition of the signed symmetric algebra

For an internally integer-graded `R`-module `V` with grading `G`, splitting `V` into its even and
odd parity summands `TauCeti.parityGrading G.piece 0` and `TauCeti.parityGrading G.piece 1`
compares `TauCeti.SignedSym G` with the tensor product of the symmetric algebra on the even part
and the exterior algebra on the odd part: `SignedSym G ≃ₐ[R]
SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R] ExteriorAlgebra R (parityGrading G.piece 1)`.
Because `SymmetricAlgebra R (parityGrading G.piece 0)` has purely even parity, the Koszul sign
between the two tensor factors is `+1`, so their super tensor product is Mathlib's ordinary
`Algebra.TensorProduct`.

We separate the maps that hold over an arbitrary commutative ring from those that require `2` to
be invertible:

* Over any commutative ring `R`, even-parity generators are central in `SignedSym G`, giving the
  inclusion `fromSymmetricEven`, the factor projections `toSymmetricEven` and `toExteriorOdd`
  (hence injectivity of `fromSymmetricEven`), and the comparison map `toSymTensorExterior`.
* When `Invertible (2 : R)` holds (in particular over `ℚ`), odd-parity generators in `SignedSym G`
  square to zero, giving `fromExteriorOdd`, `fromSymTensorExterior`, the algebra equivalence
  `symTensorExteriorEquiv`, and module freeness of `SignedSym G` when its parity pieces (or all
  graded pieces) are free.

The comparison respects parity, word length (`TauCeti.SignedSym.lengthPiece`), and functoriality
along degree-preserving linear maps (`TauCeti.SignedSym.map`). For the purely even and purely odd
specializations (`symmetricAlgebraEquiv`, `toExteriorAlgebra`, `exteriorAlgebraEquiv`, and
single-degree grading identification), see
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.SymmetricExterior`.

The construction realizes the polynomial-exterior description of the free supercommutative algebra
in J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1).

## Main definitions

* `TauCeti.SignedSym.fromSymmetricEven`, `TauCeti.SignedSym.toSymmetricEven`: inclusion and
  projection for `SymmetricAlgebra R (parityGrading G.piece 0)`, over any commutative ring.
* `TauCeti.SignedSym.toExteriorOdd`, `TauCeti.SignedSym.fromExteriorOdd`: projection and (for
  `Invertible (2 : R)`) inclusion for `ExteriorAlgebra R (parityGrading G.piece 1)`.
* `TauCeti.SignedSym.toSymTensorExterior`, `TauCeti.SignedSym.fromSymTensorExterior`,
  `TauCeti.SignedSym.symTensorExteriorEquiv`: the tensor comparison maps and algebra equivalence.

## Main results

* `TauCeti.SignedSym.fromSymmetricEven_injective`, `TauCeti.SignedSym.fromExteriorOdd_injective`,
  `TauCeti.SignedSym.toSymmetricEven_surjective`, `TauCeti.SignedSym.toExteriorOdd_surjective`, and
  `TauCeti.SignedSym.toSymTensorExterior_surjective`: injectivity of the factor inclusions and
  characteristic-free surjectivity of the projections.
* `TauCeti.SignedSym.map_lengthPiece_toSymmetricEven`,
  `TauCeti.SignedSym.map_lengthPiece_toExteriorOdd`,
  `TauCeti.SignedSym.map_parityGrading_toExteriorOdd`,
  `TauCeti.SignedSym.map_lengthPiece_toSymTensorExterior`, and
  `TauCeti.SignedSym.map_parityGrading_toSymTensorExterior`: compatibility of the factor
  projections and `toSymTensorExterior` with word length and parity over any commutative ring (and
  hence of `symTensorExteriorEquiv` when `2` is invertible).
* `TauCeti.SignedSym.instModuleFree`: freeness of `SignedSym G` as an `R`-module when `2` is
  invertible and the parity summands of `V` (for instance when all graded pieces `G.piece p`, via
  `TauCeti.instModuleFreeCoarsenGrading`) are free `R`-modules.
-/

public section

open DirectSum
open scoped TensorProduct

namespace TauCeti.SignedSym

universe u v w

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V ℤ)

/-! ### Even and odd factor inclusions and projections -/

/-- The canonical algebra map from the symmetric algebra on the even part of `V` into
`SignedSym G`; even-parity generators are central, so no invertibility of `2` is required. -/
def fromSymmetricEven : SymmetricAlgebra R (parityGrading G.piece 0) →ₐ[R] SignedSym G :=
  SymmetricAlgebra.liftOfCommute
    ⟨(generator G).comp (parityGrading G.piece 0).subtype, fun x _ =>
      commute_of_mem_parityGrading_zero G (generator_mem_parityGrading G x.2) _⟩

/-- `fromSymmetricEven` maps each symmetric generator to the corresponding `SignedSym` generator. -/
@[simp]
theorem fromSymmetricEven_ι (x : parityGrading G.piece 0) :
    fromSymmetricEven G (SymmetricAlgebra.ι R (parityGrading G.piece 0) x) = generator G x :=
  SymmetricAlgebra.liftOfCommute_ι_apply _ _ x

/-- Every element in the image of `fromSymmetricEven` has even parity. -/
theorem fromSymmetricEven_mem_parityGrading_zero
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ parityGrading (signedSymPiece G) 0 := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    simpa only [AlgHom.commutes] using
      SetLike.algebraMap_mem_graded (parityGrading (signedSymPiece G)) r
  | ι x => simpa only [fromSymmetricEven_ι] using generator_mem_parityGrading G x.2
  | mul a b ha hb => simpa only [map_mul, zero_add] using SetLike.mul_mem_graded ha hb
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- Every element in the image of `fromSymmetricEven` lies in the center of `SignedSym G`. -/
theorem fromSymmetricEven_mem_center (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ Subalgebra.center R (SignedSym G) :=
  mem_center_of_mem_parityGrading_zero G (fromSymmetricEven_mem_parityGrading_zero G s)

/-- Every element in the image of `fromSymmetricEven` commutes with all of `SignedSym G`. -/
theorem commute_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (a : SignedSym G) : Commute (fromSymmetricEven G s) a :=
  commute_of_mem_parityGrading_zero G (fromSymmetricEven_mem_parityGrading_zero G s) a

/-- `fromSymmetricEven` carries homogeneous polynomials of degree `n` into word length `n`. -/
theorem fromSymmetricEven_mem_lengthPiece {n : ℕ}
    {s : SymmetricAlgebra R (parityGrading G.piece 0)}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n) :
    fromSymmetricEven G s ∈ lengthPiece G n := by
  rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule] at hs
  rw [lengthPiece_def]
  exact (fromSymmetricEven G).apply_mem_pow_of_mem_pow
    (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x.1, by simp⟩) hs

/-- The algebra projection from `SignedSym G` onto the symmetric algebra of the even part of `V`,
sending odd-parity generators to zero. No invertibility of `2` is needed. -/
noncomputable def toSymmetricEven :
    SignedSym G →ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) :=
  lift G ((SymmetricAlgebra.ι R (parityGrading G.piece 0)).comp
      (homogeneousProj (parityGrading G.piece) 0)) <| by
    intro p q x y hx _
    simp only [LinearMap.comp_apply, homogeneousProj_apply]
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    by_cases hp : (p : ZMod 2) = 0
    · rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul, hp, zero_mul, uzpow_zero, Units.val_one,
        one_smul, mul_comm]
    · simp [decompose_apply_of_mem_ne (parityGrading G.piece) hx' hp]

/-- On generators, `toSymmetricEven` projects onto the even parity component. -/
@[simp]
theorem toSymmetricEven_generator (x : V) :
    toSymmetricEven G (generator G x) = SymmetricAlgebra.ι R (parityGrading G.piece 0)
      (DirectSum.decompose (parityGrading G.piece) x 0) := by simp [toSymmetricEven]

/-- On an even-parity generator, `toSymmetricEven` is the canonical symmetric-algebra generator. -/
theorem toSymmetricEven_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) :
    toSymmetricEven G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ := by
  rw [toSymmetricEven_generator, decompose_apply_of_mem_same (parityGrading G.piece) hx]

/-- `toSymmetricEven` annihilates odd-parity generators. -/
theorem toSymmetricEven_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) : toSymmetricEven G (generator G x) = 0 := by
  rw [toSymmetricEven_generator,
    decompose_apply_of_mem_ne (parityGrading G.piece) hx (by decide), map_zero]

/-- Over any commutative ring, `toSymmetricEven` annihilates elements of odd parity. -/
theorem toSymmetricEven_eq_zero_of_mem_parityGrading_one {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 1) : toSymmetricEven G a = 0 := by
  let ℬ : ZMod 2 → Submodule R (SymmetricAlgebra R (parityGrading G.piece 0)) :=
    fun k => if k = 0 then ⊤ else ⊥
  have : SetLike.GradedOne ℬ := ⟨Submodule.mem_top⟩
  have : SetLike.GradedMul ℬ := ⟨fun i j _ _ hi hj => by
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) i with rfl | rfl <;>
      rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) j with rfl | rfl <;> simp_all [ℬ]⟩
  have : SetLike.GradedMonoid ℬ := {}
  have hhom : LinearMap.IsHomogeneous (toSymmetricEven G).toLinearMap
      (parityGrading (signedSymPiece G)) ℬ 0 := by
    unfold toSymmetricEven
    refine isHomogeneous_lift_coarsenGrading G (Int.castAddHom (ZMod 2)) ℬ _ _ fun q x hx => ?_
    have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
    by_cases hq : (q : ZMod 2) = 0
    · simp [ℬ, hq]
    · simp [ℬ, hq, homogeneousProj_apply, decompose_apply_of_mem_ne (parityGrading G.piece) hx' hq]
  simpa [ℬ] using hhom.map_mem ha

/-- Over any commutative ring, `toSymmetricEven` maps `lengthPiece G n` onto the degree-`n`
homogeneous submodule of `SymmetricAlgebra R (parityGrading G.piece 0)`. -/
theorem map_lengthPiece_toSymmetricEven (n : ℕ) :
    (lengthPiece G n).map (toSymmetricEven G).toLinearMap =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n := by
  rw [lengthPiece_def, TauCeti.SymmetricAlgebra.homogeneousSubmodule, Submodule.map_pow,
    ← LinearMap.range_comp]
  refine congrArg (· ^ n) (le_antisymm ?_ ?_)
  · rintro _ ⟨x, rfl⟩; exact ⟨DirectSum.decompose (parityGrading G.piece) x 0, by simp⟩
  · rintro _ ⟨x, rfl⟩; exact ⟨x.1, toSymmetricEven_generator_of_mem_parityGrading_zero G x.2⟩

/-- Over any commutative ring, `toSymmetricEven` preserves word length. -/
theorem toSymmetricEven_mem_homogeneousSubmodule {n : ℕ} {a : SignedSym G}
    (ha : a ∈ lengthPiece G n) : toSymmetricEven G a ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n := by
  rw [← map_lengthPiece_toSymmetricEven G n, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- `toSymmetricEven` is a left inverse to `fromSymmetricEven` as an algebra homomorphism. -/
@[simp]
theorem toSymmetricEven_comp_fromSymmetricEven :
    (toSymmetricEven G).comp (fromSymmetricEven G) =
      AlgHom.id R (SymmetricAlgebra R (parityGrading G.piece 0)) := by
  ext x; simp [toSymmetricEven_generator_of_mem_parityGrading_zero G x.2]

/-- Applying `toSymmetricEven` after `fromSymmetricEven` recovers the original element. -/
@[simp]
theorem toSymmetricEven_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymmetricEven G (fromSymmetricEven G s) = s :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `fromSymmetricEven G` embeds the even symmetric algebra injectively
into `SignedSym G`. -/
theorem fromSymmetricEven_injective : Function.Injective (fromSymmetricEven G) :=
  Function.LeftInverse.injective (toSymmetricEven_fromSymmetricEven G)

/-- Over any commutative ring, `toSymmetricEven G` is surjective. -/
theorem toSymmetricEven_surjective : Function.Surjective (toSymmetricEven G) :=
  Function.RightInverse.surjective (toSymmetricEven_fromSymmetricEven G)

/-- Membership of `fromSymmetricEven G s` in `lengthPiece G n` is equivalent to `s` being
homogeneous of degree `n`, over any commutative ring. -/
@[simp]
theorem fromSymmetricEven_mem_lengthPiece_iff {n : ℕ}
    {s : SymmetricAlgebra R (parityGrading G.piece 0)} :
    fromSymmetricEven G s ∈ lengthPiece G n ↔
      s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) n :=
  ⟨fun h => by simpa using toSymmetricEven_mem_homogeneousSubmodule G h,
    fromSymmetricEven_mem_lengthPiece G⟩

/-- The algebra projection from `SignedSym G` onto the exterior algebra of the odd part of `V`,
sending even-parity generators to zero. Exterior generators square to zero and hence anticommute
over any commutative ring, so no invertibility of `2` is needed. -/
noncomputable def toExteriorOdd :
    SignedSym G →ₐ[R] ExteriorAlgebra R (parityGrading G.piece 1) :=
  lift G ((ExteriorAlgebra.ι R (M := parityGrading G.piece 1)).comp
      (homogeneousProj (parityGrading G.piece) 1)) <| by
    intro p q x y hx hy
    simp only [LinearMap.comp_apply, homogeneousProj_apply]
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    have hy' : y ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hy
    by_cases hp : (p : ZMod 2) = 1
    · by_cases hq : (q : ZMod 2) = 1
      · rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul, hp, hq, mul_one, uzpow_one, Units.val_neg,
          Units.val_one, neg_smul, one_smul]
        exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      · simp [decompose_apply_of_mem_ne (parityGrading G.piece) hy' hq]
    · simp [decompose_apply_of_mem_ne (parityGrading G.piece) hx' hp]

/-- On generators, `toExteriorOdd` projects onto the odd parity component. -/
@[simp]
theorem toExteriorOdd_generator (x : V) :
    toExteriorOdd G (generator G x) =
      ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) := by
  simp [toExteriorOdd]

/-- `toExteriorOdd` annihilates even-parity generators. -/
theorem toExteriorOdd_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : toExteriorOdd G (generator G x) = 0 := by
  rw [toExteriorOdd_generator,
    decompose_apply_of_mem_ne (parityGrading G.piece) hx (by decide), map_zero]

/-- On an odd-parity generator, `toExteriorOdd` is the canonical exterior-algebra generator. -/
theorem toExteriorOdd_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    toExteriorOdd G (generator G x) = ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  rw [toExteriorOdd_generator, decompose_apply_of_mem_same (parityGrading G.piece) hx]

/-- Composing `toExteriorOdd` with `fromSymmetricEven` factors through the augmentation
`SymmetricAlgebra.algebraMapInv`, over any commutative ring. -/
@[simp]
theorem toExteriorOdd_comp_fromSymmetricEven :
    (toExteriorOdd G).comp (fromSymmetricEven G) =
      (Algebra.ofId R (ExteriorAlgebra R (parityGrading G.piece 1))).comp
        SymmetricAlgebra.algebraMapInv := by
  ext x; simp [toExteriorOdd_generator_of_mem_parityGrading_zero G x.2,
    SymmetricAlgebra.algebraMapInv_ι]

/-- Applying `toExteriorOdd` after `fromSymmetricEven` extracts the constant term as a scalar,
over any commutative ring. -/
@[simp]
theorem toExteriorOdd_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toExteriorOdd G (fromSymmetricEven G s) =
      algebraMap R (ExteriorAlgebra R (parityGrading G.piece 1))
        (SymmetricAlgebra.algebraMapInv s) :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toExteriorOdd G` is surjective. -/
theorem toExteriorOdd_surjective : Function.Surjective (toExteriorOdd G) :=
  ExteriorAlgebra.induction
    (fun r => ⟨algebraMap R _ r, AlgHom.commutes _ r⟩)
    (fun x => ⟨generator G x.1, toExteriorOdd_generator_of_mem_parityGrading_one G x.2⟩)
    (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩)

/-- Over any commutative ring, `toExteriorOdd` maps `lengthPiece G n` onto the `n`-th exterior
power of `parityGrading G.piece 1`. -/
theorem map_lengthPiece_toExteriorOdd (n : ℕ) :
    (lengthPiece G n).map (toExteriorOdd G).toLinearMap = ⋀[R]^n (parityGrading G.piece 1) := by
  rw [lengthPiece_def, _root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    ← LinearMap.range_comp]
  refine congrArg (· ^ n) (le_antisymm ?_ ?_)
  · rintro _ ⟨x, rfl⟩; exact ⟨DirectSum.decompose (parityGrading G.piece) x 1, by simp⟩
  · rintro _ ⟨x, rfl⟩; exact ⟨x.1, toExteriorOdd_generator_of_mem_parityGrading_one G x.2⟩

/-- Over any commutative ring, `toExteriorOdd` maps word length `n` into `⋀[R]^n`. -/
theorem toExteriorOdd_mem_exteriorPower {n : ℕ} {a : SignedSym G} (ha : a ∈ lengthPiece G n) :
    toExteriorOdd G a ∈ ⋀[R]^n (parityGrading G.piece 1) := by
  rw [← map_lengthPiece_toExteriorOdd G n, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- Over any commutative ring, `toExteriorOdd` preserves parity with respect to
`TauCeti.ExteriorAlgebra.integerGrading`. -/
theorem toExteriorOdd_mem_parityGrading {k : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) k) :
    toExteriorOdd G a ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k := by
  have hhom : LinearMap.IsHomogeneous (toExteriorOdd G).toLinearMap
      (parityGrading (signedSymPiece G))
      (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1))) 0 := by
    unfold toExteriorOdd
    refine isHomogeneous_lift_coarsenGrading G (Int.castAddHom (ZMod 2)) _ _ _ fun q x hx => ?_
    simp only [LinearMap.comp_apply, homogeneousProj_apply, Int.coe_castAddHom]
    have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
    rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq
    · rw [hq] at hx' ⊢
      rw [decompose_apply_of_mem_ne (parityGrading G.piece) hx' (by decide), map_zero]
      exact zero_mem _
    · rw [hq] at hx' ⊢
      rw [decompose_apply_of_mem_same (parityGrading G.piece) hx']
      exact mem_parityGrading_of_mem
        (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (R := R)
          (⟨x, hx'⟩ : parityGrading G.piece 1))
  simpa only [add_zero, AlgHom.toLinearMap_apply] using hhom.map_mem ha

/-- When `2` is invertible, odd-parity generators in `SignedSym G` square to zero, inducing the
canonical algebra map from the exterior algebra on the odd part of `V`. -/
def fromExteriorOdd [Invertible (2 : R)] :
    ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R] SignedSym G :=
  ExteriorAlgebra.lift R ⟨(generator G).comp (parityGrading G.piece 1).subtype, fun x => by
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← pow_two] using
      generator_sq_eq_zero_of_mem_parityGrading_one G x.2⟩

/-- `fromExteriorOdd` maps each exterior generator to the corresponding `SignedSym` generator. -/
@[simp]
theorem fromExteriorOdd_ι [Invertible (2 : R)] (x : parityGrading G.piece 1) :
    fromExteriorOdd G (ExteriorAlgebra.ι R x) = generator G x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ x

/-- `toExteriorOdd` is a left inverse to `fromExteriorOdd` as an algebra homomorphism. -/
@[simp]
theorem toExteriorOdd_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toExteriorOdd G).comp (fromExteriorOdd G) =
      AlgHom.id R (ExteriorAlgebra R (parityGrading G.piece 1)) := by
  ext x; simp [toExteriorOdd_generator_of_mem_parityGrading_one G x.2]

/-- Applying `toExteriorOdd` after `fromExteriorOdd` recovers the original exterior element. -/
@[simp]
theorem toExteriorOdd_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toExteriorOdd G (fromExteriorOdd G e) = e :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromExteriorOdd G) e

/-- When `2` is invertible, composing `toSymmetricEven` with `fromExteriorOdd` factors through
the augmentation `ExteriorAlgebra.algebraMapInv`. -/
@[simp]
theorem toSymmetricEven_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymmetricEven G).comp (fromExteriorOdd G) =
      (Algebra.ofId R (SymmetricAlgebra R (parityGrading G.piece 0))).comp
        ExteriorAlgebra.algebraMapInv := by
  ext x; simp [toSymmetricEven_generator_of_mem_parityGrading_one G x.2,
    ExteriorAlgebra.algebraMapInv]

/-- When `2` is invertible, applying `toSymmetricEven` after `fromExteriorOdd` extracts the
constant term as a scalar. -/
@[simp]
theorem toSymmetricEven_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymmetricEven G (fromExteriorOdd G e) =
      algebraMap R (SymmetricAlgebra R (parityGrading G.piece 0))
        (ExteriorAlgebra.algebraMapInv e) :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromExteriorOdd G) e

/-- When `2` is invertible, `fromExteriorOdd G` is injective. -/
theorem fromExteriorOdd_injective [Invertible (2 : R)] : Function.Injective (fromExteriorOdd G) :=
  Function.LeftInverse.injective (toExteriorOdd_fromExteriorOdd G)

/-- `fromExteriorOdd` carries `n`-th exterior powers into word length `n`. -/
theorem fromExteriorOdd_mem_lengthPiece [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ ⋀[R]^n (parityGrading G.piece 1)) : fromExteriorOdd G e ∈ lengthPiece G n := by
  rw [_root_.ExteriorAlgebra.exteriorPower] at he
  rw [lengthPiece_def]
  exact (fromExteriorOdd G).apply_mem_pow_of_mem_pow
    (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x.1, by simp⟩) he

/-- When `2` is invertible, membership of `fromExteriorOdd G e` in `lengthPiece G n` is
equivalent to `e` lying in the `n`-th exterior power. -/
@[simp]
theorem fromExteriorOdd_mem_lengthPiece_iff [Invertible (2 : R)] {n : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromExteriorOdd G e ∈ lengthPiece G n ↔ e ∈ ⋀[R]^n (parityGrading G.piece 1) :=
  ⟨fun h => by simpa using toExteriorOdd_mem_exteriorPower G h, fromExteriorOdd_mem_lengthPiece G⟩

/-! ### The tensor product comparison and algebra equivalence -/

private noncomputable def symTensorExteriorGenerator :
    V →ₗ[R] SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) :=
  Algebra.TensorProduct.includeLeft.toLinearMap.comp
      ((SymmetricAlgebra.ι R (parityGrading G.piece 0)).comp
        (homogeneousProj (parityGrading G.piece) 0)) +
    Algebra.TensorProduct.includeRight.toLinearMap.comp
      ((ExteriorAlgebra.ι R (M := parityGrading G.piece 1)).comp
        (homogeneousProj (parityGrading G.piece) 1))

private theorem symTensorExteriorGenerator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : symTensorExteriorGenerator G x =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 := by
  simp [symTensorExteriorGenerator, decompose_apply_of_mem_same (parityGrading G.piece) hx,
    decompose_apply_of_mem_ne (j := 1) (parityGrading G.piece) hx (by decide)]

private theorem symTensorExteriorGenerator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    symTensorExteriorGenerator G x = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  simp [symTensorExteriorGenerator, decompose_apply_of_mem_same (parityGrading G.piece) hx,
    decompose_apply_of_mem_ne (j := 0) (parityGrading G.piece) hx (by decide)]

/-- The comparison algebra homomorphism from `SignedSym G` to
`SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R] ExteriorAlgebra R (parityGrading G.piece 1)`,
sending each generator `x = x₀ + x₁` to `ι x₀ ⊗ₜ 1 + 1 ⊗ₜ ι x₁` over any commutative ring. -/
noncomputable def toSymTensorExterior :
    SignedSym G →ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) :=
  lift G (symTensorExteriorGenerator G) <| by
    intro p q x y hx hy
    have hx' : x ∈ parityGrading G.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
    have hy' : y ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hy
    rw [← uzpow_intCast_eq_negOnePow, Int.cast_mul]
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) (p : ZMod 2) with hp | hp <;>
      rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) (q : ZMod 2) with hq | hq <;>
      (rw [hp] at hx' ⊢; rw [hq] at hy' ⊢)
    · simp [symTensorExteriorGenerator_of_mem_parityGrading_zero G hx',
        symTensorExteriorGenerator_of_mem_parityGrading_zero G hy', mul_comm]
    · simp [symTensorExteriorGenerator_of_mem_parityGrading_zero G hx',
        symTensorExteriorGenerator_of_mem_parityGrading_one G hy']
    · simp [symTensorExteriorGenerator_of_mem_parityGrading_one G hx',
        symTensorExteriorGenerator_of_mem_parityGrading_zero G hy']
    · rw [symTensorExteriorGenerator_of_mem_parityGrading_one G hx',
        symTensorExteriorGenerator_of_mem_parityGrading_one G hy',
        Algebra.TensorProduct.tmul_mul_tmul,
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), TensorProduct.tmul_neg]
      simp

/-- `toSymTensorExterior` splits a generator into its even symmetric and odd exterior parts. -/
@[simp]
theorem toSymTensorExterior_generator (x : V) :
    toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0)
          (DirectSum.decompose (parityGrading G.piece) x 0) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) := by
  simp [toSymTensorExterior, symTensorExteriorGenerator]

/-- On an even-parity generator, `toSymTensorExterior` lands in the left tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_parityGrading_zero G hx)

/-- On an odd-parity generator, `toSymTensorExterior` lands in the right tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    toSymTensorExterior G (generator G x) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_parityGrading_one G hx)

/-- Over any commutative ring, `toSymTensorExterior` embeds `fromSymmetricEven` as the left tensor
inclusion `s ↦ s ⊗ₜ 1`. -/
@[simp]
theorem toSymTensorExterior_comp_fromSymmetricEven :
    (toSymTensorExterior G).comp (fromSymmetricEven G) = Algebra.TensorProduct.includeLeft := by
  ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_zero G x.2]

/-- Pointwise form of `toSymTensorExterior_comp_fromSymmetricEven`. -/
@[simp]
theorem toSymTensorExterior_fromSymmetricEven
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymTensorExterior G (fromSymmetricEven G s) = s ⊗ₜ[R] 1 :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toSymTensorExterior G` is surjective. -/
theorem toSymTensorExterior_surjective : Function.Surjective (toSymTensorExterior G) := by
  have hright : ∀ e : ExteriorAlgebra R (parityGrading G.piece 1),
      ∃ b, toSymTensorExterior G b = 1 ⊗ₜ[R] e :=
    ExteriorAlgebra.induction
      (fun r => ⟨algebraMap R _ r,
        (AlgHom.commutes _ r).trans (Algebra.TensorProduct.includeRight.commutes r).symm⟩)
      (fun x => ⟨generator G x.1, toSymTensorExterior_generator_of_mem_parityGrading_one G x.2⟩)
      (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ =>
        ⟨a * b, by rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, mul_one]⟩)
      (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩)
  refine fun z => TensorProduct.inductionOn z (fun s e => ?_)
    fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [map_add, ha, hb]⟩
  obtain ⟨b, hb⟩ := hright e
  exact ⟨fromSymmetricEven G s * b, by rw [map_mul, toSymTensorExterior_fromSymmetricEven, hb,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩

/-- When `2` is invertible, `toSymTensorExterior` embeds `fromExteriorOdd` as the right tensor
inclusion `e ↦ 1 ⊗ₜ e`. -/
@[simp]
theorem toSymTensorExterior_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromExteriorOdd G) = Algebra.TensorProduct.includeRight := by
  ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_one G x.2]

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
      ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R] SignedSym G :=
  Algebra.TensorProduct.lift (fromSymmetricEven G) (fromExteriorOdd G) fun s e =>
    commute_fromSymmetricEven G s (fromExteriorOdd G e)

/-- On a pure tensor, `fromSymTensorExterior` multiplies the images of the two factors. -/
@[simp]
theorem fromSymTensorExterior_tmul [Invertible (2 : R)]
    (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    fromSymTensorExterior G (s ⊗ₜ[R] e) = fromSymmetricEven G s * fromExteriorOdd G e :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Composing `fromSymTensorExterior` with `includeLeft` recovers `fromSymmetricEven`. -/
@[simp]
theorem fromSymTensorExterior_comp_includeLeft [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeLeft = fromSymmetricEven G := by
  ext x; simp

/-- Composing `fromSymTensorExterior` with `includeRight` recovers `fromExteriorOdd`. -/
@[simp]
theorem fromSymTensorExterior_comp_includeRight [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeRight = fromExteriorOdd G := by
  ext x; simp

/-- `toSymTensorExterior` followed by `fromSymTensorExterior` is the identity on `SignedSym G`. -/
@[simp]
theorem fromSymTensorExterior_comp_toSymTensorExterior [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp (toSymTensorExterior G) = AlgHom.id R (SignedSym G) := by
  ext x
  simp only [AlgHom.comp_apply, AlgHom.id_apply, toSymTensorExterior_generator, map_add,
    fromSymTensorExterior_tmul, map_one, mul_one, one_mul, fromSymmetricEven_ι, fromExteriorOdd_ι]
  rw [← map_add, coe_decompose_zero_add_coe_decompose_one]

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
      AlgHom.id R (SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1)) := by
  apply Algebra.TensorProduct.ext
  · ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_zero G x.2]
  · ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_one G x.2]

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
    SignedSym G ≃ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) :=
  AlgEquiv.ofAlgHom (toSymTensorExterior G) (fromSymTensorExterior G)
    (toSymTensorExterior_comp_fromSymTensorExterior G)
    (fromSymTensorExterior_comp_toSymTensorExterior G)

/-- The forward direction of `symTensorExteriorEquiv` is `toSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_apply [Invertible (2 : R)] (a : SignedSym G) :
    symTensorExteriorEquiv G a = toSymTensorExterior G a := by simp [symTensorExteriorEquiv]

/-- The underlying algebra homomorphism of `symTensorExteriorEquiv` is `toSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toAlgHom = toSymTensorExterior G :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

/-- The underlying linear map of `symTensorExteriorEquiv` is that of `toSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearMap = (toSymTensorExterior G).toLinearMap :=
  AlgEquiv.toLinearMap_ofAlgHom _ _ _ _

/-- The inverse of `symTensorExteriorEquiv` is `fromSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_symm_apply [Invertible (2 : R)]
    (z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)) :
    (symTensorExteriorEquiv G).symm z = fromSymTensorExterior G z := by
  simp [symTensorExteriorEquiv]

/-- The underlying algebra homomorphism of `(symTensorExteriorEquiv G).symm` is
`fromSymTensorExterior`. -/
@[simp]
theorem symTensorExteriorEquiv_symm_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).symm.toAlgHom = fromSymTensorExterior G :=
  AlgHom.ext (symTensorExteriorEquiv_symm_apply G)

/-- The underlying linear map of `(symTensorExteriorEquiv G).symm` is that of
`fromSymTensorExterior`. Because `AlgEquiv.toLinearMap` unfolds via `AlgEquiv.toLinearEquiv`, the
`@[simp]` normal form is `symTensorExteriorEquiv_toLinearEquiv_symm_toLinearMap`. -/
theorem symTensorExteriorEquiv_symm_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).symm.toLinearMap = (fromSymTensorExterior G).toLinearMap :=
  LinearMap.ext (symTensorExteriorEquiv_symm_apply G)

/-- Normal-form `@[simp]` version of `symTensorExteriorEquiv_symm_toLinearMap`. -/
@[simp]
theorem symTensorExteriorEquiv_toLinearEquiv_symm_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearEquiv.symm.toLinearMap =
      (fromSymTensorExterior G).toLinearMap :=
  symTensorExteriorEquiv_symm_toLinearMap G

/-! ### Module freeness -/

/-- When `2` is invertible and both parity summands of `V` are free `R`-modules, `SignedSym G` is
a free `R`-module. In particular, this applies automatically when every graded piece `G.piece p`
is free, via `TauCeti.instModuleFreeCoarsenGrading`. -/
instance instModuleFree [Invertible (2 : R)]
    [Module.Free R (parityGrading G.piece 0)] [Module.Free R (parityGrading G.piece 1)] :
    Module.Free R (SignedSym G) :=
  Module.Free.of_equiv (symTensorExteriorEquiv G).symm.toLinearEquiv

/-! ### Word-length and parity compatibility -/

private theorem exists_preimage_of_mem_exteriorPower {j : ℕ}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ ⋀[R]^j (parityGrading G.piece 1)) :
    ∃ b, b ∈ lengthPiece G j ∧ b ∈ parityGrading (signedSymPiece G) (j : ZMod 2) ∧
      toExteriorOdd G b = e ∧ toSymTensorExterior G b = 1 ⊗ₜ[R] e := by
  rw [_root_.ExteriorAlgebra.exteriorPower] at he
  induction he using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    exact ⟨algebraMap R (SignedSym G) r, SetLike.algebraMap_mem_graded (lengthPiece G) r,
      Nat.cast_zero (R := ZMod 2) ▸ SetLike.algebraMap_mem_graded
        (parityGrading (signedSymPiece G)) r, AlgHom.commutes _ r,
      (AlgHom.commutes _ r).trans (Algebra.TensorProduct.includeRight.commutes r).symm⟩
  | add x y k _ _ hx hy =>
    obtain ⟨bx, hbx_len, hbx_par, hbx_odd, hbx_eq⟩ := hx
    obtain ⟨by_, hby_len, hby_par, hby_odd, hby_eq⟩ := hy
    exact ⟨bx + by_, add_mem hbx_len hby_len, add_mem hbx_par hby_par,
      by rw [map_add, hbx_odd, hby_odd], by rw [map_add, hbx_eq, hby_eq, TensorProduct.tmul_add]⟩
  | mem_mul u hu k y _ hy =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨b, hb_len, hb_par, hb_odd, hb_eq⟩ := hy
    refine ⟨generator G x.1 * b, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_comm 1 k] using
        SetLike.mul_mem_graded (generator_mem_lengthPiece G x.1) hb_len
    · rw [Nat.cast_succ, add_comm _ (1 : ZMod 2)]
      exact SetLike.mul_mem_graded (generator_mem_parityGrading G x.2) hb_par
    · rw [map_mul, toExteriorOdd_generator_of_mem_parityGrading_one G x.2, hb_odd]
    · rw [map_mul, toSymTensorExterior_generator_of_mem_parityGrading_one G x.2, hb_eq,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Over any commutative ring, `toExteriorOdd` maps the parity-`k` piece of `SignedSym G` onto
the parity-`k` piece of `ExteriorAlgebra R (parityGrading G.piece 1)`. -/
theorem map_parityGrading_toExteriorOdd (k : ZMod 2) :
    (parityGrading (signedSymPiece G) k).map (toExteriorOdd G).toLinearMap =
      parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k := by
  refine le_antisymm (by rintro _ ⟨a, ha, rfl⟩; exact toExteriorOdd_mem_parityGrading G ha) ?_
  intro e he
  refine coarsenGrading_induction he (fun p hp y hy => ?_) (zero_mem _) fun _ _ hx hy =>
    add_mem hx hy
  rcases lt_or_ge p 0 with hpneg | hpnonneg
  · rw [TauCeti.ExteriorAlgebra.integerGrading_of_neg hpneg, Submodule.mem_bot] at hy; simp [hy]
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpnonneg
  rw [TauCeti.ExteriorAlgebra.integerGrading_natCast] at hy
  have hk : (j : ZMod 2) = k := by simpa only [Int.coe_castAddHom, Int.cast_natCast] using hp
  obtain ⟨b, -, hb_par, hb_odd, -⟩ := exists_preimage_of_mem_exteriorPower G hy
  exact ⟨b, hk ▸ hb_par, hb_odd⟩

/-- Over any commutative ring, `toSymTensorExterior` maps the word-length-`n` submodule onto the
sum of the tensor products of symmetric degree `i` and exterior degree `j` with `i + j = n`. -/
theorem map_lengthPiece_toSymTensorExterior (n : ℕ) :
    (lengthPiece G n).map (toSymTensorExterior G).toLinearMap =
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂
          (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
            (ExteriorAlgebra R (parityGrading G.piece 1)))
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  let B (i j : ℕ) := Submodule.map₂
    (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
      (ExteriorAlgebra R (parityGrading G.piece 1)))
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
    (⋀[R]^j (parityGrading G.piece 1))
  let S (m : ℕ) := ⨆ (i : ℕ) (j : ℕ) (_ : i + j = m), B i j
  have mem_S {i j m : ℕ} (hij : i + j = m) {z} (hz : z ∈ B i j) : z ∈ S m :=
    Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hij hz))
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [AlgHom.toLinearMap_apply]
    refine length_induction G (P := fun m a => toSymTensorExterior G a ∈ S m)
      (fun r => ?_) (fun _ _ _ ha hb => by rw [map_add]; exact add_mem ha hb)
      (fun m x a ih => ?_) ha
    · rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      exact mem_S (i := 0) (j := 0) rfl <| Submodule.apply_mem_map₂ _
        (SetLike.algebraMap_mem_graded
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0)) r)
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
  · refine iSup₂_le fun i j => iSup_le fun hij => Submodule.map₂_le.mpr fun s hs e he => ?_
    obtain ⟨b, hb_len, -, -, hb_eq⟩ := exists_preimage_of_mem_exteriorPower G he
    exact ⟨fromSymmetricEven G s * b,
      hij ▸ SetLike.mul_mem_graded (fromSymmetricEven_mem_lengthPiece G hs) hb_len,
      by rw [TensorProduct.mk_apply, AlgHom.toLinearMap_apply, map_mul,
        toSymTensorExterior_fromSymmetricEven, hb_eq, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]⟩

/-- Over any commutative ring, `toSymTensorExterior` maps words of length `n` into the sum of the
bidegree `(i, j)` symmetric-exterior tensor pieces with `i + j = n`. -/
theorem toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower {n : ℕ}
    {a : SignedSym G} (ha : a ∈ lengthPiece G n) :
    toSymTensorExterior G a ∈
      ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂
          (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
            (ExteriorAlgebra R (parityGrading G.piece 1)))
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  rw [← map_lengthPiece_toSymTensorExterior G n, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- When `2` is invertible, `toSymTensorExterior G a` lies in the sum of the bidegree `(i, j)`
symmetric-exterior tensor pieces with `i + j = n` if and only if `a ∈ lengthPiece G n`. -/
@[simp]
theorem toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower_iff
    [Invertible (2 : R)] {n : ℕ} {a : SignedSym G} :
    toSymTensorExterior G a ∈
        (⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
          Submodule.map₂
            (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
              (ExteriorAlgebra R (parityGrading G.piece 1)))
            (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
            (⋀[R]^j (parityGrading G.piece 1))) ↔
      a ∈ lengthPiece G n := by
  refine ⟨fun h => ?_, toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower G⟩
  rcases (map_lengthPiece_toSymTensorExterior G n).symm ▸ h with ⟨b, hb, hab⟩
  rwa [← fromSymTensorExterior_toSymTensorExterior G a, ← hab, AlgHom.toLinearMap_apply,
    fromSymTensorExterior_toSymTensorExterior]

/-- When `2` is invertible, `fromSymTensorExterior G z` has word length `n` if and only if `z`
lies in the sum of the bidegree `(i, j)` symmetric-exterior tensor pieces with `i + j = n`. -/
@[simp]
theorem fromSymTensorExterior_mem_lengthPiece_iff [Invertible (2 : R)] {n : ℕ}
    {z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromSymTensorExterior G z ∈ lengthPiece G n ↔
      z ∈ ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n),
        Submodule.map₂
          (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
            (ExteriorAlgebra R (parityGrading G.piece 1)))
          (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (parityGrading G.piece 0) i)
          (⋀[R]^j (parityGrading G.piece 1)) := by
  rw [← toSymTensorExterior_mem_iSup_map₂_homogeneousSubmodule_exteriorPower_iff G,
    toSymTensorExterior_fromSymTensorExterior]

/-- Over any commutative ring, `toSymTensorExterior` maps the parity-`k` piece of `SignedSym G`
onto the submodule of tensors whose exterior factor has parity `k`. -/
theorem map_parityGrading_toSymTensorExterior (k : ZMod 2) :
    (parityGrading (signedSymPiece G) k).map (toSymTensorExterior G).toLinearMap =
      Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  let ℬ (j : ZMod 2) := Submodule.map₂
    (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
      (ExteriorAlgebra R (parityGrading G.piece 1)))
    ⊤ (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) j)
  have : SetLike.GradedOne ℬ := ⟨Submodule.apply_mem_map₂ _ Submodule.mem_top
    (SetLike.one_mem_graded
      (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1))))⟩
  have : SetLike.GradedMul ℬ := ⟨fun _ _ _ _ hu hv =>
    ((Submodule.map₂_tmul_mul_le _ _ _ _).trans
      (Submodule.map₂_le_map₂ le_top (coarsenGrading_mul_le _ _ _ _)))
      (Submodule.mul_mem_mul hu hv)⟩
  have : SetLike.GradedMonoid ℬ := {}
  refine le_antisymm ?_ (Submodule.map₂_le.mpr fun s _ e he => ?_)
  · have hhom : LinearMap.IsHomogeneous (toSymTensorExterior G).toLinearMap
        (parityGrading (signedSymPiece G)) ℬ 0 := by
      unfold toSymTensorExterior
      refine isHomogeneous_lift_coarsenGrading G (Int.castAddHom (ZMod 2)) ℬ _ _ fun q x hx => ?_
      simp only [Int.coe_castAddHom]
      have hx' : x ∈ parityGrading G.piece (q : ZMod 2) := mem_parityGrading_of_mem hx
      rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) (q : ZMod 2) with hq | hq <;>
        rw [hq] at hx' ⊢
      · rw [symTensorExteriorGenerator_of_mem_parityGrading_zero G hx']
        exact Submodule.apply_mem_map₂ _ Submodule.mem_top (SetLike.one_mem_graded _)
      · rw [symTensorExteriorGenerator_of_mem_parityGrading_one G hx']
        exact Submodule.apply_mem_map₂ _ Submodule.mem_top <| mem_parityGrading_of_mem
          (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (R := R)
            (⟨x, hx'⟩ : parityGrading G.piece 1))
    rintro _ ⟨a, ha, rfl⟩
    simpa only [add_zero] using hhom.map_mem ha
  · rw [TensorProduct.mk_apply]
    refine coarsenGrading_induction he (fun p hp y hy => ?_)
      (by rw [TensorProduct.tmul_zero]; exact zero_mem _) fun _ _ hx hy => by
        rw [TensorProduct.tmul_add]; exact add_mem hx hy
    rcases lt_or_ge p 0 with hpneg | hpnonneg
    · rw [TauCeti.ExteriorAlgebra.integerGrading_of_neg hpneg, Submodule.mem_bot] at hy; simp [hy]
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpnonneg
    rw [TauCeti.ExteriorAlgebra.integerGrading_natCast] at hy
    obtain ⟨b, -, hb_par, -, hb_eq⟩ := exists_preimage_of_mem_exteriorPower G hy
    have hk : (0 : ZMod 2) + (j : ZMod 2) = k := by
      simpa only [zero_add, Int.coe_castAddHom, Int.cast_natCast] using hp
    exact ⟨fromSymmetricEven G s * b,
      hk ▸ SetLike.mul_mem_graded (fromSymmetricEven_mem_parityGrading_zero G s) hb_par,
      by rw [AlgHom.toLinearMap_apply, map_mul, toSymTensorExterior_fromSymmetricEven, hb_eq,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩

/-- Over any commutative ring, `toSymTensorExterior` sends elements of parity `k` into the
submodule of tensors whose exterior factor has parity `k`. -/
theorem toSymTensorExterior_mem_map₂_top_parityGrading {k : ZMod 2} {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) k) :
    toSymTensorExterior G a ∈ Submodule.map₂
      (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
        (ExteriorAlgebra R (parityGrading G.piece 1)))
      ⊤ (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  rw [← map_parityGrading_toSymTensorExterior G k, ← AlgHom.toLinearMap_apply]
  exact Submodule.mem_map_of_mem ha

/-- When `2` is invertible, `toSymTensorExterior G a` lies in the submodule of tensors whose
exterior factor has parity `k` if and only if `a ∈ parityGrading (signedSymPiece G) k`. -/
@[simp]
theorem toSymTensorExterior_mem_map₂_top_parityGrading_iff [Invertible (2 : R)]
    {k : ZMod 2} {a : SignedSym G} :
    toSymTensorExterior G a ∈ Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) ↔
      a ∈ parityGrading (signedSymPiece G) k := by
  refine ⟨fun h => ?_, toSymTensorExterior_mem_map₂_top_parityGrading G⟩
  rcases (map_parityGrading_toSymTensorExterior G k).symm ▸ h with ⟨b, hb, hab⟩
  rwa [← fromSymTensorExterior_toSymTensorExterior G a, ← hab, AlgHom.toLinearMap_apply,
    fromSymTensorExterior_toSymTensorExterior]

/-- When `2` is invertible, `fromSymTensorExterior G z` has parity `k` if and only if `z` lies in
the submodule of tensors whose exterior factor has parity `k`. -/
@[simp]
theorem fromSymTensorExterior_mem_parityGrading_iff [Invertible (2 : R)] {k : ZMod 2}
    {z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromSymTensorExterior G z ∈ parityGrading (signedSymPiece G) k ↔
      z ∈ Submodule.map₂
        (TensorProduct.mk R (SymmetricAlgebra R (parityGrading G.piece 0))
          (ExteriorAlgebra R (parityGrading G.piece 1)))
        ⊤ (parityGrading
          (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) := by
  rw [← toSymTensorExterior_mem_map₂_top_parityGrading_iff G,
    toSymTensorExterior_fromSymTensorExterior]

/-- `fromExteriorOdd` preserves parity with respect to `TauCeti.ExteriorAlgebra.integerGrading`. -/
theorem fromExteriorOdd_mem_parityGrading [Invertible (2 : R)] {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)}
    (he : e ∈ parityGrading
      (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k) :
    fromExteriorOdd G e ∈ parityGrading (signedSymPiece G) k := by
  rw [← toSymTensorExterior_mem_map₂_top_parityGrading_iff G, toSymTensorExterior_fromExteriorOdd]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top he

/-- When `2` is invertible, `fromExteriorOdd G e` has parity `k` if and only if `e` has parity `k`
with respect to `TauCeti.ExteriorAlgebra.integerGrading`. -/
@[simp]
theorem fromExteriorOdd_mem_parityGrading_iff [Invertible (2 : R)] {k : ZMod 2}
    {e : ExteriorAlgebra R (parityGrading G.piece 1)} :
    fromExteriorOdd G e ∈ parityGrading (signedSymPiece G) k ↔
      e ∈ parityGrading (TauCeti.ExteriorAlgebra.integerGrading R (parityGrading G.piece 1)) k :=
  ⟨fun h => by simpa using toExteriorOdd_mem_parityGrading G h, fromExteriorOdd_mem_parityGrading G⟩

/-! ### Functoriality along degree-preserving maps -/

section Functoriality

variable {W : Type w} [AddCommGroup W] [Module R W] (H : InternalGrading R W ℤ)

/-- `fromSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymmetricEven (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromSymmetricEven G) =
      (fromSymmetricEven H).comp (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0)) := by
  ext x; simp

/-- `fromExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromExteriorOdd [Invertible (2 : R)] (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromExteriorOdd G) =
      (fromExteriorOdd H).comp (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1)) := by
  ext x; simp

/-- `toSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem toSymmetricEven_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toSymmetricEven H).comp (map G H f hf) =
      (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0)).comp (toSymmetricEven G) := by
  ext x; simp

/-- `toExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem toExteriorOdd_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toExteriorOdd H).comp (map G H f hf) =
      (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1)).comp (toExteriorOdd G) := by
  ext x; simp

/-- `toSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem toSymTensorExterior_comp_map (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (toSymTensorExterior H).comp (map G H f hf) =
      (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0))
        (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1))).comp (toSymTensorExterior G) := by
  ext x; simp

/-- `fromSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymTensorExterior [Invertible (2 : R)] (f : V →ₗ[R] W)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    (map G H f hf).comp (fromSymTensorExterior G) =
      (fromSymTensorExterior H).comp
        (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0))
          (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1))) := by
  apply Algebra.TensorProduct.ext
  · ext x; simp
  · ext x; simp

end Functoriality

end TauCeti.SignedSym
