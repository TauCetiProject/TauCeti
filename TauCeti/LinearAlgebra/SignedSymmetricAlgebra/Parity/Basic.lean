/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Coarsen

/-!
# Parity reduction of the signed symmetric algebra

Because `TauCeti.SignedSym` is defined over any Koszul-signed degree semiring `ι`
(`[CommSemiring ι] [DecidableEq ι] [Module ι (Additive ℤˣ)]`), taking `ι = ZMod 2` constructs the
free supercommutative algebra directly from a parity-graded module
`H : InternalGrading R V (ZMod 2)`, complete with its universal property, native `ZMod 2`-grading
`signedSymPiece H`, Koszul supercommutativity, word-length grading, and odd derivations
`liftDerivation`, without choosing an integer lift.

For an integer grading `G : InternalGrading R V ℤ`, specializing
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Coarsen` to `Int.castRingHom (ZMod 2) : ℤ →+* ZMod 2`
identifies the integer-graded orbit algebra `SignedSym G` with the parity-graded orbit algebra
`SignedSym G.parity` built directly from parities (`TauCeti.SignedSym.parityEquiv`). Under this
equivalence:
* parity-homogeneous generators in `G.parity.piece` supercommute in `SignedSym G` even when they mix
  several integer degrees (`TauCeti.SignedSym.generator_mul_generator_of_mem_parity`), and the
  Koszul relation ideal of `G.parity` in `TensorAlgebra R V` equals that of `G`
  (`TauCeti.SignedSym.ker_quotient_parity`);
* `signedSymPiece G.parity` corresponds to `parityGrading (signedSymPiece G)`, giving mutually
  inverse `ZMod 2`-graded algebra maps `toParity` and `ofParity`; in particular an element of
  integer degree `p` maps into parity `p mod 2` (`TauCeti.SignedSym.parityEquiv_mem_of_mem`);
* conjugating a degree-one signed derivation of `SignedSym G` across `parityEquiv` yields an odd
  signed derivation of `SignedSym G.parity`, extending a degree-one generator assignment before or
  after parity reduction produces the same odd derivation
  (`TauCeti.SignedSym.conj_parityEquiv_liftDerivation`), and `d` defines a differential graded
  algebra structure on `SignedSym G` if and only if its parity transport squares to zero
  (`TauCeti.SignedSym.isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero`).

## Main definitions

* `TauCeti.SignedSym.parityEquiv`: the canonical `R`-algebra equivalence
  `SignedSym G ≃ₐ[R] SignedSym G.parity`.
* `TauCeti.SignedSym.toParity` and `TauCeti.SignedSym.ofParity`: the mutually inverse
  `ZMod 2`-graded algebra homomorphisms identifying `parityGrading (signedSymPiece G)` with
  `signedSymPiece G.parity`.

## Main results

* `TauCeti.signedSwapRel.parity`: every homogeneous Koszul swap for `G` is a homogeneous Koszul swap
  for `G.parity`.
* `TauCeti.SignedSym.generator_mul_generator_of_mem_parity`: parity-homogeneous generators satisfy
  the parity Koszul sign rule in `SignedSym G`.
* `TauCeti.SignedSym.ker_quotient_parity`: the Koszul relation ideal in `TensorAlgebra R V` is
  unchanged under parity reduction.
* `TauCeti.SignedSym.parityEquiv_mem_signedSymPiece_iff` and
  `TauCeti.SignedSym.parityEquiv_symm_mem_parityGrading_iff`: homogeneous pieces of
  `SignedSym G.parity` match `parityGrading (signedSymPiece G)`.
* `TauCeti.SignedSym.isHomogeneous_conj_parityEquiv`,
  `TauCeti.SignedSym.conj_parityEquiv_mul_of_leibniz`,
  `TauCeti.SignedSym.conj_parityEquiv_liftDerivation`,
  `TauCeti.SignedSym.isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero`, and
  `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_parity`: transport of homogeneous maps, odd
  derivations, and `IsDGAlgebra` differentials across `parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48,
  for the parity-graded orbit algebra and its comparison with an integer Conley–Zehnder lift.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*,
  Geom. Funct. Anal. (2000), 560–673, for `ℤ/2ℤ`-graded SFT orbit algebras when integer gradings
  reduce modulo `2`.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-- Every defining Koszul swap relation for an integer grading `G` is a defining Koszul swap
relation for its parity grading `G.parity`. -/
theorem signedSwapRel.parity {G : InternalGrading R V ℤ} {a b : TensorAlgebra R V}
    (h : signedSwapRel G a b) : signedSwapRel G.parity a b :=
  h.coarsen (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- Integer-graded generators also satisfy the Koszul sign rule for parity-homogeneous inputs, which
need not be homogeneous for the integer grading. -/
theorem generator_mul_generator_of_mem_parity {i j : ZMod 2} {x y : V}
    (hx : x ∈ G.parity.piece i) (hy : y ∈ G.parity.piece j) :
    generator G x * generator G y =
      ((-1 : ℤˣ) ^ (i * j)) • (generator G y * generator G x) :=
  generator_mul_generator_of_mem_coarsen G (f := Int.castRingHom (ZMod 2))
    (uzpow_intCast (-1)) hx hy

/-- **The parity-graded signed symmetric algebra `SignedSym G.parity` is canonically isomorphic to
the integer-graded `SignedSym G`.** -/
noncomputable def parityEquiv : SignedSym G ≃ₐ[R] SignedSym G.parity :=
  coarsenEquiv G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `parityEquiv` identifies the generators of `SignedSym G` and `SignedSym G.parity`. -/
@[simp]
theorem parityEquiv_generator (x : V) :
    parityEquiv G (generator G x) = generator G.parity x :=
  coarsenEquiv_generator G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) x

/-- The inverse of `parityEquiv` identifies the generators of `SignedSym G.parity` and
`SignedSym G`. -/
@[simp]
theorem parityEquiv_symm_generator (x : V) :
    (parityEquiv G).symm (generator G.parity x) = generator G x :=
  coarsenEquiv_symm_generator G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) x

/-- `parityEquiv` commutes with the canonical quotient maps from `TensorAlgebra R V`. -/
@[simp]
theorem parityEquiv_quotient (x : TensorAlgebra R V) :
    parityEquiv G (quotient G x) = quotient G.parity x :=
  coarsenEquiv_quotient G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) x

/-- The inverse of `parityEquiv` commutes with the canonical quotient maps from
`TensorAlgebra R V`. -/
@[simp]
theorem parityEquiv_symm_quotient (x : TensorAlgebra R V) :
    (parityEquiv G).symm (quotient G.parity x) = quotient G x :=
  coarsenEquiv_symm_quotient G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) x

/-- Two tensor-algebra elements have equal classes in `SignedSym G.parity` if and only if they have
equal classes in `SignedSym G`. -/
theorem quotient_parity_eq_iff {x y : TensorAlgebra R V} :
    quotient G.parity x = quotient G.parity y ↔ quotient G x = quotient G y :=
  quotient_coarsen_eq_iff G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- **The Koszul relation ideal of `G.parity` in `TensorAlgebra R V` equals that of `G`.** -/
@[simp]
theorem ker_quotient_parity : RingHom.ker (quotient G.parity) = RingHom.ker (quotient G) :=
  ker_quotient_coarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `parityEquiv` preserves the canonical augmentation. -/
@[simp]
theorem augmentation_parityEquiv (a : SignedSym G) :
    augmentation G.parity (parityEquiv G a) = augmentation G a :=
  augmentation_coarsenEquiv G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) a

/-- The inverse of `parityEquiv` preserves the canonical augmentation. -/
@[simp]
theorem augmentation_parityEquiv_symm (a : SignedSym G.parity) :
    augmentation G ((parityEquiv G).symm a) = augmentation G.parity a :=
  augmentation_coarsenEquiv_symm G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) a

/-- `parityEquiv` maps the word-length-`n` piece of `SignedSym G` onto that of
`SignedSym G.parity`. -/
theorem map_lengthPiece_parityEquiv (n : ℕ) :
    (lengthPiece G n).map (parityEquiv G).toLinearMap = lengthPiece G.parity n :=
  map_lengthPiece_coarsenEquiv G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) n

/-- `parityEquiv` preserves word length. -/
@[simp]
theorem parityEquiv_mem_lengthPiece_iff {n : ℕ} {a : SignedSym G} :
    parityEquiv G a ∈ lengthPiece G.parity n ↔ a ∈ lengthPiece G n :=
  coarsenEquiv_mem_lengthPiece_iff G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- The inverse of `parityEquiv` preserves word length. -/
@[simp]
theorem parityEquiv_symm_mem_lengthPiece_iff {n : ℕ} {a : SignedSym G.parity} :
    (parityEquiv G).symm a ∈ lengthPiece G n ↔ a ∈ lengthPiece G.parity n :=
  coarsenEquiv_symm_mem_lengthPiece_iff G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- The parity-`i` piece of `SignedSym G.parity` is the image under `parityEquiv` of the parity-`i`
piece of `SignedSym G`. -/
theorem signedSymPiece_parity_eq_map (i : ZMod 2) :
    signedSymPiece G.parity i =
      (parityGrading (signedSymPiece G) i).map (parityEquiv G).toLinearMap :=
  signedSymPiece_coarsen_eq_map G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) i

/-- `parityEquiv` identifies `parityGrading (signedSymPiece G)` with `signedSymPiece G.parity`. -/
theorem parityEquiv_mem_signedSymPiece_iff {i : ZMod 2} {a : SignedSym G} :
    parityEquiv G a ∈ signedSymPiece G.parity i ↔ a ∈ parityGrading (signedSymPiece G) i :=
  coarsenEquiv_mem_signedSymPiece_iff G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- The inverse of `parityEquiv` identifies `signedSymPiece G.parity` with
`parityGrading (signedSymPiece G)`. -/
theorem parityEquiv_symm_mem_parityGrading_iff {i : ZMod 2} {a : SignedSym G.parity} :
    (parityEquiv G).symm a ∈ parityGrading (signedSymPiece G) i ↔
      a ∈ signedSymPiece G.parity i :=
  coarsenEquiv_symm_mem_coarsenGrading_iff G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- An element of `SignedSym G` of integer degree `p` maps under `parityEquiv` into parity
`p mod 2` in `SignedSym G.parity`. -/
theorem parityEquiv_mem_of_mem {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) :
    parityEquiv G a ∈ signedSymPiece G.parity p :=
  coarsenEquiv_mem_of_mem G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) ha

/-- `parityEquiv` as a `ZMod 2`-graded algebra homomorphism from `parityGrading (signedSymPiece G)`
to `signedSymPiece G.parity`. -/
noncomputable def toParity :
    parityGrading (signedSymPiece G) →ₐᵍ[R] signedSymPiece G.parity :=
  toCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- The inverse of `parityEquiv` as a `ZMod 2`-graded algebra homomorphism from
`signedSymPiece G.parity` to `parityGrading (signedSymPiece G)`. -/
noncomputable def ofParity :
    signedSymPiece G.parity →ₐᵍ[R] parityGrading (signedSymPiece G) :=
  ofCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- The underlying algebra homomorphism of `toParity` is `parityEquiv`. -/
@[simp]
theorem toParity_toAlgHom : (toParity G).toAlgHom = (parityEquiv G).toAlgHom :=
  toCoarsen_toAlgHom G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `toParity` agrees pointwise with `parityEquiv`. -/
@[simp]
theorem toParity_apply (a : SignedSym G) : toParity G a = parityEquiv G a :=
  toCoarsen_apply G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) a

/-- The underlying algebra homomorphism of `ofParity` is `(parityEquiv G).symm`. -/
@[simp]
theorem ofParity_toAlgHom : (ofParity G).toAlgHom = (parityEquiv G).symm.toAlgHom :=
  ofCoarsen_toAlgHom G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `ofParity` agrees pointwise with `(parityEquiv G).symm`. -/
@[simp]
theorem ofParity_apply (a : SignedSym G.parity) : ofParity G a = (parityEquiv G).symm a :=
  ofCoarsen_apply G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) a

/-- `ofParity` is a left inverse of `toParity` as a `ZMod 2`-graded algebra homomorphism. -/
@[simp]
theorem ofParity_comp_toParity :
    (ofParity G).comp (toParity G) = GradedAlgHom.id R (parityGrading (signedSymPiece G)) :=
  ofCoarsen_comp_toCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `toParity` is a left inverse of `ofParity` as a `ZMod 2`-graded algebra homomorphism. -/
@[simp]
theorem toParity_comp_ofParity :
    (toParity G).comp (ofParity G) = GradedAlgHom.id R (signedSymPiece G.parity) :=
  toCoarsen_comp_ofCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `parityEquiv` is natural with respect to degree-preserving linear maps. -/
theorem parityEquiv_map {W : Type w} [AddCommGroup W] [Module R W]
    (H : InternalGrading R W ℤ) (φ : V →ₗ[R] W)
    (hφ : LinearMap.IsHomogeneous φ G.piece H.piece 0) (a : SignedSym G) :
    parityEquiv H (map G H φ hφ a) =
      map G.parity H.parity φ (Int.cast_zero (R := ZMod 2) ▸ hφ.parity) (parityEquiv G a) :=
  coarsenEquiv_map G H (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) φ hφ a

/-! ### Transport of integer homogeneous maps and odd derivations to `SignedSym G.parity` -/

/-- Composing an integer degree-`q` generator map `δ : V →ₗ[R] SignedSym G` with `parityEquiv`
yields a map of parity `q mod 2` for `G.parity`. -/
theorem isHomogeneous_parityEquiv_comp {δ : V →ₗ[R] SignedSym G} {q : ℤ}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (signedSymPiece G.parity) q :=
  isHomogeneous_coarsenEquiv_comp G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hδ

/-- Composing an integer degree-`1` generator map `δ : V →ₗ[R] SignedSym G` with `parityEquiv`
yields an odd generator map for `G.parity`. -/
theorem isHomogeneous_one_parityEquiv_comp {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (signedSymPiece G.parity) 1 :=
  Int.cast_one (R := ZMod 2) ▸ isHomogeneous_parityEquiv_comp G hδ

/-- Conjugating an integer degree-`q` endomorphism of `SignedSym G` by `parityEquiv` produces an
endomorphism of parity `q mod 2` on `SignedSym G.parity`. -/
theorem isHomogeneous_conj_parityEquiv {d : SignedSym G →ₗ[R] SignedSym G} {q : ℤ}
    (hd : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearEquiv.conj d)
      (signedSymPiece G.parity) (signedSymPiece G.parity) q :=
  isHomogeneous_conj_coarsenEquiv G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hd

/-- Conjugating an integer signed Leibniz endomorphism of `SignedSym G` by `parityEquiv` produces a
parity signed Leibniz endomorphism of `SignedSym G.parity`. -/
theorem conj_parityEquiv_mul_of_leibniz {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b))
    {i : ZMod 2} {a : SignedSym G.parity} (ha : a ∈ signedSymPiece G.parity i)
    (b : SignedSym G.parity) :
    (parityEquiv G).toLinearEquiv.conj d (a * b) =
      (parityEquiv G).toLinearEquiv.conj d a * b +
        ((-1 : ℤˣ) ^ i) • (a * (parityEquiv G).toLinearEquiv.conj d b) :=
  conj_coarsenEquiv_mul_of_leibniz G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hd ha b

/-- Extending an integer degree-`1` generator assignment and conjugating by `parityEquiv` agrees
with extending the parity-reduced generator assignment directly on `SignedSym G.parity`. -/
@[simp]
theorem conj_parityEquiv_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    (parityEquiv G).toLinearEquiv.conj (liftDerivation δ hδ) =
      liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_one_parityEquiv_comp G hδ) :=
  conj_coarsenEquiv_liftDerivation G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hδ

/-- The differential of a differential graded algebra structure on `SignedSym G` transports across
`parityEquiv` to an odd endomorphism of `SignedSym G.parity`. -/
theorem isHomogeneous_conj_parityEquiv_of_isDGAlgebra {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : IsDGAlgebra (signedSymPiece G) d) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearEquiv.conj d)
      (signedSymPiece G.parity) (signedSymPiece G.parity) 1 :=
  Int.cast_one (R := ZMod 2) ▸
    isHomogeneous_conj_parityEquiv G (LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ hd.map_mem ha)

/-- The differential of a differential graded algebra structure on `SignedSym G` transports across
`parityEquiv` to a parity signed Leibniz endomorphism of `SignedSym G.parity`. -/
theorem conj_parityEquiv_mul_of_isDGAlgebra {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : IsDGAlgebra (signedSymPiece G) d)
    {i : ZMod 2} {a : SignedSym G.parity} (ha : a ∈ signedSymPiece G.parity i)
    (b : SignedSym G.parity) :
    (parityEquiv G).toLinearEquiv.conj d (a * b) =
      (parityEquiv G).toLinearEquiv.conj d a * b +
        ((-1 : ℤˣ) ^ i) • (a * (parityEquiv G).toLinearEquiv.conj d b) :=
  conj_parityEquiv_mul_of_leibniz G hd.leibniz ha b

/-- The differential of a differential graded algebra structure on `SignedSym G` transports across
`parityEquiv` to a square-zero endomorphism of `SignedSym G.parity`. -/
theorem conj_parityEquiv_comp_self_of_isDGAlgebra {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : IsDGAlgebra (signedSymPiece G) d) :
    (parityEquiv G).toLinearEquiv.conj d ∘ₗ (parityEquiv G).toLinearEquiv.conj d = 0 := by
  rw [← LinearEquiv.conj_comp, LinearEquiv.map_eq_zero_iff]
  exact LinearMap.ext hd.sq_zero

/-- A degree-`1` signed Leibniz endomorphism of `SignedSym G` defines a differential graded algebra
structure if and only if its parity transport on `SignedSym G.parity` squares to zero. -/
theorem isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero {d : SignedSym G →ₗ[R] SignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1)
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b)) :
    IsDGAlgebra (signedSymPiece G) d ↔
      (parityEquiv G).toLinearEquiv.conj d ∘ₗ (parityEquiv G).toLinearEquiv.conj d = 0 := by
  rw [← LinearEquiv.conj_comp, LinearEquiv.map_eq_zero_iff]
  exact ⟨fun h ↦ LinearMap.ext h.sq_zero, fun h ↦
    { map_mem := fun ha ↦ hdeg.map_mem ha
      sq_zero := fun a ↦ LinearMap.congr_fun h a
      leibniz := fun ha b ↦ hleibniz ha b }⟩

/-- Extending an integer degree-`1` generator assignment yields a differential graded algebra
structure on `SignedSym G` if and only if the parity-reduced odd derivation on `SignedSym G.parity`
squares to zero. -/
theorem isDGAlgebra_liftDerivation_iff_parity {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
          (isHomogeneous_one_parityEquiv_comp G hδ) ∘ₗ
        liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
          (isHomogeneous_one_parityEquiv_comp G hδ) = 0 := by
  rw [isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero G
    (isHomogeneous_liftDerivation hδ) (liftDerivation_mul hδ), conj_parityEquiv_liftDerivation]

end SignedSym

end TauCeti
