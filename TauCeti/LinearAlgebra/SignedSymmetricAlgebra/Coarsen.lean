/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Parity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.RingTheory.GradedAlgebra.Coarsen

/-!
# Coarsening and parity reduction of the signed symmetric algebra

If `G` is an internal grading of an `R`-module `V` over a Koszul-signed degree semiring `ι` and
`f : ι →+* κ` is a ring homomorphism that preserves the sign character `p ↦ (-1 : ℤˣ) ^ p`, then
the Koszul swap relations of `G` generate the same two-sided ideal in `TensorAlgebra R V` as those
of the coarsened grading `G.coarsen f`: every homogeneous swap for `G` is already a homogeneous swap
for `G.coarsen f`, and conversely elements of coarsened pieces supercommute in `SignedSym G` because
each coarsened piece is the sum of the original pieces in its fibre.

Consequently `SignedSym G` is canonically isomorphic as an `R`-algebra to `SignedSym (G.coarsen f)`
(`TauCeti.SignedSym.coarsenEquiv`), compatibly with generators, the tensor-algebra quotient map,
augmentation, word length, functorial maps, the coarsened input-degree grading, and odd derivations.

Specializing to `f = Int.castRingHom (ZMod 2)` identifies the integer-graded orbit algebra
`SignedSym G` with the parity-graded orbit algebra `SignedSym G.parity` built directly from parities
(`TauCeti.SignedSym.parityEquiv`). Under this equivalence:
* the Koszul relation ideal of `G.parity` in `TensorAlgebra R V` equals that of `G`
  (`TauCeti.SignedSym.ker_quotient_parity`);
* `signedSymPiece G.parity` corresponds to `parityGrading (signedSymPiece G)`, giving mutually
  inverse `ZMod 2`-graded algebra maps `toParity` and `ofParity`; in particular an element of
  integer degree `p` maps into parity `p mod 2` (`TauCeti.SignedSym.parityEquiv_mem_of_mem`);
* conjugating a degree-one signed derivation of `SignedSym G` across `parityEquiv` yields an odd
  signed derivation of `SignedSym G.parity`, and extending a degree-one generator assignment before
  or after parity reduction produces the same odd derivation
  (`TauCeti.SignedSym.conj_parityEquiv_liftDerivation`).

## Main definitions

* `TauCeti.SignedSym.coarsenEquiv` and `TauCeti.SignedSym.parityEquiv`: the canonical `R`-algebra
  equivalences `SignedSym G ≃ₐ[R] SignedSym (G.coarsen f)` and
  `SignedSym G ≃ₐ[R] SignedSym G.parity`.
* `TauCeti.SignedSym.toCoarsen`, `TauCeti.SignedSym.ofCoarsen`, `TauCeti.SignedSym.toParity`, and
  `TauCeti.SignedSym.ofParity`: the mutually inverse graded algebra homomorphisms identifying the
  coarsened (in particular, parity) grading of `SignedSym G` with `signedSymPiece` of the coarsened
  grading.

## Main results

* `TauCeti.signedSwapRel.coarsen` and `TauCeti.signedSwapRel.parity`: every homogeneous Koszul swap
  for `G` is a homogeneous Koszul swap for `G.coarsen f` and `G.parity`.
* `TauCeti.SignedSym.ker_quotient_coarsen` and `TauCeti.SignedSym.ker_quotient_parity`: the Koszul
  relation ideal in `TensorAlgebra R V` is unchanged under sign-preserving coarsening and parity
  reduction.
* `TauCeti.SignedSym.coarsenEquiv_mem_signedSymPiece_iff` and
  `TauCeti.SignedSym.parityEquiv_mem_signedSymPiece_iff`: homogeneous pieces of `SignedSym` on the
  coarsened grading match the coarsened homogeneous pieces of `SignedSym G`.
* `TauCeti.SignedSym.isHomogeneous_conj_parityEquiv`,
  `TauCeti.SignedSym.conj_parityEquiv_mul_of_leibniz`, and
  `TauCeti.SignedSym.conj_parityEquiv_liftDerivation`: transport of odd derivations and
  compatibility with `liftDerivation`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48,
  for the parity-graded orbit algebra and its comparison with an integer Conley–Zehnder lift.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-! ### Coarsening along a sign-preserving ring homomorphism -/

section Coarsen

variable {ι : Type*} {κ : Type*} [DecidableEq ι] [DecidableEq κ]
  [CommSemiring ι] [Module ι (Additive ℤˣ)] [CommSemiring κ] [Module κ (Additive ℤˣ)]

/-- Every defining Koszul swap relation for `G` is already a defining Koszul swap relation for
`G.coarsen f` when `f : ι →+* κ` preserves `(-1 : ℤˣ) ^ ·`. -/
theorem signedSwapRel.coarsen {G : InternalGrading R V ι} {f : ι →+* κ}
    (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) {a b : TensorAlgebra R V}
    (h : signedSwapRel G a b) : signedSwapRel (G.coarsen f) a b := by
  cases h with
  | swap p q x y hx hy =>
    have hpq : (-1 : ℤˣ) ^ (f p * f q) = (-1 : ℤˣ) ^ (p * q) := by rw [← map_mul, hf]
    rw [← hpq]
    exact .swap (f p) (f q) x y (mem_coarsenGrading_of_mem f hx)
      (mem_coarsenGrading_of_mem f hy)

namespace SignedSym

variable (G : InternalGrading R V ι) {f : ι →+* κ}

private noncomputable def toCoarsenAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    SignedSym G →ₐ[R] SignedSym (G.coarsen f) :=
  lift G (generator (G.coarsen f)) fun p q x y hx hy ↦ by
    have hpq : (-1 : ℤˣ) ^ (f p * f q) = (-1 : ℤˣ) ^ (p * q) := by rw [← map_mul, hf]
    rw [← hpq]
    exact generator_mul_generator (G.coarsen f) (mem_coarsenGrading_of_mem f hx)
      (mem_coarsenGrading_of_mem f hy)

omit [Module κ (Additive ℤˣ)] in
private theorem generator_mem_coarsenGrading {k : κ} {x : V} (hx : x ∈ (G.coarsen f).piece k) :
    generator G x ∈ coarsenGrading (signedSymPiece G) f k :=
  coarsenGrading_induction (motive := fun y ↦ generator G y ∈ coarsenGrading (signedSymPiece G) f k)
    hx (fun p hp y hy ↦ by
      rw [← hp]
      exact mem_coarsenGrading_of_mem f (generator_mem_signedSymPiece G hy))
    (by simp) fun y z hy hz ↦ by rw [map_add]; exact add_mem hy hz

private noncomputable def ofCoarsenAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    SignedSym (G.coarsen f) →ₐ[R] SignedSym G :=
  lift (G.coarsen f) (generator G) fun _ _ _ _ hx hy ↦
    mul_eq_uzpow_smul_mul_of_mem_coarsenGrading hf (mul_eq_uzpow_smul_mul G)
      (generator_mem_coarsenGrading G hx) (generator_mem_coarsenGrading G hy)

/-- **Coarsening the grading of `V` along a sign-preserving ring homomorphism leaves the signed
symmetric algebra unchanged.** -/
noncomputable def coarsenEquiv (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    SignedSym G ≃ₐ[R] SignedSym (G.coarsen f) :=
  AlgEquiv.ofAlgHom (toCoarsenAlgHom G hf) (ofCoarsenAlgHom G hf)
    (hom_ext (G.coarsen f) fun x ↦ by simp [toCoarsenAlgHom, ofCoarsenAlgHom])
    (hom_ext G fun x ↦ by simp [toCoarsenAlgHom, ofCoarsenAlgHom])

/-- `coarsenEquiv` identifies the generators of `SignedSym G` and `SignedSym (G.coarsen f)`. -/
@[simp]
theorem coarsenEquiv_generator (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) (x : V) :
    coarsenEquiv G hf (generator G x) = generator (G.coarsen f) x :=
  lift_generator G (generator (G.coarsen f)) _ x

/-- The inverse of `coarsenEquiv` identifies the generators of `SignedSym (G.coarsen f)` and
`SignedSym G`. -/
@[simp]
theorem coarsenEquiv_symm_generator (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) (x : V) :
    (coarsenEquiv G hf).symm (generator (G.coarsen f) x) = generator G x :=
  lift_generator (G.coarsen f) (generator G) _ x

/-- `coarsenEquiv` commutes with the canonical quotient maps from `TensorAlgebra R V`. -/
@[simp]
theorem coarsenEquiv_quotient (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (x : TensorAlgebra R V) :
    coarsenEquiv G hf (quotient G x) = quotient (G.coarsen f) x := by
  have h : (coarsenEquiv G hf).toAlgHom.comp (quotient G) = quotient (G.coarsen f) :=
    TensorAlgebra.hom_ext <| LinearMap.ext fun v ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse of `coarsenEquiv` commutes with the canonical quotient maps from
`TensorAlgebra R V`. -/
@[simp]
theorem coarsenEquiv_symm_quotient (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (x : TensorAlgebra R V) :
    (coarsenEquiv G hf).symm (quotient (G.coarsen f) x) = quotient G x := by
  rw [AlgEquiv.symm_apply_eq, coarsenEquiv_quotient]

/-- Two tensor-algebra elements have equal classes in `SignedSym (G.coarsen f)` if and only if they
have equal classes in `SignedSym G`. -/
theorem quotient_coarsen_eq_iff (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {x y : TensorAlgebra R V} :
    quotient (G.coarsen f) x = quotient (G.coarsen f) y ↔ quotient G x = quotient G y := by
  rw [← coarsenEquiv_quotient G hf, ← coarsenEquiv_quotient G hf,
    (coarsenEquiv G hf).injective.eq_iff]

/-- **The Koszul relation ideal in `TensorAlgebra R V` is invariant under sign-preserving
coarsening.** -/
theorem ker_quotient_coarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    RingHom.ker (quotient (G.coarsen f)) = RingHom.ker (quotient G) := by
  ext x
  simp only [RingHom.mem_ker, ← coarsenEquiv_quotient G hf,
    map_eq_zero_iff _ (coarsenEquiv G hf).injective]

/-- `coarsenEquiv` preserves the canonical augmentation. -/
@[simp]
theorem augmentation_coarsenEquiv (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (a : SignedSym G) :
    augmentation (G.coarsen f) (coarsenEquiv G hf a) = augmentation G a := by
  have h : (augmentation (G.coarsen f)).comp (coarsenEquiv G hf).toAlgHom = augmentation G :=
    hom_ext G fun x ↦ by simp
  exact AlgHom.congr_fun h a

/-- The inverse of `coarsenEquiv` preserves the canonical augmentation. -/
@[simp]
theorem augmentation_coarsenEquiv_symm (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (a : SignedSym (G.coarsen f)) :
    augmentation G ((coarsenEquiv G hf).symm a) = augmentation (G.coarsen f) a := by
  simpa using (augmentation_coarsenEquiv G hf ((coarsenEquiv G hf).symm a)).symm

/-- `coarsenEquiv` maps the word-length-`n` piece of `SignedSym G` onto that of
`SignedSym (G.coarsen f)`. -/
theorem map_lengthPiece_coarsenEquiv (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) (n : ℕ) :
    (lengthPiece G n).map (coarsenEquiv G hf).toLinearMap = lengthPiece (G.coarsen f) n := by
  rw [lengthPiece_eq_map, lengthPiece_eq_map, ← Submodule.map_comp]
  congr 1
  ext x
  simp

/-- `coarsenEquiv` preserves word length. -/
@[simp]
theorem coarsenEquiv_mem_lengthPiece_iff (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {n : ℕ} {a : SignedSym G} :
    coarsenEquiv G hf a ∈ lengthPiece (G.coarsen f) n ↔ a ∈ lengthPiece G n := by
  simp [← map_lengthPiece_coarsenEquiv G hf]

/-- The degree-`k` piece of `SignedSym (G.coarsen f)` is the image under `coarsenEquiv` of the
coarsened degree-`k` piece of `SignedSym G`. -/
theorem signedSymPiece_coarsen_eq_map (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) (k : κ) :
    signedSymPiece (G.coarsen f) k =
      (coarsenGrading (signedSymPiece G) f k).map (coarsenEquiv G hf).toLinearMap := by
  rw [signedSymPiece_def, ← coarsenGrading_tensorAlgebraPiece G f,
    coarsenGrading_apply, coarsenGrading_apply, Submodule.map_iSup]
  simp_rw [Submodule.map_iSup, signedSymPiece_def, ← Submodule.map_comp]
  congr! 3
  ext x
  simp

/-- `coarsenEquiv` identifies the coarsened grading of `SignedSym G` with the input-degree grading
of `SignedSym (G.coarsen f)`. -/
theorem coarsenEquiv_mem_signedSymPiece_iff (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {k : κ} {a : SignedSym G} :
    coarsenEquiv G hf a ∈ signedSymPiece (G.coarsen f) k ↔
      a ∈ coarsenGrading (signedSymPiece G) f k := by
  simp [signedSymPiece_coarsen_eq_map G hf]

/-- An element of `SignedSym G` of degree `p` maps under `coarsenEquiv` into degree `f p`. -/
theorem coarsenEquiv_mem_of_mem (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) :
    coarsenEquiv G hf a ∈ signedSymPiece (G.coarsen f) (f p) :=
  (coarsenEquiv_mem_signedSymPiece_iff G hf).2 (mem_coarsenGrading_of_mem f ha)

/-- `coarsenEquiv` as a graded algebra homomorphism from the coarsened grading of `SignedSym G` to
`signedSymPiece (G.coarsen f)`. -/
noncomputable def toCoarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    coarsenGrading (signedSymPiece G) f →ₐᵍ[R] signedSymPiece (G.coarsen f) :=
  { (coarsenEquiv G hf).toAlgHom with
    map_mem := fun ha ↦ (coarsenEquiv_mem_signedSymPiece_iff G hf).2 ha }

/-- The inverse of `coarsenEquiv` as a graded algebra homomorphism from
`signedSymPiece (G.coarsen f)` to the coarsened grading of `SignedSym G`. -/
noncomputable def ofCoarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    signedSymPiece (G.coarsen f) →ₐᵍ[R] coarsenGrading (signedSymPiece G) f :=
  { (coarsenEquiv G hf).symm.toAlgHom with
    map_mem := fun ha ↦ (coarsenEquiv_mem_signedSymPiece_iff G hf).1 (by simpa using ha) }

/-- The underlying algebra homomorphism of `toCoarsen` is `coarsenEquiv`. -/
@[simp]
theorem toCoarsen_toAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    (toCoarsen G hf).toAlgHom = (coarsenEquiv G hf).toAlgHom := (rfl)

/-- `toCoarsen` agrees pointwise with `coarsenEquiv`. -/
@[simp]
theorem toCoarsen_apply (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) (a : SignedSym G) :
    toCoarsen G hf a = coarsenEquiv G hf a := (rfl)

/-- The underlying algebra homomorphism of `ofCoarsen` is `(coarsenEquiv G hf).symm`. -/
@[simp]
theorem ofCoarsen_toAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    (ofCoarsen G hf).toAlgHom = (coarsenEquiv G hf).symm.toAlgHom := (rfl)

/-- `ofCoarsen` agrees pointwise with `(coarsenEquiv G hf).symm`. -/
@[simp]
theorem ofCoarsen_apply (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (a : SignedSym (G.coarsen f)) :
    ofCoarsen G hf a = (coarsenEquiv G hf).symm a := (rfl)

/-- `ofCoarsen` is a left inverse of `toCoarsen` as a graded algebra homomorphism. -/
theorem ofCoarsen_comp_toCoarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    (ofCoarsen G hf).comp (toCoarsen G hf) =
      GradedAlgHom.id R (coarsenGrading (signedSymPiece G) f) := by
  ext a
  simp

/-- `toCoarsen` is a left inverse of `ofCoarsen` as a graded algebra homomorphism. -/
theorem toCoarsen_comp_ofCoarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    (toCoarsen G hf).comp (ofCoarsen G hf) =
      GradedAlgHom.id R (signedSymPiece (G.coarsen f)) := by
  ext a
  simp

/-- `coarsenEquiv` is natural with respect to degree-preserving linear maps. -/
theorem coarsenEquiv_map {W : Type w} [AddCommGroup W] [Module R W]
    (H : InternalGrading R W ι) (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    (φ : V →ₗ[R] W) (hφ : LinearMap.IsHomogeneous φ G.piece H.piece 0) (a : SignedSym G) :
    coarsenEquiv H hf (map G H φ hφ a) =
      map (G.coarsen f) (H.coarsen f) φ (map_zero f ▸ hφ.coarsenGrading f)
        (coarsenEquiv G hf a) := by
  have h : (coarsenEquiv H hf).toAlgHom.comp (map G H φ hφ) =
      (map (G.coarsen f) (H.coarsen f) φ
        (map_zero f ▸ hφ.coarsenGrading f)).comp (coarsenEquiv G hf).toAlgHom :=
    hom_ext G fun x ↦ by simp
  exact AlgHom.congr_fun h a

/-! ### Transport of homogeneous maps and odd derivations across `coarsenEquiv` -/

/-- Composing a degree-`q` generator map `δ : V →ₗ[R] SignedSym G` with `coarsenEquiv` yields a
degree-`f q` map for `G.coarsen f`. -/
theorem isHomogeneous_coarsenEquiv_comp (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {δ : V →ₗ[R] SignedSym G} {q : ι}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((coarsenEquiv G hf).toLinearMap ∘ₗ δ)
      (G.coarsen f).piece (signedSymPiece (G.coarsen f)) (f q) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    (coarsenEquiv_mem_signedSymPiece_iff G hf).2 ((hδ.coarsenGrading f).map_mem hx)

/-- Conjugating a degree-`q` endomorphism of `SignedSym G` by `coarsenEquiv` produces a
degree-`f q` endomorphism of `SignedSym (G.coarsen f)`. -/
theorem isHomogeneous_conj_coarsenEquiv (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {d : SignedSym G →ₗ[R] SignedSym G} {q : ι}
    (hd : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((coarsenEquiv G hf).toLinearEquiv.conj d)
      (signedSymPiece (G.coarsen f)) (signedSymPiece (G.coarsen f)) (f q) :=
  LinearMap.isHomogeneous_def.2 fun _ a ha ↦ by
    have ha' : (coarsenEquiv G hf).symm a ∈ coarsenGrading (signedSymPiece G) f _ :=
      (coarsenEquiv_mem_signedSymPiece_iff G hf).1 (by simpa using ha)
    simpa using (coarsenEquiv_mem_signedSymPiece_iff G hf).2 ((hd.coarsenGrading f).map_mem ha')

/-- Conjugating a signed Leibniz endomorphism of `SignedSym G` by `coarsenEquiv` produces a signed
Leibniz endomorphism of `SignedSym (G.coarsen f)`. -/
theorem conj_coarsenEquiv_mul_of_leibniz (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : ∀ {p : ι} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + ((-1 : ℤˣ) ^ p) • (a * d b))
    {k : κ} {a : SignedSym (G.coarsen f)} (ha : a ∈ signedSymPiece (G.coarsen f) k)
    (b : SignedSym (G.coarsen f)) :
    (coarsenEquiv G hf).toLinearEquiv.conj d (a * b) =
      (coarsenEquiv G hf).toLinearEquiv.conj d a * b +
        ((-1 : ℤˣ) ^ k) • (a * (coarsenEquiv G hf).toLinearEquiv.conj d b) := by
  have ha' : (coarsenEquiv G hf).symm a ∈ coarsenGrading (signedSymPiece G) f k :=
    (coarsenEquiv_mem_signedSymPiece_iff G hf).1 (by simpa using ha)
  have hleib := leibniz_coarsenGrading_of_leibniz hf hd ha' ((coarsenEquiv G hf).symm b)
  simpa [LinearEquiv.conj_apply, map_add, map_mul, map_zsmul_unit] using
    congrArg (coarsenEquiv G hf) hleib

/-- Extending a degree-`1` generator assignment and conjugating by `coarsenEquiv` agrees with
extending the coarsened generator assignment directly on `SignedSym (G.coarsen f)`. -/
@[simp]
theorem conj_coarsenEquiv_liftDerivation (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {δ : V →ₗ[R] SignedSym G} (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    (coarsenEquiv G hf).toLinearEquiv.conj (liftDerivation δ hδ) =
      liftDerivation ((coarsenEquiv G hf).toLinearMap ∘ₗ δ)
        (map_one f ▸ isHomogeneous_coarsenEquiv_comp G hf hδ) := by
  refine eq_liftDerivation _
    (fun ha b ↦ conj_coarsenEquiv_mul_of_leibniz G hf (liftDerivation_mul hδ) ha b)
    fun x ↦ ?_
  simp

end SignedSym

end Coarsen

/-! ### Parity reduction of an integer-graded signed symmetric algebra -/

section Parity

/-- Every defining Koszul swap relation for an integer grading `G` is a defining Koszul swap
relation for its parity grading `G.parity`. -/
theorem signedSwapRel.parity {G : InternalGrading R V ℤ} {a b : TensorAlgebra R V}
    (h : signedSwapRel G a b) : signedSwapRel G.parity a b :=
  h.coarsen (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

namespace SignedSym

variable (G : InternalGrading R V ℤ)

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
theorem toParity_toAlgHom : (toParity G).toAlgHom = (parityEquiv G).toAlgHom := (rfl)

/-- `toParity` agrees pointwise with `parityEquiv`. -/
@[simp]
theorem toParity_apply (a : SignedSym G) : toParity G a = parityEquiv G a := (rfl)

/-- The underlying algebra homomorphism of `ofParity` is `(parityEquiv G).symm`. -/
@[simp]
theorem ofParity_toAlgHom : (ofParity G).toAlgHom = (parityEquiv G).symm.toAlgHom := (rfl)

/-- `ofParity` agrees pointwise with `(parityEquiv G).symm`. -/
@[simp]
theorem ofParity_apply (a : SignedSym G.parity) : ofParity G a = (parityEquiv G).symm a := (rfl)

/-- `ofParity` is a left inverse of `toParity` as a `ZMod 2`-graded algebra homomorphism. -/
theorem ofParity_comp_toParity :
    (ofParity G).comp (toParity G) = GradedAlgHom.id R (parityGrading (signedSymPiece G)) :=
  ofCoarsen_comp_toCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `toParity` is a left inverse of `ofParity` as a `ZMod 2`-graded algebra homomorphism. -/
theorem toParity_comp_ofParity :
    (toParity G).comp (ofParity G) = GradedAlgHom.id R (signedSymPiece G.parity) :=
  toCoarsen_comp_ofCoarsen G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1))

/-- `parityEquiv` is natural with respect to degree-preserving linear maps. -/
theorem parityEquiv_map {W : Type w} [AddCommGroup W] [Module R W]
    (H : InternalGrading R W ℤ) (φ : V →ₗ[R] W)
    (hφ : LinearMap.IsHomogeneous φ G.piece H.piece 0) (a : SignedSym G) :
    parityEquiv H (map G H φ hφ a) =
      map G.parity H.parity φ
        (map_zero (Int.castRingHom (ZMod 2)) ▸ hφ.coarsenGrading (Int.castRingHom (ZMod 2)))
        (parityEquiv G a) :=
  coarsenEquiv_map G H (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) φ hφ a

/-! ### Transport of integer odd derivations to `SignedSym G.parity` -/

/-- Composing an integer degree-`q` generator map `δ : V →ₗ[R] SignedSym G` with `parityEquiv`
yields a map of parity `q mod 2` for `G.parity`. -/
theorem isHomogeneous_parityEquiv_comp {δ : V →ₗ[R] SignedSym G} {q : ℤ}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (signedSymPiece G.parity) q :=
  isHomogeneous_coarsenEquiv_comp G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hδ

/-- Conjugating an integer degree-`1` endomorphism of `SignedSym G` by `parityEquiv` produces an
odd endomorphism of `SignedSym G.parity`. -/
theorem isHomogeneous_conj_parityEquiv {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearEquiv.conj d)
      (signedSymPiece G.parity) (signedSymPiece G.parity) 1 :=
  map_one (Int.castRingHom (ZMod 2)) ▸
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
        (Int.cast_one (R := ZMod 2) ▸ isHomogeneous_parityEquiv_comp G hδ) :=
  conj_coarsenEquiv_liftDerivation G (f := Int.castRingHom (ZMod 2)) (uzpow_intCast (-1)) hδ

/-- The differential of a differential graded algebra structure on `SignedSym G` transports across
`parityEquiv` to an odd endomorphism of `SignedSym G.parity`. -/
theorem isHomogeneous_conj_parityEquiv_of_isDGAlgebra {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : IsDGAlgebra (signedSymPiece G) d) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearEquiv.conj d)
      (signedSymPiece G.parity) (signedSymPiece G.parity) 1 :=
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
  ext a
  simp [LinearEquiv.conj_apply, hd.sq_zero]

end SignedSym

end Parity

end TauCeti
