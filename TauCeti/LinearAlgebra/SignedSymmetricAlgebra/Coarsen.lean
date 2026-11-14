/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.WordLength
public import TauCeti.RingTheory.GradedAlgebra.Coarsen

/-!
# Coarsening the grading of the signed symmetric algebra

If `G` is an internal grading of an `R`-module `V` over a Koszul-signed degree semiring `ι` and
`f` is a ring homomorphism `ι →+* κ` (or any `RingHomClass` map) that preserves the sign character
`p ↦ (-1 : ℤˣ) ^ p`, then the Koszul swap relations of `G` generate the same two-sided ideal in
`TensorAlgebra R V` as those of the coarsened grading `G.coarsen f`: every homogeneous swap for `G`
is already a homogeneous swap for `G.coarsen f`, and conversely elements of coarsened pieces
supercommute in `SignedSym G` because each coarsened piece is the sum of the original pieces in its
fibre.

Consequently `SignedSym G` is canonically isomorphic as an `R`-algebra to `SignedSym (G.coarsen f)`
(`TauCeti.SignedSym.coarsenEquiv`), compatibly with generators, the tensor-algebra quotient map,
augmentation, word length, functorial maps, the coarsened input-degree grading, and odd derivations.

See `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity` for the specialization to
`Int.castRingHom (ZMod 2) : ℤ →+* ZMod 2`, comparing an integer-graded signed symmetric algebra and
its differential graded algebra structure with its parity reduction `SignedSym G.parity`.

## Main definitions

* `TauCeti.SignedSym.coarsenEquiv`: the canonical `R`-algebra equivalence
  `SignedSym G ≃ₐ[R] SignedSym (G.coarsen f)`.
* `TauCeti.SignedSym.toCoarsen` and `TauCeti.SignedSym.ofCoarsen`: the mutually inverse graded
  algebra homomorphisms identifying `coarsenGrading (signedSymPiece G) f` with
  `signedSymPiece (G.coarsen f)`.

## Main results

* `TauCeti.signedSwapRel.coarsen`: every homogeneous Koszul swap for `G` is a homogeneous Koszul
  swap for `G.coarsen f`.
* `TauCeti.SignedSym.generator_mul_generator_of_mem_coarsen`: generators in coarsened homogeneous
  pieces supercommute in `SignedSym G` with the coarsened Koszul sign.
* `TauCeti.SignedSym.ker_quotient_coarsen`: the Koszul relation ideal in `TensorAlgebra R V` is
  unchanged under sign-preserving coarsening.
* `TauCeti.SignedSym.coarsenEquiv_mem_signedSymPiece_iff` and
  `TauCeti.SignedSym.coarsenEquiv_symm_mem_coarsenGrading_iff`: homogeneous pieces of
  `SignedSym (G.coarsen f)` match the coarsened homogeneous pieces of `SignedSym G`.
* `TauCeti.SignedSym.isHomogeneous_conj_coarsenEquiv`,
  `TauCeti.SignedSym.conj_coarsenEquiv_mul_of_leibniz`, and
  `TauCeti.SignedSym.conj_coarsenEquiv_liftDerivation`: transport of homogeneous maps and signed
  derivations across `coarsenEquiv`, and compatibility with `liftDerivation`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

section Coarsen

variable {ι : Type*} {κ : Type*} {F : Type*} [DecidableEq ι] [DecidableEq κ]
  [CommSemiring ι] [Module ι (Additive ℤˣ)] [CommSemiring κ] [Module κ (Additive ℤˣ)]
  [FunLike F ι κ] [RingHomClass F ι κ]

/-- Every defining Koszul swap relation for `G` is already a defining Koszul swap relation for
`G.coarsen f` when `f` preserves `(-1 : ℤˣ) ^ ·`. -/
theorem signedSwapRel.coarsen {G : InternalGrading R V ι} {f : F}
    (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) {a b : TensorAlgebra R V}
    (h : signedSwapRel G a b) : signedSwapRel (G.coarsen f) a b := by
  cases h with
  | swap p q x y hx hy =>
    have hpq : (-1 : ℤˣ) ^ (f p * f q) = (-1 : ℤˣ) ^ (p * q) := by rw [← map_mul, hf]
    rw [← hpq]
    exact .swap (f p) (f q) x y (G.mem_coarsen_of_mem f hx) (G.mem_coarsen_of_mem f hy)

namespace SignedSym

variable (G : InternalGrading R V ι) {f : F}

private noncomputable def toCoarsenAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    SignedSym G →ₐ[R] SignedSym (G.coarsen f) :=
  lift G (generator (G.coarsen f)) fun p q x y hx hy ↦ by
    have hpq : (-1 : ℤˣ) ^ (f p * f q) = (-1 : ℤˣ) ^ (p * q) := by rw [← map_mul, hf]
    rw [← hpq]
    exact generator_mul_generator (G.coarsen f) (G.mem_coarsen_of_mem f hx)
      (G.mem_coarsen_of_mem f hy)

omit [CommSemiring κ] [Module κ (Additive ℤˣ)] [RingHomClass F ι κ] in
private theorem generator_mem_coarsenGrading {k : κ} {x : V} (hx : x ∈ (G.coarsen f).piece k) :
    generator G x ∈ coarsenGrading (signedSymPiece G) f k := by
  rw [InternalGrading.coarsen_piece] at hx
  exact coarsenGrading_induction
    (motive := fun y ↦ generator G y ∈ coarsenGrading (signedSymPiece G) f k)
    hx (fun p hp y hy ↦ by
      rw [← hp]
      exact mem_coarsenGrading_of_mem f (generator_mem_signedSymPiece G hy))
    (by simp) fun y z hy hz ↦ by rw [map_add]; exact add_mem hy hz

/-- Generators in coarsened homogeneous pieces still supercommute in `SignedSym G` with the
coarsened Koszul sign, even when they mix several degrees of `G`. -/
theorem generator_mul_generator_of_mem_coarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {i j : κ} {x y : V} (hx : x ∈ (G.coarsen f).piece i) (hy : y ∈ (G.coarsen f).piece j) :
    generator G x * generator G y =
      ((-1 : ℤˣ) ^ (i * j)) • (generator G y * generator G x) :=
  mul_eq_uzpow_smul_mul_of_mem_coarsenGrading hf (mul_eq_uzpow_smul_mul G)
    (generator_mem_coarsenGrading G hx) (generator_mem_coarsenGrading G hy)

private noncomputable def ofCoarsenAlgHom (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    SignedSym (G.coarsen f) →ₐ[R] SignedSym G :=
  lift (G.coarsen f) (generator G) fun _ _ _ _ hx hy ↦
    generator_mul_generator_of_mem_coarsen G hf hx hy

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

/-- The inverse of `coarsenEquiv` preserves word length. -/
@[simp]
theorem coarsenEquiv_symm_mem_lengthPiece_iff (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {n : ℕ} {a : SignedSym (G.coarsen f)} :
    (coarsenEquiv G hf).symm a ∈ lengthPiece G n ↔ a ∈ lengthPiece (G.coarsen f) n := by
  rw [← coarsenEquiv_mem_lengthPiece_iff G hf, AlgEquiv.apply_symm_apply]

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

/-- The inverse of `coarsenEquiv` identifies the input-degree grading of `SignedSym (G.coarsen f)`
with the coarsened grading of `SignedSym G`. -/
theorem coarsenEquiv_symm_mem_coarsenGrading_iff (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {k : κ} {a : SignedSym (G.coarsen f)} :
    (coarsenEquiv G hf).symm a ∈ coarsenGrading (signedSymPiece G) f k ↔
      a ∈ signedSymPiece (G.coarsen f) k := by
  rw [← coarsenEquiv_mem_signedSymPiece_iff G hf, AlgEquiv.apply_symm_apply]

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
    map_mem := fun ha ↦ (coarsenEquiv_symm_mem_coarsenGrading_iff G hf).2 ha }

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
@[simp]
theorem ofCoarsen_comp_toCoarsen (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p) :
    (ofCoarsen G hf).comp (toCoarsen G hf) =
      GradedAlgHom.id R (coarsenGrading (signedSymPiece G) f) := by
  ext a
  simp

/-- `toCoarsen` is a left inverse of `ofCoarsen` as a graded algebra homomorphism. -/
@[simp]
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
      map (G.coarsen f) (H.coarsen f) φ (map_zero f ▸ hφ.coarsen f)
        (coarsenEquiv G hf a) := by
  have h : (coarsenEquiv H hf).toAlgHom.comp (map G H φ hφ) =
      (map (G.coarsen f) (H.coarsen f) φ
        (map_zero f ▸ hφ.coarsen f)).comp (coarsenEquiv G hf).toAlgHom :=
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
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    rw [InternalGrading.coarsen_piece] at hx
    exact (coarsenEquiv_mem_signedSymPiece_iff G hf).2 ((hδ.coarsenGrading f).map_mem hx)

/-- Conjugating a degree-`q` endomorphism of `SignedSym G` by `coarsenEquiv` produces a
degree-`f q` endomorphism of `SignedSym (G.coarsen f)`. -/
theorem isHomogeneous_conj_coarsenEquiv (hf : ∀ p : ι, (-1 : ℤˣ) ^ f p = (-1 : ℤˣ) ^ p)
    {d : SignedSym G →ₗ[R] SignedSym G} {q : ι}
    (hd : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) q) :
    LinearMap.IsHomogeneous ((coarsenEquiv G hf).toLinearEquiv.conj d)
      (signedSymPiece (G.coarsen f)) (signedSymPiece (G.coarsen f)) (f q) :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    simpa using (coarsenEquiv_mem_signedSymPiece_iff G hf).2
      ((hd.coarsenGrading f).map_mem ((coarsenEquiv_symm_mem_coarsenGrading_iff G hf).2 ha))

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
  have hleib := leibniz_coarsenGrading_of_leibniz hf hd
    ((coarsenEquiv_symm_mem_coarsenGrading_iff G hf).2 ha) ((coarsenEquiv G hf).symm b)
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

end TauCeti
