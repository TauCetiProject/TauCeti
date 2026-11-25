/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Basic
public import TauCeti.RepresentationTheory.Rep.OfMulAction
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# The augmented complex of unimodular frames

A unimodular `p`-frame of `Rⁿ` is an `n × p` matrix with a left inverse; the frames form the
sub-`GL n R`-set `TauCeti.unimodularFrames R n (Fin p)`, and deleting the `i`-th column of a
`(p + 1)`-frame is the equivariant face `TauCeti.frameFace` (see
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Basic`).

The augmented complex of frames, `TauCeti.frameComplex k R n`, is the chain complex of
`k`-linear representations of `GL n R` whose term in degree `p` is the permutation representation
`k[F_p]` on the set `F_p` of `p`-frames, with differential the alternating sum of the faces,
`A ↦ ∑ᵢ (-1)ⁱ (A with column i deleted)`. The empty matrix is the only `0`-frame, so the term in
degree `0` is the trivial representation `k` (`TauCeti.frameComplexXZeroIso`) and the differential
out of degree `1` is the augmentation, sending every unimodular vector to `1`.

Degrees are shifted by one from the usual convention for augmented complexes, which puts the
frames of length `j + 1` in degree `j` and the augmentation in degree `-1`: here the frames of
length `p` sit in degree `p`, so that the complex is indexed by `ℕ`. Exactness of this complex in
degree `p` is the vanishing of the reduced homology of the frame complex in degree `p - 1`; for
instance, over a nontrivial ring of coefficients, it is exact in degree `0` exactly when `Rⁿ` has
a unimodular vector (`TauCeti.frameComplex_exactAt_zero_iff`), as it does when `n` is nonempty.

A group acting on a highly acyclic complex of this kind relates its homology to the homology of
the stabilisers of the frames, through the spectral sequence of group hyperhomology
(`HomologicalComplex.groupHyperhomologySpectralSequence`): this is the complex on which van der
Kallen's and Suslin's proofs of homological stability for general linear groups let `GL n R` act.

## Main definitions

* `TauCeti.frameComplex k R n`: the augmented complex of frames, a chain complex of `k`-linear
  representations of `GL n R`.
* `TauCeti.frameComplexXZeroIso`: its term in degree `0` is the trivial representation `k`.

## Main results

* `TauCeti.frameDifferential_single`: the differential on a frame.
* `TauCeti.frameComplex_exactAt_zero_iff`: over a nontrivial ring of coefficients, the complex is
  exact in degree `0` if and only if `Rⁿ` has a unimodular vector; the sufficient direction is
  `TauCeti.frameComplex_exactAt_zero_of_isUnimodular`, over any ring of coefficients.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  2.4 (unimodular sequences) and 2.9 (acyclicity of augmented complexes).
* A. A. Suslin, *Homology of `GL_n`, characteristic classes and Milnor K-theory*, in Algebraic
  K-theory, number theory, geometry and analysis, Lecture Notes in Math. 1046, Springer, 1984,
  357–375.
-/

public section

noncomputable section

open CategoryTheory Matrix MonoidAlgebra

namespace TauCeti

universe u

variable (k : Type u) [Ring k] (R : Type u) [CommRing R] (n : Type u) [Fintype n] [DecidableEq n]

/-- The face `F_(p+1) → F_p` deleting the `i`-th column, extended linearly to a morphism of
permutation representations `k[F_(p+1)] ⟶ k[F_p]`. -/
abbrev frameFaceHom {p : ℕ} (i : Fin (p + 1)) :
    Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin (p + 1))) ⟶
      Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin p)) :=
  (frameFace R n i).toRepRes (φ := MonoidHom.id _)

/-- The differential `k[F_(p+1)] ⟶ k[F_p]` of the frame complex, the alternating sum of the faces
`A ↦ ∑ᵢ (-1)ⁱ (A with column i deleted)`. -/
def frameDifferential (p : ℕ) :
    Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin (p + 1))) ⟶
      Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin p)) :=
  ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • frameFaceHom k R n i

variable {k R n}

@[simp]
theorem frameFaceHom_single {p : ℕ} (i : Fin (p + 1)) (A : unimodularFrames R n (Fin (p + 1)))
    (r : k) :
    (frameFaceHom k R n i).hom (single A r) = single (frameFace R n i A) r :=
  MulActionHom.toRepRes_hom_single _ _ _

/-- The differential of the frame complex on a frame. -/
@[simp]
theorem frameDifferential_single {p : ℕ} (A : unimodularFrames R n (Fin (p + 1))) (r : k) :
    (frameDifferential k R n p).hom (single A r) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • single (frameFace R n i A) r := by
  simp only [frameDifferential, Rep.sum_hom, Rep.zsmul_hom, Pi.smul_apply,
    Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.coe_zsmul]
  -- `simp` does not use `frameFaceHom_single` inside these sums, so close them termwise
  exact Finset.sum_congr rfl fun i _ ↦ congrArg _ (frameFaceHom_single i A r)

/-- The differential out of degree `1` sends every unimodular vector to the empty frame. -/
theorem frameDifferential_zero_single (A : unimodularFrames R n (Fin 1)) (r : k) :
    (frameDifferential k R n 0).hom (single A r) = single default r := by
  rw [frameDifferential_single, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul,
    Subsingleton.elim (frameFace R n 0 A) default]

/-- The alternating sums of faces compose to zero, by the semi-simplicial identities. -/
theorem frameDifferential_comp_frameDifferential (p : ℕ) :
    frameDifferential k R n (p + 1) ≫ frameDifferential k R n p = 0 := by
  refine Rep.ofMulAction_hom_ext fun A ↦ ?_
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, frameDifferential_single, map_sum,
    Rep.zero_hom, Representation.IntertwiningMap.coe_zero, Pi.zero_apply]
  refine (Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, frameDifferential_single]).trans ?_
  exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ single (frameFace R n j (frameFace R n i A)) (1 : k)) fun i j hij ↦ by
      rw [frameFace_comp_frameFace hij]

variable (k R n)

/-- The augmented complex of unimodular frames of `Rⁿ`, a chain complex of `k`-linear
representations of `GL n R`: its term in degree `p` is the permutation representation on the
`p`-frames, and its differential is the alternating sum of the faces. The term in degree `0` is
the trivial representation `k`, spanned by the empty frame (`TauCeti.frameComplexXZeroIso`), and
the differential out of degree `1` is the augmentation. -/
@[expose] def frameComplex : ChainComplex (Rep k (GL n R)) ℕ :=
  ChainComplex.of (fun p ↦ Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin p)))
    (frameDifferential k R n) frameDifferential_comp_frameDifferential

@[simp]
theorem frameComplex_X (p : ℕ) :
    (frameComplex k R n).X p = Rep.ofMulAction k (GL n R) (unimodularFrames R n (Fin p)) :=
  (rfl)

@[simp]
theorem frameComplex_d (p : ℕ) :
    (frameComplex k R n).d (p + 1) p = frameDifferential k R n p := by
  simp [frameComplex]

variable {k R n}

/-- The differential out of degree `1` is the augmentation: it sends every unimodular vector to
the empty frame. -/
theorem frameComplex_d_one_zero_single (A : unimodularFrames R n (Fin 1)) (r : k) :
    ((frameComplex k R n).d 1 0).hom (single A r) = single default r := by
  simp only [frameComplex_d]
  exact frameDifferential_zero_single A r

variable (k R n) in
/-- The term in degree `0` of the frame complex, the permutation representation on the single
`0`-frame, is the trivial representation `k`. -/
def frameComplexXZeroIso : (frameComplex k R n).X 0 ≅ Rep.trivial k (GL n R) k :=
  -- Mathlib's isomorphism asks for a monoid structure on the one-point `GL n R`-set, which only
  -- serves to name its point; the unique `0`-frame borrows the one of `PUnit`
  letI := (Equiv.ofUnique (unimodularFrames R n (Fin 0)) PUnit.{u + 1}).mulOneClass
  Rep.ofMulActionSubsingletonIsoTrivial k (GL n R) (unimodularFrames R n (Fin 0))

/-- The inverse identification of `k` with the term in degree `0` sends a scalar to that multiple
of the empty frame. -/
@[simp]
theorem frameComplexXZeroIso_inv_hom_apply (r : k) :
    (frameComplexXZeroIso k R n).inv.hom r = single default r :=
  -- Mathlib's isomorphism sends `r` to `r` times the point `1` of the monoid structure borrowed
  -- from `PUnit`, which is the unique `0`-frame
  congrArg (single · r) (Subsingleton.elim _ _)

/-- The identification of the term in degree `0` with `k` reads off the coefficient of the empty
frame. -/
@[simp]
theorem frameComplexXZeroIso_hom_hom_single (A : unimodularFrames R n (Fin 0)) (r : k) :
    (frameComplexXZeroIso k R n).hom.hom (single A r) = r := by
  rw [Subsingleton.elim A default, ← frameComplexXZeroIso_inv_hom_apply, Rep.hom_inv_apply]

/-- Exactness in degree `0` is the surjectivity of the augmentation `k[F_1] ⟶ k`. -/
private theorem frameComplex_exactAt_zero_iff_surjective :
    (frameComplex k R n).ExactAt 0 ↔ Function.Surjective (frameDifferential k R n 0).hom := by
  have hd : Epi ((frameComplex k R n).d 1 0) ↔ Epi (frameDifferential k R n 0) := by
    rw [frameComplex_d]
    -- after the rewrite the two sides differ only in how the source and target of the morphism
    -- are written, `(frameComplex k R n).X p` against its value `Rep.ofMulAction k _ _`
    exact Iff.rfl
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.exact_iff_epi _ (by simp), HomologicalComplex.shortComplexFunctor'_obj_f, hd,
    Rep.epi_iff_surjective]

/-- If `Rⁿ` has a unimodular vector, the augmented frame complex is exact in degree `0`: the
augmentation is onto. -/
theorem frameComplex_exactAt_zero_of_isUnimodular {v : n → R} (hv : Module.IsUnimodular R v) :
    (frameComplex k R n).ExactAt 0 := by
  refine frameComplex_exactAt_zero_iff_surjective.2 fun x ↦
    ⟨single ⟨Matrix.of fun i _ ↦ v i, mem_unimodularFrames_iff_isUnimodular (k := Fin 1) |>.2 hv⟩
      (x.coeff default), ?_⟩
  rw [frameDifferential_zero_single]
  refine MonoidAlgebra.ext (Finsupp.ext fun a ↦ ?_)
  rw [Subsingleton.elim a default]
  simp

/-- Over a nontrivial ring of coefficients, the augmented frame complex is exact in degree `0`, its
augmentation being onto, if and only if `Rⁿ` has a unimodular vector. -/
theorem frameComplex_exactAt_zero_iff [Nontrivial k] :
    (frameComplex k R n).ExactAt 0 ↔ ∃ v : n → R, Module.IsUnimodular R v := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hv⟩ ↦ frameComplex_exactAt_zero_of_isUnimodular hv⟩
  by_contra hv
  obtain ⟨y, hy⟩ := frameComplex_exactAt_zero_iff_surjective.1 h (single default 1)
  have : IsEmpty (unimodularFrames R n (Fin 1)) :=
    ⟨fun A ↦ hv ⟨_, mem_unimodularFrames_iff_isUnimodular.1 A.property⟩⟩
  -- With no `1`-frames, the free module `k[unimodularFrames R n (Fin 1)]` is zero, so the
  -- preimage `y` of `single default 1` is `0`, and so is its image.
  have hy0 : y = 0 := MonoidAlgebra.ext (Finsupp.ext fun a ↦ isEmptyElim a)
  rw [hy0, map_zero] at hy
  simpa using congrArg (fun z : k[unimodularFrames R n (Fin 0)] ↦ z.coeff default) hy

/-- If `n` is nonempty, the augmented frame complex is exact in degree `0`: the standard basis
vectors of `Rⁿ` are unimodular, so the augmentation is onto. -/
theorem frameComplex_exactAt_zero [Nonempty n] : (frameComplex k R n).ExactAt 0 :=
  frameComplex_exactAt_zero_of_isUnimodular (v := Pi.single (Classical.arbitrary n) 1)
    (IsUnit.isUnimodular_pi (i := Classical.arbitrary n) (by simp))

end TauCeti
