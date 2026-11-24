/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Unimodular
public import TauCeti.RepresentationTheory.Rep.OfMulAction
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# The augmented complex of unimodular frames

A unimodular `p`-frame of `Rⁿ` is an `n × p` matrix `A` with a left inverse `B * A = 1`: its
columns form a basis of a free direct summand of `Rⁿ` (van der Kallen's unimodular sequences of
length `p`). The general linear group `GL n R` acts on the `n × p` matrices by left multiplication
and preserves frames, `B * g⁻¹` being a left inverse of `g • A`; the frames form the
sub-`GL n R`-set `TauCeti.unimodularFrames R n p`. A `1`-frame is a unimodular vector in the sense
of `Module.IsUnimodular` (`TauCeti.mem_unimodularFrames_one_iff`). Deleting the `i`-th column of a
`(p + 1)`-frame gives a `p`-frame (`TauCeti.frameFace`), equivariantly, and these faces satisfy the
semi-simplicial identities (`TauCeti.frameFace_comp_frameFace`).

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

* `TauCeti.unimodularFrames R n p`: the unimodular `p`-frames of `Rⁿ`, as a sub-`GL n R`-set of
  the `n × p` matrices.
* `TauCeti.frameFace R n i`: the equivariant map deleting the `i`-th column of a frame.
* `TauCeti.frameComplex k R n`: the augmented complex of frames, a chain complex of `k`-linear
  representations of `GL n R`.
* `TauCeti.frameComplexXZeroIso`: its term in degree `0` is the trivial representation `k`.

## Main results

* `TauCeti.submatrix_one_mem_unimodularFrames`: the standard frame of an injective `f : Fin p → n`
  is a frame.
* `TauCeti.mem_unimodularFrames_one_iff`: the `1`-frames are the unimodular vectors.
* `TauCeti.frameFace_comp_frameFace`: the semi-simplicial identities between the faces.
* `TauCeti.frameComplex_d_single`: the differential on a frame.
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

/-! ## Unimodular frames and their faces -/

/-- The unimodular `p`-frames of `Rⁿ`: the `n × p` matrices `A` with a left inverse `B * A = 1`,
whose columns form a basis of a free direct summand of `Rⁿ`. They form a sub-`GL n R`-set of the
`n × p` matrices, `B * g⁻¹` being a left inverse of `g • A`. -/
def unimodularFrames (p : ℕ) : SubMulAction (GL n R) (Matrix n (Fin p) R) where
  carrier := {A | ∃ B : Matrix (Fin p) n R, B * A = 1}
  smul_mem' g A := by
    rintro ⟨B, hB⟩
    refine ⟨B * ((g⁻¹ : GL n R) : Matrix n n R), ?_⟩
    rw [GeneralLinearGroup.smul_def, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix n n R),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, hB]

variable {R n}

@[simp]
theorem mem_unimodularFrames_iff {p : ℕ} {A : Matrix n (Fin p) R} :
    A ∈ unimodularFrames R n p ↔ ∃ B : Matrix (Fin p) n R, B * A = 1 :=
  Iff.rfl

/-- The standard frame `(e_(f 0), …, e_(f (p - 1)))` of an injective `f : Fin p → n`, the
columns `f` of the identity matrix, is a unimodular frame. -/
theorem submatrix_one_mem_unimodularFrames {p : ℕ} {f : Fin p → n} (hf : Function.Injective f) :
    (1 : Matrix n n R).submatrix id f ∈ unimodularFrames R n p :=
  ⟨(1 : Matrix n n R).submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one _ hf]⟩

/-- A `1`-frame is a unimodular vector: an `n × 1` matrix has a left inverse if and only if some
linear functional on `Rⁿ` takes the value `1` at its column. -/
theorem mem_unimodularFrames_one_iff {A : Matrix n (Fin 1) R} :
    A ∈ unimodularFrames R n 1 ↔ Module.IsUnimodular R fun i ↦ A i 0 := by
  rw [Module.isUnimodular_iff]
  refine ⟨fun ⟨B, hB⟩ ↦ ⟨LinearMap.proj 0 ∘ₗ B.mulVecLin, ?_⟩, fun ⟨f, hf⟩ ↦ ?_⟩
  · simpa [mulVec, dotProduct, Matrix.mul_apply] using congrFun (congrFun hB 0) 0
  · refine ⟨Matrix.of fun _ j ↦ f (Pi.single j 1), Matrix.ext fun i j ↦ ?_⟩
    have hsingle (l : n) : (Pi.single l 1 : n → R) = fun j ↦ if l = j then 1 else 0 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, one_apply_eq, Matrix.mul_apply]
    simp_rw [Matrix.of_apply, hsingle, mul_comm _ (A _ 0), ← smul_eq_mul (A _ 0),
      ← LinearMap.pi_apply_eq_sum_univ, hf]

/-- Deleting some columns of a frame leaves a frame. -/
theorem submatrix_mem_unimodularFrames {p q : ℕ} {A : Matrix n (Fin p) R}
    (hA : A ∈ unimodularFrames R n p) {f : Fin q → Fin p} (hf : Function.Injective f) :
    A.submatrix id f ∈ unimodularFrames R n q := by
  obtain ⟨B, hB⟩ := hA
  exact ⟨B.submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hB, submatrix_one _ hf]⟩

/-- There is exactly one `0`-frame, the empty matrix. -/
instance : Unique (unimodularFrames R n 0) where
  default := ⟨0, mem_unimodularFrames_iff.2 ⟨0, Subsingleton.elim _ _⟩⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

variable (R n) in
/-- The `i`-th face of a `(p + 1)`-frame: the `p`-frame obtained by deleting its `i`-th column.
It is equivariant for `GL n R`, which acts on frames by left multiplication. -/
def frameFace {p : ℕ} (i : Fin (p + 1)) :
    unimodularFrames R n (p + 1) →[GL n R] unimodularFrames R n p where
  toFun A := ⟨(A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove,
    submatrix_mem_unimodularFrames A.property Fin.succAbove_right_injective⟩
  map_smul' g A := Subtype.ext <| by
    simp only [SubMulAction.val_smul, GeneralLinearGroup.smul_def, id_eq]
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]

@[simp]
theorem coe_frameFace_apply {p : ℕ} (i : Fin (p + 1)) (A : unimodularFrames R n (p + 1)) :
    (frameFace R n i A : Matrix n (Fin p) R) =
      (A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove :=
  (rfl)

/-- The semi-simplicial identities: for `i ≤ j`, deleting the column `j + 1` and then the
column `i` is the same as deleting the column `i` and then the column `j`. -/
theorem frameFace_comp_frameFace {p : ℕ} {i j : Fin (p + 1)} (hij : i ≤ j)
    (A : unimodularFrames R n (p + 2)) :
    frameFace R n i (frameFace R n j.succ A) = frameFace R n j (frameFace R n i.castSucc A) := by
  refine Subtype.ext <| Matrix.ext fun r c ↦ ?_
  have h := congrFun (Fin.removeNth_removeNth_eq_swap (fun c ↦ (A : Matrix _ _ R) r c) i j.succ) c
  rw [Fin.predAbove_succ_of_le _ _ hij, Fin.succAbove_succ_of_le _ _ hij] at h
  simpa [Fin.removeNth] using h

/-! ## The augmented complex of frames -/

variable (R n)

/-- The face `F_(p+1) → F_p` deleting the `i`-th column, extended linearly to a morphism of
permutation representations `k[F_(p+1)] ⟶ k[F_p]`. -/
abbrev frameFaceHom {p : ℕ} (i : Fin (p + 1)) :
    Rep.ofMulAction k (GL n R) (unimodularFrames R n (p + 1)) ⟶
      Rep.ofMulAction k (GL n R) (unimodularFrames R n p) :=
  (frameFace R n i).toRepRes (φ := MonoidHom.id _)

/-- The differential `k[F_(p+1)] ⟶ k[F_p]` of the frame complex, the alternating sum of the faces
`A ↦ ∑ᵢ (-1)ⁱ (A with column i deleted)`. -/
def frameDifferential (p : ℕ) :
    Rep.ofMulAction k (GL n R) (unimodularFrames R n (p + 1)) ⟶
      Rep.ofMulAction k (GL n R) (unimodularFrames R n p) :=
  ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • frameFaceHom k R n i

variable {k R n}

@[simp]
theorem frameFaceHom_single {p : ℕ} (i : Fin (p + 1)) (A : unimodularFrames R n (p + 1)) (r : k) :
    (frameFaceHom k R n i).hom (single A r) = single (frameFace R n i A) r :=
  MulActionHom.toRepRes_hom_single _ _ _

/-- The differential of the frame complex on a frame. -/
theorem frameDifferential_single {p : ℕ} (A : unimodularFrames R n (p + 1)) (r : k) :
    (frameDifferential k R n p).hom (single A r) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • single (frameFace R n i A) r := by
  rw [frameDifferential, Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Rep.zsmul_hom, Representation.IntertwiningMap.coe_zsmul, Pi.smul_apply, frameFaceHom_single]

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
  ChainComplex.of (fun p ↦ Rep.ofMulAction k (GL n R) (unimodularFrames R n p))
    (frameDifferential k R n) frameDifferential_comp_frameDifferential

@[simp]
theorem frameComplex_X (p : ℕ) :
    (frameComplex k R n).X p = Rep.ofMulAction k (GL n R) (unimodularFrames R n p) :=
  (rfl)

@[simp]
theorem frameComplex_d (p : ℕ) :
    (frameComplex k R n).d (p + 1) p = frameDifferential k R n p := by
  simp [frameComplex]

variable {k R n}

/-- The differential of the frame complex on a frame. -/
theorem frameComplex_d_single {p : ℕ} (A : unimodularFrames R n (p + 1)) (r : k) :
    ((frameComplex k R n).d (p + 1) p).hom (single A r) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • single (frameFace R n i A) r := by
  simp only [frameComplex_d]
  exact frameDifferential_single A r

/-- The differential out of degree `1` is the augmentation: it sends every unimodular vector to
the empty frame. -/
theorem frameComplex_d_one_zero_single (A : unimodularFrames R n 1) (r : k) :
    ((frameComplex k R n).d 1 0).hom (single A r) = single default r := by
  rw [frameComplex_d_single, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul,
    Subsingleton.elim (frameFace R n 0 A) default]

variable (k R n) in
/-- The term in degree `0` of the frame complex, the permutation representation on the single
`0`-frame, is the trivial representation `k`. -/
def frameComplexXZeroIso : (frameComplex k R n).X 0 ≅ Rep.trivial k (GL n R) k :=
  Rep.mkIso
    { toLinearEquiv := (MonoidAlgebra.coeffLinearEquiv k).trans
        (Finsupp.uniqueLinearEquiv k k (default : unimodularFrames R n 0))
      isIntertwining' g := by
        ext x
        simp [Subsingleton.elim (g • x) x] }

/-- The identification of the term in degree `0` with `k` reads off the coefficient of the empty
frame. -/
@[simp]
theorem frameComplexXZeroIso_hom_hom_single (A : unimodularFrames R n 0) (r : k) :
    (frameComplexXZeroIso k R n).hom.hom (single A r) = r := by
  rw [Subsingleton.elim A default]
  exact (Rep.mkIso_hom_hom_apply _ (single default r : k[unimodularFrames R n 0])).trans (by simp)

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
    ⟨single ⟨Matrix.of fun i _ ↦ v i, mem_unimodularFrames_one_iff.2 hv⟩ (x.coeff default), ?_⟩
  rw [frameDifferential_single, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
  refine MonoidAlgebra.ext (Finsupp.ext fun a ↦ ?_)
  rw [Subsingleton.elim a default, Subsingleton.elim (frameFace R n 0 _) default]
  simp

/-- Over a nontrivial ring of coefficients, the augmented frame complex is exact in degree `0`, its
augmentation being onto, if and only if `Rⁿ` has a unimodular vector. -/
theorem frameComplex_exactAt_zero_iff [Nontrivial k] :
    (frameComplex k R n).ExactAt 0 ↔ ∃ v : n → R, Module.IsUnimodular R v := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hv⟩ ↦ frameComplex_exactAt_zero_of_isUnimodular hv⟩
  by_contra hv
  obtain ⟨y, hy⟩ := frameComplex_exactAt_zero_iff_surjective.1 h (single default 1)
  have : IsEmpty (unimodularFrames R n 1) :=
    ⟨fun A ↦ hv ⟨_, mem_unimodularFrames_one_iff.1 A.property⟩⟩
  rw [show y = 0 from MonoidAlgebra.ext (Finsupp.ext fun a ↦ isEmptyElim a), map_zero] at hy
  simpa using congrArg (fun z : k[unimodularFrames R n 0] ↦ z.coeff default) hy

/-- If `n` is nonempty, the augmented frame complex is exact in degree `0`: the standard basis
vectors of `Rⁿ` are unimodular, so the augmentation is onto. -/
theorem frameComplex_exactAt_zero [Nonempty n] : (frameComplex k R n).ExactAt 0 :=
  frameComplex_exactAt_zero_of_isUnimodular (v := Pi.single (Classical.arbitrary n) 1)
    (Module.isUnimodular_of_apply_eq_one (f := LinearMap.proj (Classical.arbitrary n)) (by simp))

end TauCeti
