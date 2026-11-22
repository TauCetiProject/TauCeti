/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Algebra.BigOperators.AlternatingSum
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.RepresentationTheory.Rep.TensorShortExact
public import TauCeti.RingTheory.StableRange

/-!
# The complexes of unimodular frames

A unimodular `p`-frame of `Rᵐ` is an `m × p` matrix with a left inverse: its columns form a basis
of a free direct summand of the module `Rᵐ` of columns. Deleting a column of a frame leaves a
frame, so a family of frames closed under deleting columns is a semi-simplicial set, whose
`(p - 1)`-simplices are its frames with `p` columns and whose `i`-th face deletes column `i`. Its
augmented chain complex is the free module on the frames, with the alternating sum of the faces as
differential. When a group acts on the family through `GL m R`, this is a complex of permutation
representations. These complexes are those through which van der Kallen proves homology stability
for the general linear groups: the group acts on a highly acyclic complex of frames, and the
spectral sequence of the action is built from the homology of the stabilisers of frames.

This file works with a `TauCeti.ColumnSystem φ`: a family of `m × p` matrices, one set for each
`p`, closed under deleting a column and under left multiplication by the image of
`φ : G →* GL m R`. Its augmented chain complex `TauCeti.ColumnSystem.chainComplex` is a complex of
representations of `G`, the free module on the members with `p` columns in degree `p`. The
complex is indexed by the number of columns: its degree `p` is the degree `p - 1` of the usual
augmented complex of the semi-simplicial set, and the chains on the single `m × 0` matrix, in
degree `0`, are the augmentation term. Thus exactness in degree `p` here is the vanishing of the
reduced homology of the frame complex in degree `p - 1`; exactness in degree `0` says that the
complex is nonempty, and exactness in degree `1` that it is connected.

The two families of frames are those of van der Kallen's complexes `F_n^0` and `F_n^1`:

* `TauCeti.frameSystem R m`: all unimodular frames of `Rᵐ`, with `GL m R` acting by left
  multiplication;
* `TauCeti.affineFrameSystem R m`: the unimodular frames of `Rᵐ ⊕ R` whose vectors lie in the
  affine hyperplane `Rᵐ + e_*`, their last coordinate being `1`, with `g : GL m R` acting through
  `diag(g, 1)`.

The low-degree exactness of these complexes is proved here: both are nonempty, the affine one is
connected once `m` has two elements, and the linear one is connected under Bass's stable range
condition `HasStableRangeLE R s` once `s + 1 ≤ card m`, which is van der Kallen's bound
`n ≥ sdim + 2` for `SR_(sdim+2)`. The connectivity proofs join every vertex to a standard one by
explicit paths of two or three edges, the linear case after shortening the vector by the stable
range condition.

## Main definitions

* `TauCeti.ColumnSystem`: a family of `m × p` matrices closed under deleting columns and under the
  action of `G` through `φ : G →* GL m R`.
* `TauCeti.ColumnSystem.face`: the `i`-th face, deleting column `i`.
* `TauCeti.ColumnSystem.d`: the alternating sum of the faces, a morphism of permutation
  representations.
* `TauCeti.ColumnSystem.chainComplex`: the augmented chain complex, in `Rep k G`.
* `TauCeti.ColumnSystem.Adjacent`: two members with one column are the faces of a member with two.
* `TauCeti.unimodularFrames`: the unimodular `p`-frames of `Rᵐ`.
* `TauCeti.frameSystem`, `TauCeti.affineFrameSystem`: the complexes `F_n^0` and `F_n^1`.

## Main results

* `TauCeti.ColumnSystem.face_face`: the semi-simplicial identities, and
  `TauCeti.ColumnSystem.d_comp_d`: `d ∘ d = 0`.
* `TauCeti.ColumnSystem.chainComplex_exactAt_zero`: exactness in degree `0` when some member has one
  column.
* `TauCeti.ColumnSystem.chainComplex_exactAt_one`: exactness in degree `1` when adjacency
  connects all members with one column.
* `TauCeti.frameSystem_chainComplex_exactAt_one`: the frames of `Rᵐ` form a connected complex under
  `HasStableRangeLE R s` and `s + 1 ≤ card m`.
* `TauCeti.affineFrameSystem_chainComplex_exactAt_one`: the frames in `Rᵐ + e_*` form a connected
  complex once `1 < card m`.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  §2 (unimodular sequences, the complexes `O(X)`, Convention 2.2 and Theorem 2.6) and the proof of
  Proposition 3.7 (the augmented chain complexes of frames).
-/

public section

noncomputable section

open CategoryTheory Matrix

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] {m : Type u} [Fintype m] [DecidableEq m] {G : Type v} [Monoid G]

/-- A family of matrices with rows indexed by `m`, one set of `m × p` matrices for each number `p`
of columns, closed under deleting a column and under left multiplication by the image of
`φ : G →* GL m R`. Its members with `p` columns are the `(p - 1)`-simplices of a semi-simplicial
`G`-set, the faces deleting one column. -/
@[ext]
structure ColumnSystem (φ : G →* GL m R) where
  /-- The members with `p` columns. -/
  carrier (p : ℕ) : Set (Matrix m (Fin p) R)
  /-- Deleting a column of a member gives a member. -/
  submatrix_succAbove_mem {p : ℕ} {A : Matrix m (Fin (p + 1)) R} (i : Fin (p + 1)) :
    A ∈ carrier (p + 1) → A.submatrix id i.succAbove ∈ carrier p
  /-- Members are stable under left multiplication by the image of `φ`. -/
  mul_mem {p : ℕ} (g : G) {A : Matrix m (Fin p) R} :
    A ∈ carrier p → (φ g : Matrix m m R) * A ∈ carrier p

namespace ColumnSystem

variable {φ : G →* GL m R} (F : ColumnSystem φ)

/-- `G` acts on the members with `p` columns by left multiplication through `φ`. -/
instance (p : ℕ) : MulAction G (F.carrier p) where
  smul g A := ⟨(φ g : Matrix m m R) * (A : Matrix m (Fin p) R), F.mul_mem g A.property⟩
  -- the action is being defined here, so the goals are stated through its formula
  one_smul A := Subtype.ext <| by
    change (φ 1 : Matrix m m R) * (A : Matrix m (Fin p) R) = A
    simp
  mul_smul g h A := Subtype.ext <| by
    change (φ (g * h) : Matrix m m R) * (A : Matrix m (Fin p) R) =
      (φ g : Matrix m m R) * ((φ h : Matrix m m R) * (A : Matrix m (Fin p) R))
    simp [Matrix.mul_assoc]

@[simp]
theorem coe_smul {p : ℕ} (g : G) (A : F.carrier p) :
    ((g • A : F.carrier p) : Matrix m (Fin p) R) =
      (φ g : Matrix m m R) * (A : Matrix m (Fin p) R) :=
  (rfl)

/-- The `i`-th face of a member with `p + 1` columns: delete its column `i`. -/
def face {p : ℕ} (i : Fin (p + 1)) (A : F.carrier (p + 1)) : F.carrier p :=
  ⟨(A : Matrix m (Fin (p + 1)) R).submatrix id i.succAbove,
    F.submatrix_succAbove_mem i A.property⟩

@[simp]
theorem coe_face {p : ℕ} (i : Fin (p + 1)) (A : F.carrier (p + 1)) :
    (F.face i A : Matrix m (Fin p) R) = (A : Matrix m (Fin (p + 1)) R).submatrix id i.succAbove :=
  (rfl)

/-- The faces are equivariant. -/
theorem face_smul {p : ℕ} (i : Fin (p + 1)) (g : G) (A : F.carrier (p + 1)) :
    F.face i (g • A) = g • F.face i A := by
  ext a b
  simp [Matrix.mul_apply]

/-- The semi-simplicial identity `dᵢ ∘ dⱼ₊₁ = dⱼ ∘ dᵢ` for `i ≤ j`. -/
theorem face_face {p : ℕ} {i j : Fin (p + 1)} (hij : i ≤ j) (A : F.carrier (p + 2)) :
    F.face i (F.face j.succ A) = F.face j (F.face i.castSucc A) := by
  have hlt : i.castSucc < j.succ := Fin.castSucc_lt_succ_iff.mpr hij
  ext a b
  simp only [coe_face, submatrix_apply, id]
  have h := Fin.succAbove_succAbove_succAbove_predAbove j.succ i b
  rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.predAbove_of_castSucc_lt _ _ hlt,
    Fin.pred_succ] at h
  exact congrArg ((A : Matrix m (Fin (p + 2)) R) a) h.symm

variable (k : Type w) [Ring k]

/-- The `i`-th face as a morphism of permutation representations. -/
def faceHom {p : ℕ} (i : Fin (p + 1)) :
    Rep.ofMulAction k G (F.carrier (p + 1)) ⟶ Rep.ofMulAction k G (F.carrier p) :=
  Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k (F.face i)
      isIntertwining' g := by
        refine MonoidAlgebra.lhom_ext' fun A => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single, F.face_smul] }

@[simp]
theorem faceHom_hom_single {p : ℕ} (i : Fin (p + 1)) (A : F.carrier (p + 1)) (r : k) :
    (dsimp% only ((F.faceHom k i).hom (MonoidAlgebra.single A r))) =
      MonoidAlgebra.single (F.face i A) r := by
  simp [faceHom]

/-- The semi-simplicial identities for the face morphisms. -/
theorem faceHom_comp_faceHom {p : ℕ} {i j : Fin (p + 1)} (hij : i ≤ j) :
    F.faceHom k j.succ ≫ F.faceHom k i = F.faceHom k i.castSucc ≫ F.faceHom k j := by
  ext A
  simp [F.face_face hij]

/-- The differential, the alternating sum `∑ᵢ (-1)ⁱ dᵢ` of the faces. -/
def d (p : ℕ) : Rep.ofMulAction k G (F.carrier (p + 1)) ⟶ Rep.ofMulAction k G (F.carrier p) :=
  ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • F.faceHom k i

/-- The alternating sum of the faces squares to zero. -/
theorem d_comp_d (p : ℕ) : F.d k (p + 1) ≫ F.d k p = 0 := by
  rw [d, d, Preadditive.sum_comp]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans
    (sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero (fun i j => F.faceHom k i ≫ F.faceHom k j)
      fun i j hij => F.faceHom_comp_faceHom k hij)
  rw [Preadditive.zsmul_comp, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul]

/-- The differential of a member is the alternating sum of its faces. -/
@[simp]
theorem d_hom_single {p : ℕ} (A : F.carrier (p + 1)) (r : k) :
    (dsimp% only ((F.d k p).hom (MonoidAlgebra.single A r))) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • MonoidAlgebra.single (F.face i A) r := by
  simp [d, Rep.sum_hom, Rep.zsmul_hom, Representation.IntertwiningMap.sum_apply]

/-- The augmented chain complex of a column system: the permutation representation on the
members with `p` columns in degree `p`, with the alternating sum of the faces as differential. Its
degree `0` holds the chains on the empty `m × 0` matrix, when it is a member, and the differential
out of degree `1` is the augmentation. -/
-- The body is exposed so that the objects of the complex are the permutation representations
-- `Rep.ofMulAction k G (F.carrier p)` by definition.
@[expose]
def chainComplex : ChainComplex (Rep.{max w u} k G) ℕ :=
  ChainComplex.of (fun p => Rep.ofMulAction k G (F.carrier p)) (F.d k) (F.d_comp_d k)

theorem chainComplex_X (p : ℕ) :
    (F.chainComplex k).X p = Rep.ofMulAction k G (F.carrier p) :=
  (rfl)

@[simp]
theorem chainComplex_d (p : ℕ) : (F.chainComplex k).d (p + 1) p = F.d k p :=
  ChainComplex.of_d (fun p => Rep.ofMulAction k G (F.carrier p)) (F.d k) p

/-- Two members with one column are **adjacent** when they are the two faces of a member with two
columns: the second and the first column of it. -/
def Adjacent (x y : F.carrier 1) : Prop :=
  ∃ e : F.carrier 2, F.face 1 e = x ∧ F.face 0 e = y

/-- There is at most one member without columns, the empty `m × 0` matrix. -/
instance : Subsingleton (F.carrier 0) :=
  ⟨fun _ _ => Subtype.ext <| Matrix.ext fun _ j => j.elim0⟩

/-- The augmented chain complex is exact in degree `0`, its augmentation onto the chains on the
empty member is onto, as soon as some member has one column. -/
theorem chainComplex_exactAt_zero (h : (F.carrier 1).Nonempty) :
    (F.chainComplex k).ExactAt 0 := by
  obtain ⟨A, hA⟩ := h
  have hsurj : Function.Surjective (F.d k 0).hom := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | single B r =>
      refine ⟨MonoidAlgebra.single ⟨A, hA⟩ r, ?_⟩
      simp [d_hom_single, Subsingleton.elim (F.face 0 ⟨A, hA⟩) B]
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp), Rep.exact_iff_function_exact]
  have hg : (F.chainComplex k).d 0 0 = 0 := (F.chainComplex k).shape _ _ (by simp)
  intro x
  simp only [HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_obj_f, hg, chainComplex_d]
  exact ⟨fun _ => hsurj x, fun _ => rfl⟩

/-- A boundary is a cycle. -/
@[simp]
theorem d_hom_d_hom_apply {p : ℕ} (y : Rep.ofMulAction k G (F.carrier (p + 2))) :
    (F.d k p).hom ((F.d k (p + 1)).hom y) = 0 := by
  have h := congrArg (fun f => f.hom y) (F.d_comp_d k p)
  simpa [Representation.IntertwiningMap.comp_apply] using h

/-- The `1`-cycles are the `1`-boundaries when the `1`-skeleton is connected: every member with
one column is related to a fixed one `x₀` by the equivalence relation generated by adjacency. -/
private theorem exact_d_one_d_zero (x₀ : F.carrier 1) (h : ∀ x, Relation.EqvGen F.Adjacent x₀ x) :
    Function.Exact (F.d k 1).hom (F.d k 0).hom := by
  set S := LinearMap.range (F.d k 1).hom.toLinearMap
  -- differences of basis vectors along the equivalence relation generated by adjacency are
  -- boundaries
  have hrel : ∀ x y, Relation.EqvGen F.Adjacent x y →
      MonoidAlgebra.single y (1 : k) - MonoidAlgebra.single x 1 ∈ S := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
      obtain ⟨e, rfl, rfl⟩ := hxy
      refine ⟨MonoidAlgebra.single e 1, ?_⟩
      simp [d_hom_single, Fin.sum_univ_two, sub_eq_add_neg]
    | refl x => simp
    | symm x y _ ih => simpa using S.neg_mem ih
    | trans x y z _ _ ihxy ihyz => simpa using S.add_mem ihyz ihxy
  -- every chain differs from a multiple of the basis vector at `x₀` by a boundary
  have key : ∀ z,
      z - ((F.d k 0).hom z).coeff (F.face 0 x₀) • MonoidAlgebra.single x₀ (1 : k) ∈ S := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simpa [map_add, add_smul, sub_add_sub_comm] using S.add_mem hx hy
    | single x r =>
      simpa [d_hom_single, Subsingleton.elim (F.face 0 x) (F.face 0 x₀), smul_sub] using
        S.smul_mem r (hrel _ _ (h x))
  intro z
  constructor
  · intro hz
    have hz' := key z
    rw [hz] at hz'
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (by simpa using hz')
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact F.d_hom_d_hom_apply k y

/-- The augmented chain complex is exact in degree `1` when its `1`-skeleton is connected: every
member with one column is related to a fixed one `x₀` by the equivalence relation generated by
adjacency. -/
theorem chainComplex_exactAt_one (x₀ : F.carrier 1)
    (h : ∀ x, Relation.EqvGen F.Adjacent x₀ x) : (F.chainComplex k).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp), Rep.exact_iff_function_exact]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_obj_f, chainComplex_d]
  exact F.exact_d_one_d_zero k x₀ h

end ColumnSystem

/-! ### Unimodular frames -/

section Frames

variable (R m) in
/-- The **unimodular `p`-frames** of `Rᵐ`: the `m × p` matrices with a left inverse. Their columns
form a basis of a free direct summand of the module `Rᵐ` of columns. -/
def unimodularFrames (p : ℕ) : Set (Matrix m (Fin p) R) :=
  {A | ∃ B : Matrix (Fin p) m R, B * A = 1}

omit [DecidableEq m] in
theorem mem_unimodularFrames_iff {p : ℕ} {A : Matrix m (Fin p) R} :
    A ∈ unimodularFrames R m p ↔ ∃ B : Matrix (Fin p) m R, B * A = 1 :=
  Iff.rfl

omit [DecidableEq m] in
/-- Subsequences of frames are frames. -/
theorem submatrix_mem_unimodularFrames {p q : ℕ} {A : Matrix m (Fin p) R}
    (hA : A ∈ unimodularFrames R m p) {f : Fin q → Fin p} (hf : Function.Injective f) :
    A.submatrix id f ∈ unimodularFrames R m q := by
  obtain ⟨B, hB⟩ := hA
  refine ⟨B.submatrix f id, ?_⟩
  rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hB, submatrix_one _ hf]

/-- Frames are stable under the general linear group. -/
theorem mul_mem_unimodularFrames {p : ℕ} (g : GL m R) {A : Matrix m (Fin p) R}
    (hA : A ∈ unimodularFrames R m p) : (g : Matrix m m R) * A ∈ unimodularFrames R m p := by
  obtain ⟨B, hB⟩ := hA
  exact ⟨B * ((g⁻¹ : GL m R) : Matrix m m R), by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix m m R), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, hB]⟩

/-- The standard frame `(e_(f 0), …, e_(f (p - 1)))` of an injective `f`. -/
theorem one_submatrix_mem_unimodularFrames {p : ℕ} {f : Fin p → m} (hf : Function.Injective f) :
    (1 : Matrix m m R).submatrix id f ∈ unimodularFrames R m p :=
  ⟨(1 : Matrix m m R).submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one _ hf]⟩

variable (R m) in
/-- The unimodular frames of `Rᵐ`, with `GL m R` acting by left multiplication. -/
def frameSystem : ColumnSystem (MonoidHom.id (GL m R)) where
  carrier := unimodularFrames R m
  submatrix_succAbove_mem _ hA := submatrix_mem_unimodularFrames hA Fin.succAbove_right_injective
  mul_mem g _ hA := mul_mem_unimodularFrames g hA

@[simp]
theorem frameSystem_carrier : (frameSystem R m).carrier = unimodularFrames R m :=
  (rfl)

variable (R m) in
/-- The unimodular frames of `Rᵐ ⊕ R` whose vectors lie in the affine hyperplane `Rᵐ + e_*`, the
last coordinate of each being `1`, with `g : GL m R` acting through `diag(g, 1)`. -/
def affineFrameSystem : ColumnSystem (fromBlocksGL.comp (MonoidHom.inl (GL m R) (GL Unit R))) where
  carrier p := {A | A ∈ unimodularFrames R (m ⊕ Unit) p ∧ ∀ j, A (.inr ()) j = 1}
  submatrix_succAbove_mem _ hA :=
    ⟨submatrix_mem_unimodularFrames hA.1 Fin.succAbove_right_injective, fun _ => hA.2 _⟩
  mul_mem g A hA := ⟨mul_mem_unimodularFrames _ hA.1, fun j => by
    simpa [Matrix.mul_apply, Fintype.sum_sum_type] using hA.2 j⟩

theorem mem_affineFrameSystem_carrier_iff {p : ℕ} {A : Matrix (m ⊕ Unit) (Fin p) R} :
    A ∈ (affineFrameSystem R m).carrier p ↔
      A ∈ unimodularFrames R (m ⊕ Unit) p ∧ ∀ j, A (.inr ()) j = 1 :=
  Iff.rfl

/-! ### Exactness in low degrees -/

omit [DecidableEq m] in
private theorem transpose_of_cons_mem_unimodularFrames {v : m → R} (b : m → R)
    (hb : b ⬝ᵥ v = 1) : (of ![v])ᵀ ∈ unimodularFrames R m 1 :=
  ⟨of ![b], by ext i j; fin_cases i; fin_cases j; simp [vecMul, Function.swap, hb]⟩

omit [DecidableEq m] in
private theorem transpose_of_cons_cons_mem_unimodularFrames {v w : m → R} (r₁ r₂ : m → R)
    (h₁₁ : r₁ ⬝ᵥ v = 1) (h₁₂ : r₁ ⬝ᵥ w = 0) (h₂₁ : r₂ ⬝ᵥ v = 0) (h₂₂ : r₂ ⬝ᵥ w = 1) :
    (of ![v, w])ᵀ ∈ unimodularFrames R m 2 :=
  ⟨of ![r₁, r₂], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMul, Function.swap, *]⟩

/-- Two columns `v` and `w` are adjacent in a column system containing the matrix with columns
`v, w`. -/
private theorem ColumnSystem.adjacent_of_mem {φ : G →* GL m R} (F : ColumnSystem φ)
    {v w : m → R} (hv : (of ![v])ᵀ ∈ F.carrier 1) (hw : (of ![w])ᵀ ∈ F.carrier 1)
    (h : (of ![v, w])ᵀ ∈ F.carrier 2) : F.Adjacent ⟨_, hv⟩ ⟨_, hw⟩ :=
  ⟨⟨_, h⟩, Subtype.ext <| by ext r c; fin_cases c; simp,
    Subtype.ext <| by ext r c; fin_cases c; simp⟩

variable (k : Type w) [Ring k]

/-- The complex of unimodular frames of `Rᵐ` is exact in degree `0`, the frame complex being
nonempty, as soon as `m` is nonempty. -/
theorem frameSystem_chainComplex_exactAt_zero [Nonempty m] :
    ((frameSystem R m).chainComplex k).ExactAt 0 :=
  (frameSystem R m).chainComplex_exactAt_zero k
    ⟨_, one_submatrix_mem_unimodularFrames (f := fun _ : Fin 1 => Classical.arbitrary m)
      (Function.injective_of_subsingleton _)⟩

/-- The complex of unimodular frames in the affine hyperplane `Rᵐ + e_*` is exact in degree `0`:
`e_*` is such a frame. -/
theorem affineFrameSystem_chainComplex_exactAt_zero :
    ((affineFrameSystem R m).chainComplex k).ExactAt 0 :=
  (affineFrameSystem R m).chainComplex_exactAt_zero k
    ⟨_, one_submatrix_mem_unimodularFrames (f := fun _ : Fin 1 => (.inr () : m ⊕ Unit))
      (Function.injective_of_subsingleton _), fun _ => by rw [submatrix_apply, id, one_apply_eq]⟩

/-- The complex of unimodular frames in the affine hyperplane `Rᵐ + e_*` is exact in degree `1`,
its `1`-skeleton being connected, as soon as `m` has at least two elements. No stable range
condition is needed. -/
theorem affineFrameSystem_chainComplex_exactAt_one (hm : 1 < Fintype.card m) :
    ((affineFrameSystem R m).chainComplex k).ExactAt 1 := by
  obtain ⟨i₀, i₁, hi⟩ := Fintype.exists_pair_of_one_lt_card hm
  let F := affineFrameSystem R m
  -- the vectors `(u, 1)` with `u ∈ Rᵐ` are the vertices
  have hvert : ∀ u : m → R, (of ![Sum.elim u 1])ᵀ ∈ F.carrier 1 := fun u =>
    ⟨transpose_of_cons_mem_unimodularFrames (Pi.single (.inr ()) 1) (by simp),
      fun j => by fin_cases j; simp⟩
  have hedge : ∀ u u' : m → R, (of ![Sum.elim u 1, Sum.elim u' 1])ᵀ ∈ unimodularFrames R _ 2 →
      F.Adjacent ⟨_, hvert u⟩ ⟨_, hvert u'⟩ := fun u u' h =>
    F.adjacent_of_mem _ _ ⟨h, fun j => by fin_cases j <;> simp⟩
  refine F.chainComplex_exactAt_one k ⟨_, hvert 0⟩ fun ⟨A, hA⟩ => ?_
  set u : m → R := fun r => A (.inl r) 0
  have hA' : A = (of ![Sum.elim u 1])ᵀ := by
    ext (r | r) c <;> fin_cases c
    · rfl
    · simpa using hA.2 0
  rw [show (⟨A, hA⟩ : F.carrier 1) = ⟨_, hvert u⟩ from Subtype.ext hA']
  -- the intermediate vertex `(a, 1)`, with `a i₀ = 1` and `a i₁ = u i₁ - 1`
  set a : m → R := u + Pi.single i₀ (1 - u i₀) - Pi.single i₁ 1
  have ha₀ : a i₀ = 1 := by simp [a, hi]
  have ha₁ : a i₁ = u i₁ - 1 := by simp [a, Ne.symm hi]
  refine .trans _ ⟨_, hvert a⟩ _ (.rel _ _ (hedge 0 a ?_)) (.rel _ _ (hedge a u ?_))
  · exact transpose_of_cons_cons_mem_unimodularFrames
      (Pi.single (.inr ()) 1 - Pi.single (.inl i₀) 1) (Pi.single (.inl i₀) 1)
      (by simp) (by simp [ha₀]) (by simp) (by simp [ha₀])
  · exact transpose_of_cons_cons_mem_unimodularFrames
      (u i₁ • Pi.single (.inr ()) 1 - Pi.single (.inl i₁) 1)
      (Pi.single (.inl i₁) 1 - (u i₁ - 1) • Pi.single (.inr ()) 1)
      (by simp [ha₁]) (by simp) (by simp [ha₁]) (by simp)

/-- Under Bass's stable range condition `HasStableRangeLE R s` (van der Kallen's `SR_(s+1)`), the
complex of unimodular frames of `Rᵐ` is exact in degree `1`, its `1`-skeleton being connected, as
soon as `s + 1 ≤ card m`. -/
theorem frameSystem_chainComplex_exactAt_one {R : Type u} [CommRing R] {s : ℕ}
    (hR : HasStableRangeLE R s) (hm : s + 1 ≤ Fintype.card m) :
    ((frameSystem R m).chainComplex k).ExactAt 1 := by
  obtain ⟨i₀⟩ : Nonempty m := Fintype.card_pos_iff.mp (by omega)
  let F := frameSystem R m
  have hvert : ∀ (v b : m → R), b ⬝ᵥ v = 1 → (of ![v])ᵀ ∈ F.carrier 1 :=
    fun _ b hb => transpose_of_cons_mem_unimodularFrames b hb
  refine F.chainComplex_exactAt_one k ⟨_, hvert (Pi.single i₀ 1) (Pi.single i₀ 1) (by simp)⟩
    fun ⟨A, hA⟩ => ?_
  set v : m → R := fun r => A r 0
  have hA' : A = (of ![v])ᵀ := by ext r c; fin_cases c; rfl
  obtain ⟨B, hB⟩ := id hA
  have hb : (fun r => B 0 r) ⬝ᵥ v = 1 := by
    have h := congrFun (congrFun hB 0) 0
    rw [Matrix.mul_apply, one_apply_eq] at h
    simpa only [dotProduct, v] using h
  rw [show (⟨A, hA⟩ : F.carrier 1) = ⟨_, hvert _ _ hb⟩ from Subtype.ext hA']
  by_cases hj : ∃ j, j ≠ i₀
  · obtain ⟨j, hj⟩ := hj
    obtain ⟨b, c, hb₀, hc₀, hbc⟩ := hR.exists_add_smul_dotProduct_eq_one hm
      (Module.isUnimodular_pi_iff.mpr ⟨_, by rwa [← dotProduct, dotProduct_comm]⟩) i₀
    rw [dotProduct_comm] at hbc
    -- the path `e_i₀ — e_j — e_i₀ - c — v`
    set y : m → R := Pi.single i₀ 1 - c
    set β : m → R := b + (b ⬝ᵥ c) • Pi.single i₀ 1
    have hβv : β ⬝ᵥ v = 1 := by
      rw [← hbc]
      simp [β, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, mul_comm]
    have hβy : β ⬝ᵥ y = 0 := by
      simp [β, y, add_dotProduct, dotProduct_sub, hb₀, hc₀]
    refine .trans _ ⟨_, hvert (Pi.single j 1) (Pi.single j 1) (by simp)⟩ _
      (.rel _ _ (F.adjacent_of_mem _ _ (transpose_of_cons_cons_mem_unimodularFrames
        (Pi.single i₀ 1) (Pi.single j 1) (by simp) (by simp [hj]) (by simp [Ne.symm hj])
        (by simp)))) ?_
    refine .trans _ ⟨_, hvert y (Pi.single i₀ 1) (by simp [y, hc₀])⟩ _
      (.rel _ _ (F.adjacent_of_mem _ _ (transpose_of_cons_cons_mem_unimodularFrames
        (Pi.single j 1 + c j • Pi.single i₀ 1) (Pi.single i₀ 1) (by simp [hj])
        (by simp [y, Ne.symm hj, hc₀]) (by simp [hj]) (by simp [y, hc₀])))) ?_
    exact .rel _ _ (F.adjacent_of_mem _ _ (transpose_of_cons_cons_mem_unimodularFrames
      (Pi.single i₀ 1 - v i₀ • β) β (by rw [sub_dotProduct, smul_dotProduct, hβy]; simp [y, hc₀])
      (by simp [hβv, sub_dotProduct, smul_dotProduct, v]) hβy hβv))
  · -- with a single coordinate, the bound forces `s = 0`, so that `R` is the zero ring
    push Not at hj
    have hcard : Fintype.card m ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [hj a, hj b]
    have : Subsingleton R := hasStableRangeLE_zero_iff.mp (by simpa [show s = 0 by omega] using hR)
    rw [show (⟨_, hvert _ _ hb⟩ : F.carrier 1) =
      ⟨_, hvert (Pi.single i₀ 1) (Pi.single i₀ 1) (by simp)⟩ from
        Subtype.ext (Matrix.ext fun _ _ => Subsingleton.elim _ _)]
    exact .refl _

end Frames

end TauCeti
