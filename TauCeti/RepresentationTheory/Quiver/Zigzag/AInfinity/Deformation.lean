/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basis
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.IntrinsicFormality.Criterion
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Four
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Tree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Idempotents
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Isomorphism

/-!
# Minimal `A∞` deformations and intrinsic formality of zigzag algebras

For any finite simple graph `G` and commutative ring `k`, the public componentwise zigzag algebra
`TauCeti.zigzagAlgebra k G` carries the signed path-length grading
`TauCeti.zigzagAlgebraIntegerGrade` (including the dual-number degree-two generator on
isolated-vertex components). Regarded as a differential graded algebra with zero differential, it
becomes the strict `A∞` algebra `TauCeti.zigzagAlgebraStrictAInfinityAlgebra k G`.

Following Liu and Wang (Section 4), a **minimal strictly unital `A∞` deformation** of
`zigzagAlgebra k G` (`TauCeti.IsZigzagAInfinityDeformation`) is an `A∞` algebra structure `𝒜` on the
carrier `zigzagAlgebra k G` whose internal grading is `zigzagAlgebraIntegerGrade k G`, whose unary
operation `m₁` vanishes, whose binary operation `m₂` is the associative multiplication of
`zigzagAlgebra k G`, and for which `1` is a strict unit. Strict unitality is essential already for
the one-vertex graph `A₁`: there `zigzagAlgebra k G ≅ k[ε]/(ε²)` with `|ε| = 2`, so degree counting
alone permits operations such as `m₄(ε, ε, 1, 1)` in degree `2`, whereas strict unitality forces
every operation `mₙ` (`n ≥ 3`) to vanish in every characteristic
(`TauCeti.IsZigzagAInfinityDeformation.m_eq_zero_of_subsingleton`).

The path-graded zigzag algebra is **intrinsically formal**
(`TauCeti.IsZigzagAlgebraIntrinsicallyFormal k G`) when every minimal strictly unital `A∞`
deformation on `zigzagAlgebra k G` is formal, equivalently `A∞` isomorphic to
`zigzagAlgebraStrictAInfinityAlgebra k G`. Because `zigzagAlgebraEquiv` and
`zigzagAlgebraEquivNonisolated` are graded algebra isomorphisms, minimal strictly unital
deformations and their formality pull back along graph isomorphisms (`SimpleGraph.Iso`) and, on
connected graphs with at least two vertices, correspond to minimal strictly unital deformations on
the relation quotient `nonisolatedZigzagQuotient k G`. In particular:

* When `V` is a subsingleton (the Dynkin `A₁` graph and the empty graph), `zigzagAlgebra k G` has no
  nontrivial minimal strictly unital `A∞` deformations and is intrinsically formal over every
  commutative ring (`TauCeti.isZigzagAlgebraIntrinsicallyFormal_of_subsingleton`).
* On any connected graph with at least two vertices, vanishing of the Hochschild obstruction groups
  `HH^{n, 2 - n}` (`n ≥ 3`) of `zigzagStrictAInfinityAlgebra` implies intrinsic formality over every
  commutative ring
  (`TauCeti.isZigzagAlgebraIntrinsicallyFormal_of_forall_hochschildVanishesAt_nonisolated`).
* Over a nontrivial commutative ring in which `2` is invertible, a connected graph with a vertex of
  degree at least four, two distinct vertices of degree at least three, or a copy of affine `Dₙ`
  (`n ≥ 4`) admits a non-formal quartic deformation and is not intrinsically formal.
* Over a nontrivial `ℚ`-algebra (in particular over any field of characteristic zero), every finite
  tree not isomorphic to a Dynkin diagram admits a non-formal loop deformation in arity `4`, `6`,
  `8` or `12` and is not intrinsically formal
  (`SimpleGraph.IsTree.exists_isZigzagAInfinityDeformation_not_isFormal` and
  `SimpleGraph.IsTree.not_isZigzagAlgebraIntrinsicallyFormal`).

## Main definitions

* `TauCeti.zigzagAlgebraStrictAInfinityAlgebra`: the public zigzag algebra `zigzagAlgebra k G` as a
  minimal strictly unital `A∞` algebra with `m₂` the product and all other operations zero.
* `TauCeti.IsZigzagAInfinityDeformation`: minimal strictly unital `A∞` deformations of the
  path-graded public zigzag algebra `zigzagAlgebra k G`.
* `TauCeti.zigzagAlgebraLoopAInfinityAlgebra`: loop deformations transported along
  `zigzagAlgebraEquivNonisolated` to `zigzagAlgebra k G` on connected graphs with at least two
  vertices.
* `TauCeti.zigzagAlgebraLiuWangAffineD4`: Liu--Wang's Example 4.7 transported to the public affine
  `D₄` zigzag algebra.
* `TauCeti.IsZigzagAlgebraIntrinsicallyFormal`: intrinsic formality of the path-graded public zigzag
  algebra with respect to minimal strictly unital `A∞` deformations.

## Main results

* `TauCeti.IsZigzagAInfinityDeformation.isFormal_iff_exists_isIso`: a minimal strictly unital
  deformation is formal if and only if it is `A∞` isomorphic to
  `zigzagAlgebraStrictAInfinityAlgebra k G`.
* `TauCeti.IsZigzagAInfinityDeformation.m_eq_zero_of_subsingleton` and
  `TauCeti.isZigzagAlgebraIntrinsicallyFormal_of_subsingleton`: on a graph with at most one vertex
  (`A₁` or empty), every minimal strictly unital `A∞` deformation is strict, hence formal, over any
  commutative ring.
* `TauCeti.isZigzagAlgebraIntrinsicallyFormal_of_forall_hochschildVanishesAt` and
  `TauCeti.isZigzagAlgebraIntrinsicallyFormal_of_forall_hochschildVanishesAt_nonisolated`:
  Kadeishvili's vanishing criterion for `IsZigzagAlgebraIntrinsicallyFormal`.
* `SimpleGraph.Iso.isZigzagAlgebraIntrinsicallyFormal_iff`: invariance of
  `IsZigzagAlgebraIntrinsicallyFormal` under graph isomorphism (across arbitrary vertex universes).
* `SimpleGraph.IsTree.exists_isZigzagAInfinityDeformation_not_isFormal` and
  `SimpleGraph.IsTree.not_isZigzagAlgebraIntrinsicallyFormal`: over a nontrivial `ℚ`-algebra, every
  finite non-Dynkin tree admits a non-formal `IsZigzagAInfinityDeformation` and fails
  `IsZigzagAlgebraIntrinsicallyFormal`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Section 4 and Example 4.7.
* M. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, for the
  path-length grading and the `A₁` dual-number convention.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1--3.4.
-/

public section

namespace TauCeti

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

universe u v w

/-! ### The strict `A∞` algebra of the public zigzag algebra -/

section Strict

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- **The strict `A∞` algebra of the public zigzag algebra** `zigzagAlgebra k G`: the signed
path-length graded algebra `zigzagAlgebraIntegerGrade k G` regarded as a differential graded algebra
with zero differential, so `m₂` is multiplication and `mₙ = 0` for `n ≠ 2`. -/
noncomputable def zigzagAlgebraStrictAInfinityAlgebra : AInfinityAlgebra k (zigzagAlgebra k G) :=
  (isDGAlgebra_zero (zigzagAlgebraIntegerGrade k G)).toIsNonUnitalDGAlgebra.toAInfinityAlgebra

/-- The internal grading of `zigzagAlgebraStrictAInfinityAlgebra` is
`zigzagAlgebraInternalGrading`. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_grading :
    (zigzagAlgebraStrictAInfinityAlgebra k G).grading = zigzagAlgebraInternalGrading k G := by
  ext p
  simp [zigzagAlgebraStrictAInfinityAlgebra]

/-- The graded pieces of `zigzagAlgebraStrictAInfinityAlgebra` are `zigzagAlgebraIntegerGrade`. -/
theorem zigzagAlgebraStrictAInfinityAlgebra_grading_piece :
    (zigzagAlgebraStrictAInfinityAlgebra k G).grading.piece = zigzagAlgebraIntegerGrade k G :=
  congrArg InternalGrading.piece (zigzagAlgebraStrictAInfinityAlgebra_grading k G)

/-- The unary operation of `zigzagAlgebraStrictAInfinityAlgebra` vanishes. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_m_one_apply (x : Fin 1 → zigzagAlgebra k G) :
    (zigzagAlgebraStrictAInfinityAlgebra k G).m 1 x = 0 := by
  simp [zigzagAlgebraStrictAInfinityAlgebra]

/-- The differential of `zigzagAlgebraStrictAInfinityAlgebra` vanishes. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_differential :
    (zigzagAlgebraStrictAInfinityAlgebra k G).differential = 0 := by
  simp [zigzagAlgebraStrictAInfinityAlgebra]

/-- The binary operation of `zigzagAlgebraStrictAInfinityAlgebra` is the algebra product. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_m_two_apply (x : Fin 2 → zigzagAlgebra k G) :
    (zigzagAlgebraStrictAInfinityAlgebra k G).m 2 x = x 0 * x 1 := by
  simp [zigzagAlgebraStrictAInfinityAlgebra]

/-- The bilinear multiplication of `zigzagAlgebraStrictAInfinityAlgebra` is `LinearMap.mul`. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_mul :
    (zigzagAlgebraStrictAInfinityAlgebra k G).mul = LinearMap.mul k (zigzagAlgebra k G) := by
  simp [zigzagAlgebraStrictAInfinityAlgebra]

/-- Every operation of `zigzagAlgebraStrictAInfinityAlgebra` of arity at least three vanishes. -/
theorem zigzagAlgebraStrictAInfinityAlgebra_m_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (zigzagAlgebraStrictAInfinityAlgebra k G).m n = 0 :=
  (isDGAlgebra_zero (zigzagAlgebraIntegerGrade k G)).toIsNonUnitalDGAlgebra
    |>.toAInfinityAlgebra_m_of_three_le hn

/-- Simp-normal form for vanishing of higher operations of `zigzagAlgebraStrictAInfinityAlgebra`. -/
@[simp]
theorem zigzagAlgebraStrictAInfinityAlgebra_m_add_three (n : ℕ) :
    (zigzagAlgebraStrictAInfinityAlgebra k G).m (n + 3) = 0 :=
  zigzagAlgebraStrictAInfinityAlgebra_m_of_three_le k G (by omega)

/-- Every operation of `zigzagAlgebraStrictAInfinityAlgebra` other than `m₂` vanishes. -/
theorem zigzagAlgebraStrictAInfinityAlgebra_m_eq_zero {n : ℕ} (hn : n ≠ 2) :
    (zigzagAlgebraStrictAInfinityAlgebra k G).m n = 0 := by
  rcases n with _ | _ | _ | n
  · exact (zigzagAlgebraStrictAInfinityAlgebra k G).m_zero
  · exact MultilinearMap.ext (zigzagAlgebraStrictAInfinityAlgebra_m_one_apply k G)
  · exact absurd rfl hn
  · exact zigzagAlgebraStrictAInfinityAlgebra_m_add_three k G n

/-- The strict `A∞` algebra `zigzagAlgebraStrictAInfinityAlgebra` is minimal. -/
theorem isMinimal_zigzagAlgebraStrictAInfinityAlgebra :
    (zigzagAlgebraStrictAInfinityAlgebra k G).IsMinimal :=
  (AInfinityAlgebra.isMinimal_def _).mpr (zigzagAlgebraStrictAInfinityAlgebra_differential k G)

/-- The identity `1` is a strict unit of `zigzagAlgebraStrictAInfinityAlgebra`. -/
theorem strictUnit_one_zigzagAlgebraStrictAInfinityAlgebra :
    (zigzagAlgebraStrictAInfinityAlgebra k G).StrictUnit 1 :=
  (isDGAlgebra_zero (zigzagAlgebraIntegerGrade k G)).strictUnit_one

/-- The strict `A∞` algebra `zigzagAlgebraStrictAInfinityAlgebra` is formal. -/
theorem isFormal_zigzagAlgebraStrictAInfinityAlgebra :
    (zigzagAlgebraStrictAInfinityAlgebra k G).IsFormal :=
  IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero (zigzagAlgebraIntegerGrade k G)

end Strict

/-! ### Minimal strictly unital `A∞` deformations -/

/-- A **minimal strictly unital `A∞` deformation** of the path-graded public zigzag algebra
`zigzagAlgebra k G`: an `A∞` algebra structure `𝒜` on `zigzagAlgebra k G` with the signed
path-length grading `zigzagAlgebraIntegerGrade k G`, zero unary operation (`m₁ = 0`), binary
operation `m₂` equal to the multiplication of `zigzagAlgebra k G`, and `1` as a strict unit. -/
structure IsZigzagAInfinityDeformation (k : Type w) [CommRing k] {V : Type u} [Finite V]
    (G : SimpleGraph V) (𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)) : Prop where
  /-- The internal grading is the signed path-length grading of `zigzagAlgebra k G`. -/
  grading_piece : 𝒜.grading.piece = zigzagAlgebraIntegerGrade k G
  /-- The unary operation `m₁` vanishes. -/
  isMinimal : 𝒜.IsMinimal
  /-- The binary operation `m₂` is the associative multiplication of `zigzagAlgebra k G`. -/
  m_two : ∀ x : Fin 2 → zigzagAlgebra k G, 𝒜.m 2 x = x 0 * x 1
  /-- The identity `1` of `zigzagAlgebra k G` is a strict unit for the `A∞` operations. -/
  strictUnit : 𝒜.StrictUnit 1

/-- The strict `A∞` algebra `zigzagAlgebraStrictAInfinityAlgebra` is the trivial minimal strictly
unital `A∞` deformation of `zigzagAlgebra k G`. -/
theorem isZigzagAInfinityDeformation_zigzagAlgebraStrictAInfinityAlgebra
    (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V) :
    IsZigzagAInfinityDeformation k G (zigzagAlgebraStrictAInfinityAlgebra k G) where
  grading_piece := zigzagAlgebraStrictAInfinityAlgebra_grading_piece k G
  isMinimal := isMinimal_zigzagAlgebraStrictAInfinityAlgebra k G
  m_two := zigzagAlgebraStrictAInfinityAlgebra_m_two_apply k G
  strictUnit := strictUnit_one_zigzagAlgebraStrictAInfinityAlgebra k G

namespace IsZigzagAInfinityDeformation

variable {k : Type w} [CommRing k] {V : Type u} [Finite V] {G : SimpleGraph V}
  {𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)}

/-- The bundled `InternalGrading` of a minimal strictly unital zigzag `A∞` deformation is
`zigzagAlgebraInternalGrading k G`. -/
theorem grading_eq (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.grading = zigzagAlgebraInternalGrading k G :=
  InternalGrading.ext (congrFun h.grading_piece)

/-- A minimal strictly unital zigzag `A∞` deformation has the same grading as
`zigzagAlgebraStrictAInfinityAlgebra k G`. -/
theorem grading_eq_zigzagAlgebraStrictAInfinityAlgebra (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.grading = (zigzagAlgebraStrictAInfinityAlgebra k G).grading :=
  h.grading_eq.trans (zigzagAlgebraStrictAInfinityAlgebra_grading k G).symm

/-- The unary operation of a minimal strictly unital zigzag `A∞` deformation vanishes. -/
theorem m_one_apply (h : IsZigzagAInfinityDeformation k G 𝒜) (x : Fin 1 → zigzagAlgebra k G) :
    𝒜.m 1 x = 0 :=
  h.isMinimal.m_one x

/-- The differential of a minimal strictly unital zigzag `A∞` deformation vanishes. -/
theorem differential_eq_zero (h : IsZigzagAInfinityDeformation k G 𝒜) : 𝒜.differential = 0 :=
  (AInfinityAlgebra.isMinimal_def _).mp h.isMinimal

/-- On `![x, y]`, `m₂` of a minimal strictly unital zigzag `A∞` deformation is `x * y`. -/
theorem m_two_pair (h : IsZigzagAInfinityDeformation k G 𝒜) (x y : zigzagAlgebra k G) :
    𝒜.m 2 ![x, y] = x * y :=
  h.m_two ![x, y]

/-- A minimal strictly unital zigzag `A∞` deformation has the same binary operation as
`zigzagAlgebraStrictAInfinityAlgebra k G`. -/
theorem m_two_eq_zigzagAlgebraStrictAInfinityAlgebra (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.m 2 = (zigzagAlgebraStrictAInfinityAlgebra k G).m 2 :=
  MultilinearMap.ext fun x ↦
    (h.m_two x).trans (zigzagAlgebraStrictAInfinityAlgebra_m_two_apply k G x).symm

/-- The bilinear multiplication of a minimal strictly unital zigzag `A∞` deformation is
`LinearMap.mul`. -/
theorem mul_eq (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.mul = LinearMap.mul k (zigzagAlgebra k G) :=
  LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ by
    rw [AInfinityAlgebra.mul_apply, LinearMap.mul_apply', h.m_two_pair]

/-- **Adams degree of higher operations**: for the Adams grading
`q ↦ zigzagAlgebraIntegerGrade k G (-q)` (the negative of path length, placing arrows in bidegree
`(1, -1)`), each operation `𝒜.m n` of a minimal strictly unital zigzag `A∞` deformation is
homogeneous of Adams degree `n - 2`, hence of bidegree `(2 - n, n - 2)`. -/
theorem isHomogeneous_m_adams (h : IsZigzagAInfinityDeformation k G 𝒜) (n : ℕ) :
    MultilinearMap.IsHomogeneous (𝒜.m n)
      (fun _ q ↦ zigzagAlgebraIntegerGrade k G (-q))
      (fun q ↦ zigzagAlgebraIntegerGrade k G (-q)) ((n : ℤ) - 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [𝒜.m_zero]
    exact MultilinearMap.isHomogeneous_zero _ _ _
  · rw [MultilinearMap.isHomogeneous_def]
    intro e x hx
    have hmem : ∀ i, x i ∈ 𝒜.grading.piece (-e i) := fun i ↦ by
      rw [h.grading_piece]
      exact hx i
    have hout := (𝒜.m_degree n hn).map_mem (fun i ↦ -e i) x hmem
    rw [h.grading_piece, Finset.sum_neg_distrib] at hout
    convert hout using 2
    ring

/-- A minimal strictly unital zigzag `A∞` deformation whose operations above arity two vanish is
equal to `zigzagAlgebraStrictAInfinityAlgebra k G`. -/
theorem eq_zigzagAlgebraStrictAInfinityAlgebra (h : IsZigzagAInfinityDeformation k G 𝒜)
    (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) :
    𝒜 = zigzagAlgebraStrictAInfinityAlgebra k G := by
  have hG : 𝒜.grading = InternalGrading.ofDecomposition (zigzagAlgebraIntegerGrade k G) := by
    ext p
    simp [h.grading_piece]
  refine (𝒜.eq_toAInfinityAlgebra hG h.m_two_pair hm).trans ?_
  have hd := h.differential_eq_zero
  unfold zigzagAlgebraStrictAInfinityAlgebra
  congr 1

/-- A minimal strictly unital zigzag `A∞` deformation whose operations above arity two vanish is
formal. -/
theorem isFormal_of_forall_m_eq_zero (h : IsZigzagAInfinityDeformation k G 𝒜)
    (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) : 𝒜.IsFormal :=
  h.isMinimal.isFormal hm

/-- **Formality via `A∞` isomorphism**: a minimal strictly unital zigzag `A∞` deformation is formal
if and only if it is `A∞` isomorphic to `zigzagAlgebraStrictAInfinityAlgebra k G`. -/
theorem isFormal_iff_exists_isIso (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.IsFormal ↔ ∃ f : AInfinityHom 𝒜 (zigzagAlgebraStrictAInfinityAlgebra k G), f.IsIso :=
  h.isMinimal.isFormal_iff_exists_isIso
    (isMinimal_zigzagAlgebraStrictAInfinityAlgebra k G)
    (fun _ hn ↦ zigzagAlgebraStrictAInfinityAlgebra_m_of_three_le k G hn)
    h.grading_eq_zigzagAlgebraStrictAInfinityAlgebra
    h.m_two_eq_zigzagAlgebraStrictAInfinityAlgebra

end IsZigzagAInfinityDeformation

/-! ### Pullback along graded algebra equivalences -/

section Pullback

variable {k : Type w} [CommRing k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- Pull back an `A∞` algebra structure along a graded `k`-algebra equivalence out of
`zigzagAlgebra k G`. -/
private noncomputable def comapZigzagAlgEquiv {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p) :
    AInfinityAlgebra k (zigzagAlgebra k G) :=
  ℬ.comap (zigzagAlgebraInternalGrading k G) φ.toLinearMap φ.injective hφ
    fun _ _ _ ↦ ⟨_, φ.apply_symm_apply _⟩

private theorem comapZigzagAlgEquiv_grading {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p) :
    (comapZigzagAlgEquiv ℬ φ hφ).grading = zigzagAlgebraInternalGrading k G :=
  ℬ.comap_grading (zigzagAlgebraInternalGrading k G) φ.toLinearMap φ.injective hφ _

private theorem apply_comapZigzagAlgEquiv_m {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p)
    (n : ℕ) (x : Fin n → zigzagAlgebra k G) :
    φ ((comapZigzagAlgEquiv ℬ φ hφ).m n x) = ℬ.m n (fun i ↦ φ (x i)) :=
  ℬ.map_m_comap (zigzagAlgebraInternalGrading k G) φ.toLinearMap φ.injective hφ
    (fun _ _ _ ↦ ⟨_, φ.apply_symm_apply _⟩) n x

private theorem isIso_comapZigzagAlgEquiv {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p) :
    (ℬ.comapStrictHom (zigzagAlgebraInternalGrading k G) φ.toLinearMap φ.injective hφ
      (fun _ _ _ ↦ ⟨_, φ.apply_symm_apply _⟩)).toAInfinityHom.IsIso :=
  ℬ.isIso_toAInfinityHom_comapStrictHom (zigzagAlgebraInternalGrading k G) φ.toLinearMap
    φ.injective hφ (fun _ _ _ ↦ ⟨_, φ.apply_symm_apply _⟩) φ.bijective

private theorem isFormal_comapZigzagAlgEquiv_iff {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p) :
    (comapZigzagAlgEquiv ℬ φ hφ).IsFormal ↔ ℬ.IsFormal :=
  (isIso_comapZigzagAlgEquiv ℬ φ hφ).isFormal_iff

private theorem isZigzagAInfinityDeformation_comapZigzagAlgEquiv {B : Type*} [Ring B] [Algebra k B]
    (ℬ : AInfinityAlgebra k B) (φ : zigzagAlgebra k G ≃ₐ[k] B)
    (hφ : ∀ (p : ℤ) (x : zigzagAlgebra k G),
      φ x ∈ ℬ.grading.piece p ↔ x ∈ zigzagAlgebraIntegerGrade k G p)
    (hmin : ℬ.IsMinimal) (hm₂ : ∀ x : Fin 2 → B, ℬ.m 2 x = x 0 * x 1) (hunit : ℬ.StrictUnit 1) :
    IsZigzagAInfinityDeformation k G (comapZigzagAlgEquiv ℬ φ hφ) where
  grading_piece := congrArg InternalGrading.piece (comapZigzagAlgEquiv_grading ℬ φ hφ)
  isMinimal := (AInfinityAlgebra.isMinimal_iff_m_one_eq_zero _).2 fun x ↦ φ.injective <|
    (apply_comapZigzagAlgEquiv_m ℬ φ hφ 1 ![x]).trans ((hmin.m_one _).trans (map_zero φ).symm)
  m_two x := φ.injective <|
    (apply_comapZigzagAlgEquiv_m ℬ φ hφ 2 x).trans
      ((hm₂ _).trans (map_mul φ (x 0) (x 1)).symm)
  strictUnit := AInfinityAlgebra.StrictUnit.comap ℬ (zigzagAlgebraInternalGrading k G)
    φ.toLinearMap φ.injective hφ (fun _ _ _ ↦ ⟨_, φ.apply_symm_apply _⟩) (e := 1)
    (by simpa [map_one] using hunit)

/-! #### Transport along graph isomorphisms -/

/-- Pull back a minimal strictly unital zigzag `A∞` deformation along a graph isomorphism
`e : G ≃g H`, using `TauCeti.zigzagAlgebraEquiv`. -/
noncomputable def IsZigzagAInfinityDeformation.comapGraphIso {W : Type v} [Finite W]
    {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) :
    AInfinityAlgebra k (zigzagAlgebra k G) :=
  comapZigzagAlgEquiv ℬ (zigzagAlgebraEquiv k G e) fun p x ↦ by
    rw [h.grading_piece, zigzagAlgebraEquiv_mem_zigzagAlgebraIntegerGrade_iff]

/-- The internal grading of `comapGraphIso` is `zigzagAlgebraInternalGrading k G`. -/
@[simp]
theorem IsZigzagAInfinityDeformation.comapGraphIso_grading {W : Type v} [Finite W]
    {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) :
    (h.comapGraphIso e).grading = zigzagAlgebraInternalGrading k G :=
  comapZigzagAlgEquiv_grading ℬ (zigzagAlgebraEquiv k G e) _

/-- `zigzagAlgebraEquiv` intertwines every operation of `comapGraphIso` with that of `ℬ`. -/
@[simp]
theorem IsZigzagAInfinityDeformation.zigzagAlgebraEquiv_comapGraphIso_m {W : Type v} [Finite W]
    {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) (n : ℕ)
    (x : Fin n → zigzagAlgebra k G) :
    zigzagAlgebraEquiv k G e ((h.comapGraphIso e).m n x) =
      ℬ.m n (fun i ↦ zigzagAlgebraEquiv k G e (x i)) :=
  apply_comapZigzagAlgEquiv_m ℬ (zigzagAlgebraEquiv k G e) _ n x

/-- Explicit formula for each operation of `comapGraphIso`. -/
theorem IsZigzagAInfinityDeformation.comapGraphIso_m_apply {W : Type v} [Finite W]
    {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) (n : ℕ)
    (x : Fin n → zigzagAlgebra k G) :
    (h.comapGraphIso e).m n x =
      (zigzagAlgebraEquiv k G e).symm (ℬ.m n (fun i ↦ zigzagAlgebraEquiv k G e (x i))) := by
  rw [← h.zigzagAlgebraEquiv_comapGraphIso_m e n x, AlgEquiv.symm_apply_apply]

/-- Pulling back along a graph isomorphism preserves minimal strictly unital zigzag `A∞`
deformations. -/
theorem IsZigzagAInfinityDeformation.isZigzagAInfinityDeformation_comapGraphIso {W : Type v}
    [Finite W] {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) :
    IsZigzagAInfinityDeformation k G (h.comapGraphIso e) :=
  isZigzagAInfinityDeformation_comapZigzagAlgEquiv ℬ (zigzagAlgebraEquiv k G e) _
    h.isMinimal h.m_two h.strictUnit

/-- Pulling back a minimal strictly unital zigzag `A∞` deformation along a graph isomorphism
preserves and reflects formality. -/
@[simp]
theorem IsZigzagAInfinityDeformation.isFormal_comapGraphIso_iff {W : Type v} [Finite W]
    {H : SimpleGraph W} {ℬ : AInfinityAlgebra k (zigzagAlgebra k H)}
    (h : IsZigzagAInfinityDeformation k H ℬ) (e : G ≃g H) :
    (h.comapGraphIso e).IsFormal ↔ ℬ.IsFormal :=
  isFormal_comapZigzagAlgEquiv_iff ℬ (zigzagAlgebraEquiv k G e) _

/-! #### Loop deformations on the public algebra of a connected nontrivial graph -/

omit [Finite V] in
/-- On a connected graph with at least two vertices, every vertex has an incident edge. -/
theorem exists_adj_of_connected (hconn : G.Connected) [Nontrivial V] (i : V) : ∃ j, G.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr (hconn.preconnected.not_isIsolated i)

/-- **Loop `A∞` deformation of the public zigzag algebra** on a connected graph `G` with at least
two vertices: the pullback of `TauCeti.zigzagLoopAInfinityAlgebra` along the canonical graded
algebra isomorphism `TauCeti.zigzagAlgebraEquivNonisolated`. -/
noncomputable def zigzagAlgebraLoopAInfinityAlgebra (hconn : G.Connected) [Nontrivial V]
    {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    AInfinityAlgebra k (zigzagAlgebra k G) :=
  comapZigzagAlgEquiv
    (zigzagLoopAInfinityAlgebra (exists_adj_of_connected hconn) c hc)
    (zigzagAlgebraEquivNonisolated k G hconn) fun p x ↦ by
      rw [zigzagLoopAInfinityAlgebra_grading_piece,
        zigzagAlgebraEquivNonisolated_mem_zigzagIntegerGrade_iff]

/-- The internal grading of `zigzagAlgebraLoopAInfinityAlgebra` is
`zigzagAlgebraInternalGrading k G`. -/
@[simp]
theorem zigzagAlgebraLoopAInfinityAlgebra_grading (hconn : G.Connected) [Nontrivial V]
    {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (zigzagAlgebraLoopAInfinityAlgebra hconn c hc).grading = zigzagAlgebraInternalGrading k G :=
  comapZigzagAlgEquiv_grading _ _ _

/-- `zigzagAlgebraEquivNonisolated` intertwines every operation of
`zigzagAlgebraLoopAInfinityAlgebra` with that of `zigzagLoopAInfinityAlgebra`. -/
@[simp]
theorem zigzagAlgebraEquivNonisolated_zigzagAlgebraLoopAInfinityAlgebra_m (hconn : G.Connected)
    [Nontrivial V] {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) (m : ℕ)
    (x : Fin m → zigzagAlgebra k G) :
    zigzagAlgebraEquivNonisolated k G hconn ((zigzagAlgebraLoopAInfinityAlgebra hconn c hc).m m x) =
      (zigzagLoopAInfinityAlgebra (exists_adj_of_connected hconn) c hc).m m
        (fun i ↦ zigzagAlgebraEquivNonisolated k G hconn (x i)) :=
  apply_comapZigzagAlgEquiv_m _ _ _ m x

/-- Explicit formula for each operation of `zigzagAlgebraLoopAInfinityAlgebra`. -/
theorem zigzagAlgebraLoopAInfinityAlgebra_m_apply (hconn : G.Connected) [Nontrivial V]
    {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) (m : ℕ)
    (x : Fin m → zigzagAlgebra k G) :
    (zigzagAlgebraLoopAInfinityAlgebra hconn c hc).m m x =
      (zigzagAlgebraEquivNonisolated k G hconn).symm
        ((zigzagLoopAInfinityAlgebra (exists_adj_of_connected hconn) c hc).m m
          (fun i ↦ zigzagAlgebraEquivNonisolated k G hconn (x i))) := by
  rw [← zigzagAlgebraEquivNonisolated_zigzagAlgebraLoopAInfinityAlgebra_m hconn c hc m x,
    AlgEquiv.symm_apply_apply]

/-- Every loop deformation `zigzagAlgebraLoopAInfinityAlgebra` on a connected nontrivial graph is a
minimal strictly unital `A∞` deformation of `zigzagAlgebra k G`. -/
theorem isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra (hconn : G.Connected)
    [Nontrivial V] {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    IsZigzagAInfinityDeformation k G (zigzagAlgebraLoopAInfinityAlgebra hconn c hc) :=
  isZigzagAInfinityDeformation_comapZigzagAlgEquiv _ _ _
    (isMinimal_zigzagLoopAInfinityAlgebra c hc)
    (zigzagLoopAInfinityAlgebra_m_two_apply c hc)
    (strictUnit_one_zigzagLoopAInfinityAlgebra c hc)

/-- Formality of `zigzagAlgebraLoopAInfinityAlgebra` on the public zigzag algebra agrees with
formality of `zigzagLoopAInfinityAlgebra` on the relation quotient. -/
@[simp]
theorem isFormal_zigzagAlgebraLoopAInfinityAlgebra_iff (hconn : G.Connected) [Nontrivial V]
    {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (zigzagAlgebraLoopAInfinityAlgebra hconn c hc).IsFormal ↔
      (zigzagLoopAInfinityAlgebra (exists_adj_of_connected hconn) c hc).IsFormal :=
  isFormal_comapZigzagAlgEquiv_iff _ _ _

/-- Every operation of `zigzagAlgebraLoopAInfinityAlgebra` other than `m₂` and `mₙ` vanishes. -/
theorem zigzagAlgebraLoopAInfinityAlgebra_m_eq_zero (hconn : G.Connected) [Nontrivial V]
    {n : ℕ} [NeZero n] (c : (Fin n → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) {m : ℕ} (h₂ : m ≠ 2) (hn : m ≠ n) :
    (zigzagAlgebraLoopAInfinityAlgebra hconn c hc).m m = 0 :=
  MultilinearMap.ext fun x ↦ by
    rw [zigzagAlgebraLoopAInfinityAlgebra_m_apply, zigzagLoopAInfinityAlgebra_m_eq_zero c hc h₂ hn,
      zero_apply, zero_apply, map_zero]

/-! #### Liu--Wang's Example 4.7 on the public affine `D₄` zigzag algebra -/

private instance : (AffineDynkinType.D 4).nodes.AtLeastTwo := ⟨by decide⟩

variable (k) in
/-- **Liu--Wang's quartic `A∞` algebra on the public affine `D₄` zigzag algebra** (Example 4.7),
with scalar `c`: the transport of `TauCeti.liuWangAffineD4AInfinityAlgebra` along
`zigzagAlgebraEquivNonisolated`. -/
noncomputable def zigzagAlgebraLiuWangAffineD4 (c : k) :
    AInfinityAlgebra k (zigzagAlgebra k (AffineDynkinType.D 4).graph) :=
  zigzagAlgebraLoopAInfinityAlgebra
    (AffineDynkinType.graph_connected (AffineDynkinType.valid_D.2 le_rfl))
    (liuWangAffineD4Coefficients k c) (fst_eq_snd_of_mem_support_liuWangAffineD4Coefficients c)

/-- The internal grading of `zigzagAlgebraLiuWangAffineD4` is `zigzagAlgebraInternalGrading`. -/
@[simp]
theorem zigzagAlgebraLiuWangAffineD4_grading (c : k) :
    (zigzagAlgebraLiuWangAffineD4 k c).grading =
      zigzagAlgebraInternalGrading k (AffineDynkinType.D 4).graph :=
  zigzagAlgebraLoopAInfinityAlgebra_grading _ _ _

/-- The binary operation of `zigzagAlgebraLiuWangAffineD4` is multiplication in
`zigzagAlgebra k (AffineDynkinType.D 4).graph`. -/
@[simp]
theorem zigzagAlgebraLiuWangAffineD4_m_two_apply (c : k)
    (x : Fin 2 → zigzagAlgebra k (AffineDynkinType.D 4).graph) :
    (zigzagAlgebraLiuWangAffineD4 k c).m 2 x = x 0 * x 1 :=
  (isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra _ _ _).m_two x

/-- Every operation of `zigzagAlgebraLiuWangAffineD4` other than `m₂` and `m₄` vanishes. -/
theorem zigzagAlgebraLiuWangAffineD4_m_eq_zero (c : k) {m : ℕ} (h₂ : m ≠ 2) (h₄ : m ≠ 4) :
    (zigzagAlgebraLiuWangAffineD4 k c).m m = 0 :=
  zigzagAlgebraLoopAInfinityAlgebra_m_eq_zero _ _ _ h₂ h₄

/-- Liu--Wang's affine `D₄` algebra is a minimal strictly unital `A∞` deformation of the public
affine `D₄` zigzag algebra. -/
theorem isZigzagAInfinityDeformation_zigzagAlgebraLiuWangAffineD4 (c : k) :
    IsZigzagAInfinityDeformation k (AffineDynkinType.D 4).graph
      (zigzagAlgebraLiuWangAffineD4 k c) :=
  isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra _ _ _

/-- Liu--Wang's symmetric four-rotation quartic algebra on the public affine `D₄` zigzag algebra is
formal for every scalar `c` (its `m₄` is a backtrack coboundary). -/
theorem isFormal_zigzagAlgebraLiuWangAffineD4 (c : k) :
    (zigzagAlgebraLiuWangAffineD4 k c).IsFormal := by
  rw [zigzagAlgebraLiuWangAffineD4, isFormal_zigzagAlgebraLoopAInfinityAlgebra_iff]
  simp only [liuWangAffineD4Coefficients_eq_zigzagBacktrackCoefficients]
  exact isFormal_zigzagLoopAInfinityAlgebra_zigzagBacktrackCoefficients _ _
    fst_eq_snd_of_mem_liuWangAffineD4BacktrackPairs ne_symm_of_mem_liuWangAffineD4BacktrackPairs

end Pullback

/-! ### Intrinsic formality of the public zigzag algebra -/

/-- The path-graded public zigzag algebra `zigzagAlgebra k G` is **intrinsically formal** when every
minimal strictly unital `A∞` deformation (`TauCeti.IsZigzagAInfinityDeformation`) on
`zigzagAlgebra k G` is formal. -/
def IsZigzagAlgebraIntrinsicallyFormal (k : Type w) [CommRing k] {V : Type u} [Finite V]
    (G : SimpleGraph V) : Prop :=
  ∀ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
    IsZigzagAInfinityDeformation k G 𝒜 → 𝒜.IsFormal

/-- Unfolding `IsZigzagAlgebraIntrinsicallyFormal`. -/
theorem isZigzagAlgebraIntrinsicallyFormal_def (k : Type w) [CommRing k] {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    IsZigzagAlgebraIntrinsicallyFormal k G ↔
      ∀ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
        IsZigzagAInfinityDeformation k G 𝒜 → 𝒜.IsFormal :=
  Iff.rfl

section IntrinsicFormality

variable {k : Type w} [CommRing k] {V : Type u} [Finite V] {G : SimpleGraph V}

/-- Every minimal strictly unital `A∞` deformation of an intrinsically formal zigzag algebra is
formal. -/
theorem IsZigzagAlgebraIntrinsicallyFormal.isFormal (h : IsZigzagAlgebraIntrinsicallyFormal k G)
    {𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)} (h𝒜 : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜.IsFormal :=
  h 𝒜 h𝒜

/-- Every minimal strictly unital `A∞` deformation of an intrinsically formal zigzag algebra is
`A∞` isomorphic to `zigzagAlgebraStrictAInfinityAlgebra k G`. -/
theorem IsZigzagAlgebraIntrinsicallyFormal.exists_isIso
    (h : IsZigzagAlgebraIntrinsicallyFormal k G)
    {𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)} (h𝒜 : IsZigzagAInfinityDeformation k G 𝒜) :
    ∃ f : AInfinityHom 𝒜 (zigzagAlgebraStrictAInfinityAlgebra k G), f.IsIso :=
  h𝒜.isFormal_iff_exists_isIso.mp (h.isFormal h𝒜)

/-- Unitality-free intrinsic formality of `zigzagAlgebraStrictAInfinityAlgebra k G` implies
`IsZigzagAlgebraIntrinsicallyFormal k G`. -/
theorem AInfinityAlgebra.IsIntrinsicallyFormal.isZigzagAlgebraIntrinsicallyFormal
    (h : (zigzagAlgebraStrictAInfinityAlgebra k G).IsIntrinsicallyFormal) :
    IsZigzagAlgebraIntrinsicallyFormal k G :=
  fun _ h𝒜 ↦ h.isFormal_of_isMinimal
    h𝒜.grading_eq_zigzagAlgebraStrictAInfinityAlgebra
    h𝒜.isMinimal
    h𝒜.m_two_eq_zigzagAlgebraStrictAInfinityAlgebra

/-- **Kadeishvili's vanishing criterion for the public zigzag algebra**, over any commutative ring:
if `HH^{n, 2 - n}` of `zigzagAlgebraStrictAInfinityAlgebra k G` vanishes for all `n ≥ 3`, then
`zigzagAlgebra k G` is intrinsically formal. -/
theorem isZigzagAlgebraIntrinsicallyFormal_of_forall_hochschildVanishesAt
    (hHH : ∀ n (hn : 3 ≤ n),
      (zigzagAlgebraStrictAInfinityAlgebra k G).HochschildVanishesAt ⟨n, by omega⟩) :
    IsZigzagAlgebraIntrinsicallyFormal k G :=
  fun _ h𝒜 ↦ h𝒜.isFormal_iff_exists_isIso.mpr <|
    h𝒜.isMinimal.exists_isIso_of_forall_hochschildVanishesAt
      (isMinimal_zigzagAlgebraStrictAInfinityAlgebra k G)
      (fun _ hn ↦ zigzagAlgebraStrictAInfinityAlgebra_m_of_three_le k G hn)
      h𝒜.grading_eq_zigzagAlgebraStrictAInfinityAlgebra
      h𝒜.m_two_eq_zigzagAlgebraStrictAInfinityAlgebra hHH

/-- **Kadeishvili's vanishing criterion via the relation quotient**, over any commutative ring: on a
connected graph `G` with at least two vertices, if `HH^{n, 2 - n}` of `zigzagStrictAInfinityAlgebra`
vanishes for all `n ≥ 3`, then `zigzagAlgebra k G` is intrinsically formal. -/
theorem isZigzagAlgebraIntrinsicallyFormal_of_forall_hochschildVanishesAt_nonisolated
    (hconn : G.Connected) [Nontrivial V] {hns : ∀ i : V, ∃ j, G.Adj i j}
    (hHH : ∀ n (hn : 3 ≤ n),
      (zigzagStrictAInfinityAlgebra k hns).HochschildVanishesAt ⟨n, by omega⟩) :
    IsZigzagAlgebraIntrinsicallyFormal k G := by
  intro 𝒜 h𝒜
  let ψ := (zigzagAlgebraEquivNonisolated k G hconn).symm
  have hdeg : ∀ (p : ℤ) (y : nonisolatedZigzagQuotient k G),
      ψ y ∈ 𝒜.grading.piece p ↔ y ∈ (zigzagStrictAInfinityAlgebra k hns).grading.piece p := by
    intro p y
    rw [h𝒜.grading_piece, zigzagStrictAInfinityAlgebra_grading_piece,
      ← zigzagAlgebraEquivNonisolated_mem_zigzagIntegerGrade_iff k G hconn,
      AlgEquiv.apply_symm_apply]
  have hrange : ∀ n, 0 < n → ∀ y : Fin n → nonisolatedZigzagQuotient k G,
      𝒜.m n (fun i ↦ ψ.toLinearMap (y i)) ∈ LinearMap.range ψ.toLinearMap :=
    fun _ _ _ ↦ ⟨_, ψ.apply_symm_apply _⟩
  let ℬ := 𝒜.comap (zigzagStrictAInfinityAlgebra k hns).grading ψ.toLinearMap ψ.injective hdeg
    hrange
  have hiso : (𝒜.comapStrictHom (zigzagStrictAInfinityAlgebra k hns).grading ψ.toLinearMap
      ψ.injective hdeg hrange).toAInfinityHom.IsIso :=
    𝒜.isIso_toAInfinityHom_comapStrictHom _ _ ψ.injective hdeg hrange ψ.bijective
  rw [← hiso.isFormal_iff]
  have hℬmin : ℬ.IsMinimal := (AInfinityAlgebra.isMinimal_iff_m_one_eq_zero ℬ).2 fun y ↦
    ψ.injective <| by
      have hm := 𝒜.map_m_comap _ ψ.toLinearMap ψ.injective hdeg hrange 1 ![y]
      exact hm.trans ((h𝒜.m_one_apply _).trans (map_zero ψ).symm)
  have hℬtwo : ℬ.m 2 = (zigzagStrictAInfinityAlgebra k hns).m 2 :=
    MultilinearMap.ext fun y ↦ ψ.injective <| by
      have hm := 𝒜.map_m_comap _ ψ.toLinearMap ψ.injective hdeg hrange 2 y
      exact hm.trans <| by
        rw [h𝒜.m_two, zigzagStrictAInfinityAlgebra_m_two_apply]
        simp [map_mul]
  exact (hℬmin.isFormal_iff_exists_isIso isMinimal_zigzagStrictAInfinityAlgebra
    (fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
    (𝒜.comap_grading _ _ _ _ _) hℬtwo).mpr <|
      hℬmin.exists_isIso_of_forall_hochschildVanishesAt isMinimal_zigzagStrictAInfinityAlgebra
        (fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
        (𝒜.comap_grading _ _ _ _ _) hℬtwo hHH

/-! ### Intrinsic formality of `A₁` and graphs with at most one vertex -/

/-- **Vanishing of higher operations on graphs with at most one vertex**: when `V` is a subsingleton
(the Dynkin `A₁` graph or the empty graph), every minimal strictly unital `A∞` deformation of
`zigzagAlgebra k G` has `mₙ = 0` for all `n ≥ 3`, over any commutative ring. Indeed there are no
darts, any vertex basis vector equals `1` and is killed by strict unitality, and `n ≥ 3` volume
inputs of degree `2` map into degree `n + 2 ≥ 5`, where `zigzagAlgebraIntegerGrade` vanishes. -/
theorem IsZigzagAInfinityDeformation.m_eq_zero_of_subsingleton [Subsingleton V]
    {𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)} (h : IsZigzagAInfinityDeformation k G 𝒜)
    {n : ℕ} (hn : 3 ≤ n) : 𝒜.m n = 0 := by
  classical
  refine Module.Basis.ext_multilinear (fun _ : Fin n ↦ zigzagAlgebraBasis k G) fun b ↦ ?_
  rw [zero_apply]
  by_cases hunit : ∃ (i : Fin n) (v : V), b i = .inl v
  · obtain ⟨i, v, hi⟩ := hunit
    let _ : Unique V := ⟨⟨v⟩, fun w ↦ Subsingleton.elim w v⟩
    let _ : Fintype V := Fintype.ofFinite V
    have hdefault : zigzagAlgebraBasis k G (.inl v) = 1 := by
      have hv : v = default := Subsingleton.elim v default
      rw [hv]
      exact CompleteOrthogonalIdempotents.unique_iff.mp
        (completeOrthogonalIdempotents_zigzagAlgebraBasis_inl k G)
    exact h.strictUnit.m_eq_zero_of_eq_unit (by omega) _ (by rw [hi, hdefault])
  · have hmem : ∀ j : Fin n, zigzagAlgebraBasis k G (b j) ∈ 𝒜.grading.piece 2 := by
      intro j
      rw [h.grading_piece]
      rcases hbj : b j with v | d | v
      · exact (hunit ⟨j, v, hbj⟩).elim
      · exact (G.ne_of_adj d.adj (Subsingleton.elim _ _)).elim
      · exact (zigzagAlgebraIntegerGrade_ofNat k G 2).symm ▸
          zigzagAlgebraBasis_inr_inr_mem_grade_two k G v
    have hout := (𝒜.m_degree n (by omega)).map_mem (fun _ ↦ (2 : ℤ)) _ hmem
    rw [h.grading_piece, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      zigzagAlgebraIntegerGrade_eq_bot_of_not_mem k G
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Submodule.mem_bot] at hout
    exact hout

/-- When `V` is a subsingleton, the strict `A∞` algebra is the unique minimal strictly unital `A∞`
deformation of `zigzagAlgebra k G`. -/
theorem IsZigzagAInfinityDeformation.eq_zigzagAlgebraStrictAInfinityAlgebra_of_subsingleton
    [Subsingleton V] {𝒜 : AInfinityAlgebra k (zigzagAlgebra k G)}
    (h : IsZigzagAInfinityDeformation k G 𝒜) :
    𝒜 = zigzagAlgebraStrictAInfinityAlgebra k G :=
  h.eq_zigzagAlgebraStrictAInfinityAlgebra fun _ hn ↦ h.m_eq_zero_of_subsingleton hn

/-- **Intrinsic formality of `A₁` and empty graphs**: when `V` is a subsingleton, the path-graded
public zigzag algebra `zigzagAlgebra k G` is intrinsically formal over every commutative ring. -/
theorem isZigzagAlgebraIntrinsicallyFormal_of_subsingleton (k : Type w) [CommRing k]
    {V : Type u} [Finite V] [Subsingleton V] (G : SimpleGraph V) :
    IsZigzagAlgebraIntrinsicallyFormal k G :=
  fun _ h𝒜 ↦ h𝒜.isFormal_of_forall_m_eq_zero fun _ hn ↦ h𝒜.m_eq_zero_of_subsingleton hn

/-! ### Connected non-formality criteria on the public zigzag algebra -/

omit [Finite V] in
private theorem nontrivial_of_isContained_valid {t : AffineDynkinType} (ht : t.Valid)
    (hG : t.graph.IsContained G) : Nontrivial V := by
  obtain ⟨f⟩ := hG
  obtain ⟨_, hj⟩ := t.exists_adj_graph ht ⟨0, t.nodes_pos⟩
  let _ : Nontrivial (Fin t.nodes) := hj.nontrivial
  exact f.injective.nontrivial

/-- On a connected nontrivial graph, any non-formal loop deformation on `nonisolatedZigzagQuotient`
yields a non-formal minimal strictly unital `A∞` deformation on `zigzagAlgebra k G`, refuting
`IsZigzagAlgebraIntrinsicallyFormal k G`. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra
    (hconn : G.Connected) [Nontrivial V] {n : ℕ} [NeZero n]
    {c : (Fin n → G.Dart) →₀ k} {hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd}
    (hnf : ¬(zigzagLoopAInfinityAlgebra (exists_adj_of_connected hconn) c hc).IsFormal) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := fun hf ↦
  hnf <| (isFormal_zigzagAlgebraLoopAInfinityAlgebra_iff hconn c hc).mp <|
    hf (zigzagAlgebraLoopAInfinityAlgebra hconn c hc)
      (isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra hconn c hc)

/-- **Connected graphs with a vertex of degree at least four are not intrinsically formal**, over
every nontrivial commutative ring in which `2` is invertible. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_four_le_degree [Nontrivial k]
    [Invertible (2 : k)] (hconn : G.Connected) {v : V} [Fintype (G.neighborSet v)]
    (hv : 4 ≤ G.degree v) : ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := G.nontrivial_of_degree_ne_zero (by omega : G.degree v ≠ 0)
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_four_le_degree
    (k := k) (hns := exists_adj_of_connected hconn) hv
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **Connected graphs with two distinct vertices of degree at least three are not intrinsically
formal**, over every nontrivial commutative ring in which `2` is invertible. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_three_le_degree [Nontrivial k]
    [Invertible (2 : k)] (hconn : G.Connected) {v w : V} [Fintype (G.neighborSet v)]
    [Fintype (G.neighborSet w)] (hvw : v ≠ w) (hv : 3 ≤ G.degree v) (hw : 3 ≤ G.degree w) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := ⟨⟨v, w, hvw⟩⟩
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_three_le_degree
    (k := k) (hns := exists_adj_of_connected hconn) hvw (hconn.preconnected v w) hv hw
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **Connected graphs containing a copy of affine `Dₙ` (`n ≥ 4`) are not intrinsically formal**,
over every nontrivial commutative ring in which `2` is invertible. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_D [Nontrivial k]
    [Invertible (2 : k)] (hconn : G.Connected) {n : ℕ} (hn : 4 ≤ n)
    (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := nontrivial_of_isContained_valid (AffineDynkinType.valid_D.2 hn) hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_D
    (k := k) (hns := exists_adj_of_connected hconn) hn hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `Dₙ` zigzag algebra (`n ≥ 4`) is not intrinsically formal**, over every
nontrivial commutative ring in which `2` is invertible. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineD [Nontrivial k] [Invertible (2 : k)]
    {n : ℕ} (hn : 4 ≤ n) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k (AffineDynkinType.D n).graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_D
    (AffineDynkinType.graph_connected (AffineDynkinType.valid_D.2 hn)) hn .rfl

/-- **Connected graphs containing a copy of affine `E₆` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E6.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := nontrivial_of_isContained_valid (by decide) hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E6
    (k := k) (hns := exists_adj_of_connected hconn) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₆` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE6 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E6.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E6
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-- **Connected graphs containing a copy of affine `E₇` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E7.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := nontrivial_of_isContained_valid (by decide) hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E7
    (k := k) (hns := exists_adj_of_connected hconn) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₇` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE7 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E7.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E7
    (AffineDynkinType.graph_connected (by decide)) .rfl

/-- **Connected graphs containing a copy of affine `E₈` are not intrinsically formal**, over every
nontrivial `ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8 [Nontrivial k] [Algebra ℚ k]
    (hconn : G.Connected) (hG : AffineDynkinType.E8.graph.IsContained G) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  have : Nontrivial V := nontrivial_of_isContained_valid (by decide) hG
  obtain ⟨_, _, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_E8
    (k := k) (hns := exists_adj_of_connected hconn) hG
  exact not_isZigzagAlgebraIntrinsicallyFormal_of_not_isFormal_zigzagLoopAInfinityAlgebra hconn hnf

/-- **The public affine `E₈` zigzag algebra is not intrinsically formal**, over every nontrivial
`ℚ`-algebra. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_affineE8 [Nontrivial k] [Algebra ℚ k] :
    ¬IsZigzagAlgebraIntrinsicallyFormal k AffineDynkinType.E8.graph :=
  not_isZigzagAlgebraIntrinsicallyFormal_of_isContained_E8
    (AffineDynkinType.graph_connected (by decide)) .rfl

end IntrinsicFormality

end TauCeti

/-! ### Graph-isomorphism invariance and non-Dynkin trees -/

namespace SimpleGraph.Iso

universe u v w

/-- **Intrinsic formality of the public zigzag algebra is invariant under graph isomorphism**, even
across distinct vertex universes. -/
theorem isZigzagAlgebraIntrinsicallyFormal_iff (k : Type w) [CommRing k]
    {V : Type u} {W : Type v} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    TauCeti.IsZigzagAlgebraIntrinsicallyFormal k G ↔
      TauCeti.IsZigzagAlgebraIntrinsicallyFormal k H := by
  refine ⟨fun hG ℬ hℬ ↦ ?_, fun hH 𝒜 h𝒜 ↦ ?_⟩
  · rw [← hℬ.isFormal_comapGraphIso_iff e]
    exact hG _ (hℬ.isZigzagAInfinityDeformation_comapGraphIso e)
  · rw [← h𝒜.isFormal_comapGraphIso_iff e.symm]
    exact hH _ (h𝒜.isZigzagAInfinityDeformation_comapGraphIso e.symm)

end SimpleGraph.Iso

namespace SimpleGraph.IsTree

open TauCeti

universe u w

variable {k : Type w} [CommRing k] [Nontrivial k] [Algebra ℚ k]
  {V : Type u} [Finite V] {G : SimpleGraph V}

/-- **Every finite non-Dynkin tree admits a non-formal minimal strictly unital `A∞` deformation** of
its public zigzag algebra `zigzagAlgebra k G`, over any nontrivial `ℚ`-algebra (in particular over
any field of characteristic zero). -/
theorem exists_isZigzagAInfinityDeformation_not_isFormal (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
      IsZigzagAInfinityDeformation k G 𝒜 ∧ ¬𝒜.IsFormal := by
  classical
  have := Fintype.ofFinite V
  have : Nontrivial V := by
    rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
      ⟨n, hn, h⟩ | h | h | h
    · exact nontrivial_of_isContained_valid (AffineDynkinType.valid_D.2 hn) h
    · exact nontrivial_of_isContained_valid (by decide) h
    · exact nontrivial_of_isContained_valid (by decide) h
    · exact nontrivial_of_isContained_valid (by decide) h
  obtain ⟨_, _, _, c, hc, hnf⟩ := hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra
    (k := k) (hns := exists_adj_of_connected hG.connected) hD
  exact ⟨zigzagAlgebraLoopAInfinityAlgebra hG.connected c hc,
    isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra hG.connected c hc,
    (isFormal_zigzagAlgebraLoopAInfinityAlgebra_iff hG.connected c hc).not.mpr hnf⟩

/-- **The public zigzag algebra of a finite non-Dynkin tree is not intrinsically formal**, over any
nontrivial `ℚ`-algebra (in particular over any field of characteristic zero). This proves the
non-Dynkin implication of Liu and Wang's Theorem 1.1 on `TauCeti.zigzagAlgebra k G`. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  obtain ⟨𝒜, h𝒜, hnf⟩ := hG.exists_isZigzagAInfinityDeformation_not_isFormal (k := k) hD
  exact fun hf ↦ hnf (hf 𝒜 h𝒜)

end SimpleGraph.IsTree
