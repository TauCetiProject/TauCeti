/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Submodule families in an ideal quotient

`TauCeti.GradedAlgebra.quotientPiece 𝒜 I i` is the image of the submodule `𝒜 i` under
`Ideal.Quotient.mkₐ R I`. The family can be arbitrary: multiplicative families descend to
multiplicative families, and spanning families descend to spanning families. These results apply
to overlapping families such as polynomial degree filtrations, without asserting a direct-sum
grading of the quotient.

The scalar base is a commutative semiring, and `I` is a two-sided ideal of the ambient ring.
When `𝒜` is a grading and `I` is homogeneous, the additional direct-sum construction is in
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient`.

The quotient-piece construction follows Antoine Chambert-Loir's
[Mathlib PR #36501](https://github.com/leanprover-community/mathlib4/pull/36501).

## Main results

* `TauCeti.GradedAlgebra.quotientPiece_mul_quotientPiece_le`: multiplication respects the family.
* `TauCeti.GradedAlgebra.quotientPiece_eq_span_image`: taking quotient pieces commutes with spans.
* `TauCeti.GradedAlgebra.quotientPiece_le_iff_of_eq_span`: a piece lies in a submodule of the
  quotient exactly when the classes of a spanning set of the original piece do.
* `TauCeti.GradedAlgebra.quotientPiece_eq_bot_iff`: a piece vanishes exactly when it lies in `I`.
* `TauCeti.GradedAlgebra.iSup_quotientPiece_eq_top`: a spanning family spans the quotient.
* `TauCeti.GradedAlgebra.exists_quotient_linearMap_of_map_mul`: a linear endomorphism commuting
  with multiplication by the generators of an ideal induces an endomorphism of the quotient.
-/

public section

namespace TauCeti.GradedAlgebra

variable {ι R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) (I : Ideal A) [I.IsTwoSided]

/-- The image of `𝒜 i` in the quotient by a two-sided ideal `I`. The family `𝒜` need not be
a grading. When it is a grading and `I` is homogeneous, these images grade the quotient. -/
noncomputable def quotientPiece (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

/-- A quotient piece is the image of its original submodule under the quotient map. -/
theorem quotientPiece_def (i : ι) :
    quotientPiece 𝒜 I i = (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap := (rfl)

/-- A quotient piece remains finite whenever the corresponding original piece is finite. -/
instance finite_quotientPiece (𝒜 : ι → Submodule R A) (I : Ideal A) [I.IsTwoSided] (n : ι)
    [Module.Finite R (𝒜 n)] : Module.Finite R (quotientPiece 𝒜 I n) := by
  rw [quotientPiece_def]
  infer_instance

/-- Quotienting by the zero ideal preserves the dimension of each piece. -/
@[simp]
theorem finrank_quotientPiece_bot (𝒜 : ι → Submodule R A) (n : ι) :
    Module.finrank R (quotientPiece 𝒜 ⊥ n) = Module.finrank R (𝒜 n) := by
  have hmap : (quotientPiece 𝒜 ⊥ n).map (AlgEquiv.quotientBot R A).toLinearMap = 𝒜 n := by
    simp only [quotientPiece_def, ← Submodule.map_comp]
    have hc : (AlgEquiv.quotientBot R A).toLinearMap.comp
        (Ideal.Quotient.mkₐ R ⊥).toLinearMap = LinearMap.id := by
      ext x
      exact RingEquiv.quotientBot_mk x
    rw [hc, Submodule.map_id]
  exact ((AlgEquiv.quotientBot R A).toLinearEquiv.finrank_map_eq _).symm.trans
    (congrArg (fun p : Submodule R A ↦ Module.finrank R p) hmap)

/-- Membership in the descended piece is being the class of an element of the original piece. -/
@[simp]
theorem mem_quotientPiece_iff {i : ι} {x : A ⧸ I} :
    x ∈ quotientPiece 𝒜 I i ↔ ∃ y ∈ 𝒜 i, Ideal.Quotient.mk I y = x :=
  Submodule.mem_map

/-- An element of `𝒜 i` lands in the corresponding piece of the quotient. -/
theorem mk_mem_quotientPiece {i : ι} {y : A} (hy : y ∈ 𝒜 i) :
    Ideal.Quotient.mk I y ∈ quotientPiece 𝒜 I i :=
  Submodule.mem_map.2 ⟨y, hy, rfl⟩

/-- Compatible linear maps on an algebra and its quotient preserve the quotient pieces
whenever the original map preserves the original pieces. The family need not be a grading. -/
theorem apply_mem_quotientPiece (T : A →ₗ[R] A) (Q : (A ⧸ I) →ₗ[R] (A ⧸ I))
    (hT : ∀ i x, x ∈ 𝒜 i → T x ∈ 𝒜 i)
    (hQ : ∀ x, Q (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (T x))
    (i : ι) (x : A ⧸ I) (hx : x ∈ quotientPiece 𝒜 I i) :
    Q x ∈ quotientPiece 𝒜 I i := by
  obtain ⟨y, hy, rfl⟩ := (mem_quotientPiece_iff 𝒜 I).mp hx
  rw [hQ]
  exact mk_mem_quotientPiece 𝒜 I (hT i y hy)

/-- The descended piece is the span of the images of any spanning family of the
original piece: descending commutes with spanning. -/
theorem quotientPiece_eq_span_image {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s) :
    quotientPiece 𝒜 I i = Submodule.span R ((Ideal.Quotient.mk I) '' s) := by
  rw [quotientPiece_def, hs, Submodule.map_span]
  simp only [AlgHom.coe_toLinearMap, Ideal.Quotient.mkₐ_eq_mk]

/-- If `s` spans `𝒜 i`, the descended piece lies in a submodule `N` of the quotient exactly when
the classes of the elements of `s` lie in `N`. -/
theorem quotientPiece_le_iff_of_eq_span {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s)
    {N : Submodule R (A ⧸ I)} :
    quotientPiece 𝒜 I i ≤ N ↔ ∀ z ∈ s, Ideal.Quotient.mk I z ∈ N := by
  simp [quotientPiece_eq_span_image 𝒜 I hs, Submodule.span_le, Set.subset_def]

/-- A piece vanishes in the quotient exactly when it is contained in `I`. -/
theorem quotientPiece_eq_bot_iff {i : ι} : quotientPiece 𝒜 I i = ⊥ ↔ ∀ y ∈ 𝒜 i, y ∈ I := by
  simp [← le_bot_iff, quotientPiece_def, IsConcreteLE.le_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- Multiplication adds degrees, as an inclusion of products of pieces. -/
theorem quotientPiece_mul_quotientPiece_le [Add ι] [SetLike.GradedMul 𝒜] (m n : ι) :
    quotientPiece 𝒜 I m * quotientPiece 𝒜 I n ≤ quotientPiece 𝒜 I (m + n) := by
  simp only [quotientPiece, ← Submodule.map_mul (𝒜 m) (𝒜 n) (Ideal.Quotient.mkₐ R I)]
  exact Submodule.map_mono (Submodule.mul_le.2 fun _ hx _ hy => SetLike.mul_mem_graded hx hy)

/-- **Multiplication adds degrees** in the quotient: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_quotientPiece [Add ι] [SetLike.GradedMul 𝒜] {m n : ι} {x y : A ⧸ I}
    (hx : x ∈ quotientPiece 𝒜 I m) (hy : y ∈ quotientPiece 𝒜 I n) :
    x * y ∈ quotientPiece 𝒜 I (m + n) :=
  quotientPiece_mul_quotientPiece_le 𝒜 I m n (Submodule.mul_mem_mul hx hy)

/-- The multiplicative structure of the descended pieces: the unit lies in degree `0` and
multiplication adds degrees. This supplies the instance data for downstream `GradedAlgebra`
constructions; neither independence of the pieces nor homogeneity of `I` is required. Since
`SetLike.GradedMonoid` is a `Prop`-valued class, this can be registered globally without
attaching data to unrelated quotients. -/
instance [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotientPiece 𝒜 I) where
  one_mem := mk_mem_quotientPiece 𝒜 I SetLike.GradedOne.one_mem
  mul_mem _ _ _ _ hx hy := mul_mem_quotientPiece 𝒜 I hx hy

/-- If the original pieces span `A`, their images span the quotient. The pieces may overlap. -/
theorem iSup_quotientPiece_eq_top (h𝒜 : ⨆ i, 𝒜 i = ⊤) : ⨆ i, quotientPiece 𝒜 I i = ⊤ := by
  simp only [quotientPiece]
  rw [← Submodule.map_iSup, h𝒜, Submodule.map_top, LinearMap.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective R I

end TauCeti.GradedAlgebra

namespace TauCeti.GradedAlgebra

variable {ι k A : Type*} [CommSemiring k] [CommRing A] [Algebra k A]

/-- The third isomorphism theorem identifies successive quotient pieces with the piece
in the quotient by the sum of the two ideals. No homogeneity is needed. -/
theorem map_quotientPiece_quotientPiece (𝒜 : ι → Submodule k A) (I J : Ideal A) (n : ι) :
    (quotientPiece (quotientPiece 𝒜 I) (J.map (Ideal.Quotient.mkₐ k I)) n).map
        (DoubleQuot.quotQuotEquivQuotSupₐ k I J).toLinearMap =
      quotientPiece 𝒜 (I ⊔ J) n := by
  simp only [quotientPiece_def, ← Submodule.map_comp]
  apply congrArg (fun f : A →ₗ[k] A ⧸ (I ⊔ J) ↦ (𝒜 n).map f)
  ext x
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    DoubleQuot.coe_quotQuotEquivQuotSupₐ]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J x

end TauCeti.GradedAlgebra

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A linear endomorphism commuting with multiplication by each element of a set `s` preserves the
ideal spanned by `s`, so it induces a compatible endomorphism of the quotient by that ideal, as
required by `apply_mem_quotientPiece`. -/
theorem exists_quotient_linearMap_of_map_mul {s : Set A} (T : A →ₗ[k] A)
    (hmul : ∀ f ∈ s, ∀ x, T (f * x) = f * T x) :
    ∃ Q : (A ⧸ Ideal.span s) →ₗ[k] (A ⧸ Ideal.span s),
      ∀ x, Q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (T x) := by
  have hT : (Ideal.span s).restrictScalars k ≤ ((Ideal.span s).restrictScalars k).comap T := by
    intro x hx
    -- Generalize over the multiplier, since `T` commutes only with multiplication by `s`.
    suffices h : ∀ a, T (a * x) ∈ Ideal.span s by simpa using h 1
    induction hx using Submodule.span_induction with
    | mem f hf =>
      intro a
      rw [mul_comm, hmul f hf]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span hf)
    | zero => simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add]; exact add_mem (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
  refine ⟨(Submodule.Quotient.restrictScalarsEquiv k _).conj (Submodule.mapQ _ _ T hT),
    fun x ↦ ?_⟩
  rw [LinearEquiv.conj_apply_apply, ← Ideal.Quotient.mk_eq_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply,
    Submodule.Quotient.restrictScalarsEquiv_mk, Ideal.Quotient.mk_eq_mk]

end TauCeti.GradedAlgebra
