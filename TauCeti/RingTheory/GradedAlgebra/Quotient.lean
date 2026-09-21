/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.GradedAlgebra.iSup_quotientPiece_eq_top`: a spanning family spans the quotient.
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

/-- Membership in the descended piece is being the class of an element of the original piece. -/
@[simp]
theorem mem_quotientPiece_iff {i : ι} {x : A ⧸ I} :
    x ∈ quotientPiece 𝒜 I i ↔ ∃ y ∈ 𝒜 i, Ideal.Quotient.mk I y = x :=
  Submodule.mem_map

/-- An element of `𝒜 i` lands in the corresponding piece of the quotient. -/
theorem mk_mem_quotientPiece {i : ι} {y : A} (hy : y ∈ 𝒜 i) :
    Ideal.Quotient.mk I y ∈ quotientPiece 𝒜 I i :=
  Submodule.mem_map.2 ⟨y, hy, rfl⟩

/-- The descended piece is the span of the images of any spanning family of the
original piece: descending commutes with spanning. -/
theorem quotientPiece_eq_span_image {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s) :
    quotientPiece 𝒜 I i = Submodule.span R ((Ideal.Quotient.mk I) '' s) := by
  rw [quotientPiece_def, hs, Submodule.map_span]
  simp only [AlgHom.coe_toLinearMap, Ideal.Quotient.mkₐ_eq_mk]

/-- A member of a descended piece lies in the span of `t` if the images of a spanning family of
the original piece lie in that span. -/
theorem mem_span_of_mem_quotientPiece {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s)
    {t : Set (A ⧸ I)}
    (hmem : ∀ z ∈ s, Ideal.Quotient.mk I z ∈ Submodule.span R t)
    {w : A ⧸ I} (hw : w ∈ quotientPiece 𝒜 I i) :
    w ∈ Submodule.span R t := by
  have heq := quotientPiece_eq_span_image 𝒜 I (i := i) hs
  rw [heq] at hw
  refine (Submodule.span_le.2 ?_) hw
  rintro u ⟨z, hz, rfl⟩
  exact hmem z hz

/-- A piece contained in `I` vanishes in the quotient. -/
theorem quotientPiece_eq_bot_of_le {i : ι} (hle : ∀ y ∈ 𝒜 i, y ∈ I) : quotientPiece 𝒜 I i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hle y hy)

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
