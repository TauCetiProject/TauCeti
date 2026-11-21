/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.HilbertSum

/-!
# Diagonal amplification of Hilbert-space representations

Given a Hilbert-space `⋆`-homomorphism `π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)` into the bounded operators on a
complete Hilbert space `H` over `𝕜` (`[RCLike 𝕜]`) and an index type `ι`, composing `π` with
`lp.ampliation ι 2` produces the diagonal amplified homomorphism `π.ampliation ι` on the Hilbert
direct sum `lp (fun _ : ι => H) 2` (`NonUnitalStarAlgHom.ampliation`), and `StarAlgHom.ampliation`
in the unital setting.

For complex C⋆-algebra representations, `π.ampliation ι` coincides with the constant-family
Hilbert direct sum `hilbertSum (fun _ : ι => π)` (`NonUnitalStarAlgHom.ampliation_eq_hilbertSum`),
allowing direct-sum results to transfer to amplifications. Over any nonempty index type `ι`, the
amplification preserves injectivity (`ampliation_injective_iff`) and, for complex C⋆-algebra
representations, nondegeneracy (`isNondegenerate_ampliation_iff`); nondegeneracy always passes
forward to the amplification, even for empty `ι` (`NonUnitalStarAlgHom.IsNondegenerate.ampliation`).
In particular, amplifying a separable nonzero representation by `ℕ` produces an
infinite-dimensional separable carrier on which `A` acts with the same faithfulness and
nondegeneracy.

## Main declarations

* `NonUnitalStarAlgHom.ampliation`: diagonal amplification of a nonunital `⋆`-homomorphism to
  `lp (fun _ : ι => H) 2`.
* `NonUnitalStarAlgHom.ampliation_eq_hilbertSum`: identification with the constant-family
  `hilbertSum`.
* `NonUnitalStarAlgHom.ampliation_injective_iff`,
  `NonUnitalStarAlgHom.IsNondegenerate.ampliation`,
  `NonUnitalStarAlgHom.isNondegenerate_ampliation_iff`: faithfulness and nondegeneracy of the
  amplified representation.
* `StarAlgHom.ampliation`, `StarAlgHom.ampliation_injective_iff`: the unital counterpart.

## References

* J. Peterson, *Notes on Operator Algebras*, Section 4.1.
* J. Dixmier, *C*-Algebras*, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal

namespace NonUnitalStarAlgHom

section General

variable {𝕜 A H : Type*} [RCLike 𝕜]
  [NonUnitalNonAssocSemiring A] [DistribMulAction 𝕜 A] [Star A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The diagonal amplification `a ↦ ⊕_{i : ι} π a` of a Hilbert-space `⋆`-homomorphism `π` to the
Hilbert direct sum `lp (fun _ : ι => H) 2`. -/
def ampliation (π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) :
    A →⋆ₙₐ[𝕜] (lp (fun _ : ι => H) 2 →L[𝕜] lp (fun _ : ι => H) 2) :=
  (lp.ampliationStarAlgHom ι 𝕜 H).toNonUnitalStarAlgHom.comp π

/-- Evaluating the amplified representation gives the operator ampliation `lp.ampliation ι 2`. -/
@[simp]
theorem ampliation_apply (π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) (a : A) :
    π.ampliation ι a = lp.ampliation ι 2 (π a) :=
  lp.ampliationStarAlgHom_apply (π a)

/-- Over a nonempty index type, the amplified representation is injective if and only if the
original representation is injective. -/
theorem ampliation_injective_iff (π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) [Nonempty ι] :
    Function.Injective (π.ampliation ι) ↔ Function.Injective π :=
  ⟨fun h a b hab => h (by simp [hab]),
    fun h a b hab => h (lp.ampliation_injective (ι := ι) (p := 2) (by simpa using hab))⟩

end General

section Nondegenerate

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a complex C⋆-algebra representation `π`, `π.ampliation ι` coincides with the
constant-family Hilbert direct sum `hilbertSum (fun _ : ι => π)`. -/
theorem ampliation_eq_hilbertSum (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ι : Type*) :
    π.ampliation ι = hilbertSum (fun _ : ι => π) := by
  ext a x i
  simp

/-- Amplifying a nondegenerate representation produces a nondegenerate representation (for every
index type `ι`, including empty `ι`). -/
theorem IsNondegenerate.ampliation {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)
    (ι : Type*) : (π.ampliation ι).IsNondegenerate := by
  rw [ampliation_eq_hilbertSum, isNondegenerate_hilbertSum_iff]
  exact fun _ => hπ

/-- Over a nonempty index type, the amplified representation is nondegenerate if and only if the
original representation is nondegenerate. -/
theorem isNondegenerate_ampliation_iff (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ι : Type*) [Nonempty ι] :
    (π.ampliation ι).IsNondegenerate ↔ π.IsNondegenerate := by
  rw [ampliation_eq_hilbertSum, isNondegenerate_hilbertSum_iff, forall_const]

end Nondegenerate

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {𝕜 B H : Type*} [RCLike 𝕜] [Semiring B] [Algebra 𝕜 B] [Star B]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The diagonal amplification `b ↦ ⊕_{i : ι} π b` of a unital Hilbert-space `⋆`-homomorphism `π`
to the Hilbert direct sum `lp (fun _ : ι => H) 2`. -/
def ampliation (π : B →⋆ₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) :
    B →⋆ₐ[𝕜] (lp (fun _ : ι => H) 2 →L[𝕜] lp (fun _ : ι => H) 2) :=
  (lp.ampliationStarAlgHom ι 𝕜 H).comp π

/-- Evaluating the amplified unital representation gives `lp.ampliation ι 2`. -/
@[simp]
theorem ampliation_apply (π : B →⋆ₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) (b : B) :
    π.ampliation ι b = lp.ampliation ι 2 (π b) :=
  lp.ampliationStarAlgHom_apply (π b)

/-- Forgetting the unit of `StarAlgHom.ampliation` recovers `NonUnitalStarAlgHom.ampliation`. -/
@[simp]
theorem toNonUnitalStarAlgHom_ampliation (π : B →⋆ₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) :
    (π.ampliation ι).toNonUnitalStarAlgHom = π.toNonUnitalStarAlgHom.ampliation ι :=
  (rfl)

/-- Over a nonempty index type, the amplified unital representation is injective if and only if
the original representation is injective. -/
theorem ampliation_injective_iff (π : B →⋆ₐ[𝕜] (H →L[𝕜] H)) (ι : Type*) [Nonempty ι] :
    Function.Injective (π.ampliation ι) ↔ Function.Injective π :=
  π.toNonUnitalStarAlgHom.ampliation_injective_iff ι

end StarAlgHom
