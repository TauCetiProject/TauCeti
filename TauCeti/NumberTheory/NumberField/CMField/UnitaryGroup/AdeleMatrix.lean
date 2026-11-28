/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Prod
import TauCeti.Topology.Instances.Matrix.Prod

/-!
# The adelic unitary group in the adelic matrices

Let `E` be a CM field with infinite adeles `E_∞`, finite adeles `𝔸_f` and adeles
`𝔸 = E_∞ × 𝔸_f`, let `s` be a sign vector, and let `G(s) = G_∞(s) × G_f` be the adelic unitary
group, where `G_∞(s) = U(diag s)(E_∞)` and `G_f = U(1_n)(𝔸_f)`. This file proves that
`g ↦` (the adelic matrix of `g`) is a closed embedding of `G(s)` in `M_n(𝔸)`.

This identifies the topology of `G(s)` with the subspace topology of the matrices. Each factor
`GL_n(R)` of `GL_n(E_∞) × GL_n(𝔸_f)` gets its topology from the pair of matrices `(g, g⁻¹)` in
`M_n(R) × M_n(R)`, and on the unitary subgroups the inverse matrix depends continuously on the
forward matrix, so only `g` itself matters.

## Main definitions

* `TauCeti.adelicUnitaryGroup.toAdeleMatrix E s`: the adelic matrix `G(s) →* M_n(𝔸)`.

## Main results

* `TauCeti.adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix`: the adelic matrix is a closed
  embedding.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.

## Attribution

The closed embedding statement is that of `New.G.isClosedEmbedding_adeleMatrix` in
`src/Lib/Adelic/Unitary/WeakApproximation.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC); the formalization here is independent of that code.
-/

public section
noncomputable section

open Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The **adelic matrix** of an element `g = (g_∞, g_f)` of the adelic unitary group `G(s)`: the
matrix in `M_n(𝔸)`, `𝔸 = E_∞ × 𝔸_f`, whose entry `(i, j)` is the adele `(g_∞ i j, g_f i j)`, that
is the underlying matrix of the element of `GL_n(𝔸)` with components `g_∞` and `g_f`
(`TauCeti.prodEquivGL`). It is multiplicative, and a closed embedding
(`isClosedEmbedding_toAdeleMatrix`). -/
def adelicUnitaryGroup.toAdeleMatrix (s : ι → ℤˣ) : adelicUnitaryGroup E s →* Matrix ι ι 𝔸[E] :=
  ((Units.coeHom _).comp (prodEquivGL ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm.toMonoidHom).comp
    (adelicUnitaryGroup E s).subtype

variable {E}

/-- The archimedean component of the entry `(i, j)` of the adelic matrix of `g` is `g_∞ i j`. -/
@[simp]
theorem adelicUnitaryGroup.fst_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).1 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 : Matrix ι ι (InfiniteAdeleRing E)) i j := by
  change (((prodEquivGL ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm g :
    Matrix ι ι (InfiniteAdeleRing E × 𝔸ᶠ[E])) i j).1 = _
  rw [coe_prodEquivGL_symm_apply, Matrix.of_apply]

/-- The finite component of the entry `(i, j)` of the adelic matrix of `g` is `g_f i j`. -/
@[simp]
theorem adelicUnitaryGroup.snd_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).2 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 : Matrix ι ι 𝔸ᶠ[E]) i j := by
  change (((prodEquivGL ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm g :
    Matrix ι ι (InfiniteAdeleRing E × 𝔸ᶠ[E])) i j).2 = _
  rw [coe_prodEquivGL_symm_apply, Matrix.of_apply]

/-- **`G(s)` is a closed subset of the adelic matrices**: the adelic matrix
`G(s) → M_n(𝔸)` is a closed embedding. The unitary groups `G_∞(s)` and `G_f` are closed subsets
of the matrices over `E_∞` and over `𝔸_f` with the subspace topology
(`Matrix.unitaryGroupOf.isClosedEmbedding_val`), and `M_n(𝔸)` is homeomorphic to
`M_n(E_∞) × M_n(𝔸_f)` (`Matrix.prodHomeomorph`). -/
theorem adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix (s : ι → ℤˣ) :
    IsClosedEmbedding (adelicUnitaryGroup.toAdeleMatrix E s) := by
  have hf := unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E])) isUnit_one
  rw [unitaryGroupOf_one] at hf
  -- Through `G(s) ≃ₜ G_∞(s) × G_f` and `M_n(𝔸) ≃ₜ M_n(E_∞) × M_n(𝔸_f)`, the adelic matrix is the
  -- pair of the underlying matrices of the two components.
  have h : ⇑(adelicUnitaryGroup.toAdeleMatrix E s) =
      (Matrix.prodHomeomorph ι ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm ∘
        Prod.map (fun g : infiniteAdelicUnitaryGroup E s ↦
            ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)))
          (fun g : finiteAdelicUnitaryGroup E ι ↦ ((g : GL ι 𝔸ᶠ[E]) : Matrix ι ι 𝔸ᶠ[E])) ∘
        Homeomorph.Set.prod (infiniteAdelicUnitaryGroup E s : Set (GL ι (InfiniteAdeleRing E)))
          (finiteAdelicUnitaryGroup E ι : Set (GL ι 𝔸ᶠ[E])) := by
    funext g
    refine (Matrix.prodHomeomorph _ _ _ _).eq_symm_apply.2 ?_
    rw [Matrix.prodHomeomorph_apply]
    refine Prod.ext (Matrix.ext fun i j ↦ ?_) (Matrix.ext fun i j ↦ ?_)
    · exact adelicUnitaryGroup.fst_toAdeleMatrix_apply g i j
    · exact adelicUnitaryGroup.snd_toAdeleMatrix_apply g i j
  rw [h]
  exact (Matrix.prodHomeomorph _ _ _ _).symm.isClosedEmbedding.comp
    (((unitaryGroupOf.isClosedEmbedding_val (isUnit_diagonal_intCast_units s)).prodMap hf).comp
      (Homeomorph.Set.prod _ _).isClosedEmbedding)

/-- The adelic matrix `G(s) → M_n(𝔸)` is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_toAdeleMatrix (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.toAdeleMatrix E s) :=
  (adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix s).continuous

end TauCeti
