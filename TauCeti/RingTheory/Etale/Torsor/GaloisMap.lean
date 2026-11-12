/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Basic
public import TauCeti.RingTheory.Invariant.IterTensorToPi

/-!
# The Galois isomorphisms of a finite étale torsor

Let `B` be a finite étale `G`-torsor over `A` (`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`). Then
`Spec B ×_{Spec A} Spec B` is the disjoint union of `|G|` copies of `Spec B`, and more generally
the `(k + 1)`-fold fibre power of `Spec B` over `Spec A` is the disjoint union of `|G|^k` copies.
This file packages these identifications as algebra isomorphisms:

* `TauCeti.Algebra.IsFiniteEtaleTorsor.galoisMap G A B : B ⊗[A] B ≃ₐ[B] (G → B)`, the Galois
  isomorphism `b ⊗ b' ↦ (g ↦ b * g • b')`;
* `TauCeti.Algebra.IsFiniteEtaleTorsor.iterGaloisMap G A B k :
  (⨂[A] _ : Fin (k + 1), B) ≃ₐ[A] ((Fin k → G) → B)`, the iterated Galois isomorphism
  `b₀ ⊗ b₁ ⊗ ⋯ ⊗ bₖ ↦ ((gᵢ)ᵢ ↦ b₀ * ∏ i, gᵢ • bᵢ₊₁)`.

The cases `k = 0, 1, 2` of the iterated isomorphism describe the cover, its fibre square and its
fibre cube, the rings on which descent data along a torsor live. Each group coordinate is measured
from the zeroth tensor factor (vertex coordinates): on spectra the copy indexed by
`(g₀, …, gₖ₋₁)` consists of the points `(x, g₀⁻¹ • x, …, gₖ₋₁⁻¹ • x)`.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, §1.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3 and the proof of Proposition 15.4.
-/

public section

open TensorProduct PiTensorProduct

namespace TauCeti.Algebra.IsFiniteEtaleTorsor

variable (G A B : Type*) [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B] [h : IsFiniteEtaleTorsor G A B]

/-- The Galois isomorphism `B ⊗[A] B ≃ₐ[B] (G → B)`, `b ⊗ b' ↦ (g ↦ b * g • b')`, of a finite
étale `G`-torsor: `Spec B ×_{Spec A} Spec B` is the disjoint union of `|G|` copies of `Spec B`. -/
noncomputable def galoisMap : B ⊗[A] B ≃ₐ[B] (G → B) :=
  AlgEquiv.ofBijective _ h.bijective_tensorToPi

variable {G A B}

/-- The underlying map of `galoisMap` is the Galois map `TauCeti.MulSemiringAction.tensorToPi`. -/
theorem coe_galoisMap : ⇑(galoisMap G A B) = MulSemiringAction.tensorToPi A B G := (rfl)

@[simp]
theorem galoisMap_tmul (b b' : B) (g : G) : galoisMap G A B (b ⊗ₜ b') g = b * g • b' := by
  simp [coe_galoisMap]

variable (G A B) in
/-- The iterated Galois isomorphism `B^{⊗(k+1)} ≃ₐ[A] (G^k → B)` of a finite étale `G`-torsor,
`b₀ ⊗ b₁ ⊗ ⋯ ⊗ bₖ ↦ ((gᵢ)ᵢ ↦ b₀ * ∏ i, gᵢ • bᵢ₊₁)`: the `(k + 1)`-fold fibre power of
`Spec B` over `Spec A` is the disjoint union of `|G|^k` copies of `Spec B`. -/
noncomputable def iterGaloisMap (k : ℕ) : (⨂[A] _ : Fin (k + 1), B) ≃ₐ[A] ((Fin k → G) → B) :=
  AlgEquiv.ofBijective _ (MulSemiringAction.iterTensorToPi_bijective h.bijective_tensorToPi k)

/-- The underlying map of `iterGaloisMap` is `TauCeti.MulSemiringAction.iterTensorToPi`. -/
theorem coe_iterGaloisMap (k : ℕ) :
    ⇑(iterGaloisMap G A B k) = MulSemiringAction.iterTensorToPi A B G k := (rfl)

/-- The iterated Galois isomorphism on a pure tensor `b₀ ⊗ b₁ ⊗ ⋯ ⊗ bₖ`. -/
@[simp]
theorem iterGaloisMap_tprod {k : ℕ} (b : Fin (k + 1) → B) (g : Fin k → G) :
    iterGaloisMap G A B k (tprod A b) g = b 0 * ∏ i, g i • b i.succ := by
  simp [coe_iterGaloisMap]

end TauCeti.Algebra.IsFiniteEtaleTorsor
