/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Product.Center
public import TauCeti.Algebra.WordFiltration.TensorProduct

/-!
# PBW filtrations and the enveloping algebra of a product with an abelian factor

Let `Z` be an abelian Lie algebra and `S` any Lie algebra over a commutative ring `R`. The algebra
equivalence `productEnveloping R Z S : U(Z × S) ≃ₐ[R] Sym(Z) ⊗[R] U(S)` is compatible with the
filtrations in both directions: it carries the PBW filtration of `U(Z × S)` exactly onto the total
tensor filtration `TauCeti.tensorFiltration` of the degree filtration of `Sym(Z)` (its word
filtration in the generators `SymmetricAlgebra.ι R Z`) and the PBW filtration of `U(S)`. Degree `n`
of the latter is spanned by the pure tensors `a ⊗ u` with `a` of degree at most `i`, `u` of PBW
degree at most `j` and `i + j ≤ n`.

The proof identifies `productEnveloping R Z S ∘ ι` with the generating family
`(z, s) ↦ z ⊗ 1 + 1 ⊗ s` (`productEnveloping_ι`), whose word filtration is the total tensor
filtration (`TauCeti.Algebra.wordFiltration_tensorGenerators`).

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_productEnveloping`: the image of PBW
  degree `n` is total tensor degree `n`.
* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_mem_tensorFiltration_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_symm_mem_pbwFiltration_iff`: the forward
  and inverse compatibilities, elementwise.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (Z : Type v) [LieRing Z] [LieAlgebra R Z] [IsLieAbelian Z]
variable (S : Type w) [LieRing S] [LieAlgebra R S]

local notation "US" => _root_.UniversalEnvelopingAlgebra R S
local notation "UP" => _root_.UniversalEnvelopingAlgebra R (Z × S)
local notation "T" => tensorFiltration
  (TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R Z)) (pbwFiltration R S)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On canonical generators, `productEnveloping` is the generating family
`(z, s) ↦ z ⊗ 1 + 1 ⊗ s` of `Sym(Z) ⊗[R] U(S)`. -/
theorem productEnveloping_comp_ι :
    (productEnveloping R Z S).toAlgHom.toLinearMap ∘ₗ
        (_root_.UniversalEnvelopingAlgebra.ι R : Z × S →ₗ⁅R⁆ UP).toLinearMap =
      TauCeti.Algebra.tensorGenerators (SymmetricAlgebra.ι R Z)
        (_root_.UniversalEnvelopingAlgebra.ι R : S →ₗ⁅R⁆ US).toLinearMap := by
  ext x <;> simp

/-- `productEnveloping` carries PBW degree `n` of `U(Z × S)` exactly onto total degree `n` of
`Sym(Z) ⊗[R] U(S)`, for the degree filtration of `Sym(Z)` and the PBW filtration of `U(S)`. -/
theorem map_pbwFiltration_productEnveloping (n : ℕ) :
    (pbwFiltration R (Z × S) n).map (productEnveloping R Z S).toAlgHom.toLinearMap = T n := by
  have hS : pbwFiltration R S = TauCeti.Algebra.wordFiltration
      (_root_.UniversalEnvelopingAlgebra.ι R : S →ₗ⁅R⁆ US).toLinearMap :=
    funext (pbwFiltration_def R S)
  rw [hS, ← TauCeti.Algebra.wordFiltration_tensorGenerators, pbwFiltration_def]
  refine TauCeti.Algebra.map_wordFiltration_eq _ _ _ ?_ n
  rw [Submodule.map_sup, Submodule.map_one, ← LinearMap.range_comp, productEnveloping_comp_ι]

/-- Forward compatibility: `productEnveloping` sends PBW degree `n` into total tensor degree `n`,
and an element whose image has total tensor degree `n` has PBW degree `n`. -/
theorem productEnveloping_mem_tensorFiltration_iff {n : ℕ} {x : UP} :
    productEnveloping R Z S x ∈ T n ↔ x ∈ pbwFiltration R (Z × S) n := by
  rw [← map_pbwFiltration_productEnveloping, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← (productEnveloping R Z S).injective hxy]
  · exact fun hx ↦ ⟨x, hx, rfl⟩

/-- Inverse compatibility: the inverse of `productEnveloping` sends total tensor degree `n`
into PBW degree `n`, and conversely. -/
theorem productEnveloping_symm_mem_pbwFiltration_iff {n : ℕ} {t : SymmetricAlgebra R Z ⊗[R] US} :
    (productEnveloping R Z S).symm t ∈ pbwFiltration R (Z × S) n ↔ t ∈ T n := by
  rw [← productEnveloping_mem_tensorFiltration_iff, AlgEquiv.apply_symm_apply]

end TauCeti.UniversalEnvelopingAlgebra
