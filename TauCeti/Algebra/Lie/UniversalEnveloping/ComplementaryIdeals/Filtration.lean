/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.ComplementaryIdeals
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.Product.Filtration

/-!
# PBW filtrations and the enveloping algebra of complementary ideals

Let `I` and `J` be complementary ideals of a Lie algebra `L` over a commutative ring `R`, with `I`
abelian. The algebra equivalence `envelopingEquivOfIsCompl R I J h : U(L) ≃ₐ[R] Sym(I) ⊗[R] U(J)`
is compatible with the filtrations in both directions: it carries the PBW filtration of `U(L)`
exactly onto the total tensor filtration `TauCeti.tensorFiltration` of the degree filtration of
`Sym(I)` (its word filtration in the generators `SymmetricAlgebra.ι R I`) and the PBW filtration of
`U(J)`. It is the map induced by the Lie algebra equivalence `L ≃ I × J`, which preserves PBW
degrees (`TauCeti.UniversalEnvelopingAlgebra.mapEquiv_pbwFiltration`), followed by
`productEnveloping`, whose compatibility is
`TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_productEnveloping`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_envelopingEquivOfIsCompl`: the image of
  PBW degree `n` is total tensor degree `n`.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_mem_tensorFiltration_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_symm_mem_pbwFiltration_iff`: the
  forward and inverse compatibilities, elementwise.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I J : LieIdeal R L) (h : IsCompl I J) [IsLieAbelian I]

local notation "UL" => _root_.UniversalEnvelopingAlgebra R L
local notation "UJ" => _root_.UniversalEnvelopingAlgebra R J
local notation "T" => tensorFiltration
  (TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R I)) (pbwFiltration R J)

/-- `envelopingEquivOfIsCompl` carries PBW degree `n` of `U(L)` exactly onto total degree `n` of
`Sym(I) ⊗[R] U(J)`, for the degree filtration of `Sym(I)` and the PBW filtration of `U(J)`. -/
theorem map_pbwFiltration_envelopingEquivOfIsCompl (n : ℕ) :
    (pbwFiltration R L n).map (envelopingEquivOfIsCompl R I J h).toAlgHom.toLinearMap = T n := by
  have he : (envelopingEquivOfIsCompl R I J h).toAlgHom.toLinearMap =
      (productEnveloping R I J).toAlgHom.toLinearMap ∘ₗ
        (mapEquiv R (LieIdeal.prodEquivOfIsCompl I J h).symm).toLinearMap := by
    simp only [envelopingEquivOfIsCompl_def, AlgEquiv.toAlgHom_toLinearMap,
      AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.trans_toLinearMap]
  rw [he, Submodule.map_comp, mapEquiv_pbwFiltration, map_pbwFiltration_productEnveloping]

/-- Forward compatibility: `envelopingEquivOfIsCompl` sends PBW degree `n` into total tensor
degree `n`, and an element whose image has total tensor degree `n` has PBW degree `n`. -/
@[simp]
theorem envelopingEquivOfIsCompl_mem_tensorFiltration_iff {n : ℕ} {x : UL} :
    envelopingEquivOfIsCompl R I J h x ∈ T n ↔ x ∈ pbwFiltration R L n := by
  rw [← map_pbwFiltration_envelopingEquivOfIsCompl R I J h, AlgEquiv.toAlgHom_toLinearMap,
    Submodule.mem_map_equiv]
  simp

/-- Inverse compatibility: the inverse of `envelopingEquivOfIsCompl` sends total tensor degree `n`
into PBW degree `n`, and conversely. -/
@[simp]
theorem envelopingEquivOfIsCompl_symm_mem_pbwFiltration_iff {n : ℕ}
    {t : SymmetricAlgebra R I ⊗[R] UJ} :
    (envelopingEquivOfIsCompl R I J h).symm t ∈ pbwFiltration R L n ↔ t ∈ T n := by
  rw [← envelopingEquivOfIsCompl_mem_tensorFiltration_iff R I J h, AlgEquiv.apply_symm_apply]

end TauCeti.UniversalEnvelopingAlgebra
