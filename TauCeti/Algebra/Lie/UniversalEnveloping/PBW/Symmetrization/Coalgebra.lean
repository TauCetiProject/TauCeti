/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Map
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import TauCeti.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# PBW symmetrization preserves the coalgebra structure

The canonical symmetrization from the symmetric algebra to the enveloping
algebra preserves comultiplication and counit over every commutative rational
algebra, without a freeness hypothesis. `pbwSymmetrizationCoalgHom` bundles
these identities for use with coalgebra maps and primitive elements.

Both coalgebras have primitive generators, and symmetrization sends powers of
symmetric generators to powers of enveloping generators. Consequently the
binomial coproduct formulas agree under symmetrization.

See Dixmier, *Enveloping Algebras*, §2.4, and Petracci, *Universal
representations of Lie algebras by coderivations*, §8 (arXiv:math/0303020v1).

Adapted from [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
Modified for the Tau Ceti API.
-/

public noncomputable section

namespace TauCeti.UniversalEnvelopingAlgebra

open scoped TensorProduct

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

local notation "S" => SymmetricAlgebra R L
local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- PBW symmetrization intertwines the symmetric and enveloping coproducts,
without freeness or flatness assumptions on the Lie algebra. -/
@[simp]
theorem comul_pbwSymmetrizationMap (p : S) :
    Coalgebra.comul (R := R) (pbwSymmetrizationMap R L p) =
      TensorProduct.map (pbwSymmetrizationMap R L) (pbwSymmetrizationMap R L)
        (Coalgebra.comul p) := by
  have he : (Coalgebra.comul (R := R) : U →ₗ[R] U ⊗[R] U).comp
      (pbwSymmetrizationMap R L) =
      (TensorProduct.map (pbwSymmetrizationMap R L) (pbwSymmetrizationMap R L)).comp
        (Coalgebra.comul (R := R) : S →ₗ[R] S ⊗[R] S) := by
    apply TauCeti.SymmetricAlgebra.linearMap_ext_ι_pow R L
    intro x n
    simp only [LinearMap.comp_apply, pbwSymmetrizationMap_ι_pow]
    rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow,
      TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R L x)]
    simp only [map_sum, map_nsmul, TensorProduct.map_tmul, pbwSymmetrizationMap_ι_pow]
  exact LinearMap.congr_fun he p

/-- PBW symmetrization preserves the counit. -/
@[simp]
theorem counit_pbwSymmetrizationMap (p : S) :
    Coalgebra.counit (R := R) (pbwSymmetrizationMap R L p) = Coalgebra.counit p := by
  have he : (Coalgebra.counit (R := R) : U →ₗ[R] R).comp
      (pbwSymmetrizationMap R L) = (Coalgebra.counit (R := R) : S →ₗ[R] R) := by
    apply TauCeti.SymmetricAlgebra.linearMap_ext_ι_pow R L
    intro x n
    simp
  exact LinearMap.congr_fun he p

/-- Canonical PBW symmetrization as a coalgebra homomorphism. Its underlying
linear map is the permutation-averaging map `pbwSymmetrizationMap`. -/
def pbwSymmetrizationCoalgHom : S →ₗc[R] U where
  __ := pbwSymmetrizationMap R L
  counit_comp := LinearMap.ext (counit_pbwSymmetrizationMap R L)
  map_comp_comul := LinearMap.ext fun p => (comul_pbwSymmetrizationMap R L p).symm

/-- The bundled coalgebra map has exactly the original underlying linear map. -/
@[simp]
theorem coe_pbwSymmetrizationCoalgHom :
    (pbwSymmetrizationCoalgHom R L : S →ₗ[R] U) = pbwSymmetrizationMap R L :=
  (rfl)

/-- Evaluation of the bundled map is the original symmetrization. -/
@[simp]
theorem pbwSymmetrizationCoalgHom_apply (p : S) :
    pbwSymmetrizationCoalgHom R L p = pbwSymmetrizationMap R L p :=
  (rfl)

end TauCeti.UniversalEnvelopingAlgebra
