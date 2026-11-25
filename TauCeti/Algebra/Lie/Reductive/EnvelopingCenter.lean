/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.ComplementaryIdeals

/-!
# The enveloping algebra and its center for a reductive Lie algebra

For a finite-dimensional reductive Lie algebra `L` over a field of characteristic zero, the centre
and the derived ideal are complementary (`TauCeti.isCompl_center_derivedSeries`), and the
complementary-ideal decompositions `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl`
and `TauCeti.UniversalEnvelopingAlgebra.centerEquivOfIsCompl` specialize to

`U(L) ≃ Sym(z(L)) ⊗ U([L, L])`  (`TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping`),

`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`  (`TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv`).

The latter, followed by `id ⊗ (Z(U([L, L])) ↪ U([L, L]))`, is `reductiveEnveloping` on the
underlying central element. Both are built from universal properties: no Harish-Chandra theorem is
used.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping`: `U(L) ≃ₐ[K] Sym(z(L)) ⊗ U([L, L])`.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv`:
  `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ Z(U([L, L]))`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_ι`: the value on a generator.
* `UniversalEnvelopingAlgebra.reductiveEnveloping_map_incl_center` and
  `UniversalEnvelopingAlgebra.reductiveEnveloping_map_incl_derivedSeries`: the values on the
  enveloping algebras of the centre and of the derived ideal.
* `UniversalEnvelopingAlgebra.reductiveEnveloping_symm_tmul`: the inverse on a pure tensor.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_naturality`: naturality for Lie maps
  sending the centre into the centre.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv_inclusion`: the inclusion square.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv_symm_tmul`: the pure-tensor formula.

## References

* J. Dixmier, *Enveloping Algebras*, §1.6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.1.
-/

public section

open scoped TensorProduct

open LieAlgebra

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti _root_.UniversalEnvelopingAlgebra

section Enveloping

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)

/-- The enveloping algebra of a reductive Lie algebra: `U(L) ≃ Sym(z(L)) ⊗ U([L, L])`,
`envelopingEquivOfIsCompl` for the central/derived splitting. -/
noncomputable def reductiveEnveloping : UL ≃ₐ[K] SZ ⊗[K] UD :=
  envelopingEquivOfIsCompl K (center K L) (derivedSeries K L 1) (isCompl_center_derivedSeries K L)

/-- The definition of `reductiveEnveloping`, for use outside this module. -/
theorem reductiveEnveloping_def :
    reductiveEnveloping K L =
      envelopingEquivOfIsCompl K (center K L) (derivedSeries K L 1)
        (isCompl_center_derivedSeries K L) :=
  (rfl)

/-- `reductiveEnveloping` sends a canonical generator `x` to
`ι_z(pr_z x) ⊗ 1 + 1 ⊗ ι_der(pr_der x)`. -/
theorem reductiveEnveloping_ι (x : L) :
    reductiveEnveloping K L (_root_.UniversalEnvelopingAlgebra.ι K x) =
      SymmetricAlgebra.ι K (center K L) (centerDerivedEquiv K L x).1 ⊗ₜ[K] (1 : UD) +
        (1 : SZ) ⊗ₜ[K] _root_.UniversalEnvelopingAlgebra.ι K (centerDerivedEquiv K L x).2 := by
  rw [reductiveEnveloping, envelopingEquivOfIsCompl_ι, centerDerivedEquiv_def]

/-- The `simp`-normal form of `reductiveEnveloping_ι`, stated for the canonical generators as
`simp` writes them: `ι K x` unfolds to `mkAlgHom K L (TensorAlgebra.ι K x)`. -/
@[simp]
theorem reductiveEnveloping_ι' (x : L) :
    reductiveEnveloping K L (_root_.UniversalEnvelopingAlgebra.mkAlgHom K L (TensorAlgebra.ι K x)) =
      SymmetricAlgebra.ι K (center K L) (centerDerivedEquiv K L x).1 ⊗ₜ[K] (1 : UD) +
        (1 : SZ) ⊗ₜ[K] _root_.UniversalEnvelopingAlgebra.mkAlgHom K (derivedSeries K L 1)
          (TensorAlgebra.ι K (centerDerivedEquiv K L x).2) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using reductiveEnveloping_ι K L x

/-- On the inclusion of the centre, `reductiveEnveloping` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.reductiveEnveloping_map_incl_center
    (a : _root_.UniversalEnvelopingAlgebra K (center K L)) :
    reductiveEnveloping K L (map K (center K L).incl a) =
      (symmetricAlgebraEquiv K (center K L)).symm a ⊗ₜ[K] (1 : UD) :=
  envelopingEquivOfIsCompl_map_incl_left _ _ _ _ a

/-- On the inclusion of the derived ideal, `reductiveEnveloping` is one tensored with the
element. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.reductiveEnveloping_map_incl_derivedSeries (u : UD) :
    reductiveEnveloping K L (map K (derivedSeries K L 1).incl u) = (1 : SZ) ⊗ₜ[K] u :=
  envelopingEquivOfIsCompl_map_incl_right _ _ _ _ u

/-- The inverse of `reductiveEnveloping` sends a pure tensor `a ⊗ u` to the product of the images
of `a` and `u` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.reductiveEnveloping_symm_tmul (a : SZ) (u : UD) :
    (reductiveEnveloping K L).symm (a ⊗ₜ[K] u) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl u :=
  envelopingEquivOfIsCompl_symm_tmul _ _ _ _ a u

end Enveloping

section Naturality

variable {K : Type u} {L : Type v} {L' : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L] [LieRing L']
  [LieAlgebra K L'] [FiniteDimensional K L'] [HasCentralRadical K L']

/-- `reductiveEnveloping` is natural for Lie maps sending the centre into the centre: such a map
acts on `Sym(z(L))` through its restriction to the centres and on `U([L, L])` through its
restriction to the derived ideals. -/
theorem reductiveEnveloping_naturality (f : L →ₗ⁅K⁆ L')
    (hf : ∀ z ∈ center K L, f z ∈ center K L') :
    (Algebra.TensorProduct.map
        (SymmetricAlgebra.map K ((f.restrictIdeal hf : center K L →ₗ[K] center K L')))
        (map K (f.restrictIdeal fun _ ↦ f.map_mem_derivedSeries 1))).comp
        (reductiveEnveloping K L).toAlgHom =
      (reductiveEnveloping K L').toAlgHom.comp (map K f) :=
  envelopingEquivOfIsCompl_naturality _ _ f hf _

end Naturality

section Center

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)
local notation "ZD" => Subalgebra.center K UD

/-- The center of the enveloping algebra of a reductive Lie algebra:
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`, `centerEquivOfIsCompl` for the central/derived splitting.
See `reductiveCenterEquiv_inclusion` for the inclusion square. -/
noncomputable def reductiveCenterEquiv : Subalgebra.center K UL ≃ₐ[K] SZ ⊗[K] ZD :=
  centerEquivOfIsCompl K (center K L) (derivedSeries K L 1) (isCompl_center_derivedSeries K L)

/-- The definition of `reductiveCenterEquiv`, for use outside this module. -/
theorem reductiveCenterEquiv_def :
    reductiveCenterEquiv K L =
      centerEquivOfIsCompl K (center K L) (derivedSeries K L 1)
        (isCompl_center_derivedSeries K L) :=
  (rfl)

/-- The inclusion square of `reductiveCenterEquiv`: followed by `id ⊗ val`, it is
`reductiveEnveloping` on the underlying central element. -/
@[simp]
theorem reductiveCenterEquiv_inclusion (z : Subalgebra.center K UL) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (ZD).val (reductiveCenterEquiv K L z) =
      reductiveEnveloping K L (z : UL) :=
  centerEquivOfIsCompl_inclusion _ _ _ _ z

/-- The inverse of `reductiveCenterEquiv` on a pure tensor `a ⊗ c` with `c` central is the product
of the images of `a` and `c` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem reductiveCenterEquiv_symm_tmul (a : SZ) (c : ZD) :
    ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c) : UL) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl (c : UD) :=
  centerEquivOfIsCompl_symm_tmul _ _ _ _ a c

end Center

end TauCeti.UniversalEnvelopingAlgebra
