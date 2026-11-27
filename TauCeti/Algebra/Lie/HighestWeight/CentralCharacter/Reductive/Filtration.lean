/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basic

/-!
# Degrees under the inverse Harish-Chandra isomorphisms of a reductive Lie algebra

Let `L` be a finite-dimensional reductive Lie algebra over an algebraically closed field `K` of
characteristic zero, with Harish-Chandra isomorphisms
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}` and `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`
(`TauCeti.reductiveHarishChandraIso`, `TauCeti.reductiveHarishChandraLinearIso`). Filter the
target by the total tensor filtration of the degree filtration of `Sym(z(L))` and the degree
filtration of `S(H)` restricted to the invariants. The inverse isomorphisms send total degree `n`
into PBW degree `n` of `U(L)` (`TauCeti.reductiveHarishChandraIso_symm_mem_pbwFiltration`,
`TauCeti.reductiveHarishChandraLinearIso_symm_mem_pbwFiltration`).

On a pure tensor `a ⊗ p`, the inverse is the product of the image of `a ∈ Sym(z(L)) = U(z(L))`
and of the central element of `U([L, L])` with Harish-Chandra image `p`
(`TauCeti.reductiveHarishChandraIso_symm_tmul`); the first has PBW degree the degree of `a`
(`TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_mem_pbwFiltration_iff`), the
second the degree of `p` (`TauCeti.harishChandraIso_symm_mem_pbwFiltration`), the inclusions of
`z(L)` and `[L, L]` preserve PBW degrees, and PBW degrees add under multiplication.

## Main results

* `TauCeti.reductiveHarishChandraIso_symm_mem_pbwFiltration`: the inverse Harish-Chandra
  isomorphism of `L` sends total degree `n` into PBW degree `n`.
* `TauCeti.reductiveHarishChandraLinearIso_symm_mem_pbwFiltration`: the same for the linear
  Harish-Chandra isomorphism.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra TauCeti.Algebra TauCeti.SymmetricAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L]
  {H : LieSubalgebra K (derivedSeries K L 1)} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H (derivedSeries K L 1)]
  (b : (IsKilling.rootSystem H).Base)

local notation "U" => _root_.UniversalEnvelopingAlgebra K
local notation "SZ" => _root_.SymmetricAlgebra K (center K L)

/-- The degree filtration of `Sym(z(L))`. -/
local notation "FZ" => wordFiltration (_root_.SymmetricAlgebra.ι K (center K L))

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K L] [HasCentralRadical K L] in
/-- The product of the image in `U(L)` of an element of `Sym(z(L))` of degree at most `i` and of
the image of an element of `U([L, L])` of PBW degree at most `j` has PBW degree at most `n` when
`i + j ≤ n`. Both inverse Harish-Chandra isomorphisms take this form on pure tensors. -/
private theorem map_mul_map_mem_pbwFiltration {i j n : ℕ} (hij : i + j ≤ n) {a : SZ}
    (ha : a ∈ FZ i) {c : U (derivedSeries K L 1)}
    (hc : c ∈ pbwFiltration K (derivedSeries K L 1) j) :
    map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl c ∈ pbwFiltration K L n :=
  pbwFiltration_mono K L hij (mul_mem_pbwFiltration K L
    (map_mem_pbwFiltration K _ ((symmetricAlgebraEquiv_mem_pbwFiltration_iff K _).mpr ha))
    (map_mem_pbwFiltration K _ hc))

/-- **The inverse Harish-Chandra isomorphism of a reductive Lie algebra preserves degrees**: an
element of `Sym(z(L)) ⊗ S(H)^{W·}` of total degree at most `n` is sent to a central element of PBW
degree at most `n`. -/
theorem reductiveHarishChandraIso_symm_mem_pbwFiltration {n : ℕ}
    {t : SZ ⊗[K] dotInvariants b}
    (ht : t ∈ tensorFiltration FZ (fun j ↦ (wordFiltration
      (_root_.SymmetricAlgebra.ι K H) j).comap (dotInvariants b).val.toLinearMap) n) :
    ((reductiveHarishChandraIso b).symm t : U L) ∈ pbwFiltration K L n := by
  let e : SZ ⊗[K] dotInvariants b →ₗ[K] U L :=
    (Subalgebra.center K (U L)).val.toLinearMap ∘ₗ
      (reductiveHarishChandraIso b).symm.toAlgHom.toLinearMap
  refine (Submodule.mem_comap (f := e) (x := t)).mp (tensorFiltration_le_iff.mpr ?_ ht)
  intro i j hij a ha p hp
  simp only [Submodule.mem_comap, e, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.coe_toAlgHom, Subalgebra.coe_val]
  rw [reductiveHarishChandraIso_symm_tmul]
  exact map_mul_map_mem_pbwFiltration hij ha ((harishChandraIso_symm_mem_pbwFiltration b p).mpr hp)

/-- **The inverse linear Harish-Chandra isomorphism of a reductive Lie algebra preserves
degrees**: an element of `Sym(z(L)) ⊗ S(H)^W` of total degree at most `n` is sent to a central
element of PBW degree at most `n`. -/
theorem reductiveHarishChandraLinearIso_symm_mem_pbwFiltration {n : ℕ}
    {t : SZ ⊗[K] linearInvariants H}
    (ht : t ∈ tensorFiltration FZ (fun j ↦ (wordFiltration
      (_root_.SymmetricAlgebra.ι K H) j).comap (linearInvariants H).val.toLinearMap) n) :
    ((reductiveHarishChandraLinearIso b).symm t : U L) ∈ pbwFiltration K L n := by
  let e : SZ ⊗[K] linearInvariants H →ₗ[K] U L :=
    (Subalgebra.center K (U L)).val.toLinearMap ∘ₗ
      (reductiveHarishChandraLinearIso b).symm.toAlgHom.toLinearMap
  refine (Submodule.mem_comap (f := e) (x := t)).mp (tensorFiltration_le_iff.mpr ?_ ht)
  intro i j hij a ha q hq
  simp only [Submodule.mem_comap, e, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.coe_toAlgHom, Subalgebra.coe_val]
  rw [reductiveHarishChandraLinearIso_symm_tmul]
  exact map_mul_map_mem_pbwFiltration hij ha
    ((harishChandraLinearIso_symm_mem_pbwFiltration b q).mpr hq)

end TauCeti
