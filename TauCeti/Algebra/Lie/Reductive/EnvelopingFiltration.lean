/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.EnvelopingCenter
public import TauCeti.Algebra.Lie.UniversalEnveloping.ProductFiltration

/-!
# The PBW filtration of the enveloping algebra of a reductive Lie algebra

For a finite-dimensional reductive Lie algebra `L` over a field of characteristic zero, the
algebra equivalence `reductiveEnveloping : U(L) ≃ Sym(z(L)) ⊗ U([L, L])` matches the PBW
filtration of `U(L)` with the total tensor filtration `productFiltration` of the degree filtration
of `Sym(z(L))` and the PBW filtration of `U([L, L])`, in both directions. The equivalence of Lie
algebras `L ≃ z(L) × [L, L]` preserves PBW degree exactly
(`TauCeti.UniversalEnvelopingAlgebra.mapEquiv_mem_pbwFiltration_iff`), and `productEnveloping` is
filtered (`TauCeti.UniversalEnvelopingAlgebra.productEnveloping_mem_tensorFiltration_iff`).

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_mem_productFiltration_iff`: the forward
  compatibility.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_symm_mem_pbwFiltration_iff`: the inverse
  compatibility.
* `TauCeti.UniversalEnvelopingAlgebra.map_reductiveEnveloping_pbwFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.map_reductiveEnveloping_symm_productFiltration`: the images
  of the filtration steps.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnvelopingFiltration`: the induced linear
  equivalences between the filtration steps.
-/

public section

open scoped TensorProduct

open LieAlgebra

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

section MapEquiv

variable {R : Type u} {L : Type v} {M : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- The map induced by a Lie algebra equivalence preserves PBW degree exactly. -/
@[simp]
theorem mapEquiv_mem_pbwFiltration_iff (e : L ≃ₗ⁅R⁆ M) {k : ℕ}
    {x : _root_.UniversalEnvelopingAlgebra R L} :
    mapEquiv R e x ∈ pbwFiltration R M k ↔ x ∈ pbwFiltration R L k := by
  rw [← mapEquiv_pbwFiltration R e k, ← AlgEquiv.toLinearEquiv_toLinearMap,
    Submodule.mem_map_equiv, AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_apply_apply]

end MapEquiv

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)

/-- **`reductiveEnveloping` is filtered**: an element of `U(L)` has PBW degree at most `n`
exactly when its image in `Sym(z(L)) ⊗ U([L, L])` has total tensor degree at most `n`. -/
@[simp]
theorem reductiveEnveloping_mem_productFiltration_iff {n : ℕ} {x : UL} :
    reductiveEnveloping K L x ∈ productFiltration K (center K L) (derivedSeries K L 1) n ↔
      x ∈ pbwFiltration K L n := by
  rw [reductiveEnveloping_def, AlgEquiv.trans_apply,
    productEnveloping_mem_tensorFiltration_iff, mapEquiv_mem_pbwFiltration_iff]

/-- **The inverse of `reductiveEnveloping` is filtered**: a tensor in `Sym(z(L)) ⊗ U([L, L])` has
total degree at most `n` exactly when its image in `U(L)` has PBW degree at most `n`. -/
@[simp]
theorem reductiveEnveloping_symm_mem_pbwFiltration_iff {n : ℕ} {t : SZ ⊗[K] UD} :
    (reductiveEnveloping K L).symm t ∈ pbwFiltration K L n ↔
      t ∈ productFiltration K (center K L) (derivedSeries K L 1) n := by
  rw [← reductiveEnveloping_mem_productFiltration_iff, AlgEquiv.apply_symm_apply]

/-- `reductiveEnveloping` maps each PBW filtration step onto the corresponding total tensor
filtration step. -/
theorem map_reductiveEnveloping_pbwFiltration (n : ℕ) :
    (pbwFiltration K L n).map (reductiveEnveloping K L).toLinearMap =
      productFiltration K (center K L) (derivedSeries K L 1) n := by
  ext t
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, Submodule.mem_map_equiv,
    AlgEquiv.coe_symm_toLinearEquiv, reductiveEnveloping_symm_mem_pbwFiltration_iff]

/-- The inverse of `reductiveEnveloping` maps each total tensor filtration step onto the
corresponding PBW filtration step. -/
theorem map_reductiveEnveloping_symm_productFiltration (n : ℕ) :
    (productFiltration K (center K L) (derivedSeries K L 1) n).map
        (reductiveEnveloping K L).symm.toLinearMap =
      pbwFiltration K L n := by
  ext x
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, Submodule.mem_map_equiv,
    AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_symm,
    reductiveEnveloping_mem_productFiltration_iff]

/-- The linear equivalence between PBW filtration step `n` of `U(L)` and total tensor filtration
step `n` of `Sym(z(L)) ⊗ U([L, L])` induced by `reductiveEnveloping`. -/
noncomputable def reductiveEnvelopingFiltration (n : ℕ) :
    pbwFiltration K L n ≃ₗ[K] productFiltration K (center K L) (derivedSeries K L 1) n :=
  (reductiveEnveloping K L).toLinearEquiv.ofSubmodules _ _
    (map_reductiveEnveloping_pbwFiltration K L n)

/-- `reductiveEnvelopingFiltration` acts by `reductiveEnveloping`. -/
@[simp]
theorem coe_reductiveEnvelopingFiltration_apply (n : ℕ) (x : pbwFiltration K L n) :
    (reductiveEnvelopingFiltration K L n x : SZ ⊗[K] UD) = reductiveEnveloping K L x := by
  rw [reductiveEnvelopingFiltration, LinearEquiv.ofSubmodules_apply, AlgEquiv.coe_toLinearEquiv]

/-- The inverse of `reductiveEnvelopingFiltration` acts by the inverse of `reductiveEnveloping`. -/
@[simp]
theorem coe_reductiveEnvelopingFiltration_symm_apply (n : ℕ)
    (t : productFiltration K (center K L) (derivedSeries K L 1) n) :
    ((reductiveEnvelopingFiltration K L n).symm t : UL) = (reductiveEnveloping K L).symm t := by
  rw [reductiveEnvelopingFiltration, LinearEquiv.ofSubmodules_symm_apply,
    AlgEquiv.coe_symm_toLinearEquiv]

end TauCeti.UniversalEnvelopingAlgebra
