/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basic
public import TauCeti.Algebra.Lie.Reductive.Enveloping.Filtration
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.LinearAlgebra.SymmetricAlgebra.HomogeneousBasis
import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basis

/-!
# Degrees under the Harish-Chandra isomorphisms of a reductive Lie algebra

Let `L` be a finite-dimensional reductive Lie algebra over an algebraically closed field `K` of
characteristic zero, with Harish-Chandra isomorphisms
`Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^{W·}` and `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ S(H)^W`
(`TauCeti.reductiveHarishChandraIso`, `TauCeti.reductiveHarishChandraLinearIso`). Filter the
target by the total tensor filtration of the degree filtration of `Sym(z(L))` and the degree
filtration of `S(H)` restricted to the invariants. The inverse isomorphisms send total degree `n`
into PBW degree `n` of `U(L)` (`TauCeti.reductiveHarishChandraIso_symm_mem_pbwFiltration`,
`TauCeti.reductiveHarishChandraLinearIso_symm_mem_pbwFiltration`), and conversely a central element
of PBW degree `n` has image of total degree `n`
(`TauCeti.reductiveHarishChandraIso_mem_tensorFiltration_iff`,
`TauCeti.reductiveHarishChandraLinearIso_mem_tensorFiltration_iff`): the isomorphisms identify the
two filtrations.

On a pure tensor `a ⊗ p`, the inverse is the product of the image of `a ∈ Sym(z(L)) = U(z(L))`
and of the central element of `U([L, L])` with Harish-Chandra image `p`
(`TauCeti.reductiveHarishChandraIso_symm_tmul`); the first has PBW degree the degree of `a`
(`TauCeti.UniversalEnvelopingAlgebra.symmetricAlgebraEquiv_mem_pbwFiltration_iff`), the
second the degree of `p` (`TauCeti.harishChandraIso_symm_mem_pbwFiltration`), the inclusions of
`z(L)` and `[L, L]` preserve PBW degrees, and PBW degrees add under multiplication.

For the forward direction, `U(L) ≅ Sym(z(L)) ⊗ U([L, L])` identifies PBW degree `n` with total
degree `n` (`TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_mem_tensorFiltration_iff`), and
the total filtration is strict along the inclusion `Z(U([L, L])) ⊆ U([L, L])` of the second factor
(`TauCeti.lTensor_mem_tensorFiltration_iff_of_basis`, for the monomial basis of `Sym(z(L))`
induced by a basis of `z(L)`, which is adapted to the degree filtration by
`TauCeti.SymmetricAlgebra.wordFiltration_eq_span_basis_image`): so the centre comparison sends PBW
degree `n` to total degree `n` for the PBW filtration restricted to `Z(U([L, L]))`
(`TauCeti.reductiveCenterEquiv_mem_tensorFiltration_iff`), and the Harish-Chandra isomorphism of
`[L, L]` preserves degrees.

## Main results

* `TauCeti.reductiveHarishChandraIso_symm_mem_pbwFiltration`: the inverse Harish-Chandra
  isomorphism of `L` sends total degree `n` into PBW degree `n`.
* `TauCeti.reductiveHarishChandraLinearIso_symm_mem_pbwFiltration`: the same for the linear
  Harish-Chandra isomorphism.
* `TauCeti.reductiveCenterEquiv_mem_tensorFiltration_iff`: the centre comparison identifies PBW
  degree with total degree.
* `TauCeti.reductiveHarishChandraIso_mem_tensorFiltration_iff`,
  `TauCeti.reductiveHarishChandraLinearIso_mem_tensorFiltration_iff`: the Harish-Chandra
  isomorphisms identify PBW degree with total degree.
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

omit [IsAlgClosed K] in
/-- **The centre comparison identifies PBW degree with total degree**: a central element of `U(L)`
has PBW degree at most `n` exactly when its image in `Sym(z(L)) ⊗ Z(U([L, L]))` has total degree
at most `n`, for the degree filtration of `Sym(z(L))` and the PBW filtration of `U([L, L])`
restricted to its centre. -/
theorem reductiveCenterEquiv_mem_tensorFiltration_iff {n : ℕ}
    {z : Subalgebra.center K (U L)} :
    reductiveCenterEquiv K L z ∈ tensorFiltration FZ (fun j ↦
      (pbwFiltration K (derivedSeries K L 1) j).comap
        (Subalgebra.center K (U (derivedSeries K L 1))).val.toLinearMap) n ↔
      (z : U L) ∈ pbwFiltration K L n := by
  rw [← reductiveEnveloping_mem_tensorFiltration_iff, ← reductiveCenterEquiv_inclusion]
  exact lTensor_mem_tensorFiltration_iff_of_basis
    (Module.Basis.ofVectorSpace K (center K L)).symmetricAlgebra Finsupp.degree
    (wordFiltration_eq_span_basis_image
      (Module.Basis.ofVectorSpace K (center K L)).symmetricAlgebra_mem_homogeneousSubmodule)
    (pbwFiltration_mono K _) (f := (Subalgebra.center K (U (derivedSeries K L 1))).val.toLinearMap)
    Subtype.val_injective |>.symm

omit [IsAlgClosed K] in
/-- An algebra isomorphism out of `Z(U([L, L]))` whose inverse detects `G j` by PBW degree `j`,
applied to the second factor of the centre comparison, sends a central element of PBW degree `n`
to total degree `n`. Both Harish-Chandra isomorphisms of `L` take this form. -/
private theorem congr_reductiveCenterEquiv_mem_tensorFiltration {A : Type*} [Semiring A]
    [Algebra K A] (e : Subalgebra.center K (U (derivedSeries K L 1)) ≃ₐ[K] A)
    {G : ℕ → Submodule K A}
    (he : ∀ j (p : A),
      ((e.symm p : Subalgebra.center K (U (derivedSeries K L 1))) : U (derivedSeries K L 1)) ∈
        pbwFiltration K (derivedSeries K L 1) j → p ∈ G j)
    {n : ℕ} {z : Subalgebra.center K (U L)} (hz : (z : U L) ∈ pbwFiltration K L n) :
    Algebra.TensorProduct.congr (AlgEquiv.refl : SZ ≃ₐ[K] SZ) e (reductiveCenterEquiv K L z) ∈
      tensorFiltration FZ G n :=
  tensorFiltration_le_comap_map (f := LinearMap.id) (g := e.toLinearMap) (fun _ ↦ le_rfl)
    (fun j c hc ↦ he j (e c) (by rwa [AlgEquiv.symm_apply_apply])) n
    (reductiveCenterEquiv_mem_tensorFiltration_iff.mpr hz)

/-- **The Harish-Chandra isomorphism of a reductive Lie algebra identifies the filtrations**: a
central element has PBW degree at most `n` exactly when its image in `Sym(z(L)) ⊗ S(H)^{W·}` has
total degree at most `n`. -/
theorem reductiveHarishChandraIso_mem_tensorFiltration_iff {n : ℕ}
    {z : Subalgebra.center K (U L)} :
    reductiveHarishChandraIso b z ∈ tensorFiltration FZ (fun j ↦ (wordFiltration
      (_root_.SymmetricAlgebra.ι K H) j).comap (dotInvariants b).val.toLinearMap) n ↔
      (z : U L) ∈ pbwFiltration K L n := by
  refine ⟨fun h ↦ by simpa using reductiveHarishChandraIso_symm_mem_pbwFiltration b h,
    fun h ↦ ?_⟩
  rw [reductiveHarishChandraIso_apply]
  exact congr_reductiveCenterEquiv_mem_tensorFiltration _
    (fun _ p ↦ (harishChandraIso_symm_mem_pbwFiltration b p).mp) h

/-- **The linear Harish-Chandra isomorphism of a reductive Lie algebra identifies the
filtrations**: a central element has PBW degree at most `n` exactly when its image in
`Sym(z(L)) ⊗ S(H)^W` has total degree at most `n`. -/
theorem reductiveHarishChandraLinearIso_mem_tensorFiltration_iff {n : ℕ}
    {z : Subalgebra.center K (U L)} :
    reductiveHarishChandraLinearIso b z ∈ tensorFiltration FZ (fun j ↦ (wordFiltration
      (_root_.SymmetricAlgebra.ι K H) j).comap (linearInvariants H).val.toLinearMap) n ↔
      (z : U L) ∈ pbwFiltration K L n := by
  refine ⟨fun h ↦ by simpa using reductiveHarishChandraLinearIso_symm_mem_pbwFiltration b h,
    fun h ↦ ?_⟩
  rw [reductiveHarishChandraLinearIso_apply]
  exact congr_reductiveCenterEquiv_mem_tensorFiltration _
    (fun _ p ↦ (harishChandraLinearIso_symm_mem_pbwFiltration b p).mp) h

end TauCeti
