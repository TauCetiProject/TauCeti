/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Algebra.Group.PowerClassGroup.Basic
public import TauCeti.FieldTheory.GaloisCohomology.Cyclic
public import TauCeti.FieldTheory.GaloisCohomology.Solvable
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Solvable
public import TauCeti.NumberTheory.LocalField.UnitFiltration.HerbrandQuotient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.Kummer.Cyclic

/-!
# The local second-cohomology bound

For a cyclic extension `L/K` of nonarchimedean local fields, Hilbert 90 and two-periodicity
identify the order of `H²(Gal(L/K), Lˣ)` with the Herbrand quotient of `Lˣ`, and the equivariant
valuation sequence gives `h(Lˣ) = [L : K] · h(U_L)`. Since the valuation-zero units have Herbrand
quotient `h(U_L) = 1` (`TauCeti.TateCohomology.herbrandQuotient_unitFiltration_zero`), this gives

`#H²(Gal(L/K), Lˣ) = [L : K]`.

Since two-periodicity also identifies `H²(Gal(L/K), Lˣ)` with the norm quotient
`Kˣ / N_{L/K}(Lˣ)` (`TauCeti.cyclicNormQuotientEquiv`), this is the cyclic norm index
`[Kˣ : N_{L/K}(Lˣ)] = [L : K]`. It is a Herbrand-quotient computation and uses no reciprocity. In
particular, when `K` contains a primitive `n`-th root of unity and a finite extension `L/K`
containing an `n`-th root of `b ∈ Kˣ` has full norm group `N_{L/K}(Lˣ) = Kˣ`, the cyclic radical
subextension `K(ⁿ√b)/K` also has norm index `1`, hence degree `1`, so `b ∈ (Kˣ)ⁿ`
(`IsPrimitiveRoot.mem_powerSubgroup_of_normGroup_eq_top`).

For a general finite Galois extension, the local Galois group is solvable, and the
field-theoretic solvable reduction propagates the prime-degree cyclic case to the bound
`#H²(Gal(L/K), Lˣ) ∣ [L : K]`. This bounds the relative Brauer group of a finite Galois layer;
compared with the unramified layer of the same degree, it shows that every local Brauer class is
split by an unramified extension.

## Main results

* `TauCeti.natCard_H2_units_eq_finrank`: `#H²(Gal(L/K), Lˣ) = [L : K]` for cyclic `L/K`.
* `TauCeti.index_normGroup_of_isCyclic`: `[Kˣ : N_{L/K}(Lˣ)] = [L : K]` for cyclic `L/K`.
* `IsPrimitiveRoot.mem_powerSubgroup_of_normGroup_eq_top`: if `K` contains a primitive `n`-th root
  of unity and a finite extension `L/K` containing an `n`-th root of `b ∈ Kˣ` has
  `normGroup K L = ⊤`, then `b ∈ (Kˣ)ⁿ`.
* `TauCeti.natCard_H2_units_dvd_finrank`: `#H²(Gal(L/K), Lˣ) ∣ [L : K]` for every finite Galois
  `L/K`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter IX,
  §3, Chapter XIII, §1, and Chapter XIV, §2.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §1.
-/

public noncomputable section

open IntermediateField Module ValuativeRel

namespace TauCeti

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- **The local `H²` of a cyclic extension.** For a cyclic extension `L/K` of nonarchimedean
local fields, `H²(Gal(L/K), Lˣ)` has order `[L : K]`. -/
theorem natCard_H2_units_eq_finrank [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) = finrank K L := by
  have h := natCard_H2_units_eq_herbrandQuotient (K := K) (L := L)
  rw [herbrandQuotient_units_eq_finrank] at h
  exact_mod_cast h

/-- **The cyclic norm index.** For a cyclic extension `L/K` of nonarchimedean local fields, the
norm group `N_{L/K}(Lˣ)` has index `[L : K]` in `Kˣ`. -/
theorem index_normGroup_of_isCyclic [IsCyclic (L ≃ₐ[K] L)] :
    (normGroup K L).index = finrank K L := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [← natCard_H2_units_eq_finrank K L, Subgroup.index]
  exact Nat.card_congr (Additive.ofMul.trans (cyclicNormQuotientEquiv hg).toEquiv)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- **The local `H²` bound.** For a finite Galois extension `L/K` of nonarchimedean local fields,
the order of `H²(Gal(L/K), Lˣ)` divides `[L : K]`. The statement involves only the field structure
of `L` (a finite Galois extension of `K`); no valuation or topology on `L` is assumed. -/
theorem natCard_H2_units_dvd_finrank :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) ∣
      finrank K L := by
  let _ := algebraicExtensionValuativeRel K L
  let _ := algebraicExtensionNormedFieldTopology K L
  have := finiteExtension_isNonarchimedeanLocalField K L
  have := algebraicExtension_valuativeExtension K L
  refine natCard_groupCohomology_two_units_dvd_finrank (K := K) (L := L) fun E F _ hp ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K L E
  let _ := finiteIntermediateFieldTopology K L E
  have := finiteIntermediateField_isNonarchimedeanLocalField K L E
  have := finiteIntermediateField_valuativeExtension K L E
  let _ := finiteIntermediateFieldValuativeRel E L F
  let _ := finiteIntermediateFieldTopology E L F
  have := finiteIntermediateField_isNonarchimedeanLocalField E L F
  have := finiteIntermediateField_valuativeExtension E L F
  let _ : Fact (finrank E F).Prime := ⟨hp⟩
  let _ : IsCyclic (F ≃ₐ[E] F) :=
    isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank E F)
  rw [natCard_H2_units_eq_finrank E F]

end TauCeti

namespace IsPrimitiveRoot

/-- **Serre's radical norm-top criterion.** Let `K` be a nonarchimedean local field containing a
primitive `n`-th root of unity `ζ`. If a finite extension `L/K` contains an `n`-th root `s` of
`b ∈ Kˣ` (`sⁿ = b`) and has full norm subgroup `N_{L/K}(Lˣ) = Kˣ`, then `b ∈ (Kˣ)ⁿ`. -/
theorem mem_powerSubgroup_of_normGroup_eq_top {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {b : Kˣ} {s : L}
    (hs : s ^ n = algebraMap K L b) (hnorm : TauCeti.normGroup K L = ⊤) :
    b ∈ TauCeti.powerSubgroup Kˣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, eq_comm, map_eq_one_iff _ (algebraMap K L).injective,
      Units.val_eq_one] at hs
    exact hs ▸ one_mem _
  have : NeZero n := ⟨hn⟩
  -- Embed `K(s)` as `E := K⟮ι s⟯` inside `AlgebraicClosure K` to reduce to a simple radical
  -- subextension and lower `L : Type*` to `Type` for `TauCeti.index_normGroup_of_isCyclic`.
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  set E := K⟮ι s⟯
  have : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (ι s))
  have hs' : AdjoinSimple.gen K (ι s) ^ n = algebraMap K E b :=
    Subtype.ext (by simp [← map_pow, hs])
  have hgen' : K⟮AdjoinSimple.gen K (ι s)⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top (ι s)
  let j : E →ₐ[K] L := (AlgEquiv.ofInjectiveField ι).symm.toAlgHom.comp
    (IntermediateField.inclusion (adjoin_simple_le_iff.2 (AlgHom.mem_fieldRange.2 ⟨s, rfl⟩)))
  have hnorm' : TauCeti.normGroup K E = ⊤ :=
    eq_top_iff.2 (hnorm.ge.trans j.normGroup_le_normGroup)
  let _ := TauCeti.algebraicExtensionValuativeRel K E
  let _ := TauCeti.algebraicExtensionNormedFieldTopology K E
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField K E
  have := TauCeti.algebraicExtension_valuativeExtension K E
  have := TauCeti.isGalois_of_pow_eq_of_adjoin_eq_top hζ hs' hgen'
  have := TauCeti.isCyclic_of_pow_eq_of_adjoin_eq_top hζ hs' hgen'
  have h1 : finrank K E = 1 := by
    rw [← TauCeti.index_normGroup_of_isCyclic K E, hnorm', Subgroup.index_top]
  obtain ⟨c, -, hcb⟩ := TauCeti.exists_pow_finrank_eq_algebraMap hζ hs' hgen'
  rw [h1, Nat.div_one] at hcb
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [← hcb, zero_pow hn])
  exact (TauCeti.mem_powerSubgroup_iff n).2 ⟨Units.mk0 c hc0, Units.ext (by simpa using hcb)⟩

end IsPrimitiveRoot
