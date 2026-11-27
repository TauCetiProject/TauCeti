/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.AddSubgroup.CharacterAnnihilator
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice
public import TauCeti.NumberTheory.LocalField.AddChar.Conductor

/-!
# Dual lattices for a character pairing over a nonarchimedean local field

Let `K` be a nonarchimedean local field with valuation ring `O = 𝒪[K]`, let `ψ` be a nontrivial
additive character of `K` which is trivial on a neighbourhood of `0`, with conductor exponent
`ν = ν(ψ)` (`AddChar.conductorExponent`), and let `B` be a bilinear pairing on a `K`-vector space
`V`. For an `O`-submodule `L` of `V`, the annihilator of `L` for the character pairing
`(x, y) ↦ ψ (B x y)` is the `O`-submodule `L.characterAnnihilator ψ B`.

Since `B (L, y)` is an `O`-submodule of `K`, it lies in the kernel of `ψ` exactly when it lies in
`P ^ (-ν) = {z | valuation K z ≤ uniformizer K ^ (-ν)}`, so the annihilator is the dual lattice
`L^∨ = {y | B (L, y) ⊆ P ^ (-ν)}`. Choosing `c ∈ K` of valuation `uniformizer K ^ (-ν)`, this is
Mathlib's dual submodule `LinearMap.BilinForm.dualSubmodule` of `L` for the rescaled transposed
form `c⁻¹ • B.flip`. For `B` nondegenerate and `L` an `O`-lattice with basis `e₁, …, e_d`, it
follows that `L^∨` is the lattice with basis `c • f₁, …, c • f_d`, where `B (eᵢ, f_j) = δᵢⱼ`, and
that the annihilator of `L^∨` in the first variable is `L` again.

These are the dual lattices entering the self-dual Haar measure `vol(L) vol(L^∨) = 1` on `V` and
Fourier inversion on the Schwartz–Bruhat space of `V`, through the Fourier identities for
character annihilators in `TauCeti.Analysis.Fourier.CharacterAnnihilator`. The special cases of
the multiplication pairing on `K`, the dot product on `Kⁿ` and the trace form on matrices are in
`TauCeti.NumberTheory.LocalField.AddChar.Conductor`.

## Main results

* `Submodule.mem_characterAnnihilator_iff_valuation_le`: `y` annihilates `L` exactly when
  `B (x, y) ∈ P ^ (-ν)` for every `x ∈ L`.
* `Submodule.characterAnnihilator_eq_dualSubmodule`: the annihilator of `L` is the dual submodule
  of `L` for `c⁻¹ • B.flip`.
* `Submodule.characterAnnihilator_span_of_basis`: the annihilator of the lattice spanned by a basis
  `e` of `V` is spanned by `c • f`, for `f` the `B`-dual basis of `e`.
* `Submodule.isFullLattice_characterAnnihilator`: the annihilator of a lattice is a lattice.
* `Submodule.characterAnnihilator_characterAnnihilator_flip`: the annihilator of `L^∨` for the
  transposed pairing is `L`.
* `AddChar.characterAnnihilator_leAddSubgroup`: for the multiplication pairing on `K`, the
  annihilator of the fractional ideal `P ^ m` is `P ^ (-ν - m)`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter II, §5 and Chapter VII, §2.
-/

public section

open Filter Topology ValuativeRel Module

namespace Submodule

variable {K V W M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [AddCommGroup V] [Module K V] [Module 𝒪[K] V] [IsScalarTower 𝒪[K] K V]
  [CommMonoid M] {ψ : AddChar K M}

section Pairing

variable [AddCommGroup W] [Module K W] [Module 𝒪[K] W] [IsScalarTower 𝒪[K] K W]

/-- **The dual lattice.** For a nontrivial additive character `ψ` of `K` which is trivial on a
neighbourhood of `0`, a vector `y` annihilates the `𝒪[K]`-submodule `L` under the pairing
`ψ (B x y)` exactly when `B (x, y)` lies in `P ^ (-ν(ψ))` for every `x ∈ L`. -/
theorem mem_characterAnnihilator_iff_valuation_le (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K))
    (h1 : ψ ≠ 1) (B : V →ₗ[K] W →ₗ[K] K) (L : Submodule 𝒪[K] V) (y : W) :
    y ∈ L.characterAnnihilator ψ B ↔
      ∀ x ∈ L, valuation K (B x y) ≤ uniformizer K ^ (-ψ.conductorExponent) := by
  simp_rw [mem_characterAnnihilator]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · -- `B (L, y)` is stable under `𝒪[K]`, so `ψ` is trivial on `𝒪[K] • B x y`.
    have key := (ψ.forall_mul_eq_one_iff_valuation_le h0 h1 0 (B x y)).1 fun r hr ↦ by
      -- `uniformizer K ^ (0 : ℤ) = 1`, so `r` is integral.
      have hr' : r ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).2 (by simpa using hr)
      have hrx : B ((⟨r, hr'⟩ : 𝒪[K]) • x) y = r * B x y := by
        simp [← algebraMap_smul K, Algebra.algebraMap_ofSubring]
      exact hrx ▸ h _ (L.smul_mem _ hx)
    simpa using key
  · have key := (ψ.forall_mul_eq_one_iff_valuation_le h0 h1 0 (B x y)).2 (by simpa using h x hx)
    simpa using key 1 (by simp)

end Pairing

variable {B : LinearMap.BilinForm K V} {c : K}

private theorem ne_zero_of_valuation_eq {n : ℤ} (hc : valuation K c = uniformizer K ^ n) :
    c ≠ 0 :=
  (valuation K).ne_zero_iff.1 <| hc ▸ zpow_ne_zero _ uniformizer_ne_zero

omit [Module 𝒪[K] V] [IsScalarTower 𝒪[K] K V] in
/-- Rescaling a nondegenerate form by `c⁻¹`, for `c` of valuation a power of the uniformizer, keeps
it nondegenerate. -/
private theorem nondegenerate_inv_smul {n : ℤ} (hc : valuation K c = uniformizer K ^ n)
    (hB : B.Nondegenerate) : (c⁻¹ • B).Nondegenerate :=
  (TauCeti.BilinForm.nondegenerate_smul_iff
    (IsRegular.of_ne_zero (inv_ne_zero (ne_zero_of_valuation_eq hc)))).2 hB

/-- For `c ∈ K` of valuation `uniformizer K ^ (-ν(ψ))`, the annihilator of an `𝒪[K]`-submodule
`L` under `ψ (B x y)` is the dual submodule `{y | c⁻¹ * B (x, y) ∈ 𝒪[K] for all x ∈ L}` of `L`
for the rescaled transposed form `c⁻¹ • B.flip`, in Mathlib's
`LinearMap.BilinForm.dualSubmodule`. -/
theorem characterAnnihilator_eq_dualSubmodule (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (hc : valuation K c = uniformizer K ^ (-ψ.conductorExponent)) (L : Submodule 𝒪[K] V) :
    L.characterAnnihilator ψ B = (c⁻¹ • B.flip).dualSubmodule L := by
  have hc0 : 0 < valuation K c := hc ▸ zpow_pos uniformizer_pos _
  ext y
  rw [mem_characterAnnihilator_iff_valuation_le h0 h1, LinearMap.BilinForm.mem_dualSubmodule]
  refine forall₂_congr fun x _ ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul,
    Submodule.mem_one, ← hc]
  -- `c⁻¹ * B x y` is integral exactly when `B x y` has valuation at most that of `c`.
  have hval : valuation K (c⁻¹ * B x y) ≤ 1 ↔ valuation K (B x y) ≤ valuation K c := by
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ hc0, mul_one]
  rw [← hval]
  exact ⟨fun h ↦ ⟨⟨_, (Valuation.mem_integer_iff _ _).2 h⟩, rfl⟩,
    fun ⟨r, hr⟩ ↦ hr ▸ (Valuation.mem_integer_iff _ _).1 r.property⟩

/-- For `c ∈ K` of valuation `uniformizer K ^ (-ν(ψ))` and a basis `e` of `V`, the annihilator
of the lattice spanned by `e` under `ψ (B x y)` is spanned by `c • f`, where `f` is the basis with
`B (eᵢ, f_j) = δᵢⱼ` (`B.flip.dualBasis hB.flip e`). -/
theorem characterAnnihilator_span_of_basis {ι : Type*} [Finite ι] [DecidableEq ι]
    (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (hc : valuation K c = uniformizer K ^ (-ψ.conductorExponent)) (hB : B.Nondegenerate)
    (e : Basis ι K V) :
    (span 𝒪[K] (Set.range e)).characterAnnihilator ψ B =
      span 𝒪[K] (Set.range fun i ↦ c • B.flip.dualBasis hB.flip e i) := by
  rw [characterAnnihilator_eq_dualSubmodule h0 h1 hc,
    LinearMap.BilinForm.dualSubmodule_span_of_basis _ (nondegenerate_inv_smul hc hB.flip)]
  congr 2
  funext i
  rw [Basis.dualBasis_smul_apply _ _ hB.flip _ (inv_ne_zero (ne_zero_of_valuation_eq hc)),
    inv_inv]

/-- The annihilator of an `𝒪[K]`-lattice `L` under `ψ (B x y)`, for a nondegenerate `B` and a
nontrivial `ψ` trivial on a neighbourhood of `0`, is again an `𝒪[K]`-lattice. -/
theorem isFullLattice_characterAnnihilator (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (hB : B.Nondegenerate) (L : Submodule 𝒪[K] V) [L.IsFullLattice K] :
    (L.characterAnnihilator ψ B).IsFullLattice K := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer K ^ (-ψ.conductorExponent))
  have := IsLattice.free K L
  rw [characterAnnihilator_eq_dualSubmodule h0 h1 hc]
  exact (c⁻¹ • B.flip).isFullLattice_dualSubmodule (nondegenerate_inv_smul hc hB.flip) L

/-- **Double duality.** The annihilator of the dual lattice `L^∨ = L.characterAnnihilator ψ B` of
an `𝒪[K]`-lattice `L` in the first variable, that is for the transposed pairing `B.flip`, is `L`,
for a nondegenerate `B` and a nontrivial `ψ` trivial on a neighbourhood of `0`. -/
theorem characterAnnihilator_characterAnnihilator_flip (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K))
    (h1 : ψ ≠ 1) (hB : B.Nondegenerate) (L : Submodule 𝒪[K] V) [L.IsFullLattice K] :
    (L.characterAnnihilator ψ B).characterAnnihilator ψ B.flip = L := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer K ^ (-ψ.conductorExponent))
  have := IsLattice.free K L
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  rw [characterAnnihilator_eq_dualSubmodule h0 h1 hc,
    characterAnnihilator_eq_dualSubmodule h0 h1 hc, hflip, ← map_smul]
  exact (c⁻¹ • B).dualSubmodule_dualSubmodule_flip (nondegenerate_inv_smul hc hB) L

end Submodule

namespace AddChar

variable {K M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CommMonoid M] {ψ : AddChar K M}

/-- **Duality of fractional ideals.** For a nontrivial additive character `ψ` of `K` which is
trivial on a neighbourhood of `0`, the annihilator of `P ^ m` under the pairing `ψ (x * y)` is
`P ^ (-ν(ψ) - m)`. -/
theorem characterAnnihilator_leAddSubgroup (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : K)) (h1 : ψ ≠ 1)
    (m : ℤ) :
    ((valuation K).leAddSubgroup (uniformizer K ^ m)).characterAnnihilator ψ
        (LinearMap.mul K K) =
      (valuation K).leAddSubgroup (uniformizer K ^ (-ψ.conductorExponent - m)) := by
  ext y
  simpa [AddSubgroup.mem_characterAnnihilator] using forall_mul_eq_one_iff_valuation_le h0 h1 m y

end AddChar
