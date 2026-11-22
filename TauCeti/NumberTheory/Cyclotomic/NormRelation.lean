/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.Cyclotomic.Aut
import TauCeti.NumberTheory.Cyclotomic.Basic
import TauCeti.NumberTheory.Cyclotomic.DistributionRelation
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Norm relations for relative norms of `1 - ζ`

Let `K ⊆ M = F(μ_n) ⊆ N = F(μ_{nℓ})` be fields over a base field `F` over which `Φ_{nℓ}` is
irreducible (for instance `F = ℚ`), let `ζ ∈ N` be a primitive `nℓ`-th root of unity and `η ∈ M`
with `η = ζ ^ ℓ`. Let `L` be any intermediate field of `N / K`. This file computes the norm to `K`
of `N_{N/L}(1 - ζ)` in terms of `N_{M/K}(1 - η)`:

* if `ℓ ∣ n`, then `N_{L/K}(N_{N/L}(1 - ζ)) = N_{M/K}(1 - η)`;
* if `ℓ` is a prime not dividing `n` and `K = F(μ_m)` with `m ∣ n`, then
  `N_{L/K}(N_{N/L}(1 - ζ)) * σ_ℓ⁻¹(N_{M/K}(1 - η)) = N_{M/K}(1 - η)`, where `σ_ℓ ∈ Gal(K/F)` is the
  arithmetic Frobenius `ζ_m ↦ ζ_m ^ ℓ`. Multiplicatively,
  `N_{L/K}(N_{N/L}(1 - ζ)) = N_{M/K}(1 - η) ^ (1 - σ_ℓ⁻¹)`.

For a prime `p`, take `n = m * p`, so that `M = F(μ_{mp})` and `N = F(μ_{mℓp})`, and let
`L = F(μ_{mℓ})`. Then `c_m = N_{F(μ_{mp})/F(μ_m)}(1 - ζ_{mp})` and
`c_{mℓ} = N_{F(μ_{mℓp})/F(μ_{mℓ})}(1 - ζ_{mℓp})` are Rubin's `p`-extended cyclotomic numbers, and
the two relations read `N_{L/K}(c_{mℓ}) = c_m` for `ℓ ∣ mp` and
`N_{L/K}(c_{mℓ}) = c_m ^ (1 - σ_ℓ⁻¹)` for a prime `ℓ ∤ mp`. These are the norm relations of the
Euler system of cyclotomic units, with Euler polynomial `1 - X` at every prime `ℓ ≠ p`; for
`ℓ = p` the first relation is the norm compatibility `N_{F(μ_{mp})/F(μ_m)}(c_{mp}) = c_m` in the
`p`-direction. Unlike the relations for `1 - ζ_n` itself, they have no exception at conductor `1`.

## Main results

* `IsPrimitiveRoot.norm_norm_one_sub_of_dvd`: the relation when `ℓ ∣ n`.
* `IsPrimitiveRoot.norm_norm_one_sub_mul_autEquivPow_symm_inv_apply`: the relation for a prime
  `ℓ ∤ n`, with the inverse arithmetic Frobenius given by `IsCyclotomicExtension.autEquivPow`.
* `IsPrimitiveRoot.norm_norm_one_sub_eq_div_autEquivPow_symm_inv_apply`: the same relation as a
  quotient, for `n > 1`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Chapter III, §2.1 and Remark 2.1.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

variable {F M N : Type*} [Field F] [Field M] [CommRing N] [IsDomain N] [Algebra F M] [Algebra F N]
  [Algebra M N] [IsScalarTower F M N] {n ℓ : ℕ} [NeZero n] [IsCyclotomicExtension {n} F M]
  [IsCyclotomicExtension {n * ℓ} F N]
  {K L : Type*} [Field K] [Field L] [Algebra K M] [Algebra K N] [Algebra K L] [Algebra L N]
  [IsScalarTower K M N] [IsScalarTower K L N] {ζ : N} {η : M}

/-- **The norm relation when `ℓ ∣ n`.** For `K ⊆ M = F(μ_n) ⊆ N = F(μ_{nℓ})`, an intermediate
field `L` of `N / K`, a primitive `nℓ`-th root of unity `ζ ∈ N` and `η = ζ ^ ℓ`:
`N_{L/K}(N_{N/L}(1 - ζ)) = N_{M/K}(1 - η)`. -/
theorem norm_norm_one_sub_of_dvd (hirr : Irreducible (cyclotomic (n * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (n * ℓ)) (hη : algebraMap M N η = ζ ^ ℓ) (hdvd : ℓ ∣ n) :
    Algebra.norm K (Algebra.norm L (1 - ζ)) = Algebra.norm K (1 - η) := by
  rw [Algebra.norm_norm, ← Algebra.norm_norm (S := M), hζ.norm_one_sub_of_dvd hirr hη hdvd]

section Prime

variable [hℓ : Fact ℓ.Prime] {m : ℕ} [NeZero m]

include M N in
/-- If `Φ_{nℓ}` is irreducible over `F` for a prime `ℓ ∤ n`, then so is `Φ_n`: the degrees
`[F(μ_{nℓ}) : F] = φ(n) (ℓ - 1)` and `[F(μ_{nℓ}) : F(μ_n)] = ℓ - 1` force `[F(μ_n) : F] = φ(n)`. -/
private theorem irreducible_cyclotomic_of_not_dvd (hirr : Irreducible (cyclotomic (n * ℓ) F))
    (hdvd : ¬ℓ ∣ n) : Irreducible (cyclotomic n F) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have := IsCyclotomicExtension.finiteDimensional {n} F M
  have : IsCyclotomicExtension {n * ℓ} M N := IsCyclotomicExtension.tower_top F M N
  have := IsCyclotomicExtension.finiteDimensional {n * ℓ} M N
  refine IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank F M ?_
  have h := IsCyclotomicExtension.finrank N hirr
  rw [← Module.finrank_mul_finrank F M N,
    IsCyclotomicExtension.finrank_eq_of_prime_not_dvd M N hirr hdvd,
    Nat.totient_mul ((hℓ.out.coprime_iff_not_dvd.2 hdvd).symm), Nat.totient_prime hℓ.out] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hℓ.out.one_lt) h).ge

variable [Algebra F K] [IsScalarTower F K M] [IsCyclotomicExtension {m} F K]

/-- **The norm relation for a prime `ℓ ∤ n`, with the arithmetic Frobenius.** For
`K = F(μ_m) ⊆ M = F(μ_n) ⊆ N = F(μ_{nℓ})` with `m ∣ n`, an intermediate field `L` of `N / K`, a
primitive `nℓ`-th root of unity `ζ ∈ N` and `η = ζ ^ ℓ`:
`N_{L/K}(N_{N/L}(1 - ζ)) * σ_ℓ⁻¹(N_{M/K}(1 - η)) = N_{M/K}(1 - η)`, where `σ_ℓ ∈ Gal(K/F)` is the
arithmetic Frobenius `ζ_m ↦ ζ_m ^ ℓ`, whose inverse is the image of `ℓ⁻¹ ∈ (ZMod m)ˣ` under
`(IsCyclotomicExtension.autEquivPow K h).symm`. Multiplicatively,
`N_{L/K}(N_{N/L}(1 - ζ)) = N_{M/K}(1 - η) ^ (1 - σ_ℓ⁻¹)`. -/
theorem norm_norm_one_sub_mul_autEquivPow_symm_inv_apply
    (hirr : Irreducible (cyclotomic (n * ℓ) F)) (hζ : IsPrimitiveRoot ζ (n * ℓ))
    (hη : algebraMap M N η = ζ ^ ℓ) (h : Irreducible (cyclotomic m F)) (hmn : m ∣ n)
    (hcop : ℓ.Coprime n) :
    Algebra.norm K (Algebra.norm L (1 - ζ)) *
        (IsCyclotomicExtension.autEquivPow K h).symm
          (ZMod.unitOfCoprime ℓ (hcop.coprime_dvd_right hmn))⁻¹ (Algebra.norm K (1 - η)) =
      Algebra.norm K (1 - η) := by
  have hM := irreducible_cyclotomic_of_not_dvd (M := M) (N := N) hirr
    (hℓ.out.coprime_iff_not_dvd.1 hcop)
  -- The inverse Frobenius `σ` of `M` restricts to that of `K`, and the norm `N_{M/K}` commutes
  -- with this pair.
  set σ := (IsCyclotomicExtension.autEquivPow M hM).symm (ZMod.unitOfCoprime ℓ hcop)⁻¹
  set τ := (IsCyclotomicExtension.autEquivPow K h).symm
    (ZMod.unitOfCoprime ℓ (hcop.coprime_dvd_right hmn))⁻¹
  have he :
      (algebraMap K M).comp τ.toRingEquiv = (σ.toRingEquiv : M →+* M).comp (algebraMap K M) :=
    RingHom.ext fun x ↦ by
      have := IsCyclotomicExtension.algebraMap_autEquivPow_symm_unitsMap_apply (L := M) h hM hmn
        (ZMod.unitOfCoprime ℓ hcop)⁻¹ x
      rw [map_inv, ZMod.unitsMap_unitOfCoprime] at this
      simpa [τ, σ] using this
  have hσ : τ (Algebra.norm K (1 - η)) = Algebra.norm K (σ (1 - η)) := by
    conv_lhs => rw [Algebra.norm_eq_of_equiv_equiv τ.toRingEquiv σ.toRingEquiv he]
    simp
  rw [Algebra.norm_norm (R := K) (S := L), ← Algebra.norm_norm (R := K) (S := M) (a := 1 - ζ), hσ,
    ← map_mul, hζ.norm_one_sub_mul_autEquivPow_symm_inv_apply hirr hη hM hcop]

/-- **The norm relation for a prime `ℓ ∤ n`, as a quotient.** For `n > 1`, in the setting of
`IsPrimitiveRoot.norm_norm_one_sub_mul_autEquivPow_symm_inv_apply`,
`N_{L/K}(N_{N/L}(1 - ζ)) = N_{M/K}(1 - η) / σ_ℓ⁻¹(N_{M/K}(1 - η))`. -/
theorem norm_norm_one_sub_eq_div_autEquivPow_symm_inv_apply
    (hirr : Irreducible (cyclotomic (n * ℓ) F)) (hζ : IsPrimitiveRoot ζ (n * ℓ))
    (hη : algebraMap M N η = ζ ^ ℓ) (h : Irreducible (cyclotomic m F)) (hmn : m ∣ n)
    (hcop : ℓ.Coprime n) (hn : 1 < n) :
    Algebra.norm K (Algebra.norm L (1 - ζ)) =
      Algebra.norm K (1 - η) /
        (IsCyclotomicExtension.autEquivPow K h).symm
          (ZMod.unitOfCoprime ℓ (hcop.coprime_dvd_right hmn))⁻¹ (Algebra.norm K (1 - η)) := by
  have := IsCyclotomicExtension.finiteDimensional {n} F M
  have : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite F K M
  have hne : Algebra.norm K (1 - η) ≠ 0 := Algebra.norm_ne_zero_iff.2
    (sub_ne_zero.2 ((IsPrimitiveRoot.of_algebraMap_eq_pow hζ hη).ne_one hn).symm)
  exact eq_div_of_mul_eq (by simpa using hne)
    (hζ.norm_norm_one_sub_mul_autEquivPow_symm_inv_apply hirr hη h hmn hcop)

end Prime

end IsPrimitiveRoot
