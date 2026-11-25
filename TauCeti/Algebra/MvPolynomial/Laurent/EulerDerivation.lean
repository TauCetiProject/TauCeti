/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.WeightDerivation
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.RingTheory.KoszulComplex.Commuting
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Euler derivations and the twisted de Rham complex of a split torus

On the Laurent polynomial ring `R[x_i^{±1} : i ∈ K]`, the coordinate ring of the split torus
`T = G_m^K`, the **Euler derivation** `θ_i = x_i ∂/∂x_i` multiplies the monomial `x^m` by its
exponent `m_i` (`TauCeti.LaurentRing.eulerDerivation`). The Euler derivations commute pairwise.

A Laurent polynomial `φ` defines the exponential connection `E^φ = (O_T, d + dφ)` on the torus.
In the basis `dlog x_i = dx_i / x_i` of one-forms, `d g = ∑ᵢ θ_i(g) dlog x_i`, so the twisted
differential of a function `g` has `i`-th coefficient `θ_i g + θ_i(φ) g`: this is the **twisted
Euler operator** `TauCeti.LaurentRing.twistedEuler φ i = θ_i + θ_i(φ)`. The twisted Euler
operators again commute pairwise (`TauCeti.LaurentRing.commute_twistedEuler`). Writing
differential forms in the basis `dlog x_J = dlog x_{j₁} ∧ ⋯ ∧ dlog x_{j_q}`, the twisted de Rham
complex `(Ω^•(T), d + dφ ∧)` becomes the Koszul complex of the twisted Euler operators, and this
is how it is represented here: the complex is
`TauCeti.koszulCochainDifferential (twistedEuler φ)` on `Finset K → LaurentRing R K`, whose
square vanishes by `TauCeti.koszulCochainDifferential_koszulCochainDifferential`. (The comparison
with the module of Kähler differentials of the Laurent ring is not formalized here.) Its top
cohomology `H^n_dR(T, E^φ)` is the cokernel `R[x^{±1}] ⧸ ∑ᵢ range (θ_i + θ_i φ)`
(`TauCeti.koszulTopCohomologyEquiv`).

For one variable and `φ = x` over a field of characteristic zero this cokernel is a line
spanned by the class of `1` (`TauCeti.LaurentRing.finrank_quotient_iSup_range_twistedEuler_X`):
`x^{m+1} ≡ -m x^m` modulo the image of `θ + x`, and the functional `x^{-k} ↦ 1 / k!`,
`x^k ↦ 0` for `k > 0`, vanishes on that image. Hence the twisted de Rham cohomology
`H¹_dR(G_m, E^x)` has dimension one
(`TauCeti.LaurentRing.finrank_quotient_koszulCoboundaries_twistedEuler_X`).

## Main definitions

* `TauCeti.LaurentRing.eulerDerivation i`: the Euler derivation `x_i ∂/∂x_i`.
* `TauCeti.LaurentRing.twistedEuler φ i`: the twisted Euler operator `θ_i + θ_i(φ)`.

## Main results

* `TauCeti.LaurentRing.commute_eulerDerivation` and `TauCeti.LaurentRing.commute_twistedEuler`:
  the Euler derivations, and the twisted Euler operators of a fixed `φ`, commute.
* `TauCeti.LaurentRing.finrank_quotient_koszulCoboundaries_twistedEuler_X`: `H¹_dR(G_m, E^x)` is
  one-dimensional.

## References

* A. Adolphson and S. Sperber, *On twisted de Rham cohomology*, Nagoya Math. J. 146 (1997),
  for the twisted de Rham complex of a torus in the basis `dlog x_J`.
* J.-D. Yu, *Irregular Hodge filtration on twisted de Rham cohomology*, Manuscripta Math. 144
  (2014), §4.
-/

public section

open AddMonoidAlgebra

namespace TauCeti.LaurentRing

variable {R K : Type*} [CommRing R]

/-- The **Euler derivation** `θ_i = x_i ∂/∂x_i` of the Laurent polynomial ring: it multiplies the
monomial `x^m` by the exponent `m_i`. It is the weight derivation of the `i`-th coordinate of the
exponent lattice. -/
noncomputable def eulerDerivation (i : K) : Derivation R (LaurentRing R K) (LaurentRing R K) :=
  weightDerivation ((Int.castAddHom R).comp (Finsupp.applyAddHom i))

/-- The coefficient of `x^m` in `θ_i f` is `m_i` times that of `f`. -/
@[simp]
theorem coeff_eulerDerivation (i : K) (f : LaurentRing R K) (m : K →₀ ℤ) :
    (eulerDerivation i f).coeff m = (m i : R) * f.coeff m := by
  simp [eulerDerivation]

/-- The Euler derivation `θ_i` multiplies the monomial `x^m` by `m_i`. -/
@[simp]
theorem eulerDerivation_single (i : K) (m : K →₀ ℤ) (r : R) :
    eulerDerivation i (single m r : LaurentRing R K) = single m ((m i : R) * r) := by
  simp [eulerDerivation]

/-- `θ_i x_i = x_i`. -/
@[simp]
theorem eulerDerivation_X_self (i : K) : eulerDerivation i (X i : LaurentRing R K) = X i := by
  simp [X_def]

/-- `θ_i x_j = 0` for `i ≠ j`. -/
@[simp]
theorem eulerDerivation_X_of_ne {i j : K} (h : i ≠ j) :
    eulerDerivation i (X j : LaurentRing R K) = 0 := by
  simp [X_def, h.symm]

/-- The Euler derivations commute pairwise. -/
theorem commute_eulerDerivation (i j : K) :
    Commute (eulerDerivation (R := R) i : Module.End R (LaurentRing R K))
      (eulerDerivation (R := R) j : Module.End R (LaurentRing R K)) :=
  commute_weightDerivation _ _

/-- The **twisted Euler operator** `θ_i + θ_i(φ)` of the exponential connection `d + dφ` on the
torus: in the basis `dlog x_i` of one-forms, `(d + dφ) g` has `i`-th coefficient
`θ_i g + θ_i(φ) g`. -/
noncomputable def twistedEuler (φ : LaurentRing R K) (i : K) : Module.End R (LaurentRing R K) :=
  (eulerDerivation (R := R) i : Module.End R (LaurentRing R K)) +
    LinearMap.mulLeft R (eulerDerivation i φ)

/-- `(θ_i + θ_i φ) f = θ_i f + θ_i(φ) f`. -/
@[simp]
theorem twistedEuler_apply (φ : LaurentRing R K) (i : K) (f : LaurentRing R K) :
    twistedEuler φ i f = eulerDerivation i f + eulerDerivation i φ * f := by
  rw [twistedEuler, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]

/-- For `φ = x_i`, the twisted Euler operator `θ_i + x_i` sends `x^m` to `m_i x^m + x_i x^m`. -/
theorem twistedEuler_X_single (i : K) (m : K →₀ ℤ) (r : R) :
    twistedEuler (X i : LaurentRing R K) i (single m r) =
      single m ((m i : R) * r) + single (Finsupp.single i 1 + m) r := by
  rw [twistedEuler_apply, eulerDerivation_single, eulerDerivation_X_self, X_def,
    single_mul_single, one_mul]

/-- The twisted Euler operators of a fixed Laurent polynomial commute pairwise, so that they are
the differentials of a Koszul complex, the twisted de Rham complex of the torus. -/
theorem commute_twistedEuler (φ : LaurentRing R K) (i j : K) :
    Commute (twistedEuler φ i) (twistedEuler φ j) := by
  have h (g : LaurentRing R K) : eulerDerivation i (eulerDerivation j g) =
      eulerDerivation j (eulerDerivation i g) :=
    congr($((commute_eulerDerivation (R := R) i j).eq) g)
  refine LinearMap.ext fun f ↦ ?_
  simp only [mul_apply_eq_comp, twistedEuler_apply, map_add, Derivation.leibniz, smul_eq_mul,
    h f, h φ]
  ring

/-! ### The twisted de Rham cohomology of `(G_m, x)` -/

section Example

variable {k : Type*} [Field k] [Unique K]

/-- The value `1 / (-n)!` for `n ≤ 0`, and `0` for `n > 0`, of the functional on the Laurent
ring which vanishes on the image of `θ + x`. -/
private noncomputable def residueCoeff (n : ℤ) : k :=
  if n ≤ 0 then ((-n).toNat.factorial : k)⁻¹ else 0

private theorem residueCoeff_neg_natCast (b : ℕ) :
    residueCoeff (-(b : ℤ)) = (b.factorial : k)⁻¹ := by
  simp [residueCoeff]

private theorem residueCoeff_of_pos {n : ℤ} (h : 0 < n) : residueCoeff (k := k) n = 0 := by
  simp [residueCoeff, not_le.mpr h]

private theorem residueCoeff_zero : residueCoeff (k := k) 0 = 1 := by
  simpa using residueCoeff_neg_natCast (k := k) 0

/-- The recursion `n c(n) + c(n + 1) = 0` of the coefficients, which says that the functional
kills `θ(x^n) + x · x^n = n x^n + x^{n+1}`. -/
private theorem intCast_mul_residueCoeff_add [CharZero k] (n : ℤ) :
    (n : k) * residueCoeff n + residueCoeff (n + 1) = 0 := by
  obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [residueCoeff_of_pos (n := (b : ℤ) + 1) (by omega), add_zero]
    rcases b.eq_zero_or_pos with rfl | hb
    · simp
    · rw [residueCoeff_of_pos (by omega), mul_zero]
  · rcases b with _ | a
    · simp [residueCoeff_of_pos]
    · have h : -((a + 1 : ℕ) : ℤ) + 1 = -(a : ℤ) := by omega
      rw [h, residueCoeff_neg_natCast, residueCoeff_neg_natCast, Nat.factorial_succ]
      have : ((a : k) + 1) ≠ 0 := by exact_mod_cast a.succ_ne_zero
      have : (a.factorial : k) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
      push_cast
      field_simp
      ring

/-- The functional `x^m ↦ c(m)` on the one-variable Laurent ring. -/
private noncomputable def residue : LaurentRing k K →ₗ[k] k :=
  Finsupp.linearCombination k (fun m : K →₀ ℤ ↦ residueCoeff (m default)) ∘ₗ
    (coeffLinearEquiv k).toLinearMap

private theorem residue_single (m : K →₀ ℤ) (r : k) :
    residue (single m r : LaurentRing k K) = r * residueCoeff (m default) := by
  simp [residue, coeff_single, Finsupp.linearCombination_single]

private theorem residue_one : residue (1 : LaurentRing k K) = 1 := by
  rw [one_def, residue_single, Finsupp.coe_zero, Pi.zero_apply, residueCoeff_zero, one_mul]

private theorem residue_comp_twistedEuler [CharZero k] :
    residue ∘ₗ twistedEuler (X default : LaurentRing k K) default = 0 := by
  refine lhom_ext' fun m ↦ LinearMap.ext fun r ↦ ?_
  simp only [LinearMap.comp_apply, lsingle_apply, twistedEuler_X_single, map_add, residue_single,
    LinearMap.zero_apply, Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm (1 : ℤ)]
  linear_combination r * intCast_mul_residueCoeff_add (k := k) (m default)

/-- The image of `θ + x` in the one-variable Laurent ring. -/
private noncomputable abbrev xImage (k K : Type*) [Field k] [Unique K] :
    Submodule k (LaurentRing k K) :=
  ⨆ i, LinearMap.range (twistedEuler (X default : LaurentRing k K) i)

private theorem xImage_le_ker_residue [CharZero k] :
    xImage k K ≤ LinearMap.ker (residue (k := k) (K := K)) :=
  iSup_le fun i ↦ by
    rintro _ ⟨f, rfl⟩
    rw [Unique.eq_default i, LinearMap.mem_ker, ← LinearMap.comp_apply,
      residue_comp_twistedEuler, LinearMap.zero_apply]

/-- The image of the monomial `x^n` under `θ + x` is `n x^n + x^{n+1}`. -/
private theorem smul_single_add_single_mem_xImage (n : ℤ) :
    (n : k) • (single (Finsupp.single default n) 1 : LaurentRing k K) +
      single (Finsupp.single default (n + 1)) 1 ∈ xImage k K := by
  have h := Submodule.mem_iSup_of_mem (p := fun i ↦
    LinearMap.range (twistedEuler (X default : LaurentRing k K) i)) default
    (LinearMap.mem_range_self _ (single (Finsupp.single default n) (1 : k)))
  rwa [twistedEuler_X_single, Finsupp.single_eq_same, ← Finsupp.single_add, add_comm (1 : ℤ),
    ← smul_single'] at h

/-- Every monomial `x^n` is congruent to `c(n) · 1` modulo the image of `θ + x`. -/
private theorem single_sub_residueCoeff_mem_xImage [CharZero k] (n : ℤ) :
    (single (Finsupp.single default n) 1 : LaurentRing k K) - residueCoeff (k := k) n • 1 ∈
      xImage k K := by
  induction n using Int.induction_on with
  | zero => simp [residueCoeff_zero, one_def]
  | succ i ih =>
    have hc := intCast_mul_residueCoeff_add (k := k) (i : ℤ)
    have h : (single (Finsupp.single default ((i : ℤ) + 1)) 1 : LaurentRing k K) -
        residueCoeff (k := k) ((i : ℤ) + 1) • 1 =
        (((i : ℤ) : k) • single (Finsupp.single default (i : ℤ)) 1 +
          single (Finsupp.single default ((i : ℤ) + 1)) 1) -
        ((i : ℤ) : k) • (single (Finsupp.single default (i : ℤ)) 1 -
          residueCoeff (k := k) (i : ℤ) • 1) := by
      rw [eq_neg_of_add_eq_zero_right hc]
      module
    rw [h]
    exact sub_mem (smul_single_add_single_mem_xImage _) (Submodule.smul_mem _ _ ih)
  | pred i ih =>
    have hn : ((-(i : ℤ) - 1 : ℤ) : k) ≠ 0 := by
      have : (-(i : ℤ) - 1) ≠ 0 := by omega
      exact_mod_cast this
    have hc := intCast_mul_residueCoeff_add (k := k) (-(i : ℤ) - 1)
    have hT := smul_single_add_single_mem_xImage (k := k) (K := K) (-(i : ℤ) - 1)
    rw [sub_add_cancel] at hc hT
    rw [← Submodule.smul_mem_iff _ hn]
    have h : ((-(i : ℤ) - 1 : ℤ) : k) •
        ((single (Finsupp.single default (-(i : ℤ) - 1)) 1 : LaurentRing k K) -
          residueCoeff (k := k) (-(i : ℤ) - 1) • 1) =
        (((-(i : ℤ) - 1 : ℤ) : k) • single (Finsupp.single default (-(i : ℤ) - 1)) 1 +
          single (Finsupp.single default (-(i : ℤ))) 1) -
        (single (Finsupp.single default (-(i : ℤ))) 1 - residueCoeff (k := k) (-(i : ℤ)) • 1) := by
      rw [eq_neg_of_add_eq_zero_right hc]
      module
    rw [h]
    exact sub_mem hT ih

/-- Every Laurent polynomial `f` is congruent to `residue f · 1` modulo the image of `θ + x`. -/
private theorem sub_residue_smul_one_mem_xImage [CharZero k] (f : LaurentRing k K) :
    f - residue f • (1 : LaurentRing k K) ∈ xImage k K := by
  induction f using induction_linear with
  | zero => simp
  | add f g hf hg =>
    convert add_mem hf hg using 1
    rw [map_add, add_smul]
    abel
  | single m r =>
    have h := Submodule.smul_mem _ r (single_sub_residueCoeff_mem_xImage (k := k) (K := K)
      (m default))
    rw [← Finsupp.unique_single m, smul_sub, smul_single', mul_one, smul_smul] at h
    rwa [residue_single]

/-- The residue functional induces an isomorphism of the cokernel of `θ + x` with the line. -/
private noncomputable def quotientXImageEquiv [CharZero k] :
    (LaurentRing k K ⧸ xImage k K) ≃ₗ[k] k :=
  LinearEquiv.ofBijective ((xImage k K).liftQ residue xImage_le_ker_residue) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun q hq ↦ ?_, fun a ↦ ?_⟩
    · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.liftQ_apply] at hq
      have h := sub_residue_smul_one_mem_xImage f
      rwa [hq, zero_smul, sub_zero, ← Submodule.Quotient.mk_eq_zero] at h
    · refine ⟨Submodule.Quotient.mk (a • 1), ?_⟩
      rw [Submodule.liftQ_apply, map_smul, residue_one, smul_eq_mul, mul_one]

/-- **The twisted cokernel of `(G_m, x)`**: over a field of characteristic zero, the quotient of
the one-variable Laurent ring by the image of the twisted Euler operator `θ + x` of `φ = x` is
one-dimensional, spanned by the class of `1`. -/
theorem finrank_quotient_iSup_range_twistedEuler_X [CharZero k] :
    Module.finrank k (LaurentRing k K ⧸
      ⨆ i, LinearMap.range (twistedEuler (X default : LaurentRing k K) i)) = 1 := by
  rw [quotientXImageEquiv.finrank_eq, Module.finrank_self]

/-- **`H¹_dR(G_m, E^x)` is one-dimensional**: over a field of characteristic zero, the top
cohomology of the twisted de Rham complex of the one-dimensional torus twisted by `φ = x` is a
line. -/
theorem finrank_quotient_koszulCoboundaries_twistedEuler_X [CharZero k] [LinearOrder K] :
    Module.finrank k (koszulCocycles (twistedEuler (X default : LaurentRing k K))
        (Fintype.card K) ⧸
      (koszulCoboundaries (twistedEuler (X default : LaurentRing k K)) (Fintype.card K)).comap
        (koszulCocycles (twistedEuler (X default : LaurentRing k K)) (Fintype.card K)).subtype) =
      1 := by
  rw [(koszulTopCohomologyEquiv _).finrank_eq, finrank_quotient_iSup_range_twistedEuler_X]

end Example

end TauCeti.LaurentRing
