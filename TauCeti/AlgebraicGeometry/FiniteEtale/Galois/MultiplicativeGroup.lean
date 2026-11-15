/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.CategoryTheory.Galois.Topology
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Connected
public import TauCeti.AlgebraicGeometry.FiniteEtale.Kummer
public import TauCeti.RingTheory.RootsOfUnity.TateModule.Complex

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.CategoryTheory.Galois.Connected
import TauCeti.RingTheory.Etale.LaurentPolynomial
import TauCeti.RingTheory.RootsOfUnity.TateModule.BasisChange

/-!
# The étale fundamental group of the multiplicative group

Let `K` be an algebraically closed field of characteristic zero, `𝔾_{m, K} = Spec K[T, T⁻¹]` the
multiplicative group over `K`, and `1 : Spec K ⟶ 𝔾_{m, K}` the rational point sending `T` to `1`.
This file identifies the étale fundamental group `π₁^ét(𝔾_{m, K}, 1)` — the automorphism group
`Aut (FiniteEtaleScheme.fiber (multiplicativeGroupOnePoint K K))` of the geometric fibre functor at
`1` — canonically with the Tate module `PrimeToPTateModule 1 K = lim_n μ_n(K)` as topological
groups (`TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivTateModule`).

The identification is built in three stages so that each hypothesis enters only where needed:

* **Kummer monodromy over an affine base.** Over any commutative ring `R` with a unit `t ∈ Rˣ` and
  a separably closed `R`-algebra `Ω` sending `t` to `1`, the fibre over `Spec Ω ⟶ Spec R` of the
  degree-`n` Kummer cover `Spec R[x]/(x ^ n - t)` is `μ_n(Ω)`
  (`kummerCoverFiberEquivRootsOfUnity`). When `R` supplies deck transformations for all elements of
  `μ_n(Ω)`, naturality with `kummerCoverDeck` shows that every automorphism `σ` of the fibre
  functor acts on `μ_n(Ω)` by multiplication by a root of unity `kummerMonodromyLevel σ ∈ μ_n(Ω)`,
  namely the image of `1`. Compatibility along `kummerCoverMap` assembles these finite-level
  characters into a continuous homomorphism `kummerMonodromy` into `PrimeToPTateModule p Ω`, which
  is surjective whenever `Spec R` and the Kummer covers are connected.
* **The multiplicative group in arbitrary characteristic.** For `R = K[T, T⁻¹]` and `t = T` over a
  field `K`, every Kummer cover `Spec K[T, T⁻¹][x]/(x ^ n - T)` with `n` invertible in `K` is an
  integral domain (`TauCeti.isDomain_standardTameCover_laurentPolynomial_T`), hence categorically
  connected (`isConnected_kummerCover_genericUnit`). When `K` is separably closed of exponential
  characteristic `p`, all `p'`-roots of unity already lie in `K ⊂ K[T, T⁻¹]`, giving a surjective
  continuous prime-to-`p` monodromy homomorphism
  `multiplicativeGroupPrimeToPMonodromy K p : π₁^ét(𝔾_{m, K}, 1) →ₜ* PrimeToPTateModule p K`.
* **Characteristic zero and `ℤ̂` coordinates.** When `K` is algebraically closed of characteristic
  zero, Hurwitz's theorem on `ℙ¹_K` classifies every connected finite étale cover of `𝔾_{m, K}` as
  a Kummer cover (`exists_iso_kummerCover_of_isConnected`, from
  `TauCeti.exists_algEquiv_standardTameCover_of_etale`). Since every finite étale cover decomposes
  into connected components, an automorphism trivial on all Kummer fibres is the identity, making
  `multiplicativeGroupPrimeToPMonodromy K 1` an isomorphism of topological groups. Choosing a
  compatible system `ζ = (ζ_n)_n` of primitive roots of unity further identifies
  `π₁^ét(𝔾_{m, K}, 1)` with `ℤ̂` (`multiplicativeGroupAutFiberContinuousMulEquivZHat`); replacing
  `ζ` by `ζ ^ᶻ u` for a unit `u ∈ ℤ̂ˣ` multiplies the forward parametrization by `u` and multiplies
  coordinates by `u⁻¹` (see `TauCeti.RingTheory.RootsOfUnity.TateModule.BasisChange`), while leaving
  the Tate-module isomorphism unchanged. Over `ℂ`, the standard system `ζ_n = exp(2πi / n)` makes
  this coordinate explicit.

## Main definitions

* `TauCeti.FiniteEtaleScheme.kummerMonodromyLevel`: the level-`n` Kummer character
  `Aut (fiber x) →* rootsOfUnity n Ω`.
* `TauCeti.FiniteEtaleScheme.kummerMonodromy`: the assembled continuous homomorphism
  `Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupOnePoint K Ω`: the geometric point `1` of
  `𝔾_{m, K} = Spec K[T, T⁻¹]` valued in `Ω`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupPowerCoverFiberEquiv`: the fibre over `1` of the
  degree-`n` power cover of `𝔾_{m, K}` is `μ_n(Ω)`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupPrimeToPMonodromy`: the continuous prime-to-`p`
  monodromy `π₁^ét(𝔾_{m, K}, 1) →ₜ* PrimeToPTateModule p K` for separably closed `K` of
  exponential characteristic `p`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivTateModule`: the
  canonical root-choice-free isomorphism `π₁^ét(𝔾_{m, K}, 1) ≃ₜ* PrimeToPTateModule 1 K` for
  algebraically closed `K` of characteristic zero.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivZHat`: the coordinate
  isomorphism `π₁^ét(𝔾_{m, K}, 1) ≃ₜ* zHat` attached to a compatible system of primitive roots of
  unity, and `complexMultiplicativeGroupAutFiberContinuousMulEquivZHat` over `ℂ`.

## Main results

* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity_smul`: `Aut (fiber x)` acts on the
  Kummer fibre `μ_n(Ω)` by multiplication by `kummerMonodromyLevel`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupPrimeToPMonodromy_surjective`: surjectivity of the
  prime-to-`p` monodromy of `𝔾_{m, K}` over any separably closed field.
* `TauCeti.FiniteEtaleScheme.exists_iso_kummerCover_of_isConnected`: every connected finite étale
  cover of `𝔾_{m, K}` over an algebraically closed field of characteristic zero is isomorphic to a
  Kummer power cover.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_zpowHat`,
  `TauCeti.FiniteEtaleScheme.ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat`,
  `TauCeti.FiniteEtaleScheme.toZMod_five_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat`:
  replacing `ζ` by `ζ ^ᶻ u` composes the parametrization with multiplication by `u`, composes the
  coordinate map with multiplication by `u⁻¹`, and for `u ≡ 2 (mod 5)` sends the generator carrying
  eigenvalue `ζ` from coordinate `1` to residue `3` (not `2`) modulo `5`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé XIII, §2 and
  Corollaire 2.12.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.6.12 (2).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped LaurentPolynomial PreGaloisCategory TauCeti.zHat

universe u

namespace TauCeti.FiniteEtaleScheme

/-! ### Kummer monodromy over an affine base -/

section KummerMonodromy

variable {R : CommRingCat.{u}} (t : Rˣ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- On the fibre `μ_n(Ω)` over `1` of a Kummer cover, if every `n`-th root of unity of `Ω` lifts to
an `n`-th root of unity of `R`, then an automorphism `σ` of the geometric fibre functor acts by
multiplication by the image under `σ` of the base point `1 ∈ μ_n(Ω)`: deck transformations commute
with `σ` and act transitively on `μ_n(Ω)`. -/
private theorem kummerCoverFiberEquivRootsOfUnity_smul_aux (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn ht (σ • y) =
      kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
        (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1) *
        kummerCoverFiberEquivRootsOfUnity t Ω n hn ht y := by
  let e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  obtain ⟨ζ, hζ⟩ := hdeck (e y)
  have hy : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverDeck t hn ζ).hom (e.symm 1) = y :=
    e.injective <| by
      rw [kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck, hζ, e.apply_symm_apply, mul_one]
  change e (σ • y) = e (σ • e.symm 1) * e y
  rw [← hy, PreGaloisCategory.mulAction_naturality,
    kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck, hζ, hy, mul_comm]

/-- **Level-`n` Kummer monodromy.** At a geometric point `Spec Ω ⟶ Spec R` sending the unit `t` to
`1`, when every `n`-th root of unity of `Ω` lifts to `R`, an automorphism of the geometric fibre
functor acts on the degree-`n` Kummer fibre `μ_n(Ω)` by multiplication by a root of unity, giving a
group homomorphism `Aut (fiber x) →* μ_n(Ω)`. -/
noncomputable def kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →* rootsOfUnity n Ω where
  toFun σ := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
    (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1)
  map_one' := by simp
  map_mul' σ τ := by
    rw [mul_smul, kummerCoverFiberEquivRootsOfUnity_smul_aux t Ω n hn ht hdeck σ]

/-- The level-`n` Kummer character evaluates an automorphism at the canonical point `1` of the
fibre `μ_n(Ω)`. -/
theorem kummerMonodromyLevel_apply (n : ℕ) (hn : IsUnit (n : R)) (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    kummerMonodromyLevel t Ω n hn ht hdeck σ =
      kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
        (σ • (kummerCoverFiberEquivRootsOfUnity t Ω n hn ht).symm 1) :=
  (rfl)

/-- **Action on the Kummer fibre.** Every `σ ∈ Aut (fiber x)` multiplies elements of the Kummer
fibre `μ_n(Ω)` over `1` by `kummerMonodromyLevel t Ω n hn ht hdeck σ`. -/
@[simp]
theorem kummerCoverFiberEquivRootsOfUnity_smul (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn ht (σ • y) =
      kummerMonodromyLevel t Ω n hn ht hdeck σ *
        kummerCoverFiberEquivRootsOfUnity t Ω n hn ht y :=
  kummerCoverFiberEquivRootsOfUnity_smul_aux t Ω n hn ht hdeck σ y

/-- Each finite-level Kummer character is locally constant on `Aut (fiber x)`. -/
theorem isLocallyConstant_kummerMonodromyLevel (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n)) :
    IsLocallyConstant (kummerMonodromyLevel t Ω n hn ht hdeck) := by
  let e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  have hcont : Continuous fun σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) ↦
      σ • e.symm 1 := continuous_id.smul continuous_const
  exact ((IsLocallyConstant.iff_continuous _).mpr hcont).comp e

/-- For `n ∣ m`, the level-`m` and level-`n` Kummer characters are compatible along the
`(m / n)`-th power map `μ_m(Ω) → μ_n(Ω)`. -/
theorem kummerMonodromyLevel_pow_div {n m : ℕ} (hn : IsUnit (n : R)) (hm : IsUnit (m : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck_n : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    (hdeck_m : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (h : n ∣ m) (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    (kummerMonodromyLevel t Ω m hm ht hdeck_m σ : Ωˣ) ^ (m / n) =
      kummerMonodromyLevel t Ω n hn ht hdeck_n σ := by
  let e_n := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  let e_m := kummerCoverFiberEquivRootsOfUnity t Ω m hm ht
  have hmap_one : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
      (kummerCoverMap t hn hm h) (e_m.symm 1) = e_n.symm 1 := by
    apply e_n.injective
    apply Subtype.ext
    rw [kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap, e_m.apply_symm_apply,
      e_n.apply_symm_apply]
    simp
  rw [kummerMonodromyLevel_apply,
    ← kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap t hn hm ht h,
    ← PreGaloisCategory.mulAction_naturality, hmap_one]
  rfl

/-- Over a connected base `Spec R`, if the degree-`n` Kummer cover is connected, then the level-`n`
Kummer character is surjective: `Aut (fiber x)` acts transitively on the fibre of a connected
cover. -/
theorem kummerMonodromyLevel_surjective [ConnectedSpace (Spec R)] (n : ℕ) (hn : IsUnit (n : R))
    (ht : algebraMap R Ω t = 1)
    (hdeck : Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) n))
    [PreGaloisCategory.IsConnected (kummerCover t n hn)] :
    Function.Surjective (kummerMonodromyLevel t Ω n hn ht hdeck) := fun ζ ↦ by
  let e := kummerCoverFiberEquivRootsOfUnity t Ω n hn ht
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq
    (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (e.symm 1) (e.symm ζ)
  exact ⟨σ, by rw [kummerMonodromyLevel_apply, hσ, e.apply_symm_apply]⟩

/-- **Assembled Kummer monodromy.** The compatible finite-level Kummer characters assemble into a
continuous group homomorphism `Aut (fiber x) →ₜ* PrimeToPTateModule p Ω`. -/
noncomputable def kummerMonodromy (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m)) :
    Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) →ₜ* PrimeToPTateModule p Ω where
  toMonoidHom := PrimeToPTateModule.lift
    (fun m ↦ kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m))
    fun m n σ h ↦ kummerMonodromyLevel_pow_div t Ω (hunit n) (hunit m) ht (hdeck n) (hdeck m) h σ
  continuous_toFun := PrimeToPTateModule.continuous_iff.mpr fun m ↦ by
    simpa only [MonoidHom.toFun_eq_coe, PrimeToPTateModule.proj_lift] using
      isLocallyConstant_kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m)

/-- Projecting `kummerMonodromy` to level `m` recovers `kummerMonodromyLevel`. -/
@[simp]
theorem proj_kummerMonodromy (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (σ : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) :
    PrimeToPTateModule.proj m (kummerMonodromy t Ω p ht hunit hdeck σ) =
      kummerMonodromyLevel t Ω m (hunit m) ht (hdeck m) σ :=
  PrimeToPTateModule.proj_lift _ _ m σ

/-- Over a connected base `Spec R`, if all prime-to-`p` Kummer covers along `t` are connected, then
`kummerMonodromy` is surjective onto `PrimeToPTateModule p Ω`. -/
theorem kummerMonodromy_surjective [ConnectedSpace (Spec R)] (p : ℕ) (ht : algebraMap R Ω t = 1)
    (hunit : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}, IsUnit ((m : ℕ) : R))
    (hdeck : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      Function.Surjective (restrictRootsOfUnity (algebraMap R Ω) m))
    (hconn : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime p},
      PreGaloisCategory.IsConnected (kummerCover t m (hunit m))) :
    Function.Surjective (kummerMonodromy t Ω p ht hunit hdeck) :=
  PrimeToPTateModule.surjective_of_forall_surjective_proj
    (kummerMonodromy t Ω p ht hunit hdeck).continuous fun m ↦ by
      have := hconn m
      simpa only [proj_kummerMonodromy] using
        kummerMonodromyLevel_surjective t Ω m (hunit m) ht (hdeck m)

end KummerMonodromy

/-! ### The multiplicative group `𝔾_{m, K}` -/

section MultiplicativeGroup

variable (K : Type u)

/-- **The base point `1` of `𝔾_{m, K} = Spec K[T, T⁻¹]`** valued in a `K`-algebra `Ω`, induced by
evaluating Laurent polynomials at `1 ∈ Ωˣ`. -/
noncomputable def multiplicativeGroupOnePoint [CommRing K] (Ω : Type u) [CommRing Ω] [Algebra K Ω] :
    Spec (.of Ω) ⟶ Spec (.of K[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (laurentEval (R := K) (1 : Ωˣ)).toRingHom)

private theorem algebraMap_laurentEval_one_genericUnit [CommRing K] (Ω : Type u) [CommRing Ω]
    [Algebra K Ω] :
    letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
    algebraMap K[T;T⁻¹] Ω (LaurentPolynomial.genericUnit K) = 1 := by
  let _ : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    LaurentPolynomial.genericUnit_val, laurentEval_T_one, Units.val_one]

variable [Field K]

/-- A natural number nonzero in a field `K` is invertible in `K[T, T⁻¹]`. -/
theorem isUnit_natCast_laurentPolynomial {n : ℕ} (hn : (n : K) ≠ 0) :
    IsUnit (n : (CommRingCat.of K[T;T⁻¹])) := by
  simpa using (IsUnit.mk0 (n : K) hn).map (LaurentPolynomial.C : K →+* K[T;T⁻¹])

/-- Over a field `K` of exponential characteristic `p`, every nonzero `m` coprime to `p` is
nonzero in `K`, hence invertible in `K[T, T⁻¹]`. -/
theorem isUnit_natCast_laurentPolynomial_of_coprime (p : ℕ) [ExpChar K p]
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    IsUnit ((m : ℕ) : (CommRingCat.of K[T;T⁻¹])) := by
  apply isUnit_natCast_laurentPolynomial K
  obtain _ | ⟨hq⟩ := ‹ExpChar K p›
  · exact Nat.cast_ne_zero.mpr m.2.1
  · rw [ne_eq, CharP.cast_eq_zero_iff K _ m]
    intro hdvd
    exact hq.not_dvd_one (m.2.2 ▸ Nat.dvd_gcd hdvd (dvd_refl _))

/-- **Connectedness of Kummer covers of `𝔾_{m, K}`.** For any field `K` and any `n` invertible in
`K[T, T⁻¹]`, the power cover `Spec K[T, T⁻¹][x]/(x ^ n - T) ⟶ 𝔾_{m, K}` is a connected object of
`FiniteEtaleScheme (Spec K[T, T⁻¹])`: its coordinate algebra is an integral domain
(`TauCeti.isDomain_standardTameCover_laurentPolynomial_T`). -/
instance isConnected_kummerCover_genericUnit {n : ℕ}
    (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))) :
    PreGaloisCategory.IsConnected
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn) := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hdom :
      IsDomain (standardTameCover K[T;T⁻¹] (LaurentPolynomial.genericUnit K : K[T;T⁻¹]) n) := by
    rw [LaurentPolynomial.genericUnit_val]
    exact isDomain_standardTameCover_laurentPolynomial_T K hn₀
  exact (isConnected_spec_obj_iff (.of K[T;T⁻¹])
    (kummerAlgebra (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)).mpr inferInstance

/-- **The fibre over `1` of the degree-`n` power cover of `𝔾_{m, K}` is `μ_n(Ω)`.** -/
noncomputable def multiplicativeGroupPowerCoverFiberEquiv (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (n : ℕ) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))) :
    (fiber (multiplicativeGroupOnePoint K Ω)).obj
        (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn) ≃
      rootsOfUnity n Ω :=
  letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  kummerCoverFiberEquivRootsOfUnity (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) Ω n hn
    (algebraMap_laurentEval_one_genericUnit K Ω)

/-- Over a separably closed `K`-algebra `Ω`, the geometric fibre over `1` of the degree-`n` power
cover of `𝔾_{m, K}` has cardinality `n` whenever `(n : Ω) ≠ 0` (for example whenever `n` is
invertible in `K[T, T⁻¹]`). -/
theorem card_multiplicativeGroupPowerCoverFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (n : ℕ) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))) :
    Nat.card ((fiber (multiplicativeGroupOnePoint K Ω)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)) = n := by
  have hnΩ : (n : Ω) ≠ 0 := by
    have hu : IsUnit (n : Ω) := by
      simpa using hn.map (laurentEval (R := K) (1 : Ωˣ)).toRingHom
    exact hu.ne_zero
  have : NeZero (n : Ω) := ⟨hnΩ⟩
  have : NeZero n := .of_neZero_natCast Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  rw [Nat.card_congr (multiplicativeGroupPowerCoverFiberEquiv K Ω n hn)]
  exact hζ.card_rootsOfUnity

/-- Evaluation at `1` induces a surjective map `μ_n(K[T, T⁻¹]) → μ_n(K)`, split by the constant
inclusion `C : K →+* K[T, T⁻¹]`. -/
private theorem restrictRootsOfUnity_laurentEval_one_surjective (n : ℕ) :
    Function.Surjective
      (restrictRootsOfUnity (laurentEval (R := K) (1 : Kˣ)).toRingHom n) := fun ζ ↦
  ⟨restrictRootsOfUnity (LaurentPolynomial.C : K →+* K[T;T⁻¹]) n ζ, by
    ext
    change laurentEval (R := K) (1 : Kˣ) (LaurentPolynomial.C ((ζ : Kˣ) : K)) = _
    simp⟩

section SepClosed

variable [IsSepClosed K]

/-- **The prime-to-`p` Tate monodromy of `𝔾_{m, K}`** over a separably closed field `K` of
exponential characteristic `p`: the continuous homomorphism
`π₁^ét(𝔾_{m, K}, 1) →ₜ* PrimeToPTateModule p K` sending `σ` to its eigenvalues on the Kummer power
covers of prime-to-`p` degree. -/
noncomputable def multiplicativeGroupPrimeToPMonodromy (p : ℕ) [ExpChar K p] :
    Aut (fiber (multiplicativeGroupOnePoint K K)) →ₜ* PrimeToPTateModule p K :=
  letI : Algebra K[T;T⁻¹] K := (laurentEval (R := K) (1 : Kˣ)).toRingHom.toAlgebra
  kummerMonodromy (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
    (algebraMap_laurentEval_one_genericUnit K K)
    (isUnit_natCast_laurentPolynomial_of_coprime K p)
    fun m ↦ restrictRootsOfUnity_laurentEval_one_surjective K m

/-- On the degree-`m` power cover of `𝔾_{m, K}`, an automorphism `σ ∈ π₁^ét(𝔾_{m, K}, 1)` multiplies
points of the fibre `μ_m(K)` over `1` by the level-`m` projection of
`multiplicativeGroupPrimeToPMonodromy K p σ`. -/
@[simp]
theorem multiplicativeGroupPowerCoverFiberEquiv_smul (p : ℕ) [ExpChar K p]
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (hn : IsUnit ((m : ℕ) : (CommRingCat.of K[T;T⁻¹])))
    (σ : Aut (fiber (multiplicativeGroupOnePoint K K)))
    (y : (fiber (multiplicativeGroupOnePoint K K)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) m hn)) :
    multiplicativeGroupPowerCoverFiberEquiv K K m hn (σ • y) =
      PrimeToPTateModule.proj m (multiplicativeGroupPrimeToPMonodromy K p σ) *
        multiplicativeGroupPowerCoverFiberEquiv K K m hn y := by
  let _ : Algebra K[T;T⁻¹] K := (laurentEval (R := K) (1 : Kˣ)).toRingHom.toAlgebra
  refine (kummerCoverFiberEquivRootsOfUnity_smul (R := .of K[T;T⁻¹])
    (LaurentPolynomial.genericUnit K) K m hn
    (algebraMap_laurentEval_one_genericUnit K K)
    (restrictRootsOfUnity_laurentEval_one_surjective K m) σ y).trans ?_
  exact congrArg (· * multiplicativeGroupPowerCoverFiberEquiv K K m hn y)
    (proj_kummerMonodromy (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
      (algebraMap_laurentEval_one_genericUnit K K)
      (isUnit_natCast_laurentPolynomial_of_coprime K p)
      (fun m ↦ restrictRootsOfUnity_laurentEval_one_surjective K m) m σ).symm

/-- **Surjectivity of the prime-to-`p` monodromy of `𝔾_{m, K}`** over any separably closed field `K`
of exponential characteristic `p`. -/
theorem multiplicativeGroupPrimeToPMonodromy_surjective (p : ℕ) [ExpChar K p] :
    Function.Surjective (multiplicativeGroupPrimeToPMonodromy K p) := by
  let _ : Algebra K[T;T⁻¹] K := (laurentEval (R := K) (1 : Kˣ)).toRingHom.toAlgebra
  exact kummerMonodromy_surjective (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
    (algebraMap_laurentEval_one_genericUnit K K)
    (isUnit_natCast_laurentPolynomial_of_coprime K p)
    (fun m ↦ restrictRootsOfUnity_laurentEval_one_surjective K m)
    fun m ↦ inferInstance

end SepClosed

/-! ### Classification and fundamental group in characteristic zero -/

section AlgClosedCharZero

variable [IsAlgClosed K] [CharZero K]

/-- **Geometric classification of connected finite étale covers of `𝔾_{m, K}`.** Over an
algebraically closed field `K` of characteristic zero, every connected finite étale scheme over
`𝔾_{m, K} = Spec K[T, T⁻¹]` is isomorphic to the degree-`n` Kummer power cover for some `n ≠ 0`. -/
theorem exists_iso_kummerCover_of_isConnected
    (X : FiniteEtaleScheme (Spec (.of K[T;T⁻¹]))) [PreGaloisCategory.IsConnected X] :
    ∃ (n : ℕ) (_ : n ≠ 0) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))),
      Nonempty (X ≅ kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn) := by
  obtain ⟨⟨A⟩, ⟨e⟩⟩ := (essSurj_spec (R := .of K[T;T⁻¹])).mem_essImage X
  have hconnSpec : PreGaloisCategory.IsConnected ((spec (.of K[T;T⁻¹])).obj (op A)) :=
    PreGaloisCategory.IsConnected.of_iso e.symm
  have : ConnectedSpace (PrimeSpectrum A.obj) :=
    (isConnected_spec_obj_iff (.of K[T;T⁻¹]) A).mp hconnSpec
  obtain ⟨n, hn₀, ⟨φ⟩⟩ := exists_algEquiv_standardTameCover_of_etale K A.obj
  have hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹])) :=
    isUnit_natCast_laurentPolynomial K (Nat.cast_ne_zero.mpr hn₀)
  let φ' :
      (kummerAlgebra (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn).obj ≃ₐ[K[T;T⁻¹]]
        A.obj :=
    (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : K[T;T⁻¹] ≃ₐ[K[T;T⁻¹]] K[T;T⁻¹]) _ _
      (.of_eq (by simp))).trans φ
  let isoAlg : kummerAlgebra (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn ≅ A :=
    CommAlgCat.FiniteEtale.isoMk φ'
  exact ⟨n, hn₀, hn, ⟨e.symm ≪≫ (spec (.of K[T;T⁻¹])).mapIso isoAlg.op⟩⟩

/-- Over an algebraically closed field `K` of characteristic zero, the Tate monodromy homomorphism
`π₁^ét(𝔾_{m, K}, 1) →ₜ* PrimeToPTateModule 1 K` is injective: every connected finite étale cover is
isomorphic to a Kummer cover, and every finite étale cover is covered by its connected
components. -/
theorem multiplicativeGroupPrimeToPMonodromy_injective :
    Function.Injective (multiplicativeGroupPrimeToPMonodromy K 1) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hkummer : ∀ (n : ℕ) (_ : n ≠ 0) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹])))
      (y : (fiber (multiplicativeGroupOnePoint K K)).obj
        (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)),
      σ • y = y := fun n hn₀ hn y ↦ by
    let m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} := ⟨n, hn₀, Nat.coprime_one_right n⟩
    apply (multiplicativeGroupPowerCoverFiberEquiv K K n hn).injective
    have hm := multiplicativeGroupPowerCoverFiberEquiv_smul K 1 m hn σ y
    rw [hσ, map_one, one_mul] at hm
    exact hm
  have hconn : ∀ (Y : FiniteEtaleScheme (Spec (.of K[T;T⁻¹])))
      [PreGaloisCategory.IsConnected Y]
      (y : (fiber (multiplicativeGroupOnePoint K K)).obj Y), σ • y = y := fun Y _ y ↦ by
    obtain ⟨n, hn₀, hn, ⟨iso⟩⟩ := exists_iso_kummerCover_of_isConnected K Y
    have hinj : Function.Injective ((fiber (multiplicativeGroupOnePoint K K)).map iso.hom) :=
      fun a b hab ↦ by
        have := congrArg ((fiber (multiplicativeGroupOnePoint K K)).map iso.inv) hab
        simpa [← Functor.map_comp_apply] using this
    apply hinj
    rw [← PreGaloisCategory.mulAction_naturality, hkummer n hn₀ hn]
  ext X z
  obtain ⟨Y, i, y, rfl, hY, _⟩ :=
    PreGaloisCategory.fiber_in_connected_component (fiber (multiplicativeGroupOnePoint K K)) X z
  change σ • (fiber (multiplicativeGroupOnePoint K K)).map i y =
    (fiber (multiplicativeGroupOnePoint K K)).map i y
  rw [PreGaloisCategory.mulAction_naturality, hconn Y y]

/-- **The étale fundamental group of `𝔾_{m, K}` is its Tate module `lim_n μ_n(K)`.** Over an
algebraically closed field `K` of characteristic zero, `multiplicativeGroupPrimeToPMonodromy K 1` is
a canonical, root-choice-free isomorphism of topological groups
`π₁^ét(𝔾_{m, K}, 1) ≃ₜ* PrimeToPTateModule 1 K`. -/
noncomputable def multiplicativeGroupAutFiberContinuousMulEquivTateModule :
    Aut (fiber (multiplicativeGroupOnePoint K K)) ≃ₜ* PrimeToPTateModule 1 K :=
  let e : Aut (fiber (multiplicativeGroupOnePoint K K)) ≃* PrimeToPTateModule 1 K :=
    MulEquiv.ofBijective (multiplicativeGroupPrimeToPMonodromy K 1).toMonoidHom
      ⟨multiplicativeGroupPrimeToPMonodromy_injective K,
        multiplicativeGroupPrimeToPMonodromy_surjective K 1⟩
  { e with
    continuous_toFun := (multiplicativeGroupPrimeToPMonodromy K 1).continuous
    continuous_invFun :=
      (multiplicativeGroupPrimeToPMonodromy K 1).continuous.continuous_symm_of_equiv_compact_to_t2
        (f := e.toEquiv) }

/-- `multiplicativeGroupAutFiberContinuousMulEquivTateModule` agrees with
`multiplicativeGroupPrimeToPMonodromy K 1`. -/
@[simp]
theorem multiplicativeGroupAutFiberContinuousMulEquivTateModule_apply
    (σ : Aut (fiber (multiplicativeGroupOnePoint K K))) :
    multiplicativeGroupAutFiberContinuousMulEquivTateModule K σ =
      multiplicativeGroupPrimeToPMonodromy K 1 σ :=
  (rfl)

/-- **The `ℤ̂`-coordinate isomorphism of `π₁^ét(𝔾_{m, K}, 1)`** attached to a compatible system
`ζ = (ζ_n)_n` of primitive roots of unity in `K`. Unlike
`multiplicativeGroupAutFiberContinuousMulEquivTateModule`, this isomorphism depends on the choice of
`ζ`. -/
noncomputable def multiplicativeGroupAutFiberContinuousMulEquivZHat
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m) :
    Aut (fiber (multiplicativeGroupOnePoint K K)) ≃ₜ* zHat.{u} :=
  (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).trans
    (PrimeToPTateModule.continuousMulEquivZHat ζ hζ)

/-- Composing the coordinate isomorphism with the inverse parametrization recovers the intrinsic,
root-choice-free Tate-module isomorphism regardless of which compatible primitive family `ζ` was
chosen. -/
@[simp]
theorem multiplicativeGroupAutFiberContinuousMulEquivZHat_trans_symm
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m) :
    (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).trans
        (PrimeToPTateModule.continuousMulEquivZHat ζ hζ).symm =
      multiplicativeGroupAutFiberContinuousMulEquivTateModule K := by
  ext σ
  simp [multiplicativeGroupAutFiberContinuousMulEquivZHat]

/-- **Action of `ℤ̂` on the finite Kummer fibres through `ℤ̂ → ℤ/nℤ`.** Once a compatible primitive
family `ζ = (ζ_n)_n` is fixed, the automorphism parametrized by `a ∈ ℤ̂` multiplies points of the
degree-`n` power fibre `μ_n(K)` over `1` by `ζ_n ^ (a mod n)`. -/
theorem multiplicativeGroupPowerCoverFiberEquiv_symm_zHat_smul
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : (CommRingCat.of K[T;T⁻¹])))
    (a : zHat.{u})
    (y : (fiber (multiplicativeGroupOnePoint K K)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)) :
    (multiplicativeGroupPowerCoverFiberEquiv K K n hn
        ((multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).symm a • y) : Kˣ) =
      (PrimeToPTateModule.proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Kˣ) ^
        (zHat.toZMod n (Additive.ofMul a)).val *
        (multiplicativeGroupPowerCoverFiberEquiv K K n hn y : Kˣ) := by
  let m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} := ⟨n, n.ne_zero, Nat.coprime_one_right _⟩
  have hsmul := congrArg ((↑) : rootsOfUnity n K → Kˣ)
    (multiplicativeGroupPowerCoverFiberEquiv_smul K 1 m hn
      ((multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).symm a) y)
  rw [Subgroup.coe_mul] at hsmul
  refine hsmul.trans ?_
  congr 1
  have h1 : multiplicativeGroupPrimeToPMonodromy K 1
      ((multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).symm a) = zHat.lift ζ a := by
    change multiplicativeGroupAutFiberContinuousMulEquivTateModule K
      ((multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm
        ((PrimeToPTateModule.continuousMulEquivZHat ζ hζ).symm a)) = zHat.lift ζ a
    rw [ContinuousMulEquiv.apply_symm_apply, PrimeToPTateModule.continuousMulEquivZHat_symm_apply]
  rw [h1]
  exact PrimeToPTateModule.coe_proj_zHatLift ζ n a

end AlgClosedCharZero

end MultiplicativeGroup

/-! ### Basis change and complex specialization -/

section BasisChangeAndComplex

open Additive

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- **Basis change for the parametrization `ℤ̂ ≃ₜ* π₁^ét(𝔾_{m, K}, 1)`.** Replacing `ζ` by `ζ ^ᶻ u`
(`u ∈ ℤ̂ˣ`) precomposes the parametrization with multiplication by `u`. -/
theorem multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_zpowHat
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (u : (Additive zHat.{u})ˣ) (a : Additive zHat.{u}) :
    (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
        (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u)).symm (toMul a) =
      (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).symm
        (toMul ((u : Additive zHat.{u}) * a)) := by
  simp only [multiplicativeGroupAutFiberContinuousMulEquivZHat, ContinuousMulEquiv.symm_trans_apply,
    PrimeToPTateModule.continuousMulEquivZHat_zpowHat_symm_apply hζ u a]

/-- **Basis change for the coordinate map `π₁^ét(𝔾_{m, K}, 1) ≃ₜ* ℤ̂`.** Replacing `ζ` by `ζ ^ᶻ u`
(`u ∈ ℤ̂ˣ`) multiplies the `ℤ̂`-coordinate of every `σ ∈ π₁^ét(𝔾_{m, K}, 1)` by `u⁻¹`. -/
theorem ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (u : (Additive zHat.{u})ˣ)
    (σ : Aut (fiber (multiplicativeGroupOnePoint K K))) :
    ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
        (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u) σ) =
      ((u⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}) *
        ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ σ) := by
  simp only [multiplicativeGroupAutFiberContinuousMulEquivZHat, ContinuousMulEquiv.trans_apply,
    PrimeToPTateModule.ofMul_continuousMulEquivZHat_zpowHat_apply hζ u]

/-- **Mod-`5` coordinate check on `π₁^ét(𝔾_{m, K}, 1)`.** For any profinite unit `u` with
`u ≡ 2 (mod 5)`, the generator `(multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ`
has coordinate `1` in the `ζ`-basis and residue `3` (not `2`) modulo `5` in the rescaled
`(ζ ^ᶻ u)`-basis. -/
theorem toZMod_five_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    {u : (Additive zHat.{u})ˣ} (hu : zHat.toZMod 5 (u : Additive zHat.{u}) = 2) :
    let γ := (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ
    ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ γ) = 1 ∧
      zHat.toZMod 5
        (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
          (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u) γ)) = 3 ∧
      zHat.toZMod 5
        (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
          (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u) γ)) ≠ 2 := by
  simpa only [multiplicativeGroupAutFiberContinuousMulEquivZHat, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    PrimeToPTateModule.toZMod_five_continuousMulEquivZHat_zpowHat_self hζ hu

/-- **The étale fundamental group of `𝔾_{m, ℂ}` at `1` is `ℤ̂`** via the standard compatible system
of complex primitive roots of unity `ζ_n = exp(2πi / n)` (`PrimeToPTateModule.complexExp 1`). -/
noncomputable def complexMultiplicativeGroupAutFiberContinuousMulEquivZHat :
    Aut (fiber (multiplicativeGroupOnePoint ℂ ℂ)) ≃ₜ* zHat.{0} :=
  multiplicativeGroupAutFiberContinuousMulEquivZHat ℂ
    (PrimeToPTateModule.complexExp 1)
    (PrimeToPTateModule.isPrimitiveRoot_proj_complexExp 1)

/-- Over `ℂ`, under `complexMultiplicativeGroupAutFiberContinuousMulEquivZHat`, an element `a ∈ ℤ̂`
acts on the fibre `μ_n(ℂ)` over `1` of the degree-`n` power cover of `𝔾_{m, ℂ}` through the
reduction `ℤ̂ → ℤ/nℤ`, multiplying by `exp(2πi / n) ^ (a mod n)`. -/
theorem complexMultiplicativeGroupPowerCoverFiberEquiv_symm_zHat_smul
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : (CommRingCat.of ℂ[T;T⁻¹])))
    (a : zHat.{0})
    (y : (fiber (multiplicativeGroupOnePoint ℂ ℂ)).obj
      (kummerCover (R := .of ℂ[T;T⁻¹]) (LaurentPolynomial.genericUnit ℂ) n hn)) :
    ((multiplicativeGroupPowerCoverFiberEquiv ℂ ℂ n hn
        (complexMultiplicativeGroupAutFiberContinuousMulEquivZHat.symm a • y) : ℂˣ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / n) ^ (zHat.toZMod n (ofMul a)).val *
        ((multiplicativeGroupPowerCoverFiberEquiv ℂ ℂ n hn y : ℂˣ) : ℂ) := by
  have h := congrArg (Units.val : ℂˣ → ℂ)
    (multiplicativeGroupPowerCoverFiberEquiv_symm_zHat_smul ℂ
      (PrimeToPTateModule.complexExp 1)
      (PrimeToPTateModule.isPrimitiveRoot_proj_complexExp 1) n hn a y)
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    PrimeToPTateModule.coe_proj_complexExp 1 ⟨n, n.ne_zero, Nat.coprime_one_right _⟩] at h
  exact h

end BasisChangeAndComplex

end TauCeti.FiniteEtaleScheme
