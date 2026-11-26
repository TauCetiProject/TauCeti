/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Connected
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Kummer
public import TauCeti.RingTheory.RootsOfUnity.TateModule.Complex

import TauCeti.Algebra.Polynomial.Laurent.Units
import TauCeti.CategoryTheory.Galois.Connected
import TauCeti.RingTheory.Etale.LaurentPolynomial
import TauCeti.RingTheory.RootsOfUnity.TateModule.BasisChange
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units

/-!
# The étale fundamental group of the multiplicative group

Let `K` be an algebraically closed field of characteristic zero, `𝔾_{m, K} = Spec K[T, T⁻¹]` the
multiplicative group over `K`, and `1 : Spec K ⟶ 𝔾_{m, K}` the rational point sending `T` to `1`.
This file identifies the étale fundamental group `π₁^ét(𝔾_{m, K}, 1)` — the automorphism group
`Aut (FiniteEtaleScheme.fiber (multiplicativeGroupOnePoint K K))` of the geometric fibre functor at
`1` — canonically with the Tate module `PrimeToPTateModule 1 K = lim_n μ_n(K)` as topological
groups (`TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivTateModule`).

Building on the general affine-base Kummer monodromy construction in
`TauCeti/AlgebraicGeometry/FiniteEtale/Galois/Kummer.lean` (`kummerMonodromyLevel`,
`kummerMonodromy`, `kummerCoverFiberEquivRootsOfUnity_smul`) and on the fibre count
`card_kummerCoverFiber` of `TauCeti/AlgebraicGeometry/FiniteEtale/Kummer.lean`, the
identification proceeds in two stages so that each hypothesis enters only where needed:

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

* `TauCeti.FiniteEtaleScheme.card_multiplicativeGroupPowerCoverFiber`: the fibre over `1` of a
  degree-`n` power cover of `𝔾_{m, K}` has cardinality `n`.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupPrimeToPMonodromy_surjective`: surjectivity of the
  prime-to-`p` monodromy of `𝔾_{m, K}` over any separably closed field.
* `TauCeti.FiniteEtaleScheme.exists_iso_kummerCover_of_isConnected`: every connected finite étale
  cover of `𝔾_{m, K}` over an algebraically closed field of characteristic zero is isomorphic to a
  Kummer power cover.
* `TauCeti.FiniteEtaleScheme.multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_zpowHat`,
  `TauCeti.FiniteEtaleScheme.ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat`, and
  `TauCeti.FiniteEtaleScheme.toZMod_ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat`
  show that replacing `ζ` by `ζ ^ᶻ u` composes the parametrization with multiplication by `u`,
  composes the coordinate map with multiplication by `u⁻¹`, and reduces the generator's coordinate
  modulo `n` to `(u mod n)⁻¹`.

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

/-! ### The multiplicative group `𝔾_{m, K}` -/

section MultiplicativeGroup

variable (K : Type u)

section CommRing

variable [CommRing K]

/-- **The base point `1` of `𝔾_{m, K} = Spec K[T, T⁻¹]`** valued in a `K`-algebra `Ω`, induced by
evaluating Laurent polynomials at `1 ∈ Ωˣ`. -/
noncomputable def multiplicativeGroupOnePoint (Ω : Type u) [CommRing Ω] [Algebra K Ω] :
    Spec (.of Ω) ⟶ Spec (.of K[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (laurentEval (R := K) (1 : Ωˣ)).toRingHom)

/-- `multiplicativeGroupOnePoint K Ω` is `Spec` of evaluation of Laurent polynomials at `1`. -/
theorem multiplicativeGroupOnePoint_def (Ω : Type u) [CommRing Ω] [Algebra K Ω] :
    multiplicativeGroupOnePoint K Ω =
      Spec.map (CommRingCat.ofHom (laurentEval (R := K) (1 : Ωˣ)).toRingHom) :=
  (rfl)

/-- **The fibre over `1` of the degree-`n` power cover of `𝔾_{m, K}` is `μ_n(Ω)`.** -/
noncomputable def multiplicativeGroupPowerCoverFiberEquiv (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (n : ℕ) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))) :
    (fiber (multiplicativeGroupOnePoint K Ω)).obj
        (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn) ≃
      rootsOfUnity n Ω :=
  letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  kummerCoverFiberEquivRootsOfUnity (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) Ω n hn
    (laurentEval_genericUnit (R := K) (1 : Ωˣ))

/-- On the fibres `μ_n(Ω)` over `1` of the power covers of `𝔾_{m, K}`, the map from degree `m` to
degree `n ∣ m` is the power map `ζ ↦ ζ ^ (m / n)`. -/
@[simp]
theorem multiplicativeGroupPowerCoverFiberEquiv_map_kummerCoverMap (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra K Ω] {n m : ℕ}
    (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹])))
    (hm : IsUnit (m : (CommRingCat.of K[T;T⁻¹]))) (hd : n ∣ m)
    (y : (fiber (multiplicativeGroupOnePoint K Ω)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) m hm)) :
    (multiplicativeGroupPowerCoverFiberEquiv K Ω n hn
        ((fiber (multiplicativeGroupOnePoint K Ω)).map
          (kummerCoverMap (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) hn hm hd) y) :
      Ωˣ) =
      (multiplicativeGroupPowerCoverFiberEquiv K Ω m hm y : Ωˣ) ^ (m / n) :=
  letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap (R := .of K[T;T⁻¹])
    (LaurentPolynomial.genericUnit K) hn hm (laurentEval_genericUnit (R := K) (1 : Ωˣ)) hd y

/-- On the fibre `μ_n(Ω)` over `1` of the degree-`n` power cover of `𝔾_{m, K}`, the deck
transformation of `ζ : rootsOfUnity n K[T;T⁻¹]` multiplies by its evaluation at `1`. -/
@[simp]
theorem multiplicativeGroupPowerCoverFiberEquiv_map_kummerCoverDeck (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] [Algebra K Ω] (n : ℕ) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹])))
    (ζ : rootsOfUnity n K[T;T⁻¹])
    (y : (fiber (multiplicativeGroupOnePoint K Ω)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)) :
    multiplicativeGroupPowerCoverFiberEquiv K Ω n hn
        ((fiber (multiplicativeGroupOnePoint K Ω)).map
          (kummerCoverDeck (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) hn ζ).hom y) =
      restrictRootsOfUnity (laurentEval (R := K) (1 : Ωˣ)).toRingHom n ζ *
        multiplicativeGroupPowerCoverFiberEquiv K Ω n hn y :=
  letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck (R := .of K[T;T⁻¹])
    (LaurentPolynomial.genericUnit K) hn (laurentEval_genericUnit (R := K) (1 : Ωˣ)) ζ y

/-- Over a separably closed `K`-algebra `Ω`, the geometric fibre over `1` of the degree-`n` power
cover of `𝔾_{m, K}` has cardinality `n` whenever `n` is invertible in `K[T, T⁻¹]`. -/
theorem card_multiplicativeGroupPowerCoverFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] (n : ℕ) (hn : IsUnit (n : (CommRingCat.of K[T;T⁻¹]))) :
    Nat.card ((fiber (multiplicativeGroupOnePoint K Ω)).obj
      (kummerCover (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) n hn)) = n :=
  letI : Algebra K[T;T⁻¹] Ω := (laurentEval (R := K) (1 : Ωˣ)).toRingHom.toAlgebra
  card_kummerCoverFiber (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) Ω n hn

end CommRing

variable [Field K]

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
    (fun m ↦ LaurentPolynomial.isUnit_natCast_of_coprime m.property.1 m.property.2)
    fun m ↦ restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m

/-- The level-`m` component of `multiplicativeGroupPrimeToPMonodromy K p σ` is the image of the
base point `1 ∈ μ_m(K)` under `σ`. -/
theorem proj_multiplicativeGroupPrimeToPMonodromy (p : ℕ) [ExpChar K p]
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p})
    (hn : IsUnit ((m : ℕ) : (CommRingCat.of K[T;T⁻¹])))
    (σ : Aut (fiber (multiplicativeGroupOnePoint K K))) :
    PrimeToPTateModule.proj m (multiplicativeGroupPrimeToPMonodromy K p σ) =
      multiplicativeGroupPowerCoverFiberEquiv K K m hn
        (σ • (multiplicativeGroupPowerCoverFiberEquiv K K m hn).symm 1) := by
  let _ : Algebra K[T;T⁻¹] K := (laurentEval (R := K) (1 : Kˣ)).toRingHom.toAlgebra
  exact (proj_kummerMonodromy (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
    (fun m ↦ LaurentPolynomial.isUnit_natCast_of_coprime m.property.1 m.property.2)
    (fun m ↦ restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m) m σ).trans
    (kummerMonodromyLevel_apply (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K m hn
      (laurentEval_genericUnit (R := K) (1 : Kˣ))
      (restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m) σ)

/-- On the degree-`m` power cover of `𝔾_{m, K}`, an automorphism `σ ∈ π₁^ét(𝔾_{m, K}, 1)` multiplies
points of the fibre `μ_m(K)` over `1` by the level-`m` projection of
`multiplicativeGroupPrimeToPMonodromy K p σ`. -/
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
    (laurentEval_genericUnit (R := K) (1 : Kˣ))
    (restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m) σ y).trans ?_
  exact congrArg (· * multiplicativeGroupPowerCoverFiberEquiv K K m hn y)
    (proj_kummerMonodromy (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
      (fun m ↦ LaurentPolynomial.isUnit_natCast_of_coprime m.property.1 m.property.2)
      (fun m ↦ restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m) m σ).symm

/-- **Surjectivity of the prime-to-`p` monodromy of `𝔾_{m, K}`** over any separably closed field `K`
of exponential characteristic `p`. -/
theorem multiplicativeGroupPrimeToPMonodromy_surjective (p : ℕ) [ExpChar K p] :
    Function.Surjective (multiplicativeGroupPrimeToPMonodromy K p) := by
  let _ : Algebra K[T;T⁻¹] K := (laurentEval (R := K) (1 : Kˣ)).toRingHom.toAlgebra
  exact kummerMonodromy_surjective (R := .of K[T;T⁻¹]) (LaurentPolynomial.genericUnit K) K p
    (fun m ↦ LaurentPolynomial.isUnit_natCast_of_coprime m.property.1 m.property.2)
    (fun m ↦ restrictRootsOfUnity_laurentEval_surjective (1 : Kˣ) m)
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
    LaurentPolynomial.isUnit_natCast.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn₀))
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
  rw [← PreGaloisCategory.mulAction_def, PreGaloisCategory.mulAction_naturality, hconn Y y]
  simp

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

/-- Evaluating `multiplicativeGroupAutFiberContinuousMulEquivZHat` applies
`PrimeToPTateModule.continuousMulEquivZHat` to `multiplicativeGroupPrimeToPMonodromy K 1`. -/
@[simp]
theorem multiplicativeGroupAutFiberContinuousMulEquivZHat_apply
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (σ : Aut (fiber (multiplicativeGroupOnePoint K K))) :
    multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ σ =
      PrimeToPTateModule.continuousMulEquivZHat ζ hζ
        (multiplicativeGroupPrimeToPMonodromy K 1 σ) :=
  (rfl)

/-- The inverse of `multiplicativeGroupAutFiberContinuousMulEquivZHat` sends `a ∈ ℤ̂` to the
automorphism corresponding to `zHat.lift ζ a` under the Tate-module isomorphism. -/
@[simp]
theorem multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_apply
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (a : zHat.{u}) :
    (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ).symm a =
      (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm (zHat.lift ζ a) :=
  congrArg (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm
    (PrimeToPTateModule.continuousMulEquivZHat_symm_apply hζ a)

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
  simp

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
  rw [multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_apply,
    ← multiplicativeGroupAutFiberContinuousMulEquivTateModule_apply,
    ContinuousMulEquiv.apply_symm_apply]
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
  rw [multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_apply,
    multiplicativeGroupAutFiberContinuousMulEquivZHat_symm_apply,
    ← PrimeToPTateModule.continuousMulEquivZHat_symm_apply
      (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u),
    ← PrimeToPTateModule.continuousMulEquivZHat_symm_apply hζ,
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
  rw [multiplicativeGroupAutFiberContinuousMulEquivZHat_apply,
    multiplicativeGroupAutFiberContinuousMulEquivZHat_apply,
    PrimeToPTateModule.ofMul_continuousMulEquivZHat_zpowHat_apply hζ u]

/-- **Mod-`n` coordinate of the generator in a rescaled basis.** For every `n : ℕ+` and
`u ∈ (Additive zHat)ˣ`, the generator
`γ = (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ` has residue `(u mod n)⁻¹`
modulo `n` in the rescaled `(ζ ^ᶻ u)`-basis. -/
theorem toZMod_ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat
    (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m)
    (n : ℕ+) (u : (Additive zHat.{u})ˣ) :
    zHat.toZMod n (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K
        (ζ ^ᶻ (u : Additive zHat.{u}))
        (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u)
        ((multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ))) =
      (((Units.map (zHat.toZMod.{u} n).toMonoidHom u)⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  rw [multiplicativeGroupAutFiberContinuousMulEquivZHat_apply,
    ← multiplicativeGroupAutFiberContinuousMulEquivTateModule_apply,
    ContinuousMulEquiv.apply_symm_apply]
  exact PrimeToPTateModule.toZMod_ofMul_continuousMulEquivZHat_zpowHat_self hζ n u

-- Sanity check modulo `5`: lifting `2 ∈ (ZMod 5)ˣ` to `u ∈ ℤ̂ˣ`, the generator `γ` carrying `ζ`
-- has coordinate `1` in the `ζ`-basis and residue `3` (not `2`) modulo `5` in the `(ζ ^ᶻ u)`-basis.
example (ζ : PrimeToPTateModule 1 K)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
      IsPrimitiveRoot (PrimeToPTateModule.proj m ζ : Kˣ) m) :
    ∃ u : (Additive zHat.{u})ˣ, zHat.toZMod 5 (u : Additive zHat.{u}) = 2 ∧
      let γ := (multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ
      ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K ζ hζ γ) = 1 ∧
        zHat.toZMod 5
          (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
            (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u) γ)) = 3 ∧
        zHat.toZMod 5
          (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
            (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u) γ)) ≠ 2 := by
  let v : (ZMod (5 : ℕ+))ˣ := ⟨2, 3, by decide, by decide⟩
  obtain ⟨u, hu⟩ := zHat.unitsMap_toZMod_surjective.{u} 5 v
  have hu2 : zHat.toZMod 5 (u : Additive zHat.{u}) = 2 := by
    have hval := congrArg Units.val hu
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at hval
    exact hval
  have hnew : zHat.toZMod 5
      (ofMul (multiplicativeGroupAutFiberContinuousMulEquivZHat K (ζ ^ᶻ (u : Additive zHat.{u}))
        (PrimeToPTateModule.isPrimitiveRoot_proj_zpowHat hζ u)
        ((multiplicativeGroupAutFiberContinuousMulEquivTateModule K).symm ζ))) = 3 := by
    rw [toZMod_ofMul_multiplicativeGroupAutFiberContinuousMulEquivZHat_zpowHat K ζ hζ 5 u, hu]
    decide
  refine ⟨u, hu2, ?_, hnew, hnew.symm ▸ by decide⟩
  rw [multiplicativeGroupAutFiberContinuousMulEquivZHat_apply,
    ← multiplicativeGroupAutFiberContinuousMulEquivTateModule_apply,
    ContinuousMulEquiv.apply_symm_apply, PrimeToPTateModule.continuousMulEquivZHat_self,
    zHat.ofMul_gen]

/-- **The étale fundamental group of `𝔾_{m, ℂ}` at `1` is `ℤ̂`** via the standard compatible system
of complex primitive roots of unity `ζ_n = exp(2πi / n)` (`PrimeToPTateModule.complexExp 1`). -/
noncomputable def complexMultiplicativeGroupAutFiberContinuousMulEquivZHat :
    Aut (fiber (multiplicativeGroupOnePoint ℂ ℂ)) ≃ₜ* zHat.{0} :=
  multiplicativeGroupAutFiberContinuousMulEquivZHat ℂ
    (PrimeToPTateModule.complexExp 1)
    (PrimeToPTateModule.isPrimitiveRoot_proj_complexExp 1)

/-- `complexMultiplicativeGroupAutFiberContinuousMulEquivZHat` specializes
`multiplicativeGroupAutFiberContinuousMulEquivZHat` to `PrimeToPTateModule.complexExp 1`. -/
theorem complexMultiplicativeGroupAutFiberContinuousMulEquivZHat_def :
    complexMultiplicativeGroupAutFiberContinuousMulEquivZHat =
      multiplicativeGroupAutFiberContinuousMulEquivZHat ℂ
        (PrimeToPTateModule.complexExp 1)
        (PrimeToPTateModule.isPrimitiveRoot_proj_complexExp 1) :=
  (rfl)

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
  rw [complexMultiplicativeGroupAutFiberContinuousMulEquivZHat_def]
  have h := congrArg (Units.val : ℂˣ → ℂ)
    (multiplicativeGroupPowerCoverFiberEquiv_symm_zHat_smul ℂ
      (PrimeToPTateModule.complexExp 1)
      (PrimeToPTateModule.isPrimitiveRoot_proj_complexExp 1) n hn a y)
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    PrimeToPTateModule.coe_proj_complexExp 1 ⟨n, n.ne_zero, Nat.coprime_one_right _⟩] at h
  exact h

end BasisChangeAndComplex

end TauCeti.FiniteEtaleScheme
