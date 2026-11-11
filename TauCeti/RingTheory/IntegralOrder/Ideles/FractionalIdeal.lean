/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.TensorFractionField
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Units
public import TauCeti.RingTheory.IntegralOrder.Ideles.Basic
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralIdeal

/-!
# Ideles of the base ring and fractional ideals

Let `A` be a Dedekind domain with fraction field `K`. For the order `Λ = A` in the commutative
algebra `B = K` (the bottom `A`-subalgebra of `K`), the ideles of `TauCeti.OrderIdeles` are the
classical finite ideles of `K`, and the lattice `I(α)` of an idele is the fractional ideal
`∏_v v ^ ord_v(α_v)` read off from its local valuations.

Indeed, `𝒪_v ⊗[A] K` is the completion `K_v`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersTensorEquiv`), and under this
isomorphism the completion `Λ_v` of `Λ = A` is `𝒪_v`. Hence the finite idele group `J_f(A)`,
the restricted product of the `(𝒪_v ⊗[A] K)ˣ` with respect to the `Λ_vˣ`, is the group of units
of the finite adele ring of `K`. An element `x ∈ K` lies in `I(α)` exactly when `α_v⁻¹ x ∈ 𝒪_v`
for every `v`, which is membership in the fractional ideal of `α`.

The same description gives the basic computations with ideles of `A`. An idele equal at one
place `w` to an element `b ∈ Kˣ` which is a unit at every other place, and equal to `1`
elsewhere, has lattice `b A`; for `A = ℤ` and a rational prime `p`, the idele `α_p = p`,
`α_q = 1` for `q ≠ p` has lattice `pℤ`. Conversely a family of local components lying in the
respective primes at infinitely many places, for instance `α_p = p` for infinitely many rational
primes `p`, is not an idele.

## Main definitions

* `TauCeti.OrderIdeles.finiteIdelesBotEquiv`: the isomorphism `J_f(A) ≃* 𝔸ᶠ[A, K]ˣ` between the
  finite ideles of the order `A ⊆ K` and the units of the finite adele ring.

## Main results

* `TauCeti.OrderIdeles.coe_finiteIdelesBotEquiv_apply`: this isomorphism maps each component
  `α_v` to its image in `K_v`.
* `TauCeti.OrderIdeles.lattice_bot_eq_toFractionalIdeal`: the lattice of a finite idele of `A` is
  the fractional ideal of the corresponding finite idele of `K`.
* `TauCeti.OrderIdeles.mem_lattice_bot_iff`: membership in this lattice is a condition on the
  local valuations.
* `TauCeti.OrderIdeles.lattice_bot_mulSingle_principal`: an idele equal to `b ∈ Kˣ` at `w` and to
  `1` elsewhere has lattice `b A`, when `b` is a unit at every other place.
* `TauCeti.OrderIdeles.not_forall_apply_eq_tmul_algebraMap`: no idele has components in the
  respective primes at infinitely many places.

## References

* A. Fröhlich, *Locally free modules over arithmetic orders*, J. Reine Angew. Math. 274/275
  (1975), 112–138, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open TensorProduct IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Submodule
  IsDedekindDomain.FiniteAdeleRing
open scoped RestrictedProduct Pointwise nonZeroDivisors

namespace TauCeti.OrderIdeles

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- The completion `Λ_v` of the order `A ⊆ K` consists of the elements of `𝒪_v ⊗[A] K` whose
image in `K_v` is integral. -/
theorem mem_baseChange_bot_iff {v : HeightOneSpectrum A} {y : v.adicCompletionIntegers K ⊗[A] K} :
    y ∈ (⊥ : Subalgebra A K).baseChange (v.adicCompletionIntegers K) ↔
      adicCompletionIntegersTensorEquiv K v y ∈ v.adicCompletionIntegers K := by
  rw [Subalgebra.baseChange_bot, adicCompletionIntegersTensorEquiv_mem_iff]

/-- The local units of the order `A ⊆ K` correspond to the units of `𝒪_v`. -/
private theorem mapsTo_units_map_units {v : HeightOneSpectrum A} :
    Set.MapsTo (Units.map (MonoidHom.ofClass (adicCompletionIntegersTensorEquiv K v)))
      ((⊥ : Subalgebra A K).baseChange (v.adicCompletionIntegers K)).toSubmonoid.units
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun _ hx ↦
  ⟨mem_baseChange_bot_iff.1 hx.1, mem_baseChange_bot_iff.1 hx.2⟩

/-- The units of `𝒪_v` correspond to the local units of the order `A ⊆ K`. -/
private theorem mapsTo_units_map_symm_units {v : HeightOneSpectrum A} :
    Set.MapsTo (Units.map (MonoidHom.ofClass (adicCompletionIntegersTensorEquiv K v).symm))
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units
      ((⊥ : Subalgebra A K).baseChange (v.adicCompletionIntegers K)).toSubmonoid.units :=
  fun x hx ↦ ⟨mem_baseChange_bot_iff.2 (by simpa using hx.1),
    mem_baseChange_bot_iff.2 (by simpa using hx.2)⟩

variable (A K) in
/-- **The finite ideles of the base ring are the finite ideles of its fraction field.** For the
order `A ⊆ K`, the finite idele group `J_f(A)` is the group of units of the finite adele ring
of `K`: the component `α_v ∈ (𝒪_v ⊗[A] K)ˣ` of an idele `α` corresponds to its image in
`K_vˣ`. -/
noncomputable def finiteIdelesBotEquiv : FiniteIdeles K (⊥ : Subalgebra A K) ≃* 𝔸ᶠ[A, K]ˣ where
  toFun α := (unitsContinuousMulEquiv A K).symm (RestrictedProduct.mapAlongMonoidHom _ _ id
    Filter.tendsto_id (fun v : HeightOneSpectrum A ↦
      Units.map (MonoidHom.ofClass (adicCompletionIntegersTensorEquiv K v)))
    (.of_forall fun _ ↦ mapsTo_units_map_units) α)
  invFun β := RestrictedProduct.mapAlongMonoidHom _ _ id Filter.tendsto_id
    (fun v : HeightOneSpectrum A ↦
      Units.map (MonoidHom.ofClass (adicCompletionIntegersTensorEquiv K v).symm))
    (.of_forall fun _ ↦ mapsTo_units_map_symm_units) (unitsContinuousMulEquiv A K β)
  left_inv α := RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp)
  right_inv β := (unitsContinuousMulEquiv A K).injective
    (RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp))
  map_mul' α β := by simp

/-- The component at `v` of the finite idele of `K` attached to a finite idele `α` of `A` is the
image of `α_v` in `K_v`. -/
@[simp]
theorem coe_finiteIdelesBotEquiv_apply (α : FiniteIdeles K (⊥ : Subalgebra A K))
    (v : HeightOneSpectrum A) :
    ((finiteIdelesBotEquiv A K α : 𝔸ᶠ[A, K]) v) = adicCompletionIntegersTensorEquiv K v (α v) := by
  simp [finiteIdelesBotEquiv]

/-- The component at `v` of the finite idele of `A` attached to a finite idele `β` of `K` is the
preimage of `β_v` in `𝒪_v ⊗[A] K`. -/
@[simp]
theorem coe_finiteIdelesBotEquiv_symm_apply (β : 𝔸ᶠ[A, K]ˣ) (v : HeightOneSpectrum A) :
    (((finiteIdelesBotEquiv A K).symm β v : (v.adicCompletionIntegers K ⊗[A] K)ˣ) :
      v.adicCompletionIntegers K ⊗[A] K) =
        (adicCompletionIntegersTensorEquiv K v).symm ((β : 𝔸ᶠ[A, K]) v) := by
  simp [finiteIdelesBotEquiv]

/-- An element `x` of `K` lies in the lattice `I(α)` of a finite idele `α` of `A` exactly when
`α_v⁻¹ x` is integral in `K_v` at every finite place `v`. -/
theorem mem_lattice_bot_iff {α : FiniteIdeles K (⊥ : Subalgebra A K)} {x : K} :
    x ∈ lattice K ⊥ α ↔ ∀ v : HeightOneSpectrum A,
      (adicCompletionIntegersTensorEquiv K v (α v))⁻¹ * algebraMap K (v.adicCompletion K) x ∈
        v.adicCompletionIntegers K := by
  refine mem_lattice_iff.trans (forall_congr' fun v ↦ ?_)
  rw [mem_baseChange_bot_iff, map_mul, adicCompletionIntegersTensorEquiv_tmul,
    OneMemClass.coe_one, one_mul, map_units_inv]

/-- **The lattice of an idele of `A` is its fractional ideal.** For the order `A` in its fraction
field `K`, the lattice `I(α) = K ∩ ∏_v α_v 𝒪_v` of a finite idele `α` is the fractional ideal
`∏_v v ^ ord_v(α_v)` defined by the valuations of the corresponding finite idele of `K`. -/
theorem lattice_bot_eq_toFractionalIdeal (α : FiniteIdeles K (⊥ : Subalgebra A K)) :
    lattice K ⊥ α =
      ((toFractionalIdeal (finiteIdelesBotEquiv A K α) : FractionalIdeal A⁰ K) :
        Submodule A K) := by
  ext x
  rw [mem_lattice_bot_iff, FractionalIdeal.mem_coe, mem_toFractionalIdeal_iff]
  refine forall_congr' fun v ↦ ?_
  rw [← map_inv (finiteIdelesBotEquiv A K) α, coe_finiteIdelesBotEquiv_apply,
    RestrictedProduct.inv_apply, map_units_inv]

/-- **Ideles of `A` concentrated at one place.** If `b ∈ Kˣ` is a unit at every place `v ≠ w`,
the idele equal to `b` at `w` and to `1` elsewhere has lattice `b A`. For instance, for `A = ℤ`
and a rational prime `p`, the idele `α_p = p`, `α_q = 1` for `q ≠ p` has lattice `pℤ`. -/
theorem lattice_bot_mulSingle_principal [DecidableEq (HeightOneSpectrum A)]
    {w : HeightOneSpectrum A} {b : Kˣ} (hb : ∀ v ≠ w, v.valuation K (b : K) = 1) :
    lattice K ⊥ (.mulSingle _ w (principal K ⊥
      (IntegralOrder.isOrder_bot (R := A) (F := K)).span_eq_top b w)) =
      span A {(b : K)} := by
  rw [lattice_mulSingle_principal, Algebra.toSubmodule_bot, Units.smul_def, smul_one_eq_span]
  intro v hv
  -- The image of `b` in `K_v` and its inverse are integral, because `b` is a unit at `v`.
  have hval (c : K) (hc : v.valuation K c = 1) :
      (1 : v.adicCompletionIntegers K) ⊗ₜ[A] c ∈
        (⊥ : Subalgebra A K).baseChange (v.adicCompletionIntegers K) := by
    rw [mem_baseChange_bot_iff, mem_adicCompletionIntegers,
      valued_adicCompletionIntegersTensorEquiv_one_tmul, hc]
  refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
  · rw [coe_principal_apply]
    exact hval _ (hb v hv)
  · rw [← RestrictedProduct.inv_apply, ← map_inv, coe_principal_apply]
    exact hval _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hb v hv, inv_one])

/-- **Ideles are units almost everywhere.** No finite idele `α` of `A` has components
`α_v = a_v` with `a_v` in the prime `v` at infinitely many places `v`. For instance, a family with
`α_p = p` at infinitely many rational primes `p` is not an idele relative to the `ℤ_pˣ`. -/
theorem not_forall_apply_eq_tmul_algebraMap {S : Set (HeightOneSpectrum A)} (hS : S.Infinite)
    (a : HeightOneSpectrum A → A) (ha : ∀ v ∈ S, a v ∈ v.asIdeal)
    (α : FiniteIdeles K (⊥ : Subalgebra A K)) :
    ¬∀ v ∈ S, ((α v : (v.adicCompletionIntegers K ⊗[A] K)ˣ) : v.adicCompletionIntegers K ⊗[A] K) =
      1 ⊗ₜ algebraMap A K (a v) := by
  intro h
  -- The finite idele of `K` attached to `α` is a local unit at all but finitely many places.
  obtain ⟨v, hvS, hv⟩ := ((Filter.frequently_cofinite_iff_infinite.2 hS).and_eventually
    (eventually_valued_coe_units_apply_eq_one (finiteIdelesBotEquiv A K α))).exists
  rw [coe_finiteIdelesBotEquiv_apply, h v hvS, valued_adicCompletionIntegersTensorEquiv_one_tmul,
    valuation_of_algebraMap] at hv
  exact (v.intValuation_lt_one_iff_mem _).2 (ha v hvS) |>.ne hv

end TauCeti.OrderIdeles
