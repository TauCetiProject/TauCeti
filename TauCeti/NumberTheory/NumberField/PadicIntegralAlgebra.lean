/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.RingTheory.Norm.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Algebra.Algebra.Pi
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The integral `p`-adic algebra of a number field

For a number field `K` and a prime `p`, the **integral `p`-adic algebra** of `K` is

```text
O_p = ℤ_p ⊗[ℤ] 𝓞 K,
```

with the scalars `ℤ_p` on the left, as a topological ring for the module topology over `ℤ_p`
(`TauCeti.NumberField.PadicIntegralAlgebra K p`). It is the ring on whose unit group the
`p`-adic weight characters of Hilbert modular forms live: a weight is a continuous character
of `O_pˣ`, and the norm `O_pˣ → ℤ_pˣ` produces the central weight factor.

No hypothesis on the splitting or ramification of `p` in `K` is made. The algebra is free of rank
`[K : ℚ]` over `ℤ_p` (`TauCeti.NumberField.PadicIntegralAlgebra.finrank_eq`), even when `p` ramifies
in `K`, where `O_p` is not a product of copies of `ℤ_p`. Its topology is the coordinate topology
of any `ℤ_p`-basis; it is compact and Hausdorff, multiplication and every `ℤ_p`-linear map are
continuous (`IsModuleTopology.continuous_of_linearMap`), and the powers of `p` tend to `0`.

The norm of `O_p` is `Algebra.norm ℤ_p`, the determinant of multiplication, and the norm on units
is `TauCeti.Algebra.normUnits ℤ_p`. On the image of the ring of integers the norm is the global
norm: `N(1 ⊗ x) = N_{K/ℚ}(x)`, also on global units
(`TauCeti.NumberField.PadicIntegralAlgebra.normUnits_unitsMap_algebraMap`). The inclusion
`𝓞 K → O_p`, `x ↦ 1 ⊗ x`, is injective, so a global unit other than `1` stays different from `1`
in `O_p`, even when its norm is `1`.

A `ℤ_p`-algebra map `O_p → E` is the same as a ring map `σ : 𝓞 K → E`
(`TauCeti.NumberField.PadicIntegralAlgebra.liftEquiv`). After scalar extension to a field `E` of
characteristic zero in which `K` splits, the norm is the product over the `[K : ℚ]` embeddings
`σ : K → E` of the maps `a ⊗ y ↦ a σ(y)`
(`TauCeti.NumberField.PadicIntegralAlgebra.algebraMap_norm_eq_prod_embeddings`). This is a
statement about the generic fibre: integrally, at a ramified prime, `O_p` does not split.

For `r : ℕ` the **principal unit group** `H_r ≤ O_pˣ` consists of the units `u` with
`u ≡ 1 (mod p ^ r O_p)`; it is the kernel of reduction of units modulo `p ^ r`. The groups `H_r`
decrease with `r`, start at `H_0 = O_pˣ`, are open of finite index, and meet in the identity.

## Main definitions

* `TauCeti.NumberField.PadicIntegralAlgebra K p`: the integral `p`-adic algebra `ℤ_p ⊗[ℤ] 𝓞 K`,
  with its module topology over `ℤ_p`.
* `TauCeti.NumberField.PadicIntegralAlgebra.tensorProductEquiv`: its identification with the
  tensor product `ℤ_p ⊗[ℤ] 𝓞 K`.
* `TauCeti.NumberField.PadicIntegralAlgebra.liftEquiv`: `ℤ_p`-algebra maps out of `O_p` are ring
  maps out of `𝓞 K`.
* `TauCeti.NumberField.PadicIntegralAlgebra.principalUnits K p r`: the principal unit group `H_r`.

## Main results

* `TauCeti.NumberField.PadicIntegralAlgebra.finrank_eq`: `O_p` has rank `[K : ℚ]` over `ℤ_p`, so
  the norm of a scalar `a` is `a ^ [K : ℚ]`.
* `TauCeti.NumberField.PadicIntegralAlgebra.tendsto_prime_pow_atTop_nhds_zero`: `pⁿ → 0` in
  `O_p`.
* `TauCeti.NumberField.PadicIntegralAlgebra.norm_algebraMap_ringOfIntegers`,
  `TauCeti.NumberField.PadicIntegralAlgebra.normUnits_unitsMap_algebraMap`: the norm of `1 ⊗ x`
  is the global norm of `x`, for integers and for units.
* `TauCeti.NumberField.PadicIntegralAlgebra.algebraMap_norm_eq_prod_embeddings`: over a splitting
  field of characteristic zero, the norm is the product over all embeddings of `K`.
* `TauCeti.NumberField.PadicIntegralAlgebra.mem_principalUnits_iff`: `u ∈ H_r ↔ pʳ ∣ u - 1`.
* `TauCeti.NumberField.PadicIntegralAlgebra.isOpen_principalUnits` and the `FiniteIndex`
  instance: each `H_r` is an open subgroup of finite index.
* `TauCeti.NumberField.PadicIntegralAlgebra.iInf_principalUnits`: the `H_r` meet in `1`.

## References

* C. Birkbeck, B. Heuer, C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), §6.1.
* F. Andreatta, A. Iovita, V. Pilloni, *The adic, cuspidal, Hilbert eigenvarieties*, Res. Math.
  Sci. 3 (2016), §2.
-/

public section

open scoped TensorProduct NumberField

namespace TauCeti.NumberField

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

/-- The **integral `p`-adic algebra** `O_p = ℤ_p ⊗[ℤ] 𝓞 K` of a number field `K` at a prime `p`,
with the scalars `ℤ_p` on the left. It carries the module topology over `ℤ_p`. The definition
makes sense for any field `K`; its finiteness and topological properties use that `K` is a number
field. -/
def PadicIntegralAlgebra : Type _ :=
  ℤ_[p] ⊗[ℤ] 𝓞 K

namespace PadicIntegralAlgebra

noncomputable instance : CommRing (PadicIntegralAlgebra K p) :=
  inferInstanceAs (CommRing (ℤ_[p] ⊗[ℤ] 𝓞 K))

noncomputable instance : Algebra ℤ_[p] (PadicIntegralAlgebra K p) :=
  inferInstanceAs (Algebra ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 K))

/-- The ring of integers acts on `O_p` through the right tensor factor, `x ↦ 1 ⊗ x`. -/
noncomputable instance : Algebra (𝓞 K) (PadicIntegralAlgebra K p) :=
  letI : Algebra (𝓞 K) (ℤ_[p] ⊗[ℤ] 𝓞 K) := Algebra.TensorProduct.rightAlgebra
  inferInstanceAs (Algebra (𝓞 K) (ℤ_[p] ⊗[ℤ] 𝓞 K))

/-- `O_p` carries the module topology over `ℤ_p`; for a number field this is the coordinate
topology of any `ℤ_p`-basis. -/
noncomputable instance : TopologicalSpace (PadicIntegralAlgebra K p) :=
  moduleTopology ℤ_[p] _

instance : IsModuleTopology ℤ_[p] (PadicIntegralAlgebra K p) :=
  ⟨rfl⟩

/-- The integral `p`-adic algebra is the tensor product `ℤ_p ⊗[ℤ] 𝓞 K`. -/
noncomputable def tensorProductEquiv : ℤ_[p] ⊗[ℤ] 𝓞 K ≃ₐ[ℤ_[p]] PadicIntegralAlgebra K p :=
  AlgEquiv.refl

/-- The inclusion of the ring of integers is `x ↦ 1 ⊗ x`. -/
theorem tensorProductEquiv_one_tmul (x : 𝓞 K) :
    tensorProductEquiv K p (1 ⊗ₜ x) = algebraMap (𝓞 K) (PadicIntegralAlgebra K p) x :=
  -- The algebra structure over `𝓞 K` is `Algebra.TensorProduct.rightAlgebra`, whose algebra map
  -- is the right tensor inclusion `x ↦ 1 ⊗ x`.
  (rfl)

/-- The inclusion of the scalars is `a ↦ a ⊗ 1`. -/
theorem tensorProductEquiv_tmul_one (a : ℤ_[p]) :
    tensorProductEquiv K p (a ⊗ₜ 1) = algebraMap ℤ_[p] (PadicIntegralAlgebra K p) a := by
  simpa using (tensorProductEquiv K p).commutes a

/-- The pure tensor `a ⊗ x` is the product of the scalar `a` and the integer `x`. -/
@[simp]
theorem tensorProductEquiv_tmul (a : ℤ_[p]) (x : 𝓞 K) :
    tensorProductEquiv K p (a ⊗ₜ x) =
      algebraMap ℤ_[p] (PadicIntegralAlgebra K p) a * algebraMap (𝓞 K) _ x := by
  rw [← tensorProductEquiv_tmul_one, ← tensorProductEquiv_one_tmul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

section Lift

variable (E : Type*) [CommRing E] [Algebra ℤ_[p] E]

/-- **The universal property of `O_p`.** A `ℤ_p`-algebra map `O_p → E` is the same as a ring map
`σ : 𝓞 K → E`; the map attached to `σ` sends `a ⊗ x` to `a σ(x)`. -/
noncomputable def liftEquiv : (𝓞 K →+* E) ≃ (PadicIntegralAlgebra K p →ₐ[ℤ_[p]] E) :=
  (RingHom.equivIntAlgHom (𝓞 K) E).trans <|
    (Algebra.TensorProduct.liftEquivRight ℤ ℤ_[p] (𝓞 K) E).trans <|
      AlgEquiv.arrowCongr (tensorProductEquiv K p) AlgEquiv.refl

variable {K p E}

@[simp]
theorem liftEquiv_apply_algebraMap (σ : 𝓞 K →+* E) (x : 𝓞 K) :
    liftEquiv K p E σ (algebraMap (𝓞 K) (PadicIntegralAlgebra K p) x) = σ x := by
  simp [liftEquiv, -tensorProductEquiv_tmul, ← tensorProductEquiv_one_tmul]

theorem liftEquiv_apply_tensorProductEquiv_tmul (σ : 𝓞 K →+* E) (a : ℤ_[p]) (x : 𝓞 K) :
    liftEquiv K p E σ (tensorProductEquiv K p (a ⊗ₜ x)) = algebraMap ℤ_[p] E a * σ x := by
  simp

@[simp]
theorem liftEquiv_symm_apply (f : PadicIntegralAlgebra K p →ₐ[ℤ_[p]] E) (x : 𝓞 K) :
    (liftEquiv K p E).symm f x = f (algebraMap (𝓞 K) (PadicIntegralAlgebra K p) x) := by
  conv_rhs => rw [← (liftEquiv K p E).apply_symm_apply f]
  rw [liftEquiv_apply_algebraMap]

/-- Two `ℤ_p`-algebra maps out of `O_p` agree once they agree on the image of `𝓞 K`. -/
@[ext]
theorem algHom_ext {f g : PadicIntegralAlgebra K p →ₐ[ℤ_[p]] E}
    (h : ∀ x : 𝓞 K, f (algebraMap (𝓞 K) _ x) = g (algebraMap (𝓞 K) _ x)) : f = g :=
  (liftEquiv K p E).symm.injective <| RingHom.ext fun x ↦ by simpa using h x

end Lift

/-- The powers of `p` tend to `0` in `O_p`. -/
theorem tendsto_prime_pow_atTop_nhds_zero :
    Filter.Tendsto (fun n : ℕ ↦ (p : PadicIntegralAlgebra K p) ^ n) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one PadicInt.norm_p_lt_one
  simpa [Function.comp_def] using
    ((continuous_algebraMap ℤ_[p] (PadicIntegralAlgebra K p)).tendsto 0).comp h

section NumberField

variable [NumberField K]

instance : Module.Free ℤ_[p] (PadicIntegralAlgebra K p) :=
  .of_equiv (tensorProductEquiv K p).toLinearEquiv

instance : Module.Finite ℤ_[p] (PadicIntegralAlgebra K p) :=
  .equiv (tensorProductEquiv K p).toLinearEquiv

instance : IsTopologicalRing (PadicIntegralAlgebra K p) :=
  IsModuleTopology.isTopologicalRing ℤ_[p] _

instance : CompactSpace (PadicIntegralAlgebra K p) :=
  (TauCeti.ModuleTopology.equivFunHomeomorph
    (Module.Free.chooseBasis ℤ_[p] (PadicIntegralAlgebra K p))).symm.compactSpace

instance : T2Space (PadicIntegralAlgebra K p) :=
  TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis ℤ_[p] (PadicIntegralAlgebra K p))

/-- **The rank of the integral `p`-adic algebra.** `O_p` is free of rank `[K : ℚ]` over `ℤ_p`,
whatever the decomposition of `p` in `K`. In particular a scalar `a ∈ ℤ_p` has norm
`a ^ [K : ℚ]` in `O_p` (`Algebra.norm_algebraMap`). -/
@[simp]
theorem finrank_eq : Module.finrank ℤ_[p] (PadicIntegralAlgebra K p) = Module.finrank ℚ K := by
  rw [← (tensorProductEquiv K p).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
    NumberField.RingOfIntegers.rank]

/-- The inclusion `𝓞 K → O_p`, `x ↦ 1 ⊗ x`, is injective. -/
theorem algebraMap_ringOfIntegers_injective :
    Function.Injective (algebraMap (𝓞 K) (PadicIntegralAlgebra K p)) := by
  have h : ⇑(algebraMap (𝓞 K) (PadicIntegralAlgebra K p)) =
      tensorProductEquiv K p ∘ Algebra.TensorProduct.includeRight := by
    ext x
    simp
  rw [h]
  exact (tensorProductEquiv K p).injective.comp
    (Algebra.TensorProduct.includeRight_injective (algebraMap ℤ ℤ_[p]).injective_int)

/-- **The norm of a global integer.** The norm of `1 ⊗ x` over `ℤ_p` is the norm of `x` over `ℤ`,
that is, the norm `N_{K/ℚ}(x)` read in `ℤ_p`. -/
@[simp]
theorem norm_algebraMap_ringOfIntegers (x : 𝓞 K) :
    Algebra.norm ℤ_[p] (algebraMap (𝓞 K) (PadicIntegralAlgebra K p) x) = Algebra.norm ℤ x := by
  rw [← tensorProductEquiv_one_tmul, Algebra.norm_eq_of_algEquiv,
    TauCeti.Algebra.norm_baseChange_tmul, eq_intCast]

/-- **The norm of a global unit.** The image of a unit `u` of `𝓞 K` in `O_pˣ` has norm `N(u)`,
which is `±1`, read in `ℤ_pˣ`. -/
@[simp]
theorem normUnits_unitsMap_algebraMap (u : (𝓞 K)ˣ) :
    TauCeti.Algebra.normUnits ℤ_[p]
        (Units.map (algebraMap (𝓞 K) (PadicIntegralAlgebra K p) : 𝓞 K →* PadicIntegralAlgebra K p)
          u) =
      Units.map (Int.castRingHom ℤ_[p] : ℤ →* ℤ_[p]) (TauCeti.Algebra.normUnits ℤ u) :=
  Units.ext <| by simp

/-- **The norm as a product over embeddings.** Let `E` be a field of characteristic zero
over `ℤ_p` in which `K` splits, that is, with `[K : ℚ]` embeddings `σ : K → E`. Then the image in
`E` of the norm of `x ∈ O_p` is the product of the values at `x` of the maps
`O_p → E`, `a ⊗ y ↦ a σ(y)`.

This is a statement after scalar extension to `E`; `O_p` itself need not be a product of copies
of `ℤ_p`. -/
theorem algebraMap_norm_eq_prod_embeddings {E : Type*} [Field E] [CharZero E] [Algebra ℤ_[p] E]
    (hE : Module.finrank ℚ K ≤ Fintype.card (K →+* E)) (x : PadicIntegralAlgebra K p) :
    algebraMap ℤ_[p] E (Algebra.norm ℤ_[p] x) =
      ∏ σ : K →+* E, liftEquiv K p E (σ.comp (algebraMap (𝓞 K) K)) x := by
  classical
  -- After base change to `E`, each embedding gives a character of `A = E ⊗ O_p`; there are
  -- `[K : ℚ] = dim_E A` of them, so `A` is the algebra of functions on its characters, and the norm
  -- of `1 ⊗ x` is the product of its values at the characters.
  let A := E ⊗[ℤ_[p]] PadicIntegralAlgebra K p
  let χ : (K →+* E) → (A →ₐ[E] E) := fun σ ↦
    Algebra.TensorProduct.liftEquivRight ℤ_[p] E _ E
      (liftEquiv K p E (σ.comp (algebraMap (𝓞 K) K)))
  have hχ : Function.Injective χ :=
    (Equiv.injective _).comp <| (Equiv.injective _).comp fun _ _ h ↦
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h
  have hdim : Module.finrank E A = Module.finrank ℚ K := by
    rw [Module.finrank_baseChange, finrank_eq]
  have := Fintype.ofFinite (A →ₐ[E] E)
  have hle : Fintype.card (K →+* E) ≤ Fintype.card (A →ₐ[E] E) :=
    Fintype.card_le_of_injective χ hχ
  let e := AlgEquiv.ofBijective _ (TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card
    (hdim.trans_le (hE.trans (hle.trans_eq Nat.card_eq_fintype_card.symm))))
  have hcard : Fintype.card (A →ₐ[E] E) = Fintype.card (K →+* E) :=
    le_antisymm ((Nat.card_eq_fintype_card.symm.trans_le
      (card_algHom_le_finrank E A E)).trans (hdim.trans_le hE)) hle
  have hχbij : Function.Bijective χ :=
    (Fintype.bijective_iff_injective_and_card χ).mpr ⟨hχ, hcard.symm⟩
  rw [← TauCeti.Algebra.norm_baseChange_tmul (A := E), ← Algebra.norm_eq_of_algEquiv e,
    TauCeti.Algebra.norm_pi]
  refine (Fintype.prod_bijective χ hχbij _ _ fun σ ↦ ?_).symm
  -- The character `χ σ` is `Algebra.TensorProduct.lift (Algebra.ofId E E) (liftEquiv K p E σ)`,
  -- so it sends `1 ⊗ x` to `1 * liftEquiv K p E σ x`.
  rw [AlgEquiv.ofBijective_apply, AlgHom.pi_apply, Algebra.norm_self, MonoidHom.id_apply]
  simp only [χ, Algebra.TensorProduct.liftEquivRight_apply]
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end NumberField

section PrincipalUnits

/-- The **principal unit group** `H_r = 1 + pʳ O_p` of the integral `p`-adic algebra: the units
congruent to `1` modulo the ideal generated by `p ^ r`. For `r = 0` it is all of `O_pˣ`. -/
noncomputable def principalUnits (r : ℕ) : Subgroup (PadicIntegralAlgebra K p)ˣ :=
  (Ideal.span {(p : PadicIntegralAlgebra K p)} ^ r).principalUnitGroup

variable {K p} in
/-- A unit lies in `H_r` exactly when `p ^ r` divides `u - 1`. -/
@[simp]
theorem mem_principalUnits_iff {r : ℕ} {u : (PadicIntegralAlgebra K p)ˣ} :
    u ∈ principalUnits K p r ↔
      (p : PadicIntegralAlgebra K p) ^ r ∣ (u : PadicIntegralAlgebra K p) - 1 := by
  rw [principalUnits, Ideal.mem_principalUnitGroup, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/-- `H_r` is the kernel of reduction of units modulo the ideal generated by `p ^ r`. -/
theorem principalUnits_eq_ker (r : ℕ) :
    principalUnits K p r =
      (Units.map (Ideal.Quotient.mk
        (Ideal.span {(p : PadicIntegralAlgebra K p)} ^ r)).toMonoidHom).ker :=
  Ideal.principalUnitGroup_eq_ker_unitsMap _

@[simp]
theorem principalUnits_zero : principalUnits K p 0 = ⊤ := by
  simp [principalUnits]

/-- The principal unit groups decrease: `H_s ≤ H_r` when `r ≤ s`. -/
theorem principalUnits_antitone : Antitone (principalUnits K p) :=
  Ideal.principalUnitGroup_pow_antitone _

/-- The ideal of `O_p` generated by `p ^ r`, as a `ℤ_p`-submodule, is `pʳ ℤ_p • O_p`. -/
private theorem restrictScalars_span_pow (r : ℕ) :
    (Ideal.span {(p : PadicIntegralAlgebra K p)} ^ r).restrictScalars ℤ_[p] =
      Ideal.span {(p : ℤ_[p])} ^ r • (⊤ : Submodule ℤ_[p] (PadicIntegralAlgebra K p)) := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

variable [NumberField K]

/-- The ideal of `O_p` generated by `p ^ r` is open. -/
private theorem isOpen_span_pow (r : ℕ) :
    IsOpen ((Ideal.span {(p : PadicIntegralAlgebra K p)} ^ r : Ideal (PadicIntegralAlgebra K p)) :
      Set (PadicIntegralAlgebra K p)) := by
  have h : IsOpen ((Ideal.span {(p : ℤ_[p])} ^ r : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow]
    exact (isOpen_discrete {0}).preimage (PadicInt.continuous_toZModPow r)
  have h' := IsModuleTopology.isOpen_smul_top (M := PadicIntegralAlgebra K p) h
  rwa [← restrictScalars_span_pow, Submodule.coe_restrictScalars] at h'

/-- Each principal unit group `H_r` is open in `O_pˣ`. -/
theorem isOpen_principalUnits (r : ℕ) :
    IsOpen (principalUnits K p r : Set (PadicIntegralAlgebra K p)ˣ) :=
  Ideal.isOpen_principalUnitGroup (isOpen_span_pow K p r)

/-- Each principal unit group `H_r` has finite index in the compact group `O_pˣ`. -/
instance finiteIndex_principalUnits (r : ℕ) : (principalUnits K p r).FiniteIndex :=
  have := Subgroup.quotient_finite_of_isOpen _ (isOpen_principalUnits K p r)
  Subgroup.finiteIndex_of_finite_quotient

/-- The principal unit groups meet in the identity: a unit congruent to `1` modulo every power of
`p` is `1`. -/
theorem iInf_principalUnits : ⨅ r, principalUnits K p r = ⊥ := by
  refine eq_bot_iff.mpr fun u hu ↦ Subgroup.mem_bot.mpr <| Units.val_eq_one.mp <| sub_eq_zero.mp ?_
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := PadicIntegralAlgebra K p)
    (Ideal.span {(p : ℤ_[p])}) (Ideal.span_singleton_ne_top PadicInt.p_nonunit)
  rw [← Submodule.mem_bot ℤ_[p], ← h, Submodule.mem_iInf]
  intro r
  rw [← restrictScalars_span_pow, Submodule.restrictScalars_mem]
  exact Ideal.mem_principalUnitGroup.mp (Subgroup.mem_iInf.mp hu r)

end PrincipalUnits

end PadicIntegralAlgebra

end TauCeti.NumberField
