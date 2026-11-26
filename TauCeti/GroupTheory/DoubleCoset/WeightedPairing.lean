/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.DoubleCoset.Fiber
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic.Ring

/-!
# Stabiliser-weighted pairings, level traces and Hecke adjoints on orbit spaces

Let a group `G` act on a type `α`. For a subgroup `U ≤ G`, functions on the orbit space
`U \ α` carry the **stabiliser-weighted pairing**

`⟨f, g⟩_U = ∑_{x ∈ U \ α} c_U(x)⁻¹ f(x) g(x)`,

where `c_U(x)` is the order of the stabiliser of `x` in `U` (`TauCeti.cardStabilizerOnOrbit`).
It is defined over any commutative semiring, the inverse being `Ring.inverse`; the statements
below assume the stabiliser orders are units. On finitely many orbits with unit weights the
pairing is perfect: every linear functional is pairing against a unique function.

For a subgroup `V ≤ U` of finite index the **level trace** sends a function `h` on `V \ α` to the
function on `U \ α` given by `x ↦ ∑_{u ∈ U/V} h(u⁻¹ • x)`. It is a sum, not an average. A class
`y` above `x` occurs `c_U(x)/c_V(y)` times in it, which is the weighted adjunction with pullback

`⟨f, tr h⟩_U = ⟨f|_V, h⟩_V`.

For `g ∈ G` with `U ∩ gUg⁻¹` of finite index in `U`, the **Hecke operator** `[UgU]` acts on
functions on `U \ α` by `x ↦ ∑ f((u g)⁻¹ • x)`, the sum over `u ∈ U/(U ∩ gUg⁻¹)`, so over the
left cosets `u g U` making up the double coset `UgU`. The stabiliser-weighted pairing makes the
Hecke operators of `g` and `g⁻¹` adjoint:

`⟨[UgU] f, h⟩_U = ⟨f, [Ug⁻¹U] h⟩_U`.

The proof is the weighted adjunction twice, across the identification of the orbits of
`U ∩ gUg⁻¹` with those of `g⁻¹Ug ∩ U` by translation.

These are the pairing, trace and adjoint identities of the definite quaternionic class sets
`X(U) = D^× \ G(𝔸_f) / U` of Skinner–Wiles, §3.2. To apply them, let `G(𝔸_f)` act on the left of
`D^× \ G(𝔸_f)` by `h • (D^× x) = D^× x h⁻¹`. The orbits of `U` are then the points of `X(U)`,
the operator `[UgU]` here is the double coset operator `f ↦ (x ↦ ∑ f(x gᵢ))` for
`UgU = ⊔ gᵢ U`, and the level trace is the trace map between levels. The weights there are
the orders of the stabilisers in `U / (U ∩ F^×)`. The centre `𝔸_f^×` does not act trivially on
`D^× \ G(𝔸_f)`, but its subgroup `F^×`, which lies in `D^×`, does. So these weights are the
stabiliser orders here for the induced action of `G(𝔸_f) / F^×`, under which `U` acts through
`U / (U ∩ F^×)`. Without some such quotient the stabilisers are usually infinite, their orders
`Nat.card` are `0`, and the unit hypotheses fail.

## Main definitions

* `TauCeti.stabilizerWeightedPairing`: the pairing `∑ c(x)⁻¹ f(x) g(x)` on an orbit space.
* `TauCeti.levelTrace`: the trace from `V \ α` to `U \ α`.
* `TauCeti.heckeOperator`: the double coset operator `[UgU]` on functions on `U \ α`.

## Main results

* `TauCeti.existsUnique_stabilizerWeightedPairing_eq`: perfection of the pairing for unit
  weights on finitely many orbits.
* `TauCeti.inverse_cardStabilizerOnOrbit_smul_levelTrace`: the trace at `x`, divided by
  `c_U(x)`, is the sum over the classes `y` above `x` of `h(y) / c_V(y)`.
* `TauCeti.stabilizerWeightedPairing_levelTrace`: trace and pullback are adjoint.
* `TauCeti.levelTrace_of_le`: the trace from a larger level is pullback; in particular the trace
  from a level to itself is the identity (`TauCeti.levelTrace_self`).
* `TauCeti.heckeOperator_mk`: the Hecke operator as a sum over coset representatives.
* `TauCeti.stabilizerWeightedPairing_heckeOperator`: `[UgU]` and `[Ug⁻¹U]` are adjoint.

## References

* C. M. Skinner and A. J. Wiles, *Residually reducible representations and modular forms*,
  Publ. Math. IHÉS 89 (1999), §3.2.
* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, §3.1.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

section Pairing

variable {G α : Type*} [Group G] [MulAction G α] {R : Type*} [CommSemiring R]

/-- **The stabiliser-weighted pairing** `∑_x c(x)⁻¹ f(x) g(x)` of two functions on the orbit space
of `G` acting on `α`, where `c(x)` is the order of the stabiliser of the orbit `x`
(`cardStabilizerOnOrbit`) and the inverse is `Ring.inverse`. The sum is a `finsum`, so it is `0`
when the summand `x ↦ c(x)⁻¹ f(x) g(x)` has infinite support. -/
noncomputable def stabilizerWeightedPairing (f g : orbitRel.Quotient G α → R) : R :=
  ∑ᶠ x, Ring.inverse (cardStabilizerOnOrbit x : R) * (f x * g x)

theorem stabilizerWeightedPairing_def (f g : orbitRel.Quotient G α → R) :
    stabilizerWeightedPairing f g =
      ∑ᶠ x, Ring.inverse (cardStabilizerOnOrbit x : R) * (f x * g x) :=
  (rfl)

/-- The stabiliser-weighted pairing is symmetric. -/
theorem stabilizerWeightedPairing_comm (f g : orbitRel.Quotient G α → R) :
    stabilizerWeightedPairing f g = stabilizerWeightedPairing g f := by
  simp only [stabilizerWeightedPairing_def, mul_comm (f _)]

/-- When every stabiliser is trivial, for instance for a free action, the stabiliser-weighted
pairing is the unweighted sum `∑ f(x) g(x)`. -/
theorem stabilizerWeightedPairing_eq_finsum_of_cardStabilizerOnOrbit_eq_one
    (h : ∀ x : orbitRel.Quotient G α, cardStabilizerOnOrbit x = 1)
    (f g : orbitRel.Quotient G α → R) :
    stabilizerWeightedPairing f g = ∑ᶠ x, f x * g x := by
  simp [stabilizerWeightedPairing_def, h]

/-- On finitely many orbits the pairing is additive in its first argument. -/
theorem stabilizerWeightedPairing_add_left [Finite (orbitRel.Quotient G α)]
    (f₁ f₂ g : orbitRel.Quotient G α → R) :
    stabilizerWeightedPairing (f₁ + f₂) g =
      stabilizerWeightedPairing f₁ g + stabilizerWeightedPairing f₂ g := by
  simp only [stabilizerWeightedPairing_def, Pi.add_apply, add_mul, mul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- On finitely many orbits the pairing is homogeneous in its first argument. -/
theorem stabilizerWeightedPairing_smul_left [Finite (orbitRel.Quotient G α)] (r : R)
    (f g : orbitRel.Quotient G α → R) :
    stabilizerWeightedPairing (r • f) g = r * stabilizerWeightedPairing f g := by
  have := Fintype.ofFinite (orbitRel.Quotient G α)
  simp only [stabilizerWeightedPairing_def, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Perfection of the stabiliser-weighted pairing.** If there are finitely many orbits and every
stabiliser order is a unit in `R`, every `R`-linear functional on the functions on the orbit space
is the pairing against a unique function. -/
theorem existsUnique_stabilizerWeightedPairing_eq [Finite (orbitRel.Quotient G α)]
    (hunit : ∀ x : orbitRel.Quotient G α, IsUnit (cardStabilizerOnOrbit x : R))
    (ℓ : (orbitRel.Quotient G α → R) →ₗ[R] R) :
    ∃! f : orbitRel.Quotient G α → R, ∀ g, stabilizerWeightedPairing f g = ℓ g := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient G α)
  -- the pairing is the dot product of `c⁻¹ f` with `g`, which is perfect by `dotProductEquiv`
  have hdot : ∀ f g : orbitRel.Quotient G α → R, stabilizerWeightedPairing f g =
      (fun x ↦ Ring.inverse (cardStabilizerOnOrbit x : R) * f x) ⬝ᵥ g := fun f g ↦ by
    simp [stabilizerWeightedPairing_def, finsum_eq_sum_of_fintype, dotProduct, mul_assoc]
  set e := dotProductEquiv R (orbitRel.Quotient G α)
  have hv : ∀ g, e.symm ℓ ⬝ᵥ g = ℓ g := fun g ↦ by
    rw [← dotProductEquiv_apply_apply, e.apply_symm_apply]
  refine ⟨fun x ↦ (cardStabilizerOnOrbit x : R) * e.symm ℓ x, fun g ↦ ?_,
    fun f hf ↦ funext fun x ↦ ?_⟩
  · rw [hdot, ← hv]
    congr 1
    funext x
    rw [← mul_assoc, Ring.inverse_mul_cancel _ (hunit x), one_mul]
  · have hf' : (fun x ↦ Ring.inverse (cardStabilizerOnOrbit x : R) * f x) = e.symm ℓ :=
      e.eq_symm_apply.mpr (LinearMap.ext fun g ↦ by simp [e, ← hdot, hf])
    rw [← hf', ← mul_assoc, Ring.mul_inverse_cancel _ (hunit x), one_mul]

/-- **The pairing is invariant under an equivariant equivalence.** An equivalence `e : α ≃ β`
carrying the action of `G` to that of `H` along `φ : G ≃* H` preserves the stabiliser orders of
the orbits, so it carries the stabiliser-weighted pairing on `H`-orbits of `β` to the one on
`G`-orbits of `α`. -/
theorem stabilizerWeightedPairing_comp_orbitRelQuotientCongr {H β : Type*} [Group H]
    [MulAction H β] (φ : G ≃* H) (e : α ≃ β) (he : ∀ (g : G) (a : α), e (g • a) = φ g • e a)
    (f g : orbitRel.Quotient H β → R) :
    stabilizerWeightedPairing (f ∘ MulAction.orbitRelQuotientCongr φ e he)
        (g ∘ MulAction.orbitRelQuotientCongr φ e he) =
      stabilizerWeightedPairing f g := by
  simp only [stabilizerWeightedPairing_def, Function.comp_apply]
  rw [← finsum_comp_equiv (MulAction.orbitRelQuotientCongr φ e he)]
  simp only [cardStabilizerOnOrbit_orbitRelQuotientCongr]

end Pairing

section LevelTrace

variable {G α : Type*} [Group G] [MulAction G α] {M : Type*} [AddCommMonoid M]

/-- **The level trace** from functions on the `V`-orbits to functions on the `U`-orbits: its value
at the orbit of `x` is `∑ h(u⁻¹ • x)`, the sum over `u ∈ U / (V ∩ U)`. It is a sum, not an average:
no division by the index is made. The sum is a `finsum`, so the trace is `0` at the orbit of `x`
when `c ↦ h(u⁻¹ • x)` has infinite support; the theorems below assume `V ∩ U` has finite index in
`U` (`Subgroup.IsFiniteRelIndex`), where every such sum is finite. -/
noncomputable def levelTrace (V U : Subgroup G) (h : orbitRel.Quotient V α → M) :
    orbitRel.Quotient U α → M :=
  Quotient.lift (fun x ↦ ∑ᶠ c : U ⧸ V.subgroupOf U, h (orbitOfCosetTranslate x c))
    fun x y hxy ↦ by
      obtain ⟨u, rfl⟩ := hxy
      simp only [orbitOfCosetTranslate_smul]
      exact finsum_comp_equiv (f := fun c ↦ h (orbitOfCosetTranslate y c))
        (MulAction.toPerm (u⁻¹ : U))

/-- The level trace at the orbit of `x` is the sum of `h` over the translates `u⁻¹ • x` indexed by
the cosets `u (V ∩ U)`. -/
@[simp]
theorem levelTrace_mk (V U : Subgroup G) (h : orbitRel.Quotient V α → M) (x : α) :
    levelTrace V U h (Quotient.mk'' x) =
      ∑ᶠ c : U ⧸ V.subgroupOf U, h (orbitOfCosetTranslate x c) :=
  (rfl)

/-- **The level trace from a larger level is pullback.** If `U ≤ V`, the coset space
`U / (V ∩ U)` is a point, so the trace of `h` is `h` composed with the map from `U`-orbits to
`V`-orbits. -/
theorem levelTrace_of_le {U V : Subgroup G} (hUV : U ≤ V) (h : orbitRel.Quotient V α → M) :
    levelTrace V U h = h ∘ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hUV) := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    have : Subsingleton (U ⧸ V.subgroupOf U) := by
      rw [Subgroup.subgroupOf_eq_top.mpr hUV]
      exact QuotientGroup.subsingleton_quotient_top
    rw [levelTrace_mk, finsum_eq_single _ ((1 : U) : U ⧸ V.subgroupOf U)
      fun c hc ↦ (hc (Subsingleton.elim _ _)).elim, orbitOfCosetTranslate_mk]
    simp

/-- The level trace from a level to itself is the identity. -/
@[simp]
theorem levelTrace_self (U : Subgroup G) (h : orbitRel.Quotient U α → M) :
    levelTrace U U h = h := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    rw [levelTrace_of_le le_rfl]
    simp only [Function.comp_apply, TauCeti.Setoid.map_of_le_mk]

/-- The level trace of `0` is `0`. -/
@[simp]
theorem levelTrace_zero (V U : Subgroup G) :
    levelTrace V U (0 : orbitRel.Quotient V α → M) = 0 := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x => simp

/-- The level trace is additive. -/
theorem levelTrace_add (V U : Subgroup G) [V.IsFiniteRelIndex U]
    (h₁ h₂ : orbitRel.Quotient V α → M) :
    levelTrace V U (h₁ + h₂) = levelTrace V U h₁ + levelTrace V U h₂ := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    simp only [levelTrace_mk, Pi.add_apply]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- The level trace commutes with scalar multiplication. -/
theorem levelTrace_smul {R : Type*} [DistribSMul R M] (V U : Subgroup G) [V.IsFiniteRelIndex U]
    (r : R) (h : orbitRel.Quotient V α → M) :
    levelTrace V U (r • h) = r • levelTrace V U h := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    simp only [levelTrace_mk, Pi.smul_apply]
    exact (smul_finsum' r (Set.toFinite _)).symm

variable {R : Type*} [CommSemiring R] [Module R M]

/-- **The level trace with its multiplicities.** For `V ≤ U` of finite index and a `U`-orbit `p`
whose stabiliser order is a unit, the trace at `p` divided by that order is the sum of
`h(q) / c_V(q)` over the `V`-orbits `q` above `p`. Indeed `q` occurs in the trace
`c_U(p) / c_V(q)` times. -/
theorem inverse_cardStabilizerOnOrbit_smul_levelTrace {V U : Subgroup G} (hle : V ≤ U)
    [V.IsFiniteRelIndex U] (h : orbitRel.Quotient V α → M) (p : orbitRel.Quotient U α)
    (hp : IsUnit (cardStabilizerOnOrbit p : R)) :
    Ring.inverse (cardStabilizerOnOrbit p : R) • levelTrace V U h p =
      ∑ᶠ q ∈ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle) ⁻¹' {p},
        Ring.inverse (cardStabilizerOnOrbit q : R) • h q := by
  classical
  induction p using Quotient.inductionOn' with | h x => ?_
  have := Fintype.ofFinite (U ⧸ V.subgroupOf U)
  -- the fibre over the orbit of `x` is the image of `orbitOfCosetTranslate x`
  rw [preimage_map_of_le_mk_eq_range_orbitOfCosetTranslate hle, ← Set.image_univ, ← Finset.coe_univ,
    ← Finset.coe_image, finsum_mem_coe_finset, levelTrace_mk, finsum_eq_sum_of_fintype,
    Finset.sum_comp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hq
  -- `q = orbitOfCosetTranslate x c` occurs `c_U(x) / c_V(q)` times among the cosets
  have hcount := card_fiber_orbitOfCosetTranslate_mul_cardStabilizerOnOrbit hle x c
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcount
  rw [cardStabilizerOnOrbit_mk] at hp ⊢
  -- so `c_U(x)⁻¹ * #(fibre) = c_V(q)⁻¹`, as `#(fibre) * c_V(q) = c_U(x)` is a unit
  have key {n a b : ℕ} (hn : n * b = a) (ha : IsUnit (a : R)) :
      Ring.inverse (a : R) * n = Ring.inverse (b : R) := by
    have hb : IsUnit (b : R) := isUnit_of_mul_isUnit_right (by rwa [← Nat.cast_mul, hn])
    rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ ha, ← hn, Nat.cast_mul, mul_assoc,
      Ring.mul_inverse_cancel _ hb, mul_one]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, key hcount hp]

/-- **Trace and pullback are adjoint for the stabiliser-weighted pairings.** For `V ≤ U` of finite
index, finitely many `U`-orbits and unit stabiliser orders on them,
`⟨f, tr h⟩_U = ⟨f|_V, h⟩_V`, where `f|_V` is `f` composed with the map from `V`-orbits to
`U`-orbits. -/
theorem stabilizerWeightedPairing_levelTrace {V U : Subgroup G} (hle : V ≤ U)
    [V.IsFiniteRelIndex U] [Finite (orbitRel.Quotient U α)]
    (hunit : ∀ p : orbitRel.Quotient U α, IsUnit (cardStabilizerOnOrbit p : R))
    (f : orbitRel.Quotient U α → R) (h : orbitRel.Quotient V α → R) :
    stabilizerWeightedPairing f (levelTrace V U h) =
      stabilizerWeightedPairing (f ∘ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle))
        h := by
  classical
  have := finite_orbitRelQuotient_of_le (X := α) hle
  have := Fintype.ofFinite (orbitRel.Quotient U α)
  have := Fintype.ofFinite (orbitRel.Quotient V α)
  -- regroup the sum over `V`-orbits by the `U`-orbit below, then use the trace at each `U`-orbit
  rw [stabilizerWeightedPairing_def, stabilizerWeightedPairing_def, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ
      (Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle))]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hp := inverse_cardStabilizerOnOrbit_smul_levelTrace (R := R) hle h p (hunit p)
  rw [smul_eq_mul, finsum_mem_eq_toFinset_sum] at hp
  rw [mul_left_comm, hp, Finset.mul_sum]
  refine Finset.sum_congr (by ext; simp) fun q hq ↦ ?_
  have hq' : Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (X := α) hle) q = p := by
    simpa using hq
  simp only [Function.comp_apply, hq', smul_eq_mul]
  ring

end LevelTrace

section Hecke

variable {G α : Type*} [Group G] [MulAction G α]

/-- `orbitRelQuotientSMulEquiv g hHK` carries the stabiliser-weighted pairing on the `K`-orbits to
the one on the `H`-orbits. -/
theorem stabilizerWeightedPairing_comp_orbitRelQuotientSMulEquiv {R : Type*} [CommSemiring R]
    (g : G) {H K : Subgroup G} (hHK : ConjAct.toConjAct g • H = K)
    (f₁ f₂ : orbitRel.Quotient K α → R) :
    stabilizerWeightedPairing (f₁ ∘ MulAction.orbitRelQuotientSMulEquiv g hHK)
        (f₂ ∘ MulAction.orbitRelQuotientSMulEquiv g hHK) =
      stabilizerWeightedPairing f₁ f₂ := by
  rw [MulAction.orbitRelQuotientSMulEquiv_eq_orbitRelQuotientCongr]
  exact stabilizerWeightedPairing_comp_orbitRelQuotientCongr _ _ _ f₁ f₂

variable {M : Type*} [AddCommMonoid M]

/-- **The Hecke operator** `[UgU]` on functions on the `U`-orbits: its value at the orbit of `x`
is `∑ f((u g)⁻¹ • x)`, the sum over `u ∈ U / (U ∩ gUg⁻¹)` (`heckeOperator_mk`). By
`DoubleCoset.doubleCoset_eq_iUnion_leftCosets` these `u g` represent the left cosets of `U` making
up the double coset `UgU`. It is the level trace from `U ∩ gUg⁻¹` of `f` composed with translation
by `g⁻¹`. -/
noncomputable def heckeOperator (U : Subgroup G) (g : G) (f : orbitRel.Quotient U α → M) :
    orbitRel.Quotient U α → M :=
  levelTrace (U ⊓ ConjAct.toConjAct g • U) U
    (f ∘ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le
        (conjAct_inv_smul_inf_conjAct_smul_le U g)) ∘
      MulAction.orbitRelQuotientSMulEquiv g⁻¹ rfl)

/-- The Hecke operator at the orbit of `x` is the sum of `f((u g)⁻¹ • x)` over representatives
`u` of the cosets of `U ∩ gUg⁻¹` in `U`. -/
theorem heckeOperator_mk (U : Subgroup G) (g : G) (f : orbitRel.Quotient U α → M) (x : α) :
    heckeOperator U g f (Quotient.mk'' x) =
      ∑ᶠ c : U ⧸ (U ⊓ ConjAct.toConjAct g • U).subgroupOf U,
        f (Quotient.mk'' ((((c.out : U) : G) * g)⁻¹ • x)) := by
  rw [heckeOperator, levelTrace_mk]
  refine finsum_congr fun c ↦ ?_
  -- write `c` as the class of its chosen representative, which occurs on the right
  have hc := QuotientGroup.out_eq' c
  generalize c.out = u at hc ⊢
  subst hc
  simp only [Function.comp_apply, orbitOfCosetTranslate_mk, MulAction.orbitRelQuotientSMulEquiv_mk,
    TauCeti.Setoid.map_of_le_mk, mul_inv_rev, mul_smul]

/-- The Hecke operator of the identity is the identity. -/
@[simp]
theorem heckeOperator_one (U : Subgroup G) (f : orbitRel.Quotient U α → M) :
    heckeOperator U 1 f = f := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    rw [heckeOperator, levelTrace_of_le (V := U ⊓ ConjAct.toConjAct (1 : G) • U) (by simp)]
    simp only [Function.comp_apply, MulAction.orbitRelQuotientSMulEquiv_mk, inv_one, one_smul,
      TauCeti.Setoid.map_of_le_mk]

/-- The Hecke operator of `0` is `0`. -/
@[simp]
theorem heckeOperator_zero (U : Subgroup G) (g : G) :
    heckeOperator U g (0 : orbitRel.Quotient U α → M) = 0 :=
  levelTrace_zero _ _

/-- The Hecke operator is additive. -/
theorem heckeOperator_add (U : Subgroup G) (g : G)
    [(U ⊓ ConjAct.toConjAct g • U).IsFiniteRelIndex U]
    (f₁ f₂ : orbitRel.Quotient U α → M) :
    heckeOperator U g (f₁ + f₂) = heckeOperator U g f₁ + heckeOperator U g f₂ :=
  levelTrace_add _ _ _ _

/-- The Hecke operator commutes with scalar multiplication. -/
theorem heckeOperator_smul {R : Type*} [DistribSMul R M] (U : Subgroup G) (g : G)
    [(U ⊓ ConjAct.toConjAct g • U).IsFiniteRelIndex U] (r : R) (f : orbitRel.Quotient U α → M) :
    heckeOperator U g (r • f) = r • heckeOperator U g f :=
  levelTrace_smul _ _ r _

variable {R : Type*} [CommSemiring R]

/-- **The Hecke operators of `g` and `g⁻¹` are adjoint** for the stabiliser-weighted pairing:
`⟨[UgU] f, h⟩_U = ⟨f, [Ug⁻¹U] h⟩_U`, provided there are finitely many `U`-orbits, their
stabiliser orders are units, and `U ∩ gUg⁻¹` and `U ∩ g⁻¹Ug` have finite index in `U`. -/
theorem stabilizerWeightedPairing_heckeOperator {U : Subgroup G} {g : G}
    [(U ⊓ ConjAct.toConjAct g • U).IsFiniteRelIndex U]
    [(U ⊓ ConjAct.toConjAct g⁻¹ • U).IsFiniteRelIndex U] [Finite (orbitRel.Quotient U α)]
    (hunit : ∀ p : orbitRel.Quotient U α, IsUnit (cardStabilizerOnOrbit p : R))
    (f h : orbitRel.Quotient U α → R) :
    stabilizerWeightedPairing (heckeOperator U g f) h =
      stabilizerWeightedPairing f (heckeOperator U g⁻¹ h) := by
  -- translation by `g⁻¹` identifies the orbits of `U ∩ gUg⁻¹` with those of `U ∩ g⁻¹Ug`
  have hVV' : ConjAct.toConjAct g⁻¹ • (U ⊓ ConjAct.toConjAct g • U) =
      U ⊓ ConjAct.toConjAct g⁻¹ • U := by
    rw [Subgroup.smul_inf, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, inf_comm]
  -- both sides are pairings on these orbits, by the weighted adjunction for each trace
  rw [stabilizerWeightedPairing_comm, heckeOperator, stabilizerWeightedPairing_levelTrace
    inf_le_left hunit, heckeOperator, stabilizerWeightedPairing_levelTrace inf_le_left hunit,
    ← stabilizerWeightedPairing_comp_orbitRelQuotientSMulEquiv g⁻¹ hVV',
    stabilizerWeightedPairing_comm (_ ∘ _)]
  congr 1 <;> funext q <;> induction q using Quotient.inductionOn' <;>
    simp only [Function.comp_apply, MulAction.orbitRelQuotientSMulEquiv_mk,
      TauCeti.Setoid.map_of_le_mk, smul_smul, inv_inv, mul_inv_cancel, one_smul]

end Hecke

end TauCeti
