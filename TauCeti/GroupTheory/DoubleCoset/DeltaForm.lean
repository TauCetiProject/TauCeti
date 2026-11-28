/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.ClassSum
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Delta forms and their class sums

Let `G` be a group with subgroups `Γ` and `K`. Let `Γ` act on an additive monoid `W`, and let
`χ : K →* M` be a character with values in a monoid `M` that acts on `W`. A form of level
`(K, χ)` is a function `f : G → W` with `f (γ g k) = χ(k) • γ • f(g)` for `γ ∈ Γ`, `k ∈ K`. The
**delta form** at `x : G` made from `v : W` is

`δ_{x,v}(y) = ∑_{γ ∈ Γ, x⁻¹ γ y ∈ K} χ(x⁻¹ γ y) • γ⁻¹ • v`  (`TauCeti.deltaForm`).

It is supported on the double coset `Γ x K` (`TauCeti.deltaForm_eq_zero_of_mk_ne`). When `Γ` acts
by additive maps and the actions of `Γ` and `M` commute, it is left `Γ`-equivariant
(`TauCeti.deltaForm_mul_left`); when `M` acts by additive maps and the values of `χ` commute
with each other (for instance when `M` is commutative), it transforms by `χ` on the right
(`TauCeti.deltaForm_mul_right`). Under both sets of hypotheses it is a form of
level `(K, χ)`. In the application
`G` is the group of finite adelic points of a unitary group compact at infinity, `Γ` its rational
points acting on a Weyl module `W`, `K` a level and `M = ℂˣ`; the stabiliser
`Γ_x = Γ ∩ x K x⁻¹` (`TauCeti.mackeySubgroup x K Γ`) is the group of rational points stabilising
the coset `x K`.

The terms of `δ_{x,v}(y)` are indexed by `{γ : Γ // x⁻¹ * γ * y ∈ K}`. Off `Γ x K` this index set
is empty (`DoubleCoset.isEmpty_inv_mul_mul_mem_of_mk_ne`); on `Γ x K` it is equinumerous with
`Γ_x`, so the two have the same `Nat.card` (`TauCeti.natCard_inv_mul_mul_mem`), and both are `0`
when they are infinite. Below, `#Γ_x` denotes this `Nat.card`; a class whose stabiliser is
infinite therefore gets the weight `#Γ_x⁻¹ = 0⁻¹ = 0`.

## Main results

* `TauCeti.doubleCosetClassSum_deltaForm`: for additive maps `L g : W →+ W'` to a `ℚ`-vector
  space with `L (γ x k) (χ(k) • γ • v) = L x v` for `γ ∈ Γ`, `k ∈ K`, the class sum of
  `g ↦ L g (δ_{x,v}(g))`, in which the class of `g` is weighted by `#Γ_g⁻¹` (`0` when `Γ_g` is
  infinite), is `L x v`, provided `Γ_x` is finite. Only this compatibility at the base point `x`
  and the vector `v` is assumed, and no action axioms or commutation of the two actions.
* `TauCeti.deltaForm_mul_mul_smul_smul`: changing the base point to `γ x k` and the vector to
  `χ(k) • γ • v` does not change the delta form, when `χ(k)` commutes with the values of `χ` and
  the actions commute.
* `TauCeti.finsum_inv_natCard_smul_deltaForm`: pointwise reconstruction. For `f : G → W` with
  values in a `ℚ`-vector space and `f (γ g k) = χ(k) • γ • f(g)`, representatives `c q` of the
  double cosets, and a point `y` with `Γ_y` finite, `f(y) = ∑_q #Γ_{c q}⁻¹ • δ_{c q, f(c q)}(y)`,
  where classes with infinite stabiliser get the weight `0`.
* `TauCeti.deltaForm_eq_natCard_smul_of_mk_eq`: one summand of the reconstruction: for such `f`,
  `δ_{x, f(x)} = #Γ_x • f` on the double coset `Γ x K` (and `0` off it).
* `TauCeti.eq_finsum_deltaForm`: reconstruction as functions. If there are finitely many double
  cosets and every `Γ_g` is finite, `f = ∑_q #Γ_{c q}⁻¹ • δ_{c q, f(c q)}`, a finite sum. When the
  hypotheses of the two transformation laws hold, every summand is a form of level `(K, χ)`, so
  delta forms span the forms of level `(K, χ)`.
* `TauCeti.deltaForm_self`, `TauCeti.deltaForm_self_of_eq_bot`: at its base point,
  `δ_{x,v}(x) = #Γ_x • v` when every term `χ(x⁻¹ γ x) • γ⁻¹ • v` is `v`, and `δ_{x,v}(x) = v` when
  `Γ_x` is trivial and `M` and `Γ` act by monoid actions (so that `1` acts as the identity).
* `TauCeti.deltaForm_zero`, `TauCeti.deltaForm_add`, `TauCeti.deltaForm_smul`: for actions by
  additive maps the delta form is additive in the vector it is made from, and commutes with
  scalars acting by additive maps that commute with the actions of `M` and `Γ`.
* `TauCeti.deltaForm_eq_zero_of_infinite`: for actions by additive maps, the delta form at `x` is
  `0` when `Γ_x` is infinite (its sums then take the junk value `0` of `finsum`).

## References

* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93.

The statements follow the route of the folder `grh` of https://github.com/lsernau/grh-lean at
commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean` (`New.classSum_deltaForm`).
-/

public section

namespace TauCeti

variable {G M W W' : Type*} [Group G] (Γ : Subgroup G) {K : Subgroup G}

/-! ### Two sums over the index sets -/

section Counting

variable {Γ}

/-- The point at which a law at `x` sees the term of index `γ` at `y`: `γ⁻¹ x (x⁻¹ γ y) = y`. -/
private theorem coe_inv_mul_mul_inv_mul_mul (γ : Γ) (x y : G) :
    ((γ⁻¹ : Γ) : G) * x * (x⁻¹ * γ * y) = y := by
  simp [mul_assoc]

/-- On `Γ x K`, a sum of terms all equal to `c` over the `γ ∈ Γ` with `x⁻¹ γ y ∈ K` is
`#Γ_x • c`. No finiteness is needed: if `Γ_x` is infinite, both sides are `0`. -/
private theorem finsum_const_eq_natCard_smul [AddCommMonoid W'] {x y : G}
    (h : DoubleCoset.mk Γ K x = DoubleCoset.mk Γ K y)
    {f : {γ : Γ // x⁻¹ * γ * y ∈ K} → W'} {c : W'} (hf : ∀ γ, f γ = c) :
    ∑ᶠ γ, f γ = Nat.card (mackeySubgroup x K Γ) • c := by
  rw [finsum_congr hf, finsum_const, natCard_inv_mul_mul_mem h]

/-- On `Γ x K`, a sum of terms all equal to `c` over the `γ ∈ Γ` with `x⁻¹ γ y ∈ K`, weighted by
`#Γ_x⁻¹`, is `c`. -/
private theorem inv_natCard_smul_finsum_eq [AddCommMonoid W'] [Module ℚ W'] {x y : G}
    (h : DoubleCoset.mk Γ K x = DoubleCoset.mk Γ K y) [Finite (mackeySubgroup x K Γ)]
    {f : {γ : Γ // x⁻¹ * γ * y ∈ K} → W'} {c : W'} (hf : ∀ γ, f γ = c) :
    (Nat.card (mackeySubgroup x K Γ) : ℚ)⁻¹ • ∑ᶠ γ, f γ = c := by
  have := finite_inv_mul_mul_mem (s := x) (H := K) (K := Γ) y
  have : Nonempty {γ : Γ // x⁻¹ * γ * y ∈ K} := DoubleCoset.nonempty_inv_mul_mul_mem_iff.2 h.symm
  rw [finsum_congr hf, ← natCard_inv_mul_mul_mem h]
  exact inv_natCard_smul_finsum_const c

end Counting

/-! ### The delta form -/

section Definition

variable [AddCommMonoid W] [Monoid M] [SMul M W] [SMul Γ W]

/-- **The delta form** at `x` made from `v`, for a character `χ` of `K`:
`δ_{x,v}(y) = ∑ χ(x⁻¹ γ y) • γ⁻¹ • v`, the sum over the `γ ∈ Γ` with `x⁻¹ γ y ∈ K`. It is
supported on `Γ x K`. It is a form of level `(K, χ)` when `Γ` and `M` act by additive maps, the
two actions commute and the values of `χ` commute (`TauCeti.deltaForm_mul_left`,
`TauCeti.deltaForm_mul_right`). The sum is a `finsum`, so it is `0` when it has infinitely many
nonzero terms; it is a finite sum when `Γ ∩ x K x⁻¹` is finite. To work with the individual
summands, expand it with `TauCeti.deltaForm_def`. -/
noncomputable def deltaForm (χ : K →* M) (x : G) (v : W) (y : G) : W :=
  ∑ᶠ γ : {γ : Γ // x⁻¹ * γ * y ∈ K}, χ ⟨_, γ.property⟩ • ((γ : Γ)⁻¹ • v)

/-- The rewrite lemma that expands `TauCeti.deltaForm` into its defining `finsum` over the
`γ ∈ Γ` with `x⁻¹ γ y ∈ K`; the module system hides the body of the definition from importers. -/
theorem deltaForm_def (χ : K →* M) (x : G) (v : W) (y : G) :
    deltaForm Γ χ x v y = ∑ᶠ γ : {γ : Γ // x⁻¹ * γ * y ∈ K}, χ ⟨_, γ.property⟩ • ((γ : Γ)⁻¹ • v) :=
  (rfl)

variable {Γ}

/-- The delta form at `x` vanishes off the double coset `Γ x K`. -/
@[simp]
theorem deltaForm_eq_zero_of_mk_ne (χ : K →* M) {x y : G} (v : W)
    (h : DoubleCoset.mk Γ K y ≠ DoubleCoset.mk Γ K x) : deltaForm Γ χ x v y = 0 := by
  have := DoubleCoset.isEmpty_inv_mul_mul_mem_of_mk_ne h
  rw [deltaForm_def]
  exact finsum_of_isEmpty _

/-- **The delta form at its base point.** If every term of `δ_{x,v}(x)` is `v`, that is
`χ(x⁻¹ γ x) • γ⁻¹ • v = v` for the `γ ∈ Γ_x = Γ ∩ x K x⁻¹`, then `δ_{x,v}(x) = #Γ_x • v`.
Here `#Γ_x` is `Nat.card`: when `Γ_x` is infinite both sides are `0`. -/
theorem deltaForm_self (χ : K →* M) {x : G} {v : W}
    (hv : ∀ (γ : Γ) (hγ : x⁻¹ * γ * x ∈ K), χ ⟨_, hγ⟩ • γ⁻¹ • v = v) :
    deltaForm Γ χ x v x = Nat.card (mackeySubgroup x K Γ) • v := by
  rw [deltaForm_def]
  exact finsum_const_eq_natCard_smul rfl fun γ ↦ hv γ γ.property

/-- **One summand of the reconstruction.** Let `f` satisfy `f (γ g k) = χ(k) • γ • f(g)`. On the
double coset `Γ x K`, the delta form at `x` made from `f(x)` is `#Γ_x • f`; off it, it is `0`
(`TauCeti.deltaForm_eq_zero_of_mk_ne`). Here `#Γ_x` is `Nat.card`, `0` when `Γ_x` is infinite. -/
theorem deltaForm_eq_natCard_smul_of_mk_eq (χ : K →* M) {f : G → W}
    (hf : ∀ g (γ : Γ) (k : K), f (γ * g * k) = χ k • γ • f g) {x y : G}
    (h : DoubleCoset.mk Γ K x = DoubleCoset.mk Γ K y) :
    deltaForm Γ χ x (f x) y = Nat.card (mackeySubgroup x K Γ) • f y := by
  rw [deltaForm_def]
  -- Each term is `f(y)`, as `y = γ⁻¹ x (x⁻¹ γ y)`.
  refine finsum_const_eq_natCard_smul h fun γ ↦ ?_
  have := hf x (γ : Γ)⁻¹ ⟨_, γ.property⟩
  rw [coe_inv_mul_mul_inv_mul_mul] at this
  exact this.symm

end Definition

section Laws

variable {Γ} [AddCommMonoid W]

/-- **The delta form is left equivariant** under `Γ`: `δ_{x,v}(γ₀ y) = γ₀ • δ_{x,v}(y)`, when `Γ`
acts by additive maps and its action commutes with the action of `M`. -/
theorem deltaForm_mul_left [Monoid M] [SMul M W] [DistribMulAction Γ W] [SMulCommClass M Γ W]
    (χ : K →* M) (x : G) (v : W) (γ₀ : Γ) (y : G) :
    deltaForm Γ χ x v (γ₀ * y) = γ₀ • deltaForm Γ χ x v y := by
  -- Reindex the sum at `y` by `γ ↦ γ γ₀`.
  let e := DoubleCoset.invMulMulMemEquivOfEq x γ₀ (1 : K) (y := y) (y' := γ₀ * y) (by simp)
  rw [deltaForm_def, deltaForm_def, (Group.isUnit γ₀).smul_finsum,
    ← finsum_comp_equiv e]
  refine finsum_congr fun γ ↦ ?_
  have hχ : χ ⟨_, (e γ).property⟩ = χ ⟨_, γ.property⟩ :=
    congrArg χ (Subtype.ext (by simp [e, mul_assoc]))
  have he : ((e γ : Γ))⁻¹ = γ₀⁻¹ * (γ : Γ)⁻¹ := by simp [e]
  rw [hχ, he, ← smul_comm _ γ₀, mul_smul, smul_inv_smul]

/-- **The delta form transforms by `χ` on the right**: `δ_{x,v}(y k) = χ(k) • δ_{x,v}(y)`, when
`M` acts by additive maps and `χ(k)` commutes with the values of `χ` (for instance when `M` is
commutative). -/
theorem deltaForm_mul_right [Monoid M] [DistribMulAction M W] [SMul Γ W] (χ : K →* M)
    (x : G) (v : W) (y : G) (k : K) (hk : ∀ k', Commute (χ k) (χ k')) :
    deltaForm Γ χ x v (y * k) = χ k • deltaForm Γ χ x v y := by
  -- The index sets at `y k` and at `y` are the same: reindex by `γ ↦ γ * 1`.
  let e := DoubleCoset.invMulMulMemEquivOfEq x (1 : Γ) k (y := y) (y' := y * k) (by simp)
  have he (γ) : (e γ : Γ) = γ := by simp [e]
  -- `χ k` is a unit, so acting by it commutes with the `finsum`.
  rw [deltaForm_def, deltaForm_def, ((Group.isUnit k).map χ).smul_finsum,
    ← finsum_comp_equiv e]
  refine finsum_congr fun γ ↦ ?_
  have hχ : χ ⟨_, γ.property⟩ = χ k * χ ⟨_, (e γ).property⟩ := by
    rw [(hk _).eq, ← map_mul]
    exact congrArg χ (Subtype.ext (by simp [he, mul_assoc]))
  rw [hχ, mul_smul]
  simp only [he]

/-- **The delta form at its base point, for a trivial stabiliser**: if `Γ ∩ x K x⁻¹ = ⊥` and `M`
and `Γ` act by monoid actions (so that `1` acts as the identity), then `δ_{x,v}(x) = v`. -/
@[simp]
theorem deltaForm_self_of_eq_bot [Monoid M] [MulAction M W] [MulAction Γ W] (χ : K →* M) {x : G}
    (v : W) (h : mackeySubgroup x K Γ = ⊥) : deltaForm Γ χ x v x = v := by
  -- The only `γ ∈ Γ` with `x⁻¹ γ x ∈ K` is `γ = 1`.
  have hv (γ : Γ) (hγ : x⁻¹ * γ * x ∈ K) : χ ⟨_, hγ⟩ • γ⁻¹ • v = v := by
    have h1 : (γ : G) = 1 := by
      rw [← Subgroup.mem_bot, ← h, mem_mackeySubgroup_iff]
      exact ⟨γ.property, hγ⟩
    have hk : (⟨_, hγ⟩ : K) = 1 := Subtype.ext (by simp [h1])
    have hγ1 : γ = 1 := Subtype.ext h1
    rw [hk, map_one, one_smul, hγ1, inv_one, one_smul]
  rw [deltaForm_self χ hv, h, Subgroup.card_bot, one_smul]

/-- **Changing the base point.** Moving the base point from `x` to `γ₀ x k₀` and the vector from
`v` to `χ(k₀) • γ₀ • v` does not change the delta form, when `χ(k₀)` commutes with the values of
`χ` (for instance when `M` is commutative) and the actions of `M` and `Γ` commute:
`δ_{γ₀ x k₀, χ(k₀) • γ₀ • v} = δ_{x,v}`. -/
theorem deltaForm_mul_mul_smul_smul [Monoid M] [MulAction M W] [MulAction Γ W]
    [SMulCommClass M Γ W] (χ : K →* M) (x : G) (v : W) (γ₀ : Γ) (k₀ : K)
    (hk₀ : ∀ k', Commute (χ k₀) (χ k')) :
    deltaForm Γ χ (γ₀ * x * k₀) (χ k₀ • γ₀ • v) = deltaForm Γ χ x v := by
  funext y
  -- Reindex the sum at the base point `γ₀ x k₀` by `γ ↦ γ₀⁻¹ γ`.
  let e := DoubleCoset.invMulMulMemEquivOfBaseEq (x := x) (x' := γ₀ * x * k₀) y γ₀ k₀ rfl
  rw [deltaForm_def, deltaForm_def, ← finsum_comp_equiv e]
  refine finsum_congr fun γ ↦ ?_
  have he : (e γ : Γ) = γ₀⁻¹ * γ := by simp [e]
  have hχ : χ ⟨_, (e γ).property⟩ = χ ⟨_, γ.property⟩ * χ k₀ := by
    rw [← (hk₀ _).eq, ← map_mul]
    exact congrArg χ (Subtype.ext (by simp [he, mul_assoc]))
  have he' : ((e γ : Γ))⁻¹ = (γ : Γ)⁻¹ * γ₀ := by rw [he, mul_inv_rev, inv_inv]
  rw [hχ, he', mul_smul, mul_smul, ← smul_comm (χ k₀) (γ : Γ)⁻¹]

end Laws

/-! ### Additivity in the vector -/

section Additive

variable {Γ} [AddCommMonoid W] [Monoid M]

/-- The delta form made from `0` is `0`, when both scalar operations preserve zero. -/
@[simp]
theorem deltaForm_zero [SMulZeroClass M W] [SMulZeroClass Γ W] (χ : K →* M) (x : G) :
    deltaForm Γ χ x (0 : W) = 0 := by
  funext y
  simp [deltaForm_def]

/-- With infinitely many terms the delta form is the junk value `0` of `finsum`: for actions by
additive maps, every term made from `v ≠ 0` is nonzero, as `χ` takes unit values. -/
private theorem deltaForm_eq_zero_of_infinite_index [DistribMulAction M W]
    [DistribMulAction Γ W] (χ : K →* M) {x y : G} (v : W)
    (h : Infinite {γ : Γ // x⁻¹ * γ * y ∈ K}) : deltaForm Γ χ x v y = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  rw [deltaForm_def]
  refine finsum_of_infinite_support ?_
  rw [Set.eq_univ_of_forall fun γ ↦ Function.mem_support.2 fun h ↦
    hv ((smul_eq_zero_iff_eq _).1 (((Group.isUnit _).map χ).smul_eq_zero.1 h))]
  exact Set.infinite_univ

/-- If `Γ_x = Γ ∩ x K x⁻¹` is infinite, the delta form at `x` is `0`, for actions by additive
maps: on `Γ x K` its sums have infinitely many nonzero terms (or are made from `v = 0`), so they
take the junk value `0` of `finsum`, and off `Γ x K` they are empty. -/
@[simp]
theorem deltaForm_eq_zero_of_infinite [DistribMulAction M W] [DistribMulAction Γ W]
    (χ : K →* M) {x : G} [Infinite (mackeySubgroup x K Γ)] (v : W) : deltaForm Γ χ x v = 0 := by
  funext y
  by_cases h : DoubleCoset.mk Γ K y = DoubleCoset.mk Γ K x
  · -- On `Γ x K` the index set at `y` is equivalent to `Γ_x`.
    let e := (nonempty_equiv_mackeySubgroup_of_mk_eq h.symm).some
    exact deltaForm_eq_zero_of_infinite_index χ v (Infinite.of_injective _ e.symm.injective)
  · exact deltaForm_eq_zero_of_mk_ne χ v h

/-- The delta form is additive in the vector it is made from:
`δ_{x,v+w} = δ_{x,v} + δ_{x,w}`. No finiteness is needed: with infinitely many terms all three
delta forms are `0`. -/
theorem deltaForm_add [DistribMulAction M W] [DistribMulAction Γ W] (χ : K →* M) (x : G)
    (v w : W) : deltaForm Γ χ x (v + w) = deltaForm Γ χ x v + deltaForm Γ χ x w := by
  funext y
  rcases finite_or_infinite {γ : Γ // x⁻¹ * γ * y ∈ K} with h | h
  · simp only [Pi.add_apply, deltaForm_def, smul_add]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  · simp only [Pi.add_apply, deltaForm_eq_zero_of_infinite_index χ _ h, add_zero]

/-- The delta form commutes with scalars `r` whose additive action commutes with those of `M` and
`Γ`: `δ_{x, r • v} = r • δ_{x,v}`. No finiteness is needed: with infinitely many terms both
delta forms are `0`. -/
theorem deltaForm_smul {R : Type*} [DistribMulAction M W] [DistribMulAction Γ W]
    [DistribSMul R W] [SMulCommClass R M W] [SMulCommClass R Γ W] (χ : K →* M) (x : G) (r : R)
    (v : W) : deltaForm Γ χ x (r • v) = r • deltaForm Γ χ x v := by
  funext y
  rcases finite_or_infinite {γ : Γ // x⁻¹ * γ * y ∈ K} with h | h
  · simp only [Pi.smul_apply, deltaForm_def, smul_finsum' r (Set.toFinite _)]
    exact finsum_congr fun γ ↦ by rw [← smul_comm r, ← smul_comm r]
  · simp only [Pi.smul_apply, deltaForm_eq_zero_of_infinite_index χ _ h, smul_zero]

end Additive

/-! ### The class sum of a delta form -/

section ClassSum

variable {Γ} [AddCommMonoid W] [Monoid M] [SMul M W] [SMul Γ W] {χ : K →* M}

/-- **The class sum of a delta form.** Let `L g : W →+ W'` be additive maps to a `ℚ`-vector space
with `L (γ x k) (χ(k) • γ • v) = L x v` for `γ ∈ Γ` and `k ∈ K`. If `Γ_x = Γ ∩ x K x⁻¹` is finite,
the weighted class sum `∑_{Γ g K} #Γ_g⁻¹ • L g (δ_{x,v}(g))` is `L x v`. Here `#Γ_g` is
`Nat.card`, so a class with infinite stabiliser `Γ_g` has the weight `0`. -/
theorem doubleCosetClassSum_deltaForm [AddCommGroup W'] [Module ℚ W'] (x : G) (v : W)
    [Finite (mackeySubgroup x K Γ)]
    (L : G → W →+ W') (hL : ∀ (γ : Γ) (k : K), L (γ * x * k) (χ k • γ • v) = L x v) :
    doubleCosetClassSum Γ K (fun g ↦ L g (deltaForm Γ χ x v g)) = L x v := by
  -- Only the class of `x` contributes; let `y` be its chosen representative.
  rw [doubleCosetClassSum_def, finsum_eq_single _ (DoubleCoset.mk Γ K x) fun q hq ↦ by
    rw [deltaForm_eq_zero_of_mk_ne χ v fun h ↦ hq ((DoubleCoset.out_eq' q).symm.trans h),
      map_zero, smul_zero]]
  set y := (DoubleCoset.mk Γ K x).out
  have hy : DoubleCoset.mk Γ K x = DoubleCoset.mk Γ K y := (DoubleCoset.out_eq' _).symm
  -- `Γ_y` is conjugate to `Γ_x`, so it has the same cardinality.
  have hcard : Nat.card (mackeySubgroup y K Γ) = Nat.card (mackeySubgroup x K Γ) :=
    (Nat.card_congr (nonempty_mulEquiv_mackeySubgroup_of_mk_eq hy).some.toEquiv).symm
  -- Each of the `#Γ_x` terms of `δ_{x,v}(y)` is sent to `L x v` by `L y`.
  have hterm (γ : {γ : Γ // x⁻¹ * γ * y ∈ K}) :
      L y (χ ⟨_, γ.property⟩ • (γ : Γ)⁻¹ • v) = L x v := by
    have := hL (γ : Γ)⁻¹ ⟨_, γ.property⟩
    rwa [coe_inv_mul_mul_inv_mul_mul] at this
  have := finite_inv_mul_mul_mem (s := x) (H := K) (K := Γ) y
  rw [deltaForm_def, (L y).map_finsum (Set.toFinite _), hcard,
    inv_natCard_smul_finsum_eq hy hterm]

end ClassSum

/-! ### Reconstruction from delta forms -/

section Reconstruction

variable {Γ} [AddCommMonoid W] [Module ℚ W] [Monoid M] [SMul M W] [SMul Γ W] {χ : K →* M}

/-- **Reconstruction from delta forms**, pointwise. Let `f` satisfy
`f (γ g k) = χ(k) • γ • f(g)` and take values in a `ℚ`-vector space, let `c q` be representatives
of the double cosets, and let `Γ_y` be finite. Then `f(y) = ∑_q #Γ_{c q}⁻¹ • δ_{c q, f(c q)}(y)`.
Here `#Γ_{c q}` is `Nat.card`, so a class with infinite stabiliser has the weight `0`; only the
class of `y` contributes, and its stabiliser is finite. -/
theorem finsum_inv_natCard_smul_deltaForm {f : G → W}
    (hf : ∀ g (γ : Γ) (k : K), f (γ * g * k) = χ k • γ • f g)
    (c : DoubleCoset.Quotient (Γ : Set G) K → G) (hc : ∀ q, DoubleCoset.mk Γ K (c q) = q) (y : G)
    [Finite (mackeySubgroup y K Γ)] :
    ∑ᶠ q, (Nat.card (mackeySubgroup (c q) K Γ) : ℚ)⁻¹ • deltaForm Γ χ (c q) (f (c q)) y =
      f y := by
  rw [finsum_eq_single _ (DoubleCoset.mk Γ K y) fun q hq ↦ by
    rw [deltaForm_eq_zero_of_mk_ne χ _ fun h ↦ hq ((hc q).symm.trans h.symm), smul_zero]]
  set x := c (DoubleCoset.mk Γ K y)
  have hx : DoubleCoset.mk Γ K x = DoubleCoset.mk Γ K y := hc _
  -- `Γ_x` is conjugate to the finite `Γ_y`.
  have : Finite (mackeySubgroup x K Γ) :=
    Finite.of_equiv _ (nonempty_mulEquiv_mackeySubgroup_of_mk_eq hx).some.symm.toEquiv
  -- Each term of `δ_{x, f(x)}(y)` is `f(y)`, since `y = γ⁻¹ x (x⁻¹ γ y)`.
  rw [deltaForm_eq_natCard_smul_of_mk_eq χ hf hx, ← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne') _

/-- **Reconstruction from delta forms.** If there are finitely many classes `Γ \ G / K` and
every `Γ_g` is finite, a function `f` with `f (γ g k) = χ(k) • γ • f(g)` and values in a
`ℚ`-vector space is the finite combination `f = ∑_q #Γ_{c q}⁻¹ • δ_{c q, f(c q)}` of delta forms
at representatives `c q` of the double cosets. Under the hypotheses of
`TauCeti.deltaForm_mul_left` and `TauCeti.deltaForm_mul_right` each summand is a form of level
`(K, χ)`, so delta forms span the forms of level `(K, χ)`. -/
theorem eq_finsum_deltaForm [Finite (DoubleCoset.Quotient (Γ : Set G) K)] {f : G → W}
    (hf : ∀ g (γ : Γ) (k : K), f (γ * g * k) = χ k • γ • f g)
    (c : DoubleCoset.Quotient (Γ : Set G) K → G) (hc : ∀ q, DoubleCoset.mk Γ K (c q) = q)
    (hfin : ∀ g, Finite (mackeySubgroup g K Γ)) :
    f = ∑ᶠ q, (Nat.card (mackeySubgroup (c q) K Γ) : ℚ)⁻¹ • deltaForm Γ χ (c q) (f (c q)) := by
  funext y
  have := hfin y
  rw [finsum_apply (Set.toFinite _), ← finsum_inv_natCard_smul_deltaForm hf c hc y]
  simp only [Pi.smul_apply]

end Reconstruction

end TauCeti
