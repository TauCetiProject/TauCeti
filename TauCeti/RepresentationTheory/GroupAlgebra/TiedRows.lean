/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic

/-!
# The tie ideal and tied rows

Ribet's method to first order works in the group algebra `R_J[G]` of a monoid `G` over the
polynomial ring `R_J = O[X_j : j ∈ J]`. Finitely many representations `u_x` of `G` are extended to
`R_J`-algebra maps `u_x : R_J[G] → A`, and auxiliary elements `τ_k, φ_k ∈ G` are *tied* to a
variable `X_{κ(k)}`: the relation `τ_k - 1 = X_{κ(k)} ε_{κ(k)}(φ_k) (φ_k - 1)` is imposed, for a
polynomial `ε_j ∈ O[X]`. With `I` the augmentation ideal of `R_J[G]`, `p ∈ O` and `ρ₀ ∈ R_J[G]`,
the **tie ideal** (`TauCeti.tieIdeal`) is the left ideal of `R_J[G]` spanned by

* the elements killed by every `u_x`,
* `p I`,
* the ties `τ_k - 1 - X_{κ(k)} ε_{κ(k)}(φ_k) (φ_k - 1)`, and
* `I ρ₀`.

For elements `gen_i ∈ G`, a row `(r_i)` over `R[G]` is **tied** modulo a left ideal `𝔞` if
`∑_i r_i (gen_i - 1)` lies in `𝔞` (`TauCeti.tiedRows`); the tied rows of Ribet's method are those
for the tie ideal. Modulo `0` they are the relation module `TauCeti.MonoidAlgebra.relationModule`
of the `gen_i`. They form a left `R[G]`-submodule, and the matrices of Ribet's method are
built from them: a square matrix of tied rows `B` has `B y` in the tie ideal, for `y` the column
of the `gen_i - 1`.

When the elements `z g` of `R[G]^ι` are coordinates of the `g - 1` in the `gen_i - 1` modulo `𝔞`,
the rows given by the cocycle rule, by the generators and by the linear relations among the
`g - 1` are tied (`TauCeti.sub_sub_smul_mem_tiedRows`, `TauCeti.sub_single_mem_tiedRows_iff`,
`TauCeti.linearCombination_mem_tiedRows`). For the tie ideal, so are the rows given by the ties
(`TauCeti.sub_X_smul_mem_tiedRows_tieIdeal`) and the multiples by `g - 1` of the row
(`TauCeti.tiedNormaliserRow`) of the **tied normaliser** `ρ₀ = n + (1 - n)(a - 1)`,
`n = c₁ (γ - 1)` (`TauCeti.tiedNormaliser`). The tied normaliser acts as `1` on a representation
in which `γ` acts by a scalar `y` with `c₁ (y - 1) = 1`, and as `χ(a) - 1` on a character `χ`
trivial on `γ`; in particular it lies in the augmentation ideal.

## Main definitions

* `TauCeti.tiedRows gen 𝔞`: the rows `r` with `∑_i r_i (gen_i - 1) ∈ 𝔞`.
* `TauCeti.tieIdeal u p κ τ φ ε ρ₀`: the tie ideal.
* `TauCeti.tiedNormaliser γ a c₁`: the element `n + (1 - n)(a - 1)`, `n = c₁ (γ - 1)`.
* `TauCeti.tiedNormaliserRow z γ a c₁`: its row `c₁ z γ + (1 - n) z a`.

## Main results

* `TauCeti.mem_tiedRows`, `TauCeti.tiedRows_mono`, `TauCeti.single_mem_tiedRows_iff`, and
  `TauCeti.tiedRows_bot`: tied modulo `0` means a relation.
* `TauCeti.tieIdeal_le_iff`: the universal property of the tie ideal, with its four introduction
  rules `TauCeti.iInf_ker_le_tieIdeal`, `TauCeti.smul_mem_tieIdeal`, `TauCeti.tie_mem_tieIdeal`
  and `TauCeti.mul_mem_tieIdeal`, and `TauCeti.mem_tieIdeal_of_forall_eq_zero`.
* `TauCeti.sub_sub_smul_mem_tiedRows`, `TauCeti.sub_single_mem_tiedRows_iff`,
  `TauCeti.linearCombination_mem_tiedRows`: the cocycle, generator and relation rows are tied.
* `TauCeti.smul_mem_tiedRows_tieIdeal`, `TauCeti.sub_X_smul_mem_tiedRows_tieIdeal`,
  `TauCeti.sub_one_smul_tiedNormaliserRow_mem_tiedRows_tieIdeal`: `p` times any row, the tie rows
  and the multiples of the normaliser row are tied for the tie ideal.
* `TauCeti.map_tiedNormaliser_of_eq_algebraMap`, `TauCeti.map_tiedNormaliser_of_eq_one`,
  `TauCeti.augmentation_tiedNormaliser`: the values of the tied normaliser.
* `TauCeti.map_sub_one_mul_tiedNormaliserRow`: where `γ` acts by a scalar `y` with
  `c₁ (y - 1) = 1`, the tied row `(γ - 1) (c₁ z γ + (1 - n) z a)` has the image of `z γ`.

## Provenance

The tie ideal, the tied rows and the tied normaliser, and the tied relations, are adapted from
grh-lean (https://github.com/lsernau/grh-lean, file
`src/New/Congruences/FirstOrder/RibetMatrices.lean`, Apache 2.0, Copyright 2026 Anthropic, PBC):
`New.Selmer.tieIdeal`, `New.Selmer.tiedRows`, `New.Selmer.tiedNormaliser`,
`New.Selmer.normaliserRow` and the lemmas `New.Selmer.coordRows_cocycle_mem_tiedRows`,
`New.Selmer.coordRows_gen_sub_single_mem_tiedRows`,
`New.Selmer.coordRows_linearCombination_mem_tiedRows`, `New.Selmer.coordRows_tau_sub_mem_tiedRows`,
`New.Selmer.sub_one_smul_normaliserRow_mem_tiedRows` and
`New.Selmer.exists_mem_tiedRows_polyActionAtZero_eq`. Here the representations enter only through
their extensions to the group algebra, and coordinates are taken modulo an arbitrary left ideal.

## References

* J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), for Ribet's method.
-/

public section

open MonoidAlgebra

namespace TauCeti

/-! ### Tied rows modulo a left ideal -/

section TiedRows

variable {R G ι : Type*} [Ring R] [Monoid G] [Fintype ι]

/-- The rows tied modulo a left ideal `𝔞` of `R[G]`, for elements `gen i` of `G`: the rows `r` over
`R[G]` with `∑ i, r i * (gen i - 1) ∈ 𝔞`. They form a left `R[G]`-submodule. -/
noncomputable def tiedRows (gen : ι → G) (𝔞 : Ideal R[G]) : Submodule R[G] (ι → R[G]) :=
  Submodule.comap (Fintype.linearCombination R[G] fun i ↦ single (gen i) (1 : R) - 1) 𝔞

variable {gen : ι → G} {𝔞 𝔟 : Ideal R[G]}

@[simp]
theorem mem_tiedRows {r : ι → R[G]} :
    r ∈ tiedRows gen 𝔞 ↔ ∑ i, r i * (single (gen i) 1 - 1) ∈ 𝔞 :=
  Iff.rfl

/-- Rows tied modulo `𝔞` are tied modulo every larger left ideal. -/
theorem tiedRows_mono (h : 𝔞 ≤ 𝔟) : tiedRows gen 𝔞 ≤ tiedRows gen 𝔟 :=
  Submodule.comap_mono h

/-- The rows tied modulo `0` are the relation module of the `gen i`. -/
@[simp]
theorem tiedRows_bot : tiedRows gen (⊥ : Ideal R[G]) = MonoidAlgebra.relationModule R G gen := by
  ext r
  simp

/-- The relations among the `gen i - 1` are tied modulo every left ideal. -/
theorem relationModule_le_tiedRows : MonoidAlgebra.relationModule R G gen ≤ tiedRows gen 𝔞 :=
  (tiedRows_bot (R := R) (gen := gen)).symm.le.trans (tiedRows_mono bot_le)

/-- The row with the single entry `c` at `i` is tied exactly when `c (gen i - 1)` lies in `𝔞`. -/
theorem single_mem_tiedRows_iff [DecidableEq ι] {i : ι} {c : R[G]} :
    Pi.single i c ∈ tiedRows gen 𝔞 ↔ c * (single (gen i) 1 - 1) ∈ 𝔞 := by
  rw [mem_tiedRows, Fintype.sum_eq_single i fun j hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul],
    Pi.single_eq_same]

variable {z : G → ι → R[G]}

/-- The cocycle rule. If the rows `z g` are coordinates of the `g - 1` in the `gen i - 1` modulo
`𝔞`, then the row `z (g h) - z g - g z h` is tied modulo `𝔞`. -/
theorem sub_sub_smul_mem_tiedRows
    (hz : ∀ g, ∑ i, z g i * (single (gen i) 1 - 1) - (single g 1 - 1) ∈ 𝔞) (g h : G) :
    z (g * h) - z g - single g (1 : R) • z h ∈ tiedRows gen 𝔞 := by
  have key : ∑ i, (z (g * h) - z g - single g (1 : R) • z h) i * (single (gen i) 1 - 1) =
      (∑ i, z (g * h) i * (single (gen i) 1 - 1) - (single (g * h) 1 - 1)) -
        (∑ i, z g i * (single (gen i) 1 - 1) - (single g 1 - 1)) -
        single g 1 * (∑ i, z h i * (single (gen i) 1 - 1) - (single h 1 - 1)) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, mul_sub,
      Finset.mul_sum, mul_assoc, single_mul_single, mul_one]
    abel
  rw [mem_tiedRows, key]
  exact sub_mem (sub_mem (hz _) (hz g)) (Ideal.mul_mem_left _ _ (hz h))

/-- A row `w` gives coordinates of `gen i - 1` in the `gen j - 1` modulo `𝔞` exactly when `w`
minus the unit row at `i` is tied modulo `𝔞`. -/
theorem sub_single_mem_tiedRows_iff [DecidableEq ι] {w : ι → R[G]} {i : ι} :
    w - Pi.single i 1 ∈ tiedRows gen 𝔞 ↔
      ∑ j, w j * (single (gen j) 1 - 1) - (single (gen i) 1 - 1) ∈ 𝔞 := by
  have key : ∑ j, (w - Pi.single i 1 : ι → R[G]) j * (single (gen j) 1 - 1) =
      ∑ j, w j * (single (gen j) 1 - 1) - (single (gen i) 1 - 1) := by
    simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  rw [mem_tiedRows, key]

/-- The linear relations. If the rows `z g` are coordinates of the `g - 1` in the `gen i - 1`
modulo `𝔞`, and `∑_g θ g (g - 1)` lies in `𝔞`, then the row `∑_g θ g z g` is tied modulo `𝔞`. -/
theorem linearCombination_mem_tiedRows
    (hz : ∀ g, ∑ i, z g i * (single (gen i) 1 - 1) - (single g 1 - 1) ∈ 𝔞) (θ : G →₀ R[G])
    (hθ : Finsupp.linearCombination R[G] (fun g ↦ single g (1 : R) - 1) θ ∈ 𝔞) :
    Finsupp.linearCombination R[G] z θ ∈ tiedRows gen 𝔞 := by
  have key : ∑ i, Finsupp.linearCombination R[G] z θ i * (single (gen i) 1 - 1) =
      ∑ g ∈ θ.support, θ g * (∑ i, z g i * (single (gen i) 1 - 1) - (single g (1 : R) - 1)) +
        Finsupp.linearCombination R[G] (fun g ↦ single g (1 : R) - 1) θ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_add_distrib, mul_sub,
      sub_add_cancel, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      mul_assoc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  rw [mem_tiedRows, key]
  exact add_mem (Submodule.sum_mem _ fun g _ ↦ Ideal.mul_mem_left _ _ (hz g)) hθ

end TiedRows

/-! ### The tie ideal -/

section TieIdeal

variable {O G J K Y A : Type*} [CommRing O] [Monoid G] [Semiring A] [Algebra (MvPolynomial J O) A]

/-- The **tie ideal** of Ribet's method to first order, in the group algebra `R_J[G]` of `G` over
`R_J = O[X_j : j ∈ J]`. For `R_J`-algebra maps `u x : R_J[G] → A` (the representations), `p ∈ O`,
elements `τ k, φ k ∈ G` tied to the variables `X (κ k)`, polynomials `ε j ∈ O[X]` and
`ρ₀ ∈ R_J[G]`, it is the left ideal spanned by the elements that every `u x` kills, by `p I`, by
the ties `τ k - 1 - X (κ k) • (ε (κ k))(φ k) (φ k - 1)` and by `I ρ₀`, where `I` is the
augmentation ideal. -/
noncomputable def tieIdeal (u : Y → (MvPolynomial J O)[G] →ₐ[MvPolynomial J O] A) (p : O)
    (κ : K → J) (τ φ : K → G) (ε : J → Polynomial O) (ρ₀ : (MvPolynomial J O)[G]) :
    Ideal (MvPolynomial J O)[G] :=
  (⨅ x, RingHom.ker (u x)) ⊔
    Submodule.map (LinearMap.mulRight _ (algebraMap O (MvPolynomial J O)[G] p))
      (RingHom.ker (augmentation (MvPolynomial J O) G)) ⊔
    Submodule.span _ (Set.range fun k ↦ single (τ k) 1 - 1 -
      (MvPolynomial.X (κ k) : MvPolynomial J O) •
        (Polynomial.aeval (single (φ k) (1 : MvPolynomial J O)) (ε (κ k)) *
          (single (φ k) 1 - 1))) ⊔
    Submodule.map (LinearMap.mulRight _ ρ₀) (RingHom.ker (augmentation (MvPolynomial J O) G))

variable {u : Y → (MvPolynomial J O)[G] →ₐ[MvPolynomial J O] A} {p : O} {κ : K → J} {τ φ : K → G}
  {ε : J → Polynomial O} {ρ₀ : (MvPolynomial J O)[G]}

/-- The tie ideal is the smallest left ideal that contains the elements every `u x` kills, the
`p r` and `r ρ₀` for `r` in the augmentation ideal, and the ties. -/
theorem tieIdeal_le_iff {𝔟 : Ideal (MvPolynomial J O)[G]} :
    tieIdeal u p κ τ φ ε ρ₀ ≤ 𝔟 ↔ (⨅ x, RingHom.ker (u x)) ≤ 𝔟 ∧
      (∀ r ∈ RingHom.ker (augmentation (MvPolynomial J O) G), p • r ∈ 𝔟) ∧
      (∀ k, single (τ k) 1 - 1 - (MvPolynomial.X (κ k) : MvPolynomial J O) •
        (Polynomial.aeval (single (φ k) (1 : MvPolynomial J O)) (ε (κ k)) *
          (single (φ k) 1 - 1)) ∈ 𝔟) ∧
      ∀ r ∈ RingHom.ker (augmentation (MvPolynomial J O) G), r * ρ₀ ∈ 𝔟 := by
  simp only [tieIdeal, sup_le_iff, Submodule.map_le_iff_le_comap, Submodule.span_le,
    Set.range_subset_iff, SetLike.mem_coe, IsConcreteLE.le_iff (S := RingHom.ker _),
    Submodule.mem_comap, LinearMap.mulRight_apply, ← Algebra.commutes, ← Algebra.smul_def,
    and_assoc]

/-- The elements that every `u x` kills lie in the tie ideal. -/
theorem iInf_ker_le_tieIdeal : (⨅ x, RingHom.ker (u x)) ≤ tieIdeal u p κ τ φ ε ρ₀ :=
  (tieIdeal_le_iff.mp le_rfl).1

/-- `p` times an element of the augmentation ideal lies in the tie ideal. -/
theorem smul_mem_tieIdeal {r : (MvPolynomial J O)[G]}
    (hr : r ∈ RingHom.ker (augmentation (MvPolynomial J O) G)) :
    p • r ∈ tieIdeal u p κ τ φ ε ρ₀ :=
  (tieIdeal_le_iff.mp le_rfl).2.1 r hr

/-- The tie `τ k - 1 - X (κ k) • (ε (κ k))(φ k) (φ k - 1)` lies in the tie ideal. -/
theorem tie_mem_tieIdeal (k : K) :
    single (τ k) 1 - 1 - (MvPolynomial.X (κ k) : MvPolynomial J O) •
      (Polynomial.aeval (single (φ k) (1 : MvPolynomial J O)) (ε (κ k)) * (single (φ k) 1 - 1)) ∈
      tieIdeal u p κ τ φ ε ρ₀ :=
  (tieIdeal_le_iff.mp le_rfl).2.2.1 k

/-- An element of the augmentation ideal times `ρ₀` lies in the tie ideal. -/
theorem mul_mem_tieIdeal {r : (MvPolynomial J O)[G]}
    (hr : r ∈ RingHom.ker (augmentation (MvPolynomial J O) G)) :
    r * ρ₀ ∈ tieIdeal u p κ τ φ ε ρ₀ :=
  (tieIdeal_le_iff.mp le_rfl).2.2.2 r hr

/-- An element that every `u x` kills lies in the tie ideal. In particular, coordinates of the
`u x g - 1` in the `u x (gen i) - 1` are coordinates of the `g - 1` modulo the tie ideal. -/
theorem mem_tieIdeal_of_forall_eq_zero {a : (MvPolynomial J O)[G]} (h : ∀ x, u x a = 0) :
    a ∈ tieIdeal u p κ τ φ ε ρ₀ :=
  iInf_ker_le_tieIdeal (Submodule.mem_iInf _ |>.mpr fun x ↦ RingHom.mem_ker.mpr (h x))

variable {ι : Type*} [Fintype ι] {gen : ι → G}

/-- `p` times any row is tied for the tie ideal. -/
theorem smul_mem_tiedRows_tieIdeal (r : ι → (MvPolynomial J O)[G]) :
    p • r ∈ tiedRows gen (tieIdeal u p κ τ φ ε ρ₀) := by
  have h_aug : ∑ i, r i * (single (gen i) 1 - 1) ∈
      RingHom.ker (augmentation (MvPolynomial J O) G) := by
    simp [RingHom.mem_ker]
  have key : ∑ i, (p • r) i * (single (gen i) 1 - 1) =
      p • ∑ i, r i * (single (gen i) 1 - 1) := by
    simp [Finset.smul_sum]
  rw [mem_tiedRows, key]
  exact smul_mem_tieIdeal h_aug

variable {z : G → ι → (MvPolynomial J O)[G]}

/-- The ties. If the rows `z g` are coordinates of the `g - 1` in the `gen i - 1` modulo the tie
ideal, then the row `z (τ k) - X (κ k) • (ε (κ k))(φ k) z (φ k)` is tied for the tie ideal. -/
theorem sub_X_smul_mem_tiedRows_tieIdeal
    (hz : ∀ g, ∑ i, z g i * (single (gen i) 1 - 1) - (single g 1 - 1) ∈ tieIdeal u p κ τ φ ε ρ₀)
    (k : K) :
    z (τ k) - (MvPolynomial.X (κ k) : MvPolynomial J O) •
      Polynomial.aeval (single (φ k) (1 : MvPolynomial J O)) (ε (κ k)) • z (φ k) ∈
      tiedRows gen (tieIdeal u p κ τ φ ε ρ₀) := by
  set c := Polynomial.aeval (single (φ k) (1 : MvPolynomial J O)) (ε (κ k))
  have key : ∑ i, (z (τ k) - (MvPolynomial.X (κ k) : MvPolynomial J O) • c • z (φ k)) i *
      (single (gen i) 1 - 1) =
      (single (τ k) 1 - 1 -
          (MvPolynomial.X (κ k) : MvPolynomial J O) • (c * (single (φ k) 1 - 1))) +
        ((∑ i, z (τ k) i * (single (gen i) 1 - 1) - (single (τ k) 1 - 1)) -
          (MvPolynomial.X (κ k) : MvPolynomial J O) •
            (c * (∑ i, z (φ k) i * (single (gen i) 1 - 1) - (single (φ k) 1 - 1)))) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      smul_mul_assoc, ← Finset.smul_sum, mul_assoc, ← Finset.mul_sum, mul_sub, smul_sub]
    abel
  rw [mem_tiedRows, key]
  exact add_mem (tie_mem_tieIdeal k) (sub_mem (hz _)
    (Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_left _ c (hz _))))

end TieIdeal

/-! ### The tied normaliser -/

section TiedNormaliser

variable {O G J : Type*} [CommRing O] [Monoid G]

/-- The **tied normaliser** `ρ₀ = n + (1 - n)(a - 1)` with `n = c₁ (γ - 1)`, in the group algebra
`R_J[G]` over `R_J = O[X_j : j ∈ J]`. -/
noncomputable def tiedNormaliser (γ a : G) (c₁ : O) : (MvPolynomial J O)[G] :=
  c₁ • (single γ 1 - 1) + (1 - c₁ • (single γ 1 - 1)) * (single a 1 - 1)

/-- The defining formula of the tied normaliser. -/
theorem tiedNormaliser_def (γ a : G) (c₁ : O) :
    (tiedNormaliser γ a c₁ : (MvPolynomial J O)[G]) =
      c₁ • (single γ 1 - 1) + (1 - c₁ • (single γ 1 - 1)) * (single a 1 - 1) :=
  (rfl)

/-- The row `c₁ z γ + (1 - n) z a`, `n = c₁ (γ - 1)`, of the tied normaliser: when the rows `z g`
are coordinates of the `g - 1`, its element is the tied normaliser modulo the same left ideal. -/
noncomputable def tiedNormaliserRow {ι : Type*} (z : G → ι → (MvPolynomial J O)[G]) (γ a : G)
    (c₁ : O) : ι → (MvPolynomial J O)[G] :=
  c₁ • z γ + (1 - c₁ • (single γ (1 : MvPolynomial J O) - 1)) • z a

/-- The entries of the row of the tied normaliser. -/
@[simp]
theorem tiedNormaliserRow_apply {ι : Type*} (z : G → ι → (MvPolynomial J O)[G]) (γ a : G)
    (c₁ : O) (i : ι) :
    tiedNormaliserRow z γ a c₁ i =
      c₁ • z γ i + (1 - c₁ • (single γ (1 : MvPolynomial J O) - 1)) * z a i :=
  (rfl)

variable {B : Type*} [Semiring B] [Algebra O B]

/-- Where `γ` acts by the scalar `y`, `γ - 1` acts by `y - 1`. -/
private theorem map_single_sub_one_of_eq_algebraMap (f : (MvPolynomial J O)[G] →ₐ[O] B) {γ : G}
    {y : O} (hγ : f (single γ 1) = algebraMap O B y) :
    f (single γ 1 - 1) = algebraMap O B (y - 1) := by
  rw [sub_eq_add_neg, ← map_one (algebraMap O (MvPolynomial J O)[G]), ← map_neg, map_add,
    AlgHom.commutes, hγ, ← map_add, ← sub_eq_add_neg]

/-- Where `γ` acts by a scalar `y` with `c₁ (y - 1) = 1`, `n = c₁ (γ - 1)` acts as `1`. -/
private theorem map_smul_single_sub_one_of_eq_algebraMap (f : (MvPolynomial J O)[G] →ₐ[O] B)
    {γ : G} {y : O} (hγ : f (single γ 1) = algebraMap O B y) {c₁ : O} (hc₁ : c₁ * (y - 1) = 1) :
    f (c₁ • (single γ 1 - 1)) = 1 := by
  rw [map_smul, map_single_sub_one_of_eq_algebraMap f hγ, Algebra.smul_def, ← map_mul, hc₁,
    map_one]

/-- Where `γ` acts by a scalar `y` with `c₁ (y - 1) = 1`, `1 - n` acts as `0`. -/
private theorem map_one_sub_smul_single_sub_one_of_eq_algebraMap
    (f : (MvPolynomial J O)[G] →ₐ[O] B) {γ : G} {y : O} (hγ : f (single γ 1) = algebraMap O B y)
    {c₁ : O} (hc₁ : c₁ * (y - 1) = 1) :
    f (1 - c₁ • (single γ 1 - 1)) = 0 := by
  rw [sub_eq_add_neg, ← neg_one_smul O (c₁ • _), map_add, map_one, map_smul,
    map_smul_single_sub_one_of_eq_algebraMap f hγ hc₁, Algebra.smul_def, mul_one,
    ← map_one (algebraMap O B), ← map_add, add_neg_cancel, map_zero]

/-- If `γ` acts by a scalar `y` with `c₁ (y - 1) = 1`, the tied normaliser acts as `1`. -/
theorem map_tiedNormaliser_of_eq_algebraMap (f : (MvPolynomial J O)[G] →ₐ[O] B) {γ : G} {y : O}
    (hγ : f (single γ 1) = algebraMap O B y) {c₁ : O} (hc₁ : c₁ * (y - 1) = 1) (a : G) :
    f (tiedNormaliser γ a c₁) = 1 := by
  rw [tiedNormaliser_def, map_add, map_mul, map_smul_single_sub_one_of_eq_algebraMap f hγ hc₁,
    map_one_sub_smul_single_sub_one_of_eq_algebraMap f hγ hc₁, zero_mul, add_zero]

/-- If `γ` acts trivially, the tied normaliser acts as `a - 1`. -/
theorem map_tiedNormaliser_of_eq_one {C : Type*} [Ring C] [Algebra O C]
    (f : (MvPolynomial J O)[G] →ₐ[O] C) {γ : G} (hγ : f (single γ 1) = 1) (a : G) (c₁ : O) :
    f (tiedNormaliser γ a c₁) = f (single a 1) - 1 := by
  simp [tiedNormaliser_def, hγ]

/-- The tied normaliser lies in the augmentation ideal. -/
@[simp]
theorem augmentation_tiedNormaliser (γ a : G) (c₁ : O) :
    augmentation (MvPolynomial J O) G (tiedNormaliser γ a c₁) = 0 := by
  simp [tiedNormaliser_def, Algebra.smul_def]

variable {Y A ι : Type*} [Semiring A] [Algebra (MvPolynomial J O) A] [Fintype ι]
  {u : Y → (MvPolynomial J O)[G] →ₐ[MvPolynomial J O] A} {p : O} {K : Type*} {κ : K → J}
  {τ φ : K → G} {ε : J → Polynomial O} {gen : ι → G} {z : G → ι → (MvPolynomial J O)[G]}

/-- If the rows `z g` are coordinates of the `g - 1` in the `gen i - 1` modulo the tie ideal for
the tied normaliser `ρ₀` of `(γ, a, c₁)`, then every multiple of the row of `ρ₀` by `g - 1` is tied
for that tie ideal. -/
theorem sub_one_smul_tiedNormaliserRow_mem_tiedRows_tieIdeal {γ a : G} {c₁ : O}
    (hz : ∀ g, ∑ i, z g i * (single (gen i) 1 - 1) - (single g 1 - 1) ∈
      tieIdeal u p κ τ φ ε (tiedNormaliser γ a c₁)) (g : G) :
    (single g (1 : MvPolynomial J O) - 1) • tiedNormaliserRow z γ a c₁ ∈
      tiedRows gen (tieIdeal u p κ τ φ ε (tiedNormaliser γ a c₁)) := by
  have key : ∑ i, ((single g (1 : MvPolynomial J O) - 1) • tiedNormaliserRow z γ a c₁) i *
      (single (gen i) 1 - 1) =
      (single g 1 - 1) * tiedNormaliser γ a c₁ + (single g 1 - 1) *
        (c₁ • (∑ i, z γ i * (single (gen i) 1 - 1) - (single γ 1 - 1)) +
          (1 - c₁ • (single γ 1 - 1)) *
            (∑ i, z a i * (single (gen i) 1 - 1) - (single a 1 - 1))) :=
    calc _ = (single g 1 - 1) * (c₁ • ∑ i, z γ i * (single (gen i) 1 - 1)) +
          (single g 1 - 1) * ((1 - c₁ • (single γ 1 - 1)) *
            ∑ i, z a i * (single (gen i) 1 - 1)) := by
          simp only [Pi.smul_apply, smul_eq_mul, tiedNormaliserRow_apply, mul_add, add_mul,
            Finset.sum_add_distrib, mul_assoc, smul_mul_assoc, ← Finset.mul_sum, ← Finset.smul_sum]
      _ = _ := by
          simp only [tiedNormaliser_def, smul_sub, mul_sub, mul_add]
          abel
  have h_aug : single g (1 : MvPolynomial J O) - 1 ∈
      RingHom.ker (augmentation (MvPolynomial J O) G) := by
    simp [RingHom.mem_ker]
  rw [mem_tiedRows, key]
  exact add_mem (mul_mem_tieIdeal h_aug) (Ideal.mul_mem_left _ _ (add_mem
    (Submodule.smul_of_tower_mem _ _ (hz γ)) (Ideal.mul_mem_left _ _ (hz a))))

omit [Fintype ι] in
/-- Where `γ` acts by a scalar `y` with `c₁ (y - 1) = 1`, the tied row `(γ - 1)` times the row of
the tied normaliser has the image of the row `z γ`. -/
theorem map_sub_one_mul_tiedNormaliserRow (f : (MvPolynomial J O)[G] →ₐ[O] B) {γ : G} {y : O}
    (hγ : f (single γ 1) = algebraMap O B y) {c₁ : O} (hc₁ : c₁ * (y - 1) = 1) (a : G) (i : ι) :
    f ((single γ 1 - 1) * tiedNormaliserRow z γ a c₁ i) = f (z γ i) := by
  rw [tiedNormaliserRow_apply, map_mul, map_add, map_mul,
    map_one_sub_smul_single_sub_one_of_eq_algebraMap f hγ hc₁, zero_mul, add_zero, map_smul,
    map_single_sub_one_of_eq_algebraMap f hγ, mul_smul_comm, ← Algebra.smul_def, smul_smul, hc₁,
    one_smul]

end TiedNormaliser

end TauCeti
