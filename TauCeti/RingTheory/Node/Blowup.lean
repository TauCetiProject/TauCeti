/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.AffineBlowup
public import TauCeti.RingTheory.Node.Flat
import TauCeti.RingTheory.Flat.NonZeroDivisors

/-!
# Blowing up the origin of the node `xy = πⁿ`

Let `π` be a nonzerodivisor of a commutative ring `R`, for instance a uniformizer of a discrete
valuation ring, and let `A = R[x, y] ⧸ (xy - πⁿ⁺²)`. When `R` is a discrete valuation ring with
uniformizer `π`, the closed point `(π, x, y)` is the only point at which `Spec A` is not regular.
This file computes the three affine charts of the blowup of `Spec A` along the ideal
`I = (π, x, y)`, namely the affine blowup algebras `A[I/π]`, `A[I/x]` and `A[I/y]`:

* the `π`-chart `A[I/π] = A[x/π, y/π]` is again a node, `R[u, v] ⧸ (uv - πⁿ)`, with
  `u = x/π` and `v = y/π`;
* the `x`-chart `A[I/x] = A[π/x, y/x]` is `R[x, t] ⧸ (xt - π)`, with `t = π/x`, and symmetrically
  for the `y`-chart.

Thus blowing up the origin replaces the thickness `n + 2` of the node by `n` on the only chart
that can still be singular, while the two other charts are nodes of thickness one, which over a
discrete valuation ring are regular at their origin
(`TauCeti.isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff_of_irreducible`). This is
the local computation behind the resolution of the nodes of a model of a curve over a discrete
valuation ring by repeated blowups of closed points.

## Main definitions

* `TauCeti.NodeAlgebra.originIdeal π a`: the ideal `(π, x, y)` of `R[x, y] ⧸ (xy - a)`.

## Main results

* `TauCeti.NodeAlgebra.affineBlowupBaseEquiv`: the `π`-chart of the blowup of `xy = πⁿ⁺²` at
  the origin is `xy = πⁿ`.
* `TauCeti.NodeAlgebra.affineBlowupCoordEquiv`: each coordinate chart of the blowup of `xy = πⁿ⁺²`
  at the origin is `xy = π`.

## Implementation notes

Each chart is described by an explicit `R`-algebra map `φ` from a node algebra into a localization
`S` of `A`, whose image is the affine blowup algebra. Injectivity of `φ` is proved by exhibiting a
map `ψ` from `S` to a localization of the source of `φ` at a nonzerodivisor, such that `ψ ∘ φ` is
the localization map: for the `π`-chart, `ψ` is induced by `x ↦ πu`, `y ↦ πv`, and for the
`x`-chart by `x ↦ x`, `y ↦ πⁿ⁺¹t`.

## References

* [The Stacks Project, Example 55.14.1](https://stacks.math.columbia.edu/tag/0CDC)
* [The Stacks Project, Section *Blow up algebras*](https://stacks.math.columbia.edu/tag/052P)
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Ideal MvPolynomial TauCeti.Localization

variable {R : Type*} [CommRing R]

/-! ### The ideal of the origin -/

/-- The ideal `(π, x, y)` of `R[x, y] ⧸ (xy - a)`. It cuts out the origin of the fibre over
`V(π)`; for `a = πⁿ⁺²` with `π` a uniformizer of a discrete valuation ring, it is the ideal of the
singular point of the node. -/
def originIdeal (π a : R) : Ideal (NodeAlgebra R a) :=
  span {algebraMap R _ π, coord a 0, coord a 1}

theorem originIdeal_def (π a : R) :
    originIdeal π a = span {algebraMap R _ π, coord a 0, coord a 1} :=
  (rfl)

@[simp]
theorem algebraMap_mem_originIdeal (π a : R) : algebraMap R _ π ∈ originIdeal π a :=
  subset_span (by simp)

@[simp]
theorem coord_mem_originIdeal (π a : R) (i : Fin 2) : coord a i ∈ originIdeal π a :=
  subset_span (by fin_cases i <;> simp)

/-! ### Images of algebra maps out of a node -/

section Range

variable {b c : R} {S : Type*} [CommRing S] [Algebra R S] [Algebra (NodeAlgebra R c) S]
  [IsScalarTower R (NodeAlgebra R c) S]

/-- The range of an `R`-algebra map `φ` out of a node lies in a subalgebra containing the images
of both coordinates. -/
private theorem range_le_restrictScalars (φ : NodeAlgebra R b →ₐ[R] S)
    {E : Subalgebra (NodeAlgebra R c) S} (hφ : ∀ j, φ (coord b j) ∈ E) :
    φ.range ≤ E.restrictScalars R := by
  rw [← Algebra.map_top, ← adjoin_range_coord, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact hφ j

/-- The subalgebra `A[T]` of an `A`-algebra `S` lies in the range of an `R`-algebra map `φ` out of
a node, provided this range contains `T` and the images of both coordinates of the node `A`. -/
private theorem adjoin_le_range (φ : NodeAlgebra R b →ₐ[R] S) {T : Set S} (hT : T ⊆ φ.range)
    (hc : ∀ j, algebraMap (NodeAlgebra R c) S (coord c j) ∈ φ.range) :
    (Algebra.adjoin (NodeAlgebra R c) T).restrictScalars R ≤ φ.range := by
  have hA : ∀ z, algebraMap (NodeAlgebra R c) S z ∈ φ.range := by
    have h : Algebra.adjoin R (Set.range (coord c)) ≤
        φ.range.comap (IsScalarTower.toAlgHom R (NodeAlgebra R c) S) := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hc j
    rw [adjoin_range_coord] at h
    exact fun z ↦ h Algebra.mem_top
  let F : Subalgebra (NodeAlgebra R c) S :=
    { φ.range.toSubsemiring with algebraMap_mem' := hA }
  exact Algebra.adjoin_le (S := F) hT

/-- **An injectivity criterion.** Let `S` be a localization of an `R`-algebra `A` away from `s`,
let `B = R[x, y] ⧸ (xy - b)` and let `φ : B → S`. Suppose that an `R`-algebra map `β : A → B`
sends `s` to a nonzerodivisor and that, for each coordinate `xⱼ` of `B`, the element `s · φ(xⱼ)`
of `S` is the image of some `wⱼ ∈ A` with `β(wⱼ) = β(s) xⱼ`. Then `φ` is injective: `β` induces
`ψ : S → B_{β(s)}`, and `ψ ∘ φ` is the localization map of `B`, which is injective. -/
private theorem injective_of_forall_coord {A : Type*} [CommRing A] [Algebra R A]
    [Algebra A S] [IsScalarTower R A S] {s : A} [IsLocalization.Away s S]
    (φ : NodeAlgebra R b →ₐ[R] S) (β : A →ₐ[R] NodeAlgebra R b)
    (hs : β s ∈ nonZeroDivisors (NodeAlgebra R b))
    (h : ∀ j, ∃ w : A, algebraMap A S s * φ (coord b j) = algebraMap A S w ∧
      β w = β s * coord b j) :
    Function.Injective φ := by
  set B' := Localization.Away (β s)
  have hu : IsUnit (algebraMap (NodeAlgebra R b) B' (β s)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : S →+* B' := IsLocalization.Away.lift s (g := (algebraMap _ B').comp β.toRingHom) hu
  have hψ : ∀ z : A, ψ (algebraMap A S z) = algebraMap _ B' (β z) :=
    IsLocalization.Away.lift_eq (g := (algebraMap _ B').comp β.toRingHom) _ hu
  let ψ' : S →ₐ[R] B' :=
    { ψ with
      commutes' := fun r ↦ by
        rw [RingHom.toFun_eq_coe, IsScalarTower.algebraMap_apply R A S, hψ, AlgHom.commutes,
          ← IsScalarTower.algebraMap_apply] }
  have hψ' : ∀ z : A, ψ' (algebraMap A S z) = algebraMap _ B' (β z) := hψ
  have hcoord : ∀ j, (ψ'.comp φ) (coord b j) =
      IsScalarTower.toAlgHom R (NodeAlgebra R b) B' (coord b j) := fun j ↦ by
    obtain ⟨w, hw, hβ⟩ := h j
    refine hu.mul_left_cancel ?_
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul, ← hβ, ← hψ' w, ← hw, map_mul,
      hψ' s]
  have key : ψ'.comp φ = IsScalarTower.toAlgHom R (NodeAlgebra R b) B' :=
    hom_ext b (hcoord 0) (hcoord 1)
  intro z w hzw
  refine IsLocalization.injective B' (Submonoid.powers_le.mpr hs) ?_
  have h := congr_arg ψ' hzw
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, key, IsScalarTower.coe_toAlgHom'] at h

end Range

/-! ### The `π`-chart -/

section BaseChart

variable {π : R} {n : ℕ} {S : Type*} [CommRing S] [Algebra R S]
  [Algebra (NodeAlgebra R (π ^ (n + 2))) S] [IsScalarTower R (NodeAlgebra R (π ^ (n + 2))) S]
  [IsLocalization.Away (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π) S]

/-- The fractions `x/π` and `y/π` satisfy `(x/π)(y/π) = πⁿ`. -/
private theorem divBy_mul_divBy_base :
    divBy (coord (π ^ (n + 2)) 0) (algebraMap R _ π) *
        divBy (coord (π ^ (n + 2)) 1) (algebraMap R _ π) = algebraMap R S (π ^ n) := by
  have hπ : algebraMap (NodeAlgebra R (π ^ (n + 2))) S (algebraMap R _ π) = algebraMap R S π :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  refine ((hπ ▸ IsLocalization.Away.algebraMap_isUnit (S := S) _).pow 2).mul_left_cancel ?_
  calc algebraMap R S π ^ 2 * (divBy (coord (π ^ (n + 2)) 0) (algebraMap R _ π) *
        divBy (coord (π ^ (n + 2)) 1) (algebraMap R _ π))
      = (algebraMap R S π * divBy (coord (π ^ (n + 2)) 0) (algebraMap R _ π)) *
          (algebraMap R S π * divBy (coord (π ^ (n + 2)) 1) (algebraMap R _ π)) := by ring
    _ = algebraMap R S (π ^ (n + 2)) := by
        rw [← hπ, algebraMap_mul_divBy, algebraMap_mul_divBy, ← map_mul,
          coord_zero_mul_coord_one, ← IsScalarTower.algebraMap_apply]
    _ = algebraMap R S π ^ 2 * algebraMap R S (π ^ n) := by
        rw [← map_pow, ← map_mul, pow_add, mul_comm]

variable (π n S) in
/-- The map `R[u, v] ⧸ (uv - πⁿ) → S` sending `u ↦ x/π` and `v ↦ y/π`. -/
private def baseChartHom : NodeAlgebra R (π ^ n) →ₐ[R] S :=
  lift (π ^ n) (divBy (coord (π ^ (n + 2)) 0) (algebraMap R _ π))
    (divBy (coord (π ^ (n + 2)) 1) (algebraMap R _ π)) divBy_mul_divBy_base

private theorem baseChartHom_coord (i : Fin 2) :
    baseChartHom π n S (coord (π ^ n) i) =
      divBy (coord (π ^ (n + 2)) i) (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π) := by
  rw [baseChartHom, lift_coord]
  fin_cases i <;> simp

/-- The map `R[x, y] ⧸ (xy - πⁿ⁺²) → R[u, v] ⧸ (uv - πⁿ)` sending `x ↦ πu` and `y ↦ πv`. -/
private def baseChartInv (π : R) (n : ℕ) :
    NodeAlgebra R (π ^ (n + 2)) →ₐ[R] NodeAlgebra R (π ^ n) :=
  lift (π ^ (n + 2)) (algebraMap R _ π * coord (π ^ n) 0) (algebraMap R _ π * coord (π ^ n) 1) (by
    rw [mul_mul_mul_comm, coord_zero_mul_coord_one, ← map_mul, ← map_mul, pow_add]
    ring_nf)

/-- For `π` a nonzerodivisor, `R[u, v] ⧸ (uv - πⁿ) → S` is injective. -/
private theorem baseChartHom_injective (hπ : π ∈ nonZeroDivisors R) :
    Function.Injective (baseChartHom π n S) := by
  refine injective_of_forall_coord (s := algebraMap R _ π) _ (baseChartInv π n) ?_
    fun j ↦ ⟨coord _ j, ?_, ?_⟩
  · rw [AlgHom.commutes]
    exact Module.Flat.algebraMap_mem_nonZeroDivisors hπ
  · rw [baseChartHom_coord, algebraMap_mul_divBy]
  · rw [AlgHom.commutes, baseChartInv, lift_coord]
    fin_cases j <;> simp

private theorem range_baseChartHom :
    (baseChartHom π n S).range =
      ((originIdeal π (π ^ (n + 2))).affineBlowup
        (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π) S).restrictScalars R := by
  refine le_antisymm (range_le_restrictScalars _ fun j ↦ ?_) ?_
  · rw [baseChartHom_coord]
    exact divBy_mem_affineBlowup (coord_mem_originIdeal π _ j)
  · rw [affineBlowup_eq_adjoin_of_span_eq (originIdeal_def π _).symm]
    refine adjoin_le_range _ ?_ fun j ↦
      (AlgHom.mem_range _).mpr ⟨algebraMap R _ π * coord (π ^ n) j, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl | rfl
      · simpa only [divBy_self, SetLike.mem_coe] using one_mem (baseChartHom π n S).range
      · exact ⟨coord (π ^ n) 0, baseChartHom_coord 0⟩
      · exact ⟨coord (π ^ n) 1, baseChartHom_coord 1⟩
    · rw [map_mul, AlgHom.commutes, baseChartHom_coord, IsScalarTower.algebraMap_apply R
        (NodeAlgebra R (π ^ (n + 2))) S, algebraMap_mul_divBy]

variable (n S) in
/-- **The `π`-chart of the blowup of a node.** For a nonzerodivisor `π` of `R`, let
`A = R[x, y] ⧸ (xy - πⁿ⁺²)` and `I = (π, x, y)`. The affine blowup algebra `A[I/π]` is the node
`R[u, v] ⧸ (uv - πⁿ)`, with `u = x/π` and `v = y/π`. -/
def affineBlowupBaseEquiv (hπ : π ∈ nonZeroDivisors R) :
    NodeAlgebra R (π ^ n) ≃ₐ[R]
      (originIdeal π (π ^ (n + 2))).affineBlowup
        (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π) S :=
  (AlgEquiv.ofInjective _ (baseChartHom_injective hπ)).trans
    (Subalgebra.equivOfEq _ _ range_baseChartHom)

/-- The isomorphism `R[u, v] ⧸ (uv - πⁿ) ≃ A[I/π]` sends `u` to `x/π` and `v` to `y/π`. -/
@[simp]
theorem coe_affineBlowupBaseEquiv_coord (hπ : π ∈ nonZeroDivisors R) (i : Fin 2) :
    (affineBlowupBaseEquiv n S hπ (coord (π ^ n) i) : S) =
      divBy (coord (π ^ (n + 2)) i) (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π) :=
  baseChartHom_coord i

end BaseChart

/-! ### The coordinate charts -/

/-- The map `R[x, y] ⧸ (xy - πⁿ⁺²) → R[x, t] ⧸ (xt - π)` sending `xᵢ ↦ x` and `x_{1-i} ↦ πⁿ⁺¹t`. -/
private def coordChartInv (π : R) (n : ℕ) (i : Fin 2) :
    NodeAlgebra R (π ^ (n + 2)) →ₐ[R] NodeAlgebra R π :=
  lift (π ^ (n + 2)) (![coord π 0, algebraMap R _ (π ^ (n + 1)) * coord π 1] i)
    (![coord π 0, algebraMap R _ (π ^ (n + 1)) * coord π 1] (1 - i)) (by
      have h : coord π 0 * (algebraMap R _ (π ^ (n + 1)) * coord π 1) =
          algebraMap R (NodeAlgebra R π) (π ^ (n + 2)) := by
        rw [mul_left_comm, coord_zero_mul_coord_one, ← map_mul, ← pow_succ]
      fin_cases i
      · exact h
      · exact (mul_comm _ _).trans h)

private theorem coordChartInv_coord {π : R} {n : ℕ} {i : Fin 2} :
    coordChartInv π n i (coord (π ^ (n + 2)) i) = coord π 0 := by
  rw [coordChartInv, lift_coord]
  fin_cases i <;> simp

section CoordChart

variable {π : R} {n : ℕ} {i : Fin 2} {S : Type*} [CommRing S] [Algebra R S]
  [Algebra (NodeAlgebra R (π ^ (n + 2))) S] [IsScalarTower R (NodeAlgebra R (π ^ (n + 2))) S]
  [IsLocalization.Away (coord (π ^ (n + 2)) i) S]

/-- The coordinate `xᵢ` and the fraction `π/xᵢ` satisfy `xᵢ · (π/xᵢ) = π`. -/
private theorem algebraMap_mul_divBy_coord :
    algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ i) *
        divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i) = algebraMap R S π := by
  rw [algebraMap_mul_divBy, ← IsScalarTower.algebraMap_apply]

variable (π n i S) in
/-- The map `R[x, t] ⧸ (xt - π) → S` sending `x ↦ xᵢ` and `t ↦ π/xᵢ`. -/
private def coordChartHom : NodeAlgebra R π →ₐ[R] S :=
  lift π (algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ i))
    (divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i)) algebraMap_mul_divBy_coord

private theorem coordChartHom_coord_zero :
    coordChartHom π n i S (coord π 0) = algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ i) :=
  lift_coord_zero _ _ _ _

private theorem coordChartHom_coord_one :
    coordChartHom π n i S (coord π 1) = divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i) :=
  lift_coord_one _ _ _ _

/-- The other coordinate is `x_{1-i}/xᵢ = πⁿ (π/xᵢ)²` in the chart where `xᵢ` is inverted. -/
private theorem divBy_coord_one_sub :
    divBy (coord (π ^ (n + 2)) (1 - i)) (coord (π ^ (n + 2)) i) =
      algebraMap R S (π ^ n) * divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i) ^ 2 := by
  set x := algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ i)
  refine ((IsLocalization.Away.algebraMap_isUnit (S := S) (coord (π ^ (n + 2)) i)).pow 2
    |>.mul_left_cancel ?_)
  calc x ^ 2 * divBy (coord (π ^ (n + 2)) (1 - i)) (coord (π ^ (n + 2)) i)
      = x * algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ (1 - i)) := by
        rw [pow_two, mul_assoc, algebraMap_mul_divBy]
    _ = algebraMap R S (π ^ (n + 2)) := by
        rw [← map_mul, coord_mul_coord_one_sub, ← IsScalarTower.algebraMap_apply]
    _ = x ^ 2 *
          (algebraMap R S (π ^ n) * divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i) ^ 2) := by
        rw [mul_left_comm, ← mul_pow, algebraMap_mul_divBy_coord, ← map_pow, ← map_mul, pow_add,
          mul_comm]

/-- For `π` a nonzerodivisor, `R[x, t] ⧸ (xt - π) → S` is injective. -/
private theorem coordChartHom_injective (hπ : π ∈ nonZeroDivisors R) :
    Function.Injective (coordChartHom π n i S) := by
  refine injective_of_forall_coord (s := coord _ i) _ (coordChartInv π n i) ?_
    (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [coordChartInv_coord]
    exact coord_mem_nonZeroDivisors hπ 0
  · refine ⟨coord _ i * coord _ i, ?_, ?_⟩
    · rw [coordChartHom_coord_zero, map_mul]
    · rw [map_mul, coordChartInv_coord]
  · refine ⟨algebraMap R _ π, ?_, ?_⟩
    · rw [coordChartHom_coord_one, algebraMap_mul_divBy]
    · rw [AlgHom.commutes, coordChartInv_coord, coord_zero_mul_coord_one]

private theorem range_coordChartHom :
    (coordChartHom π n i S).range =
      ((originIdeal π (π ^ (n + 2))).affineBlowup
        (coord (π ^ (n + 2)) i) S).restrictScalars R := by
  have hj : ∀ j : Fin 2, j = i ∨ j = 1 - i := by
    intro j
    fin_cases i <;> fin_cases j <;> decide
  have hother : divBy (coord (π ^ (n + 2)) (1 - i)) (coord (π ^ (n + 2)) i) ∈
      (coordChartHom π n i S).range :=
    (AlgHom.mem_range _).mpr ⟨algebraMap R _ (π ^ n) * coord π 1 ^ 2, by
      rw [map_mul, AlgHom.commutes, map_pow (coordChartHom π n i S), coordChartHom_coord_one,
        divBy_coord_one_sub]⟩
  refine le_antisymm (range_le_restrictScalars _ (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)) ?_
  · rw [coordChartHom_coord_zero]
    exact Subalgebra.algebraMap_mem _ _
  · rw [coordChartHom_coord_one]
    exact divBy_mem_affineBlowup (algebraMap_mem_originIdeal π _)
  · rw [affineBlowup_eq_adjoin_of_span_eq (originIdeal_def π _).symm]
    refine adjoin_le_range _ ?_ fun j ↦ ?_
    · rintro _ ⟨z, hz, rfl⟩
      have hself : divBy (coord (π ^ (n + 2)) i) (coord (π ^ (n + 2)) i) ∈
          (coordChartHom π n i S).range := by
        simpa only [divBy_self] using one_mem (coordChartHom π n i S).range
      rcases hz with rfl | rfl | rfl
      · exact ⟨coord π 1, coordChartHom_coord_one⟩
      · rcases hj 0 with h | h <;> rw [h] <;> assumption
      · rcases hj 1 with h | h <;> rw [h] <;> assumption
    · rcases hj j with h | h <;> subst h
      · exact ⟨coord π 0, coordChartHom_coord_zero⟩
      · rw [← algebraMap_mul_divBy (S := S) (coord (π ^ (n + 2)) (1 - i)) (coord _ i),
          ← coordChartHom_coord_zero]
        exact mul_mem (AlgHom.mem_range_self _ _) hother

variable (n i S) in
/-- **The coordinate charts of the blowup of a node.** For a nonzerodivisor `π` of `R`, let
`A = R[x₀, x₁] ⧸ (x₀x₁ - πⁿ⁺²)` and `I = (π, x₀, x₁)`. For either coordinate `xᵢ`, the affine
blowup algebra `A[I/xᵢ]` is the node `R[x, t] ⧸ (xt - π)`, with `x = xᵢ` and `t = π/xᵢ`; the other
coordinate becomes `x_{1-i}/xᵢ = πⁿt²`. -/
def affineBlowupCoordEquiv (hπ : π ∈ nonZeroDivisors R) :
    NodeAlgebra R π ≃ₐ[R]
      (originIdeal π (π ^ (n + 2))).affineBlowup
        (coord (π ^ (n + 2)) i) S :=
  (AlgEquiv.ofInjective _ (coordChartHom_injective hπ)).trans
    (Subalgebra.equivOfEq _ _ range_coordChartHom)

/-- The isomorphism `R[x, t] ⧸ (xt - π) ≃ A[I/xᵢ]` sends `x` to `xᵢ`. -/
@[simp]
theorem coe_affineBlowupCoordEquiv_coord_zero (hπ : π ∈ nonZeroDivisors R) :
    (affineBlowupCoordEquiv n i S hπ (coord π 0) : S) =
      algebraMap (NodeAlgebra R (π ^ (n + 2))) S (coord _ i) :=
  coordChartHom_coord_zero

/-- The isomorphism `R[x, t] ⧸ (xt - π) ≃ A[I/xᵢ]` sends `t` to `π/xᵢ`. -/
@[simp]
theorem coe_affineBlowupCoordEquiv_coord_one (hπ : π ∈ nonZeroDivisors R) :
    (affineBlowupCoordEquiv n i S hπ (coord π 1) : S) =
      divBy (algebraMap R _ π) (coord (π ^ (n + 2)) i) :=
  coordChartHom_coord_one

end CoordChart

end TauCeti.NodeAlgebra
