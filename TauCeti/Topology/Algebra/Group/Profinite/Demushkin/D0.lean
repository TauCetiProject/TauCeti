/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.MinimalPresentation

/-!
# The standard dyadic Demushkin presentation `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩`

This file defines the pro-`2` group `D₀`, presented on three generators `A, S, Y` by the single
relator `A²S⁴(S,Y)`, where `(x, y) = x⁻¹y⁻¹xy` is Labute's commutator convention. In Labute's
classification of Demushkin groups with `q = 2` and odd rank, `D₀` is the normal form of rank
`3` with `f = 2`; it is the abstract group that the local theory identifies with the maximal
pro-`2` quotient of the absolute Galois group of `ℚ₂`. The name `D₀`, the marked generators
`A, S, Y` and the relator `A²S⁴[S,Y]` follow Roe–Turturean, §3.1, equation (3.1), whose commutator
convention is the same. Neither that identification nor the Demushkin property itself is
established here.

What is established is that the presentation is not vacuous. The map on the free pro-`2` group
sending `A ↦ 0`, `S ↦ 1`, `Y ↦ 0` in `ℤ/2` kills the relator, because the commutator dies in
an abelian group and `2 · 0 + 4 · 1 = 0`, so it descends to a continuous surjection
`D₀ ↠ ℤ/2`. Hence `D₀` is nontrivial: the marked generator `S` is not the identity. The
marked generators topologically generate `D₀`, so `D₀` is topologically finitely generated, and a
continuous homomorphism out of `D₀` is determined by its values on `A`, `S` and `Y`.

The presentation is moreover minimal: the relator is a product of two squares and a commutator,
so it lies in the Frattini subgroup of the free pro-`2` group on three generators, and therefore
`D₀` has topological generator rank exactly `3`. This is the rank `n = 3` of the Demushkin
invariants of `D₀`.

## Main definitions

* `TauCeti.d0Relator`: the relator `A²S⁴(S,Y)` in the free pro-`2` group on `Fin 3`.
* `TauCeti.demushkinD0`: the presented pro-`2` group `D₀`.
* `TauCeti.d0A`, `TauCeti.d0S`, `TauCeti.d0Y`: its marked generators.
* `TauCeti.d0Lift`: the continuous homomorphism `D₀ → P` determined by three elements of a pro-`2`
  group `P` satisfying the relation `a²s⁴(s,y) = 1`.
* `TauCeti.d0FreeCharacter`: the character `A ↦ 0`, `S ↦ 1`, `Y ↦ 0` of the free pro-`2` group.
* `TauCeti.d0Character`: the induced character `D₀ → ℤ/2`.

## Main results

* `TauCeti.d0_relation`: the marked generators satisfy `A²S⁴(S,Y) = 1`.
* `TauCeti.d0_hom_ext`: a continuous homomorphism out of `D₀` is determined by its values on
  `A`, `S` and `Y`.
* `TauCeti.d0FreeCharacter_d0Relator`: the character kills the relator.
* `TauCeti.d0Character_surjective`: the induced character `D₀ → ℤ/2` is surjective.
* `TauCeti.d0S_ne_one` and the `Nontrivial demushkinD0` instance: `D₀` is nontrivial.
* `TauCeti.d0_topologicallyGenerates`: `A`, `S`, `Y` topologically generate `D₀`.
* `TauCeti.isTopologicallyFinitelyGenerated_demushkinD0`: `D₀` is topologically finitely
  generated.
* `TauCeti.d0Relator_mem_proPFrattini`: the relator lies in the Frattini subgroup of the free
  pro-`2` group, so the presentation of `D₀` is minimal.
* `TauCeti.topologicalGeneratorRankNat_demushkinD0`: `D₀` has topological generator rank `3`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, preprint (2026),
  §3.1, <https://roed314.github.io/gq2/>.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

/-- The dyadic Demushkin relator `A²S⁴(S,Y)` in the free pro-`2` group on the three generators
`A = of 0`, `S = of 1`, `Y = of 2`, written in Labute's commutator convention
`(x, y) = x⁻¹y⁻¹xy`. -/
noncomputable def d0Relator : freeProP 2 (Fin 3) :=
  freeProP.of 0 ^ 2 * freeProP.of 1 ^ 4 *
    ((freeProP.of 1)⁻¹ * (freeProP.of 2)⁻¹ * freeProP.of 1 * freeProP.of 2)

/-- **`D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩`**, the standard dyadic one-relator pro-`2` group, presented on
three generators by the single relator `d0Relator`. -/
noncomputable abbrev demushkinD0 : Type := presentedProP 2 (Fin 3) {d0Relator}

/-- Closedness of the defining normal subgroup, for the quotient topology instances. -/
instance isClosed_d0_definingSubgroup :
    IsClosed ((Subgroup.normalClosure {d0Relator}).topologicalClosure :
      Set (freeProP 2 (Fin 3))) :=
  Subgroup.isClosed_topologicalClosure _

/-- The marked generator `A` of `D₀`, the image of the first free pro-`2` generator. -/
noncomputable def d0A : demushkinD0 := presentedProP.of 2 {d0Relator} 0

/-- The marked generator `S` of `D₀`, the image of the second free pro-`2` generator. -/
noncomputable def d0S : demushkinD0 := presentedProP.of 2 {d0Relator} 1

/-- The marked generator `Y` of `D₀`, the image of the third free pro-`2` generator. -/
noncomputable def d0Y : demushkinD0 := presentedProP.of 2 {d0Relator} 2

/-- The first canonical generator of the presented group `D₀` is `A`. -/
@[simp]
theorem presentedProP_of_d0Relator_zero : presentedProP.of 2 {d0Relator} 0 = d0A :=
  (rfl)

/-- The second canonical generator of the presented group `D₀` is `S`. -/
@[simp]
theorem presentedProP_of_d0Relator_one : presentedProP.of 2 {d0Relator} 1 = d0S :=
  (rfl)

/-- The third canonical generator of the presented group `D₀` is `Y`. -/
@[simp]
theorem presentedProP_of_d0Relator_two : presentedProP.of 2 {d0Relator} 2 = d0Y :=
  (rfl)

/-- The set of canonical generators of `D₀` is `{A, S, Y}`. -/
theorem range_presentedProP_of_d0Relator :
    Set.range (presentedProP.of 2 {d0Relator}) = {d0A, d0S, d0Y} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The marked generators of `D₀` satisfy the defining relation `A²S⁴(S,Y) = 1`. -/
@[simp]
theorem d0_relation : d0A ^ 2 * d0S ^ 4 * (d0S⁻¹ * d0Y⁻¹ * d0S * d0Y) = 1 := by
  have h := presentedProP.mk_relator (rels := {d0Relator})
    (freeProP.of 0 ^ 2 * freeProP.of 1 ^ 4 *
      ((freeProP.of 1)⁻¹ * (freeProP.of 2)⁻¹ * freeProP.of 1 * freeProP.of 2))
    (Set.mem_singleton_iff.mpr (by rw [d0Relator]))
  simpa only [map_mul, map_pow, map_inv, presentedProP.mk_of, presentedProP_of_d0Relator_zero,
    presentedProP_of_d0Relator_one, presentedProP_of_d0Relator_two] using h

section Lift

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P] (hP : IsProP 2 P) (a s y : P)
  (h : a ^ 2 * s ^ 4 * (s⁻¹ * y⁻¹ * s * y) = 1)

/-- **The universal property of `D₀`**: three elements `a, s, y` of a pro-`2` group `P` satisfying
`a²s⁴(s,y) = 1` determine a continuous homomorphism `D₀ → P` with `A ↦ a`, `S ↦ s`, `Y ↦ y`. -/
noncomputable def d0Lift : demushkinD0 →ₜ* P :=
  presentedProP.lift (freeProP.lift hP ![a, s, y]) fun r hr ↦ by
    rw [Set.mem_singleton_iff.mp hr]
    simpa [d0Relator] using h

/-- `d0Lift` sends `A` to `a`. -/
@[simp]
theorem d0Lift_d0A : d0Lift hP a s y h d0A = a :=
  (presentedProP.lift_of _ _ 0).trans (freeProP.lift_of hP _ 0)

/-- `d0Lift` sends `S` to `s`. -/
@[simp]
theorem d0Lift_d0S : d0Lift hP a s y h d0S = s :=
  (presentedProP.lift_of _ _ 1).trans (freeProP.lift_of hP _ 1)

/-- `d0Lift` sends `Y` to `y`. -/
@[simp]
theorem d0Lift_d0Y : d0Lift hP a s y h d0Y = y :=
  (presentedProP.lift_of _ _ 2).trans (freeProP.lift_of hP _ 2)

end Lift

/-- Two continuous homomorphisms out of `D₀` into a Hausdorff group that agree on the marked
generators `A`, `S`, `Y` are equal. -/
@[ext]
theorem d0_hom_ext {Q : Type*} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {φ ψ : demushkinD0 →ₜ* Q} (hA : φ d0A = ψ d0A) (hS : φ d0S = ψ d0S) (hY : φ d0Y = ψ d0Y) :
    φ = ψ :=
  presentedProP.hom_ext_of fun i ↦ by fin_cases i <;> assumption

/-- The character of the free pro-`2` group on `A, S, Y` with values `A ↦ 0`, `S ↦ 1`, `Y ↦ 0`
in `ℤ/2`, written multiplicatively. It is the map that exhibits `D₀` as nontrivial. -/
noncomputable def d0FreeCharacter : freeProP 2 (Fin 3) →ₜ* Multiplicative (ZMod 2) :=
  freeProP.lift (isProP_multiplicative_zmod_pow 2 1) ![1, Multiplicative.ofAdd 1, 1]

/-- The values of `d0FreeCharacter` on the free generators. -/
@[simp]
theorem d0FreeCharacter_of (i : Fin 3) :
    d0FreeCharacter (freeProP.of i) = ![1, Multiplicative.ofAdd 1, 1] i :=
  freeProP.lift_of _ _ i

/-- `d0FreeCharacter` kills the relator `A²S⁴(S,Y)`: the commutator dies in the abelian group
`ℤ/2`, and `2 · 0 + 4 · 1 = 0`. -/
@[simp]
theorem d0FreeCharacter_d0Relator : d0FreeCharacter d0Relator = 1 := by
  simp only [d0Relator, map_mul, map_pow, map_inv, d0FreeCharacter_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  decide

/-- `d0FreeCharacter` is surjective, because `S` already hits the generator of `ℤ/2`. -/
theorem d0FreeCharacter_surjective : Function.Surjective d0FreeCharacter := by
  intro x
  rcases (by decide : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1) x with
    rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨freeProP.of 1, by simp⟩

/-- The character `D₀ → ℤ/2` with values `A ↦ 0`, `S ↦ 1`, `Y ↦ 0`, induced by
`d0FreeCharacter`. -/
noncomputable def d0Character : demushkinD0 →ₜ* Multiplicative (ZMod 2) :=
  presentedProP.lift d0FreeCharacter fun r hr ↦ by
    rw [Set.mem_singleton_iff.mp hr, d0FreeCharacter_d0Relator]

/-- `d0Character` is the descent of `d0FreeCharacter` along the presentation map. -/
@[simp]
theorem d0Character_comp_mk :
    d0Character.comp (presentedProP.mk 2 {d0Relator}) = d0FreeCharacter :=
  presentedProP.lift_comp_mk _ _

/-- `d0Character` agrees with `d0FreeCharacter` on the image of the free pro-`2` group. -/
@[simp]
theorem d0Character_mk (x : freeProP 2 (Fin 3)) :
    d0Character (presentedProP.mk 2 {d0Relator} x) = d0FreeCharacter x :=
  DFunLike.congr_fun d0Character_comp_mk x

/-- `d0Character` vanishes on `A`. -/
@[simp]
theorem d0Character_d0A : d0Character d0A = 1 := by
  rw [d0A, ← presentedProP.mk_of, d0Character_mk, d0FreeCharacter_of]
  simp

/-- `d0Character` takes `S` to the generator of `ℤ/2`. -/
@[simp]
theorem d0Character_d0S : d0Character d0S = Multiplicative.ofAdd 1 := by
  rw [d0S, ← presentedProP.mk_of, d0Character_mk, d0FreeCharacter_of]
  simp

/-- `d0Character` vanishes on `Y`. -/
@[simp]
theorem d0Character_d0Y : d0Character d0Y = 1 := by
  rw [d0Y, ← presentedProP.mk_of, d0Character_mk, d0FreeCharacter_of]
  simp

/-- The induced character `D₀ ↠ ℤ/2` is surjective. -/
theorem d0Character_surjective : Function.Surjective d0Character := by
  refine Function.Surjective.of_comp (g := ⇑(presentedProP.mk 2 {d0Relator})) ?_
  rw [← ContinuousMonoidHom.coe_comp, d0Character_comp_mk]
  exact d0FreeCharacter_surjective

/-- The marked generator `S` of `D₀` is not the identity: it maps to the generator of `ℤ/2`. -/
theorem d0S_ne_one : d0S ≠ 1 := fun h ↦ by
  have := d0Character_d0S
  rw [h, map_one] at this
  exact absurd this (by decide)

/-- **`D₀` is nontrivial**: the presentation `⟨A, S, Y ∣ A²S⁴(S,Y)⟩` does not collapse. -/
instance : Nontrivial demushkinD0 := nontrivial_of_ne d0S 1 d0S_ne_one

/-- `D₀` is a pro-`2` group. -/
theorem isProP_demushkinD0 : IsProP 2 demushkinD0 :=
  presentedProP.isProP 2 (Fin 3) {d0Relator}

/-- The marked generators `A`, `S`, `Y` topologically generate `D₀`. -/
theorem d0_topologicallyGenerates :
    (Subgroup.closure ({d0A, d0S, d0Y} : Set demushkinD0)).topologicalClosure = ⊤ := by
  have h := topologicalClosure_closure_image_eq_top
    (freeProP.topologicalClosure_closure_range_of_eq_top 2 (Fin 3))
    (f := (presentedProP.mk 2 {d0Relator}).toMonoidHom)
    (presentedProP.mk 2 {d0Relator}).continuous
    (presentedProP.mk_surjective 2 {d0Relator}).denseRange
  have hof : ⇑(presentedProP.mk 2 {d0Relator}).toMonoidHom ∘ freeProP.of =
      presentedProP.of 2 {d0Relator} :=
    funext fun i ↦ presentedProP.mk_of 2 {d0Relator} i
  rwa [← Set.range_comp, hof, range_presentedProP_of_d0Relator] at h

/-- `D₀` is topologically finitely generated, by its three marked generators. -/
theorem isTopologicallyFinitelyGenerated_demushkinD0 :
    IsTopologicallyFinitelyGenerated demushkinD0 :=
  (Set.toFinite {d0A, d0S, d0Y}).isTopologicallyFinitelyGenerated d0_topologicallyGenerates

/-- The relator `A²S⁴(S,Y)` lies in the Frattini subgroup of the free pro-`2` group on three
generators: `A²` and `S⁴ = (S²)²` are squares and `(S,Y) = ⁅S⁻¹, Y⁻¹⁆` is a commutator. -/
theorem d0Relator_mem_proPFrattini : d0Relator ∈ proPFrattini 2 (freeProP 2 (Fin 3)) := by
  refine mul_mem (mul_mem (pow_mem_proPFrattini _) ?_) ?_
  · have h : (freeProP.of (1 : Fin 3) : freeProP 2 (Fin 3)) ^ 4 = (freeProP.of 1 ^ 2) ^ 2 := by
      rw [← pow_mul]
    rw [h]
    exact pow_mem_proPFrattini _
  · simpa [commutatorElement_def] using commutator_le_proPFrattini Nat.prime_two
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (freeProP.of (1 : Fin 3))⁻¹)
        (Subgroup.mem_top (freeProP.of (2 : Fin 3))⁻¹))

/-- **`D₀` has topological generator rank `3`**: its presentation on `A`, `S`, `Y` is minimal,
because the relator lies in the Frattini subgroup of the free pro-`2` group. -/
@[simp]
theorem topologicalGeneratorRankNat_demushkinD0 :
    topologicalGeneratorRankNat demushkinD0 isTopologicallyFinitelyGenerated_demushkinD0 = 3 := by
  simpa using (presentedProP.topologicalGeneratorRankNat_eq_card_iff {d0Relator}).mpr
    (Set.singleton_subset_iff.mpr d0Relator_mem_proPFrattini)

end TauCeti
