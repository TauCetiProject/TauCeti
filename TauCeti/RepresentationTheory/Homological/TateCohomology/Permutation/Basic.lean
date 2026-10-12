/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.GroupAction.Stabilizer
import TauCeti.RepresentationTheory.Coinvariants
import TauCeti.RepresentationTheory.OfMulAction

/-!
# Low-degree Tate cohomology and Herbrand quotients of permutation modules

Let a finite group `G` act on a type `X`, and let `R[X]` be the permutation representation
`Rep.ofMulAction R G X`. This file computes its Tate cohomology in degrees `0` and `-1`.

* In degree `-1` it vanishes as soon as multiplication by `|G|` is injective on `R` (for instance
  when `R` has no additive torsion): an element of norm zero has orbit sums killed by `|G|`, hence
  zero orbit sums, and so lies in the augmentation submodule.
* In degree `0`, for `X` finite, it is `∏_ω R ⧸ (|G_ω|)`, the product over the orbits `ω` of the
  quotient of `R` by the order of the stabilizer of a point of `ω`. An invariant vector is
  constant on every orbit, and the norm of the basis vector at a point `x` is `|G_x|` times the
  indicator of its orbit.

Consequently the Herbrand quotient of `ℤ[X]` is `∏_ω |G_ω|`. For a transitive action it is the
order of a point stabilizer, and for `X = G ⧸ H` it is `|H|`: the Herbrand quotient of the module
induced from the trivial `H`-module `ℤ` is that of the trivial module, as Shapiro's lemma
predicts. No cyclicity is needed for these computations.

This is the lattice side of the computation of the Herbrand quotient of the `S`-units of a cyclic
extension of number fields `L/K`: there `X` is the set of places of `L` above a finite set `S` of
places of `K`, the stabilizers are the decomposition groups, and the Herbrand quotient of `ℤ[X]` is
the product of the local degrees.

## Main definitions

* `TauCeti.TateCohomology.H0LinearEquivPiQuotientStabilizer`: for `X` finite,
  `H-hat^0(G, R[X]) ≃ ∏_ω R ⧸ (|G_ω|)`.

## Main results

* `TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_ofMulAction_of_isSMulRegular`:
  `H-hat^(-1)(G, R[X]) = 0` when multiplication by `|G|` is injective on `R`.
* `TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_ofMulAction`: the instance
  `H-hat^(-1)(G, R[X]) = 0` when `R` has no additive torsion.
* `TauCeti.TateCohomology.natCard_tateCohomology_zero_ofMulAction`:
  `|H-hat^0(G, ℤ[X])| = ∏_ω |G_ω|`.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction`: `h(ℤ[X]) = ∏_ω |G_ω|`.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction_of_isPretransitive`: `h(ℤ[X]) = |G_x|`
  for a transitive action.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction_sum`: multiplicativity over a disjoint union.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction_sigma`: multiplicativity over a finite
  sigma family with finite fibre orbit spaces.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction_sigma_of_isPretransitive`: the product
  of the stabilizer orders for a finite family of transitive actions.
* `TauCeti.TateCohomology.herbrandQuotient_ofMulAction_quotient`: `h(ℤ[G ⧸ H]) = |H|`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII.
-/

public noncomputable section

universe u

open CategoryTheory MonoidAlgebra MulAction Representation LinearMap

namespace TauCeti.TateCohomology

section General

variable {R G X : Type u} [CommRing R] [Group G] [MulAction G X]

variable (R G X) in
/-- The coefficients of an invariant vector at the chosen orbit representatives, each modulo the
order of the stabilizer of its representative. Its kernel is the image of the norm. -/
private def evalOut : (Rep.ofMulAction R G X).ρ.invariants →ₗ[R]
    ((ω : orbitRel.Quotient G X) → R ⧸ Ideal.span {(Nat.card (stabilizer G ω.out) : R)}) :=
  LinearMap.pi fun ω ↦ Submodule.mkQ _ ∘ₗ Finsupp.lapply ω.out ∘ₗ
    (coeffLinearEquiv R).toLinearMap ∘ₗ Submodule.subtype _

private theorem evalOut_apply (v : (Rep.ofMulAction R G X).ρ.invariants)
    (ω : orbitRel.Quotient G X) :
    evalOut R G X v ω = Ideal.Quotient.mk _ ((v : R[X]).coeff ω.out) :=
  rfl

private theorem evalOut_surjective [Finite X] : Function.Surjective (evalOut R G X) := by
  intro c
  choose r hr using fun ω ↦ Ideal.Quotient.mk_surjective (c ω)
  have := Fintype.ofFinite X
  -- the vector whose coefficient at `x` is the chosen lift at the orbit of `x`
  let v : R[X] := ofCoeff (Finsupp.equivFunOnFinite.symm fun x ↦ r (Quotient.mk _ x))
  refine ⟨⟨v, fun g ↦ ?_⟩, funext fun ω ↦ ?_⟩
  · ext x
    simp only [v, coeff_ofMulAction, Finsupp.coe_equivFunOnFinite_symm]
    exact congrArg r (Quotient.sound (mem_orbit x g⁻¹))
  · rw [evalOut_apply]
    simp [v, hr]

variable [Fintype G]

/-- **Degree `-1` Tate cohomology of a permutation module vanishes** as soon as multiplication by
`|G|` is injective on the coefficient ring. -/
theorem subsingleton_tateCohomology_negOne_ofMulAction_of_isSMulRegular
    (hR : IsSMulRegular R (Fintype.card G)) :
    Subsingleton (tateCohomology (Rep.ofMulAction R G X) (-1)) :=
  subsingleton_of_forall_eq 0 fun x ↦ HNegOne_induction_on x fun y ↦
    (HNegOneπ_eq_zero_iff y).2 (ker_norm_ofMulAction_le_coinvariantsKer hR y.2)

/-- Degree `-1` Tate cohomology of a permutation module vanishes over a coefficient ring without
additive torsion. -/
instance subsingleton_tateCohomology_negOne_ofMulAction [IsAddTorsionFree R] :
    Subsingleton (tateCohomology (Rep.ofMulAction R G X) (-1)) :=
  subsingleton_tateCohomology_negOne_ofMulAction_of_isSMulRegular
    (.nat_of_isAddTorsionFree Fintype.card_ne_zero)

/-- The coefficient of a norm at an orbit representative is divisible by the order of its
stabilizer. -/
private theorem dvd_coeff_norm (w : R[X]) (ω : orbitRel.Quotient G X) :
    (Nat.card (stabilizer G ω.out) : R) ∣ ((ofMulAction R G X).norm w).coeff ω.out := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw => simpa using dvd_add hv hw
  | single x r =>
    -- move the basis vector to the representative of its orbit, which does not change its norm
    obtain ⟨g, hg⟩ : ∃ g : G, g • (Quotient.mk (orbitRel G X) x).out = x :=
      mem_orbit_symm.1 (Quotient.mk_out (s := orbitRel G X) x)
    rw [← hg, ← ofMulAction_single, norm_self_apply]
    by_cases hω : Quotient.mk (orbitRel G X) x = ω
    · subst hω
      rw [coeff_norm_ofMulAction_single_self, nsmul_eq_mul]
      exact dvd_mul_right _ _
    · rw [coeff_norm_ofMulAction_single_of_notMem_orbit
        fun h ↦ hω (Quotient.out_equiv_out.1 h).symm]
      exact dvd_zero _

private theorem ker_evalOut [Finite X] :
    ker (evalOut R G X) =
      (range (Rep.ofMulAction R G X).ρ.norm).submoduleOf (Rep.ofMulAction R G X).ρ.invariants := by
  have := Fintype.ofFinite (orbitRel.Quotient G X)
  ext ⟨v, hv⟩
  rw [mem_ker, funext_iff]
  refine (forall_congr' fun ω : orbitRel.Quotient G X ↦
    Ideal.Quotient.eq_zero_iff_dvd _ (v.coeff ω.out)).trans ⟨fun h ↦ ?_, ?_⟩
  · -- an invariant vector with coefficient `|G_ω| s_ω` at each representative is the norm of
    -- `∑_ω s_ω • ω.out`
    choose s hs using h
    refine ⟨∑ ω, single ω.out (s ω), eq_of_coeff_out_eq_of_forall_ofMulAction_eq
      (fun g ↦ self_norm_apply (ofMulAction R G X) g _) hv fun ω ↦ ?_⟩
    rw [map_sum, coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single ω,
      coeff_norm_ofMulAction_single_self, nsmul_eq_mul, Submodule.subtype_apply, hs]
    · intro ω' _ hω'
      exact coeff_norm_ofMulAction_single_of_notMem_orbit
        (fun h ↦ hω' (Quotient.out_equiv_out.1 h).symm) _
    · simp
  · rintro ⟨w, hw⟩ ω
    rw [Submodule.subtype_apply, Submodule.coe_mk] at hw
    rw [← hw]
    exact dvd_coeff_norm w ω

variable (R G X) in
/-- **Degree-zero Tate cohomology of a permutation module.** For a finite `G`-set `X`,
`H-hat^0(G, R[X])` is the product over the orbits `ω` of `R ⧸ (|G_ω|)`, where `G_ω` is the
stabilizer of the chosen representative of `ω`. A class is sent to the residues of the
coefficients of an invariant representative at the orbit representatives
(`H0LinearEquivPiQuotientStabilizer_H0π`). -/
def H0LinearEquivPiQuotientStabilizer [Finite X] :
    tateCohomology (Rep.ofMulAction R G X) 0 ≃ₗ[R]
      ((ω : orbitRel.Quotient G X) → R ⧸ Ideal.span {(Nat.card (stabilizer G ω.out) : R)}) :=
  (H0IsoNormQuotient _).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ ker_evalOut.symm ≪≫ₗ
    (evalOut R G X).quotKerEquivOfSurjective evalOut_surjective

-- `dsimp% only` on the left-hand side: see the comment on `H0π_eq_zero_iff`.
/-- The degree-zero equivalence sends the class of an invariant vector to the residues of its
coefficients at the orbit representatives. -/
@[simp]
theorem H0LinearEquivPiQuotientStabilizer_H0π [Finite X]
    (v : (Rep.ofMulAction R G X).ρ.invariants) (ω : orbitRel.Quotient G X) :
    (dsimp% only (H0LinearEquivPiQuotientStabilizer R G X (H0π (Rep.ofMulAction R G X) v) ω)) =
      Ideal.Quotient.mk _ ((v : R[X]).coeff ω.out) := by
  simp only [H0LinearEquivPiQuotientStabilizer, LinearEquiv.trans_apply]
  rw [Iso.toLinearEquiv_apply, H0π_comp_H0IsoNormQuotient_hom_apply]
  exact evalOut_apply v ω

end General

section Int

-- Mathlib's Tate cohomology takes its coefficient ring and its group in a single universe, so
-- with integral coefficients the group is confined to `Type`.
variable {G X : Type} [Group G] [Fintype G] [MulAction G X] [Fintype (orbitRel.Quotient G X)]

/-- The order of `H-hat^0(G, ℤ[X])` is the product over the orbits of the orders of the
stabilizers. -/
theorem natCard_tateCohomology_zero_ofMulAction :
    Nat.card (tateCohomology (Rep.ofMulAction ℤ G X) 0) =
      ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G ω.out) := by
  have : Finite X := .of_equiv _ (selfEquivSigmaOrbitsQuotientStabilizer G X).symm
  rw [Nat.card_congr (H0LinearEquivPiQuotientStabilizer ℤ G X).toEquiv, Nat.card_pi]
  exact Finset.prod_congr rfl fun ω _ ↦ by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]

/-- **The Herbrand quotient of a permutation module** `ℤ[X]` is the product over the orbits of the
orders of the stabilizers. -/
theorem herbrandQuotient_ofMulAction :
    herbrandQuotient (Rep.ofMulAction ℤ G X) =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G ω.out) : ℚ) := by
  rw [herbrandQuotient_def, natCard_tateCohomology_zero_ofMulAction,
    Nat.card_of_subsingleton (0 : tateCohomology (Rep.ofMulAction ℤ G X) (-1))]
  simp

end Int

/-- For a transitive action, the Herbrand quotient of `ℤ[X]` is the order of a point
stabilizer. -/
theorem herbrandQuotient_ofMulAction_of_isPretransitive {G X : Type} [Group G] [Fintype G]
    [MulAction G X] [IsPretransitive G X] (x : X) :
    herbrandQuotient (Rep.ofMulAction ℤ G X) = Nat.card (stabilizer G x) := by
  have := (pretransitive_iff_subsingleton_quotient G X).1 ‹_›
  have := Fintype.ofSubsingleton (Quotient.mk (orbitRel G X) x)
  rw [herbrandQuotient_ofMulAction, Fintype.prod_subsingleton _ (Quotient.mk (orbitRel G X) x),
    Nat.card_congr
      (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G X) x)).toEquiv]

/-- The Herbrand quotient of a permutation lattice on a disjoint union is the product of
those of its two summands. No cyclicity is needed. -/
theorem herbrandQuotient_ofMulAction_sum {G X Y : Type} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y]
    [Finite (orbitRel.Quotient G X)] [Finite (orbitRel.Quotient G Y)] :
    herbrandQuotient (Rep.ofMulAction ℤ G (X ⊕ Y)) =
      herbrandQuotient (Rep.ofMulAction ℤ G X) *
        herbrandQuotient (Rep.ofMulAction ℤ G Y) := by
  classical
  let e := TauCeti.MulAction.orbitRelQuotientSumEquiv (G := G) (X := X) (Y := Y)
  let := Fintype.ofFinite (orbitRel.Quotient G X)
  let := Fintype.ofFinite (orbitRel.Quotient G Y)
  let := Fintype.ofEquiv _ e.symm
  simp_rw [herbrandQuotient_ofMulAction, ← cardStabilizerOnOrbit_mk, Quotient.out_eq]
  calc
    _ = ∏ q : orbitRel.Quotient G X ⊕ orbitRel.Quotient G Y,
        ((q.elim cardStabilizerOnOrbit cardStabilizerOnOrbit : ℕ) : ℚ) :=
      (Fintype.prod_equiv e.symm _ _ fun q ↦ by simp [e]).symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

/-- The Herbrand quotient of a permutation lattice on a finite sigma family is the
product of the Herbrand quotients of its fibres, provided each fibre has finitely many orbits. -/
theorem herbrandQuotient_ofMulAction_sigma {G ι : Type} {X : ι → Type} [Group G] [Fintype G]
    [Fintype ι] [∀ i, MulAction G (X i)] [∀ i, Finite (orbitRel.Quotient G (X i))] :
    herbrandQuotient (Rep.ofMulAction ℤ G (Σ i, X i)) =
      ∏ i, herbrandQuotient (Rep.ofMulAction ℤ G (X i)) := by
  let : ∀ i, Fintype (orbitRel.Quotient G (X i)) := fun i ↦ Fintype.ofFinite _
  let e := TauCeti.MulAction.orbitRelQuotientSigmaEquiv (G := G) (Y := X)
  let := Fintype.ofEquiv (Σ i, orbitRel.Quotient G (X i)) e.symm
  rw [herbrandQuotient_ofMulAction]
  simp_rw [herbrandQuotient_ofMulAction]
  rw [← Fintype.prod_sigma (fun q : Σ i, orbitRel.Quotient G (X i) ↦
    (Nat.card (stabilizer G q.2.out) : ℚ))]
  refine Fintype.prod_equiv e _ _ fun ω ↦ ?_
  have h : orbitRel G (Σ i, X i) ω.out (Sigma.mk (e ω).1 (e ω).2.out) := by
    apply Quotient.exact
    apply e.injective
    rw [Quotient.out_eq]
    simp [e]
  rw [Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel h).toEquiv,
    TauCeti.MulAction.stabilizer_sigma_mk]

/-- For a finite family of nonempty transitive actions, the Herbrand quotient of the
permutation lattice is the product of the stabilizer orders, one for each fibre. -/
theorem herbrandQuotient_ofMulAction_sigma_of_isPretransitive {G ι : Type} {X : ι → Type}
    [Group G] [Fintype G] [Fintype ι] [∀ i, MulAction G (X i)]
    [∀ i, IsPretransitive G (X i)] (x : ∀ i, X i) :
    herbrandQuotient (Rep.ofMulAction ℤ G (Σ i, X i)) =
      ∏ i, (Nat.card (stabilizer G (x i)) : ℚ) := by
  let : ∀ i, Subsingleton (orbitRel.Quotient G (X i)) :=
    fun i ↦ (pretransitive_iff_subsingleton_quotient G (X i)).1 inferInstance
  let : ∀ i, Fintype (orbitRel.Quotient G (X i)) :=
    fun i ↦ Fintype.ofSubsingleton (Quotient.mk'' (x i))
  rw [herbrandQuotient_ofMulAction_sigma]
  exact Finset.prod_congr rfl fun i _ ↦ herbrandQuotient_ofMulAction_of_isPretransitive (x i)

/-- The Herbrand quotient of `ℤ[G ⧸ H]`, the module induced from the trivial `H`-module `ℤ`, is
`|H|`. -/
theorem herbrandQuotient_ofMulAction_quotient {G : Type} [Group G] [Fintype G] (H : Subgroup G) :
    herbrandQuotient (Rep.ofMulAction ℤ G (G ⧸ H)) = Nat.card H := by
  rw [herbrandQuotient_ofMulAction_of_isPretransitive ((1 : G) : G ⧸ H), stabilizer_quotient]

end TauCeti.TateCohomology
