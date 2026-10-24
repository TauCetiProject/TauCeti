/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.OddStructure
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The two signs of the line coordinate

A polarization `P` of a quadratic space `V = W ⊕ W' ⊕ L` carries a coordinate on its orthogonal
remainder `L` whose square is `Q`. Such a coordinate is determined only up to sign, and negating
it gives a second polarization `P⁻ = P.negLineCoordinate` with the same isotropic summands, the same
decomposition and the same pairing. Both make the exterior algebra `S = ⋀·W` into a module over
the Clifford algebra, and this file compares the two Fock actions `c_P` and `c_{P⁻}`.

The comparison is through the parity operator `J = CliffordAlgebra.involute` of `S`:

`c_{P⁻}(x) = J ∘ c_P(involute x) ∘ J` for every Clifford element `x`.

On an even element the grade involution does nothing, so `J` intertwines the two Fock actions of
the even Clifford subalgebra, and in particular the two Spin representations: the choice of sign is
invisible to `Spin(V)`.

On the whole Clifford algebra it is visible in odd dimension. There the volume element `ω` of a
spanning orthogonal list is central, odd, and squares to a scalar `c`, so whenever `W` is finite
free it acts on `S` by a scalar `λ` with `λ² = c` under `c_P`, and by `-λ` under `c_{P⁻}`.

Over a finite-dimensional field of characteristic not two, `c` is nonzero, so `λ ≠ -λ` and the two
Fock actions are the two distinct characters of the centre `F ⊕ F ω`. Each of them alone kills one
of the two central idempotents
`(1 ± λ⁻¹ ω) / 2`, so neither is faithful, but together they are: the combined action
`x ↦ (c_P(x), c_{P⁻}(x))` is an algebra isomorphism from the Clifford algebra onto
`End S × End S`. This is the operator form of the odd structure theorem
`CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one`, with the two blocks
labelled by the two signs of the line coordinate.

## Main definitions

* `TauCeti.SpinPolarizationData.negLineCoordinate`: the polarization `P⁻` with the line coordinate
  negated.
* `TauCeti.SpinPolarizationData.spinRepEquivNegLineCoordinate`: the parity operator, as an
  equivalence between the Spin representations of `P` and `P⁻`.
* `TauCeti.SpinPolarizationData.cliffordEquivEndProd`: in odd dimension over a finite-dimensional
  field of characteristic not two, the combined Fock action of `P` and `P⁻`, as an algebra
  isomorphism `CliffordAlgebra Q ≃ₐ[F] End S × End S`.

## Main results

* `TauCeti.SpinPolarizationData.spinAction_negLineCoordinate_apply`:
  `c_{P⁻}(x) = J c_P(involute x) J`.
* `TauCeti.SpinPolarizationData.spinAction_negLineCoordinate_apply_of_mem_even`: on even elements,
  `c_{P⁻}(x) = J c_P(x) J`.
* `TauCeti.SpinPolarizationData.exists_spinAction_volume_eq_algebraMap`: the volume element acts
  by opposite scalars `λ` and `-λ` under the two Fock actions, with `λ² = c`, when `W` is finite
  free.
* `TauCeti.SpinPolarizationData.spinAction_prod_bijective`: in odd dimension over a
  finite-dimensional field of characteristic not two, the combined Fock action is bijective, so the
  direct sum of the two spinor modules is faithful.
* `TauCeti.SpinPolarizationData.not_injective_spinAction_of_odd_finrank`: under the same
  hypotheses, a single Fock action is not faithful.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5: the two inequivalent
  irreducible Clifford modules in odd dimension, distinguished by the action of the volume element.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1.
-/

public section

open CliffordAlgebra Module

namespace TauCeti.SpinPolarizationData

universe u v

section CommRing

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- The polarization `P⁻` with the same isotropic summands, decomposition and pairing as `P`, and
the opposite line coordinate. The coordinate of the remainder is a square root of `Q`, so it is
pinned only up to this sign.

This is an `abbrev` so that the isotropic summand of `P⁻` is reducibly that of `P`: the two Fock
actions are then actions on one and the same spinor module `⋀·W`, with its instances, and can be
compared there. -/
abbrev negLineCoordinate : SpinPolarizationData Q where
  __ := P
  lineCoordinate := -P.lineCoordinate
  lineCoordinate_injective := neg_injective.comp P.lineCoordinate_injective
  lineCoordinate_sq z := by
    rw [LinearMap.neg_apply, neg_mul_neg, P.lineCoordinate_sq]

/-- The line coordinate of `P⁻` is the negative of that of `P`. -/
theorem lineCoordinate_negLineCoordinate (z : P.line) :
    P.negLineCoordinate.lineCoordinate z = -P.lineCoordinate z :=
  rfl

/-- Negating the line coordinate twice gives back the polarization. -/
@[simp]
theorem negLineCoordinate_negLineCoordinate : P.negLineCoordinate.negLineCoordinate = P := by
  simp only [negLineCoordinate, neg_neg]

/-- **The generators under the opposite line coordinate.** A vector acts through `P⁻` by minus the
conjugate of its action through `P` by the parity operator `J = involute` of `⋀·W`: the parity
operator anticommutes with creation and annihilation, which `P⁻` keeps, and commutes with itself,
which `P⁻` negates. -/
theorem spinAction_negLineCoordinate_ι_apply (v : V) (s : ExteriorAlgebra K P.W) :
    spinAction Q P.negLineCoordinate (ι Q v) s =
      -involute (spinAction Q P (ι Q v) (involute s)) := by
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := P.decompositionEquiv.surjective v
  simp only [P.decompositionEquiv_apply, map_add, LinearMap.add_apply, spinAction_ι_wedge,
    spinAction_ι_contract, spinAction_ι_lineOperator, LinearMap.neg_apply, neg_smul, map_mul,
    map_smul, involute_ι, involute_involute, involute_contractLeft, neg_mul, neg_add, neg_neg]

/-- **The two Fock actions differ by the parity operator.** For every Clifford element `x`,
`c_{P⁻}(x) = J ∘ c_P(involute x) ∘ J`, where `J = involute` is the grade involution of `⋀·W`. -/
theorem spinAction_negLineCoordinate_apply (x : CliffordAlgebra Q) (s : ExteriorAlgebra K P.W) :
    spinAction Q P.negLineCoordinate x s =
      involute (spinAction Q P (involute x) (involute s)) := by
  induction x using CliffordAlgebra.induction generalizing s with
  | algebraMap r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul, involute_involute]
  | ι v =>
    rw [spinAction_negLineCoordinate_ι_apply]
    simp only [involute_ι, map_neg, LinearMap.neg_apply]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb, involute_involute]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- **On the even Clifford subalgebra the parity operator intertwines the two Fock actions**:
`c_{P⁻}(x) = J ∘ c_P(x) ∘ J` for `x` even. -/
theorem spinAction_negLineCoordinate_apply_of_mem_even {x : CliffordAlgebra Q} (hx : x ∈ even Q)
    (s : ExteriorAlgebra K P.W) :
    spinAction Q P.negLineCoordinate x s = involute (spinAction Q P x (involute s)) := by
  have hx' : x ∈ evenOdd Q 0 := by rwa [← even_toSubmodule, Subalgebra.mem_toSubmodule]
  rw [spinAction_negLineCoordinate_apply, involute_eq_of_mem_even hx']

/-- **The sign of the line coordinate is invisible to the Spin group.** The parity operator
`J = involute` of `⋀·W` is an equivalence between the Spin representations of `P` and of `P⁻`. -/
noncomputable def spinRepEquivNegLineCoordinate :
    (spinRep Q P).Equiv (spinRep Q P.negLineCoordinate) :=
  .mk (involuteEquiv (Q := (0 : QuadraticForm K P.W))).toLinearEquiv fun g ↦
    LinearMap.ext fun s ↦ by
      simp [spinAction_negLineCoordinate_apply_of_mem_even P (spinGroup.mem_even g.2)]

@[simp]
theorem spinRepEquivNegLineCoordinate_apply (s : ExteriorAlgebra K P.W) :
    P.spinRepEquivNegLineCoordinate s = involute s :=
  -- `(rfl)`, not `rfl`: the body of `spinRepEquivNegLineCoordinate` is not `@[expose]`d.
  (rfl)

/-- **The volume element acts by opposite scalars under the two signs.** For a spanning list of
pairwise orthogonal vectors of odd length, the volume element `ω` is central with
`ω² = c = (-1) ^ (n choose 2) ∏ Q vᵢ`. When `W` is finite free, the Fock action of `P` sends `ω`
to a scalar `λ` with `λ² = c`, and since `ω` is odd the Fock action of `P⁻` sends it to `-λ`. -/
theorem exists_spinAction_volume_eq_algebraMap [Module.Free K P.W] [Module.Finite K P.W]
    {l : List V} (hl : l.Pairwise Q.IsOrtho) (hlen : Odd l.length)
    (hspan : Submodule.span K {x : V | x ∈ l} = ⊤) :
    ∃ a : K, a * a = (-1 : K) ^ l.length.choose 2 * (l.map Q).prod ∧
      spinAction Q P (l.map (ι Q)).prod =
        algebraMap K (Module.End K (ExteriorAlgebra K P.W)) a ∧
      spinAction Q P.negLineCoordinate (l.map (ι Q)).prod =
        algebraMap K (Module.End K (ExteriorAlgebra K P.W)) (-a) := by
  obtain ⟨a, ha⟩ := exists_spinAction_eq_algebraMap_of_mem_center P
    (prod_map_ι_mem_center_of_odd_length hl hlen hspan)
  -- Scalars act faithfully on `⋀·W`, as seen on `1`.
  have hinj : Function.Injective (algebraMap K (Module.End K (ExteriorAlgebra K P.W))) :=
    fun b c h ↦ by simpa [← Algebra.algebraMap_eq_smul_one] using congr($h 1)
  refine ⟨a, hinj ?_, ha, ?_⟩
  · rw [map_mul, ← ha, ← map_mul, prod_map_ι_sq_scalar hl, AlgHom.commutes]
  · refine LinearMap.ext fun s ↦ ?_
    rw [spinAction_negLineCoordinate_apply,
      involute_eq_of_mem_odd (prod_map_ι_mem_evenOdd_one_of_odd_length hlen), map_neg, ha]
    simp

end CommRing

/-! ### The two signs in odd dimension -/

section Field

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} (P : SpinPolarizationData Q) [NeZero (2 : F)]

/-- In odd dimension there is a Clifford element acting by `1` through `P` and by `0` through
`P⁻`: the central idempotent `(1 + λ⁻¹ ω) / 2` attached to the volume element `ω`, which acts
by `λ` and `-λ` respectively. -/
private theorem exists_spinAction_eq_one_and_spinAction_negLineCoordinate_eq_zero
    (hodd : Odd (finrank F V)) :
    ∃ e : CliffordAlgebra Q, spinAction Q P e = 1 ∧ spinAction Q P.negLineCoordinate e = 0 := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ :=
    (P.nondegenerate ((isUnit_of_invertible (2 : F)).isSMulRegular F)).exists_list_pairwise_isOrtho
  obtain ⟨a, hsq, hP, hN⟩ := exists_spinAction_volume_eq_algebraMap P hl (hlen ▸ hodd) hspan
  have ha : a ≠ 0 := by
    rintro rfl
    exact neg_one_pow_choose_two_mul_prod_map_ne_zero hQl (by rw [← hsq, mul_zero])
  refine ⟨(⅟2 : F) • (1 + a⁻¹ • (l.map (ι Q)).prod), ?_, ?_⟩
  · simp only [map_smul, map_add, hP, map_one, Algebra.algebraMap_eq_smul_one, smul_smul]
    match_scalars
    simp [ha, ← two_mul]
  · simp only [map_smul, map_add, hN, map_one, Algebra.algebraMap_eq_smul_one, smul_smul]
    match_scalars
    simp [ha]

/-- **The combined Fock action of the two signs is onto** in odd dimension: given endomorphisms
`f` and `g` of `⋀·W`, some Clifford element acts by `f` through `P` and by `g` through `P⁻`. -/
theorem spinAction_prod_surjective (hodd : Odd (finrank F V)) :
    Function.Surjective ((spinAction Q P).prod (spinAction Q P.negLineCoordinate)) := by
  obtain ⟨e, he₁, he₀⟩ := exists_spinAction_eq_one_and_spinAction_negLineCoordinate_eq_zero P hodd
  rintro ⟨f, g⟩
  obtain ⟨x, rfl⟩ := spinAction_surjective P f
  obtain ⟨y, rfl⟩ := spinAction_surjective P.negLineCoordinate g
  refine ⟨e * x + (1 - e) * y, Prod.ext ?_ ?_⟩ <;>
    simp [he₁, he₀]

/-- **The direct sum of the two spinor modules is faithful** in odd dimension: the combined Fock
action of `P` and `P⁻` is a bijection from the Clifford algebra onto `End S × End S`. -/
theorem spinAction_prod_bijective (hodd : Odd (finrank F V)) :
    Function.Bijective ((spinAction Q P).prod (spinAction Q P.negLineCoordinate)) := by
  -- The combined action is onto, and in dimension `2l + 1` both sides have dimension
  -- `2 ^ (2l + 1) = 2 · (2 ^ l) ^ 2`.
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  refine ⟨?_, spinAction_prod_surjective P hodd⟩
  obtain ⟨l, hV⟩ := hodd
  have hS := P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one hV
  have : Module.Finite F (CliffordAlgebra Q) := Module.finite_of_finrank_pos <| by
    rw [CliffordAlgebra.finrank_eq_two_pow]
    positivity
  have hdim : finrank F (CliffordAlgebra Q) =
      finrank F (Module.End F (ExteriorAlgebra F P.W) × Module.End F (ExteriorAlgebra F P.W)) := by
    rw [CliffordAlgebra.finrank_eq_two_pow, Module.finrank_prod, Module.finrank_linearMap, hS, hV]
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := ((spinAction Q P).prod (spinAction Q P.negLineCoordinate)).toLinearMap) hdim).2
    (spinAction_prod_surjective P ⟨l, hV⟩)

/-- **The odd structure theorem, labelled by the two signs of the line coordinate**: in odd
dimension the combined Fock action of `P` and `P⁻` is an algebra isomorphism from the Clifford
algebra onto `End S × End S`, for `S = ⋀·W`. -/
noncomputable def cliffordEquivEndProd (hodd : Odd (finrank F V)) :
    CliffordAlgebra Q ≃ₐ[F]
      Module.End F (ExteriorAlgebra F P.W) × Module.End F (ExteriorAlgebra F P.W) :=
  AlgEquiv.ofBijective _ (spinAction_prod_bijective P hodd)

@[simp]
theorem cliffordEquivEndProd_apply (hodd : Odd (finrank F V)) (x : CliffordAlgebra Q) :
    P.cliffordEquivEndProd hodd x = (spinAction Q P x, spinAction Q P.negLineCoordinate x) :=
  -- `(rfl)`, not `rfl`: the body of `cliffordEquivEndProd` is not `@[expose]`d.
  (rfl)

/-- **A single Fock action is not faithful in odd dimension**: the central idempotent attached to
the opposite sign is a nonzero element acting by zero. -/
theorem not_injective_spinAction_of_odd_finrank (hodd : Odd (finrank F V)) :
    ¬ Function.Injective (spinAction Q P) := by
  intro hinj
  obtain ⟨e, he₁, he₀⟩ := exists_spinAction_eq_one_and_spinAction_negLineCoordinate_eq_zero
    P.negLineCoordinate hodd
  rw [negLineCoordinate_negLineCoordinate] at he₀
  have h0 : e = 0 := hinj (by rw [he₀, map_zero])
  exact one_ne_zero (he₁.symm.trans (by rw [h0, map_zero]))

end Field

end TauCeti.SpinPolarizationData
