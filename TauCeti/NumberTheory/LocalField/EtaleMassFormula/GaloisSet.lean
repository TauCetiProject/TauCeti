/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sum
public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Galois sets over a local field, their discriminant weight, and the étale mass

Let `K` be a nonarchimedean local field with absolute Galois group
`Gal(K^sep/K) = SeparableClosure K ≃ₐ[K] SeparableClosure K`. Bhargava's mass formula counts
étale `K`-algebras of degree `n` weighted by `1 / (#Aut · q ^ v(Disc))`. By Grothendieck's Galois
theory these algebras are the finite sets with a continuous action of `Gal(K^sep/K)`, and the
étale algebra attached to a single orbit is the field fixed by the stabilizer of one of its points.
This file sets up that carrier and its weight.

For any set `X` with an action of `Gal(K^sep/K)`, `TauCeti.orbitDiscriminantExponent K X` is the
sum, over the orbits of `X`, of the discriminant exponent `d(F / K)` of the field `F` fixed by the
stabilizer of a point of the orbit (Tau Ceti's `IntermediateField.discriminantExponent`, which is
`0` on infinite subextensions). The choice of the point does not matter: the stabilizer of `σ • x`
is conjugate to that of `x`, so its fixed field is the image of that of `x` under `σ`, a
`K`-isomorphic field. Mathematically, for the Galois set of an étale algebra `A` this weight is
the valuation of the discriminant of `A`, Bhargava's `v(Disc A)`; that identification is not
proved in this file.

A Galois set of size `n`, `TauCeti.GaloisSet K n`, is a homomorphism
`Gal(K^sep/K) →* Equiv.Perm (Fin n)` with open kernel, that is a continuous action of
`Gal(K^sep/K)` on `Fin n`. Its stabilizers contain the kernel, so they are open, their fixed fields
are finite over `K`, and the degree of the field fixed by the stabilizer of `i` is the size of the
orbit of `i`, by the infinite Galois correspondence and orbit–stabilizer.

The étale mass `TauCeti.etaleMass K n` is `1 / n!` times the sum of `q ^ (-d(ρ))` over the Galois
sets `ρ` of size `n`, where `q` is the cardinality of the residue field. It is the quantity that
Bhargava's mass formula evaluates.

The Galois sets and their stabilizers make sense over any field; only the weight and the mass use
the local-field structure of `K`.

## Main definitions

* `TauCeti.orbitDiscriminantExponent K X`: the discriminant weight of a `Gal(K^sep/K)`-set.
* `TauCeti.GaloisSet K n`: the Galois sets of size `n`.
* `TauCeti.GaloisSet.mulAction`, `TauCeti.GaloisSet.discriminantExponent`,
  `TauCeti.GaloisSet.IsTransitive`: the action that a Galois set is, its weight, and transitivity.
* `TauCeti.etaleMass K n`: the étale mass `M_n(K)`.

## Main results

* `TauCeti.discriminantExponent_fixedField_stabilizer_smul` and
  `TauCeti.discriminantExponent_fixedField_stabilizer_out`: the summand of an orbit may be
  computed at any of its points.
* `TauCeti.orbitDiscriminantExponent_of_isPretransitive`: a transitive action has the weight of
  the fixed field of any point stabilizer.
* `TauCeti.orbitDiscriminantExponent_eq_zero_of_forall_smul_eq`: a trivial action has weight `0`.
* `TauCeti.orbitDiscriminantExponent_sum`: the weight is additive over disjoint unions.
* `TauCeti.orbitDiscriminantExponent_congr`: the weight is invariant under equivariant
  bijections.
* `TauCeti.GaloisSet.finrank_fixedField_stabilizer`: the field fixed by the stabilizer of `i` has
  degree the orbit size of `i`.
* `TauCeti.GaloisSet.discriminantExponent_of_isTransitive`: a transitive Galois set has the
  weight of the field fixed by the stabilizer of any point.
* `TauCeti.etaleMass_zero` and `TauCeti.etaleMass_one`: `M_0(K) = M_1(K) = 1`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021, for the
  formulation by Galois sets.
-/

public section
noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The **discriminant weight** of a set `X` with an action of `Gal(K^sep/K)`: the sum, over the
orbits of `X`, of the discriminant exponent of the field fixed by the stabilizer of a point of the
orbit. The point chosen does not matter (`discriminantExponent_fixedField_stabilizer_out`). For a
finite set with open stabilizers this is meant as the valuation of the discriminant of the
corresponding étale algebra. As a `finsum`, it is `0` when infinitely many orbits contribute. -/
def orbitDiscriminantExponent (X : Type*) [MulAction Gal(SeparableClosure K/K) X] : ℕ :=
  ∑ᶠ O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X,
    (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).discriminantExponent

/-- The defining formula of `orbitDiscriminantExponent`: a sum over the orbits, each evaluated at
its chosen representative. -/
theorem orbitDiscriminantExponent_def (X : Type*) [MulAction Gal(SeparableClosure K/K) X] :
    orbitDiscriminantExponent K X =
      ∑ᶠ O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X,
        (fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).discriminantExponent := by
  rw [orbitDiscriminantExponent]

variable {K}

section Orbit

variable {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

/-- **The fixed field of a stabilizer depends on the point only up to `K`-isomorphism**, so its
discriminant exponent is constant along an orbit: the field fixed by the stabilizer of `σ • x` is
the image under `σ` of the field fixed by the stabilizer of `x`. -/
theorem discriminantExponent_fixedField_stabilizer_smul (σ : Gal(SeparableClosure K/K)) (x : X) :
    (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x))).discriminantExponent =
      (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  rw [fixedField_stabilizer_smul]
  exact (IntermediateField.discriminantExponent_eq_of_algEquiv (intermediateFieldMap σ _)).symm

/-- The summand of `orbitDiscriminantExponent` at an orbit `O` may be computed at any point `x`
of `O` instead of the chosen representative `O.out`. -/
theorem discriminantExponent_fixedField_stabilizer_out
    {O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (h : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = O) :
    (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).discriminantExponent =
      (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_out_eq h
  rw [← hσ, discriminantExponent_fixedField_stabilizer_smul]

variable (K) in
/-- **The weight of a transitive action** is the discriminant exponent of the field fixed by the
stabilizer of any point: there is a single orbit. -/
theorem orbitDiscriminantExponent_of_isPretransitive
    [MulAction.IsPretransitive Gal(SeparableClosure K/K) X] (x : X) :
    orbitDiscriminantExponent K X =
      (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)).discriminantExponent := by
  have : Nonempty X := ⟨x⟩
  let _ := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) X).mp ‹_›).some
  rw [orbitDiscriminantExponent, finsum_unique]
  exact discriminantExponent_fixedField_stabilizer_out (Subsingleton.elim _ _)

variable (K) in
/-- **A trivial action has weight `0`**: every stabilizer is the whole Galois group, whose fixed
field is `K`. In particular a one-point set has weight `0`. -/
theorem orbitDiscriminantExponent_eq_zero_of_forall_smul_eq
    (h : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), σ • x = x) :
    orbitDiscriminantExponent K X = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun O ↦ ?_
  have : MulAction.stabilizer Gal(SeparableClosure K/K) O.out = ⊤ :=
    eq_top_iff.2 fun σ _ ↦ h σ _
  rw [this, InfiniteGalois.fixedField_bot, discriminantExponent_bot]

variable (K) in
/-- **The weight is invariant under equivariant bijections**: a `Gal(K^sep/K)`-equivariant
bijection `X ≃ Y` matches the orbits and the point stabilizers. -/
theorem orbitDiscriminantExponent_congr {Y : Type*} [MulAction Gal(SeparableClosure K/K) Y]
    (e : X ≃ Y) (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), e (σ • x) = σ • e x) :
    orbitDiscriminantExponent K X = orbitDiscriminantExponent K Y := by
  rw [orbitDiscriminantExponent, orbitDiscriminantExponent,
    ← finsum_comp_equiv (MulAction.orbitRelQuotientCongr (MulEquiv.refl _) e he)]
  refine finsum_congr fun O ↦ ?_
  induction O using Quotient.inductionOn' with | h x => ?_
  have hstab : MulAction.stabilizer Gal(SeparableClosure K/K) (e x) =
      MulAction.stabilizer Gal(SeparableClosure K/K) x := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← he, e.apply_eq_iff_eq]
  rw [discriminantExponent_fixedField_stabilizer_out rfl,
    discriminantExponent_fixedField_stabilizer_out
      (MulAction.orbitRelQuotientCongr_mk _ _ he x).symm,
    hstab]

variable (K) in
/-- **The weight of a disjoint union is the sum of the weights**, provided each summand has
finitely many orbits. The orbits of `X ⊕ Y` are those of `X` and those of `Y`, with the same
stabilizers. -/
theorem orbitDiscriminantExponent_sum {Y : Type*} [MulAction Gal(SeparableClosure K/K) Y]
    [Finite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X)]
    [Finite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) Y)] :
    orbitDiscriminantExponent K (X ⊕ Y) =
      orbitDiscriminantExponent K X + orbitDiscriminantExponent K Y := by
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X)
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) Y)
  have := Fintype.ofEquiv _ (MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := X) (Y := Y)).symm
  simp only [orbitDiscriminantExponent, finsum_eq_sum_of_fintype]
  rw [← MulAction.orbitRelQuotientSumEquiv.symm.sum_comp, Fintype.sum_sum_type]
  congr 1 <;> refine Finset.sum_congr rfl fun O _ ↦ ?_ <;>
    induction O using Quotient.inductionOn' with | h x => ?_
  -- the orbit of `Sum.inl x` (or `Sum.inr x`) has the stabilizer of `x`
  all_goals
    simp only [MulAction.orbitRelQuotientSumEquiv_symm_inl_mk,
      MulAction.orbitRelQuotientSumEquiv_symm_inr_mk]
    rw [discriminantExponent_fixedField_stabilizer_out rfl,
      discriminantExponent_fixedField_stabilizer_out rfl]
    congr 3
    ext σ
    simp [MulAction.mem_stabilizer_iff]

end Orbit

section GaloisSet

variable (K : Type*) [Field K]

/-- A **Galois set of size `n`**: a continuous action of `Gal(K^sep/K)` on `Fin n`, given as a
homomorphism `Gal(K^sep/K) →* Equiv.Perm (Fin n)` whose kernel is open in the Krull topology. -/
abbrev GaloisSet (n : ℕ) :=
  {ρ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin n) //
    IsOpen (ρ.ker : Set Gal(SeparableClosure K/K))}

namespace GaloisSet

variable {K} {n : ℕ}

/-- The action of `Gal(K^sep/K)` on `Fin n` that a Galois set is: `σ` acts by the permutation
`ρ σ`. -/
abbrev mulAction (ρ : GaloisSet K n) : MulAction Gal(SeparableClosure K/K) (Fin n) :=
  MulAction.compHom (Fin n) ρ.1

/-- In the action of a Galois set `ρ`, `σ` acts by the permutation `ρ σ`. -/
theorem smul_def (ρ : GaloisSet K n) (σ : Gal(SeparableClosure K/K)) (i : Fin n) :
    letI := ρ.mulAction
    σ • i = ρ.1 σ i :=
  rfl

/-- A Galois set is **transitive** when its action on `Fin n` is: it corresponds to a field
extension of `K` rather than a product of several. -/
def IsTransitive (ρ : GaloisSet K n) : Prop :=
  letI := ρ.mulAction
  MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n)

/-- A Galois set is transitive exactly when its action is pretransitive. -/
theorem isTransitive_def (ρ : GaloisSet K n) :
    ρ.IsTransitive ↔
      (letI := ρ.mulAction
      MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n)) :=
  Iff.rfl

/-- A Galois set is transitive exactly when any point can be carried to any other. -/
theorem isTransitive_iff (ρ : GaloisSet K n) :
    ρ.IsTransitive ↔ ∀ i j : Fin n, ∃ σ : Gal(SeparableClosure K/K), ρ.1 σ i = j :=
  letI := ρ.mulAction
  MulAction.isPretransitive_iff _ _

/-- The point stabilizers of a Galois set are open: they contain its open kernel. -/
theorem isOpen_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    IsOpen (MulAction.stabilizer Gal(SeparableClosure K/K) i : Set Gal(SeparableClosure K/K)) := by
  let _ := ρ.mulAction
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) ρ.2
  rw [MulAction.mem_stabilizer_iff, smul_def, MonoidHom.mem_ker.1 hσ, Equiv.Perm.one_apply]

/-- **The degree of a stabilizer's fixed field is the orbit size**: the field fixed by the
stabilizer of `i` has degree over `K` the cardinality of the orbit of `i`. -/
theorem finrank_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    Module.finrank K (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)) =
      Nat.card (MulAction.orbit Gal(SeparableClosure K/K) i) :=
  letI := ρ.mulAction
  IntermediateField.finrank_fixedField_stabilizer
    (Subgroup.isClosed_of_isOpen _ (ρ.isOpen_stabilizer i))

/-- The field fixed by a point stabilizer of a Galois set is finite over `K`. -/
theorem finiteDimensional_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    FiniteDimensional K (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)) := by
  let _ := ρ.mulAction
  refine Module.finite_of_finrank_pos ?_
  rw [finrank_fixedField_stabilizer, Nat.card_pos_iff]
  exact ⟨⟨⟨i, MulAction.mem_orbit_self i⟩⟩, inferInstance⟩

/-- The **trivial Galois set** of size `n`, on which `Gal(K^sep/K)` acts trivially; it corresponds
to the split algebra `K ^ n`. -/
instance : One (GaloisSet K n) :=
  ⟨⟨1, by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ⟩⟩

/-- The trivial Galois set is the trivial homomorphism. -/
@[simp]
theorem coe_one : ((1 : GaloisSet K n) : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin n)) = 1 :=
  rfl

/-- In sizes `0` and `1` the only Galois set is the trivial one; it corresponds to the zero
algebra, respectively to `K`. -/
instance [Subsingleton (Fin n)] : Unique (GaloisSet K n) where
  default := 1
  uniq _ := Subtype.ext (MonoidHom.ext fun _ ↦ Subsingleton.elim _ _)

end GaloisSet

end GaloisSet

namespace GaloisSet

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-- The **discriminant weight** `d(ρ)` of a Galois set: `orbitDiscriminantExponent` for its
action, the sum over its orbits of the discriminant exponents of the fields fixed by point
stabilizers. -/
def discriminantExponent (ρ : GaloisSet K n) : ℕ :=
  letI := ρ.mulAction
  orbitDiscriminantExponent K (Fin n)

/-- The weight of a Galois set is `orbitDiscriminantExponent` for its action. -/
theorem discriminantExponent_def (ρ : GaloisSet K n) :
    ρ.discriminantExponent =
      (letI := ρ.mulAction
      orbitDiscriminantExponent K (Fin n)) := by
  rw [discriminantExponent]

/-- **The weight of a transitive Galois set** is the discriminant exponent of the field fixed by
the stabilizer of any point: there is one orbit. -/
theorem discriminantExponent_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive)
    (i : Fin n) :
    ρ.discriminantExponent =
      (letI := ρ.mulAction
      (fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)).discriminantExponent) :=
  letI := ρ.mulAction
  haveI : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := hρ
  orbitDiscriminantExponent_of_isPretransitive K i

/-- The trivial Galois set has weight `0`: all its stabilizers fix only `K`. -/
@[simp]
theorem discriminantExponent_one : (1 : GaloisSet K n).discriminantExponent = 0 :=
  letI := (1 : GaloisSet K n).mulAction
  orbitDiscriminantExponent_eq_zero_of_forall_smul_eq K fun _ _ ↦ rfl

end GaloisSet

section EtaleMass

open scoped ENNReal Nat

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The étale mass** `M_n(K) = (1 / n!) ∑_ρ q ^ (-d(ρ))` of a nonarchimedean local field `K`
with residue field of cardinality `q`, summed over all Galois sets `ρ` of size `n`, in `ℝ≥0∞`.
Each isomorphism class of étale `K`-algebras `A` of degree `n` corresponds to `n! / #Aut_K(A)`
Galois sets, so mathematically this is Bhargava's `∑_[A] 1 / (#Aut_K(A) · q ^ v(Disc A))`; that
identification is not proved in this file. In equal
characteristic there are infinitely many Galois sets of size `n ≥ p`, which is why the sum is a
`tsum` in `ℝ≥0∞`. -/
def etaleMass (n : ℕ) : ℝ≥0∞ :=
  (n ! : ℝ≥0∞)⁻¹ * ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent

/-- The defining formula of the étale mass. -/
theorem etaleMass_def (n : ℕ) :
    etaleMass K n =
      (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent := by
  rw [etaleMass]

/-- `M_0(K) = 1`: the only Galois set of size `0` is the trivial one, of weight `0`. -/
@[simp]
theorem etaleMass_zero : etaleMass K 0 = 1 := by
  rw [etaleMass, tsum_eq_single 1 fun ρ hρ ↦ (hρ (Subsingleton.elim ρ 1)).elim]
  simp

/-- `M_1(K) = 1`: the only Galois set of size `1` is the trivial one, of weight `0`. -/
@[simp]
theorem etaleMass_one : etaleMass K 1 = 1 := by
  rw [etaleMass, tsum_eq_single 1 fun ρ hρ ↦ (hρ (Subsingleton.elim ρ 1)).elim]
  simp

end EtaleMass

end TauCeti
