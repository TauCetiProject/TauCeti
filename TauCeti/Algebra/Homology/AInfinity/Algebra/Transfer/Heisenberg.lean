/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Massey
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading

/-!
# A finite homological transfer with a nonzero ternary operation

Let `R` be a commutative ring and let `A = Λ_R(a, b, c)` be the exterior algebra on three
generators of cohomological degree one, with the differential determined by

`d a = d b = 0`,   `d c = a b`.

This is the cochain algebra of the Heisenberg Lie algebra.  Concretely, `d` is left multiplication
by `a b` after contraction against the coordinate of `c`; since `a b` is even and contraction is an
odd derivation, `d` satisfies the graded Leibniz rule, and `d² = 0` because the coordinate of `c`
vanishes on `a b`.

In the exterior basis `1, a, b, c, ab, ac, bc, abc` the differential is nonzero only on `c`, so the
cohomology has the representatives `1, a, b, ac, bc, abc`.  The homotopy `h`, left multiplication
by `c` after contraction against the coordinates of `a` and of `b`, sends `ab` to `c` and kills
the other basis vectors.  With `π = 1 - (d h + h d)`, which kills `c` and `ab` and fixes the other
basis vectors, the inclusion `i [z] = π z` of cohomology classes and the projection
`p x = [π x]` form a special contraction of `(A, d)` onto its cohomology with zero differential
(`TauCeti.HeisenbergDGA.contraction`): `p i = 1`, `1 - i p = d h + h d`, and
`h i = 0`, `p h = 0`, `h² = 0`.

Homological transfer along this contraction gives a minimal `A∞` structure on the cohomology
(`TauCeti.HeisenbergDGA.minimalModel`), whose binary operation is the cohomology product.  Since
`A` has no ternary operation, the transferred one is the Kontsevich--Soibelman/Merkulov tree sum
`p m₂ (h m₂ (i ⊗ i) ⊗ i) - p m₂ (i ⊗ h m₂ (i ⊗ i))`, the second term evaluated on the Koszul twist
of the first input.  On `([a], [a], [b])` the first term vanishes since `a² = 0`, and in the second
`h (a b) = c` while the twist turns `[a]` into `-[a]`, so

`m₃^H ([a], [a], [b]) = -p ((-a) c) = [a c]`,

which is nonzero over a nontrivial ring.  The sign is exactly the Koszul sign of moving `h` past
the first input: without it the answer would be `-[a c]`.  The quadratic component of the
extending `A∞` morphism is `f₂ ([a], [b]) = -h (a b) = -c`.  Finally `[a c]` is the value of the
defining system `(a, a, b, 0, c)` of the triple Massey product `⟨[a], [a], [b]⟩`, so the
transferred ternary operation selects an element of that Massey product.

## Main definitions

* `TauCeti.HeisenbergDGA.differential`: the differential with `d c = a b`.
* `TauCeti.HeisenbergDGA.aInfinityAlgebra`: the DG algebra `(Λ_R(a, b, c), d)` as an `A∞` algebra.
* `TauCeti.HeisenbergDGA.homotopy`: the contracting homotopy with `h (a b) = c`.
* `TauCeti.HeisenbergDGA.contraction`: the special contraction onto cohomology.
* `TauCeti.HeisenbergDGA.minimalModel`: the transferred minimal `A∞` structure on cohomology.
* `TauCeti.HeisenbergDGA.minimalModelInclusion`: the extending `A∞` quasi-isomorphism.

## Main results

* `TauCeti.HeisenbergDGA.isDGAlgebra`: `(Λ_R(a, b, c), d)` is a differential graded algebra.
* `TauCeti.HeisenbergDGA.differential_monomial`, `TauCeti.HeisenbergDGA.homotopy_monomial`: the
  differential and the homotopy on the exterior basis.
* `TauCeti.HeisenbergDGA.minimalModel_m_two`: the transferred binary operation is the cohomology
  product.
* `TauCeti.HeisenbergDGA.minimalModel_m_three`: `m₃^H ([a], [a], [b]) = [a c]`.
* `TauCeti.HeisenbergDGA.minimalModel_m_three_ne_zero`: this ternary operation is nonzero.
* `TauCeti.HeisenbergDGA.component_two_minimalModelInclusion`: `f₂ ([a], [b]) = -c`.
* `TauCeti.HeisenbergDGA.minimalModel_m_three_mem_tripleMasseyProduct`: `m₃^H ([a], [a], [b])`
  lies in the triple Massey product `⟨[a], [a], [b]⟩`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*,
  Section 6.4, for the tree formula of the transferred ternary operation.
* J. P. May, *Matric Massey products*, J. Algebra 12 (1969), 533--568, for triple Massey
  products.
-/

public section

open CliffordAlgebra TauCeti.ExteriorAlgebra

namespace TauCeti.HeisenbergDGA

variable (R : Type*) [CommRing R]

/-! ### The exterior algebra on three generators -/

/-- The exterior monomial of `Λ_R(a, b, c)` indexed by a subset of the generators: the product of
those generators in increasing order.  These form a basis. -/
noncomputable abbrev monomial (s : Finset (Fin 3)) : ExteriorAlgebra R (Fin 3 → R) :=
  (Pi.basisFun R (Fin 3)).ExteriorAlgebra s

/-- The generators `a`, `b`, `c` of `Λ_R(a, b, c)`, indexed by `0`, `1`, `2`. -/
noncomputable def gen (i : Fin 3) : ExteriorAlgebra R (Fin 3 → R) :=
  ExteriorAlgebra.ι R (Pi.single i 1)

/-- The `i`-th generator is the image under `ι` of the `i`-th standard basis vector. -/
theorem gen_def (i : Fin 3) : gen R i = ExteriorAlgebra.ι R (Pi.single i 1) := by
  rw [gen]

/-- A generator squares to zero. -/
@[simp]
theorem gen_mul_self (i : Fin 3) : gen R i * gen R i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- The basis vector of a singleton is the corresponding generator. -/
theorem monomial_singleton (i : Fin 3) : monomial R {i} = gen R i := by
  simp [gen]

/-- The basis vector of a pair is the product of the two generators in increasing order. -/
theorem monomial_pair {i j : Fin 3} (h : i < j) : monomial R {i, j} = gen R i * gen R j := by
  rw [monomial, basis_pair _ h]
  simp [gen]

/-- Left multiplication by a generator on the exterior basis. -/
private theorem gen_mul_monomial (i : Fin 3) (s : Finset (Fin 3)) :
    gen R i * monomial R s =
      if i ∈ s then 0 else basisEraseSign i (insert i s) • monomial R (insert i s) := by
  rw [gen, ← Pi.basisFun_apply R, ι_mul_basis]

/-- Contraction of a generator is its coordinate. -/
private theorem contract_gen (i j : Fin 3) :
    contractLeft ((Pi.basisFun R (Fin 3)).coord i) (gen R j) = if i = j then 1 else 0 := by
  simp only [gen, contractLeft_ι, Module.Basis.coord_apply, Pi.basisFun_repr,
    Pi.single_apply]
  split_ifs <;> simp

/-- Contraction past a generator on the left. -/
private theorem contract_gen_mul (i j : Fin 3) (x : ExteriorAlgebra R (Fin 3 → R)) :
    contractLeft ((Pi.basisFun R (Fin 3)).coord i) (gen R j * x) =
      (if i = j then x else 0) - gen R j * contractLeft ((Pi.basisFun R (Fin 3)).coord i) x := by
  simp only [gen, contractLeft_ι_mul, Module.Basis.coord_apply, Pi.basisFun_repr,
    Pi.single_apply]
  split_ifs <;> simp

/-! ### The grading -/

/-- The generators have degree one. -/
theorem gen_mem_integerGrading (i : Fin 3) : gen R i ∈ integerGrading R (Fin 3 → R) 1 :=
  ι_mem_integerGrading_one _

/-! ### The differential -/

/-- The **differential** of `Λ_R(a, b, c)`: left multiplication by `a b` after contraction against
the coordinate of `c`.  It sends `c` to `a b` and kills `a` and `b`. -/
noncomputable def differential : Module.End R (ExteriorAlgebra R (Fin 3 → R)) :=
  LinearMap.mulLeft R (gen R 0 * gen R 1) ∘ₗ
    contractLeft (Q := (0 : QuadraticForm R (Fin 3 → R))) ((Pi.basisFun R (Fin 3)).coord 2)

/-- The differential is left multiplication by `a b` after contraction against the coordinate of
`c`. -/
theorem differential_apply (x : ExteriorAlgebra R (Fin 3 → R)) :
    differential R x = gen R 0 * gen R 1 * contractLeft ((Pi.basisFun R (Fin 3)).coord 2) x :=
  (rfl)

/-- **The differential on the exterior basis**: it sends `c` to `a b` and every other basis vector
to zero. -/
theorem differential_monomial (s : Finset (Fin 3)) :
    differential R (monomial R s) = if s = {2} then monomial R {0, 1} else 0 := by
  by_cases hs : s = {2}
  · subst hs
    rw [differential_apply, monomial_singleton, contract_gen]
    simp only [↓reduceIte, mul_one, monomial_pair R (show (0 : Fin 3) < 1 by decide)]
  · simp only [hs, ite_false, differential_apply, contractLeft_coord_basis, mul_assoc,
      Units.smul_def, mul_ite, mul_zero, mul_smul_comm, gen_mul_monomial, smul_ite, smul_zero]
    split_ifs <;> first | rfl | (exfalso; revert s; decide)

/-- The product `a b` commutes with every element, being even. -/
private theorem gen_mul_gen_mul_comm (x : ExteriorAlgebra R (Fin 3 → R)) :
    gen R 0 * gen R 1 * x = x * (gen R 0 * gen R 1) := by
  rw [mul_assoc, gen, gen, ExteriorAlgebra.ι_mul_eq_involute_mul (Pi.single 1 1), ← mul_assoc,
    ExteriorAlgebra.ι_mul_eq_involute_mul (Pi.single 0 1), involute_involute, mul_assoc]

/-- **`(Λ_R(a, b, c), d)` is a differential graded algebra.** -/
theorem isDGAlgebra : IsDGAlgebra (integerGrading R (Fin 3 → R)) (differential R) where
  map_mem {p x} hx := by
    have h := ι_mul_mem_integerGrading (Pi.single 0 1) (ι_mul_mem_integerGrading (Pi.single 1 1)
      (contractLeft_mem_integerGrading ((Pi.basisFun R (Fin 3)).coord 2) hx))
    rw [← gen_def, ← gen_def, ← mul_assoc, ← differential_apply,
      show p - 1 + 1 + 1 = p + 1 by ring] at h
    exact h
  sq_zero x := by
    have h01 : contractLeft ((Pi.basisFun R (Fin 3)).coord 2) (gen R 0 * gen R 1) = 0 := by
      simp [contract_gen_mul, contract_gen]
    rw [differential_apply, differential_apply, contractLeft_mul, h01, contractLeft_contractLeft]
    simp
  leibniz {p x} hx y := by
    simp only [differential_apply, contractLeft_mul, involute_of_mem_integerGrading hx, mul_add,
      smul_mul_assoc, mul_smul_comm, ← mul_assoc, gen_mul_gen_mul_comm R x]

/-! ### The `A∞` algebra -/

/-- The DG algebra `(Λ_R(a, b, c), d)` as an `A∞` algebra: `m₁ = d`, `m₂` the product, and no
higher operations. -/
noncomputable def aInfinityAlgebra : AInfinityAlgebra R (ExteriorAlgebra R (Fin 3 → R)) :=
  (isDGAlgebra R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra

/-- The `A∞` algebra carries the exterior-degree grading. -/
@[simp]
theorem aInfinityAlgebra_grading_piece :
    (aInfinityAlgebra R).grading.piece = integerGrading R (Fin 3 → R) := by
  rw [aInfinityAlgebra, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
    InternalGrading.ofDecomposition_piece]

/-- The differential of the `A∞` algebra is `differential`. -/
@[simp]
theorem aInfinityAlgebra_differential : (aInfinityAlgebra R).differential = differential R :=
  IsNonUnitalDGAlgebra.toAInfinityAlgebra_differential _

/-- The unary operation of the `A∞` algebra is the differential. -/
@[simp]
theorem aInfinityAlgebra_m_one (x : Fin 1 → ExteriorAlgebra R (Fin 3 → R)) :
    (aInfinityAlgebra R).m 1 x = differential R (x 0) :=
  IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply _ x

/-- The binary operation of the `A∞` algebra is the exterior product. -/
@[simp]
theorem aInfinityAlgebra_m_two (x : Fin 2 → ExteriorAlgebra R (Fin 3 → R)) :
    (aInfinityAlgebra R).m 2 x = x 0 * x 1 :=
  IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply _ x

/-- The ternary operation of the `A∞` algebra vanishes. -/
@[simp]
theorem aInfinityAlgebra_m_three : (aInfinityAlgebra R).m 3 = 0 :=
  IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_of_three_le _ le_rfl

/-- An element is a cycle of the `A∞` algebra exactly when the differential kills it. -/
theorem mem_cycles_aInfinityAlgebra {x : ExteriorAlgebra R (Fin 3 → R)} :
    x ∈ (aInfinityAlgebra R).cycles ↔ differential R x = 0 := by
  simp

/-- The generators `a` and `b` are cycles. -/
theorem gen_mem_cycles {i : Fin 3} (hi : i ≠ 2) : gen R i ∈ (aInfinityAlgebra R).cycles := by
  rw [mem_cycles_aInfinityAlgebra, ← monomial_singleton, differential_monomial]
  simp [hi]

/-- The product `a c` is a cycle. -/
theorem gen_zero_mul_gen_two_mem_cycles :
    gen R 0 * gen R 2 ∈ (aInfinityAlgebra R).cycles := by
  rw [mem_cycles_aInfinityAlgebra, ← monomial_pair R (show (0 : Fin 3) < 2 by decide),
    differential_monomial]
  simp

/-! ### The contracting homotopy -/

/-- The **contracting homotopy**: left multiplication by `c` after contraction against the
coordinates of `a` and of `b`.  It sends `a b` to `c` and kills the other basis vectors. -/
noncomputable def homotopy : Module.End R (ExteriorAlgebra R (Fin 3 → R)) :=
  LinearMap.mulLeft R (gen R 2) ∘ₗ
    contractLeft (Q := (0 : QuadraticForm R (Fin 3 → R))) ((Pi.basisFun R (Fin 3)).coord 1) ∘ₗ
    contractLeft (Q := (0 : QuadraticForm R (Fin 3 → R))) ((Pi.basisFun R (Fin 3)).coord 0)

/-- The homotopy is left multiplication by `c` after contraction against the coordinates of `a`
and of `b`. -/
theorem homotopy_apply (x : ExteriorAlgebra R (Fin 3 → R)) :
    homotopy R x = gen R 2 *
      contractLeft ((Pi.basisFun R (Fin 3)).coord 1)
        (contractLeft ((Pi.basisFun R (Fin 3)).coord 0) x) :=
  (rfl)

/-- **The homotopy on the exterior basis**: it sends `a b` to `c` and every other basis vector to
zero. -/
theorem homotopy_monomial (s : Finset (Fin 3)) :
    homotopy R (monomial R s) = if s = {0, 1} then monomial R {2} else 0 := by
  by_cases hs : s = {0, 1}
  · subst hs
    rw [homotopy_apply, monomial_pair R (show (0 : Fin 3) < 1 by decide), contract_gen_mul,
      contract_gen, monomial_singleton]
    simp +decide only [↓reduceIte, mul_zero, sub_zero, contract_gen, mul_one]
  · simp only [hs, ite_false, homotopy_apply, contractLeft_coord_basis, Units.smul_def,
      apply_ite
        (contractLeft (Q := (0 : QuadraticForm R (Fin 3 → R))) ((Pi.basisFun R (Fin 3)).coord 1)),
      map_zsmul, map_zero, mul_ite, mul_zero, mul_smul_comm, gen_mul_monomial, smul_ite, smul_zero]
    split_ifs <;> first | rfl | (exfalso; revert s; decide)

/-- The homotopy has degree `-1`. -/
theorem isHomogeneous_homotopy :
    LinearMap.IsHomogeneous (homotopy R) (aInfinityAlgebra R).grading.piece
      (aInfinityAlgebra R).grading.piece (-1) := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
  rw [aInfinityAlgebra_grading_piece] at hx ⊢
  have h := ι_mul_mem_integerGrading (Pi.single 2 1)
    (contractLeft_mem_integerGrading ((Pi.basisFun R (Fin 3)).coord 1)
      (contractLeft_mem_integerGrading ((Pi.basisFun R (Fin 3)).coord 0) hx))
  rwa [← gen_def, ← homotopy_apply, show p - 1 - 1 + 1 = p + -1 by ring] at h

/-! ### The projection onto the representatives -/

/-- The **projection onto the cohomology representatives** `1, a, b, a c, b c, a b c`:
`π = 1 - (d h + h d)`.  It kills `c` and `a b` and fixes the other basis vectors. -/
noncomputable def cycleProjection : Module.End R (ExteriorAlgebra R (Fin 3 → R)) :=
  LinearMap.id - (differential R ∘ₗ homotopy R + homotopy R ∘ₗ differential R)

/-- The projection is `x ↦ x - (d h x + h d x)`. -/
theorem cycleProjection_apply (x : ExteriorAlgebra R (Fin 3 → R)) :
    cycleProjection R x =
      x - (differential R (homotopy R x) + homotopy R (differential R x)) :=
  (rfl)

/-- The projection on the exterior basis. -/
theorem cycleProjection_monomial (s : Finset (Fin 3)) :
    cycleProjection R (monomial R s) = if s = {2} ∨ s = {0, 1} then 0 else monomial R s := by
  simp only [cycleProjection_apply, homotopy_monomial, differential_monomial,
    apply_ite (differential R), apply_ite (homotopy R), map_zero]
  split_ifs <;> simp_all +decide

/-- Linear endomorphisms of `Λ_R(a, b, c)` agree once they agree on the exterior basis. -/
private theorem ext_monomial {f g : Module.End R (ExteriorAlgebra R (Fin 3 → R))}
    (h : ∀ s, f (monomial R s) = g (monomial R s)) : f = g :=
  (Pi.basisFun R (Fin 3)).ExteriorAlgebra.ext h

/-- The projection lands in the cycles. -/
theorem differential_comp_cycleProjection : differential R ∘ₗ cycleProjection R = 0 :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, cycleProjection_monomial, apply_ite (differential R),
      differential_monomial, map_zero, LinearMap.zero_apply]
    split_ifs <;> simp_all +decide

/-- The projection kills the boundaries. -/
theorem cycleProjection_comp_differential : cycleProjection R ∘ₗ differential R = 0 :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, differential_monomial, apply_ite (cycleProjection R),
      cycleProjection_monomial, map_zero, LinearMap.zero_apply]
    split_ifs <;> simp_all +decide

/-- The projection is idempotent. -/
theorem cycleProjection_comp_cycleProjection :
    cycleProjection R ∘ₗ cycleProjection R = cycleProjection R :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, cycleProjection_monomial, apply_ite (cycleProjection R),
      map_zero]
    split_ifs <;> simp_all +decide

/-- The homotopy kills the representatives. -/
theorem homotopy_comp_cycleProjection : homotopy R ∘ₗ cycleProjection R = 0 :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, cycleProjection_monomial, apply_ite (homotopy R),
      homotopy_monomial,
      map_zero, LinearMap.zero_apply]
    split_ifs <;> simp_all +decide

/-- The projection kills the image of the homotopy. -/
theorem cycleProjection_comp_homotopy : cycleProjection R ∘ₗ homotopy R = 0 :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, homotopy_monomial, apply_ite (cycleProjection R),
      cycleProjection_monomial, map_zero, LinearMap.zero_apply]
    split_ifs <;> simp_all +decide

/-- The homotopy squares to zero. -/
theorem homotopy_comp_homotopy : homotopy R ∘ₗ homotopy R = 0 :=
  ext_monomial R fun s ↦ by
    simp only [LinearMap.comp_apply, homotopy_monomial, apply_ite (homotopy R), map_zero,
      LinearMap.zero_apply]
    split_ifs <;> simp_all +decide

/-- The projection lands in the cycles. -/
theorem cycleProjection_mem_cycles (x : ExteriorAlgebra R (Fin 3 → R)) :
    cycleProjection R x ∈ (aInfinityAlgebra R).cycles := by
  rw [mem_cycles_aInfinityAlgebra, ← LinearMap.comp_apply, differential_comp_cycleProjection,
    LinearMap.zero_apply]

/-- On a cycle, the projection changes the representative by a boundary. -/
theorem cycleProjection_sub_mem_boundaries {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    cycleProjection R x - x ∈ (aInfinityAlgebra R).boundaries := by
  rw [mem_cycles_aInfinityAlgebra] at hx
  refine (aInfinityAlgebra R).mem_boundaries.2 ⟨-homotopy R x, ?_⟩
  simp [cycleProjection_apply, hx]

/-- The projection has degree zero. -/
theorem isHomogeneous_cycleProjection :
    LinearMap.IsHomogeneous (cycleProjection R) (integerGrading R (Fin 3 → R))
      (integerGrading R (Fin 3 → R)) 0 := by
  have hd : LinearMap.IsHomogeneous (differential R) (integerGrading R (Fin 3 → R))
      (integerGrading R (Fin 3 → R)) 1 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ (isDGAlgebra R).map_mem hx
  have hh : LinearMap.IsHomogeneous (homotopy R) (integerGrading R (Fin 3 → R))
      (integerGrading R (Fin 3 → R)) (-1) := by
    simpa only [aInfinityAlgebra_grading_piece] using isHomogeneous_homotopy R
  refine LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
  refine sub_mem (by simpa using hx) (add_mem ?_ ?_)
  · simpa using hd.map_mem (hh.map_mem hx)
  · simpa using hh.map_mem (hd.map_mem hx)

/-! ### The contraction onto cohomology -/

/-- The inclusion of cohomology: a class is sent to the projection of any representative. -/
private noncomputable def inclusion :
    (aInfinityAlgebra R).Cohomology →ₗ[R] ExteriorAlgebra R (Fin 3 → R) :=
  (aInfinityAlgebra R).boundariesInCycles.liftQ
    (cycleProjection R ∘ₗ (aInfinityAlgebra R).cycles.subtype) fun z hz ↦ by
      obtain ⟨y, hy⟩ := (aInfinityAlgebra R).mem_boundaries.1
        ((aInfinityAlgebra R).mem_boundariesInCycles.1 hz)
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hy,
        aInfinityAlgebra_m_one, ← LinearMap.comp_apply, cycleProjection_comp_differential,
        LinearMap.zero_apply]

private theorem inclusion_cohomologyClass {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    inclusion R ((aInfinityAlgebra R).cohomologyClass hx) = cycleProjection R x := by
  rw [AInfinityAlgebra.cohomologyClass_eq_mk, inclusion, Submodule.liftQ_apply]
  rfl

/-- The projection to cohomology: the class of the projection onto the representatives. -/
private noncomputable def projection :
    ExteriorAlgebra R (Fin 3 → R) →ₗ[R] (aInfinityAlgebra R).Cohomology :=
  (aInfinityAlgebra R).cohomologyClassLinearMap ∘ₗ
    (cycleProjection R).codRestrict (aInfinityAlgebra R).cycles (cycleProjection_mem_cycles R)

private theorem projection_apply (x : ExteriorAlgebra R (Fin 3 → R)) :
    projection R x = (aInfinityAlgebra R).cohomologyClass (cycleProjection_mem_cycles R x) := by
  simp [projection]

private theorem projection_of_mem_cycles {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    projection R x = (aInfinityAlgebra R).cohomologyClass hx := by
  rw [projection_apply, AInfinityAlgebra.cohomologyClass_eq_iff]
  exact cycleProjection_sub_mem_boundaries R hx

/-- The **special contraction of `(Λ_R(a, b, c), d)` onto its cohomology**: the inclusion sends a
class to the projection `π` of a representative, the projection sends `x` to the class of `π x`,
and the homotopy sends `a b` to `c`. -/
noncomputable def contraction :
    LinearSpecialContraction (aInfinityAlgebra R).differential
      (0 : Module.End R (aInfinityAlgebra R).Cohomology) where
  incl := inclusion R
  proj := projection R
  homotopy := homotopy R
  dM_comp_incl := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.comp_zero,
      LinearMap.zero_apply, aInfinityAlgebra_differential]
    rw [← (aInfinityAlgebra R).cohomologyClass_eq_mk z.2, inclusion_cohomologyClass,
      ← LinearMap.comp_apply, differential_comp_cycleProjection, LinearMap.zero_apply]
  proj_comp_dM := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
      aInfinityAlgebra_differential, projection_apply]
    simp_rw [← LinearMap.comp_apply (cycleProjection R), cycleProjection_comp_differential]
    exact (aInfinityAlgebra R).cohomologyClass_zero
  proj_comp_incl := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.id_comp]
    rw [← (aInfinityAlgebra R).cohomologyClass_eq_mk z.2, inclusion_cohomologyClass,
      projection_of_mem_cycles R (cycleProjection_mem_cycles R _),
      AInfinityAlgebra.cohomologyClass_eq_iff]
    exact cycleProjection_sub_mem_boundaries R z.2
  dM_comp_homotopy_add_homotopy_comp_dM := by
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, projection_apply,
      inclusion_cohomologyClass, ← LinearMap.comp_apply (cycleProjection R),
      cycleProjection_comp_cycleProjection, aInfinityAlgebra_differential, cycleProjection_apply,
      sub_sub_cancel, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  homotopy_comp_incl := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_comp,
      LinearMap.zero_apply]
    rw [← (aInfinityAlgebra R).cohomologyClass_eq_mk z.2, inclusion_cohomologyClass,
      ← LinearMap.comp_apply, homotopy_comp_cycleProjection, LinearMap.zero_apply]
  proj_comp_homotopy := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, projection_apply]
    simp_rw [← LinearMap.comp_apply (cycleProjection R), cycleProjection_comp_homotopy]
    exact (aInfinityAlgebra R).cohomologyClass_zero
  homotopy_comp_homotopy := homotopy_comp_homotopy R

/-- The inclusion of the contraction sends a class to the projection of a representative. -/
@[simp]
theorem contraction_incl_cohomologyClass {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    (contraction R).incl ((aInfinityAlgebra R).cohomologyClass hx) = cycleProjection R x :=
  inclusion_cohomologyClass R hx

/-- The projection of the contraction sends `x` to the class of its projection `π x`. -/
theorem contraction_proj_apply (x : ExteriorAlgebra R (Fin 3 → R)) :
    (contraction R).proj x =
      (aInfinityAlgebra R).cohomologyClass (cycleProjection_mem_cycles R x) :=
  projection_apply R x

/-- The projection of the contraction sends a cycle to its class. -/
@[simp]
theorem contraction_proj_of_mem_cycles {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    (contraction R).proj x = (aInfinityAlgebra R).cohomologyClass hx :=
  projection_of_mem_cycles R hx

/-- The homotopy of the contraction is `homotopy`. -/
@[simp]
theorem contraction_homotopy : (contraction R).homotopy = homotopy R := (rfl)

/-- The homotopy of the contraction has degree `-1`. -/
theorem isHomogeneous_contraction_homotopy :
    LinearMap.IsHomogeneous (contraction R).homotopy (aInfinityAlgebra R).grading.piece
      (aInfinityAlgebra R).grading.piece (-1) := by
  rw [contraction_homotopy]
  exact isHomogeneous_homotopy R

/-- The inclusion of the contraction has degree zero. -/
theorem isHomogeneous_contraction_incl :
    LinearMap.IsHomogeneous (contraction R).incl (aInfinityAlgebra R).cohomologyGrading.piece
      (aInfinityAlgebra R).grading.piece 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
  obtain ⟨y, hy, hp, rfl⟩ := (aInfinityAlgebra R).mem_cohomologyGrading_piece_iff.1 hx
  rw [aInfinityAlgebra_grading_piece] at hp ⊢
  rw [contraction_incl_cohomologyClass]
  exact (isHomogeneous_cycleProjection R).map_mem hp

/-- The projection of the contraction has degree zero. -/
theorem isHomogeneous_contraction_proj :
    LinearMap.IsHomogeneous (contraction R).proj (aInfinityAlgebra R).grading.piece
      (aInfinityAlgebra R).cohomologyGrading.piece 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
  rw [contraction_proj_apply]
  refine (aInfinityAlgebra R).cohomologyClass_mem_cohomologyGrading_piece _ ?_
  rw [aInfinityAlgebra_grading_piece] at hx ⊢
  exact (isHomogeneous_cycleProjection R).map_mem hx

/-! ### The transferred minimal model -/

/-- The **transferred minimal model** of `(Λ_R(a, b, c), d)`: the `A∞` structure on its cohomology
obtained by homological transfer along `contraction`. -/
noncomputable def minimalModel : AInfinityAlgebra R (aInfinityAlgebra R).Cohomology :=
  (aInfinityAlgebra R).transfer (contraction R) (isHomogeneous_contraction_homotopy R)
    (isHomogeneous_contraction_incl R) (isHomogeneous_contraction_proj R)

/-- The minimal model is the transfer of `aInfinityAlgebra` along `contraction`. -/
theorem minimalModel_def :
    minimalModel R = (aInfinityAlgebra R).transfer (contraction R)
      (isHomogeneous_contraction_homotopy R) (isHomogeneous_contraction_incl R)
      (isHomogeneous_contraction_proj R) :=
  (rfl)

/-- The **extending `A∞` morphism** from the transferred minimal model to `(Λ_R(a, b, c), d)`,
with linear part the inclusion of the contraction. -/
noncomputable def minimalModelInclusion : AInfinityHom (minimalModel R) (aInfinityAlgebra R) :=
  (aInfinityAlgebra R).transferInclusion (contraction R) (isHomogeneous_contraction_homotopy R)
    (isHomogeneous_contraction_incl R) (isHomogeneous_contraction_proj R)

/-- The components of the extending morphism are those of the transfer inclusion of
`aInfinityAlgebra` along `contraction`. -/
theorem component_minimalModelInclusion (n : ℕ) :
    (minimalModelInclusion R).component n = ((aInfinityAlgebra R).transferInclusion (contraction R)
      (isHomogeneous_contraction_homotopy R) (isHomogeneous_contraction_incl R)
      (isHomogeneous_contraction_proj R)).component n :=
  (rfl)

/-- The transferred structure is minimal. -/
theorem isMinimal_minimalModel : (minimalModel R).IsMinimal :=
  AInfinityAlgebra.isMinimal_transfer _ _ _ _ _ rfl

/-- The extending morphism is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelInclusion : (minimalModelInclusion R).IsQuasiIso :=
  AInfinityAlgebra.isQuasiIso_transferInclusion _ _ _ _ _

/-- The projection of a cycle represents the same class. -/
theorem cohomologyClass_cycleProjection {x : ExteriorAlgebra R (Fin 3 → R)}
    (hx : x ∈ (aInfinityAlgebra R).cycles) :
    (aInfinityAlgebra R).cohomologyClass (cycleProjection_mem_cycles R x) =
      (aInfinityAlgebra R).cohomologyClass hx :=
  (AInfinityAlgebra.cohomologyClass_eq_iff _ _ _).2 (cycleProjection_sub_mem_boundaries R hx)

/-- **The transferred binary operation is the cohomology product.** -/
theorem minimalModel_m_two (x y : (aInfinityAlgebra R).Cohomology) :
    (minimalModel R).m 2 ![x, y] = x * y := by
  obtain ⟨z, hz, rfl⟩ := (aInfinityAlgebra R).exists_cohomologyClass_eq x
  obtain ⟨w, hw, rfl⟩ := (aInfinityAlgebra R).exists_cohomologyClass_eq y
  have hz' := cycleProjection_mem_cycles R z
  have hw' := cycleProjection_mem_cycles R w
  rw [minimalModel_def, AInfinityAlgebra.mul_transfer, contraction_incl_cohomologyClass,
    contraction_incl_cohomologyClass, AInfinityAlgebra.mul_apply,
    contraction_proj_of_mem_cycles R ((aInfinityAlgebra R).m_two_mem_cycles hz' hw'),
    ← cohomologyClass_cycleProjection R hz, ← cohomologyClass_cycleProjection R hw,
    AInfinityAlgebra.cohomology_mul_eq_cohomologyMul,
    AInfinityAlgebra.cohomologyMul_cohomologyClass]

/-! ### The ternary operation on `([a], [a], [b])` -/

/-- The differential sends `c` to `a b`. -/
@[simp]
theorem differential_gen_two : differential R (gen R 2) = gen R 0 * gen R 1 := by
  rw [← monomial_singleton, differential_monomial, monomial_pair R (show (0 : Fin 3) < 1 by decide)]
  simp

/-- The homotopy sends `a b` to `c`. -/
@[simp]
theorem homotopy_gen_zero_mul_gen_one : homotopy R (gen R 0 * gen R 1) = gen R 2 := by
  rw [← monomial_pair R (show (0 : Fin 3) < 1 by decide), homotopy_monomial, monomial_singleton]
  simp

/-- The projection fixes the representatives `a` and `b`. -/
@[simp]
theorem cycleProjection_gen {i : Fin 3} (hi : i ≠ 2) : cycleProjection R (gen R i) = gen R i := by
  rw [← monomial_singleton, cycleProjection_monomial,
    ite_eq_right_iff.2 fun h ↦ absurd h (by revert i; decide)]

/-- The projection fixes the representative `a c`. -/
@[simp]
theorem cycleProjection_gen_zero_mul_gen_two :
    cycleProjection R (gen R 0 * gen R 2) = gen R 0 * gen R 2 := by
  rw [← monomial_pair R (show (0 : Fin 3) < 2 by decide), cycleProjection_monomial]
  simp +decide

/-- The Koszul twist acts on a generator of degree one by `-1`. -/
private theorem koszulTwist_gen (i : Fin 3) :
    (aInfinityAlgebra R).grading.koszulTwist 1 (gen R i) = -gen R i := by
  rw [InternalGrading.koszulTwist_one_apply_of_mem _
    (by rw [aInfinityAlgebra_grading_piece]; exact gen_mem_integerGrading R i)]
  simp

/-- The Koszul twist acts on the class of a generator by `-1`. -/
private theorem koszulTwist_cohomologyClass_gen {i : Fin 3} (hi : i ≠ 2) :
    (aInfinityAlgebra R).cohomologyGrading.koszulTwist 1
        ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R hi)) =
      -(aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R hi) := by
  rw [InternalGrading.koszulTwist_one_apply_of_mem _
    ((aInfinityAlgebra R).cohomologyClass_mem_cohomologyGrading_piece _
      (by rw [aInfinityAlgebra_grading_piece]; exact gen_mem_integerGrading R i))]
  simp

/-- **The transferred ternary operation on `([a], [a], [b])`**: `m₃^H ([a], [a], [b]) = [a c]`.
Of the Kontsevich--Soibelman/Merkulov tree sum only the term
`-p m₂ (i (τ [a]), h m₂ (i [a], i [b]))` survives, with `h (a b) = c` and the Koszul twist
`τ [a] = -[a]`. -/
theorem minimalModel_m_three :
    (minimalModel R).m 3
        ![(aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))] =
      (aInfinityAlgebra R).cohomologyClass (gen_zero_mul_gen_two_mem_cycles R) := by
  rw [minimalModel_def, AInfinityAlgebra.m_three_transfer,
    koszulTwist_cohomologyClass_gen R (i := 0) (by decide)]
  simp [contraction_proj_of_mem_cycles R (gen_zero_mul_gen_two_mem_cycles R)]

/-- The class `[a c]` is nonzero over a nontrivial ring: the inclusion of the contraction sends
it to the basis vector `a c`. -/
theorem cohomologyClass_gen_zero_mul_gen_two_ne_zero [Nontrivial R] :
    (aInfinityAlgebra R).cohomologyClass (gen_zero_mul_gen_two_mem_cycles R) ≠ 0 := by
  intro h
  have h' := congrArg (contraction R).incl h
  rw [contraction_incl_cohomologyClass, cycleProjection_gen_zero_mul_gen_two, map_zero,
    ← monomial_pair R (show (0 : Fin 3) < 2 by decide)] at h'
  exact (Pi.basisFun R (Fin 3)).ExteriorAlgebra.ne_zero _ h'

/-- **The transferred minimal model has a nonzero ternary operation** over a nontrivial ring. -/
theorem minimalModel_m_three_ne_zero [Nontrivial R] :
    (minimalModel R).m 3
        ![(aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))] ≠ 0 := by
  rw [minimalModel_m_three]
  exact cohomologyClass_gen_zero_mul_gen_two_ne_zero R

/-- **The quadratic component of the extending morphism**: `f₂ ([a], [b]) = -h (a b) = -c`. -/
theorem component_two_minimalModelInclusion :
    (minimalModelInclusion R).component 2
        ![(aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))] =
      -gen R 2 := by
  rw [component_minimalModelInclusion, AInfinityAlgebra.component_two_transferInclusion]
  simp

/-- **The transferred ternary operation selects an element of the triple Massey product**
`⟨[a], [a], [b]⟩`: `[a c]` is the value of the defining system `(a, a, b, 0, c)`, since `a a = 0`
and `d c = a b`. -/
theorem minimalModel_m_three_mem_tripleMasseyProduct :
    (minimalModel R).m 3
        ![(aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)),
          (aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))] ∈
      (aInfinityAlgebra R).tripleMasseyProduct
        ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)))
        ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)))
        ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))) := by
  let S : (aInfinityAlgebra R).TripleMasseyDefiningSystem
      ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)))
      ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 0) (by decide)))
      ((aInfinityAlgebra R).cohomologyClass (gen_mem_cycles R (i := 1) (by decide))) :=
    { a := gen R 0
      b := gen R 0
      c := gen R 1
      u := 0
      v := gen R 2
      a_mem_cycles := gen_mem_cycles R (by decide)
      b_mem_cycles := gen_mem_cycles R (by decide)
      c_mem_cycles := gen_mem_cycles R (by decide)
      cohomologyClass_a := rfl
      cohomologyClass_b := rfl
      cohomologyClass_c := rfl
      m_one_u := by simp [gen_mul_self]
      m_one_v := by simp [differential_gen_two] }
  refine AInfinityAlgebra.mem_tripleMasseyProduct.2 ⟨S, ?_⟩
  rw [minimalModel_m_three, AInfinityAlgebra.TripleMasseyDefiningSystem.value_def,
    AInfinityAlgebra.cohomologyClass_eq_iff, AInfinityAlgebra.TripleMasseyDefiningSystem.cycle_def]
  simp [S, koszulTwist_gen]

end TauCeti.HeisenbergDGA
