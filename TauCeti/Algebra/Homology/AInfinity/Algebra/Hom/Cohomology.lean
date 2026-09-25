/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Basic

/-!
# Cohomology of a morphism of A-infinity algebras

The linear part `f₁` of a morphism of `A∞` algebras is a chain map for the unary operations, so it
carries cycles to cycles and boundaries to boundaries and descends to cohomology.  It is *not* a
morphism of algebras at the chain level: the arity-two component equation only says that the
defect `f₁(m₂(a,b)) - m₂(f₁a, f₁b)` is a unary boundary, produced by the arity-two component `f₂`.
On cohomology that defect disappears, so the induced map is a morphism of the nonunital
cohomology algebras.

This is the invariance that makes cohomology usable for `A∞` algebras, and it is what the notion
of a quasi-isomorphism rests on: a morphism whose induced map on cohomology is bijective.

The arity-two component equation is read off the bar-differential equation `b_B F = F b_A` on a
two-letter word, using that a tensor word is determined by its letter component and its
deconcatenation.  Only the suspended arity-two Taylor component of `F` is needed, and it enters
solely through the boundary it produces.

## Main definitions

* `TauCeti.AInfinityHom.cyclesMap`: the linear part restricted to cycles.
* `TauCeti.AInfinityHom.cohomologyMap`: the induced morphism of nonunital cohomology algebras.
* `TauCeti.AInfinityHom.IsQuasiIso`: a morphism inducing a bijection on cohomology.

## Main results

* `TauCeti.AInfinityHom.linearPart_m_two_sub_mem_boundaries`: on cycles the linear part is
  multiplicative up to a boundary.
* `TauCeti.AInfinityHom.cohomologyMap_cohomologyClass`: the induced map sends the class of a cycle
  to the class of its image.
* `TauCeti.AInfinityHom.cohomologyMap_mem_cohomologyGrading_piece`: the induced map preserves the
  grading of cohomology.
* `TauCeti.AInfinityHom.cohomologyMap_id` and `TauCeti.AInfinityHom.cohomologyMap_comp`: passage to
  cohomology preserves identities and composition.
* `TauCeti.AInfinityHom.isQuasiIso_id` and `TauCeti.AInfinityHom.IsQuasiIso.comp`: identities are
  quasi-isomorphisms and quasi-isomorphisms compose.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### The arity-two component equation -/

/-- The suspended arity-two Taylor component of an `A∞` morphism, as a bilinear map.  It is used
only to exhibit the multiplicative defect of the linear part as a boundary. -/
private noncomputable def taylorTwo (f : AInfinityHom AA BB) : A →ₗ[R] A →ₗ[R] B :=
  ((ReducedTensorWords.prepend R A).compr₂ f.taylor).compl₂ (ReducedTensorWords.ofLetter R A)

private theorem taylorTwo_apply (f : AInfinityHom AA BB) (a b : A) :
    f.taylorTwo a b =
      f.taylor (ReducedTensorWords.of R A (2 : ℕ+)
        (PiTensorProduct.tprod R ![a, b])) := by
  rw [taylorTwo, LinearMap.compl₂_apply, LinearMap.compr₂_apply,
    ReducedTensorWords.prepend_ofLetter]

/-- The bar map of an `A∞` morphism on a two-letter word: the two letters are either both kept,
or collapsed by the arity-two component. -/
private theorem barMap_of_two (f : AInfinityHom AA BB) (a b : A) :
    f.barMap (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) =
      ReducedTensorWords.ofLetter R B (f.taylorTwo a b) +
        ReducedTensorWords.of R B (2 : ℕ+)
          (PiTensorProduct.tprod R ![f.linearPart a, f.linearPart b]) := by
  refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
  · rw [f.isCoalgHom_barMap.deconcatenation_apply, ReducedTensorWords.deconcatenation_of_two,
      TensorProduct.map_tmul, barMap_ofLetter, barMap_ofLetter, map_add,
      ReducedTensorWords.deconcatenation_ofLetter, ReducedTensorWords.deconcatenation_of_two,
      zero_add]
  · rw [← LinearMap.comp_apply, ← taylor_def, ← taylorTwo_apply, map_add,
      ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_of_two, add_zero]

/-- The arity-two component equation when the first input is homogeneous: its suspension sign is
the only degree that enters. -/
private theorem taylorTwo_component_eq (f : AInfinityHom AA BB) {p : ℤ} {a b : A}
    (ha : a ∈ AA.grading.piece p) :
    BB.m 1 ![f.taylorTwo a b] + negOnePowCast R p • BB.m 2 ![f.linearPart a, f.linearPart b] =
      f.taylorTwo (AA.m 1 ![a]) b + negOnePowCast R p • f.linearPart (AA.m 2 ![a, b])
        - negOnePowCast R p • f.taylorTwo a (AA.m 1 ![b]) := by
  have h := LinearMap.congr_fun f.taylor_comp_barMap
    (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b]))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barMap_of_two, map_add,
    AInfinityAlgebra.taylor_ofLetter,
    BB.taylor_of_two (f.linearPart a) (f.linearPart b),
    AA.barDifferential_of_two a b] at h
  simp only [map_sub, map_add] at h
  rw [← taylorTwo_apply, ← taylorTwo_apply, ← linearPart_apply] at h
  simp only [BB.grading.koszulTwist_apply_of_mem (f.linearPart_mem ha),
    AA.grading.koszulTwist_apply_of_mem ha, ← negOnePowCast_eq_intCast, one_mul,
    ← AInfinityAlgebra.mul_apply, map_smul, LinearMap.smul_apply] at h
  simpa only [AInfinityAlgebra.mul_apply] using h

/-- The arity-two component equation for arbitrary inputs: the suspension sign of the first letter
is carried by the degree-one Koszul twist. -/
private theorem linearPart_m_two_sub_eq (f : AInfinityHom AA BB) (a b : A) :
    f.linearPart (AA.m 2 ![a, b]) - BB.m 2 ![f.linearPart a, f.linearPart b] =
      BB.m 1 ![f.taylorTwo (AA.grading.koszulTwist 1 a) b]
        - f.taylorTwo (AA.m 1 ![AA.grading.koszulTwist 1 a]) b
        + f.taylorTwo a (AA.m 1 ![b]) := by
  -- Both sides are linear in each argument, so it suffices to check homogeneous letters, where
  -- the Koszul twist is the suspension sign of the first letter.
  have hhom : ∀ (p : ℤ) (x : A), x ∈ AA.grading.piece p → ∀ y : A,
      f.linearPart (AA.m 2 ![x, y]) - BB.m 2 ![f.linearPart x, f.linearPart y] =
        negOnePowCast R p • BB.m 1 ![f.taylorTwo x y]
          - negOnePowCast R p • f.taylorTwo (AA.m 1 ![x]) y
          + f.taylorTwo x (AA.m 1 ![y]) := by
    intro p x hx
    -- With the first argument fixed, both sides are linear in the second.
    let L : A →ₗ[R] B := f.linearPart ∘ₗ AA.mul x - BB.mul (f.linearPart x) ∘ₗ f.linearPart
    let Q : A →ₗ[R] B :=
      negOnePowCast R p • (BB.differential ∘ₗ f.taylorTwo x)
        - negOnePowCast R p • f.taylorTwo (AA.m 1 ![x]) + f.taylorTwo x ∘ₗ AA.differential
    suffices h : L = Q by
      intro y
      simpa [L, Q] using LinearMap.congr_fun h y
    refine AA.grading.linearMap_ext fun q y hy ↦ ?_
    have h := f.taylorTwo_component_eq (b := y) hx
    have h2 : negOnePowCast R p • BB.m 1 ![f.taylorTwo x y]
          + BB.m 2 ![f.linearPart x, f.linearPart y] =
        negOnePowCast R p • f.taylorTwo (AA.m 1 ![x]) y + f.linearPart (AA.m 2 ![x, y])
          - f.taylorTwo x (AA.m 1 ![y]) := by
      have h' := congrArg (fun z : B ↦ negOnePowCast R p • z) h
      simpa only [smul_add, smul_sub, negOnePowCast_smul_negOnePowCast_smul] using h'
    have h3 : f.linearPart (AA.m 2 ![x, y]) =
        negOnePowCast R p • BB.m 1 ![f.taylorTwo x y]
          + BB.m 2 ![f.linearPart x, f.linearPart y]
          - negOnePowCast R p • f.taylorTwo (AA.m 1 ![x]) y + f.taylorTwo x (AA.m 1 ![y]) := by
      rw [h2]
      abel
    simp only [L, Q, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, AInfinityAlgebra.mul_apply, AInfinityAlgebra.differential_apply]
    rw [h3]
    abel
  -- With the first argument homogeneous, the Koszul twist is its suspension sign, so the two
  -- displayed identities agree; both sides are linear in that argument.
  let L : A →ₗ[R] B :=
    f.linearPart ∘ₗ AA.mul.flip b - BB.mul.flip (f.linearPart b) ∘ₗ f.linearPart
  let Q : A →ₗ[R] B :=
    BB.differential ∘ₗ f.taylorTwo.flip b ∘ₗ AA.grading.koszulTwist 1
      - f.taylorTwo.flip b ∘ₗ AA.differential ∘ₗ AA.grading.koszulTwist 1
      + f.taylorTwo.flip (AA.m 1 ![b])
  suffices h : L = Q by simpa [L, Q] using LinearMap.congr_fun h a
  refine AA.grading.linearMap_ext fun p x hx ↦ ?_
  simp only [L, Q, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, AInfinityAlgebra.mul_apply, AInfinityAlgebra.differential_apply,
    AA.grading.koszulTwist_apply_of_mem hx, ← negOnePowCast_eq_intCast, one_mul, map_smul]
  exact hhom p x hx b

/-! ### Cycles, boundaries, and cohomology -/

/-- The linear part of an `A∞` morphism carries cycles to cycles. -/
theorem linearPart_mem_cycles (f : AInfinityHom AA BB) {x : A} (hx : x ∈ AA.cycles) :
    f.linearPart x ∈ BB.cycles := by
  rw [AInfinityAlgebra.mem_cycles] at hx ⊢
  rw [← f.linearPart_m_one, hx, map_zero]

/-- The linear part of an `A∞` morphism carries boundaries to boundaries. -/
theorem linearPart_mem_boundaries (f : AInfinityHom AA BB) {x : A} (hx : x ∈ AA.boundaries) :
    f.linearPart x ∈ BB.boundaries := by
  rw [AInfinityAlgebra.mem_boundaries] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨f.linearPart y, (f.linearPart_m_one y).symm⟩

/-- On cycles the linear part of an `A∞` morphism is multiplicative up to a boundary: the defect
is the unary boundary of the arity-two component. -/
theorem linearPart_m_two_sub_mem_boundaries (f : AInfinityHom AA BB) {a b : A}
    (ha : a ∈ AA.cycles) (hb : b ∈ AA.cycles) :
    f.linearPart (AA.m 2 ![a, b]) - BB.m 2 ![f.linearPart a, f.linearPart b] ∈ BB.boundaries := by
  rw [AInfinityAlgebra.mem_cycles] at ha hb
  have htwist : AA.m 1 ![AA.grading.koszulTwist 1 a] = 0 := by
    rw [AA.m_one_koszulTwist, ha, map_zero, neg_zero]
  rw [f.linearPart_m_two_sub_eq a b, htwist, hb, map_zero, LinearMap.zero_apply, map_zero,
    sub_zero, add_zero]
  exact BB.mem_boundaries.mpr ⟨f.taylorTwo (AA.grading.koszulTwist 1 a) b, rfl⟩

/-- The linear part of an `A∞` morphism, restricted to cycles. -/
noncomputable def cyclesMap (f : AInfinityHom AA BB) : AA.cycles →ₗ[R] BB.cycles :=
  f.linearPart.restrict fun _ hx ↦ f.linearPart_mem_cycles hx

/-- The cycle produced by `cyclesMap` is the linear part of the underlying cycle. -/
@[simp]
theorem coe_cyclesMap (f : AInfinityHom AA BB) (x : AA.cycles) :
    (f.cyclesMap x : B) = f.linearPart x := (rfl)

private theorem boundariesInCycles_le_comap (f : AInfinityHom AA BB) :
    AA.boundariesInCycles ≤ BB.boundariesInCycles.comap f.cyclesMap := by
  intro x hx
  rw [Submodule.mem_comap, AInfinityAlgebra.mem_boundariesInCycles, coe_cyclesMap]
  exact f.linearPart_mem_boundaries ((AA.mem_boundariesInCycles).mp hx)

private theorem mapQ_cohomologyClass (f : AInfinityHom AA BB) {x : A} (hx : x ∈ AA.cycles) :
    Submodule.mapQ AA.boundariesInCycles BB.boundariesInCycles f.cyclesMap
        f.boundariesInCycles_le_comap (AA.cohomologyClass hx) =
      BB.cohomologyClass (f.linearPart_mem_cycles hx) := by
  have hc : f.cyclesMap ⟨x, hx⟩ = ⟨f.linearPart x, f.linearPart_mem_cycles hx⟩ :=
    Subtype.ext (f.coe_cyclesMap ⟨x, hx⟩)
  rw [AA.cohomologyClass_eq_mk, Submodule.mapQ_apply, hc, ← BB.cohomologyClass_eq_mk]

/-- The morphism of nonunital cohomology algebras induced by an `A∞` morphism.  Multiplicativity
is not an identity of the linear part: it holds on cohomology because the arity-two component
makes the defect a boundary. -/
noncomputable def cohomologyMap (f : AInfinityHom AA BB) :
    AA.Cohomology →ₙₐ[R] BB.Cohomology where
  toFun := Submodule.mapQ AA.boundariesInCycles BB.boundariesInCycles f.cyclesMap
    f.boundariesInCycles_le_comap
  map_smul' r x := map_smul _ r x
  map_zero' := map_zero _
  map_add' x y := map_add _ x y
  map_mul' x y := by
    obtain ⟨u, hu, rfl⟩ := AA.exists_cohomologyClass_eq x
    obtain ⟨v, hv, rfl⟩ := AA.exists_cohomologyClass_eq y
    rw [AInfinityAlgebra.cohomology_mul_eq_cohomologyMul, AA.cohomologyMul_cohomologyClass hu hv,
      f.mapQ_cohomologyClass, f.mapQ_cohomologyClass, f.mapQ_cohomologyClass,
      AInfinityAlgebra.cohomology_mul_eq_cohomologyMul, BB.cohomologyMul_cohomologyClass,
      BB.cohomologyClass_eq_iff]
    exact f.linearPart_m_two_sub_mem_boundaries hu hv

/-- The induced map on cohomology sends the class of a cycle to the class of its image. -/
@[simp]
theorem cohomologyMap_cohomologyClass (f : AInfinityHom AA BB) {x : A} (hx : x ∈ AA.cycles) :
    f.cohomologyMap (AA.cohomologyClass hx) =
      BB.cohomologyClass (f.linearPart_mem_cycles hx) :=
  f.mapQ_cohomologyClass hx

/-- The map induced on cohomology by an `A∞` morphism preserves degrees. -/
theorem cohomologyMap_mem_cohomologyGrading_piece (f : AInfinityHom AA BB) {p : ℤ}
    {c : AA.Cohomology} (hc : c ∈ AA.cohomologyGrading.piece p) :
    f.cohomologyMap c ∈ BB.cohomologyGrading.piece p := by
  obtain ⟨x, hx, hxp, rfl⟩ := AA.mem_cohomologyGrading_piece_iff.1 hc
  rw [cohomologyMap_cohomologyClass]
  exact BB.cohomologyClass_mem_cohomologyGrading_piece _ (f.linearPart_mem hxp)

/-- Passage to cohomology sends the identity `A∞` morphism to the identity. -/
@[simp]
theorem cohomologyMap_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
  ext x
  obtain ⟨u, hu, rfl⟩ := AA.exists_cohomologyClass_eq x
  rw [cohomologyMap_cohomologyClass, NonUnitalAlgHom.coe_id, id_eq]
  congr 1
  simp only [linearPart_id, LinearMap.id_apply]

/-- Passage to cohomology preserves composition of `A∞` morphisms. -/
@[simp]
theorem cohomologyMap_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).cohomologyMap = g.cohomologyMap.comp f.cohomologyMap := by
  ext x
  obtain ⟨u, hu, rfl⟩ := AA.exists_cohomologyClass_eq x
  rw [cohomologyMap_cohomologyClass, NonUnitalAlgHom.comp_apply, cohomologyMap_cohomologyClass,
    cohomologyMap_cohomologyClass]
  congr 1
  simp only [linearPart_comp, LinearMap.comp_apply]

/-! ### Quasi-isomorphisms -/

/-- An `A∞` morphism is a quasi-isomorphism when its linear part induces a bijection on
cohomology. -/
def IsQuasiIso (f : AInfinityHom AA BB) : Prop :=
  Function.Bijective f.cohomologyMap

/-- An `A∞` morphism is a quasi-isomorphism exactly when its induced map on cohomology is
bijective. -/
theorem isQuasiIso_iff (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔ Function.Bijective f.cohomologyMap := Iff.rfl

/-- The identity `A∞` morphism is a quasi-isomorphism. -/
@[simp]
theorem isQuasiIso_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsQuasiIso := by
  rw [IsQuasiIso, cohomologyMap_id]
  exact Function.bijective_id

/-- Quasi-isomorphisms of `A∞` algebras are closed under composition. -/
theorem IsQuasiIso.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB} (hg : g.IsQuasiIso)
    (hf : f.IsQuasiIso) : (g.comp f).IsQuasiIso := by
  rw [IsQuasiIso, cohomologyMap_comp, NonUnitalAlgHom.coe_comp]
  exact Function.Bijective.comp hg hf

end AInfinityHom

end TauCeti
