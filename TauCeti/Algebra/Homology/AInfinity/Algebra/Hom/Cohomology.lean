/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology

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
* `NonUnitalAlgHom.cohomologyStrictHom`: a degree-preserving morphism of cohomology
  algebras as a strict morphism of the cohomology `A∞` algebras.
* `TauCeti.AInfinityHom.cohomologyStrictHom`: the induced map as a strict morphism of the
  cohomology `A∞` algebras.
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
* `TauCeti.AInfinityHom.cohomologyStrictHom_id` and
  `TauCeti.AInfinityHom.cohomologyStrictHom_comp`: the same laws for strict cohomology morphisms.
* `TauCeti.AInfinityHom.isQuasiIso_id` and `TauCeti.AInfinityHom.IsQuasiIso.comp`: identities are
  quasi-isomorphisms and quasi-isomorphisms compose.
* `TauCeti.AInfinityHom.IsQuasiIso.cohomologyStrictHomInv`: a quasi-isomorphism induces an inverse
  strict quasi-isomorphism between its cohomology `A∞` algebras.
* `TauCeti.AInfinityHom.IsQuasiIso.isQuasiIso_cohomologyStrictHom`: the forward strict
  cohomology morphism is a quasi-isomorphism too.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped TensorProduct

namespace NonUnitalAlgHom

open TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {B : Type uB} [AddCommGroup B] [Module R B] {𝒜 : AInfinityAlgebra R A}
  {ℬ : AInfinityAlgebra R B}

private def castStrictHom {𝒜 𝒜' : AInfinityAlgebra R A} {ℬ ℬ' : AInfinityAlgebra R B}
    (h𝒜 : 𝒜 = 𝒜') (hℬ : ℬ = ℬ') (f : AInfinityStrictHom 𝒜' ℬ') :
    AInfinityStrictHom 𝒜 ℬ := by
  cases h𝒜
  cases hℬ
  exact f

private theorem coe_castStrictHom {𝒜 𝒜' : AInfinityAlgebra R A}
    {ℬ ℬ' : AInfinityAlgebra R B} (h𝒜 : 𝒜 = 𝒜') (hℬ : ℬ = ℬ')
    (f : AInfinityStrictHom 𝒜' ℬ') : ⇑(castStrictHom h𝒜 hℬ f) = f := by
  cases h𝒜
  cases hℬ
  rfl

/-- A degree-preserving morphism between cohomology algebras is a strict morphism between the
corresponding cohomology `A∞` algebras. -/
noncomputable def cohomologyStrictHom (φ : 𝒜.Cohomology →ₙₐ[R] ℬ.Cohomology)
    (hφ : ∀ {p : ℤ} {c : 𝒜.Cohomology}, c ∈ 𝒜.cohomologyGrading.piece p →
      φ c ∈ ℬ.cohomologyGrading.piece p) :
    AInfinityStrictHom 𝒜.cohomologyAInfinityAlgebra ℬ.cohomologyAInfinityAlgebra :=
  castStrictHom 𝒜.cohomologyAInfinityAlgebra_eq_toAInfinityAlgebra
    ℬ.cohomologyAInfinityAlgebra_eq_toAInfinityAlgebra
    (NonUnitalDGAlgHom.toAInfinityStrictHom
      (hA := isNonUnitalDGAlgebra_zero 𝒜.cohomologyGrading.piece)
      (hB := isNonUnitalDGAlgebra_zero ℬ.cohomologyGrading.piece)
      { toNonUnitalAlgHom := φ
        map_mem' := hφ
        map_d' := fun _ ↦ by simp only [LinearMap.zero_apply, map_zero] })

/-- The strict morphism of cohomology `A∞` algebras induced by `φ` is `φ` itself. -/
@[simp]
theorem coe_cohomologyStrictHom (φ : 𝒜.Cohomology →ₙₐ[R] ℬ.Cohomology) (hφ) :
    ⇑(φ.cohomologyStrictHom hφ) = φ := by
  simp only [cohomologyStrictHom, coe_castStrictHom,
    NonUnitalDGAlgHom.coe_toAInfinityStrictHom]
  rfl

end NonUnitalAlgHom

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

/-- The map induced on cohomology by an `A∞` morphism, as a strict morphism of the cohomology `A∞`
algebras. -/
noncomputable def cohomologyStrictHom (f : AInfinityHom AA BB) :
    AInfinityStrictHom AA.cohomologyAInfinityAlgebra BB.cohomologyAInfinityAlgebra :=
  f.cohomologyMap.cohomologyStrictHom f.cohomologyMap_mem_cohomologyGrading_piece

/-- The strict morphism of cohomology `A∞` algebras induced by `f` is the map induced on
cohomology. -/
@[simp]
theorem coe_cohomologyStrictHom (f : AInfinityHom AA BB) :
    ⇑f.cohomologyStrictHom = f.cohomologyMap :=
  NonUnitalAlgHom.coe_cohomologyStrictHom _ _

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

/-- Passage to cohomology sends the identity to the identity strict morphism. -/
@[simp]
theorem cohomologyStrictHom_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).cohomologyStrictHom =
      AInfinityStrictHom.id AA.cohomologyAInfinityAlgebra := by
  ext c
  simp only [coe_cohomologyStrictHom, cohomologyMap_id, NonUnitalAlgHom.coe_id,
    AInfinityStrictHom.id_apply, id_eq]

/-- Passage to cohomology preserves composition as strict morphisms. -/
@[simp]
theorem cohomologyStrictHom_comp (g : AInfinityHom BB CC) (f : AInfinityHom AA BB) :
    (g.comp f).cohomologyStrictHom = g.cohomologyStrictHom.comp f.cohomologyStrictHom := by
  ext c
  simp only [coe_cohomologyStrictHom, cohomologyMap_comp, NonUnitalAlgHom.comp_apply,
    AInfinityStrictHom.comp_apply]

/-! ### Quasi-isomorphisms -/

/-- An `A∞` morphism is a quasi-isomorphism when its linear part induces a bijection on
cohomology. -/
def IsQuasiIso (f : AInfinityHom AA BB) : Prop :=
  Function.Bijective f.cohomologyMap

/-- An `A∞` morphism is a quasi-isomorphism exactly when its induced map on cohomology is
bijective. -/
theorem isQuasiIso_def (f : AInfinityHom AA BB) :
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

namespace IsQuasiIso

/-! ### The inverse map between cohomology algebras -/

/-- The map induced on cohomology by a quasi-isomorphism, as a linear equivalence. -/
noncomputable def cohomologyLinearEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AA.Cohomology ≃ₗ[R] BB.Cohomology :=
  LinearEquiv.ofBijective (f.cohomologyMap : AA.Cohomology →ₗ[R] BB.Cohomology)
    ((isQuasiIso_def f).1 hf)

/-- The cohomology linear equivalence agrees with the map induced by the morphism. -/
@[simp]
theorem cohomologyLinearEquiv_apply {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    (c : AA.Cohomology) : hf.cohomologyLinearEquiv c = f.cohomologyMap c := by
  exact LinearEquiv.ofBijective_apply _ c

/-- The inverse of the map induced on cohomology by a quasi-isomorphism, as a morphism of
cohomology algebras. -/
noncomputable def cohomologyMapInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.Cohomology →ₙₐ[R] AA.Cohomology :=
  f.cohomologyMap.inverse hf.cohomologyLinearEquiv.symm
    (fun x ↦ by
      rw [← hf.cohomologyLinearEquiv_apply x]
      exact hf.cohomologyLinearEquiv.symm_apply_apply x)
    (fun x ↦ by
      rw [← hf.cohomologyLinearEquiv_apply (hf.cohomologyLinearEquiv.symm x)]
      exact hf.cohomologyLinearEquiv.apply_symm_apply x)

/-- The inverse cohomology algebra map is the inverse linear equivalence. -/
@[simp]
theorem cohomologyMapInv_apply {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    (c : BB.Cohomology) : hf.cohomologyMapInv c = hf.cohomologyLinearEquiv.symm c := by
  simp only [cohomologyMapInv, NonUnitalAlgHom.coe_inverse]

/-- The inverse cohomology algebra map is a left inverse to the cohomology map. -/
@[simp]
theorem cohomologyMapInv_comp_cohomologyMap {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.cohomologyMapInv.comp f.cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
  ext c
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq,
    cohomologyMapInv_apply]
  rw [← hf.cohomologyLinearEquiv_apply c]
  exact hf.cohomologyLinearEquiv.symm_apply_apply c

/-- The cohomology map is a left inverse to its inverse cohomology algebra map. -/
@[simp]
theorem cohomologyMap_comp_cohomologyMapInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.cohomologyMap.comp hf.cohomologyMapInv = NonUnitalAlgHom.id R BB.Cohomology := by
  ext c
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq,
    cohomologyMapInv_apply]
  rw [← hf.cohomologyLinearEquiv_apply (hf.cohomologyLinearEquiv.symm c)]
  exact hf.cohomologyLinearEquiv.apply_symm_apply c

/-- The inverse of the map induced on cohomology by a quasi-isomorphism preserves degrees. -/
theorem cohomologyMapInv_mem_cohomologyGrading_piece {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) {p : ℤ}
    {c : BB.Cohomology} (hc : c ∈ BB.cohomologyGrading.piece p) :
    hf.cohomologyMapInv c ∈ AA.cohomologyGrading.piece p := by
  have he : LinearMap.IsHomogeneous hf.cohomologyLinearEquiv.toLinearMap
      AA.cohomologyGrading.piece BB.cohomologyGrading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    rw [add_zero, LinearEquiv.coe_coe, cohomologyLinearEquiv_apply]
    exact f.cohomologyMap_mem_cohomologyGrading_piece hx
  simpa only [cohomologyMapInv_apply, add_zero, LinearEquiv.coe_coe] using
    he.linearEquiv_symm.map_mem hc

/-- A quasi-isomorphism `AA ⟶ BB` identifies the cohomology `A∞` algebras; this is the strict
morphism in the backward direction, inverse to the map induced on cohomology. -/
noncomputable def cohomologyStrictHomInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityStrictHom BB.cohomologyAInfinityAlgebra AA.cohomologyAInfinityAlgebra :=
  hf.cohomologyMapInv.cohomologyStrictHom hf.cohomologyMapInv_mem_cohomologyGrading_piece

/-- The inverse strict morphism acts by the inverse cohomology map. -/
@[simp]
theorem coe_cohomologyStrictHomInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    ⇑hf.cohomologyStrictHomInv = hf.cohomologyMapInv :=
  NonUnitalAlgHom.coe_cohomologyStrictHom _ _

/-- The inverse strict cohomology morphism is a left inverse to the induced strict morphism. -/
@[simp]
theorem cohomologyStrictHomInv_comp_cohomologyStrictHom {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    hf.cohomologyStrictHomInv.comp f.cohomologyStrictHom =
      AInfinityStrictHom.id AA.cohomologyAInfinityAlgebra := by
  ext c
  simpa only [AInfinityStrictHom.comp_apply, AInfinityStrictHom.id_apply,
    coe_cohomologyStrictHomInv, coe_cohomologyStrictHom, NonUnitalAlgHom.comp_apply,
    NonUnitalAlgHom.coe_id, id_eq] using
    DFunLike.congr_fun (hf.cohomologyMapInv_comp_cohomologyMap) c

/-- The induced strict cohomology morphism is a left inverse to its inverse. -/
@[simp]
theorem cohomologyStrictHom_comp_cohomologyStrictHomInv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    f.cohomologyStrictHom.comp hf.cohomologyStrictHomInv =
      AInfinityStrictHom.id BB.cohomologyAInfinityAlgebra := by
  ext c
  simpa only [AInfinityStrictHom.comp_apply, AInfinityStrictHom.id_apply,
    coe_cohomologyStrictHom, coe_cohomologyStrictHomInv, NonUnitalAlgHom.comp_apply,
    NonUnitalAlgHom.coe_id, id_eq] using
    DFunLike.congr_fun (hf.cohomologyMap_comp_cohomologyMapInv) c

/-- The class map of a cohomology `A∞` algebra is bijective, since its unary operation is zero. -/
private theorem cohomologyModelClass_bijective (AA : AInfinityAlgebra R A) :
    Function.Bijective (fun x : AA.Cohomology =>
      AA.cohomologyAInfinityAlgebra.cohomologyClass (x := x) (by
        simp only [AInfinityAlgebra.mem_cycles, AA.cohomologyAInfinityAlgebra_m_one_apply])) := by
  have hcycles : AA.cohomologyAInfinityAlgebra.cycles = ⊤ := by
    ext x
    simp only [Submodule.mem_top, AInfinityAlgebra.mem_cycles,
      AA.cohomologyAInfinityAlgebra_m_one_apply]
  let e := AA.cohomologyAInfinityAlgebra.cohomologyEquivOfCyclesEqTop hcycles
  have hx (x : AA.Cohomology) : x ∈ AA.cohomologyAInfinityAlgebra.cycles := by
    simp only [AInfinityAlgebra.mem_cycles, AA.cohomologyAInfinityAlgebra_m_one_apply]
  have heq : (fun x : AA.Cohomology =>
      AA.cohomologyAInfinityAlgebra.cohomologyClass (hx x)) =
      ⇑e := by
    funext x
    exact (AA.cohomologyAInfinityAlgebra.cohomologyEquivOfCyclesEqTop_apply
      hcycles x (hx x)).symm
  rw [heq]
  exact e.bijective

/-- A strict map between cohomology models is a quasi-isomorphism when its underlying map is
bijective. -/
private theorem isQuasiIso_cohomologyModelStrictHom
    (g : AInfinityStrictHom AA.cohomologyAInfinityAlgebra
      BB.cohomologyAInfinityAlgebra) (hg : Function.Bijective g) :
    g.toAInfinityHom.IsQuasiIso := by
  let eA : AA.Cohomology → AA.cohomologyAInfinityAlgebra.Cohomology :=
    fun x => AA.cohomologyAInfinityAlgebra.cohomologyClass (x := x) (by
      simp only [AInfinityAlgebra.mem_cycles, AA.cohomologyAInfinityAlgebra_m_one_apply])
  let eB : BB.Cohomology → BB.cohomologyAInfinityAlgebra.Cohomology :=
    fun x => BB.cohomologyAInfinityAlgebra.cohomologyClass (x := x) (by
      simp only [AInfinityAlgebra.mem_cycles, BB.cohomologyAInfinityAlgebra_m_one_apply])
  have hA : Function.Bijective eA := cohomologyModelClass_bijective AA
  have hB : Function.Bijective eB := cohomologyModelClass_bijective BB
  have hcomm : ⇑g.toAInfinityHom.cohomologyMap ∘ eA = eB ∘ ⇑g := by
    funext x
    simp only [Function.comp_apply, eA, eB, cohomologyMap_cohomologyClass]
    congr 1
    simp only [AInfinityStrictHom.linearPart_toAInfinityHom,
      AInfinityStrictHom.coe_toLinearMap]
  apply (Function.Bijective.of_comp_iff _ hA).1
  rw [hcomm]
  exact hB.comp hg

/-- The inverse strict morphism between cohomology `A∞` algebras is a quasi-isomorphism. -/
theorem isQuasiIso_cohomologyStrictHomInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.cohomologyStrictHomInv.toAInfinityHom.IsQuasiIso := by
  have heq : (⇑hf.cohomologyMapInv : BB.Cohomology → AA.Cohomology) =
      ⇑hf.cohomologyLinearEquiv.symm := by
    funext x
    exact hf.cohomologyMapInv_apply x
  apply isQuasiIso_cohomologyModelStrictHom hf.cohomologyStrictHomInv
  simpa only [coe_cohomologyStrictHomInv, heq] using
    hf.cohomologyLinearEquiv.symm.bijective

/-- The strict morphism induced on cohomology by a quasi-isomorphism is itself a
quasi-isomorphism. -/
theorem isQuasiIso_cohomologyStrictHom {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.cohomologyStrictHom.toAInfinityHom.IsQuasiIso :=
  isQuasiIso_cohomologyModelStrictHom f.cohomologyStrictHom (by
    simpa only [coe_cohomologyStrictHom] using
      (isQuasiIso_def f).1 hf)

end IsQuasiIso

end AInfinityHom

end TauCeti
