/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MixedBasis.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.OrderedCoproduct
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.BaseChange
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Structure
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The coalgebra of a mixed Kostant lattice

The integral span of the mixed ordered PBW basis is a coalgebra, for any finite rational
Lie basis and any choice of binomial coordinates. This does not require the lattice to be
closed under multiplication. Its coproduct splits every exponent with coefficient one,
and its counit selects the constant monomial.

We realize the lattice inside the generated Kostant form, use the ordered coproduct formula
`TauCeti.UniversalEnvelopingAlgebra.kostantFormComul_prod_ofFn_generator` to make its image a
subcoalgebra, and transport `TauCeti.Subcoalgebra.coalgebra` back with
`LinearEquiv.coalgebra`. Rational scalar extension recovers the enveloping coalgebra via the
native `TauCeti.UniversalEnvelopingAlgebra.kostantFormBaseChange` and the rational mixed basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace Module.Basis

open TauCeti TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

attribute [local instance] TauCeti.moduleNNRat

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {n : ℕ}
variable (b : Basis (Fin n) ℚ L) (c : Finset (Fin n))

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "K" => kostantForm (fun i : {i // i ∉ c} => b i)
  (fun i : {i // i ∈ c} => b i)
local notation "W" => b.pbwKostantLattice c
local notation "B" => b.pbwKostantLatticeBasis c

private theorem lattice_mem_kostantForm {x : U} (hx : x ∈ W) : x ∈ K := by
  rw [pbwKostantLattice_def] at hx
  exact (Submodule.span_le.mpr (by
    rintro _ ⟨a, rfl⟩
    exact b.pbwKostantBasis_mem_kostantForm c a) :
      Submodule.span ℤ (Set.range (b.pbwKostantBasis c)) ≤ (subalgebraOfSubring K).toSubmodule) hx

private noncomputable def latticeInclusion : W →ₗ[ℤ] K :=
  { toFun := fun x => ⟨x, lattice_mem_kostantForm b c x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private theorem latticeInclusion_injective : Function.Injective (latticeInclusion b c) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : K => (z : U)) h)

private noncomputable def mixedIndex (i : Fin n) : {i // i ∉ c} ⊕ {i // i ∈ c} :=
  if hi : i ∈ c then .inr ⟨i, hi⟩ else .inl ⟨i, hi⟩

private theorem latticeInclusion_basis_prod (a : Fin n → ℕ) :
    latticeInclusion b c (B a) =
      (List.ofFn fun i => kostantGenerator (fun j : {i // i ∉ c} => b j)
        (fun j : {i // i ∈ c} => b j) (mixedIndex c i) (a i)).prod := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_ofFn]
  dsimp only [latticeInclusion, LinearMap.coe_mk, AddHom.coe_mk]
  rw [coe_pbwKostantLatticeBasis, pbwKostantBasis_apply]
  congr 2
  funext i
  by_cases hi : i ∈ c <;> simp [mixedIndex, hi]

private theorem comul_latticeInclusion_basis (a : Fin n → ℕ) :
    Coalgebra.comul (R := ℤ) (latticeInclusion b c (B a)) =
      ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
        latticeInclusion b c (B (fun i => (p i).1)) ⊗ₜ[ℤ]
          latticeInclusion b c (B (fun i => (p i).2)) := by
  simp_rw [latticeInclusion_basis_prod]
  exact kostantFormComul_prod_ofFn_generator _ _ (mixedIndex c) a

private noncomputable def latticeSubcoalgebra : TauCeti.Subcoalgebra ℤ K :=
  TauCeti.Subcoalgebra.ofSubmodule (LinearMap.range (latticeInclusion b c)) (by
    rintro _ ⟨x, rfl⟩
    let P := LinearMap.range (TensorProduct.map
      (LinearMap.range (latticeInclusion b c)).subtype
      (LinearMap.range (latticeInclusion b c)).subtype)
    have h : ⊤ ≤ P.comap ((Coalgebra.comul (R := ℤ)) ∘ₗ latticeInclusion b c) := by
      rw [← (B).span_eq, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply]
      rw [comul_latticeInclusion_basis]
      apply Submodule.sum_mem
      intro p _
      exact ⟨⟨latticeInclusion b c (B (fun i => (p i).1)), ⟨_, rfl⟩⟩ ⊗ₜ[ℤ]
        ⟨latticeInclusion b c (B (fun i => (p i).2)), ⟨_, rfl⟩⟩, rfl⟩
    exact h (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ W)))

private noncomputable def latticeRangeEquiv : W ≃ₗ[ℤ] (latticeSubcoalgebra b c).toSubmodule :=
  LinearEquiv.ofInjective (latticeInclusion b c) (latticeInclusion_injective b c)

private noncomputable instance kostantFlat : Module.Flat ℤ K := by
  let : HasUniqueDiv U := .of_module_rat U
  let : HasUniqueDiv K := Function.Injective.hasUniqueDiv (K).subtype.toAddMonoidHom
    (K).subtype_injective
  infer_instance

private noncomputable instance latticeRangeFlat :
    Module.Flat ℤ (latticeSubcoalgebra b c).toSubmodule := by
  let : Module.Free ℤ W := Module.Free.of_basis B
  exact Module.Flat.of_linearEquiv (latticeRangeEquiv b c).symm

private noncomputable instance latticeRangeCoalgebra :
    Coalgebra ℤ (latticeSubcoalgebra b c).toSubmodule :=
  (latticeSubcoalgebra b c).coalgebra

/-- The mixed Kostant lattice inherits its integral coalgebra from the generated Kostant form.
No closure under multiplication is assumed. -/
@[instance_reducible]
noncomputable def pbwKostantLatticeCoalgebra : Coalgebra ℤ W :=
  (latticeRangeEquiv b c).coalgebra ℤ

-- Register the structure without exposing its auxiliary image and transport definitions.
attribute [instance] pbwKostantLatticeCoalgebra

private theorem map_latticeInclusion_comul (x : W) :
    TensorProduct.map (latticeInclusion b c) (latticeInclusion b c)
        (Coalgebra.comul (R := ℤ) (A := W) x) =
      Coalgebra.comul (R := ℤ) (latticeInclusion b c x) := by
  have hcomp : (latticeInclusion b c) ∘ₗ (latticeRangeEquiv b c).symm.toLinearMap =
      (latticeSubcoalgebra b c).toSubmodule.subtype := by
    apply LinearMap.ext
    intro y
    exact LinearEquiv.ofInjective_symm_apply _ y
  unfold pbwKostantLatticeCoalgebra
  dsimp +instances only [LinearEquiv.coalgebra,
    LinearEquiv.coalgebraStruct, latticeRangeCoalgebra,
    LinearMap.comp_apply]
  rw [TauCeti.Subcoalgebra.comul_apply]
  rw [TensorProduct.map_map, hcomp]
  exact (latticeSubcoalgebra b c).map_subtype_comulLinearMap (latticeRangeEquiv b c x)

/-- The canonical injective coalgebra map from the mixed lattice into its generated Kostant
form. -/
noncomputable def pbwKostantLatticeToKostantForm : W →ₗc[ℤ] K where
  toLinearMap := latticeInclusion b c
  counit_comp := by
    unfold pbwKostantLatticeCoalgebra
    dsimp +instances [LinearEquiv.coalgebra, LinearEquiv.coalgebraStruct,
      latticeRangeCoalgebra]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TauCeti.Subcoalgebra.counit_apply]
    rfl
  map_comp_comul := LinearMap.ext (map_latticeInclusion_comul b c)

/-- The integral coalgebra inclusion preserves the underlying enveloping-algebra element. -/
@[simp]
theorem coe_pbwKostantLatticeToKostantForm (x : W) :
    (b.pbwKostantLatticeToKostantForm c x : U) = (x : U) :=
  (rfl)

/-- The mixed lattice embeds in the generated Kostant form. -/
theorem pbwKostantLatticeToKostantForm_injective :
    Function.Injective (b.pbwKostantLatticeToKostantForm c) :=
  latticeInclusion_injective b c

/-- The integral coproduct of a mixed PBW monomial splits every coordinate independently,
with coefficient one and the same coordinate order in each leg. -/
theorem comul_pbwKostantLatticeBasis (a : Fin n → ℕ) :
    Coalgebra.comul (R := ℤ) (A := W) (B a) =
      ∑ p ∈ Fintype.piFinset (fun i => Finset.antidiagonal (a i)),
        B (fun i => (p i).1) ⊗ₜ[ℤ] B (fun i => (p i).2) := by
  let : Module.Free ℤ W := Module.Free.of_basis B
  apply TensorProduct.map_injective_of_flat_flat (latticeInclusion b c) (latticeInclusion b c)
    (latticeInclusion_injective b c) (latticeInclusion_injective b c)
  rw [map_latticeInclusion_comul, comul_latticeInclusion_basis]
  simp

/-- In tensor-basis coordinates, the mixed PBW coproduct has coefficient one precisely on
pairs of exponent vectors adding to the input exponent. -/
@[simp]
theorem pbwKostantLatticeBasis_tensorProduct_repr_comul
    (a u v : Fin n → ℕ) :
    ((B).tensorProduct (B)).repr (Coalgebra.comul (R := ℤ) (B a)) (u, v) =
      if u + v = a then 1 else 0 := by
  classical
  rw [comul_pbwKostantLatticeBasis, map_sum, Finset.sum_apply']
  have hsplit (p : Fin n → ℕ × ℕ) :
      (fun i => (p i).1, fun i => (p i).2) = (u, v) ↔ p = fun i => (u i, v i) := by
    simp only [funext_iff, Prod.ext_iff, forall_and]
  simp only [← Basis.tensorProduct_apply, Basis.repr_self, Finsupp.single_apply]
  simp_rw [hsplit]
  simp only [Finset.sum_ite_eq']
  simp only [Fintype.mem_piFinset, Finset.mem_antidiagonal, funext_iff, Pi.add_apply]

/-- The integral counit becomes the enveloping-algebra counit after rational inclusion. -/
@[simp, norm_cast]
theorem intCast_counit_pbwKostantLattice (x : W) :
    (Coalgebra.counit (R := ℤ) x : ℚ) = Coalgebra.counit (R := ℚ) (x : U) := by
  rw [← CoalgHomClass.counit_comp_apply (b.pbwKostantLatticeToKostantForm c) x]
  exact intCast_kostantFormCounit_apply _ _ _

/-- The counit of a mixed integral PBW monomial is one at the zero exponent and zero elsewhere.
In particular this includes the empty Lie basis. -/
@[simp]
theorem counit_pbwKostantLatticeBasis (a : Fin n → ℕ) :
    Coalgebra.counit (R := ℤ) (B a) = if a = 0 then 1 else 0 := by
  classical
  apply Int.cast_injective (α := ℚ)
  rw [intCast_counit_pbwKostantLattice, coe_pbwKostantLatticeBasis]
  have hf (i : Fin n) : (Bialgebra.counitAlgHom ℚ U)
      (if i ∈ c then Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (b i)) (a i)
        else TauCeti.Associative.dividedPower (a i)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (b i))) = if a i = 0 then 1 else 0 := by
    by_cases hi : i ∈ c <;> cases a i <;> simp [hi]
  rw [pbwKostantBasis_apply, ← Bialgebra.counitAlgHom_apply, map_list_prod, List.map_ofFn]
  simp_rw [Function.comp_def, hf]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte, Int.cast_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact List.prod_eq_zero (List.mem_ofFn.mpr ⟨i, ite_eq_right hi⟩)

private theorem mixed_lieSpan_eq_top :
    LieSubalgebra.lieSpan ℚ L
      (Set.range (fun i : {i // i ∉ c} => b i) ∪
        Set.range (fun i : {i // i ∈ c} => b i)) = ⊤ := by
  apply LieSubalgebra.toSubmodule_injective
  apply top_unique
  rw [← b.span_eq]
  apply le_trans _ LieSubalgebra.submodule_span_le_lieSpan
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  by_cases hi : i ∈ c
  · exact Or.inr ⟨⟨i, hi⟩, rfl⟩
  · exact Or.inl ⟨⟨i, hi⟩, rfl⟩

private noncomputable def rationalLatticeMap : ℚ ⊗[ℤ] W →ₗc[ℚ] U :=
  (CoalgHom.ofClass (kostantFormBaseChange _ _ (mixed_lieSpan_eq_top b c))).comp
    (Coalgebra.TensorProduct.map (CoalgHom.id ℚ ℚ) (b.pbwKostantLatticeToKostantForm c))

private theorem rationalLatticeMap_tmul (q : ℚ) (x : W) :
    rationalLatticeMap b c (q ⊗ₜ[ℤ] x) = q • (x : U) := by
  simp [rationalLatticeMap]

private theorem rationalLatticeMap_bijective : Function.Bijective (rationalLatticeMap b c) := by
  let e := ((B).baseChange ℚ).equiv (b.pbwKostantBasis c) (Equiv.refl _)
  have he : (rationalLatticeMap b c).toLinearMap = e.toLinearMap := by
    apply ((B).baseChange ℚ).ext
    intro a
    rw [Basis.baseChange_apply]
    simp only [CoalgHom.toLinearMap_eq_ofClass, LinearMap.coe_ofClass, rationalLatticeMap_tmul,
      coe_pbwKostantLatticeBasis, one_smul]
    simpa only [e, Basis.baseChange_apply, Equiv.refl_apply, LinearEquiv.coe_coe] using
      (Basis.equiv_apply (b := (B).baseChange ℚ) (b' := b.pbwKostantBasis c)
        (e := Equiv.refl _) a).symm
  have hfun := congrArg (fun f : ℚ ⊗[ℤ] W →ₗ[ℚ] U => ⇑f) he
  exact hfun ▸ e.bijective

/-- Rational scalar extension of the mixed integral lattice recovers the enveloping coalgebra.
The comparison is the scalar multiplication map, independently of any integral straightening. -/
noncomputable def pbwKostantLatticeBaseChange : ℚ ⊗[ℤ] W ≃ₗc[ℚ] U :=
  CoalgEquiv.ofBijective (rationalLatticeMap_bijective b c)

/-- The rational coalgebra comparison sends `q ⊗ w` to `q • w`. -/
@[simp]
theorem pbwKostantLatticeBaseChange_tmul (q : ℚ) (x : W) :
    b.pbwKostantLatticeBaseChange c (q ⊗ₜ[ℤ] x) = q • (x : U) :=
  rationalLatticeMap_tmul b c q x

end Module.Basis
