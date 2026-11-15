/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.CategoryTheory.Semisimple.DualBasis

/-!
# Split simple families

Let `R` be a commutative semiring and `C` an `R`-linear preadditive category with finite
biproducts. A family `S : ι → C` is a **split simple family** (`TauCeti.IsSplitSimpleFamily`)
when

* every `S i` has scalar endomorphisms: `algebraMap R (End (S i))` is bijective;
* the family is hom-orthogonal: there are no nonzero morphisms `S i ⟶ S j` for `i ≠ j`;
* every object of `C` is isomorphic to a finite biproduct `⨁ (S ∘ f)` of members.

No finiteness of `ι`, no abelian structure and no field are assumed. This is the setting in which
a semisimple category is described by finite linear-algebraic data over `R`: in such a category
the morphism modules `S i ⟶ X` and `X ⟶ S i` are free of finite rank, and the composition
pairing between them is perfect. Concretely, every basis `b` of `S i ⟶ X` has a dual basis
`hS.homDual b` of `X ⟶ S i`, characterized by `b j ≫ hS.homDual b k = if j = k then 𝟙 else 0`,
and these dual bases satisfy the **completeness relation** `∑ i ∈ s, ∑ j, c i j ≫ b i j = 𝟙 X`
for any finite set of indices `s` outside of which `X` receives no nonzero morphisms.

Over an algebraically closed field, the chosen representatives of the simple classes of a finite
semisimple abelian category with finite-dimensional endomorphisms of simples form a split simple
family (`TauCeti.isSplitSimpleFamily_simpleClasses`), and the dual bases agree with the dual
bases `Module.Basis.homDual` of the composition pairing given by Schur's lemma
(`TauCeti.IsSplitSimpleFamily.homDual_eq_homDual`). Over a general commutative ring, the
categories presented by fusion multiplicities and F-matrices are the motivating examples: there
the simples are split, but the category is not abelian (over `ℤ`, multiplication by `2` on a
simple object is a monomorphism and an epimorphism but not an isomorphism).

## Main declarations

* `TauCeti.IsSplitSimpleFamily`: the hypothesis on `S`.
* `TauCeti.IsSplitSimpleFamily.hom_ext`: a morphism out of any object is determined by its
  composites with the morphisms from the members.
* `TauCeti.IsSplitSimpleFamily.free_hom`, `TauCeti.IsSplitSimpleFamily.finite_hom`,
  `TauCeti.IsSplitSimpleFamily.free_hom'`, `TauCeti.IsSplitSimpleFamily.finite_hom'`: the
  modules `S i ⟶ X` and `X ⟶ S i` are free of finite rank.
* `TauCeti.IsSplitSimpleFamily.homDual`: the basis of `X ⟶ S i` dual to a basis of `S i ⟶ X`,
  characterized by `TauCeti.IsSplitSimpleFamily.apply_comp_homDual` and
  `TauCeti.IsSplitSimpleFamily.eq_homDual_iff`, with coordinates computed by
  `TauCeti.IsSplitSimpleFamily.comp_homDual` and
  `TauCeti.IsSplitSimpleFamily.homDual_repr_smul_id`.
* `TauCeti.IsSplitSimpleFamily.sum_sum_comp_eq_id`: the completeness relation.
* `TauCeti.isSplitSimpleFamily_simpleClasses`: the field case.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §1.8 for the
  field case
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Module

universe w v u

namespace TauCeti

/-- A **split simple family** `S : ι → C` in an `R`-linear category with finite biproducts: each
`S i` has endomorphisms `R`, the family is hom-orthogonal, and every object is isomorphic to a
finite biproduct of members of the family. No finiteness of `ι` is assumed. -/
structure IsSplitSimpleFamily (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] [HasFiniteBiproducts C] {ι : Type*} (S : ι → C) : Prop where
  /-- Every member has scalar endomorphisms: `algebraMap R (End (S i))` is bijective. -/
  bijective_algebraMap : ∀ i, Function.Bijective (algebraMap R (End (S i)))
  /-- There are no nonzero morphisms between distinct members. -/
  homOrthogonal : HomOrthogonal S
  /-- Every object is isomorphic to a finite biproduct of members. -/
  exists_iso_biproduct : ∀ X : C, ∃ (κ : Type) (_ : Fintype κ) (f : κ → ι),
    Nonempty (X ≅ ⨁ (S ∘ f))

namespace IsSplitSimpleFamily

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasFiniteBiproducts C] {ι : Type*} {S : ι → C} (hS : IsSplitSimpleFamily R S)
include hS

section Scalars

/-- Every endomorphism of a member is a scalar multiple of the identity. -/
theorem exists_eq_smul_id {i : ι} (g : S i ⟶ S i) : ∃ r : R, g = r • 𝟙 (S i) := by
  obtain ⟨r, hr⟩ := (hS.bijective_algebraMap i).2 (End.of g)
  exact ⟨r, by rw [← End.algebraMap_asHom, hr]⟩

/-- Scalar multiples of the identity of a member are equal only for equal scalars. -/
theorem smul_id_inj {i : ι} {r s : R} : r • 𝟙 (S i) = s • 𝟙 (S i) ↔ r = s := by
  refine ⟨fun h ↦ (hS.bijective_algebraMap i).1 (End.ext ?_), fun h ↦ h ▸ rfl⟩
  rwa [End.algebraMap_asHom, End.algebraMap_asHom]

end Scalars

/-- A morphism out of any object is determined by its composites with the morphisms from the
members of a split simple family. -/
theorem hom_ext {X Y : C} {u v : X ⟶ Y} (h : ∀ i (g : S i ⟶ X), g ≫ u = g ≫ v) : u = v := by
  obtain ⟨κ, _, f, ⟨e⟩⟩ := hS.exists_iso_biproduct X
  rw [← cancel_epi e.inv]
  exact biproduct.hom_ext' _ _ fun k ↦ by simpa using h (f k) (biproduct.ι (S ∘ f) k ≫ e.inv)

section Dual

variable {i : ι} {X : C}

/-- If a family `c` in `X ⟶ S i` is dual to a family `b` in `S i ⟶ X`, then `b` is linearly
independent. -/
private theorem linearIndependent_of_comp {κ : Type*} [Finite κ] [DecidableEq κ]
    {b : κ → (S i ⟶ X)} {c : κ → (X ⟶ S i)}
    (hbc : ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0) : LinearIndependent R b := by
  cases nonempty_fintype κ
  refine Fintype.linearIndependent_iffₛ.2 fun r s h k ↦ (hS.smul_id_inj (i := i)).1 ?_
  simpa [Preadditive.sum_comp, hbc] using congrArg (· ≫ c k) h

/-- If a family `c` in `X ⟶ S i` is dual to a family `b` in `S i ⟶ X`, then `c` is linearly
independent. -/
private theorem linearIndependent_of_comp' {κ : Type*} [Finite κ] [DecidableEq κ]
    {b : κ → (S i ⟶ X)} {c : κ → (X ⟶ S i)}
    (hbc : ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0) : LinearIndependent R c := by
  cases nonempty_fintype κ
  refine Fintype.linearIndependent_iffₛ.2 fun r s h k ↦ (hS.smul_id_inj (i := i)).1 ?_
  simpa [Preadditive.comp_sum, hbc, eq_comm] using congrArg (b k ≫ ·) h

/-- The morphism modules out of a member have a basis with a dual family, obtained from a
decomposition of `X` as a biproduct of members: the inclusions of the summands isomorphic to
`S i`, and the projections onto them. -/
private theorem exists_basis_dual (i : ι) (X : C) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (a : Basis κ R (S i ⟶ X))
      (a' : κ → (X ⟶ S i)), ∀ j k, a j ≫ a' k = if j = k then 𝟙 (S i) else 0 := by
  classical
  obtain ⟨κ, _, f, ⟨e⟩⟩ := hS.exists_iso_biproduct X
  -- The summands of `X` isomorphic to `S i`, with their inclusions and projections.
  let a₀ : {k // f k = i} → (S i ⟶ X) := fun k ↦
    eqToHom (congrArg S k.2.symm) ≫ biproduct.ι (S ∘ f) k.1 ≫ e.inv
  let a' : {k // f k = i} → (X ⟶ S i) := fun k ↦
    e.hom ≫ biproduct.π (S ∘ f) k.1 ≫ eqToHom (congrArg S k.2)
  have hdual : ∀ j k, a₀ j ≫ a' k = if j = k then 𝟙 (S i) else 0 := by
    rintro j k
    split_ifs with hjk
    · subst hjk
      simp [a₀, a']
    · have : j.1 ≠ k.1 := fun h ↦ hjk (Subtype.ext h)
      simp [a₀, a', biproduct.ι_π_ne_assoc _ this]
  -- Every morphism `g : S i ⟶ X` is the sum of its components along the summands `S i`, the
  -- components along the other summands vanishing by hom-orthogonality.
  have hsum : ∀ g : S i ⟶ X, ∑ k, (g ≫ a' k) ≫ a₀ k = g := fun g ↦ by
    have hg : g = ∑ k, g ≫ e.hom ≫ biproduct.π (S ∘ f) k ≫ biproduct.ι (S ∘ f) k ≫ e.inv := by
      conv_lhs => rw [← Category.comp_id g, ← e.hom_inv_id, ← Category.id_comp e.inv,
        ← biproduct.total]
      simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    conv_rhs => rw [hg]
    rw [← Finset.sum_filter_of_ne (p := fun k ↦ f k = i) fun k _ hk ↦ by_contra fun hki ↦ hk ?_,
      Finset.sum_subtype (p := fun k ↦ f k = i) _ (by simp)]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [a₀, a']
    · have h0 := hS.homOrthogonal.eq_zero (Ne.symm hki) (g ≫ e.hom ≫ biproduct.π (S ∘ f) k)
      simp [reassoc_of% h0]
  refine ⟨_, inferInstance, inferInstance,
    Basis.mk (hS.linearIndependent_of_comp hdual) fun g _ ↦ ?_, a', by simpa using hdual⟩
  rw [← hsum g]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  obtain ⟨r, hr⟩ := hS.exists_eq_smul_id (g ≫ a' k)
  rw [hr, Linear.smul_comp, Category.id_comp]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **The morphism module out of a member is free.** -/
theorem free_hom (i : ι) (X : C) : Module.Free R (S i ⟶ X) := by
  obtain ⟨κ, _, _, a, -⟩ := hS.exists_basis_dual i X
  exact .of_basis a

/-- **The morphism module out of a member is finite.** -/
theorem finite_hom (i : ι) (X : C) : Module.Finite R (S i ⟶ X) := by
  obtain ⟨κ, _, _, a, -⟩ := hS.exists_basis_dual i X
  exact .of_basis a

variable {κ : Type*} [Finite κ] [DecidableEq κ]

omit hS [HasFiniteBiproducts C] in
/-- Composition with a family dual to a basis `b` extracts coordinates in `b`. -/
private theorem comp_eq_repr_smul_id {b : Basis κ R (S i ⟶ X)} {c : κ → (X ⟶ S i)}
    (hbc : ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0) (g : S i ⟶ X) (k : κ) :
    g ≫ c k = b.repr g k • 𝟙 (S i) := by
  cases nonempty_fintype κ
  calc g ≫ c k = (∑ m, b.repr g m • b m) ≫ c k := by rw [b.sum_repr]
  _ = b.repr g k • 𝟙 (S i) := by
    simp only [Preadditive.sum_comp, Linear.smul_comp, hbc, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Finite κ] in
/-- Every basis of `S i ⟶ X` has a dual family in `X ⟶ S i`. -/
private theorem exists_dual (b : Basis κ R (S i ⟶ X)) :
    ∃ c : κ → (X ⟶ S i), ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0 := by
  obtain ⟨κ', _, _, a, a', ha⟩ := hS.exists_basis_dual i X
  -- Transport the dual family of the basis `a` along the change of basis from `a` to `b`.
  refine ⟨fun k ↦ ∑ m, b.repr (a m) k • a' m, fun j k ↦ ?_⟩
  have hb : b.repr (b j) k = ∑ m, a.repr (b j) m * b.repr (a m) k := by
    conv_lhs => rw [← a.sum_repr (b j)]
    simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  simp only [Preadditive.comp_sum, Linear.comp_smul, comp_eq_repr_smul_id ha, smul_smul,
    ← Finset.sum_smul, mul_comm (b.repr _ k), ← hb, Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

omit [Finite κ] in
/-- The family dual to a basis of `S i ⟶ X`. -/
private def dualFamily (b : Basis κ R (S i ⟶ X)) : κ → (X ⟶ S i) :=
  (hS.exists_dual b).choose

omit [Finite κ] in
private theorem apply_comp_dualFamily (b : Basis κ R (S i ⟶ X)) (j k : κ) :
    b j ≫ hS.dualFamily b k = if j = k then 𝟙 (S i) else 0 :=
  (hS.exists_dual b).choose_spec j k

/-- The basis of `X ⟶ S i` dual to a basis `b` of `S i ⟶ X` under the composition pairing:
`b j ≫ hS.homDual b k` is `𝟙 (S i)` if `j = k` and `0` otherwise. -/
def homDual (b : Basis κ R (S i ⟶ X)) : Basis κ R (X ⟶ S i) :=
  Basis.mk (hS.linearIndependent_of_comp' (hS.apply_comp_dualFamily b)) fun h _ ↦ by
    cases nonempty_fintype κ
    choose r hr using fun k ↦ hS.exists_eq_smul_id (b k ≫ h)
    -- `h` is the combination of the dual family with the scalars of the composites `b k ≫ h`:
    -- both sides have the same composites with every morphism out of a member.
    have hh : ∑ k, r k • hS.dualFamily b k = h := by
      refine hS.hom_ext fun j g ↦ ?_
      by_cases hj : j = i
      · subst hj
        simp only [Preadditive.comp_sum, Linear.comp_smul,
          comp_eq_repr_smul_id (hS.apply_comp_dualFamily b), smul_smul]
        refine Eq.trans ?_ (congrArg (· ≫ h) (b.sum_repr g))
        simp only [Preadditive.sum_comp, Linear.smul_comp, hr, smul_smul, mul_comm]
      · exact (hS.homOrthogonal.eq_zero hj _).trans (hS.homOrthogonal.eq_zero hj _).symm
    rw [← hh]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The values of the dual basis. -/
private theorem homDual_apply (b : Basis κ R (S i ⟶ X)) (k : κ) :
    hS.homDual b k = hS.dualFamily b k := by
  simp [homDual]

/-- A basis and its dual basis compose to the identity or to zero. -/
@[simp]
theorem apply_comp_homDual (b : Basis κ R (S i ⟶ X)) (j k : κ) :
    b j ≫ hS.homDual b k = if j = k then 𝟙 (S i) else 0 := by
  rw [homDual_apply, apply_comp_dualFamily]

/-- Composing with an element of the dual basis extracts a coordinate. -/
theorem comp_homDual (b : Basis κ R (S i ⟶ X)) (g : S i ⟶ X) (k : κ) :
    g ≫ hS.homDual b k = b.repr g k • 𝟙 (S i) :=
  comp_eq_repr_smul_id (hS.apply_comp_homDual b) g k

/-- The coordinates of a morphism into `S i` in the dual basis are the scalars of its composites
with the basis. -/
theorem homDual_repr_smul_id (b : Basis κ R (S i ⟶ X)) (h : X ⟶ S i) (k : κ) :
    (hS.homDual b).repr h k • 𝟙 (S i) = b k ≫ h := by
  cases nonempty_fintype κ
  refine Eq.trans ?_ (congrArg (b k ≫ ·) ((hS.homDual b).sum_repr h))
  simp only [Preadditive.comp_sum, Linear.comp_smul, apply_comp_homDual, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The dual basis is characterized by its composites with the basis. -/
theorem eq_homDual_iff (b : Basis κ R (S i ⟶ X)) (h : X ⟶ S i) (k : κ) :
    h = hS.homDual b k ↔ ∀ j, b j ≫ h = if j = k then 𝟙 (S i) else 0 := by
  refine ⟨by rintro rfl j; exact hS.apply_comp_homDual b j k, fun H ↦ ?_⟩
  refine (hS.homDual b).ext_elem fun j ↦ (hS.smul_id_inj (i := i)).1 ?_
  rw [homDual_repr_smul_id, homDual_repr_smul_id, H, apply_comp_homDual]

/-- **The morphism module into a member is free.** -/
theorem free_hom' (i : ι) (X : C) : Module.Free R (X ⟶ S i) := by
  classical
  obtain ⟨κ, _, _, a, -⟩ := hS.exists_basis_dual i X
  exact .of_basis (hS.homDual a)

/-- **The morphism module into a member is finite.** -/
theorem finite_hom' (i : ι) (X : C) : Module.Finite R (X ⟶ S i) := by
  classical
  obtain ⟨κ, _, _, a, -⟩ := hS.exists_basis_dual i X
  exact .of_basis (hS.homDual a)

end Dual

/-- **The completeness relation.** Let `s` be a finite set of indices outside of which `X`
receives no nonzero morphisms from the members, `b i` a basis of `S i ⟶ X` and `c i` a dual family
in `X ⟶ S i` for each `i`. Then the identity of `X` is the sum, over `i ∈ s` and the basis
elements, of the composites of the dual elements with the basis elements. -/
theorem sum_sum_comp_eq_id (X : C) (s : Finset ι) (hs : ∀ j ∉ s, ∀ g : S j ⟶ X, g = 0)
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Basis (κ i) R (S i ⟶ X)) (c : ∀ i, κ i → (X ⟶ S i))
    (hc : ∀ i j k, b i j ≫ c i k = if j = k then 𝟙 (S i) else 0) :
    ∑ i ∈ s, ∑ j, c i j ≫ b i j = 𝟙 X := by
  classical
  refine hS.hom_ext fun j g ↦ ?_
  by_cases hj : j ∈ s
  · rw [Category.comp_id, Preadditive.comp_sum, Finset.sum_eq_single j]
    · -- The component at `j` expands `g` in the basis `b j`.
      simp only [Preadditive.comp_sum, ← Category.assoc, comp_eq_repr_smul_id (hc j),
        Linear.smul_comp, Category.id_comp, Basis.sum_repr]
    · -- The components at `i ≠ j` vanish by hom-orthogonality.
      intro i _ hij
      rw [Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Category.assoc, hS.homOrthogonal.eq_zero (Ne.symm hij) (g ≫ c i k), zero_comp]
    · exact fun h ↦ absurd hj h
  · rw [hs j hj g, zero_comp, zero_comp]

end IsSplitSimpleFamily

section Field

variable (k : Type w) [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [HasFiniteBiproducts C] [Linear k C] [IsFiniteSemisimpleCategory C]

/-- **The field case.** In a finite semisimple abelian category over an algebraically closed
field, whose simple objects have finite-dimensional endomorphisms, the chosen representatives of
the simple classes form a split simple family. No finiteness of the set of simple classes is
needed. -/
theorem isSplitSimpleFamily_simpleClasses
    [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)] :
    IsSplitSimpleFamily k (fun S : SimpleClasses C ↦ S.repr) where
  bijective_algebraMap S := bijective_algebraMap_end_of_simple k S.repr
  homOrthogonal := SimpleClasses.homOrthogonal_repr
  exists_iso_biproduct X := by
    obtain ⟨κ, _, f, hf, _, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
    exact ⟨κ, inferInstance, fun j ↦ SimpleClasses.classOf (f j),
      ⟨e ≪≫ biproduct.mapIso fun j ↦ (SimpleClasses.classOfReprIso (f j)).symm⟩⟩

variable {k} {ι : Type*} {S : ι → C}

/-- Over an algebraically closed field, the dual basis of a split simple family is the dual
basis `Module.Basis.homDual` of the composition pairing given by Schur's lemma. -/
theorem IsSplitSimpleFamily.homDual_eq_homDual (hS : IsSplitSimpleFamily k S) {i : ι} {X : C}
    [Simple (S i)] [FiniteDimensional k (S i ⟶ S i)] {κ : Type*} [Finite κ] [DecidableEq κ]
    (b : Basis κ k (S i ⟶ X)) : hS.homDual b = b.homDual :=
  Basis.eq_of_apply_eq fun l ↦ ((hS.eq_homDual_iff b _ l).2 fun j ↦ b.apply_comp_homDual j l).symm

end Field

end TauCeti
