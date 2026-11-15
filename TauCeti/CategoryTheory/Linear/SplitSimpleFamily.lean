/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Split simple families and dual bases of morphisms over a commutative semiring

Let `C` be a preadditive `R`-linear category over a commutative semiring `R`, and let `S` be an
object with **scalar endomorphisms**: the structure map `algebraMap R (End S)`, `r ↦ r • 𝟙 S`, is
bijective. Then for every object `X` composition defines an `R`-bilinear pairing

`TauCeti.homPairingOfBijective hS X : (S ⟶ X) × (X ⟶ S) → R`,  `f ≫ g = ⟨f, g⟩ • 𝟙 S`,

compatible with composition on the `X` side. No abelian structure and no field is needed.

A family `S : ι → C` is a **split simple family** (`TauCeti.IsSplitSimpleFamily R S`) when every
`S i` has scalar endomorphisms, the family is hom-orthogonal, and every object is isomorphic to a
finite biproduct `⨁ k, S (f k)` of members. Under such an isomorphism a morphism `S i ⟶ X` is a
column of scalars indexed by the summands `k` with `f k = i`, a morphism `X ⟶ S i` is a row of
such scalars, and the composition pairing is their dot product. Hence:

* the Hom modules `S i ⟶ X` and `X ⟶ S i` are free of finite rank, and have bases dual to each
  other under the pairing;
* the composition pairing is perfect, so every basis of `S i ⟶ X` has a dual basis of
  `X ⟶ S i`;
* the **completeness relation** holds: if `b i` is a basis of `S i ⟶ X` with dual family `c i`,
  then `∑ i ∈ s, ∑ j, c i j ≫ b i j = 𝟙 X` for every finite set `s` of indices outside of which
  `X` receives no nonzero morphism from the family.

Over an algebraically closed field the representatives of the simple classes of a finite
semisimple category form a split simple family; see `TauCeti.CategoryTheory.Semisimple.DualBasis`,
which develops the field case. Over a general commutative ring the hypothesis also applies to
categories which are not abelian, such as graded free modules of finite rank over `ℤ`, and it is
the setting in which fusion multiplicities and structure constants of a monoidal category with
finitely many split simple objects are read off as coordinates in bases of Hom modules.

## Main declarations

* `TauCeti.homPairingOfBijective`: the composition pairing of an object with scalar
  endomorphisms, characterized by `TauCeti.homPairingOfBijective_smul_id`;
* `Module.Basis.comp_eq_repr_smul_id`: composing with a dual family extracts coordinates;
* `TauCeti.IsSplitSimpleFamily`: the hypothesis on `S : ι → C`;
* `TauCeti.IsSplitSimpleFamily.exists_dual_bases`, `TauCeti.IsSplitSimpleFamily.free_finite_hom`
  and `TauCeti.IsSplitSimpleFamily.free_finite_homTo`: the Hom modules are free of finite rank, with
  mutually dual bases;
* `TauCeti.IsSplitSimpleFamily.isPerfPair_homPairingOfBijective`: the pairing is perfect, and
  `TauCeti.IsSplitSimpleFamily.exists_homDual` gives the dual basis of any basis;
* `TauCeti.IsSplitSimpleFamily.sum_sum_comp_eq_id`: the completeness relation.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §1.8, for the
  pairing over a field
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Module

universe w v u

namespace TauCeti

section Pairing

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {S : C} (hS : Function.Bijective (algebraMap R (End S)))

/-- The composition pairing between morphisms out of and into an object `S` with scalar
endomorphisms: `homPairingOfBijective hS X f g` is the scalar `c` with `f ≫ g = c • 𝟙 S`. -/
def homPairingOfBijective (X : C) : (S ⟶ X) →ₗ[R] (X ⟶ S) →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun f g ↦ (AlgEquiv.ofBijective (Algebra.ofId R (End S)) hS).symm (End.of (f ≫ g)))
    (fun f f' g ↦ by simp) (fun c f g ↦ by simp) (fun f g g' ↦ by simp) (fun c f g ↦ by simp)

variable {hS} {X : C}

/-- The composite of a morphism out of `S` with a morphism back is the scalar given by the
composition pairing. -/
@[simp]
theorem homPairingOfBijective_smul_id (f : S ⟶ X) (g : X ⟶ S) :
    homPairingOfBijective hS X f g • 𝟙 S = f ≫ g := by
  have h : algebraMap R (End S) (homPairingOfBijective hS X f g) = End.of (f ≫ g) :=
    (AlgEquiv.ofBijective (Algebra.ofId R (End S)) hS).apply_symm_apply (End.of (f ≫ g))
  simpa using congrArg End.asHom h

/-- The composition pairing takes the value `c` exactly when the composite is `c • 𝟙 S`. -/
theorem homPairingOfBijective_eq_iff (f : S ⟶ X) (g : X ⟶ S) (c : R) :
    homPairingOfBijective hS X f g = c ↔ f ≫ g = c • 𝟙 S := by
  rw [← homPairingOfBijective_smul_id (hS := hS)]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ hS.injective (End.ext ?_)⟩
  rw [End.algebraMap_asHom (R := R), End.algebraMap_asHom (R := R), h]

/-- A morphism between the two objects can be moved across the composition pairing. -/
theorem homPairingOfBijective_comp (f : S ⟶ X) {Y : C} (h : X ⟶ Y) (g : Y ⟶ S) :
    homPairingOfBijective hS Y (f ≫ h) g = homPairingOfBijective hS X f (h ≫ g) := by
  rw [homPairingOfBijective_eq_iff, homPairingOfBijective_smul_id, Category.assoc]

end Pairing

end TauCeti

namespace Module.Basis

open TauCeti

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {S X : C} {κ : Type*} [DecidableEq κ] (b : Basis κ R (S ⟶ X))
  {c : κ → (X ⟶ S)}

/-- Composing with a family dual to a basis `b` of `S ⟶ X` extracts the coordinates in `b`. -/
theorem comp_eq_repr_smul_id (hc : ∀ j k, b j ≫ c k = if j = k then 𝟙 S else 0) (f : S ⟶ X)
    (k : κ) : f ≫ c k = b.repr f k • 𝟙 S := by
  conv_lhs => rw [← b.linearCombination_repr f]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Preadditive.sum_comp]
  simp only [Linear.smul_comp, hc, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs with h <;> simp_all

/-- Pairing with a family dual to a basis `b` of `S ⟶ X` computes the coordinates in `b`. -/
theorem homPairingOfBijective_eq_repr
    {hS : Function.Bijective (algebraMap R (CategoryTheory.End S))}
    (hc : ∀ j k, b j ≫ c k = if j = k then 𝟙 S else 0) (f : S ⟶ X) (k : κ) :
    homPairingOfBijective hS X f (c k) = b.repr f k := by
  rw [homPairingOfBijective_eq_iff, b.comp_eq_repr_smul_id hc]

end Module.Basis

namespace TauCeti

/-- A **split simple family** `S : ι → C` in an `R`-linear category with finite biproducts: each
`S i` has scalar endomorphisms, the family is hom-orthogonal, and every object is isomorphic to a
finite biproduct of members of the family. No finiteness of `ι` is assumed. -/
structure IsSplitSimpleFamily (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] [HasFiniteBiproducts C] {ι : Type*} (S : ι → C) : Prop where
  /-- Each member of the family has endomorphisms the scalars `R`. -/
  bijective_algebraMap (i : ι) : Function.Bijective (algebraMap R (End (S i)))
  /-- There are no nonzero morphisms between distinct members of the family. -/
  homOrthogonal : HomOrthogonal S
  /-- Every object is a finite biproduct of members of the family. -/
  exists_iso_biproduct (X : C) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → ι), Nonempty (X ≅ ⨁ fun k ↦ S (f k))

namespace IsSplitSimpleFamily

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasFiniteBiproducts C]
variable {ι : Type*} {S : ι → C} (hS : IsSplitSimpleFamily R S)
include hS

/-- Morphisms out of an object are determined by their composites with the morphisms into it
from members of the family. -/
theorem hom_ext {X Y : C} {g g' : X ⟶ Y} (h : ∀ i (f : S i ⟶ X), f ≫ g = f ≫ g') : g = g' := by
  obtain ⟨κ, _, f, ⟨e⟩⟩ := hS.exists_iso_biproduct X
  rw [← cancel_epi e.inv]
  exact biproduct.hom_ext' _ _ fun k ↦ by
    simpa using h (f k) (biproduct.ι (fun k ↦ S (f k)) k ≫ e.inv)

/-- The summands isomorphic to `S i` in a decomposition of `X`: morphisms `u k : S i ⟶ X` and
`v k : X ⟶ S i` with `u k ≫ v l = δ k l • 𝟙`, such that `∑ k, v k ≫ u k` acts as the identity on
morphisms from `S i` and on morphisms to `S i`. -/
private theorem exists_summands (i : ι) (X : C) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (u : K → (S i ⟶ X)) (v : K → (X ⟶ S i)),
      (∀ k l, u k ≫ v l = if k = l then 𝟙 (S i) else 0) ∧
      (∀ f : S i ⟶ X, f ≫ ∑ k, v k ≫ u k = f) ∧ (∀ g : X ⟶ S i, (∑ k, v k ≫ u k) ≫ g = g) := by
  classical
  obtain ⟨κ, _, f, ⟨e⟩⟩ := hS.exists_iso_biproduct X
  -- `T k` is the idempotent of `X` projecting onto its `k`-th summand; the summands with
  -- `f k = i` are the copies of `S i`, and the others receive no morphism from `S i`.
  let T : κ → (X ⟶ X) := fun k ↦
    e.hom ≫ biproduct.π (fun k ↦ S (f k)) k ≫ biproduct.ι (fun k ↦ S (f k)) k ≫ e.inv
  have hT : ∑ k, T k = 𝟙 X := calc
    ∑ k, T k = e.hom ≫ (∑ k, biproduct.π (fun k ↦ S (f k)) k ≫
        biproduct.ι (fun k ↦ S (f k)) k) ≫ e.inv := by
      simp only [T, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 X := by rw [biproduct.total, Category.id_comp, e.hom_inv_id]
  have hsum : ∑ k : {k // f k = i},
      (e.hom ≫ biproduct.π (fun k ↦ S (f k)) k.1 ≫ eqToHom (congrArg S k.2)) ≫
        (eqToHom (congrArg S k.2.symm) ≫ biproduct.ι (fun k ↦ S (f k)) k.1 ≫ e.inv) =
      ∑ k ∈ Finset.univ.filter (f · = i), T k := by
    rw [Finset.sum_subtype (p := (f · = i)) _ (by simp) T]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [T]
  refine ⟨{k // f k = i}, inferInstance, inferInstance,
    fun k ↦ eqToHom (congrArg S k.2.symm) ≫ biproduct.ι (fun k ↦ S (f k)) k.1 ≫ e.inv,
    fun k ↦ e.hom ≫ biproduct.π (fun k ↦ S (f k)) k.1 ≫ eqToHom (congrArg S k.2), ?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩ ⟨l, hl⟩
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_assoc]
    by_cases h : k = l
    · subst h
      simp
    · simp [h]
  · intro g
    rw [hsum, Preadditive.comp_sum, Finset.sum_filter_of_ne, ← Preadditive.comp_sum, hT,
      Category.comp_id]
    intro k _ hk
    by_contra hki
    have h0 := hS.homOrthogonal.eq_zero (Ne.symm hki) (g ≫ e.hom ≫ biproduct.π (fun k ↦ S (f k)) k)
    exact hk (by simp [T, reassoc_of% h0])
  · intro g
    rw [hsum, Preadditive.sum_comp, Finset.sum_filter_of_ne, ← Preadditive.sum_comp, hT,
      Category.id_comp]
    intro k _ hk
    by_contra hki
    exact hk (by
      simp [T, hS.homOrthogonal.eq_zero hki (biproduct.ι (fun k ↦ S (f k)) k ≫ e.inv ≫ g)])

/-- **Dual bases.** For a member `S i` and any object `X`, the modules `S i ⟶ X` and `X ⟶ S i`
have bases indexed by the same finite type, dual to each other under composition. -/
theorem exists_dual_bases (i : ι) (X : C) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (u : Basis K R (S i ⟶ X))
      (v : Basis K R (X ⟶ S i)), ∀ k l, u k ≫ v l = if k = l then 𝟙 (S i) else 0 := by
  obtain ⟨K, _, _, u, v, huv, hu, hv⟩ := hS.exists_summands i X
  let p := homPairingOfBijective (hS.bijective_algebraMap i) X
  have hp : ∀ k l, p (u k) (v l) = if k = l then 1 else 0 := fun k l ↦ by
    rw [homPairingOfBijective_eq_iff, huv]
    split_ifs <;> simp
  have hdu : DualBases u fun k ↦ p.flip (v k) :=
    { eval_same k := by simp [hp]
      eval_of_ne k l hkl := by simp [hp, Ne.symm hkl]
      total {f₁ f₂} h := by
        rw [← hu f₁, ← hu f₂, Preadditive.comp_sum, Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Category.assoc, ← Category.assoc,
          ← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i),
          ← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i)]
        exact congrArg (fun x : R ↦ (x • 𝟙 (S i)) ≫ u k) (h k) }
  have hdv : DualBases v fun k ↦ p (u k) :=
    { eval_same k := by simp [hp]
      eval_of_ne k l hkl := by simp [hp, hkl]
      total {g₁ g₂} h := by
        rw [← hv g₁, ← hv g₂, Preadditive.sum_comp, Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Category.assoc, Category.assoc,
          ← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i),
          ← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i)]
        exact congrArg (fun x : R ↦ v k ≫ (x • 𝟙 (S i))) (h k) }
  exact ⟨K, inferInstance, inferInstance, hdu.basis, hdv.basis, by simpa using huv⟩

/-- **The Hom modules out of a member are free of finite rank.** -/
theorem free_finite_hom (i : ι) (X : C) :
    Module.Free R (S i ⟶ X) ∧ Module.Finite R (S i ⟶ X) := by
  obtain ⟨K, _, _, u, -, -⟩ := hS.exists_dual_bases i X
  exact ⟨.of_basis u, .of_basis u⟩

/-- **The Hom modules into a member are free of finite rank.** -/
theorem free_finite_homTo (i : ι) (X : C) :
    Module.Free R (X ⟶ S i) ∧ Module.Finite R (X ⟶ S i) := by
  obtain ⟨K, _, _, -, v, -⟩ := hS.exists_dual_bases i X
  exact ⟨.of_basis v, .of_basis v⟩

/-- **The composition pairing of a member of a split simple family is perfect.** -/
theorem isPerfPair_homPairingOfBijective (i : ι) (X : C) :
    (homPairingOfBijective (hS.bijective_algebraMap i) X).IsPerfPair := by
  obtain ⟨K, _, _, u, v, huv⟩ := hS.exists_dual_bases i X
  refine u.isPerfPair_of_apply_eq_ite v _ (Equiv.refl K) fun k l ↦ ?_
  rw [homPairingOfBijective_eq_iff, huv, Equiv.refl_apply]
  split_ifs <;> simp_all

/-- **Dual bases.** Every basis of `S i ⟶ X` has a dual basis of `X ⟶ S i` under composition. -/
theorem exists_homDual (i : ι) (X : C) {κ : Type*} [Finite κ] [DecidableEq κ]
    (b : Basis κ R (S i ⟶ X)) :
    ∃ c : Basis κ R (X ⟶ S i), ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0 := by
  have := hS.isPerfPair_homPairingOfBijective i X
  set p := homPairingOfBijective (hS.bijective_algebraMap i) X
  refine ⟨b.dualBasis.map p.flip.toPerfPair.symm, fun j k ↦ ?_⟩
  rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i), Basis.map_apply,
    LinearMap.apply_toPerfPair_flip, Basis.dualBasis_apply_self]
  split_ifs <;> simp_all

/-- Morphisms into a member `S i` are determined by their composites with the morphisms from
`S i`. -/
theorem homTo_ext (i : ι) {X : C} {g g' : X ⟶ S i} (h : ∀ f : S i ⟶ X, f ≫ g = f ≫ g') :
    g = g' := by
  refine hS.hom_ext fun j f ↦ ?_
  by_cases hij : j = i
  · subst hij
    exact h f
  · rw [hS.homOrthogonal.eq_zero hij (f ≫ g), hS.homOrthogonal.eq_zero hij (f ≫ g')]

/-- **Coordinates in a dual family.** If `c` is dual to a basis `b` of `S i ⟶ X`, every morphism
`g : X ⟶ S i` is the combination of the `c k` with coefficients its pairings with the `b k`. -/
theorem sum_homPairingOfBijective_smul_eq (i : ι) {X : C} {κ : Type*} [Fintype κ]
    [DecidableEq κ] (b : Basis κ R (S i ⟶ X)) {c : κ → (X ⟶ S i)}
    (hc : ∀ j k, b j ≫ c k = if j = k then 𝟙 (S i) else 0) (g : X ⟶ S i) :
    ∑ k, homPairingOfBijective (hS.bijective_algebraMap i) X (b k) g • c k = g := by
  refine hS.homTo_ext i fun f ↦ ?_
  rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap i) f g]
  conv_rhs => rw [← b.sum_repr f]
  simp only [Preadditive.comp_sum, Linear.comp_smul, b.comp_eq_repr_smul_id hc, smul_smul,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_smul,
    mul_comm]

/-- **The completeness relation.** Let `s` be a finite set of indices outside of which `X`
receives no nonzero morphism from the family. Choose for every `i` a basis `b i` of `S i ⟶ X` and
a family `c i` dual to it. Then the identity of `X` is the sum over `i ∈ s` of the composites
`c i j ≫ b i j`. -/
theorem sum_sum_comp_eq_id (X : C) (s : Finset ι) (hs : ∀ j ∉ s, ∀ g : S j ⟶ X, g = 0)
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Basis (κ i) R (S i ⟶ X)) (c : ∀ i, κ i → (X ⟶ S i))
    (hc : ∀ i j k, b i j ≫ c i k = if j = k then 𝟙 (S i) else 0) :
    ∑ i ∈ s, ∑ j, c i j ≫ b i j = 𝟙 X := by
  classical
  refine hS.hom_ext fun i f ↦ ?_
  by_cases hi : i ∈ s
  · rw [Preadditive.comp_sum, Finset.sum_eq_single_of_mem i hi, Category.comp_id]
    · conv_rhs => rw [← (b i).sum_repr f]
      simp [Preadditive.comp_sum, ← Category.assoc, (b i).comp_eq_repr_smul_id (hc i)]
    · intro j _ hji
      rw [Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Category.assoc, hS.homOrthogonal.eq_zero (Ne.symm hji) (f ≫ c j k), zero_comp]
  · rw [hs i hi f, zero_comp, zero_comp]

end IsSplitSimpleFamily

end TauCeti
