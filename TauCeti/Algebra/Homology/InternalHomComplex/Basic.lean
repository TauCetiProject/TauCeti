/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Basic

/-!
# The internal Hom complex of two cochain complexes

Let `C` be a closed monoidal preadditive category with countable products. For cochain complexes
`K` and `L` in `C`, the internal Hom complex `𝓗om^•(K, L)` has degree `n` term

`∏_{p + n = q} 𝓗om(K^p, L^q)`,

the product of the internal Homs `ihom (K.X p)` evaluated at `L.X q`. Its differential is the
internal version of the differential `δ z = d_L ∘ z + (-1)^{n+1} z ∘ d_K` of Mathlib's Hom
complex `CochainComplex.HomComplex`.

Rather than writing the differential down in components, we characterize everything by the
universal property of the degree `n` term. Morphisms `T ⟶ 𝓗om^n(K, L)` from an object `T` are
the same as degree `n` cochains `K ⊗ T ⟶ L`, where `K ⊗ T` is the complex obtained by tensoring
`K` on the right with `T` (`CochainComplex.internalHomComplexHomEquiv`); this is the
tensor-Hom adjunction applied to every factor of the product. The differential, and the maps
induced by morphisms of complexes, are the unique morphisms which correspond to Mathlib's
differential `CochainComplex.HomComplex.δ` and to composition of cochains under this
identification, naturally in `T`. All identities between them, including `d ∘ d = 0`, are thus
inherited from the identities between cochains.

For `C = X.Modules` this is the Hom complex of complexes of `𝒪_X`-modules of
[Stacks, Section 20.41 (0A8K)].

## Main definitions

* `CochainComplex.internalHomComplex K L`: the internal Hom complex.
* `CochainComplex.internalHomComplexHomEquiv`: morphisms into its degree `n` term are degree `n`
  cochains `K ⊗ T ⟶ L`.
* `TauCeti.internalHomComplexPrecomp` and `TauCeti.internalHomComplexPostcomp`: the maps induced
  by morphisms of complexes in the source and in the target.
* `TauCeti.internalHomComplexFunctor C`: the internal Hom complex as a bifunctor, contravariant in
  the source and covariant in the target.

## References

* [Stacks Project, Section 15.73 (0A8H)](https://stacks.math.columbia.edu/tag/0A8H): the Hom
  complex of complexes of modules.
* [Stacks Project, Section 20.41 (0A8K)](https://stacks.math.columbia.edu/tag/0A8K): the Hom
  complex of complexes of `𝒪_X`-modules.
* Joël Riou's Mathlib Hom complex `CochainComplex.HomComplex`, whose cochains and differential
  the internal Hom complex represents.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C]

namespace CochainComplex

namespace InternalHomComplex

variable (K L : CochainComplex C ℤ)

/-- The degree `n` term `∏_{p + n = q} 𝓗om(K^p, L^q)` of the internal Hom complex. -/
private abbrev X (n : ℤ) : C :=
  ∏ᶜ fun T : Triplet n ↦ (ihom (K.X T.p)).obj (L.X T.q)

/-- Morphisms into the degree `n` term of the internal Hom complex are degree `n` cochains from
the complex `K ⊗ T` to `L`. -/
private def homEquiv (T : C) (n : ℤ) :
    (T ⟶ X K L n) ≃+ Cochain (((tensorRight T).mapHomologicalComplex _).obj K) L n where
  toFun φ := Cochain.mk fun p q hpq ↦
    uncurry (φ ≫ Pi.π (fun t : Triplet n ↦ (ihom (K.X t.p)).obj (L.X t.q)) ⟨p, q, hpq⟩)
  invFun z := Pi.lift fun t ↦ curry (z.v t.p t.q t.hpq)
  left_inv φ := Pi.hom_ext _ _ fun t ↦ by simp
  right_inv z := by
    ext p q hpq
    rw [Cochain.mk_v, Pi.lift_comp_π, uncurry_curry]
  map_add' φ ψ := by
    ext
    simp [uncurry_eq, Preadditive.add_comp, MonoidalPreadditive.whiskerLeft_add]

variable {K L}

private lemma homEquiv_v {T : C} {n : ℤ} (φ : T ⟶ X K L n) (p q : ℤ) (hpq : p + n = q) :
    (homEquiv K L T n φ).v p q hpq =
      uncurry (φ ≫ Pi.π (fun t : Triplet n ↦ (ihom (K.X t.p)).obj (L.X t.q)) ⟨p, q, hpq⟩) :=
  (rfl)

private lemma homEquiv_symm_comp_π {T : C} {n : ℤ}
    (z : Cochain (((tensorRight T).mapHomologicalComplex _).obj K) L n) (p q : ℤ)
    (hpq : p + n = q) :
    (homEquiv K L T n).symm z ≫ Pi.π (fun t : Triplet n ↦ (ihom (K.X t.p)).obj (L.X t.q))
      ⟨p, q, hpq⟩ = curry (z.v p q hpq) :=
  Pi.lift_comp_π (fun t : Triplet n ↦ curry (z.v t.p t.q t.hpq)) _

private lemma homEquiv_comp {T' T : C} {n : ℤ} (g : T' ⟶ T) (φ : T ⟶ X K L n) :
    homEquiv K L T' n (g ≫ φ) =
      (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K)).comp
        (homEquiv K L T n φ) (zero_add n) := by
  ext p q hpq
  simp [homEquiv_v, uncurry_natural_left]

/-- The differential of the internal Hom complex, characterized by `homEquiv_comp_d`. -/
private def d (n m : ℤ) : X K L n ⟶ X K L m :=
  (homEquiv K L _ m).symm (δ n m (homEquiv K L _ n (𝟙 _)))

private lemma homEquiv_comp_d {T : C} {n : ℤ} (φ : T ⟶ X K L n) (m : ℤ) :
    homEquiv K L T m (φ ≫ d n m) = δ n m (homEquiv K L T n φ) := by
  rw [homEquiv_comp, d, AddEquiv.apply_symm_apply, ← δ_ofHom_comp, ← homEquiv_comp,
    Category.comp_id]

private lemma homEquiv_d {n : ℤ} (m : ℤ) :
    homEquiv K L _ m (d n m) = δ n m (homEquiv K L (X K L n) n (𝟙 _)) := by
  rw [← homEquiv_comp_d, Category.id_comp]

end InternalHomComplex

open InternalHomComplex

variable (K L : CochainComplex C ℤ)

/-- The internal Hom complex `𝓗om^•(K, L)` of two cochain complexes in a closed monoidal
preadditive category with countable products. Its degree `n` term is
`∏_{p + n = q} 𝓗om(K^p, L^q)`, and morphisms into it from an object `T` are the degree `n`
cochains `K ⊗ T ⟶ L` (`CochainComplex.internalHomComplexHomEquiv`), compatibly with the
differentials (`CochainComplex.internalHomComplexHomEquiv_comp_d`) and naturally in `T`
(`CochainComplex.internalHomComplexHomEquiv_comp`). -/
def internalHomComplex : CochainComplex C ℤ where
  X := InternalHomComplex.X K L
  d := InternalHomComplex.d
  shape n m hnm := by
    rw [InternalHomComplex.d, δ_shape n m hnm, map_zero]
  d_comp_d' n m k _ _ := (homEquiv K L _ k).injective (by
    rw [homEquiv_comp_d, homEquiv_d, δ_δ, map_zero])

/-- The projection from the degree `n` term `∏_{p + n = q} 𝓗om(K^p, L^q)` of the internal Hom
complex to its factor `𝓗om(K^p, L^q)`. -/
def internalHomComplexπ (n p q : ℤ) (hpq : p + n = q) :
    (internalHomComplex K L).X n ⟶ (ihom (K.X p)).obj (L.X q) :=
  Pi.π (fun t : Triplet n ↦ (ihom (K.X t.p)).obj (L.X t.q)) ⟨p, q, hpq⟩

/-- Morphisms from `T` into the degree `n` term of the internal Hom complex `𝓗om^•(K, L)` are the
degree `n` cochains from `K ⊗ T` to `L`: this is the tensor-Hom adjunction in every factor of the
product. -/
def internalHomComplexHomEquiv (T : C) (n : ℤ) :
    (T ⟶ (internalHomComplex K L).X n) ≃+
      Cochain (((tensorRight T).mapHomologicalComplex _).obj K) L n :=
  homEquiv K L T n

variable {K L}

/-- The component of the cochain attached to `φ` is the uncurried projection of `φ`. -/
lemma internalHomComplexHomEquiv_v {T : C} {n : ℤ} (φ : T ⟶ (internalHomComplex K L).X n)
    (p q : ℤ) (hpq : p + n = q) :
    (internalHomComplexHomEquiv K L T n φ).v p q hpq =
      uncurry (φ ≫ internalHomComplexπ K L n p q hpq) :=
  (rfl)

/-- Projecting the morphism attached to a cochain gives the curried component of the cochain. -/
@[reassoc (attr := simp)]
lemma internalHomComplexHomEquiv_symm_comp_π {T : C} {n : ℤ}
    (z : Cochain (((tensorRight T).mapHomologicalComplex _).obj K) L n) (p q : ℤ)
    (hpq : p + n = q) :
    (internalHomComplexHomEquiv K L T n).symm z ≫ internalHomComplexπ K L n p q hpq =
      curry (z.v p q hpq) :=
  homEquiv_symm_comp_π z p q hpq

/-- The identification `internalHomComplexHomEquiv` is natural in the test object `T`. -/
lemma internalHomComplexHomEquiv_comp {T' T : C} {n : ℤ} (g : T' ⟶ T)
    (φ : T ⟶ (internalHomComplex K L).X n) :
    internalHomComplexHomEquiv K L T' n (g ≫ φ) =
      (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K)).comp
        (internalHomComplexHomEquiv K L T n φ) (zero_add n) :=
  homEquiv_comp g φ

/-- Under `internalHomComplexHomEquiv`, the differential of the internal Hom complex is Mathlib's
differential of cochains. -/
@[simp]
lemma internalHomComplexHomEquiv_comp_d {T : C} {n : ℤ} (φ : T ⟶ (internalHomComplex K L).X n)
    (m : ℤ) :
    internalHomComplexHomEquiv K L T m (φ ≫ (internalHomComplex K L).d n m) =
      δ n m (internalHomComplexHomEquiv K L T n φ) :=
  homEquiv_comp_d φ m

/-- Two morphisms into a term of the internal Hom complex are equal if their cochains are. -/
lemma internalHomComplex_hom_ext {T : C} {n : ℤ} {φ ψ : T ⟶ (internalHomComplex K L).X n}
    (h : internalHomComplexHomEquiv K L T n φ = internalHomComplexHomEquiv K L T n ψ) : φ = ψ :=
  (internalHomComplexHomEquiv K L T n).injective h

/-- Two morphisms out of a term of the internal Hom complex into another one are equal if their
cochains are. -/
lemma internalHomComplex_hom_ext' {K' L' : CochainComplex C ℤ} {n n' : ℤ}
    {a b : (internalHomComplex K L).X n ⟶ (internalHomComplex K' L').X n'}
    (h : internalHomComplexHomEquiv K' L' _ n' (𝟙 _ ≫ a) =
      internalHomComplexHomEquiv K' L' _ n' (𝟙 _ ≫ b)) : a = b := by
  simpa using internalHomComplex_hom_ext h

end CochainComplex

namespace TauCeti

open CochainComplex

variable {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex C ℤ}

/-- The cochain `(f ⊗ T) ∘ z` attached to a morphism `f : K₁ ⟶ K₂` and a cochain
`z : K₂ ⊗ T ⟶ L` of degree `n`. -/
private abbrev precompCochain (f : K₁ ⟶ K₂) {L : CochainComplex C ℤ} {T : C} {n : ℤ}
    (z : Cochain (((tensorRight T).mapHomologicalComplex _).obj K₂) L n) :
    Cochain (((tensorRight T).mapHomologicalComplex _).obj K₁) L n :=
  (Cochain.ofHom (((tensorRight T).mapHomologicalComplex _).map f)).comp z (zero_add n)

omit [MonoidalClosed C] [HasCountableProducts C] in
private lemma ofHom_whiskerLeft_comp_precompCochain (f : K₁ ⟶ K₂) {L : CochainComplex C ℤ}
    {T' T : C} (g : T' ⟶ T) {n : ℤ}
    (z : Cochain (((tensorRight T).mapHomologicalComplex _).obj K₂) L n) :
    (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K₁)).comp
        (precompCochain f z) (zero_add n) =
      precompCochain f ((Cochain.ofHom
        ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app K₂)).comp z
          (zero_add n)) := by
  ext p q hpq
  simp [whisker_exchange_assoc]

/-- Precomposition with a morphism `f : K₁ ⟶ K₂` of cochain complexes, as a morphism
`𝓗om^•(K₂, L) ⟶ 𝓗om^•(K₁, L)` of internal Hom complexes. It is characterized by
`TauCeti.internalHomComplexHomEquiv_comp_precomp_f`. -/
def internalHomComplexPrecomp (f : K₁ ⟶ K₂) (L : CochainComplex C ℤ) :
    internalHomComplex K₂ L ⟶ internalHomComplex K₁ L where
  f n := (internalHomComplexHomEquiv K₁ L _ n).symm
    (precompCochain f (internalHomComplexHomEquiv K₂ L _ n (𝟙 _)))
  comm' n m _ := internalHomComplex_hom_ext (by
    rw [internalHomComplexHomEquiv_comp_d, internalHomComplexHomEquiv_comp,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, δ_ofHom_comp,
      ofHom_whiskerLeft_comp_precompCochain, ← internalHomComplexHomEquiv_comp,
      Category.comp_id, ← internalHomComplexHomEquiv_comp_d, Category.id_comp])

/-- Under `internalHomComplexHomEquiv`, precomposition with `f` acts on cochains by precomposition
with `f ⊗ T`. -/
@[simp]
lemma internalHomComplexHomEquiv_comp_precomp_f (f : K₁ ⟶ K₂) {L : CochainComplex C ℤ} {T : C}
    {n : ℤ} (φ : T ⟶ (internalHomComplex K₂ L).X n) :
    internalHomComplexHomEquiv K₁ L T n (φ ≫ (internalHomComplexPrecomp f L).f n) =
      (Cochain.ofHom (((tensorRight T).mapHomologicalComplex _).map f)).comp
        (internalHomComplexHomEquiv K₂ L T n φ) (zero_add n) := by
  rw [internalHomComplexHomEquiv_comp, internalHomComplexPrecomp, AddEquiv.apply_symm_apply,
    ofHom_whiskerLeft_comp_precompCochain, ← internalHomComplexHomEquiv_comp,
    Category.comp_id]

/-- Postcomposition with a morphism `g : L₁ ⟶ L₂` of cochain complexes, as a morphism
`𝓗om^•(K, L₁) ⟶ 𝓗om^•(K, L₂)` of internal Hom complexes. It is characterized by
`TauCeti.internalHomComplexHomEquiv_comp_postcomp_f`. -/
def internalHomComplexPostcomp (K : CochainComplex C ℤ) (g : L₁ ⟶ L₂) :
    internalHomComplex K L₁ ⟶ internalHomComplex K L₂ where
  f n := (internalHomComplexHomEquiv K L₂ _ n).symm
    ((internalHomComplexHomEquiv K L₁ _ n (𝟙 _)).comp (Cochain.ofHom g) (add_zero n))
  comm' n m _ := internalHomComplex_hom_ext (by
    rw [internalHomComplexHomEquiv_comp_d, internalHomComplexHomEquiv_comp,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, δ_comp_ofHom,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← internalHomComplexHomEquiv_comp,
      Category.comp_id, ← internalHomComplexHomEquiv_comp_d, Category.id_comp])

/-- Under `internalHomComplexHomEquiv`, postcomposition with `g` acts on cochains by
postcomposition with `g`. -/
@[simp]
lemma internalHomComplexHomEquiv_comp_postcomp_f {K : CochainComplex C ℤ} (g : L₁ ⟶ L₂) {T : C}
    {n : ℤ} (φ : T ⟶ (internalHomComplex K L₁).X n) :
    internalHomComplexHomEquiv K L₂ T n (φ ≫ (internalHomComplexPostcomp K g).f n) =
      (internalHomComplexHomEquiv K L₁ T n φ).comp (Cochain.ofHom g) (add_zero n) := by
  rw [internalHomComplexHomEquiv_comp, internalHomComplexPostcomp, AddEquiv.apply_symm_apply,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← internalHomComplexHomEquiv_comp,
    Category.comp_id]

@[simp]
lemma internalHomComplexPrecomp_id (K L : CochainComplex C ℤ) :
    internalHomComplexPrecomp (𝟙 K) L = 𝟙 _ := by
  ext n : 1
  refine internalHomComplex_hom_ext' ?_
  rw [internalHomComplexHomEquiv_comp_precomp_f, CategoryTheory.Functor.map_id, Cochain.id_comp,
    HomologicalComplex.id_f, Category.comp_id]

@[simp]
lemma internalHomComplexPrecomp_comp (f : K₁ ⟶ K₂) (f' : K₂ ⟶ K₃) (L : CochainComplex C ℤ) :
    internalHomComplexPrecomp (f ≫ f') L =
      internalHomComplexPrecomp f' L ≫ internalHomComplexPrecomp f L := by
  ext n : 1
  refine internalHomComplex_hom_ext' ?_
  rw [HomologicalComplex.comp_f, ← Category.assoc, internalHomComplexHomEquiv_comp_precomp_f,
    internalHomComplexHomEquiv_comp_precomp_f, internalHomComplexHomEquiv_comp_precomp_f,
    CategoryTheory.Functor.map_comp, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

@[simp]
lemma internalHomComplexPostcomp_id (K L : CochainComplex C ℤ) :
    internalHomComplexPostcomp K (𝟙 L) = 𝟙 _ := by
  ext n : 1
  refine internalHomComplex_hom_ext' ?_
  rw [internalHomComplexHomEquiv_comp_postcomp_f, Cochain.comp_id, HomologicalComplex.id_f,
    Category.comp_id]

@[simp]
lemma internalHomComplexPostcomp_comp (K : CochainComplex C ℤ) (g : L₁ ⟶ L₂) (g' : L₂ ⟶ L₃) :
    internalHomComplexPostcomp K (g ≫ g') =
      internalHomComplexPostcomp K g ≫ internalHomComplexPostcomp K g' := by
  ext n : 1
  refine internalHomComplex_hom_ext' ?_
  rw [HomologicalComplex.comp_f, ← Category.assoc, internalHomComplexHomEquiv_comp_postcomp_f,
    internalHomComplexHomEquiv_comp_postcomp_f, internalHomComplexHomEquiv_comp_postcomp_f,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_second_is_zero_cochain]

/-- Precomposition and postcomposition commute. -/
lemma internalHomComplexPrecomp_postcomp_comm (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) :
    internalHomComplexPrecomp f L₁ ≫ internalHomComplexPostcomp K₁ g =
      internalHomComplexPostcomp K₂ g ≫ internalHomComplexPrecomp f L₂ := by
  ext n : 1
  refine internalHomComplex_hom_ext' ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc,
    internalHomComplexHomEquiv_comp_postcomp_f, internalHomComplexHomEquiv_comp_precomp_f,
    internalHomComplexHomEquiv_comp_precomp_f, internalHomComplexHomEquiv_comp_postcomp_f,
    Cochain.comp_assoc_of_first_is_zero_cochain]

variable (C) in
/-- The internal Hom complex as a bifunctor, contravariant in the source cochain complex and
covariant in the target one. -/
@[expose, simps]
def internalHomComplexFunctor :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K :=
    { obj L := internalHomComplex K.unop L
      map g := internalHomComplexPostcomp K.unop g
      map_id L := internalHomComplexPostcomp_id K.unop L
      map_comp g g' := internalHomComplexPostcomp_comp K.unop g g' }
  map f :=
    { app L := internalHomComplexPrecomp f.unop L
      naturality _ _ g := (internalHomComplexPrecomp_postcomp_comm f.unop g).symm }
  map_id K := by ext L : 2; exact internalHomComplexPrecomp_id K.unop L
  map_comp f f' := by ext L : 2; exact internalHomComplexPrecomp_comp f'.unop f.unop L

end TauCeti
