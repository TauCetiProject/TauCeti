/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.CommSq
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct

/-!
# The Mayer–Vietoris sequence of a pushout of simplicial sets

Consider a commutative square of simplicial sets
```
     t
 X₁  ⟶  X₂
l|       |r
 v       v
 X₃  ⟶  X₄
     b
```
and an object `R` of an abelian category with coproducts. Its Mayer–Vietoris short complex of
chain complexes is `C(X₁; R) ⟶ C(X₂; R) ⊞ C(X₃; R) ⟶ C(X₄; R)`, with first map `(t, -l)` and
second map `r + b`. When the square is a pushout and `t` is a monomorphism, this short complex is
short exact: the chain complex functor preserves pushouts, and a pushout square in an abelian
category is right exact in this form. The homology sequence of this short exact sequence is the
Mayer–Vietoris long exact sequence
`⋯ ⟶ Hₙ(X₁) ⟶ Hₙ(X₂) ⊞ Hₙ(X₃) ⟶ Hₙ(X₄) ⟶ Hₙ₋₁(X₁) ⟶ ⋯`,
whose first two maps are `(t_*, -l_*)` and `r_* + b_*`.

The typical pushout square is that of two subcomplexes `A` and `B` of a simplicial set, their
intersection and their union (`SSet.Subcomplex.BicartSq.isPushout`). The Mayer–Vietoris sequence
of singular homology for an open cover by two sets is obtained from such a square.

## Main definitions and results

* `SSet.mayerVietorisShortComplex`: the Mayer–Vietoris short complex of chain complexes.
* `SSet.shortExact_mayerVietorisShortComplex`: it is short exact for a pushout square whose top
  map is a monomorphism.
* `SSet.mayerVietorisToBiprod`, `SSet.mayerVietorisFromBiprod`: the maps
  `Hₙ(X₁) ⟶ Hₙ(X₂) ⊞ Hₙ(X₃)` and `Hₙ(X₂) ⊞ Hₙ(X₃) ⟶ Hₙ(X₄)`.
* `SSet.mayerVietorisδ`: the connecting morphism `Hₙ(X₄) ⟶ Hₘ(X₁)` for `m + 1 = n`.
* `SSet.mayerVietoris_exact₁`, `SSet.mayerVietoris_exact₂`, `SSet.mayerVietoris_exact₃`:
  exactness at `Hₘ(X₁)`, at `Hₙ(X₂) ⊞ Hₙ(X₃)` and at `Hₙ(X₄)`.
* `SSet.mayerVietorisδ_naturality`: the connecting morphism is natural in maps of pushout squares.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- The Mayer–Vietoris short complex of chain complexes of a commutative square of simplicial sets:
`C(X₁; R) ⟶ C(X₂; R) ⊞ C(X₃; R) ⟶ C(X₄; R)`, with first map `(t, -l)` and second map `r + b`. -/
abbrev mayerVietorisShortComplex (sq : CommSq t l r b) : ShortComplex (ChainComplex C ℕ) where
  X₁ := X₁.chainComplex R
  X₂ := X₂.chainComplex R ⊞ X₃.chainComplex R
  X₃ := X₄.chainComplex R
  f := biprod.lift (chainComplexMap t R) (-chainComplexMap l R)
  g := biprod.desc (chainComplexMap r R) (chainComplexMap b R)
  zero := by simp [← Functor.map_comp, sq.w]

/-- **The Mayer–Vietoris short exact sequence of chain complexes.** For a pushout square of
simplicial sets whose top map is a monomorphism, the Mayer–Vietoris short complex is short
exact. -/
lemma shortExact_mayerVietorisShortComplex (sq : IsPushout t l r b) [Mono t] :
    (mayerVietorisShortComplex R sq.toCommSq).ShortExact where
  -- The chain complex functor preserves pushouts, and the short complex that Mathlib attaches to
  -- the image of the square, `CommSq.shortComplex`, has the same objects and maps as the
  -- Mayer–Vietoris short complex.
  exact := (sq.map ((chainComplexFunctor C).obj R)).exact_shortComplex
  mono_f := mono_of_mono_fac (biprod.lift_fst (chainComplexMap t R) (-chainComplexMap l R))
  epi_g := (sq.map ((chainComplexFunctor C).obj R)).epi_shortComplex_g

/-! ### The long exact sequence -/

/-- The first map `Hₙ(X₁) ⟶ Hₙ(X₂) ⊞ Hₙ(X₃)` of the Mayer–Vietoris sequence, with components
`t_*` and `-l_*`. -/
def mayerVietorisToBiprod (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    X₁.homology R n ⟶ X₂.homology R n ⊞ X₃.homology R n :=
  biprod.lift (SSet.homologyMap t R n) (-SSet.homologyMap l R n)

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_fst (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ biprod.fst = SSet.homologyMap t R n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_snd (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ biprod.snd = -SSet.homologyMap l R n :=
  biprod.lift_snd _ _

/-- The second map `Hₙ(X₂) ⊞ Hₙ(X₃) ⟶ Hₙ(X₄)` of the Mayer–Vietoris sequence, the sum of `r_*`
and `b_*`. -/
def mayerVietorisFromBiprod (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    X₂.homology R n ⊞ X₃.homology R n ⟶ X₄.homology R n :=
  biprod.desc (SSet.homologyMap r R n) (SSet.homologyMap b R n)

@[reassoc (attr := simp)]
lemma inl_mayerVietorisFromBiprod (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    biprod.inl ≫ mayerVietorisFromBiprod R r b n = SSet.homologyMap r R n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_mayerVietorisFromBiprod (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    biprod.inr ≫ mayerVietorisFromBiprod R r b n = SSet.homologyMap b R n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_fromBiprod (sq : CommSq t l r b) (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ mayerVietorisFromBiprod R r b n = 0 := by
  simp [mayerVietorisToBiprod, mayerVietorisFromBiprod, ← homologyMap_comp, sq.w]

variable {Y₁ Y₂ Y₃ Y₄ : SSet.{w}} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
  (φ₁ : X₁ ⟶ Y₁) (φ₂ : X₂ ⟶ Y₂) (φ₃ : X₃ ⟶ Y₃) (φ₄ : X₄ ⟶ Y₄)

/-- The first map of the Mayer–Vietoris sequence is natural in maps of squares. -/
@[reassoc]
lemma mayerVietorisToBiprod_naturality (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l')
    (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ biprod.map (SSet.homologyMap φ₂ R n) (SSet.homologyMap φ₃ R n) =
      SSet.homologyMap φ₁ R n ≫ mayerVietorisToBiprod R t' l' n := by
  ext <;> simp [← homologyMap_comp, ht, hl]

/-- The second map of the Mayer–Vietoris sequence is natural in maps of squares. -/
@[reassoc]
lemma mayerVietorisFromBiprod_naturality (hr : r ≫ φ₄ = φ₂ ≫ r') (hb : b ≫ φ₄ = φ₃ ≫ b')
    (n : ℕ) :
    mayerVietorisFromBiprod R r b n ≫ SSet.homologyMap φ₄ R n =
      biprod.map (SSet.homologyMap φ₂ R n) (SSet.homologyMap φ₃ R n) ≫
        mayerVietorisFromBiprod R r' b' n := by
  ext <;> simp [← homologyMap_comp, hr, hb]

/-- Homology commutes with the biproduct in the middle of the Mayer–Vietoris short complex. -/
private abbrev homologyBiprodIso (n : ℕ) :
    (X₂.chainComplex R ⊞ X₃.chainComplex R).homology n ≅
      X₂.homology R n ⊞ X₃.homology R n :=
  (HomologicalComplex.homologyFunctor C _ n).mapBiprod _ _

private lemma homologyMap_lift_comp_homologyBiprodIso_hom (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    HomologicalComplex.homologyMap (biprod.lift (chainComplexMap t R) (-chainComplexMap l R)) n ≫
        (homologyBiprodIso R n).hom =
      mayerVietorisToBiprod R t l n :=
  (biprod.map_lift_mapBiprod (HomologicalComplex.homologyFunctor C _ n) (X₂.chainComplex R)
    (X₃.chainComplex R) (chainComplexMap t R) (-chainComplexMap l R)).trans
    (by rw [Functor.map_neg]; rfl)

private lemma homologyBiprodIso_hom_comp_fromBiprod (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) (n : ℕ) :
    (homologyBiprodIso R n).hom ≫ mayerVietorisFromBiprod R r b n =
      HomologicalComplex.homologyMap (biprod.desc (chainComplexMap r R) (chainComplexMap b R)) n :=
  biprod.mapBiprod_hom_desc (HomologicalComplex.homologyFunctor C _ n) _ _ _ _

variable (sq : IsPushout t l r b) [Mono t]

/-- The Mayer–Vietoris connecting morphism `Hₙ(X₄) ⟶ Hₘ(X₁)`, where `m + 1 = n`: the connecting
morphism of the Mayer–Vietoris short exact sequence of chain complexes. -/
def mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) : X₄.homology R n ⟶ X₁.homology R m :=
  (shortExact_mayerVietorisShortComplex R sq).δ n m h

lemma mayerVietorisδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h = (shortExact_mayerVietorisShortComplex R sq).δ n m h := (rfl)

@[reassoc (attr := simp)]
lemma mayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ mayerVietorisToBiprod R t l m = 0 := by
  have := (shortExact_mayerVietorisShortComplex R sq).δ_comp n m h
  rw [mayerVietorisδ, ← homologyMap_lift_comp_homologyBiprodIso_hom, reassoc_of% this, zero_comp]

@[reassoc (attr := simp)]
lemma mayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisFromBiprod R r b n ≫ mayerVietorisδ R sq n m h = 0 := by
  have := (shortExact_mayerVietorisShortComplex R sq).comp_δ n m h
  rw [← cancel_epi (homologyBiprodIso R n).hom, comp_zero, ← Category.assoc,
    homologyBiprodIso_hom_comp_fromBiprod, mayerVietorisδ, this]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₘ(X₁)`.** -/
lemma mayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R sq n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mayerVietorisShortComplex R sq).homology_exact₁ n m h)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIso R m) ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    exact (homologyMap_lift_comp_homologyBiprodIso_hom R t l m).symm

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X₂) ⊞ Hₙ(X₃)`.** -/
lemma mayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisToBiprod_fromBiprod R sq.toCommSq n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mayerVietorisShortComplex R sq).homology_exact₂ n)
  refine ShortComplex.isoMk (Iso.refl _) (homologyBiprodIso R n) (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    exact (homologyMap_lift_comp_homologyBiprodIso_hom R t l n).symm
  · rw [Iso.refl_hom, Category.comp_id]
    exact homologyBiprodIso_hom_comp_fromBiprod R r b n

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X₄)`.** -/
lemma mayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisFromBiprod_δ R sq n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mayerVietorisShortComplex R sq).homology_exact₃ n m h)
  refine ShortComplex.isoMk (homologyBiprodIso R n) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact homologyBiprodIso_hom_comp_fromBiprod R r b n
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

/-- **Naturality of the Mayer–Vietoris connecting morphism** in maps of pushout squares. -/
@[reassoc]
lemma mayerVietorisδ_naturality (sq' : IsPushout t' l' r' b') [Mono t']
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ SSet.homologyMap φ₁ R m =
      SSet.homologyMap φ₄ R n ≫ mayerVietorisδ R sq' n m h := by
  let ψ : mayerVietorisShortComplex R sq.toCommSq ⟶ mayerVietorisShortComplex R sq'.toCommSq :=
    { τ₁ := chainComplexMap φ₁ R
      τ₂ := biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R)
      τ₃ := chainComplexMap φ₄ R
      comm₁₂ := by apply biprod.hom_ext <;> simp [← Functor.map_comp, ht, hl]
      comm₂₃ := by apply biprod.hom_ext' <;> simp [← Functor.map_comp, hr, hb] }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m h

end SSet
