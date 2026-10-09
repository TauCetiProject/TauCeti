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
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative
public import TauCeti.Algebra.Homology.HomologySequenceBiprod

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

* `SSet.shortExact_mayerVietorisShortComplex`: it is short exact for a pushout square whose top
  map is a monomorphism; `SSet.shortExact_mayerVietoris` writes it with middle term
  `C(X₂) ⊞ C(X₃)`, and its first map is split in each degree
  (`SSet.isSplitMono_biprod_lift_chainComplexMap_f`).
* `SSet.mayerVietorisToBiprod`, `SSet.mayerVietorisFromBiprod`: the maps
  `Hₙ(X₁) ⟶ Hₙ(X₂) ⊞ Hₙ(X₃)` and `Hₙ(X₂) ⊞ Hₙ(X₃) ⟶ Hₙ(X₄)`.
* `SSet.mayerVietorisδ`: the connecting morphism `Hₙ(X₄) ⟶ Hₘ(X₁)` for `m + 1 = n`.
* `SSet.mayerVietoris_exact₁`, `SSet.mayerVietoris_exact₂`, `SSet.mayerVietoris_exact₃`:
  exactness at `Hₘ(X₁)`, at `Hₙ(X₂) ⊞ Hₙ(X₃)` and at `Hₙ(X₄)`.
* `SSet.epi_mayerVietorisFromBiprod_zero`: surjectivity at the degree-zero endpoint.
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

/-- **The Mayer–Vietoris short exact sequence of chain complexes.** For a pushout square of
simplicial sets whose top map is a monomorphism, the Mayer–Vietoris short complex is short
exact. -/
lemma shortExact_mayerVietorisShortComplex (sq : IsPushout t l r b) [Mono t] :
    (sq.map ((chainComplexFunctor C).obj R)).shortComplex.ShortExact where
  -- The chain complex functor preserves pushouts.
  exact := (sq.map ((chainComplexFunctor C).obj R)).exact_shortComplex
  mono_f := by
    -- Expose the chain map before typeclass synthesis of its mono instance.
    change Mono (biprod.lift (chainComplexMap t R) (-chainComplexMap l R))
    have : Mono (chainComplexMap t R) := inferInstance
    exact mono_of_mono_fac (biprod.lift_fst (chainComplexMap t R) (-chainComplexMap l R))
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

private lemma mayerVietorisToBiprod_eq (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃) (n : ℕ) :
    mayerVietorisToBiprod R t l n =
      biprod.lift (SSet.homologyMap t R n)
        (HomologicalComplex.homologyMap (-chainComplexMap l R) n) := by
  rw [mayerVietorisToBiprod, HomologicalComplex.homologyMap_neg]

/-- In each degree, the first map `C(X₁) ⟶ C(X₂) ⊞ C(X₃)` of the Mayer–Vietoris sequence is a split
monomorphism when `t` is a monomorphism. -/
instance isSplitMono_biprod_lift_chainComplexMap_f [Mono t] (i : ℕ) :
    IsSplitMono ((biprod.lift (chainComplexMap t R) (-chainComplexMap l R)).f i) := by
  -- `SSetPair.of t` has `t` as its structure map, so this is the split monomorphism instance for
  -- the chains of a pair of simplicial sets.
  have : IsSplitMono ((chainComplexMap t R).f i) :=
    inferInstanceAs (IsSplitMono ((chainComplexMap (SSetPair.of t).hom R).f i))
  exact IsSplitMono.mk'
    { retraction := (biprod.fst : X₂.chainComplex R ⊞ X₃.chainComplex R ⟶ _).f i ≫
        retraction ((chainComplexMap t R).f i)
      id := by rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_fst,
        IsSplitMono.id] }

variable (sq : IsPushout t l r b) [Mono t]

/-- The Mayer–Vietoris short exact sequence, written with its middle term `C(X₂) ⊞ C(X₃)`. -/
lemma shortExact_mayerVietoris :
    (ShortComplex.mk (biprod.lift (chainComplexMap t R) (-chainComplexMap l R))
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R))
      (sq.map ((chainComplexFunctor C).obj R)).shortComplex.zero).ShortExact :=
  shortExact_mayerVietorisShortComplex R sq

/-- The Mayer–Vietoris connecting morphism `Hₙ(X₄) ⟶ Hₘ(X₁)`, where `m + 1 = n`: the connecting
morphism of the Mayer–Vietoris short exact sequence of chain complexes. -/
def mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) : X₄.homology R n ⟶ X₁.homology R m :=
  (shortExact_mayerVietorisShortComplex R sq).δ n m h

lemma mayerVietorisδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h = (shortExact_mayerVietorisShortComplex R sq).δ n m h := (rfl)

@[reassoc (attr := simp)]
lemma mayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ mayerVietorisToBiprod R t l m = 0 := by
  rw [mayerVietorisToBiprod_eq]
  exact (shortExact_mayerVietoris R sq).δ_comp_biprod_lift_homologyMap n m h

@[reassoc (attr := simp)]
lemma mayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisFromBiprod R r b n ≫ mayerVietorisδ R sq n m h = 0 :=
  (shortExact_mayerVietoris R sq).biprod_desc_homologyMap_comp_δ n m h

/-- **Exactness of the Mayer–Vietoris sequence at `Hₘ(X₁)`.** -/
lemma mayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R sq n m h)).Exact := by
  convert (shortExact_mayerVietoris R sq).biprod_homology_exact₁ n m h using 2
  exacts [rfl, mayerVietorisToBiprod_eq R t l m]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X₂) ⊞ Hₙ(X₃)`.** -/
lemma mayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisToBiprod_fromBiprod R sq.toCommSq n)).Exact := by
  convert (shortExact_mayerVietoris R sq).biprod_homology_exact₂ n using 2
  exacts [mayerVietorisToBiprod_eq R t l n, rfl]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X₄)`.** -/
lemma mayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisFromBiprod_δ R sq n m h)).Exact :=
  (shortExact_mayerVietoris R sq).biprod_homology_exact₃ n m h

include sq in
/-- The map `H₀(X₂) ⊞ H₀(X₃) ⟶ H₀(X₄)` at the end of the Mayer–Vietoris sequence is an
epimorphism. -/
lemma epi_mayerVietorisFromBiprod_zero : Epi (mayerVietorisFromBiprod R r b 0) := by
  have : Epi ((biprod.desc (chainComplexMap r R) (chainComplexMap b R)).f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (shortExact_mayerVietorisShortComplex R sq) 0).epi_g
  have : Epi (HomologicalComplex.homologyMap
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R)) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
  exact HomologicalComplex.epi_biprod_desc_homologyMap 0

/-- **Naturality of the Mayer–Vietoris connecting morphism** in maps of pushout squares. -/
@[reassoc]
lemma mayerVietorisδ_naturality (sq' : IsPushout t' l' r' b') [Mono t']
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ SSet.homologyMap φ₁ R m =
      SSet.homologyMap φ₄ R n ≫ mayerVietorisδ R sq' n m h := by
  let ψ : (sq.map ((chainComplexFunctor C).obj R)).shortComplex ⟶
      (sq'.map ((chainComplexFunctor C).obj R)).shortComplex :=
    { τ₁ := chainComplexMap φ₁ R
      τ₂ := biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R)
      τ₃ := chainComplexMap φ₄ R
      comm₁₂ := by
        -- Expose the two `f` maps to check the square on both biproduct projections.
        change chainComplexMap φ₁ R ≫
            biprod.lift (chainComplexMap t' R) (-chainComplexMap l' R) =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫
            biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R)
        apply biprod.hom_ext <;> simp [← Functor.map_comp, ht, hl]
      comm₂₃ := by
        -- Expose the two `g` maps to check the square on both biproduct inclusions.
        change biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R) ≫
            biprod.desc (chainComplexMap r' R) (chainComplexMap b' R) =
          biprod.desc (chainComplexMap r R) (chainComplexMap b R) ≫ chainComplexMap φ₄ R
        apply biprod.hom_ext' <;> simp [← Functor.map_comp, hr, hb] }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m h

end SSet
