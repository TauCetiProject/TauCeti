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
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.Algebra.Homology.HomologySequenceBiprod
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.CategoryTheory.Subfunctor.Basic
public import TauCeti.Order.CompleteLattice.MulticoequalizerDiagram
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

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
* `SSet.mayerVietorisShortComplexMap`: the map of Mayer–Vietoris short exact sequences induced by
  a map of pushout squares.
* `SSet.mayerVietorisδ_naturality`: the connecting morphism is natural in maps of pushout squares.
* `SSet.quasiIso_chainComplexMap_of_isPushout`: a map of pushout squares that induces
  quasi-isomorphisms on chains at three corners induces one at the fourth.
* `SSet.quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq`: for a bicartesian square of subcomplexes
  `A₁, A₂, A₃, A₄` and a further subcomplex `S`, if `S ⊓ Aᵢ ⊆ Aᵢ` is a quasi-isomorphism on chains
  for `i = 1, 2, 3`, then so is `S ⊓ A₄ ⊆ A₄`.

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

variable {φ₁ φ₂ φ₃ φ₄} in
/-- The map of Mayer–Vietoris short complexes of chain complexes induced by a map of pushout
squares: `C(φ₁)`, `C(φ₂) ⊞ C(φ₃)` and `C(φ₄)` on the three terms. -/
def mayerVietorisShortComplexMap (sq : IsPushout t l r b) (sq' : IsPushout t' l' r' b')
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') :
    (sq.map ((chainComplexFunctor C).obj R)).shortComplex ⟶
      (sq'.map ((chainComplexFunctor C).obj R)).shortComplex where
  τ₁ := chainComplexMap φ₁ R
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
    apply biprod.hom_ext' <;> simp [← Functor.map_comp, hr, hb]

section

variable {φ₁ φ₂ φ₃ φ₄} (sq : IsPushout t l r b) (sq' : IsPushout t' l' r' b')
  (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
  (hb : b ≫ φ₄ = φ₃ ≫ b')

@[simp]
lemma mayerVietorisShortComplexMap_τ₁ :
    (mayerVietorisShortComplexMap R sq sq' ht hl hr hb).τ₁ = chainComplexMap φ₁ R := (rfl)

@[simp]
lemma mayerVietorisShortComplexMap_τ₂ :
    (mayerVietorisShortComplexMap R sq sq' ht hl hr hb).τ₂ =
      biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R) := (rfl)

@[simp]
lemma mayerVietorisShortComplexMap_τ₃ :
    (mayerVietorisShortComplexMap R sq sq' ht hl hr hb).τ₃ = chainComplexMap φ₄ R := (rfl)

end

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
omit [Mono t] in
/-- The map `H₀(X₂) ⊞ H₀(X₃) ⟶ H₀(X₄)` at the end of the Mayer–Vietoris sequence is an
epimorphism. -/
lemma epi_mayerVietorisFromBiprod_zero : Epi (mayerVietorisFromBiprod R r b 0) := by
  have : Epi ((biprod.desc (chainComplexMap r R) (chainComplexMap b R)).f 0) :=
    have : Epi (biprod.desc (chainComplexMap r R) (chainComplexMap b R)) :=
      (sq.map ((chainComplexFunctor C).obj R)).epi_shortComplex_g
    inferInstance
  have : Epi (HomologicalComplex.homologyMap
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R)) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
  exact (HomologicalComplex.epi_biprod_desc_homologyMap_iff 0).2 inferInstance

/-- **Naturality of the Mayer–Vietoris connecting morphism** in maps of pushout squares. -/
@[reassoc]
lemma mayerVietorisδ_naturality (sq' : IsPushout t' l' r' b') [Mono t']
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ SSet.homologyMap φ₁ R m =
      SSet.homologyMap φ₄ R n ≫ mayerVietorisδ R sq' n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (mayerVietorisShortComplexMap R sq sq' ht hl hr hb) _ _ n m h

omit [Mono t] in
/-- Chain lifts with the same boundary determine a cycle in the union term. -/
lemma exists_cycle_of_chain_lifts (sq : CommSq t l r b) {A : C} (q : ℕ)
    (w : A ⟶ (X₁.chainComplex R).X q)
    (u : A ⟶ (X₂.chainComplex R).X (q + 1))
    (v : A ⟶ (X₃.chainComplex R).X (q + 1))
    (hu : u ≫ (X₂.chainComplex R).d (q + 1) q = w ≫ (SSet.chainComplexMap t R).f q)
    (hv : v ≫ (X₃.chainComplex R).d (q + 1) q = w ≫ (SSet.chainComplexMap l R).f q) :
    ∃ z : A ⟶ (X₄.chainComplex R).cycles (q + 1),
      u ≫ (SSet.chainComplexMap r R).f (q + 1) -
        v ≫ (SSet.chainComplexMap b R).f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1) := by
  let x := u ≫ (SSet.chainComplexMap r R).f (q + 1) -
    v ≫ (SSet.chainComplexMap b R).f (q + 1)
  have hx : x ≫ (X₄.chainComplex R).d (q + 1) q = 0 := by
    dsimp only [x]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc,
      HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm,
      ← Category.assoc, ← Category.assoc, hu, hv]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      sq.w, sub_self]
  exact ⟨(X₄.chainComplex R).liftCycles x q (ChainComplex.next_nat_succ q) hx,
    ((X₄.chainComplex R).liftCycles_i x q (ChainComplex.next_nat_succ q) hx).symm⟩

open HomologicalComplex

/-- Two chain lifts with a common boundary compute the native Mayer–Vietoris connecting map. -/
lemma homologyπ_mayerVietorisδ_of_chain_lifts (sq : IsPushout t l r b) {A : C} (q : ℕ)
    (z : A ⟶ (X₄.chainComplex R).cycles (q + 1))
    (w : A ⟶ (X₁.chainComplex R).cycles q)
    (u : A ⟶ (X₂.chainComplex R).X (q + 1))
    (v : A ⟶ (X₃.chainComplex R).X (q + 1))
    (huv : u ≫ (SSet.chainComplexMap r R).f (q + 1) -
        v ≫ (SSet.chainComplexMap b R).f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1))
    (hu : u ≫ (X₂.chainComplex R).d (q + 1) q =
      w ≫ (X₁.chainComplex R).iCycles q ≫ (SSet.chainComplexMap t R).f q)
    (hv : v ≫ (X₃.chainComplex R).d (q + 1) q =
      w ≫ (X₁.chainComplex R).iCycles q ≫ (SSet.chainComplexMap l R).f q) :
    z ≫ (X₄.chainComplex R).homologyπ (q + 1) ≫ SSet.mayerVietorisδ R sq (q + 1) q rfl =
      w ≫ (X₁.chainComplex R).homologyπ q := by
  let SC := (sq.map ((SSet.chainComplexFunctor C).obj R)).shortComplex
  let x₂ : A ⟶ SC.X₂.X (q + 1) :=
    u ≫ (biprod.inl : X₂.chainComplex R ⟶ X₂.chainComplex R ⊞ X₃.chainComplex R).f (q + 1) -
      v ≫ (biprod.inr : X₃.chainComplex R ⟶ X₂.chainComplex R ⊞ X₃.chainComplex R).f (q + 1)
  have hx₂ : x₂ ≫ SC.g.f (q + 1) = z ≫ (X₄.chainComplex R).iCycles (q + 1) := by
    dsimp only [SC, x₂, CommSq.shortComplex_g]
    simpa only [Preadditive.sub_comp, Category.assoc,
      biprod_inl_desc_f, biprod_inr_desc_f] using huv
  have hx₁ : w ≫ (X₁.chainComplex R).iCycles q ≫ SC.f.f q =
      x₂ ≫ SC.X₂.d (q + 1) q := by
    dsimp only [SC, x₂, CommSq.shortComplex_f]
    apply HomologicalComplex.biprodX_ext_to
    · simp only [Category.assoc, biprod_lift_fst_f, Preadditive.sub_comp,
        ← HomologicalComplex.Hom.comm, HomologicalComplex.biprod_inl_fst_f_assoc,
        HomologicalComplex.biprod_inr_fst_f_assoc, zero_comp, comp_zero, sub_zero]
      exact hu.symm
    · simp only [Category.assoc, biprod_lift_snd_f, HomologicalComplex.neg_f_apply,
        Preadditive.comp_neg, Preadditive.sub_comp, ← HomologicalComplex.Hom.comm,
        HomologicalComplex.biprod_inl_snd_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
        zero_comp, comp_zero, zero_sub]
      exact congrArg Neg.neg hv.symm
  have he := (SSet.shortExact_mayerVietorisShortComplex R sq).δ_eq
    (q + 1) q rfl (z ≫ (X₄.chainComplex R).iCycles (q + 1)) (by simp)
    x₂ hx₂ (w ≫ (X₁.chainComplex R).iCycles q)
    (by simpa only [Category.assoc] using hx₁)
    ((ComplexShape.down ℕ).next q) rfl
  have hz : (X₄.chainComplex R).liftCycles
      (z ≫ (X₄.chainComplex R).iCycles (q + 1)) q (ChainComplex.next_nat_succ q)
      (by simp) = z := by
    rw [← cancel_mono ((X₄.chainComplex R).iCycles (q + 1)), liftCycles_i]
  have hw : (X₁.chainComplex R).liftCycles (w ≫ (X₁.chainComplex R).iCycles q)
      ((ComplexShape.down ℕ).next q) rfl (by simp) = w := by
    rw [← cancel_mono ((X₁.chainComplex R).iCycles q), liftCycles_i]
  erw [hz, hw] at he
  exact he

include sq in
variable {φ₁ φ₂ φ₃ φ₄} in
/-- **Comparison of Mayer–Vietoris sequences.** For a map of pushout squares of simplicial sets
whose top maps are monomorphisms, if the maps of chains with coefficients in `R` induced on three
corners `X₁`, `X₂` and `X₃` are quasi-isomorphisms, then so is the one induced on the fourth corner
`X₄`. -/
lemma quasiIso_chainComplexMap_of_isPushout (sq' : IsPushout t' l' r' b') [Mono t']
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (h₁ : QuasiIso (chainComplexMap φ₁ R))
    (h₂ : QuasiIso (chainComplexMap φ₂ R)) (h₃ : QuasiIso (chainComplexMap φ₃ R)) :
    QuasiIso (chainComplexMap φ₄ R) := by
  let ψ := mayerVietorisShortComplexMap R sq sq' ht hl hr hb
  have hψ₂ : QuasiIso ψ.τ₂ := by
    rw [mayerVietorisShortComplexMap_τ₂]
    exact HomologicalComplex.quasiIso_biprod_map _ _
  have hψ₃ : QuasiIso ψ.τ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (shortExact_mayerVietorisShortComplex R sq) (shortExact_mayerVietorisShortComplex R sq')
    (by rwa [mayerVietorisShortComplexMap_τ₁]) hψ₂
  rwa [mayerVietorisShortComplexMap_τ₃] at hψ₃

section Subcomplex

variable {X : SSet.{w}} {S A₁ A₂ A₃ A₄ : X.Subcomplex}

/-- **Comparison of Mayer–Vietoris sequences of subcomplexes.** Let `A₁, A₂, A₃, A₄` be a
bicartesian square of subcomplexes of `X`, so that `A₂ ⊔ A₃ = A₄` and `A₂ ⊓ A₃ = A₁`, and let `S`
be a further subcomplex. If the inclusions `S ⊓ A₁ ⊆ A₁`, `S ⊓ A₂ ⊆ A₂` and `S ⊓ A₃ ⊆ A₃` induce
quasi-isomorphisms on chains with coefficients in `R`, then so does `S ⊓ A₄ ⊆ A₄`. -/
lemma quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq (hsq : Subcomplex.BicartSq A₁ A₂ A₃ A₄)
    (h₁ : QuasiIso (chainComplexMap (Subcomplex.homOfLE (inf_le_right : S ⊓ A₁ ≤ A₁)) R))
    (h₂ : QuasiIso (chainComplexMap (Subcomplex.homOfLE (inf_le_right : S ⊓ A₂ ≤ A₂)) R))
    (h₃ : QuasiIso (chainComplexMap (Subcomplex.homOfLE (inf_le_right : S ⊓ A₃ ≤ A₃)) R)) :
    QuasiIso (chainComplexMap (Subcomplex.homOfLE (inf_le_right : S ⊓ A₄ ≤ A₄)) R) :=
  -- The inclusions `S ⊓ Aᵢ ⊆ Aᵢ` form a map of pushout squares; each square commutes because
  -- both of its composites are the inclusion of a subcomplex.
  quasiIso_chainComplexMap_of_isPushout R (Subcomplex.BicartSq.isPushout (hsq.inf_left S))
    hsq.isPushout
    (by rw [Subcomplex.homOfLE_comp, Subcomplex.homOfLE_comp])
    (by rw [Subcomplex.homOfLE_comp, Subcomplex.homOfLE_comp])
    (by rw [Subcomplex.homOfLE_comp, Subcomplex.homOfLE_comp])
    (by rw [Subcomplex.homOfLE_comp, Subcomplex.homOfLE_comp]) h₁ h₂ h₃

end Subcomplex

end SSet
