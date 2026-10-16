/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# The relative Mayer–Vietoris sequence of a square of pairs of simplicial sets

Consider a commutative square of pairs of simplicial sets
```
     t
 P₁  ⟶  P₂
l|       |r
 v       v
 P₃  ⟶  P₄
     b
```
whose square of subobjects and square of ambient simplicial sets are both pushouts with
monomorphic top maps, and let `R` be an object of an abelian category with coproducts. The
relative Mayer–Vietoris short complex `C(P₁; R) ⟶ C(P₂; R) ⊞ C(P₃; R) ⟶ C(P₄; R)` of relative
chain complexes, with first map `(t, -l)` and second map `r + b`, is then short exact
(`SSetPair.shortExact_mayerVietoris`). Its homology sequence is the relative Mayer–Vietoris long
exact sequence
`⋯ ⟶ Hₙ(P₁) ⟶ Hₙ(P₂) ⊞ Hₙ(P₃) ⟶ Hₙ(P₄) ⟶ Hₙ₋₁(P₁) ⟶ ⋯`.

The relative chains of a pair are the cokernel of the chains of its subobject in those of its
ambient simplicial set, so the relative short complex is the cokernel of the morphism from the
absolute Mayer–Vietoris short exact sequence of the subobjects to that of the ambient simplicial
sets. The ambient component of that morphism in the last term is a monomorphism, so the snake
lemma (`CategoryTheory.ShortComplex.ShortExact.of_isColimit_cokernelCofork`) shows that the
cokernel is short exact.

In the typical instance the four ambient simplicial sets are one simplicial set `K` with identity
maps between them, and the subobjects are the intersection, the two members and the union of two
subcomplexes of `K`. For the singular simplicial set of a space `X` and the singular simplices of
open sets `U ∩ V`, `U`, `V` and of `U` or `V`, the small-chain theorem turns this into the sequence
`⋯ ⟶ Hₙ(X, U ∩ V) ⟶ Hₙ(X, U) ⊞ Hₙ(X, V) ⟶ Hₙ(X, U ∪ V) ⟶ ⋯` (`TopCat.relativeMayerVietorisδ`).

## Main definitions and results

* `SSetPair.shortExact_mayerVietoris`: the relative Mayer–Vietoris short complex is short exact.
* `SSetPair.mayerVietorisToBiprod`, `SSetPair.mayerVietorisFromBiprod`: the maps
  `Hₙ(P₁) ⟶ Hₙ(P₂) ⊞ Hₙ(P₃)` and `Hₙ(P₂) ⊞ Hₙ(P₃) ⟶ Hₙ(P₄)`.
* `SSetPair.mayerVietorisδ`: the connecting morphism `Hₙ(P₄) ⟶ Hₘ(P₁)` for `m + 1 = n`.
* `SSetPair.mayerVietoris_exact₁`, `SSetPair.mayerVietoris_exact₂`,
  `SSetPair.mayerVietoris_exact₃`: exactness at `Hₘ(P₁)`, at `Hₙ(P₂) ⊞ Hₙ(P₃)` and at `Hₙ(P₄)`.
* `SSetPair.epi_mayerVietorisFromBiprod_zero`: surjectivity at the degree-zero endpoint.
* `SSetPair.mayerVietorisToBiprod_naturality`, `SSetPair.mayerVietorisFromBiprod_naturality`,
  `SSetPair.mayerVietorisδ_naturality`: the maps of the sequence are natural in maps of squares
  of pairs.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the relative Mayer–Vietoris sequence.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {P₁ P₂ P₃ P₄ : SSetPair.{w}} {t : P₁ ⟶ P₂} {l : P₁ ⟶ P₃} {r : P₂ ⟶ P₄} {b : P₃ ⟶ P₄}

/-! ### The short exact sequence of relative chain complexes -/

variable (t l r b) in
/-- The first map `C(P₁) ⟶ C(P₂) ⊞ C(P₃)` of relative chains followed by the second map
`C(P₂) ⊞ C(P₃) ⟶ C(P₄)` vanishes for a commutative square of pairs. -/
lemma mayerVietoris_chainComplex_zero (w : t ≫ r = l ≫ b) :
    biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫
      biprod.desc (chainComplexMap r R) (chainComplexMap b R) = 0 := by
  simp [← Functor.map_comp, w]

/-- **The relative Mayer–Vietoris short exact sequence.** For a commutative square of pairs of
simplicial sets whose squares of subobjects and of ambient simplicial sets are pushouts with
monomorphic top maps, the relative chain complexes form a short exact sequence
`C(P₁) ⟶ C(P₂) ⊞ C(P₃) ⟶ C(P₄)` with first map `(t, -l)` and second map `r + b`. -/
theorem shortExact_mayerVietoris (sqL : IsPushout t.left l.left r.left b.left) [Mono t.left]
    (sqR : IsPushout t.right l.right r.right b.right) [Mono t.right] :
    (ShortComplex.mk _ _ (mayerVietoris_chainComplex_zero R t l r b
      (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w))).ShortExact := by
  -- The absolute Mayer–Vietoris short exact sequences of the subobjects and of the ambient
  -- simplicial sets.
  let L₁ := ShortComplex.mk (biprod.lift (SSet.chainComplexMap t.left R)
    (-SSet.chainComplexMap l.left R)) (biprod.desc (SSet.chainComplexMap r.left R)
    (SSet.chainComplexMap b.left R))
    (sqL.map ((SSet.chainComplexFunctor C).obj R)).shortComplex.zero
  let L₂ := ShortComplex.mk (biprod.lift (SSet.chainComplexMap t.right R)
    (-SSet.chainComplexMap l.right R)) (biprod.desc (SSet.chainComplexMap r.right R)
    (SSet.chainComplexMap b.right R))
    (sqR.map ((SSet.chainComplexFunctor C).obj R)).shortComplex.zero
  -- The morphism between them given by the inclusions of the subobjects.
  let v : L₁ ⟶ L₂ :=
    { τ₁ := SSet.chainComplexMap P₁.hom R
      τ₂ := biprod.map (SSet.chainComplexMap P₂.hom R) (SSet.chainComplexMap P₃.hom R)
      τ₃ := SSet.chainComplexMap P₄.hom R
      comm₁₂ := by
        apply biprod.hom_ext <;>
          simp [L₁, L₂, chainComplexMap_left_comp_chainComplexMap_hom]
      comm₂₃ := by
        apply biprod.hom_ext' <;>
          simp [L₁, L₂, chainComplexMap_left_comp_chainComplexMap_hom] }
  -- The quotient maps from ambient to relative chains.
  let π : L₂ ⟶ ShortComplex.mk _ _ (mayerVietoris_chainComplex_zero R t l r b
      (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w)) :=
    { τ₁ := P₁.chainComplexπ R
      τ₂ := biprod.map (P₂.chainComplexπ R) (P₃.chainComplexπ R)
      τ₃ := P₄.chainComplexπ R
      comm₁₂ := by
        apply biprod.hom_ext <;>
          simp [L₂, chainComplexπ_naturality]
      comm₂₃ := by
        apply biprod.hom_ext' <;>
          simp [L₂, chainComplexπ_naturality] }
  have hw : v ≫ π = 0 := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
    · simp [v, π]
    · apply biprod.hom_ext' <;> simp [v, π]
    · simp [v, π]
  have : Mono v.τ₃ := inferInstanceAs (Mono (SSet.chainComplexMap P₄.hom R))
  have := (SSet.shortExact_mayerVietoris R sqL).epi_g
  refine (SSet.shortExact_mayerVietoris R sqR).of_isColimit_cokernelCofork
    (SSet.shortExact_mayerVietoris R sqL).exact v π hw ?_
  apply ShortComplex.isColimitOfIsColimitπ <;>
    apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
  · exact P₁.isColimitCokernelCoforkChainComplex R
  · exact CokernelCofork.isColimitBiprod (P₂.isColimitCokernelCoforkChainComplex R)
      (P₃.isColimitCokernelCoforkChainComplex R)
  · exact P₄.isColimitCokernelCoforkChainComplex R

/-! ### The long exact sequence -/

variable (t l) in
/-- The first map `Hₙ(P₁) ⟶ Hₙ(P₂) ⊞ Hₙ(P₃)` of the relative Mayer–Vietoris sequence, with
components `t_*` and `-l_*`. -/
def mayerVietorisToBiprod (n : ℕ) :
    P₁.homology R n ⟶ P₂.homology R n ⊞ P₃.homology R n :=
  biprod.lift (SSetPair.homologyMap t R n) (-SSetPair.homologyMap l R n)

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_fst (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ biprod.fst = SSetPair.homologyMap t R n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_snd (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ biprod.snd = -SSetPair.homologyMap l R n :=
  biprod.lift_snd _ _

variable (r b) in
/-- The second map `Hₙ(P₂) ⊞ Hₙ(P₃) ⟶ Hₙ(P₄)` of the relative Mayer–Vietoris sequence, the sum of
`r_*` and `b_*`. -/
def mayerVietorisFromBiprod (n : ℕ) :
    P₂.homology R n ⊞ P₃.homology R n ⟶ P₄.homology R n :=
  biprod.desc (SSetPair.homologyMap r R n) (SSetPair.homologyMap b R n)

@[reassoc (attr := simp)]
lemma inl_mayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ mayerVietorisFromBiprod R r b n = SSetPair.homologyMap r R n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_mayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ mayerVietorisFromBiprod R r b n = SSetPair.homologyMap b R n :=
  biprod.inr_desc _ _

@[reassoc (attr := simp)]
lemma mayerVietorisToBiprod_fromBiprod (w : t ≫ r = l ≫ b) (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫ mayerVietorisFromBiprod R r b n = 0 := by
  simp [mayerVietorisToBiprod, mayerVietorisFromBiprod, ← homologyMap_comp, w]

variable {Q₁ Q₂ Q₃ Q₄ : SSetPair.{w}} {t' : Q₁ ⟶ Q₂} {l' : Q₁ ⟶ Q₃} {r' : Q₂ ⟶ Q₄}
  {b' : Q₃ ⟶ Q₄} (φ₁ : P₁ ⟶ Q₁) (φ₂ : P₂ ⟶ Q₂) (φ₃ : P₃ ⟶ Q₃) (φ₄ : P₄ ⟶ Q₄)

/-- The first map of the relative Mayer–Vietoris sequence is natural in maps of squares of
pairs. -/
@[reassoc]
lemma mayerVietorisToBiprod_naturality (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l')
    (n : ℕ) :
    mayerVietorisToBiprod R t l n ≫
        biprod.map (SSetPair.homologyMap φ₂ R n) (SSetPair.homologyMap φ₃ R n) =
      SSetPair.homologyMap φ₁ R n ≫ mayerVietorisToBiprod R t' l' n := by
  ext <;> simp [← homologyMap_comp, ht, hl]

/-- The second map of the relative Mayer–Vietoris sequence is natural in maps of squares of
pairs. -/
@[reassoc]
lemma mayerVietorisFromBiprod_naturality (hr : r ≫ φ₄ = φ₂ ≫ r') (hb : b ≫ φ₄ = φ₃ ≫ b')
    (n : ℕ) :
    mayerVietorisFromBiprod R r b n ≫ SSetPair.homologyMap φ₄ R n =
      biprod.map (SSetPair.homologyMap φ₂ R n) (SSetPair.homologyMap φ₃ R n) ≫
        mayerVietorisFromBiprod R r' b' n := by
  ext <;> simp [← homologyMap_comp, hr, hb]

private lemma mayerVietorisToBiprod_eq (n : ℕ) :
    mayerVietorisToBiprod R t l n =
      biprod.lift (SSetPair.homologyMap t R n)
        (HomologicalComplex.homologyMap (-chainComplexMap l R) n) := by
  rw [mayerVietorisToBiprod, HomologicalComplex.homologyMap_neg]

variable (sqL : IsPushout t.left l.left r.left b.left) [Mono t.left]
  (sqR : IsPushout t.right l.right r.right b.right) [Mono t.right]

/-- The relative Mayer–Vietoris connecting morphism `Hₙ(P₄) ⟶ Hₘ(P₁)`, where `m + 1 = n`: the
connecting morphism of the relative Mayer–Vietoris short exact sequence of chain complexes. -/
def mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) : P₄.homology R n ⟶ P₁.homology R m :=
  (shortExact_mayerVietoris R sqL sqR).δ n m (by simpa)

lemma mayerVietorisδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sqL sqR n m h = (shortExact_mayerVietoris R sqL sqR).δ n m (by simpa) :=
  (rfl)

@[reassoc (attr := simp)]
lemma mayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sqL sqR n m h ≫ mayerVietorisToBiprod R t l m = 0 := by
  rw [mayerVietorisToBiprod_eq]
  exact (shortExact_mayerVietoris R sqL sqR).δ_comp_biprod_lift_homologyMap n m (by simpa)

@[reassoc (attr := simp)]
lemma mayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisFromBiprod R r b n ≫ mayerVietorisδ R sqL sqR n m h = 0 :=
  (shortExact_mayerVietoris R sqL sqR).biprod_desc_homologyMap_comp_δ n m (by simpa)

/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₘ(P₁)`.** -/
lemma mayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R sqL sqR n m h)).Exact := by
  convert (shortExact_mayerVietoris R sqL sqR).biprod_homology_exact₁ n m (by simpa) using 2
  exacts [rfl, mayerVietorisToBiprod_eq R m]

include sqL sqR in
/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₙ(P₂) ⊞ Hₙ(P₃)`.** -/
lemma mayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (mayerVietorisToBiprod_fromBiprod R
      (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w) n)).Exact := by
  convert (shortExact_mayerVietoris R sqL sqR).biprod_homology_exact₂ n using 2
  exacts [mayerVietorisToBiprod_eq R n, rfl]

/-- **Exactness of the relative Mayer–Vietoris sequence at `Hₙ(P₄)`.** -/
lemma mayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisFromBiprod_δ R sqL sqR n m h)).Exact :=
  (shortExact_mayerVietoris R sqL sqR).biprod_homology_exact₃ n m (by simpa)

include sqL sqR in
/-- The map `H₀(P₂) ⊞ H₀(P₃) ⟶ H₀(P₄)` at the end of the relative Mayer–Vietoris sequence is an
epimorphism. -/
lemma epi_mayerVietorisFromBiprod_zero : Epi (mayerVietorisFromBiprod R r b 0) := by
  have : Epi ((biprod.desc (chainComplexMap r R) (chainComplexMap b R)).f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (shortExact_mayerVietoris R sqL sqR) 0).epi_g
  have : Epi (HomologicalComplex.homologyMap
      (biprod.desc (chainComplexMap r R) (chainComplexMap b R)) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
  exact HomologicalComplex.epi_biprod_desc_homologyMap 0

/-- **Naturality of the relative Mayer–Vietoris connecting morphism** in maps of squares of
pairs. -/
@[reassoc]
lemma mayerVietorisδ_naturality (sqL' : IsPushout t'.left l'.left r'.left b'.left) [Mono t'.left]
    (sqR' : IsPushout t'.right l'.right r'.right b'.right) [Mono t'.right]
    (ht : t ≫ φ₂ = φ₁ ≫ t') (hl : l ≫ φ₃ = φ₁ ≫ l') (hr : r ≫ φ₄ = φ₂ ≫ r')
    (hb : b ≫ φ₄ = φ₃ ≫ b') (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sqL sqR n m h ≫ SSetPair.homologyMap φ₁ R m =
      SSetPair.homologyMap φ₄ R n ≫ mayerVietorisδ R sqL' sqR' n m h := by
  let ψ : ShortComplex.mk _ _ (mayerVietoris_chainComplex_zero R t l r b
        (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w)) ⟶
      ShortComplex.mk _ _ (mayerVietoris_chainComplex_zero R t' l' r' b'
        (MorphismProperty.Arrow.Hom.ext sqL'.w sqR'.w)) :=
    { τ₁ := chainComplexMap φ₁ R
      τ₂ := biprod.map (chainComplexMap φ₂ R) (chainComplexMap φ₃ R)
      τ₃ := chainComplexMap φ₄ R
      comm₁₂ := by apply biprod.hom_ext <;> simp [← Functor.map_comp, ht, hl]
      comm₂₃ := by apply biprod.hom_ext' <;> simp [← Functor.map_comp, hr, hb] }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m (by simpa)

end SSetPair
