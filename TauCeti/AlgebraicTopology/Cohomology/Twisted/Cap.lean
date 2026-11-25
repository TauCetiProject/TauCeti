/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Action
public import TauCeti.AlgebraicTopology.Singular.Twisted.AlexanderWhitney.Relative

/-!
# Cap products with local coefficients

Let `L` and `K` be local systems of modules over a commutative ring `R` on a space `X`, and let
`M` be an `R`-module. A twisted cochain of degree `p` with values in `M` is a morphism
`φ : C_p(X; L) ⟶ M`, so it reads a coefficient of `L` at the initial vertex of a simplex. Its cap
product with a chain twisted by `L ⊗ K` is a chain twisted by `M ⊗ K`, the tensor product of the
constant system `M` with `K`: a singular `(p + q)`-simplex `σ` with coefficient `a ⊗ b` goes to its
back `q`-face, with coefficient `φ(a') ⊗ b'`, where `a'` is `a` placed on the front `p`-face of
`σ` and `b'` is `b` transported along the edge of `σ` from vertex `0` to vertex `p`, the initial
vertex of the back face (`TauCeti.LocalCoefficientSystem.ιTwistedChainComplex_capChain`).
This is Hatcher's front-face/back-face formula `σ ⌢ φ = φ(σ|[v₀, …, v_p]) σ|[v_p, …, v_n]` with
the coefficients paired at `v₀` and the result transported to the first vertex of the surviving
back face.

The construction applies the cap product of chains and cochains along a diagonal,
`TauCeti.ChainComplex.capChain`, to the twisted Alexander–Whitney diagonal
`TauCeti.LocalCoefficientSystem.twistedAlexanderWhitneyDiagonal`, with the action
`TauCeti.LocalCoefficientSystem.twistedChainComplexAction` of `M` on the chains twisted by `K`,
which sends `m ⊗ (σ, b)` to `(σ, m ⊗ b)`. So it satisfies the boundary formula
`∂(x ⌢ φ) = (-1)^p (∂x ⌢ φ - x ⌢ δφ)` (`TauCeti.ChainComplex.capChain_comp_d`) and descends to the
cap product of twisted cohomology and twisted homology,

`Hᵖ(X; L, M) ⟶ (Hₙ(X; L ⊗ K) ⟶ H_q(X; M ⊗ K))`,  `p + q = n`,

(`TauCeti.LocalCoefficientSystem.twistedCap`), which is `R`-linear in the cohomology class,
natural in both coefficient systems
(`TauCeti.LocalCoefficientSystem.twistedCap_coefficient_naturality`) and satisfies the projection
formula `f_*(x ⌢ f^*α) = f_*x ⌢ α` for continuous maps
(`TauCeti.LocalCoefficientSystem.twistedCap_space_naturality`). Any pairing of local systems
`M ⊗ K ⟶ K'` or `T ⟶ L ⊗ K` is then applied by a change of coefficients on homology. For instance,
if `o` is a local system with `o ⊗ o` isomorphic to the constant system `R`, such as the
orientation system of a real vector bundle, capping with a class with coefficients in `o` sends
untwisted homology to homology twisted by `o`.

For a pair `(X, A)`, a relative cochain vanishes on the front faces of the simplices of `A`, so the
cap product descends to relative chains: the twisted diagonal read in relative chains in its first
factor gives the relative diagonal `C(X, A; L ⊗ K) ⟶ C(X, A; L) ⊗ C(X; K)`
(`TopPair.twistedAlexanderWhitneyDiagonal`), and with it the relative cap product

`Hᵖ(X, A; L, M) ⟶ (Hₙ(X, A; L ⊗ K) ⟶ H_q(X; M ⊗ K))`

(`TopPair.twistedCap`), which agrees with the absolute one on the image of relative cohomology
(`TopPair.twistedCap_twistedCohomologyπ`) and satisfies the projection formula for maps of pairs
(`TopPair.twistedCap_space_naturality`), since the relative diagonal is natural in maps of pairs
(`TopPair.twistedAlexanderWhitneyDiagonal_space_naturality`).

Followed by a push-forward, it gives `TopPair.twistedPushforwardCap`: for a map `p₀ : X ⟶ Y`,
local systems `L`, `K` and `N` on `Y` with a morphism `ε : K ⟶ L ⊗ N`, and a class
`u ∈ Hⁿ(X, A; p₀^*L, R)`, the morphism `Hₘ(X, A; p₀^*K) ⟶ Hₚ(Y; N)`, `x ↦ p₀_*(ε_* x ⌢ u)`,
`R`-linear in `u`. The morphism `ε` reads a chain twisted by `p₀^*K` as a chain twisted by
`p₀^*L ⊗ p₀^*N`, and the cap product with `u` consumes the first factor, the constant system `R`
being the unit of the tensor product (`TauCeti.LocalCoefficientSystem.constantTensorIso`). For a
copairing `R ⟶ L ⊗ L` tensored with a local system `J` on `Y`, this is a morphism
`Hₘ(X, A; p₀^*J) ⟶ Hₚ(Y; L ⊗ J)`. It is natural in maps of pairs over `Y`
(`TopPair.twistedPushforwardCap_naturality`). This is the form of the homology Thom map
`x ↦ π_*(x ⌢ u)` of a possibly non-orientable vector bundle `E` with Thom pair `(E, E₀)`, when the
Thom class `u` is a relative class with coefficients in the orientation system of `E`
(`TauCeti.twistedHomologyThomMap`).

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.ιTwistedChainComplex_capChain`: the cap product of a simplex and
  a twisted cochain.
* `TauCeti.LocalCoefficientSystem.twistedCap`: the cap product on twisted (co)homology, with
  `TauCeti.LocalCoefficientSystem.twistedCap_homologyπ` computing it on classes of cycles and
  cocycles, `TauCeti.LocalCoefficientSystem.twistedCap_coefficient_naturality` its naturality in the
  coefficient systems and `TauCeti.LocalCoefficientSystem.twistedCap_space_naturality` the
  projection formula.
* `TopPair.twistedCap`: the relative cap product, with `TopPair.twistedCap_homologyπ`,
  `TopPair.twistedCap_twistedCohomologyπ`, `TopPair.twistedCap_coefficient_naturality` and the
  projection formula `TopPair.twistedCap_space_naturality`.
* `TopPair.twistedPushforwardCap`: a change of coefficients `K ⟶ L ⊗ N`, the relative cap
  product with a class twisted by the pull-back of `L` and a push-forward, with its naturality in
  maps of pairs `TopPair.twistedPushforwardCap_naturality`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.3 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X : TopCat.{v}}

section Cap

variable (L K : LocalCoefficientSystem.{max v w, v, max v w} R X) (M : ModuleCat.{max v w} R)

/-- **The cap product of a simplex and a twisted cochain**: a cochain `φ` of degree `p` caps the
singular `(p + q)`-simplex `σ`, with a coefficient of `L ⊗ K` at its initial vertex, to the back
`q`-face of `σ`. The coefficient of `L` is evaluated by `φ` on the front `p`-face, which has the
same initial vertex, and the coefficient of `K` is transported along the edge from vertex `0` to
vertex `p`, the initial vertex of the back face. -/
lemma ιTwistedChainComplex_capChain (p q n : ℕ) (h : p + q = n)
    (φ : L.twistedChainComplex.X p ⟶ M) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex (L ⊗ K) n σ ≫
        TauCeti.ChainComplex.capChain R (twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ =
      ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
          ιTwistedChainComplex L p
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
        K.map (vertexTransport (SimplexCategory.subinterval p q (by omega)).op σ)) ≫
        ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K) q
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  -- The cochain kills every bidegree except `(p, q)`.
  rw [TauCeti.ChainComplex.capChain_apply,
    ιTwistedChainComplex_twistedAlexanderWhitneyDiagonal_f_comp_of_ne_left L K p q n h σ _
      (fun _ _ hij hi ↦ TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left _ _ _ hij hi),
    TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc, Category.assoc,
    Category.comp_id, ← tensorHom_comp_whiskerLeft_assoc,
    -- `M` acts on the summand of the back face.
    whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f]

/-- **The cap product of twisted cohomology and twisted homology**,
`Hᵖ(X; L, M) ⟶ (Hₙ(X; L ⊗ K) ⟶ H_q(X; M ⊗ K))` for `p + q = n`: the cap product along the twisted
Alexander–Whitney diagonal and the action of `M` on the chains twisted by `K`. It is `R`-linear in
the cohomology class. -/
def twistedCap (p q n : ℕ) (h : p + q = n) :
    L.twistedCohomology R M p →ₗ[R]
      ((L ⊗ K).twistedHomology n ⟶ ((constantFunctor X).obj M ⊗ K).twistedHomology q) :=
  TauCeti.ChainComplex.cap R (twistedAlexanderWhitneyDiagonal L K) (twistedChainComplexAction M K)
    p q n h

/-- The cap product of the classes of a twisted cycle and a twisted cocycle is the class of their
cap product. -/
@[reassoc (attr := simp)]
lemma twistedCap_homologyπ (p q n : ℕ) (h : p + q = n)
    (φ : (L.twistedCochainComplex R M).cycles p) :
    (L ⊗ K).twistedChainComplex.homologyπ n ≫
        twistedCap L K M p q n h ((L.twistedCochainComplex R M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles R (twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ ≫
        ((constantFunctor X).obj M ⊗ K).twistedChainComplex.homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

variable {L K M} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- **Naturality of the cap product in the coefficient systems**: for morphisms `η : L ⟶ L'` and
`θ : K ⟶ K'`, capping with the pulled-back class `η^* α` and changing coefficients along `θ` is
changing coefficients along `η ⊗ θ` and capping with `α`. -/
lemma twistedCap_coefficient_naturality (η : L ⟶ L') (θ : K ⟶ K') (p q n : ℕ) (h : p + q = n)
    (α : L'.twistedCohomology R M p) :
    twistedCap L K M p q n h (twistedCohomologyCoefficientMap R M η p α) ≫
        twistedHomologyCoefficientMap ((constantFunctor X).obj M ◁ θ) q =
      twistedHomologyCoefficientMap (η ⊗ₘ θ) n ≫ twistedCap L' K' M p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (twistedAlexanderWhitneyDiagonal_naturality η θ) (twistedChainComplexAction_naturality θ)
    p q n h α

section Space

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)
  (M : ModuleCat.{max v w} R)

/-- **The projection formula for the twisted cap product**: for `f : X ⟶ Y`, a class `α` of
`Hᵖ(Y; L, M)` and a class `x` of `Hₙ(X; f^*L ⊗ f^*K)`, `f_*(x ⌢ f^*α) = f_*x ⌢ α`, where the
pushforwards are taken after the canonical identifications `f^*L ⊗ f^*K ≅ f^*(L ⊗ K)` and
`M ⊗ f^*K ≅ f^*(M ⊗ K)`. -/
lemma twistedCap_space_naturality (p q n : ℕ) (h : p + q = n) (α : L.twistedCohomology R M p) :
    twistedCap ((pullback f.hom).obj L) ((pullback f.hom).obj K) M p q n h
        (twistedCohomologyMap R M f L p α) ≫
        twistedHomologyCoefficientMap (pullbackConstantTensorIso f.hom M K).hom q ≫
          twistedHomologyMap f ((constantFunctor Y).obj M ⊗ K) q =
      twistedHomologyCoefficientMap (pullbackTensorIso f.hom L K).inv n ≫
        twistedHomologyMap f (L ⊗ K) n ≫ twistedCap L K M p q n h α := by
  have hD : (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K)) ≫ twistedAlexanderWhitneyDiagonal L K =
        twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ twistedChainComplexMap f K) := by
    rw [Category.assoc, twistedAlexanderWhitneyDiagonal_space_naturality,
      ← twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
      twistedChainComplexCoefficientMap_id, Category.id_comp]
  have hcap := TauCeti.ChainComplex.cap_naturality (k := R) (twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K)
    (twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K))
    (twistedChainComplexAction M ((pullback f.hom).obj K))
    (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K))
    (twistedChainComplexMap f L) (twistedChainComplexMap f K)
    (twistedChainComplexCoefficientMap (pullbackConstantTensorIso f.hom M K).hom ≫
      twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K)) hD
    (twistedChainComplexAction_space_naturality f M K) p q n h α
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc] at hcap
  exact hcap

end Space

end Cap

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] (P : TopPair.{v})
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R P.fst) (M : ModuleCat.{max v w} R)

/-- **The relative cap product with local coefficients**,
`Hᵖ(X, A; L, M) ⟶ (Hₙ(X, A; L ⊗ K) ⟶ H_q(X; M ⊗ K))` for `p + q = n`: a relative cochain vanishes
on the front faces of the simplices of `A`, so capping with it descends to relative chains. It is
`R`-linear in the cohomology class. -/
def twistedCap (p q n : ℕ) (h : p + q = n) :
    P.twistedCohomology L R M p →ₗ[R]
      (P.twistedHomology (L ⊗ K) n ⟶ ((constantFunctor P.fst).obj M ⊗ K).twistedHomology q) :=
  TauCeti.ChainComplex.cap R (P.twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K) p q n h

/-- The relative cap product of the classes of a relative twisted cycle and a relative twisted
cocycle is the class of their cap product. -/
@[reassoc (attr := simp)]
lemma twistedCap_homologyπ (p q n : ℕ) (h : p + q = n)
    (φ : (P.twistedCochainComplex L R M).cycles p) :
    (P.twistedChainComplex (L ⊗ K)).homologyπ n ≫
        P.twistedCap L K M p q n h ((P.twistedCochainComplex L R M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles R (P.twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ ≫
        ((constantFunctor P.fst).obj M ⊗ K).twistedChainComplex.homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **The relative and absolute cap products agree**: capping with the image in `Hᵖ(X; L, M)` of a
relative class `α` is passing to relative homology and capping with `α`. -/
lemma twistedCap_twistedCohomologyπ (p q n : ℕ) (h : p + q = n)
    (α : P.twistedCohomology L R M p) :
    LocalCoefficientSystem.twistedCap L K M p q n h (P.twistedCohomologyπ L R M p α) =
      P.twistedHomologyπ (L ⊗ K) n ≫ P.twistedCap L K M p q n h α := by
  have hcap := TauCeti.ChainComplex.cap_naturality (k := R) (P.twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K) (L.twistedAlexanderWhitneyDiagonal K)
    (twistedChainComplexAction M K) (P.twistedChainComplexπ (L ⊗ K)) (P.twistedChainComplexπ L)
    (𝟙 _) (𝟙 _) (P.twistedChainComplexπ_twistedAlexanderWhitneyDiagonal L K) (by simp) p q n h α
  rwa [HomologicalComplex.homologyMap_id, Category.comp_id] at hcap

variable {P L K M} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R P.fst}

/-- **Naturality of the relative cap product in the coefficient systems**: for morphisms
`η : L ⟶ L'` and `θ : K ⟶ K'`, capping with the pulled-back relative class `η^* α` and changing
coefficients along `θ` is changing relative coefficients along `η ⊗ θ` and capping with `α`. -/
lemma twistedCap_coefficient_naturality (η : L ⟶ L') (θ : K ⟶ K') (p q n : ℕ) (h : p + q = n)
    (α : P.twistedCohomology L' R M p) :
    P.twistedCap L K M p q n h (P.twistedCohomologyCoefficientMap R M η p α) ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap ((constantFunctor P.fst).obj M ◁ θ) q =
      P.twistedHomologyCoefficientMap (η ⊗ₘ θ) n ≫ P.twistedCap L' K' M p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (TopPair.twistedAlexanderWhitneyDiagonal_naturality η θ)
    (twistedChainComplexAction_naturality θ) p q n h α

section Space

variable {Q : TopPair.{v}} (f : P ⟶ Q)
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R Q.fst) (M : ModuleCat.{max v w} R)

/-- **The projection formula for the relative twisted cap product**: for a map of pairs
`f : (X, A) ⟶ (Y, B)`, a class `α` of `Hᵖ(Y, B; L, M)` and a class `x` of
`Hₙ(X, A; f^*L ⊗ f^*K)`, `f_*(x ⌢ f^*α) = f_*x ⌢ α`, where the pushforwards are taken after the
canonical identifications `f^*L ⊗ f^*K ≅ f^*(L ⊗ K)` and `M ⊗ f^*K ≅ f^*(M ⊗ K)`. -/
lemma twistedCap_space_naturality (p q n : ℕ) (h : p + q = n)
    (α : Q.twistedCohomology L R M p) :
    P.twistedCap ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)
        ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K) M p q n h
        (twistedCohomologyMap R M f L p α) ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          (pullbackConstantTensorIso (Hom.fst f).hom M K).hom q ≫
          LocalCoefficientSystem.twistedHomologyMap (Hom.fst f)
            ((constantFunctor Q.fst).obj M ⊗ K) q =
      P.twistedHomologyCoefficientMap (pullbackTensorIso (Hom.fst f).hom L K).inv n ≫
        twistedHomologyMap f (L ⊗ K) n ≫ Q.twistedCap L K M p q n h α := by
  have hD : (P.twistedChainComplexCoefficientMap (pullbackTensorIso (Hom.fst f).hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K)) ≫ Q.twistedAlexanderWhitneyDiagonal L K =
        P.twistedAlexanderWhitneyDiagonal
            ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)
            ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ
            LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) K) := by
    rw [Category.assoc, twistedAlexanderWhitneyDiagonal_space_naturality,
      ← P.twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
      P.twistedChainComplexCoefficientMap_id, Category.id_comp]
  have hcap := TauCeti.ChainComplex.cap_naturality (k := R) (Q.twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K)
    (P.twistedAlexanderWhitneyDiagonal ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)
      ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K))
    (twistedChainComplexAction M ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K))
    (P.twistedChainComplexCoefficientMap (pullbackTensorIso (Hom.fst f).hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K))
    (twistedChainComplexMap f L) (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) K)
    (LocalCoefficientSystem.twistedChainComplexCoefficientMap
        (pullbackConstantTensorIso (Hom.fst f).hom M K).hom ≫
      LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f)
        ((constantFunctor Q.fst).obj M ⊗ K)) hD
    (twistedChainComplexAction_space_naturality (Hom.fst f) M K) p q n h α
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc] at hcap
  exact hcap

end Space

section PushforwardCap

variable {Y : TopCat.{v}} (p₀ : P.fst ⟶ Y) (L : LocalCoefficientSystem.{max v w, v, max v w} R Y)
  {K N : LocalCoefficientSystem.{max v w, v, max v w} R Y} (ε : K ⟶ L ⊗ N)

/-- **The relative cap product followed by push-forward, with local coefficients**: for a pair
`P = (X, A)`, a map `p₀ : X ⟶ Y`, local systems `L`, `K` and `N` on `Y` with a morphism
`ε : K ⟶ L ⊗ N`, and a relative class `u ∈ Hⁿ(X, A; p₀^*L, R)`, the morphism
`Hₘ(X, A; p₀^*K) ⟶ Hₚ(Y; N)`, `x ↦ p₀_*(ε_* x ⌢ u)` (`n + p = m`), `R`-linear in `u`. The morphism
`ε` reads a chain twisted by `p₀^*K` as a chain twisted by `p₀^*L ⊗ p₀^*N`; capping with `u`
consumes the first factor. For a copairing `R ⟶ L ⊗ L` tensored with a local system `J` on `Y`,
this is a morphism `Hₘ(X, A; p₀^*J) ⟶ Hₚ(Y; L ⊗ J)`. For the Thom pair `(E, E₀)` of a vector
bundle, its projection and the orientation local system `o(E)`, whose tensor square is constant,
this is the homology Thom map with coefficients twisted by `o(E)`
(`TauCeti.twistedHomologyThomMap`). -/
def twistedPushforwardCap (n p m : ℕ) (h : n + p = m) :
    P.twistedCohomology ((LocalCoefficientSystem.pullback p₀.hom).obj L) R (ModuleCat.of R R) n
      →ₗ[R] (P.twistedHomology ((LocalCoefficientSystem.pullback p₀.hom).obj K) m ⟶
        N.twistedHomology p) :=
  Linear.rightComp R _
      (LocalCoefficientSystem.twistedHomologyCoefficientMap
          (constantTensorIso ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom p ≫
        LocalCoefficientSystem.twistedHomologyMap p₀ N p) ∘ₗ
    Linear.leftComp R _ (P.twistedHomologyCoefficientMap
      ((LocalCoefficientSystem.pullback p₀.hom).map ε ≫ (pullbackTensorIso p₀.hom L N).hom) m) ∘ₗ
    P.twistedCap ((LocalCoefficientSystem.pullback p₀.hom).obj L)
      ((LocalCoefficientSystem.pullback p₀.hom).obj N) (ModuleCat.of R R) n p m h

/-- `TopPair.twistedPushforwardCap` is the change of coefficients along `ε`, the relative cap
product with `u`, the identification `R ⊗ p₀^*N ≅ p₀^*N` and the push-forward along `p₀`. -/
lemma twistedPushforwardCap_apply {n p m : ℕ} (h : n + p = m)
    (u : P.twistedCohomology ((LocalCoefficientSystem.pullback p₀.hom).obj L) R
      (ModuleCat.of R R) n) :
    P.twistedPushforwardCap p₀ L ε n p m h u =
      P.twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback p₀.hom).map ε ≫ (pullbackTensorIso p₀.hom L N).hom) m ≫
        P.twistedCap ((LocalCoefficientSystem.pullback p₀.hom).obj L)
          ((LocalCoefficientSystem.pullback p₀.hom).obj N) (ModuleCat.of R R) n p m h u ≫
          LocalCoefficientSystem.twistedHomologyCoefficientMap
            (constantTensorIso ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom p ≫
            LocalCoefficientSystem.twistedHomologyMap p₀ N p :=
  (rfl)

variable {P' : TopPair.{v}} (φ : P' ⟶ P)

/-- Pulling `ε` back along `φ` and then along `p₀`, or along their composite, gives the same change
of coefficients on `X'`. -/
private lemma twistedHomologyCoefficientMap_pullback_comp (m : ℕ) :
    P'.twistedHomologyCoefficientMap ((pullbackCompIso (Hom.fst φ).hom p₀.hom).inv.app K) m ≫
      P'.twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullback (Hom.fst φ ≫ p₀).hom).map ε ≫
          (pullbackTensorIso (Hom.fst φ ≫ p₀).hom L N).hom) m ≫
      P'.twistedHomologyCoefficientMap
        ((pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app L ⊗ₘ
          (pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app N) m =
      P'.twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullback (Hom.fst φ).hom).map
          ((LocalCoefficientSystem.pullback p₀.hom).map ε ≫
            (pullbackTensorIso p₀.hom L N).hom)) m ≫
        P'.twistedHomologyCoefficientMap
          (pullbackTensorIso (Hom.fst φ).hom ((LocalCoefficientSystem.pullback p₀.hom).obj L)
            ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom m := by
  simp only [← P'.twistedHomologyCoefficientMap_comp, Functor.map_comp, Category.assoc,
    TopCat.hom_comp]
  congr 1
  -- Move `ε` past `(p₀ ∘ φ)^* ≅ φ^* p₀^*`, then compare the two tensor comparisons.
  rw [← NatTrans.naturality_assoc, pullbackTensorIso_pullbackCompIso, Functor.comp_map]

/-- The identification `R ⊗ p₀^*N ≅ p₀^*N` is compatible with pulling back along `φ`. -/
private lemma twistedHomologyCoefficientMap_constantTensorIso_pullback (p : ℕ) :
    LocalCoefficientSystem.twistedHomologyCoefficientMap
        ((constantFunctor P'.fst).obj (ModuleCat.of R R) ◁
          (pullbackCompIso (Hom.fst φ).hom p₀.hom).inv.app N) p ≫
      LocalCoefficientSystem.twistedHomologyCoefficientMap
        (constantTensorIso ((LocalCoefficientSystem.pullback (Hom.fst φ ≫ p₀).hom).obj N)).hom p ≫
      LocalCoefficientSystem.twistedHomologyCoefficientMap
        ((pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app N) p =
      LocalCoefficientSystem.twistedHomologyCoefficientMap
        (pullbackConstantTensorIso (Hom.fst φ).hom (ModuleCat.of R R)
          ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom p ≫
      LocalCoefficientSystem.twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullback (Hom.fst φ).hom).map
          (constantTensorIso ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom) p := by
  simp only [← LocalCoefficientSystem.twistedHomologyCoefficientMap_comp, TopCat.hom_comp]
  congr 1
  -- Move the identification `R ⊗ K ≅ K` past `(p₀ ∘ φ)^*N ≅ φ^* p₀^*N`, then pull it back.
  rw [constantTensorIso_hom_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id,
    pullbackConstantTensorIso_hom_map_constantTensorIso_hom]
  -- Both sides are the identification for `(pullback p₀ ⋙ pullback φ).obj N`, which is
  -- `(pullback φ).obj ((pullback p₀).obj N)` by `Functor.comp_obj`.
  rfl

/-- **Naturality of the twisted push-forward cap product in maps of pairs**: for a map of pairs
`φ : (X', A') ⟶ (X, A)` and `u ∈ Hⁿ(X, A; p₀^*L, R)`, pushing a class forward along `φ` and then
capping with `u` and pushing forward along `p₀` is capping with `φ^*u` and pushing forward along
`p₀ ∘ φ`, after identifying `φ^*p₀^*K` with `(p₀ ∘ φ)^*K` and `φ^*p₀^*L` with `(p₀ ∘ φ)^*L`. -/
lemma twistedPushforwardCap_naturality {n p m : ℕ} (h : n + p = m)
    (u : P.twistedCohomology ((LocalCoefficientSystem.pullback p₀.hom).obj L) R
      (ModuleCat.of R R) n) :
    P'.twistedHomologyCoefficientMap ((pullbackCompIso (Hom.fst φ).hom p₀.hom).inv.app K) m ≫
      P'.twistedPushforwardCap (Hom.fst φ ≫ p₀) L ε n p m h
        (P'.twistedCohomologyCoefficientMap R (ModuleCat.of R R)
          ((pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app L) n
          (twistedCohomologyMap R (ModuleCat.of R R) φ _ n u)) =
      twistedHomologyMap φ ((LocalCoefficientSystem.pullback p₀.hom).obj K) m ≫
        P.twistedPushforwardCap p₀ L ε n p m h u := by
  rw [twistedPushforwardCap_apply, twistedPushforwardCap_apply]
  -- The cap product with `φ^*u`, read through `φ^*p₀^*L ≅ (p₀ ∘ φ)^*L` and its analogue for `N`.
  have h₁ := congrArg (· ≫ LocalCoefficientSystem.twistedHomologyCoefficientMap
    ((constantFunctor P'.fst).obj (ModuleCat.of R R) ◁
      (pullbackCompIso (Hom.fst φ).hom p₀.hom).inv.app N) p)
    (P'.twistedCap_coefficient_naturality
      (L := (LocalCoefficientSystem.pullback (Hom.fst φ ≫ p₀).hom).obj L)
      (K := (LocalCoefficientSystem.pullback (Hom.fst φ ≫ p₀).hom).obj N)
      ((pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app L)
      ((pullbackCompIso (Hom.fst φ).hom p₀.hom).hom.app N) n p m h
      (twistedCohomologyMap R (ModuleCat.of R R) φ _ n u))
  simp only [Category.assoc] at h₁
  rw [← LocalCoefficientSystem.twistedHomologyCoefficientMap_comp,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app] at h₁
  -- `Iso.hom_inv_id_app` gives `𝟙` on `(pullback (p₀.hom.comp φ.hom)).obj N`, the domain of
  -- `pullbackCompIso`, while the whiskering's implicit objects use `(pullback (φ ≫ p₀).hom).obj N`.
  -- These agree by `TopCat.hom_comp`, which is `rfl` but not reducible; rewriting with it first
  -- fails because the implicit objects of `twistedHomologyCoefficientMap` would also change.
  erw [MonoidalCategory.whiskerLeft_id] at h₁
  rw [LocalCoefficientSystem.twistedHomologyCoefficientMap_id, Category.comp_id] at h₁
  -- The projection formula for `φ`, with the pull-back of `p₀^*L ⊗ p₀^*N` unfolded.
  have h₂ := congrArg (P'.twistedHomologyCoefficientMap (pullbackTensorIso (Hom.fst φ).hom
    ((LocalCoefficientSystem.pullback p₀.hom).obj L)
    ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom m ≫ ·)
    (twistedCap_space_naturality φ ((LocalCoefficientSystem.pullback p₀.hom).obj L)
      ((LocalCoefficientSystem.pullback p₀.hom).obj N) (ModuleCat.of R R) n p m h u)
  simp only [twistedHomologyCoefficientMap_hom_inv_id_assoc] at h₂
  rw [reassoc_of% TopPair.twistedHomologyMap_naturality φ
      (L := (LocalCoefficientSystem.pullback p₀.hom).obj K), ← reassoc_of% h₂,
    reassoc_of% LocalCoefficientSystem.twistedHomologyMap_naturality (Hom.fst φ)
      (constantTensorIso ((LocalCoefficientSystem.pullback p₀.hom).obj N)).hom p,
    LocalCoefficientSystem.twistedHomologyMap_comp (Hom.fst φ) p₀ N p, h₁]
  simp only [Category.assoc]
  rw [reassoc_of% twistedHomologyCoefficientMap_pullback_comp,
    reassoc_of% twistedHomologyCoefficientMap_constantTensorIso_pullback]
  -- The two sides differ only by `(pullback p₀ ⋙ pullback φ).obj L` and its analogue for `N`, which
  -- are `(pullback φ).obj ((pullback p₀).obj L)` and its analogue by `Functor.comp_obj`.
  rfl

end PushforwardCap

end TopPair
