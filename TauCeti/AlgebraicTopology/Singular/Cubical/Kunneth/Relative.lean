/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth
public import TauCeti.Topology.Category.TopPair

/-!
# The relative cubical Eilenberg–Zilber and Künneth theorems

For a space `X` and a topological pair `P = (Y, B)`, the cubical cross product
`N(X) ⊗ N(Y) ⟶ N(X × Y)` carries `N(X) ⊗ N(B)` into `N(X × B)`, so it descends to the **relative
cubical cross product** (`TauCeti.cubicalCrossProductRel`)

`N(X) ⊗ N(Y, B) ⟶ N(X × Y, X × B)`,

on the relative normalized cubical chains of the pair `X × (Y, B) = (X × Y, X × B)`
(`TopPair.prodLeft`). It sends `a ⊗ [b]` to `[a × b]`
(`TauCeti.cubicalCrossProductRel_f_ιTensorObj_tmul`) and is natural in `X` and in maps of pairs
(`TauCeti.cubicalCrossProductRel_naturality`).

The normalized cubical chains are projective, hence flat, so tensoring with `N(X)` preserves the
short exact sequence `N(B) ⟶ N(Y) ⟶ N(Y, B)`. The three cross products form a morphism from this
tensored sequence to the sequence `N(X × B) ⟶ N(X × Y) ⟶ N(X × Y, X × B)` of the product pair
(`TauCeti.cubicalCrossProductShortComplexMap`). The absolute cross products are
quasi-isomorphisms by the cubical Eilenberg–Zilber theorem, so by the five lemma, applied to the
long exact homology sequences, so is the relative one
(`TauCeti.quasiIso_cubicalCrossProductRel`). This is the **relative Eilenberg–Zilber theorem**, with
the pair in the second factor.

Consequently the relative Künneth map
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, X × B; k)`
(`TauCeti.cubicalHomologyKunnethRel`) is an isomorphism whenever the algebraic Künneth map of the
chain complexes is, for instance over a field (`TauCeti.isIso_cubicalHomologyKunnethRel`). The
connecting morphism of the pair `X × (Y, B)` sends `x × y` to `(-1)ᵖ x × δ y` for `x ∈ Hₚ(X)`
(`TauCeti.homologyCross_comp_homologyMap_cubicalCrossProductRel_comp_cubicalHomologyδ`): the
boundary of a product with a relative class is the product with its boundary.

## Main definitions

* `TauCeti.cubicalCrossProductRel k X P`: the relative cross product
  `N(X) ⊗ N(Y, B) ⟶ N(X × Y, X × B)`.
* `TauCeti.cubicalCrossProductShortComplexMap k X P`: the morphism of short exact sequences given
  by the absolute and relative cross products.
* `TauCeti.cubicalHomologyKunnethRel k X P n`: the relative Künneth map of cubical homology.

## Main results

* `TauCeti.quasiIso_cubicalCrossProductRel`: the relative cross product is a quasi-isomorphism.
* `TauCeti.isIso_cubicalHomologyKunnethRel`: the relative Künneth theorem.
* `TauCeti.homologyCross_comp_homologyMap_cubicalCrossProductRel_comp_cubicalHomologyδ`: the
  connecting morphism of `X × (Y, B)` on a relative cross product.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Section 3.B, the relative cross product and the relative
  Künneth formula.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits

universe u

namespace TauCeti

variable (k : Type u) [CommRing k] (X : TopCat.{u}) (P : TopPair.{u})

/-- Tensoring with a module of normalized cubical chains preserves finite limits, since the
chains are projective and so flat. -/
instance preservesFiniteLimits_tensorLeft_normalizedCubicalChainComplex_X (p : ℕ) :
    PreservesFiniteLimits (tensorLeft (((normalizedCubicalChainComplex k).obj X).X p)) :=
  inferInstanceAs
    (PreservesFiniteLimits (tensorLeft (ModuleCat.of k (NormalizedCubicalChain X k p))))

/-- Tensoring on the left with `N(X)` preserves the short exact sequence
`N(B) ⟶ N(Y) ⟶ N(Y, B)` of normalized cubical chains of a pair `(Y, B)`. -/
theorem shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex :
    (tensorLeftShortComplex ((normalizedCubicalChainComplex k).obj X)
      (P.cubicalChainComplexShortComplex k)).ShortExact :=
  shortExact_tensorLeftShortComplex_of_preservesFiniteLimits _
    (P.shortExact_cubicalChainComplexShortComplex k) fun n ↦
      (Finset.antidiagonal n).finite_toSet.subset fun x hx ↦ by simpa using hx

/-- The cross product carries `N(X) ⊗ N(B)` into the chains of `X × B`, which vanish in the
relative chains of `X × (Y, B)`. -/
private theorem cubicalCrossProduct_cokernel_condition :
    (normalizedCubicalChainComplex k).obj X ◁ (normalizedCubicalChainComplex k).map P.map ≫
        cubicalCrossProduct k X P.fst ≫ cokernel.π ((normalizedCubicalChainComplex k).map
          (P.prodLeft X).map) = 0 := by
  have h := cubicalCrossProduct_naturality (R := k) (𝟙 X) P.map
  rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h
  have hc := cokernel.condition ((normalizedCubicalChainComplex k).map (P.prodLeft X).map)
  exact ((reassoc_of% h) _).trans
    ((congrArg (cubicalCrossProduct k X P.snd ≫ ·) hc).trans Limits.comp_zero)

/-- **The relative cubical cross product** `N(X) ⊗ N(Y, B) ⟶ N(X × Y, X × B)` of a space `X` and
a pair `P = (Y, B)`, induced by the cross product `N(X) ⊗ N(Y) ⟶ N(X × Y)` on the cokernels; it
is characterized by `TauCeti.whiskerLeft_π_cubicalCrossProductRel`. -/
def cubicalCrossProductRel :
    (normalizedCubicalChainComplex k).obj X ⊗ P.cubicalChainComplex k ⟶
      (P.prodLeft X).cubicalChainComplex k :=
  have hS := shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X P
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (cubicalCrossProduct_cokernel_condition k X P))

/-- The relative cross product is induced by the cross product: on `N(X) ⊗ N(Y)` it is the cross
product followed by the projection to the relative chains of `X × (Y, B)`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_π_cubicalCrossProductRel :
    (normalizedCubicalChainComplex k).obj X ◁ cokernel.π ((normalizedCubicalChainComplex k).map
        P.map) ≫ cubicalCrossProductRel k X P =
      cubicalCrossProduct k X P.fst ≫
        cokernel.π ((normalizedCubicalChainComplex k).map (P.prodLeft X).map) :=
  have hS := shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X P
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- On the summand of bidegree `(p, q)`, the relative cross product of a chain of `X` and the class
of a chain of `Y` is the class of their cross product. -/
@[reassoc]
theorem whiskerLeft_π_f_ι_cubicalCrossProductRel_f {p q n : ℕ} (h : p + q = n) :
    (((normalizedCubicalChainComplex k).obj X).X p ◁
        (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f q) ≫
      ιTensorObj ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) p q n h ≫
        (cubicalCrossProductRel k X P).f n =
      cubicalCrossProductSummand k X P.fst p q n h ≫
        (cokernel.π ((normalizedCubicalChainComplex k).map (P.prodLeft X).map)).f n := by
  rw [← ι_whiskerLeft_assoc, ← comp_f]
  exact (congrArg (ιTensorObj _ _ p q n h ≫ ·)
    ((congrArg (fun φ ↦ φ.f n) (whiskerLeft_π_cubicalCrossProductRel k X P)).trans
      (comp_f _ _ n))).trans (ι_cubicalCrossProduct_f_assoc (R := k) (X := X) (Y := P.fst) h _)

/-- The relative cross product sends `a ⊗ [b]` to `[a × b]`, reindexed along `p + q = n`, for
normalized chains `a` of `X` and `b` of `Y`. -/
theorem cubicalCrossProductRel_f_ιTensorObj_tmul {p q n : ℕ} (h : p + q = n)
    (a : NormalizedCubicalChain X k p) (b : NormalizedCubicalChain P.fst k q) :
    (cubicalCrossProductRel k X P).f n
        (ιTensorObj ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) p q n h
          (a ⊗ₜ (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f q b)) =
      (cokernel.π ((normalizedCubicalChainComplex k).map (P.prodLeft X).map)).f n
        (NormalizedCubicalChain.cast k h
          (NormalizedCubicalChain.crossProduct X P.fst k p q a b)) := by
  have := ConcreteCategory.congr_hom (whiskerLeft_π_f_ι_cubicalCrossProductRel_f k X P h)
    (a ⊗ₜ b)
  exact this.trans (congrArg _ (cubicalCrossProductSummand_apply k X P.fst p q n h a b))

/-- The morphism of short exact sequences from `N(X) ⊗ (N(B) ⟶ N(Y) ⟶ N(Y, B))` to
`N(X × B) ⟶ N(X × Y) ⟶ N(X × Y, X × B)` given by the absolute and relative cross products. -/
def cubicalCrossProductShortComplexMap :
    tensorLeftShortComplex ((normalizedCubicalChainComplex k).obj X)
        (P.cubicalChainComplexShortComplex k) ⟶
      (P.prodLeft X).cubicalChainComplexShortComplex k where
  τ₁ := cubicalCrossProduct k X P.snd
  τ₂ := cubicalCrossProduct k X P.fst
  τ₃ := cubicalCrossProductRel k X P
  comm₁₂ := by
    have h := cubicalCrossProduct_naturality (R := k) (𝟙 X) P.map
    rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h
    exact h.symm
  comm₂₃ := (whiskerLeft_π_cubicalCrossProductRel k X P).symm

@[simp]
theorem cubicalCrossProductShortComplexMap_τ₁ :
    (cubicalCrossProductShortComplexMap k X P).τ₁ = cubicalCrossProduct k X P.snd :=
  (rfl)

@[simp]
theorem cubicalCrossProductShortComplexMap_τ₂ :
    (cubicalCrossProductShortComplexMap k X P).τ₂ = cubicalCrossProduct k X P.fst :=
  (rfl)

@[simp]
theorem cubicalCrossProductShortComplexMap_τ₃ :
    (cubicalCrossProductShortComplexMap k X P).τ₃ = cubicalCrossProductRel k X P :=
  (rfl)

/-- **Naturality of the relative cross product** in the space and in maps of pairs. -/
@[reassoc]
theorem cubicalCrossProductRel_naturality {X' : TopCat.{u}} {P' : TopPair.{u}} (g : X ⟶ X')
    (f : P ⟶ P') :
    ((normalizedCubicalChainComplex k).map g ⊗ₘ TopPair.cubicalChainComplexMap k f) ≫
        cubicalCrossProductRel k X' P' =
      cubicalCrossProductRel k X P ≫
        TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap f g) := by
  have hS := shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X P
  have : Epi ((normalizedCubicalChainComplex k).obj X ◁
      cokernel.π ((normalizedCubicalChainComplex k).map P.map)) := hS.epi_g
  refine (cancel_epi ((normalizedCubicalChainComplex k).obj X ◁
      cokernel.π ((normalizedCubicalChainComplex k).map P.map))).1 ?_
  have h₁ : (normalizedCubicalChainComplex k).obj X ◁
        cokernel.π ((normalizedCubicalChainComplex k).map P.map) ≫
          ((normalizedCubicalChainComplex k).map g ⊗ₘ TopPair.cubicalChainComplexMap k f) =
      ((normalizedCubicalChainComplex k).map g ⊗ₘ
        (normalizedCubicalChainComplex k).map (TopPair.Hom.fst f)) ≫
          (normalizedCubicalChainComplex k).obj X' ◁
            cokernel.π ((normalizedCubicalChainComplex k).map P'.map) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, TopPair.π_cubicalChainComplexMap]
  calc _ = ((normalizedCubicalChainComplex k).map g ⊗ₘ
        (normalizedCubicalChainComplex k).map (TopPair.Hom.fst f)) ≫
          cubicalCrossProduct k X' P'.fst ≫
            cokernel.π ((normalizedCubicalChainComplex k).map (P'.prodLeft X').map) := by
        rw [reassoc_of% h₁, whiskerLeft_π_cubicalCrossProductRel]
    _ = cubicalCrossProduct k X P.fst ≫
          (normalizedCubicalChainComplex k).map (g ⊗ₘ TopPair.Hom.fst f) ≫
            cokernel.π ((normalizedCubicalChainComplex k).map (P'.prodLeft X').map) :=
        cubicalCrossProduct_naturality_assoc _ _ _
    _ = cubicalCrossProduct k X P.fst ≫
          cokernel.π ((normalizedCubicalChainComplex k).map (P.prodLeft X).map) ≫
            TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap f g) :=
        congrArg (cubicalCrossProduct k X P.fst ≫ ·)
          (TopPair.π_cubicalChainComplexMap k (TopPair.prodLeftMap f g)).symm
    _ = _ := (whiskerLeft_π_cubicalCrossProductRel_assoc k X P _).symm

/-- **The relative cubical Eilenberg–Zilber theorem**: the relative cross product
`N(X) ⊗ N(Y, B) ⟶ N(X × Y, X × B)` is a quasi-isomorphism. By the five lemma, this follows from
the absolute Eilenberg–Zilber theorem for `X × B` and `X × Y`. -/
instance quasiIso_cubicalCrossProductRel : QuasiIso (cubicalCrossProductRel k X P) :=
  HomologySequence.quasiIso_τ₃ (cubicalCrossProductShortComplexMap k X P)
    (shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X P)
    ((P.prodLeft X).shortExact_cubicalChainComplexShortComplex k)
    (inferInstanceAs (QuasiIso (cubicalCrossProduct k X P.snd)))
    (inferInstanceAs (QuasiIso (cubicalCrossProduct k X P.fst)))

/-- The relative cross product induces an isomorphism on homology. -/
instance isIso_homologyMap_cubicalCrossProductRel (n : ℕ) :
    IsIso (homologyMap (cubicalCrossProductRel k X P) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- **The relative Künneth map of cubical homology**,
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, X × B; k)`: the algebraic Künneth map of the
chain complexes `N(X)` and `N(Y, B)` followed by the map induced by the relative cross product. -/
def cubicalHomologyKunnethRel (n : ℕ) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ ((normalizedCubicalChainComplex k).obj X).homology p)
        (fun q ↦ (P.cubicalChainComplex k).homology q) n ⟶
      ((P.prodLeft X).cubicalChainComplex k).homology n :=
  homologyKunneth ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) n ≫
    homologyMap (cubicalCrossProductRel k X P) n

/-- The relative Künneth map is the algebraic Künneth map followed by the map induced by the
relative cross product. -/
theorem cubicalHomologyKunnethRel_def (n : ℕ) :
    cubicalHomologyKunnethRel k X P n =
      homologyKunneth ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) n ≫
        homologyMap (cubicalCrossProductRel k X P) n :=
  (rfl)

/-- The relative Künneth map restricts to the homology cross product followed by the map induced
by the relative cross product on each summand. -/
@[reassoc (attr := simp)]
theorem ι_cubicalHomologyKunnethRel (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj
        (fun p ↦ ((normalizedCubicalChainComplex k).obj X).homology p)
        (fun q ↦ (P.cubicalChainComplex k).homology q) p q n h ≫
      cubicalHomologyKunnethRel k X P n =
      homologyCross ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) p q n h ≫
        homologyMap (cubicalCrossProductRel k X P) n := by
  rw [cubicalHomologyKunnethRel_def, ← Category.assoc, ι_homologyKunneth]

/-- **Naturality of the relative Künneth map** in the space and in maps of pairs. -/
@[reassoc]
theorem cubicalHomologyKunnethRel_naturality {X' : TopCat.{u}} {P' : TopPair.{u}} (g : X ⟶ X')
    (f : P ⟶ P') (n : ℕ) :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ homologyMap ((normalizedCubicalChainComplex k).map g) p)
        (fun q ↦ homologyMap (TopPair.cubicalChainComplexMap k f) q) n ≫
      cubicalHomologyKunnethRel k X' P' n =
      cubicalHomologyKunnethRel k X P n ≫
        homologyMap (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap f g)) n := by
  rw [cubicalHomologyKunnethRel_def, cubicalHomologyKunnethRel_def, ← Category.assoc,
    homologyKunneth_naturality, Category.assoc, ← homologyMap_comp, Category.assoc,
    ← homologyMap_comp, ← cubicalCrossProductRel_naturality,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap]

/-- **The relative Künneth theorem for cubical homology**: if the cycles of `N(X)` and `N(Y, B)`
split off their terms and their homology splits off the cycles, the relative Künneth map
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, X × B; k)` is an isomorphism. -/
theorem isIso_cubicalHomologyKunnethRel
    [∀ p, IsSplitMono (((normalizedCubicalChainComplex k).obj X).iCycles p)]
    [∀ p, IsSplitEpi (((normalizedCubicalChainComplex k).obj X).homologyπ p)]
    [∀ q, IsSplitMono ((P.cubicalChainComplex k).iCycles q)]
    [∀ q, IsSplitEpi ((P.cubicalChainComplex k).homologyπ q)] (n : ℕ) :
    IsIso (cubicalHomologyKunnethRel k X P n) := by
  rw [cubicalHomologyKunnethRel_def]
  infer_instance

/-- **The relative Künneth theorem over a semisimple ring**, for instance a field:
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y, B; k) ≅ Hₙ(X × Y, X × B; k)`. -/
instance isIso_cubicalHomologyKunnethRel_of_isSemisimpleRing [IsSemisimpleRing k] (n : ℕ) :
    IsIso (cubicalHomologyKunnethRel k X P n) :=
  isIso_cubicalHomologyKunnethRel k X P n

/-- **The connecting morphism on a relative cross product**: the connecting morphism
`Hₙ(X × Y, X × B) ⟶ Hₙ₋₁(X × B)` of the pair `X × (Y, B)` sends the relative cross product
`x × y` of `x ∈ Hₚ(X)` and `y ∈ H_q(Y, B)` to `(-1)ᵖ x × δ y`, where `δ y ∈ H_{q-1}(B)` is the
connecting morphism of `(Y, B)`. -/
theorem homologyCross_comp_homologyMap_cubicalCrossProductRel_comp_cubicalHomologyδ
    {p q q' n n' : ℕ} (hq : q' + 1 = q) (h : p + q = n) (h' : p + q' = n') :
    homologyCross ((normalizedCubicalChainComplex k).obj X) (P.cubicalChainComplex k) p q n h ≫
        homologyMap (cubicalCrossProductRel k X P) n ≫
          (P.prodLeft X).cubicalHomologyδ k n n' (by omega) =
      ((-1 : ℤ) ^ p) • ((((normalizedCubicalChainComplex k).obj X).homology p ◁
          P.cubicalHomologyδ k q q' hq) ≫
        homologyCross ((normalizedCubicalChainComplex k).obj X)
          ((normalizedCubicalChainComplex k).obj P.snd) p q' n' h') ≫
          homologyMap (cubicalCrossProduct k X P.snd) n' := by
  have hS := shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X P
  have hδ := HomologySequence.δ_naturality (cubicalCrossProductShortComplexMap k X P) hS
    ((P.prodLeft X).shortExact_cubicalChainComplexShortComplex k) n n' (by simp; omega)
  rw [TopPair.cubicalHomologyδ_def k (P.prodLeft X) n n' (by omega),
    TopPair.cubicalHomologyδ_def k P q q' hq]
  refine (congrArg (_ ≫ ·) hδ.symm).trans ?_
  have : (tensorLeft (((normalizedCubicalChainComplex k).obj X).cycles p)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  rw [← Category.assoc, homologyCross_comp_δ _ (P.shortExact_cubicalChainComplexShortComplex k) hS
    (q' := q') hq h h']
  rw [cubicalCrossProductShortComplexMap_τ₁, ComplexShape.ε_down_ℕ, Preadditive.zsmul_comp]
  push_cast
  simp only [Category.assoc]
  -- `push_cast` writes the sign `(-1) ^ p` with the monoid power instance of `ℤ`, which `congr`
  -- identifies with the power in the statement
  congr 1

end TauCeti
