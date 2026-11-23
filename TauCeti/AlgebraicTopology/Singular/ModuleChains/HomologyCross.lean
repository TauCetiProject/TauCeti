/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# The bilinear cross product with coefficients in a commutative ring

The singular homology cross product lands in homology with coefficients in `k ⊗ k`.
Identifying these coefficients with `k` by multiplication gives a bilinear map on the
homology of the singular chain complexes with coefficients in `k`. This form of the API
lets one use linearity to track multiplicities of parametrized products of cycles.

The construction uses `TopCat.singularHomologyCross` and its naturality, without choosing
cycle representatives or another shuffle map.

The projections of `X × Y` kill cross products with a class of positive degree in the other
factor: `pr₂_* (a × b) = 0` when `a` has positive degree
(`TopCat.singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero`), and
`pr₁_* (a × b) = 0` when `b` has positive degree
(`TopCat.singularHomologyMap_fst_singularHomologyCrossBilinear_eq_zero`). The projection factors
through the product with a point, whose homology vanishes in positive degrees. For instance,
every class of `H₂(S¹ × Y; k)` in the image of `[S¹] × H₁(Y; k)` maps to zero in `H₂(Y; k)`, so
every class pulled back from `Y` along the projection vanishes on it.

For arbitrary module coefficients `R` and `S`, the cross product
`Hᵢ(X; R) ⊗ Hⱼ(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)` is natural for maps of both factors on pure tensors,
`(f × g)_*(α × β) = f_* α × g_* β` (`TauCeti.homologyMap_prodMap_singularHomologyCross_tmul`),
and additive in the second factor (`TauCeti.singularHomologyCross_tmul_sub`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.B (the homology cross product).
-/

public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology TauCeti

universe w

namespace TopCat

open TensorProduct

variable (k : Type w) [CommRing k] (X Y : TopCat.{w})

/-- The cross product with coefficients in a commutative ring, as a bilinear map. The
coefficient identification `k ⊗ k ≅ k` is the left unitor, so it multiplies coefficients. -/
def singularHomologyCrossBilinear (p q n : ℕ) (h : p + q = n) :
    ((singularChains k).obj X).homology p →ₗ[k]
      ((singularChains k).obj Y).homology q →ₗ[k]
        ((singularChains k).obj (of (X × Y))).homology n :=
  TensorProduct.curry (singularHomologyCross X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) p q n h ≫
    ((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X ⊗ Y)).hom

/-- The bilinear cross product is the categorical cross product followed by the coefficient
identification `k ⊗ k ≅ k`. -/
theorem singularHomologyCrossBilinear_apply (p q n : ℕ) (h : p + q = n)
    (a : ((singularChains k).obj X).homology p)
    (b : ((singularChains k).obj Y).homology q) :
    singularHomologyCrossBilinear k X Y p q n h a b =
      ((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X ⊗ Y)
        (singularHomologyCross X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) p q n h (a ⊗ₜ b)) := (rfl)

variable {X Y} {X' Y' : TopCat.{w}}

/-- Naturality of the bilinear cross product in both spaces. -/
theorem singularHomologyCrossBilinear_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (p q n : ℕ) (h : p + q = n)
    (a : ((singularChains k).obj X).homology p)
    (b : ((singularChains k).obj Y).homology q) :
    ContinuousMap.singularHomologyMap k n (f.hom.prodMap g.hom)
        (singularHomologyCrossBilinear k X Y p q n h a b) =
      singularHomologyCrossBilinear k X' Y' p q n h
        (ContinuousMap.singularHomologyMap k p f.hom a)
        (ContinuousMap.singularHomologyMap k q g.hom b) := by
  have hn := singularHomologyCross_naturality_assoc f g (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) p q n h
    (((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X' ⊗ Y'))
  rw [NatTrans.naturality] at hn
  -- The categorical coefficient unit is `ModuleCat.of k k`, so its homology objects and
  -- induced maps are precisely those of `singularChains k` and `singularHomologyMap`.
  -- Give the inputs that presentation here so the categorical tensor evaluation lemma matches.
  let a' : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ _)).obj X := a
  let b' : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).obj Y := b
  have he := (congrArg (fun t ↦ t (a' ⊗ₜ[k] b')) hn).symm
  simp only [CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  simp only [singularHomologyCrossBilinear_apply]
  -- TopCat's cartesian monoidal structure defines `X ⊗ Y` as `TopCat.of (X × Y)`
  -- and `f ⊗ g` as `TopCat.ofHom (f.hom.prodMap g.hom)`. This identification accounts
  -- for the remaining definitional equality between the two induced homology maps.
  convert he using 1
  rfl

/-- Naturality of the bilinear cross product in the second space, with the first space fixed. -/
theorem singularHomologyCrossBilinear_naturality_right {A B B' : Type w} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B')) (p q n : ℕ) (h : p + q = n)
    (a : ((singularChains k).obj (of A)).homology p)
    (b : ((singularChains k).obj (of B)).homology q) :
    ContinuousMap.singularHomologyMap k n ((ContinuousMap.id A).prodMap g)
        (singularHomologyCrossBilinear k (of A) (of B) p q n h a b) =
      singularHomologyCrossBilinear k (of A) (of B') p q n h a
        (ContinuousMap.singularHomologyMap k q g b) := by
  simpa only [hom_id, hom_ofHom, ContinuousMap.singularHomologyMap_id] using
    singularHomologyCrossBilinear_naturality k (𝟙 (of A)) (ofHom g) p q n h a b

/-- **The second projection kills cross products with positive-degree classes.** For
`a ∈ Hₚ(A; k)` with `p ≠ 0` and any `b ∈ H_q(B; k)`, the image of `a × b` under the projection
`A × B → B` is zero. -/
@[simp]
theorem singularHomologyMap_snd_singularHomologyCrossBilinear_eq_zero {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] {p q n : ℕ} (h : p + q = n) (hp : p ≠ 0)
    (a : ((singularChains k).obj (of A)).homology p)
    (b : ((singularChains k).obj (of B)).homology q) :
    ContinuousMap.singularHomologyMap k n (ContinuousMap.snd : C(A × B, B))
        (singularHomologyCrossBilinear k (of A) (of B) p q n h a b) = 0 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  let c : C(A, PUnit.{w + 1}) := ContinuousMap.const A PUnit.unit
  have hsnd : (ContinuousMap.snd : C(A × B, B)) =
      (ContinuousMap.snd : C(PUnit.{w + 1} × B, B)).comp (c.prodMap (ContinuousMap.id B)) :=
    ContinuousMap.ext fun _ ↦ rfl
  -- The homology of `singularChains k` is that of the singular homology functor with
  -- coefficients in the monoidal unit `ModuleCat.of k k`, which vanishes in positive degrees
  -- for the contractible point.
  have hc : ContinuousMap.singularHomologyMap k (p + 1) c a = 0 :=
    (ModuleCat.subsingleton_singularHomology_of_contractibleSpace (𝟙_ (ModuleCat.{w} k))
      (of PUnit.{w + 1}) p).elim _ _
  have hnat := singularHomologyCrossBilinear_naturality k (ofHom c)
    (𝟙 (of B)) (p + 1) q n h a b
  simp only [hom_ofHom, hom_id, ContinuousMap.singularHomologyMap_id, hc,
    LinearMap.map_zero₂] at hnat
  rw [hsnd, ContinuousMap.singularHomologyMap_comp, hnat, map_zero]

/-- **The first projection kills cross products with positive-degree classes.** For any
`a ∈ Hₚ(A; k)` and `b ∈ H_q(B; k)` with `q ≠ 0`, the image of `a × b` under the projection
`A × B → A` is zero. -/
@[simp]
theorem singularHomologyMap_fst_singularHomologyCrossBilinear_eq_zero {A B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] {p q n : ℕ} (h : p + q = n) (hq : q ≠ 0)
    (a : ((singularChains k).obj (of A)).homology p)
    (b : ((singularChains k).obj (of B)).homology q) :
    ContinuousMap.singularHomologyMap k n (ContinuousMap.fst : C(A × B, A))
        (singularHomologyCrossBilinear k (of A) (of B) p q n h a b) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  let c : C(B, PUnit.{w + 1}) := ContinuousMap.const B PUnit.unit
  have hfst : (ContinuousMap.fst : C(A × B, A)) =
      (ContinuousMap.fst : C(A × PUnit.{w + 1}, A)).comp ((ContinuousMap.id A).prodMap c) :=
    ContinuousMap.ext fun _ ↦ rfl
  -- As above, `H_{q+1}` of the point with coefficients in `k` vanishes.
  have hc : ContinuousMap.singularHomologyMap k (q + 1) c b = 0 :=
    (ModuleCat.subsingleton_singularHomology_of_contractibleSpace (𝟙_ (ModuleCat.{w} k))
      (of PUnit.{w + 1}) q).elim _ _
  rw [hfst, ContinuousMap.singularHomologyMap_comp, singularHomologyCrossBilinear_naturality_right,
    hc, map_zero, map_zero]

end TopCat

namespace TauCeti

section ModuleCoefficients

variable {k : Type w} [CommRing k] (R S : ModuleCat.{w} k) {Y : Type w} [TopologicalSpace Y]

/-- **Naturality of the cross product**, on pure tensors: for maps `f : X → X'` and `g : Y → Y'`,
`(f × g)_*(α × β) = f_* α × g_* β`. -/
theorem homologyMap_prodMap_singularHomologyCross_tmul {X X' Y' : Type w} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y')) {i j n : ℕ}
    (h : i + j = n) (α : ((TopCat.toSSet.obj (TopCat.of X)).homology R i : ModuleCat.{w} k))
    (β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (f.prodMap g))) (R ⊗ S) n).hom
        ((TopCat.singularHomologyCross (TopCat.of X) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) =
      (TopCat.singularHomologyCross (TopCat.of X') (TopCat.of Y') R S i j n h).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R i).hom α ⊗ₜ
          (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) S j).hom β) := by
  -- Both maps send `(x, y)` to `(f x, g y)`.
  have hfg : TopCat.ofHom f ⊗ₘ TopCat.ofHom g = TopCat.ofHom (f.prodMap g) :=
    TopCat.ext fun _ ↦ rfl
  have := congrArg (fun φ ↦ φ.hom (α ⊗ₜ β))
    (TopCat.singularHomologyCross_naturality (TopCat.ofHom f) (TopCat.ofHom g) R S i j n h)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hfg,
    ModuleCat.hom_tensorHom] at this
  -- `this` is the claim up to the action of `f_* ⊗ₘ g_*` on a pure tensor and the functor maps as
  -- `SSet.homologyMap`; these cannot be rewritten in `this`, whose classes are typed by the objects
  -- of the homology functor rather than by `SSet.homology`.
  exact this.symm

/-- The cross product is additive in the second factor: `α × (β - β') = α × β - α × β'`. -/
theorem singularHomologyCross_tmul_sub {X : Type w} [TopologicalSpace X] {i j n : ℕ}
    (h : i + j = n) (α : ((TopCat.toSSet.obj (TopCat.of X)).homology R i : ModuleCat.{w} k))
    (β β' : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)) :
    (TopCat.singularHomologyCross (TopCat.of X) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ (β - β')) =
      (TopCat.singularHomologyCross (TopCat.of X) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β) -
        (TopCat.singularHomologyCross (TopCat.of X) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β') :=
  -- The tensor product of `ModuleCat` is not syntactically `TensorProduct`, so `simp` does not
  -- apply `TensorProduct.tmul_sub` here.
  (congrArg _ (TensorProduct.tmul_sub _ _ _)).trans (map_sub _ _ _)

end ModuleCoefficients

end TauCeti
