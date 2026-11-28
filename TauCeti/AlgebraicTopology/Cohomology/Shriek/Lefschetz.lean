/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Lefschetz
public import TauCeti.AlgebraicTopology.Cohomology.Shriek

/-!
# Shriek maps through Lefschetz duality

Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding of an oriented
`m`-manifold whose complement `∂X = X ∖ ι(M)` is collared, such as the closure `Ū` of a relatively
compact open set `U` with smooth boundary in a manifold. Capping absolute cohomology with the
fundamental class `[X, ∂X]` relative to the boundary is a map
`D_X : Hᵖ(X; L) → H_{m-p}(X, ∂X; L)`
(`TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`), which is bijective by Lefschetz
duality when `∂X` is itself a manifold
(`TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`). Shriek maps between
`X` and closed oriented manifolds are defined from it exactly as between closed manifolds
(`TauCeti.HomologicalOrientation.shriek`), with `D_X` in place of a Poincaré duality map.

* For a continuous map `π : X → Q` to a closed oriented `n`-manifold, the shriek map
  (`TauCeti.HomologicalOrientation.shriekIntoRel`)

  `π_! = D_X ∘ π^* ∘ D_Q⁻¹ : H_q(Q; L) → H_{q'}(X, ∂X; L)`,  `p + q = n`, `p + q' = m`,

  is characterized by `π_!([Q] ⌢ α) = [X, ∂X] ⌢ π^*α`
  (`TauCeti.HomologicalOrientation.shriekIntoRel_singularCapAddHom`). Only Poincaré duality of `Q`
  enters its definition.
* For a continuous map `φ : S → X` from a closed oriented `l`-manifold, the shriek map
  (`TauCeti.HomologicalOrientation.shriekFromRel`)

  `φ_! = D_S ∘ φ^* ∘ D_X⁻¹ : H_q(X, ∂X; L) → H_{q'}(S; L)`,  `p + q = m`, `p + q' = l`,

  is characterized by `φ_!([X, ∂X] ⌢ β) = [S] ⌢ φ^*β`
  (`TauCeti.HomologicalOrientation.shriekFromRel_absoluteCapFundamentalClassRel`). It inverts `D_X`,
  so it needs the boundary to be a manifold.

Both are compatible with the shriek maps of closed manifolds:
`(g ∘ π)_! = π_! ∘ g_!` (`TauCeti.HomologicalOrientation.shriekIntoRel_comp`),
`(φ ∘ ψ)_! = ψ_! ∘ φ_!` (`TauCeti.HomologicalOrientation.shriekFromRel_comp`), and the composite
through `X` is the shriek map of the composite map,

`φ_! ∘ π_! = (π ∘ φ)_!`

(`TauCeti.HomologicalOrientation.shriekFromRel_comp_shriekIntoRel`).

This gives the singular-homology form of Proposition 5.13 of Barraud, Damian, Humilière and
Oancea. Let `S` and `Q` both have dimension `n`, and suppose `(π ∘ φ)_*[S] = d • [Q]`. The kernel of
`π_!` lies in that of `(π ∘ φ)_!`, and `(π ∘ φ)_* ∘ (π ∘ φ)_! = d • id`
(`TauCeti.HomologicalOrientation.map_shriek`). So every class killed by `π_!` is killed by `d`
(`TauCeti.HomologicalOrientation.zsmul_eq_zero_of_shriekIntoRel_eq_zero`); in particular `π_!` is
injective when `d = ±1` (`TauCeti.HomologicalOrientation.injective_shriekIntoRel_of_isUnit`). For a
preconnected `Q`, `d` is the degree of `π ∘ φ`
(`TauCeti.HomologicalOrientation.degree_smul_eq_zero_of_shriekIntoRel_eq_zero`). In the source,
`X = Ū` for a domain `U` in the cotangent bundle `T*Q`, `π` is the bundle projection and `φ` a map
of a closed oriented manifold into `U`; this kernel controls which closed characteristics of `∂U`
the cotangent criterion detects.

## Main definitions

* `TauCeti.HomologicalOrientation.shriekIntoRel`: the shriek map `H_q(Q; L) → H_{q'}(X, ∂X; L)` of
  a map `X → Q`.
* `TauCeti.HomologicalOrientation.shriekFromRel`: the shriek map `H_q(X, ∂X; L) → H_{q'}(S; L)` of a
  map `S → X`.

## Main results

* `TauCeti.HomologicalOrientation.shriekIntoRel_singularCapAddHom`,
  `TauCeti.HomologicalOrientation.shriekFromRel_absoluteCapFundamentalClassRel`: the characteristic
  properties, and `TauCeti.HomologicalOrientation.shriekIntoRel_unique`,
  `TauCeti.HomologicalOrientation.shriekFromRel_unique`: the shriek maps are determined by them.
* `TauCeti.HomologicalOrientation.shriekFromRel_comp_shriekIntoRel`: `φ_! ∘ π_! = (π ∘ φ)_!`.
* `TauCeti.HomologicalOrientation.zsmul_eq_zero_of_shriekIntoRel_eq_zero`: if
  `(π ∘ φ)_*[S] = d • [Q]`, the kernel of `π_!` is `d`-torsion.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.13 and its proof.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.43 (Lefschetz duality).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module Topology Set AlgebraicTopology

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X} [TopologicalSpace M] [T2Space X] [CompactSpace X] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {m : ℕ}
  (o : HomologicalOrientation M E m) (hm : finrank ℝ E = m) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)
  {Q S S' : Type} [TopologicalSpace Q] [T2Space Q] [CompactSpace Q]
  [TopologicalSpace S] [T2Space S] [CompactSpace S] [TopologicalSpace S'] [T2Space S']
  [CompactSpace S'] {F H H' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F Q] [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [ChartedSpace H S] [NormedAddCommGroup H'] [NormedSpace ℝ H'] [FiniteDimensional ℝ H']
  [ChartedSpace H' S'] {n l l' : ℕ}
  (oQ : HomologicalOrientation Q F n) (hn : finrank ℝ F = n)
  (oS : HomologicalOrientation S H l) (hl : finrank ℝ H = l) (L : ModuleCat.{0} ℤ)
  {p q q' q'' : ℕ}

/-! ### The shriek map of a map to a closed manifold -/

/-- **The shriek map** `π_! = D_X ∘ π^* ∘ D_Q⁻¹ : H_q(Q; L) →+ H_{q'}(X, ∂X; L)` of a continuous map
`π : X → Q` to a closed oriented `n`-manifold, for `p + q = n` and `p + q' = m`. Here `D_Q` caps
with the fundamental class of `Q`, invertible by Poincaré duality
(`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`), and `D_X` caps
absolute cohomology with the fundamental class `[X, ∂X]` relative to the boundary
(`TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`). -/
def shriekIntoRel (π : C(X, Q)) (hq : p + q = n) (hq' : p + q' = m) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Q) →+
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
        (C := ModuleCat.{0} ℤ) L q' :=
  (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q' hq').hom.toAddMonoidHom.comp <|
    (TopCat.singularCohomologyMap (TopCat.ofHom π) p).hom.toAddMonoidHom.comp
      (AddEquiv.ofBijective _
        (oQ.bijective_singularCapAddHom_fundamentalClass hn L p q hq)).symm.toAddMonoidHom

/-- **Characteristic property of the shriek map** of `π : X → Q`:
`π_!([Q] ⌢ α) = [X, ∂X] ⌢ π^*α`. -/
@[simp]
theorem shriekIntoRel_singularCapAddHom (π : C(X, Q)) (hq : p + q = n) (hq' : p + q' = m)
    (α : (TopCat.of Q).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq'
        ((TopCat.of Q).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq (oQ.fundamentalClass hn) α) =
      o.absoluteCapFundamentalClassRel hm hι hιf hf L p q' hq'
        ((TopCat.singularCohomologyMap (TopCat.ofHom π) p).hom α) := by
  have hα : (AddEquiv.ofBijective _
      (oQ.bijective_singularCapAddHom_fundamentalClass hn L p q hq)).symm
      ((TopCat.of Q).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq (oQ.fundamentalClass hn) α) = α :=
    (AddEquiv.ofBijective _ _).symm_apply_apply α
  -- Unfolded, `π_!([Q] ⌢ α)` is `D_X(π^*(D_Q⁻¹([Q] ⌢ α)))`.
  exact congrArg (fun a ↦ o.absoluteCapFundamentalClassRel hm hι hιf hf L p q' hq'
    ((TopCat.singularCohomologyMap (TopCat.ofHom π) p).hom a)) hα

/-- The shriek map of `π : X → Q` is determined by its characteristic property: an additive map
`g` with `g([Q] ⌢ α) = [X, ∂X] ⌢ π^*α` for every `α` is `π_!`. -/
theorem shriekIntoRel_unique (π : C(X, Q)) (hq : p + q = n) (hq' : p + q' = m)
    {g : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Q) →+
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
        (C := ModuleCat.{0} ℤ) L q'}
    (hg : ∀ α : (TopCat.of Q).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p,
      g ((TopCat.of Q).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq (oQ.fundamentalClass hn) α) =
        o.absoluteCapFundamentalClassRel hm hι hιf hf L p q' hq'
          ((TopCat.singularCohomologyMap (TopCat.ofHom π) p).hom α)) :
    g = o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq' := by
  ext y
  obtain ⟨α, rfl⟩ := (oQ.bijective_singularCapAddHom_fundamentalClass hn L p q hq).2 y
  rw [hg, shriekIntoRel_singularCapAddHom]

/-- **Functoriality**: `(g ∘ π)_! = π_! ∘ g_!` for a continuous map `π : X → Q` and a continuous map
`g : Q → S` of closed oriented manifolds. -/
theorem shriekIntoRel_comp (π : C(X, Q)) (g : C(Q, S)) (hq : p + q = l) (hq' : p + q' = n)
    (hq'' : p + q'' = m) :
    o.shriekIntoRel hm hι hιf hf oS hl L (g.comp π) hq hq'' =
      (o.shriekIntoRel hm hι hιf hf oQ hn L π hq' hq'').comp (oQ.shriek hn oS hl L g hq hq') := by
  refine (shriekIntoRel_unique o hm hι hιf hf oS hl L (g.comp π) hq hq'' fun α ↦ ?_).symm
  rw [AddMonoidHom.comp_apply, shriek_singularCapAddHom, shriekIntoRel_singularCapAddHom,
    ← ModuleCat.comp_apply, ← TopCat.singularCohomologyMap_comp, TopCat.ofHom_comp]

/-! ### The shriek map of a map from a closed manifold -/

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [ChartedSpace G N] (hG : finrank ℝ G + 1 = m)

/-- **The shriek map** `φ_! = D_S ∘ φ^* ∘ D_X⁻¹ : H_q(X, ∂X; L) →+ H_{q'}(S; L)` of a continuous map
`φ : S → X` from a closed oriented `l`-manifold, for `p + q = m` and `p + q' = l`. Here `D_X` caps
absolute cohomology with the fundamental class `[X, ∂X]` relative to the boundary, invertible by
Lefschetz duality since the boundary is a manifold of dimension `m - 1`
(`TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`), and `D_S` caps with the
fundamental class of `S`. -/
def shriekFromRel (φ : C(S, X)) (hq : p + q = m) (hq' : p + q' = l) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
        (C := ModuleCat.{0} ℤ) L q →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q').obj L).obj (TopCat.of S) :=
  ((TopCat.of S).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq' (oS.fundamentalClass hl)).comp <|
    (TopCat.singularCohomologyMap (TopCat.ofHom φ) p).hom.toAddMonoidHom.comp
      (AddEquiv.ofBijective (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q hq).hom
        (o.bijective_absoluteCapFundamentalClassRel hm hι hιf hf L hG p q hq)).symm.toAddMonoidHom

/-- **Characteristic property of the shriek map** of `φ : S → X`:
`φ_!([X, ∂X] ⌢ β) = [S] ⌢ φ^*β`. -/
@[simp]
theorem shriekFromRel_absoluteCapFundamentalClassRel (φ : C(S, X)) (hq : p + q = m)
    (hq' : p + q' = l)
    (β : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.shriekFromRel hm hι hιf hf oS hl L hG φ hq hq'
        (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q hq β) =
      (TopCat.of S).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq' (oS.fundamentalClass hl)
        ((TopCat.singularCohomologyMap (TopCat.ofHom φ) p).hom β) := by
  have hβ : (AddEquiv.ofBijective (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q hq).hom
      (o.bijective_absoluteCapFundamentalClassRel hm hι hιf hf L hG p q hq)).symm
      (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q hq β) = β :=
    (AddEquiv.ofBijective _ _).symm_apply_apply β
  -- Unfolded, `φ_!([X, ∂X] ⌢ β)` is `D_S(φ^*(D_X⁻¹([X, ∂X] ⌢ β)))`.
  exact congrArg (fun b ↦ (TopCat.of S).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq'
    (oS.fundamentalClass hl) ((TopCat.singularCohomologyMap (TopCat.ofHom φ) p).hom b)) hβ

/-- The shriek map of `φ : S → X` is determined by its characteristic property: an additive map
`g` with `g([X, ∂X] ⌢ β) = [S] ⌢ φ^*β` for every `β` is `φ_!`. -/
theorem shriekFromRel_unique (φ : C(S, X)) (hq : p + q = m) (hq' : p + q' = l)
    {g : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
        (C := ModuleCat.{0} ℤ) L q →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q').obj L).obj (TopCat.of S)}
    (hg : ∀ β : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p,
      g (o.absoluteCapFundamentalClassRel hm hι hιf hf L p q hq β) =
        (TopCat.of S).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq' (oS.fundamentalClass hl)
          ((TopCat.singularCohomologyMap (TopCat.ofHom φ) p).hom β)) :
    g = o.shriekFromRel hm hι hιf hf oS hl L hG φ hq hq' := by
  ext y
  obtain ⟨β, rfl⟩ := (o.bijective_absoluteCapFundamentalClassRel hm hι hιf hf L hG p q hq).2 y
  exact (hg β).trans
    (o.shriekFromRel_absoluteCapFundamentalClassRel hm hι hιf hf oS hl L hG φ hq hq' β).symm

/-- **Functoriality**: `(φ ∘ ψ)_! = ψ_! ∘ φ_!` for a continuous map `φ : S → X` and a continuous
map `ψ : S' → S` of closed oriented manifolds. -/
theorem shriekFromRel_comp (oS' : HomologicalOrientation S' H' l') (hl' : finrank ℝ H' = l')
    (φ : C(S, X)) (ψ : C(S', S)) (hq : p + q = m) (hq' : p + q' = l) (hq'' : p + q'' = l') :
    o.shriekFromRel hm hι hιf hf oS' hl' L hG (φ.comp ψ) hq hq'' =
      (oS'.shriek hl' oS hl L ψ hq' hq'').comp
        (o.shriekFromRel hm hι hιf hf oS hl L hG φ hq hq') := by
  refine (shriekFromRel_unique o hm hι hιf hf oS' hl' L hG (φ.comp ψ) hq hq'' fun β ↦ ?_).symm
  rw [AddMonoidHom.comp_apply, shriekFromRel_absoluteCapFundamentalClassRel,
    shriek_singularCapAddHom, ← ModuleCat.comp_apply, ← TopCat.singularCohomologyMap_comp,
    TopCat.ofHom_comp]

/-! ### The composite through `X` -/

/-- **The composite through `X`**: for continuous maps `φ : S → X` and `π : X → Q`, with `S` and
`Q` closed oriented manifolds, `φ_! ∘ π_! = (π ∘ φ)_!`. -/
theorem shriekFromRel_comp_shriekIntoRel (π : C(X, Q)) (φ : C(S, X)) (hq : p + q = n)
    (hq' : p + q' = m) (hq'' : p + q'' = l) :
    (o.shriekFromRel hm hι hιf hf oS hl L hG φ hq' hq'').comp
        (o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq') =
      oS.shriek hl oQ hn L (π.comp φ) hq hq'' := by
  refine shriek_unique oS hl oQ hn L (π.comp φ) hq hq'' fun α ↦ ?_
  rw [AddMonoidHom.comp_apply, shriekIntoRel_singularCapAddHom,
    shriekFromRel_absoluteCapFundamentalClassRel, ← ModuleCat.comp_apply,
    ← TopCat.singularCohomologyMap_comp, TopCat.ofHom_comp]

include hG in
/-- The kernel of `π_!` lies in the kernel of `(π ∘ φ)_!`: if `π_!(y) = 0`, then
`(π ∘ φ)_!(y) = φ_!(π_!(y)) = 0`. -/
theorem shriek_comp_eq_zero_of_shriekIntoRel_eq_zero (π : C(X, Q)) (φ : C(S, X)) (hq : p + q = n)
    (hq' : p + q' = m) (hq'' : p + q'' = l)
    {y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Q)}
    (hy : o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq' y = 0) :
    oS.shriek hl oQ hn L (π.comp φ) hq hq'' y = 0 := by
  rw [← o.shriekFromRel_comp_shriekIntoRel hm hι hιf hf oQ hn oS hl L hG π φ hq hq' hq'',
    AddMonoidHom.comp_apply, hy, map_zero]

/-! ### Proposition 5.13: the kernel of `π_!` is torsion -/

section Torsion

variable (oS : HomologicalOrientation S H n) (hl : finrank ℝ H = n)

include hG

/-- **The kernel of `π_!` is `d`-torsion** (Barraud–Damian–Humilière–Oancea, Proposition 5.13): for
continuous maps `φ : S → X` and `π : X → Q` with `S` and `Q` closed oriented `n`-manifolds and
`(π ∘ φ)_*[S] = d • [Q]`, every class `y ∈ H_q(Q; L)` with `π_!(y) = 0` satisfies `d • y = 0`. -/
theorem zsmul_eq_zero_of_shriekIntoRel_eq_zero (π : C(X, Q)) (φ : C(S, X)) (hq : p + q = n)
    (hq' : p + q' = m) {d : ℤ}
    (hd : oS.mapFundamentalClass hl (π.comp φ) = d • oQ.fundamentalClass hn)
    {y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Q)}
    (hy : o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq' y = 0) :
    d • y = 0 :=
  oS.zsmul_eq_zero_of_shriek_eq_zero hl oQ hn L (π.comp φ) hq hd
    (o.shriek_comp_eq_zero_of_shriekIntoRel_eq_zero hm hι hιf hf oQ hn oS hl L hG π φ hq hq' hq hy)

/-- **The kernel of `π_!` is `deg(π ∘ φ)`-torsion**: for continuous maps `φ : S → X` and `π : X → Q`
with `S` and `Q` closed oriented `n`-manifolds and `Q` preconnected, every class `y ∈ H_q(Q; L)`
with `π_!(y) = 0` is killed by the degree of `π ∘ φ`. -/
theorem degree_smul_eq_zero_of_shriekIntoRel_eq_zero [PreconnectedSpace Q] (π : C(X, Q))
    (φ : C(S, X)) (hq : p + q = n) (hq' : p + q' = m)
    {y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of Q)}
    (hy : o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq' y = 0) :
    oS.degree oQ hl (π.comp φ) • y = 0 :=
  o.zsmul_eq_zero_of_shriekIntoRel_eq_zero hm hι hιf hf oQ hn L hG oS hl π φ hq hq'
    (oS.mapFundamentalClass_eq_degree_smul oQ hl hn (π.comp φ)) hy

/-- If some `φ : S → X` makes `π ∘ φ` of degree `±1`, that is `(π ∘ φ)_*[S] = d • [Q]` with `d` a
unit, then `π_!` is injective. -/
theorem injective_shriekIntoRel_of_isUnit (π : C(X, Q)) (φ : C(S, X)) (hq : p + q = n)
    (hq' : p + q' = m) {d : ℤ} (hd₁ : IsUnit d)
    (hd : oS.mapFundamentalClass hl (π.comp φ) = d • oQ.fundamentalClass hn) :
    Function.Injective (o.shriekIntoRel hm hι hιf hf oQ hn L π hq hq') := by
  -- `φ_! ∘ π_! = (π ∘ φ)_!` is injective, since `π ∘ φ` has degree `±1`.
  refine Function.Injective.of_comp (f := o.shriekFromRel hm hι hιf hf oS hl L hG φ hq' hq) ?_
  rw [← AddMonoidHom.coe_comp, o.shriekFromRel_comp_shriekIntoRel hm hι hιf hf oQ hn oS hl L hG π φ
    hq hq' hq]
  exact oS.injective_shriek_of_isUnit hl oQ hn L (π.comp φ) hq hd₁ hd

end Torsion

end HomologicalOrientation

end TauCeti
