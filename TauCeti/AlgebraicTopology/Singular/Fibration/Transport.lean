/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.Transport

/-!
# Path transport on singular homology of fibres of a Serre fibration

Since singular homology with coefficients in any module `M` over any ring `R` inverts weak homotopy
equivalences (`TauCeti.TopCat.weakEquivalences_isInvertedBy_singularHomologyFunctor`), specializing
the general path transport construction `TauCeti.TopCat.fiberIsoOfPath` yields path transport
isomorphisms `H_n(p⁻¹(b₀); M) ≅ H_n(p⁻¹(b₁); M)` for every Serre fibration `p : E ⟶ B` and path
`γ : Path b₀ b₁` (`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`).

## Main results

* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath`: a path in `B` induces singular homology
  isomorphisms between the fibres over its endpoints in every degree and for any coefficient module
  `M`.
* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_inv_comp_map_fiberι`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_naturality`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_pullbackFst`, and
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_naturality_coefficients`: compatibility with
  `p.fiberι`, characterization over contractible bases, base change, and naturality in fibration
  morphisms and coefficient morphisms.
* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_refl`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_symm`,
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_trans`, and
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_congr`: groupoid functoriality and homotopy
  invariance in the path `γ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition 4.21 and Theorem 4.41.
-/

public section

open CategoryTheory AlgebraicTopology

universe u v

namespace TauCeti.TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  {R : Type v} [Ring R] (M : ModuleCat.{u} R)

/-- **Path transport on singular homology of fibres of a Serre fibration.** A path `γ` from `b₀` to
`b₁` in `B` induces an isomorphism `H_n(p⁻¹(b₀); M) ≅ H_n(p⁻¹(b₁); M)` in every degree `n` for any
coefficient module `M`, obtained by specializing `TauCeti.TopCat.fiberIsoOfPath` to singular
homology. -/
noncomputable def fiberSingularHomologyIsoOfPath {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀)) ≅
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :=
  fiberIsoOfPath (weakEquivalences_isInvertedBy_singularHomologyFunctor M n) hp γ

/-- Path transport on singular homology is `TauCeti.TopCat.fiberIsoOfPath` specialized to
singular homology. -/
theorem fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ n =
      fiberIsoOfPath (weakEquivalences_isInvertedBy_singularHomologyFunctor M n) hp γ := by
  simp [fiberSingularHomologyIsoOfPath]

/-- Path transport along `γ : Path b₀ b₁` followed by the homology map of the fibre inclusion at
`1` into the base change along `γ` equals the homology map of the fibre inclusion at `0`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_hom_comp_map_pullbackFiberι {b₀ b₁ : B} (γ : Path b₀ b₁)
    (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
            (_root_.TopCat.pathEquiv.symm γ).hom₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
          (_root_.TopCat.pathEquiv.symm γ).hom₀) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberIsoOfPath_hom_comp_map_pullbackFiberι]

/-- The inverse of `fiberSingularHomologyIsoOfPath` followed by the homology map of the fibre
inclusion at `0` into the base change along `γ` equals the homology map of the fibre inclusion at
`1`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_inv_comp_map_pullbackFiberι {b₀ b₁ : B} (γ : Path b₀ b₁)
    (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).inv ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
            (_root_.TopCat.pathEquiv.symm γ).hom₀) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
          (_root_.TopCat.pathEquiv.symm γ).hom₁) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberIsoOfPath_inv_comp_map_pullbackFiberι]

/-- Characterization of `(fiberSingularHomologyIsoOfPath hp M γ n).hom`: a morphism equals it if
and only if postcomposing with the fibre inclusion at `1` into the base change along `γ` gives the
fibre inclusion at `0`. -/
theorem eq_fiberSingularHomologyIsoOfPath_hom_iff {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ)
    (f : ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :
    f = (fiberSingularHomologyIsoOfPath hp M γ n).hom ↔
      f ≫ ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 1)
            (_root_.TopCat.pathEquiv.symm γ).hom₁) =
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (_root_.TopCat.pathEquiv.symm γ).hom (k := 0)
            (_root_.TopCat.pathEquiv.symm γ).hom₀) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, eq_fiberIsoOfPath_hom_iff]

/-- Path transport along `γ : Path b₀ b₁` commutes with the homology maps induced by the fibre
inclusions `p⁻¹(b₀) ⟶ E` and `p⁻¹(b₁) ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_hom_comp_map_fiberι]

/-- The inverse of `fiberSingularHomologyIsoOfPath` commutes with the homology maps induced by the
fibre inclusions `p⁻¹(b₁) ⟶ E` and `p⁻¹(b₀) ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_inv_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).inv ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_inv_comp_map_fiberι]

/-- Over a contractible base, path transport on fibre singular homology along any path
`γ : Path b₀ b₁` equals the homology map of `p.fiberι b₀` followed by the inverse of the homology
map of `p.fiberι b₁`. -/
theorem fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace [ContractibleSpace B]
    {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    have := (isWeakHomotopyEquivalence_fiberι_of_contractibleSpace hp b₀).isIso_singularHomologyMap
      M n
    have := (isWeakHomotopyEquivalence_fiberι_of_contractibleSpace hp b₁).isIso_singularHomologyMap
      M n
    fiberSingularHomologyIsoOfPath hp M γ n =
      asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀)) ≪≫
        (asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁))).symm := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_eq_of_contractibleSpace]

/-- Naturality of `fiberSingularHomologyIsoOfPath` in maps of Serre fibrations. -/
@[reassoc]
theorem fiberSingularHomologyIsoOfPath_naturality {E' B' : _root_.TopCat.{u}} {p' : E' ⟶ B'}
    (hp' : serreFibrations p') {f : E ⟶ E'} {g : B ⟶ B'} (sq : CommSq f p p' g)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀) ≫
        (fiberSingularHomologyIsoOfPath hp' M (γ.map g.hom.continuous) n).hom := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_naturality]

/-- Base change compatibility of `fiberSingularHomologyIsoOfPath` along a morphism `f : B' ⟶ B`:
if a path `γ'` in `B'` lifts `γ` in `B` along `f`, then path transport along `γ` for `p` is
conjugate via `p.fiberPullbackFstIso f` to path transport along `γ'` for
`TopCat.pullbackFst f p`. -/
theorem fiberSingularHomologyIsoOfPath_pullbackFst {B' : _root_.TopCat.{u}} (f : B' ⟶ B)
    {x₀ x₁ : B'} (γ' : Path x₀ x₁) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (hb₀ : f x₀ = b₀) (hb₁ : f x₁ = b₁) (hγ : ∀ t, f (γ' t) = γ t) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ n =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
          (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm) ≪≫
        fiberSingularHomologyIsoOfPath (mem_serreFibrations_pullbackFst hp f) M γ' n ≪≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
          (p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁)) := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath]
  exact fiberIsoOfPath_pullbackFst
    (weakEquivalences_isInvertedBy_singularHomologyFunctor M n) hp f γ' γ hb₀ hb₁ hγ

/-- Naturality of `fiberSingularHomologyIsoOfPath` in morphisms of coefficient modules
`φ : M ⟶ M'`. -/
@[reassoc]
theorem fiberSingularHomologyIsoOfPath_naturality_coefficients {M' : ModuleCat.{u} R}
    (φ : M ⟶ M') {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map φ).app (p.fiber b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).map φ).app (p.fiber b₀) ≫
        (fiberSingularHomologyIsoOfPath hp M' γ n).hom := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath]
  exact fiberIsoOfPath_hom_comp_app (weakEquivalences_isInvertedBy_singularHomologyFunctor M n) hp
    (weakEquivalences_isInvertedBy_singularHomologyFunctor M' n)
    ((singularHomologyFunctor (ModuleCat.{u} R) n).map φ) γ

/-- Path transport along the constant path `Path.refl b` is the identity isomorphism. -/
@[simp]
theorem fiberSingularHomologyIsoOfPath_refl (b : B) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M (Path.refl b) n = Iso.refl _ := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_refl]

/-- Path transport along the reversed path `γ.symm` is the inverse isomorphism. -/
@[simp]
theorem fiberSingularHomologyIsoOfPath_symm {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ.symm n =
      (fiberSingularHomologyIsoOfPath hp M γ n).symm := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_symm]

/-- Path transport along a concatenation `γ.trans δ` is the composition of the path transport
isomorphisms along `γ` and `δ`. -/
@[simp]
theorem fiberSingularHomologyIsoOfPath_trans {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂)
    (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M (γ.trans δ) n =
      fiberSingularHomologyIsoOfPath hp M γ n ≪≫ fiberSingularHomologyIsoOfPath hp M δ n := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath, fiberIsoOfPath_trans]

/-- Homotopic paths with fixed endpoints induce the same isomorphism on the singular homology of the
fibres. -/
theorem fiberSingularHomologyIsoOfPath_congr {b₀ b₁ : B} {γ₀ γ₁ : Path b₀ b₁}
    (h : γ₀.Homotopic γ₁) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ₀ n = fiberSingularHomologyIsoOfPath hp M γ₁ n := by
  rw [fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath,
    fiberSingularHomologyIsoOfPath_eq_fiberIsoOfPath]
  exact fiberIsoOfPath_congr (weakEquivalences_isInvertedBy_singularHomologyFunctor M n) hp h

end TauCeti.TopCat
