/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.AlgebraicTopology.Sphere.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Serre fibrations over a sphere

Let `p : E → Sⁿ` be a Serre fibration over the unit sphere of an `(n + 1)`-dimensional real inner
product space, and write `F_b = p⁻¹(b)` for its fibres. This file relates the singular homology of
the fibres, with coefficients in a ring `R`.

* The complement of a point `x` of the sphere is contractible
  (`TauCeti.contractibleSpace_compl_singleton_sphere`). So over `Sⁿ ∖ {x}` the fibration has a
  weakly contractible base, and the fibre over any other point `b` includes into `E ∖ F_x` by a
  weak homotopy equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_inclusion_preimage_compl`).
* The local homology of `E` along `F_x` is the homology of `F_x` shifted by `n`:
  `H_{m + n}(E, E ∖ F_x) ≅ H_m(F_x)`, and it vanishes below degree `n`
  (`TauCeti.TopCat.singularHomologyComplFiberIso`, in the stereographic chart from `-x`).

When `E` has the homology of a point, the connecting morphism of the pair `(E, E ∖ F_x)` is an
isomorphism in positive degrees. Composing the three identifications gives the **Wang
isomorphism** `H_{k+1}(F_b) ≅ H_{k+2}(E, E ∖ F_x) ≅ H_m(F_x)` for `m + n = k + 2`
(`TauCeti.TopCat.sphereFiberWangIso`), and `H_{k+1}(F_b) = 0` for `k + 2 < n`
(`TauCeti.TopCat.isZero_singularHomology_sphereFiber`). This is the Wang sequence of a fibration
over a sphere in the case of an acyclic total space. For the path fibration of `Sⁿ`, whose total
space is contractible and whose fibre over the base point is the loop space, it computes the
homology of `ΩSⁿ`.

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_inclusion_preimage_compl`: for `b ≠ x`, the inclusion
  `F_b → E ∖ F_x` is a weak homotopy equivalence.
* `TauCeti.TopCat.singularHomologyPreimageComplIso`: the induced isomorphism
  `H_m(F_b) ≅ H_m(E ∖ F_x)`.
* `TauCeti.TopCat.sphereFiberWangIso`: for acyclic `E`, `b ≠ x` and `m + n = k + 2`,
  `H_{k+1}(F_b) ≅ H_m(F_x)`.
* `TauCeti.TopCat.isZero_singularHomology_sphereFiber`: for acyclic `E` and `k + 2 < n`,
  `H_{k+1}(F_b) = 0`.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology
open scoped Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

variable {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of (sphere (0 : V) 1)}

/-- **Over the complement of a point, the fibre is a weak homotopy equivalence.** For a Serre
fibration `p : E → Sⁿ` and two points `b ≠ x` of the sphere, the inclusion of the fibre
`p⁻¹(b)` into the part of `E` over `Sⁿ ∖ {x}` is a weak homotopy equivalence: `Sⁿ ∖ {x}` is
contractible. -/
theorem isWeakHomotopyEquivalence_inclusion_preimage_compl (hp : serreFibrations p)
    {b x : sphere (0 : V) 1} (h : b ≠ x) :
    (ContinuousMap.inclusion (((disjoint_singleton.2 h).preimage p).subset_compl_right)
      ).IsWeakHomotopyEquivalence := by
  have := TauCeti.contractibleSpace_compl_singleton_sphere x
  -- The restriction of `p` over `Sⁿ ∖ {x}`, a Serre fibration over a contractible base.
  set q : _root_.TopCat.of ↥(p ⁻¹' {x})ᶜ ⟶ _root_.TopCat.of ↥({x}ᶜ : Set (sphere (0 : V) 1)) :=
    _root_.TopCat.ofHom (p.hom.restrictPreimage {x}ᶜ)
  have hq : serreFibrations q := mem_serreFibrations_restrictPreimage hp {x}ᶜ
  let b' : ↥({x}ᶜ : Set (sphere (0 : V) 1)) := ⟨b, h⟩
  -- Its fibre over `b` is the fibre of `p` over `b`.
  let e : ↥(p ⁻¹' {b}) ≃ₜ q.fiber b' :=
    { toFun z :=
        ⟨⟨z.1, ((disjoint_singleton.2 h).preimage p).subset_compl_right z.2⟩, Subtype.ext z.2⟩
      invFun z := ⟨z.1.1, congrArg Subtype.val z.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have hfib : (q.fiberι b').hom.IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun _ ↦
      isNConnected_fiberι_of_mem_serreFibrations hq fun _ _ ↦ inferInstance
  have he : ContinuousMap.inclusion (((disjoint_singleton.2 h).preimage p).subset_compl_right) =
      (q.fiberι b').hom.comp e.toHomotopyEquiv.toFun :=
    ContinuousMap.ext fun z ↦ (_root_.TopCat.Hom.fiberι_apply q b' (e z)).symm
  rw [he]
  exact hfib.comp e.toHomotopyEquiv.isWeakHomotopyEquivalence

variable (R : Type u) [Ring R]

/-- The inclusion of the fibre over `b` into the part of `E` over `Sⁿ ∖ {x}` induces isomorphisms
`H_m(p⁻¹(b)) ≅ H_m(E ∖ p⁻¹(x))`. -/
def singularHomologyPreimageComplIso (hp : serreFibrations p) {b x : sphere (0 : V) 1}
    (h : b ≠ x) (m : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' {x})ᶜ) :=
  @asIso _ _ _ _ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
    (ModuleCat.of R R)).map (_root_.TopCat.ofHom
      (ContinuousMap.inclusion (((disjoint_singleton.2 h).preimage p).subset_compl_right))))
    ((isWeakHomotopyEquivalence_inclusion_preimage_compl hp h).isIso_singularHomologyMap
      (ModuleCat.of R R) m)

@[simp]
theorem singularHomologyPreimageComplIso_hom (hp : serreFibrations p) {b x : sphere (0 : V) 1}
    (h : b ≠ x) (m : ℕ) :
    (singularHomologyPreimageComplIso R hp h m).hom =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).map (_root_.TopCat.ofHom
          (ContinuousMap.inclusion (((disjoint_singleton.2 h).preimage p).subset_compl_right))) :=
  (rfl)

/-- The stereographic projection from the antipode `-x` of a point `x` of the unit sphere, a
chart at `x` with values in the orthogonal complement of `x`, a space of dimension `n`. -/
private abbrev antipodalStereographic (x : sphere (0 : V) 1) :
    OpenPartialHomeomorph (sphere (0 : V) 1) (ℝ ∙ ((-x : sphere (0 : V) 1) : V))ᗮ :=
  stereographic (norm_eq_of_mem_sphere (-x))

/-- A point `x` of the sphere lies in the source of the stereographic projection from `-x`. -/
private theorem mem_antipodalStereographic_source (x : sphere (0 : V) 1) :
    x ∈ (antipodalStereographic x).source := by
  rw [stereographic_source, mem_compl_singleton_iff]
  exact ne_neg_of_mem_unit_sphere ℝ x

/-- The orthogonal complement of a point of the unit sphere of an `(n + 1)`-dimensional space has
dimension `n`. -/
private theorem finrank_orthogonal_span_sphere (x : sphere (0 : V) 1) :
    finrank ℝ (ℝ ∙ (x : V))ᗮ = n :=
  Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere x)

/-- The local homology `H_{m + n}(E, E ∖ p⁻¹(x)) ≅ H_m(p⁻¹(x))` of a Serre fibration over `Sⁿ`
along the fibre over `x`, read in the stereographic chart from `-x`. -/
private def singularHomologyComplSphereFiberIso (hp : serreFibrations p) (x : sphere (0 : V) 1)
    (m k : ℕ) (h : m + n = k) :
    (TopPair.ofSubset (p ⁻¹' {x})ᶜ).singularHomology (ModuleCat.of R R) k ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {x})) :=
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  singularHomologyComplFiberIso (B := _root_.TopCat.of (sphere (0 : V) 1)) (p := p) R
    (antipodalStereographic x) (mem_antipodalStereographic_source x)
    (by rw [stereographic_target]; exact subset_univ _) one_pos hp m k
    (by rw [finrank_orthogonal_span_sphere (n := n)]; exact h)

/-- The local homology `H_k(E, E ∖ p⁻¹(x))` of a Serre fibration over `Sⁿ` vanishes for `k < n`. -/
private theorem isZero_singularHomology_complSphereFiber (hp : serreFibrations p)
    (x : sphere (0 : V) 1) {k : ℕ} (hk : k < n) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x})ᶜ).singularHomology (ModuleCat.of R R) k) :=
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  isZero_singularHomology_complFiber (B := _root_.TopCat.of (sphere (0 : V) 1)) (p := p) R
    (antipodalStereographic x) (mem_antipodalStereographic_source x) hp
    (by rwa [finrank_orthogonal_span_sphere (n := n)])

/-- For a total space `E` with the homology of a point, the connecting morphism
`H_{k+2}(E, E ∖ p⁻¹(x)) ⟶ H_{k+1}(E ∖ p⁻¹(x))` is an isomorphism. -/
private def singularHomologyComplSphereFiberδIso
    (hE : ∀ k, IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj E)) (x : sphere (0 : V) 1) (k : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {x})ᶜ).singularHomology (ModuleCat.of R R) (k + 2) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of ↥(p ⁻¹' {x})ᶜ) :=
  @asIso _ _ _ _ ((TopPair.ofSubset (p ⁻¹' {x})ᶜ).singularHomologyδ (ModuleCat.of R R) (k + 2)
    (k + 1)) ((TopPair.ofSubset (p ⁻¹' {x})ᶜ).isIso_singularHomologyδ_of_isZero
      (ModuleCat.of R R) (k + 2) (k + 1) (hE (k + 1)) (hE k))

/-- **The Wang isomorphism for a Serre fibration over a sphere with acyclic total space.** Let
`p : E → Sⁿ` be a Serre fibration whose total space has the homology of a point, and let `b ≠ x`.
Then `H_{k+1}(p⁻¹(b)) ≅ H_m(p⁻¹(x))` whenever `m + n = k + 2`: the fibre over `b` is weakly
equivalent to `E ∖ p⁻¹(x)`, whose homology in positive degrees is that of the pair
`(E, E ∖ p⁻¹(x))` one degree up, which is the homology of `p⁻¹(x)` shifted by `n`. -/
def sphereFiberWangIso (hp : serreFibrations p)
    (hE : ∀ k, IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj E)) {b x : sphere (0 : V) 1} (h : b ≠ x) (k m : ℕ)
    (hkm : m + n = k + 2) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {x})) :=
  singularHomologyPreimageComplIso R hp h (k + 1) ≪≫
    (singularHomologyComplSphereFiberδIso R hE x k).symm ≪≫
      singularHomologyComplSphereFiberIso R hp x m (k + 2) hkm

/-- **Low-degree vanishing for a Serre fibration over a sphere with acyclic total space.** If
`p : E → Sⁿ` is a Serre fibration whose total space has the homology of a point, then
`H_{k+1}(p⁻¹(b)) = 0` whenever `k + 2 < n`. -/
theorem isZero_singularHomology_sphereFiber (hp : serreFibrations p)
    (hE : ∀ k, IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj E)) {b x : sphere (0 : V) 1} (h : b ≠ x) {k : ℕ} (hk : k + 2 < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b}))) :=
  (isZero_singularHomology_complSphereFiber R hp x hk).of_iso
    (singularHomologyPreimageComplIso R hp h (k + 1) ≪≫
      (singularHomologyComplSphereFiberδIso R hE x k).symm)

end TauCeti.TopCat
