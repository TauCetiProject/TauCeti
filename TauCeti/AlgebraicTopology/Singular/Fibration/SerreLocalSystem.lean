/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.Contractible
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.TopCat.Path

/-!
# The local system of fibre homology of a Serre fibration

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`). A Serre fibration need
not have a transport map between its fibres, but it has one on homology. For a path `γ` from `b₀`
to `b₁` in `B`, the base change `γ*E = {(t, e) | γ t = p e}` of `p` along `γ` is a Serre fibration
over the interval, and since the interval is contractible, the inclusions `e ↦ (0, e)` and
`e ↦ (1, e)` of the fibres over `b₀` and `b₁` into `γ*E` are weak homotopy equivalences. The
**transport** along `γ` (`TauCeti.TopCat.fiberHomologyTransport`) is the composite

`Hₙ(p⁻¹(b₀); M) ≅ Hₙ(γ*E; M) ≅ Hₙ(p⁻¹(b₁); M)`

of the isomorphisms they induce on singular homology with coefficients in a module `M`. It depends
only on the homotopy class of `γ` relative to its end points, sends constant paths to identities
and concatenations to composites, so `b ↦ Hₙ(p⁻¹(b); M)` is a local coefficient system on `B`
(`TauCeti.TopCat.serreFiberLocalSystem`), the local system of fibre homology of `p`. With path
transport as its monodromy, it is the coefficient system of the second page
`E²_{s,t} = H_s(B; H_t(F))` of the Serre spectral sequence of `p`.

All of this is a special case of transport over an arbitrary contractible parameter space `K`
(`TauCeti.TopCat.pullbackFiberTransport`): for a map `g : K → B` and points `k₀, k₁` of `K`, the
fibre inclusions `TopCat.Hom.pullbackFiberι` into the base change of `p` along `g` at `k₀` and `k₁`
are weak homotopy equivalences (`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackFiberι`). They
induce isomorphisms on homology, so they compose to a map between the homology of the fibres over
`g k₀` and `g k₁`. This transport is transitive, natural in maps of parameter spaces over `B` and
in maps of fibrations, and trivial along paths in `K` on which `g` is constant. Homotopy invariance
follows by taking for `K` the square, on which a homotopy of paths is defined.

When `p` has a lifting function `Λ`, so that it is a Hurewicz fibration with a transport map
`Λ.transport γ` between its fibres, the transport on homology is the map induced by
`Λ.transport γ` (`TauCeti.TopCat.fiberHomologyTransport_eq_singularHomologyMap_fiberTransport`):
the lifts of `γ` give a homotopy, in `γ*E`, from the inclusion of the fibre over `b₀` to the
transport followed by the inclusion of the fibre over `b₁`. So the local system of fibre homology
agrees with the one built from a lifting function
(`TauCeti.TopCat.serreFiberLocalSystemIsoFiberLocalSystem`, against `TauCeti.fiberLocalSystem`).

A map of Serre fibrations, that is, a commutative square from `p` to `p'` over `g : B → B'`, maps
the local system of fibre homology of `p` to the pullback along `g` of that of `p'`, acting on the
fibres by the maps it induces (`CategoryTheory.CommSq.serreFiberLocalSystemMap`). This is an
isomorphism when the maps of fibres are weak homotopy equivalences, as for the base change of a
Serre fibration.

## Main definitions

* `TauCeti.TopCat.pullbackFiberTransport`: transport on homology over a contractible parameter
  space.
* `TauCeti.TopCat.fiberHomologyTransport`: transport on homology along a path.
* `TauCeti.TopCat.serreFiberLocalSystem`: the local system `b ↦ Hₙ(p⁻¹(b); M)`.
* `TauCeti.TopCat.serreFiberLocalSystemOn`: its restriction, with coefficients `R`, to a subspace
  of the base.
* `CategoryTheory.CommSq.serreFiberLocalSystemMap`: the morphism of local systems induced by a map
  of Serre fibrations.

## Main results

* `TauCeti.TopCat.fiberHomologyTransport_congr`, `TauCeti.TopCat.fiberHomologyTransport_refl`,
  `TauCeti.TopCat.fiberHomologyTransport_trans`: transport is invariant under homotopy and
  functorial.
* `TauCeti.TopCat.fiberHomologyTransport_naturality`: transport is natural in maps of Serre
  fibrations.
* `TauCeti.TopCat.fiberHomologyTransport_eq_singularHomologyMap_fiberTransport`: for a fibration
  with a lifting function, transport on homology is induced by the transport map.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (local coefficients) and Section 4.2 (fibrations).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.2.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

universe w u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-! ### Fibre inclusions into a base change -/

section Pullback

variable {K : TopCat.{u}}

variable (hp : serreFibrations p)
include hp

variable {R : Type w} [Ring R] (M : ModuleCat.{u} R) (n : ℕ)

/-- Over a contractible base, the fibre inclusions into a base change of a Serre fibration induce
isomorphisms on singular homology with coefficients in any module. -/
theorem isIso_singularHomologyMap_pullbackFiberι [ContractibleSpace K]
    (g : K ⟶ B) {k : K} {b : B} (h : g k = b) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h)) :=
  (isWeakHomotopyEquivalence_pullbackFiberι hp g h).isIso_singularHomologyMap M n

/-- **Transport on homology over a contractible parameter space.** For a Serre fibration `p`, a map
`g : K ⟶ B` from a contractible space and points `k₀, k₁` of `K` over `b₀, b₁`, the map
`Hₙ(p⁻¹(b₀); M) → Hₙ(p⁻¹(b₁); M)` induced by the inclusion of the fibre over `b₀` into the base
change of `p` along `g` at `k₀`, followed by the inverse of the isomorphism induced by the inclusion
of the fibre over `b₁` at `k₁`. -/
def pullbackFiberTransport [ContractibleSpace K] (g : K ⟶ B)
    {k₀ k₁ : K} {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁) :=
  have := isIso_singularHomologyMap_pullbackFiberι hp M n g h₁
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₀) ≫
    inv (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₁))

variable [ContractibleSpace K]

/-- Transport followed by the fibre inclusion at the end point is the fibre inclusion at the
starting point. -/
@[reassoc (attr := simp)]
theorem pullbackFiberTransport_comp_map_pullbackFiberι (g : K ⟶ B)
    {k₀ k₁ : K} {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) :
    pullbackFiberTransport hp M n g h₀ h₁ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₀) := by
  have := isIso_singularHomologyMap_pullbackFiberι hp M n g h₁
  simp [pullbackFiberTransport]

/-- **Characterization of transport.** Transport is the unique map which, followed by the fibre
inclusion at the end point, is the fibre inclusion at the starting point. -/
theorem eq_pullbackFiberTransport_iff (g : K ⟶ B) {k₀ k₁ : K}
    {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁)
    (f : ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :
    f = pullbackFiberTransport hp M n g h₀ h₁ ↔
      f ≫ ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₁) =
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h₀) := by
  have := isIso_singularHomologyMap_pullbackFiberι hp M n g h₁
  rw [← cancel_mono (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
    (p.pullbackFiberι g h₁)), pullbackFiberTransport_comp_map_pullbackFiberι]

/-- Transport from a point to itself is the identity. -/
@[simp]
theorem pullbackFiberTransport_self (g : K ⟶ B) {k : K} {b : B}
    (h : g k = b) : pullbackFiberTransport hp M n g h h = 𝟙 _ :=
  ((eq_pullbackFiberTransport_iff hp M n g h h _).2 (Category.id_comp _)).symm

/-- **Transport is transitive.** -/
@[reassoc (attr := simp)]
theorem pullbackFiberTransport_comp_pullbackFiberTransport (g : K ⟶ B)
    {k₀ k₁ k₂ : K} {b₀ b₁ b₂ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁) (h₂ : g k₂ = b₂) :
    pullbackFiberTransport hp M n g h₀ h₁ ≫ pullbackFiberTransport hp M n g h₁ h₂ =
      pullbackFiberTransport hp M n g h₀ h₂ :=
  (eq_pullbackFiberTransport_iff hp M n g h₀ h₂ _).2 (by simp)

/-- **Transport along a path on which the map to `B` is constant is the identity.** If `γ` is a path
from `k₀` to `k₁` in `K` which `g` maps to the point `b`, then transport from `k₀` to `k₁` is the
identity of the homology of the fibre over `b`: the fibre inclusions at `k₀` and `k₁` are homotopic
through the fibre inclusions at the points of `γ`. -/
theorem pullbackFiberTransport_eq_id (g : K ⟶ B) {k₀ k₁ : K} {b : B}
    (γ : Path k₀ k₁) (hγ : ∀ t, g (γ t) = b) (h₀ : g k₀ = b) (h₁ : g k₁ = b) :
    pullbackFiberTransport hp M n g h₀ h₁ = 𝟙 _ := by
  refine ((eq_pullbackFiberTransport_iff hp M n g h₀ h₁ _).2 ?_).symm
  let H : _root_.TopCat.Homotopy (p.pullbackFiberι g h₁) (p.pullbackFiberι g h₀) :=
    { toFun x := ⟨(γ (σ x.1), x.2.val), (hγ _).trans (x.2.property : p x.2.val = b).symm⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (by rw [TopCat.Hom.coe_pullbackFiberι_apply]; simp)
      map_one_left x := Subtype.ext (by rw [TopCat.Hom.coe_pullbackFiberι_apply]; simp) }
  rw [Category.id_comp]
  exact H.congr_homologyMap_singularChainComplexFunctor M n

/-- **Transport is natural in maps of Serre fibrations.** For a commutative square from `p` to `p'`
over `g_B : B ⟶ B'`, and a map `φ : K ⟶ K'` of contractible parameter spaces compatible with
`g : K ⟶ B` and `g' : K' ⟶ B'`, transport along `g` followed by the map of fibres over `b₁` is the
map of fibres over `b₀` followed by transport along `g'`. -/
@[reassoc]
theorem pullbackFiberTransport_naturality {E' B' K' : TopCat.{u}} {p' : E' ⟶ B'}
    [ContractibleSpace K'] {f : E ⟶ E'} {g_B : B ⟶ B'} (sq : CommSq f p p' g_B)
    (hp' : serreFibrations p') (g : K ⟶ B) (g' : K' ⟶ B') (φ : K ⟶ K')
    (hφ : φ ≫ g' = g ≫ g_B) {k₀ k₁ : K} {b₀ b₁ : B} (h₀ : g k₀ = b₀) (h₁ : g k₁ = b₁)
    (h₀' : g' (φ k₀) = g_B b₀) (h₁' : g' (φ k₁) = g_B b₁) :
    pullbackFiberTransport hp M n g h₀ h₁ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀) ≫
        pullbackFiberTransport hp' M n g' h₀' h₁' := by
  have := isIso_singularHomologyMap_pullbackFiberι hp' M n g' h₁'
  -- On a fibre, the map of base changes acts by the map of fibres, at the image under `φ` of the
  -- base point.
  have hm {k : K} {b : B} (h : g k = b) (h' : g' (φ k) = g_B b) :
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b) ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p'.pullbackFiberι g' h') =
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.pullbackFiberι g h) ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
            (sq.pullbackMapOfCompEq φ hφ) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq.pullbackFiberι_comp_pullbackMapOfCompEq]
  rw [← cancel_mono (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
    (p'.pullbackFiberι g' h₁'))]
  simp only [Category.assoc, hm h₁ h₁', hm h₀ h₀', pullbackFiberTransport_comp_map_pullbackFiberι,
    pullbackFiberTransport_comp_map_pullbackFiberι_assoc]

/-- **Transport is natural in maps of parameter spaces.** If `φ : K' ⟶ K` lies over `B`, that is
`φ ≫ g = g'`, transport along `g'` from `k₀` to `k₁` is transport along `g` from `φ k₀` to
`φ k₁`, here written `k₀'` and `k₁'`. -/
theorem pullbackFiberTransport_comp_left {K' : TopCat.{u}} [ContractibleSpace K']
    (g : K ⟶ B) (g' : K' ⟶ B) (φ : K' ⟶ K) (hφ : φ ≫ g = g')
    {k₀ k₁ : K'} {k₀' k₁' : K} (hk₀ : φ k₀ = k₀') (hk₁ : φ k₁ = k₁') {b₀ b₁ : B}
    (h₀ : g' k₀ = b₀) (h₁ : g' k₁ = b₁) (h₀' : g k₀' = b₀) (h₁' : g k₁' = b₁) :
    pullbackFiberTransport hp M n g' h₀ h₁ = pullbackFiberTransport hp M n g h₀' h₁' := by
  subst hφ hk₀ hk₁
  -- This is naturality for the identity map of `p`.
  simpa using pullbackFiberTransport_naturality hp M n (CommSq.mk (by simp : 𝟙 E ≫ p = p ≫ 𝟙 B))
    hp (φ ≫ g) g φ (Category.comp_id _).symm h₀ h₁ h₀' h₁'

end Pullback

/-! ### Transport along paths -/

section Path

variable {b₀ b₁ b₂ : B}

variable (hp : serreFibrations p) {R : Type w} [Ring R] (M : ModuleCat.{u} R) (n : ℕ)
include hp

/-- **Transport on fibre homology along a path.** For a Serre fibration `p` and a path `γ` from
`b₀` to `b₁`, the isomorphism `Hₙ(p⁻¹(b₀); M) ≅ Hₙ(γ*E; M)` induced by the inclusion of the fibre
over `b₀` into the base change `γ*E` of `p` along `γ`, followed by the inverse of the isomorphism
`Hₙ(p⁻¹(b₁); M) ≅ Hₙ(γ*E; M)` induced by the inclusion of the fibre over `b₁`. -/
def fiberHomologyTransport (γ : Path b₀ b₁) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁) :=
  pullbackFiberTransport hp M n (TopCat.pathEquiv.symm γ).hom (k₀ := 0) (k₁ := 1)
    (TopCat.pathEquiv.symm γ).hom₀ (TopCat.pathEquiv.symm γ).hom₁

/-- Transport along a path is transport over the interval, along the path seen as a map from
`TopCat.I`, from `0` to `1`. -/
lemma fiberHomologyTransport_eq_pullbackFiberTransport (γ : Path b₀ b₁) :
    fiberHomologyTransport hp M n γ =
      pullbackFiberTransport hp M n (TopCat.pathEquiv.symm γ).hom (k₀ := 0) (k₁ := 1)
        (TopCat.pathEquiv.symm γ).hom₀ (TopCat.pathEquiv.symm γ).hom₁ :=
  (rfl)

/-- **Characterization of transport along a path.** Transport along `γ` followed by the inclusion
of the fibre over `b₁` into `γ*E` is the inclusion of the fibre over `b₀`. -/
@[reassoc (attr := simp)]
theorem fiberHomologyTransport_comp_map_pullbackFiberι
    (γ : Path b₀ b₁) :
    fiberHomologyTransport hp M n γ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 1)
            (TopCat.pathEquiv.symm γ).hom₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 0)
          (TopCat.pathEquiv.symm γ).hom₀) := by
  rw [fiberHomologyTransport_eq_pullbackFiberTransport]
  exact pullbackFiberTransport_comp_map_pullbackFiberι hp M n _ _ _

/-- Transport along `γ` is the unique map which, followed by the inclusion of the fibre over `b₁`
into `γ*E`, is the inclusion of the fibre over `b₀`. -/
theorem eq_fiberHomologyTransport_iff (γ : Path b₀ b₁)
    (f : ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :
    f = fiberHomologyTransport hp M n γ ↔
      f ≫ ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 1)
            (TopCat.pathEquiv.symm γ).hom₁) =
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 0)
            (TopCat.pathEquiv.symm γ).hom₀) := by
  rw [fiberHomologyTransport_eq_pullbackFiberTransport]
  exact eq_pullbackFiberTransport_iff hp M n _ _ _ f

/-- **Transport along a constant path is the identity.** -/
@[simp]
theorem fiberHomologyTransport_refl (b : B) :
    fiberHomologyTransport hp M n (Path.refl b) = 𝟙 _ := by
  rw [fiberHomologyTransport_eq_pullbackFiberTransport]
  exact pullbackFiberTransport_eq_id hp M n (TopCat.pathEquiv.symm (Path.refl b)).hom (b := b)
    ⟨⟨fun t ↦ TopCat.I.homeomorph.symm t, by fun_prop⟩,
      TopCat.I.homeomorph.symm_apply_eq.2 TopCat.I.homeomorph_zero.symm,
      TopCat.I.homeomorph.symm_apply_eq.2 TopCat.I.homeomorph_one.symm⟩
    (fun _ ↦ by rw [TopCat.pathEquiv_symm_hom_apply, Path.refl_apply]) (by simp) (by simp)

/-- **Transport is invariant under homotopy of paths** relative to their end points. -/
theorem fiberHomologyTransport_congr {γ γ' : Path b₀ b₁}
    (h : γ.Homotopic γ') :
    fiberHomologyTransport hp M n γ = fiberHomologyTransport hp M n γ' := by
  obtain ⟨F⟩ := h
  -- Transport over the square on which `F` is defined: transport along `γ` and `γ'` is transport
  -- along its left and right edges, and transport along its bottom and top edges, on which `F` is
  -- constant, is the identity.
  let g : TopCat.of (ULift.{u} (I × I)) ⟶ B :=
    TopCat.ofHom (F.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)
  let φ (s : I) : TopCat.I.{u} ⟶ TopCat.of (ULift.{u} (I × I)) :=
    TopCat.ofHom ⟨fun t ↦ ULift.up (s, TopCat.I.homeomorph t), by fun_prop⟩
  let edge (t : I) : Path (ULift.up ((0 : I), t)) (ULift.up ((1 : I), t)) :=
    ⟨⟨fun s ↦ ULift.up (s, t), by fun_prop⟩, rfl, rfl⟩
  have hl : fiberHomologyTransport hp M n γ = pullbackFiberTransport hp M n g
      (k₀ := ULift.up (0, 0)) (k₁ := ULift.up (0, 1)) (F.source 0) (F.target 0) :=
    pullbackFiberTransport_comp_left hp M n g _ (φ 0)
      (by ext t; simp [g, φ]) (by simp [φ]) (by simp [φ]) _ _ _ _
  have hr : fiberHomologyTransport hp M n γ' = pullbackFiberTransport hp M n g
      (k₀ := ULift.up (1, 0)) (k₁ := ULift.up (1, 1)) (F.source 1) (F.target 1) :=
    pullbackFiberTransport_comp_left hp M n g _ (φ 1)
      (by ext t; simp [g, φ]) (by simp [φ]) (by simp [φ]) _ _ _ _
  have hb := pullbackFiberTransport_eq_id hp M n g (edge 0) (fun s ↦ F.source s) (F.source 0)
    (F.source 1)
  have ht := pullbackFiberTransport_eq_id hp M n g (edge 1) (fun s ↦ F.target s) (F.target 0)
    (F.target 1)
  rw [hl, hr, ← Category.comp_id (pullbackFiberTransport hp M n g _ (F.target 0)), ← ht,
    pullbackFiberTransport_comp_pullbackFiberTransport,
    ← pullbackFiberTransport_comp_pullbackFiberTransport hp M n g _ (F.source 1), hb,
    Category.id_comp]

/-- **Transport along a concatenation is the composite of the transports.** -/
@[simp]
theorem fiberHomologyTransport_trans (γ : Path b₀ b₁)
    (δ : Path b₁ b₂) :
    fiberHomologyTransport hp M n (γ.trans δ) =
      fiberHomologyTransport hp M n γ ≫ fiberHomologyTransport hp M n δ := by
  -- Transport over the interval along `γ.trans δ` passes through the midpoint, and its two halves
  -- are transport along `γ` and along `δ`.
  rw [fiberHomologyTransport_eq_pullbackFiberTransport,
    fiberHomologyTransport_eq_pullbackFiberTransport,
    fiberHomologyTransport_eq_pullbackFiberTransport,
    ← pullbackFiberTransport_comp_pullbackFiberTransport hp M n _ _
      (TopCat.pathEquiv_symm_trans_hom_midpoint γ δ),
    pullbackFiberTransport_comp_left hp M n _ _ TopCat.I.firstHalf
      (TopCat.firstHalf_comp_pathEquiv_symm_trans_hom γ δ)
      TopCat.I.firstHalf_zero TopCat.I.firstHalf_one (TopCat.pathEquiv.symm γ).hom₀
      (TopCat.pathEquiv.symm γ).hom₁
      (TopCat.pathEquiv.symm (γ.trans δ)).hom₀ (TopCat.pathEquiv_symm_trans_hom_midpoint γ δ),
    pullbackFiberTransport_comp_left hp M n _ _ TopCat.I.secondHalf
      (TopCat.secondHalf_comp_pathEquiv_symm_trans_hom γ δ)
      TopCat.I.secondHalf_zero TopCat.I.secondHalf_one (TopCat.pathEquiv.symm δ).hom₀
      (TopCat.pathEquiv.symm δ).hom₁
      (TopCat.pathEquiv_symm_trans_hom_midpoint γ δ) (TopCat.pathEquiv.symm (γ.trans δ)).hom₁]

/-- **Transport along a path is natural in maps of Serre fibrations.** For a commutative square
from `p` to `p'` over `g : B ⟶ B'`, transport along `γ` followed by the map of fibres over `b₁` is
the map of fibres over `b₀` followed by transport along the image of `γ` under `g`. -/
@[reassoc]
theorem fiberHomologyTransport_naturality {E' B' : TopCat.{u}} {p' : E' ⟶ B'} {f : E ⟶ E'}
    {g : B ⟶ B'} (sq : CommSq f p p' g) (hp' : serreFibrations p') (γ : Path b₀ b₁) :
    fiberHomologyTransport hp M n γ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀) ≫
        fiberHomologyTransport hp' M n (γ.map g.hom.continuous) :=
  pullbackFiberTransport_naturality hp M n sq hp' (TopCat.pathEquiv.symm γ).hom
    (TopCat.pathEquiv.symm (γ.map g.hom.continuous)).hom (𝟙 _)
    (by rw [Category.id_comp, TopCat.pathEquiv_symm_map_hom])
    (TopCat.pathEquiv.symm γ).hom₀ (TopCat.pathEquiv.symm γ).hom₁ (by simp) (by simp)

/-- **The local system of fibre homology of a Serre fibration** `b ↦ Hₙ(p⁻¹(b); M)`, with
singular homology with coefficients in a module `M`. The class of a path acts by transport along
it (`TauCeti.TopCat.fiberHomologyTransport`). -/
def serreFiberLocalSystem : LocalCoefficientSystem.{w, u, u} R B where
  obj b := ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as)
  map {b₀ b₁} := Quotient.lift (fun γ ↦ fiberHomologyTransport hp M n γ)
    (fun _ _ h ↦ fiberHomologyTransport_congr hp M n h)
  -- The identity of the fundamental groupoid is the class of the constant path
  -- (`FundamentalGroupoid.id_eq_path_refl`).
  map_id b := fiberHomologyTransport_refl hp M n b.as
  -- Composition in the fundamental groupoid is the class of the concatenation
  -- (`FundamentalGroupoid.comp_eq`), on which `Quotient.lift` evaluates by definition.
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with | mk γ =>
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    exact fiberHomologyTransport_trans hp M n γ δ

/-- The value of the local system of fibre homology at a point is the homology of the fibre over
it. -/
def serreFiberLocalSystemObjIso (b : FundamentalGroupoid B) :
    (serreFiberLocalSystem hp M n).obj b ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as) :=
  Iso.refl _

/-- The local system of fibre homology sends the class of a path to transport along it. -/
@[simp]
theorem serreFiberLocalSystem_map_mk {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) :
    (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) =
      (serreFiberLocalSystemObjIso hp M n b₀).hom ≫ fiberHomologyTransport hp M n γ ≫
        (serreFiberLocalSystemObjIso hp M n b₁).inv := by
  simp only [serreFiberLocalSystemObjIso, Iso.refl_hom, Iso.refl_inv]
  -- `Quotient.lift` evaluates on the class of a path by definition.
  rfl

/-! ### Comparison with the transport of a lifting function -/

/-- **Transport on homology is induced by the transport of a lifting function.** If the Serre
fibration `p` has a lifting function `Λ`, transport along `γ` on the homology of the fibres is the
map induced by the transport map `Λ.transport γ`: the lifts of `γ` from the points of the fibre over
`b₀` form a homotopy, in `γ*E`, from the inclusion of that fibre to the transport followed by the
inclusion of the fibre over `b₁`. -/
theorem fiberHomologyTransport_eq_singularHomologyMap_fiberTransport
    (Λ : LiftingFunction p.hom) (γ : Path b₀ b₁) :
    fiberHomologyTransport hp M n γ =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberTransport Λ γ) := by
  refine ((eq_fiberHomologyTransport_iff hp M n γ _).2 ?_).symm
  let H : _root_.TopCat.Homotopy
      (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 0) (TopCat.pathEquiv.symm γ).hom₀)
      (fiberTransport Λ γ ≫
        p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 1) (TopCat.pathEquiv.symm γ).hom₁) :=
    { toFun x := ⟨(TopCat.I.homeomorph.symm x.1, Λ.lift x.2.val γ.toContinuousMap
          (γ.source.trans (x.2.property : p x.2.val = b₀).symm) x.1),
        (Λ.apply_lift _ _ _ x.1).symm⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
        exact continuous_eval.comp
          ((Λ.continuous_lift (by fun_prop) continuous_const _).prodMk continuous_fst)
      map_zero_left x := Subtype.ext <| by
        rw [TopCat.Hom.coe_pullbackFiberι_apply]
        exact Prod.ext rfl (Λ.lift_zero _ _ _)
      map_one_left x := Subtype.ext <| by
        rw [ConcreteCategory.comp_apply, TopCat.Hom.coe_pullbackFiberι_apply]
        exact Prod.ext rfl ((Λ.transport_apply_coe γ x).symm.trans
          (congrArg Subtype.val (ContinuousMap.congr_fun (fiberTransport_hom Λ γ).symm x))) }
  rw [← Functor.map_comp]
  exact (H.congr_homologyMap_singularChainComplexFunctor M n).symm

/-- **The local system of fibre homology agrees with the one of a lifting function.** For a Serre
fibration with a lifting function `Λ`, the local system `b ↦ Hₙ(p⁻¹(b); k)` of simplicial singular
homology with coefficients in a ring `k` is isomorphic, through the comparison of simplicial and
cubical singular homology, to `TauCeti.fiberLocalSystem Λ k n`, built from the transport maps of
`Λ` on normalized cubical chains. -/
def serreFiberLocalSystemIsoFiberLocalSystem
    (Λ : LiftingFunction p.hom) (k : Type u) [Ring k] :
    serreFiberLocalSystem hp (ModuleCat.of k k) n ≅ fiberLocalSystem Λ k n :=
  NatIso.ofComponents
    (fun b ↦ serreFiberLocalSystemObjIso hp _ n b ≪≫ (fiberLocalSystemSingularObjIso Λ k n b).symm)
    fun {b₀ b₁} q ↦ by
      induction q using Path.Homotopic.Quotient.ind with | mk γ =>
      rw [serreFiberLocalSystem_map_mk, fiberLocalSystem_map_mk_singular,
        fiberHomologyTransport_eq_singularHomologyMap_fiberTransport hp _ n Λ]
      -- `serreFiberLocalSystemObjIso` is the identity, and the map induced on
      -- `singularHomologyFunctor` is by definition the map induced on the homology of
      -- `singularChains`; `rw` cannot see through either, so `change` states both sides on the
      -- homology of `singularChains`.
      change HomologicalComplex.homologyMap ((singularChains k).map (fiberTransport Λ γ)) n ≫
          (fiberLocalSystemSingularObjIso Λ k n b₁).inv =
        (fiberLocalSystemSingularObjIso Λ k n b₀).inv ≫
          (fiberLocalSystemSingularObjIso Λ k n b₀).hom ≫
          HomologicalComplex.homologyMap ((singularChains k).map (fiberTransport Λ γ)) n ≫
          (fiberLocalSystemSingularObjIso Λ k n b₁).inv
      rw [Iso.inv_hom_id_assoc]

/-- The components of `TauCeti.TopCat.serreFiberLocalSystemIsoFiberLocalSystem` are the
comparisons of simplicial and cubical singular homology of the fibres. -/
@[simp]
theorem serreFiberLocalSystemIsoFiberLocalSystem_hom_app
    (Λ : LiftingFunction p.hom) (k : Type u) [Ring k] (b : FundamentalGroupoid B) :
    (serreFiberLocalSystemIsoFiberLocalSystem hp n Λ k).hom.app b =
      (serreFiberLocalSystemObjIso hp _ n b).hom ≫ (fiberLocalSystemSingularObjIso Λ k n b).inv :=
  (rfl)

end Path

section Restriction

variable (C : Set B) (R : Type u) [Ring R] (hp : serreFibrations p)

/-- The local system of fibre homology `b ↦ Hq(p⁻¹(b); R)` of a Serre fibration `p`, restricted to
a subspace `C ⊆ B`. -/
abbrev serreFiberLocalSystemOn (q : ℕ) : LocalCoefficientSystem.{u, u, u} R (TopCat.of C) :=
  (LocalCoefficientSystem.pullback ⟨Subtype.val, continuous_subtypeVal⟩).obj
    (serreFiberLocalSystem hp (ModuleCat.of R R) q)

end Restriction

end TauCeti.TopCat

/-! ### Maps of Serre fibrations -/

namespace CategoryTheory.CommSq

open TauCeti TauCeti.TopCat

variable {E B E' B' : TopCat.{u}} {f : E ⟶ E'} {p : E ⟶ B} {p' : E' ⟶ B'} {g : B ⟶ B'}
  (sq : CommSq f p p' g) (hp : serreFibrations p) (hp' : serreFibrations p') {R : Type w} [Ring R]
  (M : ModuleCat.{u} R) (n : ℕ)

/-- **Functoriality of the local system of fibre homology in maps of Serre fibrations.** A
commutative square from `p` to `p'` over `g` maps the local system of fibre homology of `p` to the
pullback along `g` of that of `p'`, acting on the fibre over each point by the map induced by
`CommSq.fiberMap`. -/
def serreFiberLocalSystemMap :
    serreFiberLocalSystem hp M n ⟶
      (LocalCoefficientSystem.pullback g.hom).obj (serreFiberLocalSystem hp' M n) where
  app b :=
    (serreFiberLocalSystemObjIso hp M n b).hom ≫
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
      (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv
  naturality {b₀ b₁} q := by
    induction q using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The pulled-back functor agrees with `serreFiberLocalSystem hp' M n` on `.mk (g b.as)` only
    -- up to unfolding `FundamentalGroupoid.map`, so `change` aligns the endpoints before `rw`.
    change (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) ≫
        ((serreFiberLocalSystemObjIso hp M n b₁).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (g b₁.as))).inv) =
      ((serreFiberLocalSystemObjIso hp M n b₀).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (g b₀.as))).inv) ≫
        (serreFiberLocalSystem hp' M n).map
          (Path.Homotopic.Quotient.mk (γ.map g.hom.continuous))
    rw [serreFiberLocalSystem_map_mk, serreFiberLocalSystem_map_mk]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact fiberHomologyTransport_naturality hp M n sq hp' γ

/-- On the fibre over `b`, the map of local systems induced by a map of Serre fibrations is the map
induced on homology by the map of fibres. -/
@[simp]
theorem serreFiberLocalSystemMap_app (b : FundamentalGroupoid B) :
    (sq.serreFiberLocalSystemMap hp hp' M n).app b =
      (serreFiberLocalSystemObjIso hp M n b).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
        (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv :=
  (rfl)

/-- When a map of Serre fibrations induces weak homotopy equivalences of all fibres, as for the
base change of a Serre fibration along any map, the induced map of local systems of fibre homology
is an isomorphism. -/
theorem isIso_serreFiberLocalSystemMap (h : ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) :
    IsIso (sq.serreFiberLocalSystemMap hp hp' M n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro b
  have := (h b.as).isIso_singularHomologyMap M n
  -- Unfold `app b` across the definitional equality `(FundamentalGroupoid.map g.hom).obj b =
  -- .mk (g b.as)` so each factor's domain and codomain match at reducible transparency.
  change IsIso ((serreFiberLocalSystemObjIso hp M n b).hom ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
    (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv)
  infer_instance

end CategoryTheory.CommSq
