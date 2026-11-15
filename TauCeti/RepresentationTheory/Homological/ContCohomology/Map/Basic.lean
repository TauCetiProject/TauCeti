/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology.Map
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Functoriality of continuous cohomology in all degrees across independent universes

Mathlib's `ContinuousCohomology.map` pulls continuous cohomology back along a compatible pair
`(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)`, but because `TopRep.Hom` and `TopModuleCat.Hom` live in a
single universe, it requires `G` and `H` to share one universe and `X` and `Y` to share one
universe. The low-degree files `Map/DegreeOne.lean` and `Map/DegreeTwo.lean` lift that restriction
in degrees `1` and `2` for discrete modules (and locally compact groups in degree `2`) by passing
through explicit inhomogeneous cochains.

On the canonical homogeneous cochain complex `TopRep.homogeneousCochains`, however, pullback along
a compatible pair needs neither discreteness, nor local compactness, nor low degree: Mathlib's
unbundled `ContRepresentation.coind₁ResMap` and `ContIntertwiningMap.mapInvariantsOfRes` already
operate across independent group and representation universes. Combining them with the
cross-universe cycle and homology maps of `TauCeti.Algebra.Category.ModuleCat.Topology.Homology.Map`
yields continuous `k`-linear maps and equivalences in **every** degree `n` for **arbitrary**
topological rings `k`, **arbitrary** topological groups `G` and `H`, and **arbitrary** continuous
representations `X` and `Y` in independent universes:

* `TauCeti.ContCohomology.resolutionXResMap` and `TauCeti.ContCohomology.homogeneousCochainsResMap`:
  pullback on the coinduced resolution and on homogeneous cochains;
* `TauCeti.ContCohomology.cocyclesResMap` and `TauCeti.ContCohomology.continuousCohomologyResMap`:
  continuous `k`-linear pullback on canonical cocycles and canonical continuous cohomology in every
  degree, agreeing with `ContinuousCohomology.cocyclesMap` and `ContinuousCohomology.map` in a
  single universe;
* `TauCeti.ContCohomology.homogeneousCochainsResCLE`, `TauCeti.ContCohomology.cocyclesResCLE` and
  `TauCeti.ContCohomology.continuousCohomologyResCLE`: continuous `k`-linear equivalences induced by
  a topological group isomorphism `φ : H ≃ₜ* G` and an equivalence of continuous representations
  `e : (X.ρ.restrict φ).Equiv Y.ρ`;
* `TauCeti.ContCohomology.continuousCohomologyUniverseCLE`: for `G : Type u` and
  `X : TopRep.{u} k G`, the canonical continuous `k`-linear equivalence between
  `continuousCohomology.{uk, u, u} n X` and `continuousCohomology.{uk, u, 0} n X`, preserving
  cocycle classes and cocycle values and natural in compatible pairs and coefficient maps.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2 and §5:
  homogeneous cochains and functoriality under compatible pairs.
-/

public noncomputable section

open CategoryTheory ContRepresentation

namespace TauCeti.ContCohomology

universe vX vY vZ uk uG uH uK

section ResolutionAndCochains

variable {k : Type uk} [Ring k] [TopologicalSpace k]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max uG vX, uk, uG} k G} {Y : TopRep.{max uH vY, uk, uH} k H}

/-- Pullback between the terms of the canonical coinduced resolutions of `X` and `Y` along a
continuous homomorphism `φ : H →ₜ* G` and a continuous intertwining map
`f : X.ρ.restrict φ →ⁱL Y.ρ`, with the universes of `G`, `H`, `X` and `Y` independent. -/
def resolutionXResMap (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) :
    (i : ℕ) →
      (TopRep.resolutionX.{uk, uG, vX} X i).ρ.restrict (φ : H →* G) →ⁱL
        (TopRep.resolutionX.{uk, uH, vY} Y i).ρ
  | 0 => f
  | i + 1 => coind₁ResMap φ (resolutionXResMap φ f i)

/-- In resolution degree zero, `resolutionXResMap` is the given intertwining map `f`. -/
@[simp]
theorem resolutionXResMap_zero (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) :
    resolutionXResMap.{vX, vY} φ f 0 = f :=
  (rfl)

/-- In resolution degree `i + 1`, `resolutionXResMap` is `coind₁ResMap` of the degree-`i` map. -/
theorem resolutionXResMap_succ (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (i : ℕ) :
    resolutionXResMap.{vX, vY} φ f (i + 1) =
      coind₁ResMap φ (resolutionXResMap.{vX, vY} φ f i) :=
  (rfl)

/-- Pointwise in degree `i + 1`, `resolutionXResMap` precomposes with `φ` and postcomposes with
the degree-`i` map. -/
@[simp]
theorem resolutionXResMap_succ_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (i : ℕ) (F : (TopRep.resolutionX.{uk, uG, vX} X (i + 1)).V) (h : H) :
    DFunLike.coe (F := C(H, (TopRep.resolutionX.{uk, uH, vY} Y i).V))
        (resolutionXResMap.{vX, vY} φ f (i + 1) F) h =
      resolutionXResMap.{vX, vY} φ f i
        (DFunLike.coe (F := C(G, (TopRep.resolutionX.{uk, uG, vX} X i).V)) F (φ h)) :=
  (rfl)

/-- `resolutionXResMap` intertwines the action of `φ h` on the resolution of `X` with the action
of `h` on the resolution of `Y`. -/
theorem resolutionXResMap_ρ_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (i : ℕ) (h : H) (x : (TopRep.resolutionX.{uk, uG, vX} X i).V) :
    resolutionXResMap.{vX, vY} φ f i ((TopRep.resolutionX.{uk, uG, vX} X i).ρ (φ h) x) =
      (TopRep.resolutionX.{uk, uH, vY} Y i).ρ h (resolutionXResMap.{vX, vY} φ f i x) :=
  (resolutionXResMap.{vX, vY} φ f i).isIntertwining h x

/-- `resolutionXResMap` commutes with the recursive differentials `TopRep.d` of the coinduced
resolutions. -/
theorem resolutionXResMap_comp_d (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (i : ℕ) :
    (TopRep.d.{uk, uH, vY} Y i).hom.comp (resolutionXResMap.{vX, vY} φ f i) =
      (resolutionXResMap.{vX, vY} φ f (i + 1)).comp
        ((TopRep.d.{uk, uG, vX} X i).hom.restrict (φ : H →* G)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [resolutionXResMap_succ, TopRep.hom_d_succ, ContIntertwiningMap.restrict_sub,
      ContIntertwiningMap.sub_comp, ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict]
    rw [ih, resolutionXResMap_succ, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- Pointwise form of `resolutionXResMap_comp_d`. -/
theorem resolutionXResMap_d_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (i : ℕ)
    (x : (TopRep.resolutionX.{uk, uG, vX} X i).V) :
    (TopRep.d.{uk, uH, vY} Y i).hom (resolutionXResMap.{vX, vY} φ f i x) =
      resolutionXResMap.{vX, vY} φ f (i + 1) ((TopRep.d.{uk, uG, vX} X i).hom x) :=
  congr($(resolutionXResMap_comp_d.{vX, vY} φ f i) x)

/-- Continuous `k`-linear pullback on degree-`n` homogeneous cochains along `(φ, f)`, with the
universes of `G`, `H`, `X` and `Y` independent. -/
def homogeneousCochainsResMap (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (n : ℕ) :
    (TopRep.homogeneousCochains.{uk, uG, vX} X).X n →L[k]
      (TopRep.homogeneousCochains.{uk, uH, vY} Y).X n :=
  (resolutionXResMap.{vX, vY} φ f (n + 1)).mapInvariantsOfRes (φ : H →* G)

/-- On the underlying invariant function in degree `n + 1` of the resolution,
`homogeneousCochainsResMap` acts as `resolutionXResMap`. -/
theorem coe_homogeneousCochainsResMap_apply (φ : H →ₜ* G)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{uk, uG, vX} X).X n) :
    (homogeneousCochainsResMap.{vX, vY} φ f n σ).val =
      resolutionXResMap.{vX, vY} φ f (n + 1) σ.val :=
  (rfl)

/-- `homogeneousCochainsResMap` commutes with the differentials of `TopRep.homogeneousCochains`. -/
theorem homogeneousCochainsResMap_comm_d (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j)
    (σ : (TopRep.homogeneousCochains.{uk, uG, vX} X).X i) :
    ((TopRep.homogeneousCochains.{uk, uH, vY} Y).d i j).hom
        (homogeneousCochainsResMap.{vX, vY} φ f i σ) =
      homogeneousCochainsResMap.{vX, vY} φ f j
        (((TopRep.homogeneousCochains.{uk, uG, vX} X).d i j).hom σ) := by
  obtain rfl : i + 1 = j := hij
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply, coe_homogeneousCochainsResMap_apply,
    coe_homogeneousCochainsResMap_apply, TopRep.homogeneousCochains.d_apply,
    resolutionXResMap_d_apply]

/-- Continuous `k`-linear pullback on canonical degree-`n` cocycles along `(φ, f)`, with
independent universes. -/
def cocyclesResMap (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (n : ℕ) :
    _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n →L[k]
      _root_.ContinuousCohomology.cocycles.{uk, uH, vY} Y n :=
  HomologicalComplex.cyclesMapCLM
    (TopRep.homogeneousCochains.{uk, uG, vX} X)
    (TopRep.homogeneousCochains.{uk, uH, vY} Y)
    (homogeneousCochainsResMap.{vX, vY} φ f)
    (homogeneousCochainsResMap_comm_d.{vX, vY} φ f) n

/-- Under the cycle inclusion `iCycles`, `cocyclesResMap` acts on homogeneous cochains as
`homogeneousCochainsResMap`. -/
theorem iCycles_cocyclesResMap_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (n : ℕ) (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n) :
    (TopRep.homogeneousCochains.{uk, uH, vY} Y).iCycles n (cocyclesResMap.{vX, vY} φ f n z) =
      homogeneousCochainsResMap.{vX, vY} φ f n
        ((TopRep.homogeneousCochains.{uk, uG, vX} X).iCycles n z) :=
  HomologicalComplex.iCycles_cyclesMapCLM_apply _ _ _ _ n z

/-- In degree zero, `cocyclesResMap` sends a homogeneous cocycle `z` to `h₀ ↦ f (z (φ h₀))`. -/
theorem iCycles_cocyclesResMap_zero_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X 0) (h₀ : H) :
    ((TopRep.homogeneousCochains.{uk, uH, vY} Y).iCycles 0
        (cocyclesResMap.{vX, vY} φ f 0 z)).val h₀ =
      f (((TopRep.homogeneousCochains.{uk, uG, vX} X).iCycles 0 z).val (φ h₀)) := by
  rw [iCycles_cocyclesResMap_apply, coe_homogeneousCochainsResMap_apply]
  exact resolutionXResMap_succ_apply.{vX, vY} φ f 0 _ h₀

/-- In degree one, `cocyclesResMap` sends a homogeneous cocycle `z` to
`(h₀, h₁) ↦ f (z (φ h₀) (φ h₁))`. -/
theorem iCycles_cocyclesResMap_one_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X 1) (h₀ h₁ : H) :
    ((TopRep.homogeneousCochains.{uk, uH, vY} Y).iCycles 1
        (cocyclesResMap.{vX, vY} φ f 1 z)).val h₀ h₁ =
      f (((TopRep.homogeneousCochains.{uk, uG, vX} X).iCycles 1 z).val (φ h₀) (φ h₁)) := by
  rw [iCycles_cocyclesResMap_apply, coe_homogeneousCochainsResMap_apply]
  exact (congrArg (fun w : C(H, Y.V) ↦ w h₁)
    (resolutionXResMap_succ_apply.{vX, vY} φ f 1 _ h₀)).trans
    (resolutionXResMap_succ_apply.{vX, vY} φ f 0 _ h₁)

/-- In degree two, `cocyclesResMap` sends a homogeneous cocycle `z` to
`(h₀, h₁, h₂) ↦ f (z (φ h₀) (φ h₁) (φ h₂))`. -/
theorem iCycles_cocyclesResMap_two_apply (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X 2) (h₀ h₁ h₂ : H) :
    ((TopRep.homogeneousCochains.{uk, uH, vY} Y).iCycles 2
        (cocyclesResMap.{vX, vY} φ f 2 z)).val h₀ h₁ h₂ =
      f (((TopRep.homogeneousCochains.{uk, uG, vX} X).iCycles 2 z).val
        (φ h₀) (φ h₁) (φ h₂)) := by
  rw [iCycles_cocyclesResMap_apply, coe_homogeneousCochainsResMap_apply]
  exact (congrArg (fun w : C(H, C(H, Y.V)) ↦ w h₁ h₂)
    (resolutionXResMap_succ_apply.{vX, vY} φ f 2 _ h₀)).trans
    ((congrArg (fun w : C(H, Y.V) ↦ w h₂)
      (resolutionXResMap_succ_apply.{vX, vY} φ f 1 _ h₁)).trans
      (resolutionXResMap_succ_apply.{vX, vY} φ f 0 _ h₂))

/-- **Pullback on canonical continuous cohomology in all degrees across independent universes.**
Given a continuous group homomorphism `φ : H →ₜ* G` and a continuous intertwining map
`f : X.ρ.restrict φ →ⁱL Y.ρ`, `continuousCohomologyResMap` is the induced continuous `k`-linear map
`Hⁿ(G, X) →L[k] Hⁿ(H, Y)`. -/
def continuousCohomologyResMap (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (n : ℕ) :
    continuousCohomology.{uk, uG, vX} n X →L[k] continuousCohomology.{uk, uH, vY} n Y :=
  HomologicalComplex.homologyMapCLM
    (TopRep.homogeneousCochains.{uk, uG, vX} X)
    (TopRep.homogeneousCochains.{uk, uH, vY} Y)
    (homogeneousCochainsResMap.{vX, vY} φ f)
    (homogeneousCochainsResMap_comm_d.{vX, vY} φ f) n

/-- **The map on classes is induced by the map on cocycles.** `continuousCohomologyResMap` carries
the canonical cohomology class of a cocycle `z` to the canonical class of
`cocyclesResMap φ f n z`. -/
@[simp]
theorem continuousCohomologyResMap_π (φ : H →ₜ* G) (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ)
    (n : ℕ) (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n) :
    continuousCohomologyResMap.{vX, vY} φ f n (_root_.ContinuousCohomology.π.{uk, uG, vX} X n z) =
      _root_.ContinuousCohomology.π.{uk, uH, vY} Y n (cocyclesResMap.{vX, vY} φ f n z) :=
  HomologicalComplex.homologyMapCLM_homologyπ _ _ _ _ n z

/-- Two compatible pairs with propositionally equal homomorphisms and pointwise equal coefficient
maps induce the same map on continuous cohomology. -/
theorem continuousCohomologyResMap_congr {φ ψ : H →ₜ* G} (hφ : φ = ψ)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (g : X.ρ.restrict (ψ : H →* G) →ⁱL Y.ρ)
    (hfg : ∀ x : X.V, f x = g x) (n : ℕ) :
    continuousCohomologyResMap.{vX, vY} φ f n = continuousCohomologyResMap.{vX, vY} ψ g n := by
  subst hφ
  congr 1
  exact ContIntertwiningMap.ext (ContinuousLinearMap.ext hfg)

end ResolutionAndCochains

section Functoriality

variable {k : Type uk} [Ring k] [TopologicalSpace k]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- When `φ : G →ₜ* G` and `f : X.ρ.restrict φ →ⁱL X.ρ` act as the identity on elements (at a
single extra universe parameter), `resolutionXResMap φ f i` acts as the identity in every degree. -/
theorem resolutionXResMap_apply_eq_self {X : TopRep.{max uG vX, uk, uG} k G}
    {φ : G →ₜ* G} (hφ : ∀ g, φ g = g)
    {f : X.ρ.restrict (φ : G →* G) →ⁱL X.ρ} (hf : ∀ x, f x = x) :
    ∀ (i : ℕ) (x : (TopRep.resolutionX.{uk, uG, vX} X i).V),
      resolutionXResMap.{vX, vX} φ f i x = x
  | 0, x => hf x
  | i + 1, F => by
    ext g
    rw [resolutionXResMap_succ_apply, hφ g, resolutionXResMap_apply_eq_self hφ hf i]

/-- `resolutionXResMap` respects composition across three independent group and coefficient
universes. -/
theorem resolutionXResMap_comp {X : TopRep.{max uG vX, uk, uG} k G}
    {Y : TopRep.{max uH vY, uk, uH} k H} {Z : TopRep.{max uK vZ, uk, uK} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (g : Y.ρ.restrict (ψ : K →* H) →ⁱL Z.ρ) :
    ∀ i : ℕ,
      resolutionXResMap.{vX, vZ} (φ.comp ψ) (g.comp (f.restrict (ψ : K →* H))) i =
        (resolutionXResMap.{vY, vZ} ψ g i).comp
          ((resolutionXResMap.{vX, vY} φ f i).restrict (ψ : K →* H))
  | 0 => rfl
  | i + 1 => by
    rw [resolutionXResMap_succ, resolutionXResMap_succ, resolutionXResMap_succ,
      resolutionXResMap_comp φ ψ f g i]
    ext F x
    rfl

/-- When `φ` and `f` act as the identity on elements (at a single extra universe parameter),
`homogeneousCochainsResMap φ f n` is the identity continuous linear map. -/
theorem homogeneousCochainsResMap_eq_id {X : TopRep.{max uG vX, uk, uG} k G}
    {φ : G →ₜ* G} (hφ : ∀ g, φ g = g)
    {f : X.ρ.restrict (φ : G →* G) →ⁱL X.ρ} (hf : ∀ x, f x = x) (n : ℕ) :
    homogeneousCochainsResMap.{vX, vX} φ f n =
      ContinuousLinearMap.id k ((TopRep.homogeneousCochains.{uk, uG, vX} X).X n) := by
  ext σ
  apply Subtype.ext
  exact (coe_homogeneousCochainsResMap_apply.{vX, vX} φ f n σ).trans
    (resolutionXResMap_apply_eq_self.{vX} hφ hf (n + 1) σ.val)

/-- `homogeneousCochainsResMap` respects composition across three independent universes. -/
theorem homogeneousCochainsResMap_comp {X : TopRep.{max uG vX, uk, uG} k G}
    {Y : TopRep.{max uH vY, uk, uH} k H} {Z : TopRep.{max uK vZ, uk, uK} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (g : Y.ρ.restrict (ψ : K →* H) →ⁱL Z.ρ) (n : ℕ) :
    homogeneousCochainsResMap.{vX, vZ} (φ.comp ψ) (g.comp (f.restrict (ψ : K →* H))) n =
      (homogeneousCochainsResMap.{vY, vZ} ψ g n).comp
        (homogeneousCochainsResMap.{vX, vY} φ f n) := by
  ext σ
  apply Subtype.ext
  rw [ContinuousLinearMap.comp_apply, coe_homogeneousCochainsResMap_apply,
    coe_homogeneousCochainsResMap_apply, coe_homogeneousCochainsResMap_apply,
    resolutionXResMap_comp.{vX, vY, vZ} φ ψ f g (n + 1)]
  rfl

/-- When `φ` and `f` act as the identity on elements, `cocyclesResMap φ f n` is the identity
continuous linear map. -/
theorem cocyclesResMap_eq_id {X : TopRep.{max uG vX, uk, uG} k G}
    {φ : G →ₜ* G} (hφ : ∀ g, φ g = g)
    {f : X.ρ.restrict (φ : G →* G) →ⁱL X.ρ} (hf : ∀ x, f x = x) (n : ℕ) :
    cocyclesResMap.{vX, vX} φ f n =
      ContinuousLinearMap.id k (_root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n) := by
  rw [cocyclesResMap, ← HomologicalComplex.cyclesMapCLM_id]
  refine HomologicalComplex.cyclesMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [homogeneousCochainsResMap_eq_id.{vX} hφ hf n]

/-- `cocyclesResMap` respects composition across three independent universes. -/
theorem cocyclesResMap_comp {X : TopRep.{max uG vX, uk, uG} k G}
    {Y : TopRep.{max uH vY, uk, uH} k H} {Z : TopRep.{max uK vZ, uk, uK} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (g : Y.ρ.restrict (ψ : K →* H) →ⁱL Z.ρ) (n : ℕ) :
    cocyclesResMap.{vX, vZ} (φ.comp ψ) (g.comp (f.restrict (ψ : K →* H))) n =
      (cocyclesResMap.{vY, vZ} ψ g n).comp (cocyclesResMap.{vX, vY} φ f n) := by
  rw [cocyclesResMap, cocyclesResMap, cocyclesResMap, ← HomologicalComplex.cyclesMapCLM_comp]
  refine HomologicalComplex.cyclesMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [homogeneousCochainsResMap_comp.{vX, vY, vZ} φ ψ f g n]

/-- When `φ` and `f` act as the identity on elements, `continuousCohomologyResMap φ f n` is the
identity continuous linear map. -/
theorem continuousCohomologyResMap_eq_id {X : TopRep.{max uG vX, uk, uG} k G}
    {φ : G →ₜ* G} (hφ : ∀ g, φ g = g)
    {f : X.ρ.restrict (φ : G →* G) →ⁱL X.ρ} (hf : ∀ x, f x = x) (n : ℕ) :
    continuousCohomologyResMap.{vX, vX} φ f n =
      ContinuousLinearMap.id k (continuousCohomology.{uk, uG, vX} n X) := by
  rw [continuousCohomologyResMap, ← HomologicalComplex.homologyMapCLM_id]
  refine HomologicalComplex.homologyMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [homogeneousCochainsResMap_eq_id.{vX} hφ hf n]

/-- `continuousCohomologyResMap` respects composition across three independent universes. -/
theorem continuousCohomologyResMap_comp {X : TopRep.{max uG vX, uk, uG} k G}
    {Y : TopRep.{max uH vY, uk, uH} k H} {Z : TopRep.{max uK vZ, uk, uK} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : X.ρ.restrict (φ : H →* G) →ⁱL Y.ρ) (g : Y.ρ.restrict (ψ : K →* H) →ⁱL Z.ρ) (n : ℕ) :
    continuousCohomologyResMap.{vX, vZ} (φ.comp ψ) (g.comp (f.restrict (ψ : K →* H))) n =
      (continuousCohomologyResMap.{vY, vZ} ψ g n).comp
        (continuousCohomologyResMap.{vX, vY} φ f n) := by
  rw [continuousCohomologyResMap, continuousCohomologyResMap, continuousCohomologyResMap,
    ← HomologicalComplex.homologyMapCLM_comp]
  refine HomologicalComplex.homologyMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [homogeneousCochainsResMap_comp.{vX, vY, vZ} φ ψ f g n]

end Functoriality

section SameUniverse

variable {k : Type uk} [Ring k] [TopologicalSpace k]
  {G H : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max uG vX, uk, uG} k G} {Y : TopRep.{max uG vX, uk, uG} k H}

/-- In a single universe, `resolutionXResMap` is the underlying intertwining map of Mathlib's
`ContinuousCohomology.resolutionMap`. -/
theorem hom_resolutionMap (φ : H →ₜ* G) (g : TopRep.res (φ : H →* G) X ⟶ Y) :
    ∀ i : ℕ, (_root_.ContinuousCohomology.resolutionMap φ g i).hom =
      resolutionXResMap.{vX, vX} φ g.hom i
  | 0 => rfl
  | i + 1 => by
    rw [_root_.ContinuousCohomology.resolutionMap_succ, resolutionXResMap_succ,
      TopRep.hom_ofHom, hom_resolutionMap φ g i]

/-- In a single universe, `homogeneousCochainsResMap` is the underlying continuous linear map of
`ContinuousCohomology.cochainsMap`. -/
theorem hom_cochainsMap_f (φ : H →ₜ* G) (g : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    ((_root_.ContinuousCohomology.cochainsMap φ g).f n).hom =
      homogeneousCochainsResMap.{vX, vX} φ g.hom n := by
  rw [_root_.ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap, TopModuleCat.hom_ofHom,
    homogeneousCochainsResMap, hom_resolutionMap]

/-- In a single universe, `cocyclesResMap` is the underlying continuous linear map of
`ContinuousCohomology.cocyclesMap`. -/
theorem hom_cocyclesMap (φ : H →ₜ* G) (g : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    (_root_.ContinuousCohomology.cocyclesMap φ g n).hom =
      cocyclesResMap.{vX, vX} φ g.hom n := by
  rw [_root_.ContinuousCohomology.cocyclesMap, HomologicalComplex.hom_cyclesMap]
  refine HomologicalComplex.cyclesMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [hom_cochainsMap_f]

/-- In a single universe, `continuousCohomologyResMap` is the underlying continuous linear map of
Mathlib's `ContinuousCohomology.map`. -/
theorem hom_map (φ : H →ₜ* G) (g : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    (_root_.ContinuousCohomology.map φ g n).hom =
      continuousCohomologyResMap.{vX, vX} φ g.hom n := by
  rw [_root_.ContinuousCohomology.map, HomologicalComplex.hom_homologyMap]
  refine HomologicalComplex.homologyMapCLM_congr _ _ _ _ fun z ↦ ?_
  rw [hom_cochainsMap_f]

/-- In a single universe, `continuousCohomologyResMap` at `φ = id` is the underlying continuous
linear map of `TauCeti.ContinuousCohomology.coeffMap`. -/
theorem hom_coeffMap {X' : TopRep.{max uG vX, uk, uG} k G} (g : X ⟶ X') (n : ℕ) :
    (TauCeti.ContinuousCohomology.coeffMap g n).hom =
      continuousCohomologyResMap.{vX, vX} (ContinuousMonoidHom.id G) g.hom n := by
  rw [TauCeti.ContinuousCohomology.coeffMap_def]
  exact hom_map (ContinuousMonoidHom.id G) g n

end SameUniverse

private theorem comp_restrict_apply {R G₁' G₂' G₃' V W U : Type*} [Ring R]
    [Monoid G₁'] [Monoid G₂'] [Monoid G₃']
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [AddCommGroup U] [Module R U] [TopologicalSpace U] [IsTopologicalAddGroup U]
    {π₁ : ContRepresentation R G₁' V} {π₂ : ContRepresentation R G₂' W}
    {π₃ : ContRepresentation R G₃' U} {φ : G₂' →* G₁'} {ψ : G₃' →* G₂'}
    (f : π₂.restrict ψ →ⁱL π₃) (g : π₁.restrict φ →ⁱL π₂) (v : V) :
    (f.comp (g.restrict ψ)) v = f (g v) :=
  (rfl)

private theorem toContIntertwiningMap_apply {R G' V W : Type*} [Ring R] [Monoid G']
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    {ρ : ContRepresentation R G' V} {σ : ContRepresentation R G' W} (φ : ρ.Equiv σ) (v : V) :
    φ.toContIntertwiningMap v = φ v :=
  (rfl)

section Equiv

variable {k : Type uk} [Ring k] [TopologicalSpace k]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max uG vX, uk, uG} k G} {Y : TopRep.{max uH vY, uk, uH} k H}

/-- Continuous `k`-linear equivalence on degree-`n` homogeneous cochains induced by a topological
group isomorphism `φ : H ≃ₜ* G` and an equivalence of continuous representations
`e : (X.ρ.restrict φ).Equiv Y.ρ` across independent universes. -/
def homogeneousCochainsResCLE (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ) :
    (TopRep.homogeneousCochains.{uk, uG, vX} X).X n ≃L[k]
      (TopRep.homogeneousCochains.{uk, uH, vY} Y).X n :=
  let e' : (Y.ρ.restrict ((φ.symm : G →ₜ* H) : G →* H)).Equiv X.ρ :=
    e.symmRestrict ((φ.symm : G →ₜ* H) : G →* H) φ.apply_symm_apply
  ContinuousLinearEquiv.equivOfInverse
    (homogeneousCochainsResMap.{vX, vY} (φ : H →ₜ* G) e.toContIntertwiningMap n)
    (homogeneousCochainsResMap.{vY, vX} (φ.symm : G →ₜ* H) e'.toContIntertwiningMap n)
    (fun σ ↦ by
      have hcomp := DFunLike.congr_fun
        (homogeneousCochainsResMap_comp.{vX, vY, vX} (φ : H →ₜ* G) (φ.symm : G →ₜ* H)
          e.toContIntertwiningMap e'.toContIntertwiningMap n) σ
      have hid := DFunLike.congr_fun
        (homogeneousCochainsResMap_eq_id.{vX} (X := X)
          (φ := (φ : H →ₜ* G).comp (φ.symm : G →ₜ* H)) φ.apply_symm_apply
          (f := e'.toContIntertwiningMap.comp
            (e.toContIntertwiningMap.restrict ((φ.symm : G →ₜ* H) : G →* H)))
          (fun x ↦ (comp_restrict_apply e'.toContIntertwiningMap e.toContIntertwiningMap x).trans
            ((toContIntertwiningMap_apply e' _).trans
              ((congrArg e' (toContIntertwiningMap_apply e x)).trans
                ((Equiv.symmRestrict_apply e _ _ (e x)).trans (e.symm_apply_apply x))))) n) σ
      exact hcomp.symm.trans hid)
    (fun σ ↦ by
      have hcomp := DFunLike.congr_fun
        (homogeneousCochainsResMap_comp.{vY, vX, vY} (φ.symm : G →ₜ* H) (φ : H →ₜ* G)
          e'.toContIntertwiningMap e.toContIntertwiningMap n) σ
      have hid := DFunLike.congr_fun
        (homogeneousCochainsResMap_eq_id.{vY} (X := Y)
          (φ := (φ.symm : G →ₜ* H).comp (φ : H →ₜ* G)) φ.symm_apply_apply
          (f := e.toContIntertwiningMap.comp
            (e'.toContIntertwiningMap.restrict ((φ : H →ₜ* G) : H →* G)))
          (fun y ↦ (comp_restrict_apply e.toContIntertwiningMap e'.toContIntertwiningMap y).trans
            ((toContIntertwiningMap_apply e _).trans
              ((congrArg e (toContIntertwiningMap_apply e' y)).trans
                ((congrArg e (Equiv.symmRestrict_apply e _ _ y)).trans
                  (e.apply_symm_apply y))))) n) σ
      exact hcomp.symm.trans hid)

/-- Forward evaluation of `homogeneousCochainsResCLE`. -/
theorem homogeneousCochainsResCLE_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ)
    (n : ℕ) (σ : (TopRep.homogeneousCochains.{uk, uG, vX} X).X n) :
    homogeneousCochainsResCLE.{vX, vY} φ e n σ =
      homogeneousCochainsResMap.{vX, vY} (φ : H →ₜ* G) e.toContIntertwiningMap n σ :=
  (rfl)

/-- Inverse evaluation of `homogeneousCochainsResCLE`. -/
theorem homogeneousCochainsResCLE_symm_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{uk, uH, vY} Y).X n) :
    (homogeneousCochainsResCLE.{vX, vY} φ e n).symm σ =
      homogeneousCochainsResMap.{vY, vX} (φ.symm : G →ₜ* H)
        (e.symmRestrict ((φ.symm : G →ₜ* H) : G →* H) φ.apply_symm_apply).toContIntertwiningMap
        n σ :=
  (rfl)

/-- `homogeneousCochainsResCLE` commutes with the differentials of `TopRep.homogeneousCochains`. -/
theorem homogeneousCochainsResCLE_comm_d (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j)
    (σ : (TopRep.homogeneousCochains.{uk, uG, vX} X).X i) :
    ((TopRep.homogeneousCochains.{uk, uH, vY} Y).d i j).hom
        (homogeneousCochainsResCLE.{vX, vY} φ e i σ) =
      homogeneousCochainsResCLE.{vX, vY} φ e j
        (((TopRep.homogeneousCochains.{uk, uG, vX} X).d i j).hom σ) := by
  simp only [homogeneousCochainsResCLE_apply]
  exact homogeneousCochainsResMap_comm_d.{vX, vY} (φ : H →ₜ* G) e.toContIntertwiningMap i j hij σ

/-- Continuous `k`-linear equivalence on canonical degree-`n` cocycles induced by a topological
group isomorphism `φ : H ≃ₜ* G` and an equivalence of continuous representations
`e : (X.ρ.restrict φ).Equiv Y.ρ` across independent universes. -/
def cocyclesResCLE (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ) :
    _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n ≃L[k]
      _root_.ContinuousCohomology.cocycles.{uk, uH, vY} Y n :=
  HomologicalComplex.cyclesMapCLE
    (TopRep.homogeneousCochains.{uk, uG, vX} X)
    (TopRep.homogeneousCochains.{uk, uH, vY} Y)
    (homogeneousCochainsResCLE.{vX, vY} φ e)
    (homogeneousCochainsResCLE_comm_d.{vX, vY} φ e) n

/-- Forward evaluation of `cocyclesResCLE`. -/
@[simp]
theorem cocyclesResCLE_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n) :
    cocyclesResCLE.{vX, vY} φ e n z =
      cocyclesResMap.{vX, vY} (φ : H →ₜ* G) e.toContIntertwiningMap n z := by
  rw [cocyclesResCLE, HomologicalComplex.cyclesMapCLE_apply, cocyclesResMap]
  refine DFunLike.congr_fun (HomologicalComplex.cyclesMapCLM_congr _ _ _ _ fun w ↦ ?_) z
  rfl

/-- Inverse evaluation of `cocyclesResCLE`. -/
@[simp]
theorem cocyclesResCLE_symm_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uH, vY} Y n) :
    (cocyclesResCLE.{vX, vY} φ e n).symm z =
      cocyclesResMap.{vY, vX} (φ.symm : G →ₜ* H)
        (e.symmRestrict ((φ.symm : G →ₜ* H) : G →* H) φ.apply_symm_apply).toContIntertwiningMap
        n z := by
  rw [cocyclesResCLE, HomologicalComplex.cyclesMapCLE_symm_apply, cocyclesResMap]
  refine DFunLike.congr_fun (HomologicalComplex.cyclesMapCLM_congr _ _ _ _ fun w ↦ ?_) z
  rfl

/-- **Continuous `k`-linear equivalence on canonical continuous cohomology in all degrees across
independent universes.** Induced by a topological group isomorphism `φ : H ≃ₜ* G` and an
equivalence of continuous representations `e : (X.ρ.restrict φ).Equiv Y.ρ`. -/
def continuousCohomologyResCLE (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ) :
    continuousCohomology.{uk, uG, vX} n X ≃L[k] continuousCohomology.{uk, uH, vY} n Y :=
  HomologicalComplex.homologyMapCLE
    (TopRep.homogeneousCochains.{uk, uG, vX} X)
    (TopRep.homogeneousCochains.{uk, uH, vY} Y)
    (homogeneousCochainsResCLE.{vX, vY} φ e)
    (homogeneousCochainsResCLE_comm_d.{vX, vY} φ e) n

/-- Forward evaluation of `continuousCohomologyResCLE`. -/
@[simp]
theorem continuousCohomologyResCLE_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ)
    (n : ℕ) (x : continuousCohomology.{uk, uG, vX} n X) :
    continuousCohomologyResCLE.{vX, vY} φ e n x =
      continuousCohomologyResMap.{vX, vY} (φ : H →ₜ* G) e.toContIntertwiningMap n x := by
  rw [continuousCohomologyResCLE, HomologicalComplex.homologyMapCLE_apply,
    continuousCohomologyResMap]
  refine DFunLike.congr_fun (HomologicalComplex.homologyMapCLM_congr _ _ _ _ fun w ↦ ?_) x
  rfl

/-- Inverse evaluation of `continuousCohomologyResCLE`. -/
@[simp]
theorem continuousCohomologyResCLE_symm_apply (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ) (n : ℕ)
    (y : continuousCohomology.{uk, uH, vY} n Y) :
    (continuousCohomologyResCLE.{vX, vY} φ e n).symm y =
      continuousCohomologyResMap.{vY, vX} (φ.symm : G →ₜ* H)
        (e.symmRestrict ((φ.symm : G →ₜ* H) : G →* H) φ.apply_symm_apply).toContIntertwiningMap
        n y := by
  rw [continuousCohomologyResCLE, HomologicalComplex.homologyMapCLE_symm_apply,
    continuousCohomologyResMap]
  refine DFunLike.congr_fun (HomologicalComplex.homologyMapCLM_congr _ _ _ _ fun w ↦ ?_) y
  rfl

/-- `continuousCohomologyResCLE` carries cocycle classes to cocycle classes. -/
theorem continuousCohomologyResCLE_π (φ : H ≃ₜ* G)
    (e : (X.ρ.restrict ((φ : H →ₜ* G) : H →* G)).Equiv Y.ρ)
    (n : ℕ) (z : _root_.ContinuousCohomology.cocycles.{uk, uG, vX} X n) :
    continuousCohomologyResCLE.{vX, vY} φ e n
        (_root_.ContinuousCohomology.π.{uk, uG, vX} X n z) =
      _root_.ContinuousCohomology.π.{uk, uH, vY} Y n (cocyclesResCLE.{vX, vY} φ e n z) := by
  rw [continuousCohomologyResCLE_apply, cocyclesResCLE_apply, continuousCohomologyResMap_π]

end Equiv

/-! ### Independence of the extra universe parameter on `TopRep.{u} k G` -/

section Universe

private theorem coe_refl_apply {G' : Type uG} [Group G'] [TopologicalSpace G'] (g : G') :
    ((ContinuousMulEquiv.refl G' : G' →ₜ* G') : G' →* G') g = g :=
  (rfl)

variable {k : Type uk} [Ring k] [TopologicalSpace k]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For `X : TopRep.{uG} k G`, the degree-`n` homogeneous cochain modules formed at the extra
universe parameters `uG` and `0` are canonically isomorphic as topological `k`-modules. -/
def homogeneousCochainsUniverseCLE (X : TopRep.{uG, uk, uG} k G) (n : ℕ) :
    (TopRep.homogeneousCochains.{uk, uG, uG} X).X n ≃L[k]
      (TopRep.homogeneousCochains.{uk, uG, 0} X).X n :=
  homogeneousCochainsResCLE.{uG, 0} (ContinuousMulEquiv.refl G)
    (X.ρ.restrictOfEqId coe_refl_apply) n

/-- `homogeneousCochainsUniverseCLE` commutes with the differentials of
`TopRep.homogeneousCochains`, forming a chain isomorphism between the homogeneous cochain complexes
at `uG` and `0`. -/
theorem homogeneousCochainsUniverseCLE_comm_d (X : TopRep.{uG, uk, uG} k G)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j)
    (σ : (TopRep.homogeneousCochains.{uk, uG, uG} X).X i) :
    ((TopRep.homogeneousCochains.{uk, uG, 0} X).d i j).hom
        (homogeneousCochainsUniverseCLE X i σ) =
      homogeneousCochainsUniverseCLE X j
        (((TopRep.homogeneousCochains.{uk, uG, uG} X).d i j).hom σ) :=
  homogeneousCochainsResCLE_comm_d.{uG, 0} (ContinuousMulEquiv.refl G)
    (X.ρ.restrictOfEqId coe_refl_apply) i j hij σ

/-- For `X : TopRep.{uG} k G`, the canonical degree-`n` cocycle modules formed at the extra
universe parameters `uG` and `0` are canonically isomorphic as topological `k`-modules. -/
def cocyclesUniverseCLE (X : TopRep.{uG, uk, uG} k G) (n : ℕ) :
    _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X n ≃L[k]
      _root_.ContinuousCohomology.cocycles.{uk, uG, 0} X n :=
  cocyclesResCLE.{uG, 0} (ContinuousMulEquiv.refl G)
    (X.ρ.restrictOfEqId coe_refl_apply) n

/-- Under `iCycles`, `cocyclesUniverseCLE` acts on homogeneous cochains as
`homogeneousCochainsUniverseCLE`. -/
theorem iCycles_cocyclesUniverseCLE_apply (X : TopRep.{uG, uk, uG} k G) (n : ℕ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X n) :
    (TopRep.homogeneousCochains.{uk, uG, 0} X).iCycles n (cocyclesUniverseCLE X n z) =
      homogeneousCochainsUniverseCLE X n
        ((TopRep.homogeneousCochains.{uk, uG, uG} X).iCycles n z) := by
  rw [cocyclesUniverseCLE, cocyclesResCLE_apply, homogeneousCochainsUniverseCLE,
    homogeneousCochainsResCLE_apply, iCycles_cocyclesResMap_apply]

/-- **Extra-universe comparison for canonical continuous cohomology.** For `G : Type uG` and
`X : TopRep.{uG} k G`, the continuous cohomology objects `continuousCohomology.{uk, uG, uG} n X`
and `continuousCohomology.{uk, uG, 0} n X` (which share the same `X` since
`max uG uG = uG = max uG 0`, but are not definitionally equal) are canonically isomorphic as
topological `k`-modules in every degree `n`. -/
def continuousCohomologyUniverseCLE (X : TopRep.{uG, uk, uG} k G) (n : ℕ) :
    continuousCohomology.{uk, uG, uG} n X ≃L[k] continuousCohomology.{uk, uG, 0} n X :=
  continuousCohomologyResCLE.{uG, 0} (ContinuousMulEquiv.refl G)
    (X.ρ.restrictOfEqId coe_refl_apply) n

/-- `continuousCohomologyUniverseCLE` sends the canonical class of a cocycle `z` to the canonical
class of `cocyclesUniverseCLE X n z`. -/
@[simp]
theorem continuousCohomologyUniverseCLE_π (X : TopRep.{uG, uk, uG} k G) (n : ℕ)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X n) :
    continuousCohomologyUniverseCLE X n (_root_.ContinuousCohomology.π.{uk, uG, uG} X n z) =
      _root_.ContinuousCohomology.π.{uk, uG, 0} X n (cocyclesUniverseCLE X n z) := by
  rw [continuousCohomologyUniverseCLE, cocyclesUniverseCLE, continuousCohomologyResCLE_π]

/-- In degree zero, `cocyclesUniverseCLE` preserves the values of a homogeneous cocycle on `G`. -/
theorem iCycles_cocyclesUniverseCLE_zero_apply (X : TopRep.{uG, uk, uG} k G)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X 0) (g₀ : G) :
    ((TopRep.homogeneousCochains.{uk, uG, 0} X).iCycles 0
        (cocyclesUniverseCLE X 0 z)).val g₀ =
      ((TopRep.homogeneousCochains.{uk, uG, uG} X).iCycles 0 z).val g₀ := by
  rw [cocyclesUniverseCLE, cocyclesResCLE_apply, iCycles_cocyclesResMap_zero_apply,
    toContIntertwiningMap_apply, restrictOfEqId_apply]
  rfl

/-- In degree one, `cocyclesUniverseCLE` preserves the values of a homogeneous cocycle on `G²`. -/
theorem iCycles_cocyclesUniverseCLE_one_apply (X : TopRep.{uG, uk, uG} k G)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X 1) (g₀ g₁ : G) :
    ((TopRep.homogeneousCochains.{uk, uG, 0} X).iCycles 1
        (cocyclesUniverseCLE X 1 z)).val g₀ g₁ =
      ((TopRep.homogeneousCochains.{uk, uG, uG} X).iCycles 1 z).val g₀ g₁ := by
  rw [cocyclesUniverseCLE, cocyclesResCLE_apply, iCycles_cocyclesResMap_one_apply,
    toContIntertwiningMap_apply, restrictOfEqId_apply]
  rfl

/-- In degree two, `cocyclesUniverseCLE` preserves the values of a homogeneous cocycle on `G³`. -/
theorem iCycles_cocyclesUniverseCLE_two_apply (X : TopRep.{uG, uk, uG} k G)
    (z : _root_.ContinuousCohomology.cocycles.{uk, uG, uG} X 2) (g₀ g₁ g₂ : G) :
    ((TopRep.homogeneousCochains.{uk, uG, 0} X).iCycles 2
        (cocyclesUniverseCLE X 2 z)).val g₀ g₁ g₂ =
      ((TopRep.homogeneousCochains.{uk, uG, uG} X).iCycles 2 z).val g₀ g₁ g₂ := by
  rw [cocyclesUniverseCLE, cocyclesResCLE_apply, iCycles_cocyclesResMap_two_apply,
    toContIntertwiningMap_apply, restrictOfEqId_apply]
  rfl

/-- **Naturality of `continuousCohomologyUniverseCLE` under compatible pairs.** -/
theorem continuousCohomologyUniverseCLE_map_apply {H' : Type uG} [Group H'] [TopologicalSpace H']
    [IsTopologicalGroup H'] {X : TopRep.{uG, uk, uG} k G} {Y : TopRep.{uG, uk, uG} k H'}
    (φ : H' →ₜ* G) (f : TopRep.res (φ : H' →* G) X ⟶ Y) (n : ℕ)
    (x : continuousCohomology.{uk, uG, uG} n X) :
    continuousCohomologyUniverseCLE Y n (_root_.ContinuousCohomology.map.{uk, uG, uG} φ f n x) =
      _root_.ContinuousCohomology.map.{uk, uG, 0} φ f n
        (continuousCohomologyUniverseCLE X n x) := by
  have hLHS : (_root_.ContinuousCohomology.map.{uk, uG, uG} φ f n) x =
      continuousCohomologyResMap.{uG, uG} φ f.hom n x :=
    DFunLike.congr_fun (hom_map.{uG} φ f n) x
  have hRHS : (_root_.ContinuousCohomology.map.{uk, uG, 0} φ f n)
        (continuousCohomologyUniverseCLE X n x) =
      continuousCohomologyResMap.{0, 0} φ f.hom n (continuousCohomologyUniverseCLE X n x) :=
    DFunLike.congr_fun (hom_map.{0} φ f n) _
  rw [hLHS, hRHS, continuousCohomologyUniverseCLE, continuousCohomologyUniverseCLE,
    continuousCohomologyResCLE_apply, continuousCohomologyResCLE_apply]
  let f' : X.ρ.restrict (φ : H' →* G) →ⁱL Y.ρ := f.hom
  let idY := (Y.ρ.restrictOfEqId (coe_refl_apply (G' := H'))).toContIntertwiningMap
  let idX := (X.ρ.restrictOfEqId (coe_refl_apply (G' := G))).toContIntertwiningMap
  have h1 := DFunLike.congr_fun
    (continuousCohomologyResMap_comp.{uG, uG, 0} φ (ContinuousMulEquiv.refl H' : H' →ₜ* H')
      f' idY n) x
  have h2 := DFunLike.congr_fun
    (continuousCohomologyResMap_comp.{uG, 0, 0} (ContinuousMulEquiv.refl G : G →ₜ* G) φ
      idX f' n) x
  have hcongr := DFunLike.congr_fun
    (continuousCohomologyResMap_congr.{uG, 0} (X := X) (Y := Y)
      (ContinuousMonoidHom.ext fun _ ↦ rfl)
      (idY.comp (f'.restrict ((ContinuousMulEquiv.refl H' : H' →ₜ* H') : H' →* H')))
      (f'.comp (idX.restrict (φ : H' →* G)))
      (fun v ↦ ((comp_restrict_apply idY f' v).trans (by
          rw [toContIntertwiningMap_apply, restrictOfEqId_apply])).trans
        ((comp_restrict_apply f' idX v).trans (by
          rw [toContIntertwiningMap_apply, restrictOfEqId_apply])).symm) n) x
  exact h1.symm.trans (hcongr.trans h2)

/-- **Naturality of `continuousCohomologyUniverseCLE` under coefficient maps.** -/
@[simp]
theorem continuousCohomologyUniverseCLE_coeffMap_apply {X Y : TopRep.{uG, uk, uG} k G}
    (f : X ⟶ Y) (n : ℕ) (x : continuousCohomology.{uk, uG, uG} n X) :
    continuousCohomologyUniverseCLE Y n
        (TauCeti.ContinuousCohomology.coeffMap.{uk, uG, uG} f n x) =
      TauCeti.ContinuousCohomology.coeffMap.{uk, uG, 0} f n
        (continuousCohomologyUniverseCLE X n x) := by
  rw [TauCeti.ContinuousCohomology.coeffMap_def, TauCeti.ContinuousCohomology.coeffMap_def]
  exact continuousCohomologyUniverseCLE_map_apply (ContinuousMonoidHom.id G) f n x

/-- At `uG = 0`, `homogeneousCochainsUniverseCLE` is the identity equivalence in every degree. -/
@[simp]
theorem homogeneousCochainsUniverseCLE_zero_universe {G₀ : Type 0} [Group G₀]
    [TopologicalSpace G₀] [IsTopologicalGroup G₀] (X : TopRep.{0, uk, 0} k G₀) (n : ℕ) :
    homogeneousCochainsUniverseCLE X n =
      ContinuousLinearEquiv.refl k ((TopRep.homogeneousCochains.{uk, 0, 0} X).X n) := by
  ext σ
  rw [homogeneousCochainsUniverseCLE, homogeneousCochainsResCLE_apply]
  exact DFunLike.congr_fun
    (homogeneousCochainsResMap_eq_id.{0} (fun _ ↦ rfl)
      (fun _ ↦ by rw [toContIntertwiningMap_apply, restrictOfEqId_apply]) n) σ

/-- At `uG = 0`, `cocyclesUniverseCLE` is the identity equivalence in every degree. -/
@[simp]
theorem cocyclesUniverseCLE_zero_universe {G₀ : Type 0} [Group G₀]
    [TopologicalSpace G₀] [IsTopologicalGroup G₀] (X : TopRep.{0, uk, 0} k G₀) (n : ℕ) :
    cocyclesUniverseCLE X n =
      ContinuousLinearEquiv.refl k (_root_.ContinuousCohomology.cocycles.{uk, 0, 0} X n) := by
  ext z
  rw [cocyclesUniverseCLE, cocyclesResCLE_apply]
  exact DFunLike.congr_fun
    (cocyclesResMap_eq_id.{0} (fun _ ↦ rfl)
      (fun _ ↦ by rw [toContIntertwiningMap_apply, restrictOfEqId_apply]) n) z

/-- At `uG = 0` the two extra-universe parameters coincide, and `continuousCohomologyUniverseCLE`
is the identity equivalence in every degree. -/
@[simp]
theorem continuousCohomologyUniverseCLE_zero_universe {G₀ : Type 0} [Group G₀]
    [TopologicalSpace G₀] [IsTopologicalGroup G₀] (X : TopRep.{0, uk, 0} k G₀) (n : ℕ) :
    continuousCohomologyUniverseCLE X n =
      ContinuousLinearEquiv.refl k (continuousCohomology.{uk, 0, 0} n X) := by
  ext x
  rw [continuousCohomologyUniverseCLE, continuousCohomologyResCLE_apply]
  exact DFunLike.congr_fun
    (continuousCohomologyResMap_eq_id.{0} (fun _ ↦ rfl)
      (fun _ ↦ by rw [toContIntertwiningMap_apply, restrictOfEqId_apply]) n) x

end Universe

end TauCeti.ContCohomology
